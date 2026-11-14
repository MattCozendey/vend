import Base
import ./code.bend as Codes
import ./shared.bend as Shared

# Crit-bit maps
# -------------
# A map from keys to values. A key is a list of words, read as its bits: the
# bits of each word, the lowest first, one word after the other. Two keys are
# equal exactly when their bits are.
#
# A map is a crit-bit tree (a PATRICIA tree): an entry is a leaf that holds
# its whole key, and a fork splits the keys under it at the first bit where
# they differ. So n entries cost n leaves and fewer than n forks, whatever the
# keys, and a key is held once, shared with whoever made it. A read goes down
# the forks, then compares one key; it skips the words that the keys share.
#
# A fork holds the position of its bit, the key of its first entry (its rep),
# the value of the key that ends at its bit, if any, and the keys whose bit
# there is zero and one. The first entry is the one that ends there, else the
# first of the zero side, else of the one side. So the shape of a map is a
# function of its entries: two maps that hold the same entries are equal.

# a map: no entry, one entry, or a fork at the bit pos
type Crit<-V: Data> is Data:
  Crit.Tip{}
  Crit.Leaf{key: List<&2, U32>, value: V}
  Crit.Fork{rep: List<&2, U32>, pos: Nat, end: Maybe<&2, V>, zero: Crit<V>, one: Crit<V>}

# Bits of keys
# ------------

# the bits of the word w, the lowest first
def Word.bits(n: Nat, w: Word(n)) -> List<&2, Bool>:
  match n:
    case 0n:
      []
    case 1n+p:
      match w:
        case WCon{b, t}:
          b <> Word.bits(p, t)

# the bits of the key k
def Key.bits(k: List<&2, U32>) -> List<&2, Bool>:
  match k:
    case Nil{}:
      []
    case Con{U32{w}, r}:
      List.append(&2, Bool, Word.bits(32n, w), Key.bits(r))

# a and b are the same key, when the words before them were the same (ok):
# a walk that makes no closure
def Key.is_eq.go(a: List<&2, U32>, b: List<&2, U32>, ok: Bool) -> Bool:
  match a b ok:
    case _ _ False{}:
      False{}
    case Nil{} Nil{} True{}:
      True{}
    case Con{x, ra} Con{y, rb} True{}:
      Key.is_eq.go(ra, rb, U32.is_eq(x, y))
    case _ _ True{}:
      False{}

# a and b are the same key
def Key.is_eq(a: List<&2, U32>, b: List<&2, U32>) -> Bool:
  Key.is_eq.go(a, b, True{})

# Key.is_eq.go is the test of the lists, when the words before were the same
def Key.is_eq_go(a: List<&2, U32>, b: List<&2, U32>, ok: Bool) -> {
  Key.is_eq.go(a, b, ok) == List.all.if(u => Shared.List.is_eq(~U32, ~U32.is_eq, a, b), ok): Bool
}:
  match a:
    case Nil{}:
      match b:
        case Nil{}:
          match ok:
            case False{}:
              {==}
            case True{}:
              {==}
        case Con{head, tail}:
          match head:
            case U32{data}:
              match ok:
                case False{}:
                  {==}
                case True{}:
                  {==}
    case Con{head, tail}:
      match b:
        case Nil{}:
          match ok:
            case False{}:
              {==}
            case True{}:
              {==}
        case Con{head1, tail1}:
          match head1:
            case U32{data}:
              match ok:
                case False{}:
                  {==}
                case True{}:
                  Key.is_eq_go(tail, tail1, Cmp.is_eq(U32.cmp(head, U32{data})))

# Key.is_eq is the test of the lists, word by word
def Key.is_eq_list(a: List<&2, U32>, b: List<&2, U32>) -> {
  Key.is_eq(a, b) == Shared.List.is_eq(~U32, ~U32.is_eq, a, b): Bool
}:
  Key.is_eq_go(a, b, True{})

# the first position where the bits a and b differ, or one ends before the
# other (none: they are equal)
def Bits.diff(a: List<&2, Bool>, b: List<&2, Bool>) -> Maybe<&2, Nat>:
  match a b:
    case Nil{} Nil{}:
      None{}
    case Con{x, ra} Con{y, rb}:
      Shared.Bool.when(
        Maybe<&2, Nat>,
        Shared.Bool.is_eq(x, y),
        u => Maybe.map(&2, Nat, Nat, n => 1n+n, Bits.diff(ra, rb)),
        u => Some{0n}
      )
    case _ _:
      Some{0n}

# the first position where the words w and v of n bits differ (none: equal)
def Word.diff(n: Nat, w: Word(n), v: Word(n)) -> Maybe<&2, Nat>:
  match n:
    case 0n:
      None{}
    case 1n+p:
      match w v:
        case WCon{x, rw} WCon{y, rv}:
          Shared.Bool.when(
            Maybe<&2, Nat>,
            Shared.Bool.is_eq(x, y),
            u => Maybe.map(&2, Nat, Nat, m => 1n+m, Word.diff(p, rw, rv)),
            u => Some{0n}
          )

# the first position where the keys a and b differ, after at bits (none:
# equal)
def Key.diff.go(a: List<&2, U32>, b: List<&2, U32>, +at: Nat) -> Maybe<&2, Nat>:
  match a b:
    case Nil{} Nil{}:
      None{}
    case Con{U32{w}, ra} Con{U32{v}, rb}:
      +d = Word.diff(32n, w, v)
      Shared.Bool.when(
        Maybe<&2, Nat>,
        Maybe.is_none(&2, Nat, d),
        u => Key.diff.go(ra, rb, Nat.add(at, 32n)),
        u => Maybe.map(&2, Nat, Nat, n => Nat.add(at, n), d)
      )
    case _ _:
      Some{at}

# the first position where the keys a and b differ, after at bits, as
# Key.diff.go gives it: two equal words are passed with one compare, and no
# read of their bits
def Key.diff.fast(a: List<&2, U32>, b: List<&2, U32>, +at: Nat) -> Maybe<&2, Nat>:
  match a b:
    case Nil{} Nil{}:
      None{}
    case Con{+x, +ra} Con{+y, +rb}:
      Shared.Bool.when(
        Maybe<&2, Nat>,
        U32.is_eq(x, y),
        u => Key.diff.fast(ra, rb, Nat.add(at, 32n)),
        u => Key.diff.go(x <> ra, y <> rb, at)
      )
    case _ _:
      Some{at}

# the first position where the keys a and b differ (none: equal)
def Key.diff(a: List<&2, U32>, b: List<&2, U32>) -> Maybe<&2, Nat>:
  Key.diff.fast(a, b, 0n)

# Cursors
# -------
# A cursor reads the bits of a key from a place: some words of the key, and
# the count of their first bits that are read. A bit is read with one shift
# of its word, and whole words are passed with one compare each.

# a place in a key: the bits of the words rest, after the first at of them
type Cur is Data:
  Cur{at: Nat, rest: List<&2, U32>}

# a cursor at the start of the key k
def Cur.of(k: List<&2, U32>) -> Cur:
  Cur{0n, k}

# the bits bs after the first n: a clear def, for the laws, that reads n
# first
def Bits.past(n: Nat, bs: List<&2, Bool>) -> List<&2, Bool>:
  match n:
    case 0n:
      bs
    case 1n+p:
      List.drop(&2, Bool, bs, 1n+p)

# the bits that the cursor c has yet to read
def Cur.bits(c: Cur) -> List<&2, Bool>:
  match c:
    case Cur{n, r}:
      Bits.past(n, Key.bits(r))

# the words ws have no bit after their first n, where lt says that n is
# less than 32
def Cur.done.go(ws: List<&2, U32>, lt: Bool, +n: Nat) -> Bool:
  match ws lt:
    case Nil{} _:
      True{}
    case Con{w, r} True{}:
      False{}
    case Con{w, r} False{}:
      Cur.done.go(r, Nat.is_lt(Nat.sub(n, 32n), 32n), Nat.sub(n, 32n))

# the cursor c has no bit left
def Cur.done(c: Cur) -> Bool:
  match c:
    case Cur{+n, r}:
      Cur.done.go(r, Nat.is_lt(n, 32n), n)

# the lowest bit of the word w
def U32.low(w: U32) -> Bool:
  match w:
    case U32{WCon{b, t}}:
      b

# the bit n of the words ws (False: none), where lt says that n is less
# than 32
def Cur.bit.go(ws: List<&2, U32>, lt: Bool, +n: Nat) -> Bool:
  match ws lt:
    case Nil{} _:
      False{}
    case Con{w, r} True{}:
      U32.low(U32.shrn(w, n))
    case Con{w, r} False{}:
      Cur.bit.go(r, Nat.is_lt(Nat.sub(n, 32n), 32n), Nat.sub(n, 32n))

# the next bit of the cursor c (False: none is left)
def Cur.bit(c: Cur) -> Bool:
  match c:
    case Cur{+n, r}:
      Cur.bit.go(r, Nat.is_lt(n, 32n), n)

# the cursor c one bit on
def Cur.next(c: Cur) -> Cur:
  match c:
    case Cur{n, r}:
      Cur{1n+n, r}

# a cursor n bits into the words ws, past each whole word before the bit,
# where le says that n is at least 32
def Cur.seek(ws: List<&2, U32>, le: Bool, +n: Nat) -> Cur:
  match ws le:
    case Nil{} _:
      Cur{0n, []}
    case Con{w, r} False{}:
      Cur{n, w <> r}
    case Con{w, r} True{}:
      Cur.seek(r, Nat.is_le(32n, Nat.sub(n, 32n)), Nat.sub(n, 32n))

# a cursor n bits into the words ws
def Cur.words(ws: List<&2, U32>, +n: Nat) -> Cur:
  Cur.seek(ws, Nat.is_le(32n, n), n)

# the cursor c, n bits on
def Cur.skip(n: Nat, c: Cur) -> Cur:
  match c:
    case Cur{at, r}:
      Cur.words(r, Nat.add(at, n))

# Reads
# -----

# the value of the key that ends at a fork, when it is k: the key of the
# first entry of the fork, rep
def Crit.ended(-V: Data, rep: List<&2, U32>, e: Maybe<&2, V>, k: List<&2, U32>) -> Maybe<&2, V>:
  match e:
    case None{}:
      None{}
    case Some{v}:
      Shared.Maybe.when(V, Key.is_eq(rep, k), u => Some{v})

# the value of the key k in m, whose bits from the bit at on are bs: a clear
# def, for the laws
def Crit.find(-V: Data, m: Crit<V>, +at: Nat, +bs: List<&2, Bool>, +k: List<&2, U32>) -> Maybe<&2, V>:
  match m:
    case Crit.Tip{}:
      None{}
    case Crit.Leaf{k2, v}:
      Shared.Maybe.when(V, Key.is_eq(k2, k), u => Some{v})
    case Crit.Fork{rep, +pos, e, z, o}:
      +rb = List.drop(&2, Bool, bs, Nat.sub(pos, at))
      Shared.Bool.when(
        Maybe<&2, V>,
        List.is_empty(&2, Bool, rb),
        u => Crit.ended(V, rep, e, k),
        u => Shared.Bool.when(
          Maybe<&2, V>,
          Shared.List.head_or(Bool, rb, False{}),
          u => Crit.find(V, o, 1n+pos, List.drop(&2, Bool, rb, 1n), k),
          u => Crit.find(V, z, 1n+pos, List.drop(&2, Bool, rb, 1n), k)
        )
      )

# the value of the key k in m, read from the cursor c at the bit at
def Crit.get.go(-V: Data, m: Crit<V>, +at: Nat, +c: Cur, +k: List<&2, U32>) -> Maybe<&2, V>:
  match m:
    case Crit.Tip{}:
      None{}
    case Crit.Leaf{k2, v}:
      Shared.Maybe.when(V, Key.is_eq(k2, k), u => Some{v})
    case Crit.Fork{rep, +pos, e, z, o}:
      +c2 = Cur.skip(Nat.sub(pos, at), c)
      Shared.Bool.when(
        Maybe<&2, V>,
        Cur.done(c2),
        u => Crit.ended(V, rep, e, k),
        u => Shared.Bool.when(
          Maybe<&2, V>,
          Cur.bit(c2),
          u => Crit.get.go(V, o, 1n+pos, Cur.next(c2), k),
          u => Crit.get.go(V, z, 1n+pos, Cur.next(c2), k)
        )
      )

# the value of the key k in m, if m holds k
def Crit.get(-V: Data, m: Crit<V>, +k: List<&2, U32>) -> Maybe<&2, V>:
  Crit.get.go(V, m, 0n, Cur.of(k), k)

# what m holds under the key k, read through every entry: a clear def, for
# the laws, that does not read bits
def Crit.lookup(-V: Data, m: Crit<V>, +k: List<&2, U32>) -> Maybe<&2, V>:
  match m:
    case Crit.Tip{}:
      None{}
    case Crit.Leaf{k2, v}:
      Shared.Maybe.when(V, Key.is_eq(k2, k), u => Some{v})
    case Crit.Fork{rep, p, e, z, o}:
      Maybe.or(&2, V, Crit.ended(V, rep, e, k), Maybe.or(&2, V, Crit.lookup(V, z, k), Crit.lookup(V, o, k)))

# m holds the key k
def Crit.has(-V: Data, m: Crit<V>, +k: List<&2, U32>) -> Bool:
  Maybe.is_some(&2, V, Crit.get(V, m, k))

# a cursor at the bit i of the key k
def Key.at(k: List<&2, U32>, i: Nat) -> Cur:
  Cur.skip(i, Cur.of(k))

# Writes
# ------

# the key of the first entry of m, or d when m holds none
def Crit.rep(-V: Data, m: Crit<V>, d: List<&2, U32>) -> List<&2, U32>:
  match m:
    case Crit.Tip{}:
      d
    case Crit.Leaf{k, v}:
      k
    case Crit.Fork{r, p, e, z, o}:
      r

# the map of a fork at the bit pos, in its one shape: the value e of the key
# k that ends there, and the sides z and o. A fork of one entry is that
# entry; a fork with no end and one side is that side
def Crit.mk(-V: Data, k: List<&2, U32>, pos: Nat, e: Maybe<&2, V>, z: Crit<V>, o: Crit<V>) -> Crit<V>:
  match e z o:
    case None{} Crit.Tip{} y:
      y
    case None{} x Crit.Tip{}:
      x
    case Some{v} Crit.Tip{} Crit.Tip{}:
      Crit.Leaf{k, v}
    case Some{v} x y:
      Crit.Fork{k, pos, Some{v}, x, y}
    case None{} +x y:
      Crit.Fork{Crit.rep(V, x, k), pos, None{}, x, y}

# the fork at the bit d of the entry x, whose key ends at d, and the map y,
# on the side b
def Crit.join.end(-V: Data, x: Crit<V>, y: Crit<V>, +d: Nat, b: Bool) -> Crit<V>:
  match x b:
    case Crit.Leaf{k, v} True{}:
      Crit.Fork{k, d, Some{v}, Crit.Tip{}, y}
    case Crit.Leaf{k, v} False{}:
      Crit.Fork{k, d, Some{v}, y, Crit.Tip{}}
    case +x1 b1:
      Crit.Fork{Crit.rep(V, x1, []), d, None{}, x1, y}

# the fork at the bit d of the maps x and y, whose keys agree before d and
# differ there: the side of each is its first key's bit at d, or its end
def Crit.join(-V: Data, +x: Crit<V>, +y: Crit<V>, +d: Nat) -> Crit<V>:
  +kx = Crit.rep(V, x, [])
  +ky = Crit.rep(V, y, [])
  +cx = Key.at(kx, d)
  +cy = Key.at(ky, d)
  Shared.Bool.when(
    Crit<V>,
    Cur.done(cx),
    u => Crit.join.end(V, x, y, d, Cur.bit(cy)),
    u => Shared.Bool.when(
      Crit<V>,
      Cur.done(cy),
      v => Crit.join.end(V, y, x, d, Cur.bit(cx)),
      v => Shared.Bool.when(
        Crit<V>,
        Cur.bit(cx),
        w => Crit.Fork{ky, d, None{}, y, x},
        w => Crit.Fork{kx, d, None{}, x, y}
      )
    )
  )

# the key of the entry of m that a read of the cursor c, from the bit at,
# reaches: of all keys of m, one that agrees longest with the key of c (none:
# m is empty)
def Crit.near(-V: Data, m: Crit<V>, +at: Nat, +c: Cur) -> Maybe<&2, List<&2, U32>>:
  match m:
    case Crit.Tip{}:
      None{}
    case Crit.Leaf{k, v}:
      Some{k}
    case Crit.Fork{+rep, +pos, e, z, o}:
      +c2 = Cur.skip(Nat.sub(pos, at), c)
      Shared.Bool.when(
        Maybe<&2, List<&2, U32>>,
        Cur.done(c2),
        u => Some{rep},
        u => Shared.Bool.when(
          Maybe<&2, List<&2, U32>>,
          Cur.bit(c2),
          u => Maybe.or(&2, List<&2, U32>, Crit.near(V, o, 1n+pos, Cur.next(c2)), Some{rep}),
          u => Maybe.or(&2, List<&2, U32>, Crit.near(V, z, 1n+pos, Cur.next(c2)), Some{rep})
        )
      )

# the first bit d, if any, is before pos
def Crit.above(d: Maybe<&2, Nat>, +pos: Nat) -> Bool:
  match d:
    case None{}:
      False{}
    case Some{x}:
      Nat.is_lt(x, pos)

# v, or f of the old value w and v
def Crit.merge(~V: Data, ~f: V -> V -> V, e: Maybe<&2, V>, v: V) -> V:
  match e:
    case None{}:
      v
    case Some{w}:
      f(w, v)

# Crit.put at a fork at the bit pos that holds k's place, once the cursor c2
# is at pos: put z and put o put k into each side, from the cursor after pos
def Crit.put.fork(
  ~V: Data,
  ~f: V -> V -> V,
  +k: List<&2, U32>,
  +v: V,
  +rep: List<&2, U32>,
  +pos: Nat,
  +e: Maybe<&2, V>,
  +z: Crit<V>,
  +o: Crit<V>,
  +c2: Cur,
  pz: Cur -> Crit<V>,
  po: Cur -> Crit<V>
) -> Crit<V>:
  Shared.Bool.when(
    Crit<V>,
    Cur.done(c2),
    u => Crit.mk(V, k, pos, Some{Crit.merge(~V, ~f, e, v)}, z, o),
    u => Shared.Bool.when(
      Crit<V>,
      Cur.bit(c2),
      w => Crit.mk(V, rep, pos, e, z, po(Cur.next(c2))),
      w => Crit.mk(V, rep, pos, e, pz(Cur.next(c2)), o)
    )
  )

# m, read from the cursor c at the bit at, with the key k bound to v (to f
# of the old value and v, when m binds k), where d is the first bit where k
# differs from the key that the read reaches (none: k is that key)
def Crit.put(
  ~V: Data,
  ~f: V -> V -> V,
  m: Crit<V>,
  +at: Nat,
  +c: Cur,
  +k: List<&2, U32>,
  +v: V,
  +d: Maybe<&2, Nat>
) -> Crit<V>:
  match m:
    case Crit.Tip{}:
      Crit.Leaf{k, v}
    case Crit.Leaf{+k2, +w}:
      Shared.Bool.when(
        Crit<V>,
        Maybe.is_none(&2, Nat, d),
        u => Crit.Leaf{k2, f(w, v)},
        u => Crit.join(V, Crit.Leaf{k, v}, Crit.Leaf{k2, w}, Maybe.default(&2, Nat, d, 0n))
      )
    case Crit.Fork{+rep, +pos, +e, +z, +o}:
      Shared.Bool.when(
        Crit<V>,
        Crit.above(d, pos),
        u => Crit.join(V, Crit.Leaf{k, v}, Crit.Fork{rep, pos, e, z, o}, Maybe.default(&2, Nat, d, 0n)),
        u => Crit.put.fork(
          ~V,
          ~f,
          k,
          v,
          rep,
          pos,
          e,
          z,
          o,
          Cur.skip(Nat.sub(pos, at), c),
          z2 => Crit.put(~V, ~f, z, 1n+pos, z2, k, v, d),
          o2 => Crit.put(~V, ~f, o, 1n+pos, o2, k, v, d)
        )
      )

# the first bit where k differs from the key n that a read reaches (none: k
# is n, or m is empty)
def Crit.diff(k: List<&2, U32>, n: Maybe<&2, List<&2, U32>>) -> Maybe<&2, Nat>:
  match n:
    case None{}:
      None{}
    case Some{x}:
      Key.diff(k, x)

# m with the key k bound to v, or to f of the old value and v
def Crit.upsert(~V: Data, ~f: V -> V -> V, +m: Crit<V>, +k: List<&2, U32>, v: V) -> Crit<V>:
  Crit.put(~V, ~f, m, 0n, Cur.of(k), k, v, Crit.diff(k, Crit.near(V, m, 0n, Cur.of(k))))

# m with the key k bound to v
def Crit.set(~V: Data, +m: Crit<V>, +k: List<&2, U32>, v: V) -> Crit<V>:
  Crit.upsert(~V, ~(w => x => x), m, k, v)

# a map with no entry
def Crit.new(-V: Data) -> Crit<V>:
  Crit.Tip{}

# Crit.drop at a fork at the bit pos, once the cursor c2 is at pos: dz and do
# drop k from each side, from the cursor after pos
def Crit.drop.fork(
  -V: Data,
  +k: List<&2, U32>,
  +rep: List<&2, U32>,
  +pos: Nat,
  +e: Maybe<&2, V>,
  +z: Crit<V>,
  +o: Crit<V>,
  +c2: Cur,
  dz: Cur -> Crit<V>,
  dn: Cur -> Crit<V>
) -> Crit<V>:
  Shared.Bool.when(
    Crit<V>,
    Cur.done(c2),
    u => Shared.Bool.when(
      Crit<V>,
      Key.is_eq(rep, k),
      w => Crit.mk(V, rep, pos, None{}, z, o),
      w => Crit.Fork{rep, pos, e, z, o}
    ),
    u => Shared.Bool.when(
      Crit<V>,
      Cur.bit(c2),
      w => Crit.mk(V, rep, pos, e, z, dn(Cur.next(c2))),
      w => Crit.mk(V, rep, pos, e, dz(Cur.next(c2)), o)
    )
  )

# m, read from the cursor c at the bit at, without the key k
def Crit.drop.go(-V: Data, m: Crit<V>, +at: Nat, +c: Cur, +k: List<&2, U32>) -> Crit<V>:
  match m:
    case Crit.Tip{}:
      Crit.Tip{}
    case Crit.Leaf{+k2, +w}:
      Shared.Bool.when(Crit<V>, Key.is_eq(k2, k), u => Crit.Tip{}, u => Crit.Leaf{k2, w})
    case Crit.Fork{+rep, +pos, +e, +z, +o}:
      Crit.drop.fork(
        V,
        k,
        rep,
        pos,
        e,
        z,
        o,
        Cur.skip(Nat.sub(pos, at), c),
        z2 => Crit.drop.go(V, z, 1n+pos, z2, k),
        o2 => Crit.drop.go(V, o, 1n+pos, o2, k)
      )

# m without the key k
def Crit.drop(-V: Data, m: Crit<V>, +k: List<&2, U32>) -> Crit<V>:
  Crit.drop.go(V, m, 0n, Cur.of(k), k)

# the bit of the key k at pos (False: k ends before it)
def Key.bit(k: List<&2, U32>, pos: Nat) -> Bool:
  Cur.bit(Key.at(k, pos))

# Crit.union of two forks whose keys agree before both bits, by how the bit
# pa of a compares to the bit pb of b (c): at one bit, the sides join two by
# two (in parallel); else the deeper fork goes to its side of the other
def Crit.union.at(
  ~V: Data,
  ~j: V -> V -> V,
  c: Cmp,
  +ra: List<&2, U32>,
  +pa: Nat,
  +ea: Maybe<&2, V>,
  +rb: List<&2, U32>,
  +pb: Nat,
  +eb: Maybe<&2, V>,
  both: Crit<V> -> Crit<V> -> Crit<V>,
  zz: Unit -> Crit<V>,
  oo: Unit -> Crit<V>,
  zb: Unit -> Crit<V>,
  ob: Unit -> Crit<V>,
  az: Unit -> Crit<V>,
  ao: Unit -> Crit<V>,
  +za: Crit<V>,
  +oa: Crit<V>,
  +zb2: Crit<V>,
  +ob2: Crit<V>
) -> Crit<V>:
  match c:
    case EQ{}:
      zs os = zz(Unit{}) oo(Unit{})
      both(zs, os)
    case LT{}:
      Shared.Bool.when(
        Crit<V>,
        Key.bit(rb, pa),
        u => Crit.mk(V, ra, pa, ea, za, ob(Unit{})),
        u => Crit.mk(V, ra, pa, ea, zb(Unit{}), oa)
      )
    case GT{}:
      Shared.Bool.when(
        Crit<V>,
        Key.bit(ra, pb),
        u => Crit.mk(V, rb, pb, eb, zb2, ao(Unit{})),
        u => Crit.mk(V, rb, pb, eb, az(Unit{}), ob2)
      )

# the entries of a and b: where both hold a key, j of their values
def Crit.union(~V: Data, ~j: V -> V -> V, +a: Crit<V>, +b: Crit<V>) -> Crit<V>:
  match a b:
    case Crit.Tip{} y:
      y
    case x Crit.Tip{}:
      x
    case Crit.Leaf{+k, +v} y:
      Crit.upsert(~V, ~(w => x => j(x, w)), b, k, v)
    case x Crit.Leaf{+k, +w}:
      Crit.upsert(~V, ~j, a, k, w)
    case Crit.Fork{+ra, +pa, +ea, +za, +oa} Crit.Fork{+rb, +pb, +eb, +zb, +ob}:
      +d = Key.diff(ra, rb)
      Shared.Bool.when(
        Crit<V>,
        Bool.and(Crit.above(d, pa), Crit.above(d, pb)),
        u => Crit.join(V, a, b, Maybe.default(&2, Nat, d, 0n)),
        u => Crit.union.at(
          ~V,
          ~j,
          Nat.cmp(pa, pb),
          ra,
          pa,
          ea,
          rb,
          pb,
          eb,
          zs => os => Crit.mk(
            V,
            Bool.pick(List<&2, U32>, Maybe.is_some(&2, V, ea), ra, rb),
            pa,
            Shared.Maybe.join(~V, ~j, ea, eb),
            zs,
            os
          ),
          u2 => Crit.union(~V, ~j, za, zb),
          u2 => Crit.union(~V, ~j, oa, ob),
          u2 => Crit.union(~V, ~j, za, b),
          u2 => Crit.union(~V, ~j, oa, b),
          u2 => Crit.union(~V, ~j, a, zb),
          u2 => Crit.union(~V, ~j, a, ob),
          za,
          oa,
          zb,
          ob
        )
      )

# Crit.minus of two forks whose keys agree before both bits, by how the bit
# pa of a compares to the bit pb of b (c)
def Crit.minus.at(
  -V: Data,
  c: Cmp,
  +ra: List<&2, U32>,
  +pa: Nat,
  +ea: Maybe<&2, V>,
  +rb: List<&2, U32>,
  +pb: Nat,
  +eb: Maybe<&2, V>,
  zz: Unit -> Crit<V>,
  oo: Unit -> Crit<V>,
  zb: Unit -> Crit<V>,
  ob: Unit -> Crit<V>,
  az: Unit -> Crit<V>,
  ao: Unit -> Crit<V>,
  +za: Crit<V>,
  +oa: Crit<V>
) -> Crit<V>:
  match c:
    case EQ{}:
      zs os = zz(Unit{}) oo(Unit{})
      Crit.mk(V, ra, pa, Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, eb), None{}, ea), zs, os)
    case LT{}:
      Shared.Bool.when(
        Crit<V>,
        Key.bit(rb, pa),
        u => Crit.mk(V, ra, pa, ea, za, ob(Unit{})),
        u => Crit.mk(V, ra, pa, ea, zb(Unit{}), oa)
      )
    case GT{}:
      Shared.Bool.when(Crit<V>, Key.bit(ra, pb), u => ao(Unit{}), u => az(Unit{}))

# the entries of a whose keys b lacks
def Crit.minus(-V: Data, +a: Crit<V>, +b: Crit<V>) -> Crit<V>:
  match a b:
    case Crit.Tip{} y:
      Crit.Tip{}
    case x Crit.Tip{}:
      x
    case Crit.Leaf{+k, +v} y:
      Shared.Bool.when(Crit<V>, Crit.has(V, b, k), u => Crit.Tip{}, u => Crit.Leaf{k, v})
    case x Crit.Leaf{+k, w}:
      Crit.drop(V, a, k)
    case Crit.Fork{+ra, +pa, +ea, +za, +oa} Crit.Fork{+rb, +pb, +eb, +zb, +ob}:
      +d = Key.diff(ra, rb)
      Shared.Bool.when(
        Crit<V>,
        Bool.and(Crit.above(d, pa), Crit.above(d, pb)),
        u => a,
        u => Crit.minus.at(
          V,
          Nat.cmp(pa, pb),
          ra,
          pa,
          ea,
          rb,
          pb,
          eb,
          u2 => Crit.minus(V, za, zb),
          u2 => Crit.minus(V, oa, ob),
          u2 => Crit.minus(V, za, b),
          u2 => Crit.minus(V, oa, b),
          u2 => Crit.minus(V, a, zb),
          u2 => Crit.minus(V, a, ob),
          za,
          oa
        )
      )

# the number of entries of m
def Crit.size(-V: Data, m: Crit<V>) -> Nat:
  match m:
    case Crit.Tip{}:
      0n
    case Crit.Leaf{k, v}:
      1n
    case Crit.Fork{r, p, e, z, o}:
      zs os = Crit.size(V, z) Crit.size(V, o)
      Shared.Nat.add_if(Maybe.is_some(&2, V, e), Nat.add(zs, os))

# an entry of a map: a key and its value
type Bind<-V: Data> is Data:
  Bind{key: List<&2, U32>, value: V}

# the entries of m, in the order of their keys, then rest
def Crit.entries.go(-V: Data, m: Crit<V>, rest: List<&2, Bind<V>>) -> List<&2, Bind<V>>:
  match m:
    case Crit.Tip{}:
      rest
    case Crit.Leaf{k, v}:
      Bind{k, v} <> rest
    case Crit.Fork{r, p, None{}, z, o}:
      Crit.entries.go(V, z, Crit.entries.go(V, o, rest))
    case Crit.Fork{r, p, Some{v}, z, o}:
      Bind{r, v} <> Crit.entries.go(V, z, Crit.entries.go(V, o, rest))

# the entries of m, in the order of their keys
def Crit.entries(-V: Data, m: Crit<V>) -> List<&2, Bind<V>>:
  Crit.entries.go(V, m, [])

# each key of the entries es is a key of m
def Crit.within.go(-V: Data, es: List<&2, Bind<V>>, +m: Crit<V>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Con{Bind{k, v}, rest}:
      List.all.if(u => Crit.within.go(V, rest, m), Crit.has(V, m, k))

# each key of a is a key of b
def Crit.within(-V: Data, a: Crit<V>, b: Crit<V>) -> Bool:
  Crit.within.go(V, Crit.entries(V, a), b)

# Laws of cursors
# ---------------
# A cursor reads exactly the bits that it has yet to read (Cur.bits): each
# move of a cursor is the same move on its bits.

# a word of n bits has n bits
def Word.bits_length(n: Nat, w: Word(n)) -> {List.length(&2, Bool, Word.bits(n, w)) == n: Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{b, t}:
          %Equal.sym(Nat, List.length(&2, Bool, Word.bits(p, t)), p, Word.bits_length(p, t)): {
            1n+_ == 1n+p: Nat
          }
          {==}

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- a proof does not run
# the bits after the first n are the bits without their first n
def Bits.past_drop(n: Nat, bs: List<&2, Bool>) -> {
  Bits.past(n, bs) == List.drop(&2, Bool, bs, n): List<&2, Bool>
}:
  match n:
    case 0n:
      Equal.sym(List<&2, Bool>, List.drop(&2, Bool, bs, 0n), bs, Shared.List.drop_zero(&2, Bool, bs))
    case 1n+p:
      {==}

# bits without their first n and then one more are without their first 1+n
def Bits.drop_succ(xs: List<&2, Bool>, n: Nat) -> {
  List.drop(&2, Bool, xs, 1n+n) == List.drop(&2, Bool, List.drop(&2, Bool, xs, n), 1n): List<&2, Bool>
}:
  match xs n:
    case Nil{} n:
      {==}
    case Con{h, t} 0n:
      {==}
    case Con{h, t} 1n+p:
      Bits.drop_succ(t, p)

# bits without their first a and then n more are without their first a+n
def Bits.drop_add(xs: List<&2, Bool>, a: Nat, -n: Nat) -> {
  List.drop(&2, Bool, List.drop(&2, Bool, xs, a), n) == List.drop(&2, Bool, xs, Nat.add(a, n)): List<&2, Bool>
}:
  match xs a:
    case Nil{} a:
      {==}
    case Con{h, t} 0n:
      {==}
    case Con{h, t} 1n+p:
      Bits.drop_add(t, p, n)

# the bit n of the bits xs (False: none)
def Bits.nth(xs: List<&2, Bool>, n: Nat) -> Bool:
  Shared.List.head_or(Bool, List.drop(&2, Bool, xs, n), False{})

# the bits xs without their first, then False: the bits of a word shifted
# down by one
def Bits.shift(xs: List<&2, Bool>) -> List<&2, Bool>:
  match xs:
    case Nil{}:
      []
    case Con{x, r}:
      List.append(&2, Bool, r, [False{}])

# a False after the bits changes no bit
def Bits.nth_pad(r: List<&2, Bool>, n: Nat) -> {
  Bits.nth(List.append(&2, Bool, r, [False{}]), n) == Bits.nth(r, n): Bool
}:
  match r n:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+p:
      {==}
    case Con{y, t} 0n:
      {==}
    case Con{y, t} 1n+p:
      Bits.nth_pad(t, p)

# the bit n of bits shifted down by one is their bit 1+n
def Bits.nth_shift(xs: List<&2, Bool>, n: Nat) -> {
  Bits.nth(Bits.shift(xs), n) == Bits.nth(xs, 1n+n): Bool
}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, r}:
      Bits.nth_pad(r, n)

# a bit of bits before others is the bit of the first
def Bits.nth_append(a: List<&2, Bool>, -b: List<&2, Bool>, n: Nat) -> {
  Nat.is_lt(n, List.length(&2, Bool, a)) == True{}: Bool
} -> {Bits.nth(List.append(&2, Bool, a, b), n) == Bits.nth(a, n): Bool}:
  match a n:
    case Nil{} 0n:
      h => Empty.absurd(
        {Bits.nth(List.append(&2, Bool, [], b), 0n) == Bits.nth([], 0n): Bool},
        Shared.Bool.false_ne_true(h)
      )
    case Nil{} 1n+p:
      h => Empty.absurd(
        {Bits.nth(List.append(&2, Bool, [], b), 1n+p) == Bits.nth([], 1n+p): Bool},
        Shared.Bool.false_ne_true(h)
      )
    case Con{x, t} 0n:
      h => {==}
    case Con{x, t} 1n+p:
      h => Bits.nth_append(t, b, p)(h)

# bits before others have a bit after their first n, when they are more
# than n
def Bits.left_append(a: List<&2, Bool>, -b: List<&2, Bool>, n: Nat) -> {
  Nat.is_lt(n, List.length(&2, Bool, a)) == True{}: Bool
} -> {
  List.is_empty(&2, Bool, List.drop(&2, Bool, List.append(&2, Bool, a, b), n)) == False{}: Bool
}:
  match a n:
    case Nil{} 0n:
      h => Empty.absurd(
        {List.is_empty(&2, Bool, List.drop(&2, Bool, List.append(&2, Bool, [], b), 0n)) == False{}: Bool},
        Shared.Bool.false_ne_true(h)
      )
    case Nil{} 1n+p:
      h => Empty.absurd(
        {List.is_empty(&2, Bool, List.drop(&2, Bool, List.append(&2, Bool, [], b), 1n+p)) == False{}: Bool},
        Shared.Bool.false_ne_true(h)
      )
    case Con{x, t} 0n:
      h => {==}
    case Con{x, t} 1n+p:
      h => Bits.left_append(t, b, p)(h)

# the bits of a word that makes room for one more high bit are its bits,
# then False
def Word.bits_pad(p: Nat, t: Word(p)) -> {
  Word.bits(1n+p, Word.shr.pad(p, t)) == List.append(&2, Bool, Word.bits(p, t), [False{}]): List<&2, Bool>
}:
  match p:
    case 0n:
      {==}
    case 1n+q:
      match t:
        case WCon{b, t2}:
          Equal.cong(
            List<&2, Bool>,
            List<&2, Bool>,
            z => b <> z,
            Word.bits(1n+q, Word.shr.pad(q, t2)),
            List.append(&2, Bool, Word.bits(q, t2), [False{}]),
            Word.bits_pad(q, t2)
          )

# the bits of a word shifted down by one are its bits shifted down by one
def Word.bits_shr(n: Nat, w: Word(n)) -> {
  Word.bits(n, Word.shr(n, w)) == Bits.shift(Word.bits(n, w)): List<&2, Bool>
}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{b, t}:
          Word.bits_pad(p, t)

# a word shifted down by one and then by n is shifted down by n and then by
# one
def U32.shrn_shr(a: U32, n: Nat) -> {U32.shrn(U32.shr(a), n) == U32.shr(U32.shrn(a, n)): U32}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(
        U32,
        U32,
        U32.shr,
        U32.shrn(U32.shr(a), p),
        U32.shr(U32.shrn(a, p)),
        U32.shrn_shr(a, p)
      )

# the lowest bit of a word shifted down by n is the bit n of its bits
def U32.low_shrn(n: Nat, +w: Word(32n)) -> {
  U32.low(U32.shrn(U32{w}, n)) == Bits.nth(Word.bits(32n, w), n): Bool
}:
  match n:
    case 0n:
      match w:
        case WCon{b, t}:
          {==}
    case 1n+(+p):
      Equal.trans(
        Bool,
        U32.low(U32.shrn(U32{w}, 1n+p)),
        U32.low(U32.shrn(U32{Word.shr(32n, w)}, p)),
        Bits.nth(Word.bits(32n, w), 1n+p),
        Equal.cong(
          U32,
          Bool,
          U32.low,
          U32.shr(U32.shrn(U32{w}, p)),
          U32.shrn(U32.shr(U32{w}), p),
          Equal.sym(
            U32,
            U32.shrn(U32.shr(U32{w}), p),
            U32.shr(U32.shrn(U32{w}, p)),
            U32.shrn_shr(U32{w}, p)
          )
        ),
        Equal.trans(
          Bool,
          U32.low(U32.shrn(U32{Word.shr(32n, w)}, p)),
          Bits.nth(Bits.shift(Word.bits(32n, w)), p),
          Bits.nth(Word.bits(32n, w), 1n+p),
          Equal.trans(
            Bool,
            U32.low(U32.shrn(U32{Word.shr(32n, w)}, p)),
            Bits.nth(Word.bits(32n, Word.shr(32n, w)), p),
            Bits.nth(Bits.shift(Word.bits(32n, w)), p),
            U32.low_shrn(p, Word.shr(32n, w)),
            Equal.cong(
              List<&2, Bool>,
              Bool,
              z => Bits.nth(z, p),
              Word.bits(32n, Word.shr(32n, w)),
              Bits.shift(Word.bits(32n, w)),
              Word.bits_shr(32n, w)
            )
          ),
          Bits.nth_shift(Word.bits(32n, w), p)
        )
      )

# the bits of a word and of the words after it, without their first n, are
# the bits of the words after it without their first n-32, when n is at
# least 32
def Key.drop_word(+x: Word(32n), r: List<&2, U32>, n: Nat) -> {
  Nat.is_le(32n, n) == True{}: Bool
} -> {
  List.drop(&2, Bool, Key.bits(U32{x} <> r), n) == List.drop(&2, Bool, Key.bits(r), Nat.sub(n, 32n)): List<&2, Bool>
}:
  h => (
    %Word.bits_length(32n, x): {List.drop(&2, Bool, List.append(&2, Bool, Word.bits(32n, x), Key.bits(r)), n) == List.drop(&2, Bool, Key.bits(r), Nat.sub(n, _)): List<&2, Bool>}
    Shared.List.drop_append_le(Bool, Word.bits(32n, x), Key.bits(r), n)((
        %Equal.sym(Nat, List.length(&2, Bool, Word.bits(32n, x)), 32n, Word.bits_length(32n, x)): {Nat.is_le(_, n) == True{}: Bool}
        h)))

# the bit n of some words, read word by word, is the bit n of their bits
def Cur.bit_go(ws: List<&2, U32>, lt: Bool, +n: Nat) -> {
  lt == Nat.is_lt(n, 32n): Bool
} -> {Cur.bit.go(ws, lt, n) == Bits.nth(Key.bits(ws), n): Bool}:
  match ws lt:
    case Nil{} lt:
      e => {==}
    case Con{U32{+x}, +r} True{}:
      e => Equal.trans(
        Bool,
        U32.low(U32.shrn(U32{x}, n)),
        Bits.nth(Word.bits(32n, x), n),
        Bits.nth(List.append(&2, Bool, Word.bits(32n, x), Key.bits(r)), n),
        U32.low_shrn(n, x),
        Equal.sym(
          Bool,
          Bits.nth(List.append(&2, Bool, Word.bits(32n, x), Key.bits(r)), n),
          Bits.nth(Word.bits(32n, x), n),
          Bits.nth_append(Word.bits(32n, x), Key.bits(r), n)((
              %Equal.sym(Nat, List.length(&2, Bool, Word.bits(32n, x)), 32n, Word.bits_length(32n, x)): {Nat.is_lt(n, _) == True{}: Bool}
              Equal.sym(Bool, True{}, Nat.is_lt(n, 32n), e)))
        )
      )
    case Con{U32{+x}, +r} False{}:
      e => (
        %Equal.sym(List<&2, Bool>, List.drop(&2, Bool, Key.bits(U32{x} <> r), n), List.drop(&2, Bool, Key.bits(r), Nat.sub(n, 32n)), Key.drop_word(x, r, n)(Shared.Nat.nlt_le(n, 32n)(Equal.sym(Bool, False{}, Nat.is_lt(n, 32n), e)))): {Cur.bit.go(r, Nat.is_lt(Nat.sub(n, 32n), 32n), Nat.sub(n, 32n)) == Shared.List.head_or(Bool, _, False{}): Bool}
        Cur.bit_go(r, Nat.is_lt(Nat.sub(n, 32n), 32n), Nat.sub(n, 32n))({==}))

# some words have no bit after their first n, read word by word, when
# their bits have none
def Cur.done_go(ws: List<&2, U32>, lt: Bool, +n: Nat) -> {
  lt == Nat.is_lt(n, 32n): Bool
} -> {
  Cur.done.go(ws, lt, n) == List.is_empty(&2, Bool, List.drop(&2, Bool, Key.bits(ws), n)): Bool
}:
  match ws lt:
    case Nil{} lt:
      e => {==}
    case Con{U32{+x}, +r} True{}:
      e => Equal.sym(
        Bool,
        List.is_empty(&2, Bool, List.drop(&2, Bool, List.append(&2, Bool, Word.bits(32n, x), Key.bits(r)), n)),
        False{},
        Bits.left_append(Word.bits(32n, x), Key.bits(r), n)((
            %Equal.sym(Nat, List.length(&2, Bool, Word.bits(32n, x)), 32n, Word.bits_length(32n, x)): {Nat.is_lt(n, _) == True{}: Bool}
            Equal.sym(Bool, True{}, Nat.is_lt(n, 32n), e)))
      )
    case Con{U32{+x}, +r} False{}:
      e => (
        %Equal.sym(List<&2, Bool>, List.drop(&2, Bool, Key.bits(U32{x} <> r), n), List.drop(&2, Bool, Key.bits(r), Nat.sub(n, 32n)), Key.drop_word(x, r, n)(Shared.Nat.nlt_le(n, 32n)(Equal.sym(Bool, False{}, Nat.is_lt(n, 32n), e)))): {Cur.done.go(r, Nat.is_lt(Nat.sub(n, 32n), 32n), Nat.sub(n, 32n)) == List.is_empty(&2, Bool, _): Bool}
        Cur.done_go(r, Nat.is_lt(Nat.sub(n, 32n), 32n), Nat.sub(n, 32n))({==}))

# a cursor n bits into some words, a word at a time, reads their bits after
# the first n
def Cur.seek_bits(ws: List<&2, U32>, le: Bool, +n: Nat) -> {
  le == Nat.is_le(32n, n): Bool
} -> {Cur.bits(Cur.seek(ws, le, n)) == List.drop(&2, Bool, Key.bits(ws), n): List<&2, Bool>}:
  match ws le:
    case Nil{} le:
      e => {==}
    case Con{U32{x}, +r} False{}:
      e => Bits.past_drop(n, Key.bits(U32{x} <> r))
    case Con{U32{+x}, +r} True{}:
      e => (
        %Equal.sym(List<&2, Bool>, List.drop(&2, Bool, Key.bits(U32{x} <> r), n), List.drop(&2, Bool, Key.bits(r), Nat.sub(n, 32n)), Key.drop_word(x, r, n)(Equal.sym(Bool, True{}, Nat.is_le(32n, n), e))): {Cur.bits(Cur.seek(r, Nat.is_le(32n, Nat.sub(n, 32n)), Nat.sub(n, 32n))) == _: List<&2, Bool>}
        Cur.seek_bits(r, Nat.is_le(32n, Nat.sub(n, 32n)), Nat.sub(n, 32n))({==}))

# a cursor n bits into the words ws reads their bits after the first n
def Cur.words_bits(ws: List<&2, U32>, +n: Nat) -> {
  Cur.bits(Cur.words(ws, n)) == List.drop(&2, Bool, Key.bits(ws), n): List<&2, Bool>
}:
  Cur.seek_bits(ws, Nat.is_le(32n, n), n)({==})

# a cursor one bit on reads its bits after the first
def Cur.next_bits(c: Cur) -> {Cur.bits(Cur.next(c)) == List.drop(&2, Bool, Cur.bits(c), 1n): List<&2, Bool>}:
  match c:
    case Cur{+n, +r}:
      %Equal.sym(List<&2, Bool>, Bits.past(n, Key.bits(r)), List.drop(&2, Bool, Key.bits(r), n), Bits.past_drop(n, Key.bits(r))): {List.drop(&2, Bool, Key.bits(r), 1n+n) == List.drop(&2, Bool, _, 1n): List<&2, Bool>}
      Bits.drop_succ(Key.bits(r), n)

# a cursor is done when it has no bit left
def Cur.done_bits(c: Cur) -> {Cur.done(c) == List.is_empty(&2, Bool, Cur.bits(c)): Bool}:
  match c:
    case Cur{+n, +r}:
      %Equal.sym(List<&2, Bool>, Bits.past(n, Key.bits(r)), List.drop(&2, Bool, Key.bits(r), n), Bits.past_drop(n, Key.bits(r))): {Cur.done.go(r, Nat.is_lt(n, 32n), n) == List.is_empty(&2, Bool, _): Bool}
      Cur.done_go(r, Nat.is_lt(n, 32n), n)({==})

# the next bit of a cursor is the first of its bits
def Cur.bit_bits(c: Cur) -> {Cur.bit(c) == Shared.List.head_or(Bool, Cur.bits(c), False{}): Bool}:
  match c:
    case Cur{+n, +r}:
      %Equal.sym(List<&2, Bool>, Bits.past(n, Key.bits(r)), List.drop(&2, Bool, Key.bits(r), n), Bits.past_drop(n, Key.bits(r))): {Cur.bit.go(r, Nat.is_lt(n, 32n), n) == Shared.List.head_or(Bool, _, False{}): Bool}
      Cur.bit_go(r, Nat.is_lt(n, 32n), n)({==})

# a cursor n bits on reads its bits after the first n
def Cur.skip_bits(n: Nat, c: Cur) -> {
  Cur.bits(Cur.skip(n, c)) == List.drop(&2, Bool, Cur.bits(c), n): List<&2, Bool>
}:
  match c:
    case Cur{+at, +r}:
      %Equal.sym(List<&2, Bool>, Bits.past(at, Key.bits(r)), List.drop(&2, Bool, Key.bits(r), at), Bits.past_drop(at, Key.bits(r))): {Cur.bits(Cur.words(r, Nat.add(at, n))) == List.drop(&2, Bool, _, n): List<&2, Bool>}
      %Equal.sym(List<&2, Bool>, List.drop(&2, Bool, List.drop(&2, Bool, Key.bits(r), at), n), List.drop(&2, Bool, Key.bits(r), Nat.add(at, n)), Bits.drop_add(Key.bits(r), at, n)): {Cur.bits(Cur.words(r, Nat.add(at, n))) == _: List<&2, Bool>}
      Cur.words_bits(r, Nat.add(at, n))
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# the read of a key from a cursor finds what the clear read of its bits finds
def Crit.get_find(-V: Data, m: Crit<V>, +at: Nat, +c: Cur, +k: List<&2, U32>) -> {
  Crit.get.go(V, m, at, c, k) == Crit.find(V, m, at, Cur.bits(c), k): Maybe<&2, V>
}:
  match m:
    case Crit.Tip{}:
      {==}
    case Crit.Leaf{k2, v}:
      {==}
    case Crit.Fork{+rep, +pos, +e, +z, +o}:
      %Cur.skip_bits(Nat.sub(pos, at), c): {
        Crit.get.go(V, Crit.Fork{rep, pos, e, z, o}, at, c, k)
          == Shared.Bool.when(
            Maybe<&2, V>,
            List.is_empty(&2, Bool, _),
            u => Crit.ended(V, rep, e, k),
            u => Shared.Bool.when(Maybe<&2, V>, Shared.List.head_or(Bool, _, False{}), u => Crit.find(V, o, 1n+pos, List.drop(&2, Bool, _, 1n), k), u => Crit.find(V, z, 1n+pos, List.drop(&2, Bool, _, 1n), k))
          ): Maybe<&2, V>
      }
      %Cur.done_bits(Cur.skip(Nat.sub(pos, at), c)): {
        Crit.get.go(V, Crit.Fork{rep, pos, e, z, o}, at, c, k)
          == Shared.Bool.when(
            Maybe<&2, V>,
            _,
            u => Crit.ended(V, rep, e, k),
            u => Shared.Bool.when(Maybe<&2, V>, Shared.List.head_or(Bool, Cur.bits(Cur.skip(Nat.sub(pos, at), c)), False{}), u => Crit.find(V, o, 1n+pos, List.drop(&2, Bool, Cur.bits(Cur.skip(Nat.sub(pos, at), c)), 1n), k), u => Crit.find(V, z, 1n+pos, List.drop(&2, Bool, Cur.bits(Cur.skip(Nat.sub(pos, at), c)), 1n), k))
          ): Maybe<&2, V>
      }
      %Cur.bit_bits(Cur.skip(Nat.sub(pos, at), c)): {
        Crit.get.go(V, Crit.Fork{rep, pos, e, z, o}, at, c, k)
          == Shared.Bool.when(
            Maybe<&2, V>,
            Cur.done(Cur.skip(Nat.sub(pos, at), c)),
            u => Crit.ended(V, rep, e, k),
            u => Shared.Bool.when(Maybe<&2, V>, _, u => Crit.find(V, o, 1n+pos, List.drop(&2, Bool, Cur.bits(Cur.skip(Nat.sub(pos, at), c)), 1n), k), u => Crit.find(V, z, 1n+pos, List.drop(&2, Bool, Cur.bits(Cur.skip(Nat.sub(pos, at), c)), 1n), k))
          ): Maybe<&2, V>
      }
      %Cur.next_bits(Cur.skip(Nat.sub(pos, at), c)): {
        Crit.get.go(V, Crit.Fork{rep, pos, e, z, o}, at, c, k)
          == Shared.Bool.when(
            Maybe<&2, V>,
            Cur.done(Cur.skip(Nat.sub(pos, at), c)),
            u => Crit.ended(V, rep, e, k),
            u => Shared.Bool.when(Maybe<&2, V>, Cur.bit(Cur.skip(Nat.sub(pos, at), c)), u => Crit.find(V, o, 1n+pos, _, k), u => Crit.find(V, z, 1n+pos, _, k))
          ): Maybe<&2, V>
      }
      %Crit.get_find(V, o, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), k): {
        Crit.get.go(V, Crit.Fork{rep, pos, e, z, o}, at, c, k)
          == Shared.Bool.when(
            Maybe<&2, V>,
            Cur.done(Cur.skip(Nat.sub(pos, at), c)),
            u => Crit.ended(V, rep, e, k),
            u => Shared.Bool.when(Maybe<&2, V>, Cur.bit(Cur.skip(Nat.sub(pos, at), c)), u => _, u => Crit.find(V, z, 1n+pos, Cur.bits(Cur.next(Cur.skip(Nat.sub(pos, at), c))), k))
          ): Maybe<&2, V>
      }
      %Crit.get_find(V, z, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), k): {
        Crit.get.go(V, Crit.Fork{rep, pos, e, z, o}, at, c, k)
          == Shared.Bool.when(
            Maybe<&2, V>,
            Cur.done(Cur.skip(Nat.sub(pos, at), c)),
            u => Crit.ended(V, rep, e, k),
            u => Shared.Bool.when(Maybe<&2, V>, Cur.bit(Cur.skip(Nat.sub(pos, at), c)), u => Crit.get.go(V, o, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), k), u => _)
          ): Maybe<&2, V>
      }
      {==}

# the read of a key finds what the clear read of its bits finds
def Crit.get_is_find(-V: Data, m: Crit<V>, +k: List<&2, U32>) -> {
  Crit.get(V, m, k) == Crit.find(V, m, 0n, Key.bits(k), k): Maybe<&2, V>
}:
  Crit.get_find(V, m, 0n, Cur.of(k), k)

# Laws of differences
# -------------------

# the first difference of a part that agrees is the first one after it, n on
def Bits.then(d: Maybe<&2, Nat>, +n: Nat, rest: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match d:
    case Some{x}:
      Some{x}
    case None{}:
      Maybe.map(&2, Nat, Nat, m => Nat.add(n, m), rest)

# a difference moved by no bits is the same
def Bits.map_zero(d: Maybe<&2, Nat>) -> {Maybe.map(&2, Nat, Nat, m => Nat.add(0n, m), d) == d: Maybe<&2, Nat>}:
  match d:
    case None{}:
      {==}
    case Some{x}:
      {==}

# the words w and v differ first where their bits do
def Word.diff_bits(n: Nat, w: Word(n), v: Word(n)) -> {
  Word.diff(n, w, v) == Bits.diff(Word.bits(n, w), Word.bits(n, v)): Maybe<&2, Nat>
}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w v:
        case WCon{+x, +rw} WCon{+y, +rv}:
          %Equal.sym(
            Maybe<&2, Nat>,
            Word.diff(p, rw, rv),
            Bits.diff(Word.bits(p, rw), Word.bits(p, rv)),
            Word.diff_bits(p, rw, rv)
          ): {
            Shared.Bool.when(
              Maybe<&2, Nat>,
              Shared.Bool.is_eq(x, y),
              u => Maybe.map(&2, Nat, Nat, m => 1n+m, _),
              u => Some{0n}
            )
              == Shared.Bool.when(
                Maybe<&2, Nat>,
                Shared.Bool.is_eq(x, y),
                u => Maybe.map(&2, Nat, Nat, m => 1n+m, Bits.diff(Word.bits(p, rw), Word.bits(p, rv))),
                u => Some{0n}
              ): Maybe<&2, Nat>
          }
          {==}

# a difference one bit on, after a part of p bits, is after a part of p + 1
def Bits.then_succ(d: Maybe<&2, Nat>, +p: Nat, e: Maybe<&2, Nat>) -> {
  Maybe.map(&2, Nat, Nat, m => 1n+m, Bits.then(d, p, e))
    == Bits.then(Maybe.map(&2, Nat, Nat, m => 1n+m, d), 1n+p, e): Maybe<&2, Nat>
}:
  match d e:
    case Some{x} e1:
      {==}
    case None{} None{}:
      {==}
    case None{} Some{m}:
      {==}

# Bits.diff_append at a first bit, once it is known whether x and y are the
# same (b)
def Bits.diff_append.at(
  +p: Nat,
  +x: Bool,
  +y: Bool,
  +rw: Word(p),
  +rv: Word(p),
  +a: List<&2, Bool>,
  +b2: List<&2, Bool>,
  b: Bool,
  ih: {
    Bits.diff(List.append(&2, Bool, Word.bits(p, rw), a), List.append(&2, Bool, Word.bits(p, rv), b2))
      == Bits.then(Word.diff(p, rw, rv), p, Bits.diff(a, b2)): Maybe<&2, Nat>
  }
) -> {
  Shared.Bool.when(
    Maybe<&2, Nat>,
    b,
    u => Maybe.map(
      &2,
      Nat,
      Nat,
      n => 1n+n,
      Bits.diff(List.append(&2, Bool, Word.bits(p, rw), a), List.append(&2, Bool, Word.bits(p, rv), b2))
    ),
    u => Some{0n}
  )
    == Bits.then(
      Shared.Bool.when(
        Maybe<&2, Nat>,
        b,
        u => Maybe.map(&2, Nat, Nat, m => 1n+m, Word.diff(p, rw, rv)),
        u => Some{0n}
      ),
      1n+p,
      Bits.diff(a, b2)
    ): Maybe<&2, Nat>
}:
  match b:
    case True{}:
      %Equal.sym(
        Maybe<&2, Nat>,
        Bits.diff(List.append(&2, Bool, Word.bits(p, rw), a), List.append(&2, Bool, Word.bits(p, rv), b2)),
        Bits.then(Word.diff(p, rw, rv), p, Bits.diff(a, b2)),
        ih
      ): {
        Maybe.map(&2, Nat, Nat, n => 1n+n, _)
          == Bits.then(Maybe.map(&2, Nat, Nat, m => 1n+m, Word.diff(p, rw, rv)), 1n+p, Bits.diff(a, b2)): Maybe<&2, Nat>
      }
      Bits.then_succ(Word.diff(p, rw, rv), p, Bits.diff(a, b2))
    case False{}:
      {==}

# words of n bits, each with bits after it, differ first where the words do,
# else where the bits after them do, n on
def Bits.diff_append(n: Nat, w: Word(n), v: Word(n), +a: List<&2, Bool>, +b: List<&2, Bool>) -> {
  Bits.diff(List.append(&2, Bool, Word.bits(n, w), a), List.append(&2, Bool, Word.bits(n, v), b))
    == Bits.then(Word.diff(n, w, v), n, Bits.diff(a, b)): Maybe<&2, Nat>
}:
  match n:
    case 0n:
      Equal.sym(
        Maybe<&2, Nat>,
        Maybe.map(&2, Nat, Nat, m => Nat.add(0n, m), Bits.diff(a, b)),
        Bits.diff(a, b),
        Bits.map_zero(Bits.diff(a, b))
      )
    case 1n+(+p):
      match w v:
        case WCon{+x, +rw} WCon{+y, +rv}:
          Bits.diff_append.at(p, x, y, rw, rv, a, b, Shared.Bool.is_eq(x, y), Bits.diff_append(p, rw, rv, a, b))

# a difference moved by at + 32 bits is moved by 32, then by at
def Bits.map_add(+at: Nat, +n: Nat, d: Maybe<&2, Nat>) -> {
  Maybe.map(&2, Nat, Nat, m => Nat.add(Nat.add(at, n), m), d)
    == Maybe.map(&2, Nat, Nat, m => Nat.add(at, m), Maybe.map(&2, Nat, Nat, m => Nat.add(n, m), d)): Maybe<&2, Nat>
}:
  match d:
    case None{}:
      {==}
    case Some{x}:
      %Shared.Nat.add_assoc(at, n, x): {Some{Nat.add(Nat.add(at, n), x)} == Some{_}: Maybe<&2, Nat>}
      {==}

# Key.diff.go at two first words, once their difference d is known
def Key.diff.at(
  +at: Nat,
  d: Maybe<&2, Nat>,
  ra: List<&2, U32>,
  rb: List<&2, U32>,
  ih: {
    Key.diff.go(ra, rb, Nat.add(at, 32n))
      == Maybe.map(&2, Nat, Nat, m => Nat.add(Nat.add(at, 32n), m), Bits.diff(Key.bits(ra), Key.bits(rb))): Maybe<&2, Nat>
  }
) -> {
  Shared.Bool.when(
    Maybe<&2, Nat>,
    Maybe.is_none(&2, Nat, d),
    u => Key.diff.go(ra, rb, Nat.add(at, 32n)),
    u => Maybe.map(&2, Nat, Nat, n => Nat.add(at, n), d)
  )
    == Maybe.map(&2, Nat, Nat, m => Nat.add(at, m), Bits.then(d, 32n, Bits.diff(Key.bits(ra), Key.bits(rb)))): Maybe<&2, Nat>
}:
  match d:
    case None{}:
      %Equal.sym(
        Maybe<&2, Nat>,
        Key.diff.go(ra, rb, Nat.add(at, 32n)),
        Maybe.map(&2, Nat, Nat, m => Nat.add(Nat.add(at, 32n), m), Bits.diff(Key.bits(ra), Key.bits(rb))),
        ih
      ): {
        _
          == Maybe.map(
            &2,
            Nat,
            Nat,
            m => Nat.add(at, m),
            Maybe.map(&2, Nat, Nat, m => Nat.add(32n, m), Bits.diff(Key.bits(ra), Key.bits(rb)))
          ): Maybe<&2, Nat>
      }
      Bits.map_add(at, 32n, Bits.diff(Key.bits(ra), Key.bits(rb)))
    case Some{x}:
      {==}

# the keys a and b differ first where their bits do, at bits on
def Key.diff_go_bits(+a: List<&2, U32>, +b: List<&2, U32>, +at: Nat) -> {
  Key.diff.go(a, b, at) == Maybe.map(&2, Nat, Nat, m => Nat.add(at, m), Bits.diff(Key.bits(a), Key.bits(b))): Maybe<&2, Nat>
}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Con{U32{+w}, +ra} Con{U32{+v}, +rb}:
      %Equal.sym(
        Maybe<&2, Nat>,
        Bits.diff(
          List.append(&2, Bool, Word.bits(32n, w), Key.bits(ra)),
          List.append(&2, Bool, Word.bits(32n, v), Key.bits(rb))
        ),
        Bits.then(Word.diff(32n, w, v), 32n, Bits.diff(Key.bits(ra), Key.bits(rb))),
        Bits.diff_append(32n, w, v, Key.bits(ra), Key.bits(rb))
      ): {
        Key.diff.go(U32{w} <> ra, U32{v} <> rb, at) == Maybe.map(&2, Nat, Nat, m => Nat.add(at, m), _): Maybe<&2, Nat>
      }
      Key.diff.at(at, Word.diff(32n, w, v), ra, rb, Key.diff_go_bits(ra, rb, Nat.add(at, 32n)))
    case Nil{} Con{U32{WCon{b0, t}}, r}:
      %Equal.sym(Nat, Nat.add(at, 0n), at, Shared.Nat.add_zero(at)): {Some{at} == Some{_}: Maybe<&2, Nat>}
      {==}
    case Con{U32{WCon{b0, t}}, r} Nil{}:
      %Equal.sym(Nat, Nat.add(at, 0n), at, Shared.Nat.add_zero(at)): {Some{at} == Some{_}: Maybe<&2, Nat>}
      {==}

# what holds of a test that is true, and of one that is false, holds of the
# test b
def Bool.split(
  -P: Bool -> Type,
  b: Bool,
  t: {b == True{}: Bool} -> P(True{}),
  f: {b == False{}: Bool} -> P(False{})
) -> P(b):
  match b:
    case True{}:
      t({==})
    case False{}:
      f({==})

# the bits of the number x
def U32.word(x: U32) -> Word(32n):
  match x:
    case U32{w}:
      w

# a word differs from itself nowhere
def Word.diff_self(n: Nat, w: Word(n)) -> {Word.diff(n, w, w) == None{}: Maybe<&2, Nat>}:
  match n:
    case 0n:
      {==}
    case 1n+np:
      match w:
        case WCon{head, tail}:
          %Equal.sym(Bool, Shared.Bool.is_eq(head, head), True{}, Shared.Bool.is_eq_refl(head)): {Shared.Bool.when(Maybe<&2, Nat>, _, u => Maybe.map(&2, Nat, Nat, m => 1n+m, Word.diff(np, tail, tail)), u => Some{0n}) == None{}: Maybe<&2, Nat>}
          %Equal.sym(Maybe<&2, Nat>, Word.diff(np, tail, tail), None{}, Word.diff_self(np, tail)): {Maybe.map(&2, Nat, Nat, m => 1n+m, _) == None{}: Maybe<&2, Nat>}
          {==}

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- a proof does not run
# Key.diff.fast gives what Key.diff.go gives
def Key.diff_fast_go(a: List<&2, U32>, b: List<&2, U32>, at: Nat) -> {
  Key.diff.fast(a, b, at) == Key.diff.go(a, b, at): Maybe<&2, Nat>
}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Con{U32{+w}, ra} Con{U32{+v}, rb}:
      Bool.split(
        c => {
          Shared.Bool.when(Maybe<&2, Nat>, c, u => Key.diff.fast(ra, rb, Nat.add(at, 32n)), u => Key.diff.go(U32{w} <> ra, U32{v} <> rb, at))
            == Key.diff.go(U32{w} <> ra, U32{v} <> rb, at): Maybe<&2, Nat>
        },
        U32.is_eq(U32{w}, U32{v}),
        he => (
          %Equal.cong(U32, Word(32n), U32.word, U32{w}, U32{v}, Shared.U32.is_eq_sound(U32{w}, U32{v})(he)): {Key.diff.fast(ra, rb, Nat.add(at, 32n)) == Key.diff.go(U32{w} <> ra, U32{_} <> rb, at): Maybe<&2, Nat>}
          %Equal.sym(Maybe<&2, Nat>, Word.diff(32n, w, w), None{}, Word.diff_self(32n, w)): {Key.diff.fast(ra, rb, Nat.add(at, 32n)) == Shared.Bool.when(Maybe<&2, Nat>, Maybe.is_none(&2, Nat, _), u => Key.diff.go(ra, rb, Nat.add(at, 32n)), u => Maybe.map(&2, Nat, Nat, n => Nat.add(at, n), Word.diff(32n, w, w))): Maybe<&2, Nat>}
          Key.diff_fast_go(ra, rb, Nat.add(at, 32n))),
        ef => {==}
      )
    case Nil{} Con{y, rb}:
      {==}
    case Con{x, ra} Nil{}:
      {==}
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# the keys a and b differ first where their bits do
def Key.diff_bits(+a: List<&2, U32>, +b: List<&2, U32>) -> {
  Key.diff(a, b) == Bits.diff(Key.bits(a), Key.bits(b)): Maybe<&2, Nat>
}:
  %Equal.sym(Maybe<&2, Nat>, Key.diff.fast(a, b, 0n), Key.diff.go(a, b, 0n), Key.diff_fast_go(a, b, 0n)): {_ == Bits.diff(Key.bits(a), Key.bits(b)): Maybe<&2, Nat>}
  %Equal.sym(
    Maybe<&2, Nat>,
    Key.diff.go(a, b, 0n),
    Maybe.map(&2, Nat, Nat, m => Nat.add(0n, m), Bits.diff(Key.bits(a), Key.bits(b))),
    Key.diff_go_bits(a, b, 0n)
  ): {_ == Bits.diff(Key.bits(a), Key.bits(b)): Maybe<&2, Nat>}
  Bits.map_zero(Bits.diff(Key.bits(a), Key.bits(b)))

# Laws of reads
# -------------

# a fork in its one shape holds what its parts hold
def Crit.mk_lookup(
  -V: Data,
  +k0: List<&2, U32>,
  +pos: Nat,
  e: Maybe<&2, V>,
  z: Crit<V>,
  o: Crit<V>,
  +k: List<&2, U32>
) -> {
  Crit.lookup(V, Crit.mk(V, k0, pos, e, z, o), k)
    == Maybe.or(&2, V, Crit.ended(V, k0, e, k), Maybe.or(&2, V, Crit.lookup(V, z, k), Crit.lookup(V, o, k))): Maybe<&2, V>
}:
  match e z o:
    case None{} Crit.Tip{} Crit.Tip{}:
      {==}
    case None{} Crit.Tip{} Crit.Leaf{kl2, vl2}:
      {==}
    case None{} Crit.Tip{} Crit.Fork{fr2, fp2, fe2, fz2, fo2}:
      {==}
    case None{} Crit.Leaf{kl, vl} Crit.Tip{}:
      Equal.sym(Maybe<&2, V>, Maybe.or(&2, V, Crit.lookup(V, Crit.Leaf{kl, vl}, k), None{}), Crit.lookup(V, Crit.Leaf{kl, vl}, k), Shared.Maybe.or_none(V, Crit.lookup(V, Crit.Leaf{kl, vl}, k)))
    case None{} Crit.Leaf{kl, vl} Crit.Leaf{kl2, vl2}:
      {==}
    case None{} Crit.Leaf{kl, vl} Crit.Fork{fr2, fp2, fe2, fz2, fo2}:
      {==}
    case None{} Crit.Fork{fr, fp, fe, fz, fo} Crit.Tip{}:
      Equal.sym(Maybe<&2, V>, Maybe.or(&2, V, Crit.lookup(V, Crit.Fork{fr, fp, fe, fz, fo}, k), None{}), Crit.lookup(V, Crit.Fork{fr, fp, fe, fz, fo}, k), Shared.Maybe.or_none(V, Crit.lookup(V, Crit.Fork{fr, fp, fe, fz, fo}, k)))
    case None{} Crit.Fork{fr, fp, fe, fz, fo} Crit.Leaf{kl2, vl2}:
      {==}
    case None{} Crit.Fork{fr, fp, fe, fz, fo} Crit.Fork{fr2, fp2, fe2, fz2, fo2}:
      {==}
    case Some{v} Crit.Tip{} Crit.Tip{}:
      Equal.sym(Maybe<&2, V>, Maybe.or(&2, V, Shared.Maybe.when(V, Key.is_eq(k0, k), u => Some{v}), None{}), Shared.Maybe.when(V, Key.is_eq(k0, k), u => Some{v}), Shared.Maybe.or_none(V, Shared.Maybe.when(V, Key.is_eq(k0, k), u => Some{v})))
    case Some{v} Crit.Tip{} Crit.Leaf{kl2, vl2}:
      {==}
    case Some{v} Crit.Tip{} Crit.Fork{fr2, fp2, fe2, fz2, fo2}:
      {==}
    case Some{v} Crit.Leaf{kl, vl} Crit.Tip{}:
      {==}
    case Some{v} Crit.Leaf{kl, vl} Crit.Leaf{kl2, vl2}:
      {==}
    case Some{v} Crit.Leaf{kl, vl} Crit.Fork{fr2, fp2, fe2, fz2, fo2}:
      {==}
    case Some{v} Crit.Fork{fr, fp, fe, fz, fo} Crit.Tip{}:
      {==}
    case Some{v} Crit.Fork{fr, fp, fe, fz, fo} Crit.Leaf{kl2, vl2}:
      {==}
    case Some{v} Crit.Fork{fr, fp, fe, fz, fo} Crit.Fork{fr2, fp2, fe2, fz2, fo2}:
      {==}

# a fork of an entry that ends at its bit and a map holds what both hold
def Crit.join.end_lookup(-V: Data, x: Crit<V>, +y: Crit<V>, +d: Nat, b: Bool, +q: List<&2, U32>) -> {
  Crit.lookup(V, Crit.join.end(V, x, y, d, b), q)
    == Maybe.or(&2, V, Crit.lookup(V, x, q), Crit.lookup(V, y, q)): Maybe<&2, V>
}:
  match x b:
    case Crit.Leaf{k, v} True{}:
      {==}
    case Crit.Leaf{k, v} False{}:
      %Equal.sym(
        Maybe<&2, V>,
        Maybe.or(&2, V, Crit.lookup(V, y, q), None{}),
        Crit.lookup(V, y, q),
        Shared.Maybe.or_none(V, Crit.lookup(V, y, q))
      ): {
        Maybe.or(&2, V, Shared.Maybe.when(V, Key.is_eq(k, q), u => Some{v}), _)
          == Maybe.or(&2, V, Shared.Maybe.when(V, Key.is_eq(k, q), u => Some{v}), Crit.lookup(V, y, q)): Maybe<&2, V>
      }
      {==}
    case Crit.Tip{} b1:
      {==}
    case Crit.Fork{r, p, e, z, o} b1:
      {==}

# the fork of two maps that hold no key in common holds what both hold
def Crit.join_lookup(-V: Data, +x: Crit<V>, +y: Crit<V>, +d: Nat, +q: List<&2, U32>) -> {
  Bool.or(Maybe.is_none(&2, V, Crit.lookup(V, x, q)), Maybe.is_none(&2, V, Crit.lookup(V, y, q))) == True{}: Bool
} -> {Crit.lookup(V, Crit.join(V, x, y, d), q) == Maybe.or(&2, V, Crit.lookup(V, x, q), Crit.lookup(V, y, q)): Maybe<&2, V>}:
  +h =>
    +swap = Equal.trans(
      Maybe<&2, V>,
      Maybe.or(&2, V, Crit.lookup(V, y, q), Crit.lookup(V, x, q)),
      Maybe.or(&2, V, Crit.lookup(V, x, q), Crit.lookup(V, y, q)),
      Maybe.or(&2, V, Crit.lookup(V, x, q), Crit.lookup(V, y, q)),
      Shared.Maybe.or_comm(V, Crit.lookup(V, y, q), Crit.lookup(V, x, q))(
        %Shared.Bool.or_comm(Maybe.is_none(&2, V, Crit.lookup(V, x, q)), Maybe.is_none(&2, V, Crit.lookup(V, y, q))): {_ == True{}: Bool}
        h
      ),
      {==}
    )
    +kx = Crit.rep(V, x, [])
    +ky = Crit.rep(V, y, [])
    Shared.Bool.when_cases(
      Crit<V>,
      t => {Crit.lookup(V, t, q) == Maybe.or(&2, V, Crit.lookup(V, x, q), Crit.lookup(V, y, q)): Maybe<&2, V>},
      Cur.done(Key.at(kx, d)),
      u => Crit.join.end(V, x, y, d, Cur.bit(Key.at(ky, d))),
      u => Shared.Bool.when(
        Crit<V>,
        Cur.done(Key.at(ky, d)),
        v => Crit.join.end(V, y, x, d, Cur.bit(Key.at(kx, d))),
        v => Shared.Bool.when(
          Crit<V>,
          Cur.bit(Key.at(kx, d)),
          w => Crit.Fork{ky, d, None{}, y, x},
          w => Crit.Fork{kx, d, None{}, x, y}
        )
      ),
      e1 => Crit.join.end_lookup(V, x, y, d, Cur.bit(Key.at(ky, d)), q),
      e1 => Shared.Bool.when_cases(
        Crit<V>,
        t => {Crit.lookup(V, t, q) == Maybe.or(&2, V, Crit.lookup(V, x, q), Crit.lookup(V, y, q)): Maybe<&2, V>},
        Cur.done(Key.at(ky, d)),
        v => Crit.join.end(V, y, x, d, Cur.bit(Key.at(kx, d))),
        v => Shared.Bool.when(
          Crit<V>,
          Cur.bit(Key.at(kx, d)),
          w => Crit.Fork{ky, d, None{}, y, x},
          w => Crit.Fork{kx, d, None{}, x, y}
        ),
        e2 => Equal.trans(
          Maybe<&2, V>,
          Crit.lookup(V, Crit.join.end(V, y, x, d, Cur.bit(Key.at(kx, d))), q),
          Maybe.or(&2, V, Crit.lookup(V, y, q), Crit.lookup(V, x, q)),
          Maybe.or(&2, V, Crit.lookup(V, x, q), Crit.lookup(V, y, q)),
          Crit.join.end_lookup(V, y, x, d, Cur.bit(Key.at(kx, d)), q),
          swap
        ),
        e2 => Shared.Bool.when_cases(
          Crit<V>,
          t => {Crit.lookup(V, t, q) == Maybe.or(&2, V, Crit.lookup(V, x, q), Crit.lookup(V, y, q)): Maybe<&2, V>},
          Cur.bit(Key.at(kx, d)),
          w => Crit.Fork{ky, d, None{}, y, x},
          w => Crit.Fork{kx, d, None{}, x, y},
          e3 => swap,
          e3 => {==}
        )
      )
    )


# Shape
# -----
# A map that the writes build is well formed (Crit.wf): each fork splits its
# keys at its bit, which is after the bit of the fork above it; the keys of
# each side agree with its rep before the bit and have their side's bit there;
# the key that ends at the bit is the rep; and a fork holds two entries at
# least.

# a first difference d is at n or after (none: no difference)
def Bits.agree(d: Maybe<&2, Nat>, +n: Nat) -> Bool:
  match d:
    case None{}:
      True{}
    case Some{x}:
      Nat.is_le(n, x)

# the keys a and b agree on their first n bits
def Key.agree(a: List<&2, U32>, b: List<&2, U32>, +n: Nat) -> Bool:
  Bits.agree(Key.diff(a, b), n)

# the bit of the key k at pos (none: k ends there, or before)
def Key.side(k: List<&2, U32>, +pos: Nat) -> Maybe<&2, Bool>:
  +c = Key.at(k, pos)
  Shared.Bool.when(Maybe<&2, Bool>, Cur.done(c), u => None{}, u => Some{Cur.bit(c)})

# a side of a fork: its rep, its bit, and which side
type Place is Data:
  Place{rep: List<&2, U32>, pos: Nat, side: Bool}

# the key k belongs to the side g: it agrees with the rep before the bit, and
# has the side's bit there
def Place.has(g: Place, k: List<&2, U32>) -> Bool:
  match g:
    case Place{rep, +pos, b}:
      +k = k
      List.all.if(
        u => Shared.Maybe.is_eq(~Bool, ~Shared.Bool.is_eq, Key.side(k, pos), Some{b}),
        Key.agree(k, rep, pos)
      )

# p holds of g and the key of each entry of m
def Crit.all(~V: Data, ~G: Data, ~p: G -> List<&2, U32> -> Bool, m: Crit<V>, +g: G) -> Bool:
  match m:
    case Crit.Tip{}:
      True{}
    case Crit.Leaf{k, v}:
      p(g)(k)
    case Crit.Fork{rep, pos, e, z, o}:
      List.all.if(
        u => List.all.if(u2 => Crit.all(~V, ~G, ~p, o, g), Crit.all(~V, ~G, ~p, z, g)),
        Bool.or(Maybe.is_none(&2, V, e), p(g)(rep))
      )

# a fork of the end e and the sides z and o holds two entries at least
def Crit.shape(-V: Data, e: Maybe<&2, V>, z: Crit<V>, o: Crit<V>) -> Bool:
  match e z o:
    case Some{v} Crit.Tip{} Crit.Tip{}:
      False{}
    case Some{v} z1 o1:
      True{}
    case None{} Crit.Tip{} o1:
      False{}
    case None{} z1 Crit.Tip{}:
      False{}
    case None{} z1 o1:
      True{}

# the rep of a fork at pos is its first key: the key that ends at pos, else
# the first of the zero side
def Crit.rep_ok(-V: Data, +rep: List<&2, U32>, +pos: Nat, e: Maybe<&2, V>, z: Crit<V>) -> Bool:
  match e:
    case Some{v}:
      Nat.is_eq(List.length(&2, Bool, Key.bits(rep)), pos)
    case None{}:
      Key.is_eq(rep, Crit.rep(V, z, rep))

# m is well formed, below a fork at a bit before lo
def Crit.wf(~V: Data, m: Crit<V>, +lo: Nat) -> Bool:
  match m:
    case Crit.Tip{}:
      True{}
    case Crit.Leaf{k, v}:
      True{}
    case Crit.Fork{+rep, +pos, +e, +z, +o}:
      List.all.if(
        u => List.all.if(
          u => List.all.if(
            u => List.all.if(
              u => List.all.if(
                u => List.all.if(u => Crit.wf(~V, o, 1n+pos), Crit.wf(~V, z, 1n+pos)),
                Crit.all(~V, ~Place, ~Place.has, o, Place{rep, pos, True{}})
              ),
              Crit.all(~V, ~Place, ~Place.has, z, Place{rep, pos, False{}})
            ),
            Crit.rep_ok(V, rep, pos, e, z)
          ),
          Crit.shape(V, e, z, o)
        ),
        Nat.is_le(lo, pos)
      )

# Agreement of bits
# -----------------
# Two lists of bits agree on their first n when both have them and they are
# the same, or both end before; a first difference is where they stop
# agreeing. Agreement is an equivalence on each n, so differences obey the
# laws of a tree of prefixes.

# the bits a and b agree on their first n
def Bits.agree_n(n: Nat, a: List<&2, Bool>, b: List<&2, Bool>) -> Bool:
  match n a b:
    case 0n x y:
      True{}
    case 1n+p Nil{} Nil{}:
      True{}
    case 1n+p Con{x, ra} Con{y, rb}:
      Bool.and(Shared.Bool.is_eq(x, y), Bits.agree_n(p, ra, rb))
    case 1n+p x y:
      False{}

# the first of the bits bs (none: there is none)
def Bits.head(bs: List<&2, Bool>) -> Maybe<&2, Bool>:
  match bs:
    case Nil{}:
      None{}
    case Con{x, r}:
      Some{x}

# the bit of bs at n (none: bs ends before)
def Bits.at(bs: List<&2, Bool>, n: Nat) -> Maybe<&2, Bool>:
  Bits.head(List.drop(&2, Bool, bs, n))

# a difference agrees on 0 bits
def Bits.agree.zero(d: Maybe<&2, Nat>) -> {Bits.agree(d, 0n) == True{}: Bool}:
  match d:
    case None{}:
      {==}
    case Some{x}:
      Shared.Nat.le_zero(x)

# a difference one bit on is one more, and agreement moves with it
def Bits.agree.shift(d: Maybe<&2, Nat>, p: Nat) -> {
  Bits.agree(Maybe.map(&2, Nat, Nat, m => 1n+m, d), 1n+p) == Bits.agree(d, p): Bool
}:
  match d:
    case None{}:
      {==}
    case Some{x}:
      {==}

# at 0 bits, the bits of a and b agree whichever way they differ
def Bits.agree_diff.zero_step(x: Bool, y: Bool, d: Maybe<&2, Nat>) -> {
  Bits.agree(Shared.Bool.when(Maybe<&2, Nat>, Shared.Bool.is_eq(x, y), u => Maybe.map(&2, Nat, Nat, m => 1n+m, d), u => Some{0n}), 0n) == True{}: Bool
}:
  match x y:
    case True{} True{}:
      Bits.agree.zero(Maybe.map(&2, Nat, Nat, m => 1n+m, d))
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      Bits.agree.zero(Maybe.map(&2, Nat, Nat, m => 1n+m, d))

# one bit on: the first bits decide, and the rest agrees with r
def Bits.agree_diff.step(
  x: Bool,
  y: Bool,
  +d: Maybe<&2, Nat>,
  p: Nat,
  r: Bool,
  ih: {Bits.agree(d, p) == r: Bool}
) -> {
  Bits.agree(Shared.Bool.when(Maybe<&2, Nat>, Shared.Bool.is_eq(x, y), u => Maybe.map(&2, Nat, Nat, m => 1n+m, d), u => Some{0n}), 1n+p) == Bool.and(Shared.Bool.is_eq(x, y), r): Bool
}:
  match x y:
    case True{} True{}:
      Equal.trans(Bool, Bits.agree(Maybe.map(&2, Nat, Nat, m => 1n+m, d), 1n+p), Bits.agree(d, p), r, Bits.agree.shift(d, p), ih)
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      Equal.trans(Bool, Bits.agree(Maybe.map(&2, Nat, Nat, m => 1n+m, d), 1n+p), Bits.agree(d, p), r, Bits.agree.shift(d, p), ih)

# a first difference is at n or after exactly when the bits agree on their
# first n
law Bits.agree_diff:
  for a: List<&2, Bool>
  for b: List<&2, Bool>
  for n: Nat
  {Bits.agree(Bits.diff(a, b), n) == Bits.agree_n(n, a, b): Bool}

def Bits.agree_diff(a, b, n):
  match a b:
    case Nil{} Nil{}:
      match n:
        case 0n:
          {==}
        case 1n+p:
          {==}
    case Con{+x, +ra} Con{+y, +rb}:
      match n:
        case 0n:
          Bits.agree_diff.zero_step(x, y, Bits.diff(ra, rb))
        case 1n+(+p):
          Bits.agree_diff.step(x, y, Bits.diff(ra, rb), p, Bits.agree_n(p, ra, rb), Bits.agree_diff(ra, rb, p))
    case Nil{} Con{y, rb}:
      match n:
        case 0n:
          {==}
        case 1n+p:
          {==}
    case Con{x, ra} Nil{}:
      match n:
        case 0n:
          {==}
        case 1n+p:
          {==}

# Bool.is_eq does not depend on the order of its arguments
def Bits.is_eq_comm(a: Bool, b: Bool) -> {Shared.Bool.is_eq(a, b) == Shared.Bool.is_eq(b, a): Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# equal left parts and equal right parts give equal ands
def Bits.and_cong(
  a: Bool,
  b: Bool,
  c: Bool,
  d: Bool,
  ea: {a == c: Bool},
  eb: {b == d: Bool}
) -> {Bool.and(a, b) == Bool.and(c, d): Bool}:
  Equal.trans(
    Bool,
    Bool.and(a, b),
    Bool.and(c, b),
    Bool.and(c, d),
    Equal.cong(Bool, Bool, u => Bool.and(u, b), a, c, ea),
    Equal.cong(Bool, Bool, v => Bool.and(c, v), b, d, eb)
  )

# agreement is the same either way round
law Bits.agree_n_sym:
  for a: List<&2, Bool>
  for b: List<&2, Bool>
  for n: Nat
  {Bits.agree_n(n, a, b) == Bits.agree_n(n, b, a): Bool}

def Bits.agree_n_sym(a, b, n):
  match a b:
    case Nil{} Nil{}:
      match n:
        case 0n:
          {==}
        case 1n+p:
          {==}
    case Con{+x, +ra} Con{+y, +rb}:
      match n:
        case 0n:
          {==}
        case 1n+(+p):
          Bits.and_cong(
            Shared.Bool.is_eq(x, y),
            Bits.agree_n(p, ra, rb),
            Shared.Bool.is_eq(y, x),
            Bits.agree_n(p, rb, ra),
            Bits.is_eq_comm(x, y),
            Bits.agree_n_sym(ra, rb, p)
          )
    case Nil{} Con{y, rb}:
      match n:
        case 0n:
          {==}
        case 1n+p:
          {==}
    case Con{x, ra} Nil{}:
      match n:
        case 0n:
          {==}
        case 1n+p:
          {==}

# the step of agree_n_trans: x, y, z are the first bits, a, b, c what follows
# them; ih is the claim for what follows, and the claim holds for the first bits
def Bits.agree_n_trans.step(
  x: Bool,
  y: Bool,
  z: Bool,
  a: Bool,
  b: Bool,
  c: Bool,
  ih: {a == True{}: Bool} -> {b == True{}: Bool} -> {c == True{}: Bool},
  h1: {Bool.and(Shared.Bool.is_eq(x, y), a) == True{}: Bool},
  h2: {Bool.and(Shared.Bool.is_eq(y, z), b) == True{}: Bool}
) -> {Bool.and(Shared.Bool.is_eq(x, z), c) == True{}: Bool}:
  match x y z:
    case True{} True{} True{}:
      ih(h1)(h2)
    case True{} True{} False{}:
      Empty.absurd({Bool.and(Shared.Bool.is_eq(True{}, False{}), c) == True{}: Bool}, Shared.Bool.false_ne_true(h2))
    case True{} False{} True{}:
      Empty.absurd({Bool.and(Shared.Bool.is_eq(True{}, True{}), c) == True{}: Bool}, Shared.Bool.false_ne_true(h1))
    case True{} False{} False{}:
      Empty.absurd({Bool.and(Shared.Bool.is_eq(True{}, False{}), c) == True{}: Bool}, Shared.Bool.false_ne_true(h1))
    case False{} True{} True{}:
      Empty.absurd({Bool.and(Shared.Bool.is_eq(False{}, True{}), c) == True{}: Bool}, Shared.Bool.false_ne_true(h1))
    case False{} True{} False{}:
      Empty.absurd({Bool.and(Shared.Bool.is_eq(False{}, False{}), c) == True{}: Bool}, Shared.Bool.false_ne_true(h1))
    case False{} False{} True{}:
      Empty.absurd({Bool.and(Shared.Bool.is_eq(False{}, True{}), c) == True{}: Bool}, Shared.Bool.false_ne_true(h2))
    case False{} False{} False{}:
      ih(h1)(h2)

# what agrees with what agrees with c agrees with c
law Bits.agree_n_trans:
  for a: List<&2, Bool>
  for b: List<&2, Bool>
  for c: List<&2, Bool>
  for n: Nat
  {Bits.agree_n(n, a, b) == True{}: Bool}
    -> {Bits.agree_n(n, b, c) == True{}: Bool}
    -> {Bits.agree_n(n, a, c) == True{}: Bool}

def Bits.agree_n_trans(a, b, c, n):
  match a b c:
    case Nil{} Nil{} Nil{}:
      match n:
        case 0n:
          h1 => h2 => {==}
        case 1n+(+p):
          h1 => h2 => {==}
    case Nil{} Nil{} Con{z, rc}:
      match n:
        case 0n:
          h1 => h2 => {==}
        case 1n+(+p):
          h1 => h2 => Empty.absurd({Bits.agree_n(1n+p, Nil{}, Con{z, rc}) == True{}: Bool}, Shared.Bool.false_ne_true(h2))
    case Nil{} Con{x, ra} Nil{}:
      match n:
        case 0n:
          h1 => h2 => {==}
        case 1n+(+p):
          h1 => h2 => {==}
    case Nil{} Con{x, ra} Con{z, rc}:
      match n:
        case 0n:
          h1 => h2 => {==}
        case 1n+(+p):
          h1 => h2 => Empty.absurd({Bits.agree_n(1n+p, Nil{}, Con{z, rc}) == True{}: Bool}, Shared.Bool.false_ne_true(h1))
    case Con{x, ra} Nil{} Nil{}:
      match n:
        case 0n:
          h1 => h2 => {==}
        case 1n+(+p):
          h1 => h2 => Empty.absurd({Bits.agree_n(1n+p, Con{x, ra}, Nil{}) == True{}: Bool}, Shared.Bool.false_ne_true(h1))
    case Con{x, ra} Nil{} Con{z, rc}:
      match n:
        case 0n:
          h1 => h2 => {==}
        case 1n+(+p):
          h1 => h2 => Empty.absurd({Bits.agree_n(1n+p, Con{x, ra}, Con{z, rc}) == True{}: Bool}, Shared.Bool.false_ne_true(h1))
    case Con{x, ra} Con{y, rb} Nil{}:
      match n:
        case 0n:
          h1 => h2 => {==}
        case 1n+(+p):
          h1 => h2 => Empty.absurd({Bits.agree_n(1n+p, Con{x, ra}, Nil{}) == True{}: Bool}, Shared.Bool.false_ne_true(h2))
    case Con{x, +ra} Con{y, +rb} Con{z, +rc}:
      match n:
        case 0n:
          h1 => h2 => {==}
        case 1n+(+p):
          h1 => h2 => Bits.agree_n_trans.step(
            x,
            y,
            z,
            Bits.agree_n(p, ra, rb),
            Bits.agree_n(p, rb, rc),
            Bits.agree_n(p, ra, rc),
            Bits.agree_n_trans(ra, rb, rc, p),
            h1,
            h2
          )

# the step of agree_n_le: x and y are the first bits, a and c what follows
# them; ih turns agreement on a into agreement on c, and h gives a
def Bits.agree_n_le.step(
  x: Bool,
  y: Bool,
  a: Bool,
  c: Bool,
  ih: {a == True{}: Bool} -> {c == True{}: Bool},
  h: {Bool.and(Shared.Bool.is_eq(x, y), a) == True{}: Bool}
) -> {Bool.and(Shared.Bool.is_eq(x, y), c) == True{}: Bool}:
  match x y:
    case True{} True{}:
      ih(h)
    case True{} False{}:
      Empty.absurd({Bool.and(Shared.Bool.is_eq(True{}, False{}), c) == True{}: Bool}, Shared.Bool.false_ne_true(h))
    case False{} True{}:
      Empty.absurd({Bool.and(Shared.Bool.is_eq(False{}, True{}), c) == True{}: Bool}, Shared.Bool.false_ne_true(h))
    case False{} False{}:
      ih(h)

# bits that agree on their first n agree on fewer
law Bits.agree_n_le:
  for a: List<&2, Bool>
  for b: List<&2, Bool>
  for m: Nat
  for n: Nat
  {Nat.is_le(m, n) == True{}: Bool}
    -> {Bits.agree_n(n, a, b) == True{}: Bool}
    -> {Bits.agree_n(m, a, b) == True{}: Bool}

def Bits.agree_n_le(a, b, m, n):
  match a b:
    case Nil{} Nil{}:
      match m:
        case 0n:
          h1 => h2 => {==}
        case 1n+p:
          h1 => h2 => {==}
    case Con{x, +ra} Con{y, +rb}:
      match m:
        case 0n:
          h1 => h2 => {==}
        case 1n+(+p):
          match n:
            case 0n:
              h1 => h2 => Empty.absurd({Bits.agree_n(1n+p, Con{x, ra}, Con{y, rb}) == True{}: Bool}, Shared.Bool.false_ne_true(h1))
            case 1n+(+q):
              h1 => h2 => Bits.agree_n_le.step(x, y, Bits.agree_n(q, ra, rb), Bits.agree_n(p, ra, rb), Bits.agree_n_le(ra, rb, p, q)(h1), h2)
    case Nil{} Con{y, rb}:
      match m:
        case 0n:
          h1 => h2 => {==}
        case 1n+(+p):
          match n:
            case 0n:
              h1 => h2 => Empty.absurd({Bits.agree_n(1n+p, Nil{}, Con{y, rb}) == True{}: Bool}, Shared.Bool.false_ne_true(h1))
            case 1n+(+q):
              h1 => h2 => Empty.absurd({Bits.agree_n(1n+p, Nil{}, Con{y, rb}) == True{}: Bool}, Shared.Bool.false_ne_true(h2))
    case Con{x, ra} Nil{}:
      match m:
        case 0n:
          h1 => h2 => {==}
        case 1n+(+p):
          match n:
            case 0n:
              h1 => h2 => Empty.absurd({Bits.agree_n(1n+p, Con{x, ra}, Nil{}) == True{}: Bool}, Shared.Bool.false_ne_true(h1))
            case 1n+(+q):
              h1 => h2 => Empty.absurd({Bits.agree_n(1n+p, Con{x, ra}, Nil{}) == True{}: Bool}, Shared.Bool.false_ne_true(h2))

# the zero step of agree_n_succ: two first bits, and the empty rest
def Bits.agree_n_succ.zero(x: Bool, y: Bool) -> {Bool.and(Shared.Bool.is_eq(x, y), True{}) == Shared.Bool.is_eq(x, y): Bool}:
  match x y:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# bits agree on n + 1 exactly when they agree on n and have the same bit at n
law Bits.agree_n_succ:
  for a: List<&2, Bool>
  for b: List<&2, Bool>
  for n: Nat
  {
    Bits.agree_n(1n+n, a, b)
      == Bool.and(
        Bits.agree_n(n, a, b),
        Shared.Maybe.is_eq(~Bool, ~Shared.Bool.is_eq, Bits.at(a, n), Bits.at(b, n))
      ): Bool
  }

def Bits.agree_n_succ(a, b, n):
  match a b:
    case Nil{} Nil{}:
      match n:
        case 0n:
          {==}
        case 1n+p:
          {==}
    case Con{+x, +ra} Con{+y, +rb}:
      match n:
        case 0n:
          Bits.agree_n_succ.zero(x, y)
        case 1n+(+p):
          Equal.trans(
            Bool,
            Bool.and(Shared.Bool.is_eq(x, y), Bits.agree_n(1n+p, ra, rb)),
            Bool.and(Shared.Bool.is_eq(x, y), Bool.and(Bits.agree_n(p, ra, rb), Shared.Maybe.is_eq(~Bool, ~Shared.Bool.is_eq, Bits.at(ra, p), Bits.at(rb, p)))),
            Bool.and(Bool.and(Shared.Bool.is_eq(x, y), Bits.agree_n(p, ra, rb)), Shared.Maybe.is_eq(~Bool, ~Shared.Bool.is_eq, Bits.at(ra, p), Bits.at(rb, p))),
            Equal.cong(
              Bool,
              Bool,
              u => Bool.and(Shared.Bool.is_eq(x, y), u),
              Bits.agree_n(1n+p, ra, rb),
              Bool.and(Bits.agree_n(p, ra, rb), Shared.Maybe.is_eq(~Bool, ~Shared.Bool.is_eq, Bits.at(ra, p), Bits.at(rb, p))),
              Bits.agree_n_succ(ra, rb, p)
            ),
            Shared.Bool.and_assoc(Shared.Bool.is_eq(x, y), Bits.agree_n(p, ra, rb), Shared.Maybe.is_eq(~Bool, ~Shared.Bool.is_eq, Bits.at(ra, p), Bits.at(rb, p)))
          )
    case Nil{} Con{y, rb}:
      match n:
        case 0n:
          {==}
        case 1n+p:
          {==}
    case Con{x, ra} Nil{}:
      match n:
        case 0n:
          {==}
        case 1n+p:
          {==}

# a list that is empty has no head
def Key.side_bits.nil(bs: List<&2, Bool>, e: {List.is_empty(&2, Bool, bs) == True{}: Bool}) -> {Bits.head(bs) == None{}: Maybe<&2, Bool>}:
  match bs:
    case Nil{}:
      {==}
    case Con{x, r}:
      Empty.absurd({Some{x} == None{}: Maybe<&2, Bool>}, Shared.Bool.false_ne_true(e))

# a list that is not empty has a head: its first bit
def Key.side_bits.some(bs: List<&2, Bool>, e: {List.is_empty(&2, Bool, bs) == False{}: Bool}) -> {Some{Shared.List.head_or(Bool, bs, False{})} == Bits.head(bs): Maybe<&2, Bool>}:
  match bs:
    case Nil{}:
      Empty.absurd({Some{False{}} == None{}: Maybe<&2, Bool>}, Shared.Bool.false_ne_true(Equal.sym(Bool, List.is_empty(&2, Bool, Nil{}), False{}, e)))
    case Con{x, r}:
      {==}

# the bit of a cursor, or none when it is done, is the head of the bits it has
# yet to read
def Key.side_bits.cur(+c: Cur) -> {
  Shared.Bool.when(Maybe<&2, Bool>, Cur.done(c), u => None{}, u => Some{Cur.bit(c)}) == Bits.head(Cur.bits(c)): Maybe<&2, Bool>
}:
  Shared.Bool.when_cases(
    Maybe<&2, Bool>,
    m => {m == Bits.head(Cur.bits(c)): Maybe<&2, Bool>},
    Cur.done(c),
    u => None{},
    u => Some{Cur.bit(c)},
    h => Equal.sym(
      Maybe<&2, Bool>,
      Bits.head(Cur.bits(c)),
      None{},
      Key.side_bits.nil(Cur.bits(c), Equal.trans(Bool, List.is_empty(&2, Bool, Cur.bits(c)), Cur.done(c), True{}, Equal.sym(Bool, Cur.done(c), List.is_empty(&2, Bool, Cur.bits(c)), Cur.done_bits(c)), h))
    ),
    h => Equal.trans(
      Maybe<&2, Bool>,
      Some{Cur.bit(c)},
      Some{Shared.List.head_or(Bool, Cur.bits(c), False{})},
      Bits.head(Cur.bits(c)),
      Equal.cong(Bool, Maybe<&2, Bool>, b => Some{b}, Cur.bit(c), Shared.List.head_or(Bool, Cur.bits(c), False{}), Cur.bit_bits(c)),
      Key.side_bits.some(Cur.bits(c), Equal.trans(Bool, List.is_empty(&2, Bool, Cur.bits(c)), Cur.done(c), False{}, Equal.sym(Bool, Cur.done(c), List.is_empty(&2, Bool, Cur.bits(c)), Cur.done_bits(c)), h))
    )
  )

# the side of a key at pos is its bit there
law Key.side_bits:
  for k: List<&2, U32>
  for pos: Nat
  {Key.side(k, pos) == Bits.at(Key.bits(k), pos): Maybe<&2, Bool>}

# the side of a key at pos is its bit there, with pos used more than once
def Key.side_bits.at(+k: List<&2, U32>, +pos: Nat) -> {
  Key.side(k, pos) == Bits.at(Key.bits(k), pos): Maybe<&2, Bool>
}:
  Equal.trans(
    Maybe<&2, Bool>,
    Key.side(k, pos),
    Bits.head(Cur.bits(Key.at(k, pos))),
    Bits.at(Key.bits(k), pos),
    Key.side_bits.cur(Key.at(k, pos)),
    Equal.sym(
      Maybe<&2, Bool>,
      Bits.at(Key.bits(k), pos),
      Bits.head(Cur.bits(Key.at(k, pos))),
      Equal.cong(
        List<&2, Bool>,
        Maybe<&2, Bool>,
        bs => Bits.head(bs),
        List.drop(&2, Bool, Key.bits(k), pos),
        Cur.bits(Key.at(k, pos)),
        Equal.sym(List<&2, Bool>, Cur.bits(Key.at(k, pos)), List.drop(&2, Bool, Key.bits(k), pos), Cur.skip_bits(pos, Cur.of(k)))
      )
    )
  )

def Key.side_bits(k, pos):
  Key.side_bits.at(k, pos)

# Laws of maps
# ------------
# The laws of a map are stated by the clear read (Crit.lookup), for maps that
# the writes build (Crit.wf): each write is the same write on the clear read,
# a read is the clear read, and two maps that read the same are equal.

# Key.is_eq is True only for equal keys
def Key.is_eq_sound(+a: List<&2, U32>, +b: List<&2, U32>) -> {Key.is_eq(a, b) == True{}: Bool} -> {a == b: List<&2, U32>}:
  h => Shared.List.is_eq_sound(~U32, ~U32.is_eq, ~Shared.U32.laws(), a, b)((
      %Key.is_eq_list(a, b): {_ == True{}: Bool}
      h))

# Key.is_eq is True for a key and itself
def Key.is_eq_refl(+a: List<&2, U32>) -> {Key.is_eq(a, a) == True{}: Bool}:
  %Equal.sym(Bool, Key.is_eq(a, a), Shared.List.is_eq(~U32, ~U32.is_eq, a, a), Key.is_eq_list(a, a)): {_ == True{}: Bool}
  Shared.List.is_eq_refl(~U32, ~U32.is_eq, ~Shared.U32.laws(), a)

# the laws of Key.is_eq
def Key.laws() -> Shared.Eq.Laws(List<&2, U32>, Key.is_eq):
  (x => Key.is_eq_refl(x), x => y => Key.is_eq_sound(x, y))

# a choice that does not hold is nothing
def Crit.when_none(-V: Data, b: Bool, -k: Unit -> Maybe<&2, V>) -> ({b == True{}: Bool} -> Empty) -> {
  Shared.Maybe.when(V, b, k) == None{}: Maybe<&2, V>
}:
  match b:
    case True{}:
      h => Empty.absurd({k(Unit{}) == None{}: Maybe<&2, V>}, h({==}))
    case False{}:
      h => {==}

# p of g passes a key and fails a key: they are not the same
def Crit.pass_eq(
  ~G: Data,
  ~p: G -> List<&2, U32> -> Bool,
  +g: G,
  +a: List<&2, U32>,
  +b: List<&2, U32>,
  e: {a == b: List<&2, U32>},
  h: {p(g)(a) == True{}: Bool},
  n: {p(g)(b) == False{}: Bool}
) -> Empty:
  Shared.Bool.false_ne_true(
    Equal.trans(
      Bool,
      False{},
      p(g)(a),
      True{},
      Equal.trans(
        Bool,
        False{},
        p(g)(b),
        p(g)(a),
        Equal.sym(Bool, p(g)(b), False{}, n),
        Equal.sym(Bool, p(g)(a), p(g)(b), Equal.cong(List<&2, U32>, Bool, x => p(g)(x), a, b, e))
      ),
      h
    )
  )

# three choices of which none holds are nothing
def Crit.or3_none(-V: Data, a: Maybe<&2, V>, b: Maybe<&2, V>, c: Maybe<&2, V>) -> {a == None{}: Maybe<&2, V>} -> {
  b == None{}: Maybe<&2, V>
} -> {c == None{}: Maybe<&2, V>} -> {Maybe.or(&2, V, a, Maybe.or(&2, V, b, c)) == None{}: Maybe<&2, V>}:
  match a b:
    case None{} None{}:
      ha => hb => hc => hc
    case None{} Some{y}:
      ha => hb => hc => Empty.absurd({Some{y} == None{}: Maybe<&2, V>}, Shared.Maybe.none_ne_some(V, y, Equal.sym(Maybe<&2, V>, Some{y}, None{}, hb)))
    case Some{x} y:
      ha => hb => hc => Empty.absurd({Some{x} == None{}: Maybe<&2, V>}, Shared.Maybe.none_ne_some(V, x, Equal.sym(Maybe<&2, V>, Some{x}, None{}, ha)))

# of three choices, when the first two are nothing, the third
def Crit.or_third(-V: Data, a: Maybe<&2, V>, b: Maybe<&2, V>, c: Maybe<&2, V>) -> {a == None{}: Maybe<&2, V>} -> {
  b == None{}: Maybe<&2, V>
} -> {Maybe.or(&2, V, a, Maybe.or(&2, V, b, c)) == c: Maybe<&2, V>}:
  match a b:
    case None{} None{}:
      ha => hb => {==}
    case None{} Some{y}:
      ha => hb => Empty.absurd({Some{y} == c: Maybe<&2, V>}, Shared.Maybe.none_ne_some(V, y, Equal.sym(Maybe<&2, V>, Some{y}, None{}, hb)))
    case Some{x} y:
      ha => hb => Empty.absurd({Some{x} == c: Maybe<&2, V>}, Shared.Maybe.none_ne_some(V, x, Equal.sym(Maybe<&2, V>, Some{x}, None{}, ha)))

# of three choices, when the first and the third are nothing, the second
def Crit.or_second(-V: Data, a: Maybe<&2, V>, b: Maybe<&2, V>, c: Maybe<&2, V>) -> {a == None{}: Maybe<&2, V>} -> {
  c == None{}: Maybe<&2, V>
} -> {Maybe.or(&2, V, a, Maybe.or(&2, V, b, c)) == b: Maybe<&2, V>}:
  match a b:
    case None{} None{}:
      ha => hc => hc
    case None{} Some{y}:
      ha => hc => {==}
    case Some{x} y:
      ha => hc => Empty.absurd({Some{x} == y: Maybe<&2, V>}, Shared.Maybe.none_ne_some(V, x, Equal.sym(Maybe<&2, V>, Some{x}, None{}, ha)))

# of three choices, when the last two are nothing, the first
def Crit.or_first(-V: Data, a: Maybe<&2, V>, b: Maybe<&2, V>, c: Maybe<&2, V>) -> {b == None{}: Maybe<&2, V>} -> {
  c == None{}: Maybe<&2, V>
} -> {Maybe.or(&2, V, a, Maybe.or(&2, V, b, c)) == a: Maybe<&2, V>}:
  match a:
    case Some{x}:
      hb => hc => {==}
    case None{}:
      hb => hc => Crit.or3_none(V, None{}, b, c)({==})(hb)(hc)

# the end of a fork whose rep passes, read at a key that fails, is nothing
def Crit.lookup_all.ended(
  ~V: Data,
  ~G: Data,
  ~p: G -> List<&2, U32> -> Bool,
  +rep: List<&2, U32>,
  e: Maybe<&2, V>,
  +g: G,
  +q: List<&2, U32>
) -> {Bool.or(Maybe.is_none(&2, V, e), p(g)(rep)) == True{}: Bool} -> {p(g)(q) == False{}: Bool} -> {
  Crit.ended(V, rep, e, q) == None{}: Maybe<&2, V>
}:
  match e:
    case None{}:
      h => n => {==}
    case Some{v}:
      h => n => Crit.when_none(V, Key.is_eq(rep, q), u => Some{v})(eq => Crit.pass_eq(~G, ~p, g, rep, q, Key.is_eq_sound(rep, q)(eq), h, n))

# a map whose keys all pass p holds no key that fails p
def Crit.lookup_all(~V: Data, ~G: Data, ~p: G -> List<&2, U32> -> Bool, m: Crit<V>, +g: G, +q: List<&2, U32>) -> {
  Crit.all(~V, ~G, ~p, m, g) == True{}: Bool
} -> {p(g)(q) == False{}: Bool} -> {Crit.lookup(V, m, q) == None{}: Maybe<&2, V>}:
  match m:
    case Crit.Tip{}:
      h => n => {==}
    case Crit.Leaf{+k, v}:
      +h => +n => Crit.when_none(V, Key.is_eq(k, q), u => Some{v})(eq => Crit.pass_eq(~G, ~p, g, k, q, Key.is_eq_sound(k, q)(eq), h, n))
    case Crit.Fork{+rep, pos, +e, +z, +o}:
      +h => +n =>
        +hit = Bool.or(Maybe.is_none(&2, V, e), p(g)(rep))
        +hr = Shared.List.all.if_rest(hit, u => List.all.if(u2 => Crit.all(~V, ~G, ~p, o, g), Crit.all(~V, ~G, ~p, z, g)))(h)
        Crit.or3_none(V, Crit.ended(V, rep, e, q), Crit.lookup(V, z, q), Crit.lookup(V, o, q))(
          Crit.lookup_all.ended(~V, ~G, ~p, rep, e, g, q)(
            Shared.List.all.if_hit(hit, u => List.all.if(u2 => Crit.all(~V, ~G, ~p, o, g), Crit.all(~V, ~G, ~p, z, g)))(h)
          )(n)
        )(
          Crit.lookup_all(~V, ~G, ~p, z, g, q)(
            Shared.List.all.if_hit(Crit.all(~V, ~G, ~p, z, g), u2 => Crit.all(~V, ~G, ~p, o, g))(hr)
          )(n)
        )(
          Crit.lookup_all(~V, ~G, ~p, o, g, q)(
            Shared.List.all.if_rest(Crit.all(~V, ~G, ~p, z, g), u2 => Crit.all(~V, ~G, ~p, o, g))(hr)
          )(n)
        )

# an "all" whose rest fails fails
def Crit.all_if_false(a: Bool, x: Bool) -> {x == False{}: Bool} -> {List.all.if(u => x, a) == False{}: Bool}:
  match a:
    case False{}:
      h => {==}
    case True{}:
      h => h

# a key whose side at pos is not b is not on the side b of a fork at pos
def Place.has_not(
  +rep: List<&2, U32>,
  +pos: Nat,
  +b: Bool,
  +k: List<&2, U32>,
  s: Maybe<&2, Bool>,
  hs: {Key.side(k, pos) == s: Maybe<&2, Bool>},
  hn: {Shared.Maybe.is_eq(~Bool, ~Shared.Bool.is_eq, s, Some{b}) == False{}: Bool}
) -> {Place.has(Place{rep, pos, b}, k) == False{}: Bool}:
  Crit.all_if_false(
    Key.agree(k, rep, pos),
    Shared.Maybe.is_eq(~Bool, ~Shared.Bool.is_eq, Key.side(k, pos), Some{b})
  )((
    %Equal.sym(Maybe<&2, Bool>, Key.side(k, pos), s, hs): {
      Shared.Maybe.is_eq(~Bool, ~Shared.Bool.is_eq, _, Some{b}) == False{}: Bool
    }
    hn
  ))

# a well formed fork: its bit is at lo or after
def Crit.wf.le(~V: Data, +rep: List<&2, U32>, +pos: Nat, +e: Maybe<&2, V>, +z: Crit<V>, +o: Crit<V>, +lo: Nat) -> {
  Crit.wf(~V, Crit.Fork{rep, pos, e, z, o}, lo) == True{}: Bool
} -> {Nat.is_le(lo, pos) == True{}: Bool}:
  h => Shared.List.all.if_hit(Nat.is_le(lo, pos), u => List.all.if(u => List.all.if(u => List.all.if(u => List.all.if(u => List.all.if(u => Crit.wf(~V, o, 1n+pos), Crit.wf(~V, z, 1n+pos)), Crit.all(~V, ~Place, ~Place.has, o, Place{rep, pos, True{}})), Crit.all(~V, ~Place, ~Place.has, z, Place{rep, pos, False{}})), Crit.rep_ok(V, rep, pos, e, z)), Crit.shape(V, e, z, o)))(h)

# a well formed fork: it holds two entries at least
def Crit.wf.shape(~V: Data, +rep: List<&2, U32>, +pos: Nat, +e: Maybe<&2, V>, +z: Crit<V>, +o: Crit<V>, +lo: Nat) -> {
  Crit.wf(~V, Crit.Fork{rep, pos, e, z, o}, lo) == True{}: Bool
} -> {Crit.shape(V, e, z, o) == True{}: Bool}:
  h => Shared.List.all.if_hit(Crit.shape(V, e, z, o), u => List.all.if(u => List.all.if(u => List.all.if(u => List.all.if(u => Crit.wf(~V, o, 1n+pos), Crit.wf(~V, z, 1n+pos)), Crit.all(~V, ~Place, ~Place.has, o, Place{rep, pos, True{}})), Crit.all(~V, ~Place, ~Place.has, z, Place{rep, pos, False{}})), Crit.rep_ok(V, rep, pos, e, z)))(Shared.List.all.if_rest(Nat.is_le(lo, pos), u => List.all.if(u => List.all.if(u => List.all.if(u => List.all.if(u => List.all.if(u => Crit.wf(~V, o, 1n+pos), Crit.wf(~V, z, 1n+pos)), Crit.all(~V, ~Place, ~Place.has, o, Place{rep, pos, True{}})), Crit.all(~V, ~Place, ~Place.has, z, Place{rep, pos, False{}})), Crit.rep_ok(V, rep, pos, e, z)), Crit.shape(V, e, z, o)))(h))

# a well formed fork: its rep is its first key
def Crit.wf.rep_ok(~V: Data, +rep: List<&2, U32>, +pos: Nat, +e: Maybe<&2, V>, +z: Crit<V>, +o: Crit<V>, +lo: Nat) -> {
  Crit.wf(~V, Crit.Fork{rep, pos, e, z, o}, lo) == True{}: Bool
} -> {Crit.rep_ok(V, rep, pos, e, z) == True{}: Bool}:
  h => Shared.List.all.if_hit(Crit.rep_ok(V, rep, pos, e, z), u => List.all.if(u => List.all.if(u => List.all.if(u => Crit.wf(~V, o, 1n+pos), Crit.wf(~V, z, 1n+pos)), Crit.all(~V, ~Place, ~Place.has, o, Place{rep, pos, True{}})), Crit.all(~V, ~Place, ~Place.has, z, Place{rep, pos, False{}})))(Shared.List.all.if_rest(Crit.shape(V, e, z, o), u => List.all.if(u => List.all.if(u => List.all.if(u => List.all.if(u => Crit.wf(~V, o, 1n+pos), Crit.wf(~V, z, 1n+pos)), Crit.all(~V, ~Place, ~Place.has, o, Place{rep, pos, True{}})), Crit.all(~V, ~Place, ~Place.has, z, Place{rep, pos, False{}})), Crit.rep_ok(V, rep, pos, e, z)))(Shared.List.all.if_rest(Nat.is_le(lo, pos), u => List.all.if(u => List.all.if(u => List.all.if(u => List.all.if(u => List.all.if(u => Crit.wf(~V, o, 1n+pos), Crit.wf(~V, z, 1n+pos)), Crit.all(~V, ~Place, ~Place.has, o, Place{rep, pos, True{}})), Crit.all(~V, ~Place, ~Place.has, z, Place{rep, pos, False{}})), Crit.rep_ok(V, rep, pos, e, z)), Crit.shape(V, e, z, o)))(h)))

# a well formed fork: the keys of its zero side are on that side
def Crit.wf.all_z(~V: Data, +rep: List<&2, U32>, +pos: Nat, +e: Maybe<&2, V>, +z: Crit<V>, +o: Crit<V>, +lo: Nat) -> {
  Crit.wf(~V, Crit.Fork{rep, pos, e, z, o}, lo) == True{}: Bool
} -> {Crit.all(~V, ~Place, ~Place.has, z, Place{rep, pos, False{}}) == True{}: Bool}:
  h => Shared.List.all.if_hit(Crit.all(~V, ~Place, ~Place.has, z, Place{rep, pos, False{}}), u => List.all.if(u => List.all.if(u => Crit.wf(~V, o, 1n+pos), Crit.wf(~V, z, 1n+pos)), Crit.all(~V, ~Place, ~Place.has, o, Place{rep, pos, True{}})))(Shared.List.all.if_rest(Crit.rep_ok(V, rep, pos, e, z), u => List.all.if(u => List.all.if(u => List.all.if(u => Crit.wf(~V, o, 1n+pos), Crit.wf(~V, z, 1n+pos)), Crit.all(~V, ~Place, ~Place.has, o, Place{rep, pos, True{}})), Crit.all(~V, ~Place, ~Place.has, z, Place{rep, pos, False{}})))(Shared.List.all.if_rest(Crit.shape(V, e, z, o), u => List.all.if(u => List.all.if(u => List.all.if(u => List.all.if(u => Crit.wf(~V, o, 1n+pos), Crit.wf(~V, z, 1n+pos)), Crit.all(~V, ~Place, ~Place.has, o, Place{rep, pos, True{}})), Crit.all(~V, ~Place, ~Place.has, z, Place{rep, pos, False{}})), Crit.rep_ok(V, rep, pos, e, z)))(Shared.List.all.if_rest(Nat.is_le(lo, pos), u => List.all.if(u => List.all.if(u => List.all.if(u => List.all.if(u => List.all.if(u => Crit.wf(~V, o, 1n+pos), Crit.wf(~V, z, 1n+pos)), Crit.all(~V, ~Place, ~Place.has, o, Place{rep, pos, True{}})), Crit.all(~V, ~Place, ~Place.has, z, Place{rep, pos, False{}})), Crit.rep_ok(V, rep, pos, e, z)), Crit.shape(V, e, z, o)))(h))))

# a well formed fork: the keys of its one side are on that side
def Crit.wf.all_o(~V: Data, +rep: List<&2, U32>, +pos: Nat, +e: Maybe<&2, V>, +z: Crit<V>, +o: Crit<V>, +lo: Nat) -> {
  Crit.wf(~V, Crit.Fork{rep, pos, e, z, o}, lo) == True{}: Bool
} -> {Crit.all(~V, ~Place, ~Place.has, o, Place{rep, pos, True{}}) == True{}: Bool}:
  h => Shared.List.all.if_hit(Crit.all(~V, ~Place, ~Place.has, o, Place{rep, pos, True{}}), u => List.all.if(u => Crit.wf(~V, o, 1n+pos), Crit.wf(~V, z, 1n+pos)))(Shared.List.all.if_rest(Crit.all(~V, ~Place, ~Place.has, z, Place{rep, pos, False{}}), u => List.all.if(u => List.all.if(u => Crit.wf(~V, o, 1n+pos), Crit.wf(~V, z, 1n+pos)), Crit.all(~V, ~Place, ~Place.has, o, Place{rep, pos, True{}})))(Shared.List.all.if_rest(Crit.rep_ok(V, rep, pos, e, z), u => List.all.if(u => List.all.if(u => List.all.if(u => Crit.wf(~V, o, 1n+pos), Crit.wf(~V, z, 1n+pos)), Crit.all(~V, ~Place, ~Place.has, o, Place{rep, pos, True{}})), Crit.all(~V, ~Place, ~Place.has, z, Place{rep, pos, False{}})))(Shared.List.all.if_rest(Crit.shape(V, e, z, o), u => List.all.if(u => List.all.if(u => List.all.if(u => List.all.if(u => Crit.wf(~V, o, 1n+pos), Crit.wf(~V, z, 1n+pos)), Crit.all(~V, ~Place, ~Place.has, o, Place{rep, pos, True{}})), Crit.all(~V, ~Place, ~Place.has, z, Place{rep, pos, False{}})), Crit.rep_ok(V, rep, pos, e, z)))(Shared.List.all.if_rest(Nat.is_le(lo, pos), u => List.all.if(u => List.all.if(u => List.all.if(u => List.all.if(u => List.all.if(u => Crit.wf(~V, o, 1n+pos), Crit.wf(~V, z, 1n+pos)), Crit.all(~V, ~Place, ~Place.has, o, Place{rep, pos, True{}})), Crit.all(~V, ~Place, ~Place.has, z, Place{rep, pos, False{}})), Crit.rep_ok(V, rep, pos, e, z)), Crit.shape(V, e, z, o)))(h)))))

# a well formed fork: its zero side is well formed
def Crit.wf.wf_z(~V: Data, +rep: List<&2, U32>, +pos: Nat, +e: Maybe<&2, V>, +z: Crit<V>, +o: Crit<V>, +lo: Nat) -> {
  Crit.wf(~V, Crit.Fork{rep, pos, e, z, o}, lo) == True{}: Bool
} -> {Crit.wf(~V, z, 1n+pos) == True{}: Bool}:
  h => Shared.List.all.if_hit(Crit.wf(~V, z, 1n+pos), u => Crit.wf(~V, o, 1n+pos))(Shared.List.all.if_rest(Crit.all(~V, ~Place, ~Place.has, o, Place{rep, pos, True{}}), u => List.all.if(u => Crit.wf(~V, o, 1n+pos), Crit.wf(~V, z, 1n+pos)))(Shared.List.all.if_rest(Crit.all(~V, ~Place, ~Place.has, z, Place{rep, pos, False{}}), u => List.all.if(u => List.all.if(u => Crit.wf(~V, o, 1n+pos), Crit.wf(~V, z, 1n+pos)), Crit.all(~V, ~Place, ~Place.has, o, Place{rep, pos, True{}})))(Shared.List.all.if_rest(Crit.rep_ok(V, rep, pos, e, z), u => List.all.if(u => List.all.if(u => List.all.if(u => Crit.wf(~V, o, 1n+pos), Crit.wf(~V, z, 1n+pos)), Crit.all(~V, ~Place, ~Place.has, o, Place{rep, pos, True{}})), Crit.all(~V, ~Place, ~Place.has, z, Place{rep, pos, False{}})))(Shared.List.all.if_rest(Crit.shape(V, e, z, o), u => List.all.if(u => List.all.if(u => List.all.if(u => List.all.if(u => Crit.wf(~V, o, 1n+pos), Crit.wf(~V, z, 1n+pos)), Crit.all(~V, ~Place, ~Place.has, o, Place{rep, pos, True{}})), Crit.all(~V, ~Place, ~Place.has, z, Place{rep, pos, False{}})), Crit.rep_ok(V, rep, pos, e, z)))(Shared.List.all.if_rest(Nat.is_le(lo, pos), u => List.all.if(u => List.all.if(u => List.all.if(u => List.all.if(u => List.all.if(u => Crit.wf(~V, o, 1n+pos), Crit.wf(~V, z, 1n+pos)), Crit.all(~V, ~Place, ~Place.has, o, Place{rep, pos, True{}})), Crit.all(~V, ~Place, ~Place.has, z, Place{rep, pos, False{}})), Crit.rep_ok(V, rep, pos, e, z)), Crit.shape(V, e, z, o)))(h))))))

# a well formed fork: its one side is well formed
def Crit.wf.wf_o(~V: Data, +rep: List<&2, U32>, +pos: Nat, +e: Maybe<&2, V>, +z: Crit<V>, +o: Crit<V>, +lo: Nat) -> {
  Crit.wf(~V, Crit.Fork{rep, pos, e, z, o}, lo) == True{}: Bool
} -> {Crit.wf(~V, o, 1n+pos) == True{}: Bool}:
  h => Shared.List.all.if_rest(Crit.wf(~V, z, 1n+pos), u => Crit.wf(~V, o, 1n+pos))(Shared.List.all.if_rest(Crit.all(~V, ~Place, ~Place.has, o, Place{rep, pos, True{}}), u => List.all.if(u => Crit.wf(~V, o, 1n+pos), Crit.wf(~V, z, 1n+pos)))(Shared.List.all.if_rest(Crit.all(~V, ~Place, ~Place.has, z, Place{rep, pos, False{}}), u => List.all.if(u => List.all.if(u => Crit.wf(~V, o, 1n+pos), Crit.wf(~V, z, 1n+pos)), Crit.all(~V, ~Place, ~Place.has, o, Place{rep, pos, True{}})))(Shared.List.all.if_rest(Crit.rep_ok(V, rep, pos, e, z), u => List.all.if(u => List.all.if(u => List.all.if(u => Crit.wf(~V, o, 1n+pos), Crit.wf(~V, z, 1n+pos)), Crit.all(~V, ~Place, ~Place.has, o, Place{rep, pos, True{}})), Crit.all(~V, ~Place, ~Place.has, z, Place{rep, pos, False{}})))(Shared.List.all.if_rest(Crit.shape(V, e, z, o), u => List.all.if(u => List.all.if(u => List.all.if(u => List.all.if(u => Crit.wf(~V, o, 1n+pos), Crit.wf(~V, z, 1n+pos)), Crit.all(~V, ~Place, ~Place.has, o, Place{rep, pos, True{}})), Crit.all(~V, ~Place, ~Place.has, z, Place{rep, pos, False{}})), Crit.rep_ok(V, rep, pos, e, z)))(Shared.List.all.if_rest(Nat.is_le(lo, pos), u => List.all.if(u => List.all.if(u => List.all.if(u => List.all.if(u => List.all.if(u => Crit.wf(~V, o, 1n+pos), Crit.wf(~V, z, 1n+pos)), Crit.all(~V, ~Place, ~Place.has, o, Place{rep, pos, True{}})), Crit.all(~V, ~Place, ~Place.has, z, Place{rep, pos, False{}})), Crit.rep_ok(V, rep, pos, e, z)), Crit.shape(V, e, z, o)))(h))))))

# a fork is well formed when each of its parts is
def Crit.wf.intro(~V: Data, +rep: List<&2, U32>, +pos: Nat, +e: Maybe<&2, V>, +z: Crit<V>, +o: Crit<V>, +lo: Nat) -> {Nat.is_le(lo, pos) == True{}: Bool} -> {Crit.shape(V, e, z, o) == True{}: Bool} -> {Crit.rep_ok(V, rep, pos, e, z) == True{}: Bool} -> {Crit.all(~V, ~Place, ~Place.has, z, Place{rep, pos, False{}}) == True{}: Bool} -> {Crit.all(~V, ~Place, ~Place.has, o, Place{rep, pos, True{}}) == True{}: Bool} -> {Crit.wf(~V, z, 1n+pos) == True{}: Bool} -> {Crit.wf(~V, o, 1n+pos) == True{}: Bool} -> {Crit.wf(~V, Crit.Fork{rep, pos, e, z, o}, lo) == True{}: Bool}:
  le => sh => ro => az => ao => wz => wo => Shared.List.all.if_both(Nat.is_le(lo, pos), u => List.all.if(u => List.all.if(u => List.all.if(u => List.all.if(u => List.all.if(u => Crit.wf(~V, o, 1n+pos), Crit.wf(~V, z, 1n+pos)), Crit.all(~V, ~Place, ~Place.has, o, Place{rep, pos, True{}})), Crit.all(~V, ~Place, ~Place.has, z, Place{rep, pos, False{}})), Crit.rep_ok(V, rep, pos, e, z)), Crit.shape(V, e, z, o)))(le)(Shared.List.all.if_both(Crit.shape(V, e, z, o), u => List.all.if(u => List.all.if(u => List.all.if(u => List.all.if(u => Crit.wf(~V, o, 1n+pos), Crit.wf(~V, z, 1n+pos)), Crit.all(~V, ~Place, ~Place.has, o, Place{rep, pos, True{}})), Crit.all(~V, ~Place, ~Place.has, z, Place{rep, pos, False{}})), Crit.rep_ok(V, rep, pos, e, z)))(sh)(Shared.List.all.if_both(Crit.rep_ok(V, rep, pos, e, z), u => List.all.if(u => List.all.if(u => List.all.if(u => Crit.wf(~V, o, 1n+pos), Crit.wf(~V, z, 1n+pos)), Crit.all(~V, ~Place, ~Place.has, o, Place{rep, pos, True{}})), Crit.all(~V, ~Place, ~Place.has, z, Place{rep, pos, False{}})))(ro)(Shared.List.all.if_both(Crit.all(~V, ~Place, ~Place.has, z, Place{rep, pos, False{}}), u => List.all.if(u => List.all.if(u => Crit.wf(~V, o, 1n+pos), Crit.wf(~V, z, 1n+pos)), Crit.all(~V, ~Place, ~Place.has, o, Place{rep, pos, True{}})))(az)(Shared.List.all.if_both(Crit.all(~V, ~Place, ~Place.has, o, Place{rep, pos, True{}}), u => List.all.if(u => Crit.wf(~V, o, 1n+pos), Crit.wf(~V, z, 1n+pos)))(ao)(Shared.List.all.if_both(Crit.wf(~V, z, 1n+pos), u => Crit.wf(~V, o, 1n+pos))(wz)(wo))))))

# a map well formed below a fork at a bit before a is well formed below one
# before any b up to a
def Crit.wf_mono(~V: Data, m: Crit<V>, +a: Nat, +b: Nat) -> {Crit.wf(~V, m, a) == True{}: Bool} -> {Nat.is_le(b, a) == True{}: Bool} -> {
  Crit.wf(~V, m, b) == True{}: Bool
}:
  match m:
    case Crit.Tip{}:
      h => l => {==}
    case Crit.Leaf{k, v}:
      h => l => {==}
    case Crit.Fork{+rep, +pos, +e, +z, +o}:
      +h => l => Shared.List.all.if_both(Nat.is_le(b, pos), u => List.all.if(u => List.all.if(u => List.all.if(u => List.all.if(u => List.all.if(u => Crit.wf(~V, o, 1n+pos), Crit.wf(~V, z, 1n+pos)), Crit.all(~V, ~Place, ~Place.has, o, Place{rep, pos, True{}})), Crit.all(~V, ~Place, ~Place.has, z, Place{rep, pos, False{}})), Crit.rep_ok(V, rep, pos, e, z)), Crit.shape(V, e, z, o)))(Shared.Nat.le_trans(b, a, pos)(l)(Crit.wf.le(~V, rep, pos, e, z, o, a)(h)))(
        Shared.List.all.if_rest(Nat.is_le(a, pos), u => List.all.if(u => List.all.if(u => List.all.if(u => List.all.if(u => List.all.if(u => Crit.wf(~V, o, 1n+pos), Crit.wf(~V, z, 1n+pos)), Crit.all(~V, ~Place, ~Place.has, o, Place{rep, pos, True{}})), Crit.all(~V, ~Place, ~Place.has, z, Place{rep, pos, False{}})), Crit.rep_ok(V, rep, pos, e, z)), Crit.shape(V, e, z, o)))(h)
      )

# dropping all of a list leaves nothing
def Crit.drop_length(xs: List<&2, Bool>) -> {List.drop(&2, Bool, xs, List.length(&2, Bool, xs)) == []: List<&2, Bool>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      Crit.drop_length(t)

# dropping a, then b less a, is dropping b
def Crit.drop_drop(xs: List<&2, Bool>, a: Nat, +b: Nat) -> {Nat.is_le(a, b) == True{}: Bool} -> {
  List.drop(&2, Bool, List.drop(&2, Bool, xs, a), Nat.sub(b, a)) == List.drop(&2, Bool, xs, b): List<&2, Bool>
}:
  match xs a:
    case Nil{} a1:
      h => {==}
    case Con{+x, +t} 0n:
      h =>
        %Equal.sym(Nat, Nat.sub(b, 0n), b, Shared.Nat.sub_zero(b)): {
          List.drop(&2, Bool, x <> t, _) == List.drop(&2, Bool, x <> t, b): List<&2, Bool>
        }
        {==}
    case Con{x, t} 1n+p:
      match b:
        case 0n:
          h => Empty.absurd({List.drop(&2, Bool, List.drop(&2, Bool, t, p), 0n) == List.drop(&2, Bool, x <> t, 0n): List<&2, Bool>}, Shared.Bool.false_ne_true(h))
        case 1n+q:
          Crit.drop_drop(t, p, q)

# dropping p, then one, is dropping 1 + p
def Crit.drop_drop_one(xs: List<&2, Bool>, p: Nat) -> {
  List.drop(&2, Bool, List.drop(&2, Bool, xs, p), 1n) == List.drop(&2, Bool, xs, 1n+p): List<&2, Bool>
}:
  match xs p:
    case Nil{} p1:
      {==}
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+q:
      Crit.drop_drop_one(t, q)

# a test that is not True is False
def Crit.false_of(b: Bool) -> ({b == True{}: Bool} -> Empty) -> {b == False{}: Bool}:
  match b:
    case True{}:
      h => Empty.absurd({True{} == False{}: Bool}, h({==}))
    case False{}:
      h => {==}

# a choice whose test is False is nothing
def Crit.when_false(-V: Data, +b: Bool, -k: Unit -> Maybe<&2, V>) -> {b == False{}: Bool} -> {
  Shared.Maybe.when(V, b, k) == None{}: Maybe<&2, V>
}:
  h => Crit.when_none(V, b, k)(t => Shared.Bool.false_ne_true(Equal.trans(Bool, False{}, b, True{}, Equal.sym(Bool, b, False{}, h), t)))

# keys that differ differ either way round
def Key.ne_sym(+q: List<&2, U32>, +k: List<&2, U32>) -> {Key.is_eq(q, k) == False{}: Bool} -> {Key.is_eq(k, q) == False{}: Bool}:
  h => Crit.false_of(Key.is_eq(k, q))(
    t => Shared.Bool.false_ne_true(
      Equal.trans(
        Bool,
        False{},
        Key.is_eq(q, k),
        True{},
        Equal.sym(Bool, Key.is_eq(q, k), False{}, h),
        (
          %Equal.sym(List<&2, U32>, k, q, Key.is_eq_sound(k, q)(t)): {Key.is_eq(q, _) == True{}: Bool}
          Key.is_eq_refl(q)
        )
      )
    )
  )

# a key that is k differs from each key that differs from k
def Key.ne_of_eq(+a: List<&2, U32>, +k: List<&2, U32>, +q: List<&2, U32>) -> {Key.is_eq(a, k) == True{}: Bool} -> {
  Key.is_eq(q, k) == False{}: Bool
} -> {Key.is_eq(a, q) == False{}: Bool}:
  t => h =>
    %Equal.sym(List<&2, U32>, a, k, Key.is_eq_sound(a, k)(t)): {Key.is_eq(_, q) == False{}: Bool}
    Key.ne_sym(q, k)(h)

# the end of a fork, read at a key that is not its rep, is nothing
def Crit.ended_ne(-V: Data, +rep: List<&2, U32>, e: Maybe<&2, V>, +q: List<&2, U32>) -> {Key.is_eq(rep, q) == False{}: Bool} -> {
  Crit.ended(V, rep, e, q) == None{}: Maybe<&2, V>
}:
  match e:
    case None{}:
      h => {==}
    case Some{v}:
      h => Crit.when_false(V, Key.is_eq(rep, q), u => Some{v})(h)

# what holds when the test holds, and when it does not, holds of the pick
def Crit.pick_cases(-A: Data, c: Bool, -a: A, -b: A, -x: A) -> ({c == True{}: Bool} -> {a == x: A}) -> ({c == False{}: Bool} -> {
  b == x: A
}) -> {Bool.pick(A, c, a, b) == x: A}:
  match c:
    case True{}:
      ht => hf => ht({==})
    case False{}:
      ht => hf => hf({==})

# a key that goes on past pos is not a key of pos bits
def Crit.end_not(
  +rep: List<&2, U32>,
  +pos: Nat,
  +k: List<&2, U32>,
  +x: Bool,
  +r: List<&2, Bool>,
  hl: {List.length(&2, Bool, Key.bits(rep)) == pos: Nat},
  hd: {List.drop(&2, Bool, Key.bits(k), pos) == x <> r: List<&2, Bool>},
  eq: {rep == k: List<&2, U32>}
) -> Empty:
  Shared.Bool.false_ne_true(
    Equal.cong(
      List<&2, Bool>,
      Bool,
      l => List.is_empty(&2, Bool, l),
      x <> r,
      [],
      Equal.trans(
        List<&2, Bool>,
        x <> r,
        List.drop(&2, Bool, Key.bits(k), pos),
        [],
        Equal.sym(List<&2, Bool>, List.drop(&2, Bool, Key.bits(k), pos), x <> r, hd),
        (
          %eq: {List.drop(&2, Bool, Key.bits(_), pos) == []: List<&2, Bool>}
          %hl: {List.drop(&2, Bool, Key.bits(rep), _) == []: List<&2, Bool>}
          Crit.drop_length(Key.bits(rep))
        )
      )
    )
  )

# the end of a fork, read at a key that goes on past its bit, is nothing
def Crit.ended_past(
  -V: Data,
  +rep: List<&2, U32>,
  +pos: Nat,
  e: Maybe<&2, V>,
  -z: Crit<V>,
  +k: List<&2, U32>,
  +x: Bool,
  +r: List<&2, Bool>
) -> {Crit.rep_ok(V, rep, pos, e, z) == True{}: Bool} -> {List.drop(&2, Bool, Key.bits(k), pos) == x <> r: List<&2, Bool>} -> {
  Crit.ended(V, rep, e, k) == None{}: Maybe<&2, V>
}:
  match e:
    case None{}:
      hr => hd => {==}
    case Some{v}:
      +hr => +hd => Crit.when_none(V, Key.is_eq(rep, k), u => Some{v})(
        eq => Crit.end_not(
          rep,
          pos,
          k,
          x,
          r,
          Shared.Nat.is_eq_sound(List.length(&2, Bool, Key.bits(rep)), pos)(hr),
          hd,
          Key.is_eq_sound(rep, k)(eq)
        )
      )

# the side of a key at pos is the head of its bits from pos
def Crit.side_drop(+k: List<&2, U32>, +pos: Nat, +d: List<&2, Bool>) -> {List.drop(&2, Bool, Key.bits(k), pos) == d: List<&2, Bool>} -> {
  Key.side(k, pos) == Bits.head(d): Maybe<&2, Bool>
}:
  hd => Equal.trans(
    Maybe<&2, Bool>,
    Key.side(k, pos),
    Bits.at(Key.bits(k), pos),
    Bits.head(d),
    Key.side_bits(k, pos),
    Equal.cong(List<&2, Bool>, Maybe<&2, Bool>, l => Bits.head(l), List.drop(&2, Bool, Key.bits(k), pos), d, hd)
  )

# no Some is None
def Crit.some_ne_none(-A: Data, -x: A, e: {Some{x} == None{}: Maybe<&2, A>}) -> Empty:
  Shared.Maybe.none_ne_some(A, x, Equal.sym(Maybe<&2, A>, Some{x}, None{}, e))

# bits differ from themselves nowhere
def Bits.diff_self(bs: List<&2, Bool>) -> {Bits.diff(bs, bs) == None{}: Maybe<&2, Nat>}:
  match bs:
    case Nil{}:
      {==}
    case Con{True{}, +r}:
      %Equal.sym(Maybe<&2, Nat>, Bits.diff(r, r), None{}, Bits.diff_self(r)): {Maybe.map(&2, Nat, Nat, n => 1n+n, _) == None{}: Maybe<&2, Nat>}
      {==}
    case Con{False{}, +r}:
      %Equal.sym(Maybe<&2, Nat>, Bits.diff(r, r), None{}, Bits.diff_self(r)): {Maybe.map(&2, Nat, Nat, n => 1n+n, _) == None{}: Maybe<&2, Nat>}
      {==}

# a key differs from itself nowhere
def Key.diff_self(+k: List<&2, U32>) -> {Key.diff(k, k) == None{}: Maybe<&2, Nat>}:
  %Equal.sym(Maybe<&2, Nat>, Key.diff(k, k), Bits.diff(Key.bits(k), Key.bits(k)), Key.diff_bits(k, k)): {_ == None{}: Maybe<&2, Nat>}
  Bits.diff_self(Key.bits(k))

# a key agrees with itself on any number of bits
def Key.agree_self(+k: List<&2, U32>, +n: Nat) -> {Key.agree(k, k, n) == True{}: Bool}:
  %Equal.sym(Maybe<&2, Nat>, Key.diff(k, k), None{}, Key.diff_self(k)): {Bits.agree(_, n) == True{}: Bool}
  {==}

# a difference one on that is none was none
def Crit.map_succ_none(d: Maybe<&2, Nat>) -> {Maybe.map(&2, Nat, Nat, m => 1n+m, d) == None{}: Maybe<&2, Nat>} -> {d == None{}: Maybe<&2, Nat>}:
  match d:
    case None{}:
      h => {==}
    case Some{x}:
      h => Empty.absurd({Some{x} == None{}: Maybe<&2, Nat>}, Crit.some_ne_none(Nat, 1n+x, h))

# words that differ nowhere are equal
def Word.diff_none(n: Nat, w: Word(n), v: Word(n)) -> {Word.diff(n, w, v) == None{}: Maybe<&2, Nat>} -> {w == v: Word(n)}:
  match n:
    case 0n:
      match w v:
        case WNil{} WNil{}:
          h => {==}
    case 1n+(+p):
      match w v:
        case WCon{True{}, +rw} WCon{True{}, +rv}:
          h =>
            %Word.diff_none(p, rw, rv)(Crit.map_succ_none(Word.diff(p, rw, rv))(h)): {WCon{True{}, rw} == WCon{True{}, _}: Word(1n+p)}
            {==}
        case WCon{False{}, +rw} WCon{False{}, +rv}:
          h =>
            %Word.diff_none(p, rw, rv)(Crit.map_succ_none(Word.diff(p, rw, rv))(h)): {WCon{False{}, rw} == WCon{False{}, _}: Word(1n+p)}
            {==}
        case WCon{True{}, rw} WCon{False{}, rv}:
          h => Empty.absurd({WCon{True{}, rw} == WCon{False{}, rv}: Word(1n+p)}, Crit.some_ne_none(Nat, 0n, h))
        case WCon{False{}, rw} WCon{True{}, rv}:
          h => Empty.absurd({WCon{False{}, rw} == WCon{True{}, rv}: Word(1n+p)}, Crit.some_ne_none(Nat, 0n, h))

# Key.diff_go_none at two first words, once their difference dd is known
def Key.diff_go_none.at(
  +w: Word(32n),
  +v: Word(32n),
  +ra: List<&2, U32>,
  +rb: List<&2, U32>,
  +at: Nat,
  dd: Maybe<&2, Nat>,
  ih: {Key.diff.go(ra, rb, Nat.add(at, 32n)) == None{}: Maybe<&2, Nat>} -> {ra == rb: List<&2, U32>}
) -> {Word.diff(32n, w, v) == dd: Maybe<&2, Nat>} -> {
  Shared.Bool.when(
    Maybe<&2, Nat>,
    Maybe.is_none(&2, Nat, dd),
    u => Key.diff.go(ra, rb, Nat.add(at, 32n)),
    u => Maybe.map(&2, Nat, Nat, n => Nat.add(at, n), dd)
  )
    == None{}: Maybe<&2, Nat>
} -> {U32{w} <> ra == U32{v} <> rb: List<&2, U32>}:
  match dd:
    case None{}:
      hw => h =>
        %Word.diff_none(32n, w, v)(hw): {U32{w} <> ra == U32{_} <> rb: List<&2, U32>}
        %ih(h): {U32{w} <> ra == U32{w} <> _: List<&2, U32>}
        {==}
    case Some{y}:
      hw => h => Empty.absurd({U32{w} <> ra == U32{v} <> rb: List<&2, U32>}, Crit.some_ne_none(Nat, Nat.add(at, y), h))

# keys that differ nowhere, after at bits, are equal
def Key.diff_go_none(+a: List<&2, U32>, +b: List<&2, U32>, +at: Nat) -> {Key.diff.go(a, b, at) == None{}: Maybe<&2, Nat>} -> {
  a == b: List<&2, U32>
}:
  match a b:
    case Nil{} Nil{}:
      h => {==}
    case Con{U32{+w}, +ra} Con{U32{+v}, +rb}:
      h => Key.diff_go_none.at(w, v, ra, rb, at, Word.diff(32n, w, v), Key.diff_go_none(ra, rb, Nat.add(at, 32n)))({==})(h)
    case Nil{} Con{U32{w}, rb}:
      h => Empty.absurd({[] == U32{w} <> rb: List<&2, U32>}, Crit.some_ne_none(Nat, at, h))
    case Con{U32{w}, ra} Nil{}:
      h => Empty.absurd({U32{w} <> ra == []: List<&2, U32>}, Crit.some_ne_none(Nat, at, h))

# keys that differ nowhere are equal
def Key.diff_none(+a: List<&2, U32>, +b: List<&2, U32>) -> {Key.diff(a, b) == None{}: Maybe<&2, Nat>} -> {a == b: List<&2, U32>}:
  h => Key.diff_go_none(a, b, 0n)(Equal.trans(Maybe<&2, Nat>, Key.diff.go(a, b, 0n), Key.diff.fast(a, b, 0n), None{}, Equal.sym(Maybe<&2, Nat>, Key.diff.fast(a, b, 0n), Key.diff.go(a, b, 0n), Key.diff_fast_go(a, b, 0n)), h))

# a difference that is none is None
def Crit.none_of(d: Maybe<&2, Nat>) -> {Maybe.is_none(&2, Nat, d) == True{}: Bool} -> {d == None{}: Maybe<&2, Nat>}:
  match d:
    case None{}:
      h => {==}
    case Some{x}:
      h => Empty.absurd({Some{x} == None{}: Maybe<&2, Nat>}, Shared.Bool.false_ne_true(h))

# bits that differ first at x have different bits at x
def Bits.diff_at(+a: List<&2, Bool>, +b: List<&2, Bool>, +x: Nat) -> {Bits.diff(a, b) == Some{x}: Maybe<&2, Nat>} -> {
  Shared.Maybe.is_eq(~Bool, ~Shared.Bool.is_eq, Bits.at(a, x), Bits.at(b, x)) == False{}: Bool
}:
  +h =>
    +ex = Shared.Maybe.is_eq(~Bool, ~Shared.Bool.is_eq, Bits.at(a, x), Bits.at(b, x))
    Equal.trans(
      Bool,
      ex,
      Bool.and(Bits.agree_n(x, a, b), ex),
      False{},
      Equal.cong(Bool, Bool, t => Bool.and(t, ex), True{}, Bits.agree_n(x, a, b), Equal.sym(Bool, Bits.agree_n(x, a, b), True{}, (
          %Bits.agree_diff(a, b, x): {_ == True{}: Bool}
          %Equal.sym(Maybe<&2, Nat>, Bits.diff(a, b), Some{x}, h): {Bits.agree(_, x) == True{}: Bool}
          Shared.Nat.le_refl(x)
        ))),
      Equal.trans(
        Bool,
        Bool.and(Bits.agree_n(x, a, b), ex),
        Bits.agree_n(1n+x, a, b),
        False{},
        Equal.sym(Bool, Bits.agree_n(1n+x, a, b), Bool.and(Bits.agree_n(x, a, b), ex), Bits.agree_n_succ(a, b, x)),
        (
          %Bits.agree_diff(a, b, 1n+x): {_ == False{}: Bool}
          %Equal.sym(Maybe<&2, Nat>, Bits.diff(a, b), Some{x}, h): {Bits.agree(_, 1n+x) == False{}: Bool}
          Shared.Nat.succ_nle(x)
        )
      )
    )

# a list that is gone after a is gone after any b at least a
def Crit.drop_nil_le(+xs: List<&2, Bool>, +a: Nat, +b: Nat) -> {List.drop(&2, Bool, xs, a) == []: List<&2, Bool>} -> {
  Nat.is_le(a, b) == True{}: Bool
} -> {List.drop(&2, Bool, xs, b) == []: List<&2, Bool>}:
  h => l => Equal.trans(
    List<&2, Bool>,
    List.drop(&2, Bool, xs, b),
    List.drop(&2, Bool, List.drop(&2, Bool, xs, a), Nat.sub(b, a)),
    [],
    Equal.sym(List<&2, Bool>, List.drop(&2, Bool, List.drop(&2, Bool, xs, a), Nat.sub(b, a)), List.drop(&2, Bool, xs, b), Crit.drop_drop(xs, a, b)(l)),
    Equal.cong(List<&2, Bool>, List<&2, Bool>, t => List.drop(&2, Bool, t, Nat.sub(b, a)), List.drop(&2, Bool, xs, a), [], h)
  )

# Crit.end_is, once the difference dd of k and rep is known
def Crit.end_is.at(+rep: List<&2, U32>, +pos: Nat, +k: List<&2, U32>, dd: Maybe<&2, Nat>) -> {Key.diff(k, rep) == dd: Maybe<&2, Nat>} -> {
  Nat.is_eq(List.length(&2, Bool, Key.bits(rep)), pos) == True{}: Bool
} -> {List.drop(&2, Bool, Key.bits(k), pos) == []: List<&2, Bool>} -> {Crit.above(dd, pos) == False{}: Bool} -> {
  Key.is_eq(rep, k) == True{}: Bool
}:
  match dd:
    case None{}:
      he => hl => hd => ha =>
        %Key.diff_none(k, rep)(he): {Key.is_eq(_, k) == True{}: Bool}
        Key.is_eq_refl(k)
    case Some{+x}:
      +he => +hl => +hd => +ha =>
        +le = Shared.Nat.nlt_le(x, pos)(ha)
        +nk = Crit.drop_nil_le(Key.bits(k), pos, x)(hd)(le)
        +nr = Crit.drop_nil_le(Key.bits(rep), pos, x)((
          %Shared.Nat.is_eq_sound(List.length(&2, Bool, Key.bits(rep)), pos)(hl): {List.drop(&2, Bool, Key.bits(rep), _) == []: List<&2, Bool>}
          Crit.drop_length(Key.bits(rep))
        ))(le)
        Empty.absurd(
          {Key.is_eq(rep, k) == True{}: Bool},
          Shared.Bool.false_ne_true(
            Equal.trans(
              Bool,
              False{},
              Shared.Maybe.is_eq(~Bool, ~Shared.Bool.is_eq, Bits.at(Key.bits(k), x), Bits.at(Key.bits(rep), x)),
              True{},
              Equal.sym(
                Bool,
                Shared.Maybe.is_eq(~Bool, ~Shared.Bool.is_eq, Bits.at(Key.bits(k), x), Bits.at(Key.bits(rep), x)),
                False{},
                Bits.diff_at(Key.bits(k), Key.bits(rep), x)(
                  Equal.trans(Maybe<&2, Nat>, Bits.diff(Key.bits(k), Key.bits(rep)), Key.diff(k, rep), Some{x}, Equal.sym(Maybe<&2, Nat>, Key.diff(k, rep), Bits.diff(Key.bits(k), Key.bits(rep)), Key.diff_bits(k, rep)), he)
                )
              ),
              (
                %Equal.sym(List<&2, Bool>, List.drop(&2, Bool, Key.bits(k), x), [], nk): {
                  Shared.Maybe.is_eq(~Bool, ~Shared.Bool.is_eq, Bits.head(_), Bits.head(List.drop(&2, Bool, Key.bits(rep), x))) == True{}: Bool
                }
                %Equal.sym(List<&2, Bool>, List.drop(&2, Bool, Key.bits(rep), x), [], nr): {
                  Shared.Maybe.is_eq(~Bool, ~Shared.Bool.is_eq, Bits.head([]), Bits.head(_)) == True{}: Bool
                }
                {==}
              )
            )
          )
        )

# a fork's end key of pos bits is a key k that ends by pos and differs from
# it nowhere before pos
def Crit.end_is(+rep: List<&2, U32>, +pos: Nat, +k: List<&2, U32>) -> {
  Nat.is_eq(List.length(&2, Bool, Key.bits(rep)), pos) == True{}: Bool
} -> {List.drop(&2, Bool, Key.bits(k), pos) == []: List<&2, Bool>} -> {Crit.above(Key.diff(k, rep), pos) == False{}: Bool} -> {
  Key.is_eq(rep, k) == True{}: Bool
}:
  Crit.end_is.at(rep, pos, k, Key.diff(k, rep))({==})

# a cursor whose bits are d is done exactly when d is empty
def Crit.done_of(+c: Cur, +d: List<&2, Bool>) -> {Cur.bits(c) == d: List<&2, Bool>} -> {Cur.done(c) == List.is_empty(&2, Bool, d): Bool}:
  h => Equal.trans(
    Bool,
    Cur.done(c),
    List.is_empty(&2, Bool, Cur.bits(c)),
    List.is_empty(&2, Bool, d),
    Cur.done_bits(c),
    Equal.cong(List<&2, Bool>, Bool, l => List.is_empty(&2, Bool, l), Cur.bits(c), d, h)
  )

# the bit of a cursor whose bits are d is the head of d
def Crit.bit_of(+c: Cur, +d: List<&2, Bool>) -> {Cur.bits(c) == d: List<&2, Bool>} -> {
  Cur.bit(c) == Shared.List.head_or(Bool, d, False{}): Bool
}:
  h => Equal.trans(
    Bool,
    Cur.bit(c),
    Shared.List.head_or(Bool, Cur.bits(c), False{}),
    Shared.List.head_or(Bool, d, False{}),
    Cur.bit_bits(c),
    Equal.cong(List<&2, Bool>, Bool, l => Shared.List.head_or(Bool, l, False{}), Cur.bits(c), d, h)
  )

# two answers of one test that differ: no such test
def Crit.clash(+b: Bool, +x: Bool, +y: Bool, hx: {b == x: Bool}, hy: {b == y: Bool}, n: {x == y: Bool} -> Empty) -> Empty:
  n(Equal.trans(Bool, x, b, y, Equal.sym(Bool, b, x, hx), hy))

# the bits of a cursor at the bit pos, read from a cursor at the bit at of k,
# are k's bits from pos
def Crit.skip_at(+k: List<&2, U32>, +at: Nat, +pos: Nat, +c: Cur) -> {Nat.is_le(at, pos) == True{}: Bool} -> {
  Cur.bits(c) == List.drop(&2, Bool, Key.bits(k), at): List<&2, Bool>
} -> {Cur.bits(Cur.skip(Nat.sub(pos, at), c)) == List.drop(&2, Bool, Key.bits(k), pos): List<&2, Bool>}:
  l => hc => Equal.trans(
    List<&2, Bool>,
    Cur.bits(Cur.skip(Nat.sub(pos, at), c)),
    List.drop(&2, Bool, Cur.bits(c), Nat.sub(pos, at)),
    List.drop(&2, Bool, Key.bits(k), pos),
    Cur.skip_bits(Nat.sub(pos, at), c),
    Equal.trans(
      List<&2, Bool>,
      List.drop(&2, Bool, Cur.bits(c), Nat.sub(pos, at)),
      List.drop(&2, Bool, List.drop(&2, Bool, Key.bits(k), at), Nat.sub(pos, at)),
      List.drop(&2, Bool, Key.bits(k), pos),
      Equal.cong(List<&2, Bool>, List<&2, Bool>, l2 => List.drop(&2, Bool, l2, Nat.sub(pos, at)), Cur.bits(c), List.drop(&2, Bool, Key.bits(k), at), hc),
      Crit.drop_drop(Key.bits(k), at, pos)(l)
    )
  )

# the bits of a cursor one on from one at the bit pos of k are k's bits from
# the bit after
def Crit.next_at(+k: List<&2, U32>, +pos: Nat, +c2: Cur) -> {Cur.bits(c2) == List.drop(&2, Bool, Key.bits(k), pos): List<&2, Bool>} -> {
  Cur.bits(Cur.next(c2)) == List.drop(&2, Bool, Key.bits(k), 1n+pos): List<&2, Bool>
}:
  hc => Equal.trans(
    List<&2, Bool>,
    Cur.bits(Cur.next(c2)),
    List.drop(&2, Bool, Cur.bits(c2), 1n),
    List.drop(&2, Bool, Key.bits(k), 1n+pos),
    Cur.next_bits(c2),
    Equal.trans(
      List<&2, Bool>,
      List.drop(&2, Bool, Cur.bits(c2), 1n),
      List.drop(&2, Bool, List.drop(&2, Bool, Key.bits(k), pos), 1n),
      List.drop(&2, Bool, Key.bits(k), 1n+pos),
      Equal.cong(List<&2, Bool>, List<&2, Bool>, l2 => List.drop(&2, Bool, l2, 1n), Cur.bits(c2), List.drop(&2, Bool, Key.bits(k), pos), hc),
      Crit.drop_drop_one(Key.bits(k), pos)
    )
  )

# a choice of nothing, then x, is x, when the first choice e is nothing
def Crit.or_none_first(-V: Data, e: Maybe<&2, V>, +x: Maybe<&2, V>) -> {e == None{}: Maybe<&2, V>} -> {
  x == Maybe.or(&2, V, e, x): Maybe<&2, V>
}:
  h => Equal.cong(Maybe<&2, V>, Maybe<&2, V>, t => Maybe.or(&2, V, t, x), None{}, e, Equal.sym(Maybe<&2, V>, e, None{}, h))

# the end of a fork whose keys pass p passes p, or there is none
def Crit.all.hit(~V: Data, ~G: Data, ~p: G -> List<&2, U32> -> Bool, +rep: List<&2, U32>, +pos: Nat, +e: Maybe<&2, V>, +z: Crit<V>, +o: Crit<V>, +g: G) -> {
  Crit.all(~V, ~G, ~p, Crit.Fork{rep, pos, e, z, o}, g) == True{}: Bool
} -> {Bool.or(Maybe.is_none(&2, V, e), p(g)(rep)) == True{}: Bool}:
  h => Shared.List.all.if_hit(Bool.or(Maybe.is_none(&2, V, e), p(g)(rep)), u => List.all.if(u2 => Crit.all(~V, ~G, ~p, o, g), Crit.all(~V, ~G, ~p, z, g)))(h)

# the zero side of a fork whose keys pass p passes p
def Crit.all.z(~V: Data, ~G: Data, ~p: G -> List<&2, U32> -> Bool, +rep: List<&2, U32>, +pos: Nat, +e: Maybe<&2, V>, +z: Crit<V>, +o: Crit<V>, +g: G) -> {
  Crit.all(~V, ~G, ~p, Crit.Fork{rep, pos, e, z, o}, g) == True{}: Bool
} -> {Crit.all(~V, ~G, ~p, z, g) == True{}: Bool}:
  h => Shared.List.all.if_hit(Crit.all(~V, ~G, ~p, z, g), u2 => Crit.all(~V, ~G, ~p, o, g))(
    Shared.List.all.if_rest(Bool.or(Maybe.is_none(&2, V, e), p(g)(rep)), u => List.all.if(u2 => Crit.all(~V, ~G, ~p, o, g), Crit.all(~V, ~G, ~p, z, g)))(h)
  )

# the one side of a fork whose keys pass p passes p
def Crit.all.o(~V: Data, ~G: Data, ~p: G -> List<&2, U32> -> Bool, +rep: List<&2, U32>, +pos: Nat, +e: Maybe<&2, V>, +z: Crit<V>, +o: Crit<V>, +g: G) -> {
  Crit.all(~V, ~G, ~p, Crit.Fork{rep, pos, e, z, o}, g) == True{}: Bool
} -> {Crit.all(~V, ~G, ~p, o, g) == True{}: Bool}:
  h => Shared.List.all.if_rest(Crit.all(~V, ~G, ~p, z, g), u2 => Crit.all(~V, ~G, ~p, o, g))(
    Shared.List.all.if_rest(Bool.or(Maybe.is_none(&2, V, e), p(g)(rep)), u => List.all.if(u2 => Crit.all(~V, ~G, ~p, o, g), Crit.all(~V, ~G, ~p, z, g)))(h)
  )

# a choice of a, else some y, is some
def Crit.or_some_is_some(-A: Data, a: Maybe<&2, A>, -y: A) -> {Maybe.is_some(&2, A, Maybe.or(&2, A, a, Some{y})) == True{}: Bool}:
  match a:
    case None{}:
      {==}
    case Some{x}:
      {==}

# a choice of a that is some, else r, is a
def Crit.or_of_some(-A: Data, a: Maybe<&2, A>, -r: Maybe<&2, A>) -> {Maybe.is_some(&2, A, a) == True{}: Bool} -> {
  Maybe.or(&2, A, a, r) == a: Maybe<&2, A>
}:
  match a:
    case None{}:
      h => Empty.absurd({r == None{}: Maybe<&2, A>}, Shared.Bool.false_ne_true(h))
    case Some{x}:
      h => {==}

# a choice of a, else some y, takes no more choices
def Crit.or_absorb(-A: Data, a: Maybe<&2, A>, -y: A, -r: Maybe<&2, A>) -> {
  Maybe.or(&2, A, Maybe.or(&2, A, a, Some{y}), r) == Maybe.or(&2, A, a, Some{y}): Maybe<&2, A>
}:
  match a:
    case None{}:
      {==}
    case Some{x}:
      {==}

# a choice x of a, else some y, that is some n after the choice r, is some n
def Crit.or_step(-A: Data, +x: Maybe<&2, A>, +a: Maybe<&2, A>, +y: A, +r: Maybe<&2, A>, +n: A) -> {
  x == Maybe.or(&2, A, a, Some{y}): Maybe<&2, A>
} -> {Maybe.or(&2, A, x, r) == Some{n}: Maybe<&2, A>} -> {Maybe.or(&2, A, a, Some{y}) == Some{n}: Maybe<&2, A>}:
  h1 => h2 => Equal.trans(
    Maybe<&2, A>,
    Maybe.or(&2, A, a, Some{y}),
    Maybe.or(&2, A, x, r),
    Some{n},
    Equal.trans(
      Maybe<&2, A>,
      Maybe.or(&2, A, a, Some{y}),
      Maybe.or(&2, A, Maybe.or(&2, A, a, Some{y}), r),
      Maybe.or(&2, A, x, r),
      Equal.sym(Maybe<&2, A>, Maybe.or(&2, A, Maybe.or(&2, A, a, Some{y}), r), Maybe.or(&2, A, a, Some{y}), Crit.or_absorb(A, a, y, r)),
      Equal.cong(Maybe<&2, A>, Maybe<&2, A>, t => Maybe.or(&2, A, t, r), Maybe.or(&2, A, a, Some{y}), x, Equal.sym(Maybe<&2, A>, x, Maybe.or(&2, A, a, Some{y}), h1))
    ),
    h2
  )

# a choice x that is some y, and some n after the choice r: y is n
def Crit.or_done(-A: Data, +x: Maybe<&2, A>, +y: A, +r: Maybe<&2, A>, +n: A) -> {x == Some{y}: Maybe<&2, A>} -> {
  Maybe.or(&2, A, x, r) == Some{n}: Maybe<&2, A>
} -> {y == n: A}:
  h1 => h2 => Shared.Maybe.some_inj(
    A,
    y,
    n,
    Equal.trans(
      Maybe<&2, A>,
      Some{y},
      Maybe.or(&2, A, x, r),
      Some{n},
      Equal.cong(Maybe<&2, A>, Maybe<&2, A>, t => Maybe.or(&2, A, t, r), Some{y}, x, Equal.sym(Maybe<&2, A>, x, Some{y}, h1)),
      h2
    )
  )

# a choice of a, else some y, that is some n: a is some n, or y is n
def Crit.or_pick(-A: Data, -T: Type, a: Maybe<&2, A>, +y: A, +n: A) -> ({a == Some{n}: Maybe<&2, A>} -> T) -> ({y == n: A} -> T) -> {
  Maybe.or(&2, A, a, Some{y}) == Some{n}: Maybe<&2, A>
} -> T:
  match a:
    case None{}:
      ha => hy => s => hy(Shared.Maybe.some_inj(A, y, n, s))
    case Some{x}:
      ha => hy => s => ha(s)

# the key that a read reaches at a fork where it is done is the rep
def Crit.near_done(-V: Data, +rep: List<&2, U32>, +pos: Nat, -e: Maybe<&2, V>, -z: Crit<V>, -o: Crit<V>, +at: Nat, +c: Cur) -> {
  Cur.done(Cur.skip(Nat.sub(pos, at), c)) == True{}: Bool
} -> {Crit.near(V, Crit.Fork{rep, pos, e, z, o}, at, c) == Some{rep}: Maybe<&2, List<&2, U32>>}:
  h => Shared.Bool.when_cases(
    Maybe<&2, List<&2, U32>>,
    t => {t == Some{rep}: Maybe<&2, List<&2, U32>>},
    Cur.done(Cur.skip(Nat.sub(pos, at), c)),
    u => Some{rep},
    u => Shared.Bool.when(
      Maybe<&2, List<&2, U32>>,
      Cur.bit(Cur.skip(Nat.sub(pos, at), c)),
      u => Maybe.or(&2, List<&2, U32>, Crit.near(V, o, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c))), Some{rep}),
      u => Maybe.or(&2, List<&2, U32>, Crit.near(V, z, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c))), Some{rep})
    ),
    t1 => {==},
    t1 => Empty.absurd(
      {
        Shared.Bool.when(
          Maybe<&2, List<&2, U32>>,
          Cur.bit(Cur.skip(Nat.sub(pos, at), c)),
          u => Maybe.or(&2, List<&2, U32>, Crit.near(V, o, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c))), Some{rep}),
          u => Maybe.or(&2, List<&2, U32>, Crit.near(V, z, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c))), Some{rep})
        )
          == Some{rep}: Maybe<&2, List<&2, U32>>
      },
      Crit.clash(Cur.done(Cur.skip(Nat.sub(pos, at), c)), True{}, False{}, h, t1, Shared.Bool.true_ne_false)
    )
  )

# the key that a read reaches at a fork where it goes on to the side b
def Crit.near_side(
  -V: Data,
  +rep: List<&2, U32>,
  +pos: Nat,
  -e: Maybe<&2, V>,
  +z: Crit<V>,
  +o: Crit<V>,
  +at: Nat,
  +c: Cur,
  b: Bool
) -> {Cur.done(Cur.skip(Nat.sub(pos, at), c)) == False{}: Bool} -> {Cur.bit(Cur.skip(Nat.sub(pos, at), c)) == b: Bool} -> {
  Crit.near(V, Crit.Fork{rep, pos, e, z, o}, at, c)
    == Maybe.or(&2, List<&2, U32>, Crit.near(V, Bool.pick(Crit<V>, b, o, z), 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c))), Some{rep}): Maybe<&2, List<&2, U32>>
}:
  match b:
    case True{}:
      h => hb =>
        %Equal.sym(Bool, Cur.done(Cur.skip(Nat.sub(pos, at), c)), False{}, h): {
          Shared.Bool.when(
            Maybe<&2, List<&2, U32>>,
            _,
            u => Some{rep},
            u => Shared.Bool.when(
              Maybe<&2, List<&2, U32>>,
              Cur.bit(Cur.skip(Nat.sub(pos, at), c)),
              u => Maybe.or(&2, List<&2, U32>, Crit.near(V, o, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c))), Some{rep}),
              u => Maybe.or(&2, List<&2, U32>, Crit.near(V, z, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c))), Some{rep})
            )
          )
            == Maybe.or(&2, List<&2, U32>, Crit.near(V, o, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c))), Some{rep}): Maybe<&2, List<&2, U32>>
        }
        %Equal.sym(Bool, Cur.bit(Cur.skip(Nat.sub(pos, at), c)), True{}, hb): {
          Shared.Bool.when(
            Maybe<&2, List<&2, U32>>,
            _,
            u => Maybe.or(&2, List<&2, U32>, Crit.near(V, o, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c))), Some{rep}),
            u => Maybe.or(&2, List<&2, U32>, Crit.near(V, z, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c))), Some{rep})
          )
            == Maybe.or(&2, List<&2, U32>, Crit.near(V, o, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c))), Some{rep}): Maybe<&2, List<&2, U32>>
        }
        {==}
    case False{}:
      h => hb =>
        %Equal.sym(Bool, Cur.done(Cur.skip(Nat.sub(pos, at), c)), False{}, h): {
          Shared.Bool.when(
            Maybe<&2, List<&2, U32>>,
            _,
            u => Some{rep},
            u => Shared.Bool.when(
              Maybe<&2, List<&2, U32>>,
              Cur.bit(Cur.skip(Nat.sub(pos, at), c)),
              u => Maybe.or(&2, List<&2, U32>, Crit.near(V, o, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c))), Some{rep}),
              u => Maybe.or(&2, List<&2, U32>, Crit.near(V, z, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c))), Some{rep})
            )
          )
            == Maybe.or(&2, List<&2, U32>, Crit.near(V, z, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c))), Some{rep}): Maybe<&2, List<&2, U32>>
        }
        %Equal.sym(Bool, Cur.bit(Cur.skip(Nat.sub(pos, at), c)), False{}, hb): {
          Shared.Bool.when(
            Maybe<&2, List<&2, U32>>,
            _,
            u => Maybe.or(&2, List<&2, U32>, Crit.near(V, o, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c))), Some{rep}),
            u => Maybe.or(&2, List<&2, U32>, Crit.near(V, z, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c))), Some{rep})
          )
            == Maybe.or(&2, List<&2, U32>, Crit.near(V, z, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c))), Some{rep}): Maybe<&2, List<&2, U32>>
        }
        {==}

# a read of a fork reaches some key
def Crit.near_some(-V: Data, +rep: List<&2, U32>, +pos: Nat, -e: Maybe<&2, V>, +z: Crit<V>, +o: Crit<V>, +at: Nat, +c: Cur) -> {
  Maybe.is_some(&2, List<&2, U32>, Crit.near(V, Crit.Fork{rep, pos, e, z, o}, at, c)) == True{}: Bool
}:
  Shared.Bool.when_cases(
    Maybe<&2, List<&2, U32>>,
    t => {Maybe.is_some(&2, List<&2, U32>, t) == True{}: Bool},
    Cur.done(Cur.skip(Nat.sub(pos, at), c)),
    u => Some{rep},
    u => Shared.Bool.when(
      Maybe<&2, List<&2, U32>>,
      Cur.bit(Cur.skip(Nat.sub(pos, at), c)),
      u => Maybe.or(&2, List<&2, U32>, Crit.near(V, o, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c))), Some{rep}),
      u => Maybe.or(&2, List<&2, U32>, Crit.near(V, z, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c))), Some{rep})
    ),
    t1 => {==},
    t1 => Shared.Bool.when_cases(
      Maybe<&2, List<&2, U32>>,
      t => {Maybe.is_some(&2, List<&2, U32>, t) == True{}: Bool},
      Cur.bit(Cur.skip(Nat.sub(pos, at), c)),
      u => Maybe.or(&2, List<&2, U32>, Crit.near(V, o, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c))), Some{rep}),
      u => Maybe.or(&2, List<&2, U32>, Crit.near(V, z, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c))), Some{rep}),
      t2 => Crit.or_some_is_some(List<&2, U32>, Crit.near(V, o, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c))), rep),
      t2 => Crit.or_some_is_some(List<&2, U32>, Crit.near(V, z, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c))), rep)
    )
  )

# m has no entry
def Crit.is_tip(-V: Data, m: Crit<V>) -> Bool:
  match m:
    case Crit.Tip{}:
      True{}
    case Crit.Leaf{k, v}:
      False{}
    case Crit.Fork{r, p, e, z, o}:
      False{}

# a fork of two entries at least, with no end, has a zero side
def Crit.shape_none_z(-V: Data, z: Crit<V>, o: Crit<V>) -> {Crit.shape(V, None{}, z, o) == True{}: Bool} -> {Crit.is_tip(V, z) == False{}: Bool}:
  match z o:
    case Crit.Tip{} Crit.Tip{}:
      h => Empty.absurd({True{} == False{}: Bool}, Shared.Bool.false_ne_true(h))
    case Crit.Tip{} Crit.Leaf{k, v}:
      h => Empty.absurd({True{} == False{}: Bool}, Shared.Bool.false_ne_true(h))
    case Crit.Tip{} Crit.Fork{r, p, e, z1, o1}:
      h => Empty.absurd({True{} == False{}: Bool}, Shared.Bool.false_ne_true(h))
    case Crit.Leaf{k, v} o2:
      h => {==}
    case Crit.Fork{r, p, e, z1, o1} o2:
      h => {==}

# Crit.rep_pass at a fork, by its end e; ih is the claim for its zero side
def Crit.rep_pass.fork(
  ~V: Data,
  ~G: Data,
  ~p: G -> List<&2, U32> -> Bool,
  +rep: List<&2, U32>,
  +pos: Nat,
  e: Maybe<&2, V>,
  +z: Crit<V>,
  +o: Crit<V>,
  +lo: Nat,
  +g: G,
  ih: {Crit.wf(~V, z, 1n+pos) == True{}: Bool} -> {Crit.all(~V, ~G, ~p, z, g) == True{}: Bool} -> {Crit.is_tip(V, z) == False{}: Bool} -> {
    p(g)(Crit.rep(V, z, rep)) == True{}: Bool
  }
) -> {Crit.wf(~V, Crit.Fork{rep, pos, e, z, o}, lo) == True{}: Bool} -> {Crit.all(~V, ~G, ~p, Crit.Fork{rep, pos, e, z, o}, g) == True{}: Bool} -> {
  p(g)(rep) == True{}: Bool
}:
  match e:
    case None{}:
      +h => a =>
        %Equal.sym(List<&2, U32>, rep, Crit.rep(V, z, rep), Key.is_eq_sound(rep, Crit.rep(V, z, rep))(Crit.wf.rep_ok(~V, rep, pos, None{}, z, o, lo)(h))): {
          p(g)(_) == True{}: Bool
        }
        ih(Crit.wf.wf_z(~V, rep, pos, None{}, z, o, lo)(h))(Crit.all.z(~V, ~G, ~p, rep, pos, None{}, z, o, g)(a))(
          Crit.shape_none_z(V, z, o)(Crit.wf.shape(~V, rep, pos, None{}, z, o, lo)(h))
        )
    case Some{v}:
      h => a => Crit.all.hit(~V, ~G, ~p, rep, pos, Some{v}, z, o, g)(a)

# the first key of a well formed map with an entry, whose keys pass p, passes p
def Crit.rep_pass(~V: Data, ~G: Data, ~p: G -> List<&2, U32> -> Bool, m: Crit<V>, +lo: Nat, +g: G, +d: List<&2, U32>) -> {
  Crit.wf(~V, m, lo) == True{}: Bool
} -> {Crit.all(~V, ~G, ~p, m, g) == True{}: Bool} -> {Crit.is_tip(V, m) == False{}: Bool} -> {p(g)(Crit.rep(V, m, d)) == True{}: Bool}:
  match m:
    case Crit.Tip{}:
      h => a => t => Empty.absurd({p(g)(d) == True{}: Bool}, Shared.Bool.true_ne_false(t))
    case Crit.Leaf{k, v}:
      h => a => t => a
    case Crit.Fork{+rep, +pos, +e, +z, +o}:
      h => a => t => Crit.rep_pass.fork(~V, ~G, ~p, rep, pos, e, z, o, lo, g, Crit.rep_pass(~V, ~G, ~p, z, 1n+pos, g, rep))(h)(a)

# the key that a read of a well formed map reaches, when its keys pass p,
# passes p
def Crit.near_pass(~V: Data, ~G: Data, ~p: G -> List<&2, U32> -> Bool, m: Crit<V>, +lo: Nat, +at: Nat, +c: Cur, +g: G, +n: List<&2, U32>) -> {
  Crit.wf(~V, m, lo) == True{}: Bool
} -> {Crit.all(~V, ~G, ~p, m, g) == True{}: Bool} -> {Crit.near(V, m, at, c) == Some{n}: Maybe<&2, List<&2, U32>>} -> {p(g)(n) == True{}: Bool}:
  match m:
    case Crit.Tip{}:
      h => a => s => Empty.absurd({p(g)(n) == True{}: Bool}, Shared.Maybe.none_ne_some(List<&2, U32>, n, s))
    case Crit.Leaf{+k, v}:
      h => a => s =>
        %Shared.Maybe.some_inj(List<&2, U32>, k, n, s): {p(g)(_) == True{}: Bool}
        a
    case Crit.Fork{+rep, +pos, +e, +z, +o}:
      +h => +a => Shared.Bool.when_cases(
        Maybe<&2, List<&2, U32>>,
        t => {t == Some{n}: Maybe<&2, List<&2, U32>>} -> {p(g)(n) == True{}: Bool},
        Cur.done(Cur.skip(Nat.sub(pos, at), c)),
        u => Some{rep},
        u => Shared.Bool.when(
          Maybe<&2, List<&2, U32>>,
          Cur.bit(Cur.skip(Nat.sub(pos, at), c)),
          u => Maybe.or(&2, List<&2, U32>, Crit.near(V, o, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c))), Some{rep}),
          u => Maybe.or(&2, List<&2, U32>, Crit.near(V, z, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c))), Some{rep})
        ),
        t1 => s =>
          %Shared.Maybe.some_inj(List<&2, U32>, rep, n, s): {p(g)(_) == True{}: Bool}
          Crit.rep_pass(~V, ~G, ~p, Crit.Fork{rep, pos, e, z, o}, lo, g, [])(h)(a)({==}),
        t1 => Shared.Bool.when_cases(
          Maybe<&2, List<&2, U32>>,
          t => {t == Some{n}: Maybe<&2, List<&2, U32>>} -> {p(g)(n) == True{}: Bool},
          Cur.bit(Cur.skip(Nat.sub(pos, at), c)),
          u => Maybe.or(&2, List<&2, U32>, Crit.near(V, o, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c))), Some{rep}),
          u => Maybe.or(&2, List<&2, U32>, Crit.near(V, z, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c))), Some{rep}),
          t2 => Crit.or_pick(List<&2, U32>, {p(g)(n) == True{}: Bool}, Crit.near(V, o, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c))), rep, n)(
            Crit.near_pass(~V, ~G, ~p, o, 1n+pos, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), g, n)(Crit.wf.wf_o(~V, rep, pos, e, z, o, lo)(h))(
              Crit.all.o(~V, ~G, ~p, rep, pos, e, z, o, g)(a)
            )
          )(
            eq => (
              %eq: {p(g)(_) == True{}: Bool}
              Crit.rep_pass(~V, ~G, ~p, Crit.Fork{rep, pos, e, z, o}, lo, g, [])(h)(a)({==})
            )
          ),
          t2 => Crit.or_pick(List<&2, U32>, {p(g)(n) == True{}: Bool}, Crit.near(V, z, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c))), rep, n)(
            Crit.near_pass(~V, ~G, ~p, z, 1n+pos, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), g, n)(Crit.wf.wf_z(~V, rep, pos, e, z, o, lo)(h))(
              Crit.all.z(~V, ~G, ~p, rep, pos, e, z, o, g)(a)
            )
          )(
            eq => (
              %eq: {p(g)(_) == True{}: Bool}
              Crit.rep_pass(~V, ~G, ~p, Crit.Fork{rep, pos, e, z, o}, lo, g, [])(h)(a)({==})
            )
          )
        )
      )

# a key on a side of a fork agrees with its rep before its bit
def Place.has_agree(+rep: List<&2, U32>, +pos: Nat, +b: Bool, +k: List<&2, U32>) -> {Place.has(Place{rep, pos, b}, k) == True{}: Bool} -> {
  Key.agree(k, rep, pos) == True{}: Bool
}:
  h => Shared.List.all.if_hit(Key.agree(k, rep, pos), u => Shared.Maybe.is_eq(~Bool, ~Shared.Bool.is_eq, Key.side(k, pos), Some{b}))(h)

# a key that does not agree with the rep of a fork before its bit is on no side
def Place.has_not_agree(+rep: List<&2, U32>, +pos: Nat, +b: Bool, +k: List<&2, U32>) -> {Key.agree(k, rep, pos) == False{}: Bool} -> {
  Place.has(Place{rep, pos, b}, k) == False{}: Bool
}:
  h =>
    %Equal.sym(Bool, Key.agree(k, rep, pos), False{}, h): {
      List.all.if(u => Shared.Maybe.is_eq(~Bool, ~Shared.Bool.is_eq, Key.side(k, pos), Some{b}), _) == False{}: Bool
    }
    {==}

# the key that a read of a well formed fork reaches agrees with its rep
# before its bit
def Crit.near_agree(
  ~V: Data,
  +rep: List<&2, U32>,
  +pos: Nat,
  +e: Maybe<&2, V>,
  +z: Crit<V>,
  +o: Crit<V>,
  +lo: Nat,
  +at: Nat,
  +c: Cur,
  +n: List<&2, U32>
) -> {Crit.wf(~V, Crit.Fork{rep, pos, e, z, o}, lo) == True{}: Bool} -> {
  Crit.near(V, Crit.Fork{rep, pos, e, z, o}, at, c) == Some{n}: Maybe<&2, List<&2, U32>>
} -> {Key.agree(n, rep, pos) == True{}: Bool}:
  +h => Shared.Bool.when_cases(
    Maybe<&2, List<&2, U32>>,
    t => {t == Some{n}: Maybe<&2, List<&2, U32>>} -> {Key.agree(n, rep, pos) == True{}: Bool},
    Cur.done(Cur.skip(Nat.sub(pos, at), c)),
    u => Some{rep},
    u => Shared.Bool.when(
      Maybe<&2, List<&2, U32>>,
      Cur.bit(Cur.skip(Nat.sub(pos, at), c)),
      u => Maybe.or(&2, List<&2, U32>, Crit.near(V, o, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c))), Some{rep}),
      u => Maybe.or(&2, List<&2, U32>, Crit.near(V, z, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c))), Some{rep})
    ),
    t1 => s =>
      %Shared.Maybe.some_inj(List<&2, U32>, rep, n, s): {Key.agree(_, rep, pos) == True{}: Bool}
      Key.agree_self(rep, pos),
    t1 => Shared.Bool.when_cases(
      Maybe<&2, List<&2, U32>>,
      t => {t == Some{n}: Maybe<&2, List<&2, U32>>} -> {Key.agree(n, rep, pos) == True{}: Bool},
      Cur.bit(Cur.skip(Nat.sub(pos, at), c)),
      u => Maybe.or(&2, List<&2, U32>, Crit.near(V, o, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c))), Some{rep}),
      u => Maybe.or(&2, List<&2, U32>, Crit.near(V, z, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c))), Some{rep}),
      t2 => Crit.or_pick(List<&2, U32>, {Key.agree(n, rep, pos) == True{}: Bool}, Crit.near(V, o, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c))), rep, n)(
        s2 => Place.has_agree(rep, pos, True{}, n)(
          Crit.near_pass(~V, ~Place, ~Place.has, o, 1n+pos, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), Place{rep, pos, True{}}, n)(
            Crit.wf.wf_o(~V, rep, pos, e, z, o, lo)(h)
          )(Crit.wf.all_o(~V, rep, pos, e, z, o, lo)(h))(s2)
        )
      )(
        eq => (
          %eq: {Key.agree(_, rep, pos) == True{}: Bool}
          Key.agree_self(rep, pos)
        )
      ),
      t2 => Crit.or_pick(List<&2, U32>, {Key.agree(n, rep, pos) == True{}: Bool}, Crit.near(V, z, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c))), rep, n)(
        s2 => Place.has_agree(rep, pos, False{}, n)(
          Crit.near_pass(~V, ~Place, ~Place.has, z, 1n+pos, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), Place{rep, pos, False{}}, n)(
            Crit.wf.wf_z(~V, rep, pos, e, z, o, lo)(h)
          )(Crit.wf.all_z(~V, rep, pos, e, z, o, lo)(h))(s2)
        )
      )(
        eq => (
          %eq: {Key.agree(_, rep, pos) == True{}: Bool}
          Key.agree_self(rep, pos)
        )
      )
    )
  )

# two keys agree on n bits exactly when their bits do
def Key.agree_bits(+a: List<&2, U32>, +b: List<&2, U32>, +n: Nat) -> {Key.agree(a, b, n) == Bits.agree_n(n, Key.bits(a), Key.bits(b)): Bool}:
  Equal.trans(
    Bool,
    Key.agree(a, b, n),
    Bits.agree(Bits.diff(Key.bits(a), Key.bits(b)), n),
    Bits.agree_n(n, Key.bits(a), Key.bits(b)),
    Equal.cong(Maybe<&2, Nat>, Bool, t => Bits.agree(t, n), Key.diff(a, b), Bits.diff(Key.bits(a), Key.bits(b)), Key.diff_bits(a, b)),
    Bits.agree_diff(Key.bits(a), Key.bits(b), n)
  )

# two keys that agree with a third on n bits agree with each other
def Key.agree_join(+a: List<&2, U32>, +b: List<&2, U32>, +c: List<&2, U32>, +n: Nat) -> {Key.agree(a, c, n) == True{}: Bool} -> {
  Key.agree(b, c, n) == True{}: Bool
} -> {Key.agree(a, b, n) == True{}: Bool}:
  h1 => h2 => Equal.trans(
    Bool,
    Key.agree(a, b, n),
    Bits.agree_n(n, Key.bits(a), Key.bits(b)),
    True{},
    Key.agree_bits(a, b, n),
    Bits.agree_n_trans(Key.bits(a), Key.bits(c), Key.bits(b), n)(
      Equal.trans(Bool, Bits.agree_n(n, Key.bits(a), Key.bits(c)), Key.agree(a, c, n), True{}, Equal.sym(Bool, Key.agree(a, c, n), Bits.agree_n(n, Key.bits(a), Key.bits(c)), Key.agree_bits(a, c, n)), h1)
    )(
      Equal.trans(
        Bool,
        Bits.agree_n(n, Key.bits(c), Key.bits(b)),
        Bits.agree_n(n, Key.bits(b), Key.bits(c)),
        True{},
        Bits.agree_n_sym(Key.bits(c), Key.bits(b), n),
        Equal.trans(Bool, Bits.agree_n(n, Key.bits(b), Key.bits(c)), Key.agree(b, c, n), True{}, Equal.sym(Bool, Key.agree(b, c, n), Bits.agree_n(n, Key.bits(b), Key.bits(c)), Key.agree_bits(b, c, n)), h2)
      )
    )
  )

# a first difference before pos does not agree on pos bits
def Crit.above_agree(d: Maybe<&2, Nat>, +pos: Nat) -> {Crit.above(d, pos) == True{}: Bool} -> {Bits.agree(d, pos) == False{}: Bool}:
  match d:
    case None{}:
      h => Empty.absurd({True{} == False{}: Bool}, Shared.Bool.false_ne_true(h))
    case Some{+x}:
      h => Crit.false_of(Nat.is_le(pos, x))(t => Crit.clash(Nat.is_lt(x, pos), True{}, False{}, h, Shared.Nat.le_nlt(pos, x)(t), Shared.Bool.true_ne_false))

# a well formed fork holds no key that does not agree with its rep before its
# bit
def Crit.not_in_fork(~V: Data, +rep: List<&2, U32>, +pos: Nat, +e: Maybe<&2, V>, +z: Crit<V>, +o: Crit<V>, +lo: Nat, +k: List<&2, U32>) -> {
  Crit.wf(~V, Crit.Fork{rep, pos, e, z, o}, lo) == True{}: Bool
} -> {Key.agree(k, rep, pos) == False{}: Bool} -> {Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k) == None{}: Maybe<&2, V>}:
  +h => +n => Crit.or3_none(V, Crit.ended(V, rep, e, k), Crit.lookup(V, z, k), Crit.lookup(V, o, k))(
    Crit.ended_ne(V, rep, e, k)(
      Crit.false_of(Key.is_eq(rep, k))(
        t => Shared.Bool.false_ne_true(
          Equal.trans(
            Bool,
            False{},
            Key.agree(k, rep, pos),
            True{},
            Equal.sym(Bool, Key.agree(k, rep, pos), False{}, n),
            (
              %Equal.sym(List<&2, U32>, rep, k, Key.is_eq_sound(rep, k)(t)): {Key.agree(k, _, pos) == True{}: Bool}
              Key.agree_self(k, pos)
            )
          )
        )
      )
    )
  )(
    Crit.lookup_all(~V, ~Place, ~Place.has, z, Place{rep, pos, False{}}, k)(Crit.wf.all_z(~V, rep, pos, e, z, o, lo)(h))(
      Place.has_not_agree(rep, pos, False{}, k)(n)
    )
  )(
    Crit.lookup_all(~V, ~Place, ~Place.has, o, Place{rep, pos, True{}}, k)(Crit.wf.all_o(~V, rep, pos, e, z, o, lo)(h))(
      Place.has_not_agree(rep, pos, True{}, k)(n)
    )
  )

# a fork whose end passes p, and whose sides do, passes p
def Crit.all.intro(~V: Data, ~G: Data, ~p: G -> List<&2, U32> -> Bool, +rep: List<&2, U32>, +pos: Nat, +e: Maybe<&2, V>, +z: Crit<V>, +o: Crit<V>, +g: G) -> {
  Bool.or(Maybe.is_none(&2, V, e), p(g)(rep)) == True{}: Bool
} -> {Crit.all(~V, ~G, ~p, z, g) == True{}: Bool} -> {Crit.all(~V, ~G, ~p, o, g) == True{}: Bool} -> {
  Crit.all(~V, ~G, ~p, Crit.Fork{rep, pos, e, z, o}, g) == True{}: Bool
}:
  hh => hz => ho => Shared.List.all.if_both(Bool.or(Maybe.is_none(&2, V, e), p(g)(rep)), u => List.all.if(u2 => Crit.all(~V, ~G, ~p, o, g), Crit.all(~V, ~G, ~p, z, g)))(hh)(
    Shared.List.all.if_both(Crit.all(~V, ~G, ~p, z, g), u2 => Crit.all(~V, ~G, ~p, o, g))(hz)(ho)
  )

# an end that passes one test passes another that the first implies
def Crit.or_hit_move(-V: Data, e: Maybe<&2, V>, -x: Bool, -y: Bool) -> ({x == True{}: Bool} -> {y == True{}: Bool}) -> {
  Bool.or(Maybe.is_none(&2, V, e), x) == True{}: Bool
} -> {Bool.or(Maybe.is_none(&2, V, e), y) == True{}: Bool}:
  match e:
    case None{}:
      f => h => {==}
    case Some{v}:
      f => h => f(h)

# a key on a side of a fork at pos with rep r is on the same side of one with
# rep r2, when r2 agrees with r before pos
def Place.move(+r: List<&2, U32>, +r2: List<&2, U32>, +pos: Nat, +b: Bool, +k: List<&2, U32>) -> {Key.agree(r2, r, pos) == True{}: Bool} -> {
  Place.has(Place{r, pos, b}, k) == True{}: Bool
} -> {Place.has(Place{r2, pos, b}, k) == True{}: Bool}:
  ha => +h => Shared.List.all.if_both(Key.agree(k, r2, pos), u => Shared.Maybe.is_eq(~Bool, ~Shared.Bool.is_eq, Key.side(k, pos), Some{b}))(
    Key.agree_join(k, r2, r, pos)(Place.has_agree(r, pos, b, k)(h))(ha)
  )(Shared.List.all.if_rest(Key.agree(k, r, pos), u => Shared.Maybe.is_eq(~Bool, ~Shared.Bool.is_eq, Key.side(k, pos), Some{b}))(h))

# the keys on a side of a fork at pos with rep r are on the same side of one
# with rep r2, when r2 agrees with r before pos
def Crit.place_shift(~V: Data, m: Crit<V>, +r: List<&2, U32>, +r2: List<&2, U32>, +pos: Nat, +b: Bool) -> {Key.agree(r2, r, pos) == True{}: Bool} -> {
  Crit.all(~V, ~Place, ~Place.has, m, Place{r, pos, b}) == True{}: Bool
} -> {Crit.all(~V, ~Place, ~Place.has, m, Place{r2, pos, b}) == True{}: Bool}:
  match m:
    case Crit.Tip{}:
      ha => h => {==}
    case Crit.Leaf{+k, v}:
      ha => h => Place.move(r, r2, pos, b, k)(ha)(h)
    case Crit.Fork{+rep, +p2, +e, +z, +o}:
      +ha => +h => Crit.all.intro(~V, ~Place, ~Place.has, rep, p2, e, z, o, Place{r2, pos, b})(
        Crit.or_hit_move(V, e, Place.has(Place{r, pos, b}, rep), Place.has(Place{r2, pos, b}, rep))(Place.move(r, r2, pos, b, rep)(ha))(
          Crit.all.hit(~V, ~Place, ~Place.has, rep, p2, e, z, o, Place{r, pos, b})(h)
        )
      )(Crit.place_shift(~V, z, r, r2, pos, b)(ha)(Crit.all.z(~V, ~Place, ~Place.has, rep, p2, e, z, o, Place{r, pos, b})(h)))(
        Crit.place_shift(~V, o, r, r2, pos, b)(ha)(Crit.all.o(~V, ~Place, ~Place.has, rep, p2, e, z, o, Place{r, pos, b})(h))
      )

# a rep that is right for its end is of pos bits, or there is no end
def Crit.rep_or(-V: Data, +rep: List<&2, U32>, +pos: Nat, e: Maybe<&2, V>, -z: Crit<V>) -> {Crit.rep_ok(V, rep, pos, e, z) == True{}: Bool} -> {
  Bool.or(Maybe.is_none(&2, V, e), Nat.is_eq(List.length(&2, Bool, Key.bits(rep)), pos)) == True{}: Bool
}:
  match e:
    case None{}:
      h => {==}
    case Some{v}:
      h => h

# a fork in its one shape holds the keys of its parts
def Crit.mk_all(~V: Data, ~G: Data, ~p: G -> List<&2, U32> -> Bool, +r: List<&2, U32>, +pos: Nat, e: Maybe<&2, V>, z: Crit<V>, o: Crit<V>, +g: G) -> {
  Bool.or(Maybe.is_none(&2, V, e), p(g)(r)) == True{}: Bool
} -> {Crit.all(~V, ~G, ~p, z, g) == True{}: Bool} -> {Crit.all(~V, ~G, ~p, o, g) == True{}: Bool} -> {
  Crit.all(~V, ~G, ~p, Crit.mk(V, r, pos, e, z, o), g) == True{}: Bool
}:
  match e z o:
    case None{} Crit.Tip{} Crit.Tip{}:
      +hh => +hz => +ho => {==}
    case None{} Crit.Tip{} Crit.Leaf{+kl2, +vl2}:
      +hh => +hz => +ho => ho
    case None{} Crit.Tip{} Crit.Fork{+fr2, +fp2, +fe2, +fz2, +fo2}:
      +hh => +hz => +ho => ho
    case None{} Crit.Leaf{+kl, +vl} Crit.Tip{}:
      +hh => +hz => +ho => hz
    case None{} Crit.Leaf{+kl, +vl} Crit.Leaf{+kl2, +vl2}:
      +hh => +hz => +ho => Crit.all.intro(~V, ~G, ~p, kl, pos, None{}, Crit.Leaf{kl, vl}, Crit.Leaf{kl2, vl2}, g)({==})(hz)(ho)
    case None{} Crit.Leaf{+kl, +vl} Crit.Fork{+fr2, +fp2, +fe2, +fz2, +fo2}:
      +hh => +hz => +ho => Crit.all.intro(~V, ~G, ~p, kl, pos, None{}, Crit.Leaf{kl, vl}, Crit.Fork{fr2, fp2, fe2, fz2, fo2}, g)({==})(hz)(ho)
    case None{} Crit.Fork{+fr, +fp, +fe, +fz, +fo} Crit.Tip{}:
      +hh => +hz => +ho => hz
    case None{} Crit.Fork{+fr, +fp, +fe, +fz, +fo} Crit.Leaf{+kl2, +vl2}:
      +hh => +hz => +ho => Crit.all.intro(~V, ~G, ~p, fr, pos, None{}, Crit.Fork{fr, fp, fe, fz, fo}, Crit.Leaf{kl2, vl2}, g)({==})(hz)(ho)
    case None{} Crit.Fork{+fr, +fp, +fe, +fz, +fo} Crit.Fork{+fr2, +fp2, +fe2, +fz2, +fo2}:
      +hh => +hz => +ho => Crit.all.intro(~V, ~G, ~p, fr, pos, None{}, Crit.Fork{fr, fp, fe, fz, fo}, Crit.Fork{fr2, fp2, fe2, fz2, fo2}, g)({==})(hz)(ho)
    case Some{+v} Crit.Tip{} Crit.Tip{}:
      +hh => +hz => +ho => hh
    case Some{+v} Crit.Tip{} Crit.Leaf{+kl2, +vl2}:
      +hh => +hz => +ho => Crit.all.intro(~V, ~G, ~p, r, pos, Some{v}, Crit.Tip{}, Crit.Leaf{kl2, vl2}, g)(hh)(hz)(ho)
    case Some{+v} Crit.Tip{} Crit.Fork{+fr2, +fp2, +fe2, +fz2, +fo2}:
      +hh => +hz => +ho => Crit.all.intro(~V, ~G, ~p, r, pos, Some{v}, Crit.Tip{}, Crit.Fork{fr2, fp2, fe2, fz2, fo2}, g)(hh)(hz)(ho)
    case Some{+v} Crit.Leaf{+kl, +vl} Crit.Tip{}:
      +hh => +hz => +ho => Crit.all.intro(~V, ~G, ~p, r, pos, Some{v}, Crit.Leaf{kl, vl}, Crit.Tip{}, g)(hh)(hz)(ho)
    case Some{+v} Crit.Leaf{+kl, +vl} Crit.Leaf{+kl2, +vl2}:
      +hh => +hz => +ho => Crit.all.intro(~V, ~G, ~p, r, pos, Some{v}, Crit.Leaf{kl, vl}, Crit.Leaf{kl2, vl2}, g)(hh)(hz)(ho)
    case Some{+v} Crit.Leaf{+kl, +vl} Crit.Fork{+fr2, +fp2, +fe2, +fz2, +fo2}:
      +hh => +hz => +ho => Crit.all.intro(~V, ~G, ~p, r, pos, Some{v}, Crit.Leaf{kl, vl}, Crit.Fork{fr2, fp2, fe2, fz2, fo2}, g)(hh)(hz)(ho)
    case Some{+v} Crit.Fork{+fr, +fp, +fe, +fz, +fo} Crit.Tip{}:
      +hh => +hz => +ho => Crit.all.intro(~V, ~G, ~p, r, pos, Some{v}, Crit.Fork{fr, fp, fe, fz, fo}, Crit.Tip{}, g)(hh)(hz)(ho)
    case Some{+v} Crit.Fork{+fr, +fp, +fe, +fz, +fo} Crit.Leaf{+kl2, +vl2}:
      +hh => +hz => +ho => Crit.all.intro(~V, ~G, ~p, r, pos, Some{v}, Crit.Fork{fr, fp, fe, fz, fo}, Crit.Leaf{kl2, vl2}, g)(hh)(hz)(ho)
    case Some{+v} Crit.Fork{+fr, +fp, +fe, +fz, +fo} Crit.Fork{+fr2, +fp2, +fe2, +fz2, +fo2}:
      +hh => +hz => +ho => Crit.all.intro(~V, ~G, ~p, r, pos, Some{v}, Crit.Fork{fr, fp, fe, fz, fo}, Crit.Fork{fr2, fp2, fe2, fz2, fo2}, g)(hh)(hz)(ho)

# a fork in its one shape is well formed when its parts are
def Crit.mk_wf(~V: Data, +r: List<&2, U32>, +pos: Nat, e: Maybe<&2, V>, z: Crit<V>, o: Crit<V>, +lo: Nat) -> {Nat.is_le(lo, pos) == True{}: Bool} -> {
  Bool.or(Maybe.is_none(&2, V, e), Nat.is_eq(List.length(&2, Bool, Key.bits(r)), pos)) == True{}: Bool
} -> {Crit.all(~V, ~Place, ~Place.has, z, Place{r, pos, False{}}) == True{}: Bool} -> {
  Crit.all(~V, ~Place, ~Place.has, o, Place{r, pos, True{}}) == True{}: Bool
} -> {Crit.wf(~V, z, 1n+pos) == True{}: Bool} -> {Crit.wf(~V, o, 1n+pos) == True{}: Bool} -> {
  Crit.wf(~V, Crit.mk(V, r, pos, e, z, o), lo) == True{}: Bool
}:
  match e z o:
    case None{} Crit.Tip{} Crit.Tip{}:
      +le => +hr => +az => +ao => +wz => +wo => {==}
    case None{} Crit.Tip{} Crit.Leaf{+kl2, +vl2}:
      +le => +hr => +az => +ao => +wz => +wo => {==}
    case None{} Crit.Tip{} Crit.Fork{+fr2, +fp2, +fe2, +fz2, +fo2}:
      +le => +hr => +az => +ao => +wz => +wo => Crit.wf_mono(~V, Crit.Fork{fr2, fp2, fe2, fz2, fo2}, 1n+pos, lo)(wo)(Shared.Nat.le_succ(lo, pos)(le))
    case None{} Crit.Leaf{+kl, +vl} Crit.Tip{}:
      +le => +hr => +az => +ao => +wz => +wo => {==}
    case None{} Crit.Leaf{+kl, +vl} Crit.Leaf{+kl2, +vl2}:
      +le => +hr => +az => +ao => +wz => +wo => 
        +ag = Place.has_agree(r, pos, False{}, kl)(Crit.rep_pass(~V, ~Place, ~Place.has, Crit.Leaf{kl, vl}, 1n+pos, Place{r, pos, False{}}, r)(wz)(az)({==}))
        Crit.wf.intro(~V, kl, pos, None{}, Crit.Leaf{kl, vl}, Crit.Leaf{kl2, vl2}, lo)(le)({==})(Key.is_eq_refl(kl))(
          Crit.place_shift(~V, Crit.Leaf{kl, vl}, r, kl, pos, False{})(ag)(az)
        )(Crit.place_shift(~V, Crit.Leaf{kl2, vl2}, r, kl, pos, True{})(ag)(ao))(wz)(wo)
    case None{} Crit.Leaf{+kl, +vl} Crit.Fork{+fr2, +fp2, +fe2, +fz2, +fo2}:
      +le => +hr => +az => +ao => +wz => +wo => 
        +ag = Place.has_agree(r, pos, False{}, kl)(Crit.rep_pass(~V, ~Place, ~Place.has, Crit.Leaf{kl, vl}, 1n+pos, Place{r, pos, False{}}, r)(wz)(az)({==}))
        Crit.wf.intro(~V, kl, pos, None{}, Crit.Leaf{kl, vl}, Crit.Fork{fr2, fp2, fe2, fz2, fo2}, lo)(le)({==})(Key.is_eq_refl(kl))(
          Crit.place_shift(~V, Crit.Leaf{kl, vl}, r, kl, pos, False{})(ag)(az)
        )(Crit.place_shift(~V, Crit.Fork{fr2, fp2, fe2, fz2, fo2}, r, kl, pos, True{})(ag)(ao))(wz)(wo)
    case None{} Crit.Fork{+fr, +fp, +fe, +fz, +fo} Crit.Tip{}:
      +le => +hr => +az => +ao => +wz => +wo => Crit.wf_mono(~V, Crit.Fork{fr, fp, fe, fz, fo}, 1n+pos, lo)(wz)(Shared.Nat.le_succ(lo, pos)(le))
    case None{} Crit.Fork{+fr, +fp, +fe, +fz, +fo} Crit.Leaf{+kl2, +vl2}:
      +le => +hr => +az => +ao => +wz => +wo => 
        +ag = Place.has_agree(r, pos, False{}, fr)(Crit.rep_pass(~V, ~Place, ~Place.has, Crit.Fork{fr, fp, fe, fz, fo}, 1n+pos, Place{r, pos, False{}}, r)(wz)(az)({==}))
        Crit.wf.intro(~V, fr, pos, None{}, Crit.Fork{fr, fp, fe, fz, fo}, Crit.Leaf{kl2, vl2}, lo)(le)({==})(Key.is_eq_refl(fr))(
          Crit.place_shift(~V, Crit.Fork{fr, fp, fe, fz, fo}, r, fr, pos, False{})(ag)(az)
        )(Crit.place_shift(~V, Crit.Leaf{kl2, vl2}, r, fr, pos, True{})(ag)(ao))(wz)(wo)
    case None{} Crit.Fork{+fr, +fp, +fe, +fz, +fo} Crit.Fork{+fr2, +fp2, +fe2, +fz2, +fo2}:
      +le => +hr => +az => +ao => +wz => +wo => 
        +ag = Place.has_agree(r, pos, False{}, fr)(Crit.rep_pass(~V, ~Place, ~Place.has, Crit.Fork{fr, fp, fe, fz, fo}, 1n+pos, Place{r, pos, False{}}, r)(wz)(az)({==}))
        Crit.wf.intro(~V, fr, pos, None{}, Crit.Fork{fr, fp, fe, fz, fo}, Crit.Fork{fr2, fp2, fe2, fz2, fo2}, lo)(le)({==})(Key.is_eq_refl(fr))(
          Crit.place_shift(~V, Crit.Fork{fr, fp, fe, fz, fo}, r, fr, pos, False{})(ag)(az)
        )(Crit.place_shift(~V, Crit.Fork{fr2, fp2, fe2, fz2, fo2}, r, fr, pos, True{})(ag)(ao))(wz)(wo)
    case Some{+v} Crit.Tip{} Crit.Tip{}:
      +le => +hr => +az => +ao => +wz => +wo => {==}
    case Some{+v} Crit.Tip{} Crit.Leaf{+kl2, +vl2}:
      +le => +hr => +az => +ao => +wz => +wo => Crit.wf.intro(~V, r, pos, Some{v}, Crit.Tip{}, Crit.Leaf{kl2, vl2}, lo)(le)({==})(hr)(az)(ao)(wz)(wo)
    case Some{+v} Crit.Tip{} Crit.Fork{+fr2, +fp2, +fe2, +fz2, +fo2}:
      +le => +hr => +az => +ao => +wz => +wo => Crit.wf.intro(~V, r, pos, Some{v}, Crit.Tip{}, Crit.Fork{fr2, fp2, fe2, fz2, fo2}, lo)(le)({==})(hr)(az)(ao)(wz)(wo)
    case Some{+v} Crit.Leaf{+kl, +vl} Crit.Tip{}:
      +le => +hr => +az => +ao => +wz => +wo => Crit.wf.intro(~V, r, pos, Some{v}, Crit.Leaf{kl, vl}, Crit.Tip{}, lo)(le)({==})(hr)(az)(ao)(wz)(wo)
    case Some{+v} Crit.Leaf{+kl, +vl} Crit.Leaf{+kl2, +vl2}:
      +le => +hr => +az => +ao => +wz => +wo => Crit.wf.intro(~V, r, pos, Some{v}, Crit.Leaf{kl, vl}, Crit.Leaf{kl2, vl2}, lo)(le)({==})(hr)(az)(ao)(wz)(wo)
    case Some{+v} Crit.Leaf{+kl, +vl} Crit.Fork{+fr2, +fp2, +fe2, +fz2, +fo2}:
      +le => +hr => +az => +ao => +wz => +wo => Crit.wf.intro(~V, r, pos, Some{v}, Crit.Leaf{kl, vl}, Crit.Fork{fr2, fp2, fe2, fz2, fo2}, lo)(le)({==})(hr)(az)(ao)(wz)(wo)
    case Some{+v} Crit.Fork{+fr, +fp, +fe, +fz, +fo} Crit.Tip{}:
      +le => +hr => +az => +ao => +wz => +wo => Crit.wf.intro(~V, r, pos, Some{v}, Crit.Fork{fr, fp, fe, fz, fo}, Crit.Tip{}, lo)(le)({==})(hr)(az)(ao)(wz)(wo)
    case Some{+v} Crit.Fork{+fr, +fp, +fe, +fz, +fo} Crit.Leaf{+kl2, +vl2}:
      +le => +hr => +az => +ao => +wz => +wo => Crit.wf.intro(~V, r, pos, Some{v}, Crit.Fork{fr, fp, fe, fz, fo}, Crit.Leaf{kl2, vl2}, lo)(le)({==})(hr)(az)(ao)(wz)(wo)
    case Some{+v} Crit.Fork{+fr, +fp, +fe, +fz, +fo} Crit.Fork{+fr2, +fp2, +fe2, +fz2, +fo2}:
      +le => +hr => +az => +ao => +wz => +wo => Crit.wf.intro(~V, r, pos, Some{v}, Crit.Fork{fr, fp, fe, fz, fo}, Crit.Fork{fr2, fp2, fe2, fz2, fo2}, lo)(le)({==})(hr)(az)(ao)(wz)(wo)

# a map with no entry is well formed
law Crit.new_wf:
  for ~V: Data
  {Crit.wf(~V, Crit.new(V), 0n) == True{}: Bool}

def Crit.new_wf(ty):
  {==}

# a list that is empty is []
def Crit.empty_of(xs: List<&2, Bool>) -> {List.is_empty(&2, Bool, xs) == True{}: Bool} -> {xs == []: List<&2, Bool>}:
  match xs:
    case Nil{}:
      h => {==}
    case Con{x, r}:
      h => Empty.absurd({x <> r == []: List<&2, Bool>}, Shared.Bool.false_ne_true(h))

# a choice whose test is True is its value
def Crit.when_true(-V: Data, +b: Bool, -k: Unit -> Maybe<&2, V>) -> {b == True{}: Bool} -> {
  Shared.Maybe.when(V, b, k) == k(Unit{}): Maybe<&2, V>
}:
  h =>
    %Equal.sym(Bool, b, True{}, h): {Shared.Maybe.when(V, _, k) == k(Unit{}): Maybe<&2, V>}
    {==}

# an entry holds its own key
def Crit.leaf_self(-V: Data, +k: List<&2, U32>, +v: V) -> {Crit.lookup(V, Crit.Leaf{k, v}, k) == Some{v}: Maybe<&2, V>}:
  Crit.when_true(V, Key.is_eq(k, k), u => Some{v})(Key.is_eq_refl(k))

# two reads of which the first is nothing hold no key in common
def Crit.disj_left(-V: Data, a: Maybe<&2, V>, -b: Maybe<&2, V>) -> {a == None{}: Maybe<&2, V>} -> {
  Bool.or(Maybe.is_none(&2, V, a), Maybe.is_none(&2, V, b)) == True{}: Bool
}:
  match a:
    case None{}:
      h => {==}
    case Some{x}:
      h => Empty.absurd({Maybe.is_none(&2, V, b) == True{}: Bool}, Crit.some_ne_none(V, x, h))

# two reads of which the second is nothing hold no key in common
def Crit.disj_right(-V: Data, +a: Maybe<&2, V>, b: Maybe<&2, V>) -> {b == None{}: Maybe<&2, V>} -> {
  Bool.or(Maybe.is_none(&2, V, a), Maybe.is_none(&2, V, b)) == True{}: Bool
}:
  match b:
    case None{}:
      h => Shared.Bool.or_true_right(Maybe.is_none(&2, V, a))
    case Some{x}:
      h => Empty.absurd({Bool.or(Maybe.is_none(&2, V, a), False{}) == True{}: Bool}, Crit.some_ne_none(V, x, h))

# k's side at pos, from a cursor at pos that is not done, is its bit
def Crit.side_cur(+k: List<&2, U32>, +pos: Nat, +c2: Cur) -> {Cur.bits(c2) == List.drop(&2, Bool, Key.bits(k), pos): List<&2, Bool>} -> {
  Cur.done(c2) == False{}: Bool
} -> {Key.side(k, pos) == Some{Cur.bit(c2)}: Maybe<&2, Bool>}:
  +h2 => t1 => Equal.trans(
    Maybe<&2, Bool>,
    Key.side(k, pos),
    Bits.head(List.drop(&2, Bool, Key.bits(k), pos)),
    Some{Cur.bit(c2)},
    Crit.side_drop(k, pos, List.drop(&2, Bool, Key.bits(k), pos))({==}),
    Equal.sym(
      Maybe<&2, Bool>,
      Some{Cur.bit(c2)},
      Bits.head(List.drop(&2, Bool, Key.bits(k), pos)),
      Equal.trans(
        Maybe<&2, Bool>,
        Some{Cur.bit(c2)},
        Some{Shared.List.head_or(Bool, List.drop(&2, Bool, Key.bits(k), pos), False{})},
        Bits.head(List.drop(&2, Bool, Key.bits(k), pos)),
        Equal.cong(Bool, Maybe<&2, Bool>, b => Some{b}, Cur.bit(c2), Shared.List.head_or(Bool, List.drop(&2, Bool, Key.bits(k), pos), False{}), Crit.bit_of(c2, List.drop(&2, Bool, Key.bits(k), pos))(h2)),
        Key.side_bits.some(
          List.drop(&2, Bool, Key.bits(k), pos),
          Equal.trans(
            Bool,
            List.is_empty(&2, Bool, List.drop(&2, Bool, Key.bits(k), pos)),
            Cur.done(c2),
            False{},
            Equal.sym(Bool, Cur.done(c2), List.is_empty(&2, Bool, List.drop(&2, Bool, Key.bits(k), pos)), Crit.done_of(c2, List.drop(&2, Bool, Key.bits(k), pos))(h2)),
            t1
          )
        )
      )
    )
  )

# k's bits from pos, from a cursor at pos that is done, are none
def Crit.nil_of_done(+k: List<&2, U32>, +pos: Nat, +c2: Cur) -> {Cur.bits(c2) == List.drop(&2, Bool, Key.bits(k), pos): List<&2, Bool>} -> {
  Cur.done(c2) == True{}: Bool
} -> {List.drop(&2, Bool, Key.bits(k), pos) == []: List<&2, Bool>}:
  h2 => t1 => Crit.empty_of(List.drop(&2, Bool, Key.bits(k), pos))(
    Equal.trans(
      Bool,
      List.is_empty(&2, Bool, List.drop(&2, Bool, Key.bits(k), pos)),
      Cur.done(c2),
      True{},
      Equal.sym(Bool, Cur.done(c2), List.is_empty(&2, Bool, List.drop(&2, Bool, Key.bits(k), pos)), Crit.done_of(c2, List.drop(&2, Bool, Key.bits(k), pos))(h2)),
      t1
    )
  )

# a well formed fork holds no k on the side that k's bit at pos is not
def Crit.off_side(~V: Data, +rep: List<&2, U32>, +pos: Nat, +x: Crit<V>, +b: Bool, +k: List<&2, U32>, +c2: Cur) -> {
  Crit.all(~V, ~Place, ~Place.has, x, Place{rep, pos, b}) == True{}: Bool
} -> {Cur.bits(c2) == List.drop(&2, Bool, Key.bits(k), pos): List<&2, Bool>} -> {Cur.done(c2) == False{}: Bool} -> {
  Shared.Bool.is_eq(Cur.bit(c2), b) == False{}: Bool
} -> {Crit.lookup(V, x, k) == None{}: Maybe<&2, V>}:
  a => h2 => t1 => hb => Crit.lookup_all(~V, ~Place, ~Place.has, x, Place{rep, pos, b}, k)(a)(
    Place.has_not(rep, pos, b, k, Some{Cur.bit(c2)}, Crit.side_cur(k, pos, c2)(h2)(t1), hb)
  )

# a well formed fork holds no k on either side, when k ends at pos
def Crit.no_side(~V: Data, +rep: List<&2, U32>, +pos: Nat, +x: Crit<V>, +b: Bool, +k: List<&2, U32>) -> {
  Crit.all(~V, ~Place, ~Place.has, x, Place{rep, pos, b}) == True{}: Bool
} -> {List.drop(&2, Bool, Key.bits(k), pos) == []: List<&2, Bool>} -> {Crit.lookup(V, x, k) == None{}: Maybe<&2, V>}:
  a => hd => Crit.lookup_all(~V, ~Place, ~Place.has, x, Place{rep, pos, b}, k)(a)(Place.has_not(rep, pos, b, k, None{}, Crit.side_drop(k, pos, [])(hd), {==}))

# the end of a fork, read at a key that goes on past its bit, is nothing
def Crit.ended_long(-V: Data, +rep: List<&2, U32>, +pos: Nat, e: Maybe<&2, V>, -z: Crit<V>, +k: List<&2, U32>, d: List<&2, Bool>) -> {
  Crit.rep_ok(V, rep, pos, e, z) == True{}: Bool
} -> {List.drop(&2, Bool, Key.bits(k), pos) == d: List<&2, Bool>} -> {List.is_empty(&2, Bool, d) == False{}: Bool} -> {
  Crit.ended(V, rep, e, k) == None{}: Maybe<&2, V>
}:
  match d:
    case Nil{}:
      hr => hd => he => Empty.absurd({Crit.ended(V, rep, e, k) == None{}: Maybe<&2, V>}, Shared.Bool.true_ne_false(he))
    case Con{+x, +r}:
      hr => hd => he => Crit.ended_past(V, rep, pos, e, z, k, x, r)(hr)(hd)

# the end of a fork, read at a key k that ends at its bit and differs from
# its rep nowhere before, is its end
def Crit.ended_self(-V: Data, +rep: List<&2, U32>, +pos: Nat, e: Maybe<&2, V>, -z: Crit<V>, +k: List<&2, U32>) -> {
  Crit.rep_ok(V, rep, pos, e, z) == True{}: Bool
} -> {List.drop(&2, Bool, Key.bits(k), pos) == []: List<&2, Bool>} -> {Crit.above(Key.diff(k, rep), pos) == False{}: Bool} -> {
  Crit.ended(V, rep, e, k) == e: Maybe<&2, V>
}:
  match e:
    case None{}:
      hr => hd => ha => {==}
    case Some{w}:
      hr => hd => ha => Crit.when_true(V, Key.is_eq(rep, k), u => Some{w})(Crit.end_is(rep, pos, k)(hr)(hd)(ha))

# the end of a fork, read at a key q other than a key k that ends at its bit
# and differs from its rep nowhere before, is nothing
def Crit.ended_done(-V: Data, +rep: List<&2, U32>, +pos: Nat, e: Maybe<&2, V>, -z: Crit<V>, +k: List<&2, U32>, +q: List<&2, U32>) -> {
  Crit.rep_ok(V, rep, pos, e, z) == True{}: Bool
} -> {List.drop(&2, Bool, Key.bits(k), pos) == []: List<&2, Bool>} -> {Crit.above(Key.diff(k, rep), pos) == False{}: Bool} -> {
  Key.is_eq(q, k) == False{}: Bool
} -> {Crit.ended(V, rep, e, q) == None{}: Maybe<&2, V>}:
  match e:
    case None{}:
      hr => hd => ha => hq => {==}
    case Some{w}:
      hr => hd => ha => hq => Crit.ended_ne(V, rep, Some{w}, q)(Key.ne_of_eq(rep, k, q)(Crit.end_is(rep, pos, k)(hr)(hd)(ha))(hq))

# the first bit where k differs from the rep of a fork, where a read of k is
# done, is not above it
def Crit.done_above(
  -V: Data,
  +rep: List<&2, U32>,
  +pos: Nat,
  +e: Maybe<&2, V>,
  +z: Crit<V>,
  +o: Crit<V>,
  +at: Nat,
  +c: Cur,
  +k: List<&2, U32>,
  +d: Maybe<&2, Nat>,
  +r: Maybe<&2, List<&2, U32>>,
  +n: List<&2, U32>
) -> {Maybe.or(&2, List<&2, U32>, Crit.near(V, Crit.Fork{rep, pos, e, z, o}, at, c), r) == Some{n}: Maybe<&2, List<&2, U32>>} -> {
  d == Key.diff(k, n): Maybe<&2, Nat>
} -> {Crit.above(d, pos) == False{}: Bool} -> {Cur.done(Cur.skip(Nat.sub(pos, at), c)) == True{}: Bool} -> {
  Crit.above(Key.diff(k, rep), pos) == False{}: Bool
}:
  hn => hd => ha => t1 =>
    %Equal.sym(
      List<&2, U32>,
      rep,
      n,
      Crit.or_done(List<&2, U32>, Crit.near(V, Crit.Fork{rep, pos, e, z, o}, at, c), rep, r, n)(Crit.near_done(V, rep, pos, e, z, o, at, c)(t1))(hn)
    ): {Crit.above(Key.diff(k, _), pos) == False{}: Bool}
    %hd: {Crit.above(_, pos) == False{}: Bool}
    ha

# the key that a read of a side reaches, once a read of the fork goes there
def Crit.near_child(
  -V: Data,
  +rep: List<&2, U32>,
  +pos: Nat,
  +e: Maybe<&2, V>,
  +z: Crit<V>,
  +o: Crit<V>,
  +at: Nat,
  +c: Cur,
  +b: Bool,
  +r: Maybe<&2, List<&2, U32>>,
  +n: List<&2, U32>
) -> {Maybe.or(&2, List<&2, U32>, Crit.near(V, Crit.Fork{rep, pos, e, z, o}, at, c), r) == Some{n}: Maybe<&2, List<&2, U32>>} -> {
  Cur.done(Cur.skip(Nat.sub(pos, at), c)) == False{}: Bool
} -> {Cur.bit(Cur.skip(Nat.sub(pos, at), c)) == b: Bool} -> {
  Maybe.or(&2, List<&2, U32>, Crit.near(V, Bool.pick(Crit<V>, b, o, z), 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c))), Some{rep})
    == Some{n}: Maybe<&2, List<&2, U32>>
}:
  hn => t1 => t2 => Crit.or_step(
    List<&2, U32>,
    Crit.near(V, Crit.Fork{rep, pos, e, z, o}, at, c),
    Crit.near(V, Bool.pick(Crit<V>, b, o, z), 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c))),
    rep,
    r,
    n
  )(Crit.near_side(V, rep, pos, e, z, o, at, c, b)(t1)(t2))(hn)

# Crit.put_other at a fork that holds k's place, from the cursor c2 at its
# bit: pz and po are the writes of its sides
def Crit.put_other.fork(
  ~V: Data,
  ~f: V -> V -> V,
  +k: List<&2, U32>,
  +v: V,
  +rep: List<&2, U32>,
  +pos: Nat,
  +e: Maybe<&2, V>,
  +z: Crit<V>,
  +o: Crit<V>,
  +c2: Cur,
  +pz: Crit<V>,
  +po: Crit<V>,
  +q: List<&2, U32>
) -> {Key.is_eq(q, k) == False{}: Bool} -> ({Cur.done(c2) == True{}: Bool} -> {Crit.ended(V, rep, e, q) == None{}: Maybe<&2, V>}) -> (
  {Cur.done(c2) == False{}: Bool} -> {Cur.bit(c2) == False{}: Bool} -> {Crit.lookup(V, pz, q) == Crit.lookup(V, z, q): Maybe<&2, V>}
) -> ({Cur.done(c2) == False{}: Bool} -> {Cur.bit(c2) == True{}: Bool} -> {Crit.lookup(V, po, q) == Crit.lookup(V, o, q): Maybe<&2, V>}) -> {
  Crit.lookup(
    V,
    Shared.Bool.when(
      Crit<V>,
      Cur.done(c2),
      u => Crit.mk(V, k, pos, Some{Crit.merge(~V, ~f, e, v)}, z, o),
      u => Shared.Bool.when(Crit<V>, Cur.bit(c2), w => Crit.mk(V, rep, pos, e, z, po), w => Crit.mk(V, rep, pos, e, pz, o))
    ),
    q
  )
    == Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, q): Maybe<&2, V>
}:
  +hq => hE => iz => io => Shared.Bool.when_cases(
    Crit<V>,
    t => {Crit.lookup(V, t, q) == Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, q): Maybe<&2, V>},
    Cur.done(c2),
    u => Crit.mk(V, k, pos, Some{Crit.merge(~V, ~f, e, v)}, z, o),
    u => Shared.Bool.when(Crit<V>, Cur.bit(c2), w => Crit.mk(V, rep, pos, e, z, po), w => Crit.mk(V, rep, pos, e, pz, o)),
    t1 => Equal.trans(
      Maybe<&2, V>,
      Crit.lookup(V, Crit.mk(V, k, pos, Some{Crit.merge(~V, ~f, e, v)}, z, o), q),
      Maybe.or(&2, V, Crit.ended(V, k, Some{Crit.merge(~V, ~f, e, v)}, q), Maybe.or(&2, V, Crit.lookup(V, z, q), Crit.lookup(V, o, q))),
      Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, q),
      Crit.mk_lookup(V, k, pos, Some{Crit.merge(~V, ~f, e, v)}, z, o, q),
      Equal.trans(
        Maybe<&2, V>,
        Maybe.or(&2, V, Crit.ended(V, k, Some{Crit.merge(~V, ~f, e, v)}, q), Maybe.or(&2, V, Crit.lookup(V, z, q), Crit.lookup(V, o, q))),
        Maybe.or(&2, V, Crit.lookup(V, z, q), Crit.lookup(V, o, q)),
        Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, q),
        Equal.cong(
          Maybe<&2, V>,
          Maybe<&2, V>,
          t => Maybe.or(&2, V, t, Maybe.or(&2, V, Crit.lookup(V, z, q), Crit.lookup(V, o, q))),
          Crit.ended(V, k, Some{Crit.merge(~V, ~f, e, v)}, q),
          None{},
          Crit.when_false(V, Key.is_eq(k, q), u => Some{Crit.merge(~V, ~f, e, v)})(Key.ne_sym(q, k)(hq))
        ),
        Crit.or_none_first(V, Crit.ended(V, rep, e, q), Maybe.or(&2, V, Crit.lookup(V, z, q), Crit.lookup(V, o, q)))(hE(t1))
      )
    ),
    +t1 => Shared.Bool.when_cases(
      Crit<V>,
      t => {Crit.lookup(V, t, q) == Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, q): Maybe<&2, V>},
      Cur.bit(c2),
      w => Crit.mk(V, rep, pos, e, z, po),
      w => Crit.mk(V, rep, pos, e, pz, o),
      t2 => Equal.trans(
        Maybe<&2, V>,
        Crit.lookup(V, Crit.mk(V, rep, pos, e, z, po), q),
        Maybe.or(&2, V, Crit.ended(V, rep, e, q), Maybe.or(&2, V, Crit.lookup(V, z, q), Crit.lookup(V, po, q))),
        Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, q),
        Crit.mk_lookup(V, rep, pos, e, z, po, q),
        Equal.cong(
          Maybe<&2, V>,
          Maybe<&2, V>,
          t => Maybe.or(&2, V, Crit.ended(V, rep, e, q), Maybe.or(&2, V, Crit.lookup(V, z, q), t)),
          Crit.lookup(V, po, q),
          Crit.lookup(V, o, q),
          io(t1)(t2)
        )
      ),
      t2 => Equal.trans(
        Maybe<&2, V>,
        Crit.lookup(V, Crit.mk(V, rep, pos, e, pz, o), q),
        Maybe.or(&2, V, Crit.ended(V, rep, e, q), Maybe.or(&2, V, Crit.lookup(V, pz, q), Crit.lookup(V, o, q))),
        Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, q),
        Crit.mk_lookup(V, rep, pos, e, pz, o, q),
        Equal.cong(
          Maybe<&2, V>,
          Maybe<&2, V>,
          t => Maybe.or(&2, V, Crit.ended(V, rep, e, q), Maybe.or(&2, V, t, Crit.lookup(V, o, q))),
          Crit.lookup(V, pz, q),
          Crit.lookup(V, z, q),
          iz(t1)(t2)
        )
      )
    )
  )

# a fork of an entry of k and a map, read at another key, is the map
def Crit.join_other(-V: Data, +k: List<&2, U32>, +v: V, +y: Crit<V>, +d: Nat, +q: List<&2, U32>) -> {Key.is_eq(q, k) == False{}: Bool} -> {
  Crit.lookup(V, Crit.join(V, Crit.Leaf{k, v}, y, d), q) == Crit.lookup(V, y, q): Maybe<&2, V>
}:
  +hq => Equal.trans(
    Maybe<&2, V>,
    Crit.lookup(V, Crit.join(V, Crit.Leaf{k, v}, y, d), q),
    Maybe.or(&2, V, Crit.lookup(V, Crit.Leaf{k, v}, q), Crit.lookup(V, y, q)),
    Crit.lookup(V, y, q),
    Crit.join_lookup(V, Crit.Leaf{k, v}, y, d, q)(
      Crit.disj_left(V, Crit.lookup(V, Crit.Leaf{k, v}, q), Crit.lookup(V, y, q))(
        Crit.when_false(V, Key.is_eq(k, q), u => Some{v})(Key.ne_sym(q, k)(hq))
      )
    ),
    Equal.cong(
      Maybe<&2, V>,
      Maybe<&2, V>,
      t => Maybe.or(&2, V, t, Crit.lookup(V, y, q)),
      Crit.lookup(V, Crit.Leaf{k, v}, q),
      None{},
      Crit.when_false(V, Key.is_eq(k, q), u => Some{v})(Key.ne_sym(q, k)(hq))
    )
  )

# the key k2 of an entry that a write of k reaches where k differs nowhere is
# not a key q other than k
def Crit.leaf_ne(+k: List<&2, U32>, +n: List<&2, U32>, +k2: List<&2, U32>, +q: List<&2, U32>, +d: Maybe<&2, Nat>) -> {
  Some{k2} == Some{n}: Maybe<&2, List<&2, U32>>
} -> {d == Key.diff(k, n): Maybe<&2, Nat>} -> {Maybe.is_none(&2, Nat, d) == True{}: Bool} -> {Key.is_eq(q, k) == False{}: Bool} -> {
  Key.is_eq(k2, q) == False{}: Bool
}:
  hn => hd => t1 => hq =>
    %Equal.trans(
      List<&2, U32>,
      k,
      n,
      k2,
      Key.diff_none(k, n)(Equal.trans(Maybe<&2, Nat>, Key.diff(k, n), d, None{}, Equal.sym(Maybe<&2, Nat>, d, Key.diff(k, n), hd), Crit.none_of(d)(t1))),
      Equal.sym(List<&2, U32>, k2, n, Shared.Maybe.some_inj(List<&2, U32>, k2, n, hn))
    ): {Key.is_eq(_, q) == False{}: Bool}
    Key.ne_sym(q, k)(hq)
  

# a write of k into a well formed map, read from k's cursor, keeps each other
# key; n is the key that the read reaches (r when m is empty), and d where k
# differs from it
def Crit.put_other(
  ~V: Data,
  ~f: V -> V -> V,
  m: Crit<V>,
  +lo: Nat,
  +at: Nat,
  +c: Cur,
  +k: List<&2, U32>,
  +v: V,
  +d: Maybe<&2, Nat>,
  +r: Maybe<&2, List<&2, U32>>,
  +n: List<&2, U32>,
  +q: List<&2, U32>
) -> {Crit.wf(~V, m, lo) == True{}: Bool} -> {Nat.is_le(at, lo) == True{}: Bool} -> {
  Cur.bits(c) == List.drop(&2, Bool, Key.bits(k), at): List<&2, Bool>
} -> {Maybe.or(&2, List<&2, U32>, Crit.near(V, m, at, c), r) == Some{n}: Maybe<&2, List<&2, U32>>} -> {d == Key.diff(k, n): Maybe<&2, Nat>} -> {
  Key.is_eq(q, k) == False{}: Bool
} -> {Crit.lookup(V, Crit.put(~V, ~f, m, at, c, k, v, d), q) == Crit.lookup(V, m, q): Maybe<&2, V>}:
  match m:
    case Crit.Tip{}:
      h => l => hc => hn => hd => hq => Crit.when_false(V, Key.is_eq(k, q), u => Some{v})(Key.ne_sym(q, k)(hq))
    case Crit.Leaf{+k2, +w}:
      h => l => hc => +hn => +hd => +hq => Shared.Bool.when_cases(
        Crit<V>,
        t => {Crit.lookup(V, t, q) == Crit.lookup(V, Crit.Leaf{k2, w}, q): Maybe<&2, V>},
        Maybe.is_none(&2, Nat, d),
        u => Crit.Leaf{k2, f(w, v)},
        u => Crit.join(V, Crit.Leaf{k, v}, Crit.Leaf{k2, w}, Maybe.default(&2, Nat, d, 0n)),
        +t1 =>
          +fk = Crit.leaf_ne(k, n, k2, q, d)(hn)(hd)(t1)(hq)
          Equal.trans(
            Maybe<&2, V>,
            Crit.lookup(V, Crit.Leaf{k2, f(w, v)}, q),
            None{},
            Crit.lookup(V, Crit.Leaf{k2, w}, q),
            Crit.when_false(V, Key.is_eq(k2, q), u => Some{f(w, v)})(fk),
            Equal.sym(Maybe<&2, V>, Crit.lookup(V, Crit.Leaf{k2, w}, q), None{}, Crit.when_false(V, Key.is_eq(k2, q), u => Some{w})(fk))
          ),
        +t1 => Crit.join_other(V, k, v, Crit.Leaf{k2, w}, Maybe.default(&2, Nat, d, 0n), q)(hq)
      )
    case Crit.Fork{+rep, +pos, +e, +z, +o}:
      +h => +l => +hc => +hn => +hd => +hq =>
        +h2 = Crit.skip_at(k, at, pos, c)(Shared.Nat.le_trans(at, lo, pos)(l)(Crit.wf.le(~V, rep, pos, e, z, o, lo)(h)))(hc)
        Shared.Bool.when_cases(
          Crit<V>,
          t => {Crit.lookup(V, t, q) == Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, q): Maybe<&2, V>},
          Crit.above(d, pos),
          u => Crit.join(V, Crit.Leaf{k, v}, Crit.Fork{rep, pos, e, z, o}, Maybe.default(&2, Nat, d, 0n)),
          u => Crit.put.fork(
            ~V,
            ~f,
            k,
            v,
            rep,
            pos,
            e,
            z,
            o,
            Cur.skip(Nat.sub(pos, at), c),
            z2 => Crit.put(~V, ~f, z, 1n+pos, z2, k, v, d),
            o2 => Crit.put(~V, ~f, o, 1n+pos, o2, k, v, d)
          ),
          +ta => Crit.join_other(V, k, v, Crit.Fork{rep, pos, e, z, o}, Maybe.default(&2, Nat, d, 0n), q)(hq),
          +ta => Crit.put_other.fork(
            ~V,
            ~f,
            k,
            v,
            rep,
            pos,
            e,
            z,
            o,
            Cur.skip(Nat.sub(pos, at), c),
            Crit.put(~V, ~f, z, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), k, v, d),
            Crit.put(~V, ~f, o, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), k, v, d),
            q
          )(hq)(
            +t1 => Crit.ended_done(V, rep, pos, e, z, k, q)(Crit.wf.rep_ok(~V, rep, pos, e, z, o, lo)(h))(Crit.nil_of_done(k, pos, Cur.skip(Nat.sub(pos, at), c))(h2)(t1))(
              Crit.done_above(V, rep, pos, e, z, o, at, c, k, d, r, n)(hn)(hd)(ta)(t1)
            )(hq)
          )(
            +t1 => +t2 => Crit.put_other(~V, ~f, z, 1n+pos, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), k, v, d, Some{rep}, n, q)(
              Crit.wf.wf_z(~V, rep, pos, e, z, o, lo)(h)
            )(Shared.Nat.le_refl(1n+pos))(Crit.next_at(k, pos, Cur.skip(Nat.sub(pos, at), c))(h2))(
              Crit.near_child(V, rep, pos, e, z, o, at, c, False{}, r, n)(hn)(t1)(t2)
            )(hd)(hq)
          )(
            +t1 => +t2 => Crit.put_other(~V, ~f, o, 1n+pos, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), k, v, d, Some{rep}, n, q)(
              Crit.wf.wf_o(~V, rep, pos, e, z, o, lo)(h)
            )(Shared.Nat.le_refl(1n+pos))(Crit.next_at(k, pos, Cur.skip(Nat.sub(pos, at), c))(h2))(
              Crit.near_child(V, rep, pos, e, z, o, at, c, True{}, r, n)(hn)(t1)(t2)
            )(hd)(hq)
          )
        )

# the key k2 of an entry that a write of k reaches, where k differs from it
# nowhere, is k
def Crit.leaf_eq(+k: List<&2, U32>, +n: List<&2, U32>, +k2: List<&2, U32>, +d: Maybe<&2, Nat>) -> {Some{k2} == Some{n}: Maybe<&2, List<&2, U32>>} -> {
  d == Key.diff(k, n): Maybe<&2, Nat>
} -> {Maybe.is_none(&2, Nat, d) == True{}: Bool} -> {Key.is_eq(k2, k) == True{}: Bool}:
  hn => hd => t1 =>
    %Equal.trans(
      List<&2, U32>,
      k,
      n,
      k2,
      Key.diff_none(k, n)(Equal.trans(Maybe<&2, Nat>, Key.diff(k, n), d, None{}, Equal.sym(Maybe<&2, Nat>, d, Key.diff(k, n), hd), Crit.none_of(d)(t1))),
      Equal.sym(List<&2, U32>, k2, n, Shared.Maybe.some_inj(List<&2, U32>, k2, n, hn))
    ): {Key.is_eq(_, k) == True{}: Bool}
    Key.is_eq_refl(k)

# the key k2 of an entry that a write of k reaches, where k differs from it,
# is not k
def Crit.leaf_ne2(+k: List<&2, U32>, +n: List<&2, U32>, +k2: List<&2, U32>, +d: Maybe<&2, Nat>) -> {Some{k2} == Some{n}: Maybe<&2, List<&2, U32>>} -> {
  d == Key.diff(k, n): Maybe<&2, Nat>
} -> {Maybe.is_none(&2, Nat, d) == False{}: Bool} -> {Key.is_eq(k2, k) == False{}: Bool}:
  +hn => +hd => +t1 => Crit.false_of(Key.is_eq(k2, k))(
    t => Crit.clash(
      Maybe.is_none(&2, Nat, d),
      True{},
      False{},
      Equal.cong(
        Maybe<&2, Nat>,
        Bool,
        x => Maybe.is_none(&2, Nat, x),
        d,
        None{},
        Equal.trans(
          Maybe<&2, Nat>,
          d,
          Key.diff(k, n),
          None{},
          hd,
          (
            %Equal.trans(
              List<&2, U32>,
              k,
              k2,
              n,
              Equal.sym(List<&2, U32>, k2, k, Key.is_eq_sound(k2, k)(t)),
              Shared.Maybe.some_inj(List<&2, U32>, k2, n, hn)
            ): {Key.diff(k, _) == None{}: Maybe<&2, Nat>}
            Key.diff_self(k)
          )
        )
      ),
      t1,
      Shared.Bool.true_ne_false
    )
  )

# a fork of an entry of k and a map that lacks k binds k to the entry's value
def Crit.join_new(~V: Data, ~f: V -> V -> V, +k: List<&2, U32>, +v: V, +y: Crit<V>, +x: Nat) -> {Crit.lookup(V, y, k) == None{}: Maybe<&2, V>} -> {
  Crit.lookup(V, Crit.join(V, Crit.Leaf{k, v}, y, x), k) == Some{Crit.merge(~V, ~f, Crit.lookup(V, y, k), v)}: Maybe<&2, V>
}:
  +nl => Equal.trans(
    Maybe<&2, V>,
    Crit.lookup(V, Crit.join(V, Crit.Leaf{k, v}, y, x), k),
    Maybe.or(&2, V, Crit.lookup(V, Crit.Leaf{k, v}, k), Crit.lookup(V, y, k)),
    Some{Crit.merge(~V, ~f, Crit.lookup(V, y, k), v)},
    Crit.join_lookup(V, Crit.Leaf{k, v}, y, x, k)(Crit.disj_right(V, Crit.lookup(V, Crit.Leaf{k, v}, k), Crit.lookup(V, y, k))(nl)),
    (
      %Equal.sym(Maybe<&2, V>, Crit.lookup(V, y, k), None{}, nl): {
        Maybe.or(&2, V, Crit.lookup(V, Crit.Leaf{k, v}, k), _) == Some{Crit.merge(~V, ~f, _, v)}: Maybe<&2, V>
      }
      %Equal.sym(Maybe<&2, V>, Crit.lookup(V, Crit.Leaf{k, v}, k), Some{v}, Crit.leaf_self(V, k, v)): {Maybe.or(&2, V, _, None{}) == Some{v}: Maybe<&2, V>}
      {==}
    )
  )

# a key that differs from the key that a read of a well formed fork reaches
# before the fork's bit does not agree with its rep before the bit
def Crit.above_out(
  ~V: Data,
  +rep: List<&2, U32>,
  +pos: Nat,
  +e: Maybe<&2, V>,
  +z: Crit<V>,
  +o: Crit<V>,
  +lo: Nat,
  +at: Nat,
  +c: Cur,
  +k: List<&2, U32>,
  +d: Maybe<&2, Nat>,
  +r: Maybe<&2, List<&2, U32>>,
  +n: List<&2, U32>
) -> {Crit.wf(~V, Crit.Fork{rep, pos, e, z, o}, lo) == True{}: Bool} -> {
  Maybe.or(&2, List<&2, U32>, Crit.near(V, Crit.Fork{rep, pos, e, z, o}, at, c), r) == Some{n}: Maybe<&2, List<&2, U32>>
} -> {d == Key.diff(k, n): Maybe<&2, Nat>} -> {Crit.above(d, pos) == True{}: Bool} -> {Key.agree(k, rep, pos) == False{}: Bool}:
  +h => +hn => +hd => +ta => Crit.false_of(Key.agree(k, rep, pos))(
    t => Crit.clash(
      Key.agree(k, n, pos),
      True{},
      False{},
      Key.agree_join(k, n, rep, pos)(t)(
        Crit.near_agree(~V, rep, pos, e, z, o, lo, at, c, n)(h)(
          Equal.trans(
            Maybe<&2, List<&2, U32>>,
            Crit.near(V, Crit.Fork{rep, pos, e, z, o}, at, c),
            Maybe.or(&2, List<&2, U32>, Crit.near(V, Crit.Fork{rep, pos, e, z, o}, at, c), r),
            Some{n},
            Equal.sym(
              Maybe<&2, List<&2, U32>>,
              Maybe.or(&2, List<&2, U32>, Crit.near(V, Crit.Fork{rep, pos, e, z, o}, at, c), r),
              Crit.near(V, Crit.Fork{rep, pos, e, z, o}, at, c),
              Crit.or_of_some(List<&2, U32>, Crit.near(V, Crit.Fork{rep, pos, e, z, o}, at, c), r)(Crit.near_some(V, rep, pos, e, z, o, at, c))
            ),
            hn
          )
        )
      ),
      (
        %hd: {Bits.agree(_, pos) == False{}: Bool}
        Crit.above_agree(d, pos)(ta)
      ),
      Shared.Bool.true_ne_false
    )
  )

# Crit.put_new at a fork that holds k's place, from the cursor c2 at its
# bit: pz and po are the writes of its sides
def Crit.put_new.fork(
  ~V: Data,
  ~f: V -> V -> V,
  +k: List<&2, U32>,
  +v: V,
  +rep: List<&2, U32>,
  +pos: Nat,
  +e: Maybe<&2, V>,
  +z: Crit<V>,
  +o: Crit<V>,
  +c2: Cur,
  +pz: Crit<V>,
  +po: Crit<V>
) -> ({Cur.done(c2) == True{}: Bool} -> {Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k) == e: Maybe<&2, V>}) -> (
  {Cur.done(c2) == False{}: Bool} -> {Crit.ended(V, rep, e, k) == None{}: Maybe<&2, V>}
) -> ({Cur.done(c2) == False{}: Bool} -> {Cur.bit(c2) == True{}: Bool} -> {Crit.lookup(V, z, k) == None{}: Maybe<&2, V>}) -> (
  {Cur.done(c2) == False{}: Bool} -> {Cur.bit(c2) == False{}: Bool} -> {Crit.lookup(V, o, k) == None{}: Maybe<&2, V>}
) -> (
  {Cur.done(c2) == False{}: Bool} -> {Cur.bit(c2) == False{}: Bool} -> {
    Crit.lookup(V, pz, k) == Some{Crit.merge(~V, ~f, Crit.lookup(V, z, k), v)}: Maybe<&2, V>
  }
) -> (
  {Cur.done(c2) == False{}: Bool} -> {Cur.bit(c2) == True{}: Bool} -> {
    Crit.lookup(V, po, k) == Some{Crit.merge(~V, ~f, Crit.lookup(V, o, k), v)}: Maybe<&2, V>
  }
) -> {
  Crit.lookup(
    V,
    Shared.Bool.when(
      Crit<V>,
      Cur.done(c2),
      u => Crit.mk(V, k, pos, Some{Crit.merge(~V, ~f, e, v)}, z, o),
      u => Shared.Bool.when(Crit<V>, Cur.bit(c2), w => Crit.mk(V, rep, pos, e, z, po), w => Crit.mk(V, rep, pos, e, pz, o))
    ),
    k
  )
    == Some{Crit.merge(~V, ~f, Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k), v)}: Maybe<&2, V>
}:
  hE => hN => hz1 => ho0 => iz => io => Shared.Bool.when_cases(
    Crit<V>,
    t => {Crit.lookup(V, t, k) == Some{Crit.merge(~V, ~f, Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k), v)}: Maybe<&2, V>},
    Cur.done(c2),
    u => Crit.mk(V, k, pos, Some{Crit.merge(~V, ~f, e, v)}, z, o),
    u => Shared.Bool.when(Crit<V>, Cur.bit(c2), w => Crit.mk(V, rep, pos, e, z, po), w => Crit.mk(V, rep, pos, e, pz, o)),
    t1 => Equal.trans(
      Maybe<&2, V>,
      Crit.lookup(V, Crit.mk(V, k, pos, Some{Crit.merge(~V, ~f, e, v)}, z, o), k),
      Maybe.or(&2, V, Crit.ended(V, k, Some{Crit.merge(~V, ~f, e, v)}, k), Maybe.or(&2, V, Crit.lookup(V, z, k), Crit.lookup(V, o, k))),
      Some{Crit.merge(~V, ~f, Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k), v)},
      Crit.mk_lookup(V, k, pos, Some{Crit.merge(~V, ~f, e, v)}, z, o, k),
      (
        %Equal.sym(Bool, Key.is_eq(k, k), True{}, Key.is_eq_refl(k)): {
          Maybe.or(
            &2,
            V,
            Shared.Maybe.when(V, _, u => Some{Crit.merge(~V, ~f, e, v)}),
            Maybe.or(&2, V, Crit.lookup(V, z, k), Crit.lookup(V, o, k))
          )
            == Some{Crit.merge(~V, ~f, Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k), v)}: Maybe<&2, V>
        }
        %Equal.sym(Maybe<&2, V>, Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k), e, hE(t1)): {
          Some{Crit.merge(~V, ~f, e, v)} == Some{Crit.merge(~V, ~f, _, v)}: Maybe<&2, V>
        }
        {==}
      )
    ),
    +t1 =>
      +n1 = hN(t1)
      Shared.Bool.when_cases(
      Crit<V>,
      t => {Crit.lookup(V, t, k) == Some{Crit.merge(~V, ~f, Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k), v)}: Maybe<&2, V>},
      Cur.bit(c2),
      w => Crit.mk(V, rep, pos, e, z, po),
      w => Crit.mk(V, rep, pos, e, pz, o),
      +t2 =>
        +zz = hz1(t1)(t2)
        Equal.trans(
        Maybe<&2, V>,
        Crit.lookup(V, Crit.mk(V, rep, pos, e, z, po), k),
        Maybe.or(&2, V, Crit.ended(V, rep, e, k), Maybe.or(&2, V, Crit.lookup(V, z, k), Crit.lookup(V, po, k))),
        Some{Crit.merge(~V, ~f, Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k), v)},
        Crit.mk_lookup(V, rep, pos, e, z, po, k),
        Equal.trans(
          Maybe<&2, V>,
          Maybe.or(&2, V, Crit.ended(V, rep, e, k), Maybe.or(&2, V, Crit.lookup(V, z, k), Crit.lookup(V, po, k))),
          Crit.lookup(V, po, k),
          Some{Crit.merge(~V, ~f, Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k), v)},
          Crit.or_third(V, Crit.ended(V, rep, e, k), Crit.lookup(V, z, k), Crit.lookup(V, po, k))(n1)(zz),
          Equal.trans(
            Maybe<&2, V>,
            Crit.lookup(V, po, k),
            Some{Crit.merge(~V, ~f, Crit.lookup(V, o, k), v)},
            Some{Crit.merge(~V, ~f, Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k), v)},
            io(t1)(t2),
            Equal.cong(
              Maybe<&2, V>,
              Maybe<&2, V>,
              t => Some{Crit.merge(~V, ~f, t, v)},
              Crit.lookup(V, o, k),
              Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k),
              Equal.sym(
                Maybe<&2, V>,
                Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k),
                Crit.lookup(V, o, k),
                Crit.or_third(V, Crit.ended(V, rep, e, k), Crit.lookup(V, z, k), Crit.lookup(V, o, k))(n1)(zz)
              )
            )
          )
        )
      ),
      +t2 =>
        +oo = ho0(t1)(t2)
        Equal.trans(
        Maybe<&2, V>,
        Crit.lookup(V, Crit.mk(V, rep, pos, e, pz, o), k),
        Maybe.or(&2, V, Crit.ended(V, rep, e, k), Maybe.or(&2, V, Crit.lookup(V, pz, k), Crit.lookup(V, o, k))),
        Some{Crit.merge(~V, ~f, Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k), v)},
        Crit.mk_lookup(V, rep, pos, e, pz, o, k),
        Equal.trans(
          Maybe<&2, V>,
          Maybe.or(&2, V, Crit.ended(V, rep, e, k), Maybe.or(&2, V, Crit.lookup(V, pz, k), Crit.lookup(V, o, k))),
          Crit.lookup(V, pz, k),
          Some{Crit.merge(~V, ~f, Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k), v)},
          Crit.or_second(V, Crit.ended(V, rep, e, k), Crit.lookup(V, pz, k), Crit.lookup(V, o, k))(n1)(oo),
          Equal.trans(
            Maybe<&2, V>,
            Crit.lookup(V, pz, k),
            Some{Crit.merge(~V, ~f, Crit.lookup(V, z, k), v)},
            Some{Crit.merge(~V, ~f, Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k), v)},
            iz(t1)(t2),
            Equal.cong(
              Maybe<&2, V>,
              Maybe<&2, V>,
              t => Some{Crit.merge(~V, ~f, t, v)},
              Crit.lookup(V, z, k),
              Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k),
              Equal.sym(
                Maybe<&2, V>,
                Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k),
                Crit.lookup(V, z, k),
                Crit.or_second(V, Crit.ended(V, rep, e, k), Crit.lookup(V, z, k), Crit.lookup(V, o, k))(n1)(oo)
              )
            )
          )
        )
      )
    )
  )

# a write of k into a well formed map, read from k's cursor, binds k to v,
# or to f of the old value and v; n is the key that the read reaches (r when
# m is empty), and d where k differs from it
def Crit.put_new(
  ~V: Data,
  ~f: V -> V -> V,
  m: Crit<V>,
  +lo: Nat,
  +at: Nat,
  +c: Cur,
  +k: List<&2, U32>,
  +v: V,
  +d: Maybe<&2, Nat>,
  +r: Maybe<&2, List<&2, U32>>,
  +n: List<&2, U32>
) -> {Crit.wf(~V, m, lo) == True{}: Bool} -> {Nat.is_le(at, lo) == True{}: Bool} -> {
  Cur.bits(c) == List.drop(&2, Bool, Key.bits(k), at): List<&2, Bool>
} -> {Maybe.or(&2, List<&2, U32>, Crit.near(V, m, at, c), r) == Some{n}: Maybe<&2, List<&2, U32>>} -> {d == Key.diff(k, n): Maybe<&2, Nat>} -> {
  Crit.lookup(V, Crit.put(~V, ~f, m, at, c, k, v, d), k) == Some{Crit.merge(~V, ~f, Crit.lookup(V, m, k), v)}: Maybe<&2, V>
}:
  match m:
    case Crit.Tip{}:
      h => l => hc => hn => hd => Crit.leaf_self(V, k, v)
    case Crit.Leaf{+k2, +w}:
      h => l => hc => +hn => +hd => Shared.Bool.when_cases(
        Crit<V>,
        t => {Crit.lookup(V, t, k) == Some{Crit.merge(~V, ~f, Crit.lookup(V, Crit.Leaf{k2, w}, k), v)}: Maybe<&2, V>},
        Maybe.is_none(&2, Nat, d),
        u => Crit.Leaf{k2, f(w, v)},
        u => Crit.join(V, Crit.Leaf{k, v}, Crit.Leaf{k2, w}, Maybe.default(&2, Nat, d, 0n)),
        t1 =>
          %Equal.sym(Bool, Key.is_eq(k2, k), True{}, Crit.leaf_eq(k, n, k2, d)(hn)(hd)(t1)): {
            Shared.Maybe.when(V, _, u => Some{f(w, v)}) == Some{Crit.merge(~V, ~f, Shared.Maybe.when(V, _, u => Some{w}), v)}: Maybe<&2, V>
          }
          {==},
        t1 => Crit.join_new(~V, ~f, k, v, Crit.Leaf{k2, w}, Maybe.default(&2, Nat, d, 0n))(
          Crit.when_false(V, Key.is_eq(k2, k), u => Some{w})(Crit.leaf_ne2(k, n, k2, d)(hn)(hd)(t1))
        )
      )
    case Crit.Fork{+rep, +pos, +e, +z, +o}:
      +h => +l => +hc => +hn => +hd =>
        +h2 = Crit.skip_at(k, at, pos, c)(Shared.Nat.le_trans(at, lo, pos)(l)(Crit.wf.le(~V, rep, pos, e, z, o, lo)(h)))(hc)
        Shared.Bool.when_cases(
          Crit<V>,
          t => {Crit.lookup(V, t, k) == Some{Crit.merge(~V, ~f, Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k), v)}: Maybe<&2, V>},
          Crit.above(d, pos),
          u => Crit.join(V, Crit.Leaf{k, v}, Crit.Fork{rep, pos, e, z, o}, Maybe.default(&2, Nat, d, 0n)),
          u => Crit.put.fork(
            ~V,
            ~f,
            k,
            v,
            rep,
            pos,
            e,
            z,
            o,
            Cur.skip(Nat.sub(pos, at), c),
            z2 => Crit.put(~V, ~f, z, 1n+pos, z2, k, v, d),
            o2 => Crit.put(~V, ~f, o, 1n+pos, o2, k, v, d)
          ),
          +ta => Crit.join_new(~V, ~f, k, v, Crit.Fork{rep, pos, e, z, o}, Maybe.default(&2, Nat, d, 0n))(
            Crit.not_in_fork(~V, rep, pos, e, z, o, lo, k)(h)(Crit.above_out(~V, rep, pos, e, z, o, lo, at, c, k, d, r, n)(h)(hn)(hd)(ta))
          ),
          +ta => Crit.put_new.fork(
            ~V,
            ~f,
            k,
            v,
            rep,
            pos,
            e,
            z,
            o,
            Cur.skip(Nat.sub(pos, at), c),
            Crit.put(~V, ~f, z, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), k, v, d),
            Crit.put(~V, ~f, o, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), k, v, d)
          )(
            +t1 =>
              +nil = Crit.nil_of_done(k, pos, Cur.skip(Nat.sub(pos, at), c))(h2)(t1)
              Equal.trans(
                Maybe<&2, V>,
                Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k),
                Crit.ended(V, rep, e, k),
                e,
                Crit.or_first(V, Crit.ended(V, rep, e, k), Crit.lookup(V, z, k), Crit.lookup(V, o, k))(
                  Crit.no_side(~V, rep, pos, z, False{}, k)(Crit.wf.all_z(~V, rep, pos, e, z, o, lo)(h))(nil)
                )(Crit.no_side(~V, rep, pos, o, True{}, k)(Crit.wf.all_o(~V, rep, pos, e, z, o, lo)(h))(nil)),
                Crit.ended_self(V, rep, pos, e, z, k)(Crit.wf.rep_ok(~V, rep, pos, e, z, o, lo)(h))(nil)(
                  Crit.done_above(V, rep, pos, e, z, o, at, c, k, d, r, n)(hn)(hd)(ta)(t1)
                )
              )
          )(
            t1 => Crit.ended_long(V, rep, pos, e, z, k, List.drop(&2, Bool, Key.bits(k), pos))(Crit.wf.rep_ok(~V, rep, pos, e, z, o, lo)(h))({==})(
              Equal.trans(
                Bool,
                List.is_empty(&2, Bool, List.drop(&2, Bool, Key.bits(k), pos)),
                Cur.done(Cur.skip(Nat.sub(pos, at), c)),
                False{},
                Equal.sym(
                  Bool,
                  Cur.done(Cur.skip(Nat.sub(pos, at), c)),
                  List.is_empty(&2, Bool, List.drop(&2, Bool, Key.bits(k), pos)),
                  Crit.done_of(Cur.skip(Nat.sub(pos, at), c), List.drop(&2, Bool, Key.bits(k), pos))(h2)
                ),
                t1
              )
            )
          )(
            t1 => t2 => Crit.off_side(~V, rep, pos, z, False{}, k, Cur.skip(Nat.sub(pos, at), c))(Crit.wf.all_z(~V, rep, pos, e, z, o, lo)(h))(h2)(t1)((
              %Equal.sym(Bool, Cur.bit(Cur.skip(Nat.sub(pos, at), c)), True{}, t2): {Shared.Bool.is_eq(_, False{}) == False{}: Bool}
              {==}
            ))
          )(
            t1 => t2 => Crit.off_side(~V, rep, pos, o, True{}, k, Cur.skip(Nat.sub(pos, at), c))(Crit.wf.all_o(~V, rep, pos, e, z, o, lo)(h))(h2)(t1)((
              %Equal.sym(Bool, Cur.bit(Cur.skip(Nat.sub(pos, at), c)), False{}, t2): {Shared.Bool.is_eq(_, True{}) == False{}: Bool}
              {==}
            ))
          )(
            +t1 => +t2 => Crit.put_new(~V, ~f, z, 1n+pos, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), k, v, d, Some{rep}, n)(
              Crit.wf.wf_z(~V, rep, pos, e, z, o, lo)(h)
            )(Shared.Nat.le_refl(1n+pos))(Crit.next_at(k, pos, Cur.skip(Nat.sub(pos, at), c))(h2))(
              Crit.near_child(V, rep, pos, e, z, o, at, c, False{}, r, n)(hn)(t1)(t2)
            )(hd)
          )(
            +t1 => +t2 => Crit.put_new(~V, ~f, o, 1n+pos, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), k, v, d, Some{rep}, n)(
              Crit.wf.wf_o(~V, rep, pos, e, z, o, lo)(h)
            )(Shared.Nat.le_refl(1n+pos))(Crit.next_at(k, pos, Cur.skip(Nat.sub(pos, at), c))(h2))(
              Crit.near_child(V, rep, pos, e, z, o, at, c, True{}, r, n)(hn)(t1)(t2)
            )(hd)
          )
        )

# no number is below 0
def Crit.lt_zero(a: Nat) -> {Nat.is_lt(a, 0n) == False{}: Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

# a difference that is some is some of its value
def Crit.some_of(d: Maybe<&2, Nat>) -> {Maybe.is_none(&2, Nat, d) == False{}: Bool} -> {d == Some{Maybe.default(&2, Nat, d, 0n)}: Maybe<&2, Nat>}:
  match d:
    case None{}:
      h => Empty.absurd({None{} == Some{0n}: Maybe<&2, Nat>}, Shared.Bool.true_ne_false(h))
    case Some{x}:
      h => {==}

# a first difference before pos is some
def Crit.above_some(d: Maybe<&2, Nat>, +pos: Nat) -> {Crit.above(d, pos) == True{}: Bool} -> {d == Some{Maybe.default(&2, Nat, d, 0n)}: Maybe<&2, Nat>}:
  match d:
    case None{}:
      h => Empty.absurd({None{} == Some{0n}: Maybe<&2, Nat>}, Shared.Bool.false_ne_true(h))
    case Some{x}:
      h => {==}

# a first difference at x that is before pos: x is before pos
def Crit.above_lt(d: Maybe<&2, Nat>, +pos: Nat, +x: Nat) -> {d == Some{x}: Maybe<&2, Nat>} -> {Crit.above(d, pos) == True{}: Bool} -> {
  Nat.is_lt(x, pos) == True{}: Bool
}:
  sd => ta =>
    %sd: {Crit.above(_, pos) == True{}: Bool}
    ta

# a first difference that is not before pos agrees on pos bits
def Crit.not_above_agree(d: Maybe<&2, Nat>, +pos: Nat) -> {Crit.above(d, pos) == False{}: Bool} -> {Bits.agree(d, pos) == True{}: Bool}:
  match d:
    case None{}:
      h => {==}
    case Some{+x}:
      h => Shared.Nat.nlt_le(x, pos)(h)

# keys that differ first at x agree on x bits
def Crit.agree_at(+k: List<&2, U32>, +n: List<&2, U32>, +d: Maybe<&2, Nat>, +x: Nat) -> {d == Key.diff(k, n): Maybe<&2, Nat>} -> {
  d == Some{x}: Maybe<&2, Nat>
} -> {Key.agree(k, n, x) == True{}: Bool}:
  hd => sd =>
    %hd: {Bits.agree(_, x) == True{}: Bool}
    %Equal.sym(Maybe<&2, Nat>, d, Some{x}, sd): {Bits.agree(_, x) == True{}: Bool}
    Shared.Nat.le_refl(x)

# agreement is the same either way round
def Key.agree_sym(+a: List<&2, U32>, +b: List<&2, U32>, +n: Nat) -> {Key.agree(a, b, n) == True{}: Bool} -> {Key.agree(b, a, n) == True{}: Bool}:
  h => Key.agree_join(b, a, b, n)(Key.agree_self(b, n))(h)

# keys that agree on n bits agree on fewer
def Key.agree_le(+a: List<&2, U32>, +b: List<&2, U32>, +m: Nat, +n: Nat) -> {Nat.is_le(m, n) == True{}: Bool} -> {Key.agree(a, b, n) == True{}: Bool} -> {
  Key.agree(a, b, m) == True{}: Bool
}:
  l => h => Equal.trans(
    Bool,
    Key.agree(a, b, m),
    Bits.agree_n(m, Key.bits(a), Key.bits(b)),
    True{},
    Key.agree_bits(a, b, m),
    Bits.agree_n_le(Key.bits(a), Key.bits(b), m, n)(l)(
      Equal.trans(Bool, Bits.agree_n(n, Key.bits(a), Key.bits(b)), Key.agree(a, b, n), True{}, Equal.sym(Bool, Key.agree(a, b, n), Bits.agree_n(n, Key.bits(a), Key.bits(b)), Key.agree_bits(a, b, n)), h)
    )
  )

# keys that agree on 1 + x bits have the same bit at x
def Key.at_eq(+a: List<&2, U32>, +b: List<&2, U32>, +x: Nat) -> {Key.agree(a, b, 1n+x) == True{}: Bool} -> {
  Bits.at(Key.bits(a), x) == Bits.at(Key.bits(b), x): Maybe<&2, Bool>
}:
  h => Shared.Maybe.is_eq_sound(~Bool, ~Shared.Bool.is_eq, x1 => y1 => Shared.Bool.is_eq_sound(x1, y1), Bits.at(Key.bits(a), x), Bits.at(Key.bits(b), x))(
    Shared.Bool.and_true_right(
      Bits.agree_n(x, Key.bits(a), Key.bits(b)),
      Shared.Maybe.is_eq(~Bool, ~Shared.Bool.is_eq, Bits.at(Key.bits(a), x), Bits.at(Key.bits(b), x))
    )(
      Equal.trans(
        Bool,
        Bool.and(Bits.agree_n(x, Key.bits(a), Key.bits(b)), Shared.Maybe.is_eq(~Bool, ~Shared.Bool.is_eq, Bits.at(Key.bits(a), x), Bits.at(Key.bits(b), x))),
        Bits.agree_n(1n+x, Key.bits(a), Key.bits(b)),
        True{},
        Equal.sym(
          Bool,
          Bits.agree_n(1n+x, Key.bits(a), Key.bits(b)),
          Bool.and(Bits.agree_n(x, Key.bits(a), Key.bits(b)), Shared.Maybe.is_eq(~Bool, ~Shared.Bool.is_eq, Bits.at(Key.bits(a), x), Bits.at(Key.bits(b), x))),
          Bits.agree_n_succ(Key.bits(a), Key.bits(b), x)
        ),
        Equal.trans(
          Bool,
          Bits.agree_n(1n+x, Key.bits(a), Key.bits(b)),
          Key.agree(a, b, 1n+x),
          True{},
          Equal.sym(Bool, Key.agree(a, b, 1n+x), Bits.agree_n(1n+x, Key.bits(a), Key.bits(b)), Key.agree_bits(a, b, 1n+x)),
          h
        )
      )
    )
  )

# keys that agree on pos bits and have the same side at pos agree on 1 + pos
def Key.agree_succ(+a: List<&2, U32>, +b: List<&2, U32>, +pos: Nat, +s: Bool) -> {Key.agree(a, b, pos) == True{}: Bool} -> {
  Key.side(a, pos) == Some{s}: Maybe<&2, Bool>
} -> {Key.side(b, pos) == Some{s}: Maybe<&2, Bool>} -> {Key.agree(a, b, 1n+pos) == True{}: Bool}:
  h => sa => sb => Equal.trans(
    Bool,
    Key.agree(a, b, 1n+pos),
    Bits.agree_n(1n+pos, Key.bits(a), Key.bits(b)),
    True{},
    Key.agree_bits(a, b, 1n+pos),
    Equal.trans(
      Bool,
      Bits.agree_n(1n+pos, Key.bits(a), Key.bits(b)),
      Bool.and(Bits.agree_n(pos, Key.bits(a), Key.bits(b)), Shared.Maybe.is_eq(~Bool, ~Shared.Bool.is_eq, Bits.at(Key.bits(a), pos), Bits.at(Key.bits(b), pos))),
      True{},
      Bits.agree_n_succ(Key.bits(a), Key.bits(b), pos),
      (
        %Equal.sym(
          Bool,
          Bits.agree_n(pos, Key.bits(a), Key.bits(b)),
          True{},
          Equal.trans(Bool, Bits.agree_n(pos, Key.bits(a), Key.bits(b)), Key.agree(a, b, pos), True{}, Equal.sym(Bool, Key.agree(a, b, pos), Bits.agree_n(pos, Key.bits(a), Key.bits(b)), Key.agree_bits(a, b, pos)), h)
        ): {Bool.and(_, Shared.Maybe.is_eq(~Bool, ~Shared.Bool.is_eq, Bits.at(Key.bits(a), pos), Bits.at(Key.bits(b), pos))) == True{}: Bool}
        %Equal.sym(
          Maybe<&2, Bool>,
          Bits.at(Key.bits(a), pos),
          Some{s},
          Equal.trans(Maybe<&2, Bool>, Bits.at(Key.bits(a), pos), Key.side(a, pos), Some{s}, Equal.sym(Maybe<&2, Bool>, Key.side(a, pos), Bits.at(Key.bits(a), pos), Key.side_bits(a, pos)), sa)
        ): {Shared.Maybe.is_eq(~Bool, ~Shared.Bool.is_eq, _, Bits.at(Key.bits(b), pos)) == True{}: Bool}
        %Equal.sym(
          Maybe<&2, Bool>,
          Bits.at(Key.bits(b), pos),
          Some{s},
          Equal.trans(Maybe<&2, Bool>, Bits.at(Key.bits(b), pos), Key.side(b, pos), Some{s}, Equal.sym(Maybe<&2, Bool>, Key.side(b, pos), Bits.at(Key.bits(b), pos), Key.side_bits(b, pos)), sb)
        ): {Shared.Maybe.is_eq(~Bool, ~Shared.Bool.is_eq, Some{s}, _) == True{}: Bool}
        Shared.Bool.is_eq_refl(s)
      )
    )
  )

# a list with bits from n on is at least n long
def Crit.drop_some_le(xs: List<&2, Bool>, +n: Nat) -> {List.is_empty(&2, Bool, List.drop(&2, Bool, xs, n)) == False{}: Bool} -> {
  Nat.is_le(n, List.length(&2, Bool, xs)) == True{}: Bool
}:
  match xs n:
    case Nil{} m:
      h => Empty.absurd({Nat.is_le(m, 0n) == True{}: Bool}, Shared.Bool.true_ne_false(h))
    case Con{x, t} 0n:
      h => {==}
    case Con{x, t} 1n+p:
      h => Crit.drop_some_le(t, p)(h)

# a list with no bits from n on is at most n long
def Crit.drop_nil_len(xs: List<&2, Bool>, +n: Nat) -> {List.drop(&2, Bool, xs, n) == []: List<&2, Bool>} -> {
  Nat.is_le(List.length(&2, Bool, xs), n) == True{}: Bool
}:
  match xs n:
    case Nil{} m:
      h => Shared.Nat.le_zero(m)
    case Con{x, t} 0n:
      h => Empty.absurd(
        {Nat.is_le(1n+List.length(&2, Bool, t), 0n) == True{}: Bool},
        Shared.Bool.false_ne_true(Equal.cong(List<&2, Bool>, Bool, l => List.is_empty(&2, Bool, l), x <> t, [], h))
      )
    case Con{x, t} 1n+p:
      h => Crit.drop_nil_len(t, p)(h)

# a list longer than x has bits from x on
def Crit.len_drop(xs: List<&2, Bool>, +x: Nat) -> {Nat.is_lt(x, List.length(&2, Bool, xs)) == True{}: Bool} -> {
  List.is_empty(&2, Bool, List.drop(&2, Bool, xs, x)) == False{}: Bool
}:
  match xs x:
    case Nil{} m:
      h => Empty.absurd({True{} == False{}: Bool}, Shared.Bool.false_ne_true(Equal.trans(Bool, False{}, Nat.is_lt(m, 0n), True{}, Equal.sym(Bool, Nat.is_lt(m, 0n), False{}, Crit.lt_zero(m)), h)))
    case Con{y, t} 0n:
      h => {==}
    case Con{y, t} 1n+p:
      h => Crit.len_drop(t, p)(h)

# bits that agree with bits at least n long on n bits are at least n long
def Crit.agree_len(n: Nat, a: List<&2, Bool>, b: List<&2, Bool>) -> {Bits.agree_n(n, a, b) == True{}: Bool} -> {
  Nat.is_le(n, List.length(&2, Bool, b)) == True{}: Bool
} -> {Nat.is_le(n, List.length(&2, Bool, a)) == True{}: Bool}:
  match n a b:
    case 0n x y:
      h => l => Shared.Nat.le_zero(List.length(&2, Bool, x))
    case 1n+(+p) Nil{} Nil{}:
      h => l => l
    case 1n+(+p) Con{x, +ra} Con{y, +rb}:
      h => l => Crit.agree_len(p, ra, rb)(Shared.Bool.and_true_right(Shared.Bool.is_eq(x, y), Bits.agree_n(p, ra, rb))(h))(l)
    case 1n+(+p) Nil{} Con{y, rb}:
      h => l => Empty.absurd({Nat.is_le(1n+p, 0n) == True{}: Bool}, Shared.Bool.false_ne_true(h))
    case 1n+(+p) Con{x, ra} Nil{}:
      h => l => Empty.absurd({Nat.is_le(1n+p, 1n+List.length(&2, Bool, ra)) == True{}: Bool}, Shared.Bool.false_ne_true(h))

# numbers at most each other are the same
def Crit.le_eq(a: Nat, b: Nat) -> {Nat.is_le(a, b) == True{}: Bool} -> {Nat.is_le(b, a) == True{}: Bool} -> {Nat.is_eq(a, b) == True{}: Bool}:
  match a b:
    case 0n 0n:
      h1 => h2 => {==}
    case 0n 1n+q:
      h1 => h2 => Empty.absurd({Nat.is_eq(0n, 1n+q) == True{}: Bool}, Shared.Bool.false_ne_true(h2))
    case 1n+p 0n:
      h1 => h2 => Empty.absurd({Nat.is_eq(1n+p, 0n) == True{}: Bool}, Shared.Bool.false_ne_true(h1))
    case 1n+p 1n+q:
      Crit.le_eq(p, q)

# x below p: x + 1 is at most p
def Crit.lt_le_succ(x: Nat, p: Nat) -> {Nat.is_lt(x, p) == True{}: Bool} -> {Nat.is_le(1n+x, p) == True{}: Bool}:
  match x p:
    case 0n 0n:
      h => Empty.absurd({Nat.is_le(1n, 0n) == True{}: Bool}, Shared.Bool.false_ne_true(h))
    case 0n 1n+q:
      h => Shared.Nat.le_zero(q)
    case 1n+a 0n:
      h => Empty.absurd({Nat.is_le(2n+a, 0n) == True{}: Bool}, Shared.Bool.false_ne_true(h))
    case 1n+a 1n+q:
      Crit.lt_le_succ(a, q)

# a list with a head is not empty
def Crit.head_ne(xs: List<&2, Bool>, -b: Bool) -> {Bits.head(xs) == Some{b}: Maybe<&2, Bool>} -> {List.is_empty(&2, Bool, xs) == False{}: Bool}:
  match xs:
    case Nil{}:
      h => Empty.absurd({True{} == False{}: Bool}, Shared.Maybe.none_ne_some(Bool, b, h))
    case Con{x, r}:
      h => {==}

# an "or" whose right side holds holds
def Crit.or_right(a: Bool, +b: Bool) -> {b == True{}: Bool} -> {Bool.or(a, b) == True{}: Bool}:
  h =>
    %Equal.sym(Bool, b, True{}, h): {Bool.or(a, _) == True{}: Bool}
    Shared.Bool.or_true_right(a)

# a bit that is not True is False
def Crit.ne_true(b: Bool) -> {Shared.Bool.is_eq(True{}, b) == False{}: Bool} -> {b == False{}: Bool}:
  match b:
    case True{}:
      h => Empty.absurd({True{} == False{}: Bool}, Shared.Bool.true_ne_false(h))
    case False{}:
      h => {==}

# a bit that is not False is True
def Crit.ne_false(b: Bool) -> {Shared.Bool.is_eq(False{}, b) == False{}: Bool} -> {b == True{}: Bool}:
  match b:
    case True{}:
      h => {==}
    case False{}:
      h => Empty.absurd({False{} == True{}: Bool}, Shared.Bool.true_ne_false(h))

# sides that differ, once each is known
def Crit.ne_sides(+a: List<&2, U32>, +b: List<&2, U32>, +x: Nat, +sa: Maybe<&2, Bool>, +sb: Maybe<&2, Bool>) -> {
  Key.side(a, x) == sa: Maybe<&2, Bool>
} -> {Key.side(b, x) == sb: Maybe<&2, Bool>} -> {
  Shared.Maybe.is_eq(~Bool, ~Shared.Bool.is_eq, Key.side(a, x), Key.side(b, x)) == False{}: Bool
} -> {Shared.Maybe.is_eq(~Bool, ~Shared.Bool.is_eq, sa, sb) == False{}: Bool}:
  h1 => h2 => h =>
    %h1: {Shared.Maybe.is_eq(~Bool, ~Shared.Bool.is_eq, _, sb) == False{}: Bool}
    %h2: {Shared.Maybe.is_eq(~Bool, ~Shared.Bool.is_eq, Key.side(a, x), _) == False{}: Bool}
    h

# keys that differ first at x have different sides at x
def Crit.diff_sides(+a: List<&2, U32>, +b: List<&2, U32>, +x: Nat) -> {Key.diff(a, b) == Some{x}: Maybe<&2, Nat>} -> {
  Shared.Maybe.is_eq(~Bool, ~Shared.Bool.is_eq, Key.side(a, x), Key.side(b, x)) == False{}: Bool
}:
  hd =>
    %Equal.sym(Maybe<&2, Bool>, Key.side(a, x), Bits.at(Key.bits(a), x), Key.side_bits(a, x)): {
      Shared.Maybe.is_eq(~Bool, ~Shared.Bool.is_eq, _, Key.side(b, x)) == False{}: Bool
    }
    %Equal.sym(Maybe<&2, Bool>, Key.side(b, x), Bits.at(Key.bits(b), x), Key.side_bits(b, x)): {
      Shared.Maybe.is_eq(~Bool, ~Shared.Bool.is_eq, Bits.at(Key.bits(a), x), _) == False{}: Bool
    }
    Bits.diff_at(Key.bits(a), Key.bits(b), x)(
      Equal.trans(Maybe<&2, Nat>, Bits.diff(Key.bits(a), Key.bits(b)), Key.diff(a, b), Some{x}, Equal.sym(Maybe<&2, Nat>, Key.diff(a, b), Bits.diff(Key.bits(a), Key.bits(b)), Key.diff_bits(a, b)), hd)
    )

# k differs first at x from n, which has rep's bit at x: k and rep have
# different sides at x
def Crit.sides_ne(+k: List<&2, U32>, +n: List<&2, U32>, +rep: List<&2, U32>, +x: Nat) -> {Key.diff(k, n) == Some{x}: Maybe<&2, Nat>} -> {
  Bits.at(Key.bits(n), x) == Bits.at(Key.bits(rep), x): Maybe<&2, Bool>
} -> {Shared.Maybe.is_eq(~Bool, ~Shared.Bool.is_eq, Key.side(k, x), Key.side(rep, x)) == False{}: Bool}:
  hd => hat =>
    %Equal.sym(Maybe<&2, Bool>, Key.side(k, x), Bits.at(Key.bits(k), x), Key.side_bits(k, x)): {
      Shared.Maybe.is_eq(~Bool, ~Shared.Bool.is_eq, _, Key.side(rep, x)) == False{}: Bool
    }
    %Equal.sym(Maybe<&2, Bool>, Key.side(rep, x), Bits.at(Key.bits(rep), x), Key.side_bits(rep, x)): {
      Shared.Maybe.is_eq(~Bool, ~Shared.Bool.is_eq, Bits.at(Key.bits(k), x), _) == False{}: Bool
    }
    %hat: {Shared.Maybe.is_eq(~Bool, ~Shared.Bool.is_eq, Bits.at(Key.bits(k), x), _) == False{}: Bool}
    Bits.diff_at(Key.bits(k), Key.bits(n), x)(
      Equal.trans(Maybe<&2, Nat>, Bits.diff(Key.bits(k), Key.bits(n)), Key.diff(k, n), Some{x}, Equal.sym(Maybe<&2, Nat>, Key.diff(k, n), Bits.diff(Key.bits(k), Key.bits(n)), Key.diff_bits(k, n)), hd)
    )

# the side of a key at x, from its cursor at x that is not done
def Crit.side_of(+k: List<&2, U32>, +x: Nat, +b: Bool) -> {Cur.done(Key.at(k, x)) == False{}: Bool} -> {Cur.bit(Key.at(k, x)) == b: Bool} -> {
  Key.side(k, x) == Some{b}: Maybe<&2, Bool>
}:
  hd => hb =>
    %Equal.sym(Bool, Cur.done(Key.at(k, x)), False{}, hd): {
      Shared.Bool.when(Maybe<&2, Bool>, _, u => None{}, u => Some{Cur.bit(Key.at(k, x))}) == Some{b}: Maybe<&2, Bool>
    }
    %Equal.sym(Bool, Cur.bit(Key.at(k, x)), b, hb): {Some{_} == Some{b}: Maybe<&2, Bool>}
    {==}

# a key whose cursor at x is done has no bits from x on
def Crit.at_nil(+k: List<&2, U32>, +x: Nat) -> {Cur.done(Key.at(k, x)) == True{}: Bool} -> {List.drop(&2, Bool, Key.bits(k), x) == []: List<&2, Bool>}:
  h => Crit.nil_of_done(k, x, Key.at(k, x))(Cur.skip_bits(x, Cur.of(k)))(h)

# a key whose cursor at x is not done has bits from x on
def Crit.at_some(+k: List<&2, U32>, +x: Nat) -> {Cur.done(Key.at(k, x)) == False{}: Bool} -> {
  List.is_empty(&2, Bool, List.drop(&2, Bool, Key.bits(k), x)) == False{}: Bool
}:
  h => Equal.trans(
    Bool,
    List.is_empty(&2, Bool, List.drop(&2, Bool, Key.bits(k), x)),
    Cur.done(Key.at(k, x)),
    False{},
    Equal.sym(Bool, Cur.done(Key.at(k, x)), List.is_empty(&2, Bool, List.drop(&2, Bool, Key.bits(k), x)), Crit.done_of(Key.at(k, x), List.drop(&2, Bool, Key.bits(k), x))(Cur.skip_bits(x, Cur.of(k)))),
    h
  )

# a key that agrees with a fork's rep before its bit and has its side there
# is on that side
def Place.intro(+r: List<&2, U32>, +pos: Nat, +b: Bool, +k: List<&2, U32>) -> {Key.agree(k, r, pos) == True{}: Bool} -> {
  Key.side(k, pos) == Some{b}: Maybe<&2, Bool>
} -> {Place.has(Place{r, pos, b}, k) == True{}: Bool}:
  ha => hs => Shared.List.all.if_both(Key.agree(k, r, pos), u => Shared.Maybe.is_eq(~Bool, ~Shared.Bool.is_eq, Key.side(k, pos), Some{b}))(ha)((
    %Equal.sym(Maybe<&2, Bool>, Key.side(k, pos), Some{b}, hs): {Shared.Maybe.is_eq(~Bool, ~Shared.Bool.is_eq, _, Some{b}) == True{}: Bool}
    Shared.Bool.is_eq_refl(b)
  ))

# a read of a map with an entry reaches some key
def Crit.near_nontip(-V: Data, m: Crit<V>, +at: Nat, +c: Cur) -> {Crit.is_tip(V, m) == False{}: Bool} -> {
  Maybe.is_some(&2, List<&2, U32>, Crit.near(V, m, at, c)) == True{}: Bool
}:
  match m:
    case Crit.Tip{}:
      h => Empty.absurd({False{} == True{}: Bool}, Shared.Bool.true_ne_false(h))
    case Crit.Leaf{k, v}:
      h => {==}
    case Crit.Fork{+r, +p, +e, +z, +o}:
      h => Crit.near_some(V, r, p, e, z, o, at, c)

# the rep of a well formed fork is at least as long as its bit
def Crit.rep_long(~V: Data, +rep: List<&2, U32>, +pos: Nat, e: Maybe<&2, V>, +z: Crit<V>, +o: Crit<V>, +lo: Nat) -> {
  Crit.wf(~V, Crit.Fork{rep, pos, e, z, o}, lo) == True{}: Bool
} -> {Nat.is_le(pos, List.length(&2, Bool, Key.bits(rep))) == True{}: Bool}:
  match e:
    case Some{v}:
      h =>
        %Equal.sym(
          Nat,
          List.length(&2, Bool, Key.bits(rep)),
          pos,
          Shared.Nat.is_eq_sound(List.length(&2, Bool, Key.bits(rep)), pos)(Crit.wf.rep_ok(~V, rep, pos, Some{v}, z, o, lo)(h))
        ): {Nat.is_le(pos, _) == True{}: Bool}
        Shared.Nat.le_refl(pos)
    case None{}:
      +h =>
        +has = Crit.rep_pass(~V, ~Place, ~Place.has, z, 1n+pos, Place{rep, pos, False{}}, rep)(Crit.wf.wf_z(~V, rep, pos, None{}, z, o, lo)(h))(
          Crit.wf.all_z(~V, rep, pos, None{}, z, o, lo)(h)
        )(Crit.shape_none_z(V, z, o)(Crit.wf.shape(~V, rep, pos, None{}, z, o, lo)(h)))
        +se = Shared.Maybe.is_eq_sound(~Bool, ~Shared.Bool.is_eq, x1 => y1 => Shared.Bool.is_eq_sound(x1, y1), Key.side(Crit.rep(V, z, rep), pos), Some{False{}})(
          Shared.List.all.if_rest(
            Key.agree(Crit.rep(V, z, rep), rep, pos),
            u => Shared.Maybe.is_eq(~Bool, ~Shared.Bool.is_eq, Key.side(Crit.rep(V, z, rep), pos), Some{False{}})
          )(has)
        )
        %Equal.sym(List<&2, U32>, rep, Crit.rep(V, z, rep), Key.is_eq_sound(rep, Crit.rep(V, z, rep))(Crit.wf.rep_ok(~V, rep, pos, None{}, z, o, lo)(h))): {
          Nat.is_le(pos, List.length(&2, Bool, Key.bits(_))) == True{}: Bool
        }
        Crit.drop_some_le(Key.bits(Crit.rep(V, z, rep)), pos)(
          Crit.head_ne(List.drop(&2, Bool, Key.bits(Crit.rep(V, z, rep)), pos), False{})(
            Equal.trans(
              Maybe<&2, Bool>,
              Bits.head(List.drop(&2, Bool, Key.bits(Crit.rep(V, z, rep)), pos)),
              Key.side(Crit.rep(V, z, rep), pos),
              Some{False{}},
              Equal.sym(
                Maybe<&2, Bool>,
                Key.side(Crit.rep(V, z, rep), pos),
                Bits.head(List.drop(&2, Bool, Key.bits(Crit.rep(V, z, rep)), pos)),
                Crit.side_drop(Crit.rep(V, z, rep), pos, List.drop(&2, Bool, Key.bits(Crit.rep(V, z, rep)), pos))({==})
              ),
              se
            )
          )
        )

# a key that ends by pos and agrees with a well formed fork's rep before pos
# is pos bits long
def Crit.done_len(~V: Data, +rep: List<&2, U32>, +pos: Nat, +e: Maybe<&2, V>, +z: Crit<V>, +o: Crit<V>, +lo: Nat, +k: List<&2, U32>) -> {
  Crit.wf(~V, Crit.Fork{rep, pos, e, z, o}, lo) == True{}: Bool
} -> {List.drop(&2, Bool, Key.bits(k), pos) == []: List<&2, Bool>} -> {Key.agree(k, rep, pos) == True{}: Bool} -> {
  Nat.is_eq(List.length(&2, Bool, Key.bits(k)), pos) == True{}: Bool
}:
  h => hd => ha => Crit.le_eq(List.length(&2, Bool, Key.bits(k)), pos)(Crit.drop_nil_len(Key.bits(k), pos)(hd))(
    Crit.agree_len(pos, Key.bits(k), Key.bits(rep))(
      Equal.trans(Bool, Bits.agree_n(pos, Key.bits(k), Key.bits(rep)), Key.agree(k, rep, pos), True{}, Equal.sym(Bool, Key.agree(k, rep, pos), Bits.agree_n(pos, Key.bits(k), Key.bits(rep)), Key.agree_bits(k, rep, pos)), ha)
    )(Crit.rep_long(~V, rep, pos, e, z, o, lo)(h))
  )

# a well formed fork is well formed below any bit up to its own
def Crit.wf_lower(~V: Data, +rep: List<&2, U32>, +pos: Nat, +e: Maybe<&2, V>, +z: Crit<V>, +o: Crit<V>, +a: Nat, +b: Nat) -> {
  Crit.wf(~V, Crit.Fork{rep, pos, e, z, o}, a) == True{}: Bool
} -> {Nat.is_le(b, pos) == True{}: Bool} -> {Crit.wf(~V, Crit.Fork{rep, pos, e, z, o}, b) == True{}: Bool}:
  +h => l => Crit.wf.intro(~V, rep, pos, e, z, o, b)(l)(Crit.wf.shape(~V, rep, pos, e, z, o, a)(h))(Crit.wf.rep_ok(~V, rep, pos, e, z, o, a)(h))(
    Crit.wf.all_z(~V, rep, pos, e, z, o, a)(h)
  )(Crit.wf.all_o(~V, rep, pos, e, z, o, a)(h))(Crit.wf.wf_z(~V, rep, pos, e, z, o, a)(h))(Crit.wf.wf_o(~V, rep, pos, e, z, o, a)(h))

# a fork of an entry that ends at its bit and a map passes p, when both do
def Crit.join_end_all(~V: Data, ~G: Data, ~p: G -> List<&2, U32> -> Bool, +k: List<&2, U32>, +v: V, +y: Crit<V>, +x: Nat, b: Bool, +g: G) -> {
  p(g)(k) == True{}: Bool
} -> {Crit.all(~V, ~G, ~p, y, g) == True{}: Bool} -> {Crit.all(~V, ~G, ~p, Crit.join.end(V, Crit.Leaf{k, v}, y, x, b), g) == True{}: Bool}:
  match b:
    case True{}:
      hk => hy => Crit.all.intro(~V, ~G, ~p, k, x, Some{v}, Crit.Tip{}, y, g)(hk)({==})(hy)
    case False{}:
      hk => hy => Crit.all.intro(~V, ~G, ~p, k, x, Some{v}, y, Crit.Tip{}, g)(hk)(hy)({==})

# a fork of a map whose first key ends at its bit and an entry passes p,
# when both do
def Crit.join_end_all2(~V: Data, ~G: Data, ~p: G -> List<&2, U32> -> Bool, y: Crit<V>, +k: List<&2, U32>, +v: V, +x: Nat, b: Bool, +g: G) -> {
  p(g)(k) == True{}: Bool
} -> {Crit.all(~V, ~G, ~p, y, g) == True{}: Bool} -> {Crit.all(~V, ~G, ~p, Crit.join.end(V, y, Crit.Leaf{k, v}, x, b), g) == True{}: Bool}:
  match y b:
    case Crit.Leaf{+k2, +w} True{}:
      hk => hy => Crit.all.intro(~V, ~G, ~p, k2, x, Some{w}, Crit.Tip{}, Crit.Leaf{k, v}, g)(hy)({==})(hk)
    case Crit.Leaf{+k2, +w} False{}:
      hk => hy => Crit.all.intro(~V, ~G, ~p, k2, x, Some{w}, Crit.Leaf{k, v}, Crit.Tip{}, g)(hy)(hk)({==})
    case Crit.Tip{} b1:
      hk => hy => Crit.all.intro(~V, ~G, ~p, [], x, None{}, Crit.Tip{}, Crit.Leaf{k, v}, g)({==})({==})(hk)
    case Crit.Fork{+r, +q, +e, +z, +o} b1:
      hk => hy => Crit.all.intro(~V, ~G, ~p, r, x, None{}, Crit.Fork{r, q, e, z, o}, Crit.Leaf{k, v}, g)({==})(hy)(hk)

# a fork of an entry and a map passes p, when both do
def Crit.join_all(~V: Data, ~G: Data, ~p: G -> List<&2, U32> -> Bool, +k: List<&2, U32>, +v: V, +y: Crit<V>, +x: Nat, +g: G) -> {
  p(g)(k) == True{}: Bool
} -> {Crit.all(~V, ~G, ~p, y, g) == True{}: Bool} -> {Crit.all(~V, ~G, ~p, Crit.join(V, Crit.Leaf{k, v}, y, x), g) == True{}: Bool}:
  +hk => +hy => Shared.Bool.when_cases(
    Crit<V>,
    t => {Crit.all(~V, ~G, ~p, t, g) == True{}: Bool},
    Cur.done(Key.at(k, x)),
    u => Crit.join.end(V, Crit.Leaf{k, v}, y, x, Cur.bit(Key.at(Crit.rep(V, y, []), x))),
    u => Shared.Bool.when(
      Crit<V>,
      Cur.done(Key.at(Crit.rep(V, y, []), x)),
      q1 => Crit.join.end(V, y, Crit.Leaf{k, v}, x, Cur.bit(Key.at(k, x))),
      q1 => Shared.Bool.when(Crit<V>, Cur.bit(Key.at(k, x)), q2 => Crit.Fork{Crit.rep(V, y, []), x, None{}, y, Crit.Leaf{k, v}}, q2 => Crit.Fork{k, x, None{}, Crit.Leaf{k, v}, y})
    ),
    +t1 => Crit.join_end_all(~V, ~G, ~p, k, v, y, x, Cur.bit(Key.at(Crit.rep(V, y, []), x)), g)(hk)(hy),
    +t1 => Shared.Bool.when_cases(
      Crit<V>,
      t => {Crit.all(~V, ~G, ~p, t, g) == True{}: Bool},
      Cur.done(Key.at(Crit.rep(V, y, []), x)),
      q1 => Crit.join.end(V, y, Crit.Leaf{k, v}, x, Cur.bit(Key.at(k, x))),
      q1 => Shared.Bool.when(Crit<V>, Cur.bit(Key.at(k, x)), q2 => Crit.Fork{Crit.rep(V, y, []), x, None{}, y, Crit.Leaf{k, v}}, q2 => Crit.Fork{k, x, None{}, Crit.Leaf{k, v}, y}),
      +t2 => Crit.join_end_all2(~V, ~G, ~p, y, k, v, x, Cur.bit(Key.at(k, x)), g)(hk)(hy),
      +t2 => Shared.Bool.when_cases(
        Crit<V>,
        t => {Crit.all(~V, ~G, ~p, t, g) == True{}: Bool},
        Cur.bit(Key.at(k, x)),
        q2 => Crit.Fork{Crit.rep(V, y, []), x, None{}, y, Crit.Leaf{k, v}},
        q2 => Crit.Fork{k, x, None{}, Crit.Leaf{k, v}, y},
        +t3 => Crit.all.intro(~V, ~G, ~p, Crit.rep(V, y, []), x, None{}, y, Crit.Leaf{k, v}, g)({==})(hy)(hk),
        +t3 => Crit.all.intro(~V, ~G, ~p, k, x, None{}, Crit.Leaf{k, v}, y, g)({==})(hk)(hy)
      )
    )
  )

# a write of k passes p, when the map and k do
def Crit.put_all(~V: Data, ~f: V -> V -> V, ~G: Data, ~p: G -> List<&2, U32> -> Bool, m: Crit<V>, +at: Nat, +c: Cur, +k: List<&2, U32>, +v: V, +d: Maybe<&2, Nat>, +g: G) -> {
  Crit.all(~V, ~G, ~p, m, g) == True{}: Bool
} -> {p(g)(k) == True{}: Bool} -> {Crit.all(~V, ~G, ~p, Crit.put(~V, ~f, m, at, c, k, v, d), g) == True{}: Bool}:
  match m:
    case Crit.Tip{}:
      h => hk => hk
    case Crit.Leaf{+k2, +w}:
      +h => +hk => Shared.Bool.when_cases(
        Crit<V>,
        t => {Crit.all(~V, ~G, ~p, t, g) == True{}: Bool},
        Maybe.is_none(&2, Nat, d),
        u => Crit.Leaf{k2, f(w, v)},
        u => Crit.join(V, Crit.Leaf{k, v}, Crit.Leaf{k2, w}, Maybe.default(&2, Nat, d, 0n)),
        t1 => h,
        t1 => Crit.join_all(~V, ~G, ~p, k, v, Crit.Leaf{k2, w}, Maybe.default(&2, Nat, d, 0n), g)(hk)(h)
      )
    case Crit.Fork{+rep, +pos, +e, +z, +o}:
      +h => +hk => Shared.Bool.when_cases(
        Crit<V>,
        t => {Crit.all(~V, ~G, ~p, t, g) == True{}: Bool},
        Crit.above(d, pos),
        u => Crit.join(V, Crit.Leaf{k, v}, Crit.Fork{rep, pos, e, z, o}, Maybe.default(&2, Nat, d, 0n)),
        u => Crit.put.fork(
            ~V,
            ~f,
            k,
            v,
            rep,
            pos,
            e,
            z,
            o,
            Cur.skip(Nat.sub(pos, at), c),
            z2 => Crit.put(~V, ~f, z, 1n+pos, z2, k, v, d),
            o2 => Crit.put(~V, ~f, o, 1n+pos, o2, k, v, d)
          ),
        ta => Crit.join_all(~V, ~G, ~p, k, v, Crit.Fork{rep, pos, e, z, o}, Maybe.default(&2, Nat, d, 0n), g)(hk)(h),
        ta => Shared.Bool.when_cases(
            Crit<V>,
            t => {Crit.all(~V, ~G, ~p, t, g) == True{}: Bool},
            Cur.done(Cur.skip(Nat.sub(pos, at), c)),
            u => Crit.mk(V, k, pos, Some{Crit.merge(~V, ~f, e, v)}, z, o),
            u => Shared.Bool.when(Crit<V>, Cur.bit(Cur.skip(Nat.sub(pos, at), c)), w => Crit.mk(V, rep, pos, e, z, Crit.put(~V, ~f, o, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), k, v, d)), w => Crit.mk(V, rep, pos, e, Crit.put(~V, ~f, z, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), k, v, d), o)),
            +t1 => Crit.mk_all(~V, ~G, ~p, k, pos, Some{Crit.merge(~V, ~f, e, v)}, z, o, g)(hk)(Crit.all.z(~V, ~G, ~p, rep, pos, e, z, o, g)(h))(Crit.all.o(~V, ~G, ~p, rep, pos, e, z, o, g)(h)),
            +t1 => Shared.Bool.when_cases(
              Crit<V>,
              t => {Crit.all(~V, ~G, ~p, t, g) == True{}: Bool},
              Cur.bit(Cur.skip(Nat.sub(pos, at), c)),
              w => Crit.mk(V, rep, pos, e, z, Crit.put(~V, ~f, o, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), k, v, d)),
              w => Crit.mk(V, rep, pos, e, Crit.put(~V, ~f, z, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), k, v, d), o),
              +t2 => Crit.mk_all(~V, ~G, ~p, rep, pos, e, z, Crit.put(~V, ~f, o, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), k, v, d), g)(Crit.all.hit(~V, ~G, ~p, rep, pos, e, z, o, g)(h))(Crit.all.z(~V, ~G, ~p, rep, pos, e, z, o, g)(h))(Crit.put_all(~V, ~f, ~G, ~p, o, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), k, v, d, g)(Crit.all.o(~V, ~G, ~p, rep, pos, e, z, o, g)(h))(hk)),
              +t2 => Crit.mk_all(~V, ~G, ~p, rep, pos, e, Crit.put(~V, ~f, z, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), k, v, d), o, g)(Crit.all.hit(~V, ~G, ~p, rep, pos, e, z, o, g)(h))(Crit.put_all(~V, ~f, ~G, ~p, z, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), k, v, d, g)(Crit.all.z(~V, ~G, ~p, rep, pos, e, z, o, g)(h))(hk))(Crit.all.o(~V, ~G, ~p, rep, pos, e, z, o, g)(h))
            )
          )
      )

# a key on a side of a fork at pos, where k agrees with the rep before
# x < pos and the rep's side at x is b, is on the side b of a fork of k at x
def Place.down(+rep: List<&2, U32>, +pos: Nat, +bb: Bool, +k: List<&2, U32>, +x: Nat, +b: Bool, +key: List<&2, U32>) -> {Nat.is_lt(x, pos) == True{}: Bool} -> {
  Key.agree(k, rep, x) == True{}: Bool
} -> {Key.side(rep, x) == Some{b}: Maybe<&2, Bool>} -> {Place.has(Place{rep, pos, bb}, key) == True{}: Bool} -> {Place.has(Place{k, x, b}, key) == True{}: Bool}:
  lt => ha => sr => h =>
    +a2 = Key.agree_le(key, rep, 1n+x, pos)(Crit.lt_le_succ(x, pos)(lt))(Place.has_agree(rep, pos, bb, key)(h))
    Place.intro(k, x, b, key)(Key.agree_join(key, k, rep, x)(Key.agree_le(key, rep, x, 1n+x)(Shared.Nat.le_succ(x, x)(Shared.Nat.le_refl(x)))(a2))(ha))(
      Equal.trans(
        Maybe<&2, Bool>,
        Key.side(key, x),
        Key.side(rep, x),
        Some{b},
        Equal.trans(
          Maybe<&2, Bool>,
          Key.side(key, x),
          Bits.at(Key.bits(key), x),
          Key.side(rep, x),
          Key.side_bits(key, x),
          Equal.trans(Maybe<&2, Bool>, Bits.at(Key.bits(key), x), Bits.at(Key.bits(rep), x), Key.side(rep, x), Key.at_eq(key, rep, x)(a2), Equal.sym(Maybe<&2, Bool>, Key.side(rep, x), Bits.at(Key.bits(rep), x), Key.side_bits(rep, x)))
        ),
        sr
      )
    )

# the keys on a side of a fork at pos are on the side b of a fork of k at
# x < pos, where k agrees with the rep before x and the rep's side at x is b
def Crit.place_down(~V: Data, m: Crit<V>, +rep: List<&2, U32>, +pos: Nat, +bb: Bool, +k: List<&2, U32>, +x: Nat, +b: Bool) -> {
  Nat.is_lt(x, pos) == True{}: Bool
} -> {Key.agree(k, rep, x) == True{}: Bool} -> {Key.side(rep, x) == Some{b}: Maybe<&2, Bool>} -> {
  Crit.all(~V, ~Place, ~Place.has, m, Place{rep, pos, bb}) == True{}: Bool
} -> {Crit.all(~V, ~Place, ~Place.has, m, Place{k, x, b}) == True{}: Bool}:
  match m:
    case Crit.Tip{}:
      lt => ha => sr => h => {==}
    case Crit.Leaf{+key, w}:
      lt => ha => sr => h => Place.down(rep, pos, bb, k, x, b, key)(lt)(ha)(sr)(h)
    case Crit.Fork{+r2, +p2, +e2, +z2, +o2}:
      +lt => +ha => +sr => +h => Crit.all.intro(~V, ~Place, ~Place.has, r2, p2, e2, z2, o2, Place{k, x, b})(
        Crit.or_hit_move(V, e2, Place.has(Place{rep, pos, bb}, r2), Place.has(Place{k, x, b}, r2))(Place.down(rep, pos, bb, k, x, b, r2)(lt)(ha)(sr))(
          Crit.all.hit(~V, ~Place, ~Place.has, r2, p2, e2, z2, o2, Place{rep, pos, bb})(h)
        )
      )(Crit.place_down(~V, z2, rep, pos, bb, k, x, b)(lt)(ha)(sr)(Crit.all.z(~V, ~Place, ~Place.has, r2, p2, e2, z2, o2, Place{rep, pos, bb})(h)))(
        Crit.place_down(~V, o2, rep, pos, bb, k, x, b)(lt)(ha)(sr)(Crit.all.o(~V, ~Place, ~Place.has, r2, p2, e2, z2, o2, Place{rep, pos, bb})(h))
      )

# the keys of a well formed fork at pos are on the side b of a fork of k at
# x < pos, where k agrees with its rep before x and the rep's side at x is b
def Crit.fork_place(~V: Data, +rep: List<&2, U32>, +pos: Nat, +e: Maybe<&2, V>, +z: Crit<V>, +o: Crit<V>, +ly: Nat, +k: List<&2, U32>, +x: Nat, +b: Bool) -> {
  Crit.wf(~V, Crit.Fork{rep, pos, e, z, o}, ly) == True{}: Bool
} -> {Nat.is_lt(x, pos) == True{}: Bool} -> {Key.agree(k, rep, x) == True{}: Bool} -> {Key.side(rep, x) == Some{b}: Maybe<&2, Bool>} -> {
  Crit.all(~V, ~Place, ~Place.has, Crit.Fork{rep, pos, e, z, o}, Place{k, x, b}) == True{}: Bool
}:
  +h => +lt => +ha => +sr => Crit.all.intro(~V, ~Place, ~Place.has, rep, pos, e, z, o, Place{k, x, b})(
    Crit.or_right(Maybe.is_none(&2, V, e), Place.has(Place{k, x, b}, rep))(Place.intro(k, x, b, rep)(Key.agree_sym(k, rep, x)(ha))(sr))
  )(Crit.place_down(~V, z, rep, pos, False{}, k, x, b)(lt)(ha)(sr)(Crit.wf.all_z(~V, rep, pos, e, z, o, ly)(h)))(
    Crit.place_down(~V, o, rep, pos, True{}, k, x, b)(lt)(ha)(sr)(Crit.wf.all_o(~V, rep, pos, e, z, o, ly)(h))
  )

# a fork of an entry of k that ends at x and an entry of k2 is well formed
def Crit.jwl_end(~V: Data, +k: List<&2, U32>, +v: V, +k2: List<&2, U32>, +w: V, +x: Nat, +lo: Nat, b: Bool) -> {Nat.is_le(lo, x) == True{}: Bool} -> {
  Nat.is_eq(List.length(&2, Bool, Key.bits(k)), x) == True{}: Bool
} -> {Place.has(Place{k, x, b}, k2) == True{}: Bool} -> {Crit.wf(~V, Crit.join.end(V, Crit.Leaf{k, v}, Crit.Leaf{k2, w}, x, b), lo) == True{}: Bool}:
  match b:
    case True{}:
      le => len => has => Crit.wf.intro(~V, k, x, Some{v}, Crit.Tip{}, Crit.Leaf{k2, w}, lo)(le)({==})(len)({==})(has)({==})({==})
    case False{}:
      le => len => has => Crit.wf.intro(~V, k, x, Some{v}, Crit.Leaf{k2, w}, Crit.Tip{}, lo)(le)({==})(len)(has)({==})({==})({==})

# a fork of an entry of k that ends at x and a well formed fork is well formed
def Crit.jwf_end(~V: Data, +k: List<&2, U32>, +v: V, +rep: List<&2, U32>, +pos: Nat, +e: Maybe<&2, V>, +z: Crit<V>, +o: Crit<V>, +x: Nat, +lo: Nat, b: Bool) -> {
  Nat.is_le(lo, x) == True{}: Bool
} -> {Nat.is_eq(List.length(&2, Bool, Key.bits(k)), x) == True{}: Bool} -> {
  Crit.all(~V, ~Place, ~Place.has, Crit.Fork{rep, pos, e, z, o}, Place{k, x, b}) == True{}: Bool
} -> {Crit.wf(~V, Crit.Fork{rep, pos, e, z, o}, 1n+x) == True{}: Bool} -> {
  Crit.wf(~V, Crit.join.end(V, Crit.Leaf{k, v}, Crit.Fork{rep, pos, e, z, o}, x, b), lo) == True{}: Bool
}:
  match b:
    case True{}:
      le => len => ay => wy => Crit.wf.intro(~V, k, x, Some{v}, Crit.Tip{}, Crit.Fork{rep, pos, e, z, o}, lo)(le)({==})(len)({==})(ay)({==})(wy)
    case False{}:
      le => len => ay => wy => Crit.wf.intro(~V, k, x, Some{v}, Crit.Fork{rep, pos, e, z, o}, Crit.Tip{}, lo)(le)({==})(len)(ay)({==})(wy)({==})

# a key that ends where its cursor is done has no side there
def Crit.side_none(+k: List<&2, U32>, +x: Nat) -> {Cur.done(Key.at(k, x)) == True{}: Bool} -> {Key.side(k, x) == None{}: Maybe<&2, Bool>}:
  hd =>
    %Equal.sym(Bool, Cur.done(Key.at(k, x)), True{}, hd): {
      Shared.Bool.when(Maybe<&2, Bool>, _, u => None{}, u => Some{Cur.bit(Key.at(k, x))}) == None{}: Maybe<&2, Bool>
    }
    {==}

# keys that differ first at x agree on x bits
def Key.agree_of_diff(+a: List<&2, U32>, +b: List<&2, U32>, +x: Nat) -> {Key.diff(a, b) == Some{x}: Maybe<&2, Nat>} -> {Key.agree(a, b, x) == True{}: Bool}:
  hd =>
    %Equal.sym(Maybe<&2, Nat>, Key.diff(a, b), Some{x}, hd): {Bits.agree(_, x) == True{}: Bool}
    Shared.Nat.le_refl(x)

# a fork of two entries whose keys differ first at x is well formed below x
def Crit.join_wf_leaf(~V: Data, +k: List<&2, U32>, +v: V, +k2: List<&2, U32>, +w: V, +x: Nat, +lo: Nat) -> {Key.diff(k, k2) == Some{x}: Maybe<&2, Nat>} -> {
  Nat.is_le(lo, x) == True{}: Bool
} -> {Crit.wf(~V, Crit.join(V, Crit.Leaf{k, v}, Crit.Leaf{k2, w}, x), lo) == True{}: Bool}:
  +hd => +le =>
    +ag = Key.agree_of_diff(k, k2, x)(hd)
    +ag2 = Key.agree_sym(k, k2, x)(ag)
    +sne = Crit.diff_sides(k, k2, x)(hd)
    Shared.Bool.when_cases(
    Crit<V>,
    t => {Crit.wf(~V, t, lo) == True{}: Bool},
    Cur.done(Key.at(k, x)),
    u => Crit.join.end(V, Crit.Leaf{k, v}, Crit.Leaf{k2, w}, x, Cur.bit(Key.at(Crit.rep(V, Crit.Leaf{k2, w}, []), x))),
    u => Shared.Bool.when(
      Crit<V>,
      Cur.done(Key.at(Crit.rep(V, Crit.Leaf{k2, w}, []), x)),
      q1 => Crit.join.end(V, Crit.Leaf{k2, w}, Crit.Leaf{k, v}, x, Cur.bit(Key.at(k, x))),
      q1 => Shared.Bool.when(Crit<V>, Cur.bit(Key.at(k, x)), q2 => Crit.Fork{Crit.rep(V, Crit.Leaf{k2, w}, []), x, None{}, Crit.Leaf{k2, w}, Crit.Leaf{k, v}}, q2 => Crit.Fork{k, x, None{}, Crit.Leaf{k, v}, Crit.Leaf{k2, w}})
    ),
    +t1 => 
      +t2n = Crit.false_of(Cur.done(Key.at(k2, x)))(t => Shared.Bool.true_ne_false(Crit.ne_sides(k, k2, x, None{}, None{})(Crit.side_none(k, x)(t1))(Crit.side_none(k2, x)(t))(sne)))
      Crit.jwl_end(~V, k, v, k2, w, x, lo, Cur.bit(Key.at(k2, x)))(le)(Crit.le_eq(List.length(&2, Bool, Key.bits(k)), x)(Crit.drop_nil_len(Key.bits(k), x)(Crit.at_nil(k, x)(t1)))(Crit.agree_len(x, Key.bits(k), Key.bits(k2))(Equal.trans(Bool, Bits.agree_n(x, Key.bits(k), Key.bits(k2)), Key.agree(k, k2, x), True{}, Equal.sym(Bool, Key.agree(k, k2, x), Bits.agree_n(x, Key.bits(k), Key.bits(k2)), Key.agree_bits(k, k2, x)), ag))(Crit.drop_some_le(Key.bits(k2), x)(Crit.at_some(k2, x)(t2n)))))(
        Place.intro(k, x, Cur.bit(Key.at(k2, x)), k2)(ag2)(Crit.side_of(k2, x, Cur.bit(Key.at(k2, x)))(t2n)({==}))
      ),
    +t1 => Shared.Bool.when_cases(
      Crit<V>,
      t => {Crit.wf(~V, t, lo) == True{}: Bool},
      Cur.done(Key.at(Crit.rep(V, Crit.Leaf{k2, w}, []), x)),
      q1 => Crit.join.end(V, Crit.Leaf{k2, w}, Crit.Leaf{k, v}, x, Cur.bit(Key.at(k, x))),
      q1 => Shared.Bool.when(Crit<V>, Cur.bit(Key.at(k, x)), q2 => Crit.Fork{Crit.rep(V, Crit.Leaf{k2, w}, []), x, None{}, Crit.Leaf{k2, w}, Crit.Leaf{k, v}}, q2 => Crit.Fork{k, x, None{}, Crit.Leaf{k, v}, Crit.Leaf{k2, w}}),
      +t2 => Crit.jwl_end(~V, k2, w, k, v, x, lo, Cur.bit(Key.at(k, x)))(le)(Crit.le_eq(List.length(&2, Bool, Key.bits(k2)), x)(Crit.drop_nil_len(Key.bits(k2), x)(Crit.at_nil(k2, x)(t2)))(Crit.agree_len(x, Key.bits(k2), Key.bits(k))(Equal.trans(Bool, Bits.agree_n(x, Key.bits(k2), Key.bits(k)), Key.agree(k2, k, x), True{}, Equal.sym(Bool, Key.agree(k2, k, x), Bits.agree_n(x, Key.bits(k2), Key.bits(k)), Key.agree_bits(k2, k, x)), ag2))(Crit.drop_some_le(Key.bits(k), x)(Crit.at_some(k, x)(t1)))))(
        Place.intro(k2, x, Cur.bit(Key.at(k, x)), k)(ag)(Crit.side_of(k, x, Cur.bit(Key.at(k, x)))(t1)({==}))
      ),
      +t2 => Shared.Bool.when_cases(
        Crit<V>,
        t => {Crit.wf(~V, t, lo) == True{}: Bool},
        Cur.bit(Key.at(k, x)),
        q2 => Crit.Fork{Crit.rep(V, Crit.Leaf{k2, w}, []), x, None{}, Crit.Leaf{k2, w}, Crit.Leaf{k, v}},
        q2 => Crit.Fork{k, x, None{}, Crit.Leaf{k, v}, Crit.Leaf{k2, w}},
        +t3 => 
          +b2 = Crit.ne_true(Cur.bit(Key.at(k2, x)))(Crit.ne_sides(k, k2, x, Some{True{}}, Some{Cur.bit(Key.at(k2, x))})(Crit.side_of(k, x, True{})(t1)(t3))(Crit.side_of(k2, x, Cur.bit(Key.at(k2, x)))(t2)({==}))(sne))
          Crit.wf.intro(~V, k2, x, None{}, Crit.Leaf{k2, w}, Crit.Leaf{k, v}, lo)(le)({==})(Key.is_eq_refl(k2))(
            Place.intro(k2, x, False{}, k2)(Key.agree_self(k2, x))(Crit.side_of(k2, x, False{})(t2)(b2))
          )(Place.intro(k2, x, True{}, k)(ag)(Crit.side_of(k, x, True{})(t1)(t3)))({==})({==}),
        +t3 => 
          +b2 = Crit.ne_false(Cur.bit(Key.at(k2, x)))(Crit.ne_sides(k, k2, x, Some{False{}}, Some{Cur.bit(Key.at(k2, x))})(Crit.side_of(k, x, False{})(t1)(t3))(Crit.side_of(k2, x, Cur.bit(Key.at(k2, x)))(t2)({==}))(sne))
          Crit.wf.intro(~V, k, x, None{}, Crit.Leaf{k, v}, Crit.Leaf{k2, w}, lo)(le)({==})(Key.is_eq_refl(k))(
            Place.intro(k, x, False{}, k)(Key.agree_self(k, x))(Crit.side_of(k, x, False{})(t1)(t3))
          )(Place.intro(k, x, True{}, k2)(ag2)(Crit.side_of(k2, x, True{})(t2)(b2)))({==})({==})
      )
    )
  )

# a fork of an entry of k and a well formed fork at pos, where k agrees with
# its rep before x < pos and differs from it at x, is well formed below x
def Crit.join_wf_fork(~V: Data, +k: List<&2, U32>, +v: V, +rep: List<&2, U32>, +pos: Nat, +e: Maybe<&2, V>, +z: Crit<V>, +o: Crit<V>, +x: Nat, +lo: Nat, +ly: Nat) -> {
  Crit.wf(~V, Crit.Fork{rep, pos, e, z, o}, ly) == True{}: Bool
} -> {Nat.is_le(lo, x) == True{}: Bool} -> {Nat.is_lt(x, pos) == True{}: Bool} -> {Key.agree(k, rep, x) == True{}: Bool} -> {
  Shared.Maybe.is_eq(~Bool, ~Shared.Bool.is_eq, Key.side(k, x), Key.side(rep, x)) == False{}: Bool
} -> {Crit.wf(~V, Crit.join(V, Crit.Leaf{k, v}, Crit.Fork{rep, pos, e, z, o}, x), lo) == True{}: Bool}:
  +h => +le => +lt => +ha => +sne =>
    +nr = Crit.len_drop(Key.bits(rep), x)(Shared.Nat.lt_le(x, pos, List.length(&2, Bool, Key.bits(rep)))(lt)(Crit.rep_long(~V, rep, pos, e, z, o, ly)(h)))
    +t2n = Equal.trans(
      Bool,
      Cur.done(Key.at(rep, x)),
      List.is_empty(&2, Bool, List.drop(&2, Bool, Key.bits(rep), x)),
      False{},
      Crit.done_of(Key.at(rep, x), List.drop(&2, Bool, Key.bits(rep), x))(Cur.skip_bits(x, Cur.of(rep))),
      nr
    )
    +sr = Crit.side_of(rep, x, Cur.bit(Key.at(rep, x)))(t2n)({==})
    +ay = Crit.fork_place(~V, rep, pos, e, z, o, ly, k, x, Cur.bit(Key.at(rep, x)))(h)(lt)(ha)(sr)
    +wy = Crit.wf_lower(~V, rep, pos, e, z, o, ly, 1n+x)(h)(Crit.lt_le_succ(x, pos)(lt))
    +ar = Key.agree_sym(k, rep, x)(ha)
    Shared.Bool.when_cases(
    Crit<V>,
    t => {Crit.wf(~V, t, lo) == True{}: Bool},
    Cur.done(Key.at(k, x)),
    u => Crit.join.end(V, Crit.Leaf{k, v}, Crit.Fork{rep, pos, e, z, o}, x, Cur.bit(Key.at(rep, x))),
    u => Shared.Bool.when(
      Crit<V>,
      Cur.done(Key.at(rep, x)),
      q1 => Crit.join.end(V, Crit.Fork{rep, pos, e, z, o}, Crit.Leaf{k, v}, x, Cur.bit(Key.at(k, x))),
      q1 => Shared.Bool.when(Crit<V>, Cur.bit(Key.at(k, x)), q2 => Crit.Fork{rep, x, None{}, Crit.Fork{rep, pos, e, z, o}, Crit.Leaf{k, v}}, q2 => Crit.Fork{k, x, None{}, Crit.Leaf{k, v}, Crit.Fork{rep, pos, e, z, o}})
    ),
    +t1 => Crit.jwf_end(~V, k, v, rep, pos, e, z, o, x, lo, Cur.bit(Key.at(rep, x)))(le)(Crit.le_eq(List.length(&2, Bool, Key.bits(k)), x)(Crit.drop_nil_len(Key.bits(k), x)(Crit.at_nil(k, x)(t1)))(Crit.agree_len(x, Key.bits(k), Key.bits(rep))(Equal.trans(Bool, Bits.agree_n(x, Key.bits(k), Key.bits(rep)), Key.agree(k, rep, x), True{}, Equal.sym(Bool, Key.agree(k, rep, x), Bits.agree_n(x, Key.bits(k), Key.bits(rep)), Key.agree_bits(k, rep, x)), ha))(Crit.drop_some_le(Key.bits(rep), x)(nr))))(ay)(wy),
    +t1 => Shared.Bool.when_cases(
      Crit<V>,
      t => {Crit.wf(~V, t, lo) == True{}: Bool},
      Cur.done(Key.at(rep, x)),
      q1 => Crit.join.end(V, Crit.Fork{rep, pos, e, z, o}, Crit.Leaf{k, v}, x, Cur.bit(Key.at(k, x))),
      q1 => Shared.Bool.when(Crit<V>, Cur.bit(Key.at(k, x)), q2 => Crit.Fork{rep, x, None{}, Crit.Fork{rep, pos, e, z, o}, Crit.Leaf{k, v}}, q2 => Crit.Fork{k, x, None{}, Crit.Leaf{k, v}, Crit.Fork{rep, pos, e, z, o}}),
      +t2 => Empty.absurd({Crit.wf(~V, Crit.join.end(V, Crit.Fork{rep, pos, e, z, o}, Crit.Leaf{k, v}, x, Cur.bit(Key.at(k, x))), lo) == True{}: Bool}, Crit.clash(Cur.done(Key.at(rep, x)), True{}, False{}, t2, t2n, Shared.Bool.true_ne_false)),
      +t2 => Shared.Bool.when_cases(
        Crit<V>,
        t => {Crit.wf(~V, t, lo) == True{}: Bool},
        Cur.bit(Key.at(k, x)),
        q2 => Crit.Fork{rep, x, None{}, Crit.Fork{rep, pos, e, z, o}, Crit.Leaf{k, v}},
        q2 => Crit.Fork{k, x, None{}, Crit.Leaf{k, v}, Crit.Fork{rep, pos, e, z, o}},
        +t3 => 
          +bf = Crit.ne_true(Cur.bit(Key.at(rep, x)))(Crit.ne_sides(k, rep, x, Some{True{}}, Some{Cur.bit(Key.at(rep, x))})(Crit.side_of(k, x, True{})(t1)(t3))(sr)(sne))
          Crit.wf.intro(~V, rep, x, None{}, Crit.Fork{rep, pos, e, z, o}, Crit.Leaf{k, v}, lo)(le)({==})(Key.is_eq_refl(rep))(
            Crit.place_shift(~V, Crit.Fork{rep, pos, e, z, o}, k, rep, x, False{})(ar)((
              %bf: {Crit.all(~V, ~Place, ~Place.has, Crit.Fork{rep, pos, e, z, o}, Place{k, x, _}) == True{}: Bool}
              ay
            ))
          )(Place.intro(rep, x, True{}, k)(ha)(Crit.side_of(k, x, True{})(t1)(t3)))(wy)({==}),
        +t3 => 
          +bt = Crit.ne_false(Cur.bit(Key.at(rep, x)))(Crit.ne_sides(k, rep, x, Some{False{}}, Some{Cur.bit(Key.at(rep, x))})(Crit.side_of(k, x, False{})(t1)(t3))(sr)(sne))
          Crit.wf.intro(~V, k, x, None{}, Crit.Leaf{k, v}, Crit.Fork{rep, pos, e, z, o}, lo)(le)({==})(Key.is_eq_refl(k))(
            Place.intro(k, x, False{}, k)(Key.agree_self(k, x))(Crit.side_of(k, x, False{})(t1)(t3))
          )((
            %bt: {Crit.all(~V, ~Place, ~Place.has, Crit.Fork{rep, pos, e, z, o}, Place{k, x, _}) == True{}: Bool}
            ay
          ))({==})(wy)
      )
    )
  )

# a key that differs from the key that a read of a well formed fork reaches
# nowhere before its bit agrees with its rep before the bit
def Crit.k_agree_rep(
  ~V: Data,
  +rep: List<&2, U32>,
  +pos: Nat,
  +e: Maybe<&2, V>,
  +z: Crit<V>,
  +o: Crit<V>,
  +lo: Nat,
  +at: Nat,
  +c: Cur,
  +k: List<&2, U32>,
  +d: Maybe<&2, Nat>,
  +r: Maybe<&2, List<&2, U32>>,
  +n: List<&2, U32>
) -> {Crit.wf(~V, Crit.Fork{rep, pos, e, z, o}, lo) == True{}: Bool} -> {Maybe.or(&2, List<&2, U32>, Crit.near(V, Crit.Fork{rep, pos, e, z, o}, at, c), r) == Some{n}: Maybe<&2, List<&2, U32>>} -> {
  d == Key.diff(k, n): Maybe<&2, Nat>
} -> {Crit.above(d, pos) == False{}: Bool} -> {Key.agree(k, rep, pos) == True{}: Bool}:
  +h => +hn => +hd => +ta => Key.agree_join(k, rep, n, pos)((
    %hd: {Bits.agree(_, pos) == True{}: Bool}
    Crit.not_above_agree(d, pos)(ta)
  ))(Key.agree_sym(n, rep, pos)(Crit.near_agree(~V, rep, pos, e, z, o, lo, at, c, n)(h)(Equal.trans(Maybe<&2, List<&2, U32>>, Crit.near(V, Crit.Fork{rep, pos, e, z, o}, at, c), Maybe.or(&2, List<&2, U32>, Crit.near(V, Crit.Fork{rep, pos, e, z, o}, at, c), r), Some{n}, Equal.sym(Maybe<&2, List<&2, U32>>, Maybe.or(&2, List<&2, U32>, Crit.near(V, Crit.Fork{rep, pos, e, z, o}, at, c), r), Crit.near(V, Crit.Fork{rep, pos, e, z, o}, at, c), Crit.or_of_some(List<&2, U32>, Crit.near(V, Crit.Fork{rep, pos, e, z, o}, at, c), r)(Crit.near_some(V, rep, pos, e, z, o, at, c))), hn))))

# Crit.inv_child, for a side with an entry
def Crit.inv_nontip(~V: Data, +x: Crit<V>, +rep: List<&2, U32>, +pos: Nat, +b: Bool, +at2: Nat, +c2: Cur, +k: List<&2, U32>, +d: Maybe<&2, Nat>, +n: List<&2, U32>) -> {
  Crit.is_tip(V, x) == False{}: Bool
} -> {Crit.wf(~V, x, 1n+pos) == True{}: Bool} -> {Crit.all(~V, ~Place, ~Place.has, x, Place{rep, pos, b}) == True{}: Bool} -> {
  Maybe.or(&2, List<&2, U32>, Crit.near(V, x, at2, c2), Some{rep}) == Some{n}: Maybe<&2, List<&2, U32>>
} -> {d == Key.diff(k, n): Maybe<&2, Nat>} -> {Key.agree(k, n, pos) == True{}: Bool} -> {Key.side(k, pos) == Some{b}: Maybe<&2, Bool>} -> {
  Bits.agree(d, 1n+pos) == True{}: Bool
}:
  nt => w => a => hn => hd => ak => sk =>
    +has = Crit.near_pass(~V, ~Place, ~Place.has, x, 1n+pos, at2, c2, Place{rep, pos, b}, n)(w)(a)(
      Equal.trans(
        Maybe<&2, List<&2, U32>>,
        Crit.near(V, x, at2, c2),
        Maybe.or(&2, List<&2, U32>, Crit.near(V, x, at2, c2), Some{rep}),
        Some{n},
        Equal.sym(Maybe<&2, List<&2, U32>>, Maybe.or(&2, List<&2, U32>, Crit.near(V, x, at2, c2), Some{rep}), Crit.near(V, x, at2, c2), Crit.or_of_some(List<&2, U32>, Crit.near(V, x, at2, c2), Some{rep})(Crit.near_nontip(V, x, at2, c2)(nt))),
        hn
      )
    )
    %Equal.sym(Maybe<&2, Nat>, d, Key.diff(k, n), hd): {Bits.agree(_, 1n+pos) == True{}: Bool}
    Key.agree_succ(k, n, pos, b)(ak)(sk)(
      Shared.Maybe.is_eq_sound(~Bool, ~Shared.Bool.is_eq, x1 => y1 => Shared.Bool.is_eq_sound(x1, y1), Key.side(n, pos), Some{b})(
        Shared.List.all.if_rest(Key.agree(n, rep, pos), u => Shared.Maybe.is_eq(~Bool, ~Shared.Bool.is_eq, Key.side(n, pos), Some{b}))(has)
      )
    )

# k fits a side of a fork at the bit after it: the side has no entry, or k
# differs from the key that a read of the side reaches nowhere before
def Crit.inv_child(~V: Data, x: Crit<V>, +rep: List<&2, U32>, +pos: Nat, +b: Bool, +at2: Nat, +c2: Cur, +k: List<&2, U32>, +d: Maybe<&2, Nat>, +n: List<&2, U32>) -> {
  Crit.wf(~V, x, 1n+pos) == True{}: Bool
} -> {Crit.all(~V, ~Place, ~Place.has, x, Place{rep, pos, b}) == True{}: Bool} -> {
  Maybe.or(&2, List<&2, U32>, Crit.near(V, x, at2, c2), Some{rep}) == Some{n}: Maybe<&2, List<&2, U32>>
} -> {d == Key.diff(k, n): Maybe<&2, Nat>} -> {Key.agree(k, n, pos) == True{}: Bool} -> {Key.side(k, pos) == Some{b}: Maybe<&2, Bool>} -> {
  Bool.or(Crit.is_tip(V, x), Bits.agree(d, 1n+pos)) == True{}: Bool
}:
  match x:
    case Crit.Tip{}:
      w => a => hn => hd => ak => sk => {==}
    case Crit.Leaf{+k3, +w3}:
      w => a => hn => hd => ak => sk => Crit.inv_nontip(~V, Crit.Leaf{k3, w3}, rep, pos, b, at2, c2, k, d, n)({==})(w)(a)(hn)(hd)(ak)(sk)
    case Crit.Fork{+r3, +p3, +e3, +z3, +o3}:
      w => a => hn => hd => ak => sk => Crit.inv_nontip(~V, Crit.Fork{r3, p3, e3, z3, o3}, rep, pos, b, at2, c2, k, d, n)({==})(w)(a)(hn)(hd)(ak)(sk)

# a write of k into a well formed map, read from k's cursor, keeps it well
# formed; n is the key that the read reaches (r when m is empty), and d where
# k differs from it, which is not before lo unless m is empty
def Crit.put_wf(
  ~V: Data,
  ~f: V -> V -> V,
  m: Crit<V>,
  +lo: Nat,
  +at: Nat,
  +c: Cur,
  +k: List<&2, U32>,
  +v: V,
  +d: Maybe<&2, Nat>,
  +r: Maybe<&2, List<&2, U32>>,
  +n: List<&2, U32>
) -> {Crit.wf(~V, m, lo) == True{}: Bool} -> {Nat.is_le(at, lo) == True{}: Bool} -> {
  Cur.bits(c) == List.drop(&2, Bool, Key.bits(k), at): List<&2, Bool>
} -> {Maybe.or(&2, List<&2, U32>, Crit.near(V, m, at, c), r) == Some{n}: Maybe<&2, List<&2, U32>>} -> {d == Key.diff(k, n): Maybe<&2, Nat>} -> {
  Bool.or(Crit.is_tip(V, m), Bits.agree(d, lo)) == True{}: Bool
} -> {Crit.wf(~V, Crit.put(~V, ~f, m, at, c, k, v, d), lo) == True{}: Bool}:
  match m:
    case Crit.Tip{}:
      h => l => hc => hn => hd => hi => {==}
    case Crit.Leaf{+k2, +w}:
      h => l => hc => +hn => +hd => +hi => Shared.Bool.when_cases(
        Crit<V>,
        t => {Crit.wf(~V, t, lo) == True{}: Bool},
        Maybe.is_none(&2, Nat, d),
        u => Crit.Leaf{k2, f(w, v)},
        u => Crit.join(V, Crit.Leaf{k, v}, Crit.Leaf{k2, w}, Maybe.default(&2, Nat, d, 0n)),
        t1 => {==},
        +t1 =>
          +sd = Crit.some_of(d)(t1)
          Crit.join_wf_leaf(~V, k, v, k2, w, Maybe.default(&2, Nat, d, 0n), lo)((
            %Equal.sym(List<&2, U32>, k2, n, Shared.Maybe.some_inj(List<&2, U32>, k2, n, hn)): {Key.diff(k, _) == Some{Maybe.default(&2, Nat, d, 0n)}: Maybe<&2, Nat>}
            Equal.trans(Maybe<&2, Nat>, Key.diff(k, n), d, Some{Maybe.default(&2, Nat, d, 0n)}, Equal.sym(Maybe<&2, Nat>, d, Key.diff(k, n), hd), sd)
          ))(Equal.trans(Bool, Bits.agree(Some{Maybe.default(&2, Nat, d, 0n)}, lo), Bits.agree(d, lo), True{}, Equal.cong(Maybe<&2, Nat>, Bool, t => Bits.agree(t, lo), Some{Maybe.default(&2, Nat, d, 0n)}, d, Equal.sym(Maybe<&2, Nat>, d, Some{Maybe.default(&2, Nat, d, 0n)}, sd)), hi))
      )
    case Crit.Fork{+rep, +pos, +e, +z, +o}:
      +h => +l => +hc => +hn => +hd => +hi =>
        +h2 = Crit.skip_at(k, at, pos, c)(Shared.Nat.le_trans(at, lo, pos)(l)(Crit.wf.le(~V, rep, pos, e, z, o, lo)(h)))(hc)
        Shared.Bool.when_cases(
          Crit<V>,
          t => {Crit.wf(~V, t, lo) == True{}: Bool},
          Crit.above(d, pos),
          u => Crit.join(V, Crit.Leaf{k, v}, Crit.Fork{rep, pos, e, z, o}, Maybe.default(&2, Nat, d, 0n)),
          u => Crit.put.fork(
            ~V,
            ~f,
            k,
            v,
            rep,
            pos,
            e,
            z,
            o,
            Cur.skip(Nat.sub(pos, at), c),
            z2 => Crit.put(~V, ~f, z, 1n+pos, z2, k, v, d),
            o2 => Crit.put(~V, ~f, o, 1n+pos, o2, k, v, d)
          ),
          +ta =>
            +sd = Crit.above_some(d, pos)(ta)
            +lt = Crit.above_lt(d, pos, Maybe.default(&2, Nat, d, 0n))(sd)(ta)
            +anr = Crit.near_agree(~V, rep, pos, e, z, o, lo, at, c, n)(h)(Equal.trans(Maybe<&2, List<&2, U32>>, Crit.near(V, Crit.Fork{rep, pos, e, z, o}, at, c), Maybe.or(&2, List<&2, U32>, Crit.near(V, Crit.Fork{rep, pos, e, z, o}, at, c), r), Some{n}, Equal.sym(Maybe<&2, List<&2, U32>>, Maybe.or(&2, List<&2, U32>, Crit.near(V, Crit.Fork{rep, pos, e, z, o}, at, c), r), Crit.near(V, Crit.Fork{rep, pos, e, z, o}, at, c), Crit.or_of_some(List<&2, U32>, Crit.near(V, Crit.Fork{rep, pos, e, z, o}, at, c), r)(Crit.near_some(V, rep, pos, e, z, o, at, c))), hn))
            Crit.join_wf_fork(~V, k, v, rep, pos, e, z, o, Maybe.default(&2, Nat, d, 0n), lo, lo)(h)(
              Equal.trans(Bool, Bits.agree(Some{Maybe.default(&2, Nat, d, 0n)}, lo), Bits.agree(d, lo), True{}, Equal.cong(Maybe<&2, Nat>, Bool, t => Bits.agree(t, lo), Some{Maybe.default(&2, Nat, d, 0n)}, d, Equal.sym(Maybe<&2, Nat>, d, Some{Maybe.default(&2, Nat, d, 0n)}, sd)), hi)
            )(lt)(
              Key.agree_join(k, rep, n, Maybe.default(&2, Nat, d, 0n))(Crit.agree_at(k, n, d, Maybe.default(&2, Nat, d, 0n))(hd)(sd))(Key.agree_sym(n, rep, Maybe.default(&2, Nat, d, 0n))(Key.agree_le(n, rep, Maybe.default(&2, Nat, d, 0n), pos)(Shared.Nat.lt_weak(Maybe.default(&2, Nat, d, 0n), pos)(lt))(anr)))
            )(
              Crit.sides_ne(k, n, rep, Maybe.default(&2, Nat, d, 0n))(Equal.trans(Maybe<&2, Nat>, Key.diff(k, n), d, Some{Maybe.default(&2, Nat, d, 0n)}, Equal.sym(Maybe<&2, Nat>, d, Key.diff(k, n), hd), sd))(
                Key.at_eq(n, rep, Maybe.default(&2, Nat, d, 0n))(Key.agree_le(n, rep, 1n+Maybe.default(&2, Nat, d, 0n), pos)(Crit.lt_le_succ(Maybe.default(&2, Nat, d, 0n), pos)(lt))(anr))
              )
            ),
          +ta => Shared.Bool.when_cases(
            Crit<V>,
            t => {Crit.wf(~V, t, lo) == True{}: Bool},
            Cur.done(Cur.skip(Nat.sub(pos, at), c)),
            u => Crit.mk(V, k, pos, Some{Crit.merge(~V, ~f, e, v)}, z, o),
            u => Shared.Bool.when(Crit<V>, Cur.bit(Cur.skip(Nat.sub(pos, at), c)), q1 => Crit.mk(V, rep, pos, e, z, Crit.put(~V, ~f, o, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), k, v, d)), q1 => Crit.mk(V, rep, pos, e, Crit.put(~V, ~f, z, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), k, v, d), o)),
            +t1 =>
              +nil = Crit.nil_of_done(k, pos, Cur.skip(Nat.sub(pos, at), c))(h2)(t1)
              +akr = Crit.not_above_agree(Key.diff(k, rep), pos)(Crit.done_above(V, rep, pos, e, z, o, at, c, k, d, r, n)(hn)(hd)(ta)(t1))
              Crit.mk_wf(~V, k, pos, Some{Crit.merge(~V, ~f, e, v)}, z, o, lo)(Crit.wf.le(~V, rep, pos, e, z, o, lo)(h))(Crit.done_len(~V, rep, pos, e, z, o, lo, k)(h)(nil)(akr))(
                Crit.place_shift(~V, z, rep, k, pos, False{})(akr)(Crit.wf.all_z(~V, rep, pos, e, z, o, lo)(h))
              )(Crit.place_shift(~V, o, rep, k, pos, True{})(akr)(Crit.wf.all_o(~V, rep, pos, e, z, o, lo)(h)))(Crit.wf.wf_z(~V, rep, pos, e, z, o, lo)(h))(Crit.wf.wf_o(~V, rep, pos, e, z, o, lo)(h)),
            +t1 => Shared.Bool.when_cases(
              Crit<V>,
              t => {Crit.wf(~V, t, lo) == True{}: Bool},
              Cur.bit(Cur.skip(Nat.sub(pos, at), c)),
              q1 => Crit.mk(V, rep, pos, e, z, Crit.put(~V, ~f, o, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), k, v, d)),
              q1 => Crit.mk(V, rep, pos, e, Crit.put(~V, ~f, z, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), k, v, d), o),
              +t2 =>
                +sk = Equal.trans(
                  Maybe<&2, Bool>,
                  Key.side(k, pos),
                  Some{Cur.bit(Cur.skip(Nat.sub(pos, at), c))},
                  Some{True{}},
                  Crit.side_cur(k, pos, Cur.skip(Nat.sub(pos, at), c))(h2)(t1),
                  Equal.cong(Bool, Maybe<&2, Bool>, t => Some{t}, Cur.bit(Cur.skip(Nat.sub(pos, at), c)), True{}, t2)
                )
                Crit.mk_wf(~V, rep, pos, e, z, Crit.put(~V, ~f, o, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), k, v, d), lo)(Crit.wf.le(~V, rep, pos, e, z, o, lo)(h))(Crit.rep_or(V, rep, pos, e, z)(Crit.wf.rep_ok(~V, rep, pos, e, z, o, lo)(h)))(Crit.wf.all_z(~V, rep, pos, e, z, o, lo)(h))(Crit.put_all(~V, ~f, ~Place, ~Place.has, o, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), k, v, d, Place{rep, pos, True{}})(Crit.wf.all_o(~V, rep, pos, e, z, o, lo)(h))(Place.intro(rep, pos, True{}, k)(Crit.k_agree_rep(~V, rep, pos, e, z, o, lo, at, c, k, d, r, n)(h)(hn)(hd)(ta))(sk)))(Crit.wf.wf_z(~V, rep, pos, e, z, o, lo)(h))(Crit.put_wf(~V, ~f, o, 1n+pos, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), k, v, d, Some{rep}, n)(Crit.wf.wf_o(~V, rep, pos, e, z, o, lo)(h))(Shared.Nat.le_refl(1n+pos))(Crit.next_at(k, pos, Cur.skip(Nat.sub(pos, at), c))(h2))(Crit.near_child(V, rep, pos, e, z, o, at, c, True{}, r, n)(hn)(t1)(t2))(hd)(Crit.inv_child(~V, o, rep, pos, True{}, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), k, d, n)(Crit.wf.wf_o(~V, rep, pos, e, z, o, lo)(h))(Crit.wf.all_o(~V, rep, pos, e, z, o, lo)(h))(Crit.near_child(V, rep, pos, e, z, o, at, c, True{}, r, n)(hn)(t1)(t2))(hd)((
                  %hd: {Bits.agree(_, pos) == True{}: Bool}
                  Crit.not_above_agree(d, pos)(ta)
                ))(sk))),
              +t2 =>
                +sk = Equal.trans(
                  Maybe<&2, Bool>,
                  Key.side(k, pos),
                  Some{Cur.bit(Cur.skip(Nat.sub(pos, at), c))},
                  Some{False{}},
                  Crit.side_cur(k, pos, Cur.skip(Nat.sub(pos, at), c))(h2)(t1),
                  Equal.cong(Bool, Maybe<&2, Bool>, t => Some{t}, Cur.bit(Cur.skip(Nat.sub(pos, at), c)), False{}, t2)
                )
                Crit.mk_wf(~V, rep, pos, e, Crit.put(~V, ~f, z, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), k, v, d), o, lo)(Crit.wf.le(~V, rep, pos, e, z, o, lo)(h))(Crit.rep_or(V, rep, pos, e, z)(Crit.wf.rep_ok(~V, rep, pos, e, z, o, lo)(h)))(Crit.put_all(~V, ~f, ~Place, ~Place.has, z, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), k, v, d, Place{rep, pos, False{}})(Crit.wf.all_z(~V, rep, pos, e, z, o, lo)(h))(Place.intro(rep, pos, False{}, k)(Crit.k_agree_rep(~V, rep, pos, e, z, o, lo, at, c, k, d, r, n)(h)(hn)(hd)(ta))(sk)))(Crit.wf.all_o(~V, rep, pos, e, z, o, lo)(h))(Crit.put_wf(~V, ~f, z, 1n+pos, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), k, v, d, Some{rep}, n)(Crit.wf.wf_z(~V, rep, pos, e, z, o, lo)(h))(Shared.Nat.le_refl(1n+pos))(Crit.next_at(k, pos, Cur.skip(Nat.sub(pos, at), c))(h2))(Crit.near_child(V, rep, pos, e, z, o, at, c, False{}, r, n)(hn)(t1)(t2))(hd)(Crit.inv_child(~V, z, rep, pos, False{}, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), k, d, n)(Crit.wf.wf_z(~V, rep, pos, e, z, o, lo)(h))(Crit.wf.all_z(~V, rep, pos, e, z, o, lo)(h))(Crit.near_child(V, rep, pos, e, z, o, at, c, False{}, r, n)(hn)(t1)(t2))(hd)((
                  %hd: {Bits.agree(_, pos) == True{}: Bool}
                  Crit.not_above_agree(d, pos)(ta)
                ))(sk)))(Crit.wf.wf_o(~V, rep, pos, e, z, o, lo)(h))
            )
          )
        )

# Crit.upsert_wf, once the key that a read of k reaches is known (nm)
def Crit.upsert_wf.at(~V: Data, ~f: V -> V -> V, +m: Crit<V>, +k: List<&2, U32>, +v: V, nm: Maybe<&2, List<&2, U32>>) -> {Crit.wf(~V, m, 0n) == True{}: Bool} -> {
  Crit.near(V, m, 0n, Cur.of(k)) == nm: Maybe<&2, List<&2, U32>>
} -> {Crit.wf(~V, Crit.put(~V, ~f, m, 0n, Cur.of(k), k, v, Crit.diff(k, nm)), 0n) == True{}: Bool}:
  match nm:
    case None{}:
      h => hm => Crit.put_wf(~V, ~f, m, 0n, 0n, Cur.of(k), k, v, None{}, Some{k}, k)(h)({==})(Equal.sym(List<&2, Bool>, List.drop(&2, Bool, Key.bits(k), 0n), Key.bits(k), Shared.List.drop_zero(&2, Bool, Key.bits(k))))(
        %Equal.sym(Maybe<&2, List<&2, U32>>, Crit.near(V, m, 0n, Cur.of(k)), None{}, hm): {Maybe.or(&2, List<&2, U32>, _, Some{k}) == Some{k}: Maybe<&2, List<&2, U32>>}
        {==}
      )(Equal.sym(Maybe<&2, Nat>, Key.diff(k, k), None{}, Key.diff_self(k)))(Shared.Bool.or_true_right(Crit.is_tip(V, m)))
    case Some{+x}:
      h => hm => Crit.put_wf(~V, ~f, m, 0n, 0n, Cur.of(k), k, v, Key.diff(k, x), None{}, x)(h)({==})(Equal.sym(List<&2, Bool>, List.drop(&2, Bool, Key.bits(k), 0n), Key.bits(k), Shared.List.drop_zero(&2, Bool, Key.bits(k))))(
        Equal.trans(Maybe<&2, List<&2, U32>>, Maybe.or(&2, List<&2, U32>, Crit.near(V, m, 0n, Cur.of(k)), None{}), Crit.near(V, m, 0n, Cur.of(k)), Some{x}, Shared.Maybe.or_none(List<&2, U32>, Crit.near(V, m, 0n, Cur.of(k))), hm)
      )({==})(Crit.or_right(Crit.is_tip(V, m), Bits.agree(Key.diff(k, x), 0n))(Bits.agree.zero(Key.diff(k, x))))

# Crit.upsert_wf, with m and k used more than once
def Crit.upsert_wf.go(~V: Data, ~f: V -> V -> V, +m: Crit<V>, +k: List<&2, U32>, +v: V) -> {Crit.wf(~V, m, 0n) == True{}: Bool} -> {
  Crit.wf(~V, Crit.upsert(~V, ~f, m, k, v), 0n) == True{}: Bool
}:
  h => Crit.upsert_wf.at(~V, ~f, m, k, v, Crit.near(V, m, 0n, Cur.of(k)))(h)({==})

# a write keeps a map well formed
law Crit.upsert_wf:
  for ~V: Data
  for ~f: V -> V -> V
  for m: Crit<V>
  for k: List<&2, U32>
  for v: V
  {Crit.wf(~V, m, 0n) == True{}: Bool} -> {Crit.wf(~V, Crit.upsert(~V, ~f, m, k, v), 0n) == True{}: Bool}

def Crit.upsert_wf(ty, f, m, k, v):
  Crit.upsert_wf.go(~ty, ~f, m, k, v)

# Crit.upsert_lookup in a map well formed below any bit, once the key that a
# read of k reaches is known (nm)
def Crit.upsert_lookup.at(~V: Data, ~f: V -> V -> V, +m: Crit<V>, +lo: Nat, +k: List<&2, U32>, +v: V, +q: List<&2, U32>, nm: Maybe<&2, List<&2, U32>>) -> {
  Crit.wf(~V, m, lo) == True{}: Bool
} -> {Crit.near(V, m, 0n, Cur.of(k)) == nm: Maybe<&2, List<&2, U32>>} -> {
  Crit.lookup(V, Crit.put(~V, ~f, m, 0n, Cur.of(k), k, v, Crit.diff(k, nm)), q)
    == Bool.pick(Maybe<&2, V>, Key.is_eq(q, k), Some{Crit.merge(~V, ~f, Crit.lookup(V, m, k), v)}, Crit.lookup(V, m, q)): Maybe<&2, V>
}:
  match nm:
    case None{}:
      +h => +hm => Equal.sym(
        Maybe<&2, V>,
        Bool.pick(Maybe<&2, V>, Key.is_eq(q, k), Some{Crit.merge(~V, ~f, Crit.lookup(V, m, k), v)}, Crit.lookup(V, m, q)),
        Crit.lookup(V, Crit.put(~V, ~f, m, 0n, Cur.of(k), k, v, None{}), q),
        Crit.pick_cases(
          Maybe<&2, V>,
          Key.is_eq(q, k),
          Some{Crit.merge(~V, ~f, Crit.lookup(V, m, k), v)},
          Crit.lookup(V, m, q),
          Crit.lookup(V, Crit.put(~V, ~f, m, 0n, Cur.of(k), k, v, None{}), q)
        )(
          t => (
            %Equal.sym(List<&2, U32>, q, k, Key.is_eq_sound(q, k)(t)): {
              Some{Crit.merge(~V, ~f, Crit.lookup(V, m, k), v)} == Crit.lookup(V, Crit.put(~V, ~f, m, 0n, Cur.of(k), k, v, None{}), _): Maybe<&2, V>
            }
            Equal.sym(
              Maybe<&2, V>,
              Crit.lookup(V, Crit.put(~V, ~f, m, 0n, Cur.of(k), k, v, None{}), k),
              Some{Crit.merge(~V, ~f, Crit.lookup(V, m, k), v)},
              Crit.put_new(~V, ~f, m, lo, 0n, Cur.of(k), k, v, None{}, Some{k}, k)(h)(Shared.Nat.le_zero(lo))(
                Equal.sym(List<&2, Bool>, List.drop(&2, Bool, Key.bits(k), 0n), Key.bits(k), Shared.List.drop_zero(&2, Bool, Key.bits(k)))
              )(
                %Equal.sym(Maybe<&2, List<&2, U32>>, Crit.near(V, m, 0n, Cur.of(k)), None{}, hm): {
                  Maybe.or(&2, List<&2, U32>, _, Some{k}) == Some{k}: Maybe<&2, List<&2, U32>>
                }
                {==}
              )(Equal.sym(Maybe<&2, Nat>, Key.diff(k, k), None{}, Key.diff_self(k)))
            )
          )
        )(
          t => Equal.sym(
            Maybe<&2, V>,
            Crit.lookup(V, Crit.put(~V, ~f, m, 0n, Cur.of(k), k, v, None{}), q),
            Crit.lookup(V, m, q),
            Crit.put_other(~V, ~f, m, lo, 0n, Cur.of(k), k, v, None{}, Some{k}, k, q)(h)(Shared.Nat.le_zero(lo))(
              Equal.sym(List<&2, Bool>, List.drop(&2, Bool, Key.bits(k), 0n), Key.bits(k), Shared.List.drop_zero(&2, Bool, Key.bits(k)))
            )(
              %Equal.sym(Maybe<&2, List<&2, U32>>, Crit.near(V, m, 0n, Cur.of(k)), None{}, hm): {
                Maybe.or(&2, List<&2, U32>, _, Some{k}) == Some{k}: Maybe<&2, List<&2, U32>>
              }
              {==}
            )(Equal.sym(Maybe<&2, Nat>, Key.diff(k, k), None{}, Key.diff_self(k)))(t)
          )
        )
      )
    case Some{+x}:
      +h => +hm => Equal.sym(
        Maybe<&2, V>,
        Bool.pick(Maybe<&2, V>, Key.is_eq(q, k), Some{Crit.merge(~V, ~f, Crit.lookup(V, m, k), v)}, Crit.lookup(V, m, q)),
        Crit.lookup(V, Crit.put(~V, ~f, m, 0n, Cur.of(k), k, v, Key.diff(k, x)), q),
        Crit.pick_cases(
          Maybe<&2, V>,
          Key.is_eq(q, k),
          Some{Crit.merge(~V, ~f, Crit.lookup(V, m, k), v)},
          Crit.lookup(V, m, q),
          Crit.lookup(V, Crit.put(~V, ~f, m, 0n, Cur.of(k), k, v, Key.diff(k, x)), q)
        )(
          t => (
            %Equal.sym(List<&2, U32>, q, k, Key.is_eq_sound(q, k)(t)): {
              Some{Crit.merge(~V, ~f, Crit.lookup(V, m, k), v)} == Crit.lookup(V, Crit.put(~V, ~f, m, 0n, Cur.of(k), k, v, Key.diff(k, x)), _): Maybe<&2, V>
            }
            Equal.sym(
              Maybe<&2, V>,
              Crit.lookup(V, Crit.put(~V, ~f, m, 0n, Cur.of(k), k, v, Key.diff(k, x)), k),
              Some{Crit.merge(~V, ~f, Crit.lookup(V, m, k), v)},
              Crit.put_new(~V, ~f, m, lo, 0n, Cur.of(k), k, v, Key.diff(k, x), None{}, x)(h)(Shared.Nat.le_zero(lo))(
                Equal.sym(List<&2, Bool>, List.drop(&2, Bool, Key.bits(k), 0n), Key.bits(k), Shared.List.drop_zero(&2, Bool, Key.bits(k)))
              )(
                Equal.trans(
                  Maybe<&2, List<&2, U32>>,
                  Maybe.or(&2, List<&2, U32>, Crit.near(V, m, 0n, Cur.of(k)), None{}),
                  Crit.near(V, m, 0n, Cur.of(k)),
                  Some{x},
                  Shared.Maybe.or_none(List<&2, U32>, Crit.near(V, m, 0n, Cur.of(k))),
                  hm
                )
              )({==})
            )
          )
        )(
          t => Equal.sym(
            Maybe<&2, V>,
            Crit.lookup(V, Crit.put(~V, ~f, m, 0n, Cur.of(k), k, v, Key.diff(k, x)), q),
            Crit.lookup(V, m, q),
            Crit.put_other(~V, ~f, m, lo, 0n, Cur.of(k), k, v, Key.diff(k, x), None{}, x, q)(h)(Shared.Nat.le_zero(lo))(
              Equal.sym(List<&2, Bool>, List.drop(&2, Bool, Key.bits(k), 0n), Key.bits(k), Shared.List.drop_zero(&2, Bool, Key.bits(k)))
            )(
              Equal.trans(
                Maybe<&2, List<&2, U32>>,
                Maybe.or(&2, List<&2, U32>, Crit.near(V, m, 0n, Cur.of(k)), None{}),
                Crit.near(V, m, 0n, Cur.of(k)),
                Some{x},
                Shared.Maybe.or_none(List<&2, U32>, Crit.near(V, m, 0n, Cur.of(k))),
                hm
              )
            )({==})(t)
          )
        )
      )

# Crit.upsert_lookup, with m, k and q used more than once
def Crit.upsert_lookup.go(~V: Data, ~f: V -> V -> V, +m: Crit<V>, +k: List<&2, U32>, +v: V, +q: List<&2, U32>) -> {
  Crit.wf(~V, m, 0n) == True{}: Bool
} -> {
  Crit.lookup(V, Crit.upsert(~V, ~f, m, k, v), q)
    == Bool.pick(Maybe<&2, V>, Key.is_eq(q, k), Some{Crit.merge(~V, ~f, Crit.lookup(V, m, k), v)}, Crit.lookup(V, m, q)): Maybe<&2, V>
}:
  h => Crit.upsert_lookup.at(~V, ~f, m, 0n, k, v, q, Crit.near(V, m, 0n, Cur.of(k)))(h)({==})

# a write binds its key, to f of the old value and v when there was one, and
# no other key
law Crit.upsert_lookup:
  for ~V: Data
  for ~f: V -> V -> V
  for m: Crit<V>
  for k: List<&2, U32>
  for v: V
  for q: List<&2, U32>
  {Crit.wf(~V, m, 0n) == True{}: Bool} -> {
    Crit.lookup(V, Crit.upsert(~V, ~f, m, k, v), q)
      == Bool.pick(Maybe<&2, V>, Key.is_eq(q, k), Some{Crit.merge(~V, ~f, Crit.lookup(V, m, k), v)}, Crit.lookup(V, m, q)): Maybe<&2, V>
  }

def Crit.upsert_lookup(ty, f, m, k, v, q):
  Crit.upsert_lookup.go(~ty, ~f, m, k, v, q)

# a drop keeps only keys of the map
def Crit.drop_all(~V: Data, ~G: Data, ~p: G -> List<&2, U32> -> Bool, m: Crit<V>, +at: Nat, +c: Cur, +k: List<&2, U32>, +g: G) -> {
  Crit.all(~V, ~G, ~p, m, g) == True{}: Bool
} -> {Crit.all(~V, ~G, ~p, Crit.drop.go(V, m, at, c, k), g) == True{}: Bool}:
  match m:
    case Crit.Tip{}:
      h => {==}
    case Crit.Leaf{+k2, +w}:
      h => Shared.Bool.when_cases(
        Crit<V>,
        t => {Crit.all(~V, ~G, ~p, t, g) == True{}: Bool},
        Key.is_eq(k2, k),
        u => Crit.Tip{},
        u => Crit.Leaf{k2, w},
        t1 => {==},
        t1 => h
      )
    case Crit.Fork{+rep, +pos, +e, +z, +o}:
      +h => Shared.Bool.when_cases(
        Crit<V>,
        t => {Crit.all(~V, ~G, ~p, t, g) == True{}: Bool},
        Cur.done(Cur.skip(Nat.sub(pos, at), c)),
        u => Shared.Bool.when(Crit<V>, Key.is_eq(rep, k), w => Crit.mk(V, rep, pos, None{}, z, o), w => Crit.Fork{rep, pos, e, z, o}),
        u => Shared.Bool.when(Crit<V>, Cur.bit(Cur.skip(Nat.sub(pos, at), c)), w => Crit.mk(V, rep, pos, e, z, Crit.drop.go(V, o, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), k)), w => Crit.mk(V, rep, pos, e, Crit.drop.go(V, z, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), k), o)),
        t1 => Shared.Bool.when_cases(
          Crit<V>,
          t => {Crit.all(~V, ~G, ~p, t, g) == True{}: Bool},
          Key.is_eq(rep, k),
          w => Crit.mk(V, rep, pos, None{}, z, o),
          w => Crit.Fork{rep, pos, e, z, o},
          t2 => Crit.mk_all(~V, ~G, ~p, rep, pos, None{}, z, o, g)({==})(Crit.all.z(~V, ~G, ~p, rep, pos, e, z, o, g)(h))(Crit.all.o(~V, ~G, ~p, rep, pos, e, z, o, g)(h)),
          t2 => h
        ),
        t1 => Shared.Bool.when_cases(
          Crit<V>,
          t => {Crit.all(~V, ~G, ~p, t, g) == True{}: Bool},
          Cur.bit(Cur.skip(Nat.sub(pos, at), c)),
          w => Crit.mk(V, rep, pos, e, z, Crit.drop.go(V, o, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), k)),
          w => Crit.mk(V, rep, pos, e, Crit.drop.go(V, z, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), k), o),
          t2 => Crit.mk_all(~V, ~G, ~p, rep, pos, e, z, Crit.drop.go(V, o, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), k), g)(Crit.all.hit(~V, ~G, ~p, rep, pos, e, z, o, g)(h))(Crit.all.z(~V, ~G, ~p, rep, pos, e, z, o, g)(h))(Crit.drop_all(~V, ~G, ~p, o, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), k, g)(Crit.all.o(~V, ~G, ~p, rep, pos, e, z, o, g)(h))),
          t2 => Crit.mk_all(~V, ~G, ~p, rep, pos, e, Crit.drop.go(V, z, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), k), o, g)(Crit.all.hit(~V, ~G, ~p, rep, pos, e, z, o, g)(h))(Crit.drop_all(~V, ~G, ~p, z, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), k, g)(Crit.all.z(~V, ~G, ~p, rep, pos, e, z, o, g)(h)))(Crit.all.o(~V, ~G, ~p, rep, pos, e, z, o, g)(h))
        )
      )

# a drop, read from any cursor, keeps a map well formed
def Crit.drop_go_wf(~V: Data, m: Crit<V>, +lo: Nat, +at: Nat, +c: Cur, +k: List<&2, U32>) -> {Crit.wf(~V, m, lo) == True{}: Bool} -> {
  Crit.wf(~V, Crit.drop.go(V, m, at, c, k), lo) == True{}: Bool
}:
  match m:
    case Crit.Tip{}:
      h => {==}
    case Crit.Leaf{+k2, +w}:
      h => Shared.Bool.when_cases(
        Crit<V>,
        t => {Crit.wf(~V, t, lo) == True{}: Bool},
        Key.is_eq(k2, k),
        u => Crit.Tip{},
        u => Crit.Leaf{k2, w},
        t1 => {==},
        t1 => {==}
      )
    case Crit.Fork{+rep, +pos, +e, +z, +o}:
      +h => Shared.Bool.when_cases(
        Crit<V>,
        t => {Crit.wf(~V, t, lo) == True{}: Bool},
        Cur.done(Cur.skip(Nat.sub(pos, at), c)),
        u => Shared.Bool.when(Crit<V>, Key.is_eq(rep, k), w => Crit.mk(V, rep, pos, None{}, z, o), w => Crit.Fork{rep, pos, e, z, o}),
        u => Shared.Bool.when(Crit<V>, Cur.bit(Cur.skip(Nat.sub(pos, at), c)), w => Crit.mk(V, rep, pos, e, z, Crit.drop.go(V, o, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), k)), w => Crit.mk(V, rep, pos, e, Crit.drop.go(V, z, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), k), o)),
        t1 => Shared.Bool.when_cases(
          Crit<V>,
          t => {Crit.wf(~V, t, lo) == True{}: Bool},
          Key.is_eq(rep, k),
          w => Crit.mk(V, rep, pos, None{}, z, o),
          w => Crit.Fork{rep, pos, e, z, o},
          t2 => Crit.mk_wf(~V, rep, pos, None{}, z, o, lo)(Crit.wf.le(~V, rep, pos, e, z, o, lo)(h))({==})(Crit.wf.all_z(~V, rep, pos, e, z, o, lo)(h))(Crit.wf.all_o(~V, rep, pos, e, z, o, lo)(h))(Crit.wf.wf_z(~V, rep, pos, e, z, o, lo)(h))(Crit.wf.wf_o(~V, rep, pos, e, z, o, lo)(h)),
          t2 => h
        ),
        t1 => Shared.Bool.when_cases(
          Crit<V>,
          t => {Crit.wf(~V, t, lo) == True{}: Bool},
          Cur.bit(Cur.skip(Nat.sub(pos, at), c)),
          w => Crit.mk(V, rep, pos, e, z, Crit.drop.go(V, o, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), k)),
          w => Crit.mk(V, rep, pos, e, Crit.drop.go(V, z, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), k), o),
          t2 => Crit.mk_wf(~V, rep, pos, e, z, Crit.drop.go(V, o, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), k), lo)(Crit.wf.le(~V, rep, pos, e, z, o, lo)(h))(Crit.rep_or(V, rep, pos, e, z)(Crit.wf.rep_ok(~V, rep, pos, e, z, o, lo)(h)))(Crit.wf.all_z(~V, rep, pos, e, z, o, lo)(h))(Crit.drop_all(~V, ~Place, ~Place.has, o, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), k, Place{rep, pos, True{}})(Crit.wf.all_o(~V, rep, pos, e, z, o, lo)(h)))(Crit.wf.wf_z(~V, rep, pos, e, z, o, lo)(h))(Crit.drop_go_wf(~V, o, 1n+pos, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), k)(Crit.wf.wf_o(~V, rep, pos, e, z, o, lo)(h))),
          t2 => Crit.mk_wf(~V, rep, pos, e, Crit.drop.go(V, z, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), k), o, lo)(Crit.wf.le(~V, rep, pos, e, z, o, lo)(h))(Crit.rep_or(V, rep, pos, e, z)(Crit.wf.rep_ok(~V, rep, pos, e, z, o, lo)(h)))(Crit.drop_all(~V, ~Place, ~Place.has, z, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), k, Place{rep, pos, False{}})(Crit.wf.all_z(~V, rep, pos, e, z, o, lo)(h)))(Crit.wf.all_o(~V, rep, pos, e, z, o, lo)(h))(Crit.drop_go_wf(~V, z, 1n+pos, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), k)(Crit.wf.wf_z(~V, rep, pos, e, z, o, lo)(h)))(Crit.wf.wf_o(~V, rep, pos, e, z, o, lo)(h))
        )
      )

# a drop keeps a map well formed, with k used more than once
def Crit.drop_wf.at(~V: Data, m: Crit<V>, +k: List<&2, U32>) -> {Crit.wf(~V, m, 0n) == True{}: Bool} -> {
  Crit.wf(~V, Crit.drop(V, m, k), 0n) == True{}: Bool
}:
  h => Crit.drop_go_wf(~V, m, 0n, 0n, Cur.of(k), k)(h)

# a drop keeps a map well formed
law Crit.drop_wf:
  for ~V: Data
  for m: Crit<V>
  for k: List<&2, U32>
  {Crit.wf(~V, m, 0n) == True{}: Bool} -> {Crit.wf(~V, Crit.drop(V, m, k), 0n) == True{}: Bool}

def Crit.drop_wf(ty, m, k):
  Crit.drop_wf.at(~ty, m, k)

# Crit.drop_go_other at a fork, from the cursor c2 at its bit: the drops dz
# and dn of its sides keep each other key
def Crit.drop_fork_other(
  -V: Data,
  +k: List<&2, U32>,
  +rep: List<&2, U32>,
  +pos: Nat,
  +e: Maybe<&2, V>,
  +z: Crit<V>,
  +o: Crit<V>,
  +c2: Cur,
  +dz: Crit<V>,
  +dn: Crit<V>,
  +q: List<&2, U32>
) -> {Key.is_eq(q, k) == False{}: Bool} -> {Crit.lookup(V, dz, q) == Crit.lookup(V, z, q): Maybe<&2, V>} -> {
  Crit.lookup(V, dn, q) == Crit.lookup(V, o, q): Maybe<&2, V>
} -> {
  Crit.lookup(
    V,
    Shared.Bool.when(
      Crit<V>,
      Cur.done(c2),
      u => Shared.Bool.when(Crit<V>, Key.is_eq(rep, k), w => Crit.mk(V, rep, pos, None{}, z, o), w => Crit.Fork{rep, pos, e, z, o}),
      u => Shared.Bool.when(Crit<V>, Cur.bit(c2), w => Crit.mk(V, rep, pos, e, z, dn), w => Crit.mk(V, rep, pos, e, dz, o))
    ),
    q
  )
    == Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, q): Maybe<&2, V>
}:
  +h => iz => io => Shared.Bool.when_cases(
    Crit<V>,
    t => {Crit.lookup(V, t, q) == Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, q): Maybe<&2, V>},
    Cur.done(c2),
    u => Shared.Bool.when(Crit<V>, Key.is_eq(rep, k), w => Crit.mk(V, rep, pos, None{}, z, o), w => Crit.Fork{rep, pos, e, z, o}),
    u => Shared.Bool.when(
      Crit<V>,
      Cur.bit(c2),
      w => Crit.mk(V, rep, pos, e, z, dn),
      w => Crit.mk(V, rep, pos, e, dz, o)
    ),
    hd => Shared.Bool.when_cases(
      Crit<V>,
      t => {Crit.lookup(V, t, q) == Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, q): Maybe<&2, V>},
      Key.is_eq(rep, k),
      w => Crit.mk(V, rep, pos, None{}, z, o),
      w => Crit.Fork{rep, pos, e, z, o},
      hr => Equal.trans(
        Maybe<&2, V>,
        Crit.lookup(V, Crit.mk(V, rep, pos, None{}, z, o), q),
        Maybe.or(&2, V, Crit.lookup(V, z, q), Crit.lookup(V, o, q)),
        Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, q),
        Crit.mk_lookup(V, rep, pos, None{}, z, o, q),
        Crit.or_none_first(V, Crit.ended(V, rep, e, q), Maybe.or(&2, V, Crit.lookup(V, z, q), Crit.lookup(V, o, q)))(
          Crit.ended_ne(V, rep, e, q)(Key.ne_of_eq(rep, k, q)(hr)(h))
        )
      ),
      hr => {==}
    ),
    hd => Shared.Bool.when_cases(
      Crit<V>,
      t => {Crit.lookup(V, t, q) == Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, q): Maybe<&2, V>},
      Cur.bit(c2),
      w => Crit.mk(V, rep, pos, e, z, dn),
      w => Crit.mk(V, rep, pos, e, dz, o),
      hb => Equal.trans(
        Maybe<&2, V>,
        Crit.lookup(V, Crit.mk(V, rep, pos, e, z, dn), q),
        Maybe.or(&2, V, Crit.ended(V, rep, e, q), Maybe.or(&2, V, Crit.lookup(V, z, q), Crit.lookup(V, dn, q))),
        Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, q),
        Crit.mk_lookup(V, rep, pos, e, z, dn, q),
        Equal.cong(
          Maybe<&2, V>,
          Maybe<&2, V>,
          t => Maybe.or(&2, V, Crit.ended(V, rep, e, q), Maybe.or(&2, V, Crit.lookup(V, z, q), t)),
          Crit.lookup(V, dn, q),
          Crit.lookup(V, o, q),
          io
        )
      ),
      hb => Equal.trans(
        Maybe<&2, V>,
        Crit.lookup(V, Crit.mk(V, rep, pos, e, dz, o), q),
        Maybe.or(&2, V, Crit.ended(V, rep, e, q), Maybe.or(&2, V, Crit.lookup(V, dz, q), Crit.lookup(V, o, q))),
        Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, q),
        Crit.mk_lookup(V, rep, pos, e, dz, o, q),
        Equal.cong(
          Maybe<&2, V>,
          Maybe<&2, V>,
          t => Maybe.or(&2, V, Crit.ended(V, rep, e, q), Maybe.or(&2, V, t, Crit.lookup(V, o, q))),
          Crit.lookup(V, dz, q),
          Crit.lookup(V, z, q),
          iz
        )
      )
    )
  )

# a drop, read from any cursor, keeps each key but its own
def Crit.drop_go_other(-V: Data, m: Crit<V>, +at: Nat, +c: Cur, +k: List<&2, U32>, +q: List<&2, U32>) -> {
  Key.is_eq(q, k) == False{}: Bool
} -> {Crit.lookup(V, Crit.drop.go(V, m, at, c, k), q) == Crit.lookup(V, m, q): Maybe<&2, V>}:
  match m:
    case Crit.Tip{}:
      h => {==}
    case Crit.Leaf{+k2, +w}:
      +h => Shared.Bool.when_cases(
        Crit<V>,
        t => {Crit.lookup(V, t, q) == Crit.lookup(V, Crit.Leaf{k2, w}, q): Maybe<&2, V>},
        Key.is_eq(k2, k),
        u => Crit.Tip{},
        u => Crit.Leaf{k2, w},
        hr => Equal.sym(
          Maybe<&2, V>,
          Crit.lookup(V, Crit.Leaf{k2, w}, q),
          None{},
          Crit.when_false(V, Key.is_eq(k2, q), u => Some{w})(Key.ne_of_eq(k2, k, q)(hr)(h))
        ),
        hr => {==}
      )
    case Crit.Fork{+rep, +pos, +e, +z, +o}:
      +h => Crit.drop_fork_other(
        V,
        k,
        rep,
        pos,
        e,
        z,
        o,
        Cur.skip(Nat.sub(pos, at), c),
        Crit.drop.go(V, z, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), k),
        Crit.drop.go(V, o, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), k),
        q
      )(h)(Crit.drop_go_other(V, z, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), k, q)(h))(
        Crit.drop_go_other(V, o, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), k, q)(h)
      )

# Crit.drop_go_none at a fork, from the cursor c2 at its bit, where k's bits
# from the bit are d: the drops dz and dn of its sides hold no k
def Crit.drop_fork_none(
  ~V: Data,
  +k: List<&2, U32>,
  +rep: List<&2, U32>,
  +pos: Nat,
  +e: Maybe<&2, V>,
  +z: Crit<V>,
  +o: Crit<V>,
  +c2: Cur,
  +dz: Crit<V>,
  +dn: Crit<V>,
  d: List<&2, Bool>
) -> {List.drop(&2, Bool, Key.bits(k), pos) == d: List<&2, Bool>} -> {Cur.bits(c2) == d: List<&2, Bool>} -> {
  Crit.rep_ok(V, rep, pos, e, z) == True{}: Bool
} -> {Crit.all(~V, ~Place, ~Place.has, z, Place{rep, pos, False{}}) == True{}: Bool} -> {
  Crit.all(~V, ~Place, ~Place.has, o, Place{rep, pos, True{}}) == True{}: Bool
} -> {Crit.lookup(V, dz, k) == None{}: Maybe<&2, V>} -> {Crit.lookup(V, dn, k) == None{}: Maybe<&2, V>} -> {
  Crit.lookup(
    V,
    Shared.Bool.when(
      Crit<V>,
      Cur.done(c2),
      u => Shared.Bool.when(Crit<V>, Key.is_eq(rep, k), w => Crit.mk(V, rep, pos, None{}, z, o), w => Crit.Fork{rep, pos, e, z, o}),
      u => Shared.Bool.when(Crit<V>, Cur.bit(c2), w => Crit.mk(V, rep, pos, e, z, dn), w => Crit.mk(V, rep, pos, e, dz, o))
    ),
    k
  )
    == None{}: Maybe<&2, V>
}:
  match d:
    case Nil{}:
      +hd => +hc => hr => +az => +ao => iz => io =>
        +nz = Crit.lookup_all(~V, ~Place, ~Place.has, z, Place{rep, pos, False{}}, k)(az)(
          Place.has_not(rep, pos, False{}, k, None{}, Crit.side_drop(k, pos, [])(hd), {==})
        )
        +no = Crit.lookup_all(~V, ~Place, ~Place.has, o, Place{rep, pos, True{}}, k)(ao)(
          Place.has_not(rep, pos, True{}, k, None{}, Crit.side_drop(k, pos, [])(hd), {==})
        )
        Shared.Bool.when_cases(
          Crit<V>,
          t => {Crit.lookup(V, t, k) == None{}: Maybe<&2, V>},
          Cur.done(c2),
          u => Shared.Bool.when(Crit<V>, Key.is_eq(rep, k), w => Crit.mk(V, rep, pos, None{}, z, o), w => Crit.Fork{rep, pos, e, z, o}),
          u => Shared.Bool.when(Crit<V>, Cur.bit(c2), w => Crit.mk(V, rep, pos, e, z, dn), w => Crit.mk(V, rep, pos, e, dz, o)),
          t1 => Shared.Bool.when_cases(
            Crit<V>,
            t => {Crit.lookup(V, t, k) == None{}: Maybe<&2, V>},
            Key.is_eq(rep, k),
            w => Crit.mk(V, rep, pos, None{}, z, o),
            w => Crit.Fork{rep, pos, e, z, o},
            hq => Equal.trans(
              Maybe<&2, V>,
              Crit.lookup(V, Crit.mk(V, rep, pos, None{}, z, o), k),
              Maybe.or(&2, V, Crit.lookup(V, z, k), Crit.lookup(V, o, k)),
              None{},
              Crit.mk_lookup(V, rep, pos, None{}, z, o, k),
              Crit.or3_none(V, None{}, Crit.lookup(V, z, k), Crit.lookup(V, o, k))({==})(nz)(no)
            ),
            hq => Crit.or3_none(V, Crit.ended(V, rep, e, k), Crit.lookup(V, z, k), Crit.lookup(V, o, k))(Crit.ended_ne(V, rep, e, k)(hq))(nz)(no)
          ),
          t1 => Empty.absurd(
            {Crit.lookup(V, Shared.Bool.when(Crit<V>, Cur.bit(c2), w => Crit.mk(V, rep, pos, e, z, dn), w => Crit.mk(V, rep, pos, e, dz, o)), k) == None{}: Maybe<&2, V>},
            Crit.clash(Cur.done(c2), True{}, False{}, Crit.done_of(c2, [])(hc), t1, Shared.Bool.true_ne_false)
          )
        )
    case Con{True{}, +r}:
      +hd => +hc => hr => +az => ao => iz => io =>
        Shared.Bool.when_cases(
          Crit<V>,
          t => {Crit.lookup(V, t, k) == None{}: Maybe<&2, V>},
          Cur.done(c2),
          u => Shared.Bool.when(Crit<V>, Key.is_eq(rep, k), w => Crit.mk(V, rep, pos, None{}, z, o), w => Crit.Fork{rep, pos, e, z, o}),
          u => Shared.Bool.when(Crit<V>, Cur.bit(c2), w => Crit.mk(V, rep, pos, e, z, dn), w => Crit.mk(V, rep, pos, e, dz, o)),
          t1 => Empty.absurd(
            {Crit.lookup(V, Shared.Bool.when(Crit<V>, Key.is_eq(rep, k), w => Crit.mk(V, rep, pos, None{}, z, o), w => Crit.Fork{rep, pos, e, z, o}), k) == None{}: Maybe<&2, V>},
            Crit.clash(Cur.done(c2), False{}, True{}, Crit.done_of(c2, True{} <> r)(hc), t1, Shared.Bool.false_ne_true)
          ),
          t1 => Shared.Bool.when_cases(
            Crit<V>,
            t => {Crit.lookup(V, t, k) == None{}: Maybe<&2, V>},
            Cur.bit(c2),
            w => Crit.mk(V, rep, pos, e, z, dn),
            w => Crit.mk(V, rep, pos, e, dz, o),
            hb => Equal.trans(
              Maybe<&2, V>,
              Crit.lookup(V, Crit.mk(V, rep, pos, e, z, dn), k),
              Maybe.or(&2, V, Crit.ended(V, rep, e, k), Maybe.or(&2, V, Crit.lookup(V, z, k), Crit.lookup(V, dn, k))),
              None{},
              Crit.mk_lookup(V, rep, pos, e, z, dn, k),
              Crit.or3_none(V, Crit.ended(V, rep, e, k), Crit.lookup(V, z, k), Crit.lookup(V, dn, k))(
                Crit.ended_past(V, rep, pos, e, z, k, True{}, r)(hr)(hd)
              )(
                Crit.lookup_all(~V, ~Place, ~Place.has, z, Place{rep, pos, False{}}, k)(az)(
                  Place.has_not(rep, pos, False{}, k, Some{True{}}, Crit.side_drop(k, pos, True{} <> r)(hd), {==})
                )
              )(io)
            ),
            hb => Empty.absurd(
              {Crit.lookup(V, Crit.mk(V, rep, pos, e, dz, o), k) == None{}: Maybe<&2, V>},
              Crit.clash(Cur.bit(c2), True{}, False{}, Crit.bit_of(c2, True{} <> r)(hc), hb, Shared.Bool.true_ne_false)
            )
          )
        )
    case Con{False{}, +r}:
      +hd => +hc => hr => az => +ao => iz => io =>
        Shared.Bool.when_cases(
          Crit<V>,
          t => {Crit.lookup(V, t, k) == None{}: Maybe<&2, V>},
          Cur.done(c2),
          u => Shared.Bool.when(Crit<V>, Key.is_eq(rep, k), w => Crit.mk(V, rep, pos, None{}, z, o), w => Crit.Fork{rep, pos, e, z, o}),
          u => Shared.Bool.when(Crit<V>, Cur.bit(c2), w => Crit.mk(V, rep, pos, e, z, dn), w => Crit.mk(V, rep, pos, e, dz, o)),
          t1 => Empty.absurd(
            {Crit.lookup(V, Shared.Bool.when(Crit<V>, Key.is_eq(rep, k), w => Crit.mk(V, rep, pos, None{}, z, o), w => Crit.Fork{rep, pos, e, z, o}), k) == None{}: Maybe<&2, V>},
            Crit.clash(Cur.done(c2), False{}, True{}, Crit.done_of(c2, False{} <> r)(hc), t1, Shared.Bool.false_ne_true)
          ),
          t1 => Shared.Bool.when_cases(
            Crit<V>,
            t => {Crit.lookup(V, t, k) == None{}: Maybe<&2, V>},
            Cur.bit(c2),
            w => Crit.mk(V, rep, pos, e, z, dn),
            w => Crit.mk(V, rep, pos, e, dz, o),
            hb => Empty.absurd(
              {Crit.lookup(V, Crit.mk(V, rep, pos, e, z, dn), k) == None{}: Maybe<&2, V>},
              Crit.clash(Cur.bit(c2), False{}, True{}, Crit.bit_of(c2, False{} <> r)(hc), hb, Shared.Bool.false_ne_true)
            ),
            hb => Equal.trans(
              Maybe<&2, V>,
              Crit.lookup(V, Crit.mk(V, rep, pos, e, dz, o), k),
              Maybe.or(&2, V, Crit.ended(V, rep, e, k), Maybe.or(&2, V, Crit.lookup(V, dz, k), Crit.lookup(V, o, k))),
              None{},
              Crit.mk_lookup(V, rep, pos, e, dz, o, k),
              Crit.or3_none(V, Crit.ended(V, rep, e, k), Crit.lookup(V, dz, k), Crit.lookup(V, o, k))(
                Crit.ended_past(V, rep, pos, e, z, k, False{}, r)(hr)(hd)
              )(iz)(
                Crit.lookup_all(~V, ~Place, ~Place.has, o, Place{rep, pos, True{}}, k)(ao)(
                  Place.has_not(rep, pos, True{}, k, Some{False{}}, Crit.side_drop(k, pos, False{} <> r)(hd), {==})
                )
              )
            )
          )
        )

# a drop of k, read from k's cursor, from a well formed map, holds no k
def Crit.drop_go_none(~V: Data, m: Crit<V>, +lo: Nat, +at: Nat, +c: Cur, +k: List<&2, U32>) -> {Crit.wf(~V, m, lo) == True{}: Bool} -> {
  Nat.is_le(at, lo) == True{}: Bool
} -> {Cur.bits(c) == List.drop(&2, Bool, Key.bits(k), at): List<&2, Bool>} -> {
  Crit.lookup(V, Crit.drop.go(V, m, at, c, k), k) == None{}: Maybe<&2, V>
}:
  match m:
    case Crit.Tip{}:
      h => l => hc => {==}
    case Crit.Leaf{+k2, +w}:
      h => l => hc => Shared.Bool.when_cases(
        Crit<V>,
        t => {Crit.lookup(V, t, k) == None{}: Maybe<&2, V>},
        Key.is_eq(k2, k),
        u => Crit.Tip{},
        u => Crit.Leaf{k2, w},
        hr => {==},
        hr => Crit.when_false(V, Key.is_eq(k2, k), u => Some{w})(hr)
      )
    case Crit.Fork{+rep, +pos, +e, +z, +o}:
      +h => +l => +hc =>
        +c2 = Cur.skip(Nat.sub(pos, at), c)
        +h2 = Crit.skip_at(k, at, pos, c)(Shared.Nat.le_trans(at, lo, pos)(l)(Crit.wf.le(~V, rep, pos, e, z, o, lo)(h)))(hc)
        Crit.drop_fork_none(
          ~V,
          k,
          rep,
          pos,
          e,
          z,
          o,
          c2,
          Crit.drop.go(V, z, 1n+pos, Cur.next(c2), k),
          Crit.drop.go(V, o, 1n+pos, Cur.next(c2), k),
          List.drop(&2, Bool, Key.bits(k), pos)
        )({==})(h2)(Crit.wf.rep_ok(~V, rep, pos, e, z, o, lo)(h))(Crit.wf.all_z(~V, rep, pos, e, z, o, lo)(h))(
          Crit.wf.all_o(~V, rep, pos, e, z, o, lo)(h)
        )(
          Crit.drop_go_none(~V, z, 1n+pos, 1n+pos, Cur.next(c2), k)(Crit.wf.wf_z(~V, rep, pos, e, z, o, lo)(h))(
            Shared.Nat.le_refl(1n+pos)
          )(Crit.next_at(k, pos, c2)(h2))
        )(
          Crit.drop_go_none(~V, o, 1n+pos, 1n+pos, Cur.next(c2), k)(Crit.wf.wf_o(~V, rep, pos, e, z, o, lo)(h))(
            Shared.Nat.le_refl(1n+pos)
          )(Crit.next_at(k, pos, c2)(h2))
        )

# a drop unbinds its key and no other, in a map well formed below any bit
def Crit.drop_lookup.at(~V: Data, +m: Crit<V>, +lo: Nat, +k: List<&2, U32>, +q: List<&2, U32>) -> {Crit.wf(~V, m, lo) == True{}: Bool} -> {
  Crit.lookup(V, Crit.drop(V, m, k), q) == Bool.pick(Maybe<&2, V>, Key.is_eq(q, k), None{}, Crit.lookup(V, m, q)): Maybe<&2, V>
}:
  h => Equal.sym(
    Maybe<&2, V>,
    Bool.pick(Maybe<&2, V>, Key.is_eq(q, k), None{}, Crit.lookup(V, m, q)),
    Crit.lookup(V, Crit.drop(V, m, k), q),
    Crit.pick_cases(Maybe<&2, V>, Key.is_eq(q, k), None{}, Crit.lookup(V, m, q), Crit.lookup(V, Crit.drop(V, m, k), q))(
      t => (
        %Equal.sym(List<&2, U32>, q, k, Key.is_eq_sound(q, k)(t)): {None{} == Crit.lookup(V, Crit.drop(V, m, k), _): Maybe<&2, V>}
        Equal.sym(
          Maybe<&2, V>,
          Crit.lookup(V, Crit.drop(V, m, k), k),
          None{},
          Crit.drop_go_none(~V, m, lo, 0n, Cur.of(k), k)(h)(Shared.Nat.le_zero(lo))(
            Equal.sym(List<&2, Bool>, List.drop(&2, Bool, Key.bits(k), 0n), Key.bits(k), Shared.List.drop_zero(&2, Bool, Key.bits(k)))
          )
        )
      )
    )(
      f => Equal.sym(
        Maybe<&2, V>,
        Crit.lookup(V, Crit.drop(V, m, k), q),
        Crit.lookup(V, m, q),
        Crit.drop_go_other(V, m, 0n, Cur.of(k), k, q)(f)
      )
    )
  )

# a drop unbinds its key and no other
law Crit.drop_lookup:
  for ~V: Data
  for m: Crit<V>
  for k: List<&2, U32>
  for q: List<&2, U32>
  {Crit.wf(~V, m, 0n) == True{}: Bool} -> {Crit.lookup(V, Crit.drop(V, m, k), q) == Bool.pick(Maybe<&2, V>, Key.is_eq(q, k), None{}, Crit.lookup(V, m, q)): Maybe<&2, V>}

def Crit.drop_lookup(ty, m, k, q):
  Crit.drop_lookup.at(~ty, m, 0n, k, q)

# a pick between nothing and nothing is nothing
def Crit.pick_none(-A: Data, c: Bool) -> {Bool.pick(Maybe<&2, A>, c, None{}, None{}) == None{}: Maybe<&2, A>}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

# a pick between nothing and a that is nothing is nothing
def Crit.pick_none2(-A: Data, +c: Bool, a: Maybe<&2, A>) -> {a == None{}: Maybe<&2, A>} -> {Bool.pick(Maybe<&2, A>, c, None{}, a) == None{}: Maybe<&2, A>}:
  h =>
    %Equal.sym(Maybe<&2, A>, a, None{}, h): {Bool.pick(Maybe<&2, A>, c, None{}, _) == None{}: Maybe<&2, A>}
    Crit.pick_none(A, c)

# a pick between nothing and the value of a key, by whether the same key
# holds, is nothing
def Crit.pick_when(-V: Data, b: Bool, -w: V, -u: V) -> {
  Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Shared.Maybe.when(V, b, x => Some{w})), None{}, Shared.Maybe.when(V, b, x => Some{u})) == None{}: Maybe<&2, V>
}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# a value that is not some is none
def Crit.none_by(-V: Data, m: Maybe<&2, V>) -> ({Maybe.is_some(&2, V, m) == True{}: Bool} -> Empty) -> {m == None{}: Maybe<&2, V>}:
  match m:
    case None{}:
      f => {==}
    case Some{x}:
      f => Empty.absurd({Some{x} == None{}: Maybe<&2, V>}, f({==}))

# a value that is nothing wherever b holds is the pick between nothing and it
def Crit.pick_disj(-V: Data, lb: Maybe<&2, V>, -la: Maybe<&2, V>) -> ({Maybe.is_some(&2, V, lb) == True{}: Bool} -> {la == None{}: Maybe<&2, V>}) -> {
  la == Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, lb), None{}, la): Maybe<&2, V>
}:
  match lb:
    case None{}:
      f => {==}
    case Some{w}:
      f => f({==})

# picks between nothing and a value, by tests that agree where it is some
def Crit.pick_same(-V: Data, la: Maybe<&2, V>, c1: Bool, c2: Bool) -> ({Maybe.is_some(&2, V, la) == True{}: Bool} -> {c1 == c2: Bool}) -> {
  Bool.pick(Maybe<&2, V>, c1, None{}, la) == Bool.pick(Maybe<&2, V>, c2, None{}, la): Maybe<&2, V>
}:
  match la:
    case None{}:
      f => Equal.trans(Maybe<&2, V>, Bool.pick(Maybe<&2, V>, c1, None{}, None{}), None{}, Bool.pick(Maybe<&2, V>, c2, None{}, None{}), Crit.pick_none(V, c1), Equal.sym(Maybe<&2, V>, Bool.pick(Maybe<&2, V>, c2, None{}, None{}), None{}, Crit.pick_none(V, c2)))
    case Some{+u}:
      f => Equal.cong(Bool, Maybe<&2, V>, t => Bool.pick(Maybe<&2, V>, t, None{}, Some{u}), c1, c2, f({==}))

# an "and" of two true tests is true
def Crit.and_true(a: Bool, +b: Bool) -> {a == True{}: Bool} -> {b == True{}: Bool} -> {Bool.and(a, b) == True{}: Bool}:
  match a:
    case True{}:
      ha => hb => hb
    case False{}:
      ha => hb => Empty.absurd({False{} == True{}: Bool}, Shared.Bool.false_ne_true(ha))

# numbers that compare less are less
def Crit.cmp_lt(+a: Nat, +b: Nat) -> {Nat.cmp(a, b) == LT{}: Cmp} -> {Nat.is_lt(a, b) == True{}: Bool}:
  h =>
    %Equal.sym(Cmp, Nat.cmp(a, b), LT{}, h): {Cmp.is_lt(_) == True{}: Bool}
    {==}

# numbers that compare more: the second is less
def Crit.cmp_gt(a: Nat, b: Nat) -> {Nat.cmp(a, b) == GT{}: Cmp} -> {Nat.is_lt(b, a) == True{}: Bool}:
  match a b:
    case 0n 0n:
      h => Empty.absurd({Nat.is_lt(0n, 0n) == True{}: Bool}, Shared.Bool.true_ne_false(Equal.cong(Cmp, Bool, c => Cmp.is_eq(c), EQ{}, GT{}, h)))
    case 0n 1n+q:
      h => Empty.absurd({Nat.is_lt(1n+q, 0n) == True{}: Bool}, Shared.Bool.true_ne_false(Equal.cong(Cmp, Bool, c => Cmp.is_lt(c), LT{}, GT{}, h)))
    case 1n+p 0n:
      h => {==}
    case 1n+p 1n+q:
      Crit.cmp_gt(p, q)

# numbers that compare equal are equal
def Crit.cmp_eq(+a: Nat, +b: Nat) -> {Nat.cmp(a, b) == EQ{}: Cmp} -> {a == b: Nat}:
  h => Shared.Nat.is_eq_sound(a, b)((
    %Equal.sym(Cmp, Nat.cmp(a, b), EQ{}, h): {Cmp.is_eq(_) == True{}: Bool}
    {==}
  ))

# a difference before the lower of two bits, when it is not before both
def Crit.above_lt_left(d: Maybe<&2, Nat>, +pa: Nat, +pb: Nat) -> {Bool.and(Crit.above(d, pa), Crit.above(d, pb)) == False{}: Bool} -> {
  Nat.is_lt(pa, pb) == True{}: Bool
} -> {Crit.above(d, pa) == False{}: Bool}:
  match d:
    case None{}:
      h => l => {==}
    case Some{+x}:
      +h => +l => Crit.false_of(Nat.is_lt(x, pa))(
        +t => Crit.clash(
          Bool.and(Nat.is_lt(x, pa), Nat.is_lt(x, pb)),
          True{},
          False{},
          Crit.and_true(Nat.is_lt(x, pa), Nat.is_lt(x, pb))(t)(Shared.Nat.lt_le(x, pa, pb)(t)(Shared.Nat.lt_weak(pa, pb)(l))),
          h,
          Shared.Bool.true_ne_false
        )
      )

# a difference before the lower second of two bits, when it is not before both
def Crit.above_lt_right(d: Maybe<&2, Nat>, +pa: Nat, +pb: Nat) -> {Bool.and(Crit.above(d, pa), Crit.above(d, pb)) == False{}: Bool} -> {
  Nat.is_lt(pb, pa) == True{}: Bool
} -> {Crit.above(d, pb) == False{}: Bool}:
  match d:
    case None{}:
      h => l => {==}
    case Some{+x}:
      +h => +l => Crit.false_of(Nat.is_lt(x, pb))(
        +t => Crit.clash(
          Bool.and(Nat.is_lt(x, pa), Nat.is_lt(x, pb)),
          True{},
          False{},
          Crit.and_true(Nat.is_lt(x, pa), Nat.is_lt(x, pb))(Shared.Nat.lt_le(x, pb, pa)(t)(Shared.Nat.lt_weak(pb, pa)(l)))(t),
          h,
          Shared.Bool.true_ne_false
        )
      )

# a difference not before a bit and itself is not before it
def Crit.above_eq(+d: Maybe<&2, Nat>, +p: Nat) -> {Bool.and(Crit.above(d, p), Crit.above(d, p)) == False{}: Bool} -> {Crit.above(d, p) == False{}: Bool}:
  +h => Crit.false_of(Crit.above(d, p))(
    +t => Crit.clash(Bool.and(Crit.above(d, p), Crit.above(d, p)), True{}, False{}, Crit.and_true(Crit.above(d, p), Crit.above(d, p))(t)(t), h, Shared.Bool.true_ne_false)
  )

# a key with a side at pos has bits from pos on
def Crit.side_some_ne(+q: List<&2, U32>, +pos: Nat, +b: Bool) -> {Key.side(q, pos) == Some{b}: Maybe<&2, Bool>} -> {
  List.is_empty(&2, Bool, List.drop(&2, Bool, Key.bits(q), pos)) == False{}: Bool
}:
  hs => Crit.head_ne(List.drop(&2, Bool, Key.bits(q), pos), b)(
    Equal.trans(
      Maybe<&2, Bool>,
      Bits.head(List.drop(&2, Bool, Key.bits(q), pos)),
      Key.side(q, pos),
      Some{b},
      Equal.sym(Maybe<&2, Bool>, Key.side(q, pos), Bits.head(List.drop(&2, Bool, Key.bits(q), pos)), Crit.side_drop(q, pos, List.drop(&2, Bool, Key.bits(q), pos))({==})),
      hs
    )
  )

# a list with no head is empty
def Crit.head_none(xs: List<&2, Bool>) -> {Bits.head(xs) == None{}: Maybe<&2, Bool>} -> {xs == []: List<&2, Bool>}:
  match xs:
    case Nil{}:
      h => {==}
    case Con{x, r}:
      h => Empty.absurd({x <> r == []: List<&2, Bool>}, Crit.some_ne_none(Bool, x, h))

# a key with no side at pos has no bits from pos on
def Crit.side_nil(+q: List<&2, U32>, +pos: Nat) -> {Key.side(q, pos) == None{}: Maybe<&2, Bool>} -> {List.drop(&2, Bool, Key.bits(q), pos) == []: List<&2, Bool>}:
  hs => Crit.head_none(List.drop(&2, Bool, Key.bits(q), pos))(
    Equal.trans(
      Maybe<&2, Bool>,
      Bits.head(List.drop(&2, Bool, Key.bits(q), pos)),
      Key.side(q, pos),
      None{},
      Equal.sym(Maybe<&2, Bool>, Key.side(q, pos), Bits.head(List.drop(&2, Bool, Key.bits(q), pos)), Crit.side_drop(q, pos, List.drop(&2, Bool, Key.bits(q), pos))({==})),
      hs
    )
  )

# Crit.side_split, once the side s is known
def Crit.side_split.at(-T: Type, +q: List<&2, U32>, +pos: Nat, s: Maybe<&2, Bool>) -> {Key.side(q, pos) == s: Maybe<&2, Bool>} -> (
  {Key.side(q, pos) == Some{True{}}: Maybe<&2, Bool>} -> T
) -> ({Key.side(q, pos) == Some{False{}}: Maybe<&2, Bool>} -> T) -> ({Key.side(q, pos) == None{}: Maybe<&2, Bool>} -> T) -> T:
  match s:
    case None{}:
      e => f1 => f2 => f3 => f3(e)
    case Some{True{}}:
      e => f1 => f2 => f3 => f1(e)
    case Some{False{}}:
      e => f1 => f2 => f3 => f2(e)

# what holds for each side of a key at pos holds
def Crit.side_split(-T: Type, +q: List<&2, U32>, +pos: Nat) -> ({Key.side(q, pos) == Some{True{}}: Maybe<&2, Bool>} -> T) -> (
  {Key.side(q, pos) == Some{False{}}: Maybe<&2, Bool>} -> T
) -> ({Key.side(q, pos) == None{}: Maybe<&2, Bool>} -> T) -> T:
  Crit.side_split.at(T, q, pos, Key.side(q, pos))({==})

# a read of a well formed fork at a key on its side b is a read of that side
def Crit.route_side(~V: Data, +rep: List<&2, U32>, +pos: Nat, +e: Maybe<&2, V>, +z: Crit<V>, +o: Crit<V>, +lo: Nat, +q: List<&2, U32>, b: Bool) -> {
  Crit.wf(~V, Crit.Fork{rep, pos, e, z, o}, lo) == True{}: Bool
} -> {Key.side(q, pos) == Some{b}: Maybe<&2, Bool>} -> {
  Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, q) == Crit.lookup(V, Bool.pick(Crit<V>, b, o, z), q): Maybe<&2, V>
}:
  match b:
    case True{}:
      +h => +hs => Crit.or_third(V, Crit.ended(V, rep, e, q), Crit.lookup(V, z, q), Crit.lookup(V, o, q))(
        Crit.ended_long(V, rep, pos, e, z, q, List.drop(&2, Bool, Key.bits(q), pos))(Crit.wf.rep_ok(~V, rep, pos, e, z, o, lo)(h))({==})(Crit.side_some_ne(q, pos, True{})(hs))
      )(Crit.lookup_all(~V, ~Place, ~Place.has, z, Place{rep, pos, False{}}, q)(Crit.wf.all_z(~V, rep, pos, e, z, o, lo)(h))(Place.has_not(rep, pos, False{}, q, Some{True{}}, hs, {==})))
    case False{}:
      +h => +hs => Crit.or_second(V, Crit.ended(V, rep, e, q), Crit.lookup(V, z, q), Crit.lookup(V, o, q))(
        Crit.ended_long(V, rep, pos, e, z, q, List.drop(&2, Bool, Key.bits(q), pos))(Crit.wf.rep_ok(~V, rep, pos, e, z, o, lo)(h))({==})(Crit.side_some_ne(q, pos, False{})(hs))
      )(Crit.lookup_all(~V, ~Place, ~Place.has, o, Place{rep, pos, True{}}, q)(Crit.wf.all_o(~V, rep, pos, e, z, o, lo)(h))(Place.has_not(rep, pos, True{}, q, Some{False{}}, hs, {==})))

# a read of a well formed fork at a key that ends at its bit is its end
def Crit.route_end(~V: Data, +rep: List<&2, U32>, +pos: Nat, +e: Maybe<&2, V>, +z: Crit<V>, +o: Crit<V>, +lo: Nat, +q: List<&2, U32>) -> {
  Crit.wf(~V, Crit.Fork{rep, pos, e, z, o}, lo) == True{}: Bool
} -> {Key.side(q, pos) == None{}: Maybe<&2, Bool>} -> {Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, q) == Crit.ended(V, rep, e, q): Maybe<&2, V>}:
  +h => hs =>
    +nil = Crit.side_nil(q, pos)(hs)
    Crit.or_first(V, Crit.ended(V, rep, e, q), Crit.lookup(V, z, q), Crit.lookup(V, o, q))(
      Crit.no_side(~V, rep, pos, z, False{}, q)(Crit.wf.all_z(~V, rep, pos, e, z, o, lo)(h))(nil)
    )(Crit.no_side(~V, rep, pos, o, True{}, q)(Crit.wf.all_o(~V, rep, pos, e, z, o, lo)(h))(nil))

# a test that is not False is True
def Crit.true_of(b: Bool) -> ({b == False{}: Bool} -> Empty) -> {b == True{}: Bool}:
  match b:
    case True{}:
      h => {==}
    case False{}:
      h => Empty.absurd({False{} == True{}: Bool}, h({==}))

# a key that a map holds, whose keys are on a side, is on that side
def Crit.in_place(~V: Data, +m: Crit<V>, +g: Place, +q: List<&2, U32>) -> {Crit.all(~V, ~Place, ~Place.has, m, g) == True{}: Bool} -> {
  Maybe.is_some(&2, V, Crit.lookup(V, m, q)) == True{}: Bool
} -> {Place.has(g, q) == True{}: Bool}:
  +a => +s => Crit.true_of(Place.has(g, q))(
    t => Crit.clash(
      Maybe.is_some(&2, V, Crit.lookup(V, m, q)),
      True{},
      False{},
      s,
      Equal.cong(Maybe<&2, V>, Bool, x => Maybe.is_some(&2, V, x), Crit.lookup(V, m, q), None{}, Crit.lookup_all(~V, ~Place, ~Place.has, m, g, q)(a)(t)),
      Shared.Bool.true_ne_false
    )
  )

# a key on a side of a fork has that side at its bit
def Place.has_side(+r: List<&2, U32>, +pos: Nat, +b: Bool, +q: List<&2, U32>) -> {Place.has(Place{r, pos, b}, q) == True{}: Bool} -> {
  Key.side(q, pos) == Some{b}: Maybe<&2, Bool>
}:
  h => Shared.Maybe.is_eq_sound(~Bool, ~Shared.Bool.is_eq, x1 => y1 => Shared.Bool.is_eq_sound(x1, y1), Key.side(q, pos), Some{b})(
    Shared.List.all.if_rest(Key.agree(q, r, pos), u => Shared.Maybe.is_eq(~Bool, ~Shared.Bool.is_eq, Key.side(q, pos), Some{b}))(h)
  )

# a key that a well formed fork holds agrees with its rep before its bit
def Crit.in_fork_agree(~V: Data, +rep: List<&2, U32>, +pos: Nat, +e: Maybe<&2, V>, +z: Crit<V>, +o: Crit<V>, +lo: Nat, +q: List<&2, U32>) -> {
  Crit.wf(~V, Crit.Fork{rep, pos, e, z, o}, lo) == True{}: Bool
} -> {Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, q)) == True{}: Bool} -> {Key.agree(q, rep, pos) == True{}: Bool}:
  +h => +s => Crit.true_of(Key.agree(q, rep, pos))(
    t => Crit.clash(
      Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, q)),
      True{},
      False{},
      s,
      Equal.cong(Maybe<&2, V>, Bool, x => Maybe.is_some(&2, V, x), Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, q), None{}, Crit.not_in_fork(~V, rep, pos, e, z, o, lo, q)(h)(t)),
      Shared.Bool.true_ne_false
    )
  )

# the end of a fork of two ends, the first unless the second is some, read
# at q
def Crit.ended_pick(-V: Data, +ra: List<&2, U32>, eb: Maybe<&2, V>, ea: Maybe<&2, V>, +q: List<&2, U32>) -> {Crit.ended(V, ra, ea, q) == None{}: Maybe<&2, V>} -> {
  Crit.ended(V, ra, Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, eb), None{}, ea), q) == None{}: Maybe<&2, V>
}:
  match eb:
    case None{}:
      h => h
    case Some{w}:
      h => {==}

# the end of a difference of two forks at one bit: the end of a, unless b
# has one, read at q
def Crit.ends_minus(
  -V: Data,
  +ra: List<&2, U32>,
  +pa: Nat,
  ea: Maybe<&2, V>,
  -za: Crit<V>,
  +rb: List<&2, U32>,
  +pb: Nat,
  eb: Maybe<&2, V>,
  -zb: Crit<V>,
  +q: List<&2, U32>
) -> {Crit.rep_ok(V, ra, pa, ea, za) == True{}: Bool} -> {Crit.rep_ok(V, rb, pb, eb, zb) == True{}: Bool} -> {pa == pb: Nat} -> {
  Crit.above(Key.diff(ra, rb), pa) == False{}: Bool
} -> {
  Crit.ended(V, ra, Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, eb), None{}, ea), q)
    == Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.ended(V, rb, eb, q)), None{}, Crit.ended(V, ra, ea, q)): Maybe<&2, V>
}:
  match ea eb:
    case None{} None{}:
      hra => hrb => eqp => hab => {==}
    case Some{u} None{}:
      hra => hrb => eqp => hab => {==}
    case None{} Some{w}:
      hra => hrb => eqp => hab => Equal.sym(
        Maybe<&2, V>,
        Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Shared.Maybe.when(V, Key.is_eq(rb, q), x => Some{w})), None{}, None{}),
        None{},
        Crit.pick_none(V, Maybe.is_some(&2, V, Shared.Maybe.when(V, Key.is_eq(rb, q), x => Some{w})))
      )
    case Some{u} Some{w}:
      hra => hrb => eqp => hab =>
        %Key.is_eq_sound(rb, ra)(
          Crit.end_is(rb, pa, ra)((
            %Equal.sym(Nat, pa, pb, eqp): {Nat.is_eq(List.length(&2, Bool, Key.bits(rb)), _) == True{}: Bool}
            hrb
          ))((
            %Shared.Nat.is_eq_sound(List.length(&2, Bool, Key.bits(ra)), pa)(hra): {
              List.drop(&2, Bool, Key.bits(ra), _) == []: List<&2, Bool>
            }
            Crit.drop_length(Key.bits(ra))
          ))(hab)
        ): {
          None{} == Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Shared.Maybe.when(V, Key.is_eq(rb, q), x => Some{w})), None{}, Shared.Maybe.when(V, Key.is_eq(_, q), x => Some{u})): Maybe<&2, V>
        }
        Equal.sym(
          Maybe<&2, V>,
          Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Shared.Maybe.when(V, Key.is_eq(rb, q), x => Some{w})), None{}, Shared.Maybe.when(V, Key.is_eq(rb, q), x => Some{u})),
          None{},
          Crit.pick_when(V, Key.is_eq(rb, q), w, u)
        )

# Crit.is_some_when, once the test of q and k is known
def Crit.is_some_when.at(-V: Data, +k: List<&2, U32>, +q: List<&2, U32>, -w: V, b: Bool) -> {Key.is_eq(q, k) == b: Bool} -> {
  Maybe.is_some(&2, V, Shared.Maybe.when(V, Key.is_eq(k, q), u => Some{w})) == b: Bool
}:
  match b:
    case True{}:
      e =>
        %Equal.sym(List<&2, U32>, q, k, Key.is_eq_sound(q, k)(e)): {Maybe.is_some(&2, V, Shared.Maybe.when(V, Key.is_eq(k, _), u => Some{w})) == True{}: Bool}
        %Equal.sym(Bool, Key.is_eq(k, k), True{}, Key.is_eq_refl(k)): {Maybe.is_some(&2, V, Shared.Maybe.when(V, _, u => Some{w})) == True{}: Bool}
        {==}
    case False{}:
      e =>
        %Equal.sym(Bool, Key.is_eq(k, q), False{}, Key.ne_sym(q, k)(e)): {Maybe.is_some(&2, V, Shared.Maybe.when(V, _, u => Some{w})) == False{}: Bool}
        {==}

# an entry holds q exactly when q is its key
def Crit.is_some_when(-V: Data, +k: List<&2, U32>, +q: List<&2, U32>, -w: V) -> {
  Maybe.is_some(&2, V, Shared.Maybe.when(V, Key.is_eq(k, q), u => Some{w})) == Key.is_eq(q, k): Bool
}:
  Crit.is_some_when.at(V, k, q, w, Key.is_eq(q, k))({==})

# the keys on a side of a fork are on the same side, named by an equal bit
def Crit.all_place_b(~V: Data, +m: Crit<V>, +r: List<&2, U32>, +pos: Nat, b1: Bool, +b2: Bool) -> {b1 == b2: Bool} -> {
  Crit.all(~V, ~Place, ~Place.has, m, Place{r, pos, b1}) == True{}: Bool
} -> {Crit.all(~V, ~Place, ~Place.has, m, Place{r, pos, b2}) == True{}: Bool}:
  e => h =>
    %e: {Crit.all(~V, ~Place, ~Place.has, m, Place{r, pos, _}) == True{}: Bool}
    h

# the keys of a and of b are on one side of a fork at the bit before lo
# (r and s: its rep and side), or lo is 0
def Crit.fits(~V: Data, a: Crit<V>, b: Crit<V>, lo: Nat, +r: List<&2, U32>, +s: Bool) -> Bool:
  match lo:
    case 0n:
      True{}
    case 1n+(+p):
      Bool.and(Crit.all(~V, ~Place, ~Place.has, a, Place{r, p, s}), Crit.all(~V, ~Place, ~Place.has, b, Place{r, p, s}))

# Crit.fits either way round
def Crit.fits_swap(~V: Data, +a: Crit<V>, +b: Crit<V>, lo: Nat, +r: List<&2, U32>, +s: Bool) -> {Crit.fits(~V, a, b, lo, r, s) == True{}: Bool} -> {
  Crit.fits(~V, b, a, lo, r, s) == True{}: Bool
}:
  match lo:
    case 0n:
      h => {==}
    case 1n+(+p):
      +h => Crit.and_true(Crit.all(~V, ~Place, ~Place.has, b, Place{r, p, s}), Crit.all(~V, ~Place, ~Place.has, a, Place{r, p, s}))(
        Shared.Bool.and_true_right(Crit.all(~V, ~Place, ~Place.has, a, Place{r, p, s}), Crit.all(~V, ~Place, ~Place.has, b, Place{r, p, s}))(h)
      )(Shared.Bool.and_true_left(Crit.all(~V, ~Place, ~Place.has, a, Place{r, p, s}), Crit.all(~V, ~Place, ~Place.has, b, Place{r, p, s}))(h))

# keys on one side of a fork agree on one bit past it
def Crit.fit_agree(+k: List<&2, U32>, +x: List<&2, U32>, +r: List<&2, U32>, +p: Nat, +s: Bool) -> {Place.has(Place{r, p, s}, k) == True{}: Bool} -> {
  Place.has(Place{r, p, s}, x) == True{}: Bool
} -> {Key.agree(k, x, 1n+p) == True{}: Bool}:
  +hk => +hx => Key.agree_succ(k, x, p, s)(Key.agree_join(k, x, r, p)(Place.has_agree(r, p, s, k)(hk))(Place.has_agree(r, p, s, x)(hx)))(
    Place.has_side(r, p, s, k)(hk)
  )(Place.has_side(r, p, s, x)(hx))

# k fits a well formed map m at lo: it agrees with the key a read of m reaches
def Crit.fit_hi(~V: Data, +m: Crit<V>, +k: List<&2, U32>, -v: V, +x: List<&2, U32>, +r: List<&2, U32>, +s: Bool, lo: Nat) -> {Crit.wf(~V, m, lo) == True{}: Bool} -> {
  Crit.near(V, m, 0n, Cur.of(k)) == Some{x}: Maybe<&2, List<&2, U32>>
} -> {Crit.fits(~V, Crit.Leaf{k, v}, m, lo, r, s) == True{}: Bool} -> {Bool.or(Crit.is_tip(V, m), Bits.agree(Key.diff(k, x), lo)) == True{}: Bool}:
  match lo:
    case 0n:
      h => hm => hf => Crit.or_right(Crit.is_tip(V, m), Bits.agree(Key.diff(k, x), 0n))(Bits.agree.zero(Key.diff(k, x)))
    case 1n+(+p):
      h => hm => +hf => Crit.or_right(Crit.is_tip(V, m), Bits.agree(Key.diff(k, x), 1n+p))(
        Crit.fit_agree(k, x, r, p, s)(Shared.Bool.and_true_left(Place.has(Place{r, p, s}, k), Crit.all(~V, ~Place, ~Place.has, m, Place{r, p, s}))(hf))(
          Crit.near_pass(~V, ~Place, ~Place.has, m, 1n+p, 0n, Cur.of(k), Place{r, p, s}, x)(h)(Shared.Bool.and_true_right(Place.has(Place{r, p, s}, k), Crit.all(~V, ~Place, ~Place.has, m, Place{r, p, s}))(hf))(hm)
        )
      )

# Crit.upsert_fit, once the key that a read of k reaches is known (nm)
def Crit.upsert_fit.at(~V: Data, ~f: V -> V -> V, +m: Crit<V>, +lo: Nat, +k: List<&2, U32>, +v: V, +r: List<&2, U32>, +s: Bool, nm: Maybe<&2, List<&2, U32>>) -> {Crit.wf(~V, m, lo) == True{}: Bool} -> {
  Crit.near(V, m, 0n, Cur.of(k)) == nm: Maybe<&2, List<&2, U32>>
} -> {Crit.fits(~V, Crit.Leaf{k, v}, m, lo, r, s) == True{}: Bool} -> {Crit.wf(~V, Crit.put(~V, ~f, m, 0n, Cur.of(k), k, v, Crit.diff(k, nm)), lo) == True{}: Bool}:
  match nm:
    case None{}:
      h => hm => hf => Crit.put_wf(~V, ~f, m, lo, 0n, Cur.of(k), k, v, None{}, Some{k}, k)(h)(Shared.Nat.le_zero(lo))(
        Equal.sym(List<&2, Bool>, List.drop(&2, Bool, Key.bits(k), 0n), Key.bits(k), Shared.List.drop_zero(&2, Bool, Key.bits(k)))
      )(
        %Equal.sym(Maybe<&2, List<&2, U32>>, Crit.near(V, m, 0n, Cur.of(k)), None{}, hm): {Maybe.or(&2, List<&2, U32>, _, Some{k}) == Some{k}: Maybe<&2, List<&2, U32>>}
        {==}
      )(Equal.sym(Maybe<&2, Nat>, Key.diff(k, k), None{}, Key.diff_self(k)))(Shared.Bool.or_true_right(Crit.is_tip(V, m)))
    case Some{+x}:
      +h => +hm => hf => Crit.put_wf(~V, ~f, m, lo, 0n, Cur.of(k), k, v, Key.diff(k, x), None{}, x)(h)(Shared.Nat.le_zero(lo))(
        Equal.sym(List<&2, Bool>, List.drop(&2, Bool, Key.bits(k), 0n), Key.bits(k), Shared.List.drop_zero(&2, Bool, Key.bits(k)))
      )(Equal.trans(Maybe<&2, List<&2, U32>>, Maybe.or(&2, List<&2, U32>, Crit.near(V, m, 0n, Cur.of(k)), None{}), Crit.near(V, m, 0n, Cur.of(k)), Some{x}, Shared.Maybe.or_none(List<&2, U32>, Crit.near(V, m, 0n, Cur.of(k))), hm))({==})(
        Crit.fit_hi(~V, m, k, v, x, r, s, lo)(h)(hm)(hf)
      )

# a write of a key that fits a well formed map keeps it well formed
def Crit.upsert_fit(~V: Data, ~f: V -> V -> V, +m: Crit<V>, +lo: Nat, +k: List<&2, U32>, +v: V, +r: List<&2, U32>, +s: Bool) -> {Crit.wf(~V, m, lo) == True{}: Bool} -> {
  Crit.fits(~V, Crit.Leaf{k, v}, m, lo, r, s) == True{}: Bool
} -> {Crit.wf(~V, Crit.upsert(~V, ~f, m, k, v), lo) == True{}: Bool}:
  h => hf => Crit.upsert_fit.at(~V, ~f, m, lo, k, v, r, s, Crit.near(V, m, 0n, Cur.of(k)))(h)({==})(hf)

# a fork of two maps whose first keys end at its bit, or not, passes p when both do
def Crit.join_end_all.any(~V: Data, ~G: Data, ~p: G -> List<&2, U32> -> Bool, x: Crit<V>, +y: Crit<V>, +d: Nat, b: Bool, +g: G) -> {Crit.all(~V, ~G, ~p, x, g) == True{}: Bool} -> {
  Crit.all(~V, ~G, ~p, y, g) == True{}: Bool
} -> {Crit.all(~V, ~G, ~p, Crit.join.end(V, x, y, d, b), g) == True{}: Bool}:
  match x b:
    case Crit.Leaf{+k, +v} True{}:
      hx => hy => Crit.all.intro(~V, ~G, ~p, k, d, Some{v}, Crit.Tip{}, y, g)(hx)({==})(hy)
    case Crit.Leaf{+k, +v} False{}:
      hx => hy => Crit.all.intro(~V, ~G, ~p, k, d, Some{v}, y, Crit.Tip{}, g)(hx)(hy)({==})
    case Crit.Tip{} b1:
      hx => hy => Crit.all.intro(~V, ~G, ~p, [], d, None{}, Crit.Tip{}, y, g)({==})({==})(hy)
    case Crit.Fork{+r, +q, +e, +z, +o} b1:
      hx => hy => Crit.all.intro(~V, ~G, ~p, r, d, None{}, Crit.Fork{r, q, e, z, o}, y, g)({==})(hx)(hy)

# a fork of two maps passes p when both do
def Crit.join_all.any(~V: Data, ~G: Data, ~p: G -> List<&2, U32> -> Bool, +x: Crit<V>, +y: Crit<V>, +d: Nat, +g: G) -> {Crit.all(~V, ~G, ~p, x, g) == True{}: Bool} -> {
  Crit.all(~V, ~G, ~p, y, g) == True{}: Bool
} -> {Crit.all(~V, ~G, ~p, Crit.join(V, x, y, d), g) == True{}: Bool}:
  +hx => +hy => Shared.Bool.when_cases(
    Crit<V>,
    t => {Crit.all(~V, ~G, ~p, t, g) == True{}: Bool},
    Cur.done(Key.at(Crit.rep(V, x, []), d)),
    u => Crit.join.end(V, x, y, d, Cur.bit(Key.at(Crit.rep(V, y, []), d))),
    u => Shared.Bool.when(
      Crit<V>,
      Cur.done(Key.at(Crit.rep(V, y, []), d)),
      q1 => Crit.join.end(V, y, x, d, Cur.bit(Key.at(Crit.rep(V, x, []), d))),
      q1 => Shared.Bool.when(Crit<V>, Cur.bit(Key.at(Crit.rep(V, x, []), d)), q2 => Crit.Fork{Crit.rep(V, y, []), d, None{}, y, x}, q2 => Crit.Fork{Crit.rep(V, x, []), d, None{}, x, y})
    ),
    t1 => Crit.join_end_all.any(~V, ~G, ~p, x, y, d, Cur.bit(Key.at(Crit.rep(V, y, []), d)), g)(hx)(hy),
    t1 => Shared.Bool.when_cases(
      Crit<V>,
      t => {Crit.all(~V, ~G, ~p, t, g) == True{}: Bool},
      Cur.done(Key.at(Crit.rep(V, y, []), d)),
      q1 => Crit.join.end(V, y, x, d, Cur.bit(Key.at(Crit.rep(V, x, []), d))),
      q1 => Shared.Bool.when(Crit<V>, Cur.bit(Key.at(Crit.rep(V, x, []), d)), q2 => Crit.Fork{Crit.rep(V, y, []), d, None{}, y, x}, q2 => Crit.Fork{Crit.rep(V, x, []), d, None{}, x, y}),
      t2 => Crit.join_end_all.any(~V, ~G, ~p, y, x, d, Cur.bit(Key.at(Crit.rep(V, x, []), d)), g)(hy)(hx),
      t2 => Shared.Bool.when_cases(
        Crit<V>,
        t => {Crit.all(~V, ~G, ~p, t, g) == True{}: Bool},
        Cur.bit(Key.at(Crit.rep(V, x, []), d)),
        q2 => Crit.Fork{Crit.rep(V, y, []), d, None{}, y, x},
        q2 => Crit.Fork{Crit.rep(V, x, []), d, None{}, x, y},
        t3 => Crit.all.intro(~V, ~G, ~p, Crit.rep(V, y, []), d, None{}, y, x, g)({==})(hy)(hx),
        t3 => Crit.all.intro(~V, ~G, ~p, Crit.rep(V, x, []), d, None{}, x, y, g)({==})(hx)(hy)
      )
    )
  )

# the end of a union of two ends passes p when both do
def Crit.hit_join(~V: Data, ~j: V -> V -> V, ~G: Data, ~p: G -> List<&2, U32> -> Bool, ea: Maybe<&2, V>, eb: Maybe<&2, V>, +ra: List<&2, U32>, +rb: List<&2, U32>, +g: G) -> {
  Bool.or(Maybe.is_none(&2, V, ea), p(g)(ra)) == True{}: Bool
} -> {Bool.or(Maybe.is_none(&2, V, eb), p(g)(rb)) == True{}: Bool} -> {Bool.or(Maybe.is_none(&2, V, Shared.Maybe.join(~V, ~j, ea, eb)), p(g)(Bool.pick(List<&2, U32>, Maybe.is_some(&2, V, ea), ra, rb))) == True{}: Bool}:
  match ea eb:
    case None{} None{}:
      ha => hb => {==}
    case None{} Some{w}:
      ha => hb => hb
    case Some{u} None{}:
      ha => hb => ha
    case Some{u} Some{w}:
      ha => hb => ha

# the union of two forks whose reps do not differ before both bits passes p
# when both do, by how the bits compare (c)
def Crit.union_at_all(~V: Data, ~j: V -> V -> V, ~G: Data, ~p: G -> List<&2, U32> -> Bool, +ra: List<&2, U32>, +pa: Nat, +ea: Maybe<&2, V>, +za: Crit<V>, +oa: Crit<V>, +rb: List<&2, U32>, +pb: Nat, +eb: Maybe<&2, V>, +zb: Crit<V>, +ob: Crit<V>, +g: G, c: Cmp) -> {Crit.all(~V, ~G, ~p, Crit.Fork{ra, pa, ea, za, oa}, g) == True{}: Bool} -> {Crit.all(~V, ~G, ~p, Crit.Fork{rb, pb, eb, zb, ob}, g) == True{}: Bool} -> {Crit.all(~V, ~G, ~p, Crit.union(~V, ~j, za, zb), g) == True{}: Bool} -> {Crit.all(~V, ~G, ~p, Crit.union(~V, ~j, oa, ob), g) == True{}: Bool} -> {Crit.all(~V, ~G, ~p, Crit.union(~V, ~j, za, Crit.Fork{rb, pb, eb, zb, ob}), g) == True{}: Bool} -> {Crit.all(~V, ~G, ~p, Crit.union(~V, ~j, oa, Crit.Fork{rb, pb, eb, zb, ob}), g) == True{}: Bool} -> {Crit.all(~V, ~G, ~p, Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, zb), g) == True{}: Bool} -> {Crit.all(~V, ~G, ~p, Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, ob), g) == True{}: Bool} -> {Crit.all(~V, ~G, ~p, Crit.union.at(~V, ~j, c, ra, pa, ea, rb, pb, eb, zs => os => Crit.mk(V, Bool.pick(List<&2, U32>, Maybe.is_some(&2, V, ea), ra, rb), pa, Shared.Maybe.join(~V, ~j, ea, eb), zs, os), u2 => Crit.union(~V, ~j, za, zb), u2 => Crit.union(~V, ~j, oa, ob), u2 => Crit.union(~V, ~j, za, Crit.Fork{rb, pb, eb, zb, ob}), u2 => Crit.union(~V, ~j, oa, Crit.Fork{rb, pb, eb, zb, ob}), u2 => Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, zb), u2 => Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, ob), za, oa, zb, ob), g) == True{}: Bool}:
  match c:
    case EQ{}:
      +ha => +hb => i1 => i2 => i3 => i4 => i5 => i6 => Crit.mk_all(~V, ~G, ~p, Bool.pick(List<&2, U32>, Maybe.is_some(&2, V, ea), ra, rb), pa, Shared.Maybe.join(~V, ~j, ea, eb), Crit.union(~V, ~j, za, zb), Crit.union(~V, ~j, oa, ob), g)(
        Crit.hit_join(~V, ~j, ~G, ~p, ea, eb, ra, rb, g)(Crit.all.hit(~V, ~G, ~p, ra, pa, ea, za, oa, g)(ha))(Crit.all.hit(~V, ~G, ~p, rb, pb, eb, zb, ob, g)(hb))
      )(i1)(i2)
    case LT{}:
      +ha => hb => i1 => i2 => i3 => i4 => i5 => i6 => Shared.Bool.when_cases(
        Crit<V>,
        t => {Crit.all(~V, ~G, ~p, t, g) == True{}: Bool},
        Key.bit(rb, pa),
        u => Crit.mk(V, ra, pa, ea, za, Crit.union(~V, ~j, oa, Crit.Fork{rb, pb, eb, zb, ob})),
        u => Crit.mk(V, ra, pa, ea, Crit.union(~V, ~j, za, Crit.Fork{rb, pb, eb, zb, ob}), oa),
        t3 => Crit.mk_all(~V, ~G, ~p, ra, pa, ea, za, Crit.union(~V, ~j, oa, Crit.Fork{rb, pb, eb, zb, ob}), g)(Crit.all.hit(~V, ~G, ~p, ra, pa, ea, za, oa, g)(ha))(Crit.all.z(~V, ~G, ~p, ra, pa, ea, za, oa, g)(ha))(i4),
        t3 => Crit.mk_all(~V, ~G, ~p, ra, pa, ea, Crit.union(~V, ~j, za, Crit.Fork{rb, pb, eb, zb, ob}), oa, g)(Crit.all.hit(~V, ~G, ~p, ra, pa, ea, za, oa, g)(ha))(i3)(Crit.all.o(~V, ~G, ~p, ra, pa, ea, za, oa, g)(ha))
      )
    case GT{}:
      ha => +hb => i1 => i2 => i3 => i4 => i5 => i6 => Shared.Bool.when_cases(
        Crit<V>,
        t => {Crit.all(~V, ~G, ~p, t, g) == True{}: Bool},
        Key.bit(ra, pb),
        u => Crit.mk(V, rb, pb, eb, zb, Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, ob)),
        u => Crit.mk(V, rb, pb, eb, Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, zb), ob),
        t3 => Crit.mk_all(~V, ~G, ~p, rb, pb, eb, zb, Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, ob), g)(Crit.all.hit(~V, ~G, ~p, rb, pb, eb, zb, ob, g)(hb))(Crit.all.z(~V, ~G, ~p, rb, pb, eb, zb, ob, g)(hb))(i6),
        t3 => Crit.mk_all(~V, ~G, ~p, rb, pb, eb, Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, zb), ob, g)(Crit.all.hit(~V, ~G, ~p, rb, pb, eb, zb, ob, g)(hb))(i5)(Crit.all.o(~V, ~G, ~p, rb, pb, eb, zb, ob, g)(hb))
      )

# a union passes p when both maps do
def Crit.union_all(~V: Data, ~j: V -> V -> V, ~G: Data, ~p: G -> List<&2, U32> -> Bool, +a: Crit<V>, +b: Crit<V>, +g: G) -> {Crit.all(~V, ~G, ~p, a, g) == True{}: Bool} -> {
  Crit.all(~V, ~G, ~p, b, g) == True{}: Bool
} -> {Crit.all(~V, ~G, ~p, Crit.union(~V, ~j, a, b), g) == True{}: Bool}:
  match a b:
    case Crit.Tip{} Crit.Tip{}:
      ha => hb => {==}
    case Crit.Tip{} Crit.Leaf{k2, w2}:
      ha => hb => hb
    case Crit.Tip{} Crit.Fork{r2, p2, e2, z2, o2}:
      ha => hb => hb
    case Crit.Leaf{k, v} Crit.Tip{}:
      ha => hb => ha
    case Crit.Fork{ra, pa, ea, za, oa} Crit.Tip{}:
      ha => hb => ha
    case Crit.Leaf{+k, +v} Crit.Leaf{+k2, +w}:
      ha => hb => Crit.put_all(~V, ~(w => x => j(x, w)), ~G, ~p, Crit.Leaf{k2, w}, 0n, Cur.of(k), k, v, Crit.diff(k, Crit.near(V, Crit.Leaf{k2, w}, 0n, Cur.of(k))), g)(hb)(ha)
    case Crit.Leaf{+k, +v} Crit.Fork{+rb, +pb, +eb, +zb, +ob}:
      ha => hb => Crit.put_all(~V, ~(w => x => j(x, w)), ~G, ~p, Crit.Fork{rb, pb, eb, zb, ob}, 0n, Cur.of(k), k, v, Crit.diff(k, Crit.near(V, Crit.Fork{rb, pb, eb, zb, ob}, 0n, Cur.of(k))), g)(hb)(ha)
    case Crit.Fork{+ra, +pa, +ea, +za, +oa} Crit.Leaf{+k, +w}:
      ha => hb => Crit.put_all(~V, ~j, ~G, ~p, Crit.Fork{ra, pa, ea, za, oa}, 0n, Cur.of(k), k, w, Crit.diff(k, Crit.near(V, Crit.Fork{ra, pa, ea, za, oa}, 0n, Cur.of(k))), g)(ha)(hb)
    case Crit.Fork{+ra, +pa, +ea, +za, +oa} Crit.Fork{+rb, +pb, +eb, +zb, +ob}:
      +ha => +hb => Shared.Bool.when_cases(
        Crit<V>,
        t => {Crit.all(~V, ~G, ~p, t, g) == True{}: Bool},
        Bool.and(Crit.above(Key.diff(ra, rb), pa), Crit.above(Key.diff(ra, rb), pb)),
        u => Crit.join(V, Crit.Fork{ra, pa, ea, za, oa}, Crit.Fork{rb, pb, eb, zb, ob}, Maybe.default(&2, Nat, Key.diff(ra, rb), 0n)),
        u => Crit.union.at(~V, ~j, Nat.cmp(pa, pb), ra, pa, ea, rb, pb, eb, zs => os => Crit.mk(V, Bool.pick(List<&2, U32>, Maybe.is_some(&2, V, ea), ra, rb), pa, Shared.Maybe.join(~V, ~j, ea, eb), zs, os), u2 => Crit.union(~V, ~j, za, zb), u2 => Crit.union(~V, ~j, oa, ob), u2 => Crit.union(~V, ~j, za, Crit.Fork{rb, pb, eb, zb, ob}), u2 => Crit.union(~V, ~j, oa, Crit.Fork{rb, pb, eb, zb, ob}), u2 => Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, zb), u2 => Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, ob), za, oa, zb, ob),
        t => Crit.join_all.any(~V, ~G, ~p, Crit.Fork{ra, pa, ea, za, oa}, Crit.Fork{rb, pb, eb, zb, ob}, Maybe.default(&2, Nat, Key.diff(ra, rb), 0n), g)(ha)(hb),
        t => Crit.union_at_all(~V, ~j, ~G, ~p, ra, pa, ea, za, oa, rb, pb, eb, zb, ob, g, Nat.cmp(pa, pb))(ha)(hb)(
          Crit.union_all(~V, ~j, ~G, ~p, za, zb, g)(Crit.all.z(~V, ~G, ~p, ra, pa, ea, za, oa, g)(ha))(Crit.all.z(~V, ~G, ~p, rb, pb, eb, zb, ob, g)(hb))
        )(Crit.union_all(~V, ~j, ~G, ~p, oa, ob, g)(Crit.all.o(~V, ~G, ~p, ra, pa, ea, za, oa, g)(ha))(Crit.all.o(~V, ~G, ~p, rb, pb, eb, zb, ob, g)(hb)))(
          Crit.union_all(~V, ~j, ~G, ~p, za, b, g)(Crit.all.z(~V, ~G, ~p, ra, pa, ea, za, oa, g)(ha))(hb)
        )(Crit.union_all(~V, ~j, ~G, ~p, oa, b, g)(Crit.all.o(~V, ~G, ~p, ra, pa, ea, za, oa, g)(ha))(hb))(
          Crit.union_all(~V, ~j, ~G, ~p, a, zb, g)(ha)(Crit.all.z(~V, ~G, ~p, rb, pb, eb, zb, ob, g)(hb))
        )(Crit.union_all(~V, ~j, ~G, ~p, a, ob, g)(ha)(Crit.all.o(~V, ~G, ~p, rb, pb, eb, zb, ob, g)(hb)))
      )

# the cursor at x of the rep of a well formed fork at a later bit is not done
def Crit.rep_not_done(~V: Data, +rep: List<&2, U32>, +pos: Nat, +e: Maybe<&2, V>, +z: Crit<V>, +o: Crit<V>, +lo: Nat, +x: Nat) -> {Crit.wf(~V, Crit.Fork{rep, pos, e, z, o}, lo) == True{}: Bool} -> {
  Nat.is_lt(x, pos) == True{}: Bool
} -> {Cur.done(Key.at(rep, x)) == False{}: Bool}:
  h => lt => Equal.trans(
    Bool,
    Cur.done(Key.at(rep, x)),
    List.is_empty(&2, Bool, List.drop(&2, Bool, Key.bits(rep), x)),
    False{},
    Crit.done_of(Key.at(rep, x), List.drop(&2, Bool, Key.bits(rep), x))(Cur.skip_bits(x, Cur.of(rep))),
    Crit.len_drop(Key.bits(rep), x)(Shared.Nat.lt_le(x, pos, List.length(&2, Bool, Key.bits(rep)))(lt)(Crit.rep_long(~V, rep, pos, e, z, o, lo)(h)))
  )

# a fork of two well formed forks whose reps differ first at x, before both
# bits, is well formed below x
def Crit.join_wf_ff(~V: Data, +ra: List<&2, U32>, +pa: Nat, +ea: Maybe<&2, V>, +za: Crit<V>, +oa: Crit<V>, +rb: List<&2, U32>, +pb: Nat, +eb: Maybe<&2, V>, +zb: Crit<V>, +ob: Crit<V>, +la: Nat, +lb: Nat, +lo: Nat, +x: Nat) -> {Crit.wf(~V, Crit.Fork{ra, pa, ea, za, oa}, la) == True{}: Bool} -> {Crit.wf(~V, Crit.Fork{rb, pb, eb, zb, ob}, lb) == True{}: Bool} -> {Nat.is_le(lo, x) == True{}: Bool} -> {
  Nat.is_lt(x, pa) == True{}: Bool
} -> {Nat.is_lt(x, pb) == True{}: Bool} -> {Key.diff(ra, rb) == Some{x}: Maybe<&2, Nat>} -> {Crit.wf(~V, Crit.join(V, Crit.Fork{ra, pa, ea, za, oa}, Crit.Fork{rb, pb, eb, zb, ob}, x), lo) == True{}: Bool}:
  +ha => +hb => +le => +lta => +ltb => +hd =>
    +na = Crit.rep_not_done(~V, ra, pa, ea, za, oa, la, x)(ha)(lta)
    +nb = Crit.rep_not_done(~V, rb, pb, eb, zb, ob, lb, x)(hb)(ltb)
    +sa = Crit.side_of(ra, x, Cur.bit(Key.at(ra, x)))(na)({==})
    +sb = Crit.side_of(rb, x, Cur.bit(Key.at(rb, x)))(nb)({==})
    +sne = Crit.diff_sides(ra, rb, x)(hd)
    +ab = Key.agree_of_diff(ra, rb, x)(hd)
    +wa = Crit.wf_lower(~V, ra, pa, ea, za, oa, la, 1n+x)(ha)(Crit.lt_le_succ(x, pa)(lta))
    +wb = Crit.wf_lower(~V, rb, pb, eb, zb, ob, lb, 1n+x)(hb)(Crit.lt_le_succ(x, pb)(ltb))
    +aa = Crit.fork_place(~V, ra, pa, ea, za, oa, la, ra, x, Cur.bit(Key.at(ra, x)))(ha)(lta)(Key.agree_self(ra, x))(sa)
    +bb = Crit.fork_place(~V, rb, pb, eb, zb, ob, lb, ra, x, Cur.bit(Key.at(rb, x)))(hb)(ltb)(ab)(sb)
    Shared.Bool.when_cases(
      Crit<V>,
      t => {Crit.wf(~V, t, lo) == True{}: Bool},
      Cur.done(Key.at(ra, x)),
      u => Crit.join.end(V, Crit.Fork{ra, pa, ea, za, oa}, Crit.Fork{rb, pb, eb, zb, ob}, x, Cur.bit(Key.at(rb, x))),
      u => Shared.Bool.when(
        Crit<V>,
        Cur.done(Key.at(rb, x)),
        q1 => Crit.join.end(V, Crit.Fork{rb, pb, eb, zb, ob}, Crit.Fork{ra, pa, ea, za, oa}, x, Cur.bit(Key.at(ra, x))),
        q1 => Shared.Bool.when(Crit<V>, Cur.bit(Key.at(ra, x)), q2 => Crit.Fork{rb, x, None{}, Crit.Fork{rb, pb, eb, zb, ob}, Crit.Fork{ra, pa, ea, za, oa}}, q2 => Crit.Fork{ra, x, None{}, Crit.Fork{ra, pa, ea, za, oa}, Crit.Fork{rb, pb, eb, zb, ob}})
      ),
      t1 => Empty.absurd({Crit.wf(~V, Crit.join.end(V, Crit.Fork{ra, pa, ea, za, oa}, Crit.Fork{rb, pb, eb, zb, ob}, x, Cur.bit(Key.at(rb, x))), lo) == True{}: Bool}, Crit.clash(Cur.done(Key.at(ra, x)), True{}, False{}, t1, na, Shared.Bool.true_ne_false)),
      t1 => Shared.Bool.when_cases(
        Crit<V>,
        t => {Crit.wf(~V, t, lo) == True{}: Bool},
        Cur.done(Key.at(rb, x)),
        q1 => Crit.join.end(V, Crit.Fork{rb, pb, eb, zb, ob}, Crit.Fork{ra, pa, ea, za, oa}, x, Cur.bit(Key.at(ra, x))),
        q1 => Shared.Bool.when(Crit<V>, Cur.bit(Key.at(ra, x)), q2 => Crit.Fork{rb, x, None{}, Crit.Fork{rb, pb, eb, zb, ob}, Crit.Fork{ra, pa, ea, za, oa}}, q2 => Crit.Fork{ra, x, None{}, Crit.Fork{ra, pa, ea, za, oa}, Crit.Fork{rb, pb, eb, zb, ob}}),
        t2 => Empty.absurd({Crit.wf(~V, Crit.join.end(V, Crit.Fork{rb, pb, eb, zb, ob}, Crit.Fork{ra, pa, ea, za, oa}, x, Cur.bit(Key.at(ra, x))), lo) == True{}: Bool}, Crit.clash(Cur.done(Key.at(rb, x)), True{}, False{}, t2, nb, Shared.Bool.true_ne_false)),
        t2 => Shared.Bool.when_cases(
          Crit<V>,
          t => {Crit.wf(~V, t, lo) == True{}: Bool},
          Cur.bit(Key.at(ra, x)),
          q2 => Crit.Fork{rb, x, None{}, Crit.Fork{rb, pb, eb, zb, ob}, Crit.Fork{ra, pa, ea, za, oa}},
          q2 => Crit.Fork{ra, x, None{}, Crit.Fork{ra, pa, ea, za, oa}, Crit.Fork{rb, pb, eb, zb, ob}},
          +t3 =>
            +bf = Crit.ne_true(Cur.bit(Key.at(rb, x)))(Crit.ne_sides(ra, rb, x, Some{True{}}, Some{Cur.bit(Key.at(rb, x))})(Crit.side_of(ra, x, True{})(na)(t3))(sb)(sne))
            Crit.wf.intro(~V, rb, x, None{}, Crit.Fork{rb, pb, eb, zb, ob}, Crit.Fork{ra, pa, ea, za, oa}, lo)(le)({==})(Key.is_eq_refl(rb))(
              Crit.place_shift(~V, Crit.Fork{rb, pb, eb, zb, ob}, ra, rb, x, False{})(Key.agree_sym(ra, rb, x)(ab))(Crit.all_place_b(~V, Crit.Fork{rb, pb, eb, zb, ob}, ra, x, Cur.bit(Key.at(rb, x)), False{})(bf)(bb))
            )(Crit.place_shift(~V, Crit.Fork{ra, pa, ea, za, oa}, ra, rb, x, True{})(Key.agree_sym(ra, rb, x)(ab))(Crit.all_place_b(~V, Crit.Fork{ra, pa, ea, za, oa}, ra, x, Cur.bit(Key.at(ra, x)), True{})(t3)(aa)))(wb)(wa),
          +t3 =>
            +bt = Crit.ne_false(Cur.bit(Key.at(rb, x)))(Crit.ne_sides(ra, rb, x, Some{False{}}, Some{Cur.bit(Key.at(rb, x))})(Crit.side_of(ra, x, False{})(na)(t3))(sb)(sne))
            Crit.wf.intro(~V, ra, x, None{}, Crit.Fork{ra, pa, ea, za, oa}, Crit.Fork{rb, pb, eb, zb, ob}, lo)(le)({==})(Key.is_eq_refl(ra))(Crit.all_place_b(~V, Crit.Fork{ra, pa, ea, za, oa}, ra, x, Cur.bit(Key.at(ra, x)), False{})(t3)(aa))(
              Crit.all_place_b(~V, Crit.Fork{rb, pb, eb, zb, ob}, ra, x, Cur.bit(Key.at(rb, x)), True{})(bt)(bb)
            )(wa)(wb)
        )
      )
    )

# the reps of two well formed forks whose keys fit lo agree on lo bits
def Crit.fit_le(~V: Data, +ra: List<&2, U32>, +pa: Nat, +ea: Maybe<&2, V>, +za: Crit<V>, +oa: Crit<V>, +rb: List<&2, U32>, +pb: Nat, +eb: Maybe<&2, V>, +zb: Crit<V>, +ob: Crit<V>, lo: Nat, +r: List<&2, U32>, +s: Bool) -> {Crit.wf(~V, Crit.Fork{ra, pa, ea, za, oa}, lo) == True{}: Bool} -> {Crit.wf(~V, Crit.Fork{rb, pb, eb, zb, ob}, lo) == True{}: Bool} -> {Crit.fits(~V, Crit.Fork{ra, pa, ea, za, oa}, Crit.Fork{rb, pb, eb, zb, ob}, lo, r, s) == True{}: Bool} -> {
  Bits.agree(Key.diff(ra, rb), lo) == True{}: Bool
}:
  match lo:
    case 0n:
      ha => hb => hf => Bits.agree.zero(Key.diff(ra, rb))
    case 1n+(+p):
      ha => hb => +hf => Crit.fit_agree(ra, rb, r, p, s)(
        Crit.rep_pass(~V, ~Place, ~Place.has, Crit.Fork{ra, pa, ea, za, oa}, 1n+p, Place{r, p, s}, [])(ha)(Shared.Bool.and_true_left(Crit.all(~V, ~Place, ~Place.has, Crit.Fork{ra, pa, ea, za, oa}, Place{r, p, s}), Crit.all(~V, ~Place, ~Place.has, Crit.Fork{rb, pb, eb, zb, ob}, Place{r, p, s}))(hf))({==})
      )(Crit.rep_pass(~V, ~Place, ~Place.has, Crit.Fork{rb, pb, eb, zb, ob}, 1n+p, Place{r, p, s}, [])(hb)(Shared.Bool.and_true_right(Crit.all(~V, ~Place, ~Place.has, Crit.Fork{ra, pa, ea, za, oa}, Place{r, p, s}), Crit.all(~V, ~Place, ~Place.has, Crit.Fork{rb, pb, eb, zb, ob}, Place{r, p, s}))(hf))({==}))

# a pick of two keys that agree on pos bits agrees with each
def Crit.pick_agree_l(c: Bool, +ra: List<&2, U32>, +rb: List<&2, U32>, +pos: Nat) -> {Key.agree(rb, ra, pos) == True{}: Bool} -> {Key.agree(Bool.pick(List<&2, U32>, c, ra, rb), ra, pos) == True{}: Bool}:
  match c:
    case True{}:
      h => Key.agree_self(ra, pos)
    case False{}:
      h => h

def Crit.pick_agree_r(c: Bool, +ra: List<&2, U32>, +rb: List<&2, U32>, +pos: Nat) -> {Key.agree(rb, ra, pos) == True{}: Bool} -> {Key.agree(Bool.pick(List<&2, U32>, c, ra, rb), rb, pos) == True{}: Bool}:
  match c:
    case True{}:
      h => Key.agree_sym(rb, ra, pos)(h)
    case False{}:
      h => Key.agree_self(rb, pos)

# the rep of a union of two forks at one bit is right for its end
def Crit.rep_or_union(~V: Data, ~j: V -> V -> V, +ra: List<&2, U32>, +pa: Nat, ea: Maybe<&2, V>, -za: Crit<V>, +rb: List<&2, U32>, +pb: Nat, eb: Maybe<&2, V>, -zb: Crit<V>) -> {
  Crit.rep_ok(V, ra, pa, ea, za) == True{}: Bool
} -> {Crit.rep_ok(V, rb, pb, eb, zb) == True{}: Bool} -> {pa == pb: Nat} -> {
  Bool.or(Maybe.is_none(&2, V, Shared.Maybe.join(~V, ~j, ea, eb)), Nat.is_eq(List.length(&2, Bool, Key.bits(Bool.pick(List<&2, U32>, Maybe.is_some(&2, V, ea), ra, rb))), pa)) == True{}: Bool
}:
  match ea eb:
    case None{} None{}:
      hra => hrb => eqp => {==}
    case Some{u} None{}:
      hra => hrb => eqp => hra
    case Some{u} Some{w}:
      hra => hrb => eqp => hra
    case None{} Some{w}:
      hra => hrb => eqp =>
        %Equal.sym(Nat, pa, pb, eqp): {Nat.is_eq(List.length(&2, Bool, Key.bits(rb)), _) == True{}: Bool}
        hrb

# the keys on a side of a fork at a bit are on that side of one at an equal bit
def Crit.all_pos(~V: Data, +m: Crit<V>, +r: List<&2, U32>, p1: Nat, +p2: Nat, +b: Bool) -> {p1 == p2: Nat} -> {
  Crit.all(~V, ~Place, ~Place.has, m, Place{r, p1, b}) == True{}: Bool
} -> {Crit.all(~V, ~Place, ~Place.has, m, Place{r, p2, b}) == True{}: Bool}:
  e => h =>
    %e: {Crit.all(~V, ~Place, ~Place.has, m, Place{r, _, b}) == True{}: Bool}
    h

# the union of two well formed forks whose reps do not differ before both
# bits is well formed, by how the bits compare (c)
def Crit.union_at_wf(~V: Data, ~j: V -> V -> V, +ra: List<&2, U32>, +pa: Nat, +ea: Maybe<&2, V>, +za: Crit<V>, +oa: Crit<V>, +rb: List<&2, U32>, +pb: Nat, +eb: Maybe<&2, V>, +zb: Crit<V>, +ob: Crit<V>, +lo: Nat, c: Cmp) -> {Nat.cmp(pa, pb) == c: Cmp} -> {Crit.wf(~V, Crit.Fork{ra, pa, ea, za, oa}, lo) == True{}: Bool} -> {Crit.wf(~V, Crit.Fork{rb, pb, eb, zb, ob}, lo) == True{}: Bool} -> {Bool.and(Crit.above(Key.diff(ra, rb), pa), Crit.above(Key.diff(ra, rb), pb)) == False{}: Bool} -> ({pa == pb: Nat} -> {Crit.wf(~V, Crit.union(~V, ~j, za, zb), 1n+pa) == True{}: Bool}) -> ({pa == pb: Nat} -> {Crit.wf(~V, Crit.union(~V, ~j, oa, ob), 1n+pa) == True{}: Bool}) -> ({Nat.is_lt(pa, pb) == True{}: Bool} -> {Crit.all(~V, ~Place, ~Place.has, Crit.Fork{rb, pb, eb, zb, ob}, Place{ra, pa, False{}}) == True{}: Bool} -> {Crit.wf(~V, Crit.union(~V, ~j, za, Crit.Fork{rb, pb, eb, zb, ob}), 1n+pa) == True{}: Bool}) -> ({Nat.is_lt(pa, pb) == True{}: Bool} -> {Crit.all(~V, ~Place, ~Place.has, Crit.Fork{rb, pb, eb, zb, ob}, Place{ra, pa, True{}}) == True{}: Bool} -> {Crit.wf(~V, Crit.union(~V, ~j, oa, Crit.Fork{rb, pb, eb, zb, ob}), 1n+pa) == True{}: Bool}) -> ({Nat.is_lt(pb, pa) == True{}: Bool} -> {Crit.all(~V, ~Place, ~Place.has, Crit.Fork{ra, pa, ea, za, oa}, Place{rb, pb, False{}}) == True{}: Bool} -> {Crit.wf(~V, Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, zb), 1n+pb) == True{}: Bool}) -> ({Nat.is_lt(pb, pa) == True{}: Bool} -> {Crit.all(~V, ~Place, ~Place.has, Crit.Fork{ra, pa, ea, za, oa}, Place{rb, pb, True{}}) == True{}: Bool} -> {Crit.wf(~V, Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, ob), 1n+pb) == True{}: Bool}) -> {Crit.wf(~V, Crit.union.at(~V, ~j, c, ra, pa, ea, rb, pb, eb, zs => os => Crit.mk(V, Bool.pick(List<&2, U32>, Maybe.is_some(&2, V, ea), ra, rb), pa, Shared.Maybe.join(~V, ~j, ea, eb), zs, os), u2 => Crit.union(~V, ~j, za, zb), u2 => Crit.union(~V, ~j, oa, ob), u2 => Crit.union(~V, ~j, za, Crit.Fork{rb, pb, eb, zb, ob}), u2 => Crit.union(~V, ~j, oa, Crit.Fork{rb, pb, eb, zb, ob}), u2 => Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, zb), u2 => Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, ob), za, oa, zb, ob), lo) == True{}: Bool}:
  match c:
    case EQ{}:
      hc => +ha => +hb => +hn => i1 => i2 => i3 => i4 => i5 => i6 =>
        +eqp = Crit.cmp_eq(pa, pb)(hc)
        +hab = Crit.above_eq(Key.diff(ra, rb), pa)(Equal.trans(Bool, Bool.and(Crit.above(Key.diff(ra, rb), pa), Crit.above(Key.diff(ra, rb), pa)), Bool.and(Crit.above(Key.diff(ra, rb), pa), Crit.above(Key.diff(ra, rb), pb)), False{}, Equal.cong(Nat, Bool, t => Bool.and(Crit.above(Key.diff(ra, rb), pa), Crit.above(Key.diff(ra, rb), t)), pa, pb, eqp), hn))
        +arb = Key.agree_sym(ra, rb, pa)(Crit.not_above_agree(Key.diff(ra, rb), pa)(hab))
        +azb = Crit.all_pos(~V, zb, rb, pb, pa, False{})(Equal.sym(Nat, pa, pb, eqp))(Crit.wf.all_z(~V, rb, pb, eb, zb, ob, lo)(hb))
        +aob = Crit.all_pos(~V, ob, rb, pb, pa, True{})(Equal.sym(Nat, pa, pb, eqp))(Crit.wf.all_o(~V, rb, pb, eb, zb, ob, lo)(hb))
        Crit.mk_wf(~V, Bool.pick(List<&2, U32>, Maybe.is_some(&2, V, ea), ra, rb), pa, Shared.Maybe.join(~V, ~j, ea, eb), Crit.union(~V, ~j, za, zb), Crit.union(~V, ~j, oa, ob), lo)(Crit.wf.le(~V, ra, pa, ea, za, oa, lo)(ha))(
          Crit.rep_or_union(~V, ~j, ra, pa, ea, za, rb, pb, eb, zb)(Crit.wf.rep_ok(~V, ra, pa, ea, za, oa, lo)(ha))(Crit.wf.rep_ok(~V, rb, pb, eb, zb, ob, lo)(hb))(eqp)
        )(Crit.union_all(~V, ~j, ~Place, ~Place.has, za, zb, Place{Bool.pick(List<&2, U32>, Maybe.is_some(&2, V, ea), ra, rb), pa, False{}})(Crit.place_shift(~V, za, ra, Bool.pick(List<&2, U32>, Maybe.is_some(&2, V, ea), ra, rb), pa, False{})(Crit.pick_agree_l(Maybe.is_some(&2, V, ea), ra, rb, pa)(arb))(Crit.wf.all_z(~V, ra, pa, ea, za, oa, lo)(ha)))(Crit.place_shift(~V, zb, rb, Bool.pick(List<&2, U32>, Maybe.is_some(&2, V, ea), ra, rb), pa, False{})(Crit.pick_agree_r(Maybe.is_some(&2, V, ea), ra, rb, pa)(arb))(azb)))(Crit.union_all(~V, ~j, ~Place, ~Place.has, oa, ob, Place{Bool.pick(List<&2, U32>, Maybe.is_some(&2, V, ea), ra, rb), pa, True{}})(Crit.place_shift(~V, oa, ra, Bool.pick(List<&2, U32>, Maybe.is_some(&2, V, ea), ra, rb), pa, True{})(Crit.pick_agree_l(Maybe.is_some(&2, V, ea), ra, rb, pa)(arb))(Crit.wf.all_o(~V, ra, pa, ea, za, oa, lo)(ha)))(Crit.place_shift(~V, ob, rb, Bool.pick(List<&2, U32>, Maybe.is_some(&2, V, ea), ra, rb), pa, True{})(Crit.pick_agree_r(Maybe.is_some(&2, V, ea), ra, rb, pa)(arb))(aob)))(i1(eqp))(i2(eqp))
    case LT{}:
      hc => +ha => +hb => hn => i1 => i2 => i3 => i4 => i5 => i6 =>
        +lt = Crit.cmp_lt(pa, pb)(hc)
        +hab = Crit.above_lt_left(Key.diff(ra, rb), pa, pb)(hn)(lt)
        +allb = Crit.fork_place(~V, rb, pb, eb, zb, ob, lo, ra, pa, Cur.bit(Key.at(rb, pa)))(hb)(lt)(Crit.not_above_agree(Key.diff(ra, rb), pa)(hab))(Crit.side_of(rb, pa, Cur.bit(Key.at(rb, pa)))(Crit.rep_not_done(~V, rb, pb, eb, zb, ob, lo, pa)(hb)(lt))({==}))
        Shared.Bool.when_cases(
          Crit<V>,
          t => {Crit.wf(~V, t, lo) == True{}: Bool},
          Key.bit(rb, pa),
          u => Crit.mk(V, ra, pa, ea, za, Crit.union(~V, ~j, oa, Crit.Fork{rb, pb, eb, zb, ob})),
          u => Crit.mk(V, ra, pa, ea, Crit.union(~V, ~j, za, Crit.Fork{rb, pb, eb, zb, ob}), oa),
          +t3 =>
          +allt = Crit.all_place_b(~V, Crit.Fork{rb, pb, eb, zb, ob}, ra, pa, Key.bit(rb, pa), True{})(t3)(allb)
          Crit.mk_wf(~V, ra, pa, ea, za, Crit.union(~V, ~j, oa, Crit.Fork{rb, pb, eb, zb, ob}), lo)(Crit.wf.le(~V, ra, pa, ea, za, oa, lo)(ha))(Crit.rep_or(V, ra, pa, ea, za)(Crit.wf.rep_ok(~V, ra, pa, ea, za, oa, lo)(ha)))(Crit.wf.all_z(~V, ra, pa, ea, za, oa, lo)(ha))(Crit.union_all(~V, ~j, ~Place, ~Place.has, oa, Crit.Fork{rb, pb, eb, zb, ob}, Place{ra, pa, True{}})(Crit.wf.all_o(~V, ra, pa, ea, za, oa, lo)(ha))(allt))(Crit.wf.wf_z(~V, ra, pa, ea, za, oa, lo)(ha))(i4(lt)(allt)),
          +t3 =>
          +allt = Crit.all_place_b(~V, Crit.Fork{rb, pb, eb, zb, ob}, ra, pa, Key.bit(rb, pa), False{})(t3)(allb)
          Crit.mk_wf(~V, ra, pa, ea, Crit.union(~V, ~j, za, Crit.Fork{rb, pb, eb, zb, ob}), oa, lo)(Crit.wf.le(~V, ra, pa, ea, za, oa, lo)(ha))(Crit.rep_or(V, ra, pa, ea, za)(Crit.wf.rep_ok(~V, ra, pa, ea, za, oa, lo)(ha)))(Crit.union_all(~V, ~j, ~Place, ~Place.has, za, Crit.Fork{rb, pb, eb, zb, ob}, Place{ra, pa, False{}})(Crit.wf.all_z(~V, ra, pa, ea, za, oa, lo)(ha))(allt))(Crit.wf.all_o(~V, ra, pa, ea, za, oa, lo)(ha))(i3(lt)(allt))(Crit.wf.wf_o(~V, ra, pa, ea, za, oa, lo)(ha))
        )
    case GT{}:
      hc => +ha => +hb => hn => i1 => i2 => i3 => i4 => i5 => i6 =>
        +gt = Crit.cmp_gt(pa, pb)(hc)
        +hab = Crit.above_lt_right(Key.diff(ra, rb), pa, pb)(hn)(gt)
        +alla = Crit.fork_place(~V, ra, pa, ea, za, oa, lo, rb, pb, Cur.bit(Key.at(ra, pb)))(ha)(gt)(Key.agree_sym(ra, rb, pb)(Crit.not_above_agree(Key.diff(ra, rb), pb)(hab)))(Crit.side_of(ra, pb, Cur.bit(Key.at(ra, pb)))(Crit.rep_not_done(~V, ra, pa, ea, za, oa, lo, pb)(ha)(gt))({==}))
        Shared.Bool.when_cases(
          Crit<V>,
          t => {Crit.wf(~V, t, lo) == True{}: Bool},
          Key.bit(ra, pb),
          u => Crit.mk(V, rb, pb, eb, zb, Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, ob)),
          u => Crit.mk(V, rb, pb, eb, Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, zb), ob),
          +t3 =>
          +allt = Crit.all_place_b(~V, Crit.Fork{ra, pa, ea, za, oa}, rb, pb, Key.bit(ra, pb), True{})(t3)(alla)
          Crit.mk_wf(~V, rb, pb, eb, zb, Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, ob), lo)(Crit.wf.le(~V, rb, pb, eb, zb, ob, lo)(hb))(Crit.rep_or(V, rb, pb, eb, zb)(Crit.wf.rep_ok(~V, rb, pb, eb, zb, ob, lo)(hb)))(Crit.wf.all_z(~V, rb, pb, eb, zb, ob, lo)(hb))(Crit.union_all(~V, ~j, ~Place, ~Place.has, Crit.Fork{ra, pa, ea, za, oa}, ob, Place{rb, pb, True{}})(allt)(Crit.wf.all_o(~V, rb, pb, eb, zb, ob, lo)(hb)))(Crit.wf.wf_z(~V, rb, pb, eb, zb, ob, lo)(hb))(i6(gt)(allt)),
          +t3 =>
          +allt = Crit.all_place_b(~V, Crit.Fork{ra, pa, ea, za, oa}, rb, pb, Key.bit(ra, pb), False{})(t3)(alla)
          Crit.mk_wf(~V, rb, pb, eb, Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, zb), ob, lo)(Crit.wf.le(~V, rb, pb, eb, zb, ob, lo)(hb))(Crit.rep_or(V, rb, pb, eb, zb)(Crit.wf.rep_ok(~V, rb, pb, eb, zb, ob, lo)(hb)))(Crit.union_all(~V, ~j, ~Place, ~Place.has, Crit.Fork{ra, pa, ea, za, oa}, zb, Place{rb, pb, False{}})(allt)(Crit.wf.all_z(~V, rb, pb, eb, zb, ob, lo)(hb)))(Crit.wf.all_o(~V, rb, pb, eb, zb, ob, lo)(hb))(i5(gt)(allt))(Crit.wf.wf_o(~V, rb, pb, eb, zb, ob, lo)(hb))
        )

# the union of two well formed maps whose keys fit lo is well formed
def Crit.union_go_wf(~V: Data, ~j: V -> V -> V, +a: Crit<V>, +b: Crit<V>, +lo: Nat, +r: List<&2, U32>, +s: Bool) -> {Crit.wf(~V, a, lo) == True{}: Bool} -> {Crit.wf(~V, b, lo) == True{}: Bool} -> {Crit.fits(~V, a, b, lo, r, s) == True{}: Bool} -> {Crit.wf(~V, Crit.union(~V, ~j, a, b), lo) == True{}: Bool}:
  match a b:
    case Crit.Tip{} Crit.Tip{}:
      ha => hb => hf => {==}
    case Crit.Tip{} Crit.Leaf{k2, w2}:
      ha => hb => hf => hb
    case Crit.Tip{} Crit.Fork{r2, p2, e2, z2, o2}:
      ha => hb => hf => hb
    case Crit.Leaf{k, v} Crit.Tip{}:
      ha => hb => hf => ha
    case Crit.Fork{ra, pa, ea, za, oa} Crit.Tip{}:
      ha => hb => hf => ha
    case Crit.Leaf{+k, +v} Crit.Leaf{+k2, +w}:
      ha => hb => hf => Crit.upsert_fit(~V, ~(w => x => j(x, w)), Crit.Leaf{k2, w}, lo, k, v, r, s)(hb)(hf)
    case Crit.Leaf{+k, +v} Crit.Fork{+rb, +pb, +eb, +zb, +ob}:
      ha => hb => hf => Crit.upsert_fit(~V, ~(w => x => j(x, w)), Crit.Fork{rb, pb, eb, zb, ob}, lo, k, v, r, s)(hb)(hf)
    case Crit.Fork{+ra, +pa, +ea, +za, +oa} Crit.Leaf{+k, +w}:
      ha => hb => hf => Crit.upsert_fit(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, lo, k, w, r, s)(ha)(Crit.fits_swap(~V, Crit.Fork{ra, pa, ea, za, oa}, Crit.Leaf{k, w}, lo, r, s)(hf))
    case Crit.Fork{+ra, +pa, +ea, +za, +oa} Crit.Fork{+rb, +pb, +eb, +zb, +ob}:
      +ha => +hb => +hf => Shared.Bool.when_cases(
        Crit<V>,
        t => {Crit.wf(~V, t, lo) == True{}: Bool},
        Bool.and(Crit.above(Key.diff(ra, rb), pa), Crit.above(Key.diff(ra, rb), pb)),
        u => Crit.join(V, Crit.Fork{ra, pa, ea, za, oa}, Crit.Fork{rb, pb, eb, zb, ob}, Maybe.default(&2, Nat, Key.diff(ra, rb), 0n)),
        u => Crit.union.at(~V, ~j, Nat.cmp(pa, pb), ra, pa, ea, rb, pb, eb, zs => os => Crit.mk(V, Bool.pick(List<&2, U32>, Maybe.is_some(&2, V, ea), ra, rb), pa, Shared.Maybe.join(~V, ~j, ea, eb), zs, os), u2 => Crit.union(~V, ~j, za, zb), u2 => Crit.union(~V, ~j, oa, ob), u2 => Crit.union(~V, ~j, za, Crit.Fork{rb, pb, eb, zb, ob}), u2 => Crit.union(~V, ~j, oa, Crit.Fork{rb, pb, eb, zb, ob}), u2 => Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, zb), u2 => Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, ob), za, oa, zb, ob),
        +t =>
          +sd = Crit.above_some(Key.diff(ra, rb), pa)(Shared.Bool.and_true_left(Crit.above(Key.diff(ra, rb), pa), Crit.above(Key.diff(ra, rb), pb))(t))
          Crit.join_wf_ff(~V, ra, pa, ea, za, oa, rb, pb, eb, zb, ob, lo, lo, lo, Maybe.default(&2, Nat, Key.diff(ra, rb), 0n))(ha)(hb)(
            Equal.trans(Bool, Bits.agree(Some{Maybe.default(&2, Nat, Key.diff(ra, rb), 0n)}, lo), Bits.agree(Key.diff(ra, rb), lo), True{}, Equal.cong(Maybe<&2, Nat>, Bool, q => Bits.agree(q, lo), Some{Maybe.default(&2, Nat, Key.diff(ra, rb), 0n)}, Key.diff(ra, rb), Equal.sym(Maybe<&2, Nat>, Key.diff(ra, rb), Some{Maybe.default(&2, Nat, Key.diff(ra, rb), 0n)}, sd)), Crit.fit_le(~V, ra, pa, ea, za, oa, rb, pb, eb, zb, ob, lo, r, s)(ha)(hb)(hf))
          )(Crit.above_lt(Key.diff(ra, rb), pa, Maybe.default(&2, Nat, Key.diff(ra, rb), 0n))(sd)(Shared.Bool.and_true_left(Crit.above(Key.diff(ra, rb), pa), Crit.above(Key.diff(ra, rb), pb))(t)))(
            Crit.above_lt(Key.diff(ra, rb), pb, Maybe.default(&2, Nat, Key.diff(ra, rb), 0n))(sd)(Shared.Bool.and_true_right(Crit.above(Key.diff(ra, rb), pa), Crit.above(Key.diff(ra, rb), pb))(t))
          )(sd),
        +t => Crit.union_at_wf(~V, ~j, ra, pa, ea, za, oa, rb, pb, eb, zb, ob, lo, Nat.cmp(pa, pb))({==})(ha)(hb)(t)(
          +eqp => Crit.union_go_wf(~V, ~j, za, zb, 1n+pa, ra, False{})(Crit.wf.wf_z(~V, ra, pa, ea, za, oa, lo)(ha))((
            %Equal.sym(Nat, pa, pb, eqp): {Crit.wf(~V, zb, 1n+_) == True{}: Bool}
            Crit.wf.wf_z(~V, rb, pb, eb, zb, ob, lo)(hb)
          ))(
            Crit.and_true(Crit.all(~V, ~Place, ~Place.has, za, Place{ra, pa, False{}}), Crit.all(~V, ~Place, ~Place.has, zb, Place{ra, pa, False{}}))(Crit.wf.all_z(~V, ra, pa, ea, za, oa, lo)(ha))(
              Crit.place_shift(~V, zb, rb, ra, pa, False{})(Crit.not_above_agree(Key.diff(ra, rb), pa)(Crit.above_eq(Key.diff(ra, rb), pa)(Equal.trans(Bool, Bool.and(Crit.above(Key.diff(ra, rb), pa), Crit.above(Key.diff(ra, rb), pa)), Bool.and(Crit.above(Key.diff(ra, rb), pa), Crit.above(Key.diff(ra, rb), pb)), False{}, Equal.cong(Nat, Bool, q => Bool.and(Crit.above(Key.diff(ra, rb), pa), Crit.above(Key.diff(ra, rb), q)), pa, pb, eqp), t))))((
                %Equal.sym(Nat, pa, pb, eqp): {Crit.all(~V, ~Place, ~Place.has, zb, Place{rb, _, False{}}) == True{}: Bool}
                Crit.wf.all_z(~V, rb, pb, eb, zb, ob, lo)(hb)
              ))
            )
          )
        )(
          +eqp => Crit.union_go_wf(~V, ~j, oa, ob, 1n+pa, ra, True{})(Crit.wf.wf_o(~V, ra, pa, ea, za, oa, lo)(ha))((
            %Equal.sym(Nat, pa, pb, eqp): {Crit.wf(~V, ob, 1n+_) == True{}: Bool}
            Crit.wf.wf_o(~V, rb, pb, eb, zb, ob, lo)(hb)
          ))(
            Crit.and_true(Crit.all(~V, ~Place, ~Place.has, oa, Place{ra, pa, True{}}), Crit.all(~V, ~Place, ~Place.has, ob, Place{ra, pa, True{}}))(Crit.wf.all_o(~V, ra, pa, ea, za, oa, lo)(ha))(
              Crit.place_shift(~V, ob, rb, ra, pa, True{})(Crit.not_above_agree(Key.diff(ra, rb), pa)(Crit.above_eq(Key.diff(ra, rb), pa)(Equal.trans(Bool, Bool.and(Crit.above(Key.diff(ra, rb), pa), Crit.above(Key.diff(ra, rb), pa)), Bool.and(Crit.above(Key.diff(ra, rb), pa), Crit.above(Key.diff(ra, rb), pb)), False{}, Equal.cong(Nat, Bool, q => Bool.and(Crit.above(Key.diff(ra, rb), pa), Crit.above(Key.diff(ra, rb), q)), pa, pb, eqp), t))))((
                %Equal.sym(Nat, pa, pb, eqp): {Crit.all(~V, ~Place, ~Place.has, ob, Place{rb, _, True{}}) == True{}: Bool}
                Crit.wf.all_o(~V, rb, pb, eb, zb, ob, lo)(hb)
              ))
            )
          )
        )(
          lt => +ab => Crit.union_go_wf(~V, ~j, za, b, 1n+pa, ra, False{})(Crit.wf.wf_z(~V, ra, pa, ea, za, oa, lo)(ha))(Crit.wf_lower(~V, rb, pb, eb, zb, ob, lo, 1n+pa)(hb)(Crit.lt_le_succ(pa, pb)(lt)))(
            Crit.and_true(Crit.all(~V, ~Place, ~Place.has, za, Place{ra, pa, False{}}), Crit.all(~V, ~Place, ~Place.has, Crit.Fork{rb, pb, eb, zb, ob}, Place{ra, pa, False{}}))(Crit.wf.all_z(~V, ra, pa, ea, za, oa, lo)(ha))(ab)
          )
        )(
          lt => +ab => Crit.union_go_wf(~V, ~j, oa, b, 1n+pa, ra, True{})(Crit.wf.wf_o(~V, ra, pa, ea, za, oa, lo)(ha))(Crit.wf_lower(~V, rb, pb, eb, zb, ob, lo, 1n+pa)(hb)(Crit.lt_le_succ(pa, pb)(lt)))(
            Crit.and_true(Crit.all(~V, ~Place, ~Place.has, oa, Place{ra, pa, True{}}), Crit.all(~V, ~Place, ~Place.has, Crit.Fork{rb, pb, eb, zb, ob}, Place{ra, pa, True{}}))(Crit.wf.all_o(~V, ra, pa, ea, za, oa, lo)(ha))(ab)
          )
        )(
          gt => +aa => Crit.union_go_wf(~V, ~j, a, zb, 1n+pb, rb, False{})(Crit.wf_lower(~V, ra, pa, ea, za, oa, lo, 1n+pb)(ha)(Crit.lt_le_succ(pb, pa)(gt)))(Crit.wf.wf_z(~V, rb, pb, eb, zb, ob, lo)(hb))(
            Crit.and_true(Crit.all(~V, ~Place, ~Place.has, Crit.Fork{ra, pa, ea, za, oa}, Place{rb, pb, False{}}), Crit.all(~V, ~Place, ~Place.has, zb, Place{rb, pb, False{}}))(aa)(Crit.wf.all_z(~V, rb, pb, eb, zb, ob, lo)(hb))
          )
        )(
          gt => +aa => Crit.union_go_wf(~V, ~j, a, ob, 1n+pb, rb, True{})(Crit.wf_lower(~V, ra, pa, ea, za, oa, lo, 1n+pb)(ha)(Crit.lt_le_succ(pb, pa)(gt)))(Crit.wf.wf_o(~V, rb, pb, eb, zb, ob, lo)(hb))(
            Crit.and_true(Crit.all(~V, ~Place, ~Place.has, Crit.Fork{ra, pa, ea, za, oa}, Place{rb, pb, True{}}), Crit.all(~V, ~Place, ~Place.has, ob, Place{rb, pb, True{}}))(aa)(Crit.wf.all_o(~V, rb, pb, eb, zb, ob, lo)(hb))
          )
        )
      )

# a union keeps maps well formed
law Crit.union_wf:
  for ~V: Data
  for ~j: V -> V -> V
  for a: Crit<V>
  for b: Crit<V>
  {Crit.wf(~V, a, 0n) == True{}: Bool} -> {Crit.wf(~V, b, 0n) == True{}: Bool} -> {Crit.wf(~V, Crit.union(~V, ~j, a, b), 0n) == True{}: Bool}

def Crit.union_wf(ty, j, a, b):
  ha => hb => Crit.union_go_wf(~ty, ~j, a, b, 0n, [], False{})(ha)(hb)({==})

# what holds when a test holds, and when it does not, holds
def Crit.bool_split(-T: Type, b: Bool) -> ({b == True{}: Bool} -> T) -> ({b == False{}: Bool} -> T) -> T:
  match b:
    case True{}:
      ft => ff => ft({==})
    case False{}:
      ft => ff => ff({==})

# a value that is not some is None
def Crit.none_of_some(-V: Data, m: Maybe<&2, V>) -> {Maybe.is_some(&2, V, m) == False{}: Bool} -> {m == None{}: Maybe<&2, V>}:
  match m:
    case None{}:
      h => {==}
    case Some{x}:
      h => Empty.absurd({Some{x} == None{}: Maybe<&2, V>}, Shared.Bool.true_ne_false(h))

# nothing joined with b is b
def Crit.join_none_l(~V: Data, ~j: V -> V -> V, m: Maybe<&2, V>) -> {Shared.Maybe.join(~V, ~j, None{}, m) == m: Maybe<&2, V>}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

# a join of nothing and nothing is nothing
def Crit.join_nn(~V: Data, ~j: V -> V -> V, x: Maybe<&2, V>, y: Maybe<&2, V>) -> {x == None{}: Maybe<&2, V>} -> {y == None{}: Maybe<&2, V>} -> {Shared.Maybe.join(~V, ~j, x, y) == None{}: Maybe<&2, V>}:
  match x y:
    case None{} None{}:
      hx => hy => {==}
    case None{} Some{b}:
      hx => hy => Empty.absurd({Some{b} == None{}: Maybe<&2, V>}, Crit.some_ne_none(V, b, hy))
    case Some{a} y1:
      hx => hy => Empty.absurd({Shared.Maybe.join(~V, ~j, Some{a}, y1) == None{}: Maybe<&2, V>}, Crit.some_ne_none(V, a, hx))

# of two reads of which one at most is some, the choice is the join
def Crit.or_join(~V: Data, ~j: V -> V -> V, x: Maybe<&2, V>, y: Maybe<&2, V>) -> {Bool.or(Maybe.is_none(&2, V, x), Maybe.is_none(&2, V, y)) == True{}: Bool} -> {
  Maybe.or(&2, V, x, y) == Shared.Maybe.join(~V, ~j, x, y): Maybe<&2, V>
}:
  match x y:
    case None{} None{}:
      h => {==}
    case None{} Some{b}:
      h => {==}
    case Some{a} None{}:
      h => {==}
    case Some{a} Some{b}:
      h => Empty.absurd({Some{a} == Some{j(a, b)}: Maybe<&2, V>}, Shared.Bool.false_ne_true(h))

# two reads that are not both some hold no key in common
def Crit.disj_of(-V: Data, x: Maybe<&2, V>, y: Maybe<&2, V>) -> ({Maybe.is_some(&2, V, x) == True{}: Bool} -> {Maybe.is_some(&2, V, y) == True{}: Bool} -> Empty) -> {
  Bool.or(Maybe.is_none(&2, V, x), Maybe.is_none(&2, V, y)) == True{}: Bool
}:
  match x y:
    case None{} y1:
      f => {==}
    case Some{a} None{}:
      f => {==}
    case Some{a} Some{b}:
      f => Empty.absurd({False{} == True{}: Bool}, f({==})({==}))

# a choice of the value u, where b, that is nothing is nothing for any value
def Crit.when_none_any(-V: Data, b: Bool, -u: V, -x: V) -> {Shared.Maybe.when(V, b, y => Some{u}) == None{}: Maybe<&2, V>} -> {
  Shared.Maybe.when(V, b, y => Some{x}) == None{}: Maybe<&2, V>
}:
  match b:
    case True{}:
      h => Empty.absurd({Some{x} == None{}: Maybe<&2, V>}, Crit.some_ne_none(V, u, h))
    case False{}:
      h => {==}

# a choice of the join of u and w is the join of the choices of u and w
def Crit.join_when(~V: Data, ~j: V -> V -> V, b: Bool, -u: V, -w: V) -> {
  Shared.Maybe.when(V, b, y => Some{j(u, w)}) == Shared.Maybe.join(~V, ~j, Shared.Maybe.when(V, b, y => Some{u}), Shared.Maybe.when(V, b, y => Some{w})): Maybe<&2, V>
}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# a write with the join flipped joins the new value on the left
def Crit.merge_join_l(~V: Data, ~j: V -> V -> V, m: Maybe<&2, V>, +v: V) -> {Some{Crit.merge(~V, ~(w => x => j(x, w)), m, v)} == Shared.Maybe.join(~V, ~j, Some{v}, m): Maybe<&2, V>}:
  match m:
    case None{}:
      {==}
    case Some{u}:
      {==}

# a write with the join joins the new value on the right
def Crit.merge_join_r(~V: Data, ~j: V -> V -> V, m: Maybe<&2, V>, +w: V) -> {Some{Crit.merge(~V, ~j, m, w)} == Shared.Maybe.join(~V, ~j, m, Some{w}): Maybe<&2, V>}:
  match m:
    case None{}:
      {==}
    case Some{u}:
      {==}

# the union of an entry and a map that is well formed below any bit
def Crit.union_leaf_l(~V: Data, ~j: V -> V -> V, +k: List<&2, U32>, +v: V, +y: Crit<V>, +ly: Nat, +q: List<&2, U32>) -> {Crit.wf(~V, y, ly) == True{}: Bool} -> {
  Crit.lookup(V, Crit.upsert(~V, ~(w => x => j(x, w)), y, k, v), q) == Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Leaf{k, v}, q), Crit.lookup(V, y, q)): Maybe<&2, V>
}:
  h => Equal.trans(
    Maybe<&2, V>,
    Crit.lookup(V, Crit.upsert(~V, ~(w => x => j(x, w)), y, k, v), q),
    Bool.pick(Maybe<&2, V>, Key.is_eq(q, k), Some{Crit.merge(~V, ~(w => x => j(x, w)), Crit.lookup(V, y, k), v)}, Crit.lookup(V, y, q)),
    Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Leaf{k, v}, q), Crit.lookup(V, y, q)),
    Crit.upsert_lookup.at(~V, ~(w => x => j(x, w)), y, ly, k, v, q, Crit.near(V, y, 0n, Cur.of(k)))(h)({==}),
    Crit.pick_cases(Maybe<&2, V>, Key.is_eq(q, k), Some{Crit.merge(~V, ~(w => x => j(x, w)), Crit.lookup(V, y, k), v)}, Crit.lookup(V, y, q), Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Leaf{k, v}, q), Crit.lookup(V, y, q)))(
      t => (
        %Equal.sym(List<&2, U32>, q, k, Key.is_eq_sound(q, k)(t)): {Some{Crit.merge(~V, ~(w => x => j(x, w)), Crit.lookup(V, y, k), v)} == Shared.Maybe.join(~V, ~j, Shared.Maybe.when(V, Key.is_eq(k, _), u => Some{v}), Crit.lookup(V, y, _)): Maybe<&2, V>}
        %Equal.sym(Bool, Key.is_eq(k, k), True{}, Key.is_eq_refl(k)): {Some{Crit.merge(~V, ~(w => x => j(x, w)), Crit.lookup(V, y, k), v)} == Shared.Maybe.join(~V, ~j, Shared.Maybe.when(V, _, u => Some{v}), Crit.lookup(V, y, k)): Maybe<&2, V>}
        Crit.merge_join_l(~V, ~j, Crit.lookup(V, y, k), v)
      )
    )(
      f => (
        %Equal.sym(Bool, Key.is_eq(k, q), False{}, Key.ne_sym(q, k)(f)): {Crit.lookup(V, y, q) == Shared.Maybe.join(~V, ~j, Shared.Maybe.when(V, _, u => Some{v}), Crit.lookup(V, y, q)): Maybe<&2, V>}
        Equal.sym(Maybe<&2, V>, Shared.Maybe.join(~V, ~j, None{}, Crit.lookup(V, y, q)), Crit.lookup(V, y, q), Crit.join_none_l(~V, ~j, Crit.lookup(V, y, q)))
      )
    )
  )

# the union of a map that is well formed below any bit and an entry
def Crit.union_leaf_r(~V: Data, ~j: V -> V -> V, +a: Crit<V>, +la: Nat, +k: List<&2, U32>, +w: V, +q: List<&2, U32>) -> {Crit.wf(~V, a, la) == True{}: Bool} -> {
  Crit.lookup(V, Crit.upsert(~V, ~j, a, k, w), q) == Shared.Maybe.join(~V, ~j, Crit.lookup(V, a, q), Crit.lookup(V, Crit.Leaf{k, w}, q)): Maybe<&2, V>
}:
  h => Equal.trans(
    Maybe<&2, V>,
    Crit.lookup(V, Crit.upsert(~V, ~j, a, k, w), q),
    Bool.pick(Maybe<&2, V>, Key.is_eq(q, k), Some{Crit.merge(~V, ~j, Crit.lookup(V, a, k), w)}, Crit.lookup(V, a, q)),
    Shared.Maybe.join(~V, ~j, Crit.lookup(V, a, q), Crit.lookup(V, Crit.Leaf{k, w}, q)),
    Crit.upsert_lookup.at(~V, ~j, a, la, k, w, q, Crit.near(V, a, 0n, Cur.of(k)))(h)({==}),
    Crit.pick_cases(Maybe<&2, V>, Key.is_eq(q, k), Some{Crit.merge(~V, ~j, Crit.lookup(V, a, k), w)}, Crit.lookup(V, a, q), Shared.Maybe.join(~V, ~j, Crit.lookup(V, a, q), Crit.lookup(V, Crit.Leaf{k, w}, q)))(
      t => (
        %Equal.sym(List<&2, U32>, q, k, Key.is_eq_sound(q, k)(t)): {Some{Crit.merge(~V, ~j, Crit.lookup(V, a, k), w)} == Shared.Maybe.join(~V, ~j, Crit.lookup(V, a, _), Shared.Maybe.when(V, Key.is_eq(k, _), u => Some{w})): Maybe<&2, V>}
        %Equal.sym(Bool, Key.is_eq(k, k), True{}, Key.is_eq_refl(k)): {Some{Crit.merge(~V, ~j, Crit.lookup(V, a, k), w)} == Shared.Maybe.join(~V, ~j, Crit.lookup(V, a, k), Shared.Maybe.when(V, _, u => Some{w})): Maybe<&2, V>}
        Crit.merge_join_r(~V, ~j, Crit.lookup(V, a, k), w)
      )
    )(
      f => (
        %Equal.sym(Bool, Key.is_eq(k, q), False{}, Key.ne_sym(q, k)(f)): {Crit.lookup(V, a, q) == Shared.Maybe.join(~V, ~j, Crit.lookup(V, a, q), Shared.Maybe.when(V, _, u => Some{w})): Maybe<&2, V>}
        Equal.sym(Maybe<&2, V>, Shared.Maybe.join(~V, ~j, Crit.lookup(V, a, q), None{}), Crit.lookup(V, a, q), Shared.Maybe.join_none(~V, ~j, Crit.lookup(V, a, q)))
      )
    )
  )

# two well formed forks whose reps differ before both bits hold no key in
# common
def Crit.forks_disj(~V: Data, +ra: List<&2, U32>, +pa: Nat, +ea: Maybe<&2, V>, +za: Crit<V>, +oa: Crit<V>, +rb: List<&2, U32>, +pb: Nat, +eb: Maybe<&2, V>, +zb: Crit<V>, +ob: Crit<V>, +la: Nat, +lb: Nat, +q: List<&2, U32>) -> {Crit.wf(~V, Crit.Fork{ra, pa, ea, za, oa}, la) == True{}: Bool} -> {Crit.wf(~V, Crit.Fork{rb, pb, eb, zb, ob}, lb) == True{}: Bool} -> {Bool.and(Crit.above(Key.diff(ra, rb), pa), Crit.above(Key.diff(ra, rb), pb)) == True{}: Bool} -> {Bool.or(Maybe.is_none(&2, V, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q)), Maybe.is_none(&2, V, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q))) == True{}: Bool}:
  +ha => +hb => +hab => Crit.disj_of(V, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q))(
    +s => +t =>
      +sd = Crit.above_some(Key.diff(ra, rb), pa)(Shared.Bool.and_true_left(Crit.above(Key.diff(ra, rb), pa), Crit.above(Key.diff(ra, rb), pb))(hab))
      +lta = Crit.above_lt(Key.diff(ra, rb), pa, Maybe.default(&2, Nat, Key.diff(ra, rb), 0n))(sd)(Shared.Bool.and_true_left(Crit.above(Key.diff(ra, rb), pa), Crit.above(Key.diff(ra, rb), pb))(hab))
      +ltb = Crit.above_lt(Key.diff(ra, rb), pb, Maybe.default(&2, Nat, Key.diff(ra, rb), 0n))(sd)(Shared.Bool.and_true_right(Crit.above(Key.diff(ra, rb), pa), Crit.above(Key.diff(ra, rb), pb))(hab))
      +qa = Key.agree_le(q, ra, 1n+Maybe.default(&2, Nat, Key.diff(ra, rb), 0n), pa)(Crit.lt_le_succ(Maybe.default(&2, Nat, Key.diff(ra, rb), 0n), pa)(lta))(Crit.in_fork_agree(~V, ra, pa, ea, za, oa, la, q)(ha)(s))
      +qb = Key.agree_le(q, rb, 1n+Maybe.default(&2, Nat, Key.diff(ra, rb), 0n), pb)(Crit.lt_le_succ(Maybe.default(&2, Nat, Key.diff(ra, rb), 0n), pb)(ltb))(Crit.in_fork_agree(~V, rb, pb, eb, zb, ob, lb, q)(hb)(t))
      Crit.clash(
        Key.agree(ra, rb, 1n+Maybe.default(&2, Nat, Key.diff(ra, rb), 0n)),
        True{},
        False{},
        Key.agree_join(ra, rb, q, 1n+Maybe.default(&2, Nat, Key.diff(ra, rb), 0n))(Key.agree_sym(q, ra, 1n+Maybe.default(&2, Nat, Key.diff(ra, rb), 0n))(qa))(Key.agree_sym(q, rb, 1n+Maybe.default(&2, Nat, Key.diff(ra, rb), 0n))(qb)),
        (
          %Equal.sym(Maybe<&2, Nat>, Key.diff(ra, rb), Some{Maybe.default(&2, Nat, Key.diff(ra, rb), 0n)}, sd): {Bits.agree(_, 1n+Maybe.default(&2, Nat, Key.diff(ra, rb), 0n)) == False{}: Bool}
          Shared.Nat.succ_nle(Maybe.default(&2, Nat, Key.diff(ra, rb), 0n))
        ),
        Shared.Bool.true_ne_false
      )
  )

# the end of a union of two forks at one bit, read at q, is nothing when
# both ends are
def Crit.ended_union_none(~V: Data, ~j: V -> V -> V, +ra: List<&2, U32>, ea: Maybe<&2, V>, +rb: List<&2, U32>, eb: Maybe<&2, V>, +q: List<&2, U32>) -> {Crit.ended(V, ra, ea, q) == None{}: Maybe<&2, V>} -> {
  Crit.ended(V, rb, eb, q) == None{}: Maybe<&2, V>
} -> {Crit.ended(V, Bool.pick(List<&2, U32>, Maybe.is_some(&2, V, ea), ra, rb), Shared.Maybe.join(~V, ~j, ea, eb), q) == None{}: Maybe<&2, V>}:
  match ea eb:
    case None{} None{}:
      h1 => h2 => {==}
    case Some{u} None{}:
      h1 => h2 => h1
    case None{} Some{w}:
      h1 => h2 => h2
    case Some{u} Some{w}:
      h1 => h2 => Crit.when_none_any(V, Key.is_eq(ra, q), u, j(u, w))(h1)

# the end of a union of two forks at one bit, read at q
def Crit.ends_union(
  ~V: Data,
  ~j: V -> V -> V,
  +ra: List<&2, U32>,
  +pa: Nat,
  ea: Maybe<&2, V>,
  -za: Crit<V>,
  +rb: List<&2, U32>,
  +pb: Nat,
  eb: Maybe<&2, V>,
  -zb: Crit<V>,
  +q: List<&2, U32>
) -> {Crit.rep_ok(V, ra, pa, ea, za) == True{}: Bool} -> {Crit.rep_ok(V, rb, pb, eb, zb) == True{}: Bool} -> {pa == pb: Nat} -> {
  Crit.above(Key.diff(ra, rb), pa) == False{}: Bool
} -> {Crit.ended(V, Bool.pick(List<&2, U32>, Maybe.is_some(&2, V, ea), ra, rb), Shared.Maybe.join(~V, ~j, ea, eb), q) == Shared.Maybe.join(~V, ~j, Crit.ended(V, ra, ea, q), Crit.ended(V, rb, eb, q)): Maybe<&2, V>}:
  match ea eb:
    case None{} None{}:
      hra => hrb => eqp => hab => {==}
    case Some{u} None{}:
      hra => hrb => eqp => hab => Equal.sym(Maybe<&2, V>, Shared.Maybe.join(~V, ~j, Crit.ended(V, ra, Some{u}, q), None{}), Crit.ended(V, ra, Some{u}, q), Shared.Maybe.join_none(~V, ~j, Crit.ended(V, ra, Some{u}, q)))
    case None{} Some{w}:
      hra => hrb => eqp => hab => Equal.sym(Maybe<&2, V>, Shared.Maybe.join(~V, ~j, None{}, Crit.ended(V, rb, Some{w}, q)), Crit.ended(V, rb, Some{w}, q), Crit.join_none_l(~V, ~j, Crit.ended(V, rb, Some{w}, q)))
    case Some{u} Some{w}:
      hra => hrb => eqp => hab =>
        %Key.is_eq_sound(rb, ra)(
          Crit.end_is(rb, pa, ra)((
            %Equal.sym(Nat, pa, pb, eqp): {Nat.is_eq(List.length(&2, Bool, Key.bits(rb)), _) == True{}: Bool}
            hrb
          ))((
            %Shared.Nat.is_eq_sound(List.length(&2, Bool, Key.bits(ra)), pa)(hra): {List.drop(&2, Bool, Key.bits(ra), _) == []: List<&2, Bool>}
            Crit.drop_length(Key.bits(ra))
          ))(hab)
        ): {Crit.ended(V, _, Some{j(u, w)}, q) == Shared.Maybe.join(~V, ~j, Shared.Maybe.when(V, Key.is_eq(_, q), x => Some{u}), Shared.Maybe.when(V, Key.is_eq(rb, q), x => Some{w})): Maybe<&2, V>}
        Crit.join_when(~V, ~j, Key.is_eq(rb, q), u, w)

# the union of two well formed forks at one bit, whose reps agree before it
def Crit.union_eq(~V: Data, ~j: V -> V -> V, +ra: List<&2, U32>, +pa: Nat, +ea: Maybe<&2, V>, +za: Crit<V>, +oa: Crit<V>, +rb: List<&2, U32>, +pb: Nat, +eb: Maybe<&2, V>, +zb: Crit<V>, +ob: Crit<V>, +la: Nat, +lb: Nat, +q: List<&2, U32>) -> {Crit.wf(~V, Crit.Fork{ra, pa, ea, za, oa}, la) == True{}: Bool} -> {Crit.wf(~V, Crit.Fork{rb, pb, eb, zb, ob}, lb) == True{}: Bool} -> {pa == pb: Nat} -> {Crit.above(Key.diff(ra, rb), pa) == False{}: Bool} -> {
  Crit.lookup(V, Crit.union(~V, ~j, za, zb), q) == Shared.Maybe.join(~V, ~j, Crit.lookup(V, za, q), Crit.lookup(V, zb, q)): Maybe<&2, V>
} -> {Crit.lookup(V, Crit.union(~V, ~j, oa, ob), q) == Shared.Maybe.join(~V, ~j, Crit.lookup(V, oa, q), Crit.lookup(V, ob, q)): Maybe<&2, V>} -> {
  Crit.lookup(V, Crit.mk(V, Bool.pick(List<&2, U32>, Maybe.is_some(&2, V, ea), ra, rb), pa, Shared.Maybe.join(~V, ~j, ea, eb), Crit.union(~V, ~j, za, zb), Crit.union(~V, ~j, oa, ob)), q) == Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)): Maybe<&2, V>
}:
  +ha => +hb => +eqp => +hab => +iz => +io => Equal.trans(
    Maybe<&2, V>,
    Crit.lookup(V, Crit.mk(V, Bool.pick(List<&2, U32>, Maybe.is_some(&2, V, ea), ra, rb), pa, Shared.Maybe.join(~V, ~j, ea, eb), Crit.union(~V, ~j, za, zb), Crit.union(~V, ~j, oa, ob)), q),
    Maybe.or(&2, V, Crit.ended(V, Bool.pick(List<&2, U32>, Maybe.is_some(&2, V, ea), ra, rb), Shared.Maybe.join(~V, ~j, ea, eb), q), Maybe.or(&2, V, Crit.lookup(V, Crit.union(~V, ~j, za, zb), q), Crit.lookup(V, Crit.union(~V, ~j, oa, ob), q))),
    Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)),
    Crit.mk_lookup(V, Bool.pick(List<&2, U32>, Maybe.is_some(&2, V, ea), ra, rb), pa, Shared.Maybe.join(~V, ~j, ea, eb), Crit.union(~V, ~j, za, zb), Crit.union(~V, ~j, oa, ob), q),
    Crit.side_split({Maybe.or(&2, V, Crit.ended(V, Bool.pick(List<&2, U32>, Maybe.is_some(&2, V, ea), ra, rb), Shared.Maybe.join(~V, ~j, ea, eb), q), Maybe.or(&2, V, Crit.lookup(V, Crit.union(~V, ~j, za, zb), q), Crit.lookup(V, Crit.union(~V, ~j, oa, ob), q))) == Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)): Maybe<&2, V>}, q, pa)(
      +hs => Equal.trans(Maybe<&2, V>, Maybe.or(&2, V, Crit.ended(V, Bool.pick(List<&2, U32>, Maybe.is_some(&2, V, ea), ra, rb), Shared.Maybe.join(~V, ~j, ea, eb), q), Maybe.or(&2, V, Crit.lookup(V, Crit.union(~V, ~j, za, zb), q), Crit.lookup(V, Crit.union(~V, ~j, oa, ob), q))), Crit.lookup(V, Crit.union(~V, ~j, oa, ob), q), Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), Crit.or_third(V, Crit.ended(V, Bool.pick(List<&2, U32>, Maybe.is_some(&2, V, ea), ra, rb), Shared.Maybe.join(~V, ~j, ea, eb), q), Crit.lookup(V, Crit.union(~V, ~j, za, zb), q), Crit.lookup(V, Crit.union(~V, ~j, oa, ob), q))(Crit.ended_union_none(~V, ~j, ra, ea, rb, eb, q)(Crit.ended_long(V, ra, pa, ea, za, q, List.drop(&2, Bool, Key.bits(q), pa))(Crit.wf.rep_ok(~V, ra, pa, ea, za, oa, la)(ha))({==})(Crit.side_some_ne(q, pa, True{})(hs)))(Crit.ended_long(V, rb, pb, eb, zb, q, List.drop(&2, Bool, Key.bits(q), pb))(Crit.wf.rep_ok(~V, rb, pb, eb, zb, ob, lb)(hb))({==})(Crit.side_some_ne(q, pb, True{})((
          %eqp: {Key.side(q, _) == Some{True{}}: Maybe<&2, Bool>}
          hs
        )))))(Equal.trans(Maybe<&2, V>, Crit.lookup(V, Crit.union(~V, ~j, za, zb), q), Shared.Maybe.join(~V, ~j, Crit.lookup(V, za, q), Crit.lookup(V, zb, q)), None{}, iz, Crit.join_nn(~V, ~j, Crit.lookup(V, za, q), Crit.lookup(V, zb, q))(Crit.lookup_all(~V, ~Place, ~Place.has, za, Place{ra, pa, False{}}, q)(Crit.wf.all_z(~V, ra, pa, ea, za, oa, la)(ha))(Place.has_not(ra, pa, False{}, q, Some{True{}}, hs, {==})))(Crit.lookup_all(~V, ~Place, ~Place.has, zb, Place{rb, pb, False{}}, q)(Crit.wf.all_z(~V, rb, pb, eb, zb, ob, lb)(hb))(Place.has_not(rb, pb, False{}, q, Some{True{}}, (
          %eqp: {Key.side(q, _) == Some{True{}}: Maybe<&2, Bool>}
          hs
        ), {==}))))), Equal.trans(Maybe<&2, V>, Crit.lookup(V, Crit.union(~V, ~j, oa, ob), q), Shared.Maybe.join(~V, ~j, Crit.lookup(V, oa, q), Crit.lookup(V, ob, q)), Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), io, Equal.sym(Maybe<&2, V>, Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), Shared.Maybe.join(~V, ~j, Crit.lookup(V, oa, q), Crit.lookup(V, ob, q)), Equal.trans(Maybe<&2, V>, Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), Shared.Maybe.join(~V, ~j, Crit.lookup(V, oa, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), Shared.Maybe.join(~V, ~j, Crit.lookup(V, oa, q), Crit.lookup(V, ob, q)), Equal.cong(Maybe<&2, V>, Maybe<&2, V>, t => Shared.Maybe.join(~V, ~j, t, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, oa, q), Crit.route_side(~V, ra, pa, ea, za, oa, la, q, True{})(ha)(hs)), Equal.cong(Maybe<&2, V>, Maybe<&2, V>, t => Shared.Maybe.join(~V, ~j, Crit.lookup(V, oa, q), t), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q), Crit.lookup(V, ob, q), Crit.route_side(~V, rb, pb, eb, zb, ob, lb, q, True{})(hb)((
          %eqp: {Key.side(q, _) == Some{True{}}: Maybe<&2, Bool>}
          hs
        )))))))
    )(
      +hs => Equal.trans(Maybe<&2, V>, Maybe.or(&2, V, Crit.ended(V, Bool.pick(List<&2, U32>, Maybe.is_some(&2, V, ea), ra, rb), Shared.Maybe.join(~V, ~j, ea, eb), q), Maybe.or(&2, V, Crit.lookup(V, Crit.union(~V, ~j, za, zb), q), Crit.lookup(V, Crit.union(~V, ~j, oa, ob), q))), Crit.lookup(V, Crit.union(~V, ~j, za, zb), q), Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), Crit.or_second(V, Crit.ended(V, Bool.pick(List<&2, U32>, Maybe.is_some(&2, V, ea), ra, rb), Shared.Maybe.join(~V, ~j, ea, eb), q), Crit.lookup(V, Crit.union(~V, ~j, za, zb), q), Crit.lookup(V, Crit.union(~V, ~j, oa, ob), q))(Crit.ended_union_none(~V, ~j, ra, ea, rb, eb, q)(Crit.ended_long(V, ra, pa, ea, za, q, List.drop(&2, Bool, Key.bits(q), pa))(Crit.wf.rep_ok(~V, ra, pa, ea, za, oa, la)(ha))({==})(Crit.side_some_ne(q, pa, False{})(hs)))(Crit.ended_long(V, rb, pb, eb, zb, q, List.drop(&2, Bool, Key.bits(q), pb))(Crit.wf.rep_ok(~V, rb, pb, eb, zb, ob, lb)(hb))({==})(Crit.side_some_ne(q, pb, False{})((
          %eqp: {Key.side(q, _) == Some{False{}}: Maybe<&2, Bool>}
          hs
        )))))(Equal.trans(Maybe<&2, V>, Crit.lookup(V, Crit.union(~V, ~j, oa, ob), q), Shared.Maybe.join(~V, ~j, Crit.lookup(V, oa, q), Crit.lookup(V, ob, q)), None{}, io, Crit.join_nn(~V, ~j, Crit.lookup(V, oa, q), Crit.lookup(V, ob, q))(Crit.lookup_all(~V, ~Place, ~Place.has, oa, Place{ra, pa, True{}}, q)(Crit.wf.all_o(~V, ra, pa, ea, za, oa, la)(ha))(Place.has_not(ra, pa, True{}, q, Some{False{}}, hs, {==})))(Crit.lookup_all(~V, ~Place, ~Place.has, ob, Place{rb, pb, True{}}, q)(Crit.wf.all_o(~V, rb, pb, eb, zb, ob, lb)(hb))(Place.has_not(rb, pb, True{}, q, Some{False{}}, (
          %eqp: {Key.side(q, _) == Some{False{}}: Maybe<&2, Bool>}
          hs
        ), {==}))))), Equal.trans(Maybe<&2, V>, Crit.lookup(V, Crit.union(~V, ~j, za, zb), q), Shared.Maybe.join(~V, ~j, Crit.lookup(V, za, q), Crit.lookup(V, zb, q)), Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), iz, Equal.sym(Maybe<&2, V>, Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), Shared.Maybe.join(~V, ~j, Crit.lookup(V, za, q), Crit.lookup(V, zb, q)), Equal.trans(Maybe<&2, V>, Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), Shared.Maybe.join(~V, ~j, Crit.lookup(V, za, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), Shared.Maybe.join(~V, ~j, Crit.lookup(V, za, q), Crit.lookup(V, zb, q)), Equal.cong(Maybe<&2, V>, Maybe<&2, V>, t => Shared.Maybe.join(~V, ~j, t, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, za, q), Crit.route_side(~V, ra, pa, ea, za, oa, la, q, False{})(ha)(hs)), Equal.cong(Maybe<&2, V>, Maybe<&2, V>, t => Shared.Maybe.join(~V, ~j, Crit.lookup(V, za, q), t), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q), Crit.lookup(V, zb, q), Crit.route_side(~V, rb, pb, eb, zb, ob, lb, q, False{})(hb)((
          %eqp: {Key.side(q, _) == Some{False{}}: Maybe<&2, Bool>}
          hs
        )))))))
    )(
      +hs =>
          +nil = Crit.side_nil(q, pa)(hs)
          +nilb = Crit.side_nil(q, pb)((
          %eqp: {Key.side(q, _) == None{}: Maybe<&2, Bool>}
          hs
        ))
          Equal.trans(
            Maybe<&2, V>,
            Maybe.or(&2, V, Crit.ended(V, Bool.pick(List<&2, U32>, Maybe.is_some(&2, V, ea), ra, rb), Shared.Maybe.join(~V, ~j, ea, eb), q), Maybe.or(&2, V, Crit.lookup(V, Crit.union(~V, ~j, za, zb), q), Crit.lookup(V, Crit.union(~V, ~j, oa, ob), q))),
            Crit.ended(V, Bool.pick(List<&2, U32>, Maybe.is_some(&2, V, ea), ra, rb), Shared.Maybe.join(~V, ~j, ea, eb), q),
            Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)),
            Crit.or_first(V, Crit.ended(V, Bool.pick(List<&2, U32>, Maybe.is_some(&2, V, ea), ra, rb), Shared.Maybe.join(~V, ~j, ea, eb), q), Crit.lookup(V, Crit.union(~V, ~j, za, zb), q), Crit.lookup(V, Crit.union(~V, ~j, oa, ob), q))(
              Equal.trans(Maybe<&2, V>, Crit.lookup(V, Crit.union(~V, ~j, za, zb), q), Shared.Maybe.join(~V, ~j, Crit.lookup(V, za, q), Crit.lookup(V, zb, q)), None{}, iz, Crit.join_nn(~V, ~j, Crit.lookup(V, za, q), Crit.lookup(V, zb, q))(Crit.no_side(~V, ra, pa, za, False{}, q)(Crit.wf.all_z(~V, ra, pa, ea, za, oa, la)(ha))(nil))(Crit.no_side(~V, rb, pb, zb, False{}, q)(Crit.wf.all_z(~V, rb, pb, eb, zb, ob, lb)(hb))(nilb)))
            )(Equal.trans(Maybe<&2, V>, Crit.lookup(V, Crit.union(~V, ~j, oa, ob), q), Shared.Maybe.join(~V, ~j, Crit.lookup(V, oa, q), Crit.lookup(V, ob, q)), None{}, io, Crit.join_nn(~V, ~j, Crit.lookup(V, oa, q), Crit.lookup(V, ob, q))(Crit.no_side(~V, ra, pa, oa, True{}, q)(Crit.wf.all_o(~V, ra, pa, ea, za, oa, la)(ha))(nil))(Crit.no_side(~V, rb, pb, ob, True{}, q)(Crit.wf.all_o(~V, rb, pb, eb, zb, ob, lb)(hb))(nilb)))),
            Equal.trans(
              Maybe<&2, V>,
              Crit.ended(V, Bool.pick(List<&2, U32>, Maybe.is_some(&2, V, ea), ra, rb), Shared.Maybe.join(~V, ~j, ea, eb), q),
              Shared.Maybe.join(~V, ~j, Crit.ended(V, ra, ea, q), Crit.ended(V, rb, eb, q)),
              Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)),
              Crit.ends_union(~V, ~j, ra, pa, ea, za, rb, pb, eb, zb, q)(Crit.wf.rep_ok(~V, ra, pa, ea, za, oa, la)(ha))(Crit.wf.rep_ok(~V, rb, pb, eb, zb, ob, lb)(hb))(eqp)(hab),
              Equal.sym(
                Maybe<&2, V>,
                Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)),
                Shared.Maybe.join(~V, ~j, Crit.ended(V, ra, ea, q), Crit.ended(V, rb, eb, q)),
                Equal.trans(
                  Maybe<&2, V>,
                  Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)),
                  Shared.Maybe.join(~V, ~j, Crit.ended(V, ra, ea, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)),
                  Shared.Maybe.join(~V, ~j, Crit.ended(V, ra, ea, q), Crit.ended(V, rb, eb, q)),
                  Equal.cong(Maybe<&2, V>, Maybe<&2, V>, t => Shared.Maybe.join(~V, ~j, t, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.ended(V, ra, ea, q), Crit.route_end(~V, ra, pa, ea, za, oa, la, q)(ha)(hs)),
                  Equal.cong(Maybe<&2, V>, Maybe<&2, V>, t => Shared.Maybe.join(~V, ~j, Crit.ended(V, ra, ea, q), t), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q), Crit.ended(V, rb, eb, q), Crit.route_end(~V, rb, pb, eb, zb, ob, lb, q)(hb)((
          %eqp: {Key.side(q, _) == None{}: Maybe<&2, Bool>}
          hs
        )))
                )
              )
            )
          )
    )
  )

# the union of two well formed forks whose reps agree before the bit pa of
# the first, which is before the bit pb of the second: b goes to its side of a
def Crit.union_lt(~V: Data, ~j: V -> V -> V, +ra: List<&2, U32>, +pa: Nat, +ea: Maybe<&2, V>, +za: Crit<V>, +oa: Crit<V>, +rb: List<&2, U32>, +pb: Nat, +eb: Maybe<&2, V>, +zb: Crit<V>, +ob: Crit<V>, +la: Nat, +lb: Nat, +q: List<&2, U32>) -> {Crit.wf(~V, Crit.Fork{ra, pa, ea, za, oa}, la) == True{}: Bool} -> {Crit.wf(~V, Crit.Fork{rb, pb, eb, zb, ob}, lb) == True{}: Bool} -> {Nat.is_lt(pa, pb) == True{}: Bool} -> {Crit.above(Key.diff(ra, rb), pa) == False{}: Bool} -> {
  Crit.lookup(V, Crit.union(~V, ~j, za, Crit.Fork{rb, pb, eb, zb, ob}), q) == Shared.Maybe.join(~V, ~j, Crit.lookup(V, za, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)): Maybe<&2, V>
} -> {Crit.lookup(V, Crit.union(~V, ~j, oa, Crit.Fork{rb, pb, eb, zb, ob}), q) == Shared.Maybe.join(~V, ~j, Crit.lookup(V, oa, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)): Maybe<&2, V>} -> {
  Crit.lookup(V, Shared.Bool.when(Crit<V>, Key.bit(rb, pa), u => Crit.mk(V, ra, pa, ea, za, Crit.union(~V, ~j, oa, Crit.Fork{rb, pb, eb, zb, ob})), u => Crit.mk(V, ra, pa, ea, Crit.union(~V, ~j, za, Crit.Fork{rb, pb, eb, zb, ob}), oa)), q) == Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)): Maybe<&2, V>
}:
  +ha => +hb => +lt => +hab => +iz => +io =>
    +nr = Crit.len_drop(Key.bits(rb), pa)(Shared.Nat.lt_le(pa, pb, List.length(&2, Bool, Key.bits(rb)))(lt)(Crit.rep_long(~V, rb, pb, eb, zb, ob, lb)(hb)))
    +t2n = Equal.trans(
      Bool,
      Cur.done(Key.at(rb, pa)),
      List.is_empty(&2, Bool, List.drop(&2, Bool, Key.bits(rb), pa)),
      False{},
      Crit.done_of(Key.at(rb, pa), List.drop(&2, Bool, Key.bits(rb), pa))(Cur.skip_bits(pa, Cur.of(rb))),
      nr
    )
    +allb = Crit.fork_place(~V, rb, pb, eb, zb, ob, lb, ra, pa, Cur.bit(Key.at(rb, pa)))(hb)(lt)(Crit.not_above_agree(Key.diff(ra, rb), pa)(hab))(Crit.side_of(rb, pa, Cur.bit(Key.at(rb, pa)))(t2n)({==}))
    Shared.Bool.when_cases(
      Crit<V>,
      t => {Crit.lookup(V, t, q) == Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)): Maybe<&2, V>},
      Key.bit(rb, pa),
      u => Crit.mk(V, ra, pa, ea, za, Crit.union(~V, ~j, oa, Crit.Fork{rb, pb, eb, zb, ob})),
      u => Crit.mk(V, ra, pa, ea, Crit.union(~V, ~j, za, Crit.Fork{rb, pb, eb, zb, ob}), oa),
      +t3 =>
          +allt = Crit.all_place_b(~V, Crit.Fork{rb, pb, eb, zb, ob}, ra, pa, Key.bit(rb, pa), True{})(t3)(allb)
          Equal.trans(
            Maybe<&2, V>,
            Crit.lookup(V, Crit.mk(V, ra, pa, ea, za, Crit.union(~V, ~j, oa, Crit.Fork{rb, pb, eb, zb, ob})), q),
            Maybe.or(&2, V, Crit.ended(V, ra, ea, q), Maybe.or(&2, V, Crit.lookup(V, za, q), Crit.lookup(V, Crit.union(~V, ~j, oa, Crit.Fork{rb, pb, eb, zb, ob}), q))),
            Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)),
            Crit.mk_lookup(V, ra, pa, ea, za, Crit.union(~V, ~j, oa, Crit.Fork{rb, pb, eb, zb, ob}), q),
            Crit.bool_split({Maybe.or(&2, V, Crit.ended(V, ra, ea, q), Maybe.or(&2, V, Crit.lookup(V, za, q), Crit.lookup(V, Crit.union(~V, ~j, oa, Crit.Fork{rb, pb, eb, zb, ob}), q))) == Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)): Maybe<&2, V>}, Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)))(
              +ct =>
                +hsq = Place.has_side(ra, pa, True{}, q)(Crit.in_place(~V, Crit.Fork{rb, pb, eb, zb, ob}, Place{ra, pa, True{}}, q)(allt)(ct))
                Equal.trans(
                  Maybe<&2, V>,
                  Maybe.or(&2, V, Crit.ended(V, ra, ea, q), Maybe.or(&2, V, Crit.lookup(V, za, q), Crit.lookup(V, Crit.union(~V, ~j, oa, Crit.Fork{rb, pb, eb, zb, ob}), q))),
                  Crit.lookup(V, Crit.union(~V, ~j, oa, Crit.Fork{rb, pb, eb, zb, ob}), q),
                  Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)),
                  Crit.or_third(V, Crit.ended(V, ra, ea, q), Crit.lookup(V, za, q), Crit.lookup(V, Crit.union(~V, ~j, oa, Crit.Fork{rb, pb, eb, zb, ob}), q))(Crit.ended_long(V, ra, pa, ea, za, q, List.drop(&2, Bool, Key.bits(q), pa))(Crit.wf.rep_ok(~V, ra, pa, ea, za, oa, la)(ha))({==})(Crit.side_some_ne(q, pa, True{})(hsq)))(Crit.lookup_all(~V, ~Place, ~Place.has, za, Place{ra, pa, False{}}, q)(Crit.wf.all_z(~V, ra, pa, ea, za, oa, la)(ha))(Place.has_not(ra, pa, False{}, q, Some{True{}}, hsq, {==}))),
                  Equal.trans(Maybe<&2, V>, Crit.lookup(V, Crit.union(~V, ~j, oa, Crit.Fork{rb, pb, eb, zb, ob}), q), Shared.Maybe.join(~V, ~j, Crit.lookup(V, oa, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), io, Equal.cong(Maybe<&2, V>, Maybe<&2, V>, t => Shared.Maybe.join(~V, ~j, t, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), Crit.lookup(V, oa, q), Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Equal.sym(Maybe<&2, V>, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, oa, q), Crit.route_side(~V, ra, pa, ea, za, oa, la, q, True{})(ha)(hsq))))
                )
            )(
              +cf =>
                +lbn = Crit.none_of_some(V, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q))(cf)
                Equal.trans(
                  Maybe<&2, V>,
                  Maybe.or(&2, V, Crit.ended(V, ra, ea, q), Maybe.or(&2, V, Crit.lookup(V, za, q), Crit.lookup(V, Crit.union(~V, ~j, oa, Crit.Fork{rb, pb, eb, zb, ob}), q))),
                  Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q),
                  Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)),
                  Equal.cong(Maybe<&2, V>, Maybe<&2, V>, t => Maybe.or(&2, V, Crit.ended(V, ra, ea, q), Maybe.or(&2, V, Crit.lookup(V, za, q), t)), Crit.lookup(V, Crit.union(~V, ~j, oa, Crit.Fork{rb, pb, eb, zb, ob}), q), Crit.lookup(V, oa, q), Equal.trans(Maybe<&2, V>, Crit.lookup(V, Crit.union(~V, ~j, oa, Crit.Fork{rb, pb, eb, zb, ob}), q), Shared.Maybe.join(~V, ~j, Crit.lookup(V, oa, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), Crit.lookup(V, oa, q), io, Equal.trans(Maybe<&2, V>, Shared.Maybe.join(~V, ~j, Crit.lookup(V, oa, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), Shared.Maybe.join(~V, ~j, Crit.lookup(V, oa, q), None{}), Crit.lookup(V, oa, q), Equal.cong(Maybe<&2, V>, Maybe<&2, V>, t => Shared.Maybe.join(~V, ~j, Crit.lookup(V, oa, q), t), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q), None{}, lbn), Shared.Maybe.join_none(~V, ~j, Crit.lookup(V, oa, q))))),
                  Equal.sym(Maybe<&2, V>, Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Equal.trans(Maybe<&2, V>, Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), None{}), Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Equal.cong(Maybe<&2, V>, Maybe<&2, V>, t => Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), t), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q), None{}, lbn), Shared.Maybe.join_none(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q))))
                )
            )
          ),
      +t3 =>
          +allt = Crit.all_place_b(~V, Crit.Fork{rb, pb, eb, zb, ob}, ra, pa, Key.bit(rb, pa), False{})(t3)(allb)
          Equal.trans(
            Maybe<&2, V>,
            Crit.lookup(V, Crit.mk(V, ra, pa, ea, Crit.union(~V, ~j, za, Crit.Fork{rb, pb, eb, zb, ob}), oa), q),
            Maybe.or(&2, V, Crit.ended(V, ra, ea, q), Maybe.or(&2, V, Crit.lookup(V, Crit.union(~V, ~j, za, Crit.Fork{rb, pb, eb, zb, ob}), q), Crit.lookup(V, oa, q))),
            Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)),
            Crit.mk_lookup(V, ra, pa, ea, Crit.union(~V, ~j, za, Crit.Fork{rb, pb, eb, zb, ob}), oa, q),
            Crit.bool_split({Maybe.or(&2, V, Crit.ended(V, ra, ea, q), Maybe.or(&2, V, Crit.lookup(V, Crit.union(~V, ~j, za, Crit.Fork{rb, pb, eb, zb, ob}), q), Crit.lookup(V, oa, q))) == Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)): Maybe<&2, V>}, Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)))(
              +ct =>
                +hsq = Place.has_side(ra, pa, False{}, q)(Crit.in_place(~V, Crit.Fork{rb, pb, eb, zb, ob}, Place{ra, pa, False{}}, q)(allt)(ct))
                Equal.trans(
                  Maybe<&2, V>,
                  Maybe.or(&2, V, Crit.ended(V, ra, ea, q), Maybe.or(&2, V, Crit.lookup(V, Crit.union(~V, ~j, za, Crit.Fork{rb, pb, eb, zb, ob}), q), Crit.lookup(V, oa, q))),
                  Crit.lookup(V, Crit.union(~V, ~j, za, Crit.Fork{rb, pb, eb, zb, ob}), q),
                  Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)),
                  Crit.or_second(V, Crit.ended(V, ra, ea, q), Crit.lookup(V, Crit.union(~V, ~j, za, Crit.Fork{rb, pb, eb, zb, ob}), q), Crit.lookup(V, oa, q))(Crit.ended_long(V, ra, pa, ea, za, q, List.drop(&2, Bool, Key.bits(q), pa))(Crit.wf.rep_ok(~V, ra, pa, ea, za, oa, la)(ha))({==})(Crit.side_some_ne(q, pa, False{})(hsq)))(Crit.lookup_all(~V, ~Place, ~Place.has, oa, Place{ra, pa, True{}}, q)(Crit.wf.all_o(~V, ra, pa, ea, za, oa, la)(ha))(Place.has_not(ra, pa, True{}, q, Some{False{}}, hsq, {==}))),
                  Equal.trans(Maybe<&2, V>, Crit.lookup(V, Crit.union(~V, ~j, za, Crit.Fork{rb, pb, eb, zb, ob}), q), Shared.Maybe.join(~V, ~j, Crit.lookup(V, za, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), iz, Equal.cong(Maybe<&2, V>, Maybe<&2, V>, t => Shared.Maybe.join(~V, ~j, t, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), Crit.lookup(V, za, q), Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Equal.sym(Maybe<&2, V>, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, za, q), Crit.route_side(~V, ra, pa, ea, za, oa, la, q, False{})(ha)(hsq))))
                )
            )(
              +cf =>
                +lbn = Crit.none_of_some(V, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q))(cf)
                Equal.trans(
                  Maybe<&2, V>,
                  Maybe.or(&2, V, Crit.ended(V, ra, ea, q), Maybe.or(&2, V, Crit.lookup(V, Crit.union(~V, ~j, za, Crit.Fork{rb, pb, eb, zb, ob}), q), Crit.lookup(V, oa, q))),
                  Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q),
                  Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)),
                  Equal.cong(Maybe<&2, V>, Maybe<&2, V>, t => Maybe.or(&2, V, Crit.ended(V, ra, ea, q), Maybe.or(&2, V, t, Crit.lookup(V, oa, q))), Crit.lookup(V, Crit.union(~V, ~j, za, Crit.Fork{rb, pb, eb, zb, ob}), q), Crit.lookup(V, za, q), Equal.trans(Maybe<&2, V>, Crit.lookup(V, Crit.union(~V, ~j, za, Crit.Fork{rb, pb, eb, zb, ob}), q), Shared.Maybe.join(~V, ~j, Crit.lookup(V, za, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), Crit.lookup(V, za, q), iz, Equal.trans(Maybe<&2, V>, Shared.Maybe.join(~V, ~j, Crit.lookup(V, za, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), Shared.Maybe.join(~V, ~j, Crit.lookup(V, za, q), None{}), Crit.lookup(V, za, q), Equal.cong(Maybe<&2, V>, Maybe<&2, V>, t => Shared.Maybe.join(~V, ~j, Crit.lookup(V, za, q), t), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q), None{}, lbn), Shared.Maybe.join_none(~V, ~j, Crit.lookup(V, za, q))))),
                  Equal.sym(Maybe<&2, V>, Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Equal.trans(Maybe<&2, V>, Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), None{}), Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Equal.cong(Maybe<&2, V>, Maybe<&2, V>, t => Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), t), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q), None{}, lbn), Shared.Maybe.join_none(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q))))
                )
            )
          )
    )

# the union of two well formed forks whose reps agree before the bit pb of
# the second, which is before the bit pa of the first: a goes to its side of b
def Crit.union_gt(~V: Data, ~j: V -> V -> V, +ra: List<&2, U32>, +pa: Nat, +ea: Maybe<&2, V>, +za: Crit<V>, +oa: Crit<V>, +rb: List<&2, U32>, +pb: Nat, +eb: Maybe<&2, V>, +zb: Crit<V>, +ob: Crit<V>, +la: Nat, +lb: Nat, +q: List<&2, U32>) -> {Crit.wf(~V, Crit.Fork{ra, pa, ea, za, oa}, la) == True{}: Bool} -> {Crit.wf(~V, Crit.Fork{rb, pb, eb, zb, ob}, lb) == True{}: Bool} -> {Nat.is_lt(pb, pa) == True{}: Bool} -> {Crit.above(Key.diff(ra, rb), pb) == False{}: Bool} -> {
  Crit.lookup(V, Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, zb), q) == Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, zb, q)): Maybe<&2, V>
} -> {Crit.lookup(V, Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, ob), q) == Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, ob, q)): Maybe<&2, V>} -> {
  Crit.lookup(V, Shared.Bool.when(Crit<V>, Key.bit(ra, pb), u => Crit.mk(V, rb, pb, eb, zb, Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, ob)), u => Crit.mk(V, rb, pb, eb, Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, zb), ob)), q) == Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)): Maybe<&2, V>
}:
  +ha => +hb => +gt => +hab => +iz => +io =>
    +nr = Crit.len_drop(Key.bits(ra), pb)(Shared.Nat.lt_le(pb, pa, List.length(&2, Bool, Key.bits(ra)))(gt)(Crit.rep_long(~V, ra, pa, ea, za, oa, la)(ha)))
    +t2n = Equal.trans(
      Bool,
      Cur.done(Key.at(ra, pb)),
      List.is_empty(&2, Bool, List.drop(&2, Bool, Key.bits(ra), pb)),
      False{},
      Crit.done_of(Key.at(ra, pb), List.drop(&2, Bool, Key.bits(ra), pb))(Cur.skip_bits(pb, Cur.of(ra))),
      nr
    )
    +alla = Crit.fork_place(~V, ra, pa, ea, za, oa, la, rb, pb, Cur.bit(Key.at(ra, pb)))(ha)(gt)(Key.agree_sym(ra, rb, pb)(Crit.not_above_agree(Key.diff(ra, rb), pb)(hab)))(Crit.side_of(ra, pb, Cur.bit(Key.at(ra, pb)))(t2n)({==}))
    Shared.Bool.when_cases(
      Crit<V>,
      t => {Crit.lookup(V, t, q) == Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)): Maybe<&2, V>},
      Key.bit(ra, pb),
      u => Crit.mk(V, rb, pb, eb, zb, Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, ob)),
      u => Crit.mk(V, rb, pb, eb, Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, zb), ob),
      +t3 =>
          +allt = Crit.all_place_b(~V, Crit.Fork{ra, pa, ea, za, oa}, rb, pb, Key.bit(ra, pb), True{})(t3)(alla)
          Equal.trans(
            Maybe<&2, V>,
            Crit.lookup(V, Crit.mk(V, rb, pb, eb, zb, Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, ob)), q),
            Maybe.or(&2, V, Crit.ended(V, rb, eb, q), Maybe.or(&2, V, Crit.lookup(V, zb, q), Crit.lookup(V, Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, ob), q))),
            Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)),
            Crit.mk_lookup(V, rb, pb, eb, zb, Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, ob), q),
            Crit.bool_split({Maybe.or(&2, V, Crit.ended(V, rb, eb, q), Maybe.or(&2, V, Crit.lookup(V, zb, q), Crit.lookup(V, Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, ob), q))) == Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)): Maybe<&2, V>}, Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q)))(
              +ct =>
                +hsq = Place.has_side(rb, pb, True{}, q)(Crit.in_place(~V, Crit.Fork{ra, pa, ea, za, oa}, Place{rb, pb, True{}}, q)(allt)(ct))
                Equal.trans(
                  Maybe<&2, V>,
                  Maybe.or(&2, V, Crit.ended(V, rb, eb, q), Maybe.or(&2, V, Crit.lookup(V, zb, q), Crit.lookup(V, Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, ob), q))),
                  Crit.lookup(V, Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, ob), q),
                  Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)),
                  Crit.or_third(V, Crit.ended(V, rb, eb, q), Crit.lookup(V, zb, q), Crit.lookup(V, Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, ob), q))(Crit.ended_long(V, rb, pb, eb, zb, q, List.drop(&2, Bool, Key.bits(q), pb))(Crit.wf.rep_ok(~V, rb, pb, eb, zb, ob, lb)(hb))({==})(Crit.side_some_ne(q, pb, True{})(hsq)))(Crit.lookup_all(~V, ~Place, ~Place.has, zb, Place{rb, pb, False{}}, q)(Crit.wf.all_z(~V, rb, pb, eb, zb, ob, lb)(hb))(Place.has_not(rb, pb, False{}, q, Some{True{}}, hsq, {==}))),
                  Equal.trans(Maybe<&2, V>, Crit.lookup(V, Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, ob), q), Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, ob, q)), Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), io, Equal.cong(Maybe<&2, V>, Maybe<&2, V>, t => Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), t), Crit.lookup(V, ob, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q), Equal.sym(Maybe<&2, V>, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q), Crit.lookup(V, ob, q), Crit.route_side(~V, rb, pb, eb, zb, ob, lb, q, True{})(hb)(hsq))))
                )
            )(
              +cf =>
                +lan = Crit.none_of_some(V, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q))(cf)
                Equal.trans(
                  Maybe<&2, V>,
                  Maybe.or(&2, V, Crit.ended(V, rb, eb, q), Maybe.or(&2, V, Crit.lookup(V, zb, q), Crit.lookup(V, Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, ob), q))),
                  Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q),
                  Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)),
                  Equal.cong(Maybe<&2, V>, Maybe<&2, V>, t => Maybe.or(&2, V, Crit.ended(V, rb, eb, q), Maybe.or(&2, V, Crit.lookup(V, zb, q), t)), Crit.lookup(V, Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, ob), q), Crit.lookup(V, ob, q), Equal.trans(Maybe<&2, V>, Crit.lookup(V, Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, ob), q), Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, ob, q)), Crit.lookup(V, ob, q), io, Equal.trans(Maybe<&2, V>, Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, ob, q)), Shared.Maybe.join(~V, ~j, None{}, Crit.lookup(V, ob, q)), Crit.lookup(V, ob, q), Equal.cong(Maybe<&2, V>, Maybe<&2, V>, t => Shared.Maybe.join(~V, ~j, t, Crit.lookup(V, ob, q)), Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), None{}, lan), Crit.join_none_l(~V, ~j, Crit.lookup(V, ob, q))))),
                  Equal.sym(Maybe<&2, V>, Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q), Equal.trans(Maybe<&2, V>, Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), Shared.Maybe.join(~V, ~j, None{}, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q), Equal.cong(Maybe<&2, V>, Maybe<&2, V>, t => Shared.Maybe.join(~V, ~j, t, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), None{}, lan), Crit.join_none_l(~V, ~j, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q))))
                )
            )
          ),
      +t3 =>
          +allt = Crit.all_place_b(~V, Crit.Fork{ra, pa, ea, za, oa}, rb, pb, Key.bit(ra, pb), False{})(t3)(alla)
          Equal.trans(
            Maybe<&2, V>,
            Crit.lookup(V, Crit.mk(V, rb, pb, eb, Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, zb), ob), q),
            Maybe.or(&2, V, Crit.ended(V, rb, eb, q), Maybe.or(&2, V, Crit.lookup(V, Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, zb), q), Crit.lookup(V, ob, q))),
            Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)),
            Crit.mk_lookup(V, rb, pb, eb, Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, zb), ob, q),
            Crit.bool_split({Maybe.or(&2, V, Crit.ended(V, rb, eb, q), Maybe.or(&2, V, Crit.lookup(V, Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, zb), q), Crit.lookup(V, ob, q))) == Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)): Maybe<&2, V>}, Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q)))(
              +ct =>
                +hsq = Place.has_side(rb, pb, False{}, q)(Crit.in_place(~V, Crit.Fork{ra, pa, ea, za, oa}, Place{rb, pb, False{}}, q)(allt)(ct))
                Equal.trans(
                  Maybe<&2, V>,
                  Maybe.or(&2, V, Crit.ended(V, rb, eb, q), Maybe.or(&2, V, Crit.lookup(V, Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, zb), q), Crit.lookup(V, ob, q))),
                  Crit.lookup(V, Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, zb), q),
                  Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)),
                  Crit.or_second(V, Crit.ended(V, rb, eb, q), Crit.lookup(V, Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, zb), q), Crit.lookup(V, ob, q))(Crit.ended_long(V, rb, pb, eb, zb, q, List.drop(&2, Bool, Key.bits(q), pb))(Crit.wf.rep_ok(~V, rb, pb, eb, zb, ob, lb)(hb))({==})(Crit.side_some_ne(q, pb, False{})(hsq)))(Crit.lookup_all(~V, ~Place, ~Place.has, ob, Place{rb, pb, True{}}, q)(Crit.wf.all_o(~V, rb, pb, eb, zb, ob, lb)(hb))(Place.has_not(rb, pb, True{}, q, Some{False{}}, hsq, {==}))),
                  Equal.trans(Maybe<&2, V>, Crit.lookup(V, Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, zb), q), Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, zb, q)), Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), iz, Equal.cong(Maybe<&2, V>, Maybe<&2, V>, t => Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), t), Crit.lookup(V, zb, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q), Equal.sym(Maybe<&2, V>, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q), Crit.lookup(V, zb, q), Crit.route_side(~V, rb, pb, eb, zb, ob, lb, q, False{})(hb)(hsq))))
                )
            )(
              +cf =>
                +lan = Crit.none_of_some(V, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q))(cf)
                Equal.trans(
                  Maybe<&2, V>,
                  Maybe.or(&2, V, Crit.ended(V, rb, eb, q), Maybe.or(&2, V, Crit.lookup(V, Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, zb), q), Crit.lookup(V, ob, q))),
                  Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q),
                  Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)),
                  Equal.cong(Maybe<&2, V>, Maybe<&2, V>, t => Maybe.or(&2, V, Crit.ended(V, rb, eb, q), Maybe.or(&2, V, t, Crit.lookup(V, ob, q))), Crit.lookup(V, Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, zb), q), Crit.lookup(V, zb, q), Equal.trans(Maybe<&2, V>, Crit.lookup(V, Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, zb), q), Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, zb, q)), Crit.lookup(V, zb, q), iz, Equal.trans(Maybe<&2, V>, Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, zb, q)), Shared.Maybe.join(~V, ~j, None{}, Crit.lookup(V, zb, q)), Crit.lookup(V, zb, q), Equal.cong(Maybe<&2, V>, Maybe<&2, V>, t => Shared.Maybe.join(~V, ~j, t, Crit.lookup(V, zb, q)), Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), None{}, lan), Crit.join_none_l(~V, ~j, Crit.lookup(V, zb, q))))),
                  Equal.sym(Maybe<&2, V>, Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q), Equal.trans(Maybe<&2, V>, Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), Shared.Maybe.join(~V, ~j, None{}, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q), Equal.cong(Maybe<&2, V>, Maybe<&2, V>, t => Shared.Maybe.join(~V, ~j, t, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), None{}, lan), Crit.join_none_l(~V, ~j, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q))))
                )
            )
          )
    )

# the union of two well formed forks whose reps do not differ before both
# bits, by how the bits compare (c)
def Crit.union_at_lookup(~V: Data, ~j: V -> V -> V, +ra: List<&2, U32>, +pa: Nat, +ea: Maybe<&2, V>, +za: Crit<V>, +oa: Crit<V>, +rb: List<&2, U32>, +pb: Nat, +eb: Maybe<&2, V>, +zb: Crit<V>, +ob: Crit<V>, +la: Nat, +lb: Nat, +q: List<&2, U32>, c: Cmp) -> {Nat.cmp(pa, pb) == c: Cmp} -> {Crit.wf(~V, Crit.Fork{ra, pa, ea, za, oa}, la) == True{}: Bool} -> {Crit.wf(~V, Crit.Fork{rb, pb, eb, zb, ob}, lb) == True{}: Bool} -> {Bool.and(Crit.above(Key.diff(ra, rb), pa), Crit.above(Key.diff(ra, rb), pb)) == False{}: Bool} -> {Crit.lookup(V, Crit.union(~V, ~j, za, zb), q) == Shared.Maybe.join(~V, ~j, Crit.lookup(V, za, q), Crit.lookup(V, zb, q)): Maybe<&2, V>} -> {Crit.lookup(V, Crit.union(~V, ~j, oa, ob), q) == Shared.Maybe.join(~V, ~j, Crit.lookup(V, oa, q), Crit.lookup(V, ob, q)): Maybe<&2, V>} -> {Crit.lookup(V, Crit.union(~V, ~j, za, Crit.Fork{rb, pb, eb, zb, ob}), q) == Shared.Maybe.join(~V, ~j, Crit.lookup(V, za, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)): Maybe<&2, V>} -> {Crit.lookup(V, Crit.union(~V, ~j, oa, Crit.Fork{rb, pb, eb, zb, ob}), q) == Shared.Maybe.join(~V, ~j, Crit.lookup(V, oa, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)): Maybe<&2, V>} -> {Crit.lookup(V, Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, zb), q) == Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, zb, q)): Maybe<&2, V>} -> {Crit.lookup(V, Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, ob), q) == Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, ob, q)): Maybe<&2, V>} -> {
  Crit.lookup(V, Crit.union.at(~V, ~j, c, ra, pa, ea, rb, pb, eb, zs => os => Crit.mk(V, Bool.pick(List<&2, U32>, Maybe.is_some(&2, V, ea), ra, rb), pa, Shared.Maybe.join(~V, ~j, ea, eb), zs, os), u2 => Crit.union(~V, ~j, za, zb), u2 => Crit.union(~V, ~j, oa, ob), u2 => Crit.union(~V, ~j, za, Crit.Fork{rb, pb, eb, zb, ob}), u2 => Crit.union(~V, ~j, oa, Crit.Fork{rb, pb, eb, zb, ob}), u2 => Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, zb), u2 => Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, ob), za, oa, zb, ob), q) == Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)): Maybe<&2, V>
}:
  match c:
    case EQ{}:
      hc => ha => hb => +hn => i1 => i2 => i3 => i4 => i5 => i6 =>
        +eqp = Crit.cmp_eq(pa, pb)(hc)
        Crit.union_eq(~V, ~j, ra, pa, ea, za, oa, rb, pb, eb, zb, ob, la, lb, q)(ha)(hb)(eqp)(
          Crit.above_eq(Key.diff(ra, rb), pa)(Equal.trans(Bool, Bool.and(Crit.above(Key.diff(ra, rb), pa), Crit.above(Key.diff(ra, rb), pa)), Bool.and(Crit.above(Key.diff(ra, rb), pa), Crit.above(Key.diff(ra, rb), pb)), False{}, Equal.cong(Nat, Bool, t => Bool.and(Crit.above(Key.diff(ra, rb), pa), Crit.above(Key.diff(ra, rb), t)), pa, pb, eqp), hn))
        )(i1)(i2)
    case LT{}:
      +hc => ha => hb => hn => i1 => i2 => i3 => i4 => i5 => i6 => Crit.union_lt(~V, ~j, ra, pa, ea, za, oa, rb, pb, eb, zb, ob, la, lb, q)(ha)(hb)(Crit.cmp_lt(pa, pb)(hc))(
        Crit.above_lt_left(Key.diff(ra, rb), pa, pb)(hn)(Crit.cmp_lt(pa, pb)(hc))
      )(i3)(i4)
    case GT{}:
      +hc => ha => hb => hn => i1 => i2 => i3 => i4 => i5 => i6 => Crit.union_gt(~V, ~j, ra, pa, ea, za, oa, rb, pb, eb, zb, ob, la, lb, q)(ha)(hb)(Crit.cmp_gt(pa, pb)(hc))(
        Crit.above_lt_right(Key.diff(ra, rb), pa, pb)(hn)(Crit.cmp_gt(pa, pb)(hc))
      )(i5)(i6)

# the union of two well formed maps holds what either holds, and j of both
# where both hold a key
def Crit.union_go_lookup(~V: Data, ~j: V -> V -> V, +a: Crit<V>, +b: Crit<V>, +la: Nat, +lb: Nat, +q: List<&2, U32>) -> {Crit.wf(~V, a, la) == True{}: Bool} -> {
  Crit.wf(~V, b, lb) == True{}: Bool
} -> {Crit.lookup(V, Crit.union(~V, ~j, a, b), q) == Shared.Maybe.join(~V, ~j, Crit.lookup(V, a, q), Crit.lookup(V, b, q)): Maybe<&2, V>}:
  match a b:
    case Crit.Tip{} Crit.Tip{}:
      ha => hb => {==}
    case Crit.Tip{} Crit.Leaf{+k2, +w2}:
      ha => hb => Equal.sym(Maybe<&2, V>, Shared.Maybe.join(~V, ~j, None{}, Crit.lookup(V, Crit.Leaf{k2, w2}, q)), Crit.lookup(V, Crit.Leaf{k2, w2}, q), Crit.join_none_l(~V, ~j, Crit.lookup(V, Crit.Leaf{k2, w2}, q)))
    case Crit.Tip{} Crit.Fork{+r2, +p2, +e2, +z2, +o2}:
      ha => hb => Equal.sym(Maybe<&2, V>, Shared.Maybe.join(~V, ~j, None{}, Crit.lookup(V, Crit.Fork{r2, p2, e2, z2, o2}, q)), Crit.lookup(V, Crit.Fork{r2, p2, e2, z2, o2}, q), Crit.join_none_l(~V, ~j, Crit.lookup(V, Crit.Fork{r2, p2, e2, z2, o2}, q)))
    case Crit.Leaf{+k, +v} Crit.Tip{}:
      ha => hb => Equal.sym(Maybe<&2, V>, Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Leaf{k, v}, q), None{}), Crit.lookup(V, Crit.Leaf{k, v}, q), Shared.Maybe.join_none(~V, ~j, Crit.lookup(V, Crit.Leaf{k, v}, q)))
    case Crit.Fork{+ra, +pa, +ea, +za, +oa} Crit.Tip{}:
      ha => hb => Equal.sym(Maybe<&2, V>, Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), None{}), Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Shared.Maybe.join_none(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q)))
    case Crit.Leaf{+k, +v} Crit.Leaf{+k2, +w}:
      ha => hb => Crit.union_leaf_l(~V, ~j, k, v, Crit.Leaf{k2, w}, lb, q)(hb)
    case Crit.Leaf{+k, +v} Crit.Fork{+rb, +pb, +eb, +zb, +ob}:
      ha => hb => Crit.union_leaf_l(~V, ~j, k, v, Crit.Fork{rb, pb, eb, zb, ob}, lb, q)(hb)
    case Crit.Fork{+ra, +pa, +ea, +za, +oa} Crit.Leaf{+k, +w}:
      ha => hb => Crit.union_leaf_r(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, la, k, w, q)(ha)
    case Crit.Fork{+ra, +pa, +ea, +za, +oa} Crit.Fork{+rb, +pb, +eb, +zb, +ob}:
      +ha => +hb => Shared.Bool.when_cases(
        Crit<V>,
        t => {Crit.lookup(V, t, q) == Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)): Maybe<&2, V>},
        Bool.and(Crit.above(Key.diff(ra, rb), pa), Crit.above(Key.diff(ra, rb), pb)),
        u => Crit.join(V, Crit.Fork{ra, pa, ea, za, oa}, Crit.Fork{rb, pb, eb, zb, ob}, Maybe.default(&2, Nat, Key.diff(ra, rb), 0n)),
        u => Crit.union.at(~V, ~j, Nat.cmp(pa, pb), ra, pa, ea, rb, pb, eb, zs => os => Crit.mk(V, Bool.pick(List<&2, U32>, Maybe.is_some(&2, V, ea), ra, rb), pa, Shared.Maybe.join(~V, ~j, ea, eb), zs, os), u2 => Crit.union(~V, ~j, za, zb), u2 => Crit.union(~V, ~j, oa, ob), u2 => Crit.union(~V, ~j, za, Crit.Fork{rb, pb, eb, zb, ob}), u2 => Crit.union(~V, ~j, oa, Crit.Fork{rb, pb, eb, zb, ob}), u2 => Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, zb), u2 => Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, ob), za, oa, zb, ob),
        +t => Equal.trans(
          Maybe<&2, V>,
          Crit.lookup(V, Crit.join(V, Crit.Fork{ra, pa, ea, za, oa}, Crit.Fork{rb, pb, eb, zb, ob}, Maybe.default(&2, Nat, Key.diff(ra, rb), 0n)), q),
          Maybe.or(&2, V, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)),
          Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)),
          Crit.join_lookup(V, Crit.Fork{ra, pa, ea, za, oa}, Crit.Fork{rb, pb, eb, zb, ob}, Maybe.default(&2, Nat, Key.diff(ra, rb), 0n), q)(Crit.forks_disj(~V, ra, pa, ea, za, oa, rb, pb, eb, zb, ob, la, lb, q)(ha)(hb)(t)),
          Crit.or_join(~V, ~j, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q))(Crit.forks_disj(~V, ra, pa, ea, za, oa, rb, pb, eb, zb, ob, la, lb, q)(ha)(hb)(t))
        ),
        +t => Crit.union_at_lookup(~V, ~j, ra, pa, ea, za, oa, rb, pb, eb, zb, ob, la, lb, q, Nat.cmp(pa, pb))({==})(ha)(hb)(t)(
          Crit.union_go_lookup(~V, ~j, za, zb, 1n+pa, 1n+pb, q)(Crit.wf.wf_z(~V, ra, pa, ea, za, oa, la)(ha))(Crit.wf.wf_z(~V, rb, pb, eb, zb, ob, lb)(hb))
        )(Crit.union_go_lookup(~V, ~j, oa, ob, 1n+pa, 1n+pb, q)(Crit.wf.wf_o(~V, ra, pa, ea, za, oa, la)(ha))(Crit.wf.wf_o(~V, rb, pb, eb, zb, ob, lb)(hb)))(
          Crit.union_go_lookup(~V, ~j, za, b, 1n+pa, lb, q)(Crit.wf.wf_z(~V, ra, pa, ea, za, oa, la)(ha))(hb)
        )(Crit.union_go_lookup(~V, ~j, oa, b, 1n+pa, lb, q)(Crit.wf.wf_o(~V, ra, pa, ea, za, oa, la)(ha))(hb))(
          Crit.union_go_lookup(~V, ~j, a, zb, la, 1n+pb, q)(ha)(Crit.wf.wf_z(~V, rb, pb, eb, zb, ob, lb)(hb))
        )(Crit.union_go_lookup(~V, ~j, a, ob, la, 1n+pb, q)(ha)(Crit.wf.wf_o(~V, rb, pb, eb, zb, ob, lb)(hb)))
      )

# a union holds what either holds, and j of both where both hold a key
law Crit.union_lookup:
  for ~V: Data
  for ~j: V -> V -> V
  for a: Crit<V>
  for b: Crit<V>
  for q: List<&2, U32>
  {Crit.wf(~V, a, 0n) == True{}: Bool} -> {Crit.wf(~V, b, 0n) == True{}: Bool} -> {
    Crit.lookup(V, Crit.union(~V, ~j, a, b), q) == Shared.Maybe.join(~V, ~j, Crit.lookup(V, a, q), Crit.lookup(V, b, q)): Maybe<&2, V>
  }

def Crit.union_lookup(ty, j, a, b, q):
  ha => hb => Crit.union_go_lookup(~ty, ~j, a, b, 0n, 0n, q)(ha)(hb)

# Crit.find_lookup at a fork, once the bits of k from pos are d
def Crit.find_lookup.fork(
  ~V: Data,
  +rep: List<&2, U32>,
  +pos: Nat,
  +e: Maybe<&2, V>,
  +z: Crit<V>,
  +o: Crit<V>,
  +k: List<&2, U32>,
  d: List<&2, Bool>
) -> {List.drop(&2, Bool, Key.bits(k), pos) == d: List<&2, Bool>} -> {Crit.rep_ok(V, rep, pos, e, z) == True{}: Bool} -> {
  Crit.all(~V, ~Place, ~Place.has, z, Place{rep, pos, False{}}) == True{}: Bool
} -> {Crit.all(~V, ~Place, ~Place.has, o, Place{rep, pos, True{}}) == True{}: Bool} -> {
  Crit.find(V, z, 1n+pos, List.drop(&2, Bool, d, 1n), k) == Crit.lookup(V, z, k): Maybe<&2, V>
} -> {Crit.find(V, o, 1n+pos, List.drop(&2, Bool, d, 1n), k) == Crit.lookup(V, o, k): Maybe<&2, V>} -> {
  Shared.Bool.when(
    Maybe<&2, V>,
    List.is_empty(&2, Bool, d),
    u => Crit.ended(V, rep, e, k),
    u => Shared.Bool.when(
      Maybe<&2, V>,
      Shared.List.head_or(Bool, d, False{}),
      u => Crit.find(V, o, 1n+pos, List.drop(&2, Bool, d, 1n), k),
      u => Crit.find(V, z, 1n+pos, List.drop(&2, Bool, d, 1n), k)
    )
  )
    == Maybe.or(&2, V, Crit.ended(V, rep, e, k), Maybe.or(&2, V, Crit.lookup(V, z, k), Crit.lookup(V, o, k))): Maybe<&2, V>
}:
  match d:
    case Nil{}:
      +hd => hr => az => ao => iz => io => Equal.sym(
        Maybe<&2, V>,
        Maybe.or(&2, V, Crit.ended(V, rep, e, k), Maybe.or(&2, V, Crit.lookup(V, z, k), Crit.lookup(V, o, k))),
        Crit.ended(V, rep, e, k),
        Crit.or_first(V, Crit.ended(V, rep, e, k), Crit.lookup(V, z, k), Crit.lookup(V, o, k))(
          Crit.lookup_all(~V, ~Place, ~Place.has, z, Place{rep, pos, False{}}, k)(az)(
            Place.has_not(rep, pos, False{}, k, None{}, Crit.side_drop(k, pos, [])(hd), {==})
          )
        )(
          Crit.lookup_all(~V, ~Place, ~Place.has, o, Place{rep, pos, True{}}, k)(ao)(
            Place.has_not(rep, pos, True{}, k, None{}, Crit.side_drop(k, pos, [])(hd), {==})
          )
        )
      )
    case Con{True{}, +r}:
      +hd => hr => az => ao => iz => io => Equal.trans(
        Maybe<&2, V>,
        Crit.find(V, o, 1n+pos, List.drop(&2, Bool, True{} <> r, 1n), k),
        Crit.lookup(V, o, k),
        Maybe.or(&2, V, Crit.ended(V, rep, e, k), Maybe.or(&2, V, Crit.lookup(V, z, k), Crit.lookup(V, o, k))),
        io,
        Equal.sym(
          Maybe<&2, V>,
          Maybe.or(&2, V, Crit.ended(V, rep, e, k), Maybe.or(&2, V, Crit.lookup(V, z, k), Crit.lookup(V, o, k))),
          Crit.lookup(V, o, k),
          Crit.or_third(V, Crit.ended(V, rep, e, k), Crit.lookup(V, z, k), Crit.lookup(V, o, k))(
            Crit.ended_past(V, rep, pos, e, z, k, True{}, r)(hr)(hd)
          )(
            Crit.lookup_all(~V, ~Place, ~Place.has, z, Place{rep, pos, False{}}, k)(az)(
              Place.has_not(rep, pos, False{}, k, Some{True{}}, Crit.side_drop(k, pos, True{} <> r)(hd), {==})
            )
          )
        )
      )
    case Con{False{}, +r}:
      +hd => hr => az => ao => iz => io => Equal.trans(
        Maybe<&2, V>,
        Crit.find(V, z, 1n+pos, List.drop(&2, Bool, False{} <> r, 1n), k),
        Crit.lookup(V, z, k),
        Maybe.or(&2, V, Crit.ended(V, rep, e, k), Maybe.or(&2, V, Crit.lookup(V, z, k), Crit.lookup(V, o, k))),
        iz,
        Equal.sym(
          Maybe<&2, V>,
          Maybe.or(&2, V, Crit.ended(V, rep, e, k), Maybe.or(&2, V, Crit.lookup(V, z, k), Crit.lookup(V, o, k))),
          Crit.lookup(V, z, k),
          Crit.or_second(V, Crit.ended(V, rep, e, k), Crit.lookup(V, z, k), Crit.lookup(V, o, k))(
            Crit.ended_past(V, rep, pos, e, z, k, False{}, r)(hr)(hd)
          )(
            Crit.lookup_all(~V, ~Place, ~Place.has, o, Place{rep, pos, True{}}, k)(ao)(
              Place.has_not(rep, pos, True{}, k, Some{False{}}, Crit.side_drop(k, pos, False{} <> r)(hd), {==})
            )
          )
        )
      )

# the clear read of the bits of k from the bit at, in a well formed map
# below a fork at a bit before at, is the read through every entry
def Crit.find_lookup(~V: Data, m: Crit<V>, +lo: Nat, +at: Nat, +k: List<&2, U32>) -> {Crit.wf(~V, m, lo) == True{}: Bool} -> {
  Nat.is_le(at, lo) == True{}: Bool
} -> {Crit.find(V, m, at, List.drop(&2, Bool, Key.bits(k), at), k) == Crit.lookup(V, m, k): Maybe<&2, V>}:
  match m:
    case Crit.Tip{}:
      h => l => {==}
    case Crit.Leaf{k2, v}:
      h => l => {==}
    case Crit.Fork{+rep, +pos, +e, +z, +o}:
      +h => +l =>
        %Equal.sym(
          List<&2, Bool>,
          List.drop(&2, Bool, List.drop(&2, Bool, Key.bits(k), at), Nat.sub(pos, at)),
          List.drop(&2, Bool, Key.bits(k), pos),
          Crit.drop_drop(Key.bits(k), at, pos)(Shared.Nat.le_trans(at, lo, pos)(l)(Crit.wf.le(~V, rep, pos, e, z, o, lo)(h)))
        ): {
          Shared.Bool.when(
            Maybe<&2, V>,
            List.is_empty(&2, Bool, _),
            u => Crit.ended(V, rep, e, k),
            u => Shared.Bool.when(
              Maybe<&2, V>,
              Shared.List.head_or(Bool, _, False{}),
              u => Crit.find(V, o, 1n+pos, List.drop(&2, Bool, _, 1n), k),
              u => Crit.find(V, z, 1n+pos, List.drop(&2, Bool, _, 1n), k)
            )
          )
            == Maybe.or(&2, V, Crit.ended(V, rep, e, k), Maybe.or(&2, V, Crit.lookup(V, z, k), Crit.lookup(V, o, k))): Maybe<&2, V>
        }
        Crit.find_lookup.fork(~V, rep, pos, e, z, o, k, List.drop(&2, Bool, Key.bits(k), pos))({==})(
          Crit.wf.rep_ok(~V, rep, pos, e, z, o, lo)(h)
        )(Crit.wf.all_z(~V, rep, pos, e, z, o, lo)(h))(Crit.wf.all_o(~V, rep, pos, e, z, o, lo)(h))((
          %Equal.sym(
            List<&2, Bool>,
            List.drop(&2, Bool, List.drop(&2, Bool, Key.bits(k), pos), 1n),
            List.drop(&2, Bool, Key.bits(k), 1n+pos),
            Crit.drop_drop_one(Key.bits(k), pos)
          ): {Crit.find(V, z, 1n+pos, _, k) == Crit.lookup(V, z, k): Maybe<&2, V>}
          Crit.find_lookup(~V, z, 1n+pos, 1n+pos, k)(Crit.wf.wf_z(~V, rep, pos, e, z, o, lo)(h))(Shared.Nat.le_refl(1n+pos))
        ))((
          %Equal.sym(
            List<&2, Bool>,
            List.drop(&2, Bool, List.drop(&2, Bool, Key.bits(k), pos), 1n),
            List.drop(&2, Bool, Key.bits(k), 1n+pos),
            Crit.drop_drop_one(Key.bits(k), pos)
          ): {Crit.find(V, o, 1n+pos, _, k) == Crit.lookup(V, o, k): Maybe<&2, V>}
          Crit.find_lookup(~V, o, 1n+pos, 1n+pos, k)(Crit.wf.wf_o(~V, rep, pos, e, z, o, lo)(h))(Shared.Nat.le_refl(1n+pos))
        ))

# a read of a map well formed below any bit is its clear read
def Crit.get_lookup.lo(~V: Data, +m: Crit<V>, +lo: Nat, +k: List<&2, U32>) -> {Crit.wf(~V, m, lo) == True{}: Bool} -> {
  Crit.get(V, m, k) == Crit.lookup(V, m, k): Maybe<&2, V>
}:
  h => Equal.trans(
    Maybe<&2, V>,
    Crit.get(V, m, k),
    Crit.find(V, m, 0n, Key.bits(k), k),
    Crit.lookup(V, m, k),
    Crit.get_is_find(V, m, k),
    (
      %Shared.List.drop_zero(&2, Bool, Key.bits(k)): {Crit.find(V, m, 0n, _, k) == Crit.lookup(V, m, k): Maybe<&2, V>}
      Crit.find_lookup(~V, m, lo, 0n, k)(h)(Shared.Nat.le_zero(lo))
    )
  )

# an end that is the first unless the second is some passes a test when the
# first does
def Crit.or_pick_none(-V: Data, eb: Maybe<&2, V>, ea: Maybe<&2, V>, -x: Bool) -> {Bool.or(Maybe.is_none(&2, V, ea), x) == True{}: Bool} -> {
  Bool.or(Maybe.is_none(&2, V, Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, eb), None{}, ea)), x) == True{}: Bool
}:
  match eb:
    case None{}:
      h => h
    case Some{w}:
      h => {==}

# the difference of two forks whose reps do not differ before both bits
# passes p when a does, by how the bits compare (c)
def Crit.minus_at_all(~V: Data, ~G: Data, ~p: G -> List<&2, U32> -> Bool, +ra: List<&2, U32>, +pa: Nat, +ea: Maybe<&2, V>, +za: Crit<V>, +oa: Crit<V>, +rb: List<&2, U32>, +pb: Nat, +eb: Maybe<&2, V>, +zb: Crit<V>, +ob: Crit<V>, +g: G, c: Cmp) -> {Crit.all(~V, ~G, ~p, Crit.Fork{ra, pa, ea, za, oa}, g) == True{}: Bool} -> {Crit.all(~V, ~G, ~p, Crit.minus(V, za, zb), g) == True{}: Bool} -> {Crit.all(~V, ~G, ~p, Crit.minus(V, oa, ob), g) == True{}: Bool} -> {Crit.all(~V, ~G, ~p, Crit.minus(V, za, Crit.Fork{rb, pb, eb, zb, ob}), g) == True{}: Bool} -> {Crit.all(~V, ~G, ~p, Crit.minus(V, oa, Crit.Fork{rb, pb, eb, zb, ob}), g) == True{}: Bool} -> {Crit.all(~V, ~G, ~p, Crit.minus(V, Crit.Fork{ra, pa, ea, za, oa}, zb), g) == True{}: Bool} -> {Crit.all(~V, ~G, ~p, Crit.minus(V, Crit.Fork{ra, pa, ea, za, oa}, ob), g) == True{}: Bool} -> {Crit.all(~V, ~G, ~p, Crit.minus.at(V, c, ra, pa, ea, rb, pb, eb, u2 => Crit.minus(V, za, zb), u2 => Crit.minus(V, oa, ob), u2 => Crit.minus(V, za, Crit.Fork{rb, pb, eb, zb, ob}), u2 => Crit.minus(V, oa, Crit.Fork{rb, pb, eb, zb, ob}), u2 => Crit.minus(V, Crit.Fork{ra, pa, ea, za, oa}, zb), u2 => Crit.minus(V, Crit.Fork{ra, pa, ea, za, oa}, ob), za, oa), g) == True{}: Bool}:
  match c:
    case EQ{}:
      +h => i1 => i2 => i3 => i4 => i5 => i6 => Crit.mk_all(~V, ~G, ~p, ra, pa, Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, eb), None{}, ea), Crit.minus(V, za, zb), Crit.minus(V, oa, ob), g)(
        Crit.or_pick_none(V, eb, ea, p(g)(ra))(Crit.all.hit(~V, ~G, ~p, ra, pa, ea, za, oa, g)(h))
      )(i1)(i2)
    case LT{}:
      +h => i1 => i2 => i3 => i4 => i5 => i6 => Shared.Bool.when_cases(
        Crit<V>,
        t => {Crit.all(~V, ~G, ~p, t, g) == True{}: Bool},
        Key.bit(rb, pa),
        u => Crit.mk(V, ra, pa, ea, za, Crit.minus(V, oa, Crit.Fork{rb, pb, eb, zb, ob})),
        u => Crit.mk(V, ra, pa, ea, Crit.minus(V, za, Crit.Fork{rb, pb, eb, zb, ob}), oa),
        t3 => Crit.mk_all(~V, ~G, ~p, ra, pa, ea, za, Crit.minus(V, oa, Crit.Fork{rb, pb, eb, zb, ob}), g)(Crit.all.hit(~V, ~G, ~p, ra, pa, ea, za, oa, g)(h))(Crit.all.z(~V, ~G, ~p, ra, pa, ea, za, oa, g)(h))(i4),
        t3 => Crit.mk_all(~V, ~G, ~p, ra, pa, ea, Crit.minus(V, za, Crit.Fork{rb, pb, eb, zb, ob}), oa, g)(Crit.all.hit(~V, ~G, ~p, ra, pa, ea, za, oa, g)(h))(i3)(Crit.all.o(~V, ~G, ~p, ra, pa, ea, za, oa, g)(h))
      )
    case GT{}:
      h => i1 => i2 => i3 => i4 => i5 => i6 => Shared.Bool.when_cases(
        Crit<V>,
        t => {Crit.all(~V, ~G, ~p, t, g) == True{}: Bool},
        Key.bit(ra, pb),
        u => Crit.minus(V, Crit.Fork{ra, pa, ea, za, oa}, ob),
        u => Crit.minus(V, Crit.Fork{ra, pa, ea, za, oa}, zb),
        t3 => i6,
        t3 => i5
      )

# the difference of two maps holds only keys of the first
def Crit.minus_all(~V: Data, ~G: Data, ~p: G -> List<&2, U32> -> Bool, +a: Crit<V>, +b: Crit<V>, +g: G) -> {Crit.all(~V, ~G, ~p, a, g) == True{}: Bool} -> {
  Crit.all(~V, ~G, ~p, Crit.minus(V, a, b), g) == True{}: Bool
}:
  match a b:
    case Crit.Tip{} Crit.Tip{}:
      h => {==}
    case Crit.Tip{} Crit.Leaf{k2, w2}:
      h => {==}
    case Crit.Tip{} Crit.Fork{r2, p2, e2, z2, o2}:
      h => {==}
    case Crit.Leaf{k, v} Crit.Tip{}:
      h => h
    case Crit.Fork{ra, pa, ea, za, oa} Crit.Tip{}:
      h => h
    case Crit.Leaf{+k, +v} Crit.Leaf{+k2, +w}:
      h => Shared.Bool.when_cases(Crit<V>, t => {Crit.all(~V, ~G, ~p, t, g) == True{}: Bool}, Crit.has(V, Crit.Leaf{k2, w}, k), u => Crit.Tip{}, u => Crit.Leaf{k, v}, t1 => {==}, t1 => h)
    case Crit.Leaf{+k, +v} Crit.Fork{+rb, +pb, +eb, +zb, +ob}:
      h => Shared.Bool.when_cases(Crit<V>, t => {Crit.all(~V, ~G, ~p, t, g) == True{}: Bool}, Crit.has(V, Crit.Fork{rb, pb, eb, zb, ob}, k), u => Crit.Tip{}, u => Crit.Leaf{k, v}, t1 => {==}, t1 => h)
    case Crit.Fork{+ra, +pa, +ea, +za, +oa} Crit.Leaf{+k, +w}:
      h => Crit.drop_all(~V, ~G, ~p, Crit.Fork{ra, pa, ea, za, oa}, 0n, Cur.of(k), k, g)(h)
    case Crit.Fork{+ra, +pa, +ea, +za, +oa} Crit.Fork{+rb, +pb, +eb, +zb, +ob}:
      +h => Shared.Bool.when_cases(
        Crit<V>,
        t => {Crit.all(~V, ~G, ~p, t, g) == True{}: Bool},
        Bool.and(Crit.above(Key.diff(ra, rb), pa), Crit.above(Key.diff(ra, rb), pb)),
        u => Crit.Fork{ra, pa, ea, za, oa},
        u => Crit.minus.at(V, Nat.cmp(pa, pb), ra, pa, ea, rb, pb, eb, u2 => Crit.minus(V, za, zb), u2 => Crit.minus(V, oa, ob), u2 => Crit.minus(V, za, Crit.Fork{rb, pb, eb, zb, ob}), u2 => Crit.minus(V, oa, Crit.Fork{rb, pb, eb, zb, ob}), u2 => Crit.minus(V, Crit.Fork{ra, pa, ea, za, oa}, zb), u2 => Crit.minus(V, Crit.Fork{ra, pa, ea, za, oa}, ob), za, oa),
        t => h,
        t => Crit.minus_at_all(~V, ~G, ~p, ra, pa, ea, za, oa, rb, pb, eb, zb, ob, g, Nat.cmp(pa, pb))(h)(Crit.minus_all(~V, ~G, ~p, za, zb, g)(Crit.all.z(~V, ~G, ~p, ra, pa, ea, za, oa, g)(h)))(
          Crit.minus_all(~V, ~G, ~p, oa, ob, g)(Crit.all.o(~V, ~G, ~p, ra, pa, ea, za, oa, g)(h))
        )(Crit.minus_all(~V, ~G, ~p, za, b, g)(Crit.all.z(~V, ~G, ~p, ra, pa, ea, za, oa, g)(h)))(Crit.minus_all(~V, ~G, ~p, oa, b, g)(Crit.all.o(~V, ~G, ~p, ra, pa, ea, za, oa, g)(h)))(
          Crit.minus_all(~V, ~G, ~p, a, zb, g)(h)
        )(Crit.minus_all(~V, ~G, ~p, a, ob, g)(h))
      )

# the difference of two well formed forks whose reps do not differ before
# both bits is well formed, by how the bits compare (c)
def Crit.minus_at_wf(~V: Data, +ra: List<&2, U32>, +pa: Nat, +ea: Maybe<&2, V>, +za: Crit<V>, +oa: Crit<V>, +rb: List<&2, U32>, +pb: Nat, +eb: Maybe<&2, V>, +zb: Crit<V>, +ob: Crit<V>, +la: Nat, c: Cmp) -> {Crit.wf(~V, Crit.Fork{ra, pa, ea, za, oa}, la) == True{}: Bool} -> {Crit.wf(~V, Crit.minus(V, za, zb), 1n+pa) == True{}: Bool} -> {Crit.wf(~V, Crit.minus(V, oa, ob), 1n+pa) == True{}: Bool} -> {Crit.wf(~V, Crit.minus(V, za, Crit.Fork{rb, pb, eb, zb, ob}), 1n+pa) == True{}: Bool} -> {Crit.wf(~V, Crit.minus(V, oa, Crit.Fork{rb, pb, eb, zb, ob}), 1n+pa) == True{}: Bool} -> {Crit.wf(~V, Crit.minus(V, Crit.Fork{ra, pa, ea, za, oa}, zb), la) == True{}: Bool} -> {Crit.wf(~V, Crit.minus(V, Crit.Fork{ra, pa, ea, za, oa}, ob), la) == True{}: Bool} -> {Crit.wf(~V, Crit.minus.at(V, c, ra, pa, ea, rb, pb, eb, u2 => Crit.minus(V, za, zb), u2 => Crit.minus(V, oa, ob), u2 => Crit.minus(V, za, Crit.Fork{rb, pb, eb, zb, ob}), u2 => Crit.minus(V, oa, Crit.Fork{rb, pb, eb, zb, ob}), u2 => Crit.minus(V, Crit.Fork{ra, pa, ea, za, oa}, zb), u2 => Crit.minus(V, Crit.Fork{ra, pa, ea, za, oa}, ob), za, oa), la) == True{}: Bool}:
  match c:
    case EQ{}:
      +h => w1 => w2 => w3 => w4 => w5 => w6 => Crit.mk_wf(~V, ra, pa, Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, eb), None{}, ea), Crit.minus(V, za, zb), Crit.minus(V, oa, ob), la)(Crit.wf.le(~V, ra, pa, ea, za, oa, la)(h))(
        Crit.or_pick_none(V, eb, ea, Nat.is_eq(List.length(&2, Bool, Key.bits(ra)), pa))(Crit.rep_or(V, ra, pa, ea, za)(Crit.wf.rep_ok(~V, ra, pa, ea, za, oa, la)(h)))
      )(Crit.minus_all(~V, ~Place, ~Place.has, za, zb, Place{ra, pa, False{}})(Crit.wf.all_z(~V, ra, pa, ea, za, oa, la)(h)))(Crit.minus_all(~V, ~Place, ~Place.has, oa, ob, Place{ra, pa, True{}})(Crit.wf.all_o(~V, ra, pa, ea, za, oa, la)(h)))(w1)(w2)
    case LT{}:
      +h => w1 => w2 => +w3 => +w4 => w5 => w6 => Shared.Bool.when_cases(
        Crit<V>,
        t => {Crit.wf(~V, t, la) == True{}: Bool},
        Key.bit(rb, pa),
        u => Crit.mk(V, ra, pa, ea, za, Crit.minus(V, oa, Crit.Fork{rb, pb, eb, zb, ob})),
        u => Crit.mk(V, ra, pa, ea, Crit.minus(V, za, Crit.Fork{rb, pb, eb, zb, ob}), oa),
        t3 => Crit.mk_wf(~V, ra, pa, ea, za, Crit.minus(V, oa, Crit.Fork{rb, pb, eb, zb, ob}), la)(Crit.wf.le(~V, ra, pa, ea, za, oa, la)(h))(Crit.rep_or(V, ra, pa, ea, za)(Crit.wf.rep_ok(~V, ra, pa, ea, za, oa, la)(h)))(Crit.wf.all_z(~V, ra, pa, ea, za, oa, la)(h))(
          Crit.minus_all(~V, ~Place, ~Place.has, oa, Crit.Fork{rb, pb, eb, zb, ob}, Place{ra, pa, True{}})(Crit.wf.all_o(~V, ra, pa, ea, za, oa, la)(h))
        )(Crit.wf.wf_z(~V, ra, pa, ea, za, oa, la)(h))(w4),
        t3 => Crit.mk_wf(~V, ra, pa, ea, Crit.minus(V, za, Crit.Fork{rb, pb, eb, zb, ob}), oa, la)(Crit.wf.le(~V, ra, pa, ea, za, oa, la)(h))(Crit.rep_or(V, ra, pa, ea, za)(Crit.wf.rep_ok(~V, ra, pa, ea, za, oa, la)(h)))(
          Crit.minus_all(~V, ~Place, ~Place.has, za, Crit.Fork{rb, pb, eb, zb, ob}, Place{ra, pa, False{}})(Crit.wf.all_z(~V, ra, pa, ea, za, oa, la)(h))
        )(Crit.wf.all_o(~V, ra, pa, ea, za, oa, la)(h))(w3)(Crit.wf.wf_o(~V, ra, pa, ea, za, oa, la)(h))
      )
    case GT{}:
      h => w1 => w2 => w3 => w4 => +w5 => +w6 => Shared.Bool.when_cases(
        Crit<V>,
        t => {Crit.wf(~V, t, la) == True{}: Bool},
        Key.bit(ra, pb),
        u => Crit.minus(V, Crit.Fork{ra, pa, ea, za, oa}, ob),
        u => Crit.minus(V, Crit.Fork{ra, pa, ea, za, oa}, zb),
        t3 => w6,
        t3 => w5
      )

# the difference of two well formed maps is well formed
def Crit.minus_go_wf(~V: Data, +a: Crit<V>, +b: Crit<V>, +la: Nat, +lb: Nat) -> {Crit.wf(~V, a, la) == True{}: Bool} -> {Crit.wf(~V, b, lb) == True{}: Bool} -> {
  Crit.wf(~V, Crit.minus(V, a, b), la) == True{}: Bool
}:
  match a b:
    case Crit.Tip{} Crit.Tip{}:
      ha => hb => {==}
    case Crit.Tip{} Crit.Leaf{k2, w2}:
      ha => hb => {==}
    case Crit.Tip{} Crit.Fork{r2, p2, e2, z2, o2}:
      ha => hb => {==}
    case Crit.Leaf{k, v} Crit.Tip{}:
      ha => hb => {==}
    case Crit.Fork{ra, pa, ea, za, oa} Crit.Tip{}:
      ha => hb => ha
    case Crit.Leaf{+k, +v} Crit.Leaf{+k2, +w}:
      ha => hb => Shared.Bool.when_cases(Crit<V>, t => {Crit.wf(~V, t, la) == True{}: Bool}, Crit.has(V, Crit.Leaf{k2, w}, k), u => Crit.Tip{}, u => Crit.Leaf{k, v}, t1 => {==}, t1 => {==})
    case Crit.Leaf{+k, +v} Crit.Fork{+rb, +pb, +eb, +zb, +ob}:
      ha => hb => Shared.Bool.when_cases(Crit<V>, t => {Crit.wf(~V, t, la) == True{}: Bool}, Crit.has(V, Crit.Fork{rb, pb, eb, zb, ob}, k), u => Crit.Tip{}, u => Crit.Leaf{k, v}, t1 => {==}, t1 => {==})
    case Crit.Fork{+ra, +pa, +ea, +za, +oa} Crit.Leaf{+k, +w}:
      ha => hb => Crit.drop_go_wf(~V, Crit.Fork{ra, pa, ea, za, oa}, la, 0n, Cur.of(k), k)(ha)
    case Crit.Fork{+ra, +pa, +ea, +za, +oa} Crit.Fork{+rb, +pb, +eb, +zb, +ob}:
      +ha => +hb => Shared.Bool.when_cases(
        Crit<V>,
        t => {Crit.wf(~V, t, la) == True{}: Bool},
        Bool.and(Crit.above(Key.diff(ra, rb), pa), Crit.above(Key.diff(ra, rb), pb)),
        u => Crit.Fork{ra, pa, ea, za, oa},
        u => Crit.minus.at(V, Nat.cmp(pa, pb), ra, pa, ea, rb, pb, eb, u2 => Crit.minus(V, za, zb), u2 => Crit.minus(V, oa, ob), u2 => Crit.minus(V, za, Crit.Fork{rb, pb, eb, zb, ob}), u2 => Crit.minus(V, oa, Crit.Fork{rb, pb, eb, zb, ob}), u2 => Crit.minus(V, Crit.Fork{ra, pa, ea, za, oa}, zb), u2 => Crit.minus(V, Crit.Fork{ra, pa, ea, za, oa}, ob), za, oa),
        t => ha,
        t => Crit.minus_at_wf(~V, ra, pa, ea, za, oa, rb, pb, eb, zb, ob, la, Nat.cmp(pa, pb))(ha)(
          Crit.minus_go_wf(~V, za, zb, 1n+pa, 1n+pb)(Crit.wf.wf_z(~V, ra, pa, ea, za, oa, la)(ha))(Crit.wf.wf_z(~V, rb, pb, eb, zb, ob, lb)(hb))
        )(Crit.minus_go_wf(~V, oa, ob, 1n+pa, 1n+pb)(Crit.wf.wf_o(~V, ra, pa, ea, za, oa, la)(ha))(Crit.wf.wf_o(~V, rb, pb, eb, zb, ob, lb)(hb)))(
          Crit.minus_go_wf(~V, za, b, 1n+pa, lb)(Crit.wf.wf_z(~V, ra, pa, ea, za, oa, la)(ha))(hb)
        )(Crit.minus_go_wf(~V, oa, b, 1n+pa, lb)(Crit.wf.wf_o(~V, ra, pa, ea, za, oa, la)(ha))(hb))(
          Crit.minus_go_wf(~V, a, zb, la, 1n+pb)(ha)(Crit.wf.wf_z(~V, rb, pb, eb, zb, ob, lb)(hb))
        )(Crit.minus_go_wf(~V, a, ob, la, 1n+pb)(ha)(Crit.wf.wf_o(~V, rb, pb, eb, zb, ob, lb)(hb)))
      )

# a difference keeps maps well formed
law Crit.minus_wf:
  for ~V: Data
  for a: Crit<V>
  for b: Crit<V>
  {Crit.wf(~V, a, 0n) == True{}: Bool} -> {Crit.wf(~V, b, 0n) == True{}: Bool} -> {Crit.wf(~V, Crit.minus(V, a, b), 0n) == True{}: Bool}

def Crit.minus_wf(ty, a, b):
  ha => hb => Crit.minus_go_wf(~ty, a, b, 0n, 0n)(ha)(hb)

# Crit.leaf_minus where the entry's key is the key q or not (b), and the map
# holds it
def Crit.leaf_minus.t(-V: Data, +y: Crit<V>, +k: List<&2, U32>, +q: List<&2, U32>, -v: V, b: Bool) -> {Key.is_eq(k, q) == b: Bool} -> {
  Maybe.is_some(&2, V, Crit.lookup(V, y, k)) == True{}: Bool
} -> {Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, y, q)), None{}, Shared.Maybe.when(V, b, u => Some{v})) == None{}: Maybe<&2, V>}:
  match b:
    case True{}:
      e => hs =>
        %Key.is_eq_sound(k, q)(e): {Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, y, _)), None{}, Some{v}) == None{}: Maybe<&2, V>}
        %Equal.sym(Bool, Maybe.is_some(&2, V, Crit.lookup(V, y, k)), True{}, hs): {Bool.pick(Maybe<&2, V>, _, None{}, Some{v}) == None{}: Maybe<&2, V>}
        {==}
    case False{}:
      e => hs => Crit.pick_none(V, Maybe.is_some(&2, V, Crit.lookup(V, y, q)))

# Crit.leaf_minus where the entry's key is the key q or not (b), and the map
# lacks it
def Crit.leaf_minus.f(-V: Data, +y: Crit<V>, +k: List<&2, U32>, +q: List<&2, U32>, -v: V, b: Bool) -> {Key.is_eq(k, q) == b: Bool} -> {
  Maybe.is_some(&2, V, Crit.lookup(V, y, k)) == False{}: Bool
} -> {Shared.Maybe.when(V, b, u => Some{v}) == Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, y, q)), None{}, Shared.Maybe.when(V, b, u => Some{v})): Maybe<&2, V>}:
  match b:
    case True{}:
      e => hs =>
        %Key.is_eq_sound(k, q)(e): {Some{v} == Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, y, _)), None{}, Some{v}): Maybe<&2, V>}
        %Equal.sym(Bool, Maybe.is_some(&2, V, Crit.lookup(V, y, k)), False{}, hs): {Some{v} == Bool.pick(Maybe<&2, V>, _, None{}, Some{v}): Maybe<&2, V>}
        {==}
    case False{}:
      e => hs => Equal.sym(Maybe<&2, V>, Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, y, q)), None{}, None{}), None{}, Crit.pick_none(V, Maybe.is_some(&2, V, Crit.lookup(V, y, q))))

# the difference of an entry and a well formed map
def Crit.leaf_minus(~V: Data, +k: List<&2, U32>, +v: V, +y: Crit<V>, +ly: Nat, +q: List<&2, U32>) -> {Crit.wf(~V, y, ly) == True{}: Bool} -> {
  Crit.lookup(V, Shared.Bool.when(Crit<V>, Crit.has(V, y, k), u => Crit.Tip{}, u => Crit.Leaf{k, v}), q)
    == Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, y, q)), None{}, Crit.lookup(V, Crit.Leaf{k, v}, q)): Maybe<&2, V>
}:
  +h => Shared.Bool.when_cases(
    Crit<V>,
    t => {Crit.lookup(V, t, q) == Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, y, q)), None{}, Crit.lookup(V, Crit.Leaf{k, v}, q)): Maybe<&2, V>},
    Crit.has(V, y, k),
    u => Crit.Tip{},
    u => Crit.Leaf{k, v},
    t1 => Equal.sym(
      Maybe<&2, V>,
      Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, y, q)), None{}, Crit.lookup(V, Crit.Leaf{k, v}, q)),
      None{},
      Crit.leaf_minus.t(V, y, k, q, v, Key.is_eq(k, q))({==})(
        Equal.trans(Bool, Maybe.is_some(&2, V, Crit.lookup(V, y, k)), Maybe.is_some(&2, V, Crit.get(V, y, k)), True{}, Equal.cong(Maybe<&2, V>, Bool, x => Maybe.is_some(&2, V, x), Crit.lookup(V, y, k), Crit.get(V, y, k), Equal.sym(Maybe<&2, V>, Crit.get(V, y, k), Crit.lookup(V, y, k), Crit.get_lookup.lo(~V, y, ly, k)(h))), t1)
      )
    ),
    t1 => Crit.leaf_minus.f(V, y, k, q, v, Key.is_eq(k, q))({==})(
      Equal.trans(Bool, Maybe.is_some(&2, V, Crit.lookup(V, y, k)), Maybe.is_some(&2, V, Crit.get(V, y, k)), False{}, Equal.cong(Maybe<&2, V>, Bool, x => Maybe.is_some(&2, V, x), Crit.lookup(V, y, k), Crit.get(V, y, k), Equal.sym(Maybe<&2, V>, Crit.get(V, y, k), Crit.lookup(V, y, k), Crit.get_lookup.lo(~V, y, ly, k)(h))), t1)
    )
  )

# the difference of two well formed forks whose reps differ before both bits
# is the first: they hold no key in common
def Crit.minus_both(~V: Data, +ra: List<&2, U32>, +pa: Nat, +ea: Maybe<&2, V>, +za: Crit<V>, +oa: Crit<V>, +rb: List<&2, U32>, +pb: Nat, +eb: Maybe<&2, V>, +zb: Crit<V>, +ob: Crit<V>, +la: Nat, +lb: Nat, +q: List<&2, U32>) -> {Crit.wf(~V, Crit.Fork{ra, pa, ea, za, oa}, la) == True{}: Bool} -> {Crit.wf(~V, Crit.Fork{rb, pb, eb, zb, ob}, lb) == True{}: Bool} -> {
  Bool.and(Crit.above(Key.diff(ra, rb), pa), Crit.above(Key.diff(ra, rb), pb)) == True{}: Bool
} -> {Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q) == Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), None{}, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q)): Maybe<&2, V>}:
  +ha => +hb => +hab => Crit.pick_disj(V, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q), Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q))(
    +t => Crit.none_by(V, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q))(
      +s =>
        +sd = Crit.above_some(Key.diff(ra, rb), pa)(Shared.Bool.and_true_left(Crit.above(Key.diff(ra, rb), pa), Crit.above(Key.diff(ra, rb), pb))(hab))
        +lta = Crit.above_lt(Key.diff(ra, rb), pa, Maybe.default(&2, Nat, Key.diff(ra, rb), 0n))(sd)(Shared.Bool.and_true_left(Crit.above(Key.diff(ra, rb), pa), Crit.above(Key.diff(ra, rb), pb))(hab))
        +ltb = Crit.above_lt(Key.diff(ra, rb), pb, Maybe.default(&2, Nat, Key.diff(ra, rb), 0n))(sd)(Shared.Bool.and_true_right(Crit.above(Key.diff(ra, rb), pa), Crit.above(Key.diff(ra, rb), pb))(hab))
        +qa = Key.agree_le(q, ra, 1n+Maybe.default(&2, Nat, Key.diff(ra, rb), 0n), pa)(Crit.lt_le_succ(Maybe.default(&2, Nat, Key.diff(ra, rb), 0n), pa)(lta))(Crit.in_fork_agree(~V, ra, pa, ea, za, oa, la, q)(ha)(s))
        +qb = Key.agree_le(q, rb, 1n+Maybe.default(&2, Nat, Key.diff(ra, rb), 0n), pb)(Crit.lt_le_succ(Maybe.default(&2, Nat, Key.diff(ra, rb), 0n), pb)(ltb))(Crit.in_fork_agree(~V, rb, pb, eb, zb, ob, lb, q)(hb)(t))
        Crit.clash(
          Key.agree(ra, rb, 1n+Maybe.default(&2, Nat, Key.diff(ra, rb), 0n)),
          True{},
          False{},
          Key.agree_join(ra, rb, q, 1n+Maybe.default(&2, Nat, Key.diff(ra, rb), 0n))(Key.agree_sym(q, ra, 1n+Maybe.default(&2, Nat, Key.diff(ra, rb), 0n))(qa))(Key.agree_sym(q, rb, 1n+Maybe.default(&2, Nat, Key.diff(ra, rb), 0n))(qb)),
          (
            %Equal.sym(Maybe<&2, Nat>, Key.diff(ra, rb), Some{Maybe.default(&2, Nat, Key.diff(ra, rb), 0n)}, sd): {Bits.agree(_, 1n+Maybe.default(&2, Nat, Key.diff(ra, rb), 0n)) == False{}: Bool}
            Shared.Nat.succ_nle(Maybe.default(&2, Nat, Key.diff(ra, rb), 0n))
          ),
          Shared.Bool.true_ne_false
        )
    )
  )

# the difference of two well formed forks at one bit, whose reps agree before
# it
def Crit.minus_eq(~V: Data, +ra: List<&2, U32>, +pa: Nat, +ea: Maybe<&2, V>, +za: Crit<V>, +oa: Crit<V>, +rb: List<&2, U32>, +pb: Nat, +eb: Maybe<&2, V>, +zb: Crit<V>, +ob: Crit<V>, +la: Nat, +lb: Nat, +q: List<&2, U32>) -> {Crit.wf(~V, Crit.Fork{ra, pa, ea, za, oa}, la) == True{}: Bool} -> {Crit.wf(~V, Crit.Fork{rb, pb, eb, zb, ob}, lb) == True{}: Bool} -> {pa == pb: Nat} -> {Crit.above(Key.diff(ra, rb), pa) == False{}: Bool} -> {
  Crit.lookup(V, Crit.minus(V, za, zb), q) == Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, zb, q)), None{}, Crit.lookup(V, za, q)): Maybe<&2, V>
} -> {Crit.lookup(V, Crit.minus(V, oa, ob), q) == Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, ob, q)), None{}, Crit.lookup(V, oa, q)): Maybe<&2, V>} -> {
  Crit.lookup(V, Crit.mk(V, ra, pa, Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, eb), None{}, ea), Crit.minus(V, za, zb), Crit.minus(V, oa, ob)), q) == Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), None{}, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q)): Maybe<&2, V>
}:
  +ha => +hb => +eqp => +hab => +iz => +io => Equal.trans(
    Maybe<&2, V>,
    Crit.lookup(V, Crit.mk(V, ra, pa, Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, eb), None{}, ea), Crit.minus(V, za, zb), Crit.minus(V, oa, ob)), q),
    Maybe.or(&2, V, Crit.ended(V, ra, Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, eb), None{}, ea), q), Maybe.or(&2, V, Crit.lookup(V, Crit.minus(V, za, zb), q), Crit.lookup(V, Crit.minus(V, oa, ob), q))),
    Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), None{}, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q)),
    Crit.mk_lookup(V, ra, pa, Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, eb), None{}, ea), Crit.minus(V, za, zb), Crit.minus(V, oa, ob), q),
    Crit.side_split({Maybe.or(&2, V, Crit.ended(V, ra, Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, eb), None{}, ea), q), Maybe.or(&2, V, Crit.lookup(V, Crit.minus(V, za, zb), q), Crit.lookup(V, Crit.minus(V, oa, ob), q))) == Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), None{}, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q)): Maybe<&2, V>}, q, pa)(
      +hs => Equal.trans(Maybe<&2, V>, Maybe.or(&2, V, Crit.ended(V, ra, Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, eb), None{}, ea), q), Maybe.or(&2, V, Crit.lookup(V, Crit.minus(V, za, zb), q), Crit.lookup(V, Crit.minus(V, oa, ob), q))), Crit.lookup(V, Crit.minus(V, oa, ob), q), Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), None{}, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q)), Crit.or_third(V, Crit.ended(V, ra, Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, eb), None{}, ea), q), Crit.lookup(V, Crit.minus(V, za, zb), q), Crit.lookup(V, Crit.minus(V, oa, ob), q))(Crit.ended_pick(V, ra, eb, ea, q)(Crit.ended_long(V, ra, pa, ea, za, q, List.drop(&2, Bool, Key.bits(q), pa))(Crit.wf.rep_ok(~V, ra, pa, ea, za, oa, la)(ha))({==})(Crit.side_some_ne(q, pa, True{})(hs))))(Equal.trans(Maybe<&2, V>, Crit.lookup(V, Crit.minus(V, za, zb), q), Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, zb, q)), None{}, Crit.lookup(V, za, q)), None{}, iz, Crit.pick_none2(V, Maybe.is_some(&2, V, Crit.lookup(V, zb, q)), Crit.lookup(V, za, q))(Crit.lookup_all(~V, ~Place, ~Place.has, za, Place{ra, pa, False{}}, q)(Crit.wf.all_z(~V, ra, pa, ea, za, oa, la)(ha))(Place.has_not(ra, pa, False{}, q, Some{True{}}, hs, {==}))))), Equal.trans(Maybe<&2, V>, Crit.lookup(V, Crit.minus(V, oa, ob), q), Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, ob, q)), None{}, Crit.lookup(V, oa, q)), Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), None{}, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q)), io, Equal.sym(Maybe<&2, V>, Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), None{}, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q)), Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, ob, q)), None{}, Crit.lookup(V, oa, q)), Equal.trans(Maybe<&2, V>, Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), None{}, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q)), Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, ob, q)), None{}, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q)), Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, ob, q)), None{}, Crit.lookup(V, oa, q)), Equal.cong(Maybe<&2, V>, Maybe<&2, V>, t => Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, t), None{}, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q)), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q), Crit.lookup(V, ob, q), Crit.route_side(~V, rb, pb, eb, zb, ob, lb, q, True{})(hb)((
          %eqp: {Key.side(q, _) == Some{True{}}: Maybe<&2, Bool>}
          hs
        ))), Equal.cong(Maybe<&2, V>, Maybe<&2, V>, t => Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, ob, q)), None{}, t), Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, oa, q), Crit.route_side(~V, ra, pa, ea, za, oa, la, q, True{})(ha)(hs))))))
    )(
      +hs => Equal.trans(Maybe<&2, V>, Maybe.or(&2, V, Crit.ended(V, ra, Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, eb), None{}, ea), q), Maybe.or(&2, V, Crit.lookup(V, Crit.minus(V, za, zb), q), Crit.lookup(V, Crit.minus(V, oa, ob), q))), Crit.lookup(V, Crit.minus(V, za, zb), q), Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), None{}, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q)), Crit.or_second(V, Crit.ended(V, ra, Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, eb), None{}, ea), q), Crit.lookup(V, Crit.minus(V, za, zb), q), Crit.lookup(V, Crit.minus(V, oa, ob), q))(Crit.ended_pick(V, ra, eb, ea, q)(Crit.ended_long(V, ra, pa, ea, za, q, List.drop(&2, Bool, Key.bits(q), pa))(Crit.wf.rep_ok(~V, ra, pa, ea, za, oa, la)(ha))({==})(Crit.side_some_ne(q, pa, False{})(hs))))(Equal.trans(Maybe<&2, V>, Crit.lookup(V, Crit.minus(V, oa, ob), q), Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, ob, q)), None{}, Crit.lookup(V, oa, q)), None{}, io, Crit.pick_none2(V, Maybe.is_some(&2, V, Crit.lookup(V, ob, q)), Crit.lookup(V, oa, q))(Crit.lookup_all(~V, ~Place, ~Place.has, oa, Place{ra, pa, True{}}, q)(Crit.wf.all_o(~V, ra, pa, ea, za, oa, la)(ha))(Place.has_not(ra, pa, True{}, q, Some{False{}}, hs, {==}))))), Equal.trans(Maybe<&2, V>, Crit.lookup(V, Crit.minus(V, za, zb), q), Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, zb, q)), None{}, Crit.lookup(V, za, q)), Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), None{}, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q)), iz, Equal.sym(Maybe<&2, V>, Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), None{}, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q)), Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, zb, q)), None{}, Crit.lookup(V, za, q)), Equal.trans(Maybe<&2, V>, Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), None{}, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q)), Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, zb, q)), None{}, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q)), Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, zb, q)), None{}, Crit.lookup(V, za, q)), Equal.cong(Maybe<&2, V>, Maybe<&2, V>, t => Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, t), None{}, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q)), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q), Crit.lookup(V, zb, q), Crit.route_side(~V, rb, pb, eb, zb, ob, lb, q, False{})(hb)((
          %eqp: {Key.side(q, _) == Some{False{}}: Maybe<&2, Bool>}
          hs
        ))), Equal.cong(Maybe<&2, V>, Maybe<&2, V>, t => Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, zb, q)), None{}, t), Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.lookup(V, za, q), Crit.route_side(~V, ra, pa, ea, za, oa, la, q, False{})(ha)(hs))))))
    )(
      +hs =>
          +nil = Crit.side_nil(q, pa)(hs)
          Equal.trans(
            Maybe<&2, V>,
            Maybe.or(&2, V, Crit.ended(V, ra, Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, eb), None{}, ea), q), Maybe.or(&2, V, Crit.lookup(V, Crit.minus(V, za, zb), q), Crit.lookup(V, Crit.minus(V, oa, ob), q))),
            Crit.ended(V, ra, Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, eb), None{}, ea), q),
            Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), None{}, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q)),
            Crit.or_first(V, Crit.ended(V, ra, Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, eb), None{}, ea), q), Crit.lookup(V, Crit.minus(V, za, zb), q), Crit.lookup(V, Crit.minus(V, oa, ob), q))(
              Equal.trans(Maybe<&2, V>, Crit.lookup(V, Crit.minus(V, za, zb), q), Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, zb, q)), None{}, Crit.lookup(V, za, q)), None{}, iz, Crit.pick_none2(V, Maybe.is_some(&2, V, Crit.lookup(V, zb, q)), Crit.lookup(V, za, q))(Crit.no_side(~V, ra, pa, za, False{}, q)(Crit.wf.all_z(~V, ra, pa, ea, za, oa, la)(ha))(nil)))
            )(Equal.trans(Maybe<&2, V>, Crit.lookup(V, Crit.minus(V, oa, ob), q), Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, ob, q)), None{}, Crit.lookup(V, oa, q)), None{}, io, Crit.pick_none2(V, Maybe.is_some(&2, V, Crit.lookup(V, ob, q)), Crit.lookup(V, oa, q))(Crit.no_side(~V, ra, pa, oa, True{}, q)(Crit.wf.all_o(~V, ra, pa, ea, za, oa, la)(ha))(nil)))),
            Equal.trans(
              Maybe<&2, V>,
              Crit.ended(V, ra, Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, eb), None{}, ea), q),
              Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.ended(V, rb, eb, q)), None{}, Crit.ended(V, ra, ea, q)),
              Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), None{}, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q)),
              Crit.ends_minus(V, ra, pa, ea, za, rb, pb, eb, zb, q)(Crit.wf.rep_ok(~V, ra, pa, ea, za, oa, la)(ha))(Crit.wf.rep_ok(~V, rb, pb, eb, zb, ob, lb)(hb))(eqp)(hab),
              Equal.sym(
                Maybe<&2, V>,
                Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), None{}, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q)),
                Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.ended(V, rb, eb, q)), None{}, Crit.ended(V, ra, ea, q)),
                Equal.trans(
                  Maybe<&2, V>,
                  Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), None{}, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q)),
                  Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.ended(V, rb, eb, q)), None{}, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q)),
                  Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.ended(V, rb, eb, q)), None{}, Crit.ended(V, ra, ea, q)),
                  Equal.cong(Maybe<&2, V>, Maybe<&2, V>, t => Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, t), None{}, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q)), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q), Crit.ended(V, rb, eb, q), Crit.route_end(~V, rb, pb, eb, zb, ob, lb, q)(hb)((
          %eqp: {Key.side(q, _) == None{}: Maybe<&2, Bool>}
          hs
        ))),
                  Equal.cong(Maybe<&2, V>, Maybe<&2, V>, t => Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.ended(V, rb, eb, q)), None{}, t), Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Crit.ended(V, ra, ea, q), Crit.route_end(~V, ra, pa, ea, za, oa, la, q)(ha)(hs))
                )
              )
            )
          )
    )
  )

# the difference of two well formed forks whose reps agree before the bit pa
# of the first, which is before the bit pb of the second: b goes to its side
# of a
def Crit.minus_lt(~V: Data, +ra: List<&2, U32>, +pa: Nat, +ea: Maybe<&2, V>, +za: Crit<V>, +oa: Crit<V>, +rb: List<&2, U32>, +pb: Nat, +eb: Maybe<&2, V>, +zb: Crit<V>, +ob: Crit<V>, +la: Nat, +lb: Nat, +q: List<&2, U32>) -> {Crit.wf(~V, Crit.Fork{ra, pa, ea, za, oa}, la) == True{}: Bool} -> {Crit.wf(~V, Crit.Fork{rb, pb, eb, zb, ob}, lb) == True{}: Bool} -> {Nat.is_lt(pa, pb) == True{}: Bool} -> {Crit.above(Key.diff(ra, rb), pa) == False{}: Bool} -> {
  Crit.lookup(V, Crit.minus(V, za, Crit.Fork{rb, pb, eb, zb, ob}), q) == Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), None{}, Crit.lookup(V, za, q)): Maybe<&2, V>
} -> {Crit.lookup(V, Crit.minus(V, oa, Crit.Fork{rb, pb, eb, zb, ob}), q) == Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), None{}, Crit.lookup(V, oa, q)): Maybe<&2, V>} -> {
  Crit.lookup(V, Shared.Bool.when(Crit<V>, Key.bit(rb, pa), u => Crit.mk(V, ra, pa, ea, za, Crit.minus(V, oa, Crit.Fork{rb, pb, eb, zb, ob})), u => Crit.mk(V, ra, pa, ea, Crit.minus(V, za, Crit.Fork{rb, pb, eb, zb, ob}), oa)), q) == Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), None{}, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q)): Maybe<&2, V>
}:
  +ha => +hb => +lt => +hab => +iz => +io =>
    +nr = Crit.len_drop(Key.bits(rb), pa)(Shared.Nat.lt_le(pa, pb, List.length(&2, Bool, Key.bits(rb)))(lt)(Crit.rep_long(~V, rb, pb, eb, zb, ob, lb)(hb)))
    +t2n = Equal.trans(
      Bool,
      Cur.done(Key.at(rb, pa)),
      List.is_empty(&2, Bool, List.drop(&2, Bool, Key.bits(rb), pa)),
      False{},
      Crit.done_of(Key.at(rb, pa), List.drop(&2, Bool, Key.bits(rb), pa))(Cur.skip_bits(pa, Cur.of(rb))),
      nr
    )
    +allb = Crit.fork_place(~V, rb, pb, eb, zb, ob, lb, ra, pa, Cur.bit(Key.at(rb, pa)))(hb)(lt)(Crit.not_above_agree(Key.diff(ra, rb), pa)(hab))(Crit.side_of(rb, pa, Cur.bit(Key.at(rb, pa)))(t2n)({==}))
    Shared.Bool.when_cases(
      Crit<V>,
      t => {Crit.lookup(V, t, q) == Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), None{}, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q)): Maybe<&2, V>},
      Key.bit(rb, pa),
      u => Crit.mk(V, ra, pa, ea, za, Crit.minus(V, oa, Crit.Fork{rb, pb, eb, zb, ob})),
      u => Crit.mk(V, ra, pa, ea, Crit.minus(V, za, Crit.Fork{rb, pb, eb, zb, ob}), oa),
      +t3 =>
          +allt = Crit.all_place_b(~V, Crit.Fork{rb, pb, eb, zb, ob}, ra, pa, Key.bit(rb, pa), True{})(t3)(allb)
          Equal.trans(
            Maybe<&2, V>,
            Crit.lookup(V, Crit.mk(V, ra, pa, ea, za, Crit.minus(V, oa, Crit.Fork{rb, pb, eb, zb, ob})), q),
            Maybe.or(&2, V, Crit.ended(V, ra, ea, q), Maybe.or(&2, V, Crit.lookup(V, za, q), Crit.lookup(V, Crit.minus(V, oa, Crit.Fork{rb, pb, eb, zb, ob}), q))),
            Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), None{}, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q)),
            Crit.mk_lookup(V, ra, pa, ea, za, Crit.minus(V, oa, Crit.Fork{rb, pb, eb, zb, ob}), q),
            Equal.sym(
              Maybe<&2, V>,
              Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), None{}, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q)),
              Maybe.or(&2, V, Crit.ended(V, ra, ea, q), Maybe.or(&2, V, Crit.lookup(V, za, q), Crit.lookup(V, Crit.minus(V, oa, Crit.Fork{rb, pb, eb, zb, ob}), q))),
              Crit.pick_cases(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), None{}, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Maybe.or(&2, V, Crit.ended(V, ra, ea, q), Maybe.or(&2, V, Crit.lookup(V, za, q), Crit.lookup(V, Crit.minus(V, oa, Crit.Fork{rb, pb, eb, zb, ob}), q))))(
                +ct =>
                  +hsq = Place.has_side(ra, pa, True{}, q)(Crit.in_place(~V, Crit.Fork{rb, pb, eb, zb, ob}, Place{ra, pa, True{}}, q)(allt)(ct))
                  Equal.sym(Maybe<&2, V>, Maybe.or(&2, V, Crit.ended(V, ra, ea, q), Maybe.or(&2, V, Crit.lookup(V, za, q), Crit.lookup(V, Crit.minus(V, oa, Crit.Fork{rb, pb, eb, zb, ob}), q))), None{}, Crit.or3_none(V, Crit.ended(V, ra, ea, q), Crit.lookup(V, za, q), Crit.lookup(V, Crit.minus(V, oa, Crit.Fork{rb, pb, eb, zb, ob}), q))(Crit.ended_long(V, ra, pa, ea, za, q, List.drop(&2, Bool, Key.bits(q), pa))(Crit.wf.rep_ok(~V, ra, pa, ea, za, oa, la)(ha))({==})(Crit.side_some_ne(q, pa, True{})(hsq)))(Crit.lookup_all(~V, ~Place, ~Place.has, za, Place{ra, pa, False{}}, q)(Crit.wf.all_z(~V, ra, pa, ea, za, oa, la)(ha))(Place.has_not(ra, pa, False{}, q, Some{True{}}, hsq, {==})))(Equal.trans(Maybe<&2, V>, Crit.lookup(V, Crit.minus(V, oa, Crit.Fork{rb, pb, eb, zb, ob}), q), Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), None{}, Crit.lookup(V, oa, q)), None{}, io, (
                %Equal.sym(Bool, Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), True{}, ct): {Bool.pick(Maybe<&2, V>, _, None{}, Crit.lookup(V, oa, q)) == None{}: Maybe<&2, V>}
                {==}
              ))))
              )(
                cf => Equal.cong(Maybe<&2, V>, Maybe<&2, V>, t => Maybe.or(&2, V, Crit.ended(V, ra, ea, q), Maybe.or(&2, V, Crit.lookup(V, za, q), t)), Crit.lookup(V, oa, q), Crit.lookup(V, Crit.minus(V, oa, Crit.Fork{rb, pb, eb, zb, ob}), q), Equal.sym(Maybe<&2, V>, Crit.lookup(V, Crit.minus(V, oa, Crit.Fork{rb, pb, eb, zb, ob}), q), Crit.lookup(V, oa, q), Equal.trans(Maybe<&2, V>, Crit.lookup(V, Crit.minus(V, oa, Crit.Fork{rb, pb, eb, zb, ob}), q), Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), None{}, Crit.lookup(V, oa, q)), Crit.lookup(V, oa, q), io, (
                %Equal.sym(Bool, Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), False{}, cf): {Bool.pick(Maybe<&2, V>, _, None{}, Crit.lookup(V, oa, q)) == Crit.lookup(V, oa, q): Maybe<&2, V>}
                {==}
              ))))
              )
            )
          ),
      +t3 =>
          +allt = Crit.all_place_b(~V, Crit.Fork{rb, pb, eb, zb, ob}, ra, pa, Key.bit(rb, pa), False{})(t3)(allb)
          Equal.trans(
            Maybe<&2, V>,
            Crit.lookup(V, Crit.mk(V, ra, pa, ea, Crit.minus(V, za, Crit.Fork{rb, pb, eb, zb, ob}), oa), q),
            Maybe.or(&2, V, Crit.ended(V, ra, ea, q), Maybe.or(&2, V, Crit.lookup(V, Crit.minus(V, za, Crit.Fork{rb, pb, eb, zb, ob}), q), Crit.lookup(V, oa, q))),
            Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), None{}, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q)),
            Crit.mk_lookup(V, ra, pa, ea, Crit.minus(V, za, Crit.Fork{rb, pb, eb, zb, ob}), oa, q),
            Equal.sym(
              Maybe<&2, V>,
              Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), None{}, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q)),
              Maybe.or(&2, V, Crit.ended(V, ra, ea, q), Maybe.or(&2, V, Crit.lookup(V, Crit.minus(V, za, Crit.Fork{rb, pb, eb, zb, ob}), q), Crit.lookup(V, oa, q))),
              Crit.pick_cases(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), None{}, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Maybe.or(&2, V, Crit.ended(V, ra, ea, q), Maybe.or(&2, V, Crit.lookup(V, Crit.minus(V, za, Crit.Fork{rb, pb, eb, zb, ob}), q), Crit.lookup(V, oa, q))))(
                +ct =>
                  +hsq = Place.has_side(ra, pa, False{}, q)(Crit.in_place(~V, Crit.Fork{rb, pb, eb, zb, ob}, Place{ra, pa, False{}}, q)(allt)(ct))
                  Equal.sym(Maybe<&2, V>, Maybe.or(&2, V, Crit.ended(V, ra, ea, q), Maybe.or(&2, V, Crit.lookup(V, Crit.minus(V, za, Crit.Fork{rb, pb, eb, zb, ob}), q), Crit.lookup(V, oa, q))), None{}, Crit.or3_none(V, Crit.ended(V, ra, ea, q), Crit.lookup(V, Crit.minus(V, za, Crit.Fork{rb, pb, eb, zb, ob}), q), Crit.lookup(V, oa, q))(Crit.ended_long(V, ra, pa, ea, za, q, List.drop(&2, Bool, Key.bits(q), pa))(Crit.wf.rep_ok(~V, ra, pa, ea, za, oa, la)(ha))({==})(Crit.side_some_ne(q, pa, False{})(hsq)))(Equal.trans(Maybe<&2, V>, Crit.lookup(V, Crit.minus(V, za, Crit.Fork{rb, pb, eb, zb, ob}), q), Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), None{}, Crit.lookup(V, za, q)), None{}, iz, (
                %Equal.sym(Bool, Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), True{}, ct): {Bool.pick(Maybe<&2, V>, _, None{}, Crit.lookup(V, za, q)) == None{}: Maybe<&2, V>}
                {==}
              )))(Crit.lookup_all(~V, ~Place, ~Place.has, oa, Place{ra, pa, True{}}, q)(Crit.wf.all_o(~V, ra, pa, ea, za, oa, la)(ha))(Place.has_not(ra, pa, True{}, q, Some{False{}}, hsq, {==}))))
              )(
                cf => Equal.cong(Maybe<&2, V>, Maybe<&2, V>, t => Maybe.or(&2, V, Crit.ended(V, ra, ea, q), Maybe.or(&2, V, t, Crit.lookup(V, oa, q))), Crit.lookup(V, za, q), Crit.lookup(V, Crit.minus(V, za, Crit.Fork{rb, pb, eb, zb, ob}), q), Equal.sym(Maybe<&2, V>, Crit.lookup(V, Crit.minus(V, za, Crit.Fork{rb, pb, eb, zb, ob}), q), Crit.lookup(V, za, q), Equal.trans(Maybe<&2, V>, Crit.lookup(V, Crit.minus(V, za, Crit.Fork{rb, pb, eb, zb, ob}), q), Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), None{}, Crit.lookup(V, za, q)), Crit.lookup(V, za, q), iz, (
                %Equal.sym(Bool, Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), False{}, cf): {Bool.pick(Maybe<&2, V>, _, None{}, Crit.lookup(V, za, q)) == Crit.lookup(V, za, q): Maybe<&2, V>}
                {==}
              ))))
              )
            )
          )
    )

# the difference of two well formed forks whose reps agree before the bit pb
# of the second, which is before the bit pa of the first: a goes to its side
# of b
def Crit.minus_gt(~V: Data, +ra: List<&2, U32>, +pa: Nat, +ea: Maybe<&2, V>, +za: Crit<V>, +oa: Crit<V>, +rb: List<&2, U32>, +pb: Nat, +eb: Maybe<&2, V>, +zb: Crit<V>, +ob: Crit<V>, +la: Nat, +lb: Nat, +q: List<&2, U32>) -> {Crit.wf(~V, Crit.Fork{ra, pa, ea, za, oa}, la) == True{}: Bool} -> {Crit.wf(~V, Crit.Fork{rb, pb, eb, zb, ob}, lb) == True{}: Bool} -> {Nat.is_lt(pb, pa) == True{}: Bool} -> {Crit.above(Key.diff(ra, rb), pb) == False{}: Bool} -> {
  Crit.lookup(V, Crit.minus(V, Crit.Fork{ra, pa, ea, za, oa}, zb), q) == Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, zb, q)), None{}, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q)): Maybe<&2, V>
} -> {Crit.lookup(V, Crit.minus(V, Crit.Fork{ra, pa, ea, za, oa}, ob), q) == Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, ob, q)), None{}, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q)): Maybe<&2, V>} -> {
  Crit.lookup(V, Shared.Bool.when(Crit<V>, Key.bit(ra, pb), u => Crit.minus(V, Crit.Fork{ra, pa, ea, za, oa}, ob), u => Crit.minus(V, Crit.Fork{ra, pa, ea, za, oa}, zb)), q) == Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), None{}, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q)): Maybe<&2, V>
}:
  +ha => +hb => +gt => +hab => +iz => +io =>
    +nr = Crit.len_drop(Key.bits(ra), pb)(Shared.Nat.lt_le(pb, pa, List.length(&2, Bool, Key.bits(ra)))(gt)(Crit.rep_long(~V, ra, pa, ea, za, oa, la)(ha)))
    +t2n = Equal.trans(
      Bool,
      Cur.done(Key.at(ra, pb)),
      List.is_empty(&2, Bool, List.drop(&2, Bool, Key.bits(ra), pb)),
      False{},
      Crit.done_of(Key.at(ra, pb), List.drop(&2, Bool, Key.bits(ra), pb))(Cur.skip_bits(pb, Cur.of(ra))),
      nr
    )
    +alla = Crit.fork_place(~V, ra, pa, ea, za, oa, la, rb, pb, Cur.bit(Key.at(ra, pb)))(ha)(gt)(Key.agree_sym(ra, rb, pb)(Crit.not_above_agree(Key.diff(ra, rb), pb)(hab)))(Crit.side_of(ra, pb, Cur.bit(Key.at(ra, pb)))(t2n)({==}))
    Shared.Bool.when_cases(
      Crit<V>,
      t => {Crit.lookup(V, t, q) == Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), None{}, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q)): Maybe<&2, V>},
      Key.bit(ra, pb),
      u => Crit.minus(V, Crit.Fork{ra, pa, ea, za, oa}, ob),
      u => Crit.minus(V, Crit.Fork{ra, pa, ea, za, oa}, zb),
      +t3 =>
          +allt = Crit.all_place_b(~V, Crit.Fork{ra, pa, ea, za, oa}, rb, pb, Key.bit(ra, pb), True{})(t3)(alla)
          Equal.trans(
            Maybe<&2, V>,
            Crit.lookup(V, Crit.minus(V, Crit.Fork{ra, pa, ea, za, oa}, ob), q),
            Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, ob, q)), None{}, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q)),
            Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), None{}, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q)),
            io,
            Crit.pick_same(V, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Maybe.is_some(&2, V, Crit.lookup(V, ob, q)), Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)))(
              s => Equal.sym(
                Bool,
                Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)),
                Maybe.is_some(&2, V, Crit.lookup(V, ob, q)),
                Equal.cong(Maybe<&2, V>, Bool, x => Maybe.is_some(&2, V, x), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q), Crit.lookup(V, ob, q), Crit.route_side(~V, rb, pb, eb, zb, ob, lb, q, True{})(hb)(Place.has_side(rb, pb, True{}, q)(Crit.in_place(~V, Crit.Fork{ra, pa, ea, za, oa}, Place{rb, pb, True{}}, q)(allt)(s))))
              )
            )
          ),
      +t3 =>
          +allt = Crit.all_place_b(~V, Crit.Fork{ra, pa, ea, za, oa}, rb, pb, Key.bit(ra, pb), False{})(t3)(alla)
          Equal.trans(
            Maybe<&2, V>,
            Crit.lookup(V, Crit.minus(V, Crit.Fork{ra, pa, ea, za, oa}, zb), q),
            Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, zb, q)), None{}, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q)),
            Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), None{}, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q)),
            iz,
            Crit.pick_same(V, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q), Maybe.is_some(&2, V, Crit.lookup(V, zb, q)), Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)))(
              s => Equal.sym(
                Bool,
                Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)),
                Maybe.is_some(&2, V, Crit.lookup(V, zb, q)),
                Equal.cong(Maybe<&2, V>, Bool, x => Maybe.is_some(&2, V, x), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q), Crit.lookup(V, zb, q), Crit.route_side(~V, rb, pb, eb, zb, ob, lb, q, False{})(hb)(Place.has_side(rb, pb, False{}, q)(Crit.in_place(~V, Crit.Fork{ra, pa, ea, za, oa}, Place{rb, pb, False{}}, q)(allt)(s))))
              )
            )
          )
    )

# the difference of two well formed forks whose reps do not differ before
# both bits, by how the bits compare (c)
def Crit.minus_at_lookup(~V: Data, +ra: List<&2, U32>, +pa: Nat, +ea: Maybe<&2, V>, +za: Crit<V>, +oa: Crit<V>, +rb: List<&2, U32>, +pb: Nat, +eb: Maybe<&2, V>, +zb: Crit<V>, +ob: Crit<V>, +la: Nat, +lb: Nat, +q: List<&2, U32>, c: Cmp) -> {Nat.cmp(pa, pb) == c: Cmp} -> {Crit.wf(~V, Crit.Fork{ra, pa, ea, za, oa}, la) == True{}: Bool} -> {Crit.wf(~V, Crit.Fork{rb, pb, eb, zb, ob}, lb) == True{}: Bool} -> {Bool.and(Crit.above(Key.diff(ra, rb), pa), Crit.above(Key.diff(ra, rb), pb)) == False{}: Bool} -> {Crit.lookup(V, Crit.minus(V, za, zb), q) == Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, zb, q)), None{}, Crit.lookup(V, za, q)): Maybe<&2, V>} -> {Crit.lookup(V, Crit.minus(V, oa, ob), q) == Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, ob, q)), None{}, Crit.lookup(V, oa, q)): Maybe<&2, V>} -> {Crit.lookup(V, Crit.minus(V, za, Crit.Fork{rb, pb, eb, zb, ob}), q) == Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), None{}, Crit.lookup(V, za, q)): Maybe<&2, V>} -> {Crit.lookup(V, Crit.minus(V, oa, Crit.Fork{rb, pb, eb, zb, ob}), q) == Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), None{}, Crit.lookup(V, oa, q)): Maybe<&2, V>} -> {Crit.lookup(V, Crit.minus(V, Crit.Fork{ra, pa, ea, za, oa}, zb), q) == Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, zb, q)), None{}, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q)): Maybe<&2, V>} -> {Crit.lookup(V, Crit.minus(V, Crit.Fork{ra, pa, ea, za, oa}, ob), q) == Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, ob, q)), None{}, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q)): Maybe<&2, V>} -> {
  Crit.lookup(V, Crit.minus.at(V, c, ra, pa, ea, rb, pb, eb, u2 => Crit.minus(V, za, zb), u2 => Crit.minus(V, oa, ob), u2 => Crit.minus(V, za, Crit.Fork{rb, pb, eb, zb, ob}), u2 => Crit.minus(V, oa, Crit.Fork{rb, pb, eb, zb, ob}), u2 => Crit.minus(V, Crit.Fork{ra, pa, ea, za, oa}, zb), u2 => Crit.minus(V, Crit.Fork{ra, pa, ea, za, oa}, ob), za, oa), q) == Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), None{}, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q)): Maybe<&2, V>
}:
  match c:
    case EQ{}:
      hc => ha => hb => +hn => i1 => i2 => i3 => i4 => i5 => i6 =>
        +eqp = Crit.cmp_eq(pa, pb)(hc)
        Crit.minus_eq(~V, ra, pa, ea, za, oa, rb, pb, eb, zb, ob, la, lb, q)(ha)(hb)(eqp)(
          Crit.above_eq(Key.diff(ra, rb), pa)(Equal.trans(Bool, Bool.and(Crit.above(Key.diff(ra, rb), pa), Crit.above(Key.diff(ra, rb), pa)), Bool.and(Crit.above(Key.diff(ra, rb), pa), Crit.above(Key.diff(ra, rb), pb)), False{}, Equal.cong(Nat, Bool, t => Bool.and(Crit.above(Key.diff(ra, rb), pa), Crit.above(Key.diff(ra, rb), t)), pa, pb, eqp), hn))
        )(i1)(i2)
    case LT{}:
      +hc => ha => hb => hn => i1 => i2 => i3 => i4 => i5 => i6 => Crit.minus_lt(~V, ra, pa, ea, za, oa, rb, pb, eb, zb, ob, la, lb, q)(ha)(hb)(Crit.cmp_lt(pa, pb)(hc))(
        Crit.above_lt_left(Key.diff(ra, rb), pa, pb)(hn)(Crit.cmp_lt(pa, pb)(hc))
      )(i3)(i4)
    case GT{}:
      +hc => ha => hb => hn => i1 => i2 => i3 => i4 => i5 => i6 => Crit.minus_gt(~V, ra, pa, ea, za, oa, rb, pb, eb, zb, ob, la, lb, q)(ha)(hb)(Crit.cmp_gt(pa, pb)(hc))(
        Crit.above_lt_right(Key.diff(ra, rb), pa, pb)(hn)(Crit.cmp_gt(pa, pb)(hc))
      )(i5)(i6)

# the difference of two well formed maps holds what a holds under the keys
# that b lacks
def Crit.minus_go_lookup(~V: Data, +a: Crit<V>, +b: Crit<V>, +la: Nat, +lb: Nat, +q: List<&2, U32>) -> {Crit.wf(~V, a, la) == True{}: Bool} -> {
  Crit.wf(~V, b, lb) == True{}: Bool
} -> {Crit.lookup(V, Crit.minus(V, a, b), q) == Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, b, q)), None{}, Crit.lookup(V, a, q)): Maybe<&2, V>}:
  match a b:
    case Crit.Tip{} Crit.Tip{}:
      ha => hb => Equal.sym(Maybe<&2, V>, Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, Crit.Tip{}, q)), None{}, None{}), None{}, Crit.pick_none(V, Maybe.is_some(&2, V, Crit.lookup(V, Crit.Tip{}, q))))
    case Crit.Tip{} Crit.Leaf{+k2, +w2}:
      ha => hb => Equal.sym(Maybe<&2, V>, Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, Crit.Leaf{k2, w2}, q)), None{}, None{}), None{}, Crit.pick_none(V, Maybe.is_some(&2, V, Crit.lookup(V, Crit.Leaf{k2, w2}, q))))
    case Crit.Tip{} Crit.Fork{+r2, +p2, +e2, +z2, +o2}:
      ha => hb => Equal.sym(Maybe<&2, V>, Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{r2, p2, e2, z2, o2}, q)), None{}, None{}), None{}, Crit.pick_none(V, Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{r2, p2, e2, z2, o2}, q))))
    case Crit.Leaf{k, v} Crit.Tip{}:
      ha => hb => {==}
    case Crit.Fork{ra, pa, ea, za, oa} Crit.Tip{}:
      ha => hb => {==}
    case Crit.Leaf{+k, +v} Crit.Leaf{+k2, +w}:
      ha => hb => Crit.leaf_minus(~V, k, v, Crit.Leaf{k2, w}, lb, q)(hb)
    case Crit.Leaf{+k, +v} Crit.Fork{+rb, +pb, +eb, +zb, +ob}:
      ha => hb => Crit.leaf_minus(~V, k, v, Crit.Fork{rb, pb, eb, zb, ob}, lb, q)(hb)
    case Crit.Fork{+ra, +pa, +ea, +za, +oa} Crit.Leaf{+k, +w}:
      ha => hb => Equal.trans(
        Maybe<&2, V>,
        Crit.lookup(V, Crit.drop(V, Crit.Fork{ra, pa, ea, za, oa}, k), q),
        Bool.pick(Maybe<&2, V>, Key.is_eq(q, k), None{}, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q)),
        Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, Crit.Leaf{k, w}, q)), None{}, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q)),
        Crit.drop_lookup.at(~V, Crit.Fork{ra, pa, ea, za, oa}, la, k, q)(ha),
        Equal.cong(Bool, Maybe<&2, V>, t => Bool.pick(Maybe<&2, V>, t, None{}, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q)), Key.is_eq(q, k), Maybe.is_some(&2, V, Crit.lookup(V, Crit.Leaf{k, w}, q)), Equal.sym(Bool, Maybe.is_some(&2, V, Crit.lookup(V, Crit.Leaf{k, w}, q)), Key.is_eq(q, k), Crit.is_some_when(V, k, q, w)))
      )
    case Crit.Fork{+ra, +pa, +ea, +za, +oa} Crit.Fork{+rb, +pb, +eb, +zb, +ob}:
      +ha => +hb => Shared.Bool.when_cases(
        Crit<V>,
        t => {Crit.lookup(V, t, q) == Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, q)), None{}, Crit.lookup(V, Crit.Fork{ra, pa, ea, za, oa}, q)): Maybe<&2, V>},
        Bool.and(Crit.above(Key.diff(ra, rb), pa), Crit.above(Key.diff(ra, rb), pb)),
        u => Crit.Fork{ra, pa, ea, za, oa},
        u => Crit.minus.at(V, Nat.cmp(pa, pb), ra, pa, ea, rb, pb, eb, u2 => Crit.minus(V, za, zb), u2 => Crit.minus(V, oa, ob), u2 => Crit.minus(V, za, Crit.Fork{rb, pb, eb, zb, ob}), u2 => Crit.minus(V, oa, Crit.Fork{rb, pb, eb, zb, ob}), u2 => Crit.minus(V, Crit.Fork{ra, pa, ea, za, oa}, zb), u2 => Crit.minus(V, Crit.Fork{ra, pa, ea, za, oa}, ob), za, oa),
        +t => Crit.minus_both(~V, ra, pa, ea, za, oa, rb, pb, eb, zb, ob, la, lb, q)(ha)(hb)(t),
        +t => Crit.minus_at_lookup(~V, ra, pa, ea, za, oa, rb, pb, eb, zb, ob, la, lb, q, Nat.cmp(pa, pb))({==})(ha)(hb)(t)(
          Crit.minus_go_lookup(~V, za, zb, 1n+pa, 1n+pb, q)(Crit.wf.wf_z(~V, ra, pa, ea, za, oa, la)(ha))(Crit.wf.wf_z(~V, rb, pb, eb, zb, ob, lb)(hb))
        )(Crit.minus_go_lookup(~V, oa, ob, 1n+pa, 1n+pb, q)(Crit.wf.wf_o(~V, ra, pa, ea, za, oa, la)(ha))(Crit.wf.wf_o(~V, rb, pb, eb, zb, ob, lb)(hb)))(
          Crit.minus_go_lookup(~V, za, b, 1n+pa, lb, q)(Crit.wf.wf_z(~V, ra, pa, ea, za, oa, la)(ha))(hb)
        )(Crit.minus_go_lookup(~V, oa, b, 1n+pa, lb, q)(Crit.wf.wf_o(~V, ra, pa, ea, za, oa, la)(ha))(hb))(
          Crit.minus_go_lookup(~V, a, zb, la, 1n+pb, q)(ha)(Crit.wf.wf_z(~V, rb, pb, eb, zb, ob, lb)(hb))
        )(Crit.minus_go_lookup(~V, a, ob, la, 1n+pb, q)(ha)(Crit.wf.wf_o(~V, rb, pb, eb, zb, ob, lb)(hb)))
      )

# a difference holds what a holds under the keys that b lacks
law Crit.minus_lookup:
  for ~V: Data
  for a: Crit<V>
  for b: Crit<V>
  for q: List<&2, U32>
  {Crit.wf(~V, a, 0n) == True{}: Bool} -> {Crit.wf(~V, b, 0n) == True{}: Bool} -> {
    Crit.lookup(V, Crit.minus(V, a, b), q) == Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, b, q)), None{}, Crit.lookup(V, a, q)): Maybe<&2, V>
  }

def Crit.minus_lookup(ty, a, b, q):
  ha => hb => Crit.minus_go_lookup(~ty, a, b, 0n, 0n, q)(ha)(hb)

# a read of a well formed map is its clear read, with k used more than once
def Crit.get_lookup.at(~ty: Data, +m: Crit<ty>, +k: List<&2, U32>) -> {Crit.wf(~ty, m, 0n) == True{}: Bool} -> {
  Crit.get(ty, m, k) == Crit.lookup(ty, m, k): Maybe<&2, ty>
}:
  h => Equal.trans(
    Maybe<&2, ty>,
    Crit.get(ty, m, k),
    Crit.find(ty, m, 0n, Key.bits(k), k),
    Crit.lookup(ty, m, k),
    Crit.get_is_find(ty, m, k),
    (
      %Shared.List.drop_zero(&2, Bool, Key.bits(k)): {
        Crit.find(ty, m, 0n, _, k) == Crit.lookup(ty, m, k): Maybe<&2, ty>
      }
      Crit.find_lookup(~ty, m, 0n, 0n, k)(h)({==})
    )
  )

# a read of a well formed map is its clear read
law Crit.get_lookup:
  for ~V: Data
  for m: Crit<V>
  for k: List<&2, U32>
  {Crit.wf(~V, m, 0n) == True{}: Bool} -> {Crit.get(V, m, k) == Crit.lookup(V, m, k): Maybe<&2, V>}

def Crit.get_lookup(ty, m, k):
  Crit.get_lookup.at(~ty, m, k)

# the end e of a fork with rep r is an entry of x, or there is none
def Crit.sub_end(-V: Data, +r: List<&2, U32>, e: Maybe<&2, V>, +x: Crit<V>) -> Data:
  match e:
    case None{}:
      Unit
    case Some{v}:
      {Crit.lookup(V, x, r) == Some{v}: Maybe<&2, V>}

# each entry of m is an entry of x: a proof of it is data, read at any key
def Crit.sub(-V: Data, m: Crit<V>, +x: Crit<V>) -> Data:
  match m:
    case Crit.Tip{}:
      Unit
    case Crit.Leaf{k, v}:
      {Crit.lookup(V, x, k) == Some{v}: Maybe<&2, V>}
    case Crit.Fork{+r, p, e, z, o}:
      Sigma<&2, &2, Crit.sub_end(V, r, e, x), _ => Sigma<&2, &2, Crit.sub(V, z, x), _ => Crit.sub(V, o, x)>>

# each entry of the list es is an entry of x
def Crit.agrees(-V: Data, es: List<&2, Bind<V>>, +x: Crit<V>) -> Data:
  match es:
    case Nil{}:
      Unit
    case Con{Bind{k, v}, r}:
      Sigma<&2, &2, {Crit.lookup(V, x, k) == Some{v}: Maybe<&2, V>}, _ => Crit.agrees(V, r, x)>

# Crit.sub of a fork: its end
def Crit.sub.e(-V: Data, -r: List<&2, U32>, -p: Nat, -e: Maybe<&2, V>, -z: Crit<V>, -o: Crit<V>, -x: Crit<V>, c: Crit.sub(V, Crit.Fork{r, p, e, z, o}, x)) -> Crit.sub_end(V, r, e, x):
  (ce, czo) = c
  ce

# Crit.sub of a fork: its zero side
def Crit.sub.z(-V: Data, -r: List<&2, U32>, -p: Nat, -e: Maybe<&2, V>, -z: Crit<V>, -o: Crit<V>, -x: Crit<V>, c: Crit.sub(V, Crit.Fork{r, p, e, z, o}, x)) -> Crit.sub(V, z, x):
  (ce, czo) = c
  (cz, co) = czo
  cz

# Crit.sub of a fork: its one side
def Crit.sub.o(-V: Data, -r: List<&2, U32>, -p: Nat, -e: Maybe<&2, V>, -z: Crit<V>, -o: Crit<V>, -x: Crit<V>, c: Crit.sub(V, Crit.Fork{r, p, e, z, o}, x)) -> Crit.sub(V, o, x):
  (ce, czo) = c
  (cz, co) = czo
  co

# Crit.agrees of a list with a head: the head
def Crit.agrees.hd(-V: Data, -k: List<&2, U32>, -v: V, -r: List<&2, Bind<V>>, -x: Crit<V>, c: Crit.agrees(V, Bind{k, v} <> r, x)) -> {
  Crit.lookup(V, x, k) == Some{v}: Maybe<&2, V>
}:
  (h, t) = c
  h

# Crit.agrees of a list with a head: the rest
def Crit.agrees.tl(-V: Data, -k: List<&2, U32>, -v: V, -r: List<&2, Bind<V>>, -x: Crit<V>, c: Crit.agrees(V, Bind{k, v} <> r, x)) -> Crit.agrees(V, r, x):
  (h, t) = c
  t

# the value of an entry whose key is k, when the test of r and k is b
def Crit.pick_end.at(-V: Data, +r: List<&2, U32>, -w: V, +x: Crit<V>, +k: List<&2, U32>, -v: V, b: Bool) -> {Key.is_eq(r, k) == b: Bool} -> {
  Crit.lookup(V, x, r) == Some{w}: Maybe<&2, V>
} -> {Shared.Maybe.when(V, b, u => Some{w}) == Some{v}: Maybe<&2, V>} -> {Crit.lookup(V, x, k) == Some{v}: Maybe<&2, V>}:
  match b:
    case True{}:
      eb => cw => hw =>
        %Key.is_eq_sound(r, k)(eb): {Crit.lookup(V, x, _) == Some{v}: Maybe<&2, V>}
        Equal.trans(Maybe<&2, V>, Crit.lookup(V, x, r), Some{w}, Some{v}, cw, hw)
    case False{}:
      eb => cw => hw => Empty.absurd({Crit.lookup(V, x, k) == Some{v}: Maybe<&2, V>}, Shared.Maybe.none_ne_some(V, v, hw))

# the end of a fork, read at k, that is some v is an entry of x
def Crit.pick_end(-V: Data, +r: List<&2, U32>, e: Maybe<&2, V>, +x: Crit<V>, +k: List<&2, U32>, -v: V) -> Crit.sub_end(V, r, e, x) -> {
  Crit.ended(V, r, e, k) == Some{v}: Maybe<&2, V>
} -> {Crit.lookup(V, x, k) == Some{v}: Maybe<&2, V>}:
  match e:
    case None{}:
      c => h => Empty.absurd({Crit.lookup(V, x, k) == Some{v}: Maybe<&2, V>}, Shared.Maybe.none_ne_some(V, v, h))
    case Some{w}:
      c => h => Crit.pick_end.at(V, r, w, x, k, v, Key.is_eq(r, k))({==})(c)(h)

# a choice of three that is some v is one of them
def Crit.or3_some(-V: Data, -T: Type, a: Maybe<&2, V>, b: Maybe<&2, V>, -c: Maybe<&2, V>, -v: V) -> ({a == Some{v}: Maybe<&2, V>} -> T) -> (
  {b == Some{v}: Maybe<&2, V>} -> T
) -> ({c == Some{v}: Maybe<&2, V>} -> T) -> {Maybe.or(&2, V, a, Maybe.or(&2, V, b, c)) == Some{v}: Maybe<&2, V>} -> T:
  match a b:
    case Some{x} y:
      f1 => f2 => f3 => h => f1(h)
    case None{} Some{y}:
      f1 => f2 => f3 => h => f2(h)
    case None{} None{}:
      f1 => f2 => f3 => h => f3(h)

# an entry of m is an entry of x, when each entry of m is
def Crit.sub_pick(-V: Data, m: Crit<V>, +x: Crit<V>, +k: List<&2, U32>, -v: V) -> Crit.sub(V, m, x) -> {Crit.lookup(V, m, k) == Some{v}: Maybe<&2, V>} -> {
  Crit.lookup(V, x, k) == Some{v}: Maybe<&2, V>
}:
  match m:
    case Crit.Tip{}:
      c => h => Empty.absurd({Crit.lookup(V, x, k) == Some{v}: Maybe<&2, V>}, Shared.Maybe.none_ne_some(V, v, h))
    case Crit.Leaf{+k2, w}:
      c => h => Crit.pick_end.at(V, k2, w, x, k, v, Key.is_eq(k2, k))({==})(c)(h)
    case Crit.Fork{+r, +p, +e, +z, +o}:
      +c => Crit.or3_some(V, {Crit.lookup(V, x, k) == Some{v}: Maybe<&2, V>}, Crit.ended(V, r, e, k), Crit.lookup(V, z, k), Crit.lookup(V, o, k), v)(
        h => Crit.pick_end(V, r, e, x, k, v)(Crit.sub.e(V, r, p, e, z, o, x, c))(h)
      )(h => Crit.sub_pick(V, z, x, k, v)(Crit.sub.z(V, r, p, e, z, o, x, c))(h))(h => Crit.sub_pick(V, o, x, k, v)(Crit.sub.o(V, r, p, e, z, o, x, c))(h))

# a side is the same as itself
def Crit.mis_refl(m: Maybe<&2, Bool>) -> {Shared.Maybe.is_eq(~Bool, ~Shared.Bool.is_eq, m, m) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{+value}:
      match value:
        case False{}:
          {==}
        case True{}:
          {==}

# the first key of a map with an entry does not depend on the default
def Crit.rep_irr(-V: Data, m: Crit<V>, -d1: List<&2, U32>, -d2: List<&2, U32>) -> {Crit.is_tip(V, m) == False{}: Bool} -> {
  Crit.rep(V, m, d1) == Crit.rep(V, m, d2): List<&2, U32>
}:
  match m:
    case Crit.Tip{}:
      h => Empty.absurd({d1 == d2: List<&2, U32>}, Shared.Bool.true_ne_false(h))
    case Crit.Leaf{k, v}:
      h => {==}
    case Crit.Fork{r, p, e, z, o}:
      h => {==}

# a choice whose first is some is some
def Crit.or_some_left(-V: Data, a: Maybe<&2, V>, -b: Maybe<&2, V>) -> {Maybe.is_some(&2, V, a) == True{}: Bool} -> {Maybe.is_some(&2, V, Maybe.or(&2, V, a, b)) == True{}: Bool}:
  match a:
    case None{}:
      h => Empty.absurd({Maybe.is_some(&2, V, b) == True{}: Bool}, Shared.Bool.false_ne_true(h))
    case Some{x}:
      h => {==}

# a fork of two entries at least, with no end, has a one side
def Crit.shape_none_o(-V: Data, z: Crit<V>, o: Crit<V>) -> {Crit.shape(V, None{}, z, o) == True{}: Bool} -> {Crit.is_tip(V, o) == False{}: Bool}:
  match z o:
    case Crit.Tip{} Crit.Tip{}:
      h => Empty.absurd({True{} == False{}: Bool}, Shared.Bool.false_ne_true(h))
    case Crit.Tip{} Crit.Leaf{k2, v2}:
      h => Empty.absurd({False{} == False{}: Bool}, Shared.Bool.false_ne_true(h))
    case Crit.Tip{} Crit.Fork{r2, p2, e2, z2, o2}:
      h => Empty.absurd({False{} == False{}: Bool}, Shared.Bool.false_ne_true(h))
    case Crit.Leaf{k, v} Crit.Tip{}:
      h => Empty.absurd({True{} == False{}: Bool}, Shared.Bool.false_ne_true(h))
    case Crit.Fork{r, p, e, z1, o1} Crit.Tip{}:
      h => Empty.absurd({True{} == False{}: Bool}, Shared.Bool.false_ne_true(h))
    case Crit.Leaf{k, v} Crit.Leaf{k2, v2}:
      h => {==}
    case Crit.Leaf{k, v} Crit.Fork{r2, p2, e2, z2, o2}:
      h => {==}
    case Crit.Fork{r, p, e, z1, o1} Crit.Leaf{k2, v2}:
      h => {==}
    case Crit.Fork{r, p, e, z1, o1} Crit.Fork{r2, p2, e2, z2, o2}:
      h => {==}

# a fork of an end and no zero side has a one side
def Crit.shape_some_o(-V: Data, -v: V, o: Crit<V>) -> {Crit.shape(V, Some{v}, Crit.Tip{}, o) == True{}: Bool} -> {Crit.is_tip(V, o) == False{}: Bool}:
  match o:
    case Crit.Tip{}:
      h => Empty.absurd({True{} == False{}: Bool}, Shared.Bool.false_ne_true(h))
    case Crit.Leaf{k, w}:
      h => {==}
    case Crit.Fork{r, p, e, z, o1}:
      h => {==}

# a key of pos bits has no side at pos
def Crit.side_len(+r: List<&2, U32>, +pos: Nat) -> {Nat.is_eq(List.length(&2, Bool, Key.bits(r)), pos) == True{}: Bool} -> {Key.side(r, pos) == None{}: Maybe<&2, Bool>}:
  h => Crit.side_drop(r, pos, [])((
    %Shared.Nat.is_eq_sound(List.length(&2, Bool, Key.bits(r)), pos)(h): {List.drop(&2, Bool, Key.bits(r), _) == []: List<&2, Bool>}
    Crit.drop_length(Key.bits(r))
  ))

# Crit.rep_in at a fork, by its end e; ih is the claim for its zero side
def Crit.rep_in.fork(~V: Data, +rep: List<&2, U32>, +pos: Nat, e: Maybe<&2, V>, +z: Crit<V>, +o: Crit<V>, +lo: Nat, ih: {Crit.wf(~V, z, 1n+pos) == True{}: Bool} -> {
  Crit.is_tip(V, z) == False{}: Bool
} -> {Maybe.is_some(&2, V, Crit.lookup(V, z, Crit.rep(V, z, rep))) == True{}: Bool}) -> {Crit.wf(~V, Crit.Fork{rep, pos, e, z, o}, lo) == True{}: Bool} -> {
  Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, rep)) == True{}: Bool
}:
  match e:
    case Some{v}:
      h =>
        %Equal.sym(Bool, Key.is_eq(rep, rep), True{}, Key.is_eq_refl(rep)): {
          Maybe.is_some(&2, V, Maybe.or(&2, V, Shared.Maybe.when(V, _, u => Some{v}), Maybe.or(&2, V, Crit.lookup(V, z, rep), Crit.lookup(V, o, rep)))) == True{}: Bool
        }
        {==}
    case None{}:
      +h =>
        %Equal.sym(List<&2, U32>, rep, Crit.rep(V, z, rep), Key.is_eq_sound(rep, Crit.rep(V, z, rep))(Crit.wf.rep_ok(~V, rep, pos, None{}, z, o, lo)(h))): {
          Maybe.is_some(&2, V, Maybe.or(&2, V, Crit.lookup(V, z, _), Crit.lookup(V, o, _))) == True{}: Bool
        }
        Crit.or_some_left(V, Crit.lookup(V, z, Crit.rep(V, z, rep)), Crit.lookup(V, o, Crit.rep(V, z, rep)))(
          ih(Crit.wf.wf_z(~V, rep, pos, None{}, z, o, lo)(h))(Crit.shape_none_z(V, z, o)(Crit.wf.shape(~V, rep, pos, None{}, z, o, lo)(h)))
        )

# the first key of a well formed map with an entry is a key of it
def Crit.rep_in(~V: Data, m: Crit<V>, +lo: Nat, +d: List<&2, U32>) -> {Crit.wf(~V, m, lo) == True{}: Bool} -> {Crit.is_tip(V, m) == False{}: Bool} -> {
  Maybe.is_some(&2, V, Crit.lookup(V, m, Crit.rep(V, m, d))) == True{}: Bool
}:
  match m:
    case Crit.Tip{}:
      h => t => Empty.absurd({Maybe.is_some(&2, V, None{}) == True{}: Bool}, Shared.Bool.true_ne_false(t))
    case Crit.Leaf{+k, v}:
      h => t =>
        %Equal.sym(Bool, Key.is_eq(k, k), True{}, Key.is_eq_refl(k)): {Maybe.is_some(&2, V, Shared.Maybe.when(V, _, u => Some{v})) == True{}: Bool}
        {==}
    case Crit.Fork{+r, +p, +e, +z, +o}:
      h => t => Crit.rep_in.fork(~V, r, p, e, z, o, lo, w => nt => Crit.rep_in(~V, z, 1n+p, r)(w)(nt))(h)

# Crit.sub_up and Crit.sub_down for the end of a fork
def Crit.sub_end_up(~V: Data, +r3: List<&2, U32>, e3: Maybe<&2, V>, +rep: List<&2, U32>, +pos: Nat, +e: Maybe<&2, V>, +z: Crit<V>, +o: Crit<V>, +lo: Nat, +r2: List<&2, U32>, +b: Bool) -> Crit.sub_end(V, r3, e3, Bool.pick(Crit<V>, b, o, z)) -> {
  Bool.or(Maybe.is_none(&2, V, e3), Place.has(Place{r2, pos, b}, r3)) == True{}: Bool
} -> {Crit.wf(~V, Crit.Fork{rep, pos, e, z, o}, lo) == True{}: Bool} -> Crit.sub_end(V, r3, e3, Crit.Fork{rep, pos, e, z, o}):
  match e3:
    case None{}:
      c => a => h => Unit{}
    case Some{w}:
      c => a => h => Equal.trans(Maybe<&2, V>, Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, r3), Crit.lookup(V, Bool.pick(Crit<V>, b, o, z), r3), Some{w}, Crit.route_side(~V, rep, pos, e, z, o, lo, r3, b)(h)(Place.has_side(r2, pos, b, r3)(a)), c)

def Crit.sub_end_down(~V: Data, +r3: List<&2, U32>, e3: Maybe<&2, V>, +rep: List<&2, U32>, +pos: Nat, +e: Maybe<&2, V>, +z: Crit<V>, +o: Crit<V>, +lo: Nat, +r2: List<&2, U32>, +b: Bool) -> Crit.sub_end(V, r3, e3, Crit.Fork{rep, pos, e, z, o}) -> {
  Bool.or(Maybe.is_none(&2, V, e3), Place.has(Place{r2, pos, b}, r3)) == True{}: Bool
} -> {Crit.wf(~V, Crit.Fork{rep, pos, e, z, o}, lo) == True{}: Bool} -> Crit.sub_end(V, r3, e3, Bool.pick(Crit<V>, b, o, z)):
  match e3:
    case None{}:
      c => a => h => Unit{}
    case Some{w}:
      c => a => h => Equal.trans(Maybe<&2, V>, Crit.lookup(V, Bool.pick(Crit<V>, b, o, z), r3), Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, r3), Some{w}, Equal.sym(Maybe<&2, V>, Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, r3), Crit.lookup(V, Bool.pick(Crit<V>, b, o, z), r3), Crit.route_side(~V, rep, pos, e, z, o, lo, r3, b)(h)(Place.has_side(r2, pos, b, r3)(a))), c)

# the entries of m that are entries of a side b of a well formed fork, whose
# keys have the side b at its bit, are entries of the fork
def Crit.sub_up(~V: Data, m: Crit<V>, +rep: List<&2, U32>, +pos: Nat, +e: Maybe<&2, V>, +z: Crit<V>, +o: Crit<V>, +lo: Nat, +r2: List<&2, U32>, +b: Bool) -> Crit.sub(V, m, Bool.pick(Crit<V>, b, o, z)) -> {
  Crit.all(~V, ~Place, ~Place.has, m, Place{r2, pos, b}) == True{}: Bool
} -> {Crit.wf(~V, Crit.Fork{rep, pos, e, z, o}, lo) == True{}: Bool} -> Crit.sub(V, m, Crit.Fork{rep, pos, e, z, o}):
  match m:
    case Crit.Tip{}:
      c => a => h => Unit{}
    case Crit.Leaf{+k, v}:
      c => a => h => Equal.trans(Maybe<&2, V>, Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k), Crit.lookup(V, Bool.pick(Crit<V>, b, o, z), k), Some{v}, Crit.route_side(~V, rep, pos, e, z, o, lo, k, b)(h)(Place.has_side(r2, pos, b, k)(a)), c)
    case Crit.Fork{+r3, +p3, +e3, +z3, +o3}:
      +c => +a => +h => (
        Crit.sub_end_up(~V, r3, e3, rep, pos, e, z, o, lo, r2, b)(Crit.sub.e(V, r3, p3, e3, z3, o3, Bool.pick(Crit<V>, b, o, z), c))(Crit.all.hit(~V, ~Place, ~Place.has, r3, p3, e3, z3, o3, Place{r2, pos, b})(a))(h),
        (
          Crit.sub_up(~V, z3, rep, pos, e, z, o, lo, r2, b)(Crit.sub.z(V, r3, p3, e3, z3, o3, Bool.pick(Crit<V>, b, o, z), c))(Crit.all.z(~V, ~Place, ~Place.has, r3, p3, e3, z3, o3, Place{r2, pos, b})(a))(h),
          Crit.sub_up(~V, o3, rep, pos, e, z, o, lo, r2, b)(Crit.sub.o(V, r3, p3, e3, z3, o3, Bool.pick(Crit<V>, b, o, z), c))(Crit.all.o(~V, ~Place, ~Place.has, r3, p3, e3, z3, o3, Place{r2, pos, b})(a))(h)
        )
      )

# the entries of m that are entries of a well formed fork, whose keys have
# the side b at its bit, are entries of its side b
def Crit.sub_down(~V: Data, m: Crit<V>, +rep: List<&2, U32>, +pos: Nat, +e: Maybe<&2, V>, +z: Crit<V>, +o: Crit<V>, +lo: Nat, +r2: List<&2, U32>, +b: Bool) -> Crit.sub(V, m, Crit.Fork{rep, pos, e, z, o}) -> {
  Crit.all(~V, ~Place, ~Place.has, m, Place{r2, pos, b}) == True{}: Bool
} -> {Crit.wf(~V, Crit.Fork{rep, pos, e, z, o}, lo) == True{}: Bool} -> Crit.sub(V, m, Bool.pick(Crit<V>, b, o, z)):
  match m:
    case Crit.Tip{}:
      c => a => h => Unit{}
    case Crit.Leaf{+k, v}:
      c => a => h => Equal.trans(Maybe<&2, V>, Crit.lookup(V, Bool.pick(Crit<V>, b, o, z), k), Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k), Some{v}, Equal.sym(Maybe<&2, V>, Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k), Crit.lookup(V, Bool.pick(Crit<V>, b, o, z), k), Crit.route_side(~V, rep, pos, e, z, o, lo, k, b)(h)(Place.has_side(r2, pos, b, k)(a))), c)
    case Crit.Fork{+r3, +p3, +e3, +z3, +o3}:
      +c => +a => +h => (
        Crit.sub_end_down(~V, r3, e3, rep, pos, e, z, o, lo, r2, b)(Crit.sub.e(V, r3, p3, e3, z3, o3, Crit.Fork{rep, pos, e, z, o}, c))(Crit.all.hit(~V, ~Place, ~Place.has, r3, p3, e3, z3, o3, Place{r2, pos, b})(a))(h),
        (
          Crit.sub_down(~V, z3, rep, pos, e, z, o, lo, r2, b)(Crit.sub.z(V, r3, p3, e3, z3, o3, Crit.Fork{rep, pos, e, z, o}, c))(Crit.all.z(~V, ~Place, ~Place.has, r3, p3, e3, z3, o3, Place{r2, pos, b})(a))(h),
          Crit.sub_down(~V, o3, rep, pos, e, z, o, lo, r2, b)(Crit.sub.o(V, r3, p3, e3, z3, o3, Crit.Fork{rep, pos, e, z, o}, c))(Crit.all.o(~V, ~Place, ~Place.has, r3, p3, e3, z3, o3, Place{r2, pos, b})(a))(h)
        )
      )

# the end of a fork is an entry of it
def Crit.self_end(-V: Data, +r: List<&2, U32>, +p: Nat, e: Maybe<&2, V>, +z: Crit<V>, +o: Crit<V>) -> Crit.sub_end(V, r, e, Crit.Fork{r, p, e, z, o}):
  match e:
    case None{}:
      Unit{}
    case Some{v}:
      %Equal.sym(Bool, Key.is_eq(r, r), True{}, Key.is_eq_refl(r)): {
        Maybe.or(&2, V, Shared.Maybe.when(V, _, u => Some{v}), Maybe.or(&2, V, Crit.lookup(V, z, r), Crit.lookup(V, o, r))) == Some{v}: Maybe<&2, V>
      }
      {==}

# each entry of a well formed map is an entry of it
def Crit.sub_self(~V: Data, m: Crit<V>, +lo: Nat) -> {Crit.wf(~V, m, lo) == True{}: Bool} -> Crit.sub(V, m, m):
  match m:
    case Crit.Tip{}:
      h => Unit{}
    case Crit.Leaf{+k, +v}:
      h => Crit.leaf_self(V, k, v)
    case Crit.Fork{+r, +p, +e, +z, +o}:
      +h => (
        Crit.self_end(V, r, p, e, z, o),
        (
          Crit.sub_up(~V, z, r, p, e, z, o, lo, r, False{})(Crit.sub_self(~V, z, 1n+p)(Crit.wf.wf_z(~V, r, p, e, z, o, lo)(h)))(Crit.wf.all_z(~V, r, p, e, z, o, lo)(h))(h),
          Crit.sub_up(~V, o, r, p, e, z, o, lo, r, True{})(Crit.sub_self(~V, o, 1n+p)(Crit.wf.wf_o(~V, r, p, e, z, o, lo)(h)))(Crit.wf.all_o(~V, r, p, e, z, o, lo)(h))(h)
        )
      )

# the entries of m, before rest, are entries of x when those of m and rest are
def Crit.sub_to_list(-V: Data, m: Crit<V>, +rest: List<&2, Bind<V>>, +x: Crit<V>) -> Crit.sub(V, m, x) -> Crit.agrees(V, rest, x) -> Crit.agrees(V, Crit.entries.go(V, m, rest), x):
  match m:
    case Crit.Tip{}:
      c => ar => ar
    case Crit.Leaf{k, v}:
      c => ar => (c, ar)
    case Crit.Fork{+r, +p, None{}, +z, +o}:
      +c => ar => Crit.sub_to_list(V, z, Crit.entries.go(V, o, rest), x)(Crit.sub.z(V, r, p, None{}, z, o, x, c))(
        Crit.sub_to_list(V, o, rest, x)(Crit.sub.o(V, r, p, None{}, z, o, x, c))(ar)
      )
    case Crit.Fork{+r, +p, Some{+v}, +z, +o}:
      +c => ar => (
        Crit.sub.e(V, r, p, Some{v}, z, o, x, c),
        Crit.sub_to_list(V, z, Crit.entries.go(V, o, rest), x)(Crit.sub.z(V, r, p, Some{v}, z, o, x, c))(
          Crit.sub_to_list(V, o, rest, x)(Crit.sub.o(V, r, p, Some{v}, z, o, x, c))(ar)
        )
      )

# the entries after those of m are entries of x when all are
def Crit.agrees_rest(-V: Data, m: Crit<V>, +rest: List<&2, Bind<V>>, +x: Crit<V>) -> Crit.agrees(V, Crit.entries.go(V, m, rest), x) -> Crit.agrees(V, rest, x):
  match m:
    case Crit.Tip{}:
      c => c
    case Crit.Leaf{k, v}:
      c => Crit.agrees.tl(V, k, v, rest, x, c)
    case Crit.Fork{r, p, None{}, +z, +o}:
      c => Crit.agrees_rest(V, o, rest, x)(Crit.agrees_rest(V, z, Crit.entries.go(V, o, rest), x)(c))
    case Crit.Fork{+r, p, Some{+v}, +z, +o}:
      c => Crit.agrees_rest(V, o, rest, x)(Crit.agrees_rest(V, z, Crit.entries.go(V, o, rest), x)(Crit.agrees.tl(V, r, v, Crit.entries.go(V, z, Crit.entries.go(V, o, rest)), x, c)))

# the entries of m are entries of x when its entries before rest are
def Crit.sub_of_list(-V: Data, m: Crit<V>, +rest: List<&2, Bind<V>>, +x: Crit<V>) -> Crit.agrees(V, Crit.entries.go(V, m, rest), x) -> Crit.sub(V, m, x):
  match m:
    case Crit.Tip{}:
      c => Unit{}
    case Crit.Leaf{k, v}:
      c => Crit.agrees.hd(V, k, v, rest, x, c)
    case Crit.Fork{r, p, None{}, +z, +o}:
      +c => (
        Unit{},
        (
          Crit.sub_of_list(V, z, Crit.entries.go(V, o, rest), x)(c),
          Crit.sub_of_list(V, o, rest, x)(Crit.agrees_rest(V, z, Crit.entries.go(V, o, rest), x)(c))
        )
      )
    case Crit.Fork{+r, p, Some{+v}, +z, +o}:
      +c => (
        Crit.agrees.hd(V, r, v, Crit.entries.go(V, z, Crit.entries.go(V, o, rest)), x, c),
        (
          Crit.sub_of_list(V, z, Crit.entries.go(V, o, rest), x)(Crit.agrees.tl(V, r, v, Crit.entries.go(V, z, Crit.entries.go(V, o, rest)), x, c)),
          Crit.sub_of_list(V, o, rest, x)(Crit.agrees_rest(V, z, Crit.entries.go(V, o, rest), x)(Crit.agrees.tl(V, r, v, Crit.entries.go(V, z, Crit.entries.go(V, o, rest)), x, c)))
        )
      )

# the entries of a are entries of a well formed map b with the same entries
def Crit.sub_of_entries(~V: Data, +a: Crit<V>, +b: Crit<V>, +lb: Nat) -> {Crit.wf(~V, b, lb) == True{}: Bool} -> {Crit.entries(V, a) == Crit.entries(V, b): List<&2, Bind<V>>} -> Crit.sub(V, a, b):
  h => en => Crit.sub_of_list(V, a, [], b)((
    %Equal.sym(List<&2, Bind<V>>, Crit.entries(V, a), Crit.entries(V, b), en): Crit.agrees(V, _, b)
    Crit.sub_to_list(V, b, [], b)(Crit.sub_self(~V, b, lb)(h))(Unit{})
  ))

# the sides of two keys at pos differ, once each is known
def Crit.mis_of(+q1: List<&2, U32>, +q2: List<&2, U32>, +pos: Nat, +b1: Maybe<&2, Bool>, +b2: Maybe<&2, Bool>) -> {Key.side(q1, pos) == b1: Maybe<&2, Bool>} -> {Key.side(q2, pos) == b2: Maybe<&2, Bool>} -> {
  Shared.Maybe.is_eq(~Bool, ~Shared.Bool.is_eq, b1, b2) == False{}: Bool
} -> {Shared.Maybe.is_eq(~Bool, ~Shared.Bool.is_eq, Key.side(q1, pos), Key.side(q2, pos)) == False{}: Bool}:
  e1 => e2 => h =>
    %Equal.sym(Maybe<&2, Bool>, Key.side(q1, pos), b1, e1): {Shared.Maybe.is_eq(~Bool, ~Shared.Bool.is_eq, _, Key.side(q2, pos)) == False{}: Bool}
    %Equal.sym(Maybe<&2, Bool>, Key.side(q2, pos), b2, e2): {Shared.Maybe.is_eq(~Bool, ~Shared.Bool.is_eq, b1, _) == False{}: Bool}
    h

# the first key of a side b of a well formed fork, with an entry, has that side
def Crit.in_side_side(~V: Data, +rep: List<&2, U32>, +pos: Nat, +e: Maybe<&2, V>, +z: Crit<V>, +o: Crit<V>, +lo: Nat, b: Bool) -> {Crit.wf(~V, Crit.Fork{rep, pos, e, z, o}, lo) == True{}: Bool} -> {
  Crit.is_tip(V, Bool.pick(Crit<V>, b, o, z)) == False{}: Bool
} -> {Key.side(Crit.rep(V, Bool.pick(Crit<V>, b, o, z), rep), pos) == Some{b}: Maybe<&2, Bool>}:
  match b:
    case True{}:
      +h => nt => Place.has_side(rep, pos, True{}, Crit.rep(V, o, rep))(
        Crit.rep_pass(~V, ~Place, ~Place.has, o, 1n+pos, Place{rep, pos, True{}}, rep)(Crit.wf.wf_o(~V, rep, pos, e, z, o, lo)(h))(Crit.wf.all_o(~V, rep, pos, e, z, o, lo)(h))(nt)
      )
    case False{}:
      +h => nt => Place.has_side(rep, pos, False{}, Crit.rep(V, z, rep))(
        Crit.rep_pass(~V, ~Place, ~Place.has, z, 1n+pos, Place{rep, pos, False{}}, rep)(Crit.wf.wf_z(~V, rep, pos, e, z, o, lo)(h))(Crit.wf.all_z(~V, rep, pos, e, z, o, lo)(h))(nt)
      )

# the first key of a side b of a well formed fork, with an entry, is a key of
# the fork
def Crit.in_side_some(~V: Data, +rep: List<&2, U32>, +pos: Nat, +e: Maybe<&2, V>, +z: Crit<V>, +o: Crit<V>, +lo: Nat, b: Bool) -> {Crit.wf(~V, Crit.Fork{rep, pos, e, z, o}, lo) == True{}: Bool} -> {
  Crit.is_tip(V, Bool.pick(Crit<V>, b, o, z)) == False{}: Bool
} -> {Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, Crit.rep(V, Bool.pick(Crit<V>, b, o, z), rep))) == True{}: Bool}:
  match b:
    case True{}:
      +h => +nt => Equal.trans(
        Bool,
        Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, Crit.rep(V, o, rep))),
        Maybe.is_some(&2, V, Crit.lookup(V, o, Crit.rep(V, o, rep))),
        True{},
        Equal.cong(Maybe<&2, V>, Bool, x => Maybe.is_some(&2, V, x), Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, Crit.rep(V, o, rep)), Crit.lookup(V, o, Crit.rep(V, o, rep)), Crit.route_side(~V, rep, pos, e, z, o, lo, Crit.rep(V, o, rep), True{})(h)(Crit.in_side_side(~V, rep, pos, e, z, o, lo, True{})(h)(nt))),
        Crit.rep_in(~V, o, 1n+pos, rep)(Crit.wf.wf_o(~V, rep, pos, e, z, o, lo)(h))(nt)
      )
    case False{}:
      +h => +nt => Equal.trans(
        Bool,
        Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, Crit.rep(V, z, rep))),
        Maybe.is_some(&2, V, Crit.lookup(V, z, Crit.rep(V, z, rep))),
        True{},
        Equal.cong(Maybe<&2, V>, Bool, x => Maybe.is_some(&2, V, x), Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, Crit.rep(V, z, rep)), Crit.lookup(V, z, Crit.rep(V, z, rep)), Crit.route_side(~V, rep, pos, e, z, o, lo, Crit.rep(V, z, rep), False{})(h)(Crit.in_side_side(~V, rep, pos, e, z, o, lo, False{})(h)(nt))),
        Crit.rep_in(~V, z, 1n+pos, rep)(Crit.wf.wf_z(~V, rep, pos, e, z, o, lo)(h))(nt)
      )

# a well formed fork with an end has two keys whose sides at its bit differ
def Crit.two.some(~V: Data, +rep: List<&2, U32>, +pos: Nat, +v: V, z: Crit<V>, +o: Crit<V>, +lo: Nat, -T: Type) -> {
  Crit.wf(~V, Crit.Fork{rep, pos, Some{v}, z, o}, lo) == True{}: Bool
} -> (@q1: List<&2, U32> -> @q2: List<&2, U32> -> {Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rep, pos, Some{v}, z, o}, q1)) == True{}: Bool} -> {Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rep, pos, Some{v}, z, o}, q2)) == True{}: Bool} -> {Shared.Maybe.is_eq(~Bool, ~Shared.Bool.is_eq, Key.side(q1, pos), Key.side(q2, pos)) == False{}: Bool} -> T) -> T:
  match z:
    case Crit.Tip{}:
      +h => f =>
        +nt = Crit.shape_some_o(V, v, o)(Crit.wf.shape(~V, rep, pos, Some{v}, Crit.Tip{}, o, lo)(h))
        f(rep)(Crit.rep(V, o, rep))(Crit.rep_in(~V, Crit.Fork{rep, pos, Some{v}, Crit.Tip{}, o}, lo, [])(h)({==}))(
          Crit.in_side_some(~V, rep, pos, Some{v}, Crit.Tip{}, o, lo, True{})(h)(nt)
        )(
          Crit.mis_of(rep, Crit.rep(V, o, rep), pos, None{}, Some{True{}})(Crit.side_len(rep, pos)(Crit.wf.rep_ok(~V, rep, pos, Some{v}, Crit.Tip{}, o, lo)(h)))(
            Crit.in_side_side(~V, rep, pos, Some{v}, Crit.Tip{}, o, lo, True{})(h)(nt)
          )({==})
        )
    case Crit.Leaf{+k3, +w3}:
      +h => f => f(rep)(k3)(Crit.rep_in(~V, Crit.Fork{rep, pos, Some{v}, Crit.Leaf{k3, w3}, o}, lo, [])(h)({==}))(
        Crit.in_side_some(~V, rep, pos, Some{v}, Crit.Leaf{k3, w3}, o, lo, False{})(h)({==})
      )(
        Crit.mis_of(rep, k3, pos, None{}, Some{False{}})(Crit.side_len(rep, pos)(Crit.wf.rep_ok(~V, rep, pos, Some{v}, Crit.Leaf{k3, w3}, o, lo)(h)))(
          Crit.in_side_side(~V, rep, pos, Some{v}, Crit.Leaf{k3, w3}, o, lo, False{})(h)({==})
        )({==})
      )
    case Crit.Fork{+r3, +p3, +e3, +z3, +o3}:
      +h => f => f(rep)(r3)(Crit.rep_in(~V, Crit.Fork{rep, pos, Some{v}, Crit.Fork{r3, p3, e3, z3, o3}, o}, lo, [])(h)({==}))(
        Crit.in_side_some(~V, rep, pos, Some{v}, Crit.Fork{r3, p3, e3, z3, o3}, o, lo, False{})(h)({==})
      )(
        Crit.mis_of(rep, r3, pos, None{}, Some{False{}})(Crit.side_len(rep, pos)(Crit.wf.rep_ok(~V, rep, pos, Some{v}, Crit.Fork{r3, p3, e3, z3, o3}, o, lo)(h)))(
          Crit.in_side_side(~V, rep, pos, Some{v}, Crit.Fork{r3, p3, e3, z3, o3}, o, lo, False{})(h)({==})
        )({==})
      )

# a well formed fork has two keys whose sides at its bit differ
def Crit.two(~V: Data, +rep: List<&2, U32>, +pos: Nat, e: Maybe<&2, V>, +z: Crit<V>, +o: Crit<V>, +lo: Nat, -T: Type) -> {Crit.wf(~V, Crit.Fork{rep, pos, e, z, o}, lo) == True{}: Bool} -> (@q1: List<&2, U32> -> @q2: List<&2, U32> -> {Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, q1)) == True{}: Bool} -> {Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, q2)) == True{}: Bool} -> {Shared.Maybe.is_eq(~Bool, ~Shared.Bool.is_eq, Key.side(q1, pos), Key.side(q2, pos)) == False{}: Bool} -> T) -> T:
  match e:
    case None{}:
      +h => f =>
        +nz = Crit.shape_none_z(V, z, o)(Crit.wf.shape(~V, rep, pos, None{}, z, o, lo)(h))
        +no = Crit.shape_none_o(V, z, o)(Crit.wf.shape(~V, rep, pos, None{}, z, o, lo)(h))
        f(Crit.rep(V, z, rep))(Crit.rep(V, o, rep))(Crit.in_side_some(~V, rep, pos, None{}, z, o, lo, False{})(h)(nz))(
          Crit.in_side_some(~V, rep, pos, None{}, z, o, lo, True{})(h)(no)
        )(
          Crit.mis_of(Crit.rep(V, z, rep), Crit.rep(V, o, rep), pos, Some{False{}}, Some{True{}})(Crit.in_side_side(~V, rep, pos, None{}, z, o, lo, False{})(h)(nz))(
            Crit.in_side_side(~V, rep, pos, None{}, z, o, lo, True{})(h)(no)
          )({==})
        )
    case Some{+v}:
      h => f => Crit.two.some(~V, rep, pos, v, z, o, lo, T)(h)(f)

# a key of a well formed fork has the side of its rep before the fork's bit
def Crit.same_side(~V: Data, +rep: List<&2, U32>, +pos: Nat, +e: Maybe<&2, V>, +z: Crit<V>, +o: Crit<V>, +lo: Nat, +q: List<&2, U32>, +x: Nat) -> {Crit.wf(~V, Crit.Fork{rep, pos, e, z, o}, lo) == True{}: Bool} -> {
  Nat.is_lt(x, pos) == True{}: Bool
} -> {Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, q)) == True{}: Bool} -> {Key.side(q, x) == Key.side(rep, x): Maybe<&2, Bool>}:
  h => lt => s => Equal.trans(
    Maybe<&2, Bool>,
    Key.side(q, x),
    Bits.at(Key.bits(q), x),
    Key.side(rep, x),
    Key.side_bits(q, x),
    Equal.trans(
      Maybe<&2, Bool>,
      Bits.at(Key.bits(q), x),
      Bits.at(Key.bits(rep), x),
      Key.side(rep, x),
      Key.at_eq(q, rep, x)(Key.agree_le(q, rep, 1n+x, pos)(Crit.lt_le_succ(x, pos)(lt))(Crit.in_fork_agree(~V, rep, pos, e, z, o, lo, q)(h)(s))),
      Equal.sym(Maybe<&2, Bool>, Key.side(rep, x), Bits.at(Key.bits(rep), x), Key.side_bits(rep, x))
    )
  )

# keys with the same side do not have different sides
def Crit.same_contra(+q1: List<&2, U32>, +q2: List<&2, U32>, +x: Nat) -> {Key.side(q1, x) == Key.side(q2, x): Maybe<&2, Bool>} -> {Shared.Maybe.is_eq(~Bool, ~Shared.Bool.is_eq, Key.side(q1, x), Key.side(q2, x)) == False{}: Bool} -> Empty:
  e => ne => Shared.Bool.false_ne_true(
    Equal.trans(
      Bool,
      False{},
      Shared.Maybe.is_eq(~Bool, ~Shared.Bool.is_eq, Key.side(q1, x), Key.side(q2, x)),
      True{},
      Equal.sym(Bool, Shared.Maybe.is_eq(~Bool, ~Shared.Bool.is_eq, Key.side(q1, x), Key.side(q2, x)), False{}, ne),
      (
        %Equal.sym(Maybe<&2, Bool>, Key.side(q1, x), Key.side(q2, x), e): {Shared.Maybe.is_eq(~Bool, ~Shared.Bool.is_eq, _, Key.side(q2, x)) == True{}: Bool}
        Crit.mis_refl(Key.side(q2, x))
      )
    )
  )

# Crit.sub_has, once the read of m at k is known (mv)
def Crit.sub_has.at(-V: Data, m: Crit<V>, +x: Crit<V>, +k: List<&2, U32>, mv: Maybe<&2, V>) -> {Crit.lookup(V, m, k) == mv: Maybe<&2, V>} -> Crit.sub(V, m, x) -> {Maybe.is_some(&2, V, mv) == True{}: Bool} -> {
  Maybe.is_some(&2, V, Crit.lookup(V, x, k)) == True{}: Bool
}:
  match mv:
    case None{}:
      e => c => s => Empty.absurd({Maybe.is_some(&2, V, Crit.lookup(V, x, k)) == True{}: Bool}, Shared.Bool.false_ne_true(s))
    case Some{v}:
      e => c => s => Equal.cong(Maybe<&2, V>, Bool, y => Maybe.is_some(&2, V, y), Crit.lookup(V, x, k), Some{v}, Crit.sub_pick(V, m, x, k, v)(c)(e))

# a key of m is a key of x, when each entry of m is an entry of x
def Crit.sub_has(-V: Data, +m: Crit<V>, +x: Crit<V>, +k: List<&2, U32>) -> Crit.sub(V, m, x) -> {Maybe.is_some(&2, V, Crit.lookup(V, m, k)) == True{}: Bool} -> {Maybe.is_some(&2, V, Crit.lookup(V, x, k)) == True{}: Bool}:
  c => s => Crit.sub_has.at(V, m, x, k, Crit.lookup(V, m, k))({==})(c)(s)

# entries of the same key are the same entry
def Crit.leaf_same(-V: Data, +k2: List<&2, U32>, -w: V, +k: List<&2, U32>, -v: V, b: Bool) -> {Key.is_eq(k2, k) == b: Bool} -> {Shared.Maybe.when(V, b, u => Some{w}) == Some{v}: Maybe<&2, V>} -> {
  Crit.Leaf{k, v} == Crit.Leaf{k2, w}: Crit<V>
}:
  match b:
    case True{}:
      eb => hw =>
        %Equal.sym(List<&2, U32>, k2, k, Key.is_eq_sound(k2, k)(eb)): {Crit.Leaf{k, v} == Crit.Leaf{_, w}: Crit<V>}
        %Equal.sym(V, w, v, Shared.Maybe.some_inj(V, w, v, hw)): {Crit.Leaf{k, v} == Crit.Leaf{k, _}: Crit<V>}
        {==}
    case False{}:
      eb => hw => Empty.absurd({Crit.Leaf{k, v} == Crit.Leaf{k2, w}: Crit<V>}, Shared.Maybe.none_ne_some(V, v, hw))

# an end read at a key that is some is the end of that key
def Crit.ws_key(-V: Data, +rb: List<&2, U32>, -w: V, +ra: List<&2, U32>, -u: V, b: Bool) -> {Key.is_eq(rb, ra) == b: Bool} -> {Shared.Maybe.when(V, b, x => Some{w}) == Some{u}: Maybe<&2, V>} -> {
  rb == ra: List<&2, U32>
}:
  match b:
    case True{}:
      eb => hw => Key.is_eq_sound(rb, ra)(eb)
    case False{}:
      eb => hw => Empty.absurd({rb == ra: List<&2, U32>}, Shared.Maybe.none_ne_some(V, u, hw))

# an end read at a key that is some u has the value u
def Crit.ws_val(-V: Data, -w: V, -u: V, b: Bool) -> {Shared.Maybe.when(V, b, x => Some{w}) == Some{u}: Maybe<&2, V>} -> {w == u: V}:
  match b:
    case True{}:
      hw => Shared.Maybe.some_inj(V, w, u, hw)
    case False{}:
      hw => Empty.absurd({w == u: V}, Shared.Maybe.none_ne_some(V, u, hw))

# forks of equal parts are equal
def Crit.fork_cong(-V: Data, -ra: List<&2, U32>, -rb: List<&2, U32>, -pa: Nat, -pb: Nat, -ea: Maybe<&2, V>, -eb: Maybe<&2, V>, -za: Crit<V>, -zb: Crit<V>, -oa: Crit<V>, -ob: Crit<V>) -> {ra == rb: List<&2, U32>} -> {
  pa == pb: Nat
} -> {ea == eb: Maybe<&2, V>} -> {za == zb: Crit<V>} -> {oa == ob: Crit<V>} -> {Crit.Fork{ra, pa, ea, za, oa} == Crit.Fork{rb, pb, eb, zb, ob}: Crit<V>}:
  e1 => e2 => e3 => e4 => e5 =>
    %e1: {Crit.Fork{ra, pa, ea, za, oa} == Crit.Fork{_, pb, eb, zb, ob}: Crit<V>}
    %e2: {Crit.Fork{ra, pa, ea, za, oa} == Crit.Fork{ra, _, eb, zb, ob}: Crit<V>}
    %e3: {Crit.Fork{ra, pa, ea, za, oa} == Crit.Fork{ra, pa, _, zb, ob}: Crit<V>}
    %e4: {Crit.Fork{ra, pa, ea, za, oa} == Crit.Fork{ra, pa, ea, _, ob}: Crit<V>}
    %e5: {Crit.Fork{ra, pa, ea, za, oa} == Crit.Fork{ra, pa, ea, za, _}: Crit<V>}
    {==}

# two well formed forks at one bit, with equal sides, whose entries are each
# other's, are equal
def Crit.det_fork(~V: Data, +ra: List<&2, U32>, +pa: Nat, ea: Maybe<&2, V>, +za: Crit<V>, +oa: Crit<V>, +rb: List<&2, U32>, +pb: Nat, eb: Maybe<&2, V>, +zb: Crit<V>, +ob: Crit<V>, +la: Nat, +lb: Nat) -> {Crit.wf(~V, Crit.Fork{ra, pa, ea, za, oa}, la) == True{}: Bool} -> {Crit.wf(~V, Crit.Fork{rb, pb, eb, zb, ob}, lb) == True{}: Bool} -> {pa == pb: Nat} -> {
  za == zb: Crit<V>
} -> {oa == ob: Crit<V>} -> Crit.sub(V, Crit.Fork{ra, pa, ea, za, oa}, Crit.Fork{rb, pb, eb, zb, ob}) -> Crit.sub(V, Crit.Fork{rb, pb, eb, zb, ob}, Crit.Fork{ra, pa, ea, za, oa}) -> {Crit.Fork{ra, pa, ea, za, oa} == Crit.Fork{rb, pb, eb, zb, ob}: Crit<V>}:
  match ea eb:
    case None{} None{}:
      +ha => +hb => eqp => +ez => eo => c1 => c2 => Crit.fork_cong(V, ra, rb, pa, pb, None{}, None{}, za, zb, oa, ob)(
        Equal.trans(
          List<&2, U32>,
          ra,
          Crit.rep(V, za, ra),
          rb,
          Key.is_eq_sound(ra, Crit.rep(V, za, ra))(Crit.wf.rep_ok(~V, ra, pa, None{}, za, oa, la)(ha)),
          Equal.trans(
            List<&2, U32>,
            Crit.rep(V, za, ra),
            Crit.rep(V, za, rb),
            rb,
            Crit.rep_irr(V, za, ra, rb)(Crit.shape_none_z(V, za, oa)(Crit.wf.shape(~V, ra, pa, None{}, za, oa, la)(ha))),
            Equal.trans(
              List<&2, U32>,
              Crit.rep(V, za, rb),
              Crit.rep(V, zb, rb),
              rb,
              Equal.cong(Crit<V>, List<&2, U32>, m => Crit.rep(V, m, rb), za, zb, ez),
              Equal.sym(List<&2, U32>, rb, Crit.rep(V, zb, rb), Key.is_eq_sound(rb, Crit.rep(V, zb, rb))(Crit.wf.rep_ok(~V, rb, pb, None{}, zb, ob, lb)(hb)))
            )
          )
        )
      )(eqp)({==})(ez)(eo)
    case Some{+u} Some{+w}:
      +ha => +hb => +eqp => ez => eo => +c1 => c2 =>
        +hw = Equal.trans(
          Maybe<&2, V>,
          Shared.Maybe.when(V, Key.is_eq(rb, ra), x => Some{w}),
          Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, ra),
          Some{u},
          Equal.sym(Maybe<&2, V>, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, ra), Shared.Maybe.when(V, Key.is_eq(rb, ra), x => Some{w}), Crit.route_end(~V, rb, pb, Some{w}, zb, ob, lb, ra)(hb)(Crit.side_len(ra, pb)((
          %eqp: {Nat.is_eq(List.length(&2, Bool, Key.bits(ra)), _) == True{}: Bool}
          Crit.wf.rep_ok(~V, ra, pa, Some{u}, za, oa, la)(ha)
        )))),
          Crit.sub_pick(V, Crit.Fork{ra, pa, Some{u}, za, oa}, Crit.Fork{rb, pb, Some{w}, zb, ob}, ra, u)(c1)(Crit.self_end(V, ra, pa, Some{u}, za, oa))
        )
        Crit.fork_cong(V, ra, rb, pa, pb, Some{u}, Some{w}, za, zb, oa, ob)(Equal.sym(List<&2, U32>, rb, ra, Crit.ws_key(V, rb, w, ra, u, Key.is_eq(rb, ra))({==})(hw)))(eqp)(
          Equal.cong(V, Maybe<&2, V>, y => Some{y}, u, w, Equal.sym(V, w, u, Crit.ws_val(V, w, u, Key.is_eq(rb, ra))(hw)))
        )(ez)(eo)
    case Some{+u} None{}:
      +ha => +hb => +eqp => ez => eo => +c1 => c2 => Empty.absurd(
        {Crit.Fork{ra, pa, Some{u}, za, oa} == Crit.Fork{rb, pb, None{}, zb, ob}: Crit<V>},
        Shared.Maybe.none_ne_some(
          V,
          u,
          Equal.trans(
            Maybe<&2, V>,
            None{},
            Crit.lookup(V, Crit.Fork{rb, pb, None{}, zb, ob}, ra),
            Some{u},
            Equal.sym(Maybe<&2, V>, Crit.lookup(V, Crit.Fork{rb, pb, None{}, zb, ob}, ra), None{}, Crit.route_end(~V, rb, pb, None{}, zb, ob, lb, ra)(hb)(Crit.side_len(ra, pb)((
          %eqp: {Nat.is_eq(List.length(&2, Bool, Key.bits(ra)), _) == True{}: Bool}
          Crit.wf.rep_ok(~V, ra, pa, Some{u}, za, oa, la)(ha)
        )))),
            Crit.sub_pick(V, Crit.Fork{ra, pa, Some{u}, za, oa}, Crit.Fork{rb, pb, None{}, zb, ob}, ra, u)(c1)(Crit.self_end(V, ra, pa, Some{u}, za, oa))
          )
        )
      )
    case None{} Some{+w}:
      +ha => +hb => +eqp => ez => eo => c1 => +c2 => Empty.absurd(
        {Crit.Fork{ra, pa, None{}, za, oa} == Crit.Fork{rb, pb, Some{w}, zb, ob}: Crit<V>},
        Shared.Maybe.none_ne_some(
          V,
          w,
          Equal.trans(
            Maybe<&2, V>,
            None{},
            Crit.lookup(V, Crit.Fork{ra, pa, None{}, za, oa}, rb),
            Some{w},
            Equal.sym(Maybe<&2, V>, Crit.lookup(V, Crit.Fork{ra, pa, None{}, za, oa}, rb), None{}, Crit.route_end(~V, ra, pa, None{}, za, oa, la, rb)(ha)(Crit.side_len(rb, pa)((
          %Equal.sym(Nat, pa, pb, eqp): {Nat.is_eq(List.length(&2, Bool, Key.bits(rb)), _) == True{}: Bool}
          Crit.wf.rep_ok(~V, rb, pb, Some{w}, zb, ob, lb)(hb)
        )))),
            Crit.sub_pick(V, Crit.Fork{rb, pb, Some{w}, zb, ob}, Crit.Fork{ra, pa, None{}, za, oa}, rb, w)(c2)(Crit.self_end(V, rb, pb, Some{w}, zb, ob))
          )
        )
      )

# two well formed forks whose entries are each other's, by how their bits
# compare (c); iz and io give equal sides once the bits are equal
def Crit.det_cmp(~V: Data, +ra: List<&2, U32>, +pa: Nat, +ea: Maybe<&2, V>, +za: Crit<V>, +oa: Crit<V>, +rb: List<&2, U32>, +pb: Nat, +eb: Maybe<&2, V>, +zb: Crit<V>, +ob: Crit<V>, +la: Nat, +lb: Nat, c: Cmp) -> {Nat.cmp(pa, pb) == c: Cmp} -> {Crit.wf(~V, Crit.Fork{ra, pa, ea, za, oa}, la) == True{}: Bool} -> {Crit.wf(~V, Crit.Fork{rb, pb, eb, zb, ob}, lb) == True{}: Bool} -> Crit.sub(V, Crit.Fork{ra, pa, ea, za, oa}, Crit.Fork{rb, pb, eb, zb, ob}) -> Crit.sub(V, Crit.Fork{rb, pb, eb, zb, ob}, Crit.Fork{ra, pa, ea, za, oa}) -> (
  {pa == pb: Nat} -> {za == zb: Crit<V>}
) -> ({pa == pb: Nat} -> {oa == ob: Crit<V>}) -> {Crit.Fork{ra, pa, ea, za, oa} == Crit.Fork{rb, pb, eb, zb, ob}: Crit<V>}:
  match c:
    case EQ{}:
      hc => ha => hb => c1 => c2 => iz => io =>
        +eqp = Crit.cmp_eq(pa, pb)(hc)
        Crit.det_fork(~V, ra, pa, ea, za, oa, rb, pb, eb, zb, ob, la, lb)(ha)(hb)(eqp)(iz(eqp))(io(eqp))(c1)(c2)
    case LT{}:
      hc => +ha => +hb => +c1 => c2 => iz => io =>
        +lt = Crit.cmp_lt(pa, pb)(hc)
        Empty.absurd(
          {Crit.Fork{ra, pa, ea, za, oa} == Crit.Fork{rb, pb, eb, zb, ob}: Crit<V>},
          Crit.two(~V, ra, pa, ea, za, oa, la, Empty)(ha)(
            +q1 => +q2 => s1 => s2 => ne => Crit.same_contra(q1, q2, pa)(
              Equal.trans(
                Maybe<&2, Bool>,
                Key.side(q1, pa),
                Key.side(rb, pa),
                Key.side(q2, pa),
                Crit.same_side(~V, rb, pb, eb, zb, ob, lb, q1, pa)(hb)(lt)(Crit.sub_has(V, Crit.Fork{ra, pa, ea, za, oa}, Crit.Fork{rb, pb, eb, zb, ob}, q1)(c1)(s1)),
                Equal.sym(Maybe<&2, Bool>, Key.side(q2, pa), Key.side(rb, pa), Crit.same_side(~V, rb, pb, eb, zb, ob, lb, q2, pa)(hb)(lt)(Crit.sub_has(V, Crit.Fork{ra, pa, ea, za, oa}, Crit.Fork{rb, pb, eb, zb, ob}, q2)(c1)(s2)))
              )
            )(ne)
          )
        )
    case GT{}:
      hc => +ha => +hb => c1 => +c2 => iz => io =>
        +gt = Crit.cmp_gt(pa, pb)(hc)
        Empty.absurd(
          {Crit.Fork{ra, pa, ea, za, oa} == Crit.Fork{rb, pb, eb, zb, ob}: Crit<V>},
          Crit.two(~V, rb, pb, eb, zb, ob, lb, Empty)(hb)(
            +q1 => +q2 => s1 => s2 => ne => Crit.same_contra(q1, q2, pb)(
              Equal.trans(
                Maybe<&2, Bool>,
                Key.side(q1, pb),
                Key.side(ra, pb),
                Key.side(q2, pb),
                Crit.same_side(~V, ra, pa, ea, za, oa, la, q1, pb)(ha)(gt)(Crit.sub_has(V, Crit.Fork{rb, pb, eb, zb, ob}, Crit.Fork{ra, pa, ea, za, oa}, q1)(c2)(s1)),
                Equal.sym(Maybe<&2, Bool>, Key.side(q2, pb), Key.side(ra, pb), Crit.same_side(~V, ra, pa, ea, za, oa, la, q2, pb)(ha)(gt)(Crit.sub_has(V, Crit.Fork{rb, pb, eb, zb, ob}, Crit.Fork{ra, pa, ea, za, oa}, q2)(c2)(s2)))
              )
            )(ne)
          )
        )

# two well formed maps whose entries are each other's are equal
def Crit.det(~V: Data, +a: Crit<V>, +b: Crit<V>, +la: Nat, +lb: Nat) -> {Crit.wf(~V, a, la) == True{}: Bool} -> {Crit.wf(~V, b, lb) == True{}: Bool} -> Crit.sub(V, a, b) -> Crit.sub(V, b, a) -> {
  a == b: Crit<V>
}:
  match a b:
    case Crit.Tip{} Crit.Tip{}:
      ha => hb => c1 => c2 => {==}
    case Crit.Tip{} Crit.Leaf{k, w}:
      ha => hb => c1 => c2 => Empty.absurd({Crit.Tip{} == Crit.Leaf{k, w}: Crit<V>}, Shared.Maybe.none_ne_some(V, w, c2))
    case Crit.Tip{} Crit.Fork{+rb, +pb, +eb, +zb, +ob}:
      ha => +hb => c1 => c2 => Empty.absurd({Crit.Tip{} == Crit.Fork{rb, pb, eb, zb, ob}: Crit<V>}, Shared.Bool.false_ne_true(Crit.sub_has(V, Crit.Fork{rb, pb, eb, zb, ob}, Crit.Tip{}, rb)(c2)(Crit.rep_in(~V, Crit.Fork{rb, pb, eb, zb, ob}, lb, [])(hb)({==}))))
    case Crit.Leaf{k, v} Crit.Tip{}:
      ha => hb => c1 => c2 => Empty.absurd({Crit.Leaf{k, v} == Crit.Tip{}: Crit<V>}, Shared.Maybe.none_ne_some(V, v, c1))
    case Crit.Fork{+ra, +pa, +ea, +za, +oa} Crit.Tip{}:
      +ha => hb => c1 => c2 => Empty.absurd({Crit.Fork{ra, pa, ea, za, oa} == Crit.Tip{}: Crit<V>}, Shared.Bool.false_ne_true(Crit.sub_has(V, Crit.Fork{ra, pa, ea, za, oa}, Crit.Tip{}, ra)(c1)(Crit.rep_in(~V, Crit.Fork{ra, pa, ea, za, oa}, la, [])(ha)({==}))))
    case Crit.Leaf{+k, +v} Crit.Leaf{+k2, +w}:
      ha => hb => c1 => c2 => Crit.leaf_same(V, k2, w, k, v, Key.is_eq(k2, k))({==})(c1)
    case Crit.Leaf{+k, +v} Crit.Fork{+rb, +pb, +eb, +zb, +ob}:
      ha => +hX => c1 => +c2 => Empty.absurd(
        {Crit.Leaf{k, v} == Crit.Fork{rb, pb, eb, zb, ob}: Crit<V>},
        Crit.two(~V, rb, pb, eb, zb, ob, lb, Empty)(hX)(
          +q1 => +q2 => s1 => s2 => ne => Crit.same_contra(q1, q2, pb)(
            Equal.cong(
              List<&2, U32>,
              Maybe<&2, Bool>,
              t => Key.side(t, pb),
              q1,
              q2,
              Equal.trans(
                List<&2, U32>,
                q1,
                k,
                q2,
                Key.is_eq_sound(q1, k)(Equal.trans(Bool, Key.is_eq(q1, k), Maybe.is_some(&2, V, Shared.Maybe.when(V, Key.is_eq(k, q1), u => Some{v})), True{}, Equal.sym(Bool, Maybe.is_some(&2, V, Shared.Maybe.when(V, Key.is_eq(k, q1), u => Some{v})), Key.is_eq(q1, k), Crit.is_some_when(V, k, q1, v)), Crit.sub_has(V, Crit.Fork{rb, pb, eb, zb, ob}, Crit.Leaf{k, v}, q1)(c2)(s1))),
                Equal.sym(List<&2, U32>, q2, k, Key.is_eq_sound(q2, k)(Equal.trans(Bool, Key.is_eq(q2, k), Maybe.is_some(&2, V, Shared.Maybe.when(V, Key.is_eq(k, q2), u => Some{v})), True{}, Equal.sym(Bool, Maybe.is_some(&2, V, Shared.Maybe.when(V, Key.is_eq(k, q2), u => Some{v})), Key.is_eq(q2, k), Crit.is_some_when(V, k, q2, v)), Crit.sub_has(V, Crit.Fork{rb, pb, eb, zb, ob}, Crit.Leaf{k, v}, q2)(c2)(s2))))
              )
            )
          )(ne)
        )
      )
    case Crit.Fork{+ra, +pa, +ea, +za, +oa} Crit.Leaf{+k, +v}:
      +hX => hb => +c1 => c2 => Empty.absurd(
        {Crit.Fork{ra, pa, ea, za, oa} == Crit.Leaf{k, v}: Crit<V>},
        Crit.two(~V, ra, pa, ea, za, oa, la, Empty)(hX)(
          +q1 => +q2 => s1 => s2 => ne => Crit.same_contra(q1, q2, pa)(
            Equal.cong(
              List<&2, U32>,
              Maybe<&2, Bool>,
              t => Key.side(t, pa),
              q1,
              q2,
              Equal.trans(
                List<&2, U32>,
                q1,
                k,
                q2,
                Key.is_eq_sound(q1, k)(Equal.trans(Bool, Key.is_eq(q1, k), Maybe.is_some(&2, V, Shared.Maybe.when(V, Key.is_eq(k, q1), u => Some{v})), True{}, Equal.sym(Bool, Maybe.is_some(&2, V, Shared.Maybe.when(V, Key.is_eq(k, q1), u => Some{v})), Key.is_eq(q1, k), Crit.is_some_when(V, k, q1, v)), Crit.sub_has(V, Crit.Fork{ra, pa, ea, za, oa}, Crit.Leaf{k, v}, q1)(c1)(s1))),
                Equal.sym(List<&2, U32>, q2, k, Key.is_eq_sound(q2, k)(Equal.trans(Bool, Key.is_eq(q2, k), Maybe.is_some(&2, V, Shared.Maybe.when(V, Key.is_eq(k, q2), u => Some{v})), True{}, Equal.sym(Bool, Maybe.is_some(&2, V, Shared.Maybe.when(V, Key.is_eq(k, q2), u => Some{v})), Key.is_eq(q2, k), Crit.is_some_when(V, k, q2, v)), Crit.sub_has(V, Crit.Fork{ra, pa, ea, za, oa}, Crit.Leaf{k, v}, q2)(c1)(s2))))
              )
            )
          )(ne)
        )
      )
    case Crit.Fork{+ra, +pa, +ea, +za, +oa} Crit.Fork{+rb, +pb, +eb, +zb, +ob}:
      +ha => +hb => +c1 => +c2 => Crit.det_cmp(~V, ra, pa, ea, za, oa, rb, pb, eb, zb, ob, la, lb, Nat.cmp(pa, pb))({==})(ha)(hb)(c1)(c2)(
        +eqp => Crit.det(~V, za, zb, 1n+pa, 1n+pb)(Crit.wf.wf_z(~V, ra, pa, ea, za, oa, la)(ha))(Crit.wf.wf_z(~V, rb, pb, eb, zb, ob, lb)(hb))(
          Crit.sub_down(~V, za, rb, pb, eb, zb, ob, lb, ra, False{})(Crit.sub.z(V, ra, pa, ea, za, oa, Crit.Fork{rb, pb, eb, zb, ob}, c1))((
            %eqp: {Crit.all(~V, ~Place, ~Place.has, za, Place{ra, _, False{}}) == True{}: Bool}
            Crit.wf.all_z(~V, ra, pa, ea, za, oa, la)(ha)
          ))(hb)
        )(
          Crit.sub_down(~V, zb, ra, pa, ea, za, oa, la, rb, False{})(Crit.sub.z(V, rb, pb, eb, zb, ob, Crit.Fork{ra, pa, ea, za, oa}, c2))((
            %Equal.sym(Nat, pa, pb, eqp): {Crit.all(~V, ~Place, ~Place.has, zb, Place{rb, _, False{}}) == True{}: Bool}
            Crit.wf.all_z(~V, rb, pb, eb, zb, ob, lb)(hb)
          ))(ha)
        )
      )(
        +eqp => Crit.det(~V, oa, ob, 1n+pa, 1n+pb)(Crit.wf.wf_o(~V, ra, pa, ea, za, oa, la)(ha))(Crit.wf.wf_o(~V, rb, pb, eb, zb, ob, lb)(hb))(
          Crit.sub_down(~V, oa, rb, pb, eb, zb, ob, lb, ra, True{})(Crit.sub.o(V, ra, pa, ea, za, oa, Crit.Fork{rb, pb, eb, zb, ob}, c1))((
            %eqp: {Crit.all(~V, ~Place, ~Place.has, oa, Place{ra, _, True{}}) == True{}: Bool}
            Crit.wf.all_o(~V, ra, pa, ea, za, oa, la)(ha)
          ))(hb)
        )(
          Crit.sub_down(~V, ob, ra, pa, ea, za, oa, la, rb, True{})(Crit.sub.o(V, rb, pb, eb, zb, ob, Crit.Fork{ra, pa, ea, za, oa}, c2))((
            %Equal.sym(Nat, pa, pb, eqp): {Crit.all(~V, ~Place, ~Place.has, ob, Place{rb, _, True{}}) == True{}: Bool}
            Crit.wf.all_o(~V, rb, pb, eb, zb, ob, lb)(hb)
          ))(ha)
        )
      )

# Crit.ext, with a and b used more than once
def Crit.ext.go(~V: Data, +a: Crit<V>, +b: Crit<V>) -> {Crit.wf(~V, a, 0n) == True{}: Bool} -> {Crit.wf(~V, b, 0n) == True{}: Bool} -> {
  Crit.entries(V, a) == Crit.entries(V, b): List<&2, Bind<V>>
} -> {a == b: Crit<V>}:
  +ha => +hb => +en => Crit.det(~V, a, b, 0n, 0n)(ha)(hb)(Crit.sub_of_entries(~V, a, b, 0n)(hb)(en))(
    Crit.sub_of_entries(~V, b, a, 0n)(ha)(Equal.sym(List<&2, Bind<V>>, Crit.entries(V, a), Crit.entries(V, b), en))
  )

# a map is its entries: two well formed maps with the same entries are the
# same map, so a map has one shape, and one code, for its content
law Crit.ext:
  for ~V: Data
  for a: Crit<V>
  for b: Crit<V>
  {Crit.wf(~V, a, 0n) == True{}: Bool} -> {Crit.wf(~V, b, 0n) == True{}: Bool} -> {
    Crit.entries(V, a) == Crit.entries(V, b): List<&2, Bind<V>>
  } -> {a == b: Crit<V>}

def Crit.ext(ty, a, b):
  Crit.ext.go(~ty, a, b)

# Crit.sub_comm for the end of a fork
def Crit.sub_comm.end(~V: Data, ~j: V -> V -> V, ~comm: @x: V -> @y: V -> {j(x, y) == j(y, x): V}, +r: List<&2, U32>, e: Maybe<&2, V>, +a: Crit<V>, +b: Crit<V>) -> {Crit.wf(~V, a, 0n) == True{}: Bool} -> {Crit.wf(~V, b, 0n) == True{}: Bool} -> Crit.sub_end(V, r, e, Crit.union(~V, ~j, a, b)) -> Crit.sub_end(V, r, e, Crit.union(~V, ~j, b, a)):
  match e:
    case None{}:
      h0 => h1 => c => Unit{}
    case Some{w}:
      +h0 => +h1 => c => Equal.trans(Maybe<&2, V>, Crit.lookup(V, Crit.union(~V, ~j, b, a), r), Crit.lookup(V, Crit.union(~V, ~j, a, b), r), Some{w}, Equal.trans(Maybe<&2, V>, Crit.lookup(V, Crit.union(~V, ~j, b, a), r), Shared.Maybe.join(~V, ~j, Crit.lookup(V, b, r), Crit.lookup(V, a, r)), Crit.lookup(V, Crit.union(~V, ~j, a, b), r), Crit.union_go_lookup(~V, ~j, b, a, 0n, 0n, r)(h1)(h0), Equal.trans(Maybe<&2, V>, Shared.Maybe.join(~V, ~j, Crit.lookup(V, b, r), Crit.lookup(V, a, r)), Shared.Maybe.join(~V, ~j, Crit.lookup(V, a, r), Crit.lookup(V, b, r)), Crit.lookup(V, Crit.union(~V, ~j, a, b), r), Shared.Maybe.join_comm(~V, ~j, ~comm, Crit.lookup(V, b, r), Crit.lookup(V, a, r)), Equal.sym(Maybe<&2, V>, Crit.lookup(V, Crit.union(~V, ~j, a, b), r), Shared.Maybe.join(~V, ~j, Crit.lookup(V, a, r), Crit.lookup(V, b, r)), Crit.union_go_lookup(~V, ~j, a, b, 0n, 0n, r)(h0)(h1)))), c)

# the entries of m that are entries of one map are entries of a map that reads
# the same
def Crit.sub_comm(~V: Data, ~j: V -> V -> V, ~comm: @x: V -> @y: V -> {j(x, y) == j(y, x): V}, m: Crit<V>, +a: Crit<V>, +b: Crit<V>) -> {Crit.wf(~V, a, 0n) == True{}: Bool} -> {Crit.wf(~V, b, 0n) == True{}: Bool} -> Crit.sub(V, m, Crit.union(~V, ~j, a, b)) -> Crit.sub(V, m, Crit.union(~V, ~j, b, a)):
  match m:
    case Crit.Tip{}:
      h0 => h1 => c => Unit{}
    case Crit.Leaf{+k, v}:
      +h0 => +h1 => c => Equal.trans(Maybe<&2, V>, Crit.lookup(V, Crit.union(~V, ~j, b, a), k), Crit.lookup(V, Crit.union(~V, ~j, a, b), k), Some{v}, Equal.trans(Maybe<&2, V>, Crit.lookup(V, Crit.union(~V, ~j, b, a), k), Shared.Maybe.join(~V, ~j, Crit.lookup(V, b, k), Crit.lookup(V, a, k)), Crit.lookup(V, Crit.union(~V, ~j, a, b), k), Crit.union_go_lookup(~V, ~j, b, a, 0n, 0n, k)(h1)(h0), Equal.trans(Maybe<&2, V>, Shared.Maybe.join(~V, ~j, Crit.lookup(V, b, k), Crit.lookup(V, a, k)), Shared.Maybe.join(~V, ~j, Crit.lookup(V, a, k), Crit.lookup(V, b, k)), Crit.lookup(V, Crit.union(~V, ~j, a, b), k), Shared.Maybe.join_comm(~V, ~j, ~comm, Crit.lookup(V, b, k), Crit.lookup(V, a, k)), Equal.sym(Maybe<&2, V>, Crit.lookup(V, Crit.union(~V, ~j, a, b), k), Shared.Maybe.join(~V, ~j, Crit.lookup(V, a, k), Crit.lookup(V, b, k)), Crit.union_go_lookup(~V, ~j, a, b, 0n, 0n, k)(h0)(h1)))), c)
    case Crit.Fork{+r, +p, +e, +z, +o}:
      +h0 => +h1 => +c => (
        Crit.sub_comm.end(~V, ~j, ~comm, r, e, a, b)(h0)(h1)(Crit.sub.e(V, r, p, e, z, o, Crit.union(~V, ~j, a, b), c)),
        (
          Crit.sub_comm(~V, ~j, ~comm, z, a, b)(h0)(h1)(Crit.sub.z(V, r, p, e, z, o, Crit.union(~V, ~j, a, b), c)),
          Crit.sub_comm(~V, ~j, ~comm, o, a, b)(h0)(h1)(Crit.sub.o(V, r, p, e, z, o, Crit.union(~V, ~j, a, b), c))
        )
      )

# Crit.union_comm, with a and b used more than once
def Crit.union_comm.go(~V: Data, ~j: V -> V -> V, ~comm: @x: V -> @y: V -> {j(x, y) == j(y, x): V}, +a: Crit<V>, +b: Crit<V>) -> {Crit.wf(~V, a, 0n) == True{}: Bool} -> {Crit.wf(~V, b, 0n) == True{}: Bool} -> {Crit.union(~V, ~j, a, b) == Crit.union(~V, ~j, b, a): Crit<V>}:
  +ha => +hb => Crit.det(~V, Crit.union(~V, ~j, a, b), Crit.union(~V, ~j, b, a), 0n, 0n)(Crit.union_go_wf(~V, ~j, a, b, 0n, [], False{})(ha)(hb)({==}))(Crit.union_go_wf(~V, ~j, b, a, 0n, [], False{})(hb)(ha)({==}))(
    Crit.sub_comm(~V, ~j, ~comm, Crit.union(~V, ~j, a, b), a, b)(ha)(hb)(Crit.sub_self(~V, Crit.union(~V, ~j, a, b), 0n)(Crit.union_go_wf(~V, ~j, a, b, 0n, [], False{})(ha)(hb)({==})))
  )(Crit.sub_comm(~V, ~j, ~comm, Crit.union(~V, ~j, b, a), b, a)(hb)(ha)(Crit.sub_self(~V, Crit.union(~V, ~j, b, a), 0n)(Crit.union_go_wf(~V, ~j, b, a, 0n, [], False{})(hb)(ha)({==}))))

# a union is the same either way round, when j is
law Crit.union_comm:
  for ~V: Data
  for ~j: V -> V -> V
  for ~comm: @x: V -> @y: V -> {j(x, y) == j(y, x): V}
  for a: Crit<V>
  for b: Crit<V>
  {Crit.wf(~V, a, 0n) == True{}: Bool} -> {Crit.wf(~V, b, 0n) == True{}: Bool} -> {Crit.union(~V, ~j, a, b) == Crit.union(~V, ~j, b, a): Crit<V>}

def Crit.union_comm(ty, j, comm, a, b):
  Crit.union_comm.go(~ty, ~j, ~comm, a, b)

# Crit.sub_assoc_r for the end of a fork
def Crit.sub_assoc_r.end(~V: Data, ~j: V -> V -> V, ~assoc: @x: V -> @y: V -> @z: V -> {j(j(x, y), z) == j(x, j(y, z)): V}, +r: List<&2, U32>, e: Maybe<&2, V>, +a: Crit<V>, +b: Crit<V>, +cm: Crit<V>) -> {Crit.wf(~V, a, 0n) == True{}: Bool} -> {Crit.wf(~V, b, 0n) == True{}: Bool} -> {Crit.wf(~V, cm, 0n) == True{}: Bool} -> Crit.sub_end(V, r, e, Crit.union(~V, ~j, Crit.union(~V, ~j, a, b), cm)) -> Crit.sub_end(V, r, e, Crit.union(~V, ~j, a, Crit.union(~V, ~j, b, cm))):
  match e:
    case None{}:
      h0 => h1 => h2 => c => Unit{}
    case Some{w}:
      +h0 => +h1 => +h2 => c => Equal.trans(Maybe<&2, V>, Crit.lookup(V, Crit.union(~V, ~j, a, Crit.union(~V, ~j, b, cm)), r), Crit.lookup(V, Crit.union(~V, ~j, Crit.union(~V, ~j, a, b), cm), r), Some{w}, Equal.trans(Maybe<&2, V>, Crit.lookup(V, Crit.union(~V, ~j, a, Crit.union(~V, ~j, b, cm)), r), Shared.Maybe.join(~V, ~j, Crit.lookup(V, a, r), Shared.Maybe.join(~V, ~j, Crit.lookup(V, b, r), Crit.lookup(V, cm, r))), Crit.lookup(V, Crit.union(~V, ~j, Crit.union(~V, ~j, a, b), cm), r), Equal.trans(Maybe<&2, V>, Crit.lookup(V, Crit.union(~V, ~j, a, Crit.union(~V, ~j, b, cm)), r), Shared.Maybe.join(~V, ~j, Crit.lookup(V, a, r), Crit.lookup(V, Crit.union(~V, ~j, b, cm), r)), Shared.Maybe.join(~V, ~j, Crit.lookup(V, a, r), Shared.Maybe.join(~V, ~j, Crit.lookup(V, b, r), Crit.lookup(V, cm, r))), Crit.union_go_lookup(~V, ~j, a, Crit.union(~V, ~j, b, cm), 0n, 0n, r)(h0)(Crit.union_go_wf(~V, ~j, b, cm, 0n, [], False{})(h1)(h2)({==})), Equal.cong(Maybe<&2, V>, Maybe<&2, V>, t => Shared.Maybe.join(~V, ~j, Crit.lookup(V, a, r), t), Crit.lookup(V, Crit.union(~V, ~j, b, cm), r), Shared.Maybe.join(~V, ~j, Crit.lookup(V, b, r), Crit.lookup(V, cm, r)), Crit.union_go_lookup(~V, ~j, b, cm, 0n, 0n, r)(h1)(h2))), Equal.trans(Maybe<&2, V>, Shared.Maybe.join(~V, ~j, Crit.lookup(V, a, r), Shared.Maybe.join(~V, ~j, Crit.lookup(V, b, r), Crit.lookup(V, cm, r))), Shared.Maybe.join(~V, ~j, Shared.Maybe.join(~V, ~j, Crit.lookup(V, a, r), Crit.lookup(V, b, r)), Crit.lookup(V, cm, r)), Crit.lookup(V, Crit.union(~V, ~j, Crit.union(~V, ~j, a, b), cm), r), Equal.sym(Maybe<&2, V>, Shared.Maybe.join(~V, ~j, Shared.Maybe.join(~V, ~j, Crit.lookup(V, a, r), Crit.lookup(V, b, r)), Crit.lookup(V, cm, r)), Shared.Maybe.join(~V, ~j, Crit.lookup(V, a, r), Shared.Maybe.join(~V, ~j, Crit.lookup(V, b, r), Crit.lookup(V, cm, r))), Shared.Maybe.join_assoc(~V, ~j, ~assoc, Crit.lookup(V, a, r), Crit.lookup(V, b, r), Crit.lookup(V, cm, r))), Equal.sym(Maybe<&2, V>, Crit.lookup(V, Crit.union(~V, ~j, Crit.union(~V, ~j, a, b), cm), r), Shared.Maybe.join(~V, ~j, Shared.Maybe.join(~V, ~j, Crit.lookup(V, a, r), Crit.lookup(V, b, r)), Crit.lookup(V, cm, r)), Equal.trans(Maybe<&2, V>, Crit.lookup(V, Crit.union(~V, ~j, Crit.union(~V, ~j, a, b), cm), r), Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.union(~V, ~j, a, b), r), Crit.lookup(V, cm, r)), Shared.Maybe.join(~V, ~j, Shared.Maybe.join(~V, ~j, Crit.lookup(V, a, r), Crit.lookup(V, b, r)), Crit.lookup(V, cm, r)), Crit.union_go_lookup(~V, ~j, Crit.union(~V, ~j, a, b), cm, 0n, 0n, r)(Crit.union_go_wf(~V, ~j, a, b, 0n, [], False{})(h0)(h1)({==}))(h2), Equal.cong(Maybe<&2, V>, Maybe<&2, V>, t => Shared.Maybe.join(~V, ~j, t, Crit.lookup(V, cm, r)), Crit.lookup(V, Crit.union(~V, ~j, a, b), r), Shared.Maybe.join(~V, ~j, Crit.lookup(V, a, r), Crit.lookup(V, b, r)), Crit.union_go_lookup(~V, ~j, a, b, 0n, 0n, r)(h0)(h1)))))), c)

# the entries of m that are entries of one map are entries of a map that reads
# the same
def Crit.sub_assoc_r(~V: Data, ~j: V -> V -> V, ~assoc: @x: V -> @y: V -> @z: V -> {j(j(x, y), z) == j(x, j(y, z)): V}, m: Crit<V>, +a: Crit<V>, +b: Crit<V>, +cm: Crit<V>) -> {Crit.wf(~V, a, 0n) == True{}: Bool} -> {Crit.wf(~V, b, 0n) == True{}: Bool} -> {Crit.wf(~V, cm, 0n) == True{}: Bool} -> Crit.sub(V, m, Crit.union(~V, ~j, Crit.union(~V, ~j, a, b), cm)) -> Crit.sub(V, m, Crit.union(~V, ~j, a, Crit.union(~V, ~j, b, cm))):
  match m:
    case Crit.Tip{}:
      h0 => h1 => h2 => c => Unit{}
    case Crit.Leaf{+k, v}:
      +h0 => +h1 => +h2 => c => Equal.trans(Maybe<&2, V>, Crit.lookup(V, Crit.union(~V, ~j, a, Crit.union(~V, ~j, b, cm)), k), Crit.lookup(V, Crit.union(~V, ~j, Crit.union(~V, ~j, a, b), cm), k), Some{v}, Equal.trans(Maybe<&2, V>, Crit.lookup(V, Crit.union(~V, ~j, a, Crit.union(~V, ~j, b, cm)), k), Shared.Maybe.join(~V, ~j, Crit.lookup(V, a, k), Shared.Maybe.join(~V, ~j, Crit.lookup(V, b, k), Crit.lookup(V, cm, k))), Crit.lookup(V, Crit.union(~V, ~j, Crit.union(~V, ~j, a, b), cm), k), Equal.trans(Maybe<&2, V>, Crit.lookup(V, Crit.union(~V, ~j, a, Crit.union(~V, ~j, b, cm)), k), Shared.Maybe.join(~V, ~j, Crit.lookup(V, a, k), Crit.lookup(V, Crit.union(~V, ~j, b, cm), k)), Shared.Maybe.join(~V, ~j, Crit.lookup(V, a, k), Shared.Maybe.join(~V, ~j, Crit.lookup(V, b, k), Crit.lookup(V, cm, k))), Crit.union_go_lookup(~V, ~j, a, Crit.union(~V, ~j, b, cm), 0n, 0n, k)(h0)(Crit.union_go_wf(~V, ~j, b, cm, 0n, [], False{})(h1)(h2)({==})), Equal.cong(Maybe<&2, V>, Maybe<&2, V>, t => Shared.Maybe.join(~V, ~j, Crit.lookup(V, a, k), t), Crit.lookup(V, Crit.union(~V, ~j, b, cm), k), Shared.Maybe.join(~V, ~j, Crit.lookup(V, b, k), Crit.lookup(V, cm, k)), Crit.union_go_lookup(~V, ~j, b, cm, 0n, 0n, k)(h1)(h2))), Equal.trans(Maybe<&2, V>, Shared.Maybe.join(~V, ~j, Crit.lookup(V, a, k), Shared.Maybe.join(~V, ~j, Crit.lookup(V, b, k), Crit.lookup(V, cm, k))), Shared.Maybe.join(~V, ~j, Shared.Maybe.join(~V, ~j, Crit.lookup(V, a, k), Crit.lookup(V, b, k)), Crit.lookup(V, cm, k)), Crit.lookup(V, Crit.union(~V, ~j, Crit.union(~V, ~j, a, b), cm), k), Equal.sym(Maybe<&2, V>, Shared.Maybe.join(~V, ~j, Shared.Maybe.join(~V, ~j, Crit.lookup(V, a, k), Crit.lookup(V, b, k)), Crit.lookup(V, cm, k)), Shared.Maybe.join(~V, ~j, Crit.lookup(V, a, k), Shared.Maybe.join(~V, ~j, Crit.lookup(V, b, k), Crit.lookup(V, cm, k))), Shared.Maybe.join_assoc(~V, ~j, ~assoc, Crit.lookup(V, a, k), Crit.lookup(V, b, k), Crit.lookup(V, cm, k))), Equal.sym(Maybe<&2, V>, Crit.lookup(V, Crit.union(~V, ~j, Crit.union(~V, ~j, a, b), cm), k), Shared.Maybe.join(~V, ~j, Shared.Maybe.join(~V, ~j, Crit.lookup(V, a, k), Crit.lookup(V, b, k)), Crit.lookup(V, cm, k)), Equal.trans(Maybe<&2, V>, Crit.lookup(V, Crit.union(~V, ~j, Crit.union(~V, ~j, a, b), cm), k), Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.union(~V, ~j, a, b), k), Crit.lookup(V, cm, k)), Shared.Maybe.join(~V, ~j, Shared.Maybe.join(~V, ~j, Crit.lookup(V, a, k), Crit.lookup(V, b, k)), Crit.lookup(V, cm, k)), Crit.union_go_lookup(~V, ~j, Crit.union(~V, ~j, a, b), cm, 0n, 0n, k)(Crit.union_go_wf(~V, ~j, a, b, 0n, [], False{})(h0)(h1)({==}))(h2), Equal.cong(Maybe<&2, V>, Maybe<&2, V>, t => Shared.Maybe.join(~V, ~j, t, Crit.lookup(V, cm, k)), Crit.lookup(V, Crit.union(~V, ~j, a, b), k), Shared.Maybe.join(~V, ~j, Crit.lookup(V, a, k), Crit.lookup(V, b, k)), Crit.union_go_lookup(~V, ~j, a, b, 0n, 0n, k)(h0)(h1)))))), c)
    case Crit.Fork{+r, +p, +e, +z, +o}:
      +h0 => +h1 => +h2 => +c => (
        Crit.sub_assoc_r.end(~V, ~j, ~assoc, r, e, a, b, cm)(h0)(h1)(h2)(Crit.sub.e(V, r, p, e, z, o, Crit.union(~V, ~j, Crit.union(~V, ~j, a, b), cm), c)),
        (
          Crit.sub_assoc_r(~V, ~j, ~assoc, z, a, b, cm)(h0)(h1)(h2)(Crit.sub.z(V, r, p, e, z, o, Crit.union(~V, ~j, Crit.union(~V, ~j, a, b), cm), c)),
          Crit.sub_assoc_r(~V, ~j, ~assoc, o, a, b, cm)(h0)(h1)(h2)(Crit.sub.o(V, r, p, e, z, o, Crit.union(~V, ~j, Crit.union(~V, ~j, a, b), cm), c))
        )
      )

# Crit.sub_assoc_l for the end of a fork
def Crit.sub_assoc_l.end(~V: Data, ~j: V -> V -> V, ~assoc: @x: V -> @y: V -> @z: V -> {j(j(x, y), z) == j(x, j(y, z)): V}, +r: List<&2, U32>, e: Maybe<&2, V>, +a: Crit<V>, +b: Crit<V>, +cm: Crit<V>) -> {Crit.wf(~V, a, 0n) == True{}: Bool} -> {Crit.wf(~V, b, 0n) == True{}: Bool} -> {Crit.wf(~V, cm, 0n) == True{}: Bool} -> Crit.sub_end(V, r, e, Crit.union(~V, ~j, a, Crit.union(~V, ~j, b, cm))) -> Crit.sub_end(V, r, e, Crit.union(~V, ~j, Crit.union(~V, ~j, a, b), cm)):
  match e:
    case None{}:
      h0 => h1 => h2 => c => Unit{}
    case Some{w}:
      +h0 => +h1 => +h2 => c => Equal.trans(Maybe<&2, V>, Crit.lookup(V, Crit.union(~V, ~j, Crit.union(~V, ~j, a, b), cm), r), Crit.lookup(V, Crit.union(~V, ~j, a, Crit.union(~V, ~j, b, cm)), r), Some{w}, Equal.trans(Maybe<&2, V>, Crit.lookup(V, Crit.union(~V, ~j, Crit.union(~V, ~j, a, b), cm), r), Shared.Maybe.join(~V, ~j, Shared.Maybe.join(~V, ~j, Crit.lookup(V, a, r), Crit.lookup(V, b, r)), Crit.lookup(V, cm, r)), Crit.lookup(V, Crit.union(~V, ~j, a, Crit.union(~V, ~j, b, cm)), r), Equal.trans(Maybe<&2, V>, Crit.lookup(V, Crit.union(~V, ~j, Crit.union(~V, ~j, a, b), cm), r), Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.union(~V, ~j, a, b), r), Crit.lookup(V, cm, r)), Shared.Maybe.join(~V, ~j, Shared.Maybe.join(~V, ~j, Crit.lookup(V, a, r), Crit.lookup(V, b, r)), Crit.lookup(V, cm, r)), Crit.union_go_lookup(~V, ~j, Crit.union(~V, ~j, a, b), cm, 0n, 0n, r)(Crit.union_go_wf(~V, ~j, a, b, 0n, [], False{})(h0)(h1)({==}))(h2), Equal.cong(Maybe<&2, V>, Maybe<&2, V>, t => Shared.Maybe.join(~V, ~j, t, Crit.lookup(V, cm, r)), Crit.lookup(V, Crit.union(~V, ~j, a, b), r), Shared.Maybe.join(~V, ~j, Crit.lookup(V, a, r), Crit.lookup(V, b, r)), Crit.union_go_lookup(~V, ~j, a, b, 0n, 0n, r)(h0)(h1))), Equal.trans(Maybe<&2, V>, Shared.Maybe.join(~V, ~j, Shared.Maybe.join(~V, ~j, Crit.lookup(V, a, r), Crit.lookup(V, b, r)), Crit.lookup(V, cm, r)), Shared.Maybe.join(~V, ~j, Crit.lookup(V, a, r), Shared.Maybe.join(~V, ~j, Crit.lookup(V, b, r), Crit.lookup(V, cm, r))), Crit.lookup(V, Crit.union(~V, ~j, a, Crit.union(~V, ~j, b, cm)), r), Shared.Maybe.join_assoc(~V, ~j, ~assoc, Crit.lookup(V, a, r), Crit.lookup(V, b, r), Crit.lookup(V, cm, r)), Equal.sym(Maybe<&2, V>, Crit.lookup(V, Crit.union(~V, ~j, a, Crit.union(~V, ~j, b, cm)), r), Shared.Maybe.join(~V, ~j, Crit.lookup(V, a, r), Shared.Maybe.join(~V, ~j, Crit.lookup(V, b, r), Crit.lookup(V, cm, r))), Equal.trans(Maybe<&2, V>, Crit.lookup(V, Crit.union(~V, ~j, a, Crit.union(~V, ~j, b, cm)), r), Shared.Maybe.join(~V, ~j, Crit.lookup(V, a, r), Crit.lookup(V, Crit.union(~V, ~j, b, cm), r)), Shared.Maybe.join(~V, ~j, Crit.lookup(V, a, r), Shared.Maybe.join(~V, ~j, Crit.lookup(V, b, r), Crit.lookup(V, cm, r))), Crit.union_go_lookup(~V, ~j, a, Crit.union(~V, ~j, b, cm), 0n, 0n, r)(h0)(Crit.union_go_wf(~V, ~j, b, cm, 0n, [], False{})(h1)(h2)({==})), Equal.cong(Maybe<&2, V>, Maybe<&2, V>, t => Shared.Maybe.join(~V, ~j, Crit.lookup(V, a, r), t), Crit.lookup(V, Crit.union(~V, ~j, b, cm), r), Shared.Maybe.join(~V, ~j, Crit.lookup(V, b, r), Crit.lookup(V, cm, r)), Crit.union_go_lookup(~V, ~j, b, cm, 0n, 0n, r)(h1)(h2)))))), c)

# the entries of m that are entries of one map are entries of a map that reads
# the same
def Crit.sub_assoc_l(~V: Data, ~j: V -> V -> V, ~assoc: @x: V -> @y: V -> @z: V -> {j(j(x, y), z) == j(x, j(y, z)): V}, m: Crit<V>, +a: Crit<V>, +b: Crit<V>, +cm: Crit<V>) -> {Crit.wf(~V, a, 0n) == True{}: Bool} -> {Crit.wf(~V, b, 0n) == True{}: Bool} -> {Crit.wf(~V, cm, 0n) == True{}: Bool} -> Crit.sub(V, m, Crit.union(~V, ~j, a, Crit.union(~V, ~j, b, cm))) -> Crit.sub(V, m, Crit.union(~V, ~j, Crit.union(~V, ~j, a, b), cm)):
  match m:
    case Crit.Tip{}:
      h0 => h1 => h2 => c => Unit{}
    case Crit.Leaf{+k, v}:
      +h0 => +h1 => +h2 => c => Equal.trans(Maybe<&2, V>, Crit.lookup(V, Crit.union(~V, ~j, Crit.union(~V, ~j, a, b), cm), k), Crit.lookup(V, Crit.union(~V, ~j, a, Crit.union(~V, ~j, b, cm)), k), Some{v}, Equal.trans(Maybe<&2, V>, Crit.lookup(V, Crit.union(~V, ~j, Crit.union(~V, ~j, a, b), cm), k), Shared.Maybe.join(~V, ~j, Shared.Maybe.join(~V, ~j, Crit.lookup(V, a, k), Crit.lookup(V, b, k)), Crit.lookup(V, cm, k)), Crit.lookup(V, Crit.union(~V, ~j, a, Crit.union(~V, ~j, b, cm)), k), Equal.trans(Maybe<&2, V>, Crit.lookup(V, Crit.union(~V, ~j, Crit.union(~V, ~j, a, b), cm), k), Shared.Maybe.join(~V, ~j, Crit.lookup(V, Crit.union(~V, ~j, a, b), k), Crit.lookup(V, cm, k)), Shared.Maybe.join(~V, ~j, Shared.Maybe.join(~V, ~j, Crit.lookup(V, a, k), Crit.lookup(V, b, k)), Crit.lookup(V, cm, k)), Crit.union_go_lookup(~V, ~j, Crit.union(~V, ~j, a, b), cm, 0n, 0n, k)(Crit.union_go_wf(~V, ~j, a, b, 0n, [], False{})(h0)(h1)({==}))(h2), Equal.cong(Maybe<&2, V>, Maybe<&2, V>, t => Shared.Maybe.join(~V, ~j, t, Crit.lookup(V, cm, k)), Crit.lookup(V, Crit.union(~V, ~j, a, b), k), Shared.Maybe.join(~V, ~j, Crit.lookup(V, a, k), Crit.lookup(V, b, k)), Crit.union_go_lookup(~V, ~j, a, b, 0n, 0n, k)(h0)(h1))), Equal.trans(Maybe<&2, V>, Shared.Maybe.join(~V, ~j, Shared.Maybe.join(~V, ~j, Crit.lookup(V, a, k), Crit.lookup(V, b, k)), Crit.lookup(V, cm, k)), Shared.Maybe.join(~V, ~j, Crit.lookup(V, a, k), Shared.Maybe.join(~V, ~j, Crit.lookup(V, b, k), Crit.lookup(V, cm, k))), Crit.lookup(V, Crit.union(~V, ~j, a, Crit.union(~V, ~j, b, cm)), k), Shared.Maybe.join_assoc(~V, ~j, ~assoc, Crit.lookup(V, a, k), Crit.lookup(V, b, k), Crit.lookup(V, cm, k)), Equal.sym(Maybe<&2, V>, Crit.lookup(V, Crit.union(~V, ~j, a, Crit.union(~V, ~j, b, cm)), k), Shared.Maybe.join(~V, ~j, Crit.lookup(V, a, k), Shared.Maybe.join(~V, ~j, Crit.lookup(V, b, k), Crit.lookup(V, cm, k))), Equal.trans(Maybe<&2, V>, Crit.lookup(V, Crit.union(~V, ~j, a, Crit.union(~V, ~j, b, cm)), k), Shared.Maybe.join(~V, ~j, Crit.lookup(V, a, k), Crit.lookup(V, Crit.union(~V, ~j, b, cm), k)), Shared.Maybe.join(~V, ~j, Crit.lookup(V, a, k), Shared.Maybe.join(~V, ~j, Crit.lookup(V, b, k), Crit.lookup(V, cm, k))), Crit.union_go_lookup(~V, ~j, a, Crit.union(~V, ~j, b, cm), 0n, 0n, k)(h0)(Crit.union_go_wf(~V, ~j, b, cm, 0n, [], False{})(h1)(h2)({==})), Equal.cong(Maybe<&2, V>, Maybe<&2, V>, t => Shared.Maybe.join(~V, ~j, Crit.lookup(V, a, k), t), Crit.lookup(V, Crit.union(~V, ~j, b, cm), k), Shared.Maybe.join(~V, ~j, Crit.lookup(V, b, k), Crit.lookup(V, cm, k)), Crit.union_go_lookup(~V, ~j, b, cm, 0n, 0n, k)(h1)(h2)))))), c)
    case Crit.Fork{+r, +p, +e, +z, +o}:
      +h0 => +h1 => +h2 => +c => (
        Crit.sub_assoc_l.end(~V, ~j, ~assoc, r, e, a, b, cm)(h0)(h1)(h2)(Crit.sub.e(V, r, p, e, z, o, Crit.union(~V, ~j, a, Crit.union(~V, ~j, b, cm)), c)),
        (
          Crit.sub_assoc_l(~V, ~j, ~assoc, z, a, b, cm)(h0)(h1)(h2)(Crit.sub.z(V, r, p, e, z, o, Crit.union(~V, ~j, a, Crit.union(~V, ~j, b, cm)), c)),
          Crit.sub_assoc_l(~V, ~j, ~assoc, o, a, b, cm)(h0)(h1)(h2)(Crit.sub.o(V, r, p, e, z, o, Crit.union(~V, ~j, a, Crit.union(~V, ~j, b, cm)), c))
        )
      )

# Crit.union_assoc, with a, b and c used more than once
def Crit.union_assoc.go(~V: Data, ~j: V -> V -> V, ~assoc: @x: V -> @y: V -> @z: V -> {j(j(x, y), z) == j(x, j(y, z)): V}, +a: Crit<V>, +b: Crit<V>, +cm: Crit<V>) -> {Crit.wf(~V, a, 0n) == True{}: Bool} -> {Crit.wf(~V, b, 0n) == True{}: Bool} -> {Crit.wf(~V, cm, 0n) == True{}: Bool} -> {Crit.union(~V, ~j, Crit.union(~V, ~j, a, b), cm) == Crit.union(~V, ~j, a, Crit.union(~V, ~j, b, cm)): Crit<V>}:
  +h0 => +h1 => +h2 =>
    +w1 = Crit.union_go_wf(~V, ~j, Crit.union(~V, ~j, a, b), cm, 0n, [], False{})(Crit.union_go_wf(~V, ~j, a, b, 0n, [], False{})(h0)(h1)({==}))(h2)({==})
    +w2 = Crit.union_go_wf(~V, ~j, a, Crit.union(~V, ~j, b, cm), 0n, [], False{})(h0)(Crit.union_go_wf(~V, ~j, b, cm, 0n, [], False{})(h1)(h2)({==}))({==})
    Crit.det(~V, Crit.union(~V, ~j, Crit.union(~V, ~j, a, b), cm), Crit.union(~V, ~j, a, Crit.union(~V, ~j, b, cm)), 0n, 0n)(w1)(w2)(Crit.sub_assoc_r(~V, ~j, ~assoc, Crit.union(~V, ~j, Crit.union(~V, ~j, a, b), cm), a, b, cm)(h0)(h1)(h2)(Crit.sub_self(~V, Crit.union(~V, ~j, Crit.union(~V, ~j, a, b), cm), 0n)(w1)))(
      Crit.sub_assoc_l(~V, ~j, ~assoc, Crit.union(~V, ~j, a, Crit.union(~V, ~j, b, cm)), a, b, cm)(h0)(h1)(h2)(Crit.sub_self(~V, Crit.union(~V, ~j, a, Crit.union(~V, ~j, b, cm)), 0n)(w2))
    )

# a union of three is the same however it is grouped, when j is
law Crit.union_assoc:
  for ~V: Data
  for ~j: V -> V -> V
  for ~assoc: @x: V -> @y: V -> @z: V -> {j(j(x, y), z) == j(x, j(y, z)): V}
  for a: Crit<V>
  for b: Crit<V>
  for c: Crit<V>
  {Crit.wf(~V, a, 0n) == True{}: Bool} -> {Crit.wf(~V, b, 0n) == True{}: Bool} -> {Crit.wf(~V, c, 0n) == True{}: Bool} -> {
    Crit.union(~V, ~j, Crit.union(~V, ~j, a, b), c) == Crit.union(~V, ~j, a, Crit.union(~V, ~j, b, c)): Crit<V>
  }

def Crit.union_assoc(ty, j, assoc, a, b, c):
  Crit.union_assoc.go(~ty, ~j, ~assoc, a, b, c)

# a well formed fork is in its one shape
def Crit.mk_canon(~V: Data, +r: List<&2, U32>, +pos: Nat, e: Maybe<&2, V>, z: Crit<V>, o: Crit<V>, +lo: Nat) -> {
  Crit.wf(~V, Crit.Fork{r, pos, e, z, o}, lo) == True{}: Bool
} -> {Crit.mk(V, r, pos, e, z, o) == Crit.Fork{r, pos, e, z, o}: Crit<V>}:
  match e z o:
    case None{} Crit.Tip{} Crit.Tip{}:
      +h => Empty.absurd({Crit.mk(V, r, pos, None{}, Crit.Tip{}, Crit.Tip{}) == Crit.Fork{r, pos, None{}, Crit.Tip{}, Crit.Tip{}}: Crit<V>}, Shared.Bool.false_ne_true(Crit.wf.shape(~V, r, pos, None{}, Crit.Tip{}, Crit.Tip{}, lo)(h)))
    case None{} Crit.Tip{} Crit.Leaf{+kl2, +vl2}:
      +h => Empty.absurd({Crit.mk(V, r, pos, None{}, Crit.Tip{}, Crit.Leaf{kl2, vl2}) == Crit.Fork{r, pos, None{}, Crit.Tip{}, Crit.Leaf{kl2, vl2}}: Crit<V>}, Shared.Bool.false_ne_true(Crit.wf.shape(~V, r, pos, None{}, Crit.Tip{}, Crit.Leaf{kl2, vl2}, lo)(h)))
    case None{} Crit.Tip{} Crit.Fork{+fr2, +fp2, +fe2, +fz2, +fo2}:
      +h => Empty.absurd({Crit.mk(V, r, pos, None{}, Crit.Tip{}, Crit.Fork{fr2, fp2, fe2, fz2, fo2}) == Crit.Fork{r, pos, None{}, Crit.Tip{}, Crit.Fork{fr2, fp2, fe2, fz2, fo2}}: Crit<V>}, Shared.Bool.false_ne_true(Crit.wf.shape(~V, r, pos, None{}, Crit.Tip{}, Crit.Fork{fr2, fp2, fe2, fz2, fo2}, lo)(h)))
    case None{} Crit.Leaf{+kl, +vl} Crit.Tip{}:
      +h => Empty.absurd({Crit.mk(V, r, pos, None{}, Crit.Leaf{kl, vl}, Crit.Tip{}) == Crit.Fork{r, pos, None{}, Crit.Leaf{kl, vl}, Crit.Tip{}}: Crit<V>}, Shared.Bool.false_ne_true(Crit.wf.shape(~V, r, pos, None{}, Crit.Leaf{kl, vl}, Crit.Tip{}, lo)(h)))
    case None{} Crit.Leaf{+kl, +vl} Crit.Leaf{+kl2, +vl2}:
      +h =>
        %Equal.sym(List<&2, U32>, r, kl, Key.is_eq_sound(r, kl)(Crit.wf.rep_ok(~V, r, pos, None{}, Crit.Leaf{kl, vl}, Crit.Leaf{kl2, vl2}, lo)(h))): {
          Crit.Fork{kl, pos, None{}, Crit.Leaf{kl, vl}, Crit.Leaf{kl2, vl2}} == Crit.Fork{_, pos, None{}, Crit.Leaf{kl, vl}, Crit.Leaf{kl2, vl2}}: Crit<V>
        }
        {==}
    case None{} Crit.Leaf{+kl, +vl} Crit.Fork{+fr2, +fp2, +fe2, +fz2, +fo2}:
      +h =>
        %Equal.sym(List<&2, U32>, r, kl, Key.is_eq_sound(r, kl)(Crit.wf.rep_ok(~V, r, pos, None{}, Crit.Leaf{kl, vl}, Crit.Fork{fr2, fp2, fe2, fz2, fo2}, lo)(h))): {
          Crit.Fork{kl, pos, None{}, Crit.Leaf{kl, vl}, Crit.Fork{fr2, fp2, fe2, fz2, fo2}} == Crit.Fork{_, pos, None{}, Crit.Leaf{kl, vl}, Crit.Fork{fr2, fp2, fe2, fz2, fo2}}: Crit<V>
        }
        {==}
    case None{} Crit.Fork{+fr, +fp, +fe, +fz, +fo} Crit.Tip{}:
      +h => Empty.absurd({Crit.mk(V, r, pos, None{}, Crit.Fork{fr, fp, fe, fz, fo}, Crit.Tip{}) == Crit.Fork{r, pos, None{}, Crit.Fork{fr, fp, fe, fz, fo}, Crit.Tip{}}: Crit<V>}, Shared.Bool.false_ne_true(Crit.wf.shape(~V, r, pos, None{}, Crit.Fork{fr, fp, fe, fz, fo}, Crit.Tip{}, lo)(h)))
    case None{} Crit.Fork{+fr, +fp, +fe, +fz, +fo} Crit.Leaf{+kl2, +vl2}:
      +h =>
        %Equal.sym(List<&2, U32>, r, fr, Key.is_eq_sound(r, fr)(Crit.wf.rep_ok(~V, r, pos, None{}, Crit.Fork{fr, fp, fe, fz, fo}, Crit.Leaf{kl2, vl2}, lo)(h))): {
          Crit.Fork{fr, pos, None{}, Crit.Fork{fr, fp, fe, fz, fo}, Crit.Leaf{kl2, vl2}} == Crit.Fork{_, pos, None{}, Crit.Fork{fr, fp, fe, fz, fo}, Crit.Leaf{kl2, vl2}}: Crit<V>
        }
        {==}
    case None{} Crit.Fork{+fr, +fp, +fe, +fz, +fo} Crit.Fork{+fr2, +fp2, +fe2, +fz2, +fo2}:
      +h =>
        %Equal.sym(List<&2, U32>, r, fr, Key.is_eq_sound(r, fr)(Crit.wf.rep_ok(~V, r, pos, None{}, Crit.Fork{fr, fp, fe, fz, fo}, Crit.Fork{fr2, fp2, fe2, fz2, fo2}, lo)(h))): {
          Crit.Fork{fr, pos, None{}, Crit.Fork{fr, fp, fe, fz, fo}, Crit.Fork{fr2, fp2, fe2, fz2, fo2}} == Crit.Fork{_, pos, None{}, Crit.Fork{fr, fp, fe, fz, fo}, Crit.Fork{fr2, fp2, fe2, fz2, fo2}}: Crit<V>
        }
        {==}
    case Some{+v} Crit.Tip{} Crit.Tip{}:
      +h => Empty.absurd({Crit.mk(V, r, pos, Some{v}, Crit.Tip{}, Crit.Tip{}) == Crit.Fork{r, pos, Some{v}, Crit.Tip{}, Crit.Tip{}}: Crit<V>}, Shared.Bool.false_ne_true(Crit.wf.shape(~V, r, pos, Some{v}, Crit.Tip{}, Crit.Tip{}, lo)(h)))
    case Some{+v} Crit.Tip{} Crit.Leaf{+kl2, +vl2}:
      h => {==}
    case Some{+v} Crit.Tip{} Crit.Fork{+fr2, +fp2, +fe2, +fz2, +fo2}:
      h => {==}
    case Some{+v} Crit.Leaf{+kl, +vl} Crit.Tip{}:
      h => {==}
    case Some{+v} Crit.Leaf{+kl, +vl} Crit.Leaf{+kl2, +vl2}:
      h => {==}
    case Some{+v} Crit.Leaf{+kl, +vl} Crit.Fork{+fr2, +fp2, +fe2, +fz2, +fo2}:
      h => {==}
    case Some{+v} Crit.Fork{+fr, +fp, +fe, +fz, +fo} Crit.Tip{}:
      h => {==}
    case Some{+v} Crit.Fork{+fr, +fp, +fe, +fz, +fo} Crit.Leaf{+kl2, +vl2}:
      h => {==}
    case Some{+v} Crit.Fork{+fr, +fp, +fe, +fz, +fo} Crit.Fork{+fr2, +fp2, +fe2, +fz2, +fo2}:
      h => {==}

# a pick between a value and itself is the value
def Crit.pick_self(-A: Data, c: Bool, -x: A) -> {Bool.pick(A, c, x, x) == x: A}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

# a number compares equal to itself
def Crit.cmp_refl(a: Nat) -> {Nat.cmp(a, a) == EQ{}: Cmp}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Crit.cmp_refl(p)

# a choice whose test is False is its second branch
def Crit.when_false_eq(-A: Type, b: Bool, -k: Unit -> A, -e: Unit -> A) -> {b == False{}: Bool} -> {Shared.Bool.when(A, b, k, e) == e(Unit{}): A}:
  match b:
    case True{}:
      h => Empty.absurd({k(Unit{}) == e(Unit{}): A}, Shared.Bool.true_ne_false(h))
    case False{}:
      h => {==}

# a union of a well formed map with itself is the map, when j is idempotent
def Crit.union_idem.go(~V: Data, ~j: V -> V -> V, ~idem: @x: V -> {j(x, x) == x: V}, a: Crit<V>, +la: Nat) -> {Crit.wf(~V, a, la) == True{}: Bool} -> {
  Crit.union(~V, ~j, a, a) == a: Crit<V>
}:
  match a:
    case Crit.Tip{}:
      h => {==}
    case Crit.Leaf{+k, +v}:
      h =>
        %Equal.sym(Maybe<&2, Nat>, Key.diff(k, k), None{}, Key.diff_self(k)): {
          Crit.put(~V, ~(w => x => j(x, w)), Crit.Leaf{k, v}, 0n, Cur.of(k), k, v, _) == Crit.Leaf{k, v}: Crit<V>
        }
        %Equal.sym(V, j(v, v), v, idem(v)): {Crit.Leaf{k, _} == Crit.Leaf{k, v}: Crit<V>}
        {==}
    case Crit.Fork{+ra, +pa, +ea, +za, +oa}:
      +h => Equal.trans(
        Crit<V>,
        Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, Crit.Fork{ra, pa, ea, za, oa}),
        Crit.union.at(~V, ~j, Nat.cmp(pa, pa), ra, pa, ea, ra, pa, ea, zs => os => Crit.mk(V, Bool.pick(List<&2, U32>, Maybe.is_some(&2, V, ea), ra, ra), pa, Shared.Maybe.join(~V, ~j, ea, ea), zs, os), u2 => Crit.union(~V, ~j, za, za), u2 => Crit.union(~V, ~j, oa, oa), u2 => Crit.union(~V, ~j, za, Crit.Fork{ra, pa, ea, za, oa}), u2 => Crit.union(~V, ~j, oa, Crit.Fork{ra, pa, ea, za, oa}), u2 => Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, za), u2 => Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, oa), za, oa, za, oa),
        Crit.Fork{ra, pa, ea, za, oa},
        Crit.when_false_eq(
          Crit<V>,
          Bool.and(Crit.above(Key.diff(ra, ra), pa), Crit.above(Key.diff(ra, ra), pa)),
          u => Crit.join(V, Crit.Fork{ra, pa, ea, za, oa}, Crit.Fork{ra, pa, ea, za, oa}, Maybe.default(&2, Nat, Key.diff(ra, ra), 0n)),
          u => Crit.union.at(~V, ~j, Nat.cmp(pa, pa), ra, pa, ea, ra, pa, ea, zs => os => Crit.mk(V, Bool.pick(List<&2, U32>, Maybe.is_some(&2, V, ea), ra, ra), pa, Shared.Maybe.join(~V, ~j, ea, ea), zs, os), u2 => Crit.union(~V, ~j, za, za), u2 => Crit.union(~V, ~j, oa, oa), u2 => Crit.union(~V, ~j, za, Crit.Fork{ra, pa, ea, za, oa}), u2 => Crit.union(~V, ~j, oa, Crit.Fork{ra, pa, ea, za, oa}), u2 => Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, za), u2 => Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, oa), za, oa, za, oa)
        )((
          %Equal.sym(Maybe<&2, Nat>, Key.diff(ra, ra), None{}, Key.diff_self(ra)): {Bool.and(Crit.above(_, pa), Crit.above(_, pa)) == False{}: Bool}
          {==}
        )),
        Equal.trans(
          Crit<V>,
          Crit.union.at(~V, ~j, Nat.cmp(pa, pa), ra, pa, ea, ra, pa, ea, zs => os => Crit.mk(V, Bool.pick(List<&2, U32>, Maybe.is_some(&2, V, ea), ra, ra), pa, Shared.Maybe.join(~V, ~j, ea, ea), zs, os), u2 => Crit.union(~V, ~j, za, za), u2 => Crit.union(~V, ~j, oa, oa), u2 => Crit.union(~V, ~j, za, Crit.Fork{ra, pa, ea, za, oa}), u2 => Crit.union(~V, ~j, oa, Crit.Fork{ra, pa, ea, za, oa}), u2 => Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, za), u2 => Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, oa), za, oa, za, oa),
          Crit.mk(V, Bool.pick(List<&2, U32>, Maybe.is_some(&2, V, ea), ra, ra), pa, Shared.Maybe.join(~V, ~j, ea, ea), Crit.union(~V, ~j, za, za), Crit.union(~V, ~j, oa, oa)),
          Crit.Fork{ra, pa, ea, za, oa},
          Equal.cong(Cmp, Crit<V>, c => Crit.union.at(~V, ~j, c, ra, pa, ea, ra, pa, ea, zs => os => Crit.mk(V, Bool.pick(List<&2, U32>, Maybe.is_some(&2, V, ea), ra, ra), pa, Shared.Maybe.join(~V, ~j, ea, ea), zs, os), u2 => Crit.union(~V, ~j, za, za), u2 => Crit.union(~V, ~j, oa, oa), u2 => Crit.union(~V, ~j, za, Crit.Fork{ra, pa, ea, za, oa}), u2 => Crit.union(~V, ~j, oa, Crit.Fork{ra, pa, ea, za, oa}), u2 => Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, za), u2 => Crit.union(~V, ~j, Crit.Fork{ra, pa, ea, za, oa}, oa), za, oa, za, oa), Nat.cmp(pa, pa), EQ{}, Crit.cmp_refl(pa)),
          Equal.trans(
            Crit<V>,
            Crit.mk(V, Bool.pick(List<&2, U32>, Maybe.is_some(&2, V, ea), ra, ra), pa, Shared.Maybe.join(~V, ~j, ea, ea), Crit.union(~V, ~j, za, za), Crit.union(~V, ~j, oa, oa)),
            Crit.mk(V, ra, pa, ea, za, oa),
            Crit.Fork{ra, pa, ea, za, oa},
            (
              %Equal.sym(List<&2, U32>, Bool.pick(List<&2, U32>, Maybe.is_some(&2, V, ea), ra, ra), ra, Crit.pick_self(List<&2, U32>, Maybe.is_some(&2, V, ea), ra)): {
                Crit.mk(V, _, pa, Shared.Maybe.join(~V, ~j, ea, ea), Crit.union(~V, ~j, za, za), Crit.union(~V, ~j, oa, oa)) == Crit.mk(V, ra, pa, ea, za, oa): Crit<V>
              }
              %Equal.sym(Maybe<&2, V>, Shared.Maybe.join(~V, ~j, ea, ea), ea, Shared.Maybe.join_idem(~V, ~j, ~idem, ea)): {
                Crit.mk(V, ra, pa, _, Crit.union(~V, ~j, za, za), Crit.union(~V, ~j, oa, oa)) == Crit.mk(V, ra, pa, ea, za, oa): Crit<V>
              }
              %Equal.sym(Crit<V>, Crit.union(~V, ~j, za, za), za, Crit.union_idem.go(~V, ~j, ~idem, za, 1n+pa)(Crit.wf.wf_z(~V, ra, pa, ea, za, oa, la)(h))): {
                Crit.mk(V, ra, pa, ea, _, Crit.union(~V, ~j, oa, oa)) == Crit.mk(V, ra, pa, ea, za, oa): Crit<V>
              }
              %Equal.sym(Crit<V>, Crit.union(~V, ~j, oa, oa), oa, Crit.union_idem.go(~V, ~j, ~idem, oa, 1n+pa)(Crit.wf.wf_o(~V, ra, pa, ea, za, oa, la)(h))): {
                Crit.mk(V, ra, pa, ea, za, _) == Crit.mk(V, ra, pa, ea, za, oa): Crit<V>
              }
              {==}
            ),
            Crit.mk_canon(~V, ra, pa, ea, za, oa, la)(h)
          )
        )
      )

# a union with itself is the map, when j is
law Crit.union_idem:
  for ~V: Data
  for ~j: V -> V -> V
  for ~idem: @x: V -> {j(x, x) == x: V}
  for a: Crit<V>
  {Crit.wf(~V, a, 0n) == True{}: Bool} -> {Crit.union(~V, ~j, a, a) == a: Crit<V>}

def Crit.union_idem(ty, j, idem, a):
  h => Crit.union_idem.go(~ty, ~j, ~idem, a, 0n)(h)

# the keys after those of m are keys of b when all are
def Crit.within_rest(-V: Data, m: Crit<V>, +rest: List<&2, Bind<V>>, +b: Crit<V>) -> {Crit.within.go(V, Crit.entries.go(V, m, rest), b) == True{}: Bool} -> {Crit.within.go(V, rest, b) == True{}: Bool}:
  match m:
    case Crit.Tip{}:
      h => h
    case Crit.Leaf{+k, v}:
      h => Shared.List.all.if_rest(Crit.has(V, b, k), u => Crit.within.go(V, rest, b))(h)
    case Crit.Fork{r, p, None{}, +z, +o}:
      h => Crit.within_rest(V, o, rest, b)(Crit.within_rest(V, z, Crit.entries.go(V, o, rest), b)(h))
    case Crit.Fork{+r, p, Some{+v}, +z, +o}:
      h => Crit.within_rest(V, o, rest, b)(Crit.within_rest(V, z, Crit.entries.go(V, o, rest), b)(Shared.List.all.if_rest(Crit.has(V, b, r), u => Crit.within.go(V, Crit.entries.go(V, z, Crit.entries.go(V, o, rest)), b))(h)))

# the keys of m are keys of b when its keys before rest are
def Crit.within_all(~V: Data, m: Crit<V>, +rest: List<&2, Bind<V>>, +b: Crit<V>) -> {Crit.within.go(V, Crit.entries.go(V, m, rest), b) == True{}: Bool} -> {Crit.all(~V, ~Crit<V>, ~(x => k => Crit.has(V, x, k)), m, b) == True{}: Bool}:
  match m:
    case Crit.Tip{}:
      h => {==}
    case Crit.Leaf{+k, v}:
      h => Shared.List.all.if_hit(Crit.has(V, b, k), u => Crit.within.go(V, rest, b))(h)
    case Crit.Fork{+r, +p, None{}, +z, +o}:
      +h => Crit.all.intro(~V, ~Crit<V>, ~(x => k => Crit.has(V, x, k)), r, p, None{}, z, o, b)({==})(Crit.within_all(~V, z, Crit.entries.go(V, o, rest), b)(h))(
        Crit.within_all(~V, o, rest, b)(Crit.within_rest(V, z, Crit.entries.go(V, o, rest), b)(h))
      )
    case Crit.Fork{+r, +p, Some{+v}, +z, +o}:
      +h =>
        +t = Shared.List.all.if_rest(Crit.has(V, b, r), u => Crit.within.go(V, Crit.entries.go(V, z, Crit.entries.go(V, o, rest)), b))(h)
        Crit.all.intro(~V, ~Crit<V>, ~(x => k => Crit.has(V, x, k)), r, p, Some{v}, z, o, b)(Shared.List.all.if_hit(Crit.has(V, b, r), u => Crit.within.go(V, Crit.entries.go(V, z, Crit.entries.go(V, o, rest)), b))(h))(
          Crit.within_all(~V, z, Crit.entries.go(V, o, rest), b)(t)
        )(Crit.within_all(~V, o, rest, b)(Crit.within_rest(V, z, Crit.entries.go(V, o, rest), b)(t)))

# a map well formed below any bit holds a key exactly when it reads some
def Crit.has_lookup(~V: Data, +m: Crit<V>, +lo: Nat, +k: List<&2, U32>) -> {Crit.wf(~V, m, lo) == True{}: Bool} -> {Crit.has(V, m, k) == Maybe.is_some(&2, V, Crit.lookup(V, m, k)): Bool}:
  h => Equal.cong(Maybe<&2, V>, Bool, x => Maybe.is_some(&2, V, x), Crit.get(V, m, k), Crit.lookup(V, m, k), Crit.get_lookup.lo(~V, m, lo, k)(h))

# a key on the side b of a well formed fork is held by the side when held by
# the fork
def Crit.has_route(~V: Data, +rep: List<&2, U32>, +pos: Nat, +e: Maybe<&2, V>, +z: Crit<V>, +o: Crit<V>, +lo: Nat, +k: List<&2, U32>, b: Bool) -> {Crit.wf(~V, Crit.Fork{rep, pos, e, z, o}, lo) == True{}: Bool} -> {
  Key.side(k, pos) == Some{b}: Maybe<&2, Bool>
} -> {Crit.has(V, Bool.pick(Crit<V>, b, o, z), k) == Crit.has(V, Crit.Fork{rep, pos, e, z, o}, k): Bool}:
  match b:
    case True{}:
      +h => +hs => Equal.trans(
        Bool,
        Crit.has(V, o, k),
        Maybe.is_some(&2, V, Crit.lookup(V, o, k)),
        Crit.has(V, Crit.Fork{rep, pos, e, z, o}, k),
        Crit.has_lookup(~V, o, 1n+pos, k)(Crit.wf.wf_o(~V, rep, pos, e, z, o, lo)(h)),
        Equal.trans(
          Bool,
          Maybe.is_some(&2, V, Crit.lookup(V, o, k)),
          Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k)),
          Crit.has(V, Crit.Fork{rep, pos, e, z, o}, k),
          Equal.cong(Maybe<&2, V>, Bool, x => Maybe.is_some(&2, V, x), Crit.lookup(V, o, k), Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k), Equal.sym(Maybe<&2, V>, Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k), Crit.lookup(V, o, k), Crit.route_side(~V, rep, pos, e, z, o, lo, k, True{})(h)(hs))),
          Equal.sym(Bool, Crit.has(V, Crit.Fork{rep, pos, e, z, o}, k), Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k)), Crit.has_lookup(~V, Crit.Fork{rep, pos, e, z, o}, lo, k)(h))
        )
      )
    case False{}:
      +h => +hs => Equal.trans(
        Bool,
        Crit.has(V, z, k),
        Maybe.is_some(&2, V, Crit.lookup(V, z, k)),
        Crit.has(V, Crit.Fork{rep, pos, e, z, o}, k),
        Crit.has_lookup(~V, z, 1n+pos, k)(Crit.wf.wf_z(~V, rep, pos, e, z, o, lo)(h)),
        Equal.trans(
          Bool,
          Maybe.is_some(&2, V, Crit.lookup(V, z, k)),
          Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k)),
          Crit.has(V, Crit.Fork{rep, pos, e, z, o}, k),
          Equal.cong(Maybe<&2, V>, Bool, x => Maybe.is_some(&2, V, x), Crit.lookup(V, z, k), Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k), Equal.sym(Maybe<&2, V>, Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k), Crit.lookup(V, z, k), Crit.route_side(~V, rep, pos, e, z, o, lo, k, False{})(h)(hs))),
          Equal.sym(Bool, Crit.has(V, Crit.Fork{rep, pos, e, z, o}, k), Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k)), Crit.has_lookup(~V, Crit.Fork{rep, pos, e, z, o}, lo, k)(h))
        )
      )

# Crit.has_down for the end of a fork
def Crit.has_down_end(~V: Data, +r3: List<&2, U32>, e3: Maybe<&2, V>, +rep: List<&2, U32>, +pos: Nat, +e: Maybe<&2, V>, +z: Crit<V>, +o: Crit<V>, +lo: Nat, +r2: List<&2, U32>, +b: Bool) -> {
  Bool.or(Maybe.is_none(&2, V, e3), Crit.has(V, Crit.Fork{rep, pos, e, z, o}, r3)) == True{}: Bool
} -> {Bool.or(Maybe.is_none(&2, V, e3), Place.has(Place{r2, pos, b}, r3)) == True{}: Bool} -> {Crit.wf(~V, Crit.Fork{rep, pos, e, z, o}, lo) == True{}: Bool} -> {
  Bool.or(Maybe.is_none(&2, V, e3), Crit.has(V, Bool.pick(Crit<V>, b, o, z), r3)) == True{}: Bool
}:
  match e3:
    case None{}:
      c => a => h => {==}
    case Some{w}:
      c => a => h => Equal.trans(Bool, Crit.has(V, Bool.pick(Crit<V>, b, o, z), r3), Crit.has(V, Crit.Fork{rep, pos, e, z, o}, r3), True{}, Crit.has_route(~V, rep, pos, e, z, o, lo, r3, b)(h)(Place.has_side(r2, pos, b, r3)(a)), c)

# keys of a well formed fork, on its side b, are keys of that side
def Crit.has_down(~V: Data, m: Crit<V>, +rep: List<&2, U32>, +pos: Nat, +e: Maybe<&2, V>, +z: Crit<V>, +o: Crit<V>, +lo: Nat, +r2: List<&2, U32>, +b: Bool) -> {Crit.all(~V, ~Crit<V>, ~(x => k => Crit.has(V, x, k)), m, Crit.Fork{rep, pos, e, z, o}) == True{}: Bool} -> {
  Crit.all(~V, ~Place, ~Place.has, m, Place{r2, pos, b}) == True{}: Bool
} -> {Crit.wf(~V, Crit.Fork{rep, pos, e, z, o}, lo) == True{}: Bool} -> {Crit.all(~V, ~Crit<V>, ~(x => k => Crit.has(V, x, k)), m, Bool.pick(Crit<V>, b, o, z)) == True{}: Bool}:
  match m:
    case Crit.Tip{}:
      c => a => h => {==}
    case Crit.Leaf{+k, v}:
      c => a => h => Equal.trans(Bool, Crit.has(V, Bool.pick(Crit<V>, b, o, z), k), Crit.has(V, Crit.Fork{rep, pos, e, z, o}, k), True{}, Crit.has_route(~V, rep, pos, e, z, o, lo, k, b)(h)(Place.has_side(r2, pos, b, k)(a)), c)
    case Crit.Fork{+r3, +p3, +e3, +z3, +o3}:
      +c => +a => +h => Crit.all.intro(~V, ~Crit<V>, ~(x => k => Crit.has(V, x, k)), r3, p3, e3, z3, o3, Bool.pick(Crit<V>, b, o, z))(
        Crit.has_down_end(~V, r3, e3, rep, pos, e, z, o, lo, r2, b)(Crit.all.hit(~V, ~Crit<V>, ~(x => k => Crit.has(V, x, k)), r3, p3, e3, z3, o3, Crit.Fork{rep, pos, e, z, o})(c))(Crit.all.hit(~V, ~Place, ~Place.has, r3, p3, e3, z3, o3, Place{r2, pos, b})(a))(h)
      )(Crit.has_down(~V, z3, rep, pos, e, z, o, lo, r2, b)(Crit.all.z(~V, ~Crit<V>, ~(x => k => Crit.has(V, x, k)), r3, p3, e3, z3, o3, Crit.Fork{rep, pos, e, z, o})(c))(Crit.all.z(~V, ~Place, ~Place.has, r3, p3, e3, z3, o3, Place{r2, pos, b})(a))(h))(
        Crit.has_down(~V, o3, rep, pos, e, z, o, lo, r2, b)(Crit.all.o(~V, ~Crit<V>, ~(x => k => Crit.has(V, x, k)), r3, p3, e3, z3, o3, Crit.Fork{rep, pos, e, z, o})(c))(Crit.all.o(~V, ~Place, ~Place.has, r3, p3, e3, z3, o3, Place{r2, pos, b})(a))(h)
      )

# a key that a map holds, whose keys pass p, passes p
def Crit.in_pass(~V: Data, ~G: Data, ~p: G -> List<&2, U32> -> Bool, +m: Crit<V>, +g: G, +q: List<&2, U32>) -> {Crit.all(~V, ~G, ~p, m, g) == True{}: Bool} -> {
  Maybe.is_some(&2, V, Crit.lookup(V, m, q)) == True{}: Bool
} -> {p(g)(q) == True{}: Bool}:
  +a => +s => Crit.true_of(p(g)(q))(
    t => Crit.clash(Maybe.is_some(&2, V, Crit.lookup(V, m, q)), True{}, False{}, s, Equal.cong(Maybe<&2, V>, Bool, x => Maybe.is_some(&2, V, x), Crit.lookup(V, m, q), None{}, Crit.lookup_all(~V, ~G, ~p, m, g, q)(a)(t)), Shared.Bool.true_ne_false)
  )

# an end read at some key is some
def Crit.ended_some(-V: Data, +r: List<&2, U32>, e: Maybe<&2, V>, +q: List<&2, U32>) -> {Maybe.is_some(&2, V, Crit.ended(V, r, e, q)) == True{}: Bool} -> {Maybe.is_some(&2, V, e) == True{}: Bool}:
  match e:
    case None{}:
      h => h
    case Some{w}:
      h => {==}

# a choice of three that is some has a part that is some
def Crit.or3_is_some(-V: Data, -T: Type, a: Maybe<&2, V>, b: Maybe<&2, V>, -c: Maybe<&2, V>) -> ({Maybe.is_some(&2, V, a) == True{}: Bool} -> T) -> ({Maybe.is_some(&2, V, b) == True{}: Bool} -> T) -> (
  {Maybe.is_some(&2, V, c) == True{}: Bool} -> T
) -> {Maybe.is_some(&2, V, Maybe.or(&2, V, a, Maybe.or(&2, V, b, c))) == True{}: Bool} -> T:
  match a b:
    case Some{x} y:
      f1 => f2 => f3 => h => f1(h)
    case None{} Some{y}:
      f1 => f2 => f3 => h => f2(h)
    case None{} None{}:
      f1 => f2 => f3 => h => f3(h)

# a map that reads some key holds one entry at least
def Crit.size_some(-V: Data, m: Crit<V>, +q: List<&2, U32>) -> {Maybe.is_some(&2, V, Crit.lookup(V, m, q)) == True{}: Bool} -> {Nat.is_le(1n, Crit.size(V, m)) == True{}: Bool}:
  match m:
    case Crit.Tip{}:
      h => Empty.absurd({Nat.is_le(1n, 0n) == True{}: Bool}, Shared.Bool.false_ne_true(h))
    case Crit.Leaf{k, v}:
      h => {==}
    case Crit.Fork{+r, +p, +e, +z, +o}:
      Crit.or3_is_some(V, {Nat.is_le(1n, Crit.size(V, Crit.Fork{r, p, e, z, o})) == True{}: Bool}, Crit.ended(V, r, e, q), Crit.lookup(V, z, q), Crit.lookup(V, o, q))(
        he =>
          %Equal.sym(Bool, Maybe.is_some(&2, V, e), True{}, Crit.ended_some(V, r, e, q)(he)): {Nat.is_le(1n, Shared.Nat.add_if(_, Nat.add(Crit.size(V, z), Crit.size(V, o)))) == True{}: Bool}
          Shared.Nat.le_zero(Nat.add(Crit.size(V, z), Crit.size(V, o)))
      )(
        hz => Shared.Nat.le_add_if(Maybe.is_some(&2, V, e), 1n, Nat.add(Crit.size(V, z), Crit.size(V, o)))(
          Shared.Nat.le_trans(1n, Crit.size(V, z), Nat.add(Crit.size(V, z), Crit.size(V, o)))(Crit.size_some(V, z, q)(hz))(Shared.Nat.le_add_first(Crit.size(V, z), Crit.size(V, o)))
        )
      )(
        ho => Shared.Nat.le_add_if(Maybe.is_some(&2, V, e), 1n, Nat.add(Crit.size(V, z), Crit.size(V, o)))(
          Shared.Nat.le_trans(1n, Crit.size(V, o), Nat.add(Crit.size(V, z), Crit.size(V, o)))(Crit.size_some(V, o, q)(ho))(Shared.Nat.le_add(Crit.size(V, z), Crit.size(V, o)))
        )
      )

# a fork holds at least as many entries as its zero side
def Crit.size_z(-V: Data, +r: List<&2, U32>, +p: Nat, +e: Maybe<&2, V>, +z: Crit<V>, +o: Crit<V>) -> {Nat.is_le(Crit.size(V, z), Crit.size(V, Crit.Fork{r, p, e, z, o})) == True{}: Bool}:
  Shared.Nat.le_add_if(Maybe.is_some(&2, V, e), Crit.size(V, z), Nat.add(Crit.size(V, z), Crit.size(V, o)))(Shared.Nat.le_add_first(Crit.size(V, z), Crit.size(V, o)))

# a fork holds at least as many entries as its one side
def Crit.size_o(-V: Data, +r: List<&2, U32>, +p: Nat, +e: Maybe<&2, V>, +z: Crit<V>, +o: Crit<V>) -> {Nat.is_le(Crit.size(V, o), Crit.size(V, Crit.Fork{r, p, e, z, o})) == True{}: Bool}:
  Shared.Nat.le_add_if(Maybe.is_some(&2, V, e), Crit.size(V, o), Nat.add(Crit.size(V, z), Crit.size(V, o)))(Shared.Nat.le_add(Crit.size(V, z), Crit.size(V, o)))

# a well formed fork whose keys a fork at one bit holds is no larger, when its
# sides are no larger
def Crit.size_eq(~V: Data, +ra: List<&2, U32>, +pa: Nat, ea: Maybe<&2, V>, +za: Crit<V>, +oa: Crit<V>, +rb: List<&2, U32>, +pb: Nat, +eb: Maybe<&2, V>, +zb: Crit<V>, +ob: Crit<V>, +la: Nat, +lb: Nat) -> {
  Crit.wf(~V, Crit.Fork{ra, pa, ea, za, oa}, la) == True{}: Bool
} -> {Crit.wf(~V, Crit.Fork{rb, pb, eb, zb, ob}, lb) == True{}: Bool} -> {Crit.all(~V, ~Crit<V>, ~(x => k => Crit.has(V, x, k)), Crit.Fork{ra, pa, ea, za, oa}, Crit.Fork{rb, pb, eb, zb, ob}) == True{}: Bool} -> {pa == pb: Nat} -> {Nat.is_le(Crit.size(V, za), Crit.size(V, zb)) == True{}: Bool} -> {Nat.is_le(Crit.size(V, oa), Crit.size(V, ob)) == True{}: Bool} -> {Nat.is_le(Crit.size(V, Crit.Fork{ra, pa, ea, za, oa}), Crit.size(V, Crit.Fork{rb, pb, eb, zb, ob})) == True{}: Bool}:
  match ea:
    case None{}:
      ha => hb => hh => eqp => hz => ho => Shared.Nat.le_add_if(Maybe.is_some(&2, V, eb), Nat.add(Crit.size(V, za), Crit.size(V, oa)), Nat.add(Crit.size(V, zb), Crit.size(V, ob)))(
        Shared.Nat.add_le(Crit.size(V, za), Crit.size(V, zb), Crit.size(V, oa), Crit.size(V, ob))(hz)(ho)
      )
    case Some{+u}:
      +ha => +hb => hh => eqp => hz => ho =>
        +inb = Equal.trans(
          Bool,
          Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, ra)),
          Crit.has(V, Crit.Fork{rb, pb, eb, zb, ob}, ra),
          True{},
          Equal.sym(Bool, Crit.has(V, Crit.Fork{rb, pb, eb, zb, ob}, ra), Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, ra)), Crit.has_lookup(~V, Crit.Fork{rb, pb, eb, zb, ob}, lb, ra)(hb)),
          Crit.all.hit(~V, ~Crit<V>, ~(x => k => Crit.has(V, x, k)), ra, pa, Some{u}, za, oa, Crit.Fork{rb, pb, eb, zb, ob})(hh)
        )
        %Equal.sym(
          Bool,
          Maybe.is_some(&2, V, eb),
          True{},
          Crit.ended_some(V, rb, eb, ra)(
            Equal.trans(
              Bool,
              Maybe.is_some(&2, V, Crit.ended(V, rb, eb, ra)),
              Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, ra)),
              True{},
              Equal.cong(Maybe<&2, V>, Bool, x => Maybe.is_some(&2, V, x), Crit.ended(V, rb, eb, ra), Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, ra), Equal.sym(Maybe<&2, V>, Crit.lookup(V, Crit.Fork{rb, pb, eb, zb, ob}, ra), Crit.ended(V, rb, eb, ra), Crit.route_end(~V, rb, pb, eb, zb, ob, lb, ra)(hb)(Crit.side_len(ra, pb)((
                %eqp: {Nat.is_eq(List.length(&2, Bool, Key.bits(ra)), _) == True{}: Bool}
                Crit.wf.rep_ok(~V, ra, pa, Some{u}, za, oa, la)(ha)
              ))))),
              inb
            )
          )
        ): {Nat.is_le(1n+Nat.add(Crit.size(V, za), Crit.size(V, oa)), Shared.Nat.add_if(_, Nat.add(Crit.size(V, zb), Crit.size(V, ob)))) == True{}: Bool}
        Shared.Nat.add_if_le(True{}, Nat.add(Crit.size(V, za), Crit.size(V, oa)), Nat.add(Crit.size(V, zb), Crit.size(V, ob)))(Shared.Nat.add_le(Crit.size(V, za), Crit.size(V, zb), Crit.size(V, oa), Crit.size(V, ob))(hz)(ho))

# a key of a well formed fork held by a map is read there
def Crit.has_some(~V: Data, +x: Crit<V>, +lx: Nat, +q: List<&2, U32>) -> {Crit.wf(~V, x, lx) == True{}: Bool} -> {Crit.has(V, x, q) == True{}: Bool} -> {Maybe.is_some(&2, V, Crit.lookup(V, x, q)) == True{}: Bool}:
  h => t => Equal.trans(Bool, Maybe.is_some(&2, V, Crit.lookup(V, x, q)), Crit.has(V, x, q), True{}, Equal.sym(Bool, Crit.has(V, x, q), Maybe.is_some(&2, V, Crit.lookup(V, x, q)), Crit.has_lookup(~V, x, lx, q)(h)), t)

# a well formed fork whose keys a well formed fork holds is no larger, by
# how their bits compare (c)
def Crit.size_cmp(~V: Data, +ra: List<&2, U32>, +pa: Nat, +ea: Maybe<&2, V>, +za: Crit<V>, +oa: Crit<V>, +rb: List<&2, U32>, +pb: Nat, +eb: Maybe<&2, V>, +zb: Crit<V>, +ob: Crit<V>, +la: Nat, +lb: Nat, c: Cmp) -> {Nat.cmp(pa, pb) == c: Cmp} -> {Crit.wf(~V, Crit.Fork{ra, pa, ea, za, oa}, la) == True{}: Bool} -> {Crit.wf(~V, Crit.Fork{rb, pb, eb, zb, ob}, lb) == True{}: Bool} -> {
  Crit.all(~V, ~Crit<V>, ~(x => k => Crit.has(V, x, k)), Crit.Fork{ra, pa, ea, za, oa}, Crit.Fork{rb, pb, eb, zb, ob}) == True{}: Bool
} -> ({pa == pb: Nat} -> {Nat.is_le(Crit.size(V, za), Crit.size(V, zb)) == True{}: Bool}) -> ({pa == pb: Nat} -> {Nat.is_le(Crit.size(V, oa), Crit.size(V, ob)) == True{}: Bool}) -> ({Nat.is_lt(pb, pa) == True{}: Bool} -> {Crit.all(~V, ~Crit<V>, ~(x => k => Crit.has(V, x, k)), Crit.Fork{ra, pa, ea, za, oa}, zb) == True{}: Bool} -> {Nat.is_le(Crit.size(V, Crit.Fork{ra, pa, ea, za, oa}), Crit.size(V, zb)) == True{}: Bool}) -> ({Nat.is_lt(pb, pa) == True{}: Bool} -> {Crit.all(~V, ~Crit<V>, ~(x => k => Crit.has(V, x, k)), Crit.Fork{ra, pa, ea, za, oa}, ob) == True{}: Bool} -> {Nat.is_le(Crit.size(V, Crit.Fork{ra, pa, ea, za, oa}), Crit.size(V, ob)) == True{}: Bool}) -> {Nat.is_le(Crit.size(V, Crit.Fork{ra, pa, ea, za, oa}), Crit.size(V, Crit.Fork{rb, pb, eb, zb, ob})) == True{}: Bool}:
  match c:
    case EQ{}:
      hc => ha => hb => hh => iz => io => igz => igo =>
        +eqp = Crit.cmp_eq(pa, pb)(hc)
        Crit.size_eq(~V, ra, pa, ea, za, oa, rb, pb, eb, zb, ob, la, lb)(ha)(hb)(hh)(eqp)(iz(eqp))(io(eqp))
    case LT{}:
      hc => +ha => +hb => +hh => iz => io => igz => igo =>
        +lt = Crit.cmp_lt(pa, pb)(hc)
        Empty.absurd(
          {Nat.is_le(Crit.size(V, Crit.Fork{ra, pa, ea, za, oa}), Crit.size(V, Crit.Fork{rb, pb, eb, zb, ob})) == True{}: Bool},
          Crit.two(~V, ra, pa, ea, za, oa, la, Empty)(ha)(
            +q1 => +q2 => s1 => s2 => ne => Crit.same_contra(q1, q2, pa)(
              Equal.trans(
                Maybe<&2, Bool>,
                Key.side(q1, pa),
                Key.side(rb, pa),
                Key.side(q2, pa),
                Crit.same_side(~V, rb, pb, eb, zb, ob, lb, q1, pa)(hb)(lt)(Crit.has_some(~V, Crit.Fork{rb, pb, eb, zb, ob}, lb, q1)(hb)(Crit.in_pass(~V, ~Crit<V>, ~(x => k => Crit.has(V, x, k)), Crit.Fork{ra, pa, ea, za, oa}, Crit.Fork{rb, pb, eb, zb, ob}, q1)(hh)(s1))),
                Equal.sym(Maybe<&2, Bool>, Key.side(q2, pa), Key.side(rb, pa), Crit.same_side(~V, rb, pb, eb, zb, ob, lb, q2, pa)(hb)(lt)(Crit.has_some(~V, Crit.Fork{rb, pb, eb, zb, ob}, lb, q2)(hb)(Crit.in_pass(~V, ~Crit<V>, ~(x => k => Crit.has(V, x, k)), Crit.Fork{ra, pa, ea, za, oa}, Crit.Fork{rb, pb, eb, zb, ob}, q2)(hh)(s2))))
              )
            )(ne)
          )
        )
    case GT{}:
      hc => +ha => +hb => +hh => iz => io => igz => igo =>
        +gt = Crit.cmp_gt(pa, pb)(hc)
        +ar = Key.agree_sym(ra, rb, pb)(Crit.in_fork_agree(~V, rb, pb, eb, zb, ob, lb, ra)(hb)(Crit.has_some(~V, Crit.Fork{rb, pb, eb, zb, ob}, lb, ra)(hb)(Crit.rep_pass(~V, ~Crit<V>, ~(x => k => Crit.has(V, x, k)), Crit.Fork{ra, pa, ea, za, oa}, la, Crit.Fork{rb, pb, eb, zb, ob}, [])(ha)(hh)({==}))))
        +alla = Crit.fork_place(~V, ra, pa, ea, za, oa, la, rb, pb, Cur.bit(Key.at(ra, pb)))(ha)(gt)(ar)(Crit.side_of(ra, pb, Cur.bit(Key.at(ra, pb)))(Crit.rep_not_done(~V, ra, pa, ea, za, oa, la, pb)(ha)(gt))({==}))
        Crit.bool_split({Nat.is_le(Crit.size(V, Crit.Fork{ra, pa, ea, za, oa}), Crit.size(V, Crit.Fork{rb, pb, eb, zb, ob})) == True{}: Bool}, Cur.bit(Key.at(ra, pb)))(
          t3 => Shared.Nat.le_trans(Crit.size(V, Crit.Fork{ra, pa, ea, za, oa}), Crit.size(V, ob), Crit.size(V, Crit.Fork{rb, pb, eb, zb, ob}))(
            igo(gt)(Crit.has_down(~V, Crit.Fork{ra, pa, ea, za, oa}, rb, pb, eb, zb, ob, lb, rb, True{})(hh)(Crit.all_place_b(~V, Crit.Fork{ra, pa, ea, za, oa}, rb, pb, Cur.bit(Key.at(ra, pb)), True{})(t3)(alla))(hb))
          )(Crit.size_o(V, rb, pb, eb, zb, ob))
        )(
          t3 => Shared.Nat.le_trans(Crit.size(V, Crit.Fork{ra, pa, ea, za, oa}), Crit.size(V, zb), Crit.size(V, Crit.Fork{rb, pb, eb, zb, ob}))(
            igz(gt)(Crit.has_down(~V, Crit.Fork{ra, pa, ea, za, oa}, rb, pb, eb, zb, ob, lb, rb, False{})(hh)(Crit.all_place_b(~V, Crit.Fork{ra, pa, ea, za, oa}, rb, pb, Cur.bit(Key.at(ra, pb)), False{})(t3)(alla))(hb))
          )(Crit.size_z(V, rb, pb, eb, zb, ob))
        )

# a well formed map whose keys a well formed map holds is no larger
def Crit.size_go(~V: Data, +a: Crit<V>, +b: Crit<V>, +la: Nat, +lb: Nat) -> {Crit.wf(~V, a, la) == True{}: Bool} -> {Crit.wf(~V, b, lb) == True{}: Bool} -> {
  Crit.all(~V, ~Crit<V>, ~(x => k => Crit.has(V, x, k)), a, b) == True{}: Bool
} -> {Nat.is_le(Crit.size(V, a), Crit.size(V, b)) == True{}: Bool}:
  match a b:
    case Crit.Tip{} Crit.Tip{}:
      ha => hb => hh => {==}
    case Crit.Tip{} Crit.Leaf{k2, w2}:
      ha => hb => hh => {==}
    case Crit.Tip{} Crit.Fork{r2, p2, e2, z2, o2}:
      ha => hb => hh => Shared.Nat.le_zero(Crit.size(V, Crit.Fork{r2, p2, e2, z2, o2}))
    case Crit.Leaf{k, v} Crit.Tip{}:
      ha => hb => hh => Empty.absurd({Nat.is_le(1n, 0n) == True{}: Bool}, Shared.Bool.false_ne_true(hh))
    case Crit.Leaf{k, v} Crit.Leaf{k2, w}:
      ha => hb => hh => {==}
    case Crit.Leaf{+k, v} Crit.Fork{+rb, +pb, +eb, +zb, +ob}:
      ha => hb => hh => Crit.size_some(V, Crit.Fork{rb, pb, eb, zb, ob}, k)(Crit.has_some(~V, Crit.Fork{rb, pb, eb, zb, ob}, lb, k)(hb)(hh))
    case Crit.Fork{+ra, +pa, +ea, +za, +oa} Crit.Tip{}:
      ha => hb => hh => Empty.absurd({Nat.is_le(Crit.size(V, Crit.Fork{ra, pa, ea, za, oa}), 0n) == True{}: Bool}, Shared.Bool.false_ne_true(Crit.rep_pass(~V, ~Crit<V>, ~(x => k => Crit.has(V, x, k)), Crit.Fork{ra, pa, ea, za, oa}, la, Crit.Tip{}, [])(ha)(hh)({==})))
    case Crit.Fork{+ra, +pa, +ea, +za, +oa} Crit.Leaf{+k2, +w}:
      +ha => hb => +hh => Empty.absurd(
        {Nat.is_le(Crit.size(V, Crit.Fork{ra, pa, ea, za, oa}), 1n) == True{}: Bool},
        Crit.two(~V, ra, pa, ea, za, oa, la, Empty)(ha)(
          +q1 => +q2 => s1 => s2 => ne => Crit.same_contra(q1, q2, pa)(
            Equal.cong(
              List<&2, U32>,
              Maybe<&2, Bool>,
              t => Key.side(t, pa),
              q1,
              q2,
              Equal.trans(
                List<&2, U32>,
                q1,
                k2,
                q2,
                Key.is_eq_sound(q1, k2)(Equal.trans(Bool, Key.is_eq(q1, k2), Maybe.is_some(&2, V, Shared.Maybe.when(V, Key.is_eq(k2, q1), u => Some{w})), True{}, Equal.sym(Bool, Maybe.is_some(&2, V, Shared.Maybe.when(V, Key.is_eq(k2, q1), u => Some{w})), Key.is_eq(q1, k2), Crit.is_some_when(V, k2, q1, w)), Crit.in_pass(~V, ~Crit<V>, ~(x => k => Crit.has(V, x, k)), Crit.Fork{ra, pa, ea, za, oa}, Crit.Leaf{k2, w}, q1)(hh)(s1))),
                Equal.sym(List<&2, U32>, q2, k2, Key.is_eq_sound(q2, k2)(Equal.trans(Bool, Key.is_eq(q2, k2), Maybe.is_some(&2, V, Shared.Maybe.when(V, Key.is_eq(k2, q2), u => Some{w})), True{}, Equal.sym(Bool, Maybe.is_some(&2, V, Shared.Maybe.when(V, Key.is_eq(k2, q2), u => Some{w})), Key.is_eq(q2, k2), Crit.is_some_when(V, k2, q2, w)), Crit.in_pass(~V, ~Crit<V>, ~(x => k => Crit.has(V, x, k)), Crit.Fork{ra, pa, ea, za, oa}, Crit.Leaf{k2, w}, q2)(hh)(s2))))
              )
            )
          )(ne)
        )
      )
    case Crit.Fork{+ra, +pa, +ea, +za, +oa} Crit.Fork{+rb, +pb, +eb, +zb, +ob}:
      +ha => +hb => +hh => Crit.size_cmp(~V, ra, pa, ea, za, oa, rb, pb, eb, zb, ob, la, lb, Nat.cmp(pa, pb))({==})(ha)(hb)(hh)(
        eqp => Crit.size_go(~V, za, zb, 1n+pa, 1n+pb)(Crit.wf.wf_z(~V, ra, pa, ea, za, oa, la)(ha))(Crit.wf.wf_z(~V, rb, pb, eb, zb, ob, lb)(hb))(
          Crit.has_down(~V, za, rb, pb, eb, zb, ob, lb, ra, False{})(Crit.all.z(~V, ~Crit<V>, ~(x => k => Crit.has(V, x, k)), ra, pa, ea, za, oa, Crit.Fork{rb, pb, eb, zb, ob})(hh))(
            Crit.all_pos(~V, za, ra, pa, pb, False{})(eqp)(Crit.wf.all_z(~V, ra, pa, ea, za, oa, la)(ha))
          )(hb)
        )
      )(
        eqp => Crit.size_go(~V, oa, ob, 1n+pa, 1n+pb)(Crit.wf.wf_o(~V, ra, pa, ea, za, oa, la)(ha))(Crit.wf.wf_o(~V, rb, pb, eb, zb, ob, lb)(hb))(
          Crit.has_down(~V, oa, rb, pb, eb, zb, ob, lb, ra, True{})(Crit.all.o(~V, ~Crit<V>, ~(x => k => Crit.has(V, x, k)), ra, pa, ea, za, oa, Crit.Fork{rb, pb, eb, zb, ob})(hh))(
            Crit.all_pos(~V, oa, ra, pa, pb, True{})(eqp)(Crit.wf.all_o(~V, ra, pa, ea, za, oa, la)(ha))
          )(hb)
        )
      )(gt => hz => Crit.size_go(~V, a, zb, la, 1n+pb)(ha)(Crit.wf.wf_z(~V, rb, pb, eb, zb, ob, lb)(hb))(hz))(gt => ho => Crit.size_go(~V, a, ob, la, 1n+pb)(ha)(Crit.wf.wf_o(~V, rb, pb, eb, zb, ob, lb)(hb))(ho))

# Crit.size_le, with a and b used more than once
def Crit.size_le.go(~V: Data, +a: Crit<V>, +b: Crit<V>) -> {Crit.wf(~V, a, 0n) == True{}: Bool} -> {Crit.wf(~V, b, 0n) == True{}: Bool} -> {
  Crit.within(V, a, b) == True{}: Bool
} -> {Nat.is_le(Crit.size(V, a), Crit.size(V, b)) == True{}: Bool}:
  ha => hb => hw => Crit.size_go(~V, a, b, 0n, 0n)(ha)(hb)(Crit.within_all(~V, a, [], b)(hw))

# a map holds as many entries as it holds keys: a map that holds each key of
# another is no smaller
law Crit.size_le:
  for ~V: Data
  for a: Crit<V>
  for b: Crit<V>
  {Crit.wf(~V, a, 0n) == True{}: Bool} -> {Crit.wf(~V, b, 0n) == True{}: Bool} -> {
    Crit.within(V, a, b) == True{}: Bool
  } -> {
    Nat.is_le(Crit.size(V, a), Crit.size(V, b)) == True{}: Bool
  }

def Crit.size_le(ty, a, b):
  Crit.size_le.go(~ty, a, b)

# a number plus one is one more
def Crit.add_one(+a: Nat) -> {Nat.add(a, 1n) == 1n+a: Nat}:
  Equal.trans(Nat, Nat.add(a, 1n), 1n+Nat.add(a, 0n), 1n+a, Shared.Nat.add_succ(a, 0n), Equal.cong(Nat, Nat, t => 1n+t, Nat.add(a, 0n), a, Shared.Nat.add_zero(a)))

# a fork of an entry that ends at its bit and a map holds one more entry
def Crit.join_end_size(-V: Data, +k: List<&2, U32>, +v: V, +y: Crit<V>, +d: Nat, b: Bool) -> {
  Crit.size(V, Crit.join.end(V, Crit.Leaf{k, v}, y, d, b)) == 1n+Crit.size(V, y): Nat
}:
  match b:
    case True{}:
      {==}
    case False{}:
      Equal.cong(Nat, Nat, t => 1n+t, Nat.add(Crit.size(V, y), 0n), Crit.size(V, y), Shared.Nat.add_zero(Crit.size(V, y)))

# a fork of a map y, whose first key ends at its bit, and an entry holds one
# more entry
def Crit.join_end_size2(-V: Data, y: Crit<V>, +k: List<&2, U32>, +v: V, +d: Nat, b: Bool) -> {
  Crit.size(V, Crit.join.end(V, y, Crit.Leaf{k, v}, d, b)) == 1n+Crit.size(V, y): Nat
}:
  match y b:
    case Crit.Leaf{k2, w} True{}:
      {==}
    case Crit.Leaf{k2, w} False{}:
      {==}
    case Crit.Tip{} b1:
      {==}
    case Crit.Fork{+r, +p, +e, +z, +o} b1:
      Crit.add_one(Crit.size(V, Crit.Fork{r, p, e, z, o}))

# a fork of an entry and a map holds one more entry than the map
def Crit.join_size(-V: Data, +k: List<&2, U32>, +v: V, +y: Crit<V>, +d: Nat) -> {Crit.size(V, Crit.join(V, Crit.Leaf{k, v}, y, d)) == 1n+Crit.size(V, y): Nat}:
  +ky = Crit.rep(V, y, [])
  Shared.Bool.when_cases(
    Crit<V>,
    t => {Crit.size(V, t) == 1n+Crit.size(V, y): Nat},
    Cur.done(Key.at(k, d)),
    u => Crit.join.end(V, Crit.Leaf{k, v}, y, d, Cur.bit(Key.at(ky, d))),
    u => Shared.Bool.when(
      Crit<V>,
      Cur.done(Key.at(ky, d)),
      w => Crit.join.end(V, y, Crit.Leaf{k, v}, d, Cur.bit(Key.at(k, d))),
      w => Shared.Bool.when(Crit<V>, Cur.bit(Key.at(k, d)), w2 => Crit.Fork{ky, d, None{}, y, Crit.Leaf{k, v}}, w2 => Crit.Fork{k, d, None{}, Crit.Leaf{k, v}, y})
    ),
    t1 => Crit.join_end_size(V, k, v, y, d, Cur.bit(Key.at(ky, d))),
    t1 => Shared.Bool.when_cases(
      Crit<V>,
      t => {Crit.size(V, t) == 1n+Crit.size(V, y): Nat},
      Cur.done(Key.at(ky, d)),
      w => Crit.join.end(V, y, Crit.Leaf{k, v}, d, Cur.bit(Key.at(k, d))),
      w => Shared.Bool.when(Crit<V>, Cur.bit(Key.at(k, d)), w2 => Crit.Fork{ky, d, None{}, y, Crit.Leaf{k, v}}, w2 => Crit.Fork{k, d, None{}, Crit.Leaf{k, v}, y}),
      t2 => Crit.join_end_size2(V, y, k, v, d, Cur.bit(Key.at(k, d))),
      t2 => Shared.Bool.when_cases(
        Crit<V>,
        t => {Crit.size(V, t) == 1n+Crit.size(V, y): Nat},
        Cur.bit(Key.at(k, d)),
        w2 => Crit.Fork{ky, d, None{}, y, Crit.Leaf{k, v}},
        w2 => Crit.Fork{k, d, None{}, Crit.Leaf{k, v}, y},
        t3 => Crit.add_one(Crit.size(V, y)),
        t3 => {==}
      )
    )
  )

# one more, when a key is new, after a key was added that was not new
def Crit.add_if_end(-V: Data, e: Maybe<&2, V>, +x: Nat) -> {
  Shared.Nat.add_if(Maybe.is_none(&2, V, e), Shared.Nat.add_if(Maybe.is_some(&2, V, e), x)) == 1n+x: Nat
}:
  match e:
    case None{}:
      {==}
    case Some{v}:
      {==}

# one more on the right of a sum is one more of the sum
def Crit.add_if_right(+a: Nat, c: Bool, +x: Nat) -> {Nat.add(a, Shared.Nat.add_if(c, x)) == Shared.Nat.add_if(c, Nat.add(a, x)): Nat}:
  match c:
    case True{}:
      Shared.Nat.add_succ(a, x)
    case False{}:
      {==}

# one more on the left of a sum is one more of the sum
def Crit.add_if_left(c: Bool, +a: Nat, +x: Nat) -> {Nat.add(Shared.Nat.add_if(c, a), x) == Shared.Nat.add_if(c, Nat.add(a, x)): Nat}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

# two conditional additions of one are the same either way round
def Crit.add_if_swap(s: Bool, c: Bool, +x: Nat) -> {
  Shared.Nat.add_if(s, Shared.Nat.add_if(c, x)) == Shared.Nat.add_if(c, Shared.Nat.add_if(s, x)): Nat
}:
  match s c:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# a fork in its one shape holds as many entries as its parts
def Crit.mk_size(-V: Data, +r: List<&2, U32>, +pos: Nat, e: Maybe<&2, V>, z: Crit<V>, o: Crit<V>) -> {
  Crit.size(V, Crit.mk(V, r, pos, e, z, o)) == Shared.Nat.add_if(Maybe.is_some(&2, V, e), Nat.add(Crit.size(V, z), Crit.size(V, o))): Nat
}:
  match e z o:
    case None{} Crit.Tip{} Crit.Tip{}:
      {==}
    case None{} Crit.Tip{} Crit.Leaf{+kl2, +vl2}:
      {==}
    case None{} Crit.Tip{} Crit.Fork{+fr2, +fp2, +fe2, +fz2, +fo2}:
      {==}
    case None{} Crit.Leaf{+kl, +vl} Crit.Tip{}:
      Equal.sym(Nat, Nat.add(Crit.size(V, Crit.Leaf{kl, vl}), 0n), Crit.size(V, Crit.Leaf{kl, vl}), Shared.Nat.add_zero(Crit.size(V, Crit.Leaf{kl, vl})))
    case None{} Crit.Leaf{+kl, +vl} Crit.Leaf{+kl2, +vl2}:
      {==}
    case None{} Crit.Leaf{+kl, +vl} Crit.Fork{+fr2, +fp2, +fe2, +fz2, +fo2}:
      {==}
    case None{} Crit.Fork{+fr, +fp, +fe, +fz, +fo} Crit.Tip{}:
      Equal.sym(Nat, Nat.add(Crit.size(V, Crit.Fork{fr, fp, fe, fz, fo}), 0n), Crit.size(V, Crit.Fork{fr, fp, fe, fz, fo}), Shared.Nat.add_zero(Crit.size(V, Crit.Fork{fr, fp, fe, fz, fo})))
    case None{} Crit.Fork{+fr, +fp, +fe, +fz, +fo} Crit.Leaf{+kl2, +vl2}:
      {==}
    case None{} Crit.Fork{+fr, +fp, +fe, +fz, +fo} Crit.Fork{+fr2, +fp2, +fe2, +fz2, +fo2}:
      {==}
    case Some{+v} Crit.Tip{} Crit.Tip{}:
      {==}
    case Some{+v} Crit.Tip{} Crit.Leaf{+kl2, +vl2}:
      {==}
    case Some{+v} Crit.Tip{} Crit.Fork{+fr2, +fp2, +fe2, +fz2, +fo2}:
      {==}
    case Some{+v} Crit.Leaf{+kl, +vl} Crit.Tip{}:
      {==}
    case Some{+v} Crit.Leaf{+kl, +vl} Crit.Leaf{+kl2, +vl2}:
      {==}
    case Some{+v} Crit.Leaf{+kl, +vl} Crit.Fork{+fr2, +fp2, +fe2, +fz2, +fo2}:
      {==}
    case Some{+v} Crit.Fork{+fr, +fp, +fe, +fz, +fo} Crit.Tip{}:
      {==}
    case Some{+v} Crit.Fork{+fr, +fp, +fe, +fz, +fo} Crit.Leaf{+kl2, +vl2}:
      {==}
    case Some{+v} Crit.Fork{+fr, +fp, +fe, +fz, +fo} Crit.Fork{+fr2, +fp2, +fe2, +fz2, +fo2}:
      {==}

# Crit.put_size at a fork that holds k's place, from the cursor c2 at its
# bit: pz and po are the writes of its sides
def Crit.put_size.fork(
  ~V: Data,
  ~f: V -> V -> V,
  +k: List<&2, U32>,
  +v: V,
  +rep: List<&2, U32>,
  +pos: Nat,
  +e: Maybe<&2, V>,
  +z: Crit<V>,
  +o: Crit<V>,
  +c2: Cur,
  +pz: Crit<V>,
  +po: Crit<V>
) -> ({Cur.done(c2) == True{}: Bool} -> {Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k) == e: Maybe<&2, V>}) -> (
  {Cur.done(c2) == False{}: Bool} -> {Cur.bit(c2) == False{}: Bool} -> {Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k) == Crit.lookup(V, z, k): Maybe<&2, V>}
) -> ({Cur.done(c2) == False{}: Bool} -> {Cur.bit(c2) == True{}: Bool} -> {Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k) == Crit.lookup(V, o, k): Maybe<&2, V>}) -> (
  {Cur.done(c2) == False{}: Bool} -> {Cur.bit(c2) == False{}: Bool} -> {
    Crit.size(V, pz) == Shared.Nat.add_if(Maybe.is_none(&2, V, Crit.lookup(V, z, k)), Crit.size(V, z)): Nat
  }
) -> (
  {Cur.done(c2) == False{}: Bool} -> {Cur.bit(c2) == True{}: Bool} -> {
    Crit.size(V, po) == Shared.Nat.add_if(Maybe.is_none(&2, V, Crit.lookup(V, o, k)), Crit.size(V, o)): Nat
  }
) -> {
  Crit.size(
    V,
    Shared.Bool.when(
      Crit<V>,
      Cur.done(c2),
      u => Crit.mk(V, k, pos, Some{Crit.merge(~V, ~f, e, v)}, z, o),
      u => Shared.Bool.when(Crit<V>, Cur.bit(c2), w => Crit.mk(V, rep, pos, e, z, po), w => Crit.mk(V, rep, pos, e, pz, o))
    )
  )
    == Shared.Nat.add_if(Maybe.is_none(&2, V, Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k)), Shared.Nat.add_if(Maybe.is_some(&2, V, e), Nat.add(Crit.size(V, z), Crit.size(V, o)))): Nat
}:
  hE => hZ => hO => iz => io => Shared.Bool.when_cases(
    Crit<V>,
    t => {Crit.size(V, t) == Shared.Nat.add_if(Maybe.is_none(&2, V, Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k)), Shared.Nat.add_if(Maybe.is_some(&2, V, e), Nat.add(Crit.size(V, z), Crit.size(V, o)))): Nat},
    Cur.done(c2),
    u => Crit.mk(V, k, pos, Some{Crit.merge(~V, ~f, e, v)}, z, o),
    u => Shared.Bool.when(Crit<V>, Cur.bit(c2), w => Crit.mk(V, rep, pos, e, z, po), w => Crit.mk(V, rep, pos, e, pz, o)),
    t1 => Equal.trans(
      Nat,
      Crit.size(V, Crit.mk(V, k, pos, Some{Crit.merge(~V, ~f, e, v)}, z, o)),
      1n+Nat.add(Crit.size(V, z), Crit.size(V, o)),
      Shared.Nat.add_if(Maybe.is_none(&2, V, Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k)), Shared.Nat.add_if(Maybe.is_some(&2, V, e), Nat.add(Crit.size(V, z), Crit.size(V, o)))),
      Crit.mk_size(V, k, pos, Some{Crit.merge(~V, ~f, e, v)}, z, o),
      (
        %Equal.sym(Maybe<&2, V>, Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k), e, hE(t1)): {
          1n+Nat.add(Crit.size(V, z), Crit.size(V, o)) == Shared.Nat.add_if(Maybe.is_none(&2, V, _), Shared.Nat.add_if(Maybe.is_some(&2, V, e), Nat.add(Crit.size(V, z), Crit.size(V, o)))): Nat
        }
        Equal.sym(Nat, Shared.Nat.add_if(Maybe.is_none(&2, V, e), Shared.Nat.add_if(Maybe.is_some(&2, V, e), Nat.add(Crit.size(V, z), Crit.size(V, o)))), 1n+Nat.add(Crit.size(V, z), Crit.size(V, o)), Crit.add_if_end(V, e, Nat.add(Crit.size(V, z), Crit.size(V, o))))
      )
    ),
    +t1 => Shared.Bool.when_cases(
      Crit<V>,
      t => {Crit.size(V, t) == Shared.Nat.add_if(Maybe.is_none(&2, V, Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k)), Shared.Nat.add_if(Maybe.is_some(&2, V, e), Nat.add(Crit.size(V, z), Crit.size(V, o)))): Nat},
      Cur.bit(c2),
      w => Crit.mk(V, rep, pos, e, z, po),
      w => Crit.mk(V, rep, pos, e, pz, o),
      +t2 => Equal.trans(Nat, Crit.size(V, Crit.mk(V, rep, pos, e, z, po)), Shared.Nat.add_if(Maybe.is_some(&2, V, e), Nat.add(Crit.size(V, z), Crit.size(V, po))), Shared.Nat.add_if(Maybe.is_none(&2, V, Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k)), Shared.Nat.add_if(Maybe.is_some(&2, V, e), Nat.add(Crit.size(V, z), Crit.size(V, o)))), Crit.mk_size(V, rep, pos, e, z, po), Equal.trans(Nat, Shared.Nat.add_if(Maybe.is_some(&2, V, e), Nat.add(Crit.size(V, z), Crit.size(V, po))), Shared.Nat.add_if(Maybe.is_some(&2, V, e), Nat.add(Crit.size(V, z), Shared.Nat.add_if(Maybe.is_none(&2, V, Crit.lookup(V, o, k)), Crit.size(V, o)))), Shared.Nat.add_if(Maybe.is_none(&2, V, Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k)), Shared.Nat.add_if(Maybe.is_some(&2, V, e), Nat.add(Crit.size(V, z), Crit.size(V, o)))), Equal.cong(Nat, Nat, t => Shared.Nat.add_if(Maybe.is_some(&2, V, e), Nat.add(Crit.size(V, z), t)), Crit.size(V, po), Shared.Nat.add_if(Maybe.is_none(&2, V, Crit.lookup(V, o, k)), Crit.size(V, o)), io(t1)(t2)), Equal.trans(Nat, Shared.Nat.add_if(Maybe.is_some(&2, V, e), Nat.add(Crit.size(V, z), Shared.Nat.add_if(Maybe.is_none(&2, V, Crit.lookup(V, o, k)), Crit.size(V, o)))), Shared.Nat.add_if(Maybe.is_some(&2, V, e), Shared.Nat.add_if(Maybe.is_none(&2, V, Crit.lookup(V, o, k)), Nat.add(Crit.size(V, z), Crit.size(V, o)))), Shared.Nat.add_if(Maybe.is_none(&2, V, Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k)), Shared.Nat.add_if(Maybe.is_some(&2, V, e), Nat.add(Crit.size(V, z), Crit.size(V, o)))), Equal.cong(Nat, Nat, t => Shared.Nat.add_if(Maybe.is_some(&2, V, e), t), Nat.add(Crit.size(V, z), Shared.Nat.add_if(Maybe.is_none(&2, V, Crit.lookup(V, o, k)), Crit.size(V, o))), Shared.Nat.add_if(Maybe.is_none(&2, V, Crit.lookup(V, o, k)), Nat.add(Crit.size(V, z), Crit.size(V, o))), Crit.add_if_right(Crit.size(V, z), Maybe.is_none(&2, V, Crit.lookup(V, o, k)), Crit.size(V, o))), Equal.trans(Nat, Shared.Nat.add_if(Maybe.is_some(&2, V, e), Shared.Nat.add_if(Maybe.is_none(&2, V, Crit.lookup(V, o, k)), Nat.add(Crit.size(V, z), Crit.size(V, o)))), Shared.Nat.add_if(Maybe.is_none(&2, V, Crit.lookup(V, o, k)), Shared.Nat.add_if(Maybe.is_some(&2, V, e), Nat.add(Crit.size(V, z), Crit.size(V, o)))), Shared.Nat.add_if(Maybe.is_none(&2, V, Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k)), Shared.Nat.add_if(Maybe.is_some(&2, V, e), Nat.add(Crit.size(V, z), Crit.size(V, o)))), Crit.add_if_swap(Maybe.is_some(&2, V, e), Maybe.is_none(&2, V, Crit.lookup(V, o, k)), Nat.add(Crit.size(V, z), Crit.size(V, o))), Equal.cong(Maybe<&2, V>, Nat, t => Shared.Nat.add_if(Maybe.is_none(&2, V, t), Shared.Nat.add_if(Maybe.is_some(&2, V, e), Nat.add(Crit.size(V, z), Crit.size(V, o)))), Crit.lookup(V, o, k), Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k), Equal.sym(Maybe<&2, V>, Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k), Crit.lookup(V, o, k), hO(t1)(t2))))))),
      +t2 => Equal.trans(Nat, Crit.size(V, Crit.mk(V, rep, pos, e, pz, o)), Shared.Nat.add_if(Maybe.is_some(&2, V, e), Nat.add(Crit.size(V, pz), Crit.size(V, o))), Shared.Nat.add_if(Maybe.is_none(&2, V, Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k)), Shared.Nat.add_if(Maybe.is_some(&2, V, e), Nat.add(Crit.size(V, z), Crit.size(V, o)))), Crit.mk_size(V, rep, pos, e, pz, o), Equal.trans(Nat, Shared.Nat.add_if(Maybe.is_some(&2, V, e), Nat.add(Crit.size(V, pz), Crit.size(V, o))), Shared.Nat.add_if(Maybe.is_some(&2, V, e), Nat.add(Shared.Nat.add_if(Maybe.is_none(&2, V, Crit.lookup(V, z, k)), Crit.size(V, z)), Crit.size(V, o))), Shared.Nat.add_if(Maybe.is_none(&2, V, Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k)), Shared.Nat.add_if(Maybe.is_some(&2, V, e), Nat.add(Crit.size(V, z), Crit.size(V, o)))), Equal.cong(Nat, Nat, t => Shared.Nat.add_if(Maybe.is_some(&2, V, e), Nat.add(t, Crit.size(V, o))), Crit.size(V, pz), Shared.Nat.add_if(Maybe.is_none(&2, V, Crit.lookup(V, z, k)), Crit.size(V, z)), iz(t1)(t2)), Equal.trans(Nat, Shared.Nat.add_if(Maybe.is_some(&2, V, e), Nat.add(Shared.Nat.add_if(Maybe.is_none(&2, V, Crit.lookup(V, z, k)), Crit.size(V, z)), Crit.size(V, o))), Shared.Nat.add_if(Maybe.is_some(&2, V, e), Shared.Nat.add_if(Maybe.is_none(&2, V, Crit.lookup(V, z, k)), Nat.add(Crit.size(V, z), Crit.size(V, o)))), Shared.Nat.add_if(Maybe.is_none(&2, V, Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k)), Shared.Nat.add_if(Maybe.is_some(&2, V, e), Nat.add(Crit.size(V, z), Crit.size(V, o)))), Equal.cong(Nat, Nat, t => Shared.Nat.add_if(Maybe.is_some(&2, V, e), t), Nat.add(Shared.Nat.add_if(Maybe.is_none(&2, V, Crit.lookup(V, z, k)), Crit.size(V, z)), Crit.size(V, o)), Shared.Nat.add_if(Maybe.is_none(&2, V, Crit.lookup(V, z, k)), Nat.add(Crit.size(V, z), Crit.size(V, o))), Crit.add_if_left(Maybe.is_none(&2, V, Crit.lookup(V, z, k)), Crit.size(V, z), Crit.size(V, o))), Equal.trans(Nat, Shared.Nat.add_if(Maybe.is_some(&2, V, e), Shared.Nat.add_if(Maybe.is_none(&2, V, Crit.lookup(V, z, k)), Nat.add(Crit.size(V, z), Crit.size(V, o)))), Shared.Nat.add_if(Maybe.is_none(&2, V, Crit.lookup(V, z, k)), Shared.Nat.add_if(Maybe.is_some(&2, V, e), Nat.add(Crit.size(V, z), Crit.size(V, o)))), Shared.Nat.add_if(Maybe.is_none(&2, V, Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k)), Shared.Nat.add_if(Maybe.is_some(&2, V, e), Nat.add(Crit.size(V, z), Crit.size(V, o)))), Crit.add_if_swap(Maybe.is_some(&2, V, e), Maybe.is_none(&2, V, Crit.lookup(V, z, k)), Nat.add(Crit.size(V, z), Crit.size(V, o))), Equal.cong(Maybe<&2, V>, Nat, t => Shared.Nat.add_if(Maybe.is_none(&2, V, t), Shared.Nat.add_if(Maybe.is_some(&2, V, e), Nat.add(Crit.size(V, z), Crit.size(V, o)))), Crit.lookup(V, z, k), Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k), Equal.sym(Maybe<&2, V>, Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k), Crit.lookup(V, z, k), hZ(t1)(t2)))))))
    )
  )

# a write of k into a well formed map, read from k's cursor, adds one entry
# when the map lacks k, else none; n is the key that the read reaches (r when
# m is empty), and d where k differs from it
def Crit.put_size(
  ~V: Data,
  ~f: V -> V -> V,
  m: Crit<V>,
  +lo: Nat,
  +at: Nat,
  +c: Cur,
  +k: List<&2, U32>,
  +v: V,
  +d: Maybe<&2, Nat>,
  +r: Maybe<&2, List<&2, U32>>,
  +n: List<&2, U32>
) -> {Crit.wf(~V, m, lo) == True{}: Bool} -> {Nat.is_le(at, lo) == True{}: Bool} -> {
  Cur.bits(c) == List.drop(&2, Bool, Key.bits(k), at): List<&2, Bool>
} -> {Maybe.or(&2, List<&2, U32>, Crit.near(V, m, at, c), r) == Some{n}: Maybe<&2, List<&2, U32>>} -> {d == Key.diff(k, n): Maybe<&2, Nat>} -> {
  Crit.size(V, Crit.put(~V, ~f, m, at, c, k, v, d)) == Shared.Nat.add_if(Maybe.is_none(&2, V, Crit.lookup(V, m, k)), Crit.size(V, m)): Nat
}:
  match m:
    case Crit.Tip{}:
      h => l => hc => hn => hd => {==}
    case Crit.Leaf{+k2, +w}:
      h => l => hc => +hn => +hd => Shared.Bool.when_cases(
        Crit<V>,
        t => {Crit.size(V, t) == Shared.Nat.add_if(Maybe.is_none(&2, V, Crit.lookup(V, Crit.Leaf{k2, w}, k)), 1n): Nat},
        Maybe.is_none(&2, Nat, d),
        u => Crit.Leaf{k2, f(w, v)},
        u => Crit.join(V, Crit.Leaf{k, v}, Crit.Leaf{k2, w}, Maybe.default(&2, Nat, d, 0n)),
        t1 =>
          %Equal.sym(Bool, Key.is_eq(k2, k), True{}, Crit.leaf_eq(k, n, k2, d)(hn)(hd)(t1)): {
            1n == Shared.Nat.add_if(Maybe.is_none(&2, V, Shared.Maybe.when(V, _, u => Some{w})), 1n): Nat
          }
          {==},
        t1 => Equal.trans(
          Nat,
          Crit.size(V, Crit.join(V, Crit.Leaf{k, v}, Crit.Leaf{k2, w}, Maybe.default(&2, Nat, d, 0n))),
          2n,
          Shared.Nat.add_if(Maybe.is_none(&2, V, Crit.lookup(V, Crit.Leaf{k2, w}, k)), 1n),
          Crit.join_size(V, k, v, Crit.Leaf{k2, w}, Maybe.default(&2, Nat, d, 0n)),
          (
            %Equal.sym(Maybe<&2, V>, Crit.lookup(V, Crit.Leaf{k2, w}, k), None{}, Crit.when_false(V, Key.is_eq(k2, k), u => Some{w})(Crit.leaf_ne2(k, n, k2, d)(hn)(hd)(t1))): {
              2n == Shared.Nat.add_if(Maybe.is_none(&2, V, _), 1n): Nat
            }
            {==}
          )
        )
      )
    case Crit.Fork{+rep, +pos, +e, +z, +o}:
      +h => +l => +hc => +hn => +hd =>
        +h2 = Crit.skip_at(k, at, pos, c)(Shared.Nat.le_trans(at, lo, pos)(l)(Crit.wf.le(~V, rep, pos, e, z, o, lo)(h)))(hc)
        Shared.Bool.when_cases(
          Crit<V>,
          t => {Crit.size(V, t) == Shared.Nat.add_if(Maybe.is_none(&2, V, Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k)), Crit.size(V, Crit.Fork{rep, pos, e, z, o})): Nat},
          Crit.above(d, pos),
          u => Crit.join(V, Crit.Leaf{k, v}, Crit.Fork{rep, pos, e, z, o}, Maybe.default(&2, Nat, d, 0n)),
          u => Crit.put.fork(
            ~V,
            ~f,
            k,
            v,
            rep,
            pos,
            e,
            z,
            o,
            Cur.skip(Nat.sub(pos, at), c),
            z2 => Crit.put(~V, ~f, z, 1n+pos, z2, k, v, d),
            o2 => Crit.put(~V, ~f, o, 1n+pos, o2, k, v, d)
          ),
          +ta => Equal.trans(
            Nat,
            Crit.size(V, Crit.join(V, Crit.Leaf{k, v}, Crit.Fork{rep, pos, e, z, o}, Maybe.default(&2, Nat, d, 0n))),
            1n+Crit.size(V, Crit.Fork{rep, pos, e, z, o}),
            Shared.Nat.add_if(Maybe.is_none(&2, V, Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k)), Crit.size(V, Crit.Fork{rep, pos, e, z, o})),
            Crit.join_size(V, k, v, Crit.Fork{rep, pos, e, z, o}, Maybe.default(&2, Nat, d, 0n)),
            (
              %Equal.sym(
                Maybe<&2, V>,
                Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k),
                None{},
                Crit.not_in_fork(~V, rep, pos, e, z, o, lo, k)(h)(Crit.above_out(~V, rep, pos, e, z, o, lo, at, c, k, d, r, n)(h)(hn)(hd)(ta))
              ): {1n+Crit.size(V, Crit.Fork{rep, pos, e, z, o}) == Shared.Nat.add_if(Maybe.is_none(&2, V, _), Crit.size(V, Crit.Fork{rep, pos, e, z, o})): Nat}
              {==}
            )
          ),
          +ta => Crit.put_size.fork(
            ~V,
            ~f,
            k,
            v,
            rep,
            pos,
            e,
            z,
            o,
            Cur.skip(Nat.sub(pos, at), c),
            Crit.put(~V, ~f, z, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), k, v, d),
            Crit.put(~V, ~f, o, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), k, v, d)
          )(
            +t1 =>
              +nil = Crit.nil_of_done(k, pos, Cur.skip(Nat.sub(pos, at), c))(h2)(t1)
              Equal.trans(
                Maybe<&2, V>,
                Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k),
                Crit.ended(V, rep, e, k),
                e,
                Crit.or_first(V, Crit.ended(V, rep, e, k), Crit.lookup(V, z, k), Crit.lookup(V, o, k))(
                  Crit.no_side(~V, rep, pos, z, False{}, k)(Crit.wf.all_z(~V, rep, pos, e, z, o, lo)(h))(nil)
                )(Crit.no_side(~V, rep, pos, o, True{}, k)(Crit.wf.all_o(~V, rep, pos, e, z, o, lo)(h))(nil)),
                Crit.ended_self(V, rep, pos, e, z, k)(Crit.wf.rep_ok(~V, rep, pos, e, z, o, lo)(h))(nil)(
                  Crit.done_above(V, rep, pos, e, z, o, at, c, k, d, r, n)(hn)(hd)(ta)(t1)
                )
              )
          )(
            +t1 => t2 => Crit.or_second(V, Crit.ended(V, rep, e, k), Crit.lookup(V, z, k), Crit.lookup(V, o, k))(Crit.ended_long(V, rep, pos, e, z, k, List.drop(&2, Bool, Key.bits(k), pos))(Crit.wf.rep_ok(~V, rep, pos, e, z, o, lo)(h))({==})(Equal.trans(Bool, List.is_empty(&2, Bool, List.drop(&2, Bool, Key.bits(k), pos)), Cur.done(Cur.skip(Nat.sub(pos, at), c)), False{}, Equal.sym(Bool, Cur.done(Cur.skip(Nat.sub(pos, at), c)), List.is_empty(&2, Bool, List.drop(&2, Bool, Key.bits(k), pos)), Crit.done_of(Cur.skip(Nat.sub(pos, at), c), List.drop(&2, Bool, Key.bits(k), pos))(h2)), t1)))(
              Crit.off_side(~V, rep, pos, o, True{}, k, Cur.skip(Nat.sub(pos, at), c))(Crit.wf.all_o(~V, rep, pos, e, z, o, lo)(h))(h2)(t1)((
                %Equal.sym(Bool, Cur.bit(Cur.skip(Nat.sub(pos, at), c)), False{}, t2): {Shared.Bool.is_eq(_, True{}) == False{}: Bool}
                {==}
              ))
            )
          )(
            +t1 => t2 => Crit.or_third(V, Crit.ended(V, rep, e, k), Crit.lookup(V, z, k), Crit.lookup(V, o, k))(Crit.ended_long(V, rep, pos, e, z, k, List.drop(&2, Bool, Key.bits(k), pos))(Crit.wf.rep_ok(~V, rep, pos, e, z, o, lo)(h))({==})(Equal.trans(Bool, List.is_empty(&2, Bool, List.drop(&2, Bool, Key.bits(k), pos)), Cur.done(Cur.skip(Nat.sub(pos, at), c)), False{}, Equal.sym(Bool, Cur.done(Cur.skip(Nat.sub(pos, at), c)), List.is_empty(&2, Bool, List.drop(&2, Bool, Key.bits(k), pos)), Crit.done_of(Cur.skip(Nat.sub(pos, at), c), List.drop(&2, Bool, Key.bits(k), pos))(h2)), t1)))(
              Crit.off_side(~V, rep, pos, z, False{}, k, Cur.skip(Nat.sub(pos, at), c))(Crit.wf.all_z(~V, rep, pos, e, z, o, lo)(h))(h2)(t1)((
                %Equal.sym(Bool, Cur.bit(Cur.skip(Nat.sub(pos, at), c)), True{}, t2): {Shared.Bool.is_eq(_, False{}) == False{}: Bool}
                {==}
              ))
            )
          )(
            +t1 => +t2 => Crit.put_size(~V, ~f, z, 1n+pos, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), k, v, d, Some{rep}, n)(Crit.wf.wf_z(~V, rep, pos, e, z, o, lo)(h))(Shared.Nat.le_refl(1n+pos))(
              Crit.next_at(k, pos, Cur.skip(Nat.sub(pos, at), c))(h2)
            )(Crit.near_child(V, rep, pos, e, z, o, at, c, False{}, r, n)(hn)(t1)(t2))(hd)
          )(
            +t1 => +t2 => Crit.put_size(~V, ~f, o, 1n+pos, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), k, v, d, Some{rep}, n)(Crit.wf.wf_o(~V, rep, pos, e, z, o, lo)(h))(Shared.Nat.le_refl(1n+pos))(
              Crit.next_at(k, pos, Cur.skip(Nat.sub(pos, at), c))(h2)
            )(Crit.near_child(V, rep, pos, e, z, o, at, c, True{}, r, n)(hn)(t1)(t2))(hd)
          )
        )

# Crit.size_upsert, once the key that a read of k reaches is known (nm)
def Crit.size_upsert.at(~V: Data, ~f: V -> V -> V, +m: Crit<V>, +k: List<&2, U32>, +v: V, nm: Maybe<&2, List<&2, U32>>) -> {
  Crit.wf(~V, m, 0n) == True{}: Bool
} -> {Crit.near(V, m, 0n, Cur.of(k)) == nm: Maybe<&2, List<&2, U32>>} -> {Crit.size(V, Crit.put(~V, ~f, m, 0n, Cur.of(k), k, v, Crit.diff(k, nm))) == Shared.Nat.add_if(Maybe.is_none(&2, V, Crit.lookup(V, m, k)), Crit.size(V, m)): Nat}:
  match nm:
    case None{}:
      h => hm => Crit.put_size(~V, ~f, m, 0n, 0n, Cur.of(k), k, v, None{}, Some{k}, k)(h)({==})(Equal.sym(List<&2, Bool>, List.drop(&2, Bool, Key.bits(k), 0n), Key.bits(k), Shared.List.drop_zero(&2, Bool, Key.bits(k))))(
        %Equal.sym(Maybe<&2, List<&2, U32>>, Crit.near(V, m, 0n, Cur.of(k)), None{}, hm): {
          Maybe.or(&2, List<&2, U32>, _, Some{k}) == Some{k}: Maybe<&2, List<&2, U32>>
        }
        {==}
      )(Equal.sym(Maybe<&2, Nat>, Key.diff(k, k), None{}, Key.diff_self(k)))
    case Some{+x}:
      h => hm => Crit.put_size(~V, ~f, m, 0n, 0n, Cur.of(k), k, v, Key.diff(k, x), None{}, x)(h)({==})(Equal.sym(List<&2, Bool>, List.drop(&2, Bool, Key.bits(k), 0n), Key.bits(k), Shared.List.drop_zero(&2, Bool, Key.bits(k))))(
        Equal.trans(
          Maybe<&2, List<&2, U32>>,
          Maybe.or(&2, List<&2, U32>, Crit.near(V, m, 0n, Cur.of(k)), None{}),
          Crit.near(V, m, 0n, Cur.of(k)),
          Some{x},
          Shared.Maybe.or_none(List<&2, U32>, Crit.near(V, m, 0n, Cur.of(k))),
          hm
        )
      )({==})

# Crit.size_upsert, with m and k used more than once
def Crit.size_upsert.go(~V: Data, ~f: V -> V -> V, +m: Crit<V>, +k: List<&2, U32>, +v: V) -> {Crit.wf(~V, m, 0n) == True{}: Bool} -> {
  Crit.size(V, Crit.upsert(~V, ~f, m, k, v)) == Shared.Nat.add_if(Maybe.is_none(&2, V, Crit.lookup(V, m, k)), Crit.size(V, m)): Nat
}:
  h => Crit.size_upsert.at(~V, ~f, m, k, v, Crit.near(V, m, 0n, Cur.of(k)))(h)({==})

# a write of a key that a map lacks adds one entry; of one it holds, none
law Crit.size_upsert:
  for ~V: Data
  for ~f: V -> V -> V
  for m: Crit<V>
  for k: List<&2, U32>
  for v: V
  {Crit.wf(~V, m, 0n) == True{}: Bool} -> {
    Crit.size(V, Crit.upsert(~V, ~f, m, k, v))
      == Shared.Nat.add_if(Maybe.is_none(&2, V, Crit.lookup(V, m, k)), Crit.size(V, m)): Nat
  }

def Crit.size_upsert(ty, f, m, k, v):
  Crit.size_upsert.go(~ty, ~f, m, k, v)

# Prefixes and order
# ------------------
# A map keeps its entries in the order of the bits of their keys, so the
# keys that start with some words are one part of it, and its last entry is
# its greatest key. A key whose words hold numbers with their bits reversed
# (Key.ord) is then in the order of the numbers.

# the key k starts with the words p
def Key.starts(p: List<&2, U32>, k: List<&2, U32>) -> Bool:
  match p k:
    case Nil{} y:
      True{}
    case Con{x, rp} Nil{}:
      False{}
    case Con{+x, rp} Con{+y, rk}:
      Bool.and(U32.is_eq(x, y), Key.starts(rp, rk))

# the bits a come before the bits b: they differ first where a has a zero,
# or a ends before b does
def Bits.lt(a: List<&2, Bool>, b: List<&2, Bool>) -> Bool:
  match a b:
    case x Nil{}:
      False{}
    case Nil{} Con{y, rb}:
      True{}
    case Con{+x, ra} Con{+y, rb}:
      Bool.or(Bool.and(Bool.not(x), y), Bool.and(Shared.Bool.is_eq(x, y), Bits.lt(ra, rb)))

# the entries of m whose keys start with the words p, read from the cursor c
# of p at the bit at. Past the end of p, the keys of a fork share the bits of
# its rep, so they start with p when its rep does
def Crit.under.go(-V: Data, m: Crit<V>, +at: Nat, +c: Cur, +p: List<&2, U32>) -> Crit<V>:
  match m:
    case Crit.Tip{}:
      Crit.Tip{}
    case Crit.Leaf{+k, +v}:
      Shared.Bool.when(Crit<V>, Key.starts(p, k), u => Crit.Leaf{k, v}, u => Crit.Tip{})
    case Crit.Fork{+rep, +pos, +e, +z, +o}:
      +c2 = Cur.skip(Nat.sub(pos, at), c)
      Shared.Bool.when(
        Crit<V>,
        Cur.done(c2),
        u => Shared.Bool.when(Crit<V>, Key.starts(p, rep), w => Crit.Fork{rep, pos, e, z, o}, w => Crit.Tip{}),
        u => Shared.Bool.when(
          Crit<V>,
          Cur.bit(c2),
          w => Crit.under.go(V, o, 1n+pos, Cur.next(c2), p),
          w => Crit.under.go(V, z, 1n+pos, Cur.next(c2), p)
        )
      )

# the entries of m whose keys start with the words p: a part of m, found in
# the bits of p
def Crit.under(-V: Data, m: Crit<V>, +p: List<&2, U32>) -> Crit<V>:
  Crit.under.go(V, m, 0n, Cur.of(p), p)

# the entry m, else the one that go finds
def Crit.last.or(-V: Data, m: Maybe<&2, Bind<V>>, go: Unit -> Maybe<&2, Bind<V>>) -> Maybe<&2, Bind<V>>:
  match m:
    case Some{b}:
      Some{b}
    case None{}:
      go(Unit{})

# the entry of the key that ends at a fork of the rep rep, if any
def Crit.end.bind(-V: Data, rep: List<&2, U32>, e: Maybe<&2, V>) -> Maybe<&2, Bind<V>>:
  match e:
    case None{}:
      None{}
    case Some{v}:
      Some{Bind{rep, v}}

# the last entry of m, in the order of its keys: of a fork, the last of its
# one side, else of its zero side, else the key that ends there
def Crit.last(-V: Data, m: Crit<V>) -> Maybe<&2, Bind<V>>:
  match m:
    case Crit.Tip{}:
      None{}
    case Crit.Leaf{k, v}:
      Some{Bind{k, v}}
    case Crit.Fork{rep, pos, e, z, o}:
      Crit.last.or(V, Crit.last(V, o), u => Crit.last.or(V, Crit.last(V, z), w => Crit.end.bind(V, rep, e)))

# the word of n bits whose bits are bs, the lowest first (a False for each
# bit that bs lacks)
def Word.of(n: Nat, bs: List<&2, Bool>) -> Word(n):
  match n bs:
    case 0n x:
      WNil{}
    case 1n+p Nil{}:
      WCon{False{}, Word.of(p, [])}
    case 1n+p Con{b, r}:
      WCon{b, Word.of(p, r)}

# x with its bits in the other order, so that a map reads its highest first
def U32.rev(x: U32) -> U32:
  match x:
    case U32{w}:
      U32{Word.of(32n, List.reverse(&2, Bool, Word.bits(32n, w)))}

# the words ws, each with its bits in the other order, then r
def Words.rev(ws: List<&2, U32>, r: List<&2, U32>) -> List<&2, U32>:
  match ws:
    case Nil{}:
      r
    case Con{w, rest}:
      U32.rev(w) <> Words.rev(rest, r)

# the key of the number n, then r: its count (Codes.Code.count) with the
# bits of each word in the other order, so that the keys of numbers are in
# the order of the numbers, and none starts another
def Key.ord(n: Nat, r: List<&2, U32>) -> List<&2, U32>:
  Words.rev(Codes.Code.count(n, []), r)

# the number that the read m gives
def Key.ord.of(m: Maybe<&2, Codes.Read<Nat>>) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      None{}
    case Some{Codes.Read{n, r}}:
      Some{n}

# the number at the front of the key ws (Key.ord)
def Key.ord.value(ws: List<&2, U32>) -> Maybe<&2, Nat>:
  Key.ord.of(Codes.Code.count.read(Words.rev(ws, [])))

# the bits of a list of words, then more, are its bits, then theirs
def Key.bits_append(+p: List<&2, U32>, +a: List<&2, U32>) -> {Key.bits(List.append(&2, U32, p, a)) == List.append(&2, Bool, Key.bits(p), Key.bits(a)): List<&2, Bool>}:
  match p:
    case Nil{}:
      {==}
    case Con{U32{+w}, +r}:
      %Equal.sym(List<&2, Bool>, Key.bits(List.append(&2, U32, r, a)), List.append(&2, Bool, Key.bits(r), Key.bits(a)), Key.bits_append(r, a)): {
        List.append(&2, Bool, Word.bits(32n, w), _) == List.append(&2, Bool, List.append(&2, Bool, Word.bits(32n, w), Key.bits(r)), Key.bits(a)): List<&2, Bool>
      }
      Equal.sym(
        List<&2, Bool>,
        List.append(&2, Bool, List.append(&2, Bool, Word.bits(32n, w), Key.bits(r)), Key.bits(a)),
        List.append(&2, Bool, Word.bits(32n, w), List.append(&2, Bool, Key.bits(r), Key.bits(a))),
        Shared.List.append_assoc(Bool, Word.bits(32n, w), Key.bits(r), Key.bits(a))
      )

# bits that start alike are in the order of what follows
def Bits.lt_append(ps: List<&2, Bool>, +a: List<&2, Bool>, +b: List<&2, Bool>) -> {Bits.lt(List.append(&2, Bool, ps, a), List.append(&2, Bool, ps, b)) == Bits.lt(a, b): Bool}:
  match ps:
    case Nil{}:
      {==}
    case Con{True{}, r}:
      Bits.lt_append(r, a, b)
    case Con{False{}, r}:
      Bits.lt_append(r, a, b)

# Key.lt_after, with p, a and b used more than once
def Key.lt_after.go(+p: List<&2, U32>, +a: List<&2, U32>, +b: List<&2, U32>) -> {
  Bits.lt(Key.bits(List.append(&2, U32, p, a)), Key.bits(List.append(&2, U32, p, b))) == Bits.lt(Key.bits(a), Key.bits(b)): Bool
}:
  %Equal.sym(List<&2, Bool>, Key.bits(List.append(&2, U32, p, a)), List.append(&2, Bool, Key.bits(p), Key.bits(a)), Key.bits_append(p, a)): {
    Bits.lt(_, Key.bits(List.append(&2, U32, p, b))) == Bits.lt(Key.bits(a), Key.bits(b)): Bool
  }
  %Equal.sym(List<&2, Bool>, Key.bits(List.append(&2, U32, p, b)), List.append(&2, Bool, Key.bits(p), Key.bits(b)), Key.bits_append(p, b)): {
    Bits.lt(List.append(&2, Bool, Key.bits(p), Key.bits(a)), _) == Bits.lt(Key.bits(a), Key.bits(b)): Bool
  }
  Bits.lt_append(Key.bits(p), Key.bits(a), Key.bits(b))

# a choice of the entry m, else go, that is nothing: m is nothing
def Crit.last_or_fst(-V: Data, m: Maybe<&2, Bind<V>>, -go: Unit -> Maybe<&2, Bind<V>>) -> {Crit.last.or(V, m, go) == None{}: Maybe<&2, Bind<V>>} -> {m == None{}: Maybe<&2, Bind<V>>}:
  match m:
    case None{}:
      h => {==}
    case Some{b}:
      h => Empty.absurd({Some{b} == None{}: Maybe<&2, Bind<V>>}, Crit.some_ne_none(Bind<V>, b, h))

# a choice of the entry m, else go, that is nothing: go is nothing
def Crit.last_or_snd(-V: Data, m: Maybe<&2, Bind<V>>, -go: Unit -> Maybe<&2, Bind<V>>) -> {Crit.last.or(V, m, go) == None{}: Maybe<&2, Bind<V>>} -> {go(Unit{}) == None{}: Maybe<&2, Bind<V>>}:
  match m:
    case None{}:
      h => h
    case Some{b}:
      h => Empty.absurd({go(Unit{}) == None{}: Maybe<&2, Bind<V>>}, Crit.some_ne_none(Bind<V>, b, h))

# a fork with no entry at its end reads nothing there
def Crit.ended_bind_none(-V: Data, +r: List<&2, U32>, e: Maybe<&2, V>, +q: List<&2, U32>) -> {Crit.end.bind(V, r, e) == None{}: Maybe<&2, Bind<V>>} -> {Crit.ended(V, r, e, q) == None{}: Maybe<&2, V>}:
  match e:
    case None{}:
      h => {==}
    case Some{w}:
      h => Empty.absurd({Shared.Maybe.when(V, Key.is_eq(r, q), u => Some{w}) == None{}: Maybe<&2, V>}, Crit.some_ne_none(Bind<V>, Bind{r, w}, h))

# a map with no last entry reads nothing
def Crit.last_none.go(-V: Data, m: Crit<V>, +q: List<&2, U32>) -> {Crit.last(V, m) == None{}: Maybe<&2, Bind<V>>} -> {Crit.lookup(V, m, q) == None{}: Maybe<&2, V>}:
  match m:
    case Crit.Tip{}:
      h => {==}
    case Crit.Leaf{k, v}:
      h => Empty.absurd({Crit.lookup(V, Crit.Leaf{k, v}, q) == None{}: Maybe<&2, V>}, Crit.some_ne_none(Bind<V>, Bind{k, v}, h))
    case Crit.Fork{+r, p, +e, +z, +o}:
      +h =>
        +hz = Crit.last_or_snd(V, Crit.last(V, o), u => Crit.last.or(V, Crit.last(V, z), w => Crit.end.bind(V, r, e)))(h)
        Crit.or3_none(V, Crit.ended(V, r, e, q), Crit.lookup(V, z, q), Crit.lookup(V, o, q))(
          Crit.ended_bind_none(V, r, e, q)(Crit.last_or_snd(V, Crit.last(V, z), w => Crit.end.bind(V, r, e))(hz))
        )(Crit.last_none.go(V, z, q)(Crit.last_or_fst(V, Crit.last(V, z), w => Crit.end.bind(V, r, e))(hz)))(
          Crit.last_none.go(V, o, q)(Crit.last_or_fst(V, Crit.last(V, o), u => Crit.last.or(V, Crit.last(V, z), w => Crit.end.bind(V, r, e)))(h))
        )

# no bits come before themselves
def Bits.lt_self(bs: List<&2, Bool>) -> {Bits.lt(bs, bs) == False{}: Bool}:
  match bs:
    case Nil{}:
      {==}
    case Con{True{}, r}:
      Bits.lt_self(r)
    case Con{False{}, r}:
      Bits.lt_self(r)

# no bits come before no bits
def Bits.lt_nil(a: List<&2, Bool>) -> {Bits.lt(a, []) == False{}: Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{x, r}:
      {==}

# bits a that agree with bits b before n, where b ends, do not come before b
def Bits.lt_end(n: Nat, a: List<&2, Bool>, b: List<&2, Bool>) -> {Bits.agree_n(n, a, b) == True{}: Bool} -> {Bits.at(b, n) == None{}: Maybe<&2, Bool>} -> {Bits.lt(a, b) == False{}: Bool}:
  match n a b:
    case 0n x Nil{}:
      h => hb => Bits.lt_nil(x)
    case 0n x Con{y, rb}:
      h => hb => Empty.absurd({Bits.lt(x, y <> rb) == False{}: Bool}, Crit.some_ne_none(Bool, y, hb))
    case 1n+q Nil{} Nil{}:
      h => hb => {==}
    case 1n+q Con{True{}, ra} Con{True{}, rb}:
      h => hb => Bits.lt_end(q, ra, rb)(h)(hb)
    case 1n+q Con{False{}, ra} Con{False{}, rb}:
      h => hb => Bits.lt_end(q, ra, rb)(h)(hb)
    case 1n+q Con{True{}, ra} Con{False{}, rb}:
      h => hb => Empty.absurd({Bits.lt(True{} <> ra, False{} <> rb) == False{}: Bool}, Shared.Bool.false_ne_true(h))
    case 1n+q Con{False{}, ra} Con{True{}, rb}:
      h => hb => Empty.absurd({Bits.lt(False{} <> ra, True{} <> rb) == False{}: Bool}, Shared.Bool.false_ne_true(h))
    case 1n+q Nil{} Con{y, rb}:
      h => hb => Empty.absurd({Bits.lt([], y <> rb) == False{}: Bool}, Shared.Bool.false_ne_true(h))
    case 1n+q Con{x, ra} Nil{}:
      h => hb => {==}

# bits a with a one at n, where bits b that agree with them before n have a
# zero, do not come before b
def Bits.lt_one(n: Nat, a: List<&2, Bool>, b: List<&2, Bool>) -> {Bits.agree_n(n, a, b) == True{}: Bool} -> {Bits.at(a, n) == Some{True{}}: Maybe<&2, Bool>} -> {
  Bits.at(b, n) == Some{False{}}: Maybe<&2, Bool>
} -> {Bits.lt(a, b) == False{}: Bool}:
  match n a b:
    case 0n Con{x, ra} Con{y, rb}:
      h => ha => hb =>
        %Equal.sym(Bool, x, True{}, Shared.Maybe.some_inj(Bool, x, True{}, ha)): {Bits.lt(_ <> ra, y <> rb) == False{}: Bool}
        %Equal.sym(Bool, y, False{}, Shared.Maybe.some_inj(Bool, y, False{}, hb)): {Bits.lt(True{} <> ra, _ <> rb) == False{}: Bool}
        {==}
    case 0n Nil{} y:
      h => ha => hb => Empty.absurd({Bits.lt([], y) == False{}: Bool}, Shared.Maybe.none_ne_some(Bool, True{}, ha))
    case 0n Con{x, ra} Nil{}:
      h => ha => hb => {==}
    case 1n+q Nil{} y:
      h => ha => hb => Empty.absurd({Bits.lt([], y) == False{}: Bool}, Shared.Maybe.none_ne_some(Bool, True{}, ha))
    case 1n+q Con{x, ra} Nil{}:
      h => ha => hb => {==}
    case 1n+q Con{True{}, ra} Con{True{}, rb}:
      h => ha => hb => Bits.lt_one(q, ra, rb)(h)(ha)(hb)
    case 1n+q Con{False{}, ra} Con{False{}, rb}:
      h => ha => hb => Bits.lt_one(q, ra, rb)(h)(ha)(hb)
    case 1n+q Con{True{}, ra} Con{False{}, rb}:
      h => ha => hb => Empty.absurd({Bits.lt(True{} <> ra, False{} <> rb) == False{}: Bool}, Shared.Bool.false_ne_true(h))
    case 1n+q Con{False{}, ra} Con{True{}, rb}:
      h => ha => hb => Empty.absurd({Bits.lt(False{} <> ra, True{} <> rb) == False{}: Bool}, Shared.Bool.false_ne_true(h))

# the key of an entry
def Crit.bind_key(-V: Data, b: Bind<V>) -> List<&2, U32>:
  match b:
    case Bind{k, v}:
      k

# the value of an entry
def Crit.bind_val(-V: Data, b: Bind<V>) -> V:
  match b:
    case Bind{k, v}:
      v

# entries that are the same have the same key and value
def Crit.bind_inj_k(-V: Data, -k2: List<&2, U32>, -w: V, -k: List<&2, U32>, -v: V) -> {Some{Bind{k2, w}} == Some{Bind{k, v}}: Maybe<&2, Bind<V>>} -> {k2 == k: List<&2, U32>}:
  h => Equal.cong(Bind<V>, List<&2, U32>, b => Crit.bind_key(V, b), Bind{k2, w}, Bind{k, v}, Shared.Maybe.some_inj(Bind<V>, Bind{k2, w}, Bind{k, v}, h))

def Crit.bind_inj_v(-V: Data, -k2: List<&2, U32>, -w: V, -k: List<&2, U32>, -v: V) -> {Some{Bind{k2, w}} == Some{Bind{k, v}}: Maybe<&2, Bind<V>>} -> {w == v: V}:
  h => Equal.cong(Bind<V>, V, b => Crit.bind_val(V, b), Bind{k2, w}, Bind{k, v}, Shared.Maybe.some_inj(Bind<V>, Bind{k2, w}, Bind{k, v}, h))

# the bits of two keys agree before the bit of a fork that holds both
def Crit.agree_in(~V: Data, +r: List<&2, U32>, +p: Nat, +e: Maybe<&2, V>, +z: Crit<V>, +o: Crit<V>, +lo: Nat, +k: List<&2, U32>, +q: List<&2, U32>) -> {Crit.wf(~V, Crit.Fork{r, p, e, z, o}, lo) == True{}: Bool} -> {
  Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{r, p, e, z, o}, k)) == True{}: Bool
} -> {Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{r, p, e, z, o}, q)) == True{}: Bool} -> {Bits.agree_n(p, Key.bits(k), Key.bits(q)) == True{}: Bool}:
  +h => sk => sq => Equal.trans(
    Bool,
    Bits.agree_n(p, Key.bits(k), Key.bits(q)),
    Key.agree(k, q, p),
    True{},
    Equal.sym(Bool, Key.agree(k, q, p), Bits.agree_n(p, Key.bits(k), Key.bits(q)), Key.agree_bits(k, q, p)),
    Key.agree_join(k, q, r, p)(Crit.in_fork_agree(~V, r, p, e, z, o, lo, k)(h)(sk))(Crit.in_fork_agree(~V, r, p, e, z, o, lo, q)(h)(sq))
  )

# the bit of a key at pos, from its side
def Crit.at_of_side(+k: List<&2, U32>, +p: Nat, +s: Maybe<&2, Bool>) -> {Key.side(k, p) == s: Maybe<&2, Bool>} -> {Bits.at(Key.bits(k), p) == s: Maybe<&2, Bool>}:
  h => Equal.trans(Maybe<&2, Bool>, Bits.at(Key.bits(k), p), Key.side(k, p), s, Equal.sym(Maybe<&2, Bool>, Key.side(k, p), Bits.at(Key.bits(k), p), Key.side_bits(k, p)), h)

# Crit.last_max at an entry k of the side o of a well formed fork (lk: its
# side's claim)
def Crit.last_max.one(~V: Data, +r: List<&2, U32>, +p: Nat, +e: Maybe<&2, V>, +z: Crit<V>, +o: Crit<V>, +lo: Nat, +k: List<&2, U32>, -v: V, c: Sigma<&1, &1, {Crit.lookup(V, o, k) == Some{v}: Maybe<&2, V>}, _ => (@q: List<&2, U32> -> {Maybe.is_some(&2, V, Crit.lookup(V, o, q)) == True{}: Bool} -> {Bits.lt(Key.bits(k), Key.bits(q)) == False{}: Bool})>) -> {Crit.wf(~V, Crit.Fork{r, p, e, z, o}, lo) == True{}: Bool} -> Sigma<&1, &1, {Crit.lookup(V, Crit.Fork{r, p, e, z, o}, k) == Some{v}: Maybe<&2, V>}, _ => (@q: List<&2, U32> -> {Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{r, p, e, z, o}, q)) == True{}: Bool} -> {Bits.lt(Key.bits(k), Key.bits(q)) == False{}: Bool})>:
  (+c1, c2) = c
  +h =>
    +sk = Place.has_side(r, p, True{}, k)(Crit.in_place(~V, o, Place{r, p, True{}}, k)(Crit.wf.all_o(~V, r, p, e, z, o, lo)(h))(Equal.cong(Maybe<&2, V>, Bool, x => Maybe.is_some(&2, V, x), Crit.lookup(V, o, k), Some{v}, c1)))
    +inf = Equal.trans(Bool, Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{r, p, e, z, o}, k)), Maybe.is_some(&2, V, Crit.lookup(V, o, k)), True{}, Equal.cong(Maybe<&2, V>, Bool, x => Maybe.is_some(&2, V, x), Crit.lookup(V, Crit.Fork{r, p, e, z, o}, k), Crit.lookup(V, o, k), Crit.route_side(~V, r, p, e, z, o, lo, k, True{})(h)(sk)), Equal.cong(Maybe<&2, V>, Bool, x => Maybe.is_some(&2, V, x), Crit.lookup(V, o, k), Some{v}, c1))
    (
      Equal.trans(Maybe<&2, V>, Crit.lookup(V, Crit.Fork{r, p, e, z, o}, k), Crit.lookup(V, o, k), Some{v}, Crit.route_side(~V, r, p, e, z, o, lo, k, True{})(h)(sk), c1),
      +q => +sq => Crit.side_split({Bits.lt(Key.bits(k), Key.bits(q)) == False{}: Bool}, q, p)(
        hs => c2(q)(Equal.trans(Bool, Maybe.is_some(&2, V, Crit.lookup(V, o, q)), Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{r, p, e, z, o}, q)), True{}, Equal.cong(Maybe<&2, V>, Bool, x => Maybe.is_some(&2, V, x), Crit.lookup(V, o, q), Crit.lookup(V, Crit.Fork{r, p, e, z, o}, q), Equal.sym(Maybe<&2, V>, Crit.lookup(V, Crit.Fork{r, p, e, z, o}, q), Crit.lookup(V, o, q), Crit.route_side(~V, r, p, e, z, o, lo, q, True{})(h)(hs))), sq))
      )(
        hs => Bits.lt_one(p, Key.bits(k), Key.bits(q))(Crit.agree_in(~V, r, p, e, z, o, lo, k, q)(h)(inf)(sq))(Crit.at_of_side(k, p, Some{True{}})(sk))(Crit.at_of_side(q, p, Some{False{}})(hs))
      )(
        hs => Bits.lt_end(p, Key.bits(k), Key.bits(q))(Crit.agree_in(~V, r, p, e, z, o, lo, k, q)(h)(inf)(sq))(Crit.at_of_side(q, p, None{})(hs))
      )
    )

# Crit.last_max at an entry k of the side z of a well formed fork whose side o
# is empty
def Crit.last_max.zero(~V: Data, +r: List<&2, U32>, +p: Nat, +e: Maybe<&2, V>, +z: Crit<V>, +o: Crit<V>, +lo: Nat, +k: List<&2, U32>, -v: V, c: Sigma<&1, &1, {Crit.lookup(V, z, k) == Some{v}: Maybe<&2, V>}, _ => (@q: List<&2, U32> -> {Maybe.is_some(&2, V, Crit.lookup(V, z, q)) == True{}: Bool} -> {Bits.lt(Key.bits(k), Key.bits(q)) == False{}: Bool})>) -> {Crit.wf(~V, Crit.Fork{r, p, e, z, o}, lo) == True{}: Bool} -> {
  Crit.last(V, o) == None{}: Maybe<&2, Bind<V>>
} -> Sigma<&1, &1, {Crit.lookup(V, Crit.Fork{r, p, e, z, o}, k) == Some{v}: Maybe<&2, V>}, _ => (@q: List<&2, U32> -> {Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{r, p, e, z, o}, q)) == True{}: Bool} -> {Bits.lt(Key.bits(k), Key.bits(q)) == False{}: Bool})>:
  (+c1, c2) = c
  +h => +ln =>
    +sk = Place.has_side(r, p, False{}, k)(Crit.in_place(~V, z, Place{r, p, False{}}, k)(Crit.wf.all_z(~V, r, p, e, z, o, lo)(h))(Equal.cong(Maybe<&2, V>, Bool, x => Maybe.is_some(&2, V, x), Crit.lookup(V, z, k), Some{v}, c1)))
    +inf = Equal.trans(Bool, Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{r, p, e, z, o}, k)), Maybe.is_some(&2, V, Crit.lookup(V, z, k)), True{}, Equal.cong(Maybe<&2, V>, Bool, x => Maybe.is_some(&2, V, x), Crit.lookup(V, Crit.Fork{r, p, e, z, o}, k), Crit.lookup(V, z, k), Crit.route_side(~V, r, p, e, z, o, lo, k, False{})(h)(sk)), Equal.cong(Maybe<&2, V>, Bool, x => Maybe.is_some(&2, V, x), Crit.lookup(V, z, k), Some{v}, c1))
    (
      Equal.trans(Maybe<&2, V>, Crit.lookup(V, Crit.Fork{r, p, e, z, o}, k), Crit.lookup(V, z, k), Some{v}, Crit.route_side(~V, r, p, e, z, o, lo, k, False{})(h)(sk), c1),
      +q => +sq => Crit.side_split({Bits.lt(Key.bits(k), Key.bits(q)) == False{}: Bool}, q, p)(
        hs => Empty.absurd(
          {Bits.lt(Key.bits(k), Key.bits(q)) == False{}: Bool},
          Shared.Bool.false_ne_true(
            Equal.trans(
              Bool,
              False{},
              Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{r, p, e, z, o}, q)),
              True{},
              Equal.trans(
                Bool,
                False{},
                Maybe.is_some(&2, V, Crit.lookup(V, o, q)),
                Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{r, p, e, z, o}, q)),
                Equal.cong(Maybe<&2, V>, Bool, x => Maybe.is_some(&2, V, x), None{}, Crit.lookup(V, o, q), Equal.sym(Maybe<&2, V>, Crit.lookup(V, o, q), None{}, Crit.last_none.go(V, o, q)(ln))),
                Equal.cong(Maybe<&2, V>, Bool, x => Maybe.is_some(&2, V, x), Crit.lookup(V, o, q), Crit.lookup(V, Crit.Fork{r, p, e, z, o}, q), Equal.sym(Maybe<&2, V>, Crit.lookup(V, Crit.Fork{r, p, e, z, o}, q), Crit.lookup(V, o, q), Crit.route_side(~V, r, p, e, z, o, lo, q, True{})(h)(hs)))
              ),
              sq
            )
          )
        )
      )(
        hs => c2(q)(Equal.trans(Bool, Maybe.is_some(&2, V, Crit.lookup(V, z, q)), Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{r, p, e, z, o}, q)), True{}, Equal.cong(Maybe<&2, V>, Bool, x => Maybe.is_some(&2, V, x), Crit.lookup(V, z, q), Crit.lookup(V, Crit.Fork{r, p, e, z, o}, q), Equal.sym(Maybe<&2, V>, Crit.lookup(V, Crit.Fork{r, p, e, z, o}, q), Crit.lookup(V, z, q), Crit.route_side(~V, r, p, e, z, o, lo, q, False{})(h)(hs))), sq))
      )(
        hs => Bits.lt_end(p, Key.bits(k), Key.bits(q))(Crit.agree_in(~V, r, p, e, z, o, lo, k, q)(h)(inf)(sq))(Crit.at_of_side(q, p, None{})(hs))
      )
    )

# Crit.last_max at the end of a fork whose sides are empty
def Crit.last_max.end(-V: Data, +r: List<&2, U32>, +p: Nat, e: Maybe<&2, V>, +z: Crit<V>, +o: Crit<V>, +k: List<&2, U32>, +v: V) -> {Crit.last(V, z) == None{}: Maybe<&2, Bind<V>>} -> {
  Crit.last(V, o) == None{}: Maybe<&2, Bind<V>>
} -> {Crit.end.bind(V, r, e) == Some{Bind{k, v}}: Maybe<&2, Bind<V>>} -> Sigma<&1, &1, {Crit.lookup(V, Crit.Fork{r, p, e, z, o}, k) == Some{v}: Maybe<&2, V>}, _ => (@q: List<&2, U32> -> {Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{r, p, e, z, o}, q)) == True{}: Bool} -> {Bits.lt(Key.bits(k), Key.bits(q)) == False{}: Bool})>:
  match e:
    case None{}:
      lz => lo2 => h => Empty.absurd(Sigma<&1, &1, {Crit.lookup(V, Crit.Fork{r, p, None{}, z, o}, k) == Some{v}: Maybe<&2, V>}, _ => (@q: List<&2, U32> -> {Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{r, p, None{}, z, o}, q)) == True{}: Bool} -> {Bits.lt(Key.bits(k), Key.bits(q)) == False{}: Bool})>, Shared.Maybe.none_ne_some(Bind<V>, Bind{k, v}, h))
    case Some{+w}:
      +lz => +lo2 => +h =>
        +ek = Crit.bind_inj_k(V, r, w, k, v)(h)
        %Equal.sym(List<&2, U32>, r, k, ek): Sigma<&1, &1, {Crit.lookup(V, Crit.Fork{_, p, Some{w}, z, o}, k) == Some{v}: Maybe<&2, V>}, _ => (@q: List<&2, U32> -> {Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{_, p, Some{w}, z, o}, q)) == True{}: Bool} -> {Bits.lt(Key.bits(k), Key.bits(q)) == False{}: Bool})>
        %Equal.sym(V, w, v, Crit.bind_inj_v(V, r, w, k, v)(h)): Sigma<&1, &1, {Crit.lookup(V, Crit.Fork{k, p, Some{_}, z, o}, k) == Some{v}: Maybe<&2, V>}, _ => (@q: List<&2, U32> -> {Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{k, p, Some{_}, z, o}, q)) == True{}: Bool} -> {Bits.lt(Key.bits(k), Key.bits(q)) == False{}: Bool})>
        (
          (
            %Equal.sym(Bool, Key.is_eq(k, k), True{}, Key.is_eq_refl(k)): {
              Maybe.or(&2, V, Shared.Maybe.when(V, _, u => Some{v}), Maybe.or(&2, V, Crit.lookup(V, z, k), Crit.lookup(V, o, k))) == Some{v}: Maybe<&2, V>
            }
            {==}
          ),
          +q => sq =>
            +eq = Key.is_eq_sound(k, q)(
              Crit.true_of(Key.is_eq(k, q))(
                t => Shared.Bool.false_ne_true(
                  Equal.trans(
                    Bool,
                    False{},
                    Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{k, p, Some{v}, z, o}, q)),
                    True{},
                    Equal.cong(
                      Maybe<&2, V>,
                      Bool,
                      x => Maybe.is_some(&2, V, x),
                      None{},
                      Crit.lookup(V, Crit.Fork{k, p, Some{v}, z, o}, q),
                      Equal.sym(
                        Maybe<&2, V>,
                        Crit.lookup(V, Crit.Fork{k, p, Some{v}, z, o}, q),
                        None{},
                        Crit.or3_none(V, Crit.ended(V, k, Some{v}, q), Crit.lookup(V, z, q), Crit.lookup(V, o, q))(Crit.when_false(V, Key.is_eq(k, q), u => Some{v})(t))(
                          Crit.last_none.go(V, z, q)(lz)
                        )(Crit.last_none.go(V, o, q)(lo2))
                      )
                    ),
                    sq
                  )
                )
              )
            )
            %eq: {Bits.lt(Key.bits(k), Key.bits(_)) == False{}: Bool}
            Bits.lt_self(Key.bits(k))
        )

# Crit.last_max at a fork, once its side o's last entry is known (lo2)
def Crit.last_max.fork(~V: Data, +r: List<&2, U32>, +p: Nat, +e: Maybe<&2, V>, +z: Crit<V>, +o: Crit<V>, +lo: Nat, +k: List<&2, U32>, +v: V, lo2: Maybe<&2, Bind<V>>, lz: Maybe<&2, Bind<V>>) -> {Crit.last(V, o) == lo2: Maybe<&2, Bind<V>>} -> {
  Crit.last(V, z) == lz: Maybe<&2, Bind<V>>
} -> ({lo2 == Some{Bind{k, v}}: Maybe<&2, Bind<V>>} -> Sigma<&1, &1, {Crit.lookup(V, o, k) == Some{v}: Maybe<&2, V>}, _ => (@q: List<&2, U32> -> {Maybe.is_some(&2, V, Crit.lookup(V, o, q)) == True{}: Bool} -> {Bits.lt(Key.bits(k), Key.bits(q)) == False{}: Bool})>) -> ({lz == Some{Bind{k, v}}: Maybe<&2, Bind<V>>} -> Sigma<&1, &1, {Crit.lookup(V, z, k) == Some{v}: Maybe<&2, V>}, _ => (@q: List<&2, U32> -> {Maybe.is_some(&2, V, Crit.lookup(V, z, q)) == True{}: Bool} -> {Bits.lt(Key.bits(k), Key.bits(q)) == False{}: Bool})>) -> {Crit.wf(~V, Crit.Fork{r, p, e, z, o}, lo) == True{}: Bool} -> {
  Crit.last.or(V, lo2, u => Crit.last.or(V, lz, w => Crit.end.bind(V, r, e))) == Some{Bind{k, v}}: Maybe<&2, Bind<V>>
} -> Sigma<&1, &1, {Crit.lookup(V, Crit.Fork{r, p, e, z, o}, k) == Some{v}: Maybe<&2, V>}, _ => (@q: List<&2, U32> -> {Maybe.is_some(&2, V, Crit.lookup(V, Crit.Fork{r, p, e, z, o}, q)) == True{}: Bool} -> {Bits.lt(Key.bits(k), Key.bits(q)) == False{}: Bool})>:
  match lo2:
    case Some{b}:
      eo => ez => io => iz => h => hl => Crit.last_max.one(~V, r, p, e, z, o, lo, k, v, io(hl))(h)
    case None{}:
      match lz:
        case Some{b}:
          +eo => ez => io => iz => h => hl => Crit.last_max.zero(~V, r, p, e, z, o, lo, k, v, iz(hl))(h)(eo)
        case None{}:
          eo => ez => io => iz => h => hl => Crit.last_max.end(V, r, p, e, z, o, k, v)(ez)(eo)(hl)

# the last entry of a well formed map is an entry of it, and no key of it
# comes after it
def Crit.last_max.go(~V: Data, m: Crit<V>, +lo: Nat, +k: List<&2, U32>, +v: V) -> {Crit.wf(~V, m, lo) == True{}: Bool} -> {Crit.last(V, m) == Some{Bind{k, v}}: Maybe<&2, Bind<V>>} -> Sigma<&1, &1, {Crit.lookup(V, m, k) == Some{v}: Maybe<&2, V>}, _ => (@q: List<&2, U32> -> {Maybe.is_some(&2, V, Crit.lookup(V, m, q)) == True{}: Bool} -> {Bits.lt(Key.bits(k), Key.bits(q)) == False{}: Bool})>:
  match m:
    case Crit.Tip{}:
      h => hl => Empty.absurd(Sigma<&1, &1, {Crit.lookup(V, Crit.Tip{}, k) == Some{v}: Maybe<&2, V>}, _ => (@q: List<&2, U32> -> {Maybe.is_some(&2, V, Crit.lookup(V, Crit.Tip{}, q)) == True{}: Bool} -> {Bits.lt(Key.bits(k), Key.bits(q)) == False{}: Bool})>, Shared.Maybe.none_ne_some(Bind<V>, Bind{k, v}, hl))
    case Crit.Leaf{+k2, +w}:
      h => +hl =>
        %Equal.sym(List<&2, U32>, k2, k, Crit.bind_inj_k(V, k2, w, k, v)(hl)): Sigma<&1, &1, {Crit.lookup(V, Crit.Leaf{_, w}, k) == Some{v}: Maybe<&2, V>}, _ => (@q: List<&2, U32> -> {Maybe.is_some(&2, V, Crit.lookup(V, Crit.Leaf{_, w}, q)) == True{}: Bool} -> {Bits.lt(Key.bits(k), Key.bits(q)) == False{}: Bool})>
        %Equal.sym(V, w, v, Crit.bind_inj_v(V, k2, w, k, v)(hl)): Sigma<&1, &1, {Crit.lookup(V, Crit.Leaf{k, _}, k) == Some{v}: Maybe<&2, V>}, _ => (@q: List<&2, U32> -> {Maybe.is_some(&2, V, Crit.lookup(V, Crit.Leaf{k, _}, q)) == True{}: Bool} -> {Bits.lt(Key.bits(k), Key.bits(q)) == False{}: Bool})>
        (
          Crit.leaf_self(V, k, v),
          +q => sq =>
            %Equal.sym(List<&2, U32>, q, k, Key.is_eq_sound(q, k)(Equal.trans(Bool, Key.is_eq(q, k), Maybe.is_some(&2, V, Shared.Maybe.when(V, Key.is_eq(k, q), u => Some{v})), True{}, Equal.sym(Bool, Maybe.is_some(&2, V, Shared.Maybe.when(V, Key.is_eq(k, q), u => Some{v})), Key.is_eq(q, k), Crit.is_some_when(V, k, q, v)), sq))): {
              Bits.lt(Key.bits(k), Key.bits(_)) == False{}: Bool
            }
            Bits.lt_self(Key.bits(k))
        )
    case Crit.Fork{+r, +p, +e, +z, +o}:
      +h => hl => Crit.last_max.fork(~V, r, p, e, z, o, lo, k, v, Crit.last(V, o), Crit.last(V, z))({==})({==})(
        x => Crit.last_max.go(~V, o, 1n+p, k, v)(Crit.wf.wf_o(~V, r, p, e, z, o, lo)(h))(x)
      )(x => Crit.last_max.go(~V, z, 1n+p, k, v)(Crit.wf.wf_z(~V, r, p, e, z, o, lo)(h))(x))(h)(hl)

# the part of a well formed map under a prefix, read from any cursor, is
# well formed
def Crit.under_go_wf(~V: Data, m: Crit<V>, +lo: Nat, +at: Nat, +c: Cur, +p: List<&2, U32>) -> {Crit.wf(~V, m, lo) == True{}: Bool} -> {
  Crit.wf(~V, Crit.under.go(V, m, at, c, p), lo) == True{}: Bool
}:
  match m:
    case Crit.Tip{}:
      h => {==}
    case Crit.Leaf{+k, +v}:
      h => Shared.Bool.when_cases(Crit<V>, t => {Crit.wf(~V, t, lo) == True{}: Bool}, Key.starts(p, k), u => Crit.Leaf{k, v}, u => Crit.Tip{}, t => {==}, t => {==})
    case Crit.Fork{+rep, +pos, +e, +z, +o}:
      +h => Shared.Bool.when_cases(
        Crit<V>,
        t => {Crit.wf(~V, t, lo) == True{}: Bool},
        Cur.done(Cur.skip(Nat.sub(pos, at), c)),
        u => Shared.Bool.when(Crit<V>, Key.starts(p, rep), w => Crit.Fork{rep, pos, e, z, o}, w => Crit.Tip{}),
        u => Shared.Bool.when(Crit<V>, Cur.bit(Cur.skip(Nat.sub(pos, at), c)), w => Crit.under.go(V, o, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), p), w => Crit.under.go(V, z, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), p)),
        t => Shared.Bool.when_cases(Crit<V>, t => {Crit.wf(~V, t, lo) == True{}: Bool}, Key.starts(p, rep), w => Crit.Fork{rep, pos, e, z, o}, w => Crit.Tip{}, t2 => h, t2 => {==}),
        t => Shared.Bool.when_cases(
          Crit<V>,
          t => {Crit.wf(~V, t, lo) == True{}: Bool},
          Cur.bit(Cur.skip(Nat.sub(pos, at), c)),
          w => Crit.under.go(V, o, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), p),
          w => Crit.under.go(V, z, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), p),
          t2 => Crit.wf_mono(~V, Crit.under.go(V, o, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), p), 1n+pos, lo)(Crit.under_go_wf(~V, o, 1n+pos, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), p)(Crit.wf.wf_o(~V, rep, pos, e, z, o, lo)(h)))(Shared.Nat.le_succ(lo, pos)(Crit.wf.le(~V, rep, pos, e, z, o, lo)(h))),
          t2 => Crit.wf_mono(~V, Crit.under.go(V, z, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), p), 1n+pos, lo)(Crit.under_go_wf(~V, z, 1n+pos, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), p)(Crit.wf.wf_z(~V, rep, pos, e, z, o, lo)(h)))(Shared.Nat.le_succ(lo, pos)(Crit.wf.le(~V, rep, pos, e, z, o, lo)(h)))
        )
      )

# Crit.under_wf, with p used more than once
def Crit.under_wf.go(~V: Data, m: Crit<V>, +p: List<&2, U32>) -> {Crit.wf(~V, m, 0n) == True{}: Bool} -> {Crit.wf(~V, Crit.under(V, m, p), 0n) == True{}: Bool}:
  h => Crit.under_go_wf(~V, m, 0n, 0n, Cur.of(p), p)(h)

# the number before n (0 before 0)
def Crit.pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+q:
      q

# no successor is zero
def Crit.zero_ne_succ(-n: Nat, h: {0n == 1n+n: Nat}) -> Empty:
  Shared.Bool.true_ne_false(Equal.cong(Nat, Bool, t => Nat.is_eq(t, 0n), 0n, 1n+n, h))

# the length of two lists one after the other is the sum of their lengths
def Bits.length_append(xs: List<&2, Bool>, +ys: List<&2, Bool>) -> {List.length(&2, Bool, List.append(&2, Bool, xs, ys)) == Nat.add(List.length(&2, Bool, xs), List.length(&2, Bool, ys)): Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, r}:
      Equal.cong(Nat, Nat, t => 1n+t, List.length(&2, Bool, List.append(&2, Bool, r, ys)), Nat.add(List.length(&2, Bool, r), List.length(&2, Bool, ys)), Bits.length_append(r, ys))

# lists of one length, each followed by more, agree as far as both do when
# both parts do
def Bits.agree_append(a: List<&2, Bool>, +a2: List<&2, Bool>, b: List<&2, Bool>, +b2: List<&2, Bool>, +m: Nat) -> {List.length(&2, Bool, a) == List.length(&2, Bool, b): Nat} -> {
  Bits.agree_n(Nat.add(List.length(&2, Bool, a), m), List.append(&2, Bool, a, a2), List.append(&2, Bool, b, b2)) == Bool.and(Bits.agree_n(List.length(&2, Bool, a), a, b), Bits.agree_n(m, a2, b2)): Bool
}:
  match a b:
    case Nil{} Nil{}:
      h => {==}
    case Con{+x, +ra} Con{+y, +rb}:
      h => Equal.trans(
        Bool,
        Bool.and(Shared.Bool.is_eq(x, y), Bits.agree_n(Nat.add(List.length(&2, Bool, ra), m), List.append(&2, Bool, ra, a2), List.append(&2, Bool, rb, b2))),
        Bool.and(Shared.Bool.is_eq(x, y), Bool.and(Bits.agree_n(List.length(&2, Bool, ra), ra, rb), Bits.agree_n(m, a2, b2))),
        Bool.and(Bool.and(Shared.Bool.is_eq(x, y), Bits.agree_n(List.length(&2, Bool, ra), ra, rb)), Bits.agree_n(m, a2, b2)),
        Equal.cong(Bool, Bool, t => Bool.and(Shared.Bool.is_eq(x, y), t), Bits.agree_n(Nat.add(List.length(&2, Bool, ra), m), List.append(&2, Bool, ra, a2), List.append(&2, Bool, rb, b2)), Bool.and(Bits.agree_n(List.length(&2, Bool, ra), ra, rb), Bits.agree_n(m, a2, b2)), Bits.agree_append(ra, a2, rb, b2, m)(Equal.cong(Nat, Nat, t => Crit.pred(t), 1n+List.length(&2, Bool, ra), 1n+List.length(&2, Bool, rb), h))),
        Shared.Bool.and_assoc(Shared.Bool.is_eq(x, y), Bits.agree_n(List.length(&2, Bool, ra), ra, rb), Bits.agree_n(m, a2, b2))
      )
    case Nil{} Con{y, rb}:
      h => Empty.absurd({Bits.agree_n(Nat.add(0n, m), a2, List.append(&2, Bool, y <> rb, b2)) == Bool.and(True{}, Bits.agree_n(m, a2, b2)): Bool}, Crit.zero_ne_succ(List.length(&2, Bool, rb), h))
    case Con{x, ra} Nil{}:
      h => Empty.absurd({Bits.agree_n(Nat.add(1n+List.length(&2, Bool, ra), m), List.append(&2, Bool, x <> ra, a2), b2) == Bool.and(Bits.agree_n(1n+List.length(&2, Bool, ra), x <> ra, []), Bits.agree_n(m, a2, b2)): Bool}, Crit.zero_ne_succ(List.length(&2, Bool, ra), Equal.sym(Nat, 1n+List.length(&2, Bool, ra), 0n, h)))

# Word.cmp.fin is EQ exactly when the first bits are the same and the rest is
def Crit.cmp_fin_eq(t: Cmp, ab: Bool, bb: Bool) -> {Cmp.is_eq(Word.cmp.fin(ab, bb, t)) == Bool.and(Shared.Bool.is_eq(ab, bb), Cmp.is_eq(t)): Bool}:
  match t ab bb:
    case LT{} True{} True{}:
      {==}
    case LT{} True{} False{}:
      {==}
    case LT{} False{} True{}:
      {==}
    case LT{} False{} False{}:
      {==}
    case EQ{} True{} True{}:
      {==}
    case EQ{} True{} False{}:
      {==}
    case EQ{} False{} True{}:
      {==}
    case EQ{} False{} False{}:
      {==}
    case GT{} True{} True{}:
      {==}
    case GT{} True{} False{}:
      {==}
    case GT{} False{} True{}:
      {==}
    case GT{} False{} False{}:
      {==}

# words are equal exactly when their bits agree
def Crit.word_eq_bits(n: Nat, a: Word(n), b: Word(n)) -> {Cmp.is_eq(Word.cmp(n, a, b)) == Bits.agree_n(n, Word.bits(n, a), Word.bits(n, b)): Bool}:
  match n:
    case 0n:
      {==}
    case 1n+(+q):
      match a b:
        case WCon{+ab, +at} WCon{+bb, +bt}:
          Equal.trans(
            Bool,
            Cmp.is_eq(Word.cmp.fin(ab, bb, Word.cmp(q, at, bt))),
            Bool.and(Shared.Bool.is_eq(ab, bb), Cmp.is_eq(Word.cmp(q, at, bt))),
            Bool.and(Shared.Bool.is_eq(ab, bb), Bits.agree_n(q, Word.bits(q, at), Word.bits(q, bt))),
            Crit.cmp_fin_eq(Word.cmp(q, at, bt), ab, bb),
            Equal.cong(Bool, Bool, t => Bool.and(Shared.Bool.is_eq(ab, bb), t), Cmp.is_eq(Word.cmp(q, at, bt)), Bits.agree_n(q, Word.bits(q, at), Word.bits(q, bt)), Crit.word_eq_bits(q, at, bt))
          )

# a key starts with the words p exactly when its bits start with those of p
def Key.starts_bits(+p: List<&2, U32>, +k: List<&2, U32>) -> {Key.starts(p, k) == Bits.agree_n(List.length(&2, Bool, Key.bits(p)), Key.bits(p), Key.bits(k)): Bool}:
  match p k:
    case Nil{} y:
      {==}
    case Con{U32{WCon{b, t}}, rp} Nil{}:
      {==}
    case Con{U32{+w}, +rp} Con{U32{+v}, +rk}:
      %Equal.sym(Nat, List.length(&2, Bool, List.append(&2, Bool, Word.bits(32n, w), Key.bits(rp))), Nat.add(List.length(&2, Bool, Word.bits(32n, w)), List.length(&2, Bool, Key.bits(rp))), Bits.length_append(Word.bits(32n, w), Key.bits(rp))): {
        Bool.and(U32.is_eq(U32{w}, U32{v}), Key.starts(rp, rk)) == Bits.agree_n(_, List.append(&2, Bool, Word.bits(32n, w), Key.bits(rp)), List.append(&2, Bool, Word.bits(32n, v), Key.bits(rk))): Bool
      }
      %Equal.sym(Bool, Bits.agree_n(Nat.add(List.length(&2, Bool, Word.bits(32n, w)), List.length(&2, Bool, Key.bits(rp))), List.append(&2, Bool, Word.bits(32n, w), Key.bits(rp)), List.append(&2, Bool, Word.bits(32n, v), Key.bits(rk))), Bool.and(Bits.agree_n(List.length(&2, Bool, Word.bits(32n, w)), Word.bits(32n, w), Word.bits(32n, v)), Bits.agree_n(List.length(&2, Bool, Key.bits(rp)), Key.bits(rp), Key.bits(rk))), Bits.agree_append(Word.bits(32n, w), Key.bits(rp), Word.bits(32n, v), Key.bits(rk), List.length(&2, Bool, Key.bits(rp)))(
        Equal.trans(Nat, List.length(&2, Bool, Word.bits(32n, w)), 32n, List.length(&2, Bool, Word.bits(32n, v)), Word.bits_length(32n, w), Equal.sym(Nat, List.length(&2, Bool, Word.bits(32n, v)), 32n, Word.bits_length(32n, v)))
      )): {Bool.and(U32.is_eq(U32{w}, U32{v}), Key.starts(rp, rk)) == _: Bool}
      %Equal.sym(Nat, List.length(&2, Bool, Word.bits(32n, w)), 32n, Word.bits_length(32n, w)): {
        Bool.and(U32.is_eq(U32{w}, U32{v}), Key.starts(rp, rk)) == Bool.and(Bits.agree_n(_, Word.bits(32n, w), Word.bits(32n, v)), Bits.agree_n(List.length(&2, Bool, Key.bits(rp)), Key.bits(rp), Key.bits(rk))): Bool
      }
      %Equal.sym(Bool, Cmp.is_eq(Word.cmp(32n, w, v)), Bits.agree_n(32n, Word.bits(32n, w), Word.bits(32n, v)), Crit.word_eq_bits(32n, w, v)): {
        Bool.and(_, Key.starts(rp, rk)) == Bool.and(Bits.agree_n(32n, Word.bits(32n, w), Word.bits(32n, v)), Bits.agree_n(List.length(&2, Bool, Key.bits(rp)), Key.bits(rp), Key.bits(rk))): Bool
      }
      %Equal.sym(Bool, Key.starts(rp, rk), Bits.agree_n(List.length(&2, Bool, Key.bits(rp)), Key.bits(rp), Key.bits(rk)), Key.starts_bits(rp, rk)): {
        Bool.and(Bits.agree_n(32n, Word.bits(32n, w), Word.bits(32n, v)), _) == Bool.and(Bits.agree_n(32n, Word.bits(32n, w), Word.bits(32n, v)), Bits.agree_n(List.length(&2, Bool, Key.bits(rp)), Key.bits(rp), Key.bits(rk))): Bool
      }
      {==}

# tests that each imply the other are equal
def Crit.iff_eq(a: Bool, b: Bool) -> ({a == True{}: Bool} -> {b == True{}: Bool}) -> ({b == True{}: Bool} -> {a == True{}: Bool}) -> {a == b: Bool}:
  match a b:
    case True{} True{}:
      f => g => {==}
    case False{} False{}:
      f => g => {==}
    case True{} False{}:
      f => g => Empty.absurd({True{} == False{}: Bool}, Shared.Bool.false_ne_true(f({==})))
    case False{} True{}:
      f => g => Empty.absurd({False{} == True{}: Bool}, Shared.Bool.false_ne_true(g({==})))

# keys that agree before pos, past the end of p, both start with p or neither
def Key.starts_agree(+p: List<&2, U32>, +k: List<&2, U32>, +r: List<&2, U32>, +pos: Nat) -> {List.drop(&2, Bool, Key.bits(p), pos) == []: List<&2, Bool>} -> {Key.agree(k, r, pos) == True{}: Bool} -> {
  Key.starts(p, k) == Key.starts(p, r): Bool
}:
  hd => ha =>
    +le = Crit.drop_nil_len(Key.bits(p), pos)(hd)
    +kr = Bits.agree_n_le(Key.bits(k), Key.bits(r), List.length(&2, Bool, Key.bits(p)), pos)(le)(Equal.trans(Bool, Bits.agree_n(pos, Key.bits(k), Key.bits(r)), Key.agree(k, r, pos), True{}, Equal.sym(Bool, Key.agree(k, r, pos), Bits.agree_n(pos, Key.bits(k), Key.bits(r)), Key.agree_bits(k, r, pos)), ha))
    %Equal.sym(Bool, Key.starts(p, k), Bits.agree_n(List.length(&2, Bool, Key.bits(p)), Key.bits(p), Key.bits(k)), Key.starts_bits(p, k)): {_ == Key.starts(p, r): Bool}
    %Equal.sym(Bool, Key.starts(p, r), Bits.agree_n(List.length(&2, Bool, Key.bits(p)), Key.bits(p), Key.bits(r)), Key.starts_bits(p, r)): {Bits.agree_n(List.length(&2, Bool, Key.bits(p)), Key.bits(p), Key.bits(k)) == _: Bool}
    Crit.iff_eq(Bits.agree_n(List.length(&2, Bool, Key.bits(p)), Key.bits(p), Key.bits(k)), Bits.agree_n(List.length(&2, Bool, Key.bits(p)), Key.bits(p), Key.bits(r)))(
      t => Bits.agree_n_trans(Key.bits(p), Key.bits(k), Key.bits(r), List.length(&2, Bool, Key.bits(p)))(t)(kr)
    )(t => Bits.agree_n_trans(Key.bits(p), Key.bits(r), Key.bits(k), List.length(&2, Bool, Key.bits(p)))(t)(Equal.trans(Bool, Bits.agree_n(List.length(&2, Bool, Key.bits(p)), Key.bits(r), Key.bits(k)), Bits.agree_n(List.length(&2, Bool, Key.bits(p)), Key.bits(k), Key.bits(r)), True{}, Bits.agree_n_sym(Key.bits(r), Key.bits(k), List.length(&2, Bool, Key.bits(p))), kr)))

# a list with bits from n on is longer than n
def Crit.drop_some_lt(xs: List<&2, Bool>, +n: Nat) -> {List.is_empty(&2, Bool, List.drop(&2, Bool, xs, n)) == False{}: Bool} -> {Nat.is_le(1n+n, List.length(&2, Bool, xs)) == True{}: Bool}:
  match xs n:
    case Nil{} m:
      h => Empty.absurd({Nat.is_le(1n+m, 0n) == True{}: Bool}, Shared.Bool.true_ne_false(h))
    case Con{x, t} 0n:
      h => Shared.Nat.le_zero(List.length(&2, Bool, t))
    case Con{x, t} 1n+q:
      h => Crit.drop_some_lt(t, q)(h)

# a key that starts with p has p's bit at pos, while p goes on past pos
def Key.starts_side(+p: List<&2, U32>, +k: List<&2, U32>, +pos: Nat, +c2: Cur) -> {Cur.bits(c2) == List.drop(&2, Bool, Key.bits(p), pos): List<&2, Bool>} -> {Cur.done(c2) == False{}: Bool} -> {
  Key.starts(p, k) == True{}: Bool
} -> {Key.side(k, pos) == Some{Cur.bit(c2)}: Maybe<&2, Bool>}:
  +h2 => +t1 => st =>
    +lt = Crit.drop_some_lt(Key.bits(p), pos)(
      Equal.trans(Bool, List.is_empty(&2, Bool, List.drop(&2, Bool, Key.bits(p), pos)), Cur.done(c2), False{}, Equal.sym(Bool, Cur.done(c2), List.is_empty(&2, Bool, List.drop(&2, Bool, Key.bits(p), pos)), Crit.done_of(c2, List.drop(&2, Bool, Key.bits(p), pos))(h2)), t1)
    )
    +ag = Bits.agree_n_le(Key.bits(p), Key.bits(k), 1n+pos, List.length(&2, Bool, Key.bits(p)))(lt)(Equal.trans(Bool, Bits.agree_n(List.length(&2, Bool, Key.bits(p)), Key.bits(p), Key.bits(k)), Key.starts(p, k), True{}, Equal.sym(Bool, Key.starts(p, k), Bits.agree_n(List.length(&2, Bool, Key.bits(p)), Key.bits(p), Key.bits(k)), Key.starts_bits(p, k)), st))
    Equal.trans(
      Maybe<&2, Bool>,
      Key.side(k, pos),
      Bits.at(Key.bits(k), pos),
      Some{Cur.bit(c2)},
      Key.side_bits(k, pos),
      Equal.trans(
        Maybe<&2, Bool>,
        Bits.at(Key.bits(k), pos),
        Bits.at(Key.bits(p), pos),
        Some{Cur.bit(c2)},
        Equal.sym(Maybe<&2, Bool>, Bits.at(Key.bits(p), pos), Bits.at(Key.bits(k), pos), Key.at_eq(p, k, pos)(Equal.trans(Bool, Key.agree(p, k, 1n+pos), Bits.agree_n(1n+pos, Key.bits(p), Key.bits(k)), True{}, Key.agree_bits(p, k, 1n+pos), ag))),
        Equal.trans(Maybe<&2, Bool>, Bits.at(Key.bits(p), pos), Key.side(p, pos), Some{Cur.bit(c2)}, Equal.sym(Maybe<&2, Bool>, Key.side(p, pos), Bits.at(Key.bits(p), pos), Key.side_bits(p, pos)), Crit.side_cur(p, pos, c2)(h2)(t1))
      )
    )

# a read that is kept where it is some
def Crit.pick_keep(-V: Data, mv: Maybe<&2, V>, +c: Bool) -> ({Maybe.is_some(&2, V, mv) == True{}: Bool} -> {c == True{}: Bool}) -> {mv == Bool.pick(Maybe<&2, V>, c, mv, None{}): Maybe<&2, V>}:
  match mv:
    case None{}:
      f => Equal.sym(Maybe<&2, V>, Bool.pick(Maybe<&2, V>, c, None{}, None{}), None{}, Crit.pick_none(V, c))
    case Some{u}:
      f =>
        %Equal.sym(Bool, c, True{}, f({==})): {Some{u} == Bool.pick(Maybe<&2, V>, _, Some{u}, None{}): Maybe<&2, V>}
        {==}

# a read that is dropped where it is some
def Crit.pick_drop(-V: Data, mv: Maybe<&2, V>, +c: Bool) -> ({Maybe.is_some(&2, V, mv) == True{}: Bool} -> {c == False{}: Bool}) -> {None{} == Bool.pick(Maybe<&2, V>, c, mv, None{}): Maybe<&2, V>}:
  match mv:
    case None{}:
      f => Equal.sym(Maybe<&2, V>, Bool.pick(Maybe<&2, V>, c, None{}, None{}), None{}, Crit.pick_none(V, c))
    case Some{u}:
      f =>
        %Equal.sym(Bool, c, False{}, f({==})): {None{} == Bool.pick(Maybe<&2, V>, _, Some{u}, None{}): Maybe<&2, V>}
        {==}

# reads that are the same where c holds are picked the same
def Crit.pick_when_eq(-V: Data, c: Bool, a: Maybe<&2, V>, b: Maybe<&2, V>) -> ({c == True{}: Bool} -> {a == b: Maybe<&2, V>}) -> {Bool.pick(Maybe<&2, V>, c, a, None{}) == Bool.pick(Maybe<&2, V>, c, b, None{}): Maybe<&2, V>}:
  match c:
    case True{}:
      f => f({==})
    case False{}:
      f => {==}

# Crit.under_go_lookup at an entry that starts with p, once the test of its
# key and k is known (cb)
def Crit.under_leaf_t(-V: Data, +k2: List<&2, U32>, -w: V, +k: List<&2, U32>, +p: List<&2, U32>, cb: Bool) -> {Key.is_eq(k2, k) == cb: Bool} -> {Key.starts(p, k2) == True{}: Bool} -> {
  Shared.Maybe.when(V, cb, u => Some{w}) == Bool.pick(Maybe<&2, V>, Key.starts(p, k), Shared.Maybe.when(V, cb, u => Some{w}), None{}): Maybe<&2, V>
}:
  match cb:
    case True{}:
      e => st =>
        %Key.is_eq_sound(k2, k)(e): {Some{w} == Bool.pick(Maybe<&2, V>, Key.starts(p, _), Some{w}, None{}): Maybe<&2, V>}
        %Equal.sym(Bool, Key.starts(p, k2), True{}, st): {Some{w} == Bool.pick(Maybe<&2, V>, _, Some{w}, None{}): Maybe<&2, V>}
        {==}
    case False{}:
      e => st => Equal.sym(Maybe<&2, V>, Bool.pick(Maybe<&2, V>, Key.starts(p, k), None{}, None{}), None{}, Crit.pick_none(V, Key.starts(p, k)))

# Crit.under_go_lookup at an entry that does not start with p, once the test
# of its key and k is known (cb)
def Crit.under_leaf_f(-V: Data, +k2: List<&2, U32>, -w: V, +k: List<&2, U32>, +p: List<&2, U32>, cb: Bool) -> {Key.is_eq(k2, k) == cb: Bool} -> {Key.starts(p, k2) == False{}: Bool} -> {
  None{} == Bool.pick(Maybe<&2, V>, Key.starts(p, k), Shared.Maybe.when(V, cb, u => Some{w}), None{}): Maybe<&2, V>
}:
  match cb:
    case True{}:
      e => st =>
        %Key.is_eq_sound(k2, k)(e): {None{} == Bool.pick(Maybe<&2, V>, Key.starts(p, _), Some{w}, None{}): Maybe<&2, V>}
        %Equal.sym(Bool, Key.starts(p, k2), False{}, st): {None{} == Bool.pick(Maybe<&2, V>, _, Some{w}, None{}): Maybe<&2, V>}
        {==}
    case False{}:
      e => st => Equal.sym(Maybe<&2, V>, Bool.pick(Maybe<&2, V>, Key.starts(p, k), None{}, None{}), None{}, Crit.pick_none(V, Key.starts(p, k)))

# the part of a well formed map under p, read from the cursor of p, holds what
# the map holds under each key that starts with p
def Crit.under_go_lookup(~V: Data, m: Crit<V>, +lo: Nat, +at: Nat, +c: Cur, +p: List<&2, U32>, +k: List<&2, U32>) -> {Crit.wf(~V, m, lo) == True{}: Bool} -> {Nat.is_le(at, lo) == True{}: Bool} -> {
  Cur.bits(c) == List.drop(&2, Bool, Key.bits(p), at): List<&2, Bool>
} -> {Crit.lookup(V, Crit.under.go(V, m, at, c, p), k) == Bool.pick(Maybe<&2, V>, Key.starts(p, k), Crit.lookup(V, m, k), None{}): Maybe<&2, V>}:
  match m:
    case Crit.Tip{}:
      h => l => hc => Equal.sym(Maybe<&2, V>, Bool.pick(Maybe<&2, V>, Key.starts(p, k), None{}, None{}), None{}, Crit.pick_none(V, Key.starts(p, k)))
    case Crit.Leaf{+k2, +w}:
      h => l => hc => Shared.Bool.when_cases(
        Crit<V>,
        t => {Crit.lookup(V, t, k) == Bool.pick(Maybe<&2, V>, Key.starts(p, k), Crit.lookup(V, Crit.Leaf{k2, w}, k), None{}): Maybe<&2, V>},
        Key.starts(p, k2),
        u => Crit.Leaf{k2, w},
        u => Crit.Tip{},
        t => Crit.under_leaf_t(V, k2, w, k, p, Key.is_eq(k2, k))({==})(t),
        t => Crit.under_leaf_f(V, k2, w, k, p, Key.is_eq(k2, k))({==})(t)
      )
    case Crit.Fork{+rep, +pos, +e, +z, +o}:
      +h => +l => +hc =>
        +h2 = Crit.skip_at(p, at, pos, c)(Shared.Nat.le_trans(at, lo, pos)(l)(Crit.wf.le(~V, rep, pos, e, z, o, lo)(h)))(hc)
        Shared.Bool.when_cases(
          Crit<V>,
          t => {Crit.lookup(V, t, k) == Bool.pick(Maybe<&2, V>, Key.starts(p, k), Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k), None{}): Maybe<&2, V>},
          Cur.done(Cur.skip(Nat.sub(pos, at), c)),
          u => Shared.Bool.when(Crit<V>, Key.starts(p, rep), q1 => Crit.Fork{rep, pos, e, z, o}, q1 => Crit.Tip{}),
          u => Shared.Bool.when(Crit<V>, Cur.bit(Cur.skip(Nat.sub(pos, at), c)), q1 => Crit.under.go(V, o, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), p), q1 => Crit.under.go(V, z, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), p)),
          +t1 =>
            +nil = Crit.nil_of_done(p, pos, Cur.skip(Nat.sub(pos, at), c))(h2)(t1)
            Shared.Bool.when_cases(
              Crit<V>,
              t => {Crit.lookup(V, t, k) == Bool.pick(Maybe<&2, V>, Key.starts(p, k), Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k), None{}): Maybe<&2, V>},
              Key.starts(p, rep),
              q1 => Crit.Fork{rep, pos, e, z, o},
              q1 => Crit.Tip{},
              +t2 => Crit.pick_keep(V, Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k), Key.starts(p, k))(
                s1 => Equal.trans(Bool, Key.starts(p, k), Key.starts(p, rep), True{}, Key.starts_agree(p, k, rep, pos)(nil)(Crit.in_fork_agree(~V, rep, pos, e, z, o, lo, k)(h)(s1)), t2)
              ),
              +t2 => Crit.pick_drop(V, Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k), Key.starts(p, k))(
                s1 => Equal.trans(Bool, Key.starts(p, k), Key.starts(p, rep), False{}, Key.starts_agree(p, k, rep, pos)(nil)(Crit.in_fork_agree(~V, rep, pos, e, z, o, lo, k)(h)(s1)), t2)
              )
            ),
          +t1 => Shared.Bool.when_cases(
            Crit<V>,
            t => {Crit.lookup(V, t, k) == Bool.pick(Maybe<&2, V>, Key.starts(p, k), Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k), None{}): Maybe<&2, V>},
            Cur.bit(Cur.skip(Nat.sub(pos, at), c)),
            q1 => Crit.under.go(V, o, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), p),
            q1 => Crit.under.go(V, z, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), p),
            +t3 => Equal.trans(
              Maybe<&2, V>,
              Crit.lookup(V, Crit.under.go(V, o, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), p), k),
              Bool.pick(Maybe<&2, V>, Key.starts(p, k), Crit.lookup(V, o, k), None{}),
              Bool.pick(Maybe<&2, V>, Key.starts(p, k), Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k), None{}),
              Crit.under_go_lookup(~V, o, 1n+pos, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), p, k)(Crit.wf.wf_o(~V, rep, pos, e, z, o, lo)(h))(Shared.Nat.le_refl(1n+pos))(Crit.next_at(p, pos, Cur.skip(Nat.sub(pos, at), c))(h2)),
              Crit.pick_when_eq(V, Key.starts(p, k), Crit.lookup(V, o, k), Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k))(
                st => Equal.sym(Maybe<&2, V>, Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k), Crit.lookup(V, o, k), Crit.route_side(~V, rep, pos, e, z, o, lo, k, True{})(h)(
                  Equal.trans(Maybe<&2, Bool>, Key.side(k, pos), Some{Cur.bit(Cur.skip(Nat.sub(pos, at), c))}, Some{True{}}, Key.starts_side(p, k, pos, Cur.skip(Nat.sub(pos, at), c))(h2)(t1)(st), Equal.cong(Bool, Maybe<&2, Bool>, b => Some{b}, Cur.bit(Cur.skip(Nat.sub(pos, at), c)), True{}, t3))
                ))
              )
            ),
            +t3 => Equal.trans(
              Maybe<&2, V>,
              Crit.lookup(V, Crit.under.go(V, z, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), p), k),
              Bool.pick(Maybe<&2, V>, Key.starts(p, k), Crit.lookup(V, z, k), None{}),
              Bool.pick(Maybe<&2, V>, Key.starts(p, k), Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k), None{}),
              Crit.under_go_lookup(~V, z, 1n+pos, 1n+pos, Cur.next(Cur.skip(Nat.sub(pos, at), c)), p, k)(Crit.wf.wf_z(~V, rep, pos, e, z, o, lo)(h))(Shared.Nat.le_refl(1n+pos))(Crit.next_at(p, pos, Cur.skip(Nat.sub(pos, at), c))(h2)),
              Crit.pick_when_eq(V, Key.starts(p, k), Crit.lookup(V, z, k), Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k))(
                st => Equal.sym(Maybe<&2, V>, Crit.lookup(V, Crit.Fork{rep, pos, e, z, o}, k), Crit.lookup(V, z, k), Crit.route_side(~V, rep, pos, e, z, o, lo, k, False{})(h)(
                  Equal.trans(Maybe<&2, Bool>, Key.side(k, pos), Some{Cur.bit(Cur.skip(Nat.sub(pos, at), c))}, Some{False{}}, Key.starts_side(p, k, pos, Cur.skip(Nat.sub(pos, at), c))(h2)(t1)(st), Equal.cong(Bool, Maybe<&2, Bool>, b => Some{b}, Cur.bit(Cur.skip(Nat.sub(pos, at), c)), False{}, t3))
                ))
              )
            )
          )
        )

# Crit.under_lookup, with p and k used more than once
def Crit.under_lookup.go(~V: Data, m: Crit<V>, +p: List<&2, U32>, +k: List<&2, U32>) -> {Crit.wf(~V, m, 0n) == True{}: Bool} -> {
  Crit.lookup(V, Crit.under(V, m, p), k) == Bool.pick(Maybe<&2, V>, Key.starts(p, k), Crit.lookup(V, m, k), None{}): Maybe<&2, V>
}:
  h => Crit.under_go_lookup(~V, m, 0n, 0n, Cur.of(p), p, k)(h)({==})(Equal.sym(List<&2, Bool>, List.drop(&2, Bool, Key.bits(p), 0n), Key.bits(p), Shared.List.drop_zero(&2, Bool, Key.bits(p))))

# a word built from the bits of a word is that word
def Word.of_bits(n: Nat, w: Word(n)) -> {Word.of(n, Word.bits(n, w)) == w: Word(n)}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+(+q):
      match w:
        case WCon{+b, +t}:
          Equal.cong(Word(q), Word(1n+q), x => WCon{b, x}, Word.of(q, Word.bits(q, t)), t, Word.of_bits(q, t))

# reversing bits before acc is reversing them, then acc
def Bits.rev_go(xs: List<&2, Bool>, +acc: List<&2, Bool>) -> {
  List.reverse.go(&2, Bool, xs, acc) == List.append(&2, Bool, List.reverse.go(&2, Bool, xs, []), acc): List<&2, Bool>
}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %Equal.sym(List<&2, Bool>, List.reverse.go(&2, Bool, t, h <> acc), List.append(&2, Bool, List.reverse.go(&2, Bool, t, []), h <> acc), Bits.rev_go(t, h <> acc)): {_ == List.append(&2, Bool, List.reverse.go(&2, Bool, t, [h]), acc): List<&2, Bool>}
      %Equal.sym(List<&2, Bool>, List.reverse.go(&2, Bool, t, [h]), List.append(&2, Bool, List.reverse.go(&2, Bool, t, []), [h]), Bits.rev_go(t, [h])): {List.append(&2, Bool, List.reverse.go(&2, Bool, t, []), h <> acc) == List.append(&2, Bool, _, acc): List<&2, Bool>}
      Equal.sym(List<&2, Bool>, List.append(&2, Bool, List.append(&2, Bool, List.reverse.go(&2, Bool, t, []), [h]), acc), List.append(&2, Bool, List.reverse.go(&2, Bool, t, []), h <> acc), Shared.List.append_assoc(Bool, List.reverse.go(&2, Bool, t, []), [h], acc))

# a word built from n bits has those bits
def Word.bits_of(n: Nat, bs: List<&2, Bool>) -> {List.length(&2, Bool, bs) == n: Nat} -> {Word.bits(n, Word.of(n, bs)) == bs: List<&2, Bool>}:
  match n bs:
    case 0n Nil{}:
      h => {==}
    case 0n Con{b, r}:
      h => Empty.absurd({[] == b <> r: List<&2, Bool>}, Crit.zero_ne_succ(List.length(&2, Bool, r), Equal.sym(Nat, 1n+List.length(&2, Bool, r), 0n, h)))
    case 1n+q Nil{}:
      h => Empty.absurd({Word.bits(1n+q, Word.of(1n+q, [])) == []: List<&2, Bool>}, Crit.zero_ne_succ(q, h))
    case 1n+q Con{+b, +r}:
      h => Equal.cong(List<&2, Bool>, List<&2, Bool>, x => b <> x, Word.bits(q, Word.of(q, r)), r, Word.bits_of(q, r)(Equal.cong(Nat, Nat, t => Crit.pred(t), 1n+List.length(&2, Bool, r), 1n+q, h)))

# a reversed list is as long
def Bits.rev_length(xs: List<&2, Bool>, +acc: List<&2, Bool>) -> {List.length(&2, Bool, List.reverse.go(&2, Bool, xs, acc)) == Nat.add(List.length(&2, Bool, xs), List.length(&2, Bool, acc)): Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Equal.trans(Nat, List.length(&2, Bool, List.reverse.go(&2, Bool, t, h <> acc)), Nat.add(List.length(&2, Bool, t), 1n+List.length(&2, Bool, acc)), 1n+Nat.add(List.length(&2, Bool, t), List.length(&2, Bool, acc)), Bits.rev_length(t, h <> acc), Shared.Nat.add_succ(List.length(&2, Bool, t), List.length(&2, Bool, acc)))

# reversing bits twice gives them back
def Bits.rev_rev(xs: List<&2, Bool>, +acc: List<&2, Bool>, +ys: List<&2, Bool>) -> {List.reverse.go(&2, Bool, List.reverse.go(&2, Bool, xs, acc), ys) == List.reverse.go(&2, Bool, acc, List.append(&2, Bool, xs, ys)): List<&2, Bool>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Bits.rev_rev(t, h <> acc, ys)

# a word reversed twice is the word
def U32.rev_rev(x: U32) -> {U32.rev(U32.rev(x)) == x: U32}:
  match x:
    case U32{+w}:
      %Equal.sym(List<&2, Bool>, Word.bits(32n, Word.of(32n, List.reverse(&2, Bool, Word.bits(32n, w)))), List.reverse(&2, Bool, Word.bits(32n, w)), Word.bits_of(32n, List.reverse(&2, Bool, Word.bits(32n, w)))(
        Equal.trans(Nat, List.length(&2, Bool, List.reverse.go(&2, Bool, Word.bits(32n, w), [])), Nat.add(List.length(&2, Bool, Word.bits(32n, w)), 0n), 32n, Bits.rev_length(Word.bits(32n, w), []), Equal.trans(Nat, Nat.add(List.length(&2, Bool, Word.bits(32n, w)), 0n), List.length(&2, Bool, Word.bits(32n, w)), 32n, Shared.Nat.add_zero(List.length(&2, Bool, Word.bits(32n, w))), Word.bits_length(32n, w)))
      )): {U32{Word.of(32n, List.reverse(&2, Bool, _))} == U32{w}: U32}
      %Equal.sym(List<&2, Bool>, List.reverse.go(&2, Bool, List.reverse.go(&2, Bool, Word.bits(32n, w), []), []), List.reverse.go(&2, Bool, [], List.append(&2, Bool, Word.bits(32n, w), [])), Bits.rev_rev(Word.bits(32n, w), [], [])): {U32{Word.of(32n, _)} == U32{w}: U32}
      %Equal.sym(List<&2, Bool>, List.append(&2, Bool, Word.bits(32n, w), []), Word.bits(32n, w), Shared.List.append_nil(Bool, Word.bits(32n, w))): {U32{Word.of(32n, _)} == U32{w}: U32}
      Equal.cong(Word(32n), U32, y => U32{y}, Word.of(32n, Word.bits(32n, w)), w, Word.of_bits(32n, w))

# words reversed after words reversed are the words, then the rest reversed
def Words.rev_rev(ws: List<&2, U32>, +r: List<&2, U32>) -> {Words.rev(Words.rev(ws, r), []) == List.append(&2, U32, ws, Words.rev(r, [])): List<&2, U32>}:
  match ws:
    case Nil{}:
      {==}
    case Con{+w, +rest}:
      %U32.rev_rev(w): {U32.rev(U32.rev(w)) <> Words.rev(Words.rev(rest, r), []) == _ <> List.append(&2, U32, rest, Words.rev(r, [])): List<&2, U32>}
      Equal.cong(List<&2, U32>, List<&2, U32>, t => U32.rev(U32.rev(w)) <> t, Words.rev(Words.rev(rest, r), []), List.append(&2, U32, rest, Words.rev(r, [])), Words.rev_rev(rest, r))

# Key.ord_value, with r used more than once
def Key.ord_value.go(+n: Nat, +r: List<&2, U32>) -> {Key.ord.value(Key.ord(n, r)) == Some{n}: Maybe<&2, Nat>}:
  %Equal.sym(List<&2, U32>, Words.rev(Words.rev(Codes.Code.count(n, []), r), []), List.append(&2, U32, Codes.Code.count(n, []), Words.rev(r, [])), Words.rev_rev(Codes.Code.count(n, []), r)): {Key.ord.of(Codes.Code.count.read(_)) == Some{n}: Maybe<&2, Nat>}
  %Equal.sym(List<&2, U32>, Codes.Code.count(n, []), Codes.Code.count.go(n, 0, []), Codes.Code.count_go(n, [])): {Key.ord.of(Codes.Code.count.read(List.append(&2, U32, _, Words.rev(r, [])))) == Some{n}: Maybe<&2, Nat>}
  %Equal.sym(List<&2, U32>, List.append(&2, U32, Codes.Code.count.go(n, 0, []), Words.rev(r, [])), Codes.Code.count.go(n, 0, Words.rev(r, [])), Codes.Code.count_append(n, 0, [], Words.rev(r, []))): {Key.ord.of(Codes.Code.count.read(_)) == Some{n}: Maybe<&2, Nat>}
  %Codes.Code.count_go(n, Words.rev(r, [])): {Key.ord.of(Codes.Code.count.read(_)) == Some{n}: Maybe<&2, Nat>}
  %Equal.sym(Maybe<&2, Codes.Read<Nat>>, Codes.Code.count.read(Codes.Code.count(n, Words.rev(r, []))), Some{Codes.Read{n, Words.rev(r, [])}}, Codes.Code.count_read(n, Words.rev(r, []))): {Key.ord.of(_) == Some{n}: Maybe<&2, Nat>}
  {==}

# a zero bit before a one bit comes first, whatever follows
def Crit.bit_lt(ab: Bool, bb: Bool, -x: List<&2, Bool>, -y: List<&2, Bool>) -> {Cmp.is_lt(Bool.cmp(ab, bb)) == True{}: Bool} -> {Bits.lt(ab <> x, bb <> y) == True{}: Bool}:
  match ab bb:
    case False{} True{}:
      h => {==}
    case False{} False{}:
      h => Empty.absurd({Bits.lt(False{} <> x, False{} <> y) == True{}: Bool}, Shared.Bool.false_ne_true(h))
    case True{} True{}:
      h => Empty.absurd({Bits.lt(True{} <> x, True{} <> y) == True{}: Bool}, Shared.Bool.false_ne_true(h))
    case True{} False{}:
      h => Empty.absurd({Bits.lt(True{} <> x, False{} <> y) == True{}: Bool}, Shared.Bool.false_ne_true(h))

# the bits of a word reversed and built back are its bits reversed
def U32.rev_bits(+u: Word(32n)) -> {Word.bits(32n, Word.of(32n, List.reverse(&2, Bool, Word.bits(32n, u)))) == List.reverse(&2, Bool, Word.bits(32n, u)): List<&2, Bool>}:
  Word.bits_of(32n, List.reverse(&2, Bool, Word.bits(32n, u)))(
    Equal.trans(Nat, List.length(&2, Bool, List.reverse.go(&2, Bool, Word.bits(32n, u), [])), Nat.add(List.length(&2, Bool, Word.bits(32n, u)), 0n), 32n, Bits.rev_length(Word.bits(32n, u), []), Equal.trans(Nat, Nat.add(List.length(&2, Bool, Word.bits(32n, u)), 0n), List.length(&2, Bool, Word.bits(32n, u)), 32n, Shared.Nat.add_zero(List.length(&2, Bool, Word.bits(32n, u))), Word.bits_length(32n, u)))
  )

# bits reversed after a, then X, are the bits reversed, then a, then X
def Bits.rev_shape(+xs: List<&2, Bool>, +a: Bool, +x: List<&2, Bool>) -> {List.append(&2, Bool, List.reverse.go(&2, Bool, xs, [a]), x) == List.append(&2, Bool, List.reverse.go(&2, Bool, xs, []), a <> x): List<&2, Bool>}:
  Equal.trans(
    List<&2, Bool>,
    List.append(&2, Bool, List.reverse.go(&2, Bool, xs, [a]), x),
    List.append(&2, Bool, List.append(&2, Bool, List.reverse.go(&2, Bool, xs, []), [a]), x),
    List.append(&2, Bool, List.reverse.go(&2, Bool, xs, []), a <> x),
    Equal.cong(List<&2, Bool>, List<&2, Bool>, t => List.append(&2, Bool, t, x), List.reverse.go(&2, Bool, xs, [a]), List.append(&2, Bool, List.reverse.go(&2, Bool, xs, []), [a]), Bits.rev_go(xs, [a])),
    Shared.List.append_assoc(Bool, List.reverse.go(&2, Bool, xs, []), [a], x)
  )

# Crit.word_lt at one bit on, once the rest compares as t
def Crit.word_lt.step(+q: Nat, +ab: Bool, +at: Word(q), +bb: Bool, +bt: Word(q), +x: List<&2, Bool>, +y: List<&2, Bool>, t: Cmp) -> {Word.cmp(q, at, bt) == t: Cmp} -> (
  {Cmp.is_lt(Word.cmp(q, at, bt)) == True{}: Bool} -> {Bits.lt(List.append(&2, Bool, List.reverse.go(&2, Bool, Word.bits(q, at), []), ab <> x), List.append(&2, Bool, List.reverse.go(&2, Bool, Word.bits(q, bt), []), bb <> y)) == True{}: Bool}
) -> {Cmp.is_lt(Word.cmp.fin(ab, bb, t)) == True{}: Bool} -> {Bits.lt(List.append(&2, Bool, List.reverse.go(&2, Bool, Word.bits(q, at), []), ab <> x), List.append(&2, Bool, List.reverse.go(&2, Bool, Word.bits(q, bt), []), bb <> y)) == True{}: Bool}:
  match t:
    case LT{}:
      e => ih => h => ih(Equal.cong(Cmp, Bool, c => Cmp.is_lt(c), Word.cmp(q, at, bt), LT{}, e))
    case EQ{}:
      e => ih => h =>
        %Shared.Word.cmp_eq(q, at, bt)(e): {Bits.lt(List.append(&2, Bool, List.reverse.go(&2, Bool, Word.bits(q, at), []), ab <> x), List.append(&2, Bool, List.reverse.go(&2, Bool, Word.bits(q, _), []), bb <> y)) == True{}: Bool}
        %Equal.sym(Bool, Bits.lt(List.append(&2, Bool, List.reverse.go(&2, Bool, Word.bits(q, at), []), ab <> x), List.append(&2, Bool, List.reverse.go(&2, Bool, Word.bits(q, at), []), bb <> y)), Bits.lt(ab <> x, bb <> y), Bits.lt_append(List.reverse.go(&2, Bool, Word.bits(q, at), []), ab <> x, bb <> y)): {_ == True{}: Bool}
        Crit.bit_lt(ab, bb, x, y)(h)
    case GT{}:
      e => ih => h => Empty.absurd({Bits.lt(List.append(&2, Bool, List.reverse.go(&2, Bool, Word.bits(q, at), []), ab <> x), List.append(&2, Bool, List.reverse.go(&2, Bool, Word.bits(q, bt), []), bb <> y)) == True{}: Bool}, Shared.Bool.false_ne_true(h))

# a word below another has its reversed bits before the other's
def Crit.word_lt(n: Nat, u: Word(n), v: Word(n), +x: List<&2, Bool>, +y: List<&2, Bool>) -> {Cmp.is_lt(Word.cmp(n, u, v)) == True{}: Bool} -> {
  Bits.lt(List.append(&2, Bool, List.reverse(&2, Bool, Word.bits(n, u)), x), List.append(&2, Bool, List.reverse(&2, Bool, Word.bits(n, v)), y)) == True{}: Bool
}:
  match n:
    case 0n:
      match u v:
        case WNil{} WNil{}:
          h => Empty.absurd({Bits.lt(x, y) == True{}: Bool}, Shared.Bool.false_ne_true(h))
    case 1n+(+q):
      match u v:
        case WCon{+ab, +at} WCon{+bb, +bt}:
          h =>
            %Equal.sym(List<&2, Bool>, List.append(&2, Bool, List.reverse.go(&2, Bool, Word.bits(q, at), [ab]), x), List.append(&2, Bool, List.reverse.go(&2, Bool, Word.bits(q, at), []), ab <> x), Bits.rev_shape(Word.bits(q, at), ab, x)): {
              Bits.lt(_, List.append(&2, Bool, List.reverse.go(&2, Bool, Word.bits(q, bt), [bb]), y)) == True{}: Bool
            }
            %Equal.sym(List<&2, Bool>, List.append(&2, Bool, List.reverse.go(&2, Bool, Word.bits(q, bt), [bb]), y), List.append(&2, Bool, List.reverse.go(&2, Bool, Word.bits(q, bt), []), bb <> y), Bits.rev_shape(Word.bits(q, bt), bb, y)): {
              Bits.lt(List.append(&2, Bool, List.reverse.go(&2, Bool, Word.bits(q, at), []), ab <> x), _) == True{}: Bool
            }
            Crit.word_lt.step(q, ab, at, bb, bt, x, y, Word.cmp(q, at, bt))({==})(Crit.word_lt(q, at, bt, ab <> x, bb <> y))(h)

# the words u below v, reversed, then x and y: the first comes first
def U32.rev_lt(+u: Word(32n), +v: Word(32n), +x: List<&2, Bool>, +y: List<&2, Bool>) -> {U32.is_lt(U32{u}, U32{v}) == True{}: Bool} -> {Bits.lt(List.append(&2, Bool, Word.bits(32n, Word.of(32n, List.reverse(&2, Bool, Word.bits(32n, u)))), x), List.append(&2, Bool, Word.bits(32n, Word.of(32n, List.reverse(&2, Bool, Word.bits(32n, v)))), y)) == True{}: Bool}:
  h =>
    %Equal.sym(List<&2, Bool>, Word.bits(32n, Word.of(32n, List.reverse(&2, Bool, Word.bits(32n, u)))), List.reverse(&2, Bool, Word.bits(32n, u)), U32.rev_bits(u)): {Bits.lt(List.append(&2, Bool, _, x), List.append(&2, Bool, Word.bits(32n, Word.of(32n, List.reverse(&2, Bool, Word.bits(32n, v)))), y)) == True{}: Bool}
    %Equal.sym(List<&2, Bool>, Word.bits(32n, Word.of(32n, List.reverse(&2, Bool, Word.bits(32n, v)))), List.reverse(&2, Bool, Word.bits(32n, v)), U32.rev_bits(v)): {Bits.lt(List.append(&2, Bool, List.reverse(&2, Bool, Word.bits(32n, u)), x), List.append(&2, Bool, _, y)) == True{}: Bool}
    Crit.word_lt(32n, u, v, x, y)(h)

# a key whose first word is above c
def Crit.head_gt(c: U32, ws: List<&2, U32>) -> Bool:
  match ws:
    case Nil{}:
      False{}
    case Con{w, r}:
      U32.is_lt(c, w)

# the key of the word c, then x, comes before words whose first is above c
def Crit.head_lt(+u: Word(32n), ws: List<&2, U32>, +x: List<&2, U32>, +y: List<&2, U32>) -> {Crit.head_gt(U32{u}, ws) == True{}: Bool} -> {Bits.lt(Key.bits(Words.rev([U32{u}], x)), Key.bits(Words.rev(ws, y))) == True{}: Bool}:
  match ws:
    case Nil{}:
      h => Empty.absurd({Bits.lt(Key.bits(Words.rev([U32{u}], x)), Key.bits(y)) == True{}: Bool}, Shared.Bool.false_ne_true(h))
    case Con{U32{+v}, +rest}:
      h => U32.rev_lt(u, v, Key.bits(x), Key.bits(Words.rev(rest, y)))(h)

# U32 order is the order of the numbers
def U32.is_lt_to_nat_back(+a: U32, +b: U32) -> {Nat.is_lt(U32.to_nat(a), U32.to_nat(b)) == U32.is_lt(a, b): Bool}:
  Equal.sym(Bool, U32.is_lt(a, b), Nat.is_lt(U32.to_nat(a), U32.to_nat(b)), Shared.U32.is_lt_to_nat(a, b))

# a word below the top is below the next
def U32.lt_inc(+c: U32) -> {U32.is_eq(c, 4294967295) == False{}: Bool} -> {U32.is_lt(c, U32.inc(c)) == True{}: Bool}:
  h =>
    %U32.is_lt_to_nat_back(c, U32.inc(c)): {_ == True{}: Bool}
    %Equal.sym(Nat, U32.to_nat(U32.inc(c)), 1n+U32.to_nat(c), Shared.U32.inc_to_nat(c)(h)): {Nat.is_lt(U32.to_nat(c), _) == True{}: Bool}
    Shared.Nat.lt_succ(U32.to_nat(c))

# U32 order is transitive
def U32.lt_trans(+a: U32, +b: U32, +c: U32) -> {U32.is_lt(a, b) == True{}: Bool} -> {U32.is_lt(b, c) == True{}: Bool} -> {U32.is_lt(a, c) == True{}: Bool}:
  h1 => h2 =>
    %U32.is_lt_to_nat_back(a, c): {_ == True{}: Bool}
    Shared.Nat.lt_le(U32.to_nat(a), U32.to_nat(b), U32.to_nat(c))(Equal.trans(Bool, Nat.is_lt(U32.to_nat(a), U32.to_nat(b)), U32.is_lt(a, b), True{}, U32.is_lt_to_nat_back(a, b), h1))(
      Shared.Nat.lt_weak(U32.to_nat(b), U32.to_nat(c))(Equal.trans(Bool, Nat.is_lt(U32.to_nat(b), U32.to_nat(c)), U32.is_lt(b, c), True{}, U32.is_lt_to_nat_back(b, c), h2))
    )

# Crit.count_head one digit on, once it is known whether d + 1 is the top
def Crit.count_head.at(+m: Nat, +c: U32, +d: U32, +r: List<&2, U32>, bb: Bool) -> {U32.is_eq(U32.inc(d), 4294967295) == bb: Bool} -> {U32.is_lt(c, d) == True{}: Bool} -> {
  U32.is_eq(d, 4294967295) == False{}: Bool
} -> ({U32.is_lt(c, U32.inc(d)) == True{}: Bool} -> {U32.is_eq(U32.inc(d), 4294967295) == False{}: Bool} -> {Crit.head_gt(c, Codes.Code.count.go(m, U32.inc(d), r)) == True{}: Bool}) -> {
  Crit.head_gt(c, Shared.Bool.when(List<&2, U32>, bb, u => U32.inc(d) <> Codes.Code.count.go(m, 0, r), u => Codes.Code.count.go(m, U32.inc(d), r))) == True{}: Bool
}:
  match bb:
    case True{}:
      eb => +lt => +hd => ih => U32.lt_trans(c, d, U32.inc(d))(lt)(U32.lt_inc(d)(hd))
    case False{}:
      eb => +lt => +hd => ih => ih(U32.lt_trans(c, d, U32.inc(d))(lt)(U32.lt_inc(d)(hd)))(eb)

# the first word of a count from a digit d above c is above c
def Crit.count_head(m: Nat, +c: U32, +d: U32, +r: List<&2, U32>) -> {U32.is_lt(c, d) == True{}: Bool} -> {U32.is_eq(d, 4294967295) == False{}: Bool} -> {
  Crit.head_gt(c, Codes.Code.count.go(m, d, r)) == True{}: Bool
}:
  match m:
    case 0n:
      lt => hd => lt
    case 1n+(+q):
      lt => hd => Crit.count_head.at(q, c, d, r, U32.is_eq(U32.inc(d), 4294967295))({==})(lt)(hd)(l2 => h2 => Crit.count_head(q, c, U32.inc(d), r)(l2)(h2))

# the first word of a count of more than nothing from c is above c
def Crit.count_first.at(+m: Nat, +c: U32, +r: List<&2, U32>, bb: Bool) -> {U32.is_eq(U32.inc(c), 4294967295) == bb: Bool} -> {U32.is_eq(c, 4294967295) == False{}: Bool} -> {
  Crit.head_gt(c, Shared.Bool.when(List<&2, U32>, bb, u => U32.inc(c) <> Codes.Code.count.go(m, 0, r), u => Codes.Code.count.go(m, U32.inc(c), r))) == True{}: Bool
}:
  match bb:
    case True{}:
      eb => hc => U32.lt_inc(c)(hc)
    case False{}:
      eb => hc => Crit.count_head(m, c, U32.inc(c), r)(U32.lt_inc(c)(hc))(eb)

# the counts of a below b from c, reversed, the first before the second
def Crit.count_lt.base(+b: Nat, c: U32, +x: List<&2, U32>, +y: List<&2, U32>) -> {U32.is_eq(c, 4294967295) == False{}: Bool} -> {
  Bits.lt(Key.bits(Words.rev(Codes.Code.count.go(0n, c, []), x)), Key.bits(Words.rev(Codes.Code.count.go(1n+b, c, []), y))) == True{}: Bool
}:
  match c:
    case U32{+u}:
      hc => Crit.head_lt(u, Codes.Code.count.go(1n+b, U32{u}, []), x, y)(Crit.count_first.at(b, U32{u}, [], U32.is_eq(U32.inc(U32{u}), 4294967295))({==})(hc))

# Crit.count_lt one digit on, once it is known whether c + 1 is the top
def Crit.count_lt.step(+a: Nat, +b: Nat, c: U32, +x: List<&2, U32>, +y: List<&2, U32>, bb: Bool) -> {U32.is_eq(U32.inc(c), 4294967295) == bb: Bool} -> {
  Bits.lt(Key.bits(Words.rev(Codes.Code.count.go(a, 0, []), x)), Key.bits(Words.rev(Codes.Code.count.go(b, 0, []), y))) == True{}: Bool
} -> ({U32.is_eq(U32.inc(c), 4294967295) == False{}: Bool} -> {Bits.lt(Key.bits(Words.rev(Codes.Code.count.go(a, U32.inc(c), []), x)), Key.bits(Words.rev(Codes.Code.count.go(b, U32.inc(c), []), y))) == True{}: Bool}) -> {
  Bits.lt(Key.bits(Words.rev(Shared.Bool.when(List<&2, U32>, bb, u => U32.inc(c) <> Codes.Code.count.go(a, 0, []), u => Codes.Code.count.go(a, U32.inc(c), [])), x)), Key.bits(Words.rev(Shared.Bool.when(List<&2, U32>, bb, u => U32.inc(c) <> Codes.Code.count.go(b, 0, []), u => Codes.Code.count.go(b, U32.inc(c), [])), y))) == True{}: Bool
}:
  match c bb:
    case U32{+w} True{}:
      eb => it => ifl =>
        %Equal.sym(Bool, Bits.lt(List.append(&2, Bool, Word.bits(32n, Word.of(32n, List.reverse(&2, Bool, Word.bits(32n, Word.inc(32n, w))))), Key.bits(Words.rev(Codes.Code.count.go(a, 0, []), x))), List.append(&2, Bool, Word.bits(32n, Word.of(32n, List.reverse(&2, Bool, Word.bits(32n, Word.inc(32n, w))))), Key.bits(Words.rev(Codes.Code.count.go(b, 0, []), y)))), Bits.lt(Key.bits(Words.rev(Codes.Code.count.go(a, 0, []), x)), Key.bits(Words.rev(Codes.Code.count.go(b, 0, []), y))), Bits.lt_append(Word.bits(32n, Word.of(32n, List.reverse(&2, Bool, Word.bits(32n, Word.inc(32n, w))))), Key.bits(Words.rev(Codes.Code.count.go(a, 0, []), x)), Key.bits(Words.rev(Codes.Code.count.go(b, 0, []), y)))): {
          _ == True{}: Bool
        }
        it
    case c1 False{}:
      eb => it => ifl => ifl(eb)

# the counts of a below b from the digit c, reversed, then x and y: the
# first comes first
def Crit.count_lt(a: Nat, b: Nat, +c: U32, +x: List<&2, U32>, +y: List<&2, U32>) -> {Nat.is_lt(a, b) == True{}: Bool} -> {U32.is_eq(c, 4294967295) == False{}: Bool} -> {
  Bits.lt(Key.bits(Words.rev(Codes.Code.count.go(a, c, []), x)), Key.bits(Words.rev(Codes.Code.count.go(b, c, []), y))) == True{}: Bool
}:
  match a b:
    case 0n 0n:
      h => hc => Empty.absurd({Bits.lt(Key.bits(Words.rev(Codes.Code.count.go(0n, c, []), x)), Key.bits(Words.rev(Codes.Code.count.go(0n, c, []), y))) == True{}: Bool}, Shared.Bool.false_ne_true(h))
    case 0n 1n+q:
      h => hc => Crit.count_lt.base(q, c, x, y)(hc)
    case 1n+p 0n:
      h => hc => Empty.absurd({Bits.lt(Key.bits(Words.rev(Codes.Code.count.go(1n+p, c, []), x)), Key.bits(Words.rev(Codes.Code.count.go(0n, c, []), y))) == True{}: Bool}, Shared.Bool.false_ne_true(h))
    case 1n+(+p) 1n+(+q):
      +h => hc => Crit.count_lt.step(p, q, c, x, y, U32.is_eq(U32.inc(c), 4294967295))({==})(Crit.count_lt(p, q, 0, x, y)(h)({==}))(hb => Crit.count_lt(p, q, U32.inc(c), x, y)(h)(hb))

# Laws of prefixes and order

# a part under a prefix is well formed
law Crit.under_wf:
  for ~V: Data
  for m: Crit<V>
  for p: List<&2, U32>
  {Crit.wf(~V, m, 0n) == True{}: Bool} -> {Crit.wf(~V, Crit.under(V, m, p), 0n) == True{}: Bool}

def Crit.under_wf(ty, m, p):
  Crit.under_wf.go(~ty, m, p)

# a part under a prefix holds what the map holds under each key that starts
# with the prefix, and nothing else
law Crit.under_lookup:
  for ~V: Data
  for m: Crit<V>
  for p: List<&2, U32>
  for k: List<&2, U32>
  {Crit.wf(~V, m, 0n) == True{}: Bool} -> {
    Crit.lookup(V, Crit.under(V, m, p), k)
      == Bool.pick(Maybe<&2, V>, Key.starts(p, k), Crit.lookup(V, m, k), None{}): Maybe<&2, V>
  }

def Crit.under_lookup(ty, m, p, k):
  Crit.under_lookup.go(~ty, m, p, k)

# the last entry of a map is an entry of it, and no key of it comes after it
law Crit.last_max:
  for ~V: Data
  for m: Crit<V>
  for k: List<&2, U32>
  for v: V
  {Crit.wf(~V, m, 0n) == True{}: Bool} -> {Crit.last(V, m) == Some{Bind{k, v}}: Maybe<&2, Bind<V>>} -> (
    {Crit.lookup(V, m, k) == Some{v}: Maybe<&2, V>}
      & (
        @q: List<&2, U32> -> {Maybe.is_some(&2, V, Crit.lookup(V, m, q)) == True{}: Bool} -> {
          Bits.lt(Key.bits(k), Key.bits(q)) == False{}: Bool
        }
      )
  )

def Crit.last_max(ty, m, k, v):
  h => hl => Crit.last_max.go(~ty, m, 0n, k, v)(h)(hl)

# a map with no last entry holds nothing
law Crit.last_none:
  for ~V: Data
  for m: Crit<V>
  for q: List<&2, U32>
  {Crit.wf(~V, m, 0n) == True{}: Bool} -> {Crit.last(V, m) == None{}: Maybe<&2, Bind<V>>} -> {
    Crit.lookup(V, m, q) == None{}: Maybe<&2, V>
  }

def Crit.last_none(ty, m, q):
  h => hl => Crit.last_none.go(ty, m, q)(hl)

# the key of a number gives the number back
law Key.ord_value:
  for n: Nat
  for r: List<&2, U32>
  {Key.ord.value(Key.ord(n, r)) == Some{n}: Maybe<&2, Nat>}

def Key.ord_value(n, r):
  Key.ord_value.go(n, r)

# Key.ord_lt, with a and b used more than once
def Key.ord_lt.go(+a: Nat, +b: Nat, x: List<&2, U32>, y: List<&2, U32>) -> {Nat.is_lt(a, b) == True{}: Bool} -> {Bits.lt(Key.bits(Key.ord(a, x)), Key.bits(Key.ord(b, y))) == True{}: Bool}:
  h =>
    %Equal.sym(List<&2, U32>, Codes.Code.count(a, []), Codes.Code.count.go(a, 0, []), Codes.Code.count_go(a, [])): {Bits.lt(Key.bits(Words.rev(_, x)), Key.bits(Words.rev(Codes.Code.count(b, []), y))) == True{}: Bool}
    %Equal.sym(List<&2, U32>, Codes.Code.count(b, []), Codes.Code.count.go(b, 0, []), Codes.Code.count_go(b, [])): {Bits.lt(Key.bits(Words.rev(Codes.Code.count.go(a, 0, []), x)), Key.bits(Words.rev(_, y))) == True{}: Bool}
    Crit.count_lt(a, b, 0, x, y)(h)({==})

# the keys of numbers are in the order of the numbers, whatever follows them
law Key.ord_lt:
  for a: Nat
  for b: Nat
  for x: List<&2, U32>
  for y: List<&2, U32>
  {Nat.is_lt(a, b) == True{}: Bool} -> {Bits.lt(Key.bits(Key.ord(a, x)), Key.bits(Key.ord(b, y))) == True{}: Bool}

def Key.ord_lt(a, b, x, y):
  Key.ord_lt.go(a, b, x, y)

# keys that start with the same words are in the order of what follows
law Key.lt_after:
  for p: List<&2, U32>
  for a: List<&2, U32>
  for b: List<&2, U32>
  {
    Bits.lt(Key.bits(List.append(&2, U32, p, a)), Key.bits(List.append(&2, U32, p, b)))
      == Bits.lt(Key.bits(a), Key.bits(b)): Bool
  }

def Key.lt_after(p, a, b):
  Key.lt_after.go(p, a, b)

# Dicts
# -----
# A map in its one shape: a crit-bit map with the proof that it is well
# formed. Each operation keeps the proof, so the laws of a dict need no
# premise, and a dict is a value of its entries alone.

# a dict from keys to values of V
def Dict(-V: Data) -> Data:
  Sigma<&2, &2, Crit<V>, m => {Crit.wf(~V, m, 0n) == True{}: Bool}>

# the map of the dict d
def Dict.crit(-V: Data, d: Dict(V)) -> Crit<V>:
  match d:
    case Tuple{m, w}:
      m

# a dict with no entry
def Dict.new(~V: Data) -> Dict(V):
  (Crit.new(V), Crit.new_wf(~V))

# what d holds under the key k
def Dict.get(-V: Data, d: Dict(V), +k: List<&2, U32>) -> Maybe<&2, V>:
  Crit.get(V, Dict.crit(V, d), k)

# d holds the key k
def Dict.has(-V: Data, d: Dict(V), +k: List<&2, U32>) -> Bool:
  Maybe.is_some(&2, V, Dict.get(V, d, k))

# d with the key k bound to v
def Dict.set(~V: Data, d: Dict(V), +k: List<&2, U32>, +v: V) -> Dict(V):
  match d:
    case Tuple{+m, w}:
      (Crit.set(~V, m, k, v), Crit.upsert_wf(~V, ~(a => b => b), m, k, v)(w))

# d without the key k
def Dict.drop(~V: Data, d: Dict(V), +k: List<&2, U32>) -> Dict(V):
  match d:
    case Tuple{+m, w}:
      (Crit.drop(V, m, k), Crit.drop_wf(~V, m, k)(w))

# the entries of a whose keys b lacks
def Dict.minus(~V: Data, a: Dict(V), b: Dict(V)) -> Dict(V):
  match a b:
    case Tuple{+ma, wa} Tuple{+mb, wb}:
      (Crit.minus(V, ma, mb), Crit.minus_wf(~V, ma, mb)(wa)(wb))

# the count of the entries of d
def Dict.size(-V: Data, d: Dict(V)) -> Nat:
  Crit.size(V, Dict.crit(V, d))

# d has no entry
def Dict.is_empty(-V: Data, d: Dict(V)) -> Bool:
  Crit.is_tip(V, Dict.crit(V, d))

# the entries of d, in the order of their keys
def Dict.entries(-V: Data, d: Dict(V)) -> List<&2, Bind<V>>:
  Crit.entries(V, Dict.crit(V, d))

# the values of the entries es, in order
def Binds.values(-V: Data, es: List<&2, Bind<V>>) -> List<&2, V>:
  match es:
    case Nil{}:
      []
    case Con{Bind{k, v}, rest}:
      v <> Binds.values(V, rest)

# the values of d, in the order of their keys
def Dict.values(-V: Data, d: Dict(V)) -> List<&2, V>:
  Binds.values(V, Dict.entries(V, d))

# s with the key of each of xs, as a set
def Dict.put_keys(
  ~A: Data,
  ~key: A -> List<&2, U32>,
  xs: List<&2, A>,
  s: Dict(Unit)
) -> Dict(Unit):
  match xs:
    case Nil{}:
      s
    case Con{x, r}:
      Dict.put_keys(~A, ~key, r, Dict.set(~Unit, s, key(x), Unit{}))

# xs, each once, but for the keys in seen
def Dict.unique(
  ~A: Data,
  ~key: A -> List<&2, U32>,
  xs: List<&2, A>,
  +seen: Dict(Unit)
) -> List<&2, A>:
  match xs:
    case Nil{}:
      []
    case Con{+x, +r}:
      +k = key(x)
      Shared.Bool.when(
        List<&2, A>,
        Dict.has(Unit, seen, k),
        u => Dict.unique(~A, ~key, r, seen),
        u => x <> Dict.unique(~A, ~key, r, Dict.set(~Unit, seen, k, Unit{}))
      )

# Laws of dicts

# a new dict holds no key
law Dict.get_new:
  for ~V: Data
  for k: List<&2, U32>
  {Dict.get(V, Dict.new(~V), k) == None{}: Maybe<&2, V>}

def Dict.get_new(V, k):
  {==}

# a write that keeps the new value merges to the new value, whatever was there
def Dict.merge_new(~V: Data, e: Maybe<&2, V>, +v: V) -> {Crit.merge(~V, ~(w => x => x), e, v) == v: V}:
  match e:
    case None{}:
      {==}
    case Some{w}:
      {==}

# Dict.get_set on the map m of a dict, with its proof w
def Dict.get_set.at(~V: Data, +m: Crit<V>, +k0: List<&2, U32>, +v: V, +k: List<&2, U32>) -> {
  Crit.wf(~V, m, 0n) == True{}: Bool
} -> {
  Crit.get(V, Crit.set(~V, m, k0, v), k)
    == Bool.pick(Maybe<&2, V>, Key.is_eq(k, k0), Some{v}, Crit.get(V, m, k)): Maybe<&2, V>
}:
  +w =>
    %Equal.sym(
      Maybe<&2, V>,
      Crit.get(V, Crit.set(~V, m, k0, v), k),
      Crit.lookup(V, Crit.set(~V, m, k0, v), k),
      Crit.get_lookup(~V, Crit.set(~V, m, k0, v), k)(Crit.upsert_wf(~V, ~(a => b => b), m, k0, v)(w))
    ): {_ == Bool.pick(Maybe<&2, V>, Key.is_eq(k, k0), Some{v}, Crit.get(V, m, k)): Maybe<&2, V>}
    %Equal.sym(
      Maybe<&2, V>,
      Crit.lookup(V, Crit.set(~V, m, k0, v), k),
      Bool.pick(Maybe<&2, V>, Key.is_eq(k, k0), Some{Crit.merge(~V, ~(a => b => b), Crit.lookup(V, m, k0), v)}, Crit.lookup(V, m, k)),
      Crit.upsert_lookup(~V, ~(a => b => b), m, k0, v, k)(w)
    ): {_ == Bool.pick(Maybe<&2, V>, Key.is_eq(k, k0), Some{v}, Crit.get(V, m, k)): Maybe<&2, V>}
    %Equal.sym(Maybe<&2, V>, Crit.get(V, m, k), Crit.lookup(V, m, k), Crit.get_lookup(~V, m, k)(w)): {
      Bool.pick(Maybe<&2, V>, Key.is_eq(k, k0), Some{Crit.merge(~V, ~(a => b => b), Crit.lookup(V, m, k0), v)}, Crit.lookup(V, m, k))
        == Bool.pick(Maybe<&2, V>, Key.is_eq(k, k0), Some{v}, _): Maybe<&2, V>
    }
    %Equal.sym(V, Crit.merge(~V, ~(a => b => b), Crit.lookup(V, m, k0), v), v, Dict.merge_new(~V, Crit.lookup(V, m, k0), v)): {
      Bool.pick(Maybe<&2, V>, Key.is_eq(k, k0), Some{_}, Crit.lookup(V, m, k))
        == Bool.pick(Maybe<&2, V>, Key.is_eq(k, k0), Some{v}, Crit.lookup(V, m, k)): Maybe<&2, V>
    }
    {==}

# a write binds its key to its value, and no other key
law Dict.get_set:
  for ~V: Data
  for d: Dict(V)
  for k0: List<&2, U32>
  for v: V
  for k: List<&2, U32>
  {
    Dict.get(V, Dict.set(~V, d, k0, v), k)
      == Bool.pick(Maybe<&2, V>, Key.is_eq(k, k0), Some{v}, Dict.get(V, d, k)): Maybe<&2, V>
  }

def Dict.get_set(V, d, k0, v, k):
  match d:
    case Tuple{m, w}:
      Dict.get_set.at(~V, m, k0, v, k)(w)

# Dict.get_drop on the map m of a dict, with its proof w
def Dict.get_drop.at(~V: Data, +m: Crit<V>, +k0: List<&2, U32>, +k: List<&2, U32>) -> {
  Crit.wf(~V, m, 0n) == True{}: Bool
} -> {
  Crit.get(V, Crit.drop(V, m, k0), k)
    == Bool.pick(Maybe<&2, V>, Key.is_eq(k, k0), None{}, Crit.get(V, m, k)): Maybe<&2, V>
}:
  +w =>
    %Equal.sym(
      Maybe<&2, V>,
      Crit.get(V, Crit.drop(V, m, k0), k),
      Crit.lookup(V, Crit.drop(V, m, k0), k),
      Crit.get_lookup(~V, Crit.drop(V, m, k0), k)(Crit.drop_wf(~V, m, k0)(w))
    ): {_ == Bool.pick(Maybe<&2, V>, Key.is_eq(k, k0), None{}, Crit.get(V, m, k)): Maybe<&2, V>}
    %Equal.sym(
      Maybe<&2, V>,
      Crit.lookup(V, Crit.drop(V, m, k0), k),
      Bool.pick(Maybe<&2, V>, Key.is_eq(k, k0), None{}, Crit.lookup(V, m, k)),
      Crit.drop_lookup(~V, m, k0, k)(w)
    ): {_ == Bool.pick(Maybe<&2, V>, Key.is_eq(k, k0), None{}, Crit.get(V, m, k)): Maybe<&2, V>}
    %Equal.sym(Maybe<&2, V>, Crit.get(V, m, k), Crit.lookup(V, m, k), Crit.get_lookup(~V, m, k)(w)): {
      Bool.pick(Maybe<&2, V>, Key.is_eq(k, k0), None{}, Crit.lookup(V, m, k))
        == Bool.pick(Maybe<&2, V>, Key.is_eq(k, k0), None{}, _): Maybe<&2, V>
    }
    {==}

# a drop unbinds its key, and no other key
law Dict.get_drop:
  for ~V: Data
  for d: Dict(V)
  for k0: List<&2, U32>
  for k: List<&2, U32>
  {
    Dict.get(V, Dict.drop(~V, d, k0), k)
      == Bool.pick(Maybe<&2, V>, Key.is_eq(k, k0), None{}, Dict.get(V, d, k)): Maybe<&2, V>
  }

def Dict.get_drop(V, d, k0, k):
  match d:
    case Tuple{m, w}:
      Dict.get_drop.at(~V, m, k0, k)(w)

# Dict.get_minus on the maps ma and mb of two dicts, with their proofs wa and wb
def Dict.get_minus.at(~V: Data, +ma: Crit<V>, +mb: Crit<V>, +k: List<&2, U32>) -> {
  Crit.wf(~V, ma, 0n) == True{}: Bool
} -> {Crit.wf(~V, mb, 0n) == True{}: Bool} -> {
  Crit.get(V, Crit.minus(V, ma, mb), k)
    == Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.get(V, mb, k)), None{}, Crit.get(V, ma, k)): Maybe<&2, V>
}:
  +wa => +wb =>
    %Equal.sym(
      Maybe<&2, V>,
      Crit.get(V, Crit.minus(V, ma, mb), k),
      Crit.lookup(V, Crit.minus(V, ma, mb), k),
      Crit.get_lookup(~V, Crit.minus(V, ma, mb), k)(Crit.minus_wf(~V, ma, mb)(wa)(wb))
    ): {_ == Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.get(V, mb, k)), None{}, Crit.get(V, ma, k)): Maybe<&2, V>}
    %Equal.sym(
      Maybe<&2, V>,
      Crit.lookup(V, Crit.minus(V, ma, mb), k),
      Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, mb, k)), None{}, Crit.lookup(V, ma, k)),
      Crit.minus_lookup(~V, ma, mb, k)(wa)(wb)
    ): {_ == Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.get(V, mb, k)), None{}, Crit.get(V, ma, k)): Maybe<&2, V>}
    %Equal.sym(Maybe<&2, V>, Crit.get(V, mb, k), Crit.lookup(V, mb, k), Crit.get_lookup(~V, mb, k)(wb)): {
      Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, mb, k)), None{}, Crit.lookup(V, ma, k))
        == Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, _), None{}, Crit.get(V, ma, k)): Maybe<&2, V>
    }
    %Equal.sym(Maybe<&2, V>, Crit.get(V, ma, k), Crit.lookup(V, ma, k), Crit.get_lookup(~V, ma, k)(wa)): {
      Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, mb, k)), None{}, Crit.lookup(V, ma, k))
        == Bool.pick(Maybe<&2, V>, Maybe.is_some(&2, V, Crit.lookup(V, mb, k)), None{}, _): Maybe<&2, V>
    }
    {==}

# a difference holds what a holds under each key that b lacks
law Dict.get_minus:
  for ~V: Data
  for a: Dict(V)
  for b: Dict(V)
  for k: List<&2, U32>
  {
    Dict.get(V, Dict.minus(~V, a, b), k)
      == Bool.pick(Maybe<&2, V>, Dict.has(V, b, k), None{}, Dict.get(V, a, k)): Maybe<&2, V>
  }

def Dict.get_minus(V, a, b, k):
  match a b:
    case Tuple{ma, wa} Tuple{mb, wb}:
      Dict.get_minus.at(~V, ma, mb, k)(wa)(wb)

# Dict.size_set on the map m of a dict, with its proof w
def Dict.size_set.at(~V: Data, +m: Crit<V>, +k: List<&2, U32>, +v: V) -> {
  Crit.wf(~V, m, 0n) == True{}: Bool
} -> {
  Crit.size(V, Crit.set(~V, m, k, v))
    == Shared.Nat.add_if(Bool.not(Maybe.is_some(&2, V, Crit.get(V, m, k))), Crit.size(V, m)): Nat
}:
  +w =>
    %Equal.sym(
      Nat,
      Crit.size(V, Crit.set(~V, m, k, v)),
      Shared.Nat.add_if(Maybe.is_none(&2, V, Crit.lookup(V, m, k)), Crit.size(V, m)),
      Crit.size_upsert(~V, ~(a => b => b), m, k, v)(w)
    ): {_ == Shared.Nat.add_if(Bool.not(Maybe.is_some(&2, V, Crit.get(V, m, k))), Crit.size(V, m)): Nat}
    %Equal.sym(Maybe<&2, V>, Crit.get(V, m, k), Crit.lookup(V, m, k), Crit.get_lookup(~V, m, k)(w)): {
      Shared.Nat.add_if(Maybe.is_none(&2, V, Crit.lookup(V, m, k)), Crit.size(V, m))
        == Shared.Nat.add_if(Bool.not(Maybe.is_some(&2, V, _)), Crit.size(V, m)): Nat
    }
    {==}

# a write adds one entry exactly when its key was not there
law Dict.size_set:
  for ~V: Data
  for d: Dict(V)
  for k: List<&2, U32>
  for v: V
  {
    Dict.size(V, Dict.set(~V, d, k, v))
      == Shared.Nat.add_if(Bool.not(Dict.has(V, d, k)), Dict.size(V, d)): Nat
  }

def Dict.size_set(V, d, k, v):
  match d:
    case Tuple{m, w}:
      Dict.size_set.at(~V, m, k, v)(w)

# the proofs that a equals b: one when they are equal, none else
def Bool.code(a: Bool, b: Bool) -> Type:
  match a b:
    case True{} True{}:
      Unit
    case False{} False{}:
      Unit
    case True{} False{}:
      Empty
    case False{} True{}:
      Empty

# the proof that a equals a
def Bool.code_refl(a: Bool) -> Bool.code(a, a):
  match a:
    case True{}:
      Unit{}
    case False{}:
      Unit{}

# the proof of e in Bool.code
def Bool.encode(+a: Bool, +b: Bool, e: {a == b: Bool}) -> Bool.code(a, b):
  %e: Bool.code(a, _)
  Bool.code_refl(a)

# the equation of a proof in Bool.code
def Bool.decode(a: Bool, b: Bool, c: Bool.code(a, b)) -> {a == b: Bool}:
  match a b:
    case True{} True{}:
      {==}
    case False{} False{}:
      {==}
    case True{} False{}:
      match c:
    case False{} True{}:
      match c:

# the proof that a equals a decodes to {==}
def Bool.decode_refl(+a: Bool) -> {Bool.decode(a, a, Bool.code_refl(a)) == {==}: {a == a: Bool}}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# an equation of Bools decodes from its proof in Bool.code
def Bool.decode_encode(+a: Bool, +b: Bool, e: {a == b: Bool}) -> {Bool.decode(a, b, Bool.encode(a, b, e)) == e: {a == b: Bool}}:
  %E@e: {Bool.decode(a, _, Bool.encode(a, _, E)) == E: {a == _: Bool}}
  Bool.decode_refl(a)

# Bool.code has at most one proof
def Bool.code_one(+a: Bool, +b: Bool, c: Bool.code(a, b), d: Bool.code(a, b)) -> {c == d: Bool.code(a, b)}:
  match a b:
    case True{} True{}:
      match c d:
        case Unit{} Unit{}:
          {==}
    case False{} False{}:
      match c d:
        case Unit{} Unit{}:
          {==}
    case True{} False{}:
      match c:
    case False{} True{}:
      match c:

# an equation of Bools has one proof
def Bool.eq_one(+a: Bool, +b: Bool, +e1: {a == b: Bool}, +e2: {a == b: Bool}) -> {e1 == e2: {a == b: Bool}}:
  %Bool.decode_encode(a, b, e1): {_ == e2: {a == b: Bool}}
  %Bool.decode_encode(a, b, e2): {Bool.decode(a, b, Bool.encode(a, b, e1)) == _: {a == b: Bool}}
  %Bool.code_one(a, b, Bool.encode(a, b, e1), Bool.encode(a, b, e2)): {Bool.decode(a, b, Bool.encode(a, b, e1)) == Bool.decode(a, b, _): {a == b: Bool}}
  {==}

# two dicts on equal maps are equal: the proofs that the map is well formed are
def Dict.of_eq(~V: Data, +ma: Crit<V>, +mb: Crit<V>, e: {ma == mb: Crit<V>}) -> @wa: {
  Crit.wf(~V, ma, 0n) == True{}: Bool
} -> @wb: {Crit.wf(~V, mb, 0n) == True{}: Bool} -> {Tuple{ma, wa} == Tuple{mb, wb}: Dict(V)}:
  %e: @wa: {Crit.wf(~V, ma, 0n) == True{}: Bool} -> @wb: {Crit.wf(~V, _, 0n) == True{}: Bool} -> {Tuple{ma, wa} == Tuple{_, wb}: Dict(V)}
  +wa => +wb =>
    %Bool.eq_one(Crit.wf(~V, ma, 0n), True{}, wa, wb): {Tuple{ma, wa} == Tuple{ma, _}: Dict(V)}
    {==}

# a dict is its entries: two dicts with the same entries are the same dict
law Dict.ext:
  for ~V: Data
  for a: Dict(V)
  for b: Dict(V)
  {Dict.entries(V, a) == Dict.entries(V, b): List<&2, Bind<V>>} -> {a == b: Dict(V)}

def Dict.ext(V, a, b):
  match a b:
    case Tuple{+ma, +wa} Tuple{+mb, +wb}:
      h => Dict.of_eq(~V, ma, mb, Crit.ext(~V, ma, mb)(wa)(wb)(h))(wa)(wb)
