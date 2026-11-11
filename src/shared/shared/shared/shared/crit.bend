import Base
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

# a and b are the same key
def Key.is_eq(a: List<&2, U32>, b: List<&2, U32>) -> Bool:
  Shared.List.is_eq(~U32, ~U32.is_eq, a, b)

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

# the first position where the keys a and b differ (none: equal)
def Key.diff(a: List<&2, U32>, b: List<&2, U32>) -> Maybe<&2, Nat>:
  Key.diff.go(a, b, 0n)

# Cursors
# -------
# A cursor reads the bits of a key from a place: the bits left of the word
# that it is in, then the words after it.

# a place in a key: left bits of the current word, then the words rest
type Cur is Data:
  Cur{left: Nat, bits: Word(left), rest: List<&2, U32>}

# a cursor at the start of the key k
def Cur.of(k: List<&2, U32>) -> Cur:
  Cur{0n, WNil{}, k}

# the bits that the cursor c has yet to read
def Cur.bits(c: Cur) -> List<&2, Bool>:
  match c:
    case Cur{n, w, r}:
      List.append(&2, Bool, Word.bits(n, w), Key.bits(r))

# the cursor c has no bit left
def Cur.done(c: Cur) -> Bool:
  match c:
    case Cur{0n, w, Nil{}}:
      True{}
    case _:
      False{}

# the next bit of the cursor c (False: none is left)
def Cur.bit(c: Cur) -> Bool:
  match c:
    case Cur{1n+p, WCon{b, t}, r}:
      b
    case Cur{0n, w, Con{U32{WCon{b, t}}, r}}:
      b
    case _:
      False{}

# the cursor c one bit on (c itself: none is left)
def Cur.next(c: Cur) -> Cur:
  match c:
    case Cur{1n+p, WCon{b, t}, r}:
      Cur{p, t, r}
    case Cur{0n, w, Con{U32{WCon{b, t}}, r}}:
      Cur{31n, t, r}
    case Cur{0n, w, Nil{}}:
      Cur{0n, WNil{}, Nil{}}

# the cursor c, n bits on, one bit at a time
def Cur.drop(n: Nat, c: Cur) -> Cur:
  match n:
    case 0n:
      c
    case 1n+p:
      Cur.drop(p, Cur.next(c))

# a cursor n bits into the words ws, a whole word at a time while it can
def Cur.words(ws: List<&2, U32>, +n: Nat) -> Cur:
  match ws:
    case Nil{}:
      Cur{0n, WNil{}, Nil{}}
    case Con{+w, +r}:
      Shared.Bool.when(
        Cur,
        Nat.is_le(32n, n),
        u => Cur.words(r, Nat.sub(n, 32n)),
        u => Cur.drop(n, Cur{0n, WNil{}, w <> r})
      )

# the cursor c, n bits on
def Cur.skip(+n: Nat, c: Cur) -> Cur:
  match c:
    case Cur{+left, +w, +r}:
      Shared.Bool.when(
        Cur,
        Nat.is_le(left, n),
        u => Cur.words(r, Nat.sub(n, left)),
        u => Cur.drop(n, Cur{left, w, r})
      )

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

# a cursor one bit on reads its bits after the first
def Cur.next_bits(c: Cur) -> {Cur.bits(Cur.next(c)) == List.drop(&2, Bool, Cur.bits(c), 1n): List<&2, Bool>}:
  match c:
    case Cur{1n+p, WCon{b, t}, r}:
      +x = List.append(&2, Bool, Word.bits(p, t), Key.bits(r))
      Equal.sym(List<&2, Bool>, List.drop(&2, Bool, x, 0n), x, Shared.List.drop_zero(&2, Bool, x))
    case Cur{0n, w, Con{U32{WCon{b, t}}, r}}:
      +x = List.append(&2, Bool, Word.bits(31n, t), Key.bits(r))
      Equal.sym(List<&2, Bool>, List.drop(&2, Bool, x, 0n), x, Shared.List.drop_zero(&2, Bool, x))
    case Cur{0n, w, Nil{}}:
      {==}

# a cursor is done when it has no bit left
def Cur.done_bits(c: Cur) -> {Cur.done(c) == List.is_empty(&2, Bool, Cur.bits(c)): Bool}:
  match c:
    case Cur{1n+p, WCon{b, t}, r}:
      {==}
    case Cur{0n, w, Con{U32{WCon{b, t}}, r}}:
      {==}
    case Cur{0n, w, Nil{}}:
      {==}

# the next bit of a cursor is the first of its bits
def Cur.bit_bits(c: Cur) -> {Cur.bit(c) == Shared.List.head_or(Bool, Cur.bits(c), False{}): Bool}:
  match c:
    case Cur{1n+p, WCon{b, t}, r}:
      {==}
    case Cur{0n, w, Con{U32{WCon{b, t}}, r}}:
      {==}
    case Cur{0n, w, Nil{}}:
      {==}

# a cursor n bits on, one at a time, reads its bits after the first n
def Cur.drop_bits(n: Nat, +c: Cur) -> {Cur.bits(Cur.drop(n, c)) == List.drop(&2, Bool, Cur.bits(c), n): List<&2, Bool>}:
  match n:
    case 0n:
      Equal.sym(List<&2, Bool>, List.drop(&2, Bool, Cur.bits(c), 0n), Cur.bits(c), Shared.List.drop_zero(&2, Bool, Cur.bits(c)))
    case 1n+(+p):
      %Equal.sym(
        List<&2, Bool>,
        Cur.bits(Cur.drop(p, Cur.next(c))),
        List.drop(&2, Bool, Cur.bits(Cur.next(c)), p),
        Cur.drop_bits(p, Cur.next(c))
      ): {_ == List.drop(&2, Bool, Cur.bits(c), 1n+p): List<&2, Bool>}
      %Equal.sym(
        List<&2, Bool>,
        Cur.bits(Cur.next(c)),
        List.drop(&2, Bool, Cur.bits(c), 1n),
        Cur.next_bits(c)
      ): {List.drop(&2, Bool, _, p) == List.drop(&2, Bool, Cur.bits(c), 1n+p): List<&2, Bool>}
      Shared.List.drop_one_drop(Bool, Cur.bits(c), p)

# a cursor n bits into some words, a word at a time, reads their bits after
# the first n
def Cur.words.long(
  +x: Word(32n),
  +r: List<&2, U32>,
  +n: Nat,
  h: {Nat.is_le(32n, n) == True{}: Bool},
  ih: {Cur.bits(Cur.words(r, Nat.sub(n, 32n))) == List.drop(&2, Bool, Key.bits(r), Nat.sub(n, 32n)): List<&2, Bool>}
) -> {Cur.bits(Cur.words(r, Nat.sub(n, 32n))) == List.drop(&2, Bool, Key.bits(U32{x} <> r), n): List<&2, Bool>}:
      %Equal.sym(
        List<&2, Bool>,
        Cur.bits(Cur.words(r, Nat.sub(n, 32n))),
        List.drop(&2, Bool, Key.bits(r), Nat.sub(n, 32n)),
        ih
      ): {_ == List.drop(&2, Bool, List.append(&2, Bool, Word.bits(32n, x), Key.bits(r)), n): List<&2, Bool>}
      %Equal.sym(
        List<&2, Bool>,
        List.drop(&2, Bool, List.append(&2, Bool, Word.bits(32n, x), Key.bits(r)), n),
        List.drop(&2, Bool, Key.bits(r), Nat.sub(n, List.length(&2, Bool, Word.bits(32n, x)))),
        Shared.List.drop_append_le(Bool, Word.bits(32n, x), Key.bits(r), n)((
          %Equal.sym(Nat, List.length(&2, Bool, Word.bits(32n, x)), 32n, Word.bits_length(32n, x)): {
            Nat.is_le(_, n) == True{}: Bool
          }
          h
        ))
      ): {List.drop(&2, Bool, Key.bits(r), Nat.sub(n, 32n)) == _: List<&2, Bool>}
      %Equal.sym(Nat, List.length(&2, Bool, Word.bits(32n, x)), 32n, Word.bits_length(32n, x)): {
        List.drop(&2, Bool, Key.bits(r), Nat.sub(n, 32n)) == List.drop(&2, Bool, Key.bits(r), Nat.sub(n, _)): List<&2, Bool>
      }
      {==}

# a cursor n bits into the words ws reads their bits after the first n
def Cur.words_bits(ws: List<&2, U32>, +n: Nat) -> {
  Cur.bits(Cur.words(ws, n)) == List.drop(&2, Bool, Key.bits(ws), n): List<&2, Bool>
}:
  match ws:
    case Nil{}:
      {==}
    case Con{U32{+x}, +r}:
      Shared.Bool.when_cases(
        Cur,
        c => {Cur.bits(c) == List.drop(&2, Bool, Key.bits(U32{x} <> r), n): List<&2, Bool>},
        Nat.is_le(32n, n),
        u => Cur.words(r, Nat.sub(n, 32n)),
        u => Cur.drop(n, Cur{0n, WNil{}, U32{x} <> r}),
        h => Cur.words.long(x, r, n, h, Cur.words_bits(r, Nat.sub(n, 32n))),
        h => Cur.drop_bits(n, Cur{0n, WNil{}, U32{x} <> r})
      )

# a cursor that skips past the word it is in reads the bits after the first n
def Cur.skip.long(
  +left: Nat,
  +w: Word(left),
  +r: List<&2, U32>,
  +n: Nat,
  h: {Nat.is_le(left, n) == True{}: Bool}
) -> {
  Cur.bits(Cur.words(r, Nat.sub(n, left)))
    == List.drop(&2, Bool, List.append(&2, Bool, Word.bits(left, w), Key.bits(r)), n): List<&2, Bool>
}:
      %Equal.sym(
        List<&2, Bool>,
        Cur.bits(Cur.words(r, Nat.sub(n, left))),
        List.drop(&2, Bool, Key.bits(r), Nat.sub(n, left)),
        Cur.words_bits(r, Nat.sub(n, left))
      ): {_ == List.drop(&2, Bool, List.append(&2, Bool, Word.bits(left, w), Key.bits(r)), n): List<&2, Bool>}
      %Equal.sym(
        List<&2, Bool>,
        List.drop(&2, Bool, List.append(&2, Bool, Word.bits(left, w), Key.bits(r)), n),
        List.drop(&2, Bool, Key.bits(r), Nat.sub(n, List.length(&2, Bool, Word.bits(left, w)))),
        Shared.List.drop_append_le(Bool, Word.bits(left, w), Key.bits(r), n)((
          %Equal.sym(Nat, List.length(&2, Bool, Word.bits(left, w)), left, Word.bits_length(left, w)): {
            Nat.is_le(_, n) == True{}: Bool
          }
          h
        ))
      ): {List.drop(&2, Bool, Key.bits(r), Nat.sub(n, left)) == _: List<&2, Bool>}
      %Equal.sym(Nat, List.length(&2, Bool, Word.bits(left, w)), left, Word.bits_length(left, w)): {
        List.drop(&2, Bool, Key.bits(r), Nat.sub(n, left)) == List.drop(&2, Bool, Key.bits(r), Nat.sub(n, _)): List<&2, Bool>
      }
      {==}

# a cursor n bits on reads its bits after the first n
def Cur.skip_bits(+n: Nat, c: Cur) -> {
  Cur.bits(Cur.skip(n, c)) == List.drop(&2, Bool, Cur.bits(c), n): List<&2, Bool>
}:
  match c:
    case Cur{+left, +w, +r}:
      Shared.Bool.when_cases(
        Cur,
        c2 => {Cur.bits(c2) == List.drop(&2, Bool, Cur.bits(Cur{left, w, r}), n): List<&2, Bool>},
        Nat.is_le(left, n),
        u => Cur.words(r, Nat.sub(n, left)),
        u => Cur.drop(n, Cur{left, w, r}),
        h => Cur.skip.long(left, w, r, n, h),
        h => Cur.drop_bits(n, Cur{left, w, r})
      )

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

# the keys a and b differ first where their bits do
def Key.diff_bits(+a: List<&2, U32>, +b: List<&2, U32>) -> {
  Key.diff(a, b) == Bits.diff(Key.bits(a), Key.bits(b)): Maybe<&2, Nat>
}:
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
def Key.is_eq_sound(a: List<&2, U32>, b: List<&2, U32>) -> {Key.is_eq(a, b) == True{}: Bool} -> {a == b: List<&2, U32>}:
  Shared.List.is_eq_sound(~U32, ~U32.is_eq, ~Shared.U32.laws(), a, b)

# Key.is_eq is True for a key and itself
def Key.is_eq_refl(a: List<&2, U32>) -> {Key.is_eq(a, a) == True{}: Bool}:
  Shared.List.is_eq_refl(~U32, ~U32.is_eq, ~Shared.U32.laws(), a)

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
  Key.diff_go_none(a, b, 0n)

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

# a map with no entry is well formed
law Crit.new_wf:
  for ~V: Data
  {Crit.wf(~V, Crit.new(V), 0n) == True{}: Bool}

def Crit.new_wf(ty):
  {==}

# a write keeps a map well formed
law Crit.upsert_wf:
  for ~V: Data
  for ~f: V -> V -> V
  for m: Crit<V>
  for k: List<&2, U32>
  for v: V
  {Crit.wf(~V, m, 0n) == True{}: Bool} -> {Crit.wf(~V, Crit.upsert(~V, ~f, m, k, v), 0n) == True{}: Bool}

def Crit.upsert_wf(ty, f, m, k, v):
  ?TODO

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
  ?TODO

# a drop keeps a map well formed
law Crit.drop_wf:
  for ~V: Data
  for m: Crit<V>
  for k: List<&2, U32>
  {Crit.wf(~V, m, 0n) == True{}: Bool} -> {Crit.wf(~V, Crit.drop(V, m, k), 0n) == True{}: Bool}

def Crit.drop_wf(ty, m, k):
  ?TODO

# a choice of nothing, then x, is x, when the first choice e is nothing
def Crit.or_none_first(-V: Data, e: Maybe<&2, V>, +x: Maybe<&2, V>) -> {e == None{}: Maybe<&2, V>} -> {
  x == Maybe.or(&2, V, e, x): Maybe<&2, V>
}:
  h => Equal.cong(Maybe<&2, V>, Maybe<&2, V>, t => Maybe.or(&2, V, t, x), None{}, e, Equal.sym(Maybe<&2, V>, e, None{}, h))

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

# a drop unbinds its key and no other, with m, k and q used more than once
def Crit.drop_lookup.at(~V: Data, +m: Crit<V>, +k: List<&2, U32>, +q: List<&2, U32>) -> {Crit.wf(~V, m, 0n) == True{}: Bool} -> {
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
          Crit.drop_go_none(~V, m, 0n, 0n, Cur.of(k), k)(h)({==})(
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
  Crit.drop_lookup.at(~ty, m, k, q)

# a union keeps maps well formed
law Crit.union_wf:
  for ~V: Data
  for ~j: V -> V -> V
  for a: Crit<V>
  for b: Crit<V>
  {Crit.wf(~V, a, 0n) == True{}: Bool} -> {Crit.wf(~V, b, 0n) == True{}: Bool} -> {Crit.wf(~V, Crit.union(~V, ~j, a, b), 0n) == True{}: Bool}

def Crit.union_wf(ty, j, a, b):
  ?TODO

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
  ?TODO

# a difference keeps maps well formed
law Crit.minus_wf:
  for ~V: Data
  for a: Crit<V>
  for b: Crit<V>
  {Crit.wf(~V, a, 0n) == True{}: Bool} -> {Crit.wf(~V, b, 0n) == True{}: Bool} -> {Crit.wf(~V, Crit.minus(V, a, b), 0n) == True{}: Bool}

def Crit.minus_wf(ty, a, b):
  ?TODO

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
  ?TODO

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

# two well formed maps that read the same are the same map
law Crit.ext:
  for ~V: Data
  for a: Crit<V>
  for b: Crit<V>
  {Crit.wf(~V, a, 0n) == True{}: Bool} -> {Crit.wf(~V, b, 0n) == True{}: Bool} -> (@q: List<&2, U32> -> {Crit.lookup(V, a, q) == Crit.lookup(V, b, q): Maybe<&2, V>}) -> {a == b: Crit<V>}

def Crit.ext(ty, a, b):
  ?TODO

# a union is the same either way round, when j is
law Crit.union_comm:
  for ~V: Data
  for ~j: V -> V -> V
  for ~comm: @x: V -> @y: V -> {j(x, y) == j(y, x): V}
  for a: Crit<V>
  for b: Crit<V>
  {Crit.wf(~V, a, 0n) == True{}: Bool} -> {Crit.wf(~V, b, 0n) == True{}: Bool} -> {Crit.union(~V, ~j, a, b) == Crit.union(~V, ~j, b, a): Crit<V>}

def Crit.union_comm(ty, j, comm, a, b):
  ?TODO

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
  ?TODO

# a union with itself is the map, when j is
law Crit.union_idem:
  for ~V: Data
  for ~j: V -> V -> V
  for ~idem: @x: V -> {j(x, x) == x: V}
  for a: Crit<V>
  {Crit.wf(~V, a, 0n) == True{}: Bool} -> {Crit.union(~V, ~j, a, a) == a: Crit<V>}

def Crit.union_idem(ty, j, idem, a):
  ?TODO

# a map holds as many entries as it holds keys: a map that holds each key of
# another is no smaller
law Crit.size_le:
  for ~V: Data
  for a: Crit<V>
  for b: Crit<V>
  {Crit.wf(~V, a, 0n) == True{}: Bool} -> {Crit.wf(~V, b, 0n) == True{}: Bool} -> (@q: List<&2, U32> -> {
    Maybe.is_some(&2, V, Crit.lookup(V, a, q)) == True{}: Bool
  } -> {Maybe.is_some(&2, V, Crit.lookup(V, b, q)) == True{}: Bool}) -> {
    Nat.is_le(Crit.size(V, a), Crit.size(V, b)) == True{}: Bool
  }

def Crit.size_le(ty, a, b):
  ?TODO

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
  ?TODO
