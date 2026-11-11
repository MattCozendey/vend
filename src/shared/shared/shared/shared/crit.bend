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
def Crit.join.end(-V: Data, x: Crit<V>, y: Crit<V>, d: Nat, b: Bool) -> Crit<V>:
  match x b:
    case Crit.Leaf{k, v} True{}:
      Crit.Fork{k, d, Some{v}, Crit.Tip{}, y}
    case Crit.Leaf{k, v} False{}:
      Crit.Fork{k, d, Some{v}, y, Crit.Tip{}}
    case _ b1:
      y

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
