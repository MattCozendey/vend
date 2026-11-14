import Base
import ./crit.bend as Crits
import ./shared.bend as Shared

# The order of the entries of a map
# ---------------------------------
# A map lists its entries in the order of the bits of their keys (Key.lt): a
# key that ends comes before the keys that go on, and a zero before a one. So
# the entries of a well formed map are a sorted list, a sorted list is a
# function of what it holds under each key, and a write to a map is an insert
# into its sorted list. An index that keeps some of the entries, in order,
# then follows a write by one insert.

# the key a comes before the key b, in the order of the entries of a map
def Key.lt(a: List<&2, U32>, b: List<&2, U32>) -> Bool:
  Crits.Bits.lt(Crits.Key.bits(a), Crits.Key.bits(b))

# p holds of g and the key of each of the entries es
def Binds.all(
  ~V: Data,
  ~G: Data,
  ~p: G -> List<&2, U32> -> Bool,
  es: List<&2, Crits.Bind<V>>,
  +g: G
) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Con{Crits.Bind{k, v}, r}:
      Bool.and(p(g)(k), Binds.all(~V, ~G, ~p, r, g))

# the entries es are in the strict order of their keys: each key comes before
# the keys of the entries after it
def Binds.sorted(~V: Data, es: List<&2, Crits.Bind<V>>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Con{Crits.Bind{+k, v}, +r}:
      Bool.and(Binds.all(~V, ~List<&2, U32>, ~Key.lt, r, k), Binds.sorted(~V, r))

# the value of the first of the entries es whose key is k
def Binds.get(-V: Data, es: List<&2, Crits.Bind<V>>, +k: List<&2, U32>) -> Maybe<&2, V>:
  match es:
    case Nil{}:
      None{}
    case Con{Crits.Bind{k2, v}, r}:
      Bool.pick(Maybe<&2, V>, Crits.Key.is_eq(k2, k), Some{v}, Binds.get(V, r, k))

# the sorted entries es with the key k bound to v: a new entry at the place of
# k, or v in the entry of k
def Binds.insert(
  -V: Data,
  es: List<&2, Crits.Bind<V>>,
  +k: List<&2, U32>,
  +v: V
) -> List<&2, Crits.Bind<V>>:
  match es:
    case Nil{}:
      [Crits.Bind{k, v}]
    case Con{Crits.Bind{+k1, +v1}, +r}:
      Shared.Bool.when(
        List<&2, Crits.Bind<V>>,
        Key.lt(k, k1),
        u => Crits.Bind{k, v} <> Crits.Bind{k1, v1} <> r,
        u => Shared.Bool.when(
          List<&2, Crits.Bind<V>>,
          Crits.Key.is_eq(k1, k),
          w => Crits.Bind{k1, v} <> r,
          w => Crits.Bind{k1, v1} <> Binds.insert(V, r, k, v)
        )
      )

# the values xs, sorted by their keys, with x: at the place of its key, or in
# the place of the value of its key
def Values.insert(~V: Data, ~key: V -> List<&2, U32>, xs: List<&2, V>, +x: V) -> List<&2, V>:
  match xs:
    case Nil{}:
      [x]
    case Con{+y, +r}:
      Shared.Bool.when(
        List<&2, V>,
        Key.lt(key(x), key(y)),
        u => x <> y <> r,
        u => Shared.Bool.when(
          List<&2, V>,
          Crits.Key.is_eq(key(y), key(x)),
          w => x <> r,
          w => y <> Values.insert(~V, ~key, r, x)
        )
      )

# each of the entries es sits under the key of its value
def Binds.keyed(~V: Data, ~key: V -> List<&2, U32>, es: List<&2, Crits.Bind<V>>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Con{Crits.Bind{k, v}, r}:
      Bool.and(Crits.Key.is_eq(k, key(v)), Binds.keyed(~V, ~key, r))

# Laws of the order of bits
# -------------------------

# what holds of True when b is True, and of False when b is False, holds of b
def Bool.by(
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

# bits that come before others do not come after them
def Bits.lt_asym(
  a: List<&2, Bool>,
  b: List<&2, Bool>
) -> {Crits.Bits.lt(a, b) == True{}: Bool} -> {Crits.Bits.lt(b, a) == False{}: Bool}:
  match a b:
    case Nil{} Nil{}:
      h => {==}
    case Nil{} Con{y, rb}:
      h => {==}
    case Con{x, ra} Nil{}:
      h => Empty.absurd({Crits.Bits.lt([], x <> ra) == False{}: Bool}, Shared.Bool.false_ne_true(h))
    case Con{True{}, ra} Con{True{}, rb}:
      h => Bits.lt_asym(ra, rb)(h)
    case Con{False{}, ra} Con{False{}, rb}:
      h => Bits.lt_asym(ra, rb)(h)
    case Con{True{}, ra} Con{False{}, rb}:
      h => Empty.absurd(
        {Crits.Bits.lt(False{} <> rb, True{} <> ra) == False{}: Bool},
        Shared.Bool.false_ne_true(h)
      )
    case Con{False{}, ra} Con{True{}, rb}:
      h => {==}

# the order of bits is transitive
def Bits.lt_trans(
  a: List<&2, Bool>,
  b: List<&2, Bool>,
  c: List<&2, Bool>
) -> {
  Crits.Bits.lt(a, b) == True{}: Bool
} -> {Crits.Bits.lt(b, c) == True{}: Bool} -> {Crits.Bits.lt(a, c) == True{}: Bool}:
  match a b c:
    case x Nil{} z:
      h1 => h2 => Empty.absurd(
        {Crits.Bits.lt(x, z) == True{}: Bool},
        Shared.Bool.false_ne_true(
          Equal.trans(
            Bool,
            False{},
            Crits.Bits.lt(x, []),
            True{},
            Equal.sym(Bool, Crits.Bits.lt(x, []), False{}, Crits.Bits.lt_nil(x)),
            h1
          )
        )
      )
    case x Con{y, rb} Nil{}:
      h1 => h2 => Empty.absurd(
        {Crits.Bits.lt(x, []) == True{}: Bool},
        Shared.Bool.false_ne_true(h2)
      )
    case Nil{} Con{y, rb} Con{z, rc}:
      h1 => h2 => {==}
    case Con{False{}, ra} Con{False{}, rb} Con{False{}, rc}:
      h1 => h2 => Bits.lt_trans(ra, rb, rc)(h1)(h2)
    case Con{False{}, ra} Con{False{}, rb} Con{True{}, rc}:
      h1 => h2 => {==}
    case Con{False{}, ra} Con{True{}, rb} Con{False{}, rc}:
      h1 => h2 => Empty.absurd(
        {Crits.Bits.lt(False{} <> ra, False{} <> rc) == True{}: Bool},
        Shared.Bool.false_ne_true(h2)
      )
    case Con{False{}, ra} Con{True{}, rb} Con{True{}, rc}:
      h1 => h2 => {==}
    case Con{True{}, ra} Con{False{}, rb} Con{z, rc}:
      h1 => h2 => Empty.absurd(
        {Crits.Bits.lt(True{} <> ra, z <> rc) == True{}: Bool},
        Shared.Bool.false_ne_true(h1)
      )
    case Con{True{}, ra} Con{True{}, rb} Con{False{}, rc}:
      h1 => h2 => Empty.absurd(
        {Crits.Bits.lt(True{} <> ra, False{} <> rc) == True{}: Bool},
        Shared.Bool.false_ne_true(h2)
      )
    case Con{True{}, ra} Con{True{}, rb} Con{True{}, rc}:
      h1 => h2 => Bits.lt_trans(ra, rb, rc)(h1)(h2)

# bits of which neither come before the others are the same
def Bits.lt_none(
  a: List<&2, Bool>,
  b: List<&2, Bool>
) -> {
  Crits.Bits.lt(a, b) == False{}: Bool
} -> {Crits.Bits.lt(b, a) == False{}: Bool} -> {a == b: List<&2, Bool>}:
  match a b:
    case Nil{} Nil{}:
      h1 => h2 => {==}
    case Nil{} Con{y, rb}:
      h1 => h2 => Empty.absurd({[] == y <> rb: List<&2, Bool>}, Shared.Bool.true_ne_false(h1))
    case Con{x, ra} Nil{}:
      h1 => h2 => Empty.absurd({x <> ra == []: List<&2, Bool>}, Shared.Bool.true_ne_false(h2))
    case Con{True{}, ra} Con{True{}, rb}:
      h1 => h2 => Equal.cong(
        List<&2, Bool>,
        List<&2, Bool>,
        t => True{} <> t,
        ra,
        rb,
        Bits.lt_none(ra, rb)(h1)(h2)
      )
    case Con{False{}, ra} Con{False{}, rb}:
      h1 => h2 => Equal.cong(
        List<&2, Bool>,
        List<&2, Bool>,
        t => False{} <> t,
        ra,
        rb,
        Bits.lt_none(ra, rb)(h1)(h2)
      )
    case Con{True{}, ra} Con{False{}, rb}:
      h1 => h2 => Empty.absurd(
        {True{} <> ra == False{} <> rb: List<&2, Bool>},
        Shared.Bool.true_ne_false(h2)
      )
    case Con{False{}, ra} Con{True{}, rb}:
      h1 => h2 => Empty.absurd(
        {False{} <> ra == True{} <> rb: List<&2, Bool>},
        Shared.Bool.true_ne_false(h1)
      )

# bits a with a zero at n come before bits b that agree with them before n
# and have a one there
def Bits.lt_sides(
  n: Nat,
  a: List<&2, Bool>,
  b: List<&2, Bool>
) -> {
  Crits.Bits.agree_n(n, a, b) == True{}: Bool
} -> {
  Crits.Bits.at(a, n) == Some{False{}}: Maybe<&2, Bool>
} -> {
  Crits.Bits.at(b, n) == Some{True{}}: Maybe<&2, Bool>
} -> {Crits.Bits.lt(a, b) == True{}: Bool}:
  match n a b:
    case 0n Con{x, ra} Con{y, rb}:
      h => ha => hb =>
        %Equal.sym(
          Bool,
          x,
          False{},
          Shared.Maybe.some_inj(Bool, x, False{}, ha)
        ): {Crits.Bits.lt(_ <> ra, y <> rb) == True{}: Bool}
        %Equal.sym(
          Bool,
          y,
          True{},
          Shared.Maybe.some_inj(Bool, y, True{}, hb)
        ): {Crits.Bits.lt(False{} <> ra, _ <> rb) == True{}: Bool}
        {==}
    case 0n Nil{} y:
      h => ha => hb => Empty.absurd(
        {Crits.Bits.lt([], y) == True{}: Bool},
        Shared.Maybe.none_ne_some(Bool, False{}, ha)
      )
    case 0n Con{x, ra} Nil{}:
      h => ha => hb => Empty.absurd(
        {Crits.Bits.lt(x <> ra, []) == True{}: Bool},
        Shared.Maybe.none_ne_some(Bool, True{}, hb)
      )
    case 1n+q Nil{} y:
      h => ha => hb => Empty.absurd(
        {Crits.Bits.lt([], y) == True{}: Bool},
        Shared.Maybe.none_ne_some(Bool, False{}, ha)
      )
    case 1n+q Con{x, ra} Nil{}:
      h => ha => hb => Empty.absurd(
        {Crits.Bits.lt(x <> ra, []) == True{}: Bool},
        Shared.Maybe.none_ne_some(Bool, True{}, hb)
      )
    case 1n+q Con{True{}, ra} Con{True{}, rb}:
      h => ha => hb => Bits.lt_sides(q, ra, rb)(h)(ha)(hb)
    case 1n+q Con{False{}, ra} Con{False{}, rb}:
      h => ha => hb => Bits.lt_sides(q, ra, rb)(h)(ha)(hb)
    case 1n+q Con{True{}, ra} Con{False{}, rb}:
      h => ha => hb => Empty.absurd(
        {Crits.Bits.lt(True{} <> ra, False{} <> rb) == True{}: Bool},
        Shared.Bool.false_ne_true(h)
      )
    case 1n+q Con{False{}, ra} Con{True{}, rb}:
      h => ha => hb => {==}

# bits a that end at n come before bits b that agree with them before n and
# go on
def Bits.lt_ended(
  n: Nat,
  a: List<&2, Bool>,
  b: List<&2, Bool>,
  -y: Bool
) -> {
  Crits.Bits.agree_n(n, a, b) == True{}: Bool
} -> {
  Crits.Bits.at(a, n) == None{}: Maybe<&2, Bool>
} -> {Crits.Bits.at(b, n) == Some{y}: Maybe<&2, Bool>} -> {Crits.Bits.lt(a, b) == True{}: Bool}:
  match n a b:
    case 0n Nil{} Con{z, rb}:
      h => ha => hb => {==}
    case 0n Nil{} Nil{}:
      h => ha => hb => Empty.absurd(
        {Crits.Bits.lt([], []) == True{}: Bool},
        Shared.Maybe.none_ne_some(Bool, y, hb)
      )
    case 0n Con{x, ra} b1:
      h => ha => hb => Empty.absurd(
        {Crits.Bits.lt(x <> ra, b1) == True{}: Bool},
        Crits.Crit.some_ne_none(Bool, x, ha)
      )
    case 1n+q Nil{} Nil{}:
      h => ha => hb => Empty.absurd(
        {Crits.Bits.lt([], []) == True{}: Bool},
        Shared.Maybe.none_ne_some(Bool, y, hb)
      )
    case 1n+q Nil{} Con{z, rb}:
      h => ha => hb => {==}
    case 1n+q Con{x, ra} Nil{}:
      h => ha => hb => Empty.absurd(
        {Crits.Bits.lt(x <> ra, []) == True{}: Bool},
        Shared.Maybe.none_ne_some(Bool, y, hb)
      )
    case 1n+q Con{True{}, ra} Con{True{}, rb}:
      h => ha => hb => Bits.lt_ended(q, ra, rb, y)(h)(ha)(hb)
    case 1n+q Con{False{}, ra} Con{False{}, rb}:
      h => ha => hb => Bits.lt_ended(q, ra, rb, y)(h)(ha)(hb)
    case 1n+q Con{True{}, ra} Con{False{}, rb}:
      h => ha => hb => Empty.absurd(
        {Crits.Bits.lt(True{} <> ra, False{} <> rb) == True{}: Bool},
        Shared.Bool.false_ne_true(h)
      )
    case 1n+q Con{False{}, ra} Con{True{}, rb}:
      h => ha => hb => {==}

# Laws of the order of keys
# -------------------------

# no key comes before itself
def Key.lt_ne(
  +a: List<&2, U32>,
  +b: List<&2, U32>
) -> {Key.lt(a, b) == True{}: Bool} -> {Crits.Key.is_eq(a, b) == False{}: Bool}:
  x => Crits.Crit.false_of(Crits.Key.is_eq(a, b))(x1 => Shared.Bool.true_ne_false((
        %x: {_ == False{}: Bool}
        %Crits.Key.is_eq_sound(a, b)(x1): {Crits.Bits.lt(Crits.Key.bits(a), Crits.Key.bits(_)) == False{}: Bool}
        Crits.Bits.lt_self(Crits.Key.bits(a)))))

# a key that comes before another does not come after it
def Key.lt_asym(
  a: List<&2, U32>,
  b: List<&2, U32>
) -> {Key.lt(a, b) == True{}: Bool} -> {Key.lt(b, a) == False{}: Bool}:
  h => Bits.lt_asym(Crits.Key.bits(a), Crits.Key.bits(b))(h)

# the order of keys is transitive
def Key.lt_trans(
  a: List<&2, U32>,
  b: List<&2, U32>,
  c: List<&2, U32>
) -> {
  Key.lt(a, b) == True{}: Bool
} -> {Key.lt(b, c) == True{}: Bool} -> {Key.lt(a, c) == True{}: Bool}:
  h1 => h2 => Bits.lt_trans(Crits.Key.bits(a), Crits.Key.bits(b), Crits.Key.bits(c))(h1)(h2)

# keys with the same bits are the same
def Key.bits_inj(
  +a: List<&2, U32>,
  +b: List<&2, U32>
) -> {Crits.Key.bits(a) == Crits.Key.bits(b): List<&2, Bool>} -> {a == b: List<&2, U32>}:
  h => Crits.Key.diff_none(
    a,
    b
  )(
    Equal.trans(
      Maybe<&2, Nat>,
      Crits.Key.diff(a, b),
      Crits.Bits.diff(Crits.Key.bits(a), Crits.Key.bits(b)),
      None{},
      Crits.Key.diff_bits(a, b),
      (
        %h: {Crits.Bits.diff(Crits.Key.bits(a), _) == None{}: Maybe<&2, Nat>}
        Crits.Bits.diff_self(Crits.Key.bits(a)))
    )
  )

# of two keys that differ, one comes before the other
def Key.lt_total(
  +a: List<&2, U32>,
  +b: List<&2, U32>
) -> {
  Key.lt(a, b) == False{}: Bool
} -> {Crits.Key.is_eq(b, a) == False{}: Bool} -> {Key.lt(b, a) == True{}: Bool}:
  hn => he => Bool.by(
    x => {x == True{}: Bool},
    Key.lt(b, a),
    t => {==},
    f => Empty.absurd(
      {False{} == True{}: Bool},
      Shared.Bool.false_ne_true(
        Equal.trans(
          Bool,
          False{},
          Crits.Key.is_eq(b, a),
          True{},
          Equal.sym(Bool, Crits.Key.is_eq(b, a), False{}, he),
          (
            %Key.bits_inj(a, b)(Bits.lt_none(Crits.Key.bits(a), Crits.Key.bits(b))(hn)(f)): {Crits.Key.is_eq(_, a) == True{}: Bool}
            Crits.Key.is_eq_refl(a))
        )
      )
    )
  )

# a key on the zero side of a fork comes before a key on its one side
def Key.lt_sides(
  +r: List<&2, U32>,
  +p: Nat,
  +k: List<&2, U32>,
  +q: List<&2, U32>
) -> {
  Crits.Place.has(Crits.Place{r, p, False{}}, k) == True{}: Bool
} -> {
  Crits.Place.has(Crits.Place{r, p, True{}}, q) == True{}: Bool
} -> {Key.lt(k, q) == True{}: Bool}:
  +hk => +hq => Bits.lt_sides(
    p,
    Crits.Key.bits(k),
    Crits.Key.bits(q)
  )(
    Equal.trans(
      Bool,
      Crits.Bits.agree_n(p, Crits.Key.bits(k), Crits.Key.bits(q)),
      Crits.Key.agree(k, q, p),
      True{},
      Equal.sym(
        Bool,
        Crits.Key.agree(k, q, p),
        Crits.Bits.agree_n(p, Crits.Key.bits(k), Crits.Key.bits(q)),
        Crits.Key.agree_bits(k, q, p)
      ),
      Crits.Key.agree_join(
        k,
        q,
        r,
        p
      )(Crits.Place.has_agree(r, p, False{}, k)(hk))(Crits.Place.has_agree(r, p, True{}, q)(hq))
    )
  )(
    Crits.Crit.at_of_side(k, p, Some{False{}})(Crits.Place.has_side(r, p, False{}, k)(hk))
  )(Crits.Crit.at_of_side(q, p, Some{True{}})(Crits.Place.has_side(r, p, True{}, q)(hq)))

# the key that ends at the bit of a fork comes before a key on a side of it
def Key.lt_ended(
  +r: List<&2, U32>,
  +p: Nat,
  +b: Bool,
  +q: List<&2, U32>
) -> {
  Nat.is_eq(List.length(&2, Bool, Crits.Key.bits(r)), p) == True{}: Bool
} -> {Crits.Place.has(Crits.Place{r, p, b}, q) == True{}: Bool} -> {Key.lt(r, q) == True{}: Bool}:
  hl => +hq => Bits.lt_ended(
    p,
    Crits.Key.bits(r),
    Crits.Key.bits(q),
    b
  )(
    Equal.trans(
      Bool,
      Crits.Bits.agree_n(p, Crits.Key.bits(r), Crits.Key.bits(q)),
      Crits.Key.agree(r, q, p),
      True{},
      Equal.sym(
        Bool,
        Crits.Key.agree(r, q, p),
        Crits.Bits.agree_n(p, Crits.Key.bits(r), Crits.Key.bits(q)),
        Crits.Key.agree_bits(r, q, p)
      ),
      Crits.Key.agree_sym(q, r, p)(Crits.Place.has_agree(r, p, b, q)(hq))
    )
  )(
    Crits.Crit.at_of_side(r, p, None{})(Crits.Crit.side_len(r, p)(hl))
  )(Crits.Crit.at_of_side(q, p, Some{b})(Crits.Place.has_side(r, p, b, q)(hq)))

# Laws of sorted entries
# ----------------------

# each key of xs comes before each key of ys
def Binds.cross(~V: Data, xs: List<&2, Crits.Bind<V>>, +ys: List<&2, Crits.Bind<V>>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{Crits.Bind{k, v}, r}:
      Bool.and(Binds.all(~V, ~List<&2, U32>, ~Key.lt, ys, k), Binds.cross(~V, r, ys))

# what holds of the keys of two lists of entries holds of the keys of both
def Binds.all_append(
  ~V: Data,
  ~G: Data,
  ~p: G -> List<&2, U32> -> Bool,
  xs: List<&2, Crits.Bind<V>>,
  +ys: List<&2, Crits.Bind<V>>,
  +g: G
) -> {
  Binds.all(~V, ~G, ~p, xs, g) == True{}: Bool
} -> {
  Binds.all(~V, ~G, ~p, ys, g) == True{}: Bool
} -> {Binds.all(~V, ~G, ~p, List.append(&2, Crits.Bind<V>, xs, ys), g) == True{}: Bool}:
  match xs:
    case Nil{}:
      h1 => h2 => h2
    case Con{Crits.Bind{+k, v}, +r}:
      +h1 => h2 => Crits.Crit.and_true(
        p(g)(k),
        Binds.all(~V, ~G, ~p, List.append(&2, Crits.Bind<V>, r, ys), g)
      )(
        Shared.Bool.and_true_left(p(g)(k), Binds.all(~V, ~G, ~p, r, g))(h1)
      )(
        Binds.all_append(
          ~V,
          ~G,
          ~p,
          r,
          ys,
          g
        )(Shared.Bool.and_true_right(p(g)(k), Binds.all(~V, ~G, ~p, r, g))(h1))(h2)
      )

# a key before a key that comes before each key of es comes before each
def Binds.all_lt(
  ~V: Data,
  +g: List<&2, U32>,
  +k: List<&2, U32>,
  es: List<&2, Crits.Bind<V>>
) -> {
  Key.lt(g, k) == True{}: Bool
} -> {
  Binds.all(~V, ~List<&2, U32>, ~Key.lt, es, k) == True{}: Bool
} -> {Binds.all(~V, ~List<&2, U32>, ~Key.lt, es, g) == True{}: Bool}:
  match es:
    case Nil{}:
      h1 => h2 => {==}
    case Con{Crits.Bind{+k2, v}, +r}:
      +h1 => +h2 => Crits.Crit.and_true(
        Key.lt(g, k2),
        Binds.all(~V, ~List<&2, U32>, ~Key.lt, r, g)
      )(
        Key.lt_trans(
          g,
          k,
          k2
        )(
          h1
        )(
          Shared.Bool.and_true_left(Key.lt(k, k2), Binds.all(~V, ~List<&2, U32>, ~Key.lt, r, k))(h2)
        )
      )(
        Binds.all_lt(
          ~V,
          g,
          k,
          r
        )(
          h1
        )(
          Shared.Bool.and_true_right(
            Key.lt(k, k2),
            Binds.all(~V, ~List<&2, U32>, ~Key.lt, r, k)
          )(h2)
        )
      )

# two sorted lists, each key of the first before each of the second, are
# sorted one after the other
def Binds.sorted_append(
  ~V: Data,
  xs: List<&2, Crits.Bind<V>>,
  +ys: List<&2, Crits.Bind<V>>
) -> {
  Binds.sorted(~V, xs) == True{}: Bool
} -> {
  Binds.sorted(~V, ys) == True{}: Bool
} -> {
  Binds.cross(~V, xs, ys) == True{}: Bool
} -> {Binds.sorted(~V, List.append(&2, Crits.Bind<V>, xs, ys)) == True{}: Bool}:
  match xs:
    case Nil{}:
      h1 => h2 => h3 => h2
    case Con{Crits.Bind{+k, v}, +r}:
      +h1 => h2 => +h3 => Crits.Crit.and_true(
        Binds.all(~V, ~List<&2, U32>, ~Key.lt, List.append(&2, Crits.Bind<V>, r, ys), k),
        Binds.sorted(~V, List.append(&2, Crits.Bind<V>, r, ys))
      )(
        Binds.all_append(
          ~V,
          ~List<&2, U32>,
          ~Key.lt,
          r,
          ys,
          k
        )(
          Shared.Bool.and_true_left(
            Binds.all(~V, ~List<&2, U32>, ~Key.lt, r, k),
            Binds.sorted(~V, r)
          )(h1)
        )(
          Shared.Bool.and_true_left(
            Binds.all(~V, ~List<&2, U32>, ~Key.lt, ys, k),
            Binds.cross(~V, r, ys)
          )(h3)
        )
      )(
        Binds.sorted_append(
          ~V,
          r,
          ys
        )(
          Shared.Bool.and_true_right(
            Binds.all(~V, ~List<&2, U32>, ~Key.lt, r, k),
            Binds.sorted(~V, r)
          )(h1)
        )(
          h2
        )(
          Shared.Bool.and_true_right(
            Binds.all(~V, ~List<&2, U32>, ~Key.lt, ys, k),
            Binds.cross(~V, r, ys)
          )(h3)
        )
      )

# a key on the zero side of a fork comes before each key on its one side
def Binds.all_sides(
  ~V: Data,
  +r: List<&2, U32>,
  +p: Nat,
  +k: List<&2, U32>,
  es: List<&2, Crits.Bind<V>>
) -> {
  Crits.Place.has(Crits.Place{r, p, False{}}, k) == True{}: Bool
} -> {
  Binds.all(~V, ~Crits.Place, ~Crits.Place.has, es, Crits.Place{r, p, True{}}) == True{}: Bool
} -> {Binds.all(~V, ~List<&2, U32>, ~Key.lt, es, k) == True{}: Bool}:
  match es:
    case Nil{}:
      hk => h => {==}
    case Con{Crits.Bind{+q, v}, +rest}:
      +hk => +h => Crits.Crit.and_true(
        Key.lt(k, q),
        Binds.all(~V, ~List<&2, U32>, ~Key.lt, rest, k)
      )(
        Key.lt_sides(
          r,
          p,
          k,
          q
        )(
          hk
        )(
          Shared.Bool.and_true_left(
            Crits.Place.has(Crits.Place{r, p, True{}}, q),
            Binds.all(~V, ~Crits.Place, ~Crits.Place.has, rest, Crits.Place{r, p, True{}})
          )(h)
        )
      )(
        Binds.all_sides(
          ~V,
          r,
          p,
          k,
          rest
        )(
          hk
        )(
          Shared.Bool.and_true_right(
            Crits.Place.has(Crits.Place{r, p, True{}}, q),
            Binds.all(~V, ~Crits.Place, ~Crits.Place.has, rest, Crits.Place{r, p, True{}})
          )(h)
        )
      )

# the key that ends at the bit of a fork comes before each key on a side
def Binds.all_ended(
  ~V: Data,
  +r: List<&2, U32>,
  +p: Nat,
  +b: Bool,
  es: List<&2, Crits.Bind<V>>
) -> {
  Nat.is_eq(List.length(&2, Bool, Crits.Key.bits(r)), p) == True{}: Bool
} -> {
  Binds.all(~V, ~Crits.Place, ~Crits.Place.has, es, Crits.Place{r, p, b}) == True{}: Bool
} -> {Binds.all(~V, ~List<&2, U32>, ~Key.lt, es, r) == True{}: Bool}:
  match es:
    case Nil{}:
      hl => h => {==}
    case Con{Crits.Bind{+q, v}, +rest}:
      +hl => +h => Crits.Crit.and_true(
        Key.lt(r, q),
        Binds.all(~V, ~List<&2, U32>, ~Key.lt, rest, r)
      )(
        Key.lt_ended(
          r,
          p,
          b,
          q
        )(
          hl
        )(
          Shared.Bool.and_true_left(
            Crits.Place.has(Crits.Place{r, p, b}, q),
            Binds.all(~V, ~Crits.Place, ~Crits.Place.has, rest, Crits.Place{r, p, b})
          )(h)
        )
      )(
        Binds.all_ended(
          ~V,
          r,
          p,
          b,
          rest
        )(
          hl
        )(
          Shared.Bool.and_true_right(
            Crits.Place.has(Crits.Place{r, p, b}, q),
            Binds.all(~V, ~Crits.Place, ~Crits.Place.has, rest, Crits.Place{r, p, b})
          )(h)
        )
      )

# each key on the zero side of a fork comes before each key on its one side
def Binds.cross_sides(
  ~V: Data,
  +r: List<&2, U32>,
  +p: Nat,
  xs: List<&2, Crits.Bind<V>>,
  +ys: List<&2, Crits.Bind<V>>
) -> {
  Binds.all(~V, ~Crits.Place, ~Crits.Place.has, xs, Crits.Place{r, p, False{}}) == True{}: Bool
} -> {
  Binds.all(~V, ~Crits.Place, ~Crits.Place.has, ys, Crits.Place{r, p, True{}}) == True{}: Bool
} -> {Binds.cross(~V, xs, ys) == True{}: Bool}:
  match xs:
    case Nil{}:
      h1 => h2 => {==}
    case Con{Crits.Bind{+k, v}, +rest}:
      +h1 => +h2 => Crits.Crit.and_true(
        Binds.all(~V, ~List<&2, U32>, ~Key.lt, ys, k),
        Binds.cross(~V, rest, ys)
      )(
        Binds.all_sides(
          ~V,
          r,
          p,
          k,
          ys
        )(
          Shared.Bool.and_true_left(
            Crits.Place.has(Crits.Place{r, p, False{}}, k),
            Binds.all(~V, ~Crits.Place, ~Crits.Place.has, rest, Crits.Place{r, p, False{}})
          )(h1)
        )(h2)
      )(
        Binds.cross_sides(
          ~V,
          r,
          p,
          rest,
          ys
        )(
          Shared.Bool.and_true_right(
            Crits.Place.has(Crits.Place{r, p, False{}}, k),
            Binds.all(~V, ~Crits.Place, ~Crits.Place.has, rest, Crits.Place{r, p, False{}})
          )(h1)
        )(h2)
      )

# Crit.entries_go at a fork: the entries x of its sides, then rest, from what
# holds of each side (y: those of the one side, then rest; w: those of both)
def Crit.entries_go.fork(
  -A: Data,
  -x: List<&2, A>,
  -y: List<&2, A>,
  -w: List<&2, A>,
  ez: List<&2, A>,
  eo: List<&2, A>,
  rest: List<&2, A>
) -> {
  x == List.append(&2, A, ez, y): List<&2, A>
} -> {
  y == List.append(&2, A, eo, rest): List<&2, A>
} -> {
  w == List.append(&2, A, ez, eo): List<&2, A>
} -> {x == List.append(&2, A, w, rest): List<&2, A>}:
  e1 => e2 => e3 =>
    %Equal.sym(
      List<&2, A>,
      w,
      List.append(&2, A, ez, eo),
      e3
    ): {x == List.append(&2, A, _, rest): List<&2, A>}
    %Equal.sym(
      List<&2, A>,
      x,
      List.append(&2, A, ez, y),
      e1
    ): {_ == List.append(&2, A, List.append(&2, A, ez, eo), rest): List<&2, A>}
    %Equal.sym(
      List<&2, A>,
      y,
      List.append(&2, A, eo, rest),
      e2
    ): {
      List.append(&2, A, ez, _) == List.append(&2, A, List.append(&2, A, ez, eo), rest): List<&2, A>
    }
    Equal.sym(
      List<&2, A>,
      List.append(&2, A, List.append(&2, A, ez, eo), rest),
      List.append(&2, A, ez, List.append(&2, A, eo, rest)),
      Shared.List.append_assoc(A, ez, eo, rest)
    )

# the entries of a map, then more, are its entries, then those
def Crit.entries_go(
  -V: Data,
  m: Crits.Crit<V>,
  +rest: List<&2, Crits.Bind<V>>
) -> {
  Crits.Crit.entries.go(
    V,
    m,
    rest
  )
    == List.append(&2, Crits.Bind<V>, Crits.Crit.entries(V, m), rest): List<&2, Crits.Bind<V>>
}:
  match m:
    case Crits.Crit.Tip{}:
      {==}
    case Crits.Crit.Leaf{k, v}:
      {==}
    case Crits.Crit.Fork{r, p, None{}, +z, +o}:
      Crit.entries_go.fork(
        Crits.Bind<V>,
        Crits.Crit.entries.go(V, z, Crits.Crit.entries.go(V, o, rest)),
        Crits.Crit.entries.go(V, o, rest),
        Crits.Crit.entries.go(V, z, Crits.Crit.entries(V, o)),
        Crits.Crit.entries(V, z),
        Crits.Crit.entries(V, o),
        rest
      )(
        Crit.entries_go(V, z, Crits.Crit.entries.go(V, o, rest))
      )(Crit.entries_go(V, o, rest))(Crit.entries_go(V, z, Crits.Crit.entries(V, o)))
    case Crits.Crit.Fork{+r, p, Some{+v}, +z, +o}:
      Equal.cong(
        List<&2, Crits.Bind<V>>,
        List<&2, Crits.Bind<V>>,
        t => Crits.Bind{r, v} <> t,
        Crits.Crit.entries.go(V, z, Crits.Crit.entries.go(V, o, rest)),
        List.append(&2, Crits.Bind<V>, Crits.Crit.entries.go(V, z, Crits.Crit.entries(V, o)), rest),
        Crit.entries_go.fork(
          Crits.Bind<V>,
          Crits.Crit.entries.go(V, z, Crits.Crit.entries.go(V, o, rest)),
          Crits.Crit.entries.go(V, o, rest),
          Crits.Crit.entries.go(V, z, Crits.Crit.entries(V, o)),
          Crits.Crit.entries(V, z),
          Crits.Crit.entries(V, o),
          rest
        )(
          Crit.entries_go(V, z, Crits.Crit.entries.go(V, o, rest))
        )(Crit.entries_go(V, o, rest))(Crit.entries_go(V, z, Crits.Crit.entries(V, o)))
      )

# what holds of each key of a map, and of each key of rest, holds of each key
# of its entries, then rest
def Crit.all_entries.go(
  ~V: Data,
  ~G: Data,
  ~p: G -> List<&2, U32> -> Bool,
  m: Crits.Crit<V>,
  +rest: List<&2, Crits.Bind<V>>,
  +g: G
) -> {
  Crits.Crit.all(~V, ~G, ~p, m, g) == True{}: Bool
} -> {
  Binds.all(~V, ~G, ~p, rest, g) == True{}: Bool
} -> {Binds.all(~V, ~G, ~p, Crits.Crit.entries.go(V, m, rest), g) == True{}: Bool}:
  match m:
    case Crits.Crit.Tip{}:
      h => hr => hr
    case Crits.Crit.Leaf{+k, v}:
      h => hr => Crits.Crit.and_true(p(g)(k), Binds.all(~V, ~G, ~p, rest, g))(h)(hr)
    case Crits.Crit.Fork{+r, +ps, None{}, +z, +o}:
      +h => hr => Crit.all_entries.go(
        ~V,
        ~G,
        ~p,
        z,
        Crits.Crit.entries.go(V, o, rest),
        g
      )(
        Crits.Crit.all.z(~V, ~G, ~p, r, ps, None{}, z, o, g)(h)
      )(
        Crit.all_entries.go(
          ~V,
          ~G,
          ~p,
          o,
          rest,
          g
        )(Crits.Crit.all.o(~V, ~G, ~p, r, ps, None{}, z, o, g)(h))(hr)
      )
    case Crits.Crit.Fork{+r, +ps, Some{+v}, +z, +o}:
      +h => hr => Crits.Crit.and_true(
        p(g)(r),
        Binds.all(~V, ~G, ~p, Crits.Crit.entries.go(V, z, Crits.Crit.entries.go(V, o, rest)), g)
      )(
        Crits.Crit.all.hit(~V, ~G, ~p, r, ps, Some{v}, z, o, g)(h)
      )(
        Crit.all_entries.go(
          ~V,
          ~G,
          ~p,
          z,
          Crits.Crit.entries.go(V, o, rest),
          g
        )(
          Crits.Crit.all.z(~V, ~G, ~p, r, ps, Some{v}, z, o, g)(h)
        )(
          Crit.all_entries.go(
            ~V,
            ~G,
            ~p,
            o,
            rest,
            g
          )(Crits.Crit.all.o(~V, ~G, ~p, r, ps, Some{v}, z, o, g)(h))(hr)
        )
      )

# what holds of each key of a map holds of each key of its entries
def Crit.all_entries(
  ~V: Data,
  ~G: Data,
  ~p: G -> List<&2, U32> -> Bool,
  m: Crits.Crit<V>,
  +g: G
) -> {
  Crits.Crit.all(~V, ~G, ~p, m, g) == True{}: Bool
} -> {Binds.all(~V, ~G, ~p, Crits.Crit.entries(V, m), g) == True{}: Bool}:
  h => Crit.all_entries.go(~V, ~G, ~p, m, [], g)(h)({==})

# Crit.entries_sorted at a well formed fork: the entries of its sides, one
# side after the other, are sorted when those of each side are
def Crit.entries_sorted.sides(
  ~V: Data,
  +r: List<&2, U32>,
  +p: Nat,
  +e: Maybe<&2, V>,
  +z: Crits.Crit<V>,
  +o: Crits.Crit<V>,
  +lo: Nat
) -> {
  Crits.Crit.wf(~V, Crits.Crit.Fork{r, p, e, z, o}, lo) == True{}: Bool
} -> {
  Binds.sorted(~V, Crits.Crit.entries(V, z)) == True{}: Bool
} -> {
  Binds.sorted(~V, Crits.Crit.entries(V, o)) == True{}: Bool
} -> {Binds.sorted(~V, Crits.Crit.entries.go(V, z, Crits.Crit.entries(V, o))) == True{}: Bool}:
  +h => sz => so =>
    %Equal.sym(
      List<&2, Crits.Bind<V>>,
      Crits.Crit.entries.go(V, z, Crits.Crit.entries(V, o)),
      List.append(&2, Crits.Bind<V>, Crits.Crit.entries(V, z), Crits.Crit.entries(V, o)),
      Crit.entries_go(V, z, Crits.Crit.entries(V, o))
    ): {Binds.sorted(~V, _) == True{}: Bool}
    Binds.sorted_append(
      ~V,
      Crits.Crit.entries(V, z),
      Crits.Crit.entries(V, o)
    )(
      sz
    )(
      so
    )(
      Binds.cross_sides(
        ~V,
        r,
        p,
        Crits.Crit.entries(V, z),
        Crits.Crit.entries(V, o)
      )(
        Crit.all_entries(
          ~V,
          ~Crits.Place,
          ~Crits.Place.has,
          z,
          Crits.Place{r, p, False{}}
        )(Crits.Crit.wf.all_z(~V, r, p, e, z, o, lo)(h))
      )(
        Crit.all_entries(
          ~V,
          ~Crits.Place,
          ~Crits.Place.has,
          o,
          Crits.Place{r, p, True{}}
        )(Crits.Crit.wf.all_o(~V, r, p, e, z, o, lo)(h))
      )
    )

# Crit.entries_sorted at a well formed fork with an end: the key that ends
# there comes before each key of its sides
def Crit.entries_sorted.ended(
  ~V: Data,
  +r: List<&2, U32>,
  +p: Nat,
  +v: V,
  +z: Crits.Crit<V>,
  +o: Crits.Crit<V>,
  +lo: Nat
) -> {
  Crits.Crit.wf(~V, Crits.Crit.Fork{r, p, Some{v}, z, o}, lo) == True{}: Bool
} -> {
  Binds.all(
    ~V,
    ~List<&2, U32>,
    ~Key.lt,
    Crits.Crit.entries.go(V, z, Crits.Crit.entries(V, o)),
    r
  )
    == True{}: Bool
}:
  +h =>
    %Equal.sym(
      List<&2, Crits.Bind<V>>,
      Crits.Crit.entries.go(V, z, Crits.Crit.entries(V, o)),
      List.append(&2, Crits.Bind<V>, Crits.Crit.entries(V, z), Crits.Crit.entries(V, o)),
      Crit.entries_go(V, z, Crits.Crit.entries(V, o))
    ): {Binds.all(~V, ~List<&2, U32>, ~Key.lt, _, r) == True{}: Bool}
    Binds.all_append(
      ~V,
      ~List<&2, U32>,
      ~Key.lt,
      Crits.Crit.entries(V, z),
      Crits.Crit.entries(V, o),
      r
    )(
      Binds.all_ended(
        ~V,
        r,
        p,
        False{},
        Crits.Crit.entries(V, z)
      )(
        Crits.Crit.wf.rep_ok(~V, r, p, Some{v}, z, o, lo)(h)
      )(
        Crit.all_entries(
          ~V,
          ~Crits.Place,
          ~Crits.Place.has,
          z,
          Crits.Place{r, p, False{}}
        )(Crits.Crit.wf.all_z(~V, r, p, Some{v}, z, o, lo)(h))
      )
    )(
      Binds.all_ended(
        ~V,
        r,
        p,
        True{},
        Crits.Crit.entries(V, o)
      )(
        Crits.Crit.wf.rep_ok(~V, r, p, Some{v}, z, o, lo)(h)
      )(
        Crit.all_entries(
          ~V,
          ~Crits.Place,
          ~Crits.Place.has,
          o,
          Crits.Place{r, p, True{}}
        )(Crits.Crit.wf.all_o(~V, r, p, Some{v}, z, o, lo)(h))
      )
    )

# Crit.entries_sorted, below a fork at a bit before lo
def Crit.entries_sorted.go(
  ~V: Data,
  m: Crits.Crit<V>,
  +lo: Nat
) -> {
  Crits.Crit.wf(~V, m, lo) == True{}: Bool
} -> {Binds.sorted(~V, Crits.Crit.entries(V, m)) == True{}: Bool}:
  match m:
    case Crits.Crit.Tip{}:
      h => {==}
    case Crits.Crit.Leaf{k, v}:
      h => {==}
    case Crits.Crit.Fork{+r, +p, None{}, +z, +o}:
      +h => Crit.entries_sorted.sides(
        ~V,
        r,
        p,
        None{},
        z,
        o,
        lo
      )(
        h
      )(
        Crit.entries_sorted.go(~V, z, 1n+p)(Crits.Crit.wf.wf_z(~V, r, p, None{}, z, o, lo)(h))
      )(Crit.entries_sorted.go(~V, o, 1n+p)(Crits.Crit.wf.wf_o(~V, r, p, None{}, z, o, lo)(h)))
    case Crits.Crit.Fork{+r, +p, Some{+v}, +z, +o}:
      +h => Crits.Crit.and_true(
        Binds.all(
          ~V,
          ~List<&2, U32>,
          ~Key.lt,
          Crits.Crit.entries.go(V, z, Crits.Crit.entries(V, o)),
          r
        ),
        Binds.sorted(~V, Crits.Crit.entries.go(V, z, Crits.Crit.entries(V, o)))
      )(
        Crit.entries_sorted.ended(~V, r, p, v, z, o, lo)(h)
      )(
        Crit.entries_sorted.sides(
          ~V,
          r,
          p,
          Some{v},
          z,
          o,
          lo
        )(
          h
        )(
          Crit.entries_sorted.go(~V, z, 1n+p)(Crits.Crit.wf.wf_z(~V, r, p, Some{v}, z, o, lo)(h))
        )(Crit.entries_sorted.go(~V, o, 1n+p)(Crits.Crit.wf.wf_o(~V, r, p, Some{v}, z, o, lo)(h)))
      )

# the entries of a well formed map are in the strict order of their keys
def Crit.entries_sorted(
  ~V: Data,
  m: Crits.Crit<V>
) -> {
  Crits.Crit.wf(~V, m, 0n) == True{}: Bool
} -> {Binds.sorted(~V, Crits.Crit.entries(V, m)) == True{}: Bool}:
  h => Crit.entries_sorted.go(~V, m, 0n)(h)

# Sorted entries are what they hold
# ---------------------------------

# the entries a and b hold the same under the key of each of the entries es:
# a proof of it is data
def Binds.Same(
  -V: Data,
  es: List<&2, Crits.Bind<V>>,
  +a: List<&2, Crits.Bind<V>>,
  +b: List<&2, Crits.Bind<V>>
) -> Data:
  match es:
    case Nil{}:
      Unit
    case Con{Crits.Bind{+k, v}, r}:
      Sigma<
        &2,
        &2,
        {Binds.get(V, a, k) == Binds.get(V, b, k): Maybe<&2, V>},
        _ => Binds.Same(V, r, a, b)>

# Binds.Same of a list with a head: the head
def Binds.Same.hd(
  -V: Data,
  -k: List<&2, U32>,
  -v: V,
  -r: List<&2, Crits.Bind<V>>,
  -a: List<&2, Crits.Bind<V>>,
  -b: List<&2, Crits.Bind<V>>,
  c: Binds.Same(V, Crits.Bind{k, v} <> r, a, b)
) -> {Binds.get(V, a, k) == Binds.get(V, b, k): Maybe<&2, V>}:
  (h, t) = c
  h

# Binds.Same of a list with a head: the rest
def Binds.Same.tl(
  -V: Data,
  -k: List<&2, U32>,
  -v: V,
  -r: List<&2, Crits.Bind<V>>,
  -a: List<&2, Crits.Bind<V>>,
  -b: List<&2, Crits.Bind<V>>,
  c: Binds.Same(V, Crits.Bind{k, v} <> r, a, b)
) -> Binds.Same(V, r, a, b):
  (h, t) = c
  t

# a key that sorted entries hold after the key k comes after k
def Binds.get_lt(
  ~V: Data,
  r: List<&2, Crits.Bind<V>>,
  +k: List<&2, U32>,
  +q: List<&2, U32>,
  -w: V
) -> {
  Binds.all(~V, ~List<&2, U32>, ~Key.lt, r, k) == True{}: Bool
} -> {Binds.get(V, r, q) == Some{w}: Maybe<&2, V>} -> {Key.lt(k, q) == True{}: Bool}:
  match r:
    case Nil{}:
      ha => hg => Empty.absurd({Key.lt(k, q) == True{}: Bool}, Shared.Maybe.none_ne_some(V, w, hg))
    case Con{Crits.Bind{+k2, +v2}, +rest}:
      +ha => hg => Bool.by(
        c => {Bool.pick(Maybe<&2, V>, c, Some{v2}, Binds.get(V, rest, q)) == Some{w}: Maybe<&2, V>} -> {Key.lt(k, q) == True{}: Bool},
        Crits.Key.is_eq(k2, q),
        t => hg2 =>
          %Crits.Key.is_eq_sound(k2, q)(t): {Key.lt(k, _) == True{}: Bool}
          Shared.Bool.and_true_left(Key.lt(k, k2), Binds.all(~V, ~List<&2, U32>, ~Key.lt, rest, k))(ha),
        f => hg2 => Binds.get_lt(~V, rest, k, q, w)(Shared.Bool.and_true_right(Key.lt(k, k2), Binds.all(~V, ~List<&2, U32>, ~Key.lt, rest, k))(ha))(hg2))(hg)

# entries that hold the same under keys after k, once an entry of k is put
# before each, hold the same under them
def Binds.same_rest(
  ~V: Data,
  +k: List<&2, U32>,
  +v1: V,
  +v2: V,
  es: List<&2, Crits.Bind<V>>,
  +r1: List<&2, Crits.Bind<V>>,
  +r2: List<&2, Crits.Bind<V>>
) -> {
  Binds.all(~V, ~List<&2, U32>, ~Key.lt, es, k) == True{}: Bool
} -> Binds.Same(
  V,
  es,
  Crits.Bind{k, v1} <> r1,
  Crits.Bind{k, v2} <> r2
) -> Binds.Same(V, es, r1, r2):
  match es:
    case Nil{}:
      ha => c => Unit{}
    case Con{Crits.Bind{+q, +w}, +rest}:
      +ha => +c => ((
          %Key.lt_ne(k, q)(Shared.Bool.and_true_left(Key.lt(k, q), Binds.all(~V, ~List<&2, U32>, ~Key.lt, rest, k))(ha)): {Bool.pick(Maybe<&2, V>, _, Some{v1}, Binds.get(V, r1, q)) == Bool.pick(Maybe<&2, V>, _, Some{v2}, Binds.get(V, r2, q)): Maybe<&2, V>}
          Binds.Same.hd(V, q, w, rest, Crits.Bind{k, v1} <> r1, Crits.Bind{k, v2} <> r2, c)), Binds.same_rest(~V, k, v1, v2, rest, r1, r2)(Shared.Bool.and_true_right(Key.lt(k, q), Binds.all(~V, ~List<&2, U32>, ~Key.lt, rest, k))(ha))(Binds.Same.tl(V, q, w, rest, Crits.Bind{k, v1} <> r1, Crits.Bind{k, v2} <> r2, c)))

# what Binds.ext asks of the entries a and b
def Binds.Ext(~V: Data, +a: List<&2, Crits.Bind<V>>, +b: List<&2, Crits.Bind<V>>) -> Type:
  {
    Binds.sorted(~V, a) == True{}: Bool
  } -> {
    Binds.sorted(~V, b) == True{}: Bool
  } -> Binds.Same(V, a, a, b) -> Binds.Same(V, b, a, b) -> {a == b: List<&2, Crits.Bind<V>>}

# Binds.ext at two lists whose first entries have the same key, from Binds.ext
# of the entries after them
def Binds.ext.same(
  ~V: Data,
  +k: List<&2, U32>,
  +v1: V,
  +v2: V,
  +r1: List<&2, Crits.Bind<V>>,
  +r2: List<&2, Crits.Bind<V>>,
  ih: Binds.Ext(~V, r1, r2)
) -> Binds.Ext(~V, Crits.Bind{k, v1} <> r1, Crits.Bind{k, v2} <> r2):
  +sa => +sb => +ca => cb =>
    %Shared.Maybe.some_inj(V, v1, v2, (
        %Crits.Key.is_eq_refl(k): {Bool.pick(Maybe<&2, V>, _, Some{v1}, Binds.get(V, r1, k)) == Bool.pick(Maybe<&2, V>, _, Some{v2}, Binds.get(V, r2, k)): Maybe<&2, V>}
        Binds.Same.hd(V, k, v1, r1, Crits.Bind{k, v1} <> r1, Crits.Bind{k, v2} <> r2, ca))): {Crits.Bind{k, v1} <> r1 == Crits.Bind{k, _} <> r2: List<&2, Crits.Bind<V>>}
    Equal.cong(
      List<&2, Crits.Bind<V>>,
      List<&2, Crits.Bind<V>>,
      t => Crits.Bind{k, v1} <> t,
      r1,
      r2,
      ih(
        Shared.Bool.and_true_right(
          Binds.all(~V, ~List<&2, U32>, ~Key.lt, r1, k),
          Binds.sorted(~V, r1)
        )(sa)
      )(
        Shared.Bool.and_true_right(
          Binds.all(~V, ~List<&2, U32>, ~Key.lt, r2, k),
          Binds.sorted(~V, r2)
        )(sb)
      )(
        Binds.same_rest(
          ~V,
          k,
          v1,
          v2,
          r1,
          r1,
          r2
        )(
          Shared.Bool.and_true_left(
            Binds.all(~V, ~List<&2, U32>, ~Key.lt, r1, k),
            Binds.sorted(~V, r1)
          )(sa)
        )(Binds.Same.tl(V, k, v1, r1, Crits.Bind{k, v1} <> r1, Crits.Bind{k, v2} <> r2, ca))
      )(
        Binds.same_rest(
          ~V,
          k,
          v1,
          v2,
          r2,
          r1,
          r2
        )(
          Shared.Bool.and_true_left(
            Binds.all(~V, ~List<&2, U32>, ~Key.lt, r2, k),
            Binds.sorted(~V, r2)
          )(sb)
        )(Binds.Same.tl(V, k, v2, r2, Crits.Bind{k, v1} <> r1, Crits.Bind{k, v2} <> r2, cb))
      )
    )

# Binds.ext at two lists whose first entries have keys that differ: there are
# no such sorted lists that hold the same
def Binds.ext.differ(
  ~V: Data,
  +k1: List<&2, U32>,
  +v1: V,
  +k2: List<&2, U32>,
  +v2: V,
  +r1: List<&2, Crits.Bind<V>>,
  +r2: List<&2, Crits.Bind<V>>
) -> {
  Crits.Key.is_eq(k2, k1) == False{}: Bool
} -> Binds.Ext(~V, Crits.Bind{k1, v1} <> r1, Crits.Bind{k2, v2} <> r2):
  +f => sa => sb => ca => cb => Empty.absurd(
    {Crits.Bind{k1, v1} <> r1 == Crits.Bind{k2, v2} <> r2: List<&2, Crits.Bind<V>>},
    Shared.Bool.true_ne_false(
      Equal.trans(
        Bool,
        True{},
        Key.lt(k2, k1),
        False{},
        Equal.sym(
          Bool,
          Key.lt(k2, k1),
          True{},
          Binds.get_lt(
            ~V,
            r2,
            k2,
            k1,
            v1
          )(
            Shared.Bool.and_true_left(
              Binds.all(~V, ~List<&2, U32>, ~Key.lt, r2, k2),
              Binds.sorted(~V, r2)
            )(sb)
          )(Equal.sym(Maybe<&2, V>, Some{v1}, Binds.get(V, r2, k1), (
                %f: {Bool.pick(Maybe<&2, V>, True{}, Some{v1}, Binds.get(V, r1, k1)) == Bool.pick(Maybe<&2, V>, _, Some{v2}, Binds.get(V, r2, k1)): Maybe<&2, V>}
                %Crits.Key.is_eq_refl(k1): {Bool.pick(Maybe<&2, V>, _, Some{v1}, Binds.get(V, r1, k1)) == Bool.pick(Maybe<&2, V>, Crits.Key.is_eq(k2, k1), Some{v2}, Binds.get(V, r2, k1)): Maybe<&2, V>}
                Binds.Same.hd(V, k1, v1, r1, Crits.Bind{k1, v1} <> r1, Crits.Bind{k2, v2} <> r2, ca))))
        ),
        Key.lt_asym(
          k1,
          k2
        )(
          Binds.get_lt(
            ~V,
            r1,
            k1,
            k2,
            v2
          )(
            Shared.Bool.and_true_left(
              Binds.all(~V, ~List<&2, U32>, ~Key.lt, r1, k1),
              Binds.sorted(~V, r1)
            )(sa)
          )((
              %Crits.Key.ne_sym(k2, k1)(f): {Bool.pick(Maybe<&2, V>, _, Some{v1}, Binds.get(V, r1, k2)) == Bool.pick(Maybe<&2, V>, True{}, Some{v2}, Binds.get(V, r2, k2)): Maybe<&2, V>}
              %Crits.Key.is_eq_refl(k2): {Bool.pick(Maybe<&2, V>, Crits.Key.is_eq(k1, k2), Some{v1}, Binds.get(V, r1, k2)) == Bool.pick(Maybe<&2, V>, _, Some{v2}, Binds.get(V, r2, k2)): Maybe<&2, V>}
              Binds.Same.hd(V, k2, v2, r2, Crits.Bind{k1, v1} <> r1, Crits.Bind{k2, v2} <> r2, cb)))
        )
      )
    )
  )

# Binds.ext at two lists with a first entry each, from Binds.ext of the
# entries after them
def Binds.ext.step(
  ~V: Data,
  +k1: List<&2, U32>,
  +v1: V,
  +k2: List<&2, U32>,
  +v2: V,
  +r1: List<&2, Crits.Bind<V>>,
  +r2: List<&2, Crits.Bind<V>>,
  ih: Binds.Ext(~V, r1, r2)
) -> Binds.Ext(~V, Crits.Bind{k1, v1} <> r1, Crits.Bind{k2, v2} <> r2):
  Crits.Crit.bool_split(
    Binds.Ext(~V, Crits.Bind{k1, v1} <> r1, Crits.Bind{k2, v2} <> r2),
    Crits.Key.is_eq(k2, k1)
  )(
    t =>
      %Equal.sym(List<&2, U32>, k2, k1, Crits.Key.is_eq_sound(k2, k1)(t)): Binds.Ext(~V, Crits.Bind{k1, v1} <> r1, Crits.Bind{_, v2} <> r2)
      Binds.ext.same(~V, k1, v1, v2, r1, r2, ih))(
    f => Binds.ext.differ(~V, k1, v1, k2, v2, r1, r2)(f)
  )

# two sorted lists of entries that hold the same under each of their keys are
# the same list
def Binds.ext(
  ~V: Data,
  a: List<&2, Crits.Bind<V>>,
  b: List<&2, Crits.Bind<V>>
) -> {
  Binds.sorted(~V, a) == True{}: Bool
} -> {
  Binds.sorted(~V, b) == True{}: Bool
} -> Binds.Same(V, a, a, b) -> Binds.Same(V, b, a, b) -> {a == b: List<&2, Crits.Bind<V>>}:
  match a b:
    case Nil{} Nil{}:
      sa => sb => ca => cb => {==}
    case Nil{} Con{Crits.Bind{+k2, +v2}, +r2}:
      sa => sb => ca => cb => Empty.absurd(
        {[] == Crits.Bind{k2, v2} <> r2: List<&2, Crits.Bind<V>>},
        Shared.Maybe.none_ne_some(V, v2, (
            %Crits.Key.is_eq_refl(k2): {None{} == Bool.pick(Maybe<&2, V>, _, Some{v2}, Binds.get(V, r2, k2)): Maybe<&2, V>}
            Binds.Same.hd(V, k2, v2, r2, [], Crits.Bind{k2, v2} <> r2, cb)))
      )
    case Con{Crits.Bind{+k1, +v1}, +r1} Nil{}:
      sa => sb => ca => cb => Empty.absurd(
        {Crits.Bind{k1, v1} <> r1 == []: List<&2, Crits.Bind<V>>},
        Crits.Crit.some_ne_none(V, v1, (
            %Crits.Key.is_eq_refl(k1): {Bool.pick(Maybe<&2, V>, _, Some{v1}, Binds.get(V, r1, k1)) == None{}: Maybe<&2, V>}
            Binds.Same.hd(V, k1, v1, r1, Crits.Bind{k1, v1} <> r1, [], ca)))
      )
    case Con{Crits.Bind{+k1, +v1}, +r1} Con{Crits.Bind{+k2, +v2}, +r2}:
      Binds.ext.step(~V, k1, v1, k2, v2, r1, r2, Binds.ext(~V, r1, r2))

# Laws of an insert
# -----------------

# a choice whose test is true is its first branch
def Bool.when_true_eq(
  -A: Type,
  b: Bool,
  -k: Unit -> A,
  -e: Unit -> A
) -> {b == True{}: Bool} -> {Shared.Bool.when(A, b, k, e) == k(Unit{}): A}:
  match b:
    case True{}:
      h => {==}
    case False{}:
      h => Empty.absurd({e(Unit{}) == k(Unit{}): A}, Shared.Bool.false_ne_true(h))

# an insert of a key before the first key puts its entry first
def Binds.insert_lt(
  -V: Data,
  +k1: List<&2, U32>,
  +v1: V,
  +r: List<&2, Crits.Bind<V>>,
  +k: List<&2, U32>,
  +v: V
) -> {
  Key.lt(k, k1) == True{}: Bool
} -> {
  Binds.insert(
    V,
    Crits.Bind{k1, v1} <> r,
    k,
    v
  )
    == Crits.Bind{k, v}
    <> Crits.Bind{k1, v1}
    <> r: List<&2, Crits.Bind<V>>
}:
  hl => Bool.when_true_eq(
    List<&2, Crits.Bind<V>>,
    Key.lt(k, k1),
    u => Crits.Bind{k, v} <> Crits.Bind{k1, v1} <> r,
    u => Shared.Bool.when(
      List<&2, Crits.Bind<V>>,
      Crits.Key.is_eq(k1, k),
      w => Crits.Bind{k1, v} <> r,
      w => Crits.Bind{k1, v1} <> Binds.insert(V, r, k, v)
    )
  )(hl)

# an insert of a key after the first key goes on after the first entry
def Binds.insert_gt(
  -V: Data,
  +k1: List<&2, U32>,
  +v1: V,
  +r: List<&2, Crits.Bind<V>>,
  +k: List<&2, U32>,
  +v: V
) -> {
  Key.lt(k, k1) == False{}: Bool
} -> {
  Crits.Key.is_eq(k1, k) == False{}: Bool
} -> {
  Binds.insert(
    V,
    Crits.Bind{k1, v1} <> r,
    k,
    v
  )
    == Crits.Bind{k1, v1}
    <> Binds.insert(V, r, k, v): List<&2, Crits.Bind<V>>
}:
  hn => he => Equal.trans(
    List<&2, Crits.Bind<V>>,
    Binds.insert(V, Crits.Bind{k1, v1} <> r, k, v),
    Shared.Bool.when(
      List<&2, Crits.Bind<V>>,
      Crits.Key.is_eq(k1, k),
      w => Crits.Bind{k1, v} <> r,
      w => Crits.Bind{k1, v1} <> Binds.insert(V, r, k, v)
    ),
    Crits.Bind{k1, v1} <> Binds.insert(V, r, k, v),
    Crits.Crit.when_false_eq(
      List<&2, Crits.Bind<V>>,
      Key.lt(k, k1),
      u => Crits.Bind{k, v} <> Crits.Bind{k1, v1} <> r,
      u => Shared.Bool.when(
        List<&2, Crits.Bind<V>>,
        Crits.Key.is_eq(k1, k),
        w => Crits.Bind{k1, v} <> r,
        w => Crits.Bind{k1, v1} <> Binds.insert(V, r, k, v)
      )
    )(hn),
    Crits.Crit.when_false_eq(
      List<&2, Crits.Bind<V>>,
      Crits.Key.is_eq(k1, k),
      w => Crits.Bind{k1, v} <> r,
      w => Crits.Bind{k1, v1} <> Binds.insert(V, r, k, v)
    )(he)
  )

# the three cases of an insert into entries with a first entry: what holds of
# each holds of the insert
def Binds.insert_cases(
  -V: Data,
  -P: List<&2, Crits.Bind<V>> -> Type,
  +k1: List<&2, U32>,
  +v1: V,
  +r: List<&2, Crits.Bind<V>>,
  +k: List<&2, U32>,
  +v: V,
  lt: {Key.lt(k, k1) == True{}: Bool} -> P(Crits.Bind{k, v} <> Crits.Bind{k1, v1} <> r),
  eq: {
    Key.lt(k, k1) == False{}: Bool
  } -> {Crits.Key.is_eq(k1, k) == True{}: Bool} -> P(Crits.Bind{k1, v} <> r),
  gt: {
    Key.lt(k, k1) == False{}: Bool
  } -> {
    Crits.Key.is_eq(k1, k) == False{}: Bool
  } -> P(Crits.Bind{k1, v1} <> Binds.insert(V, r, k, v))
) -> P(Binds.insert(V, Crits.Bind{k1, v1} <> r, k, v)):
  Shared.Bool.when_cases(
    List<&2, Crits.Bind<V>>,
    P,
    Key.lt(k, k1),
    u => Crits.Bind{k, v} <> Crits.Bind{k1, v1} <> r,
    u => Shared.Bool.when(
      List<&2, Crits.Bind<V>>,
      Crits.Key.is_eq(k1, k),
      w => Crits.Bind{k1, v} <> r,
      w => Crits.Bind{k1, v1} <> Binds.insert(V, r, k, v)
    ),
    hl => lt(hl),
    +hn => Shared.Bool.when_cases(
      List<&2, Crits.Bind<V>>,
      P,
      Crits.Key.is_eq(k1, k),
      w => Crits.Bind{k1, v} <> r,
      w => Crits.Bind{k1, v1} <> Binds.insert(V, r, k, v),
      he => eq(hn)(he),
      he => gt(hn)(he)
    )
  )

# a key comes before each key of an insert when it comes before each key
# there was and before the new key
def Binds.all_insert(
  ~V: Data,
  es: List<&2, Crits.Bind<V>>,
  +g: List<&2, U32>,
  +k: List<&2, U32>,
  +v: V
) -> {
  Binds.all(~V, ~List<&2, U32>, ~Key.lt, es, g) == True{}: Bool
} -> {
  Key.lt(g, k) == True{}: Bool
} -> {Binds.all(~V, ~List<&2, U32>, ~Key.lt, Binds.insert(V, es, k, v), g) == True{}: Bool}:
  match es:
    case Nil{}:
      h => hl => Crits.Crit.and_true(Key.lt(g, k), True{})(hl)({==})
    case Con{Crits.Bind{+k1, +v1}, +r}:
      +h => +hl => Binds.insert_cases(
        V,
        x => {Binds.all(~V, ~List<&2, U32>, ~Key.lt, x, g) == True{}: Bool},
        k1,
        v1,
        r,
        k,
        v,
        ht => Crits.Crit.and_true(
          Key.lt(g, k),
          Binds.all(~V, ~List<&2, U32>, ~Key.lt, Crits.Bind{k1, v1} <> r, g)
        )(hl)(h),
        hn => he => h,
        hn => he => Crits.Crit.and_true(
          Key.lt(g, k1),
          Binds.all(~V, ~List<&2, U32>, ~Key.lt, Binds.insert(V, r, k, v), g)
        )(
          Shared.Bool.and_true_left(Key.lt(g, k1), Binds.all(~V, ~List<&2, U32>, ~Key.lt, r, g))(h)
        )(
          Binds.all_insert(
            ~V,
            r,
            g,
            k,
            v
          )(
            Shared.Bool.and_true_right(
              Key.lt(g, k1),
              Binds.all(~V, ~List<&2, U32>, ~Key.lt, r, g)
            )(h)
          )(hl)
        )
      )

# an insert into sorted entries is sorted
def Binds.insert_sorted(
  ~V: Data,
  es: List<&2, Crits.Bind<V>>,
  +k: List<&2, U32>,
  +v: V
) -> {
  Binds.sorted(~V, es) == True{}: Bool
} -> {Binds.sorted(~V, Binds.insert(V, es, k, v)) == True{}: Bool}:
  match es:
    case Nil{}:
      h => {==}
    case Con{Crits.Bind{+k1, +v1}, +r}:
      +h => Binds.insert_cases(
        V,
        x => {Binds.sorted(~V, x) == True{}: Bool},
        k1,
        v1,
        r,
        k,
        v,
        +ht => Crits.Crit.and_true(
          Binds.all(~V, ~List<&2, U32>, ~Key.lt, Crits.Bind{k1, v1} <> r, k),
          Binds.sorted(~V, Crits.Bind{k1, v1} <> r)
        )(
          Crits.Crit.and_true(
            Key.lt(k, k1),
            Binds.all(~V, ~List<&2, U32>, ~Key.lt, r, k)
          )(
            ht
          )(
            Binds.all_lt(
              ~V,
              k,
              k1,
              r
            )(
              ht
            )(
              Shared.Bool.and_true_left(
                Binds.all(~V, ~List<&2, U32>, ~Key.lt, r, k1),
                Binds.sorted(~V, r)
              )(h)
            )
          )
        )(h),
        hn => he => h,
        hn => he => Crits.Crit.and_true(
          Binds.all(~V, ~List<&2, U32>, ~Key.lt, Binds.insert(V, r, k, v), k1),
          Binds.sorted(~V, Binds.insert(V, r, k, v))
        )(
          Binds.all_insert(
            ~V,
            r,
            k1,
            k,
            v
          )(
            Shared.Bool.and_true_left(
              Binds.all(~V, ~List<&2, U32>, ~Key.lt, r, k1),
              Binds.sorted(~V, r)
            )(h)
          )(Key.lt_total(k, k1)(hn)(he))
        )(
          Binds.insert_sorted(
            ~V,
            r,
            k,
            v
          )(
            Shared.Bool.and_true_right(
              Binds.all(~V, ~List<&2, U32>, ~Key.lt, r, k1),
              Binds.sorted(~V, r)
            )(h)
          )
        )
      )

# the same key is the same, whichever is asked first
def Key.is_eq_sym(
  +a: List<&2, U32>,
  +b: List<&2, U32>
) -> {Crits.Key.is_eq(a, b) == Crits.Key.is_eq(b, a): Bool}:
  Bool.by(
    c => {c == Crits.Key.is_eq(b, a): Bool},
    Crits.Key.is_eq(a, b),
    t =>
      %Crits.Key.is_eq_sound(a, b)(t): {True{} == Crits.Key.is_eq(_, a): Bool}
      Equal.sym(Bool, Crits.Key.is_eq(a, a), True{}, Crits.Key.is_eq_refl(a)),
    f => Equal.sym(Bool, Crits.Key.is_eq(b, a), False{}, Crits.Key.ne_sym(a, b)(f)))

# two keys that differ are not both the key q
def Key.ne_both(
  +k1: List<&2, U32>,
  +k: List<&2, U32>,
  +q: List<&2, U32>
) -> {
  Crits.Key.is_eq(k1, k) == False{}: Bool
} -> {Bool.and(Crits.Key.is_eq(k1, q), Crits.Key.is_eq(k, q)) == False{}: Bool}:
  hne => Bool.by(
    c => {Bool.and(c, Crits.Key.is_eq(k, q)) == False{}: Bool},
    Crits.Key.is_eq(k1, q),
    t1 => Crits.Crit.false_of(
      Crits.Key.is_eq(k, q)
    )(
      t2 => Shared.Bool.false_ne_true(
        Equal.trans(
          Bool,
          False{},
          Crits.Key.is_eq(k1, k),
          True{},
          Equal.sym(Bool, Crits.Key.is_eq(k1, k), False{}, hne),
          (
            %Equal.sym(List<&2, U32>, k1, q, Crits.Key.is_eq_sound(k1, q)(t1)): {Crits.Key.is_eq(_, k) == True{}: Bool}
            %Equal.sym(List<&2, U32>, k, q, Crits.Key.is_eq_sound(k, q)(t2)): {Crits.Key.is_eq(q, _) == True{}: Bool}
            Crits.Key.is_eq_refl(q))
        )
      )
    ),
    f1 => {==}
  )

# a choice under the same test twice is the choice once
def Bool.pick_twice(
  -A: Type,
  c: Bool,
  -a: A,
  -b: A,
  -x: A
) -> {Bool.pick(A, c, a, x) == Bool.pick(A, c, a, Bool.pick(A, c, b, x)): A}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

# two choices whose tests are not both true can be made in any order
def Bool.pick_swap(
  -A: Type,
  c1: Bool,
  c: Bool,
  -a1: A,
  -a: A,
  -x: A
) -> {
  Bool.and(c1, c) == False{}: Bool
} -> {
  Bool.pick(A, c1, a1, Bool.pick(A, c, a, x)) == Bool.pick(A, c, a, Bool.pick(A, c1, a1, x)): A
}:
  match c1 c:
    case True{} True{}:
      h => Empty.absurd({a1 == a: A}, Shared.Bool.true_ne_false(h))
    case True{} False{}:
      h => {==}
    case False{} True{}:
      h => {==}
    case False{} False{}:
      h => {==}

# an insert holds its value under its key, and under each other key what the
# entries held
def Binds.get_insert(
  -V: Data,
  es: List<&2, Crits.Bind<V>>,
  +k: List<&2, U32>,
  +v: V,
  +q: List<&2, U32>
) -> {
  Binds.get(
    V,
    Binds.insert(V, es, k, v),
    q
  )
    == Bool.pick(Maybe<&2, V>, Crits.Key.is_eq(k, q), Some{v}, Binds.get(V, es, q)): Maybe<&2, V>
}:
  match es:
    case Nil{}:
      {==}
    case Con{Crits.Bind{+k1, +v1}, +r}:
      Binds.insert_cases(
        V,
        x => {Binds.get(V, x, q) == Bool.pick(Maybe<&2, V>, Crits.Key.is_eq(k, q), Some{v}, Bool.pick(Maybe<&2, V>, Crits.Key.is_eq(k1, q), Some{v1}, Binds.get(V, r, q))): Maybe<&2, V>},
        k1,
        v1,
        r,
        k,
        v,
        ht => {==},
        hn => he =>
          %Crits.Key.is_eq_sound(k1, k)(he): {Bool.pick(Maybe<&2, V>, Crits.Key.is_eq(k1, q), Some{v}, Binds.get(V, r, q)) == Bool.pick(Maybe<&2, V>, Crits.Key.is_eq(_, q), Some{v}, Bool.pick(Maybe<&2, V>, Crits.Key.is_eq(k1, q), Some{v1}, Binds.get(V, r, q))): Maybe<&2, V>}
          Bool.pick_twice(Maybe<&2, V>, Crits.Key.is_eq(k1, q), Some{v}, Some{v1}, Binds.get(V, r, q)),
        hn => he =>
          %Equal.sym(Maybe<&2, V>, Binds.get(V, Binds.insert(V, r, k, v), q), Bool.pick(Maybe<&2, V>, Crits.Key.is_eq(k, q), Some{v}, Binds.get(V, r, q)), Binds.get_insert(V, r, k, v, q)): {Bool.pick(Maybe<&2, V>, Crits.Key.is_eq(k1, q), Some{v1}, _) == Bool.pick(Maybe<&2, V>, Crits.Key.is_eq(k, q), Some{v}, Bool.pick(Maybe<&2, V>, Crits.Key.is_eq(k1, q), Some{v1}, Binds.get(V, r, q))): Maybe<&2, V>}
          Bool.pick_swap(Maybe<&2, V>, Crits.Key.is_eq(k1, q), Crits.Key.is_eq(k, q), Some{v1}, Some{v}, Binds.get(V, r, q))(Key.ne_both(k1, k, q)(he)))

# Entries of a map and what it holds
# ----------------------------------

# a choice of a choice, else c, is the first, else the choice of the others
def Maybe.or_assoc(
  -A: Data,
  a: Maybe<&2, A>,
  -b: Maybe<&2, A>,
  -c: Maybe<&2, A>
) -> {
  Maybe.or(
    &2,
    A,
    Maybe.or(&2, A, a, b),
    c
  )
    == Maybe.or(&2, A, a, Maybe.or(&2, A, b, c)): Maybe<&2, A>
}:
  match a:
    case None{}:
      {==}
    case Some{x}:
      {==}

# a value, else nothing, is the value
def Maybe.or_none(-A: Data, a: Maybe<&2, A>) -> {Maybe.or(&2, A, a, None{}) == a: Maybe<&2, A>}:
  match a:
    case None{}:
      {==}
    case Some{x}:
      {==}

# Crit.get_entries.go at the sides of a fork, from what holds of each side
# (gz: what the entries of both sides, then rest, hold; gn: those of the one
# side, then rest)
def Crit.get_entries.sides(
  -A: Data,
  -gz: Maybe<&2, A>,
  -gn: Maybe<&2, A>,
  lz: Maybe<&2, A>,
  -ln: Maybe<&2, A>,
  -gr: Maybe<&2, A>
) -> {
  gz == Maybe.or(&2, A, lz, gn): Maybe<&2, A>
} -> {
  gn == Maybe.or(&2, A, ln, gr): Maybe<&2, A>
} -> {gz == Maybe.or(&2, A, Maybe.or(&2, A, lz, ln), gr): Maybe<&2, A>}:
  e1 => e2 =>
    %Equal.sym(
      Maybe<&2, A>,
      gz,
      Maybe.or(&2, A, lz, gn),
      e1
    ): {_ == Maybe.or(&2, A, Maybe.or(&2, A, lz, ln), gr): Maybe<&2, A>}
    %Equal.sym(
      Maybe<&2, A>,
      gn,
      Maybe.or(&2, A, ln, gr),
      e2
    ): {Maybe.or(&2, A, lz, _) == Maybe.or(&2, A, Maybe.or(&2, A, lz, ln), gr): Maybe<&2, A>}
    Equal.sym(
      Maybe<&2, A>,
      Maybe.or(&2, A, Maybe.or(&2, A, lz, ln), gr),
      Maybe.or(&2, A, lz, Maybe.or(&2, A, ln, gr)),
      Maybe.or_assoc(A, lz, ln, gr)
    )

# the entries of a map, then rest, hold under a key what the map holds, else
# what rest holds
def Crit.get_entries.go(
  -V: Data,
  m: Crits.Crit<V>,
  +rest: List<&2, Crits.Bind<V>>,
  +q: List<&2, U32>
) -> {
  Binds.get(
    V,
    Crits.Crit.entries.go(V, m, rest),
    q
  )
    == Maybe.or(&2, V, Crits.Crit.lookup(V, m, q), Binds.get(V, rest, q)): Maybe<&2, V>
}:
  match m:
    case Crits.Crit.Tip{}:
      {==}
    case Crits.Crit.Leaf{+k, +v}:
      Bool.by(
        c => {
          Bool.pick(
            Maybe<&2, V>,
            c,
            Some{v},
            Binds.get(V, rest, q)
          )
            == Maybe.or(
              &2,
              V,
              Shared.Maybe.when(V, c, u => Some{v}),
              Binds.get(V, rest, q)
            ): Maybe<&2, V>
        },
        Crits.Key.is_eq(k, q),
        t => {==},
        f => {==}
      )
    case Crits.Crit.Fork{r, p, None{}, +z, +o}:
      Crit.get_entries.sides(
        V,
        Binds.get(V, Crits.Crit.entries.go(V, z, Crits.Crit.entries.go(V, o, rest)), q),
        Binds.get(V, Crits.Crit.entries.go(V, o, rest), q),
        Crits.Crit.lookup(V, z, q),
        Crits.Crit.lookup(V, o, q),
        Binds.get(V, rest, q)
      )(
        Crit.get_entries.go(V, z, Crits.Crit.entries.go(V, o, rest), q)
      )(Crit.get_entries.go(V, o, rest, q))
    case Crits.Crit.Fork{+r, p, Some{+v}, +z, +o}:
      Bool.by(
        c => {
          Bool.pick(
            Maybe<&2, V>,
            c,
            Some{v},
            Binds.get(V, Crits.Crit.entries.go(V, z, Crits.Crit.entries.go(V, o, rest)), q)
          )
            == Maybe.or(
              &2,
              V,
              Maybe.or(
                &2,
                V,
                Shared.Maybe.when(V, c, u => Some{v}),
                Maybe.or(&2, V, Crits.Crit.lookup(V, z, q), Crits.Crit.lookup(V, o, q))
              ),
              Binds.get(V, rest, q)
            ): Maybe<&2, V>
        },
        Crits.Key.is_eq(r, q),
        t => {==},
        f => Crit.get_entries.sides(
          V,
          Binds.get(V, Crits.Crit.entries.go(V, z, Crits.Crit.entries.go(V, o, rest)), q),
          Binds.get(V, Crits.Crit.entries.go(V, o, rest), q),
          Crits.Crit.lookup(V, z, q),
          Crits.Crit.lookup(V, o, q),
          Binds.get(V, rest, q)
        )(
          Crit.get_entries.go(V, z, Crits.Crit.entries.go(V, o, rest), q)
        )(Crit.get_entries.go(V, o, rest, q))
      )

# the entries of a map hold under each key what the map holds
def Crit.get_entries(
  -V: Data,
  +m: Crits.Crit<V>,
  +q: List<&2, U32>
) -> {Binds.get(V, Crits.Crit.entries(V, m), q) == Crits.Crit.lookup(V, m, q): Maybe<&2, V>}:
  Equal.trans(
    Maybe<&2, V>,
    Binds.get(V, Crits.Crit.entries(V, m), q),
    Maybe.or(&2, V, Crits.Crit.lookup(V, m, q), None{}),
    Crits.Crit.lookup(V, m, q),
    Crit.get_entries.go(V, m, [], q),
    Maybe.or_none(V, Crits.Crit.lookup(V, m, q))
  )

# A write is an insert
# --------------------

# the entries of a map after a write hold, under each key, what an insert
# into its entries holds
def Crit.get_set(
  ~V: Data,
  +m: Crits.Crit<V>,
  +k: List<&2, U32>,
  +v: V,
  +q: List<&2, U32>
) -> {
  Crits.Crit.wf(~V, m, 0n) == True{}: Bool
} -> {
  Binds.get(
    V,
    Crits.Crit.entries(V, Crits.Crit.set(~V, m, k, v)),
    q
  )
    == Binds.get(V, Binds.insert(V, Crits.Crit.entries(V, m), k, v), q): Maybe<&2, V>
}:
  h =>
    %Equal.sym(
      Maybe<&2, V>,
      Binds.get(V, Crits.Crit.entries(V, Crits.Crit.set(~V, m, k, v)), q),
      Crits.Crit.lookup(V, Crits.Crit.set(~V, m, k, v), q),
      Crit.get_entries(V, Crits.Crit.set(~V, m, k, v), q)
    ): {_ == Binds.get(V, Binds.insert(V, Crits.Crit.entries(V, m), k, v), q): Maybe<&2, V>}
    %Equal.sym(
      Maybe<&2, V>,
      Binds.get(V, Binds.insert(V, Crits.Crit.entries(V, m), k, v), q),
      Bool.pick(
        Maybe<&2, V>,
        Crits.Key.is_eq(k, q),
        Some{v},
        Binds.get(V, Crits.Crit.entries(V, m), q)
      ),
      Binds.get_insert(V, Crits.Crit.entries(V, m), k, v, q)
    ): {Crits.Crit.lookup(V, Crits.Crit.set(~V, m, k, v), q) == _: Maybe<&2, V>}
    %Equal.sym(
      Maybe<&2, V>,
      Binds.get(V, Crits.Crit.entries(V, m), q),
      Crits.Crit.lookup(V, m, q),
      Crit.get_entries(V, m, q)
    ): {
      Crits.Crit.lookup(
        V,
        Crits.Crit.set(~V, m, k, v),
        q
      )
        == Bool.pick(Maybe<&2, V>, Crits.Key.is_eq(k, q), Some{v}, _): Maybe<&2, V>
    }
    %Key.is_eq_sym(
      q,
      k
    ): {
      Crits.Crit.lookup(
        V,
        Crits.Crit.set(~V, m, k, v),
        q
      )
        == Bool.pick(Maybe<&2, V>, _, Some{v}, Crits.Crit.lookup(V, m, q)): Maybe<&2, V>
    }
    %Crits.Dict.merge_new(
      ~V,
      Crits.Crit.lookup(V, m, k),
      v
    ): {
      Crits.Crit.lookup(
        V,
        Crits.Crit.set(~V, m, k, v),
        q
      )
        == Bool.pick(
          Maybe<&2, V>,
          Crits.Key.is_eq(q, k),
          Some{_},
          Crits.Crit.lookup(V, m, q)
        ): Maybe<&2, V>
    }
    Crits.Crit.upsert_lookup(~V, ~(w => x => x), m, k, v, q)(h)

# the entries of a map after a write and an insert into its entries hold the
# same under the key of each of the entries es
def Crit.same_set(
  ~V: Data,
  +m: Crits.Crit<V>,
  +k: List<&2, U32>,
  +v: V,
  es: List<&2, Crits.Bind<V>>
) -> {
  Crits.Crit.wf(~V, m, 0n) == True{}: Bool
} -> Binds.Same(
  V,
  es,
  Crits.Crit.entries(V, Crits.Crit.set(~V, m, k, v)),
  Binds.insert(V, Crits.Crit.entries(V, m), k, v)
):
  match es:
    case Nil{}:
      h => Unit{}
    case Con{Crits.Bind{+q, w}, +rest}:
      +h => (Crit.get_set(~V, m, k, v, q)(h), Crit.same_set(~V, m, k, v, rest)(h))

# the entries of a well formed map after a write are an insert into its
# entries: a new entry at the place of a new key, a new value in the entry of
# a key that the map holds
def Crit.entries_set(
  ~V: Data,
  +m: Crits.Crit<V>,
  +k: List<&2, U32>,
  +v: V
) -> {
  Crits.Crit.wf(~V, m, 0n) == True{}: Bool
} -> {
  Crits.Crit.entries(
    V,
    Crits.Crit.set(~V, m, k, v)
  )
    == Binds.insert(V, Crits.Crit.entries(V, m), k, v): List<&2, Crits.Bind<V>>
}:
  +h => Binds.ext(
    ~V,
    Crits.Crit.entries(V, Crits.Crit.set(~V, m, k, v)),
    Binds.insert(V, Crits.Crit.entries(V, m), k, v)
  )(
    Crit.entries_sorted(
      ~V,
      Crits.Crit.set(~V, m, k, v)
    )(Crits.Crit.upsert_wf(~V, ~(w => x => x), m, k, v)(h))
  )(
    Binds.insert_sorted(~V, Crits.Crit.entries(V, m), k, v)(Crit.entries_sorted(~V, m)(h))
  )(
    Crit.same_set(~V, m, k, v, Crits.Crit.entries(V, Crits.Crit.set(~V, m, k, v)))(h)
  )(Crit.same_set(~V, m, k, v, Binds.insert(V, Crits.Crit.entries(V, m), k, v))(h))

# An index across a write
# -----------------------
# An index keeps the entries that pass a test, in order. A write of a new
# key is one insert into the index when its entry passes the test, and
# leaves the index as it is when not.

# an entry kept when c, before r, is a choice of two lists
def List.put_pick(
  -A: Data,
  -h: A,
  -r: List<&2, A>,
  c: Bool
) -> {List.filter.put(A, h, r, c) == Bool.pick(List<&2, A>, c, h <> r, r): List<&2, A>}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

# an entry before a choice of two lists is a choice of the entry before each
def List.cons_pick(
  -A: Data,
  -h: A,
  c: Bool,
  -a: List<&2, A>,
  -b: List<&2, A>
) -> {
  h <> Bool.pick(List<&2, A>, c, a, b) == Bool.pick(List<&2, A>, c, h <> a, h <> b): List<&2, A>
}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

# an insert of a key before each key of es into the kept entries of es puts
# its entry first
def Binds.insert_first(
  ~V: Data,
  ~f: Crits.Bind<V> -> Bool,
  es: List<&2, Crits.Bind<V>>,
  +k: List<&2, U32>,
  +v: V
) -> {
  Binds.all(~V, ~List<&2, U32>, ~Key.lt, es, k) == True{}: Bool
} -> {
  Binds.insert(
    V,
    List.filter(~Crits.Bind<V>, ~f, es),
    k,
    v
  )
    == Crits.Bind{k, v}
    <> List.filter(~Crits.Bind<V>, ~f, es): List<&2, Crits.Bind<V>>
}:
  match es:
    case Nil{}:
      h => {==}
    case Con{Crits.Bind{+k1, +v1}, +r}:
      +h => Bool.by(
        c => {
          Binds.insert(
            V,
            List.filter.put(
              Crits.Bind<V>,
              Crits.Bind{k1, v1},
              List.filter(~Crits.Bind<V>, ~f, r),
              c
            ),
            k,
            v
          )
            == Crits.Bind{k, v}
            <> List.filter.put(
              Crits.Bind<V>,
              Crits.Bind{k1, v1},
              List.filter(~Crits.Bind<V>, ~f, r),
              c
            ): List<&2, Crits.Bind<V>>
        },
        f(Crits.Bind{k1, v1}),
        t => Binds.insert_lt(
          V,
          k1,
          v1,
          List.filter(~Crits.Bind<V>, ~f, r),
          k,
          v
        )(
          Shared.Bool.and_true_left(Key.lt(k, k1), Binds.all(~V, ~List<&2, U32>, ~Key.lt, r, k))(h)
        ),
        fl => Binds.insert_first(
          ~V,
          ~f,
          r,
          k,
          v
        )(
          Shared.Bool.and_true_right(Key.lt(k, k1), Binds.all(~V, ~List<&2, U32>, ~Key.lt, r, k))(h)
        )
      )

# the kept entries of an insert of a new key into sorted entries: an insert
# into the kept entries when the new entry is kept, else the kept entries
def Binds.filter_insert(
  ~V: Data,
  ~f: Crits.Bind<V> -> Bool,
  es: List<&2, Crits.Bind<V>>,
  +k: List<&2, U32>,
  +v: V
) -> {
  Binds.sorted(~V, es) == True{}: Bool
} -> {
  Binds.get(V, es, k) == None{}: Maybe<&2, V>
} -> {
  List.filter(
    ~Crits.Bind<V>,
    ~f,
    Binds.insert(V, es, k, v)
  )
    == Bool.pick(
      List<&2, Crits.Bind<V>>,
      f(Crits.Bind{k, v}),
      Binds.insert(V, List.filter(~Crits.Bind<V>, ~f, es), k, v),
      List.filter(~Crits.Bind<V>, ~f, es)
    ): List<&2, Crits.Bind<V>>
}:
  match es:
    case Nil{}:
      hs => hg => List.put_pick(Crits.Bind<V>, Crits.Bind{k, v}, [], f(Crits.Bind{k, v}))
    case Con{Crits.Bind{+k1, +v1}, +r}:
      +hs => +hg => Binds.insert_cases(
        V,
        x => {List.filter(~Crits.Bind<V>, ~f, x) == Bool.pick(List<&2, Crits.Bind<V>>, f(Crits.Bind{k, v}), Binds.insert(V, List.filter(~Crits.Bind<V>, ~f, Crits.Bind{k1, v1} <> r), k, v), List.filter(~Crits.Bind<V>, ~f, Crits.Bind{k1, v1} <> r)): List<&2, Crits.Bind<V>>},
        k1,
        v1,
        r,
        k,
        v,
        +ht =>
          %Equal.sym(List<&2, Crits.Bind<V>>, Binds.insert(V, List.filter(~Crits.Bind<V>, ~f, Crits.Bind{k1, v1} <> r), k, v), Crits.Bind{k, v} <> List.filter(~Crits.Bind<V>, ~f, Crits.Bind{k1, v1} <> r), Binds.insert_first(~V, ~f, Crits.Bind{k1, v1} <> r, k, v)(Crits.Crit.and_true(Key.lt(k, k1), Binds.all(~V, ~List<&2, U32>, ~Key.lt, r, k))(ht)(Binds.all_lt(~V, k, k1, r)(ht)(Shared.Bool.and_true_left(Binds.all(~V, ~List<&2, U32>, ~Key.lt, r, k1), Binds.sorted(~V, r))(hs))))): {List.filter.put(Crits.Bind<V>, Crits.Bind{k, v}, List.filter(~Crits.Bind<V>, ~f, Crits.Bind{k1, v1} <> r), f(Crits.Bind{k, v})) == Bool.pick(List<&2, Crits.Bind<V>>, f(Crits.Bind{k, v}), _, List.filter(~Crits.Bind<V>, ~f, Crits.Bind{k1, v1} <> r)): List<&2, Crits.Bind<V>>}
          List.put_pick(Crits.Bind<V>, Crits.Bind{k, v}, List.filter(~Crits.Bind<V>, ~f, Crits.Bind{k1, v1} <> r), f(Crits.Bind{k, v})),
        hn => he => Empty.absurd({List.filter(~Crits.Bind<V>, ~f, Crits.Bind{k1, v} <> r) == Bool.pick(List<&2, Crits.Bind<V>>, f(Crits.Bind{k, v}), Binds.insert(V, List.filter(~Crits.Bind<V>, ~f, Crits.Bind{k1, v1} <> r), k, v), List.filter(~Crits.Bind<V>, ~f, Crits.Bind{k1, v1} <> r)): List<&2, Crits.Bind<V>>}, Crits.Crit.some_ne_none(V, v1, (
            %he: {Bool.pick(Maybe<&2, V>, _, Some{v1}, Binds.get(V, r, k)) == None{}: Maybe<&2, V>}
            hg))),
        +hn => +he =>
          %Equal.sym(List<&2, Crits.Bind<V>>, List.filter(~Crits.Bind<V>, ~f, Binds.insert(V, r, k, v)), Bool.pick(List<&2, Crits.Bind<V>>, f(Crits.Bind{k, v}), Binds.insert(V, List.filter(~Crits.Bind<V>, ~f, r), k, v), List.filter(~Crits.Bind<V>, ~f, r)), Binds.filter_insert(~V, ~f, r, k, v)(Shared.Bool.and_true_right(Binds.all(~V, ~List<&2, U32>, ~Key.lt, r, k1), Binds.sorted(~V, r))(hs))((
            %he: {Bool.pick(Maybe<&2, V>, _, Some{v1}, Binds.get(V, r, k)) == None{}: Maybe<&2, V>}
            hg))): {List.filter.put(Crits.Bind<V>, Crits.Bind{k1, v1}, _, f(Crits.Bind{k1, v1})) == Bool.pick(List<&2, Crits.Bind<V>>, f(Crits.Bind{k, v}), Binds.insert(V, List.filter(~Crits.Bind<V>, ~f, Crits.Bind{k1, v1} <> r), k, v), List.filter(~Crits.Bind<V>, ~f, Crits.Bind{k1, v1} <> r)): List<&2, Crits.Bind<V>>}
          Bool.by(
        c => {List.filter.put(Crits.Bind<V>, Crits.Bind{k1, v1}, Bool.pick(List<&2, Crits.Bind<V>>, f(Crits.Bind{k, v}), Binds.insert(V, List.filter(~Crits.Bind<V>, ~f, r), k, v), List.filter(~Crits.Bind<V>, ~f, r)), c) == Bool.pick(List<&2, Crits.Bind<V>>, f(Crits.Bind{k, v}), Binds.insert(V, List.filter.put(Crits.Bind<V>, Crits.Bind{k1, v1}, List.filter(~Crits.Bind<V>, ~f, r), c), k, v), List.filter.put(Crits.Bind<V>, Crits.Bind{k1, v1}, List.filter(~Crits.Bind<V>, ~f, r), c)): List<&2, Crits.Bind<V>>},
        f(Crits.Bind{k1, v1}),
        t =>
          %Equal.sym(List<&2, Crits.Bind<V>>, Binds.insert(V, Crits.Bind{k1, v1} <> List.filter(~Crits.Bind<V>, ~f, r), k, v), Crits.Bind{k1, v1} <> Binds.insert(V, List.filter(~Crits.Bind<V>, ~f, r), k, v), Binds.insert_gt(V, k1, v1, List.filter(~Crits.Bind<V>, ~f, r), k, v)(hn)(he)): {Crits.Bind{k1, v1} <> Bool.pick(List<&2, Crits.Bind<V>>, f(Crits.Bind{k, v}), Binds.insert(V, List.filter(~Crits.Bind<V>, ~f, r), k, v), List.filter(~Crits.Bind<V>, ~f, r)) == Bool.pick(List<&2, Crits.Bind<V>>, f(Crits.Bind{k, v}), _, Crits.Bind{k1, v1} <> List.filter(~Crits.Bind<V>, ~f, r)): List<&2, Crits.Bind<V>>}
          List.cons_pick(Crits.Bind<V>, Crits.Bind{k1, v1}, f(Crits.Bind{k, v}), Binds.insert(V, List.filter(~Crits.Bind<V>, ~f, r), k, v), List.filter(~Crits.Bind<V>, ~f, r)),
        fl => {==}))

# the entries of a map that lacks a key hold nothing under it
def Crit.get_none(
  ~V: Data,
  +m: Crits.Crit<V>,
  +k: List<&2, U32>
) -> {
  Crits.Crit.wf(~V, m, 0n) == True{}: Bool
} -> {
  Crits.Crit.has(V, m, k) == False{}: Bool
} -> {Binds.get(V, Crits.Crit.entries(V, m), k) == None{}: Maybe<&2, V>}:
  h => hh => Equal.trans(
    Maybe<&2, V>,
    Binds.get(V, Crits.Crit.entries(V, m), k),
    Crits.Crit.lookup(V, m, k),
    None{},
    Crit.get_entries(V, m, k),
    Crits.Crit.none_of_some(
      V,
      Crits.Crit.lookup(V, m, k)
    )(
      Equal.trans(
        Bool,
        Maybe.is_some(&2, V, Crits.Crit.lookup(V, m, k)),
        Crits.Crit.has(V, m, k),
        False{},
        Equal.sym(
          Bool,
          Crits.Crit.has(V, m, k),
          Maybe.is_some(&2, V, Crits.Crit.lookup(V, m, k)),
          Crits.Crit.has_lookup(~V, m, 0n, k)(h)
        ),
        hh
      )
    )
  )

# the kept entries of a well formed map after a write of a new key: an insert
# into its kept entries when the new entry is kept, else its kept entries
def Crit.filter_set(
  ~V: Data,
  ~f: Crits.Bind<V> -> Bool,
  +m: Crits.Crit<V>,
  +k: List<&2, U32>,
  +v: V
) -> {
  Crits.Crit.wf(~V, m, 0n) == True{}: Bool
} -> {
  Crits.Crit.has(V, m, k) == False{}: Bool
} -> {
  List.filter(
    ~Crits.Bind<V>,
    ~f,
    Crits.Crit.entries(V, Crits.Crit.set(~V, m, k, v))
  )
    == Bool.pick(
      List<&2, Crits.Bind<V>>,
      f(Crits.Bind{k, v}),
      Binds.insert(V, List.filter(~Crits.Bind<V>, ~f, Crits.Crit.entries(V, m)), k, v),
      List.filter(~Crits.Bind<V>, ~f, Crits.Crit.entries(V, m))
    ): List<&2, Crits.Bind<V>>
}:
  +h => hh =>
    %Equal.sym(
      List<&2, Crits.Bind<V>>,
      Crits.Crit.entries(V, Crits.Crit.set(~V, m, k, v)),
      Binds.insert(V, Crits.Crit.entries(V, m), k, v),
      Crit.entries_set(~V, m, k, v)(h)
    ): {
      List.filter(
        ~Crits.Bind<V>,
        ~f,
        _
      )
        == Bool.pick(
          List<&2, Crits.Bind<V>>,
          f(Crits.Bind{k, v}),
          Binds.insert(V, List.filter(~Crits.Bind<V>, ~f, Crits.Crit.entries(V, m)), k, v),
          List.filter(~Crits.Bind<V>, ~f, Crits.Crit.entries(V, m))
        ): List<&2, Crits.Bind<V>>
    }
    Binds.filter_insert(
      ~V,
      ~f,
      Crits.Crit.entries(V, m),
      k,
      v
    )(Crit.entries_sorted(~V, m)(h))(Crit.get_none(~V, m, k)(h)(hh))

# The values of a map across a write
# ----------------------------------
# A set of values is a map from the key of each value to the value, and its
# list is the values of its entries. A write of a value is then an insert
# into the list, by the keys of the values.

# an insert of a value whose key is before the first key puts it first
def Values.insert_lt(
  ~V: Data,
  ~key: V -> List<&2, U32>,
  +y: V,
  +r: List<&2, V>,
  +x: V
) -> {
  Key.lt(key(x), key(y)) == True{}: Bool
} -> {Values.insert(~V, ~key, y <> r, x) == x <> y <> r: List<&2, V>}:
  hl => Bool.when_true_eq(
    List<&2, V>,
    Key.lt(key(x), key(y)),
    u => x <> y <> r,
    u => Shared.Bool.when(
      List<&2, V>,
      Crits.Key.is_eq(key(y), key(x)),
      w => x <> r,
      w => y <> Values.insert(~V, ~key, r, x)
    )
  )(hl)

# an insert of a value with the first key takes the place of the first value
def Values.insert_eq(
  ~V: Data,
  ~key: V -> List<&2, U32>,
  +y: V,
  +r: List<&2, V>,
  +x: V
) -> {
  Key.lt(key(x), key(y)) == False{}: Bool
} -> {
  Crits.Key.is_eq(key(y), key(x)) == True{}: Bool
} -> {Values.insert(~V, ~key, y <> r, x) == x <> r: List<&2, V>}:
  hn => he => Equal.trans(
    List<&2, V>,
    Values.insert(~V, ~key, y <> r, x),
    Shared.Bool.when(
      List<&2, V>,
      Crits.Key.is_eq(key(y), key(x)),
      w => x <> r,
      w => y <> Values.insert(~V, ~key, r, x)
    ),
    x <> r,
    Crits.Crit.when_false_eq(
      List<&2, V>,
      Key.lt(key(x), key(y)),
      u => x <> y <> r,
      u => Shared.Bool.when(
        List<&2, V>,
        Crits.Key.is_eq(key(y), key(x)),
        w => x <> r,
        w => y <> Values.insert(~V, ~key, r, x)
      )
    )(hn),
    Bool.when_true_eq(
      List<&2, V>,
      Crits.Key.is_eq(key(y), key(x)),
      w => x <> r,
      w => y <> Values.insert(~V, ~key, r, x)
    )(he)
  )

# an insert of a value whose key is after the first key goes on after the
# first value
def Values.insert_gt(
  ~V: Data,
  ~key: V -> List<&2, U32>,
  +y: V,
  +r: List<&2, V>,
  +x: V
) -> {
  Key.lt(key(x), key(y)) == False{}: Bool
} -> {
  Crits.Key.is_eq(key(y), key(x)) == False{}: Bool
} -> {Values.insert(~V, ~key, y <> r, x) == y <> Values.insert(~V, ~key, r, x): List<&2, V>}:
  hn => he => Equal.trans(
    List<&2, V>,
    Values.insert(~V, ~key, y <> r, x),
    Shared.Bool.when(
      List<&2, V>,
      Crits.Key.is_eq(key(y), key(x)),
      w => x <> r,
      w => y <> Values.insert(~V, ~key, r, x)
    ),
    y <> Values.insert(~V, ~key, r, x),
    Crits.Crit.when_false_eq(
      List<&2, V>,
      Key.lt(key(x), key(y)),
      u => x <> y <> r,
      u => Shared.Bool.when(
        List<&2, V>,
        Crits.Key.is_eq(key(y), key(x)),
        w => x <> r,
        w => y <> Values.insert(~V, ~key, r, x)
      )
    )(hn),
    Crits.Crit.when_false_eq(
      List<&2, V>,
      Crits.Key.is_eq(key(y), key(x)),
      w => x <> r,
      w => y <> Values.insert(~V, ~key, r, x)
    )(he)
  )

# the values of an insert into entries that sit under the keys of their
# values are an insert into their values
def Binds.values_insert(
  ~V: Data,
  ~key: V -> List<&2, U32>,
  es: List<&2, Crits.Bind<V>>,
  +x: V
) -> {
  Binds.keyed(~V, ~key, es) == True{}: Bool
} -> {
  Crits.Binds.values(
    V,
    Binds.insert(V, es, key(x), x)
  )
    == Values.insert(~V, ~key, Crits.Binds.values(V, es), x): List<&2, V>
}:
  match es:
    case Nil{}:
      h => {==}
    case Con{Crits.Bind{+k1, +v1}, +r}:
      +h =>
        %Equal.sym(
          List<&2, U32>,
          k1,
          key(v1),
          Crits.Key.is_eq_sound(
            k1,
            key(v1)
          )(Shared.Bool.and_true_left(Crits.Key.is_eq(k1, key(v1)), Binds.keyed(~V, ~key, r))(h))
        ): {
          Crits.Binds.values(
            V,
            Binds.insert(V, Crits.Bind{_, v1} <> r, key(x), x)
          )
            == Values.insert(~V, ~key, v1 <> Crits.Binds.values(V, r), x): List<&2, V>
        }
        Binds.insert_cases(
          V,
          y => {
            Crits.Binds.values(
              V,
              y
            )
              == Values.insert(~V, ~key, v1 <> Crits.Binds.values(V, r), x): List<&2, V>
          },
          key(v1),
          v1,
          r,
          key(x),
          x,
          ht => Equal.sym(
            List<&2, V>,
            Values.insert(~V, ~key, v1 <> Crits.Binds.values(V, r), x),
            x <> v1 <> Crits.Binds.values(V, r),
            Values.insert_lt(~V, ~key, v1, Crits.Binds.values(V, r), x)(ht)
          ),
          hn => he => Equal.sym(
            List<&2, V>,
            Values.insert(~V, ~key, v1 <> Crits.Binds.values(V, r), x),
            x <> Crits.Binds.values(V, r),
            Values.insert_eq(~V, ~key, v1, Crits.Binds.values(V, r), x)(hn)(he)
          ),
          hn => he => Equal.trans(
            List<&2, V>,
            v1 <> Crits.Binds.values(V, Binds.insert(V, r, key(x), x)),
            v1 <> Values.insert(~V, ~key, Crits.Binds.values(V, r), x),
            Values.insert(~V, ~key, v1 <> Crits.Binds.values(V, r), x),
            Equal.cong(
              List<&2, V>,
              List<&2, V>,
              t => v1 <> t,
              Crits.Binds.values(V, Binds.insert(V, r, key(x), x)),
              Values.insert(~V, ~key, Crits.Binds.values(V, r), x),
              Binds.values_insert(
                ~V,
                ~key,
                r,
                x
              )(
                Shared.Bool.and_true_right(
                  Crits.Key.is_eq(k1, key(v1)),
                  Binds.keyed(~V, ~key, r)
                )(h)
              )
            ),
            Equal.sym(
              List<&2, V>,
              Values.insert(~V, ~key, v1 <> Crits.Binds.values(V, r), x),
              v1 <> Values.insert(~V, ~key, Crits.Binds.values(V, r), x),
              Values.insert_gt(~V, ~key, v1, Crits.Binds.values(V, r), x)(hn)(he)
            )
          )
        )

# the kept values of entries are the values of the entries whose values are
# kept
def Binds.values_filter(
  ~V: Data,
  ~f: V -> Bool,
  es: List<&2, Crits.Bind<V>>
) -> {
  List.filter(
    ~V,
    ~f,
    Crits.Binds.values(V, es)
  )
    == Crits.Binds.values(
      V,
      List.filter(~Crits.Bind<V>, ~(b => f(Crits.Crit.bind_val(V, b))), es)
    ): List<&2, V>
}:
  match es:
    case Nil{}:
      {==}
    case Con{Crits.Bind{+k1, +v1}, +r}:
      Bool.by(
        c => {
          List.filter.put(
            V,
            v1,
            List.filter(~V, ~f, Crits.Binds.values(V, r)),
            c
          )
            == Crits.Binds.values(
              V,
              List.filter.put(
                Crits.Bind<V>,
                Crits.Bind{k1, v1},
                List.filter(~Crits.Bind<V>, ~(b => f(Crits.Crit.bind_val(V, b))), r),
                c
              )
            ): List<&2, V>
        },
        f(v1),
        t => Equal.cong(
          List<&2, V>,
          List<&2, V>,
          y => v1 <> y,
          List.filter(~V, ~f, Crits.Binds.values(V, r)),
          Crits.Binds.values(
            V,
            List.filter(~Crits.Bind<V>, ~(b => f(Crits.Crit.bind_val(V, b))), r)
          ),
          Binds.values_filter(~V, ~f, r)
        ),
        fl => Binds.values_filter(~V, ~f, r)
      )

# the kept entries of entries that sit under the keys of their values sit
# under the keys of their values
def Binds.keyed_filter(
  ~V: Data,
  ~key: V -> List<&2, U32>,
  ~g: Crits.Bind<V> -> Bool,
  es: List<&2, Crits.Bind<V>>
) -> {
  Binds.keyed(~V, ~key, es) == True{}: Bool
} -> {Binds.keyed(~V, ~key, List.filter(~Crits.Bind<V>, ~g, es)) == True{}: Bool}:
  match es:
    case Nil{}:
      h => {==}
    case Con{Crits.Bind{+k1, +v1}, +r}:
      +h => Bool.by(
        c => {
          Binds.keyed(
            ~V,
            ~key,
            List.filter.put(
              Crits.Bind<V>,
              Crits.Bind{k1, v1},
              List.filter(~Crits.Bind<V>, ~g, r),
              c
            )
          )
            == True{}: Bool
        },
        g(Crits.Bind{k1, v1}),
        t => Crits.Crit.and_true(
          Crits.Key.is_eq(k1, key(v1)),
          Binds.keyed(~V, ~key, List.filter(~Crits.Bind<V>, ~g, r))
        )(
          Shared.Bool.and_true_left(Crits.Key.is_eq(k1, key(v1)), Binds.keyed(~V, ~key, r))(h)
        )(
          Binds.keyed_filter(
            ~V,
            ~key,
            ~g,
            r
          )(Shared.Bool.and_true_right(Crits.Key.is_eq(k1, key(v1)), Binds.keyed(~V, ~key, r))(h))
        ),
        fl => Binds.keyed_filter(
          ~V,
          ~key,
          ~g,
          r
        )(Shared.Bool.and_true_right(Crits.Key.is_eq(k1, key(v1)), Binds.keyed(~V, ~key, r))(h))
      )

# the values of a choice of two lists of entries are a choice of their values
def Binds.values_pick(
  -V: Data,
  c: Bool,
  -a: List<&2, Crits.Bind<V>>,
  -b: List<&2, Crits.Bind<V>>
) -> {
  Crits.Binds.values(
    V,
    Bool.pick(List<&2, Crits.Bind<V>>, c, a, b)
  )
    == Bool.pick(List<&2, V>, c, Crits.Binds.values(V, a), Crits.Binds.values(V, b)): List<&2, V>
}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

# the values of a well formed map of values under their keys, after a write
# of a value under its key, are an insert of the value into its values
def Crit.values_set(
  ~V: Data,
  ~key: V -> List<&2, U32>,
  +m: Crits.Crit<V>,
  +x: V
) -> {
  Crits.Crit.wf(~V, m, 0n) == True{}: Bool
} -> {
  Binds.keyed(~V, ~key, Crits.Crit.entries(V, m)) == True{}: Bool
} -> {
  Crits.Binds.values(
    V,
    Crits.Crit.entries(V, Crits.Crit.set(~V, m, key(x), x))
  )
    == Values.insert(~V, ~key, Crits.Binds.values(V, Crits.Crit.entries(V, m)), x): List<&2, V>
}:
  h => hk =>
    %Equal.sym(
      List<&2, Crits.Bind<V>>,
      Crits.Crit.entries(V, Crits.Crit.set(~V, m, key(x), x)),
      Binds.insert(V, Crits.Crit.entries(V, m), key(x), x),
      Crit.entries_set(~V, m, key(x), x)(h)
    ): {
      Crits.Binds.values(
        V,
        _
      )
        == Values.insert(~V, ~key, Crits.Binds.values(V, Crits.Crit.entries(V, m)), x): List<&2, V>
    }
    Binds.values_insert(~V, ~key, Crits.Crit.entries(V, m), x)(hk)

# the kept values of such a map after a write of a new value: an insert into
# its kept values when the new value is kept, else its kept values
def Crit.values_filter_set(
  ~V: Data,
  ~key: V -> List<&2, U32>,
  ~f: V -> Bool,
  +m: Crits.Crit<V>,
  +x: V
) -> {
  Crits.Crit.wf(~V, m, 0n) == True{}: Bool
} -> {
  Binds.keyed(~V, ~key, Crits.Crit.entries(V, m)) == True{}: Bool
} -> {
  Crits.Crit.has(V, m, key(x)) == False{}: Bool
} -> {
  List.filter(
    ~V,
    ~f,
    Crits.Binds.values(V, Crits.Crit.entries(V, Crits.Crit.set(~V, m, key(x), x)))
  )
    == Bool.pick(
      List<&2, V>,
      f(x),
      Values.insert(
        ~V,
        ~key,
        List.filter(~V, ~f, Crits.Binds.values(V, Crits.Crit.entries(V, m))),
        x
      ),
      List.filter(~V, ~f, Crits.Binds.values(V, Crits.Crit.entries(V, m)))
    ): List<&2, V>
}:
  h => hk => hh =>
    %Equal.sym(
      List<&2, V>,
      List.filter(
        ~V,
        ~f,
        Crits.Binds.values(V, Crits.Crit.entries(V, Crits.Crit.set(~V, m, key(x), x)))
      ),
      Crits.Binds.values(
        V,
        List.filter(
          ~Crits.Bind<V>,
          ~(b => f(Crits.Crit.bind_val(V, b))),
          Crits.Crit.entries(V, Crits.Crit.set(~V, m, key(x), x))
        )
      ),
      Binds.values_filter(~V, ~f, Crits.Crit.entries(V, Crits.Crit.set(~V, m, key(x), x)))
    ): {
      _
        == Bool.pick(
          List<&2, V>,
          f(x),
          Values.insert(
            ~V,
            ~key,
            List.filter(~V, ~f, Crits.Binds.values(V, Crits.Crit.entries(V, m))),
            x
          ),
          List.filter(~V, ~f, Crits.Binds.values(V, Crits.Crit.entries(V, m)))
        ): List<&2, V>
    }
    %Equal.sym(
      List<&2, Crits.Bind<V>>,
      List.filter(
        ~Crits.Bind<V>,
        ~(b => f(Crits.Crit.bind_val(V, b))),
        Crits.Crit.entries(V, Crits.Crit.set(~V, m, key(x), x))
      ),
      Bool.pick(
        List<&2, Crits.Bind<V>>,
        f(x),
        Binds.insert(
          V,
          List.filter(
            ~Crits.Bind<V>,
            ~(b => f(Crits.Crit.bind_val(V, b))),
            Crits.Crit.entries(V, m)
          ),
          key(x),
          x
        ),
        List.filter(~Crits.Bind<V>, ~(b => f(Crits.Crit.bind_val(V, b))), Crits.Crit.entries(V, m))
      ),
      Crit.filter_set(~V, ~(b => f(Crits.Crit.bind_val(V, b))), m, key(x), x)(h)(hh)
    ): {
      Crits.Binds.values(
        V,
        _
      )
        == Bool.pick(
          List<&2, V>,
          f(x),
          Values.insert(
            ~V,
            ~key,
            List.filter(~V, ~f, Crits.Binds.values(V, Crits.Crit.entries(V, m))),
            x
          ),
          List.filter(~V, ~f, Crits.Binds.values(V, Crits.Crit.entries(V, m)))
        ): List<&2, V>
    }
    %Equal.sym(
      List<&2, V>,
      List.filter(~V, ~f, Crits.Binds.values(V, Crits.Crit.entries(V, m))),
      Crits.Binds.values(
        V,
        List.filter(~Crits.Bind<V>, ~(b => f(Crits.Crit.bind_val(V, b))), Crits.Crit.entries(V, m))
      ),
      Binds.values_filter(~V, ~f, Crits.Crit.entries(V, m))
    ): {
      Crits.Binds.values(
        V,
        Bool.pick(
          List<&2, Crits.Bind<V>>,
          f(x),
          Binds.insert(
            V,
            List.filter(
              ~Crits.Bind<V>,
              ~(b => f(Crits.Crit.bind_val(V, b))),
              Crits.Crit.entries(V, m)
            ),
            key(x),
            x
          ),
          List.filter(
            ~Crits.Bind<V>,
            ~(b => f(Crits.Crit.bind_val(V, b))),
            Crits.Crit.entries(V, m)
          )
        )
      )
        == Bool.pick(List<&2, V>, f(x), Values.insert(~V, ~key, _, x), _): List<&2, V>
    }
    %Binds.values_insert(
      ~V,
      ~key,
      List.filter(~Crits.Bind<V>, ~(b => f(Crits.Crit.bind_val(V, b))), Crits.Crit.entries(V, m)),
      x
    )(
      Binds.keyed_filter(
        ~V,
        ~key,
        ~(b => f(Crits.Crit.bind_val(V, b))),
        Crits.Crit.entries(V, m)
      )(hk)
    ): {
      Crits.Binds.values(
        V,
        Bool.pick(
          List<&2, Crits.Bind<V>>,
          f(x),
          Binds.insert(
            V,
            List.filter(
              ~Crits.Bind<V>,
              ~(b => f(Crits.Crit.bind_val(V, b))),
              Crits.Crit.entries(V, m)
            ),
            key(x),
            x
          ),
          List.filter(
            ~Crits.Bind<V>,
            ~(b => f(Crits.Crit.bind_val(V, b))),
            Crits.Crit.entries(V, m)
          )
        )
      )
        == Bool.pick(
          List<&2, V>,
          f(x),
          _,
          Crits.Binds.values(
            V,
            List.filter(
              ~Crits.Bind<V>,
              ~(b => f(Crits.Crit.bind_val(V, b))),
              Crits.Crit.entries(V, m)
            )
          )
        ): List<&2, V>
    }
    Binds.values_pick(
      V,
      f(x),
      Binds.insert(
        V,
        List.filter(~Crits.Bind<V>, ~(b => f(Crits.Crit.bind_val(V, b))), Crits.Crit.entries(V, m)),
        key(x),
        x
      ),
      List.filter(~Crits.Bind<V>, ~(b => f(Crits.Crit.bind_val(V, b))), Crits.Crit.entries(V, m))
    )
