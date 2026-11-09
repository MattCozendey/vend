import Base
import ../../../../shared.bend as Shared

# Tries
# -----
# A trie maps keys to values. A key is a list of bits, read from the first:
# a False goes to zero, a True to one. Its shape is a function of the keys and
# values it holds, so two tries that hold the same entries are the same term,
# and a union is commutative, associative and idempotent as terms.

# a trie: the value of the empty key here, then the keys that start with False
# (zero) and with True (one)
type Trie<-V: Data> is Data:
  Tip{}
  Bin{here: Maybe<&2, V>, zero: Trie<V>, one: Trie<V>}

# a trie with no entries
def Trie.new(-V: Data) -> Trie<V>:
  Tip{}

# the value of the key k in t, or None
def Trie.get(-V: Data, t: Trie<V>, k: List<&2, Bool>) -> Maybe<&2, V>:
  match t k:
    case Tip{} r:
      None{}
    case Bin{h, z, o} Nil{}:
      h
    case Bin{h, z, o} Con{False{}, r}:
      Trie.get(V, z, r)
    case Bin{h, z, o} Con{True{}, r}:
      Trie.get(V, o, r)

# the trie with only the key k, mapped to v
def Trie.one(-V: Data, k: List<&2, Bool>, v: V) -> Trie<V>:
  match k:
    case Nil{}:
      Bin{Some{v}, Tip{}, Tip{}}
    case Con{False{}, r}:
      Bin{None{}, Trie.one(V, r, v), Tip{}}
    case Con{True{}, r}:
      Bin{None{}, Tip{}, Trie.one(V, r, v)}

# t with the key k mapped to v
def Trie.set(-V: Data, t: Trie<V>, k: List<&2, Bool>, v: V) -> Trie<V>:
  match t k:
    case Tip{} r:
      Trie.one(V, r, v)
    case Bin{h, z, o} Nil{}:
      Bin{Some{v}, z, o}
    case Bin{h, z, o} Con{False{}, r}:
      Bin{h, Trie.set(V, z, r, v), o}
    case Bin{h, z, o} Con{True{}, r}:
      Bin{h, z, Trie.set(V, o, r, v)}

# the values of t, in the order of their keys
def Trie.values(-V: Data, t: Trie<V>) -> List<&2, V>:
  match t:
    case Tip{}:
      []
    case Bin{None{}, z, o}:
      zs os = Trie.values(V, z) Trie.values(V, o)
      List.append(&2, V, zs, os)
    case Bin{Some{v}, z, o}:
      zs os = Trie.values(V, z) Trie.values(V, o)
      v <> List.append(&2, V, zs, os)

# the number of entries of t
def Trie.size(-V: Data, t: Trie<V>) -> Nat:
  match t:
    case Tip{}:
      0n
    case Bin{None{}, z, o}:
      zs os = Trie.size(V, z) Trie.size(V, o)
      Nat.add(zs, os)
    case Bin{Some{v}, z, o}:
      zs os = Trie.size(V, z) Trie.size(V, o)
      1n+Nat.add(zs, os)

# t holds the key k
def Trie.has(-V: Data, t: Trie<V>, k: List<&2, Bool>) -> Bool:
  Maybe.is_some(&2, V, Trie.get(V, t, k))

# xs, each once, but for the keys seen
def Trie.unique(~A: Data, ~key: A -> List<&2, Bool>, xs: List<&2, A>, +seen: Trie<Unit>) -> List<&2, A>:
  match xs:
    case Nil{}:
      []
    case Con{+x, +r}:
      +k = key(x)
      Shared.Bool.when(
        List<&2, A>,
        Trie.has(Unit, seen, k),
        u => Trie.unique(~A, ~key, r, seen),
        u => x <> Trie.unique(~A, ~key, r, Trie.set(Unit, seen, k, Unit{}))
      )

# no two of xs have the same key, nor one of the keys seen
def Trie.distinct(~A: Data, ~key: A -> List<&2, Bool>, xs: List<&2, A>, +seen: Trie<Unit>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, r}:
      +k = key(x)
      Shared.Bool.when(
        Bool,
        Trie.has(Unit, seen, k),
        u => False{},
        u => Trie.distinct(~A, ~key, r, Trie.set(Unit, seen, k, Unit{}))
      )

# t with the key of each of xs, as a set
def Trie.put_keys(
  ~A: Data,
  ~key: A -> List<&2, Bool>,
  xs: List<&2, A>,
  t: Trie<Unit>
) -> Trie<Unit>:
  match xs:
    case Nil{}:
      t
    case Con{x, r}:
      Trie.put_keys(~A, ~key, r, Trie.set(Unit, t, key(x), Unit{}))

# the entries of t whose keys start with k, under the rest of their keys
def Trie.under(-V: Data, t: Trie<V>, k: List<&2, Bool>) -> Trie<V>:
  match t k:
    case Tip{} r:
      Tip{}
    case Bin{h, z, o} Nil{}:
      Bin{h, z, o}
    case Bin{h, z, o} Con{False{}, r}:
      Trie.under(V, z, r)
    case Bin{h, z, o} Con{True{}, r}:
      Trie.under(V, o, r)

# Keys of text
# ------------

# the n low bits of x, the lowest first
def Trie.bits(n: Nat, +x: U32) -> List<&2, Bool>:
  match n:
    case 0n:
      []
    case 1n+p:
      U32.is_eq(U32.and(x, 1), 1) <> Trie.bits(p, U32.shr(x))

# the key of the character x: an ASCII one as False and its 7 bits, any other
# as True and its 32 bits
def Trie.char(+x: U32) -> List<&2, Bool>:
  Shared.Bool.when(
    List<&2, Bool>,
    U32.is_lt(x, 128),
    u => False{} <> Trie.bits(7n, x),
    u => True{} <> Trie.bits(32n, x)
  )

# the key of the text t: each character as True and its key, then False; so
# the key of one text never starts the key of another, and keys of texts put
# one after the other never meet
def Trie.text(t: String) -> List<&2, Bool>:
  match t:
    case SNil{}:
      [False{}]
    case SCon{Chr{x}, r}:
      True{} <> List.append(&2, Bool, Trie.char(x), Trie.text(r))

# Highest keys
# ------------
# Keys of a fixed width, read high bit first, are ordered as numbers: one is
# after zero. A descent finds the highest key whose entries a test accepts,
# in the width's number of steps when the test accepts at the top.

# the n bits of x, highest first
def Trie.word(n: Nat, x: U32) -> List<&2, Bool>:
  List.reverse(&2, Bool, Trie.bits(n, x))

# the key k of the zero branch, if any
def Trie.top.lo(m: Maybe<&2, List<&2, Bool>>) -> Maybe<&2, List<&2, Bool>>:
  match m:
    case Some{k}:
      Some{False{} <> k}
    case None{}:
      None{}

# the key hi of the one branch, if any; else the one that lo finds
def Trie.top.of(
  hi: Maybe<&2, List<&2, Bool>>,
  lo: Unit -> Maybe<&2, List<&2, Bool>>
) -> Maybe<&2, List<&2, Bool>>:
  match hi:
    case Some{k}:
      Some{True{} <> k}
    case None{}:
      Trie.top.lo(lo(Unit{}))

# the highest key of w bits whose entries (the trie under it) ok accepts, with
# c; a key with no entries is never taken
def Trie.top(
  ~V: Data,
  ~C: Data,
  ~ok: C -> Trie<V> -> Bool,
  w: Nat,
  t: Trie<V>,
  +c: C
) -> Maybe<&2, List<&2, Bool>>:
  match w t:
    case n Tip{}:
      None{}
    case 0n Bin{h, z, o}:
      Shared.Bool.when(Maybe<&2, List<&2, Bool>>, ok(c)(Bin{h, z, o}), u => Some{[]}, u => None{})
    case 1n+(+p) Bin{h, z, o}:
      Trie.top.of(Trie.top(~V, ~C, ~ok, p, o, c), u => Trie.top(~V, ~C, ~ok, p, z, c))

# the key k has w bits
def Trie.wide(k: List<&2, Bool>, w: Nat) -> Bool:
  match k w:
    case Nil{} 0n:
      True{}
    case Con{b, r} 1n+p:
      Trie.wide(r, p)
    case _ _:
      False{}

# a is not after b (keys of one width, high bit first)
def Trie.key_le(a: List<&2, Bool>, b: List<&2, Bool>) -> Bool:
  match a b:
    case Con{False{}, ra} Con{False{}, rb}:
      Trie.key_le(ra, rb)
    case Con{True{}, ra} Con{True{}, rb}:
      Trie.key_le(ra, rb)
    case Con{True{}, ra} Con{False{}, rb}:
      False{}
    case _ _:
      True{}

# the key k is not after the key m (none: k is after every key)
def Trie.below(k: List<&2, Bool>, m: Maybe<&2, List<&2, Bool>>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      Trie.key_le(k, x)

# Laws of highest keys
# --------------------

# Trie.top_ok at a key's end, by whether ok accepts the entries there (held)
def Trie.top_ok.here(
  ~V: Data,
  ~C: Data,
  ~ok: C -> Trie<V> -> Bool,
  -h0: Maybe<&2, V>,
  -z: Trie<V>,
  -o: Trie<V>,
  -c: C,
  -k: List<&2, Bool>,
  held: Bool,
  e: {ok(c)(Bin{h0, z, o}) == held: Bool}
) -> {
  Shared.Bool.when(
    Maybe<&2, List<&2, Bool>>,
    held,
    u => Some{[]},
    u => None{}
  )
    == Some{k}: Maybe<&2, List<&2, Bool>>
} -> {ok(c)(Trie.under(V, Bin{h0, z, o}, k)) == True{}: Bool}:
  match held:
    case True{}:
      h =>
        %Shared.Maybe.some_inj(
          List<&2, Bool>,
          [],
          k,
          h
        ): {ok(c)(Trie.under(V, Bin{h0, z, o}, _)) == True{}: Bool}
        e
    case False{}:
      h => Empty.absurd(
        {ok(c)(Trie.under(V, Bin{h0, z, o}, k)) == True{}: Bool},
        Shared.Maybe.none_ne_some(List<&2, Bool>, k, h)
      )

# Trie.top_ok for a key k of the zero branch z (mz is what it finds there)
def Trie.top_ok.lo(
  ~V: Data,
  ~C: Data,
  ~ok: C -> Trie<V> -> Bool,
  -h0: Maybe<&2, V>,
  -z: Trie<V>,
  -o: Trie<V>,
  -c: C,
  -k: List<&2, Bool>,
  mz: Maybe<&2, List<&2, Bool>>,
  ihz: @k2: List<
    &2,
    Bool> -> {
    mz == Some{k2}: Maybe<&2, List<&2, Bool>>
  } -> {ok(c)(Trie.under(V, z, k2)) == True{}: Bool}
) -> {
  Trie.top.lo(mz) == Some{k}: Maybe<&2, List<&2, Bool>>
} -> {ok(c)(Trie.under(V, Bin{h0, z, o}, k)) == True{}: Bool}:
  match mz:
    case Some{k2}:
      h =>
        %Shared.Maybe.some_inj(List<&2, Bool>, False{} <> k2, k, h):
          {ok(c)(Trie.under(V, Bin{h0, z, o}, _)) == True{}: Bool}
        ihz(k2)({==})
    case None{}:
      h => Empty.absurd(
        {ok(c)(Trie.under(V, Bin{h0, z, o}, k)) == True{}: Bool},
        Shared.Maybe.none_ne_some(List<&2, Bool>, k, h)
      )

# Trie.top_ok at a branch (mo is what the one branch o finds)
def Trie.top_ok.hi(
  ~V: Data,
  ~C: Data,
  ~ok: C -> Trie<V> -> Bool,
  -h0: Maybe<&2, V>,
  -z: Trie<V>,
  -o: Trie<V>,
  -c: C,
  -k: List<&2, Bool>,
  mo: Maybe<&2, List<&2, Bool>>,
  -lo: Unit -> Maybe<&2, List<&2, Bool>>,
  iho: @k2: List<
    &2,
    Bool> -> {
    mo == Some{k2}: Maybe<&2, List<&2, Bool>>
  } -> {ok(c)(Trie.under(V, o, k2)) == True{}: Bool},
  lol: {
    Trie.top.lo(lo(Unit{})) == Some{k}: Maybe<&2, List<&2, Bool>>
  } -> {ok(c)(Trie.under(V, Bin{h0, z, o}, k)) == True{}: Bool}
) -> {
  Trie.top.of(mo, lo) == Some{k}: Maybe<&2, List<&2, Bool>>
} -> {ok(c)(Trie.under(V, Bin{h0, z, o}, k)) == True{}: Bool}:
  match mo:
    case Some{k2}:
      h =>
        %Shared.Maybe.some_inj(List<&2, Bool>, True{} <> k2, k, h):
          {ok(c)(Trie.under(V, Bin{h0, z, o}, _)) == True{}: Bool}
        iho(k2)({==})
    case None{}:
      h => lol(h)

# the key that a descent finds is accepted
law Trie.top_ok:
  for ~V: Data
  for ~C: Data
  for ~ok: C -> Trie<V> -> Bool
  for w: Nat
  for t: Trie<V>
  for +c: C
  for -k: List<&2, Bool>
  {
    Trie.top(~V, ~C, ~ok, w, t, c) == Some{k}: Maybe<&2, List<&2, Bool>>
  } -> {ok(c)(Trie.under(V, t, k)) == True{}: Bool}

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
def Trie.top_ok(ty, ctx, ok, w, t, c, k):
  match w t:
    case n Tip{}:
      h => Empty.absurd(
        {ok(c)(Trie.under(ty, Tip{}, k)) == True{}: Bool},
        Shared.Maybe.none_ne_some(List<&2, Bool>, k, h)
      )
    case 0n Bin{h0, z, o}:
      Trie.top_ok.here(~ty, ~ctx, ~ok, h0, z, o, c, k, ok(c)(Bin{h0, z, o}), {==})
    case 1n+(+p) Bin{h0, +z, +o}:
      Trie.top_ok.hi(
        ~ty,
        ~ctx,
        ~ok,
        h0,
        z,
        o,
        c,
        k,
        Trie.top(~ty, ~ctx, ~ok, p, o, c),
        u => Trie.top(~ty, ~ctx, ~ok, p, z, c),
        k2 => Trie.top_ok(~ty, ~ctx, ~ok, p, o, c, k2),
        Trie.top_ok.lo(
          ~ty,
          ~ctx,
          ~ok,
          h0,
          z,
          o,
          c,
          k,
          Trie.top(~ty, ~ctx, ~ok, p, z, c),
          k2 => Trie.top_ok(~ty, ~ctx, ~ok, p, z, c, k2)
        )
      )
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# Trie.top_max for a key True <> r, once what the one branch finds (mo) is known
def Trie.top_max.one(
  mo: Maybe<&2, List<&2, Bool>>,
  lo: Unit -> Maybe<&2, List<&2, Bool>>,
  -r: List<&2, Bool>,
  ih: {Trie.below(r, mo) == True{}: Bool}
) -> {Trie.below(True{} <> r, Trie.top.of(mo, lo)) == True{}: Bool}:
  match mo:
    case Some{k}:
      ih
    case None{}:
      Empty.absurd(
        {Trie.below(True{} <> r, Trie.top.of(None{}, lo)) == True{}: Bool},
        Shared.Bool.false_ne_true(ih)
      )

# Trie.top_max for a key False <> r, once what the zero branch finds (mz) is known
def Trie.top_max.lo(
  mz: Maybe<&2, List<&2, Bool>>,
  -r: List<&2, Bool>,
  ih: {Trie.below(r, mz) == True{}: Bool}
) -> {Trie.below(False{} <> r, Trie.top.lo(mz)) == True{}: Bool}:
  match mz:
    case Some{k}:
      ih
    case None{}:
      Empty.absurd(
        {Trie.below(False{} <> r, Trie.top.lo(None{})) == True{}: Bool},
        Shared.Bool.false_ne_true(ih)
      )

# Trie.top_max for a key False <> r, once what the one branch finds (mo) is known
def Trie.top_max.zero(
  mo: Maybe<&2, List<&2, Bool>>,
  lo: Unit -> Maybe<&2, List<&2, Bool>>,
  -r: List<&2, Bool>,
  ih: {Trie.below(r, lo(Unit{})) == True{}: Bool}
) -> {Trie.below(False{} <> r, Trie.top.of(mo, lo)) == True{}: Bool}:
  match mo:
    case Some{k}:
      {==}
    case None{}:
      Trie.top_max.lo(lo(Unit{}), r, ih)

# no key after the one that a descent finds is accepted: every key of w bits
# whose entries ok accepts is at or before it
law Trie.top_max:
  for ~V: Data
  for ~C: Data
  for ~ok: C -> Trie<V> -> Bool
  for ~empty: @c: C -> {ok(c)(Tip{}) == False{}: Bool}
  for w: Nat
  for t: Trie<V>
  for +c: C
  for k: List<&2, Bool>
  {Trie.wide(k, w) == True{}: Bool}
    -> {ok(c)(Trie.under(V, t, k)) == True{}: Bool}
    -> {Trie.below(k, Trie.top(~V, ~C, ~ok, w, t, c)) == True{}: Bool}

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
def Trie.top_max(ty, ctx, ok, empty, w, t, c, k):
  match w t k:
    case n Tip{} q:
      hw => hok => Empty.absurd(
        {Trie.below(q, Trie.top(~ty, ~ctx, ~ok, n, Tip{}, c)) == True{}: Bool},
        Shared.Bool.false_ne_true(
          Equal.trans(
            Bool,
            False{},
            ok(c)(Tip{}),
            True{},
            Equal.sym(Bool, ok(c)(Tip{}), False{}, empty(c)),
            hok
          )
        )
      )
    case 0n Bin{h0, z, o} Nil{}:
      hw => hok =>
        %Equal.sym(Bool, ok(c)(Bin{h0, z, o}), True{}, hok):
          {
            Trie.below(
              [],
              Shared.Bool.when(Maybe<&2, List<&2, Bool>>, _, u => Some{[]}, u => None{})
            )
              == True{}: Bool
          }
        {==}
    case 0n Bin{h0, z, o} Con{b, r}:
      hw => hok => Empty.absurd(
        {Trie.below(b <> r, Trie.top(~ty, ~ctx, ~ok, 0n, Bin{h0, z, o}, c)) == True{}: Bool},
        Shared.Bool.false_ne_true(hw)
      )
    case 1n+p Bin{h0, z, o} Nil{}:
      hw => hok => Empty.absurd(
        {Trie.below([], Trie.top(~ty, ~ctx, ~ok, 1n+p, Bin{h0, z, o}, c)) == True{}: Bool},
        Shared.Bool.false_ne_true(hw)
      )
    case 1n+(+p) Bin{h0, +z, +o} Con{True{}, r}:
      hw => hok => Trie.top_max.one(
        Trie.top(~ty, ~ctx, ~ok, p, o, c),
        u => Trie.top(~ty, ~ctx, ~ok, p, z, c),
        r,
        Trie.top_max(~ty, ~ctx, ~ok, ~empty, p, o, c, r)(hw)(hok)
      )
    case 1n+(+p) Bin{h0, +z, +o} Con{False{}, +r}:
      hw => hok => Trie.top_max.zero(
        Trie.top(~ty, ~ctx, ~ok, p, o, c),
        u => Trie.top(~ty, ~ctx, ~ok, p, z, c),
        r,
        Trie.top_max(~ty, ~ctx, ~ok, ~empty, p, z, c, r)(hw)(hok)
      )
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# Unions
# ------
# A union joins the values of a key that both tries hold. When join is a
# semilattice (commutative, associative, idempotent), so is the union: two
# holders that take in each other's entries, in any order and any number of
# times, end with the same trie.

# the entries of a and b, joined where both hold a key
def Trie.union(~V: Data, ~join: V -> V -> V, a: Trie<V>, b: Trie<V>) -> Trie<V>:
  match a b:
    case Tip{} y:
      y
    case Bin{h, z, o} Tip{}:
      Bin{h, z, o}
    case Bin{h1, z1, o1} Bin{h2, z2, o2}:
      zs os = Trie.union(~V, ~join, z1, z2) Trie.union(~V, ~join, o1, o2)
      Bin{Shared.Maybe.join(~V, ~join, h1, h2), zs, os}

# a, unless b holds the same value
def Trie.minus.here(
  ~V: Data,
  ~same: V -> V -> Bool,
  a: Maybe<&2, V>,
  b: Maybe<&2, V>
) -> Maybe<&2, V>:
  match a b:
    case None{} y:
      None{}
    case Some{x} None{}:
      Some{x}
    case Some{+x} Some{y}:
      Bool.pick(Maybe<&2, V>, same(x, y), None{}, Some{x})

# the entries of s that r does not hold with the same value: what a holder of
# r lacks of s
def Trie.minus(~V: Data, ~same: V -> V -> Bool, s: Trie<V>, r: Trie<V>) -> Trie<V>:
  match s r:
    case Tip{} y:
      Tip{}
    case Bin{h, z, o} Tip{}:
      Bin{h, z, o}
    case Bin{h1, z1, o1} Bin{h2, z2, o2}:
      zs os = Trie.minus(~V, ~same, z1, z2) Trie.minus(~V, ~same, o1, o2)
      Bin{Trie.minus.here(~V, ~same, h1, h2), zs, os}

# Laws
# ----

# the trie of one key has its value
def Trie.get_one(
  -V: Data,
  k: List<&2, Bool>,
  v: V
) -> {Trie.get(V, Trie.one(V, k, v), k) == Some{v}: Maybe<&2, V>}:
  match k:
    case Nil{}:
      {==}
    case Con{False{}, r}:
      Trie.get_one(V, r, v)
    case Con{True{}, r}:
      Trie.get_one(V, r, v)

# k is the key k0
def Trie.same_key(k: List<&2, Bool>, k0: List<&2, Bool>) -> Bool:
  Shared.List.is_eq(~Bool, ~Shared.Bool.is_eq, k, k0)

# the trie of only k0, at k: v when k is k0, else nothing
def Trie.get_one_at(
  -V: Data,
  k0: List<&2, Bool>,
  v: V,
  k: List<&2, Bool>
) -> {
  Trie.get(
    V,
    Trie.one(V, k0, v),
    k
  )
    == Bool.pick(Maybe<&2, V>, Trie.same_key(k, k0), Some{v}, None{}): Maybe<&2, V>
}:
  match k0 k:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{False{}, r}:
      {==}
    case Nil{} Con{True{}, r}:
      {==}
    case Con{b, r0} Nil{}:
      {==}
    case Con{False{}, r0} Con{False{}, r}:
      Trie.get_one_at(V, r0, v, r)
    case Con{False{}, r0} Con{True{}, r}:
      {==}
    case Con{True{}, r0} Con{False{}, r}:
      {==}
    case Con{True{}, r0} Con{True{}, r}:
      Trie.get_one_at(V, r0, v, r)

# t with k0 set to v holds v at k0, and what t holds at any other key
law Trie.get_set:
  for -V: Data
  for t: Trie<V>
  for k0: List<&2, Bool>
  for v: V
  for k: List<&2, Bool>
  {
    Trie.get(
      V,
      Trie.set(V, t, k0, v),
      k
    )
      == Bool.pick(Maybe<&2, V>, Trie.same_key(k, k0), Some{v}, Trie.get(V, t, k)): Maybe<&2, V>
  }

def Trie.get_set(ty, t, k0, v, k):
  match t k0 k:
    case Tip{} p q:
      Trie.get_one_at(ty, p, v, q)
    case Bin{h, z, o} Nil{} Nil{}:
      {==}
    case Bin{h, z, o} Nil{} Con{False{}, r}:
      {==}
    case Bin{h, z, o} Nil{} Con{True{}, r}:
      {==}
    case Bin{h, z, o} Con{False{}, r0} Nil{}:
      {==}
    case Bin{h, z, o} Con{True{}, r0} Nil{}:
      {==}
    case Bin{h, z, o} Con{False{}, r0} Con{False{}, r}:
      Trie.get_set(ty, z, r0, v, r)
    case Bin{h, z, o} Con{False{}, r0} Con{True{}, r}:
      {==}
    case Bin{h, z, o} Con{True{}, r0} Con{False{}, r}:
      {==}
    case Bin{h, z, o} Con{True{}, r0} Con{True{}, r}:
      Trie.get_set(ty, o, r0, v, r)

# a union holds, for each key, what both sides hold, joined
law Trie.get_union:
  for ~V: Data
  for ~join: V -> V -> V
  for a: Trie<V>
  for b: Trie<V>
  for k: List<&2, Bool>
  {
    Trie.get(
      V,
      Trie.union(~V, ~join, a, b),
      k
    )
      == Shared.Maybe.join(~V, ~join, Trie.get(V, a, k), Trie.get(V, b, k)): Maybe<&2, V>
  }

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
def Trie.get_union(ty, join, a, b, k):
  match a b k:
    case Tip{} y q:
      {==}
    case Bin{h, z, o} Tip{} q:
      get1 = Trie.get(ty, Bin{h, z, o}, q)
      Equal.sym(
        Maybe<&2, ty>,
        Shared.Maybe.join(~ty, ~join, get1, None{}),
        get1,
        Shared.Maybe.join_none(~ty, ~join, get1)
      )
    case Bin{h1, z1, o1} Bin{h2, z2, o2} Nil{}:
      {==}
    case Bin{h1, z1, o1} Bin{h2, z2, o2} Con{False{}, r}:
      Trie.get_union(~ty, ~join, z1, z2, r)
    case Bin{h1, z1, o1} Bin{h2, z2, o2} Con{True{}, r}:
      Trie.get_union(~ty, ~join, o1, o2, r)
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# a union is the same either way round
law Trie.union_comm:
  for ~V: Data
  for ~join: V -> V -> V
  for ~comm: @x: V -> @y: V -> {join(x, y) == join(y, x): V}
  for a: Trie<V>
  for b: Trie<V>
  {Trie.union(~V, ~join, a, b) == Trie.union(~V, ~join, b, a): Trie<V>}

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
def Trie.union_comm(ty, join, comm, a, b):
  match a b:
    case Tip{} Tip{}:
      {==}
    case Tip{} Bin{h, z, o}:
      {==}
    case Bin{+h, +z, +o} Tip{}:
      {==}
    case Bin{h1, z1, o1} Bin{+h2, +z2, +o2}:
      pick1 = Shared.Maybe.join(~ty, ~join, h1, h2)
      union1 = Trie.union(~ty, ~join, z1, z2)
      union2 = Trie.union(~ty, ~join, o1, o2)
      union3 = Trie.union(~ty, ~join, o2, o1)
      %Shared.Maybe.join_comm(~ty, ~join, ~comm, h1, h2):
        {Bin{pick1, union1, union2} == Bin{_, Trie.union(~ty, ~join, z2, z1), union3}: Trie<ty>}
      %Trie.union_comm(~ty, ~join, ~comm, z1, z2):
        {Bin{pick1, union1, union2} == Bin{pick1, _, union3}: Trie<ty>}
      %Trie.union_comm(~ty, ~join, ~comm, o1, o2):
        {Bin{pick1, union1, union2} == Bin{pick1, union1, _}: Trie<ty>}
      {==}
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# a union groups either way
law Trie.union_assoc:
  for ~V: Data
  for ~join: V -> V -> V
  for ~assoc: @x: V -> @y: V -> @z: V -> {join(join(x, y), z) == join(x, join(y, z)): V}
  for a: Trie<V>
  for b: Trie<V>
  for c: Trie<V>
  {
    Trie.union(
      ~V,
      ~join,
      Trie.union(~V, ~join, a, b),
      c
    )
      == Trie.union(~V, ~join, a, Trie.union(~V, ~join, b, c)): Trie<V>
  }

def Trie.union_assoc(ty, join, assoc, a, b, c):
  match a b c:
    case Tip{} y w:
      {==}
    case Bin{h, z, o} Tip{} w:
      {==}
    case Bin{h1, z1, o1} Bin{h2, z2, o2} Tip{}:
      {==}
    case Bin{h1, z1, o1} Bin{h2, z2, o2} Bin{h3, z3, o3}:
      %Shared.Maybe.join_assoc(~ty, ~join, ~assoc, h1, h2, h3):
        {
          Bin{
            Shared.Maybe.join(~ty, ~join, Shared.Maybe.join(~ty, ~join, h1, h2), h3),
            Trie.union(~ty, ~join, Trie.union(~ty, ~join, z1, z2), z3),
            Trie.union(~ty, ~join, Trie.union(~ty, ~join, o1, o2), o3)
          }
            == Bin{
              _,
              Trie.union(~ty, ~join, z1, Trie.union(~ty, ~join, z2, z3)),
              Trie.union(~ty, ~join, o1, Trie.union(~ty, ~join, o2, o3))
            }: Trie<ty>
        }
      %Trie.union_assoc(~ty, ~join, ~assoc, z1, z2, z3):
        {
          Bin{
            Shared.Maybe.join(~ty, ~join, Shared.Maybe.join(~ty, ~join, h1, h2), h3),
            Trie.union(~ty, ~join, Trie.union(~ty, ~join, z1, z2), z3),
            Trie.union(~ty, ~join, Trie.union(~ty, ~join, o1, o2), o3)
          }
            == Bin{
              Shared.Maybe.join(~ty, ~join, Shared.Maybe.join(~ty, ~join, h1, h2), h3),
              _,
              Trie.union(~ty, ~join, o1, Trie.union(~ty, ~join, o2, o3))
            }: Trie<ty>
        }
      %Trie.union_assoc(~ty, ~join, ~assoc, o1, o2, o3):
        {
          Bin{
            Shared.Maybe.join(~ty, ~join, Shared.Maybe.join(~ty, ~join, h1, h2), h3),
            Trie.union(~ty, ~join, Trie.union(~ty, ~join, z1, z2), z3),
            Trie.union(~ty, ~join, Trie.union(~ty, ~join, o1, o2), o3)
          }
            == Bin{
              Shared.Maybe.join(~ty, ~join, Shared.Maybe.join(~ty, ~join, h1, h2), h3),
              Trie.union(~ty, ~join, Trie.union(~ty, ~join, z1, z2), z3),
              _
            }: Trie<ty>
        }
      {==}

# a trie joined with itself is itself
law Trie.union_idem:
  for ~V: Data
  for ~join: V -> V -> V
  for ~idem: @x: V -> {join(x, x) == x: V}
  for a: Trie<V>
  {Trie.union(~V, ~join, a, a) == a: Trie<V>}

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
def Trie.union_idem(ty, join, idem, a):
  match a:
    case Tip{}:
      {==}
    case Bin{h, +z, +o}:
      union1 = Trie.union(~ty, ~join, o, o)
      union2 = Trie.union(~ty, ~join, z, z)
      %Equal.sym(
        Maybe<&2, ty>,
        Shared.Maybe.join(~ty, ~join, h, h),
        h,
        Shared.Maybe.join_idem(~ty, ~join, ~idem, h)
      ):
        {Bin{_, union2, union1} == Bin{h, z, o}: Trie<ty>}
      %Equal.sym(Trie<ty>, union2, z, Trie.union_idem(~ty, ~join, ~idem, z)):
        {Bin{h, _, union1} == Bin{h, z, o}: Trie<ty>}
      %Equal.sym(
        Trie<ty>,
        union1,
        o,
        Trie.union_idem(~ty, ~join, ~idem, o)
      ): {Bin{h, z, _} == Bin{h, z, o}: Trie<ty>}
      {==}
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Trie.pick_minus once same(x, y) is known (held)
def Trie.pick_minus.if(
  ~V: Data,
  ~join: V -> V -> V,
  ~same: V -> V -> Bool,
  ~idem: @x: V -> {join(x, x) == x: V},
  ~laws: Shared.Eq.Laws(V, same),
  held: Bool,
  x: V,
  +y: V,
  e: {same(x, y) == held: Bool}
) -> {
  Shared.Maybe.join(
    ~V,
    ~join,
    Some{y},
    Bool.pick(Maybe<&2, V>, held, None{}, Some{x})
  )
    == Some{join(y, x)}: Maybe<&2, V>
}:
  match held:
    case True{}:
      %Equal.sym(
        V,
        x,
        y,
        Shared.Eq.sound(~V, ~same, laws, x)(y)(e)
      ): {Some{y} == Some{join(y, _)}: Maybe<&2, V>}
      %Equal.sym(V, join(y, y), y, idem(y)): {Some{y} == Some{_}: Maybe<&2, V>}
      {==}
    case False{}:
      {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# what r holds for a key, joined with what r lacks of s there, is r's joined
# with s's
def Trie.pick_minus(
  ~V: Data,
  ~join: V -> V -> V,
  ~same: V -> V -> Bool,
  ~idem: @x: V -> {join(x, x) == x: V},
  ~laws: Shared.Eq.Laws(V, same),
  s: Maybe<&2, V>,
  r: Maybe<&2, V>
) -> {
  Shared.Maybe.join(
    ~V,
    ~join,
    r,
    Trie.minus.here(~V, ~same, s, r)
  )
    == Shared.Maybe.join(~V, ~join, r, s): Maybe<&2, V>
}:
  match s r:
    case None{} y:
      {==}
    case Some{x} None{}:
      {==}
    case Some{+x} Some{+y}:
      Trie.pick_minus.if(~V, ~join, ~same, ~idem, ~laws, same(x, y), x, y, {==})

# taking in what r lacks of s is taking in s: a sync may send only that
law Trie.union_minus:
  for ~V: Data
  for ~join: V -> V -> V
  for ~same: V -> V -> Bool
  for ~idem: @x: V -> {join(x, x) == x: V}
  for ~laws: Shared.Eq.Laws(V, same)
  for s: Trie<V>
  for r: Trie<V>
  {Trie.union(~V, ~join, r, Trie.minus(~V, ~same, s, r)) == Trie.union(~V, ~join, r, s): Trie<V>}

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
def Trie.union_minus(ty, join, same, idem, laws, s, r):
  match s r:
    case Tip{} y:
      {==}
    case Bin{+h, +z, +o} Tip{}:
      {==}
    case Bin{h1, z1, o1} Bin{+h2, +z2, +o2}:
      pick1 = Shared.Maybe.join(~ty, ~join, h2, Trie.minus.here(~ty, ~same, h1, h2))
      union1 = Trie.union(~ty, ~join, z2, Trie.minus(~ty, ~same, z1, z2))
      union2 = Trie.union(~ty, ~join, o2, Trie.minus(~ty, ~same, o1, o2))
      union3 = Trie.union(~ty, ~join, o2, o1)
      %Trie.pick_minus(~ty, ~join, ~same, ~idem, ~laws, h1, h2):
        {Bin{pick1, union1, union2} == Bin{_, Trie.union(~ty, ~join, z2, z1), union3}: Trie<ty>}
      %Trie.union_minus(~ty, ~join, ~same, ~idem, ~laws, z1, z2):
        {Bin{pick1, union1, union2} == Bin{pick1, _, union3}: Trie<ty>}
      %Trie.union_minus(~ty, ~join, ~same, ~idem, ~laws, o1, o2):
        {Bin{pick1, union1, union2} == Bin{pick1, union1, _}: Trie<ty>}
      {==}
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# Sizes and keys apart
# --------------------

# k and p differ at some bit that both have
def Trie.apart(k: List<&2, Bool>, p: List<&2, Bool>) -> Bool:
  match k p:
    case Con{False{}, r} Con{False{}, q}:
      Trie.apart(r, q)
    case Con{True{}, r} Con{True{}, q}:
      Trie.apart(r, q)
    case Con{False{}, r} Con{True{}, q}:
      True{}
    case Con{True{}, r} Con{False{}, q}:
      True{}
    case _ _:
      False{}

# a trie joined with nothing is itself
def Trie.union_tip(
  ~V: Data,
  ~join: V -> V -> V,
  a: Trie<V>
) -> {Trie.union(~V, ~join, a, Tip{}) == a: Trie<V>}:
  match a:
    case Tip{}:
      {==}
    case Bin{h, z, o}:
      {==}

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# the trie of one key holds nothing at a key apart from it
def Trie.get_one_apart(
  -V: Data,
  k: List<&2, Bool>,
  p: List<&2, Bool>,
  v: V
) -> {
  Trie.apart(k, p) == True{}: Bool
} -> {Trie.get(V, Trie.one(V, k, v), p) == None{}: Maybe<&2, V>}:
  match k p:
    case Con{False{}, r} Con{False{}, q}:
      Trie.get_one_apart(V, r, q, v)
    case Con{True{}, r} Con{True{}, q}:
      Trie.get_one_apart(V, r, q, v)
    case Con{False{}, r} Con{True{}, q}:
      h => {==}
    case Con{True{}, r} Con{False{}, q}:
      h => {==}
    case Nil{} q:
      h => Empty.absurd(
        {Trie.get(V, Trie.one(V, Nil{}, v), q) == None{}: Maybe<&2, V>},
        Shared.Bool.false_ne_true(h)
      )
    case Con{b, r} Nil{}:
      h => Empty.absurd(
        {Trie.get(V, Trie.one(V, b <> r, v), Nil{}) == None{}: Maybe<&2, V>},
        Shared.Bool.false_ne_true(h)
      )
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# a key apart from k keeps its entries when one entry at k joins
law Trie.under_union_apart:
  for ~V: Data
  for ~join: V -> V -> V
  for s: Trie<V>
  for k: List<&2, Bool>
  for p: List<&2, Bool>
  for +v: V
  {Trie.apart(k, p) == True{}: Bool}
    -> {
      Trie.under(V, Trie.union(~V, ~join, s, Trie.one(V, k, v)), p) == Trie.under(V, s, p): Trie<V>
    }

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
def Trie.under_union_apart(ty, join, s, k, p, v):
  match s k p:
    case Tip{} Con{False{}, r} Con{False{}, q}:
      Trie.under_union_apart(~ty, ~join, Tip{}, r, q, v)
    case Tip{} Con{True{}, r} Con{True{}, q}:
      Trie.under_union_apart(~ty, ~join, Tip{}, r, q, v)
    case Tip{} Con{False{}, r} Con{True{}, q}:
      h => {==}
    case Tip{} Con{True{}, r} Con{False{}, q}:
      h => {==}
    case Bin{h, z, o} Con{False{}, r} Con{False{}, q}:
      Trie.under_union_apart(~ty, ~join, z, r, q, v)
    case Bin{h, z, +o} Con{False{}, r} Con{True{}, q}:
      e =>
        %Equal.sym(Trie<ty>, Trie.union(~ty, ~join, o, Tip{}), o, Trie.union_tip(~ty, ~join, o)):
          {Trie.under(ty, _, q) == Trie.under(ty, o, q): Trie<ty>}
        {==}
    case Bin{h, +z, o} Con{True{}, r} Con{False{}, q}:
      e =>
        %Equal.sym(Trie<ty>, Trie.union(~ty, ~join, z, Tip{}), z, Trie.union_tip(~ty, ~join, z)):
          {Trie.under(ty, _, q) == Trie.under(ty, z, q): Trie<ty>}
        {==}
    case Bin{h, z, o} Con{True{}, r} Con{True{}, q}:
      Trie.under_union_apart(~ty, ~join, o, r, q, v)
    case w Nil{} q:
      e => Empty.absurd(
        {
          Trie.under(
            ty,
            Trie.union(~ty, ~join, w, Trie.one(ty, Nil{}, v)),
            q
          )
            == Trie.under(ty, w, q): Trie<ty>
        },
        Shared.Bool.false_ne_true(e)
      )
    case w Con{b, r} Nil{}:
      e => Empty.absurd(
        {
          Trie.under(
            ty,
            Trie.union(~ty, ~join, w, Trie.one(ty, b <> r, v)),
            Nil{}
          )
            == Trie.under(ty, w, Nil{}): Trie<ty>
        },
        Shared.Bool.false_ne_true(e)
      )
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# a union holds at least the entries of its first side
law Trie.size_union:
  for ~V: Data
  for ~join: V -> V -> V
  for a: Trie<V>
  for b: Trie<V>
  {Nat.is_le(Trie.size(V, a), Trie.size(V, Trie.union(~V, ~join, a, b))) == True{}: Bool}

# bend-lint: expect-begin bend-lint-rules/performance/missed_fork@hint -- a proof does not run
def Trie.size_union(ty, join, a, b):
  match a b:
    case Tip{} y:
      Shared.Nat.le_zero(Trie.size(ty, y))
    case Bin{h, z, o} Tip{}:
      Shared.Nat.le_refl(Trie.size(ty, Bin{h, z, o}))
    case Bin{None{}, +z1, +o1} Bin{None{}, +z2, +o2}:
      Shared.Nat.add_le(
        Trie.size(ty, z1),
        Trie.size(ty, Trie.union(~ty, ~join, z1, z2)),
        Trie.size(ty, o1),
        Trie.size(ty, Trie.union(~ty, ~join, o1, o2))
      )(Trie.size_union(~ty, ~join, z1, z2))(Trie.size_union(~ty, ~join, o1, o2))
    case Bin{None{}, +z1, +o1} Bin{Some{y}, +z2, +o2}:
      +size1 = Trie.size(ty, Trie.union(~ty, ~join, z1, z2))
      +size2 = Trie.size(ty, Trie.union(~ty, ~join, o1, o2))
      Shared.Nat.le_succ(
        Nat.add(Trie.size(ty, z1), Trie.size(ty, o1)),
        Nat.add(size1, size2)
      )(
        Shared.Nat.add_le(
          Trie.size(ty, z1),
          size1,
          Trie.size(ty, o1),
          size2
        )(Trie.size_union(~ty, ~join, z1, z2))(Trie.size_union(~ty, ~join, o1, o2))
      )
    case Bin{Some{x}, +z1, +o1} Bin{None{}, +z2, +o2}:
      Shared.Nat.add_le(
        Trie.size(ty, z1),
        Trie.size(ty, Trie.union(~ty, ~join, z1, z2)),
        Trie.size(ty, o1),
        Trie.size(ty, Trie.union(~ty, ~join, o1, o2))
      )(Trie.size_union(~ty, ~join, z1, z2))(Trie.size_union(~ty, ~join, o1, o2))
    case Bin{Some{x}, +z1, +o1} Bin{Some{y}, +z2, +o2}:
      Shared.Nat.add_le(
        Trie.size(ty, z1),
        Trie.size(ty, Trie.union(~ty, ~join, z1, z2)),
        Trie.size(ty, o1),
        Trie.size(ty, Trie.union(~ty, ~join, o1, o2))
      )(Trie.size_union(~ty, ~join, z1, z2))(Trie.size_union(~ty, ~join, o1, o2))
# bend-lint: expect-end bend-lint-rules/performance/missed_fork@hint

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# the trie of one key has one entry
def Trie.size_one(
  -V: Data,
  k: List<&2, Bool>,
  v: V
) -> {Trie.size(V, Trie.one(V, k, v)) == 1n: Nat}:
  match k:
    case Nil{}:
      {==}
    case Con{False{}, r}:
      %Equal.sym(
        Nat,
        Trie.size(V, Trie.one(V, r, v)),
        1n,
        Trie.size_one(V, r, v)
      ): {Nat.add(_, 0n) == 1n: Nat}
      {==}
    case Con{True{}, r}:
      %Equal.sym(
        Nat,
        Trie.size(V, Trie.one(V, r, v)),
        1n,
        Trie.size_one(V, r, v)
      ): {Nat.add(0n, _) == 1n: Nat}
      {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# one entry at a key that s does not hold adds one entry
law Trie.size_union_one:
  for ~V: Data
  for ~join: V -> V -> V
  for s: Trie<V>
  for k: List<&2, Bool>
  for +v: V
  {Trie.get(V, s, k) == None{}: Maybe<&2, V>}
    -> {Trie.size(V, Trie.union(~V, ~join, s, Trie.one(V, k, v))) == 1n+Trie.size(V, s): Nat}

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
def Trie.size_union_one(ty, join, s, k, v):
  match s k:
    case Tip{} q:
      g => Trie.size_one(ty, q, v)
    case Bin{None{}, +z, +o} Nil{}:
      g =>
        +add1 = Nat.add(Trie.size(ty, z), Trie.size(ty, o))
        +union1 = Trie.union(~ty, ~join, o, Tip{})
        %Equal.sym(Trie<ty>, Trie.union(~ty, ~join, z, Tip{}), z, Trie.union_tip(~ty, ~join, z)):
          {1n+Nat.add(Trie.size(ty, _), Trie.size(ty, union1)) == 1n+add1: Nat}
        %Equal.sym(Trie<ty>, union1, o, Trie.union_tip(~ty, ~join, o)):
          {1n+Nat.add(Trie.size(ty, z), Trie.size(ty, _)) == 1n+add1: Nat}
        {==}
    case Bin{Some{y}, z, o} Nil{}:
      g => Empty.absurd(
        {
          Trie.size(
            ty,
            Trie.union(~ty, ~join, Bin{Some{y}, z, o}, Trie.one(ty, Nil{}, v))
          )
            == 1n+Trie.size(ty, Bin{Some{y}, z, o}): Nat
        },
        Shared.Bool.false_ne_true(
          Equal.cong(
            Maybe<&2, ty>,
            Bool,
            m => Maybe.is_some(&2, ty, m),
            None{},
            Some{y},
            Equal.sym(Maybe<&2, ty>, Some{y}, None{}, g)
          )
        )
      )
    case Bin{None{}, +z, +o} Con{False{}, +r}:
      g =>
        +size1 = Trie.size(ty, Trie.union(~ty, ~join, z, Trie.one(ty, r, v)))
        +add1 = Nat.add(Trie.size(ty, z), Trie.size(ty, o))
        %Equal.sym(Trie<ty>, Trie.union(~ty, ~join, o, Tip{}), o, Trie.union_tip(~ty, ~join, o)):
          {Nat.add(size1, Trie.size(ty, _)) == 1n+add1: Nat}
        %Equal.sym(Nat, size1, 1n+Trie.size(ty, z), Trie.size_union_one(~ty, ~join, z, r, v)(g)):
          {Nat.add(_, Trie.size(ty, o)) == 1n+add1: Nat}
        {==}
    case Bin{Some{y}, +z, +o} Con{False{}, +r}:
      g =>
        +size1 = Trie.size(ty, Trie.union(~ty, ~join, z, Trie.one(ty, r, v)))
        +add1 = Nat.add(Trie.size(ty, z), Trie.size(ty, o))
        %Equal.sym(Trie<ty>, Trie.union(~ty, ~join, o, Tip{}), o, Trie.union_tip(~ty, ~join, o)):
          {1n+Nat.add(size1, Trie.size(ty, _)) == 1n+1n+add1: Nat}
        %Equal.sym(Nat, size1, 1n+Trie.size(ty, z), Trie.size_union_one(~ty, ~join, z, r, v)(g)):
          {1n+Nat.add(_, Trie.size(ty, o)) == 1n+1n+add1: Nat}
        {==}
    case Bin{None{}, +z, +o} Con{True{}, +r}:
      g =>
        +size1 = Trie.size(ty, Trie.union(~ty, ~join, o, Trie.one(ty, r, v)))
        +add1 = Nat.add(Trie.size(ty, z), Trie.size(ty, o))
        %Equal.sym(Trie<ty>, Trie.union(~ty, ~join, z, Tip{}), z, Trie.union_tip(~ty, ~join, z)):
          {Nat.add(Trie.size(ty, _), size1) == 1n+add1: Nat}
        %Equal.sym(Nat, size1, 1n+Trie.size(ty, o), Trie.size_union_one(~ty, ~join, o, r, v)(g)):
          {Nat.add(Trie.size(ty, z), _) == 1n+add1: Nat}
        Shared.Nat.add_succ(Trie.size(ty, z), Trie.size(ty, o))
    case Bin{Some{y}, +z, +o} Con{True{}, +r}:
      g =>
        +add1 = Nat.add(Trie.size(ty, z), Trie.size(ty, o))
        +size1 = Trie.size(ty, Trie.union(~ty, ~join, o, Trie.one(ty, r, v)))
        %Equal.sym(Trie<ty>, Trie.union(~ty, ~join, z, Tip{}), z, Trie.union_tip(~ty, ~join, z)):
          {1n+Nat.add(Trie.size(ty, _), size1) == 1n+1n+add1: Nat}
        %Equal.sym(Nat, size1, 1n+Trie.size(ty, o), Trie.size_union_one(~ty, ~join, o, r, v)(g)):
          {1n+Nat.add(Trie.size(ty, z), _) == 1n+1n+add1: Nat}
        %Equal.sym(
          Nat,
          Nat.add(Trie.size(ty, z), 1n+Trie.size(ty, o)),
          1n+add1,
          Shared.Nat.add_succ(Trie.size(ty, z), Trie.size(ty, o))
        ):
          {1n+_ == 1n+1n+add1: Nat}
        {==}
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# the entries under p of a union are the union of the entries under p
def Trie.under_union(
  ~V: Data,
  ~join: V -> V -> V,
  a: Trie<V>,
  b: Trie<V>,
  p: List<&2, Bool>
) -> {
  Trie.under(
    V,
    Trie.union(~V, ~join, a, b),
    p
  )
    == Trie.union(~V, ~join, Trie.under(V, a, p), Trie.under(V, b, p)): Trie<V>
}:
  match a b p:
    case Tip{} y q:
      {==}
    case Bin{h, z, o} Tip{} q:
      under1 = Trie.under(V, Bin{h, z, o}, q)
      Equal.sym(
        Trie<V>,
        Trie.union(~V, ~join, under1, Tip{}),
        under1,
        Trie.union_tip(~V, ~join, under1)
      )
    case Bin{h1, z1, o1} Bin{h2, z2, o2} Nil{}:
      {==}
    case Bin{h1, z1, o1} Bin{h2, z2, o2} Con{False{}, r}:
      Trie.under_union(~V, ~join, z1, z2, r)
    case Bin{h1, z1, o1} Bin{h2, z2, o2} Con{True{}, r}:
      Trie.under_union(~V, ~join, o1, o2, r)
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# a key under p is the key after p
def Trie.get_under(
  -V: Data,
  t: Trie<V>,
  p: List<&2, Bool>,
  r: List<&2, Bool>
) -> {
  Trie.get(V, Trie.under(V, t, p), r) == Trie.get(V, t, List.append(&2, Bool, p, r)): Maybe<&2, V>
}:
  match t p:
    case Tip{} q:
      {==}
    case Bin{h, z, o} Nil{}:
      {==}
    case Bin{h, z, o} Con{False{}, q}:
      Trie.get_under(V, z, q, r)
    case Bin{h, z, o} Con{True{}, q}:
      Trie.get_under(V, o, q, r)

# the entries under no key are all the entries
def Trie.under_all(-V: Data, t: Trie<V>) -> {Trie.under(V, t, []) == t: Trie<V>}:
  match t:
    case Tip{}:
      {==}
    case Bin{h, z, o}:
      {==}

# the entries under p of the trie of one key after p are the trie of the rest
def Trie.under_one(
  -V: Data,
  p: List<&2, Bool>,
  r: List<&2, Bool>,
  v: V
) -> {Trie.under(V, Trie.one(V, List.append(&2, Bool, p, r), v), p) == Trie.one(V, r, v): Trie<V>}:
  match p:
    case Nil{}:
      Trie.under_all(V, Trie.one(V, r, v))
    case Con{False{}, q}:
      Trie.under_one(V, q, r, v)
    case Con{True{}, q}:
      Trie.under_one(V, q, r, v)

# Relations
# ---------
# A check that holds at each key of one trie, or between what two tries hold
# at each key, is a check of the tries: what it says of every key follows
# (Trie.all_get, Trie.all2_get), and it lasts below a key (Trie.all_under,
# Trie.all2_under).

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a check, or a proof, keeps each and as one value for the proofs to split on
# bend-lint: expect-begin bend-lint-rules/performance/missed_fork@hint -- a proof does not run, so it gains nothing from a fork

# p holds of what t holds at each key
def Trie.all(~V: Data, ~p: Maybe<&2, V> -> Bool, t: Trie<V>) -> Bool:
  match t:
    case Tip{}:
      True{}
    case Bin{h, z, o}:
      Bool.and(p(h), Bool.and(Trie.all(~V, ~p, z), Trie.all(~V, ~p, o)))

# r holds of what a and b hold at each key: r is True of no entry of a and
# any of b, and left checks a below a key where b holds nothing (left(t) says
# that r holds of each entry of t and no entry, in one step when it needs no
# walk)
def Trie.all2(
  ~V: Data,
  ~W: Data,
  ~r: Maybe<&2, V> -> Maybe<&2, W> -> Bool,
  ~left: Trie<V> -> Bool,
  a: Trie<V>,
  b: Trie<W>
) -> Bool:
  match a b:
    case Tip{} y:
      True{}
    case Bin{h, z, o} Tip{}:
      left(Bin{h, z, o})
    case Bin{h1, z1, o1} Bin{h2, z2, o2}:
      Bool.and(
        r(h1, h2),
        Bool.and(Trie.all2(~V, ~W, ~r, ~left, z1, z2), Trie.all2(~V, ~W, ~r, ~left, o1, o2))
      )

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# p holds at every key of t, when it holds of no entry
def Trie.all_get(
  ~V: Data,
  ~p: Maybe<&2, V> -> Bool,
  pn: {p(None{}) == True{}: Bool},
  t: Trie<V>,
  k: List<&2, Bool>
) -> {Trie.all(~V, ~p, t) == True{}: Bool} -> {p(Trie.get(V, t, k)) == True{}: Bool}:
  match t k:
    case Tip{} q:
      e => pn
    case Bin{h, +z, +o} Nil{}:
      e => Shared.Bool.and_true_left(p(h), Bool.and(Trie.all(~V, ~p, z), Trie.all(~V, ~p, o)))(e)
    case Bin{+h, +z, +o} Con{False{}, q}:
      e => Trie.all_get(
        ~V,
        ~p,
        pn,
        z,
        q
      )(
        Shared.Bool.and_true_left(
          Trie.all(~V, ~p, z),
          Trie.all(~V, ~p, o)
        )(Shared.Bool.and_true_right(p(h), Bool.and(Trie.all(~V, ~p, z), Trie.all(~V, ~p, o)))(e))
      )
    case Bin{+h, +z, +o} Con{True{}, q}:
      e => Trie.all_get(
        ~V,
        ~p,
        pn,
        o,
        q
      )(
        Shared.Bool.and_true_right(
          Trie.all(~V, ~p, z),
          Trie.all(~V, ~p, o)
        )(Shared.Bool.and_true_right(p(h), Bool.and(Trie.all(~V, ~p, z), Trie.all(~V, ~p, o)))(e))
      )

# p holds below any key of t where it holds of t
def Trie.all_under(
  ~V: Data,
  ~p: Maybe<&2, V> -> Bool,
  t: Trie<V>,
  k: List<&2, Bool>
) -> {
  Trie.all(~V, ~p, t) == True{}: Bool
} -> {Trie.all(~V, ~p, Trie.under(V, t, k)) == True{}: Bool}:
  match t k:
    case Tip{} q:
      e => {==}
    case Bin{h, z, o} Nil{}:
      e => e
    case Bin{+h, +z, +o} Con{False{}, q}:
      e => Trie.all_under(
        ~V,
        ~p,
        z,
        q
      )(
        Shared.Bool.and_true_left(
          Trie.all(~V, ~p, z),
          Trie.all(~V, ~p, o)
        )(Shared.Bool.and_true_right(p(h), Bool.and(Trie.all(~V, ~p, z), Trie.all(~V, ~p, o)))(e))
      )
    case Bin{+h, +z, +o} Con{True{}, q}:
      e => Trie.all_under(
        ~V,
        ~p,
        o,
        q
      )(
        Shared.Bool.and_true_right(
          Trie.all(~V, ~p, z),
          Trie.all(~V, ~p, o)
        )(Shared.Bool.and_true_right(p(h), Bool.and(Trie.all(~V, ~p, z), Trie.all(~V, ~p, o)))(e))
      )

# a trie where p holds only of no entry is empty
def Trie.all_size(
  ~V: Data,
  ~p: Maybe<&2, V> -> Bool,
  ~pn: @m: Maybe<&2, V> -> {p(m) == True{}: Bool} -> {Maybe.is_none(&2, V, m) == True{}: Bool},
  t: Trie<V>
) -> {Trie.all(~V, ~p, t) == True{}: Bool} -> {Trie.size(V, t) == 0n: Nat}:
  match t:
    case Tip{}:
      e => {==}
    case Bin{None{}, +z, +o}:
      +e =>
        +rest = Shared.Bool.and_true_right(
          p(None{}),
          Bool.and(Trie.all(~V, ~p, z), Trie.all(~V, ~p, o))
        )(e)
        %Equal.sym(
          Nat,
          Trie.size(V, z),
          0n,
          Trie.all_size(
            ~V,
            ~p,
            ~pn,
            z
          )(Shared.Bool.and_true_left(Trie.all(~V, ~p, z), Trie.all(~V, ~p, o))(rest))
        ): {Nat.add(_, Trie.size(V, o)) == 0n: Nat}
        %Equal.sym(
          Nat,
          Trie.size(V, o),
          0n,
          Trie.all_size(
            ~V,
            ~p,
            ~pn,
            o
          )(Shared.Bool.and_true_right(Trie.all(~V, ~p, z), Trie.all(~V, ~p, o))(rest))
        ): {Nat.add(0n, _) == 0n: Nat}
        {==}
    case Bin{Some{+c}, +z, +o}:
      e => Empty.absurd(
        {Trie.size(V, Bin{Some{c}, z, o}) == 0n: Nat},
        Shared.Bool.false_ne_true(
          pn(
            Some{c}
          )(
            Shared.Bool.and_true_left(
              p(Some{c}),
              Bool.and(Trie.all(~V, ~p, z), Trie.all(~V, ~p, o))
            )(e)
          )
        )
      )

# r holds at every key of a and b
law Trie.all2_get:
  for ~V: Data
  for ~W: Data
  for ~r: Maybe<&2, V> -> Maybe<&2, W> -> Bool
  for ~left: Trie<V> -> Bool
  for ~rn: @y: Maybe<&2, W> -> {r(None{}, y) == True{}: Bool}
  for ~lget: @t: Trie<
    V> -> @k: List<
    &2,
    Bool> -> {left(t) == True{}: Bool} -> {r(Trie.get(V, t, k), None{}) == True{}: Bool}
  for a: Trie<V>
  for b: Trie<W>
  for k: List<&2, Bool>
  {Trie.all2(~V, ~W, ~r, ~left, a, b) == True{}: Bool}
    -> {r(Trie.get(V, a, k), Trie.get(W, b, k)) == True{}: Bool}

def Trie.all2_get(tv, tw, r, left, rn, lget, a, b, k):
  match a b k:
    case Tip{} y q:
      e => rn(Trie.get(tw, y, q))
    case Bin{h, z, o} Tip{} q:
      e => lget(Bin{h, z, o})(q)(e)
    case Bin{+h1, +z1, +o1} Bin{h2, +z2, +o2} Nil{}:
      e => Shared.Bool.and_true_left(
        r(h1, h2),
        Bool.and(Trie.all2(~tv, ~tw, ~r, ~left, z1, z2), Trie.all2(~tv, ~tw, ~r, ~left, o1, o2))
      )(e)
    case Bin{+h1, +z1, +o1} Bin{+h2, +z2, +o2} Con{False{}, q}:
      e => Trie.all2_get(
        ~tv,
        ~tw,
        ~r,
        ~left,
        ~rn,
        ~lget,
        z1,
        z2,
        q
      )(
        Shared.Bool.and_true_left(
          Trie.all2(~tv, ~tw, ~r, ~left, z1, z2),
          Trie.all2(~tv, ~tw, ~r, ~left, o1, o2)
        )(
          Shared.Bool.and_true_right(
            r(h1, h2),
            Bool.and(Trie.all2(~tv, ~tw, ~r, ~left, z1, z2), Trie.all2(~tv, ~tw, ~r, ~left, o1, o2))
          )(e)
        )
      )
    case Bin{+h1, +z1, +o1} Bin{+h2, +z2, +o2} Con{True{}, q}:
      e => Trie.all2_get(
        ~tv,
        ~tw,
        ~r,
        ~left,
        ~rn,
        ~lget,
        o1,
        o2,
        q
      )(
        Shared.Bool.and_true_right(
          Trie.all2(~tv, ~tw, ~r, ~left, z1, z2),
          Trie.all2(~tv, ~tw, ~r, ~left, o1, o2)
        )(
          Shared.Bool.and_true_right(
            r(h1, h2),
            Bool.and(Trie.all2(~tv, ~tw, ~r, ~left, z1, z2), Trie.all2(~tv, ~tw, ~r, ~left, o1, o2))
          )(e)
        )
      )

# r holds below any key of a and b where it holds of a and b
law Trie.all2_under:
  for ~V: Data
  for ~W: Data
  for ~r: Maybe<&2, V> -> Maybe<&2, W> -> Bool
  for ~left: Trie<V> -> Bool
  for ~lunder: @t: Trie<
    V> -> @k: List<
    &2,
    Bool> -> {
    left(t) == True{}: Bool
  } -> {Trie.all2(~V, ~W, ~r, ~left, Trie.under(V, t, k), Tip{}) == True{}: Bool}
  for a: Trie<V>
  for b: Trie<W>
  for +k: List<&2, Bool>
  {Trie.all2(~V, ~W, ~r, ~left, a, b) == True{}: Bool}
    -> {Trie.all2(~V, ~W, ~r, ~left, Trie.under(V, a, k), Trie.under(W, b, k)) == True{}: Bool}

def Trie.all2_under(tv, tw, r, left, lunder, a, b, k):
  match a b k:
    case Tip{} y q:
      e => {==}
    case Bin{h, z, o} Tip{} q:
      e => lunder(Bin{h, z, o})(q)(e)
    case Bin{h1, z1, o1} Bin{h2, z2, o2} Nil{}:
      e => e
    case Bin{+h1, +z1, +o1} Bin{+h2, +z2, +o2} Con{False{}, q}:
      e => Trie.all2_under(
        ~tv,
        ~tw,
        ~r,
        ~left,
        ~lunder,
        z1,
        z2,
        q
      )(
        Shared.Bool.and_true_left(
          Trie.all2(~tv, ~tw, ~r, ~left, z1, z2),
          Trie.all2(~tv, ~tw, ~r, ~left, o1, o2)
        )(
          Shared.Bool.and_true_right(
            r(h1, h2),
            Bool.and(Trie.all2(~tv, ~tw, ~r, ~left, z1, z2), Trie.all2(~tv, ~tw, ~r, ~left, o1, o2))
          )(e)
        )
      )
    case Bin{+h1, +z1, +o1} Bin{+h2, +z2, +o2} Con{True{}, q}:
      e => Trie.all2_under(
        ~tv,
        ~tw,
        ~r,
        ~left,
        ~lunder,
        o1,
        o2,
        q
      )(
        Shared.Bool.and_true_right(
          Trie.all2(~tv, ~tw, ~r, ~left, z1, z2),
          Trie.all2(~tv, ~tw, ~r, ~left, o1, o2)
        )(
          Shared.Bool.and_true_right(
            r(h1, h2),
            Bool.and(Trie.all2(~tv, ~tw, ~r, ~left, z1, z2), Trie.all2(~tv, ~tw, ~r, ~left, o1, o2))
          )(e)
        )
      )
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# r holds of a trie and itself, when it holds of each entry and itself
def Trie.all2_refl(
  ~V: Data,
  ~r: Maybe<&2, V> -> Maybe<&2, V> -> Bool,
  ~left: Trie<V> -> Bool,
  ~rrefl: @m: Maybe<&2, V> -> {r(m, m) == True{}: Bool},
  a: Trie<V>
) -> {Trie.all2(~V, ~V, ~r, ~left, a, a) == True{}: Bool}:
  match a:
    case Tip{}:
      {==}
    case Bin{+h, +z, +o}:
      Shared.Bool.and_both(
        r(h, h),
        Bool.and(Trie.all2(~V, ~V, ~r, ~left, z, z), Trie.all2(~V, ~V, ~r, ~left, o, o))
      )(
        rrefl(h)
      )(
        Shared.Bool.and_both(
          Trie.all2(~V, ~V, ~r, ~left, z, z),
          Trie.all2(~V, ~V, ~r, ~left, o, o)
        )(Trie.all2_refl(~V, ~r, ~left, ~rrefl, z))(Trie.all2_refl(~V, ~r, ~left, ~rrefl, o))
      )

# r holds of s and its union with t, when q holds of s and t and each entry
# that q holds of keeps r with its join
law Trie.all2_join:
  for ~V: Data
  for ~join: V -> V -> V
  for ~q: Maybe<&2, V> -> Maybe<&2, V> -> Bool
  for ~lq: Trie<V> -> Bool
  for ~r: Maybe<&2, V> -> Maybe<&2, V> -> Bool
  for ~lr: Trie<V> -> Bool
  for ~step: @a: Maybe<
    &2,
    V> -> @b: Maybe<
    &2,
    V> -> {q(a, b) == True{}: Bool} -> {r(a, Shared.Maybe.join(~V, ~join, a, b)) == True{}: Bool}
  for ~rrefl: @m: Maybe<&2, V> -> {r(m, m) == True{}: Bool}
  for s: Trie<V>
  for t: Trie<V>
  {Trie.all2(~V, ~V, ~q, ~lq, s, t) == True{}: Bool}
    -> {Trie.all2(~V, ~V, ~r, ~lr, s, Trie.union(~V, ~join, s, t)) == True{}: Bool}

def Trie.all2_join(ty, join, q, lq, r, lr, step, rrefl, s, t):
  match s t:
    case Tip{} y:
      e => {==}
    case Bin{h, z, o} Tip{}:
      e => Trie.all2_refl(~ty, ~r, ~lr, ~rrefl, Bin{h, z, o})
    case Bin{+h1, +z1, +o1} Bin{+h2, +z2, +o2}:
      +e =>
        +rest = Shared.Bool.and_true_right(
          q(h1, h2),
          Bool.and(Trie.all2(~ty, ~ty, ~q, ~lq, z1, z2), Trie.all2(~ty, ~ty, ~q, ~lq, o1, o2))
        )(e)
        Shared.Bool.and_both(
          r(h1, Shared.Maybe.join(~ty, ~join, h1, h2)),
          Bool.and(
            Trie.all2(~ty, ~ty, ~r, ~lr, z1, Trie.union(~ty, ~join, z1, z2)),
            Trie.all2(~ty, ~ty, ~r, ~lr, o1, Trie.union(~ty, ~join, o1, o2))
          )
        )(
          step(
            h1
          )(
            h2
          )(
            Shared.Bool.and_true_left(
              q(h1, h2),
              Bool.and(Trie.all2(~ty, ~ty, ~q, ~lq, z1, z2), Trie.all2(~ty, ~ty, ~q, ~lq, o1, o2))
            )(e)
          )
        )(
          Shared.Bool.and_both(
            Trie.all2(~ty, ~ty, ~r, ~lr, z1, Trie.union(~ty, ~join, z1, z2)),
            Trie.all2(~ty, ~ty, ~r, ~lr, o1, Trie.union(~ty, ~join, o1, o2))
          )(
            Trie.all2_join(
              ~ty,
              ~join,
              ~q,
              ~lq,
              ~r,
              ~lr,
              ~step,
              ~rrefl,
              z1,
              z2
            )(
              Shared.Bool.and_true_left(
                Trie.all2(~ty, ~ty, ~q, ~lq, z1, z2),
                Trie.all2(~ty, ~ty, ~q, ~lq, o1, o2)
              )(rest)
            )
          )(
            Trie.all2_join(
              ~ty,
              ~join,
              ~q,
              ~lq,
              ~r,
              ~lr,
              ~step,
              ~rrefl,
              o1,
              o2
            )(
              Shared.Bool.and_true_right(
                Trie.all2(~ty, ~ty, ~q, ~lq, z1, z2),
                Trie.all2(~ty, ~ty, ~q, ~lq, o1, o2)
              )(rest)
            )
          )
        )

# r holds of a and the empty trie, when left holds of every trie
def Trie.all2_tip(
  ~V: Data,
  ~W: Data,
  ~r: Maybe<&2, V> -> Maybe<&2, W> -> Bool,
  ~left: Trie<V> -> Bool,
  ~ltrue: @t: Trie<V> -> {left(t) == True{}: Bool},
  a: Trie<V>
) -> {Trie.all2(~V, ~W, ~r, ~left, a, Tip{}) == True{}: Bool}:
  match a:
    case Tip{}:
      {==}
    case Bin{h, z, o}:
      ltrue(Bin{h, z, o})

# one entry at a key that s does not hold: r holds of s and it, when r holds
# of no entry of either side, and left of every trie
law Trie.all2_one:
  for ~V: Data
  for ~r: Maybe<&2, V> -> Maybe<&2, V> -> Bool
  for ~left: Trie<V> -> Bool
  for ~rn: @y: Maybe<&2, V> -> {r(None{}, y) == True{}: Bool}
  for ~rl: @a: Maybe<&2, V> -> {r(a, None{}) == True{}: Bool}
  for ~ltrue: @t: Trie<V> -> {left(t) == True{}: Bool}
  for s: Trie<V>
  for k: List<&2, Bool>
  for +x: V
  {Trie.get(V, s, k) == None{}: Maybe<&2, V>}
    -> {Trie.all2(~V, ~V, ~r, ~left, s, Trie.one(V, k, x)) == True{}: Bool}

def Trie.all2_one(ty, r, left, rn, rl, ltrue, s, k, x):
  match s k:
    case Tip{} q:
      g => {==}
    case Bin{+h, +z, +o} Nil{}:
      g =>
        %Equal.sym(Maybe<&2, ty>, h, None{}, g):
          {
            Bool.and(
              r(_, Some{x}),
              Bool.and(
                Trie.all2(~ty, ~ty, ~r, ~left, z, Tip{}),
                Trie.all2(~ty, ~ty, ~r, ~left, o, Tip{})
              )
            )
              == True{}: Bool
          }
        Shared.Bool.and_both(
          r(None{}, Some{x}),
          Bool.and(
            Trie.all2(~ty, ~ty, ~r, ~left, z, Tip{}),
            Trie.all2(~ty, ~ty, ~r, ~left, o, Tip{})
          )
        )(
          rn(Some{x})
        )(
          Shared.Bool.and_both(
            Trie.all2(~ty, ~ty, ~r, ~left, z, Tip{}),
            Trie.all2(~ty, ~ty, ~r, ~left, o, Tip{})
          )(
            Trie.all2_tip(~ty, ~ty, ~r, ~left, ~ltrue, z)
          )(Trie.all2_tip(~ty, ~ty, ~r, ~left, ~ltrue, o))
        )
    case Bin{+h, +z, +o} Con{False{}, +q}:
      g => Shared.Bool.and_both(
        r(h, None{}),
        Bool.and(
          Trie.all2(~ty, ~ty, ~r, ~left, z, Trie.one(ty, q, x)),
          Trie.all2(~ty, ~ty, ~r, ~left, o, Tip{})
        )
      )(
        rl(h)
      )(
        Shared.Bool.and_both(
          Trie.all2(~ty, ~ty, ~r, ~left, z, Trie.one(ty, q, x)),
          Trie.all2(~ty, ~ty, ~r, ~left, o, Tip{})
        )(
          Trie.all2_one(~ty, ~r, ~left, ~rn, ~rl, ~ltrue, z, q, x)(g)
        )(Trie.all2_tip(~ty, ~ty, ~r, ~left, ~ltrue, o))
      )
    case Bin{+h, +z, +o} Con{True{}, +q}:
      g => Shared.Bool.and_both(
        r(h, None{}),
        Bool.and(
          Trie.all2(~ty, ~ty, ~r, ~left, z, Tip{}),
          Trie.all2(~ty, ~ty, ~r, ~left, o, Trie.one(ty, q, x))
        )
      )(
        rl(h)
      )(
        Shared.Bool.and_both(
          Trie.all2(~ty, ~ty, ~r, ~left, z, Tip{}),
          Trie.all2(~ty, ~ty, ~r, ~left, o, Trie.one(ty, q, x))
        )(
          Trie.all2_tip(~ty, ~ty, ~r, ~left, ~ltrue, z)
        )(Trie.all2_one(~ty, ~r, ~left, ~rn, ~rl, ~ltrue, o, q, x)(g))
      )
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# Keeping
# -------
# b keeps a by r when r holds of what they hold at each key, and r of a's
# entry and no entry where b holds nothing: for an r that keeps values, b
# holds every entry of a. Keeping composes (Trie.keeps_trans) and keeps the
# count of entries from falling (Trie.keeps_size).

# b keeps a by r
def Trie.keeps(~V: Data, ~r: Maybe<&2, V> -> Maybe<&2, V> -> Bool, a: Trie<V>, b: Trie<V>) -> Bool:
  Trie.all2(~V, ~V, ~r, ~(t => Trie.all(~V, ~(m => r(m, None{})), t)), a, b)

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# r holds at every key of a and b, when b keeps a
def Trie.keeps_get(
  ~V: Data,
  ~r: Maybe<&2, V> -> Maybe<&2, V> -> Bool,
  ~rn: @y: Maybe<&2, V> -> {r(None{}, y) == True{}: Bool},
  a: Trie<V>,
  b: Trie<V>,
  k: List<&2, Bool>
) -> {
  Trie.keeps(~V, ~r, a, b) == True{}: Bool
} -> {r(Trie.get(V, a, k), Trie.get(V, b, k)) == True{}: Bool}:
  Trie.all2_get(
    ~V,
    ~V,
    ~r,
    ~(t => Trie.all(~V, ~(m => r(m, None{})), t)),
    ~rn,
    ~(t => q => Trie.all_get(~V, ~(m => r(m, None{})), rn(None{}), t, q)),
    a,
    b,
    k
  )

# the empty trie keeps a when r holds of each entry of a and no entry
def Trie.keeps_tip(
  ~V: Data,
  ~r: Maybe<&2, V> -> Maybe<&2, V> -> Bool,
  a: Trie<V>
) -> {
  Trie.all(~V, ~(m => r(m, None{})), a) == True{}: Bool
} -> {Trie.keeps(~V, ~r, a, Tip{}) == True{}: Bool}:
  match a:
    case Tip{}:
      e => {==}
    case Bin{h, z, o}:
      e => e

# what b keeps of a below a key, it keeps below it
def Trie.keeps_under(
  ~V: Data,
  ~r: Maybe<&2, V> -> Maybe<&2, V> -> Bool,
  a: Trie<V>,
  b: Trie<V>,
  k: List<&2, Bool>
) -> {
  Trie.keeps(~V, ~r, a, b) == True{}: Bool
} -> {Trie.keeps(~V, ~r, Trie.under(V, a, k), Trie.under(V, b, k)) == True{}: Bool}:
  Trie.all2_under(
    ~V,
    ~V,
    ~r,
    ~(t => Trie.all(~V, ~(m => r(m, None{})), t)),
    ~(
      +t => +q => e => Trie.keeps_tip(
        ~V,
        ~r,
        Trie.under(V, t, q)
      )(Trie.all_under(~V, ~(m => r(m, None{})), t, q)(e))
    ),
    a,
    b,
    k
  )

# any trie keeps a when r holds of each entry of a and no entry, by way of no
# entry (rtrans)
def Trie.keeps_of_all(
  ~V: Data,
  ~r: Maybe<&2, V> -> Maybe<&2, V> -> Bool,
  ~rn: @y: Maybe<&2, V> -> {r(None{}, y) == True{}: Bool},
  ~rtrans: @x: Maybe<
    &2,
    V> -> @y: Maybe<
    &2,
    V> -> @z: Maybe<
    &2,
    V> -> {r(x, y) == True{}: Bool} -> {r(y, z) == True{}: Bool} -> {r(x, z) == True{}: Bool},
  a: Trie<V>,
  b: Trie<V>
) -> {
  Trie.all(~V, ~(m => r(m, None{})), a) == True{}: Bool
} -> {Trie.keeps(~V, ~r, a, b) == True{}: Bool}:
  match a b:
    case Tip{} y:
      e => {==}
    case Bin{h, z, o} Tip{}:
      e => e
    case Bin{+h1, +z1, +o1} Bin{+h2, +z2, +o2}:
      +e =>
        +rest = Shared.Bool.and_true_right(
          r(h1, None{}),
          Bool.and(Trie.all(~V, ~(m => r(m, None{})), z1), Trie.all(~V, ~(m => r(m, None{})), o1))
        )(e)
        Shared.Bool.and_both(
          r(h1, h2),
          Bool.and(Trie.keeps(~V, ~r, z1, z2), Trie.keeps(~V, ~r, o1, o2))
        )(
          rtrans(
            h1
          )(
            None{}
          )(
            h2
          )(
            Shared.Bool.and_true_left(
              r(h1, None{}),
              Bool.and(
                Trie.all(~V, ~(m => r(m, None{})), z1),
                Trie.all(~V, ~(m => r(m, None{})), o1)
              )
            )(e)
          )(rn(h2))
        )(
          Shared.Bool.and_both(
            Trie.keeps(~V, ~r, z1, z2),
            Trie.keeps(~V, ~r, o1, o2)
          )(
            Trie.keeps_of_all(
              ~V,
              ~r,
              ~rn,
              ~rtrans,
              z1,
              z2
            )(
              Shared.Bool.and_true_left(
                Trie.all(~V, ~(m => r(m, None{})), z1),
                Trie.all(~V, ~(m => r(m, None{})), o1)
              )(rest)
            )
          )(
            Trie.keeps_of_all(
              ~V,
              ~r,
              ~rn,
              ~rtrans,
              o1,
              o2
            )(
              Shared.Bool.and_true_right(
                Trie.all(~V, ~(m => r(m, None{})), z1),
                Trie.all(~V, ~(m => r(m, None{})), o1)
              )(rest)
            )
          )
        )

# r holds of each entry of a and no entry, when it does of b and b keeps a
def Trie.all_of_keeps(
  ~V: Data,
  ~r: Maybe<&2, V> -> Maybe<&2, V> -> Bool,
  ~rtrans: @x: Maybe<
    &2,
    V> -> @y: Maybe<
    &2,
    V> -> @z: Maybe<
    &2,
    V> -> {r(x, y) == True{}: Bool} -> {r(y, z) == True{}: Bool} -> {r(x, z) == True{}: Bool},
  a: Trie<V>,
  b: Trie<V>
) -> {
  Trie.keeps(~V, ~r, a, b) == True{}: Bool
} -> {
  Trie.all(~V, ~(m => r(m, None{})), b) == True{}: Bool
} -> {Trie.all(~V, ~(m => r(m, None{})), a) == True{}: Bool}:
  match a b:
    case Tip{} y:
      g => e => {==}
    case Bin{h, z, o} Tip{}:
      g => e => g
    case Bin{+h1, +z1, +o1} Bin{+h2, +z2, +o2}:
      +g => +e =>
        +gr = Shared.Bool.and_true_right(
          r(h1, h2),
          Bool.and(Trie.keeps(~V, ~r, z1, z2), Trie.keeps(~V, ~r, o1, o2))
        )(g)
        +er = Shared.Bool.and_true_right(
          r(h2, None{}),
          Bool.and(Trie.all(~V, ~(m => r(m, None{})), z2), Trie.all(~V, ~(m => r(m, None{})), o2))
        )(e)
        Shared.Bool.and_both(
          r(h1, None{}),
          Bool.and(Trie.all(~V, ~(m => r(m, None{})), z1), Trie.all(~V, ~(m => r(m, None{})), o1))
        )(
          rtrans(
            h1
          )(
            h2
          )(
            None{}
          )(
            Shared.Bool.and_true_left(
              r(h1, h2),
              Bool.and(Trie.keeps(~V, ~r, z1, z2), Trie.keeps(~V, ~r, o1, o2))
            )(g)
          )(
            Shared.Bool.and_true_left(
              r(h2, None{}),
              Bool.and(
                Trie.all(~V, ~(m => r(m, None{})), z2),
                Trie.all(~V, ~(m => r(m, None{})), o2)
              )
            )(e)
          )
        )(
          Shared.Bool.and_both(
            Trie.all(~V, ~(m => r(m, None{})), z1),
            Trie.all(~V, ~(m => r(m, None{})), o1)
          )(
            Trie.all_of_keeps(
              ~V,
              ~r,
              ~rtrans,
              z1,
              z2
            )(
              Shared.Bool.and_true_left(Trie.keeps(~V, ~r, z1, z2), Trie.keeps(~V, ~r, o1, o2))(gr)
            )(
              Shared.Bool.and_true_left(
                Trie.all(~V, ~(m => r(m, None{})), z2),
                Trie.all(~V, ~(m => r(m, None{})), o2)
              )(er)
            )
          )(
            Trie.all_of_keeps(
              ~V,
              ~r,
              ~rtrans,
              o1,
              o2
            )(
              Shared.Bool.and_true_right(Trie.keeps(~V, ~r, z1, z2), Trie.keeps(~V, ~r, o1, o2))(gr)
            )(
              Shared.Bool.and_true_right(
                Trie.all(~V, ~(m => r(m, None{})), z2),
                Trie.all(~V, ~(m => r(m, None{})), o2)
              )(er)
            )
          )
        )

# keeping composes
law Trie.keeps_trans:
  for ~V: Data
  for ~r: Maybe<&2, V> -> Maybe<&2, V> -> Bool
  for ~rn: @y: Maybe<&2, V> -> {r(None{}, y) == True{}: Bool}
  for ~rtrans: @x: Maybe<
    &2,
    V> -> @y: Maybe<
    &2,
    V> -> @z: Maybe<
    &2,
    V> -> {r(x, y) == True{}: Bool} -> {r(y, z) == True{}: Bool} -> {r(x, z) == True{}: Bool}
  for s1: Trie<V>
  for s2: Trie<V>
  for s3: Trie<V>
  {Trie.keeps(~V, ~r, s1, s2) == True{}: Bool}
    -> {Trie.keeps(~V, ~r, s2, s3) == True{}: Bool}
    -> {Trie.keeps(~V, ~r, s1, s3) == True{}: Bool}

def Trie.keeps_trans(ty, r, rn, rtrans, s1, s2, s3):
  match s1 s2 s3:
    case Tip{} y w:
      g1 => g2 => {==}
    case Bin{h1, z1, o1} Tip{} w:
      g1 => g2 => Trie.keeps_of_all(~ty, ~r, ~rn, ~rtrans, Bin{h1, z1, o1}, w)(g1)
    case Bin{h1, z1, o1} Bin{h2, z2, o2} Tip{}:
      g1 => g2 => Trie.all_of_keeps(~ty, ~r, ~rtrans, Bin{h1, z1, o1}, Bin{h2, z2, o2})(g1)(g2)
    case Bin{+h1, +z1, +o1} Bin{+h2, +z2, +o2} Bin{+h3, +z3, +o3}:
      +g1 => +g2 =>
        +a1 = Shared.Bool.and_true_right(
          r(h1, h2),
          Bool.and(Trie.keeps(~ty, ~r, z1, z2), Trie.keeps(~ty, ~r, o1, o2))
        )(g1)
        +a2 = Shared.Bool.and_true_right(
          r(h2, h3),
          Bool.and(Trie.keeps(~ty, ~r, z2, z3), Trie.keeps(~ty, ~r, o2, o3))
        )(g2)
        Shared.Bool.and_both(
          r(h1, h3),
          Bool.and(Trie.keeps(~ty, ~r, z1, z3), Trie.keeps(~ty, ~r, o1, o3))
        )(
          rtrans(
            h1
          )(
            h2
          )(
            h3
          )(
            Shared.Bool.and_true_left(
              r(h1, h2),
              Bool.and(Trie.keeps(~ty, ~r, z1, z2), Trie.keeps(~ty, ~r, o1, o2))
            )(g1)
          )(
            Shared.Bool.and_true_left(
              r(h2, h3),
              Bool.and(Trie.keeps(~ty, ~r, z2, z3), Trie.keeps(~ty, ~r, o2, o3))
            )(g2)
          )
        )(
          Shared.Bool.and_both(
            Trie.keeps(~ty, ~r, z1, z3),
            Trie.keeps(~ty, ~r, o1, o3)
          )(
            Trie.keeps_trans(
              ~ty,
              ~r,
              ~rn,
              ~rtrans,
              z1,
              z2,
              z3
            )(
              Shared.Bool.and_true_left(
                Trie.keeps(~ty, ~r, z1, z2),
                Trie.keeps(~ty, ~r, o1, o2)
              )(a1)
            )(
              Shared.Bool.and_true_left(
                Trie.keeps(~ty, ~r, z2, z3),
                Trie.keeps(~ty, ~r, o2, o3)
              )(a2)
            )
          )(
            Trie.keeps_trans(
              ~ty,
              ~r,
              ~rn,
              ~rtrans,
              o1,
              o2,
              o3
            )(
              Shared.Bool.and_true_right(
                Trie.keeps(~ty, ~r, z1, z2),
                Trie.keeps(~ty, ~r, o1, o2)
              )(a1)
            )(
              Shared.Bool.and_true_right(
                Trie.keeps(~ty, ~r, z2, z3),
                Trie.keeps(~ty, ~r, o2, o3)
              )(a2)
            )
          )
        )

# an entry kept as no entry is no entry
def Trie.none_of_kept(
  ~V: Data,
  ~r: Maybe<&2, V> -> Maybe<&2, V> -> Bool,
  ~rs: @x: Maybe<
    &2,
    V> -> @y: Maybe<
    &2,
    V> -> {
    r(x, y) == True{}: Bool
  } -> {Maybe.is_some(&2, V, x) == True{}: Bool} -> {Maybe.is_some(&2, V, y) == True{}: Bool},
  m: Maybe<&2, V>
) -> {r(m, None{}) == True{}: Bool} -> {Maybe.is_none(&2, V, m) == True{}: Bool}:
  match m:
    case None{}:
      e => {==}
    case Some{c}:
      e => Empty.absurd(
        {Maybe.is_none(&2, V, Some{c}) == True{}: Bool},
        Shared.Bool.false_ne_true(rs(Some{c})(None{})(e)({==}))
      )

# b keeps a: b holds no fewer entries, when r keeps each entry an entry
law Trie.keeps_size:
  for ~V: Data
  for ~r: Maybe<&2, V> -> Maybe<&2, V> -> Bool
  for ~rs: @x: Maybe<
    &2,
    V> -> @y: Maybe<
    &2,
    V> -> {
    r(x, y) == True{}: Bool
  } -> {Maybe.is_some(&2, V, x) == True{}: Bool} -> {Maybe.is_some(&2, V, y) == True{}: Bool}
  for s: Trie<V>
  for s2: Trie<V>
  {Trie.keeps(~V, ~r, s, s2) == True{}: Bool}
    -> {Nat.is_le(Trie.size(V, s), Trie.size(V, s2)) == True{}: Bool}

def Trie.keeps_size(ty, r, rs, s, s2):
  match s s2:
    case Tip{} y:
      e => Shared.Nat.le_zero(Trie.size(ty, y))
    case Bin{+h, +z, +o} Tip{}:
      e =>
        %Equal.sym(
          Nat,
          Trie.size(ty, Bin{h, z, o}),
          0n,
          Trie.all_size(
            ~ty,
            ~(m => r(m, None{})),
            ~(m => Trie.none_of_kept(~ty, ~r, ~rs, m)),
            Bin{h, z, o}
          )(e)
        ): {Nat.is_le(_, 0n) == True{}: Bool}
        {==}
    case Bin{None{}, +z1, +o1} Bin{None{}, +z2, +o2}:
      +e =>
        +rest = Shared.Bool.and_true_right(
          r(None{}, None{}),
          Bool.and(Trie.keeps(~ty, ~r, z1, z2), Trie.keeps(~ty, ~r, o1, o2))
        )(e)
        Shared.Nat.add_le(
          Trie.size(ty, z1),
          Trie.size(ty, z2),
          Trie.size(ty, o1),
          Trie.size(ty, o2)
        )(
          Trie.keeps_size(
            ~ty,
            ~r,
            ~rs,
            z1,
            z2
          )(
            Shared.Bool.and_true_left(
              Trie.keeps(~ty, ~r, z1, z2),
              Trie.keeps(~ty, ~r, o1, o2)
            )(rest)
          )
        )(
          Trie.keeps_size(
            ~ty,
            ~r,
            ~rs,
            o1,
            o2
          )(
            Shared.Bool.and_true_right(
              Trie.keeps(~ty, ~r, z1, z2),
              Trie.keeps(~ty, ~r, o1, o2)
            )(rest)
          )
        )
    case Bin{None{}, +z1, +o1} Bin{Some{c2}, +z2, +o2}:
      +e =>
        +rest = Shared.Bool.and_true_right(
          r(None{}, Some{c2}),
          Bool.and(Trie.keeps(~ty, ~r, z1, z2), Trie.keeps(~ty, ~r, o1, o2))
        )(e)
        Shared.Nat.le_succ(
          Nat.add(Trie.size(ty, z1), Trie.size(ty, o1)),
          Nat.add(Trie.size(ty, z2), Trie.size(ty, o2))
        )(
          Shared.Nat.add_le(
            Trie.size(ty, z1),
            Trie.size(ty, z2),
            Trie.size(ty, o1),
            Trie.size(ty, o2)
          )(
            Trie.keeps_size(
              ~ty,
              ~r,
              ~rs,
              z1,
              z2
            )(
              Shared.Bool.and_true_left(
                Trie.keeps(~ty, ~r, z1, z2),
                Trie.keeps(~ty, ~r, o1, o2)
              )(rest)
            )
          )(
            Trie.keeps_size(
              ~ty,
              ~r,
              ~rs,
              o1,
              o2
            )(
              Shared.Bool.and_true_right(
                Trie.keeps(~ty, ~r, z1, z2),
                Trie.keeps(~ty, ~r, o1, o2)
              )(rest)
            )
          )
        )
    case Bin{Some{+c1}, +z1, +o1} Bin{Some{c2}, +z2, +o2}:
      +e =>
        +rest = Shared.Bool.and_true_right(
          r(Some{c1}, Some{c2}),
          Bool.and(Trie.keeps(~ty, ~r, z1, z2), Trie.keeps(~ty, ~r, o1, o2))
        )(e)
        Shared.Nat.add_le(
          Trie.size(ty, z1),
          Trie.size(ty, z2),
          Trie.size(ty, o1),
          Trie.size(ty, o2)
        )(
          Trie.keeps_size(
            ~ty,
            ~r,
            ~rs,
            z1,
            z2
          )(
            Shared.Bool.and_true_left(
              Trie.keeps(~ty, ~r, z1, z2),
              Trie.keeps(~ty, ~r, o1, o2)
            )(rest)
          )
        )(
          Trie.keeps_size(
            ~ty,
            ~r,
            ~rs,
            o1,
            o2
          )(
            Shared.Bool.and_true_right(
              Trie.keeps(~ty, ~r, z1, z2),
              Trie.keeps(~ty, ~r, o1, o2)
            )(rest)
          )
        )
    case Bin{Some{+c1}, +z1, +o1} Bin{None{}, +z2, +o2}:
      e => Empty.absurd(
        {
          Nat.is_le(
            Trie.size(ty, Bin{Some{c1}, z1, o1}),
            Trie.size(ty, Bin{None{}, z2, o2})
          )
            == True{}: Bool
        },
        Shared.Bool.false_ne_true(
          rs(
            Some{c1}
          )(
            None{}
          )(
            Shared.Bool.and_true_left(
              r(Some{c1}, None{}),
              Bool.and(Trie.keeps(~ty, ~r, z1, z2), Trie.keeps(~ty, ~r, o1, o2))
            )(e)
          )({==})
        )
      )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information
# bend-lint: expect-end bend-lint-rules/performance/missed_fork@hint
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# Takes
# -----
# A take keeps a's value where both tries hold a key: it adds b's entries only
# at the keys that a does not hold, so a holder never loses or changes what it
# holds.

# the entries of a, and those of b at the keys that a does not hold
def Trie.take(~V: Data, a: Trie<V>, b: Trie<V>) -> Trie<V>:
  Trie.union(~V, ~(x => y => x), a, b)

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# Trie.take_keeps at one key
def Trie.take_keeps.here(
  ~V: Data,
  ~r: Maybe<&2, V> -> Maybe<&2, V> -> Bool,
  ~rn: @y: Maybe<&2, V> -> {r(None{}, y) == True{}: Bool},
  ~rrefl: @m: Maybe<&2, V> -> {r(m, m) == True{}: Bool},
  a: Maybe<&2, V>,
  b: Maybe<&2, V>
) -> {r(a, Shared.Maybe.join(~V, ~(x => y => x), a, b)) == True{}: Bool}:
  match a b:
    case None{} y:
      rn(y)
    case Some{x} None{}:
      rrefl(Some{x})
    case Some{x} Some{y}:
      rrefl(Some{x})

# r holds of a and its take of b, when r holds of no entry and any, and of
# each entry and itself: a take keeps what a holds
def Trie.take_keeps(
  ~V: Data,
  ~r: Maybe<&2, V> -> Maybe<&2, V> -> Bool,
  ~left: Trie<V> -> Bool,
  ~rn: @y: Maybe<&2, V> -> {r(None{}, y) == True{}: Bool},
  ~rrefl: @m: Maybe<&2, V> -> {r(m, m) == True{}: Bool},
  a: Trie<V>,
  b: Trie<V>
) -> {Trie.all2(~V, ~V, ~r, ~left, a, Trie.take(~V, a, b)) == True{}: Bool}:
  match a b:
    case Tip{} y:
      {==}
    case Bin{h, z, o} Tip{}:
      Trie.all2_refl(~V, ~r, ~left, ~rrefl, Bin{h, z, o})
    case Bin{+h1, +z1, +o1} Bin{+h2, +z2, +o2}:
      Shared.Bool.and_both(
        r(h1, Shared.Maybe.join(~V, ~(x => y => x), h1, h2)),
        Bool.and(
          Trie.all2(~V, ~V, ~r, ~left, z1, Trie.take(~V, z1, z2)),
          Trie.all2(~V, ~V, ~r, ~left, o1, Trie.take(~V, o1, o2))
        )
      )(
        Trie.take_keeps.here(~V, ~r, ~rn, ~rrefl, h1, h2)
      )(
        Shared.Bool.and_both(
          Trie.all2(~V, ~V, ~r, ~left, z1, Trie.take(~V, z1, z2)),
          Trie.all2(~V, ~V, ~r, ~left, o1, Trie.take(~V, o1, o2))
        )(
          Trie.take_keeps(~V, ~r, ~left, ~rn, ~rrefl, z1, z2)
        )(Trie.take_keeps(~V, ~r, ~left, ~rn, ~rrefl, o1, o2))
      )

# a take of b is the union with b, when q holds of a and b and the join of
# two entries that q holds of is the first
def Trie.take_union(
  ~V: Data,
  ~join: V -> V -> V,
  ~q: Maybe<&2, V> -> Maybe<&2, V> -> Bool,
  ~lq: Trie<V> -> Bool,
  ~step: @x: Maybe<
    &2,
    V> -> @y: Maybe<
    &2,
    V> -> {
    q(x, y) == True{}: Bool
  } -> {
    Shared.Maybe.join(~V, ~(c => d => c), x, y) == Shared.Maybe.join(~V, ~join, x, y): Maybe<&2, V>
  },
  a: Trie<V>,
  b: Trie<V>
) -> {
  Trie.all2(~V, ~V, ~q, ~lq, a, b) == True{}: Bool
} -> {Trie.take(~V, a, b) == Trie.union(~V, ~join, a, b): Trie<V>}:
  match a b:
    case Tip{} y:
      e => {==}
    case Bin{h, z, o} Tip{}:
      e => {==}
    case Bin{+h1, +z1, +o1} Bin{+h2, +z2, +o2}:
      +e =>
        +rest = Shared.Bool.and_true_right(
          q(h1, h2),
          Bool.and(Trie.all2(~V, ~V, ~q, ~lq, z1, z2), Trie.all2(~V, ~V, ~q, ~lq, o1, o2))
        )(e)
        %Trie.take_union(~V, ~join, ~q, ~lq, ~step, z1, z2)(
          Shared.Bool.and_true_left(
            Trie.all2(~V, ~V, ~q, ~lq, z1, z2),
            Trie.all2(~V, ~V, ~q, ~lq, o1, o2)
          )(rest)
        ): {
          Bin{
            Shared.Maybe.join(~V, ~(c => d => c), h1, h2),
            Trie.take(~V, z1, z2),
            Trie.take(~V, o1, o2)
          }
            == Bin{Shared.Maybe.join(~V, ~join, h1, h2), _, Trie.union(~V, ~join, o1, o2)}: Trie<V>
        }
        %Trie.take_union(~V, ~join, ~q, ~lq, ~step, o1, o2)(
          Shared.Bool.and_true_right(
            Trie.all2(~V, ~V, ~q, ~lq, z1, z2),
            Trie.all2(~V, ~V, ~q, ~lq, o1, o2)
          )(rest)
        ): {
          Bin{
            Shared.Maybe.join(~V, ~(c => d => c), h1, h2),
            Trie.take(~V, z1, z2),
            Trie.take(~V, o1, o2)
          }
            == Bin{Shared.Maybe.join(~V, ~join, h1, h2), Trie.take(~V, z1, z2), _}: Trie<V>
        }
        %step(h1)(h2)(
          Shared.Bool.and_true_left(
            q(h1, h2),
            Bool.and(Trie.all2(~V, ~V, ~q, ~lq, z1, z2), Trie.all2(~V, ~V, ~q, ~lq, o1, o2))
          )(e)
        ): {
          Bin{
            Shared.Maybe.join(~V, ~(c => d => c), h1, h2),
            Trie.take(~V, z1, z2),
            Trie.take(~V, o1, o2)
          }
            == Bin{_, Trie.take(~V, z1, z2), Trie.take(~V, o1, o2)}: Trie<V>
        }
        {==}

# r holds of b and a's take of b, when q holds of a and b and r holds of the
# second of two entries that q holds of and the one a take keeps: a take
# holds all that b holds
def Trie.take_keeps_right(
  ~V: Data,
  ~q: Maybe<&2, V> -> Maybe<&2, V> -> Bool,
  ~lq: Trie<V> -> Bool,
  ~r: Maybe<&2, V> -> Maybe<&2, V> -> Bool,
  ~lr: Trie<V> -> Bool,
  ~step: @x: Maybe<
    &2,
    V> -> @y: Maybe<
    &2,
    V> -> {
    q(x, y) == True{}: Bool
  } -> {r(y, Shared.Maybe.join(~V, ~(c => d => c), x, y)) == True{}: Bool},
  ~rrefl: @m: Maybe<&2, V> -> {r(m, m) == True{}: Bool},
  a: Trie<V>,
  b: Trie<V>
) -> {
  Trie.all2(~V, ~V, ~q, ~lq, a, b) == True{}: Bool
} -> {Trie.all2(~V, ~V, ~r, ~lr, b, Trie.take(~V, a, b)) == True{}: Bool}:
  match a b:
    case Tip{} y:
      e => Trie.all2_refl(~V, ~r, ~lr, ~rrefl, y)
    case Bin{h, z, o} Tip{}:
      e => {==}
    case Bin{+h1, +z1, +o1} Bin{+h2, +z2, +o2}:
      +e =>
        +rest = Shared.Bool.and_true_right(
          q(h1, h2),
          Bool.and(Trie.all2(~V, ~V, ~q, ~lq, z1, z2), Trie.all2(~V, ~V, ~q, ~lq, o1, o2))
        )(e)
        Shared.Bool.and_both(
          r(h2, Shared.Maybe.join(~V, ~(c => d => c), h1, h2)),
          Bool.and(
            Trie.all2(~V, ~V, ~r, ~lr, z2, Trie.take(~V, z1, z2)),
            Trie.all2(~V, ~V, ~r, ~lr, o2, Trie.take(~V, o1, o2))
          )
        )(
          step(h1)(h2)(
            Shared.Bool.and_true_left(
              q(h1, h2),
              Bool.and(Trie.all2(~V, ~V, ~q, ~lq, z1, z2), Trie.all2(~V, ~V, ~q, ~lq, o1, o2))
            )(e)
          )
        )(
          Shared.Bool.and_both(
            Trie.all2(~V, ~V, ~r, ~lr, z2, Trie.take(~V, z1, z2)),
            Trie.all2(~V, ~V, ~r, ~lr, o2, Trie.take(~V, o1, o2))
          )(
            Trie.take_keeps_right(~V, ~q, ~lq, ~r, ~lr, ~step, ~rrefl, z1, z2)(
              Shared.Bool.and_true_left(
                Trie.all2(~V, ~V, ~q, ~lq, z1, z2),
                Trie.all2(~V, ~V, ~q, ~lq, o1, o2)
              )(rest)
            )
          )(
            Trie.take_keeps_right(~V, ~q, ~lq, ~r, ~lr, ~step, ~rrefl, o1, o2)(
              Shared.Bool.and_true_right(
                Trie.all2(~V, ~V, ~q, ~lq, z1, z2),
                Trie.all2(~V, ~V, ~q, ~lq, o1, o2)
              )(rest)
            )
          )
        )
# a's value stays, whether b's is the same or not (hit)
def Trie.take_minus.pick(
  ~V: Data,
  x: V,
  y: V,
  hit: Bool
) -> {
  Shared.Maybe.join(
    ~V,
    ~(c => d => c),
    Some{x},
    Bool.pick(Maybe<&2, V>, hit, None{}, Some{y})
  )
    == Some{x}: Maybe<&2, V>
}:
  match hit:
    case True{}:
      {==}
    case False{}:
      {==}

# Trie.take_minus at one key
def Trie.take_minus.here(
  ~V: Data,
  ~same: V -> V -> Bool,
  a: Maybe<&2, V>,
  b: Maybe<&2, V>
) -> {
  Shared.Maybe.join(
    ~V,
    ~(x => y => x),
    a,
    Trie.minus.here(~V, ~same, b, a)
  )
    == Shared.Maybe.join(~V, ~(x => y => x), a, b): Maybe<&2, V>
}:
  match a b:
    case None{} None{}:
      {==}
    case None{} Some{y}:
      {==}
    case Some{x} None{}:
      {==}
    case Some{+x} Some{+y}:
      Trie.take_minus.pick(~V, x, y, same(y, x))

# what a takes of what it lacks of b is what it takes of b: the entries that a
# sync sends are enough
def Trie.take_minus(
  ~V: Data,
  ~same: V -> V -> Bool,
  a: Trie<V>,
  b: Trie<V>
) -> {Trie.take(~V, a, Trie.minus(~V, ~same, b, a)) == Trie.take(~V, a, b): Trie<V>}:
  match a b:
    case Tip{} Tip{}:
      {==}
    case Tip{} Bin{h, z, o}:
      {==}
    case Bin{h, z, o} Tip{}:
      {==}
    case Bin{+h1, +z1, +o1} Bin{+h2, +z2, +o2}:
      %Trie.take_minus(~V, ~same, z1, z2): {
        Bin{
          Shared.Maybe.join(~V, ~(x => y => x), h1, Trie.minus.here(~V, ~same, h2, h1)),
          Trie.take(~V, z1, Trie.minus(~V, ~same, z2, z1)),
          Trie.take(~V, o1, Trie.minus(~V, ~same, o2, o1))
        }
          == Bin{Shared.Maybe.join(~V, ~(x => y => x), h1, h2), _, Trie.take(~V, o1, o2)}: Trie<V>
      }
      %Trie.take_minus(~V, ~same, o1, o2): {
        Bin{
          Shared.Maybe.join(~V, ~(x => y => x), h1, Trie.minus.here(~V, ~same, h2, h1)),
          Trie.take(~V, z1, Trie.minus(~V, ~same, z2, z1)),
          Trie.take(~V, o1, Trie.minus(~V, ~same, o2, o1))
        }
          == Bin{
            Shared.Maybe.join(~V, ~(x => y => x), h1, h2),
            Trie.take(~V, z1, Trie.minus(~V, ~same, z2, z1)),
            _
          }: Trie<V>
      }
      %Trie.take_minus.here(~V, ~same, h1, h2): {
        Bin{
          Shared.Maybe.join(~V, ~(x => y => x), h1, Trie.minus.here(~V, ~same, h2, h1)),
          Trie.take(~V, z1, Trie.minus(~V, ~same, z2, z1)),
          Trie.take(~V, o1, Trie.minus(~V, ~same, o2, o1))
        }
          == Bin{
            _,
            Trie.take(~V, z1, Trie.minus(~V, ~same, z2, z1)),
            Trie.take(~V, o1, Trie.minus(~V, ~same, o2, o1))
          }: Trie<V>
      }
      {==}
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
