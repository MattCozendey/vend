import Base
import ../../../../shared.bend as Shared

# Tries
# -----
# A trie maps keys to values. A key is a list of bits, read from the first:
# a False goes to zero, a True to one. A part with one entry is a leaf, which
# holds the rest of the key, so an entry costs a node for each bit that it
# shares with another key, and no more. No operation builds a node with zero
# or one for fewer than two entries, so the shape is a function of the keys
# and values, and a union is commutative, associative and idempotent as terms.

# bend-lint: expect-begin bend-lint-rules/layout/case@warning -- a constructor is PascalCase, as in Base (Some, Con): the rule reads a constructor as a law
# a trie: no entry (Tip), one entry at the key (Leaf), or the value of the
# empty key here, then the keys that start with False (zero) and with True
# (one)
type Trie<-V: Data> is Data:
  Tip{}
  Leaf{key: List<&2, Bool>, value: V}
  Bin{here: Maybe<&2, V>, zero: Trie<V>, one: Trie<V>}
# bend-lint: expect-end bend-lint-rules/layout/case@warning

# a trie with no entries
def Trie.new(-V: Data) -> Trie<V>:
  Tip{}

# k is the key k0
def Trie.same_key(k: List<&2, Bool>, k0: List<&2, Bool>) -> Bool:
  Shared.List.is_eq(~Bool, ~Shared.Bool.is_eq, k, k0)

# Nodes of leaves
# ---------------
# A leaf holds what a node holds: Trie.at.here, Trie.at.zero and Trie.at.one
# are the three parts of the node of the leaf of k and v.

# the value of the empty key
def Trie.at.here(-V: Data, k: List<&2, Bool>, v: V) -> Maybe<&2, V>:
  match k:
    case Nil{}:
      Some{v}
    case Con{b, r}:
      None{}

# the keys that start with False
def Trie.at.zero(-V: Data, k: List<&2, Bool>, v: V) -> Trie<V>:
  match k:
    case Con{False{}, r}:
      Leaf{r, v}
    case _:
      Tip{}

# the keys that start with True
def Trie.at.one(-V: Data, k: List<&2, Bool>, v: V) -> Trie<V>:
  match k:
    case Con{True{}, r}:
      Leaf{r, v}
    case _:
      Tip{}

# the node of h, z and o, as a leaf when it holds one entry and no node
def Trie.tidy(-V: Data, h: Maybe<&2, V>, z: Trie<V>, o: Trie<V>) -> Trie<V>:
  match h z o:
    case None{} Leaf{k, v} Tip{}:
      Leaf{False{} <> k, v}
    case None{} Tip{} Leaf{k, v}:
      Leaf{True{} <> k, v}
    case Some{x} Tip{} Tip{}:
      Leaf{[], x}
    case h1 z1 o1:
      Bin{h1, z1, o1}

# the node of h, z and o in the shape of its entries
def Trie.bin(-V: Data, h: Maybe<&2, V>, z: Trie<V>, o: Trie<V>) -> Trie<V>:
  match h z o:
    case None{} Tip{} Tip{}:
      Tip{}
    case h1 z1 o1:
      Trie.tidy(V, h1, z1, o1)

# the value of the key k in t, or None
def Trie.get(-V: Data, t: Trie<V>, k: List<&2, Bool>) -> Maybe<&2, V>:
  match t k:
    case Tip{} r:
      None{}
    case Leaf{p, v} r:
      Bool.pick(Maybe<&2, V>, Trie.same_key(r, p), Some{v}, None{})
    case Bin{h, z, o} Nil{}:
      h
    case Bin{h, z, o} Con{False{}, r}:
      Trie.get(V, z, r)
    case Bin{h, z, o} Con{True{}, r}:
      Trie.get(V, o, r)

# the trie with only the key k, mapped to v
def Trie.one(-V: Data, k: List<&2, Bool>, v: V) -> Trie<V>:
  Leaf{k, v}

# the trie of the key k, mapped to v, and the key p, mapped to w; of only k
# when p is k
def Trie.set.leaf(-V: Data, k: List<&2, Bool>, v: V, p: List<&2, Bool>, w: V) -> Trie<V>:
  match k p:
    case Nil{} Nil{}:
      Leaf{[], v}
    case Nil{} Con{False{}, q}:
      Bin{Some{v}, Leaf{q, w}, Tip{}}
    case Nil{} Con{True{}, q}:
      Bin{Some{v}, Tip{}, Leaf{q, w}}
    case Con{False{}, r} Nil{}:
      Bin{Some{w}, Leaf{r, v}, Tip{}}
    case Con{True{}, r} Nil{}:
      Bin{Some{w}, Tip{}, Leaf{r, v}}
    case Con{False{}, r} Con{False{}, q}:
      Trie.bin(V, None{}, Trie.set.leaf(V, r, v, q, w), Tip{})
    case Con{True{}, r} Con{True{}, q}:
      Trie.bin(V, None{}, Tip{}, Trie.set.leaf(V, r, v, q, w))
    case Con{False{}, r} Con{True{}, q}:
      Bin{None{}, Leaf{r, v}, Leaf{q, w}}
    case Con{True{}, r} Con{False{}, q}:
      Bin{None{}, Leaf{q, w}, Leaf{r, v}}

# t with the key k mapped to v
def Trie.set(-V: Data, t: Trie<V>, k: List<&2, Bool>, v: V) -> Trie<V>:
  match t k:
    case Tip{} r:
      Leaf{r, v}
    case Leaf{p, w} r:
      Trie.set.leaf(V, r, v, p, w)
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
    case Leaf{k, v}:
      [v]
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
    case Leaf{k, v}:
      1n
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
def Trie.unique(
  ~A: Data,
  ~key: A -> List<&2, Bool>,
  xs: List<&2, A>,
  +seen: Trie<Unit>
) -> List<&2, A>:
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

# the entry of p and v, when p starts with k, under the rest of p
def Trie.under.leaf(-V: Data, k: List<&2, Bool>, p: List<&2, Bool>, v: V) -> Trie<V>:
  match k p:
    case Nil{} q:
      Leaf{q, v}
    case Con{False{}, r} Con{False{}, q}:
      Trie.under.leaf(V, r, q, v)
    case Con{True{}, r} Con{True{}, q}:
      Trie.under.leaf(V, r, q, v)
    case _ _:
      Tip{}

# the entries of t whose keys start with k, under the rest of their keys
def Trie.under(-V: Data, t: Trie<V>, k: List<&2, Bool>) -> Trie<V>:
  match t k:
    case Tip{} r:
      Tip{}
    case Leaf{p, v} r:
      Trie.under.leaf(V, r, p, v)
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

# Laws of highest keys
# --------------------

# the entries under False <> q of a leaf are those under q of its zero part
def Trie.under_zero(
  -V: Data,
  k: List<&2, Bool>,
  -v: V,
  -q: List<&2, Bool>
) -> {Trie.under(V, Trie.at.zero(V, k, v), q) == Trie.under(V, Leaf{k, v}, False{} <> q): Trie<V>}:
  match k:
    case Nil{}:
      {==}
    case Con{False{}, r}:
      {==}
    case Con{True{}, r}:
      {==}

# the entries under True <> q of a leaf are those under q of its one part
def Trie.under_one_part(
  -V: Data,
  k: List<&2, Bool>,
  -v: V,
  -q: List<&2, Bool>
) -> {Trie.under(V, Trie.at.one(V, k, v), q) == Trie.under(V, Leaf{k, v}, True{} <> q): Trie<V>}:
  match k:
    case Nil{}:
      {==}
    case Con{False{}, r}:
      {==}
    case Con{True{}, r}:
      {==}

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# Unions
# ------
# A union joins the values of a key that both tries hold. When join is a
# semilattice (commutative, associative, idempotent), so is the union: two
# holders that take in each other's entries, in any order and any number of
# times, end with the same trie.

# the entries of k, mapped to v, and of p, mapped to w, joined when p is k
def Trie.union.fork(
  ~V: Data,
  ~join: V -> V -> V,
  k: List<&2, Bool>,
  v: V,
  p: List<&2, Bool>,
  w: V
) -> Trie<V>:
  match k p:
    case Nil{} Nil{}:
      Leaf{[], join(v, w)}
    case Nil{} Con{False{}, q}:
      Bin{Some{v}, Leaf{q, w}, Tip{}}
    case Nil{} Con{True{}, q}:
      Bin{Some{v}, Tip{}, Leaf{q, w}}
    case Con{False{}, r} Nil{}:
      Bin{Some{w}, Leaf{r, v}, Tip{}}
    case Con{True{}, r} Nil{}:
      Bin{Some{w}, Tip{}, Leaf{r, v}}
    case Con{False{}, r} Con{False{}, q}:
      Trie.bin(V, None{}, Trie.union.fork(~V, ~join, r, v, q, w), Tip{})
    case Con{True{}, r} Con{True{}, q}:
      Trie.bin(V, None{}, Tip{}, Trie.union.fork(~V, ~join, r, v, q, w))
    case Con{False{}, r} Con{True{}, q}:
      Bin{None{}, Leaf{r, v}, Leaf{q, w}}
    case Con{True{}, r} Con{False{}, q}:
      Bin{None{}, Leaf{q, w}, Leaf{r, v}}

# the entry of k, mapped to v, and the entries of y, joined where y holds k
def Trie.union.leaf(~V: Data, ~join: V -> V -> V, y: Trie<V>, k: List<&2, Bool>, v: V) -> Trie<V>:
  match y k:
    case Tip{} r:
      Leaf{r, v}
    case Leaf{p, w} r:
      Trie.union.fork(~V, ~join, r, v, p, w)
    case Bin{h, z, o} Nil{}:
      Bin{Shared.Maybe.join(~V, ~join, Some{v}, h), z, o}
    case Bin{h, z, o} Con{False{}, r}:
      Bin{h, Trie.union.leaf(~V, ~join, z, r, v), o}
    case Bin{h, z, o} Con{True{}, r}:
      Bin{h, z, Trie.union.leaf(~V, ~join, o, r, v)}

# the entries of a and b, joined where both hold a key
def Trie.union(~V: Data, ~join: V -> V -> V, a: Trie<V>, b: Trie<V>) -> Trie<V>:
  match a b:
    case Tip{} y:
      y
    case Leaf{k, v} y:
      Trie.union.leaf(~V, ~join, y, k, v)
    case Bin{h, z, o} Tip{}:
      Bin{h, z, o}
    case Bin{h, z, o} Leaf{+k, +w}:
      zs os = Trie.union(
        ~V,
        ~join,
        z,
        Trie.at.zero(V, k, w)
      ) Trie.union(~V, ~join, o, Trie.at.one(V, k, w))
      Bin{Shared.Maybe.join(~V, ~join, h, Trie.at.here(V, k, w)), zs, os}
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

# the entry of k, mapped to v, unless m is the same value
def Trie.minus.leaf(
  ~V: Data,
  ~same: V -> V -> Bool,
  k: List<&2, Bool>,
  +v: V,
  m: Maybe<&2, V>
) -> Trie<V>:
  match m:
    case None{}:
      Leaf{k, v}
    case Some{w}:
      Bool.pick(Trie<V>, same(v, w), Tip{}, Leaf{k, v})

# t without the key k, which it holds
def Trie.drop(-V: Data, t: Trie<V>, k: List<&2, Bool>) -> Trie<V>:
  match t k:
    case Tip{} r:
      Tip{}
    case Leaf{+p, v} r:
      Bool.pick(Trie<V>, Trie.same_key(r, p), Tip{}, Leaf{p, v})
    case Bin{h, z, o} Nil{}:
      Trie.tidy(V, None{}, z, o)
    case Bin{h, z, o} Con{False{}, r}:
      Trie.tidy(V, h, Trie.drop(V, z, r), o)
    case Bin{h, z, o} Con{True{}, r}:
      Trie.tidy(V, h, z, Trie.drop(V, o, r))

# s, without the key k when it holds there (m) the same value as w
def Trie.minus.cut(
  ~V: Data,
  ~same: V -> V -> Bool,
  +s: Trie<V>,
  k: List<&2, Bool>,
  w: V,
  m: Maybe<&2, V>
) -> Trie<V>:
  match m:
    case None{}:
      s
    case Some{v}:
      Shared.Bool.when(Trie<V>, same(v, w), u => Trie.drop(V, s, k), u => s)

# s, without the key k when it holds there the same value as w
def Trie.minus.one(
  ~V: Data,
  ~same: V -> V -> Bool,
  +s: Trie<V>,
  +k: List<&2, Bool>,
  w: V
) -> Trie<V>:
  Trie.minus.cut(~V, ~same, s, k, w, Trie.get(V, s, k))

# the entries of s that r does not hold with the same value: what a holder of
# r lacks of s
def Trie.minus(~V: Data, ~same: V -> V -> Bool, s: Trie<V>, r: Trie<V>) -> Trie<V>:
  match s r:
    case Tip{} y:
      Tip{}
    case Leaf{+k, v} y:
      Trie.minus.leaf(~V, ~same, k, v, Trie.get(V, y, k))
    case Bin{h, z, o} Tip{}:
      Bin{h, z, o}
    case Bin{h, z, o} Leaf{k, w}:
      Trie.minus.one(~V, ~same, Bin{h, z, o}, k, w)
    case Bin{h1, z1, o1} Bin{h2, z2, o2}:
      zs os = Trie.minus(~V, ~same, z1, z2) Trie.minus(~V, ~same, o1, o2)
      Trie.bin(V, Trie.minus.here(~V, ~same, h1, h2), zs, os)

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

# only a key and itself are the same key
def Trie.same_key_sound(
  k: List<&2, Bool>,
  k0: List<&2, Bool>
) -> {Trie.same_key(k, k0) == True{}: Bool} -> {k == k0: List<&2, Bool>}:
  Shared.List.is_eq_sound(~Bool, ~Shared.Bool.is_eq, ~Shared.Bool.laws(), k, k0)

# a leaf holds what its node holds
def Trie.get_node(
  -V: Data,
  k: List<&2, Bool>,
  -v: V,
  q: List<&2, Bool>
) -> {
  Trie.get(
    V,
    Bin{Trie.at.here(V, k, v), Trie.at.zero(V, k, v), Trie.at.one(V, k, v)},
    q
  )
    == Trie.get(V, Leaf{k, v}, q): Maybe<&2, V>
}:
  match k q:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{False{}, q}:
      {==}
    case Nil{} Con{True{}, +q}:
      {==}
    case Con{False{}, r} Nil{}:
      {==}
    case Con{False{}, r} Con{False{}, q}:
      {==}
    case Con{False{}, r} Con{True{}, +q}:
      {==}
    case Con{True{}, r} Nil{}:
      {==}
    case Con{True{}, r} Con{False{}, q}:
      {==}
    case Con{True{}, r} Con{True{}, +q}:
      {==}

# a node in the shape of its entries holds what the node holds
def Trie.get_bin(
  -V: Data,
  h: Maybe<&2, V>,
  z: Trie<V>,
  o: Trie<V>,
  k: List<&2, Bool>
) -> {Trie.get(V, Trie.bin(V, h, z, o), k) == Trie.get(V, Bin{h, z, o}, k): Maybe<&2, V>}:
  match h z o k:
    case None{} Tip{} Tip{} Nil{}:
      {==}
    case None{} Tip{} Tip{} Con{False{}, q}:
      {==}
    case None{} Tip{} Tip{} Con{True{}, +q}:
      {==}
    case None{} Tip{} Leaf{p, x} Nil{}:
      {==}
    case None{} Tip{} Leaf{p, x} Con{False{}, q}:
      {==}
    case None{} Tip{} Leaf{p, x} Con{True{}, +q}:
      {==}
    case None{} Tip{} Bin{h2, z2, o2} q:
      {==}
    case None{} Leaf{p, x} Tip{} Nil{}:
      {==}
    case None{} Leaf{p, x} Tip{} Con{False{}, q}:
      {==}
    case None{} Leaf{p, x} Tip{} Con{True{}, +q}:
      {==}
    case None{} Leaf{p, x} Leaf{p2, x2} q:
      {==}
    case None{} Leaf{p, x} Bin{h2, z2, o2} q:
      {==}
    case None{} Bin{h1, z1, o1} o q:
      {==}
    case Some{y} Tip{} Tip{} Nil{}:
      {==}
    case Some{y} Tip{} Tip{} Con{False{}, q}:
      {==}
    case Some{y} Tip{} Tip{} Con{True{}, +q}:
      {==}
    case Some{y} Tip{} Leaf{p, x} q:
      {==}
    case Some{y} Tip{} Bin{h2, z2, o2} q:
      {==}
    case Some{y} Leaf{p, x} o q:
      {==}
    case Some{y} Bin{h1, z1, o1} o q:
      {==}

# a kept node holds what the node holds
def Trie.get_keep(
  -V: Data,
  h: Maybe<&2, V>,
  z: Trie<V>,
  o: Trie<V>,
  k: List<&2, Bool>
) -> {Trie.get(V, Trie.tidy(V, h, z, o), k) == Trie.get(V, Bin{h, z, o}, k): Maybe<&2, V>}:
  match h z o k:
    case None{} Tip{} Tip{} q:
      {==}
    case None{} Tip{} Leaf{p, x} Nil{}:
      {==}
    case None{} Tip{} Leaf{p, x} Con{False{}, q}:
      {==}
    case None{} Tip{} Leaf{p, x} Con{True{}, +q}:
      {==}
    case None{} Tip{} Bin{h2, z2, o2} q:
      {==}
    case None{} Leaf{p, x} Tip{} Nil{}:
      {==}
    case None{} Leaf{p, x} Tip{} Con{False{}, q}:
      {==}
    case None{} Leaf{p, x} Tip{} Con{True{}, +q}:
      {==}
    case None{} Leaf{p, x} Leaf{p2, x2} q:
      {==}
    case None{} Leaf{p, x} Bin{h2, z2, o2} q:
      {==}
    case None{} Bin{h1, z1, o1} o q:
      {==}
    case Some{y} Tip{} Tip{} Nil{}:
      {==}
    case Some{y} Tip{} Tip{} Con{False{}, q}:
      {==}
    case Some{y} Tip{} Tip{} Con{True{}, +q}:
      {==}
    case Some{y} Tip{} Leaf{p, x} q:
      {==}
    case Some{y} Tip{} Bin{h2, z2, o2} q:
      {==}
    case Some{y} Leaf{p, x} o q:
      {==}
    case Some{y} Bin{h1, z1, o1} o q:
      {==}

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof: it does not run
# Trie.get_set for two entries
def Trie.get_set.leaf(
  -V: Data,
  k0: List<&2, Bool>,
  +v: V,
  p: List<&2, Bool>,
  +w: V,
  k: List<&2, Bool>
) -> {
  Trie.get(
    V,
    Trie.set.leaf(V, k0, v, p, w),
    k
  )
    == Bool.pick(
      Maybe<&2, V>,
      Trie.same_key(k, k0),
      Some{v},
      Trie.get(V, Leaf{p, w}, k)
    ): Maybe<&2, V>
}:
  match k0 p k:
    case Nil{} Nil{} Nil{}:
      {==}
    case Nil{} Nil{} Con{False{}, q}:
      {==}
    case Nil{} Nil{} Con{True{}, +q}:
      {==}
    case Nil{} Con{False{}, rp} Nil{}:
      {==}
    case Nil{} Con{False{}, +rp} Con{False{}, q}:
      {==}
    case Nil{} Con{False{}, +rp} Con{True{}, +q}:
      {==}
    case Nil{} Con{True{}, +rp} Nil{}:
      {==}
    case Nil{} Con{True{}, +rp} Con{False{}, q}:
      {==}
    case Nil{} Con{True{}, +rp} Con{True{}, +q}:
      {==}
    case Con{False{}, +r0} Nil{} Nil{}:
      {==}
    case Con{False{}, +r0} Nil{} Con{False{}, q}:
      {==}
    case Con{False{}, +r0} Nil{} Con{True{}, +q}:
      {==}
    case Con{False{}, +r0} Con{False{}, +rp} Nil{}:
      Trie.get_bin(V, None{}, Trie.set.leaf(V, r0, v, rp, w), Tip{}, [])
    case Con{False{}, +r0} Con{False{}, +rp} Con{False{}, +q}:
      Equal.trans(
        Maybe<&2, V>,
        Trie.get(V, Trie.bin(V, None{}, Trie.set.leaf(V, r0, v, rp, w), Tip{}), False{} <> q),
        Trie.get(V, Trie.set.leaf(V, r0, v, rp, w), q),
        Bool.pick(Maybe<&2, V>, Trie.same_key(q, r0), Some{v}, Trie.get(V, Leaf{rp, w}, q)),
        Trie.get_bin(V, None{}, Trie.set.leaf(V, r0, v, rp, w), Tip{}, False{} <> q),
        Trie.get_set.leaf(V, r0, v, rp, w, q)
      )
    case Con{False{}, +r0} Con{False{}, +rp} Con{True{}, +q}:
      Trie.get_bin(V, None{}, Trie.set.leaf(V, r0, v, rp, w), Tip{}, True{} <> q)
    case Con{False{}, +r0} Con{True{}, +rp} Nil{}:
      {==}
    case Con{False{}, +r0} Con{True{}, +rp} Con{False{}, q}:
      {==}
    case Con{False{}, +r0} Con{True{}, +rp} Con{True{}, +q}:
      {==}
    case Con{True{}, +r0} Nil{} Nil{}:
      {==}
    case Con{True{}, +r0} Nil{} Con{False{}, q}:
      {==}
    case Con{True{}, +r0} Nil{} Con{True{}, +q}:
      {==}
    case Con{True{}, +r0} Con{False{}, +rp} Nil{}:
      {==}
    case Con{True{}, +r0} Con{False{}, +rp} Con{False{}, q}:
      {==}
    case Con{True{}, +r0} Con{False{}, +rp} Con{True{}, +q}:
      {==}
    case Con{True{}, +r0} Con{True{}, +rp} Nil{}:
      Trie.get_bin(V, None{}, Tip{}, Trie.set.leaf(V, r0, v, rp, w), [])
    case Con{True{}, +r0} Con{True{}, +rp} Con{False{}, +q}:
      Trie.get_bin(V, None{}, Tip{}, Trie.set.leaf(V, r0, v, rp, w), False{} <> q)
    case Con{True{}, +r0} Con{True{}, +rp} Con{True{}, +q}:
      Equal.trans(
        Maybe<&2, V>,
        Trie.get(V, Trie.bin(V, None{}, Tip{}, Trie.set.leaf(V, r0, v, rp, w)), True{} <> q),
        Trie.get(V, Trie.set.leaf(V, r0, v, rp, w), q),
        Bool.pick(Maybe<&2, V>, Trie.same_key(q, r0), Some{v}, Trie.get(V, Leaf{rp, w}, q)),
        Trie.get_bin(V, None{}, Tip{}, Trie.set.leaf(V, r0, v, rp, w), True{} <> q),
        Trie.get_set.leaf(V, r0, v, rp, w, q)
      )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

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
      {==}
    case Leaf{p, w} p0 q:
      Trie.get_set.leaf(ty, p0, v, p, w, q)
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

# a trie joined with nothing is itself
def Trie.union_tip(
  ~V: Data,
  ~join: V -> V -> V,
  a: Trie<V>
) -> {Trie.union(~V, ~join, a, Tip{}) == a: Trie<V>}:
  match a:
    case Tip{}:
      {==}
    case Leaf{k, v}:
      {==}
    case Bin{h, z, o}:
      {==}

# Trie.get_union at a node, from its parts
def Trie.get_union.node(
  ~V: Data,
  ~join: V -> V -> V,
  -h1: Maybe<&2, V>,
  -z1: Trie<V>,
  -o1: Trie<V>,
  -h2: Maybe<&2, V>,
  -z2: Trie<V>,
  -o2: Trie<V>,
  k: List<&2, Bool>,
  ihz: @q: List<
    &2,
    Bool> -> {
    Trie.get(
      V,
      Trie.union(~V, ~join, z1, z2),
      q
    )
      == Shared.Maybe.join(~V, ~join, Trie.get(V, z1, q), Trie.get(V, z2, q)): Maybe<&2, V>
  },
  iho: @q: List<
    &2,
    Bool> -> {
    Trie.get(
      V,
      Trie.union(~V, ~join, o1, o2),
      q
    )
      == Shared.Maybe.join(~V, ~join, Trie.get(V, o1, q), Trie.get(V, o2, q)): Maybe<&2, V>
  }
) -> {
  Trie.get(
    V,
    Bin{
      Shared.Maybe.join(~V, ~join, h1, h2),
      Trie.union(~V, ~join, z1, z2),
      Trie.union(~V, ~join, o1, o2)
    },
    k
  )
    == Shared.Maybe.join(
      ~V,
      ~join,
      Trie.get(V, Bin{h1, z1, o1}, k),
      Trie.get(V, Bin{h2, z2, o2}, k)
    ): Maybe<&2, V>
}:
  match k:
    case Nil{}:
      {==}
    case Con{False{}, q}:
      ihz(q)
    case Con{True{}, q}:
      iho(q)

# Trie.get_union for two entries
def Trie.get_union.fork(
  ~V: Data,
  ~join: V -> V -> V,
  k1: List<&2, Bool>,
  +v: V,
  p: List<&2, Bool>,
  +w: V,
  k: List<&2, Bool>
) -> {
  Trie.get(
    V,
    Trie.union.fork(~V, ~join, k1, v, p, w),
    k
  )
    == Shared.Maybe.join(
      ~V,
      ~join,
      Trie.get(V, Leaf{k1, v}, k),
      Trie.get(V, Leaf{p, w}, k)
    ): Maybe<&2, V>
}:
  match k1 p k:
    case Nil{} Nil{} Nil{}:
      {==}
    case Nil{} Nil{} Con{False{}, q}:
      {==}
    case Nil{} Nil{} Con{True{}, +q}:
      {==}
    case Nil{} Con{False{}, rp} Nil{}:
      {==}
    case Nil{} Con{False{}, +rp} Con{False{}, q}:
      {==}
    case Nil{} Con{False{}, +rp} Con{True{}, +q}:
      {==}
    case Nil{} Con{True{}, +rp} Nil{}:
      {==}
    case Nil{} Con{True{}, +rp} Con{False{}, q}:
      {==}
    case Nil{} Con{True{}, +rp} Con{True{}, +q}:
      {==}
    case Con{False{}, +r1} Nil{} Nil{}:
      {==}
    case Con{False{}, +r1} Nil{} Con{False{}, q}:
      Equal.sym(
        Maybe<&2, V>,
        Shared.Maybe.join(~V, ~join, Trie.get(V, Leaf{r1, v}, q), None{}),
        Trie.get(V, Leaf{r1, v}, q),
        Shared.Maybe.join_none(~V, ~join, Trie.get(V, Leaf{r1, v}, q))
      )
    case Con{False{}, +r1} Nil{} Con{True{}, +q}:
      {==}
    case Con{False{}, +r1} Con{False{}, +rp} Nil{}:
      Trie.get_bin(V, None{}, Trie.union.fork(~V, ~join, r1, v, rp, w), Tip{}, [])
    case Con{False{}, +r1} Con{False{}, +rp} Con{False{}, +q}:
      Equal.trans(
        Maybe<&2, V>,
        Trie.get(
          V,
          Trie.bin(V, None{}, Trie.union.fork(~V, ~join, r1, v, rp, w), Tip{}),
          False{} <> q
        ),
        Trie.get(V, Trie.union.fork(~V, ~join, r1, v, rp, w), q),
        Shared.Maybe.join(~V, ~join, Trie.get(V, Leaf{r1, v}, q), Trie.get(V, Leaf{rp, w}, q)),
        Trie.get_bin(V, None{}, Trie.union.fork(~V, ~join, r1, v, rp, w), Tip{}, False{} <> q),
        Trie.get_union.fork(~V, ~join, r1, v, rp, w, q)
      )
    case Con{False{}, +r1} Con{False{}, +rp} Con{True{}, +q}:
      Trie.get_bin(V, None{}, Trie.union.fork(~V, ~join, r1, v, rp, w), Tip{}, True{} <> q)
    case Con{False{}, +r1} Con{True{}, +rp} Nil{}:
      {==}
    case Con{False{}, +r1} Con{True{}, +rp} Con{False{}, q}:
      Equal.sym(
        Maybe<&2, V>,
        Shared.Maybe.join(~V, ~join, Trie.get(V, Leaf{r1, v}, q), None{}),
        Trie.get(V, Leaf{r1, v}, q),
        Shared.Maybe.join_none(~V, ~join, Trie.get(V, Leaf{r1, v}, q))
      )
    case Con{False{}, +r1} Con{True{}, +rp} Con{True{}, +q}:
      {==}
    case Con{True{}, +r1} Nil{} Nil{}:
      {==}
    case Con{True{}, +r1} Nil{} Con{False{}, q}:
      {==}
    case Con{True{}, +r1} Nil{} Con{True{}, +q}:
      Equal.sym(
        Maybe<&2, V>,
        Shared.Maybe.join(~V, ~join, Trie.get(V, Leaf{r1, v}, q), None{}),
        Trie.get(V, Leaf{r1, v}, q),
        Shared.Maybe.join_none(~V, ~join, Trie.get(V, Leaf{r1, v}, q))
      )
    case Con{True{}, +r1} Con{False{}, +rp} Nil{}:
      {==}
    case Con{True{}, +r1} Con{False{}, +rp} Con{False{}, q}:
      {==}
    case Con{True{}, +r1} Con{False{}, +rp} Con{True{}, +q}:
      Equal.sym(
        Maybe<&2, V>,
        Shared.Maybe.join(~V, ~join, Trie.get(V, Leaf{r1, v}, q), None{}),
        Trie.get(V, Leaf{r1, v}, q),
        Shared.Maybe.join_none(~V, ~join, Trie.get(V, Leaf{r1, v}, q))
      )
    case Con{True{}, +r1} Con{True{}, +rp} Nil{}:
      Trie.get_bin(V, None{}, Tip{}, Trie.union.fork(~V, ~join, r1, v, rp, w), [])
    case Con{True{}, +r1} Con{True{}, +rp} Con{False{}, +q}:
      Trie.get_bin(V, None{}, Tip{}, Trie.union.fork(~V, ~join, r1, v, rp, w), False{} <> q)
    case Con{True{}, +r1} Con{True{}, +rp} Con{True{}, +q}:
      Equal.trans(
        Maybe<&2, V>,
        Trie.get(
          V,
          Trie.bin(V, None{}, Tip{}, Trie.union.fork(~V, ~join, r1, v, rp, w)),
          True{} <> q
        ),
        Trie.get(V, Trie.union.fork(~V, ~join, r1, v, rp, w), q),
        Shared.Maybe.join(~V, ~join, Trie.get(V, Leaf{r1, v}, q), Trie.get(V, Leaf{rp, w}, q)),
        Trie.get_bin(V, None{}, Tip{}, Trie.union.fork(~V, ~join, r1, v, rp, w), True{} <> q),
        Trie.get_union.fork(~V, ~join, r1, v, rp, w, q)
      )

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Trie.get_union for an entry and a trie
def Trie.get_union.leaf(
  ~V: Data,
  ~join: V -> V -> V,
  y: Trie<V>,
  k1: List<&2, Bool>,
  v: V,
  k: List<&2, Bool>
) -> {
  Trie.get(
    V,
    Trie.union.leaf(~V, ~join, y, k1, v),
    k
  )
    == Shared.Maybe.join(~V, ~join, Trie.get(V, Leaf{k1, v}, k), Trie.get(V, y, k)): Maybe<&2, V>
}:
  match y k1 k:
    case Tip{} +p +q:
      Equal.sym(
        Maybe<&2, V>,
        Shared.Maybe.join(~V, ~join, Trie.get(V, Leaf{p, v}, q), None{}),
        Trie.get(V, Leaf{p, v}, q),
        Shared.Maybe.join_none(~V, ~join, Trie.get(V, Leaf{p, v}, q))
      )
    case Leaf{p, w} p1 q:
      Trie.get_union.fork(~V, ~join, p1, v, p, w, q)
    case Bin{h, z, o} Nil{} Nil{}:
      {==}
    case Bin{h, z, o} Nil{} Con{False{}, q}:
      {==}
    case Bin{h, z, o} Nil{} Con{True{}, +q}:
      {==}
    case Bin{h, z, o} Con{False{}, r1} Nil{}:
      {==}
    case Bin{h, z, o} Con{False{}, +r1} Con{False{}, q}:
      Trie.get_union.leaf(~V, ~join, z, r1, v, q)
    case Bin{h, z, o} Con{False{}, +r1} Con{True{}, +q}:
      {==}
    case Bin{h, z, o} Con{True{}, +r1} Nil{}:
      {==}
    case Bin{h, z, o} Con{True{}, +r1} Con{False{}, q}:
      {==}
    case Bin{h, z, o} Con{True{}, +r1} Con{True{}, +q}:
      Trie.get_union.leaf(~V, ~join, o, r1, v, q)
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

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
    case Leaf{p, v} y q:
      Trie.get_union.leaf(~ty, ~join, y, p, v, q)
    case Bin{h, z, o} Tip{} q:
      get1 = Trie.get(ty, Bin{h, z, o}, q)
      Equal.sym(
        Maybe<&2, ty>,
        Shared.Maybe.join(~ty, ~join, get1, None{}),
        get1,
        Shared.Maybe.join_none(~ty, ~join, get1)
      )
    case Bin{h, +z, +o} Leaf{+p, +w} +q:
      %Trie.get_node(
        ty,
        p,
        w,
        q
      ): {
        Trie.get(
          ty,
          Trie.union(~ty, ~join, Bin{h, z, o}, Leaf{p, w}),
          q
        )
          == Shared.Maybe.join(~ty, ~join, Trie.get(ty, Bin{h, z, o}, q), _): Maybe<&2, ty>
      }
      Trie.get_union.node(
        ~ty,
        ~join,
        h,
        z,
        o,
        Trie.at.here(ty, p, w),
        Trie.at.zero(ty, p, w),
        Trie.at.one(ty, p, w),
        q,
        r => Trie.get_union(~ty, ~join, z, Trie.at.zero(ty, p, w), r),
        r => Trie.get_union(~ty, ~join, o, Trie.at.one(ty, p, w), r)
      )
    case Bin{h1, z1, o1} Bin{h2, z2, o2} Nil{}:
      {==}
    case Bin{h1, z1, o1} Bin{h2, z2, o2} Con{False{}, r}:
      Trie.get_union(~ty, ~join, z1, z2, r)
    case Bin{h1, z1, o1} Bin{h2, z2, o2} Con{True{}, r}:
      Trie.get_union(~ty, ~join, o1, o2, r)
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# Laws of unions
# --------------

# t has no node and no entry
def Trie.is_tip(-V: Data, t: Trie<V>) -> Bool:
  match t:
    case Tip{}:
      True{}
    case _:
      False{}

# True is not False
def Trie.true_ne_false(e: {True{} == False{}: Bool}) -> Empty:
  Shared.Bool.false_ne_true(Equal.sym(Bool, True{}, False{}, e))

# a node with a part that is not a tip is not a tip
def Trie.bin_part.f(
  -V: Data,
  x: Trie<V>
) -> {
  Trie.is_tip(V, x) == False{}: Bool
} -> {Trie.is_tip(V, Trie.bin(V, None{}, x, Tip{})) == False{}: Bool}:
  match x:
    case Tip{}:
      e => Empty.absurd(
        {Trie.is_tip(V, Trie.bin(V, None{}, Tip{}, Tip{})) == False{}: Bool},
        Trie.true_ne_false(e)
      )
    case Leaf{p, w}:
      e => {==}
    case Bin{h, z, o}:
      e => {==}

# a node with a part that is not a tip is not a tip
def Trie.bin_part.t(
  -V: Data,
  x: Trie<V>
) -> {
  Trie.is_tip(V, x) == False{}: Bool
} -> {Trie.is_tip(V, Trie.bin(V, None{}, Tip{}, x)) == False{}: Bool}:
  match x:
    case Tip{}:
      e => Empty.absurd(
        {Trie.is_tip(V, Trie.bin(V, None{}, Tip{}, Tip{})) == False{}: Bool},
        Trie.true_ne_false(e)
      )
    case Leaf{p, w}:
      e => {==}
    case Bin{h, z, o}:
      e => {==}

# the trie of two entries is not a tip
def Trie.fork_part(
  ~V: Data,
  ~join: V -> V -> V,
  k: List<&2, Bool>,
  +v: V,
  p: List<&2, Bool>,
  +w: V
) -> {Trie.is_tip(V, Trie.union.fork(~V, ~join, k, v, p, w)) == False{}: Bool}:
  match k p:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{False{}, q}:
      {==}
    case Nil{} Con{True{}, +q}:
      {==}
    case Con{False{}, +r} Nil{}:
      {==}
    case Con{False{}, +r} Con{False{}, +q}:
      Trie.bin_part.f(
        V,
        Trie.union.fork(~V, ~join, r, v, q, w)
      )(Trie.fork_part(~V, ~join, r, v, q, w))
    case Con{False{}, +r} Con{True{}, +q}:
      {==}
    case Con{True{}, +r} Nil{}:
      {==}
    case Con{True{}, +r} Con{False{}, +q}:
      {==}
    case Con{True{}, +r} Con{True{}, +q}:
      Trie.bin_part.t(
        V,
        Trie.union.fork(~V, ~join, r, v, q, w)
      )(Trie.fork_part(~V, ~join, r, v, q, w))

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# a node joined with a node in the shape of its entries
def Trie.union_bin(
  ~V: Data,
  ~join: V -> V -> V,
  h: Maybe<&2, V>,
  z: Trie<V>,
  o: Trie<V>,
  h1: Maybe<&2, V>,
  z1: Trie<V>,
  o1: Trie<V>
) -> {
  Bin{
    Shared.Maybe.join(~V, ~join, h, h1),
    Trie.union(~V, ~join, z, z1),
    Trie.union(~V, ~join, o, o1)
  }
    == Trie.union(~V, ~join, Bin{h, z, o}, Trie.bin(V, h1, z1, o1)): Trie<V>
}:
  match h1 z1 o1:
    case None{} Tip{} Tip{}:
      %Equal.sym(
        Maybe<&2, V>,
        Shared.Maybe.join(~V, ~join, h, None{}),
        h,
        Shared.Maybe.join_none(~V, ~join, h)
      ): {
        Bin{
          _,
          Trie.union(~V, ~join, z, Tip{}),
          Trie.union(~V, ~join, o, Tip{})
        }
          == Bin{h, z, o}: Trie<V>
      }
      %Equal.sym(Trie<V>, Trie.union(~V, ~join, z, Tip{}), z, Trie.union_tip(~V, ~join, z)):
        {Bin{h, _, Trie.union(~V, ~join, o, Tip{})} == Bin{h, z, o}: Trie<V>}
      %Equal.sym(Trie<V>, Trie.union(~V, ~join, o, Tip{}), o, Trie.union_tip(~V, ~join, o)):
        {Bin{h, z, _} == Bin{h, z, o}: Trie<V>}
      {==}
    case None{} Tip{} Leaf{p, x}:
      {==}
    case None{} Tip{} Bin{h2, z2, o2}:
      {==}
    case None{} Leaf{p, x} Tip{}:
      {==}
    case None{} Leaf{p, x} Leaf{p2, x2}:
      {==}
    case None{} Leaf{p, x} Bin{h2, z2, o2}:
      {==}
    case None{} Bin{h1, z1, o1} o0:
      {==}
    case Some{y} Tip{} Tip{}:
      {==}
    case Some{y} Tip{} Leaf{p, x}:
      {==}
    case Some{y} Tip{} Bin{h2, z2, o2}:
      {==}
    case Some{y} Leaf{p, x} o0:
      {==}
    case Some{y} Bin{h1, z1, o1} o0:
      {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# a node in the shape of its entries joined with a node
def Trie.bin_union(
  ~V: Data,
  ~join: V -> V -> V,
  h1: Maybe<&2, V>,
  z1: Trie<V>,
  o1: Trie<V>,
  -h: Maybe<&2, V>,
  -z: Trie<V>,
  -o: Trie<V>
) -> {
  Bin{
    Shared.Maybe.join(~V, ~join, h1, h),
    Trie.union(~V, ~join, z1, z),
    Trie.union(~V, ~join, o1, o)
  }
    == Trie.union(~V, ~join, Trie.bin(V, h1, z1, o1), Bin{h, z, o}): Trie<V>
}:
  match h1 z1 o1:
    case None{} Tip{} Tip{}:
      {==}
    case None{} Tip{} Leaf{p, x}:
      {==}
    case None{} Tip{} Bin{h2, z2, o2}:
      {==}
    case None{} Leaf{p, x} Tip{}:
      {==}
    case None{} Leaf{p, x} Leaf{p2, x2}:
      {==}
    case None{} Leaf{p, x} Bin{h2, z2, o2}:
      {==}
    case None{} Bin{h1, z1, o1} o0:
      {==}
    case Some{y} Tip{} Tip{}:
      {==}
    case Some{y} Tip{} Leaf{p, x}:
      {==}
    case Some{y} Tip{} Bin{h2, z2, o2}:
      {==}
    case Some{y} Leaf{p, x} o0:
      {==}
    case Some{y} Bin{h1, z1, o1} o0:
      {==}

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Trie.union_comm at a node, from its parts
def Trie.union_comm.node(
  ~V: Data,
  ~join: V -> V -> V,
  ~comm: @x: V -> @y: V -> {join(x, y) == join(y, x): V},
  h1: Maybe<&2, V>,
  -z1: Trie<V>,
  -o1: Trie<V>,
  h2: Maybe<&2, V>,
  -z2: Trie<V>,
  -o2: Trie<V>,
  ez: {Trie.union(~V, ~join, z1, z2) == Trie.union(~V, ~join, z2, z1): Trie<V>},
  eo: {Trie.union(~V, ~join, o1, o2) == Trie.union(~V, ~join, o2, o1): Trie<V>}
) -> {
  Bin{
    Shared.Maybe.join(~V, ~join, h1, h2),
    Trie.union(~V, ~join, z1, z2),
    Trie.union(~V, ~join, o1, o2)
  }
    == Bin{
      Shared.Maybe.join(~V, ~join, h2, h1),
      Trie.union(~V, ~join, z2, z1),
      Trie.union(~V, ~join, o2, o1)
    }: Trie<V>
}:
  -pick1 = Shared.Maybe.join(~V, ~join, h1, h2)
  -union1 = Trie.union(~V, ~join, z1, z2)
  -union2 = Trie.union(~V, ~join, o1, o2)
  -union3 = Trie.union(~V, ~join, o2, o1)
  %Shared.Maybe.join_comm(~V, ~join, ~comm, h1, h2):
    {Bin{pick1, union1, union2} == Bin{_, Trie.union(~V, ~join, z2, z1), union3}: Trie<V>}
  %ez:
    {Bin{pick1, union1, union2} == Bin{pick1, _, union3}: Trie<V>}
  %eo:
    {Bin{pick1, union1, union2} == Bin{pick1, union1, _}: Trie<V>}
  {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# Trie.union_comm for two entries
def Trie.union_comm.fork(
  ~V: Data,
  ~join: V -> V -> V,
  ~comm: @x: V -> @y: V -> {join(x, y) == join(y, x): V},
  k: List<&2, Bool>,
  v: V,
  p: List<&2, Bool>,
  w: V
) -> {Trie.union.fork(~V, ~join, k, v, p, w) == Trie.union.fork(~V, ~join, p, w, k, v): Trie<V>}:
  match k p:
    case Nil{} Nil{}:
      Equal.cong(V, Trie<V>, x => Leaf{[], x}, join(v, w), join(w, v), comm(v)(w))
    case Nil{} Con{False{}, q}:
      {==}
    case Nil{} Con{True{}, +q}:
      {==}
    case Con{False{}, r} Nil{}:
      {==}
    case Con{False{}, +r} Con{False{}, q}:
      Equal.cong(
        Trie<V>,
        Trie<V>,
        x => Trie.bin(V, None{}, x, Tip{}),
        Trie.union.fork(~V, ~join, r, v, q, w),
        Trie.union.fork(~V, ~join, q, w, r, v),
        Trie.union_comm.fork(~V, ~join, ~comm, r, v, q, w)
      )
    case Con{False{}, +r} Con{True{}, +q}:
      {==}
    case Con{True{}, +r} Nil{}:
      {==}
    case Con{True{}, +r} Con{False{}, q}:
      {==}
    case Con{True{}, +r} Con{True{}, +q}:
      Equal.cong(
        Trie<V>,
        Trie<V>,
        x => Trie.bin(V, None{}, Tip{}, x),
        Trie.union.fork(~V, ~join, r, v, q, w),
        Trie.union.fork(~V, ~join, q, w, r, v),
        Trie.union_comm.fork(~V, ~join, ~comm, r, v, q, w)
      )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Trie.union_comm for an entry and a trie
def Trie.union_comm.leaf(
  ~V: Data,
  ~join: V -> V -> V,
  ~comm: @x: V -> @y: V -> {join(x, y) == join(y, x): V},
  y: Trie<V>,
  k: List<&2, Bool>,
  v: V
) -> {Trie.union.leaf(~V, ~join, y, k, v) == Trie.union(~V, ~join, y, Leaf{k, v}): Trie<V>}:
  match y k:
    case Tip{} r:
      {==}
    case Leaf{p, w} r:
      Trie.union_comm.fork(~V, ~join, ~comm, r, v, p, w)
    case Bin{h, z, o} Nil{}:
      Trie.union_comm.node(
        ~V,
        ~join,
        ~comm,
        Some{v},
        Tip{},
        Tip{},
        h,
        z,
        o,
        Equal.sym(Trie<V>, Trie.union(~V, ~join, z, Tip{}), z, Trie.union_tip(~V, ~join, z)),
        Equal.sym(Trie<V>, Trie.union(~V, ~join, o, Tip{}), o, Trie.union_tip(~V, ~join, o))
      )
    case Bin{h, +z, +o} Con{False{}, r}:
      Trie.union_comm.node(
        ~V,
        ~join,
        ~comm,
        None{},
        Leaf{r, v},
        Tip{},
        h,
        z,
        o,
        Trie.union_comm.leaf(~V, ~join, ~comm, z, r, v),
        Equal.sym(Trie<V>, Trie.union(~V, ~join, o, Tip{}), o, Trie.union_tip(~V, ~join, o))
      )
    case Bin{h, +z, +o} Con{True{}, r}:
      Trie.union_comm.node(
        ~V,
        ~join,
        ~comm,
        None{},
        Tip{},
        Leaf{r, v},
        h,
        z,
        o,
        Equal.sym(Trie<V>, Trie.union(~V, ~join, z, Tip{}), z, Trie.union_tip(~V, ~join, z)),
        Trie.union_comm.leaf(~V, ~join, ~comm, o, r, v)
      )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# a union is the same either way round
law Trie.union_comm:
  for ~V: Data
  for ~join: V -> V -> V
  for ~comm: @x: V -> @y: V -> {join(x, y) == join(y, x): V}
  for a: Trie<V>
  for b: Trie<V>
  {Trie.union(~V, ~join, a, b) == Trie.union(~V, ~join, b, a): Trie<V>}

# bend-lint: expect-begin bend-lint-rules/performance/missed_fork@hint -- a proof: it does not run
def Trie.union_comm(ty, join, comm, a, b):
  match a b:
    case Tip{} Tip{}:
      {==}
    case Tip{} Leaf{k, v}:
      {==}
    case Tip{} Bin{h, z, o}:
      {==}
    case Leaf{k, v} y:
      Trie.union_comm.leaf(~ty, ~join, ~comm, y, k, v)
    case Bin{h, z, o} Tip{}:
      {==}
    case Bin{+h, +z, +o} Leaf{k, w}:
      Equal.sym(
        Trie<ty>,
        Trie.union.leaf(~ty, ~join, Bin{h, z, o}, k, w),
        Trie.union(~ty, ~join, Bin{h, z, o}, Leaf{k, w}),
        Trie.union_comm.leaf(~ty, ~join, ~comm, Bin{h, z, o}, k, w)
      )
    case Bin{h1, z1, o1} Bin{h2, z2, o2}:
      Trie.union_comm.node(
        ~ty,
        ~join,
        ~comm,
        h1,
        z1,
        o1,
        h2,
        z2,
        o2,
        Trie.union_comm(~ty, ~join, ~comm, z1, z2),
        Trie.union_comm(~ty, ~join, ~comm, o1, o2)
      )
# bend-lint: expect-end bend-lint-rules/performance/missed_fork@hint

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Trie.union_assoc at a node, from its parts
def Trie.union_assoc.node(
  ~V: Data,
  ~join: V -> V -> V,
  ~assoc: @x: V -> @y: V -> @z: V -> {join(join(x, y), z) == join(x, join(y, z)): V},
  h1: Maybe<&2, V>,
  -z1: Trie<V>,
  -o1: Trie<V>,
  h2: Maybe<&2, V>,
  -z2: Trie<V>,
  -o2: Trie<V>,
  h3: Maybe<&2, V>,
  -z3: Trie<V>,
  -o3: Trie<V>,
  ez: {
    Trie.union(
      ~V,
      ~join,
      Trie.union(~V, ~join, z1, z2),
      z3
    )
      == Trie.union(~V, ~join, z1, Trie.union(~V, ~join, z2, z3)): Trie<V>
  },
  eo: {
    Trie.union(
      ~V,
      ~join,
      Trie.union(~V, ~join, o1, o2),
      o3
    )
      == Trie.union(~V, ~join, o1, Trie.union(~V, ~join, o2, o3)): Trie<V>
  }
) -> {
  Bin{
    Shared.Maybe.join(~V, ~join, Shared.Maybe.join(~V, ~join, h1, h2), h3),
    Trie.union(~V, ~join, Trie.union(~V, ~join, z1, z2), z3),
    Trie.union(~V, ~join, Trie.union(~V, ~join, o1, o2), o3)
  }
    == Bin{
      Shared.Maybe.join(~V, ~join, h1, Shared.Maybe.join(~V, ~join, h2, h3)),
      Trie.union(~V, ~join, z1, Trie.union(~V, ~join, z2, z3)),
      Trie.union(~V, ~join, o1, Trie.union(~V, ~join, o2, o3))
    }: Trie<V>
}:
  -left1 = Shared.Maybe.join(~V, ~join, Shared.Maybe.join(~V, ~join, h1, h2), h3)
  -left2 = Trie.union(~V, ~join, Trie.union(~V, ~join, z1, z2), z3)
  -left3 = Trie.union(~V, ~join, Trie.union(~V, ~join, o1, o2), o3)
  %Shared.Maybe.join_assoc(~V, ~join, ~assoc, h1, h2, h3):
    {
      Bin{
        left1,
        left2,
        left3
      }
        == Bin{
          _,
          Trie.union(~V, ~join, z1, Trie.union(~V, ~join, z2, z3)),
          Trie.union(~V, ~join, o1, Trie.union(~V, ~join, o2, o3))
        }: Trie<V>
    }
  %ez:
    {
      Bin{
        left1,
        left2,
        left3
      }
        == Bin{left1, _, Trie.union(~V, ~join, o1, Trie.union(~V, ~join, o2, o3))}: Trie<V>
    }
  %eo:
    {Bin{left1, left2, left3} == Bin{left1, left2, _}: Trie<V>}
  {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# an entry joined with a node is the node of their parts
def Trie.leaf_bin(
  ~V: Data,
  ~join: V -> V -> V,
  k: List<&2, Bool>,
  -v: V,
  -h: Maybe<&2, V>,
  -z: Trie<V>,
  -o: Trie<V>
) -> {
  Bin{
    Shared.Maybe.join(~V, ~join, Trie.at.here(V, k, v), h),
    Trie.union(~V, ~join, Trie.at.zero(V, k, v), z),
    Trie.union(~V, ~join, Trie.at.one(V, k, v), o)
  }
    == Trie.union.leaf(~V, ~join, Bin{h, z, o}, k, v): Trie<V>
}:
  match k:
    case Nil{}:
      {==}
    case Con{False{}, r}:
      {==}
    case Con{True{}, r}:
      {==}

# two entries joined are the node of their parts, in the shape of its entries
def Trie.fork_node(
  ~V: Data,
  ~join: V -> V -> V,
  k: List<&2, Bool>,
  -v: V,
  p: List<&2, Bool>,
  -w: V
) -> {
  Trie.bin(
    V,
    Shared.Maybe.join(~V, ~join, Trie.at.here(V, k, v), Trie.at.here(V, p, w)),
    Trie.union(~V, ~join, Trie.at.zero(V, k, v), Trie.at.zero(V, p, w)),
    Trie.union(~V, ~join, Trie.at.one(V, k, v), Trie.at.one(V, p, w))
  )
    == Trie.union.fork(~V, ~join, k, v, p, w): Trie<V>
}:
  match k p:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{False{}, q}:
      {==}
    case Nil{} Con{True{}, q}:
      {==}
    case Con{False{}, r} Nil{}:
      {==}
    case Con{False{}, r} Con{False{}, q}:
      {==}
    case Con{False{}, r} Con{True{}, q}:
      {==}
    case Con{True{}, r} Nil{}:
      {==}
    case Con{True{}, r} Con{False{}, q}:
      {==}
    case Con{True{}, r} Con{True{}, q}:
      {==}

# a zero part joined with an entry at the empty key
def Trie.union_assoc.end.f(
  ~V: Data,
  ~join: V -> V -> V,
  x: Trie<V>,
  -v: V
) -> {
  Trie.is_tip(V, x) == False{}: Bool
} -> {
  Trie.union(
    ~V,
    ~join,
    Trie.bin(V, None{}, x, Tip{}),
    Leaf{[], v}
  )
    == Bin{Some{v}, x, Tip{}}: Trie<V>
}:
  match x:
    case Tip{}:
      e => Empty.absurd(
        {
          Trie.union(
            ~V,
            ~join,
            Trie.bin(V, None{}, Tip{}, Tip{}),
            Leaf{[], v}
          )
            == Bin{Some{v}, Tip{}, Tip{}}: Trie<V>
        },
        Trie.true_ne_false(e)
      )
    case Leaf{p, w}:
      e => {==}
    case Bin{h, z, o}:
      e => {==}

# a zero part joined with an entry of the other part
def Trie.union_assoc.far.f(
  ~V: Data,
  ~join: V -> V -> V,
  x: Trie<V>,
  -r: List<&2, Bool>,
  -v: V
) -> {
  Trie.is_tip(V, x) == False{}: Bool
} -> {
  Trie.union(
    ~V,
    ~join,
    Trie.bin(V, None{}, x, Tip{}),
    Leaf{True{} <> r, v}
  )
    == Bin{None{}, x, Leaf{r, v}}: Trie<V>
}:
  match x:
    case Tip{}:
      e => Empty.absurd(
        {
          Trie.union(
            ~V,
            ~join,
            Trie.bin(V, None{}, Tip{}, Tip{}),
            Leaf{True{} <> r, v}
          )
            == Bin{None{}, Tip{}, Leaf{r, v}}: Trie<V>
        },
        Trie.true_ne_false(e)
      )
    case Leaf{p, w}:
      e => {==}
    case Bin{h, z, o}:
      e => {==}

# a zero part joined with an entry of that part
def Trie.union_assoc.in.f(
  ~V: Data,
  ~join: V -> V -> V,
  x: Trie<V>,
  -r: List<&2, Bool>,
  -v: V
) -> {
  Trie.union(
    ~V,
    ~join,
    Trie.bin(V, None{}, x, Tip{}),
    Leaf{False{} <> r, v}
  )
    == Trie.bin(V, None{}, Trie.union(~V, ~join, x, Leaf{r, v}), Tip{}): Trie<V>
}:
  match x:
    case Tip{}:
      {==}
    case Leaf{p, w}:
      {==}
    case Bin{h, z, o}:
      {==}

# an entry at the empty key joined with a zero part
def Trie.union_assoc.end_left.f(
  ~V: Data,
  ~join: V -> V -> V,
  x: Trie<V>,
  -v: V
) -> {
  Trie.is_tip(V, x) == False{}: Bool
} -> {
  Bin{
    Some{v},
    x,
    Tip{}
  }
    == Trie.union.leaf(~V, ~join, Trie.bin(V, None{}, x, Tip{}), [], v): Trie<V>
}:
  match x:
    case Tip{}:
      e => Empty.absurd(
        {
          Bin{
            Some{v},
            Tip{},
            Tip{}
          }
            == Trie.union.leaf(~V, ~join, Trie.bin(V, None{}, Tip{}, Tip{}), [], v): Trie<V>
        },
        Trie.true_ne_false(e)
      )
    case Leaf{p, w}:
      e => {==}
    case Bin{h, z, o}:
      e => {==}

# an entry of the other part joined with a zero part
def Trie.union_assoc.far_left.f(
  ~V: Data,
  ~join: V -> V -> V,
  x: Trie<V>,
  -r: List<&2, Bool>,
  -v: V
) -> {
  Trie.is_tip(V, x) == False{}: Bool
} -> {
  Bin{
    None{},
    x,
    Leaf{r, v}
  }
    == Trie.union.leaf(~V, ~join, Trie.bin(V, None{}, x, Tip{}), True{} <> r, v): Trie<V>
}:
  match x:
    case Tip{}:
      e => Empty.absurd(
        {
          Bin{
            None{},
            Tip{},
            Leaf{r, v}
          }
            == Trie.union.leaf(
              ~V,
              ~join,
              Trie.bin(V, None{}, Tip{}, Tip{}),
              True{} <> r,
              v
            ): Trie<V>
        },
        Trie.true_ne_false(e)
      )
    case Leaf{p, w}:
      e => {==}
    case Bin{h, z, o}:
      e => {==}

# an entry of a zero part joined with that part
def Trie.union_assoc.in_left.f(
  ~V: Data,
  ~join: V -> V -> V,
  x: Trie<V>,
  r: List<&2, Bool>,
  -v: V
) -> {
  Trie.bin(
    V,
    None{},
    Trie.union.leaf(~V, ~join, x, r, v),
    Tip{}
  )
    == Trie.union.leaf(~V, ~join, Trie.bin(V, None{}, x, Tip{}), False{} <> r, v): Trie<V>
}:
  match x r:
    case Tip{} q:
      {==}
    case Leaf{p, w} q:
      {==}
    case Bin{h, z, o} Nil{}:
      {==}
    case Bin{h, z, o} Con{False{}, q}:
      {==}
    case Bin{h, z, o} Con{True{}, q}:
      {==}

# a one part joined with an entry at the empty key
def Trie.union_assoc.end.t(
  ~V: Data,
  ~join: V -> V -> V,
  x: Trie<V>,
  -v: V
) -> {
  Trie.is_tip(V, x) == False{}: Bool
} -> {
  Trie.union(
    ~V,
    ~join,
    Trie.bin(V, None{}, Tip{}, x),
    Leaf{[], v}
  )
    == Bin{Some{v}, Tip{}, x}: Trie<V>
}:
  match x:
    case Tip{}:
      e => Empty.absurd(
        {
          Trie.union(
            ~V,
            ~join,
            Trie.bin(V, None{}, Tip{}, Tip{}),
            Leaf{[], v}
          )
            == Bin{Some{v}, Tip{}, Tip{}}: Trie<V>
        },
        Trie.true_ne_false(e)
      )
    case Leaf{p, w}:
      e => {==}
    case Bin{h, z, o}:
      e => {==}

# a one part joined with an entry of the other part
def Trie.union_assoc.far.t(
  ~V: Data,
  ~join: V -> V -> V,
  x: Trie<V>,
  -r: List<&2, Bool>,
  -v: V
) -> {
  Trie.is_tip(V, x) == False{}: Bool
} -> {
  Trie.union(
    ~V,
    ~join,
    Trie.bin(V, None{}, Tip{}, x),
    Leaf{False{} <> r, v}
  )
    == Bin{None{}, Leaf{r, v}, x}: Trie<V>
}:
  match x:
    case Tip{}:
      e => Empty.absurd(
        {
          Trie.union(
            ~V,
            ~join,
            Trie.bin(V, None{}, Tip{}, Tip{}),
            Leaf{False{} <> r, v}
          )
            == Bin{None{}, Leaf{r, v}, Tip{}}: Trie<V>
        },
        Trie.true_ne_false(e)
      )
    case Leaf{p, w}:
      e => {==}
    case Bin{h, z, o}:
      e => {==}

# a one part joined with an entry of that part
def Trie.union_assoc.in.t(
  ~V: Data,
  ~join: V -> V -> V,
  x: Trie<V>,
  -r: List<&2, Bool>,
  -v: V
) -> {
  Trie.union(
    ~V,
    ~join,
    Trie.bin(V, None{}, Tip{}, x),
    Leaf{True{} <> r, v}
  )
    == Trie.bin(V, None{}, Tip{}, Trie.union(~V, ~join, x, Leaf{r, v})): Trie<V>
}:
  match x:
    case Tip{}:
      {==}
    case Leaf{p, w}:
      {==}
    case Bin{h, z, o}:
      {==}

# an entry at the empty key joined with a one part
def Trie.union_assoc.end_left.t(
  ~V: Data,
  ~join: V -> V -> V,
  x: Trie<V>,
  -v: V
) -> {
  Trie.is_tip(V, x) == False{}: Bool
} -> {
  Bin{
    Some{v},
    Tip{},
    x
  }
    == Trie.union.leaf(~V, ~join, Trie.bin(V, None{}, Tip{}, x), [], v): Trie<V>
}:
  match x:
    case Tip{}:
      e => Empty.absurd(
        {
          Bin{
            Some{v},
            Tip{},
            Tip{}
          }
            == Trie.union.leaf(~V, ~join, Trie.bin(V, None{}, Tip{}, Tip{}), [], v): Trie<V>
        },
        Trie.true_ne_false(e)
      )
    case Leaf{p, w}:
      e => {==}
    case Bin{h, z, o}:
      e => {==}

# an entry of the other part joined with a one part
def Trie.union_assoc.far_left.t(
  ~V: Data,
  ~join: V -> V -> V,
  x: Trie<V>,
  -r: List<&2, Bool>,
  -v: V
) -> {
  Trie.is_tip(V, x) == False{}: Bool
} -> {
  Bin{
    None{},
    Leaf{r, v},
    x
  }
    == Trie.union.leaf(~V, ~join, Trie.bin(V, None{}, Tip{}, x), False{} <> r, v): Trie<V>
}:
  match x:
    case Tip{}:
      e => Empty.absurd(
        {
          Bin{
            None{},
            Leaf{r, v},
            Tip{}
          }
            == Trie.union.leaf(
              ~V,
              ~join,
              Trie.bin(V, None{}, Tip{}, Tip{}),
              False{} <> r,
              v
            ): Trie<V>
        },
        Trie.true_ne_false(e)
      )
    case Leaf{p, w}:
      e => {==}
    case Bin{h, z, o}:
      e => {==}

# an entry of a one part joined with that part
def Trie.union_assoc.in_left.t(
  ~V: Data,
  ~join: V -> V -> V,
  x: Trie<V>,
  r: List<&2, Bool>,
  -v: V
) -> {
  Trie.bin(
    V,
    None{},
    Tip{},
    Trie.union.leaf(~V, ~join, x, r, v)
  )
    == Trie.union.leaf(~V, ~join, Trie.bin(V, None{}, Tip{}, x), True{} <> r, v): Trie<V>
}:
  match x r:
    case Tip{} q:
      {==}
    case Leaf{p, w} q:
      {==}
    case Bin{h, z, o} Nil{}:
      {==}
    case Bin{h, z, o} Con{False{}, q}:
      {==}
    case Bin{h, z, o} Con{True{}, q}:
      {==}

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# Trie.union_assoc for three entries
def Trie.union_assoc.fork(
  ~V: Data,
  ~join: V -> V -> V,
  ~assoc: @x: V -> @y: V -> @z: V -> {join(join(x, y), z) == join(x, join(y, z)): V},
  k1: List<&2, Bool>,
  +v1: V,
  p: List<&2, Bool>,
  +w: V,
  k3: List<&2, Bool>,
  +v3: V
) -> {
  Trie.union(
    ~V,
    ~join,
    Trie.union.fork(~V, ~join, k1, v1, p, w),
    Leaf{k3, v3}
  )
    == Trie.union.leaf(~V, ~join, Trie.union.fork(~V, ~join, p, w, k3, v3), k1, v1): Trie<V>
}:
  match k1 p k3:
    case Nil{} Nil{} Nil{}:
      Equal.cong(
        V,
        Trie<V>,
        x => Leaf{[], x},
        join(join(v1, w), v3),
        join(v1, join(w, v3)),
        assoc(v1)(w)(v3)
      )
    case Nil{} Nil{} Con{False{}, r3}:
      {==}
    case Nil{} Nil{} Con{True{}, +r3}:
      {==}
    case Nil{} Con{False{}, +rp} Nil{}:
      {==}
    case Nil{} Con{False{}, +rp} Con{False{}, +r3}:
      Trie.union_assoc.end_left.f(
        ~V,
        ~join,
        Trie.union.fork(~V, ~join, rp, w, r3, v3),
        v1
      )(Trie.fork_part(~V, ~join, rp, w, r3, v3))
    case Nil{} Con{False{}, +rp} Con{True{}, +r3}:
      {==}
    case Nil{} Con{True{}, +rp} Nil{}:
      {==}
    case Nil{} Con{True{}, +rp} Con{False{}, +r3}:
      {==}
    case Nil{} Con{True{}, +rp} Con{True{}, +r3}:
      Trie.union_assoc.end_left.t(
        ~V,
        ~join,
        Trie.union.fork(~V, ~join, rp, w, r3, v3),
        v1
      )(Trie.fork_part(~V, ~join, rp, w, r3, v3))
    case Con{False{}, +r1} Nil{} Nil{}:
      {==}
    case Con{False{}, +r1} Nil{} Con{False{}, r3}:
      {==}
    case Con{False{}, +r1} Nil{} Con{True{}, +r3}:
      {==}
    case Con{False{}, +r1} Con{False{}, +rp} Nil{}:
      Trie.union_assoc.end.f(
        ~V,
        ~join,
        Trie.union.fork(~V, ~join, r1, v1, rp, w),
        v3
      )(Trie.fork_part(~V, ~join, r1, v1, rp, w))
    case Con{False{}, +r1} Con{False{}, +rp} Con{False{}, +r3}:
      %Trie.union_assoc.in_left.f(
        ~V,
        ~join,
        Trie.union.fork(~V, ~join, rp, w, r3, v3),
        r1,
        v1
      ): {
        Trie.union(
          ~V,
          ~join,
          Trie.bin(V, None{}, Trie.union.fork(~V, ~join, r1, v1, rp, w), Tip{}),
          Leaf{False{} <> r3, v3}
        )
          == _: Trie<V>
      }
      %Trie.union_assoc.fork(
        ~V,
        ~join,
        ~assoc,
        r1,
        v1,
        rp,
        w,
        r3,
        v3
      ): {
        Trie.union(
          ~V,
          ~join,
          Trie.bin(V, None{}, Trie.union.fork(~V, ~join, r1, v1, rp, w), Tip{}),
          Leaf{False{} <> r3, v3}
        )
          == Trie.bin(V, None{}, _, Tip{}): Trie<V>
      }
      Trie.union_assoc.in.f(~V, ~join, Trie.union.fork(~V, ~join, r1, v1, rp, w), r3, v3)
    case Con{False{}, +r1} Con{False{}, +rp} Con{True{}, +r3}:
      Trie.union_assoc.far.f(
        ~V,
        ~join,
        Trie.union.fork(~V, ~join, r1, v1, rp, w),
        r3,
        v3
      )(Trie.fork_part(~V, ~join, r1, v1, rp, w))
    case Con{False{}, +r1} Con{True{}, +rp} Nil{}:
      {==}
    case Con{False{}, +r1} Con{True{}, +rp} Con{False{}, +r3}:
      {==}
    case Con{False{}, +r1} Con{True{}, +rp} Con{True{}, +r3}:
      Trie.union_assoc.far_left.t(
        ~V,
        ~join,
        Trie.union.fork(~V, ~join, rp, w, r3, v3),
        r1,
        v1
      )(Trie.fork_part(~V, ~join, rp, w, r3, v3))
    case Con{True{}, +r1} Nil{} Nil{}:
      {==}
    case Con{True{}, +r1} Nil{} Con{False{}, r3}:
      {==}
    case Con{True{}, +r1} Nil{} Con{True{}, +r3}:
      {==}
    case Con{True{}, +r1} Con{False{}, +rp} Nil{}:
      {==}
    case Con{True{}, +r1} Con{False{}, +rp} Con{False{}, +r3}:
      Trie.union_assoc.far_left.f(
        ~V,
        ~join,
        Trie.union.fork(~V, ~join, rp, w, r3, v3),
        r1,
        v1
      )(Trie.fork_part(~V, ~join, rp, w, r3, v3))
    case Con{True{}, +r1} Con{False{}, +rp} Con{True{}, +r3}:
      {==}
    case Con{True{}, +r1} Con{True{}, +rp} Nil{}:
      Trie.union_assoc.end.t(
        ~V,
        ~join,
        Trie.union.fork(~V, ~join, r1, v1, rp, w),
        v3
      )(Trie.fork_part(~V, ~join, r1, v1, rp, w))
    case Con{True{}, +r1} Con{True{}, +rp} Con{False{}, +r3}:
      Trie.union_assoc.far.t(
        ~V,
        ~join,
        Trie.union.fork(~V, ~join, r1, v1, rp, w),
        r3,
        v3
      )(Trie.fork_part(~V, ~join, r1, v1, rp, w))
    case Con{True{}, +r1} Con{True{}, +rp} Con{True{}, +r3}:
      %Trie.union_assoc.in_left.t(
        ~V,
        ~join,
        Trie.union.fork(~V, ~join, rp, w, r3, v3),
        r1,
        v1
      ): {
        Trie.union(
          ~V,
          ~join,
          Trie.bin(V, None{}, Tip{}, Trie.union.fork(~V, ~join, r1, v1, rp, w)),
          Leaf{True{} <> r3, v3}
        )
          == _: Trie<V>
      }
      %Trie.union_assoc.fork(
        ~V,
        ~join,
        ~assoc,
        r1,
        v1,
        rp,
        w,
        r3,
        v3
      ): {
        Trie.union(
          ~V,
          ~join,
          Trie.bin(V, None{}, Tip{}, Trie.union.fork(~V, ~join, r1, v1, rp, w)),
          Leaf{True{} <> r3, v3}
        )
          == Trie.bin(V, None{}, Tip{}, _): Trie<V>
      }
      Trie.union_assoc.in.t(~V, ~join, Trie.union.fork(~V, ~join, r1, v1, rp, w), r3, v3)
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# Trie.union_assoc for two entries and a trie
def Trie.union_assoc.pair(
  ~V: Data,
  ~join: V -> V -> V,
  ~assoc: @x: V -> @y: V -> @z: V -> {join(join(x, y), z) == join(x, join(y, z)): V},
  c: Trie<V>,
  k1: List<&2, Bool>,
  +v1: V,
  p: List<&2, Bool>,
  +w: V
) -> {
  Trie.union(
    ~V,
    ~join,
    Trie.union(~V, ~join, Leaf{k1, v1}, Leaf{p, w}),
    c
  )
    == Trie.union(~V, ~join, Leaf{k1, v1}, Trie.union(~V, ~join, Leaf{p, w}, c)): Trie<V>
}:
  match c k1 p:
    case Tip{} +r1 +rp:
      Trie.union_tip(~V, ~join, Trie.union.fork(~V, ~join, r1, v1, rp, w))
    case Leaf{k3, v3} r1 rp:
      Trie.union_assoc.fork(~V, ~join, ~assoc, r1, v1, rp, w, k3, v3)
    case Bin{h3, z3, o3} Nil{} Nil{}:
      Trie.union_assoc.node(
        ~V,
        ~join,
        ~assoc,
        Some{v1},
        Tip{},
        Tip{},
        Some{w},
        Tip{},
        Tip{},
        h3,
        z3,
        o3,
        {==},
        {==}
      )
    case Bin{h3, +z3, +o3} Nil{} Con{False{}, rp}:
      Trie.union_assoc.node(
        ~V,
        ~join,
        ~assoc,
        Some{v1},
        Tip{},
        Tip{},
        None{},
        Leaf{rp, w},
        Tip{},
        h3,
        z3,
        o3,
        {==},
        {==}
      )
    case Bin{h3, +z3, +o3} Nil{} Con{True{}, +rp}:
      Trie.union_assoc.node(
        ~V,
        ~join,
        ~assoc,
        Some{v1},
        Tip{},
        Tip{},
        None{},
        Tip{},
        Leaf{rp, w},
        h3,
        z3,
        o3,
        {==},
        {==}
      )
    case Bin{h3, +z3, +o3} Con{False{}, +r1} Nil{}:
      Trie.union_assoc.node(
        ~V,
        ~join,
        ~assoc,
        None{},
        Leaf{r1, v1},
        Tip{},
        Some{w},
        Tip{},
        Tip{},
        h3,
        z3,
        o3,
        {==},
        {==}
      )
    case Bin{h3, +z3, +o3} Con{False{}, +r1} Con{False{}, +rp}:
      %Trie.bin_union(
        ~V,
        ~join,
        None{},
        Trie.union.fork(~V, ~join, r1, v1, rp, w),
        Tip{},
        h3,
        z3,
        o3
      ): {
        _
          == Trie.union(
            ~V,
            ~join,
            Leaf{False{} <> r1, v1},
            Trie.union(~V, ~join, Leaf{False{} <> rp, w}, Bin{h3, z3, o3})
          ): Trie<V>
      }
      Trie.union_assoc.node(
        ~V,
        ~join,
        ~assoc,
        None{},
        Leaf{r1, v1},
        Tip{},
        None{},
        Leaf{rp, w},
        Tip{},
        h3,
        z3,
        o3,
        Trie.union_assoc.pair(~V, ~join, ~assoc, z3, r1, v1, rp, w),
        {==}
      )
    case Bin{h3, +z3, +o3} Con{False{}, +r1} Con{True{}, +rp}:
      Trie.union_assoc.node(
        ~V,
        ~join,
        ~assoc,
        None{},
        Leaf{r1, v1},
        Tip{},
        None{},
        Tip{},
        Leaf{rp, w},
        h3,
        z3,
        o3,
        {==},
        {==}
      )
    case Bin{h3, +z3, +o3} Con{True{}, +r1} Nil{}:
      Trie.union_assoc.node(
        ~V,
        ~join,
        ~assoc,
        None{},
        Tip{},
        Leaf{r1, v1},
        Some{w},
        Tip{},
        Tip{},
        h3,
        z3,
        o3,
        {==},
        {==}
      )
    case Bin{h3, +z3, +o3} Con{True{}, +r1} Con{False{}, +rp}:
      Trie.union_assoc.node(
        ~V,
        ~join,
        ~assoc,
        None{},
        Tip{},
        Leaf{r1, v1},
        None{},
        Leaf{rp, w},
        Tip{},
        h3,
        z3,
        o3,
        {==},
        {==}
      )
    case Bin{h3, +z3, +o3} Con{True{}, +r1} Con{True{}, +rp}:
      %Trie.bin_union(
        ~V,
        ~join,
        None{},
        Tip{},
        Trie.union.fork(~V, ~join, r1, v1, rp, w),
        h3,
        z3,
        o3
      ): {
        _
          == Trie.union(
            ~V,
            ~join,
            Leaf{True{} <> r1, v1},
            Trie.union(~V, ~join, Leaf{True{} <> rp, w}, Bin{h3, z3, o3})
          ): Trie<V>
      }
      Trie.union_assoc.node(
        ~V,
        ~join,
        ~assoc,
        None{},
        Tip{},
        Leaf{r1, v1},
        None{},
        Tip{},
        Leaf{rp, w},
        h3,
        z3,
        o3,
        {==},
        Trie.union_assoc.pair(~V, ~join, ~assoc, o3, r1, v1, rp, w)
      )

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Trie.union_assoc for an entry and two tries
def Trie.union_assoc.leaf(
  ~V: Data,
  ~join: V -> V -> V,
  ~assoc: @x: V -> @y: V -> @z: V -> {join(join(x, y), z) == join(x, join(y, z)): V},
  b: Trie<V>,
  c: Trie<V>,
  k1: List<&2, Bool>,
  v1: V
) -> {
  Trie.union(
    ~V,
    ~join,
    Trie.union(~V, ~join, Leaf{k1, v1}, b),
    c
  )
    == Trie.union(~V, ~join, Leaf{k1, v1}, Trie.union(~V, ~join, b, c)): Trie<V>
}:
  match b c k1:
    case Tip{} y r1:
      {==}
    case Leaf{p, w} y r1:
      Trie.union_assoc.pair(~V, ~join, ~assoc, y, r1, v1, p, w)
    case Bin{h2, z2, o2} Tip{} r1:
      Trie.union_tip(~V, ~join, Trie.union.leaf(~V, ~join, Bin{h2, z2, o2}, r1, v1))
    case Bin{h2, +z2, +o2} Leaf{+k3, +v3} Nil{}:
      Trie.union_assoc.node(
        ~V,
        ~join,
        ~assoc,
        Some{v1},
        Tip{},
        Tip{},
        h2,
        z2,
        o2,
        Trie.at.here(V, k3, v3),
        Trie.at.zero(V, k3, v3),
        Trie.at.one(V, k3, v3),
        {==},
        {==}
      )
    case Bin{h2, +z2, +o2} Leaf{+k3, +v3} Con{False{}, r1}:
      Trie.union_assoc.node(
        ~V,
        ~join,
        ~assoc,
        None{},
        Leaf{r1, v1},
        Tip{},
        h2,
        z2,
        o2,
        Trie.at.here(V, k3, v3),
        Trie.at.zero(V, k3, v3),
        Trie.at.one(V, k3, v3),
        Trie.union_assoc.leaf(~V, ~join, ~assoc, z2, Trie.at.zero(V, k3, v3), r1, v1),
        {==}
      )
    case Bin{h2, +z2, +o2} Leaf{+k3, +v3} Con{True{}, +r1}:
      Trie.union_assoc.node(
        ~V,
        ~join,
        ~assoc,
        None{},
        Tip{},
        Leaf{r1, v1},
        h2,
        z2,
        o2,
        Trie.at.here(V, k3, v3),
        Trie.at.zero(V, k3, v3),
        Trie.at.one(V, k3, v3),
        {==},
        Trie.union_assoc.leaf(~V, ~join, ~assoc, o2, Trie.at.one(V, k3, v3), r1, v1)
      )
    case Bin{h2, +z2, +o2} Bin{h3, z3, o3} Nil{}:
      Trie.union_assoc.node(
        ~V,
        ~join,
        ~assoc,
        Some{v1},
        Tip{},
        Tip{},
        h2,
        z2,
        o2,
        h3,
        z3,
        o3,
        {==},
        {==}
      )
    case Bin{h2, +z2, +o2} Bin{h3, z3, o3} Con{False{}, r1}:
      Trie.union_assoc.node(
        ~V,
        ~join,
        ~assoc,
        None{},
        Leaf{r1, v1},
        Tip{},
        h2,
        z2,
        o2,
        h3,
        z3,
        o3,
        Trie.union_assoc.leaf(~V, ~join, ~assoc, z2, z3, r1, v1),
        {==}
      )
    case Bin{h2, +z2, +o2} Bin{h3, z3, o3} Con{True{}, +r1}:
      Trie.union_assoc.node(
        ~V,
        ~join,
        ~assoc,
        None{},
        Tip{},
        Leaf{r1, v1},
        h2,
        z2,
        o2,
        h3,
        z3,
        o3,
        {==},
        Trie.union_assoc.leaf(~V, ~join, ~assoc, o2, o3, r1, v1)
      )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

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

# bend-lint: expect-begin bend-lint-rules/performance/missed_fork@hint -- a proof: it does not run
def Trie.union_assoc(ty, join, assoc, a, b, c):
  match a b c:
    case Tip{} y w:
      {==}
    case Leaf{k, v} y w:
      Trie.union_assoc.leaf(~ty, ~join, ~assoc, y, w, k, v)
    case Bin{h, z, o} Tip{} w:
      {==}
    case Bin{h1, z1, o1} Leaf{p, w} Tip{}:
      {==}
    case Bin{h1, z1, o1} Bin{h2, z2, o2} Tip{}:
      {==}
    case Bin{+h1, +z1, +o1} Leaf{+p, +w} Leaf{+k3, +v3}:
      %Trie.fork_node(
        ~ty,
        ~join,
        p,
        w,
        k3,
        v3
      ): {
        Trie.union(
          ~ty,
          ~join,
          Trie.union(~ty, ~join, Bin{h1, z1, o1}, Leaf{p, w}),
          Leaf{k3, v3}
        )
          == Trie.union(~ty, ~join, Bin{h1, z1, o1}, _): Trie<ty>
      }
      %Trie.union_bin(
        ~ty,
        ~join,
        h1,
        z1,
        o1,
        Shared.Maybe.join(~ty, ~join, Trie.at.here(ty, p, w), Trie.at.here(ty, k3, v3)),
        Trie.union(~ty, ~join, Trie.at.zero(ty, p, w), Trie.at.zero(ty, k3, v3)),
        Trie.union(~ty, ~join, Trie.at.one(ty, p, w), Trie.at.one(ty, k3, v3))
      ): {
        Trie.union(
          ~ty,
          ~join,
          Trie.union(~ty, ~join, Bin{h1, z1, o1}, Leaf{p, w}),
          Leaf{k3, v3}
        )
          == _: Trie<ty>
      }
      Trie.union_assoc.node(
        ~ty,
        ~join,
        ~assoc,
        h1,
        z1,
        o1,
        Trie.at.here(ty, p, w),
        Trie.at.zero(ty, p, w),
        Trie.at.one(ty, p, w),
        Trie.at.here(ty, k3, v3),
        Trie.at.zero(ty, k3, v3),
        Trie.at.one(ty, k3, v3),
        Trie.union_assoc(~ty, ~join, ~assoc, z1, Trie.at.zero(ty, p, w), Trie.at.zero(ty, k3, v3)),
        Trie.union_assoc(~ty, ~join, ~assoc, o1, Trie.at.one(ty, p, w), Trie.at.one(ty, k3, v3))
      )
    case Bin{+h1, +z1, +o1} Leaf{+p, +w} Bin{h3, z3, o3}:
      %Trie.leaf_bin(
        ~ty,
        ~join,
        p,
        w,
        h3,
        z3,
        o3
      ): {
        Trie.union(
          ~ty,
          ~join,
          Trie.union(~ty, ~join, Bin{h1, z1, o1}, Leaf{p, w}),
          Bin{h3, z3, o3}
        )
          == Trie.union(~ty, ~join, Bin{h1, z1, o1}, _): Trie<ty>
      }
      Trie.union_assoc.node(
        ~ty,
        ~join,
        ~assoc,
        h1,
        z1,
        o1,
        Trie.at.here(ty, p, w),
        Trie.at.zero(ty, p, w),
        Trie.at.one(ty, p, w),
        h3,
        z3,
        o3,
        Trie.union_assoc(~ty, ~join, ~assoc, z1, Trie.at.zero(ty, p, w), z3),
        Trie.union_assoc(~ty, ~join, ~assoc, o1, Trie.at.one(ty, p, w), o3)
      )
    case Bin{h1, z1, o1} Bin{h2, z2, o2} Leaf{+k3, +v3}:
      Trie.union_assoc.node(
        ~ty,
        ~join,
        ~assoc,
        h1,
        z1,
        o1,
        h2,
        z2,
        o2,
        Trie.at.here(ty, k3, v3),
        Trie.at.zero(ty, k3, v3),
        Trie.at.one(ty, k3, v3),
        Trie.union_assoc(~ty, ~join, ~assoc, z1, z2, Trie.at.zero(ty, k3, v3)),
        Trie.union_assoc(~ty, ~join, ~assoc, o1, o2, Trie.at.one(ty, k3, v3))
      )
    case Bin{h1, z1, o1} Bin{h2, z2, o2} Bin{h3, z3, o3}:
      Trie.union_assoc.node(
        ~ty,
        ~join,
        ~assoc,
        h1,
        z1,
        o1,
        h2,
        z2,
        o2,
        h3,
        z3,
        o3,
        Trie.union_assoc(~ty, ~join, ~assoc, z1, z2, z3),
        Trie.union_assoc(~ty, ~join, ~assoc, o1, o2, o3)
      )
# bend-lint: expect-end bend-lint-rules/performance/missed_fork@hint

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# two entries at one key are one entry
def Trie.fork_same(
  ~V: Data,
  ~join: V -> V -> V,
  k: List<&2, Bool>,
  a: V,
  b: V
) -> {Trie.union.fork(~V, ~join, k, a, k, b) == Leaf{k, join(a, b)}: Trie<V>}:
  match k:
    case Nil{}:
      {==}
    case Con{False{}, r}:
      Equal.cong(
        Trie<V>,
        Trie<V>,
        x => Trie.bin(V, None{}, x, Tip{}),
        Trie.union.fork(~V, ~join, r, a, r, b),
        Leaf{r, join(a, b)},
        Trie.fork_same(~V, ~join, r, a, b)
      )
    case Con{True{}, +r}:
      Equal.cong(
        Trie<V>,
        Trie<V>,
        x => Trie.bin(V, None{}, Tip{}, x),
        Trie.union.fork(~V, ~join, r, a, r, b),
        Leaf{r, join(a, b)},
        Trie.fork_same(~V, ~join, r, a, b)
      )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

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
    case Leaf{k, +v}:
      Equal.trans(
        Trie<ty>,
        Trie.union.fork(~ty, ~join, k, v, k, v),
        Leaf{k, join(v, v)},
        Leaf{k, v},
        Trie.fork_same(~ty, ~join, k, v, v),
        Equal.cong(ty, Trie<ty>, x => Leaf{k, x}, join(v, v), v, idem(v))
      )
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

# Laws of what a holder lacks
# --------------------------
# absorb says that the join keeps a value that takes in a same one. Then what
# r lacks of s is as good as s to a holder of r (Trie.union_lacks); a union
# and a take are two cases.

# an entry is not no entry
def Trie.some_ne_none(-V: Data, -x: V, e: {Some{x} == None{}: Maybe<&2, V>}) -> Empty:
  Shared.Maybe.none_ne_some(V, x, Equal.sym(Maybe<&2, V>, Some{x}, None{}, e))

# t is a node
def Trie.is_bin(-V: Data, t: Trie<V>) -> Bool:
  match t:
    case Bin{h, z, o}:
      True{}
    case _:
      False{}

# a node over a node is a node
def Trie.bin_bin.f(
  -V: Data,
  x: Trie<V>
) -> {
  Trie.is_bin(V, x) == True{}: Bool
} -> {Trie.is_bin(V, Trie.bin(V, None{}, x, Tip{})) == True{}: Bool}:
  match x:
    case Tip{}:
      e => Empty.absurd(
        {Trie.is_bin(V, Trie.bin(V, None{}, Tip{}, Tip{})) == True{}: Bool},
        Shared.Bool.false_ne_true(e)
      )
    case Leaf{p, w}:
      e => Empty.absurd(
        {Trie.is_bin(V, Trie.bin(V, None{}, Leaf{p, w}, Tip{})) == True{}: Bool},
        Shared.Bool.false_ne_true(e)
      )
    case Bin{h, z, o}:
      e => {==}

# a node over a node has the shape of its entries
def Trie.node_bin.f(
  -V: Data,
  x: Trie<V>
) -> {
  Trie.is_bin(V, x) == True{}: Bool
} -> {Bin{None{}, x, Tip{}} == Trie.bin(V, None{}, x, Tip{}): Trie<V>}:
  match x:
    case Tip{}:
      e => Empty.absurd(
        {Bin{None{}, Tip{}, Tip{}} == Trie.bin(V, None{}, Tip{}, Tip{}): Trie<V>},
        Shared.Bool.false_ne_true(e)
      )
    case Leaf{p, w}:
      e => Empty.absurd(
        {Bin{None{}, Leaf{p, w}, Tip{}} == Trie.bin(V, None{}, Leaf{p, w}, Tip{}): Trie<V>},
        Shared.Bool.false_ne_true(e)
      )
    case Bin{h, z, o}:
      e => {==}

# a node over a node is a node
def Trie.bin_bin.t(
  -V: Data,
  x: Trie<V>
) -> {
  Trie.is_bin(V, x) == True{}: Bool
} -> {Trie.is_bin(V, Trie.bin(V, None{}, Tip{}, x)) == True{}: Bool}:
  match x:
    case Tip{}:
      e => Empty.absurd(
        {Trie.is_bin(V, Trie.bin(V, None{}, Tip{}, Tip{})) == True{}: Bool},
        Shared.Bool.false_ne_true(e)
      )
    case Leaf{p, w}:
      e => Empty.absurd(
        {Trie.is_bin(V, Trie.bin(V, None{}, Tip{}, Leaf{p, w})) == True{}: Bool},
        Shared.Bool.false_ne_true(e)
      )
    case Bin{h, z, o}:
      e => {==}

# a node over a node has the shape of its entries
def Trie.node_bin.t(
  -V: Data,
  x: Trie<V>
) -> {
  Trie.is_bin(V, x) == True{}: Bool
} -> {Bin{None{}, Tip{}, x} == Trie.bin(V, None{}, Tip{}, x): Trie<V>}:
  match x:
    case Tip{}:
      e => Empty.absurd(
        {Bin{None{}, Tip{}, Tip{}} == Trie.bin(V, None{}, Tip{}, Tip{}): Trie<V>},
        Shared.Bool.false_ne_true(e)
      )
    case Leaf{p, w}:
      e => Empty.absurd(
        {Bin{None{}, Tip{}, Leaf{p, w}} == Trie.bin(V, None{}, Tip{}, Leaf{p, w}): Trie<V>},
        Shared.Bool.false_ne_true(e)
      )
    case Bin{h, z, o}:
      e => {==}

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# two entries at keys that differ are a node
def Trie.fork_bin(
  ~V: Data,
  ~join: V -> V -> V,
  k: List<&2, Bool>,
  +v: V,
  p: List<&2, Bool>,
  +w: V
) -> {
  Trie.get(V, Leaf{p, w}, k) == None{}: Maybe<&2, V>
} -> {Trie.is_bin(V, Trie.union.fork(~V, ~join, k, v, p, w)) == True{}: Bool}:
  match k p:
    case Nil{} Nil{}:
      e => Empty.absurd(
        {Trie.is_bin(V, Trie.union.fork(~V, ~join, [], v, [], w)) == True{}: Bool},
        Trie.some_ne_none(V, w, e)
      )
    case Nil{} Con{False{}, q}:
      e => {==}
    case Nil{} Con{True{}, +q}:
      e => {==}
    case Con{False{}, +r} Nil{}:
      e => {==}
    case Con{False{}, +r} Con{False{}, +q}:
      e => Trie.bin_bin.f(
        V,
        Trie.union.fork(~V, ~join, r, v, q, w)
      )(Trie.fork_bin(~V, ~join, r, v, q, w)(e))
    case Con{False{}, +r} Con{True{}, +q}:
      e => {==}
    case Con{True{}, +r} Nil{}:
      e => {==}
    case Con{True{}, +r} Con{False{}, +q}:
      e => {==}
    case Con{True{}, +r} Con{True{}, +q}:
      e => Trie.bin_bin.t(
        V,
        Trie.union.fork(~V, ~join, r, v, q, w)
      )(Trie.fork_bin(~V, ~join, r, v, q, w)(e))
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# a trie is itself joined with nothing
def Trie.tip_union(
  ~V: Data,
  ~join: V -> V -> V,
  a: Trie<V>
) -> {a == Trie.union(~V, ~join, a, Tip{}): Trie<V>}:
  match a:
    case Tip{}:
      {==}
    case Leaf{k, v}:
      {==}
    case Bin{h, z, o}:
      {==}

# a is a joined to nothing
def Trie.none_join(
  ~V: Data,
  ~join: V -> V -> V,
  a: Maybe<&2, V>
) -> {a == Shared.Maybe.join(~V, ~join, a, None{}): Maybe<&2, V>}:
  match a:
    case None{}:
      {==}
    case Some{x}:
      {==}

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Trie.union_held for two entries, by whether their keys are the same (held)
def Trie.union_held.leaf(
  ~V: Data,
  ~join: V -> V -> V,
  +p: List<&2, Bool>,
  x: V,
  k: List<&2, Bool>,
  v: V,
  w: V,
  held: Bool,
  e: {held == Trie.same_key(k, p): Bool}
) -> {
  Bool.pick(Maybe<&2, V>, held, Some{x}, None{}) == Some{w}: Maybe<&2, V>
} -> {join(w, v) == w: V} -> {Leaf{p, x} == Trie.union.fork(~V, ~join, p, x, k, v): Trie<V>}:
  match held:
    case False{}:
      g => ab => Empty.absurd(
        {Leaf{p, x} == Trie.union.fork(~V, ~join, p, x, k, v): Trie<V>},
        Shared.Maybe.none_ne_some(V, w, g)
      )
    case True{}:
      g => ab =>
        %Equal.sym(
          List<&2, Bool>,
          k,
          p,
          Trie.same_key_sound(k, p)(Equal.sym(Bool, True{}, Trie.same_key(k, p), e))
        ): {Leaf{p, x} == Trie.union.fork(~V, ~join, p, x, _, v): Trie<V>}
        %Equal.sym(V, x, w, Shared.Maybe.some_inj(V, x, w, g)):
          {Leaf{p, _} == Trie.union.fork(~V, ~join, p, _, p, v): Trie<V>}
        Equal.sym(
          Trie<V>,
          Trie.union.fork(~V, ~join, p, w, p, v),
          Leaf{p, w},
          Equal.trans(
            Trie<V>,
            Trie.union.fork(~V, ~join, p, w, p, v),
            Leaf{p, join(w, v)},
            Leaf{p, w},
            Trie.fork_same(~V, ~join, p, w, v),
            Equal.cong(V, Trie<V>, y => Leaf{p, y}, join(w, v), w, ab)
          )
        )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# r takes in nothing from an entry whose value its own value takes in
def Trie.union_held(
  ~V: Data,
  ~join: V -> V -> V,
  r: Trie<V>,
  k: List<&2, Bool>,
  v: V,
  w: V
) -> {
  Trie.get(V, r, k) == Some{w}: Maybe<&2, V>
} -> {join(w, v) == w: V} -> {r == Trie.union(~V, ~join, r, Leaf{k, v}): Trie<V>}:
  match r k:
    case Tip{} q:
      g => ab => Empty.absurd(
        {Tip{} == Trie.union(~V, ~join, Tip{}, Leaf{q, v}): Trie<V>},
        Shared.Maybe.none_ne_some(V, w, g)
      )
    case Leaf{+p, x} +q:
      Trie.union_held.leaf(~V, ~join, p, x, q, v, w, Trie.same_key(q, p), {==})
    case Bin{None{}, z, o} Nil{}:
      g => ab => Empty.absurd(
        {Bin{None{}, z, o} == Trie.union(~V, ~join, Bin{None{}, z, o}, Leaf{[], v}): Trie<V>},
        Shared.Maybe.none_ne_some(V, w, g)
      )
    case Bin{Some{x}, +z, +o} Nil{}:
      g => ab =>
        %Equal.sym(
          V,
          x,
          w,
          Shared.Maybe.some_inj(V, x, w, g)
        ): {
          Bin{
            Some{_},
            z,
            o
          }
            == Bin{
              Some{join(_, v)},
              Trie.union(~V, ~join, z, Tip{}),
              Trie.union(~V, ~join, o, Tip{})
            }: Trie<V>
        }
        %ab: {
          Bin{
            Some{_},
            z,
            o
          }
            == Bin{
              Some{join(w, v)},
              Trie.union(~V, ~join, z, Tip{}),
              Trie.union(~V, ~join, o, Tip{})
            }: Trie<V>
        }
        %Trie.tip_union(
          ~V,
          ~join,
          z
        ): {
          Bin{
            Some{join(w, v)},
            z,
            o
          }
            == Bin{Some{join(w, v)}, _, Trie.union(~V, ~join, o, Tip{})}: Trie<V>
        }
        %Trie.tip_union(
          ~V,
          ~join,
          o
        ): {Bin{Some{join(w, v)}, z, o} == Bin{Some{join(w, v)}, z, _}: Trie<V>}
        {==}
    case Bin{+h, +z, +o} Con{False{}, q}:
      g => ab =>
        %Trie.none_join(
          ~V,
          ~join,
          h
        ): {
          Bin{
            h,
            z,
            o
          }
            == Bin{
              _,
              Trie.union(~V, ~join, z, Leaf{q, v}),
              Trie.union(~V, ~join, o, Tip{})
            }: Trie<V>
        }
        %Trie.union_held(
          ~V,
          ~join,
          z,
          q,
          v,
          w
        )(g)(ab): {Bin{h, z, o} == Bin{h, _, Trie.union(~V, ~join, o, Tip{})}: Trie<V>}
        %Trie.tip_union(~V, ~join, o): {Bin{h, z, o} == Bin{h, z, _}: Trie<V>}
        {==}
    case Bin{+h, +z, +o} Con{True{}, +q}:
      g => ab =>
        %Trie.none_join(
          ~V,
          ~join,
          h
        ): {
          Bin{
            h,
            z,
            o
          }
            == Bin{
              _,
              Trie.union(~V, ~join, z, Tip{}),
              Trie.union(~V, ~join, o, Leaf{q, v})
            }: Trie<V>
        }
        %Trie.tip_union(
          ~V,
          ~join,
          z
        ): {Bin{h, z, o} == Bin{h, _, Trie.union(~V, ~join, o, Leaf{q, v})}: Trie<V>}
        %Trie.union_held(~V, ~join, o, q, v, w)(g)(ab): {Bin{h, z, o} == Bin{h, z, _}: Trie<V>}
        {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# an entry at the empty key joined with a kept node with no value here
def Trie.keep_end(
  ~V: Data,
  ~join: V -> V -> V,
  z: Trie<V>,
  o: Trie<V>,
  -w: V
) -> {Bin{Some{w}, z, o} == Trie.union.leaf(~V, ~join, Trie.tidy(V, None{}, z, o), [], w): Trie<V>}:
  match z o:
    case Tip{} Tip{}:
      {==}
    case Tip{} Leaf{p, x}:
      {==}
    case Tip{} Bin{h2, z2, o2}:
      {==}
    case Leaf{p, x} Tip{}:
      {==}
    case Leaf{p, x} Leaf{p2, x2}:
      {==}
    case Leaf{p, x} Bin{h2, z2, o2}:
      {==}
    case Bin{h1, z1, o1} o0:
      {==}

# an entry of the zero part joined with a kept node, when that part does not
# hold its key
def Trie.keep_in.f(
  ~V: Data,
  ~join: V -> V -> V,
  h: Maybe<&2, V>,
  x: Trie<V>,
  o: Trie<V>,
  +r: List<&2, Bool>,
  +w: V
) -> {
  Trie.get(V, x, r) == None{}: Maybe<&2, V>
} -> {
  Bin{
    h,
    Trie.union.leaf(~V, ~join, x, r, w),
    o
  }
    == Trie.union.leaf(~V, ~join, Trie.tidy(V, h, x, o), False{} <> r, w): Trie<V>
}:
  match h x o:
    case None{} Tip{} Tip{}:
      g => {==}
    case None{} Tip{} Leaf{p, y}:
      g => {==}
    case None{} Tip{} Bin{h2, z2, o2}:
      g => {==}
    case None{} Leaf{+p, +y} Tip{}:
      g => Trie.node_bin.f(
        V,
        Trie.union.fork(~V, ~join, r, w, p, y)
      )(Trie.fork_bin(~V, ~join, r, w, p, y)(g))
    case None{} Leaf{p, y} Leaf{p2, y2}:
      g => {==}
    case None{} Leaf{p, y} Bin{h2, z2, o2}:
      g => {==}
    case None{} Bin{h1, z1, o1} o0:
      g => {==}
    case Some{y0} Tip{} Tip{}:
      g => {==}
    case Some{y0} Tip{} Leaf{p, y}:
      g => {==}
    case Some{y0} Tip{} Bin{h2, z2, o2}:
      g => {==}
    case Some{y0} Leaf{p, y} o0:
      g => {==}
    case Some{y0} Bin{h1, z1, o1} o0:
      g => {==}

# an entry of the one part joined with a kept node, when that part does not
# hold its key
def Trie.keep_in.t(
  ~V: Data,
  ~join: V -> V -> V,
  h: Maybe<&2, V>,
  z: Trie<V>,
  x: Trie<V>,
  +r: List<&2, Bool>,
  +w: V
) -> {
  Trie.get(V, x, r) == None{}: Maybe<&2, V>
} -> {
  Bin{
    h,
    z,
    Trie.union.leaf(~V, ~join, x, r, w)
  }
    == Trie.union.leaf(~V, ~join, Trie.tidy(V, h, z, x), True{} <> r, w): Trie<V>
}:
  match h z x:
    case None{} Tip{} Tip{}:
      g => {==}
    case None{} Tip{} Leaf{+p, +y}:
      g => Trie.node_bin.t(
        V,
        Trie.union.fork(~V, ~join, r, w, p, y)
      )(Trie.fork_bin(~V, ~join, r, w, p, y)(g))
    case None{} Tip{} Bin{h2, z2, o2}:
      g => {==}
    case None{} Leaf{p, y} Tip{}:
      g => {==}
    case None{} Leaf{p, y} Leaf{p2, y2}:
      g => {==}
    case None{} Leaf{p, y} Bin{h2, z2, o2}:
      g => {==}
    case None{} Bin{h1, z1, o1} o0:
      g => {==}
    case Some{y0} Tip{} Tip{}:
      g => {==}
    case Some{y0} Tip{} Leaf{p, y}:
      g => {==}
    case Some{y0} Tip{} Bin{h2, z2, o2}:
      g => {==}
    case Some{y0} Leaf{p, y} o0:
      g => {==}
    case Some{y0} Bin{h1, z1, o1} o0:
      g => {==}

# Trie.get_drop for an entry, by whether its key is the dropped one (held)
def Trie.get_drop.leaf(
  -V: Data,
  -p: List<&2, Bool>,
  -v: V,
  -k: List<&2, Bool>,
  held: Bool,
  e: {held == Trie.same_key(k, p): Bool}
) -> {Trie.get(V, Bool.pick(Trie<V>, held, Tip{}, Leaf{p, v}), k) == None{}: Maybe<&2, V>}:
  match held:
    case True{}:
      {==}
    case False{}:
      %e: {Bool.pick(Maybe<&2, V>, _, Some{v}, None{}) == None{}: Maybe<&2, V>}
      {==}

# a trie without a key holds nothing there
def Trie.get_drop(
  -V: Data,
  t: Trie<V>,
  k: List<&2, Bool>
) -> {Trie.get(V, Trie.drop(V, t, k), k) == None{}: Maybe<&2, V>}:
  match t k:
    case Tip{} r:
      {==}
    case Leaf{p, v} r:
      Trie.get_drop.leaf(V, p, v, r, Trie.same_key(r, p), {==})
    case Bin{h, z, o} Nil{}:
      Trie.get_keep(V, None{}, z, o, [])
    case Bin{h, +z, o} Con{False{}, +r}:
      Equal.trans(
        Maybe<&2, V>,
        Trie.get(V, Trie.tidy(V, h, Trie.drop(V, z, r), o), False{} <> r),
        Trie.get(V, Trie.drop(V, z, r), r),
        None{},
        Trie.get_keep(V, h, Trie.drop(V, z, r), o, False{} <> r),
        Trie.get_drop(V, z, r)
      )
    case Bin{h, z, +o} Con{True{}, +r}:
      Equal.trans(
        Maybe<&2, V>,
        Trie.get(V, Trie.tidy(V, h, z, Trie.drop(V, o, r)), True{} <> r),
        Trie.get(V, Trie.drop(V, o, r), r),
        None{},
        Trie.get_keep(V, h, z, Trie.drop(V, o, r), True{} <> r),
        Trie.get_drop(V, o, r)
      )

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Trie.union_drop for an entry, by whether its key is the dropped one (held)
def Trie.union_drop.leaf(
  ~V: Data,
  ~join: V -> V -> V,
  p: List<&2, Bool>,
  x: V,
  +k: List<&2, Bool>,
  v: V,
  w: V,
  held: Bool,
  e: {held == Trie.same_key(k, p): Bool}
) -> {
  Bool.pick(Maybe<&2, V>, held, Some{x}, None{}) == Some{v}: Maybe<&2, V>
} -> {
  join(w, v) == w: V
} -> {
  Trie.union.leaf(
    ~V,
    ~join,
    Bool.pick(Trie<V>, held, Tip{}, Leaf{p, x}),
    k,
    w
  )
    == Trie.union.fork(~V, ~join, k, w, p, x): Trie<V>
}:
  match held:
    case False{}:
      g => ab => {==}
    case True{}:
      g => ab =>
        %Trie.same_key_sound(k, p)(Equal.sym(Bool, True{}, Trie.same_key(k, p), e)):
          {Leaf{k, w} == Trie.union.fork(~V, ~join, k, w, _, x): Trie<V>}
        %Equal.sym(V, x, v, Shared.Maybe.some_inj(V, x, v, g)):
          {Leaf{k, w} == Trie.union.fork(~V, ~join, k, w, k, _): Trie<V>}
        Equal.sym(
          Trie<V>,
          Trie.union.fork(~V, ~join, k, w, k, v),
          Leaf{k, w},
          Equal.trans(
            Trie<V>,
            Trie.union.fork(~V, ~join, k, w, k, v),
            Leaf{k, join(w, v)},
            Leaf{k, w},
            Trie.fork_same(~V, ~join, k, w, v),
            Equal.cong(V, Trie<V>, y => Leaf{k, y}, join(w, v), w, ab)
          )
        )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# an entry joined with s without its key is the entry joined with s, when its
# value takes in the value of s
def Trie.union_drop(
  ~V: Data,
  ~join: V -> V -> V,
  s: Trie<V>,
  k: List<&2, Bool>,
  v: V,
  +w: V
) -> {
  Trie.get(V, s, k) == Some{v}: Maybe<&2, V>
} -> {
  join(w, v) == w: V
} -> {
  Trie.union.leaf(
    ~V,
    ~join,
    Trie.drop(V, s, k),
    k,
    w
  )
    == Trie.union.leaf(~V, ~join, s, k, w): Trie<V>
}:
  match s k:
    case Tip{} q:
      g => ab => Empty.absurd(
        {Leaf{q, w} == Leaf{q, w}: Trie<V>},
        Shared.Maybe.none_ne_some(V, v, g)
      )
    case Leaf{+p, x} +q:
      Trie.union_drop.leaf(~V, ~join, p, x, q, v, w, Trie.same_key(q, p), {==})
    case Bin{None{}, z, o} Nil{}:
      g => ab => Empty.absurd(
        {
          Trie.union.leaf(
            ~V,
            ~join,
            Trie.tidy(V, None{}, z, o),
            [],
            w
          )
            == Trie.union.leaf(~V, ~join, Bin{None{}, z, o}, [], w): Trie<V>
        },
        Shared.Maybe.none_ne_some(V, v, g)
      )
    case Bin{Some{x}, +z, +o} Nil{}:
      g => ab =>
        %Trie.keep_end(~V, ~join, z, o, w): {_ == Bin{Some{join(w, x)}, z, o}: Trie<V>}
        %Equal.sym(V, x, v, Shared.Maybe.some_inj(V, x, v, g)):
          {Bin{Some{w}, z, o} == Bin{Some{join(w, _)}, z, o}: Trie<V>}
        %ab: {Bin{Some{_}, z, o} == Bin{Some{join(w, v)}, z, o}: Trie<V>}
        {==}
    case Bin{+h, +z, +o} Con{False{}, +q}:
      g => ab =>
        %Trie.keep_in.f(~V, ~join, h, Trie.drop(V, z, q), o, q, w)(Trie.get_drop(V, z, q)):
          {_ == Bin{h, Trie.union.leaf(~V, ~join, z, q, w), o}: Trie<V>}
        Equal.cong(
          Trie<V>,
          Trie<V>,
          y => Bin{h, y, o},
          Trie.union.leaf(~V, ~join, Trie.drop(V, z, q), q, w),
          Trie.union.leaf(~V, ~join, z, q, w),
          Trie.union_drop(~V, ~join, z, q, v, w)(g)(ab)
        )
    case Bin{+h, +z, +o} Con{True{}, +q}:
      g => ab =>
        %Trie.keep_in.t(~V, ~join, h, z, Trie.drop(V, o, q), q, w)(Trie.get_drop(V, o, q)):
          {_ == Bin{h, z, Trie.union.leaf(~V, ~join, o, q, w)}: Trie<V>}
        Equal.cong(
          Trie<V>,
          Trie<V>,
          y => Bin{h, z, y},
          Trie.union.leaf(~V, ~join, Trie.drop(V, o, q), q, w),
          Trie.union.leaf(~V, ~join, o, q, w),
          Trie.union_drop(~V, ~join, o, q, v, w)(g)(ab)
        )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Trie.union_lacks.here once same(x, y) is known (held)
def Trie.union_lacks.here.if(
  ~V: Data,
  ~join: V -> V -> V,
  ~same: V -> V -> Bool,
  ~absorb: @w: V -> @v: V -> {same(v, w) == True{}: Bool} -> {join(w, v) == w: V},
  held: Bool,
  x: V,
  y: V,
  e: {held == same(x, y): Bool}
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
      %absorb(y)(x)(Equal.sym(Bool, True{}, same(x, y), e)):
        {Some{_} == Some{join(y, x)}: Maybe<&2, V>}
      {==}
    case False{}:
      {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# what r holds for a key, joined with what r lacks of s there, is r's joined
# with s's
def Trie.union_lacks.here(
  ~V: Data,
  ~join: V -> V -> V,
  ~same: V -> V -> Bool,
  ~absorb: @w: V -> @v: V -> {same(v, w) == True{}: Bool} -> {join(w, v) == w: V},
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
      Trie.union_lacks.here.if(~V, ~join, ~same, ~absorb, same(x, y), x, y, {==})

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Trie.union_lacks for an entry of s, once same(v, w) is known (held)
def Trie.union_lacks.leaf.if(
  ~V: Data,
  ~join: V -> V -> V,
  ~same: V -> V -> Bool,
  ~absorb: @w: V -> @v: V -> {same(v, w) == True{}: Bool} -> {join(w, v) == w: V},
  +y: Trie<V>,
  k: List<&2, Bool>,
  +v: V,
  +w: V,
  held: Bool,
  e: {held == same(v, w): Bool},
  g: {Trie.get(V, y, k) == Some{w}: Maybe<&2, V>}
) -> {
  Trie.union(
    ~V,
    ~join,
    y,
    Bool.pick(Trie<V>, held, Tip{}, Leaf{k, v})
  )
    == Trie.union(~V, ~join, y, Leaf{k, v}): Trie<V>
}:
  match held:
    case True{}:
      Equal.trans(
        Trie<V>,
        Trie.union(~V, ~join, y, Tip{}),
        y,
        Trie.union(~V, ~join, y, Leaf{k, v}),
        Trie.union_tip(~V, ~join, y),
        Trie.union_held(
          ~V,
          ~join,
          y,
          k,
          v,
          w
        )(g)(absorb(w)(v)(Equal.sym(Bool, True{}, same(v, w), e)))
      )
    case False{}:
      {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Trie.union_lacks for an entry of s, once what r holds at its key is known (m)
def Trie.union_lacks.leaf(
  ~V: Data,
  ~join: V -> V -> V,
  ~same: V -> V -> Bool,
  ~absorb: @w: V -> @v: V -> {same(v, w) == True{}: Bool} -> {join(w, v) == w: V},
  y: Trie<V>,
  k: List<&2, Bool>,
  +v: V,
  m: Maybe<&2, V>,
  e: {m == Trie.get(V, y, k): Maybe<&2, V>}
) -> {
  Trie.union(
    ~V,
    ~join,
    y,
    Trie.minus.leaf(~V, ~same, k, v, m)
  )
    == Trie.union(~V, ~join, y, Leaf{k, v}): Trie<V>
}:
  match m:
    case None{}:
      {==}
    case Some{+w}:
      Trie.union_lacks.leaf.if(
        ~V,
        ~join,
        ~same,
        ~absorb,
        y,
        k,
        v,
        w,
        same(v, w),
        {==},
        Equal.sym(Maybe<&2, V>, Some{w}, Trie.get(V, y, k), e)
      )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# Trie.union_lacks for an entry of r, once same(v, w) is known (held)
def Trie.union_lacks.cut.if(
  ~V: Data,
  ~join: V -> V -> V,
  ~same: V -> V -> Bool,
  ~absorb: @w: V -> @v: V -> {same(v, w) == True{}: Bool} -> {join(w, v) == w: V},
  s: Trie<V>,
  k: List<&2, Bool>,
  +v: V,
  +w: V,
  held: Bool,
  e: {held == same(v, w): Bool},
  g: {Trie.get(V, s, k) == Some{v}: Maybe<&2, V>}
) -> {
  Trie.union.leaf(
    ~V,
    ~join,
    Shared.Bool.when(Trie<V>, held, u => Trie.drop(V, s, k), u => s),
    k,
    w
  )
    == Trie.union.leaf(~V, ~join, s, k, w): Trie<V>
}:
  match held:
    case True{}:
      Trie.union_drop(
        ~V,
        ~join,
        s,
        k,
        v,
        w
      )(g)(absorb(w)(v)(Equal.sym(Bool, True{}, same(v, w), e)))
    case False{}:
      {==}

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Trie.union_lacks for an entry of r, once what s holds at its key is known (m)
def Trie.union_lacks.cut(
  ~V: Data,
  ~join: V -> V -> V,
  ~same: V -> V -> Bool,
  ~absorb: @w: V -> @v: V -> {same(v, w) == True{}: Bool} -> {join(w, v) == w: V},
  s: Trie<V>,
  k: List<&2, Bool>,
  +w: V,
  m: Maybe<&2, V>,
  e: {m == Trie.get(V, s, k): Maybe<&2, V>}
) -> {
  Trie.union.leaf(
    ~V,
    ~join,
    Trie.minus.cut(~V, ~same, s, k, w, m),
    k,
    w
  )
    == Trie.union.leaf(~V, ~join, s, k, w): Trie<V>
}:
  match m:
    case None{}:
      {==}
    case Some{+v}:
      Trie.union_lacks.cut.if(
        ~V,
        ~join,
        ~same,
        ~absorb,
        s,
        k,
        v,
        w,
        same(v, w),
        {==},
        Equal.sym(Maybe<&2, V>, Some{v}, Trie.get(V, s, k), e)
      )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# taking in what r lacks of s is taking in s, when the join keeps a value that
# takes in a same one
def Trie.union_lacks(
  ~V: Data,
  ~join: V -> V -> V,
  ~same: V -> V -> Bool,
  ~absorb: @w: V -> @v: V -> {same(v, w) == True{}: Bool} -> {join(w, v) == w: V},
  s: Trie<V>,
  r: Trie<V>
) -> {
  Trie.union(~V, ~join, r, Trie.minus(~V, ~same, s, r)) == Trie.union(~V, ~join, r, s): Trie<V>
}:
  match s r:
    case Tip{} y:
      {==}
    case Leaf{+k, v} +y:
      Trie.union_lacks.leaf(~V, ~join, ~same, ~absorb, y, k, v, Trie.get(V, y, k), {==})
    case Bin{+h, +z, +o} Tip{}:
      {==}
    case Bin{+h, +z, +o} Leaf{+k, w}:
      Trie.union_lacks.cut(
        ~V,
        ~join,
        ~same,
        ~absorb,
        Bin{h, z, o},
        k,
        w,
        Trie.get(V, Bin{h, z, o}, k),
        {==}
      )
    case Bin{+h1, +z1, +o1} Bin{+h2, +z2, +o2}:
      -pick1 = Shared.Maybe.join(~V, ~join, h2, Trie.minus.here(~V, ~same, h1, h2))
      -union1 = Trie.union(~V, ~join, z2, Trie.minus(~V, ~same, z1, z2))
      -union2 = Trie.union(~V, ~join, o2, Trie.minus(~V, ~same, o1, o2))
      -union3 = Trie.union(~V, ~join, o2, o1)
      %Trie.union_bin(
        ~V,
        ~join,
        h2,
        z2,
        o2,
        Trie.minus.here(~V, ~same, h1, h2),
        Trie.minus(~V, ~same, z1, z2),
        Trie.minus(~V, ~same, o1, o2)
      ): {_ == Trie.union(~V, ~join, Bin{h2, z2, o2}, Bin{h1, z1, o1}): Trie<V>}
      %Trie.union_lacks.here(~V, ~join, ~same, ~absorb, h1, h2):
        {Bin{pick1, union1, union2} == Bin{_, Trie.union(~V, ~join, z2, z1), union3}: Trie<V>}
      %Trie.union_lacks(~V, ~join, ~same, ~absorb, z1, z2):
        {Bin{pick1, union1, union2} == Bin{pick1, _, union3}: Trie<V>}
      %Trie.union_lacks(~V, ~join, ~same, ~absorb, o1, o2):
        {Bin{pick1, union1, union2} == Bin{pick1, union1, _}: Trie<V>}
      {==}
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# a value takes in a same one, when the join is idempotent
def Trie.union_minus.absorb(
  ~V: Data,
  ~join: V -> V -> V,
  ~same: V -> V -> Bool,
  ~idem: @x: V -> {join(x, x) == x: V},
  ~laws: Shared.Eq.Laws(V, same),
  +w: V,
  v: V,
  e: {same(v, w) == True{}: Bool}
) -> {join(w, v) == w: V}:
  %Equal.sym(V, v, w, Shared.Eq.sound(~V, ~same, laws, v)(w)(e)): {join(w, _) == w: V}
  idem(w)
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

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

def Trie.union_minus(ty, join, same, idem, laws, s, r):
  Trie.union_lacks(
    ~ty,
    ~join,
    ~same,
    ~(w => v => e => Trie.union_minus.absorb(~ty, ~join, ~same, ~idem, ~laws, w, v, e)),
    s,
    r
  )

# Sizes and keys apart
# --------------------

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# bend-lint: expect-begin bend-lint-rules/performance/missed_fork@hint -- a proof does not run
# bend-lint: expect-end bend-lint-rules/performance/missed_fork@hint

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# Trie.get_under for an entry
def Trie.get_under.leaf(
  -V: Data,
  p: List<&2, Bool>,
  k: List<&2, Bool>,
  -v: V,
  -r: List<&2, Bool>
) -> {
  Trie.get(
    V,
    Trie.under.leaf(V, p, k, v),
    r
  )
    == Trie.get(V, Leaf{k, v}, List.append(&2, Bool, p, r)): Maybe<&2, V>
}:
  match p k:
    case Nil{} q:
      {==}
    case Con{False{}, q} Nil{}:
      {==}
    case Con{True{}, q} Nil{}:
      {==}
    case Con{False{}, q} Con{False{}, k1}:
      Trie.get_under.leaf(V, q, k1, v, r)
    case Con{True{}, q} Con{True{}, k1}:
      Trie.get_under.leaf(V, q, k1, v, r)
    case Con{False{}, q} Con{True{}, k1}:
      {==}
    case Con{True{}, q} Con{False{}, k1}:
      {==}

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
    case Leaf{k, v} q:
      Trie.get_under.leaf(V, q, k, v, r)
    case Bin{h, z, o} Nil{}:
      {==}
    case Bin{h, z, o} Con{False{}, q}:
      Trie.get_under(V, z, q, r)
    case Bin{h, z, o} Con{True{}, q}:
      Trie.get_under(V, o, q, r)

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
    case Leaf{k, v}:
      p(Some{v})
    case Bin{h, z, o}:
      Bool.and(p(h), Bool.and(Trie.all(~V, ~p, z), Trie.all(~V, ~p, o)))

# Trie.all2 for the entry of k and v and the entry of p and w: the check of
# their nodes
def Trie.all2.fork(
  ~V: Data,
  ~W: Data,
  ~r: Maybe<&2, V> -> Maybe<&2, W> -> Bool,
  ~left: Trie<V> -> Bool,
  k: List<&2, Bool>,
  v: V,
  p: List<&2, Bool>,
  w: W
) -> Bool:
  match k p:
    case Nil{} Nil{}:
      Bool.and(r(Some{v}, Some{w}), Bool.and(True{}, True{}))
    case Nil{} Con{b, q}:
      Bool.and(r(Some{v}, None{}), Bool.and(True{}, True{}))
    case Con{False{}, rr} Nil{}:
      Bool.and(r(None{}, Some{w}), Bool.and(left(Leaf{rr, v}), True{}))
    case Con{True{}, rr} Nil{}:
      Bool.and(r(None{}, Some{w}), Bool.and(True{}, left(Leaf{rr, v})))
    case Con{False{}, rr} Con{False{}, q}:
      Bool.and(r(None{}, None{}), Bool.and(Trie.all2.fork(~V, ~W, ~r, ~left, rr, v, q, w), True{}))
    case Con{True{}, rr} Con{True{}, q}:
      Bool.and(r(None{}, None{}), Bool.and(True{}, Trie.all2.fork(~V, ~W, ~r, ~left, rr, v, q, w)))
    case Con{False{}, rr} Con{True{}, q}:
      Bool.and(r(None{}, None{}), Bool.and(left(Leaf{rr, v}), True{}))
    case Con{True{}, rr} Con{False{}, q}:
      Bool.and(r(None{}, None{}), Bool.and(True{}, left(Leaf{rr, v})))

# Trie.all2 for the entry of k and v and the trie y: the check of the node of
# the entry
def Trie.all2.leaf(
  ~V: Data,
  ~W: Data,
  ~r: Maybe<&2, V> -> Maybe<&2, W> -> Bool,
  ~left: Trie<V> -> Bool,
  y: Trie<W>,
  k: List<&2, Bool>,
  v: V
) -> Bool:
  match y k:
    case Tip{} q:
      left(Leaf{q, v})
    case Leaf{p, w} q:
      Trie.all2.fork(~V, ~W, ~r, ~left, q, v, p, w)
    case Bin{h, z, o} Nil{}:
      Bool.and(r(Some{v}, h), Bool.and(True{}, True{}))
    case Bin{h, z, o} Con{False{}, rr}:
      Bool.and(r(None{}, h), Bool.and(Trie.all2.leaf(~V, ~W, ~r, ~left, z, rr, v), True{}))
    case Bin{h, z, o} Con{True{}, rr}:
      Bool.and(r(None{}, h), Bool.and(True{}, Trie.all2.leaf(~V, ~W, ~r, ~left, o, rr, v)))

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
    case Leaf{k, v} y:
      Trie.all2.leaf(~V, ~W, ~r, ~left, y, k, v)
    case Bin{h, z, o} Tip{}:
      left(Bin{h, z, o})
    case Bin{h, z, o} Leaf{+p, +w}:
      Bool.and(
        r(h, Trie.at.here(W, p, w)),
        Bool.and(
          Trie.all2(~V, ~W, ~r, ~left, z, Trie.at.zero(W, p, w)),
          Trie.all2(~V, ~W, ~r, ~left, o, Trie.at.one(W, p, w))
        )
      )
    case Bin{h1, z1, o1} Bin{h2, z2, o2}:
      Bool.and(
        r(h1, h2),
        Bool.and(Trie.all2(~V, ~W, ~r, ~left, z1, z2), Trie.all2(~V, ~W, ~r, ~left, o1, o2))
      )

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# Trie.all_get for an entry, by whether the key is its key (held)
def Trie.all_get.leaf(
  ~V: Data,
  ~p: Maybe<&2, V> -> Bool,
  -v: V,
  pn: {p(None{}) == True{}: Bool},
  e: {p(Some{v}) == True{}: Bool},
  held: Bool
) -> {p(Bool.pick(Maybe<&2, V>, held, Some{v}, None{})) == True{}: Bool}:
  match held:
    case True{}:
      e
    case False{}:
      pn

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
    case Leaf{k0, v} q:
      e => Trie.all_get.leaf(~V, ~p, v, pn, e, Trie.same_key(q, k0))
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
    case Leaf{k, c}:
      e => Empty.absurd(
        {Trie.size(V, Leaf{k, c}) == 0n: Nat},
        Shared.Bool.false_ne_true(pn(Some{c})(e))
      )
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

# a leaf and its node: the check of a leaf and a node is the check of the nodes
def Trie.all2_node.bin(
  ~V: Data,
  ~W: Data,
  ~r: Maybe<&2, V> -> Maybe<&2, W> -> Bool,
  ~left: Trie<V> -> Bool,
  k: List<&2, Bool>,
  -v: V,
  -h: Maybe<&2, W>,
  -z: Trie<W>,
  -o: Trie<W>
) -> {
  Bool.and(
    r(Trie.at.here(V, k, v), h),
    Bool.and(
      Trie.all2(~V, ~W, ~r, ~left, Trie.at.zero(V, k, v), z),
      Trie.all2(~V, ~W, ~r, ~left, Trie.at.one(V, k, v), o)
    )
  )
    == Trie.all2(~V, ~W, ~r, ~left, Leaf{k, v}, Bin{h, z, o}): Bool
}:
  match k:
    case Nil{}:
      {==}
    case Con{False{}, q}:
      {==}
    case Con{True{}, q}:
      {==}

# the check of two leaves is the check of their nodes
def Trie.all2_node.leaf(
  ~V: Data,
  ~W: Data,
  ~r: Maybe<&2, V> -> Maybe<&2, W> -> Bool,
  ~left: Trie<V> -> Bool,
  k: List<&2, Bool>,
  -v: V,
  p: List<&2, Bool>,
  -w: W
) -> {
  Bool.and(
    r(Trie.at.here(V, k, v), Trie.at.here(W, p, w)),
    Bool.and(
      Trie.all2(~V, ~W, ~r, ~left, Trie.at.zero(V, k, v), Trie.at.zero(W, p, w)),
      Trie.all2(~V, ~W, ~r, ~left, Trie.at.one(V, k, v), Trie.at.one(W, p, w))
    )
  )
    == Trie.all2(~V, ~W, ~r, ~left, Leaf{k, v}, Leaf{p, w}): Bool
}:
  match k p:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{False{}, q2}:
      {==}
    case Nil{} Con{True{}, q2}:
      {==}
    case Con{False{}, q} Nil{}:
      {==}
    case Con{False{}, q} Con{False{}, q2}:
      {==}
    case Con{False{}, q} Con{True{}, q2}:
      {==}
    case Con{True{}, q} Nil{}:
      {==}
    case Con{True{}, q} Con{False{}, q2}:
      {==}
    case Con{True{}, q} Con{True{}, q2}:
      {==}

# Trie.all2_get at a node, from its parts
def Trie.all2_get.node(
  ~V: Data,
  ~W: Data,
  ~r: Maybe<&2, V> -> Maybe<&2, W> -> Bool,
  ~left: Trie<V> -> Bool,
  h1: Maybe<&2, V>,
  +z1: Trie<V>,
  +o1: Trie<V>,
  h2: Maybe<&2, W>,
  +z2: Trie<W>,
  +o2: Trie<W>,
  k: List<&2, Bool>,
  ihz: @q: List<
    &2,
    Bool> -> {
    Trie.all2(~V, ~W, ~r, ~left, z1, z2) == True{}: Bool
  } -> {r(Trie.get(V, z1, q), Trie.get(W, z2, q)) == True{}: Bool},
  iho: @q: List<
    &2,
    Bool> -> {
    Trie.all2(~V, ~W, ~r, ~left, o1, o2) == True{}: Bool
  } -> {r(Trie.get(V, o1, q), Trie.get(W, o2, q)) == True{}: Bool}
) -> {
  Bool.and(
    r(h1, h2),
    Bool.and(Trie.all2(~V, ~W, ~r, ~left, z1, z2), Trie.all2(~V, ~W, ~r, ~left, o1, o2))
  )
    == True{}: Bool
} -> {r(Trie.get(V, Bin{h1, z1, o1}, k), Trie.get(W, Bin{h2, z2, o2}, k)) == True{}: Bool}:
  match k:
    case Nil{}:
      e => Shared.Bool.and_true_left(
        r(h1, h2),
        Bool.and(Trie.all2(~V, ~W, ~r, ~left, z1, z2), Trie.all2(~V, ~W, ~r, ~left, o1, o2))
      )(e)
    case Con{False{}, q}:
      e => ihz(
        q
      )(
        Shared.Bool.and_true_left(
          Trie.all2(~V, ~W, ~r, ~left, z1, z2),
          Trie.all2(~V, ~W, ~r, ~left, o1, o2)
        )(
          Shared.Bool.and_true_right(
            r(h1, h2),
            Bool.and(Trie.all2(~V, ~W, ~r, ~left, z1, z2), Trie.all2(~V, ~W, ~r, ~left, o1, o2))
          )(e)
        )
      )
    case Con{True{}, q}:
      e => iho(
        q
      )(
        Shared.Bool.and_true_right(
          Trie.all2(~V, ~W, ~r, ~left, z1, z2),
          Trie.all2(~V, ~W, ~r, ~left, o1, o2)
        )(
          Shared.Bool.and_true_right(
            r(h1, h2),
            Bool.and(Trie.all2(~V, ~W, ~r, ~left, z1, z2), Trie.all2(~V, ~W, ~r, ~left, o1, o2))
          )(e)
        )
      )

# Trie.all2_get for two entries
def Trie.all2_get.fork(
  ~V: Data,
  ~W: Data,
  ~r: Maybe<&2, V> -> Maybe<&2, W> -> Bool,
  ~left: Trie<V> -> Bool,
  ~rn: @y: Maybe<&2, W> -> {r(None{}, y) == True{}: Bool},
  ~lget: @t: Trie<
    V> -> @k: List<
    &2,
    Bool> -> {left(t) == True{}: Bool} -> {r(Trie.get(V, t, k), None{}) == True{}: Bool},
  k1: List<&2, Bool>,
  +v: V,
  p: List<&2, Bool>,
  +w: W,
  +k: List<&2, Bool>
) -> {
  Trie.all2.fork(~V, ~W, ~r, ~left, k1, v, p, w) == True{}: Bool
} -> {r(Trie.get(V, Leaf{k1, v}, k), Trie.get(W, Leaf{p, w}, k)) == True{}: Bool}:
  match k1 p:
    case Nil{} Nil{}:
      e =>
        %Trie.get_node(V, [], v, k): {r(_, Trie.get(W, Leaf{[], w}, k)) == True{}: Bool}
        %Trie.get_node(
          W,
          [],
          w,
          k
        ): {r(Trie.get(V, Bin{Some{v}, Tip{}, Tip{}}, k), _) == True{}: Bool}
        Trie.all2_get.node(
          ~V,
          ~W,
          ~r,
          ~left,
          Some{v},
          Tip{},
          Tip{},
          Some{w},
          Tip{},
          Tip{},
          k,
          q => e2 => rn(Trie.get(W, Tip{}, q)),
          q => e2 => rn(Trie.get(W, Tip{}, q))
        )(e)
    case Nil{} Con{False{}, +rp}:
      e =>
        %Trie.get_node(V, [], v, k): {r(_, Trie.get(W, Leaf{False{} <> rp, w}, k)) == True{}: Bool}
        %Trie.get_node(
          W,
          False{} <> rp,
          w,
          k
        ): {r(Trie.get(V, Bin{Some{v}, Tip{}, Tip{}}, k), _) == True{}: Bool}
        Trie.all2_get.node(
          ~V,
          ~W,
          ~r,
          ~left,
          Some{v},
          Tip{},
          Tip{},
          None{},
          Leaf{rp, w},
          Tip{},
          k,
          q => e2 => rn(Trie.get(W, Leaf{rp, w}, q)),
          q => e2 => rn(Trie.get(W, Tip{}, q))
        )(e)
    case Nil{} Con{True{}, +rp}:
      e =>
        %Trie.get_node(V, [], v, k): {r(_, Trie.get(W, Leaf{True{} <> rp, w}, k)) == True{}: Bool}
        %Trie.get_node(
          W,
          True{} <> rp,
          w,
          k
        ): {r(Trie.get(V, Bin{Some{v}, Tip{}, Tip{}}, k), _) == True{}: Bool}
        Trie.all2_get.node(
          ~V,
          ~W,
          ~r,
          ~left,
          Some{v},
          Tip{},
          Tip{},
          None{},
          Tip{},
          Leaf{rp, w},
          k,
          q => e2 => rn(Trie.get(W, Tip{}, q)),
          q => e2 => rn(Trie.get(W, Leaf{rp, w}, q))
        )(e)
    case Con{False{}, +r1} Nil{}:
      e =>
        %Trie.get_node(V, False{} <> r1, v, k): {r(_, Trie.get(W, Leaf{[], w}, k)) == True{}: Bool}
        %Trie.get_node(
          W,
          [],
          w,
          k
        ): {r(Trie.get(V, Bin{None{}, Leaf{r1, v}, Tip{}}, k), _) == True{}: Bool}
        Trie.all2_get.node(
          ~V,
          ~W,
          ~r,
          ~left,
          None{},
          Leaf{r1, v},
          Tip{},
          Some{w},
          Tip{},
          Tip{},
          k,
          q => e2 => lget(Leaf{r1, v})(q)(e2),
          q => e2 => rn(Trie.get(W, Tip{}, q))
        )(e)
    case Con{False{}, +r1} Con{False{}, +rp}:
      e =>
        %Trie.get_node(
          V,
          False{} <> r1,
          v,
          k
        ): {r(_, Trie.get(W, Leaf{False{} <> rp, w}, k)) == True{}: Bool}
        %Trie.get_node(
          W,
          False{} <> rp,
          w,
          k
        ): {r(Trie.get(V, Bin{None{}, Leaf{r1, v}, Tip{}}, k), _) == True{}: Bool}
        Trie.all2_get.node(
          ~V,
          ~W,
          ~r,
          ~left,
          None{},
          Leaf{r1, v},
          Tip{},
          None{},
          Leaf{rp, w},
          Tip{},
          k,
          q => e2 => Trie.all2_get.fork(~V, ~W, ~r, ~left, ~rn, ~lget, r1, v, rp, w, q)(e2),
          q => e2 => rn(Trie.get(W, Tip{}, q))
        )(e)
    case Con{False{}, +r1} Con{True{}, +rp}:
      e =>
        %Trie.get_node(
          V,
          False{} <> r1,
          v,
          k
        ): {r(_, Trie.get(W, Leaf{True{} <> rp, w}, k)) == True{}: Bool}
        %Trie.get_node(
          W,
          True{} <> rp,
          w,
          k
        ): {r(Trie.get(V, Bin{None{}, Leaf{r1, v}, Tip{}}, k), _) == True{}: Bool}
        Trie.all2_get.node(
          ~V,
          ~W,
          ~r,
          ~left,
          None{},
          Leaf{r1, v},
          Tip{},
          None{},
          Tip{},
          Leaf{rp, w},
          k,
          q => e2 => lget(Leaf{r1, v})(q)(e2),
          q => e2 => rn(Trie.get(W, Leaf{rp, w}, q))
        )(e)
    case Con{True{}, +r1} Nil{}:
      e =>
        %Trie.get_node(V, True{} <> r1, v, k): {r(_, Trie.get(W, Leaf{[], w}, k)) == True{}: Bool}
        %Trie.get_node(
          W,
          [],
          w,
          k
        ): {r(Trie.get(V, Bin{None{}, Tip{}, Leaf{r1, v}}, k), _) == True{}: Bool}
        Trie.all2_get.node(
          ~V,
          ~W,
          ~r,
          ~left,
          None{},
          Tip{},
          Leaf{r1, v},
          Some{w},
          Tip{},
          Tip{},
          k,
          q => e2 => rn(Trie.get(W, Tip{}, q)),
          q => e2 => lget(Leaf{r1, v})(q)(e2)
        )(e)
    case Con{True{}, +r1} Con{False{}, +rp}:
      e =>
        %Trie.get_node(
          V,
          True{} <> r1,
          v,
          k
        ): {r(_, Trie.get(W, Leaf{False{} <> rp, w}, k)) == True{}: Bool}
        %Trie.get_node(
          W,
          False{} <> rp,
          w,
          k
        ): {r(Trie.get(V, Bin{None{}, Tip{}, Leaf{r1, v}}, k), _) == True{}: Bool}
        Trie.all2_get.node(
          ~V,
          ~W,
          ~r,
          ~left,
          None{},
          Tip{},
          Leaf{r1, v},
          None{},
          Leaf{rp, w},
          Tip{},
          k,
          q => e2 => rn(Trie.get(W, Leaf{rp, w}, q)),
          q => e2 => lget(Leaf{r1, v})(q)(e2)
        )(e)
    case Con{True{}, +r1} Con{True{}, +rp}:
      e =>
        %Trie.get_node(
          V,
          True{} <> r1,
          v,
          k
        ): {r(_, Trie.get(W, Leaf{True{} <> rp, w}, k)) == True{}: Bool}
        %Trie.get_node(
          W,
          True{} <> rp,
          w,
          k
        ): {r(Trie.get(V, Bin{None{}, Tip{}, Leaf{r1, v}}, k), _) == True{}: Bool}
        Trie.all2_get.node(
          ~V,
          ~W,
          ~r,
          ~left,
          None{},
          Tip{},
          Leaf{r1, v},
          None{},
          Tip{},
          Leaf{rp, w},
          k,
          q => e2 => rn(Trie.get(W, Tip{}, q)),
          q => e2 => Trie.all2_get.fork(~V, ~W, ~r, ~left, ~rn, ~lget, r1, v, rp, w, q)(e2)
        )(e)

# Trie.all2_get for an entry and a trie
def Trie.all2_get.leaf(
  ~V: Data,
  ~W: Data,
  ~r: Maybe<&2, V> -> Maybe<&2, W> -> Bool,
  ~left: Trie<V> -> Bool,
  ~rn: @y: Maybe<&2, W> -> {r(None{}, y) == True{}: Bool},
  ~lget: @t: Trie<
    V> -> @k: List<
    &2,
    Bool> -> {left(t) == True{}: Bool} -> {r(Trie.get(V, t, k), None{}) == True{}: Bool},
  y: Trie<W>,
  k1: List<&2, Bool>,
  +v: V,
  +k: List<&2, Bool>
) -> {
  Trie.all2.leaf(~V, ~W, ~r, ~left, y, k1, v) == True{}: Bool
} -> {r(Trie.get(V, Leaf{k1, v}, k), Trie.get(W, y, k)) == True{}: Bool}:
  match y k1:
    case Tip{} r1:
      e => lget(Leaf{r1, v})(k)(e)
    case Leaf{p, w} r1:
      Trie.all2_get.fork(~V, ~W, ~r, ~left, ~rn, ~lget, r1, v, p, w, k)
    case Bin{h, +z, +o} Nil{}:
      e =>
        %Trie.get_node(V, [], v, k): {r(_, Trie.get(W, Bin{h, z, o}, k)) == True{}: Bool}
        Trie.all2_get.node(
          ~V,
          ~W,
          ~r,
          ~left,
          Some{v},
          Tip{},
          Tip{},
          h,
          z,
          o,
          k,
          q => e2 => rn(Trie.get(W, z, q)),
          q => e2 => rn(Trie.get(W, o, q))
        )(e)
    case Bin{+h, +z, +o} Con{False{}, +r1}:
      e =>
        %Trie.get_node(V, False{} <> r1, v, k): {r(_, Trie.get(W, Bin{h, z, o}, k)) == True{}: Bool}
        Trie.all2_get.node(
          ~V,
          ~W,
          ~r,
          ~left,
          None{},
          Leaf{r1, v},
          Tip{},
          h,
          z,
          o,
          k,
          q => e2 => Trie.all2_get.leaf(~V, ~W, ~r, ~left, ~rn, ~lget, z, r1, v, q)(e2),
          q => e2 => rn(Trie.get(W, o, q))
        )(e)
    case Bin{+h, +z, +o} Con{True{}, +r1}:
      e =>
        %Trie.get_node(V, True{} <> r1, v, k): {r(_, Trie.get(W, Bin{h, z, o}, k)) == True{}: Bool}
        Trie.all2_get.node(
          ~V,
          ~W,
          ~r,
          ~left,
          None{},
          Tip{},
          Leaf{r1, v},
          h,
          z,
          o,
          k,
          q => e2 => rn(Trie.get(W, z, q)),
          q => e2 => Trie.all2_get.leaf(~V, ~W, ~r, ~left, ~rn, ~lget, o, r1, v, q)(e2)
        )(e)

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
    case Leaf{p, v} y q:
      Trie.all2_get.leaf(~tv, ~tw, ~r, ~left, ~rn, ~lget, y, p, v, q)
    case Bin{h, z, o} Tip{} q:
      e => lget(Bin{h, z, o})(q)(e)
    case Bin{+h, +z, +o} Leaf{+p, +w} +q:
      e =>
        %Trie.get_node(tw, p, w, q): {r(Trie.get(tv, Bin{h, z, o}, q), _) == True{}: Bool}
        Trie.all2_get.node(
          ~tv,
          ~tw,
          ~r,
          ~left,
          h,
          z,
          o,
          Trie.at.here(tw, p, w),
          Trie.at.zero(tw, p, w),
          Trie.at.one(tw, p, w),
          q,
          q2 => e2 => Trie.all2_get(
            ~tv,
            ~tw,
            ~r,
            ~left,
            ~rn,
            ~lget,
            z,
            Trie.at.zero(tw, p, w),
            q2
          )(e2),
          q2 => e2 => Trie.all2_get(
            ~tv,
            ~tw,
            ~r,
            ~left,
            ~rn,
            ~lget,
            o,
            Trie.at.one(tw, p, w),
            q2
          )(e2)
        )(e)
    case Bin{+h1, +z1, +o1} Bin{h2, +z2, +o2} q:
      Trie.all2_get.node(
        ~tv,
        ~tw,
        ~r,
        ~left,
        h1,
        z1,
        o1,
        h2,
        z2,
        o2,
        q,
        q2 => e2 => Trie.all2_get(~tv, ~tw, ~r, ~left, ~rn, ~lget, z1, z2, q2)(e2),
        q2 => e2 => Trie.all2_get(~tv, ~tw, ~r, ~left, ~rn, ~lget, o1, o2, q2)(e2)
      )

# Trie.all2_under for two entries
def Trie.all2_under.fork(
  ~V: Data,
  ~W: Data,
  ~r: Maybe<&2, V> -> Maybe<&2, W> -> Bool,
  ~left: Trie<V> -> Bool,
  ~lunder: @t: Trie<
    V> -> @k: List<
    &2,
    Bool> -> {
    left(t) == True{}: Bool
  } -> {Trie.all2(~V, ~W, ~r, ~left, Trie.under(V, t, k), Tip{}) == True{}: Bool},
  k1: List<&2, Bool>,
  +v: V,
  p: List<&2, Bool>,
  +w: W,
  k: List<&2, Bool>
) -> {
  Trie.all2.fork(~V, ~W, ~r, ~left, k1, v, p, w) == True{}: Bool
} -> {
  Trie.all2(
    ~V,
    ~W,
    ~r,
    ~left,
    Trie.under(V, Leaf{k1, v}, k),
    Trie.under(W, Leaf{p, w}, k)
  )
    == True{}: Bool
}:
  match k1 p k:
    case r1 rp Nil{}:
      e => e
    case Nil{} Nil{} Con{False{}, q}:
      e => {==}
    case Nil{} Nil{} Con{True{}, +q}:
      e => {==}
    case Nil{} Con{False{}, rp} Con{False{}, q}:
      e => {==}
    case Nil{} Con{False{}, +rp} Con{True{}, +q}:
      e => {==}
    case Nil{} Con{True{}, +rp} Con{False{}, q}:
      e => {==}
    case Nil{} Con{True{}, +rp} Con{True{}, +q}:
      e => {==}
    case Con{False{}, +r1} Nil{} Con{False{}, q}:
      e => lunder(
        Leaf{r1, v}
      )(
        q
      )(
        Shared.Bool.and_true_left(
          left(Leaf{r1, v}),
          True{}
        )(Shared.Bool.and_true_right(r(None{}, Some{w}), Bool.and(left(Leaf{r1, v}), True{}))(e))
      )
    case Con{False{}, +r1} Nil{} Con{True{}, +q}:
      e => {==}
    case Con{False{}, +r1} Con{False{}, +rp} Con{False{}, q}:
      e => Trie.all2_under.fork(
        ~V,
        ~W,
        ~r,
        ~left,
        ~lunder,
        r1,
        v,
        rp,
        w,
        q
      )(
        Shared.Bool.and_true_left(
          Trie.all2.fork(~V, ~W, ~r, ~left, r1, v, rp, w),
          True{}
        )(
          Shared.Bool.and_true_right(
            r(None{}, None{}),
            Bool.and(Trie.all2.fork(~V, ~W, ~r, ~left, r1, v, rp, w), True{})
          )(e)
        )
      )
    case Con{False{}, +r1} Con{False{}, +rp} Con{True{}, +q}:
      e => {==}
    case Con{False{}, +r1} Con{True{}, +rp} Con{False{}, q}:
      e => lunder(
        Leaf{r1, v}
      )(
        q
      )(
        Shared.Bool.and_true_left(
          left(Leaf{r1, v}),
          True{}
        )(Shared.Bool.and_true_right(r(None{}, None{}), Bool.and(left(Leaf{r1, v}), True{}))(e))
      )
    case Con{False{}, +r1} Con{True{}, +rp} Con{True{}, +q}:
      e => {==}
    case Con{True{}, +r1} Nil{} Con{False{}, q}:
      e => {==}
    case Con{True{}, +r1} Nil{} Con{True{}, +q}:
      e => lunder(
        Leaf{r1, v}
      )(
        q
      )(
        Shared.Bool.and_true_right(
          True{},
          left(Leaf{r1, v})
        )(Shared.Bool.and_true_right(r(None{}, Some{w}), Bool.and(True{}, left(Leaf{r1, v})))(e))
      )
    case Con{True{}, +r1} Con{False{}, +rp} Con{False{}, q}:
      e => {==}
    case Con{True{}, +r1} Con{False{}, +rp} Con{True{}, +q}:
      e => lunder(
        Leaf{r1, v}
      )(
        q
      )(
        Shared.Bool.and_true_right(
          True{},
          left(Leaf{r1, v})
        )(Shared.Bool.and_true_right(r(None{}, None{}), Bool.and(True{}, left(Leaf{r1, v})))(e))
      )
    case Con{True{}, +r1} Con{True{}, +rp} Con{False{}, q}:
      e => {==}
    case Con{True{}, +r1} Con{True{}, +rp} Con{True{}, +q}:
      e => Trie.all2_under.fork(
        ~V,
        ~W,
        ~r,
        ~left,
        ~lunder,
        r1,
        v,
        rp,
        w,
        q
      )(
        Shared.Bool.and_true_right(
          True{},
          Trie.all2.fork(~V, ~W, ~r, ~left, r1, v, rp, w)
        )(
          Shared.Bool.and_true_right(
            r(None{}, None{}),
            Bool.and(True{}, Trie.all2.fork(~V, ~W, ~r, ~left, r1, v, rp, w))
          )(e)
        )
      )

# Trie.all2_under for an entry and a trie
def Trie.all2_under.leaf(
  ~V: Data,
  ~W: Data,
  ~r: Maybe<&2, V> -> Maybe<&2, W> -> Bool,
  ~left: Trie<V> -> Bool,
  ~lunder: @t: Trie<
    V> -> @k: List<
    &2,
    Bool> -> {
    left(t) == True{}: Bool
  } -> {Trie.all2(~V, ~W, ~r, ~left, Trie.under(V, t, k), Tip{}) == True{}: Bool},
  y: Trie<W>,
  k1: List<&2, Bool>,
  +v: V,
  k: List<&2, Bool>
) -> {
  Trie.all2.leaf(~V, ~W, ~r, ~left, y, k1, v) == True{}: Bool
} -> {
  Trie.all2(~V, ~W, ~r, ~left, Trie.under(V, Leaf{k1, v}, k), Trie.under(W, y, k)) == True{}: Bool
}:
  match y k1 k:
    case Tip{} r1 q:
      e => lunder(Leaf{r1, v})(q)(e)
    case Leaf{p, w} r1 q:
      Trie.all2_under.fork(~V, ~W, ~r, ~left, ~lunder, r1, v, p, w, q)
    case Bin{h, z, o} r1 Nil{}:
      e => e
    case Bin{+h, +z, +o} Nil{} Con{False{}, q}:
      e => {==}
    case Bin{+h, +z, +o} Nil{} Con{True{}, +q}:
      e => {==}
    case Bin{+h, +z, +o} Con{False{}, +r1} Con{False{}, q}:
      e => Trie.all2_under.leaf(
        ~V,
        ~W,
        ~r,
        ~left,
        ~lunder,
        z,
        r1,
        v,
        q
      )(
        Shared.Bool.and_true_left(
          Trie.all2.leaf(~V, ~W, ~r, ~left, z, r1, v),
          True{}
        )(
          Shared.Bool.and_true_right(
            r(None{}, h),
            Bool.and(Trie.all2.leaf(~V, ~W, ~r, ~left, z, r1, v), True{})
          )(e)
        )
      )
    case Bin{+h, +z, +o} Con{False{}, +r1} Con{True{}, +q}:
      e => {==}
    case Bin{+h, +z, +o} Con{True{}, +r1} Con{False{}, q}:
      e => {==}
    case Bin{+h, +z, +o} Con{True{}, +r1} Con{True{}, +q}:
      e => Trie.all2_under.leaf(
        ~V,
        ~W,
        ~r,
        ~left,
        ~lunder,
        o,
        r1,
        v,
        q
      )(
        Shared.Bool.and_true_right(
          True{},
          Trie.all2.leaf(~V, ~W, ~r, ~left, o, r1, v)
        )(
          Shared.Bool.and_true_right(
            r(None{}, h),
            Bool.and(True{}, Trie.all2.leaf(~V, ~W, ~r, ~left, o, r1, v))
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
    case Leaf{p, v} y q:
      Trie.all2_under.leaf(~tv, ~tw, ~r, ~left, ~lunder, y, p, v, q)
    case Bin{h, z, o} Tip{} q:
      e => lunder(Bin{h, z, o})(q)(e)
    case Bin{h, z, o} Leaf{p, w} Nil{}:
      e => e
    case Bin{+h, +z, +o} Leaf{+p, +w} Con{False{}, q}:
      e =>
        %Trie.under_zero(
          tw,
          p,
          w,
          q
        ): {Trie.all2(~tv, ~tw, ~r, ~left, Trie.under(tv, z, q), _) == True{}: Bool}
        Trie.all2_under(
          ~tv,
          ~tw,
          ~r,
          ~left,
          ~lunder,
          z,
          Trie.at.zero(tw, p, w),
          q
        )(
          Shared.Bool.and_true_left(
            Trie.all2(~tv, ~tw, ~r, ~left, z, Trie.at.zero(tw, p, w)),
            Trie.all2(~tv, ~tw, ~r, ~left, o, Trie.at.one(tw, p, w))
          )(
            Shared.Bool.and_true_right(
              r(h, Trie.at.here(tw, p, w)),
              Bool.and(
                Trie.all2(~tv, ~tw, ~r, ~left, z, Trie.at.zero(tw, p, w)),
                Trie.all2(~tv, ~tw, ~r, ~left, o, Trie.at.one(tw, p, w))
              )
            )(e)
          )
        )
    case Bin{+h, +z, +o} Leaf{+p, +w} Con{True{}, +q}:
      e =>
        %Trie.under_one_part(
          tw,
          p,
          w,
          q
        ): {Trie.all2(~tv, ~tw, ~r, ~left, Trie.under(tv, o, q), _) == True{}: Bool}
        Trie.all2_under(
          ~tv,
          ~tw,
          ~r,
          ~left,
          ~lunder,
          o,
          Trie.at.one(tw, p, w),
          q
        )(
          Shared.Bool.and_true_right(
            Trie.all2(~tv, ~tw, ~r, ~left, z, Trie.at.zero(tw, p, w)),
            Trie.all2(~tv, ~tw, ~r, ~left, o, Trie.at.one(tw, p, w))
          )(
            Shared.Bool.and_true_right(
              r(h, Trie.at.here(tw, p, w)),
              Bool.and(
                Trie.all2(~tv, ~tw, ~r, ~left, z, Trie.at.zero(tw, p, w)),
                Trie.all2(~tv, ~tw, ~r, ~left, o, Trie.at.one(tw, p, w))
              )
            )(e)
          )
        )
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
# Trie.all2_refl for an entry
def Trie.all2_refl.leaf(
  ~V: Data,
  ~r: Maybe<&2, V> -> Maybe<&2, V> -> Bool,
  ~left: Trie<V> -> Bool,
  ~rrefl: @m: Maybe<&2, V> -> {r(m, m) == True{}: Bool},
  k: List<&2, Bool>,
  +v: V
) -> {Trie.all2.fork(~V, ~V, ~r, ~left, k, v, k, v) == True{}: Bool}:
  match k:
    case Nil{}:
      Shared.Bool.and_both(r(Some{v}, Some{v}), Bool.and(True{}, True{}))(rrefl(Some{v}))({==})
    case Con{False{}, +q}:
      Shared.Bool.and_both(
        r(None{}, None{}),
        Bool.and(Trie.all2.fork(~V, ~V, ~r, ~left, q, v, q, v), True{})
      )(
        rrefl(None{})
      )(
        Shared.Bool.and_both(
          Trie.all2.fork(~V, ~V, ~r, ~left, q, v, q, v),
          True{}
        )(Trie.all2_refl.leaf(~V, ~r, ~left, ~rrefl, q, v))({==})
      )
    case Con{True{}, +q}:
      Shared.Bool.and_both(
        r(None{}, None{}),
        Bool.and(True{}, Trie.all2.fork(~V, ~V, ~r, ~left, q, v, q, v))
      )(
        rrefl(None{})
      )(
        Shared.Bool.and_both(
          True{},
          Trie.all2.fork(~V, ~V, ~r, ~left, q, v, q, v)
        )({==})(Trie.all2_refl.leaf(~V, ~r, ~left, ~rrefl, q, v))
      )

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
    case Leaf{k, v}:
      Trie.all2_refl.leaf(~V, ~r, ~left, ~rrefl, k, v)
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

# the check of an entry and a node over a part is the check of the nodes
def Trie.all2_bin.f(
  ~V: Data,
  ~W: Data,
  ~r: Maybe<&2, V> -> Maybe<&2, W> -> Bool,
  ~left: Trie<V> -> Bool,
  x: Trie<W>,
  -k: List<&2, Bool>,
  -v: V
) -> {
  Trie.is_tip(W, x) == False{}: Bool
} -> {
  Bool.and(
    r(None{}, None{}),
    Bool.and(Trie.all2.leaf(~V, ~W, ~r, ~left, x, k, v), True{})
  )
    == Trie.all2.leaf(~V, ~W, ~r, ~left, Trie.bin(W, None{}, x, Tip{}), False{} <> k, v): Bool
}:
  match x:
    case Tip{}:
      e => Empty.absurd(
        {
          Bool.and(
            r(None{}, None{}),
            Bool.and(Trie.all2.leaf(~V, ~W, ~r, ~left, Tip{}, k, v), True{})
          )
            == Trie.all2.leaf(
              ~V,
              ~W,
              ~r,
              ~left,
              Trie.bin(W, None{}, Tip{}, Tip{}),
              False{} <> k,
              v
            ): Bool
        },
        Trie.true_ne_false(e)
      )
    case Leaf{p, w}:
      e => {==}
    case Bin{h, z, o}:
      e => {==}

# the check of an entry and a node over a part is the check of the nodes
def Trie.all2_bin.t(
  ~V: Data,
  ~W: Data,
  ~r: Maybe<&2, V> -> Maybe<&2, W> -> Bool,
  ~left: Trie<V> -> Bool,
  x: Trie<W>,
  -k: List<&2, Bool>,
  -v: V
) -> {
  Trie.is_tip(W, x) == False{}: Bool
} -> {
  Bool.and(
    r(None{}, None{}),
    Bool.and(True{}, Trie.all2.leaf(~V, ~W, ~r, ~left, x, k, v))
  )
    == Trie.all2.leaf(~V, ~W, ~r, ~left, Trie.bin(W, None{}, Tip{}, x), True{} <> k, v): Bool
}:
  match x:
    case Tip{}:
      e => Empty.absurd(
        {
          Bool.and(
            r(None{}, None{}),
            Bool.and(True{}, Trie.all2.leaf(~V, ~W, ~r, ~left, Tip{}, k, v))
          )
            == Trie.all2.leaf(
              ~V,
              ~W,
              ~r,
              ~left,
              Trie.bin(W, None{}, Tip{}, Tip{}),
              True{} <> k,
              v
            ): Bool
        },
        Trie.true_ne_false(e)
      )
    case Leaf{p, w}:
      e => {==}
    case Bin{h, z, o}:
      e => {==}

# Trie.all2_join at a node, from its parts
def Trie.all2_join.node(
  ~V: Data,
  ~join: V -> V -> V,
  ~q: Maybe<&2, V> -> Maybe<&2, V> -> Bool,
  ~lq: Trie<V> -> Bool,
  ~r: Maybe<&2, V> -> Maybe<&2, V> -> Bool,
  ~lr: Trie<V> -> Bool,
  ~step: @a: Maybe<
    &2,
    V> -> @b: Maybe<
    &2,
    V> -> {q(a, b) == True{}: Bool} -> {r(a, Shared.Maybe.join(~V, ~join, a, b)) == True{}: Bool},
  ~rrefl: @m: Maybe<&2, V> -> {r(m, m) == True{}: Bool},
  +h1: Maybe<&2, V>,
  +z1: Trie<V>,
  +o1: Trie<V>,
  +h2: Maybe<&2, V>,
  +z2: Trie<V>,
  +o2: Trie<V>,
  ihz: {
    Trie.all2(~V, ~V, ~q, ~lq, z1, z2) == True{}: Bool
  } -> {Trie.all2(~V, ~V, ~r, ~lr, z1, Trie.union(~V, ~join, z1, z2)) == True{}: Bool},
  iho: {
    Trie.all2(~V, ~V, ~q, ~lq, o1, o2) == True{}: Bool
  } -> {Trie.all2(~V, ~V, ~r, ~lr, o1, Trie.union(~V, ~join, o1, o2)) == True{}: Bool}
) -> {
  Bool.and(
    q(h1, h2),
    Bool.and(Trie.all2(~V, ~V, ~q, ~lq, z1, z2), Trie.all2(~V, ~V, ~q, ~lq, o1, o2))
  )
    == True{}: Bool
} -> {
  Bool.and(
    r(h1, Shared.Maybe.join(~V, ~join, h1, h2)),
    Bool.and(
      Trie.all2(~V, ~V, ~r, ~lr, z1, Trie.union(~V, ~join, z1, z2)),
      Trie.all2(~V, ~V, ~r, ~lr, o1, Trie.union(~V, ~join, o1, o2))
    )
  )
    == True{}: Bool
}:
  +e =>
    +rest = Shared.Bool.and_true_right(
      q(h1, h2),
      Bool.and(Trie.all2(~V, ~V, ~q, ~lq, z1, z2), Trie.all2(~V, ~V, ~q, ~lq, o1, o2))
    )(e)
    Shared.Bool.and_both(
      r(h1, Shared.Maybe.join(~V, ~join, h1, h2)),
      Bool.and(
        Trie.all2(~V, ~V, ~r, ~lr, z1, Trie.union(~V, ~join, z1, z2)),
        Trie.all2(~V, ~V, ~r, ~lr, o1, Trie.union(~V, ~join, o1, o2))
      )
    )(
      step(
        h1
      )(
        h2
      )(
        Shared.Bool.and_true_left(
          q(h1, h2),
          Bool.and(Trie.all2(~V, ~V, ~q, ~lq, z1, z2), Trie.all2(~V, ~V, ~q, ~lq, o1, o2))
        )(e)
      )
    )(
      Shared.Bool.and_both(
        Trie.all2(~V, ~V, ~r, ~lr, z1, Trie.union(~V, ~join, z1, z2)),
        Trie.all2(~V, ~V, ~r, ~lr, o1, Trie.union(~V, ~join, o1, o2))
      )(
        ihz(
          Shared.Bool.and_true_left(
            Trie.all2(~V, ~V, ~q, ~lq, z1, z2),
            Trie.all2(~V, ~V, ~q, ~lq, o1, o2)
          )(rest)
        )
      )(
        iho(
          Shared.Bool.and_true_right(
            Trie.all2(~V, ~V, ~q, ~lq, z1, z2),
            Trie.all2(~V, ~V, ~q, ~lq, o1, o2)
          )(rest)
        )
      )
    )

# Trie.all2_join for two entries
def Trie.all2_join.fork(
  ~V: Data,
  ~join: V -> V -> V,
  ~q: Maybe<&2, V> -> Maybe<&2, V> -> Bool,
  ~lq: Trie<V> -> Bool,
  ~r: Maybe<&2, V> -> Maybe<&2, V> -> Bool,
  ~lr: Trie<V> -> Bool,
  ~step: @a: Maybe<
    &2,
    V> -> @b: Maybe<
    &2,
    V> -> {q(a, b) == True{}: Bool} -> {r(a, Shared.Maybe.join(~V, ~join, a, b)) == True{}: Bool},
  ~rrefl: @m: Maybe<&2, V> -> {r(m, m) == True{}: Bool},
  k1: List<&2, Bool>,
  +v: V,
  p: List<&2, Bool>,
  +w: V
) -> {
  Trie.all2.fork(~V, ~V, ~q, ~lq, k1, v, p, w) == True{}: Bool
} -> {
  Trie.all2.leaf(~V, ~V, ~r, ~lr, Trie.union.fork(~V, ~join, k1, v, p, w), k1, v) == True{}: Bool
}:
  match k1 p:
    case Nil{} Nil{}:
      Trie.all2_join.node(
        ~V,
        ~join,
        ~q,
        ~lq,
        ~r,
        ~lr,
        ~step,
        ~rrefl,
        Some{v},
        Tip{},
        Tip{},
        Some{w},
        Tip{},
        Tip{},
        e2 => {==},
        e2 => {==}
      )
    case Nil{} Con{False{}, rp}:
      Trie.all2_join.node(
        ~V,
        ~join,
        ~q,
        ~lq,
        ~r,
        ~lr,
        ~step,
        ~rrefl,
        Some{v},
        Tip{},
        Tip{},
        None{},
        Leaf{rp, w},
        Tip{},
        e2 => {==},
        e2 => {==}
      )
    case Nil{} Con{True{}, +rp}:
      Trie.all2_join.node(
        ~V,
        ~join,
        ~q,
        ~lq,
        ~r,
        ~lr,
        ~step,
        ~rrefl,
        Some{v},
        Tip{},
        Tip{},
        None{},
        Tip{},
        Leaf{rp, w},
        e2 => {==},
        e2 => {==}
      )
    case Con{False{}, +r1} Nil{}:
      Trie.all2_join.node(
        ~V,
        ~join,
        ~q,
        ~lq,
        ~r,
        ~lr,
        ~step,
        ~rrefl,
        None{},
        Leaf{r1, v},
        Tip{},
        Some{w},
        Tip{},
        Tip{},
        e2 => Trie.all2_refl.leaf(~V, ~r, ~lr, ~rrefl, r1, v),
        e2 => {==}
      )
    case Con{False{}, +r1} Con{False{}, +rp}:
      e =>
        %Trie.all2_bin.f(
          ~V,
          ~V,
          ~r,
          ~lr,
          Trie.union.fork(~V, ~join, r1, v, rp, w),
          r1,
          v
        )(Trie.fork_part(~V, ~join, r1, v, rp, w)):
          {_ == True{}: Bool}
        Trie.all2_join.node(
          ~V,
          ~join,
          ~q,
          ~lq,
          ~r,
          ~lr,
          ~step,
          ~rrefl,
          None{},
          Leaf{r1, v},
          Tip{},
          None{},
          Leaf{rp, w},
          Tip{},
          Trie.all2_join.fork(~V, ~join, ~q, ~lq, ~r, ~lr, ~step, ~rrefl, r1, v, rp, w),
          e2 => {==}
        )(e)
    case Con{False{}, +r1} Con{True{}, +rp}:
      Trie.all2_join.node(
        ~V,
        ~join,
        ~q,
        ~lq,
        ~r,
        ~lr,
        ~step,
        ~rrefl,
        None{},
        Leaf{r1, v},
        Tip{},
        None{},
        Tip{},
        Leaf{rp, w},
        e2 => Trie.all2_refl.leaf(~V, ~r, ~lr, ~rrefl, r1, v),
        e2 => {==}
      )
    case Con{True{}, +r1} Nil{}:
      Trie.all2_join.node(
        ~V,
        ~join,
        ~q,
        ~lq,
        ~r,
        ~lr,
        ~step,
        ~rrefl,
        None{},
        Tip{},
        Leaf{r1, v},
        Some{w},
        Tip{},
        Tip{},
        e2 => {==},
        e2 => Trie.all2_refl.leaf(~V, ~r, ~lr, ~rrefl, r1, v)
      )
    case Con{True{}, +r1} Con{False{}, +rp}:
      Trie.all2_join.node(
        ~V,
        ~join,
        ~q,
        ~lq,
        ~r,
        ~lr,
        ~step,
        ~rrefl,
        None{},
        Tip{},
        Leaf{r1, v},
        None{},
        Leaf{rp, w},
        Tip{},
        e2 => {==},
        e2 => Trie.all2_refl.leaf(~V, ~r, ~lr, ~rrefl, r1, v)
      )
    case Con{True{}, +r1} Con{True{}, +rp}:
      e =>
        %Trie.all2_bin.t(
          ~V,
          ~V,
          ~r,
          ~lr,
          Trie.union.fork(~V, ~join, r1, v, rp, w),
          r1,
          v
        )(Trie.fork_part(~V, ~join, r1, v, rp, w)):
          {_ == True{}: Bool}
        Trie.all2_join.node(
          ~V,
          ~join,
          ~q,
          ~lq,
          ~r,
          ~lr,
          ~step,
          ~rrefl,
          None{},
          Tip{},
          Leaf{r1, v},
          None{},
          Tip{},
          Leaf{rp, w},
          e2 => {==},
          Trie.all2_join.fork(~V, ~join, ~q, ~lq, ~r, ~lr, ~step, ~rrefl, r1, v, rp, w)
        )(e)

# Trie.all2_join for an entry and a trie
def Trie.all2_join.leaf(
  ~V: Data,
  ~join: V -> V -> V,
  ~q: Maybe<&2, V> -> Maybe<&2, V> -> Bool,
  ~lq: Trie<V> -> Bool,
  ~r: Maybe<&2, V> -> Maybe<&2, V> -> Bool,
  ~lr: Trie<V> -> Bool,
  ~step: @a: Maybe<
    &2,
    V> -> @b: Maybe<
    &2,
    V> -> {q(a, b) == True{}: Bool} -> {r(a, Shared.Maybe.join(~V, ~join, a, b)) == True{}: Bool},
  ~rrefl: @m: Maybe<&2, V> -> {r(m, m) == True{}: Bool},
  y: Trie<V>,
  k1: List<&2, Bool>,
  +v: V
) -> {
  Trie.all2.leaf(~V, ~V, ~q, ~lq, y, k1, v) == True{}: Bool
} -> {Trie.all2.leaf(~V, ~V, ~r, ~lr, Trie.union.leaf(~V, ~join, y, k1, v), k1, v) == True{}: Bool}:
  match y k1:
    case Tip{} r1:
      e => Trie.all2_refl.leaf(~V, ~r, ~lr, ~rrefl, r1, v)
    case Leaf{p, w} r1:
      Trie.all2_join.fork(~V, ~join, ~q, ~lq, ~r, ~lr, ~step, ~rrefl, r1, v, p, w)
    case Bin{h, +z, +o} Nil{}:
      Trie.all2_join.node(
        ~V,
        ~join,
        ~q,
        ~lq,
        ~r,
        ~lr,
        ~step,
        ~rrefl,
        Some{v},
        Tip{},
        Tip{},
        h,
        z,
        o,
        e2 => {==},
        e2 => {==}
      )
    case Bin{+h, +z, +o} Con{False{}, +r1}:
      Trie.all2_join.node(
        ~V,
        ~join,
        ~q,
        ~lq,
        ~r,
        ~lr,
        ~step,
        ~rrefl,
        None{},
        Leaf{r1, v},
        Tip{},
        h,
        z,
        o,
        Trie.all2_join.leaf(~V, ~join, ~q, ~lq, ~r, ~lr, ~step, ~rrefl, z, r1, v),
        e2 => {==}
      )
    case Bin{+h, +z, +o} Con{True{}, +r1}:
      Trie.all2_join.node(
        ~V,
        ~join,
        ~q,
        ~lq,
        ~r,
        ~lr,
        ~step,
        ~rrefl,
        None{},
        Tip{},
        Leaf{r1, v},
        h,
        z,
        o,
        e2 => {==},
        Trie.all2_join.leaf(~V, ~join, ~q, ~lq, ~r, ~lr, ~step, ~rrefl, o, r1, v)
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
    case Leaf{k, v} y:
      Trie.all2_join.leaf(~ty, ~join, ~q, ~lq, ~r, ~lr, ~step, ~rrefl, y, k, v)
    case Bin{h, z, o} Tip{}:
      e => Trie.all2_refl(~ty, ~r, ~lr, ~rrefl, Bin{h, z, o})
    case Bin{+h, +z, +o} Leaf{+p, +w}:
      Trie.all2_join.node(
        ~ty,
        ~join,
        ~q,
        ~lq,
        ~r,
        ~lr,
        ~step,
        ~rrefl,
        h,
        z,
        o,
        Trie.at.here(ty, p, w),
        Trie.at.zero(ty, p, w),
        Trie.at.one(ty, p, w),
        Trie.all2_join(~ty, ~join, ~q, ~lq, ~r, ~lr, ~step, ~rrefl, z, Trie.at.zero(ty, p, w)),
        Trie.all2_join(~ty, ~join, ~q, ~lq, ~r, ~lr, ~step, ~rrefl, o, Trie.at.one(ty, p, w))
      )
    case Bin{+h1, +z1, +o1} Bin{h2, +z2, +o2}:
      Trie.all2_join.node(
        ~ty,
        ~join,
        ~q,
        ~lq,
        ~r,
        ~lr,
        ~step,
        ~rrefl,
        h1,
        z1,
        o1,
        h2,
        z2,
        o2,
        Trie.all2_join(~ty, ~join, ~q, ~lq, ~r, ~lr, ~step, ~rrefl, z1, z2),
        Trie.all2_join(~ty, ~join, ~q, ~lq, ~r, ~lr, ~step, ~rrefl, o1, o2)
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
    case Leaf{k, v}:
      ltrue(Leaf{k, v})
    case Bin{h, z, o}:
      ltrue(Bin{h, z, o})

# Trie.all2_one for two entries
def Trie.all2_one.fork(
  ~V: Data,
  ~r: Maybe<&2, V> -> Maybe<&2, V> -> Bool,
  ~left: Trie<V> -> Bool,
  ~rn: @y: Maybe<&2, V> -> {r(None{}, y) == True{}: Bool},
  ~rl: @a: Maybe<&2, V> -> {r(a, None{}) == True{}: Bool},
  ~ltrue: @t: Trie<V> -> {left(t) == True{}: Bool},
  k1: List<&2, Bool>,
  +v: V,
  p: List<&2, Bool>,
  +w: V
) -> {
  Trie.get(V, Leaf{k1, v}, p) == None{}: Maybe<&2, V>
} -> {Trie.all2.fork(~V, ~V, ~r, ~left, k1, v, p, w) == True{}: Bool}:
  match k1 p:
    case Nil{} Nil{}:
      g => Empty.absurd(
        {Trie.all2.fork(~V, ~V, ~r, ~left, [], v, [], w) == True{}: Bool},
        Trie.some_ne_none(V, v, g)
      )
    case Nil{} Con{False{}, rp}:
      g => Shared.Bool.and_both(
        r(Some{v}, None{}),
        Bool.and(True{}, True{})
      )(rl(Some{v}))(Shared.Bool.and_both(True{}, True{})({==})({==}))
    case Nil{} Con{True{}, +rp}:
      g => Shared.Bool.and_both(
        r(Some{v}, None{}),
        Bool.and(True{}, True{})
      )(rl(Some{v}))(Shared.Bool.and_both(True{}, True{})({==})({==}))
    case Con{False{}, +r1} Nil{}:
      g => Shared.Bool.and_both(
        r(None{}, Some{w}),
        Bool.and(left(Leaf{r1, v}), True{})
      )(rn(Some{w}))(Shared.Bool.and_both(left(Leaf{r1, v}), True{})(ltrue(Leaf{r1, v}))({==}))
    case Con{False{}, +r1} Con{False{}, +rp}:
      g => Shared.Bool.and_both(
        r(None{}, None{}),
        Bool.and(Trie.all2.fork(~V, ~V, ~r, ~left, r1, v, rp, w), True{})
      )(
        rn(None{})
      )(
        Shared.Bool.and_both(
          Trie.all2.fork(~V, ~V, ~r, ~left, r1, v, rp, w),
          True{}
        )(Trie.all2_one.fork(~V, ~r, ~left, ~rn, ~rl, ~ltrue, r1, v, rp, w)(g))({==})
      )
    case Con{False{}, +r1} Con{True{}, +rp}:
      g => Shared.Bool.and_both(
        r(None{}, None{}),
        Bool.and(left(Leaf{r1, v}), True{})
      )(rn(None{}))(Shared.Bool.and_both(left(Leaf{r1, v}), True{})(ltrue(Leaf{r1, v}))({==}))
    case Con{True{}, +r1} Nil{}:
      g => Shared.Bool.and_both(
        r(None{}, Some{w}),
        Bool.and(True{}, left(Leaf{r1, v}))
      )(rn(Some{w}))(Shared.Bool.and_both(True{}, left(Leaf{r1, v}))({==})(ltrue(Leaf{r1, v})))
    case Con{True{}, +r1} Con{False{}, +rp}:
      g => Shared.Bool.and_both(
        r(None{}, None{}),
        Bool.and(True{}, left(Leaf{r1, v}))
      )(rn(None{}))(Shared.Bool.and_both(True{}, left(Leaf{r1, v}))({==})(ltrue(Leaf{r1, v})))
    case Con{True{}, +r1} Con{True{}, +rp}:
      g => Shared.Bool.and_both(
        r(None{}, None{}),
        Bool.and(True{}, Trie.all2.fork(~V, ~V, ~r, ~left, r1, v, rp, w))
      )(
        rn(None{})
      )(
        Shared.Bool.and_both(
          True{},
          Trie.all2.fork(~V, ~V, ~r, ~left, r1, v, rp, w)
        )({==})(Trie.all2_one.fork(~V, ~r, ~left, ~rn, ~rl, ~ltrue, r1, v, rp, w)(g))
      )

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
    case Leaf{p, w} q:
      Trie.all2_one.fork(~ty, ~r, ~left, ~rn, ~rl, ~ltrue, p, w, q, x)
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

# Trie.keeps_of_all at a node, from its parts
def Trie.keeps_of_all.node(
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
  +h1: Maybe<&2, V>,
  +z1: Trie<V>,
  +o1: Trie<V>,
  +h2: Maybe<&2, V>,
  +z2: Trie<V>,
  +o2: Trie<V>,
  ihz: {
    Trie.all(~V, ~(m => r(m, None{})), z1) == True{}: Bool
  } -> {Trie.keeps(~V, ~r, z1, z2) == True{}: Bool},
  iho: {
    Trie.all(~V, ~(m => r(m, None{})), o1) == True{}: Bool
  } -> {Trie.keeps(~V, ~r, o1, o2) == True{}: Bool}
) -> {
  Bool.and(
    r(h1, None{}),
    Bool.and(Trie.all(~V, ~(m => r(m, None{})), z1), Trie.all(~V, ~(m => r(m, None{})), o1))
  )
    == True{}: Bool
} -> {
  Bool.and(
    r(h1, h2),
    Bool.and(Trie.keeps(~V, ~r, z1, z2), Trie.keeps(~V, ~r, o1, o2))
  )
    == True{}: Bool
}:
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
          Bool.and(Trie.all(~V, ~(m => r(m, None{})), z1), Trie.all(~V, ~(m => r(m, None{})), o1))
        )(e)
      )(rn(h2))
    )(
      Shared.Bool.and_both(
        Trie.keeps(~V, ~r, z1, z2),
        Trie.keeps(~V, ~r, o1, o2)
      )(
        ihz(
          Shared.Bool.and_true_left(
            Trie.all(~V, ~(m => r(m, None{})), z1),
            Trie.all(~V, ~(m => r(m, None{})), o1)
          )(rest)
        )
      )(
        iho(
          Shared.Bool.and_true_right(
            Trie.all(~V, ~(m => r(m, None{})), z1),
            Trie.all(~V, ~(m => r(m, None{})), o1)
          )(rest)
        )
      )
    )

# Trie.keeps_of_all for two entries
def Trie.keeps_of_all.fork(
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
  k1: List<&2, Bool>,
  +v: V,
  k2: List<&2, Bool>,
  +w: V
) -> {
  r(Some{v}, None{}) == True{}: Bool
} -> {Trie.keeps(~V, ~r, Leaf{k1, v}, Leaf{k2, w}) == True{}: Bool}:
  match k1 k2:
    case Nil{} Nil{}:
      e => Shared.Bool.and_both(
        r(Some{v}, Some{w}),
        Bool.and(True{}, True{})
      )(
        rtrans(Some{v})(None{})(Some{w})(e)(rn(Some{w}))
      )(Shared.Bool.and_both(True{}, True{})({==})({==}))
    case Nil{} Con{False{}, r2}:
      e => Shared.Bool.and_both(
        r(Some{v}, None{}),
        Bool.and(True{}, True{})
      )(e)(Shared.Bool.and_both(True{}, True{})({==})({==}))
    case Nil{} Con{True{}, +r2}:
      e => Shared.Bool.and_both(
        r(Some{v}, None{}),
        Bool.and(True{}, True{})
      )(e)(Shared.Bool.and_both(True{}, True{})({==})({==}))
    case Con{False{}, +r1} Nil{}:
      e => Shared.Bool.and_both(
        r(None{}, Some{w}),
        Bool.and(r(Some{v}, None{}), True{})
      )(rn(Some{w}))(Shared.Bool.and_both(r(Some{v}, None{}), True{})(e)({==}))
    case Con{False{}, +r1} Con{False{}, +r2}:
      e => Shared.Bool.and_both(
        r(None{}, None{}),
        Bool.and(Trie.keeps(~V, ~r, Leaf{r1, v}, Leaf{r2, w}), True{})
      )(
        rn(None{})
      )(
        Shared.Bool.and_both(
          Trie.keeps(~V, ~r, Leaf{r1, v}, Leaf{r2, w}),
          True{}
        )(Trie.keeps_of_all.fork(~V, ~r, ~rn, ~rtrans, r1, v, r2, w)(e))({==})
      )
    case Con{False{}, +r1} Con{True{}, +r2}:
      e => Shared.Bool.and_both(
        r(None{}, None{}),
        Bool.and(r(Some{v}, None{}), True{})
      )(rn(None{}))(Shared.Bool.and_both(r(Some{v}, None{}), True{})(e)({==}))
    case Con{True{}, +r1} Nil{}:
      e => Shared.Bool.and_both(
        r(None{}, Some{w}),
        Bool.and(True{}, r(Some{v}, None{}))
      )(rn(Some{w}))(Shared.Bool.and_both(True{}, r(Some{v}, None{}))({==})(e))
    case Con{True{}, +r1} Con{False{}, +r2}:
      e => Shared.Bool.and_both(
        r(None{}, None{}),
        Bool.and(True{}, r(Some{v}, None{}))
      )(rn(None{}))(Shared.Bool.and_both(True{}, r(Some{v}, None{}))({==})(e))
    case Con{True{}, +r1} Con{True{}, +r2}:
      e => Shared.Bool.and_both(
        r(None{}, None{}),
        Bool.and(True{}, Trie.keeps(~V, ~r, Leaf{r1, v}, Leaf{r2, w}))
      )(
        rn(None{})
      )(
        Shared.Bool.and_both(
          True{},
          Trie.keeps(~V, ~r, Leaf{r1, v}, Leaf{r2, w})
        )({==})(Trie.keeps_of_all.fork(~V, ~r, ~rn, ~rtrans, r1, v, r2, w)(e))
      )

# Trie.keeps_of_all for an entry and a trie
def Trie.keeps_of_all.leaf(
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
  y: Trie<V>,
  k1: List<&2, Bool>,
  +v: V
) -> {r(Some{v}, None{}) == True{}: Bool} -> {Trie.keeps(~V, ~r, Leaf{k1, v}, y) == True{}: Bool}:
  match y k1:
    case Tip{} r1:
      e => e
    case Leaf{p, w} r1:
      Trie.keeps_of_all.fork(~V, ~r, ~rn, ~rtrans, r1, v, p, w)
    case Bin{+h, z, o} Nil{}:
      e => Shared.Bool.and_both(
        r(Some{v}, h),
        Bool.and(True{}, True{})
      )(rtrans(Some{v})(None{})(h)(e)(rn(h)))({==})
    case Bin{+h, +z, o} Con{False{}, +r1}:
      e => Shared.Bool.and_both(
        r(None{}, h),
        Bool.and(Trie.keeps(~V, ~r, Leaf{r1, v}, z), True{})
      )(
        rn(h)
      )(
        Shared.Bool.and_both(
          Trie.keeps(~V, ~r, Leaf{r1, v}, z),
          True{}
        )(Trie.keeps_of_all.leaf(~V, ~r, ~rn, ~rtrans, z, r1, v)(e))({==})
      )
    case Bin{+h, z, +o} Con{True{}, +r1}:
      e => Shared.Bool.and_both(
        r(None{}, h),
        Bool.and(True{}, Trie.keeps(~V, ~r, Leaf{r1, v}, o))
      )(
        rn(h)
      )(
        Shared.Bool.and_both(
          True{},
          Trie.keeps(~V, ~r, Leaf{r1, v}, o)
        )({==})(Trie.keeps_of_all.leaf(~V, ~r, ~rn, ~rtrans, o, r1, v)(e))
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
    case Leaf{k, v} y:
      Trie.keeps_of_all.leaf(~V, ~r, ~rn, ~rtrans, y, k, v)
    case Bin{h, z, o} Tip{}:
      e => e
    case Bin{+h, +z, +o} Leaf{+p, +w}:
      Trie.keeps_of_all.node(
        ~V,
        ~r,
        ~rn,
        ~rtrans,
        h,
        z,
        o,
        Trie.at.here(V, p, w),
        Trie.at.zero(V, p, w),
        Trie.at.one(V, p, w),
        Trie.keeps_of_all(~V, ~r, ~rn, ~rtrans, z, Trie.at.zero(V, p, w)),
        Trie.keeps_of_all(~V, ~r, ~rn, ~rtrans, o, Trie.at.one(V, p, w))
      )
    case Bin{+h1, +z1, +o1} Bin{h2, +z2, +o2}:
      Trie.keeps_of_all.node(
        ~V,
        ~r,
        ~rn,
        ~rtrans,
        h1,
        z1,
        o1,
        h2,
        z2,
        o2,
        Trie.keeps_of_all(~V, ~r, ~rn, ~rtrans, z1, z2),
        Trie.keeps_of_all(~V, ~r, ~rn, ~rtrans, o1, o2)
      )

# p holds of the parts of the node of an entry, when it holds of the entry
# and of no entry
def Trie.all_node(
  ~V: Data,
  ~p: Maybe<&2, V> -> Bool,
  pn: {p(None{}) == True{}: Bool},
  k: List<&2, Bool>,
  +v: V
) -> {
  p(Some{v}) == True{}: Bool
} -> {
  Bool.and(
    p(Trie.at.here(V, k, v)),
    Bool.and(Trie.all(~V, ~p, Trie.at.zero(V, k, v)), Trie.all(~V, ~p, Trie.at.one(V, k, v)))
  )
    == True{}: Bool
}:
  match k:
    case Nil{}:
      e => Shared.Bool.and_both(p(Some{v}), Bool.and(True{}, True{}))(e)({==})
    case Con{False{}, q}:
      e => Shared.Bool.and_both(
        p(None{}),
        Bool.and(p(Some{v}), True{})
      )(pn)(Shared.Bool.and_both(p(Some{v}), True{})(e)({==}))
    case Con{True{}, q}:
      e => Shared.Bool.and_both(
        p(None{}),
        Bool.and(True{}, p(Some{v}))
      )(pn)(Shared.Bool.and_both(True{}, p(Some{v}))({==})(e))

# Trie.all_of_keeps at a node, from its parts
def Trie.all_of_keeps.node(
  ~V: Data,
  ~r: Maybe<&2, V> -> Maybe<&2, V> -> Bool,
  ~rtrans: @x: Maybe<
    &2,
    V> -> @y: Maybe<
    &2,
    V> -> @z: Maybe<
    &2,
    V> -> {r(x, y) == True{}: Bool} -> {r(y, z) == True{}: Bool} -> {r(x, z) == True{}: Bool},
  +h1: Maybe<&2, V>,
  +z1: Trie<V>,
  +o1: Trie<V>,
  +h2: Maybe<&2, V>,
  +z2: Trie<V>,
  +o2: Trie<V>,
  ihz: {
    Trie.keeps(~V, ~r, z1, z2) == True{}: Bool
  } -> {
    Trie.all(~V, ~(m => r(m, None{})), z2) == True{}: Bool
  } -> {Trie.all(~V, ~(m => r(m, None{})), z1) == True{}: Bool},
  iho: {
    Trie.keeps(~V, ~r, o1, o2) == True{}: Bool
  } -> {
    Trie.all(~V, ~(m => r(m, None{})), o2) == True{}: Bool
  } -> {Trie.all(~V, ~(m => r(m, None{})), o1) == True{}: Bool}
) -> {
  Bool.and(
    r(h1, h2),
    Bool.and(Trie.keeps(~V, ~r, z1, z2), Trie.keeps(~V, ~r, o1, o2))
  )
    == True{}: Bool
} -> {
  Bool.and(
    r(h2, None{}),
    Bool.and(Trie.all(~V, ~(m => r(m, None{})), z2), Trie.all(~V, ~(m => r(m, None{})), o2))
  )
    == True{}: Bool
} -> {
  Bool.and(
    r(h1, None{}),
    Bool.and(Trie.all(~V, ~(m => r(m, None{})), z1), Trie.all(~V, ~(m => r(m, None{})), o1))
  )
    == True{}: Bool
}:
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
          Bool.and(Trie.all(~V, ~(m => r(m, None{})), z2), Trie.all(~V, ~(m => r(m, None{})), o2))
        )(e)
      )
    )(
      Shared.Bool.and_both(
        Trie.all(~V, ~(m => r(m, None{})), z1),
        Trie.all(~V, ~(m => r(m, None{})), o1)
      )(
        ihz(
          Shared.Bool.and_true_left(Trie.keeps(~V, ~r, z1, z2), Trie.keeps(~V, ~r, o1, o2))(gr)
        )(
          Shared.Bool.and_true_left(
            Trie.all(~V, ~(m => r(m, None{})), z2),
            Trie.all(~V, ~(m => r(m, None{})), o2)
          )(er)
        )
      )(
        iho(
          Shared.Bool.and_true_right(Trie.keeps(~V, ~r, z1, z2), Trie.keeps(~V, ~r, o1, o2))(gr)
        )(
          Shared.Bool.and_true_right(
            Trie.all(~V, ~(m => r(m, None{})), z2),
            Trie.all(~V, ~(m => r(m, None{})), o2)
          )(er)
        )
      )
    )

# Trie.all_of_keeps for two entries
def Trie.all_of_keeps.fork(
  ~V: Data,
  ~r: Maybe<&2, V> -> Maybe<&2, V> -> Bool,
  ~rtrans: @x: Maybe<
    &2,
    V> -> @y: Maybe<
    &2,
    V> -> @z: Maybe<
    &2,
    V> -> {r(x, y) == True{}: Bool} -> {r(y, z) == True{}: Bool} -> {r(x, z) == True{}: Bool},
  k1: List<&2, Bool>,
  +v: V,
  k2: List<&2, Bool>,
  +w: V
) -> {
  Trie.keeps(~V, ~r, Leaf{k1, v}, Leaf{k2, w}) == True{}: Bool
} -> {r(Some{w}, None{}) == True{}: Bool} -> {r(Some{v}, None{}) == True{}: Bool}:
  match k1 k2:
    case Nil{} Nil{}:
      g => e => rtrans(
        Some{v}
      )(
        Some{w}
      )(None{})(Shared.Bool.and_true_left(r(Some{v}, Some{w}), Bool.and(True{}, True{}))(g))(e)
    case Nil{} Con{False{}, r2}:
      g => e => Shared.Bool.and_true_left(r(Some{v}, None{}), Bool.and(True{}, True{}))(g)
    case Nil{} Con{True{}, +r2}:
      g => e => Shared.Bool.and_true_left(r(Some{v}, None{}), Bool.and(True{}, True{}))(g)
    case Con{False{}, +r1} Nil{}:
      g => e => Shared.Bool.and_true_left(
        r(Some{v}, None{}),
        True{}
      )(Shared.Bool.and_true_right(r(None{}, Some{w}), Bool.and(r(Some{v}, None{}), True{}))(g))
    case Con{False{}, +r1} Con{False{}, +r2}:
      g => e => Trie.all_of_keeps.fork(
        ~V,
        ~r,
        ~rtrans,
        r1,
        v,
        r2,
        w
      )(
        Shared.Bool.and_true_left(
          Trie.keeps(~V, ~r, Leaf{r1, v}, Leaf{r2, w}),
          True{}
        )(
          Shared.Bool.and_true_right(
            r(None{}, None{}),
            Bool.and(Trie.keeps(~V, ~r, Leaf{r1, v}, Leaf{r2, w}), True{})
          )(g)
        )
      )(e)
    case Con{False{}, +r1} Con{True{}, +r2}:
      g => e => Shared.Bool.and_true_left(
        r(Some{v}, None{}),
        True{}
      )(Shared.Bool.and_true_right(r(None{}, None{}), Bool.and(r(Some{v}, None{}), True{}))(g))
    case Con{True{}, +r1} Nil{}:
      g => e => Shared.Bool.and_true_right(
        True{},
        r(Some{v}, None{})
      )(Shared.Bool.and_true_right(r(None{}, Some{w}), Bool.and(True{}, r(Some{v}, None{})))(g))
    case Con{True{}, +r1} Con{False{}, +r2}:
      g => e => Shared.Bool.and_true_right(
        True{},
        r(Some{v}, None{})
      )(Shared.Bool.and_true_right(r(None{}, None{}), Bool.and(True{}, r(Some{v}, None{})))(g))
    case Con{True{}, +r1} Con{True{}, +r2}:
      g => e => Trie.all_of_keeps.fork(
        ~V,
        ~r,
        ~rtrans,
        r1,
        v,
        r2,
        w
      )(
        Shared.Bool.and_true_right(
          True{},
          Trie.keeps(~V, ~r, Leaf{r1, v}, Leaf{r2, w})
        )(
          Shared.Bool.and_true_right(
            r(None{}, None{}),
            Bool.and(True{}, Trie.keeps(~V, ~r, Leaf{r1, v}, Leaf{r2, w}))
          )(g)
        )
      )(e)

# Trie.all_of_keeps for an entry and a trie
def Trie.all_of_keeps.leaf(
  ~V: Data,
  ~r: Maybe<&2, V> -> Maybe<&2, V> -> Bool,
  ~rtrans: @x: Maybe<
    &2,
    V> -> @y: Maybe<
    &2,
    V> -> @z: Maybe<
    &2,
    V> -> {r(x, y) == True{}: Bool} -> {r(y, z) == True{}: Bool} -> {r(x, z) == True{}: Bool},
  y: Trie<V>,
  k1: List<&2, Bool>,
  +v: V
) -> {
  Trie.keeps(~V, ~r, Leaf{k1, v}, y) == True{}: Bool
} -> {
  Trie.all(~V, ~(m => r(m, None{})), y) == True{}: Bool
} -> {r(Some{v}, None{}) == True{}: Bool}:
  match y k1:
    case Tip{} r1:
      g => e => g
    case Leaf{p, w} r1:
      Trie.all_of_keeps.fork(~V, ~r, ~rtrans, r1, v, p, w)
    case Bin{+h, +z, +o} Nil{}:
      g => e => rtrans(
        Some{v}
      )(
        h
      )(
        None{}
      )(
        Shared.Bool.and_true_left(r(Some{v}, h), Bool.and(True{}, True{}))(g)
      )(
        Shared.Bool.and_true_left(
          r(h, None{}),
          Bool.and(Trie.all(~V, ~(m => r(m, None{})), z), Trie.all(~V, ~(m => r(m, None{})), o))
        )(e)
      )
    case Bin{+h, +z, +o} Con{False{}, +r1}:
      g => e => Trie.all_of_keeps.leaf(
        ~V,
        ~r,
        ~rtrans,
        z,
        r1,
        v
      )(
        Shared.Bool.and_true_left(
          Trie.keeps(~V, ~r, Leaf{r1, v}, z),
          True{}
        )(
          Shared.Bool.and_true_right(
            r(None{}, h),
            Bool.and(Trie.keeps(~V, ~r, Leaf{r1, v}, z), True{})
          )(g)
        )
      )(
        Shared.Bool.and_true_left(
          Trie.all(~V, ~(m => r(m, None{})), z),
          Trie.all(~V, ~(m => r(m, None{})), o)
        )(
          Shared.Bool.and_true_right(
            r(h, None{}),
            Bool.and(Trie.all(~V, ~(m => r(m, None{})), z), Trie.all(~V, ~(m => r(m, None{})), o))
          )(e)
        )
      )
    case Bin{+h, +z, +o} Con{True{}, +r1}:
      g => e => Trie.all_of_keeps.leaf(
        ~V,
        ~r,
        ~rtrans,
        o,
        r1,
        v
      )(
        Shared.Bool.and_true_right(
          True{},
          Trie.keeps(~V, ~r, Leaf{r1, v}, o)
        )(
          Shared.Bool.and_true_right(
            r(None{}, h),
            Bool.and(True{}, Trie.keeps(~V, ~r, Leaf{r1, v}, o))
          )(g)
        )
      )(
        Shared.Bool.and_true_right(
          Trie.all(~V, ~(m => r(m, None{})), z),
          Trie.all(~V, ~(m => r(m, None{})), o)
        )(
          Shared.Bool.and_true_right(
            r(h, None{}),
            Bool.and(Trie.all(~V, ~(m => r(m, None{})), z), Trie.all(~V, ~(m => r(m, None{})), o))
          )(e)
        )
      )

# r holds of each entry of a and no entry, when it does of b and b keeps a
def Trie.all_of_keeps(
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
  Trie.keeps(~V, ~r, a, b) == True{}: Bool
} -> {
  Trie.all(~V, ~(m => r(m, None{})), b) == True{}: Bool
} -> {Trie.all(~V, ~(m => r(m, None{})), a) == True{}: Bool}:
  match a b:
    case Tip{} y:
      g => e => {==}
    case Leaf{k, v} y:
      Trie.all_of_keeps.leaf(~V, ~r, ~rtrans, y, k, v)
    case Bin{h, z, o} Tip{}:
      g => e => g
    case Bin{+h, +z, +o} Leaf{+p, +w}:
      g => e =>
        Trie.all_of_keeps.node(
          ~V,
          ~r,
          ~rtrans,
          h,
          z,
          o,
          Trie.at.here(V, p, w),
          Trie.at.zero(V, p, w),
          Trie.at.one(V, p, w),
          Trie.all_of_keeps(~V, ~r, ~rn, ~rtrans, z, Trie.at.zero(V, p, w)),
          Trie.all_of_keeps(~V, ~r, ~rn, ~rtrans, o, Trie.at.one(V, p, w))
        )(g)(Trie.all_node(~V, ~(m => r(m, None{})), rn(None{}), p, w)(e))
    case Bin{+h1, +z1, +o1} Bin{h2, +z2, +o2}:
      Trie.all_of_keeps.node(
        ~V,
        ~r,
        ~rtrans,
        h1,
        z1,
        o1,
        h2,
        z2,
        o2,
        Trie.all_of_keeps(~V, ~r, ~rn, ~rtrans, z1, z2),
        Trie.all_of_keeps(~V, ~r, ~rn, ~rtrans, o1, o2)
      )

# Trie.keeps_trans at a node, from its parts
def Trie.keeps_trans.node(
  ~V: Data,
  ~r: Maybe<&2, V> -> Maybe<&2, V> -> Bool,
  ~rtrans: @x: Maybe<
    &2,
    V> -> @y: Maybe<
    &2,
    V> -> @z: Maybe<
    &2,
    V> -> {r(x, y) == True{}: Bool} -> {r(y, z) == True{}: Bool} -> {r(x, z) == True{}: Bool},
  +h1: Maybe<&2, V>,
  +z1: Trie<V>,
  +o1: Trie<V>,
  +h2: Maybe<&2, V>,
  +z2: Trie<V>,
  +o2: Trie<V>,
  +h3: Maybe<&2, V>,
  +z3: Trie<V>,
  +o3: Trie<V>,
  ihz: {
    Trie.keeps(~V, ~r, z1, z2) == True{}: Bool
  } -> {Trie.keeps(~V, ~r, z2, z3) == True{}: Bool} -> {Trie.keeps(~V, ~r, z1, z3) == True{}: Bool},
  iho: {
    Trie.keeps(~V, ~r, o1, o2) == True{}: Bool
  } -> {Trie.keeps(~V, ~r, o2, o3) == True{}: Bool} -> {Trie.keeps(~V, ~r, o1, o3) == True{}: Bool}
) -> {
  Bool.and(
    r(h1, h2),
    Bool.and(Trie.keeps(~V, ~r, z1, z2), Trie.keeps(~V, ~r, o1, o2))
  )
    == True{}: Bool
} -> {
  Bool.and(
    r(h2, h3),
    Bool.and(Trie.keeps(~V, ~r, z2, z3), Trie.keeps(~V, ~r, o2, o3))
  )
    == True{}: Bool
} -> {
  Bool.and(
    r(h1, h3),
    Bool.and(Trie.keeps(~V, ~r, z1, z3), Trie.keeps(~V, ~r, o1, o3))
  )
    == True{}: Bool
}:
  +g1 => +g2 =>
    +a1 = Shared.Bool.and_true_right(
      r(h1, h2),
      Bool.and(Trie.keeps(~V, ~r, z1, z2), Trie.keeps(~V, ~r, o1, o2))
    )(g1)
    +a2 = Shared.Bool.and_true_right(
      r(h2, h3),
      Bool.and(Trie.keeps(~V, ~r, z2, z3), Trie.keeps(~V, ~r, o2, o3))
    )(g2)
    Shared.Bool.and_both(
      r(h1, h3),
      Bool.and(Trie.keeps(~V, ~r, z1, z3), Trie.keeps(~V, ~r, o1, o3))
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
          Bool.and(Trie.keeps(~V, ~r, z1, z2), Trie.keeps(~V, ~r, o1, o2))
        )(g1)
      )(
        Shared.Bool.and_true_left(
          r(h2, h3),
          Bool.and(Trie.keeps(~V, ~r, z2, z3), Trie.keeps(~V, ~r, o2, o3))
        )(g2)
      )
    )(
      Shared.Bool.and_both(
        Trie.keeps(~V, ~r, z1, z3),
        Trie.keeps(~V, ~r, o1, o3)
      )(
        ihz(
          Shared.Bool.and_true_left(Trie.keeps(~V, ~r, z1, z2), Trie.keeps(~V, ~r, o1, o2))(a1)
        )(Shared.Bool.and_true_left(Trie.keeps(~V, ~r, z2, z3), Trie.keeps(~V, ~r, o2, o3))(a2))
      )(
        iho(
          Shared.Bool.and_true_right(Trie.keeps(~V, ~r, z1, z2), Trie.keeps(~V, ~r, o1, o2))(a1)
        )(Shared.Bool.and_true_right(Trie.keeps(~V, ~r, z2, z3), Trie.keeps(~V, ~r, o2, o3))(a2))
      )
    )

# Trie.keeps_trans for three entries
def Trie.keeps_trans.fork(
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
  k1: List<&2, Bool>,
  +v: V,
  k2: List<&2, Bool>,
  +w: V,
  k3: List<&2, Bool>,
  +x: V
) -> {
  Trie.keeps(~V, ~r, Leaf{k1, v}, Leaf{k2, w}) == True{}: Bool
} -> {
  Trie.keeps(~V, ~r, Leaf{k2, w}, Leaf{k3, x}) == True{}: Bool
} -> {Trie.keeps(~V, ~r, Leaf{k1, v}, Leaf{k3, x}) == True{}: Bool}:
  match k1 k2 k3:
    case Nil{} Nil{} Nil{}:
      Trie.keeps_trans.node(
        ~V,
        ~r,
        ~rtrans,
        Some{v},
        Tip{},
        Tip{},
        Some{w},
        Tip{},
        Tip{},
        Some{x},
        Tip{},
        Tip{},
        a1 => a2 => {==},
        a1 => a2 => {==}
      )
    case Nil{} Nil{} Con{False{}, r3}:
      Trie.keeps_trans.node(
        ~V,
        ~r,
        ~rtrans,
        Some{v},
        Tip{},
        Tip{},
        Some{w},
        Tip{},
        Tip{},
        None{},
        Leaf{r3, x},
        Tip{},
        a1 => a2 => {==},
        a1 => a2 => {==}
      )
    case Nil{} Nil{} Con{True{}, +r3}:
      Trie.keeps_trans.node(
        ~V,
        ~r,
        ~rtrans,
        Some{v},
        Tip{},
        Tip{},
        Some{w},
        Tip{},
        Tip{},
        None{},
        Tip{},
        Leaf{r3, x},
        a1 => a2 => {==},
        a1 => a2 => {==}
      )
    case Nil{} Con{False{}, r2} Nil{}:
      Trie.keeps_trans.node(
        ~V,
        ~r,
        ~rtrans,
        Some{v},
        Tip{},
        Tip{},
        None{},
        Leaf{r2, w},
        Tip{},
        Some{x},
        Tip{},
        Tip{},
        a1 => a2 => {==},
        a1 => a2 => {==}
      )
    case Nil{} Con{False{}, +r2} Con{False{}, r3}:
      Trie.keeps_trans.node(
        ~V,
        ~r,
        ~rtrans,
        Some{v},
        Tip{},
        Tip{},
        None{},
        Leaf{r2, w},
        Tip{},
        None{},
        Leaf{r3, x},
        Tip{},
        a1 => a2 => {==},
        a1 => a2 => {==}
      )
    case Nil{} Con{False{}, +r2} Con{True{}, +r3}:
      Trie.keeps_trans.node(
        ~V,
        ~r,
        ~rtrans,
        Some{v},
        Tip{},
        Tip{},
        None{},
        Leaf{r2, w},
        Tip{},
        None{},
        Tip{},
        Leaf{r3, x},
        a1 => a2 => {==},
        a1 => a2 => {==}
      )
    case Nil{} Con{True{}, +r2} Nil{}:
      Trie.keeps_trans.node(
        ~V,
        ~r,
        ~rtrans,
        Some{v},
        Tip{},
        Tip{},
        None{},
        Tip{},
        Leaf{r2, w},
        Some{x},
        Tip{},
        Tip{},
        a1 => a2 => {==},
        a1 => a2 => {==}
      )
    case Nil{} Con{True{}, +r2} Con{False{}, r3}:
      Trie.keeps_trans.node(
        ~V,
        ~r,
        ~rtrans,
        Some{v},
        Tip{},
        Tip{},
        None{},
        Tip{},
        Leaf{r2, w},
        None{},
        Leaf{r3, x},
        Tip{},
        a1 => a2 => {==},
        a1 => a2 => {==}
      )
    case Nil{} Con{True{}, +r2} Con{True{}, +r3}:
      Trie.keeps_trans.node(
        ~V,
        ~r,
        ~rtrans,
        Some{v},
        Tip{},
        Tip{},
        None{},
        Tip{},
        Leaf{r2, w},
        None{},
        Tip{},
        Leaf{r3, x},
        a1 => a2 => {==},
        a1 => a2 => {==}
      )
    case Con{False{}, +r1} Nil{} Nil{}:
      Trie.keeps_trans.node(
        ~V,
        ~r,
        ~rtrans,
        None{},
        Leaf{r1, v},
        Tip{},
        Some{w},
        Tip{},
        Tip{},
        Some{x},
        Tip{},
        Tip{},
        a1 => a2 => Trie.keeps_of_all.leaf(~V, ~r, ~rn, ~rtrans, Tip{}, r1, v)(a1),
        a1 => a2 => {==}
      )
    case Con{False{}, +r1} Nil{} Con{False{}, +r3}:
      Trie.keeps_trans.node(
        ~V,
        ~r,
        ~rtrans,
        None{},
        Leaf{r1, v},
        Tip{},
        Some{w},
        Tip{},
        Tip{},
        None{},
        Leaf{r3, x},
        Tip{},
        a1 => a2 => Trie.keeps_of_all.leaf(~V, ~r, ~rn, ~rtrans, Leaf{r3, x}, r1, v)(a1),
        a1 => a2 => {==}
      )
    case Con{False{}, +r1} Nil{} Con{True{}, +r3}:
      Trie.keeps_trans.node(
        ~V,
        ~r,
        ~rtrans,
        None{},
        Leaf{r1, v},
        Tip{},
        Some{w},
        Tip{},
        Tip{},
        None{},
        Tip{},
        Leaf{r3, x},
        a1 => a2 => Trie.keeps_of_all.leaf(~V, ~r, ~rn, ~rtrans, Tip{}, r1, v)(a1),
        a1 => a2 => {==}
      )
    case Con{False{}, +r1} Con{False{}, +r2} Nil{}:
      Trie.keeps_trans.node(
        ~V,
        ~r,
        ~rtrans,
        None{},
        Leaf{r1, v},
        Tip{},
        None{},
        Leaf{r2, w},
        Tip{},
        Some{x},
        Tip{},
        Tip{},
        Trie.all_of_keeps.fork(~V, ~r, ~rtrans, r1, v, r2, w),
        a1 => a2 => {==}
      )
    case Con{False{}, +r1} Con{False{}, +r2} Con{False{}, +r3}:
      Trie.keeps_trans.node(
        ~V,
        ~r,
        ~rtrans,
        None{},
        Leaf{r1, v},
        Tip{},
        None{},
        Leaf{r2, w},
        Tip{},
        None{},
        Leaf{r3, x},
        Tip{},
        Trie.keeps_trans.fork(~V, ~r, ~rn, ~rtrans, r1, v, r2, w, r3, x),
        a1 => a2 => {==}
      )
    case Con{False{}, +r1} Con{False{}, +r2} Con{True{}, +r3}:
      Trie.keeps_trans.node(
        ~V,
        ~r,
        ~rtrans,
        None{},
        Leaf{r1, v},
        Tip{},
        None{},
        Leaf{r2, w},
        Tip{},
        None{},
        Tip{},
        Leaf{r3, x},
        Trie.all_of_keeps.fork(~V, ~r, ~rtrans, r1, v, r2, w),
        a1 => a2 => {==}
      )
    case Con{False{}, +r1} Con{True{}, +r2} Nil{}:
      Trie.keeps_trans.node(
        ~V,
        ~r,
        ~rtrans,
        None{},
        Leaf{r1, v},
        Tip{},
        None{},
        Tip{},
        Leaf{r2, w},
        Some{x},
        Tip{},
        Tip{},
        a1 => a2 => Trie.keeps_of_all.leaf(~V, ~r, ~rn, ~rtrans, Tip{}, r1, v)(a1),
        a1 => a2 => {==}
      )
    case Con{False{}, +r1} Con{True{}, +r2} Con{False{}, +r3}:
      Trie.keeps_trans.node(
        ~V,
        ~r,
        ~rtrans,
        None{},
        Leaf{r1, v},
        Tip{},
        None{},
        Tip{},
        Leaf{r2, w},
        None{},
        Leaf{r3, x},
        Tip{},
        a1 => a2 => Trie.keeps_of_all.leaf(~V, ~r, ~rn, ~rtrans, Leaf{r3, x}, r1, v)(a1),
        a1 => a2 => {==}
      )
    case Con{False{}, +r1} Con{True{}, +r2} Con{True{}, +r3}:
      Trie.keeps_trans.node(
        ~V,
        ~r,
        ~rtrans,
        None{},
        Leaf{r1, v},
        Tip{},
        None{},
        Tip{},
        Leaf{r2, w},
        None{},
        Tip{},
        Leaf{r3, x},
        a1 => a2 => Trie.keeps_of_all.leaf(~V, ~r, ~rn, ~rtrans, Tip{}, r1, v)(a1),
        a1 => a2 => {==}
      )
    case Con{True{}, +r1} Nil{} Nil{}:
      Trie.keeps_trans.node(
        ~V,
        ~r,
        ~rtrans,
        None{},
        Tip{},
        Leaf{r1, v},
        Some{w},
        Tip{},
        Tip{},
        Some{x},
        Tip{},
        Tip{},
        a1 => a2 => {==},
        a1 => a2 => Trie.keeps_of_all.leaf(~V, ~r, ~rn, ~rtrans, Tip{}, r1, v)(a1)
      )
    case Con{True{}, +r1} Nil{} Con{False{}, +r3}:
      Trie.keeps_trans.node(
        ~V,
        ~r,
        ~rtrans,
        None{},
        Tip{},
        Leaf{r1, v},
        Some{w},
        Tip{},
        Tip{},
        None{},
        Leaf{r3, x},
        Tip{},
        a1 => a2 => {==},
        a1 => a2 => Trie.keeps_of_all.leaf(~V, ~r, ~rn, ~rtrans, Tip{}, r1, v)(a1)
      )
    case Con{True{}, +r1} Nil{} Con{True{}, +r3}:
      Trie.keeps_trans.node(
        ~V,
        ~r,
        ~rtrans,
        None{},
        Tip{},
        Leaf{r1, v},
        Some{w},
        Tip{},
        Tip{},
        None{},
        Tip{},
        Leaf{r3, x},
        a1 => a2 => {==},
        a1 => a2 => Trie.keeps_of_all.leaf(~V, ~r, ~rn, ~rtrans, Leaf{r3, x}, r1, v)(a1)
      )
    case Con{True{}, +r1} Con{False{}, +r2} Nil{}:
      Trie.keeps_trans.node(
        ~V,
        ~r,
        ~rtrans,
        None{},
        Tip{},
        Leaf{r1, v},
        None{},
        Leaf{r2, w},
        Tip{},
        Some{x},
        Tip{},
        Tip{},
        a1 => a2 => {==},
        a1 => a2 => Trie.keeps_of_all.leaf(~V, ~r, ~rn, ~rtrans, Tip{}, r1, v)(a1)
      )
    case Con{True{}, +r1} Con{False{}, +r2} Con{False{}, +r3}:
      Trie.keeps_trans.node(
        ~V,
        ~r,
        ~rtrans,
        None{},
        Tip{},
        Leaf{r1, v},
        None{},
        Leaf{r2, w},
        Tip{},
        None{},
        Leaf{r3, x},
        Tip{},
        a1 => a2 => {==},
        a1 => a2 => Trie.keeps_of_all.leaf(~V, ~r, ~rn, ~rtrans, Tip{}, r1, v)(a1)
      )
    case Con{True{}, +r1} Con{False{}, +r2} Con{True{}, +r3}:
      Trie.keeps_trans.node(
        ~V,
        ~r,
        ~rtrans,
        None{},
        Tip{},
        Leaf{r1, v},
        None{},
        Leaf{r2, w},
        Tip{},
        None{},
        Tip{},
        Leaf{r3, x},
        a1 => a2 => {==},
        a1 => a2 => Trie.keeps_of_all.leaf(~V, ~r, ~rn, ~rtrans, Leaf{r3, x}, r1, v)(a1)
      )
    case Con{True{}, +r1} Con{True{}, +r2} Nil{}:
      Trie.keeps_trans.node(
        ~V,
        ~r,
        ~rtrans,
        None{},
        Tip{},
        Leaf{r1, v},
        None{},
        Tip{},
        Leaf{r2, w},
        Some{x},
        Tip{},
        Tip{},
        a1 => a2 => {==},
        Trie.all_of_keeps.fork(~V, ~r, ~rtrans, r1, v, r2, w)
      )
    case Con{True{}, +r1} Con{True{}, +r2} Con{False{}, +r3}:
      Trie.keeps_trans.node(
        ~V,
        ~r,
        ~rtrans,
        None{},
        Tip{},
        Leaf{r1, v},
        None{},
        Tip{},
        Leaf{r2, w},
        None{},
        Leaf{r3, x},
        Tip{},
        a1 => a2 => {==},
        Trie.all_of_keeps.fork(~V, ~r, ~rtrans, r1, v, r2, w)
      )
    case Con{True{}, +r1} Con{True{}, +r2} Con{True{}, +r3}:
      Trie.keeps_trans.node(
        ~V,
        ~r,
        ~rtrans,
        None{},
        Tip{},
        Leaf{r1, v},
        None{},
        Tip{},
        Leaf{r2, w},
        None{},
        Tip{},
        Leaf{r3, x},
        a1 => a2 => {==},
        Trie.keeps_trans.fork(~V, ~r, ~rn, ~rtrans, r1, v, r2, w, r3, x)
      )

# Trie.keeps_trans for two entries and a trie
def Trie.keeps_trans.pair(
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
  s3: Trie<V>,
  k1: List<&2, Bool>,
  +v: V,
  k2: List<&2, Bool>,
  +w: V
) -> {
  Trie.keeps(~V, ~r, Leaf{k1, v}, Leaf{k2, w}) == True{}: Bool
} -> {
  Trie.keeps(~V, ~r, Leaf{k2, w}, s3) == True{}: Bool
} -> {Trie.keeps(~V, ~r, Leaf{k1, v}, s3) == True{}: Bool}:
  match s3 k1 k2:
    case Tip{} r1 r2:
      Trie.all_of_keeps.fork(~V, ~r, ~rtrans, r1, v, r2, w)
    case Leaf{k3, x} r1 r2:
      Trie.keeps_trans.fork(~V, ~r, ~rn, ~rtrans, r1, v, r2, w, k3, x)
    case Bin{h3, +z3, +o3} Nil{} Nil{}:
      Trie.keeps_trans.node(
        ~V,
        ~r,
        ~rtrans,
        Some{v},
        Tip{},
        Tip{},
        Some{w},
        Tip{},
        Tip{},
        h3,
        z3,
        o3,
        a1 => a2 => {==},
        a1 => a2 => {==}
      )
    case Bin{+h3, +z3, +o3} Nil{} Con{False{}, r2}:
      Trie.keeps_trans.node(
        ~V,
        ~r,
        ~rtrans,
        Some{v},
        Tip{},
        Tip{},
        None{},
        Leaf{r2, w},
        Tip{},
        h3,
        z3,
        o3,
        a1 => a2 => {==},
        a1 => a2 => {==}
      )
    case Bin{+h3, +z3, +o3} Nil{} Con{True{}, +r2}:
      Trie.keeps_trans.node(
        ~V,
        ~r,
        ~rtrans,
        Some{v},
        Tip{},
        Tip{},
        None{},
        Tip{},
        Leaf{r2, w},
        h3,
        z3,
        o3,
        a1 => a2 => {==},
        a1 => a2 => {==}
      )
    case Bin{+h3, +z3, +o3} Con{False{}, +r1} Nil{}:
      Trie.keeps_trans.node(
        ~V,
        ~r,
        ~rtrans,
        None{},
        Leaf{r1, v},
        Tip{},
        Some{w},
        Tip{},
        Tip{},
        h3,
        z3,
        o3,
        a1 => a2 => Trie.keeps_of_all.leaf(~V, ~r, ~rn, ~rtrans, z3, r1, v)(a1),
        a1 => a2 => {==}
      )
    case Bin{+h3, +z3, +o3} Con{False{}, +r1} Con{False{}, +r2}:
      Trie.keeps_trans.node(
        ~V,
        ~r,
        ~rtrans,
        None{},
        Leaf{r1, v},
        Tip{},
        None{},
        Leaf{r2, w},
        Tip{},
        h3,
        z3,
        o3,
        Trie.keeps_trans.pair(~V, ~r, ~rn, ~rtrans, z3, r1, v, r2, w),
        a1 => a2 => {==}
      )
    case Bin{+h3, +z3, +o3} Con{False{}, +r1} Con{True{}, +r2}:
      Trie.keeps_trans.node(
        ~V,
        ~r,
        ~rtrans,
        None{},
        Leaf{r1, v},
        Tip{},
        None{},
        Tip{},
        Leaf{r2, w},
        h3,
        z3,
        o3,
        a1 => a2 => Trie.keeps_of_all.leaf(~V, ~r, ~rn, ~rtrans, z3, r1, v)(a1),
        a1 => a2 => {==}
      )
    case Bin{+h3, +z3, +o3} Con{True{}, +r1} Nil{}:
      Trie.keeps_trans.node(
        ~V,
        ~r,
        ~rtrans,
        None{},
        Tip{},
        Leaf{r1, v},
        Some{w},
        Tip{},
        Tip{},
        h3,
        z3,
        o3,
        a1 => a2 => {==},
        a1 => a2 => Trie.keeps_of_all.leaf(~V, ~r, ~rn, ~rtrans, o3, r1, v)(a1)
      )
    case Bin{+h3, +z3, +o3} Con{True{}, +r1} Con{False{}, +r2}:
      Trie.keeps_trans.node(
        ~V,
        ~r,
        ~rtrans,
        None{},
        Tip{},
        Leaf{r1, v},
        None{},
        Leaf{r2, w},
        Tip{},
        h3,
        z3,
        o3,
        a1 => a2 => {==},
        a1 => a2 => Trie.keeps_of_all.leaf(~V, ~r, ~rn, ~rtrans, o3, r1, v)(a1)
      )
    case Bin{+h3, +z3, +o3} Con{True{}, +r1} Con{True{}, +r2}:
      Trie.keeps_trans.node(
        ~V,
        ~r,
        ~rtrans,
        None{},
        Tip{},
        Leaf{r1, v},
        None{},
        Tip{},
        Leaf{r2, w},
        h3,
        z3,
        o3,
        a1 => a2 => {==},
        Trie.keeps_trans.pair(~V, ~r, ~rn, ~rtrans, o3, r1, v, r2, w)
      )

# Trie.keeps_trans for an entry and two tries
def Trie.keeps_trans.leaf(
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
  s2: Trie<V>,
  s3: Trie<V>,
  k1: List<&2, Bool>,
  +v: V
) -> {
  Trie.keeps(~V, ~r, Leaf{k1, v}, s2) == True{}: Bool
} -> {
  Trie.keeps(~V, ~r, s2, s3) == True{}: Bool
} -> {Trie.keeps(~V, ~r, Leaf{k1, v}, s3) == True{}: Bool}:
  match s2 s3 k1:
    case Tip{} y r1:
      g1 => g2 => Trie.keeps_of_all.leaf(~V, ~r, ~rn, ~rtrans, y, r1, v)(g1)
    case Leaf{k2, w} y r1:
      Trie.keeps_trans.pair(~V, ~r, ~rn, ~rtrans, y, r1, v, k2, w)
    case Bin{h2, z2, o2} Tip{} r1:
      Trie.all_of_keeps.leaf(~V, ~r, ~rtrans, Bin{h2, z2, o2}, r1, v)
    case Bin{+h2, +z2, +o2} Leaf{+k3, +x} Nil{}:
      g1 => g2 =>
        %Trie.all2_node.leaf(
          ~V,
          ~V,
          ~r,
          ~(t => Trie.all(~V, ~(m => r(m, None{})), t)),
          [],
          v,
          k3,
          x
        ): {_ == True{}: Bool}
        Trie.keeps_trans.node(
          ~V,
          ~r,
          ~rtrans,
          Some{v},
          Tip{},
          Tip{},
          h2,
          z2,
          o2,
          Trie.at.here(V, k3, x),
          Trie.at.zero(V, k3, x),
          Trie.at.one(V, k3, x),
          a1 => a2 => {==},
          a1 => a2 => {==}
        )(g1)(g2)
    case Bin{+h2, +z2, +o2} Leaf{+k3, +x} Con{False{}, +r1}:
      g1 => g2 =>
        %Trie.all2_node.leaf(
          ~V,
          ~V,
          ~r,
          ~(t => Trie.all(~V, ~(m => r(m, None{})), t)),
          False{} <> r1,
          v,
          k3,
          x
        ): {_ == True{}: Bool}
        Trie.keeps_trans.node(
          ~V,
          ~r,
          ~rtrans,
          None{},
          Leaf{r1, v},
          Tip{},
          h2,
          z2,
          o2,
          Trie.at.here(V, k3, x),
          Trie.at.zero(V, k3, x),
          Trie.at.one(V, k3, x),
          Trie.keeps_trans.leaf(~V, ~r, ~rn, ~rtrans, z2, Trie.at.zero(V, k3, x), r1, v),
          a1 => a2 => {==}
        )(g1)(g2)
    case Bin{+h2, +z2, +o2} Leaf{+k3, +x} Con{True{}, +r1}:
      g1 => g2 =>
        %Trie.all2_node.leaf(
          ~V,
          ~V,
          ~r,
          ~(t => Trie.all(~V, ~(m => r(m, None{})), t)),
          True{} <> r1,
          v,
          k3,
          x
        ): {_ == True{}: Bool}
        Trie.keeps_trans.node(
          ~V,
          ~r,
          ~rtrans,
          None{},
          Tip{},
          Leaf{r1, v},
          h2,
          z2,
          o2,
          Trie.at.here(V, k3, x),
          Trie.at.zero(V, k3, x),
          Trie.at.one(V, k3, x),
          a1 => a2 => {==},
          Trie.keeps_trans.leaf(~V, ~r, ~rn, ~rtrans, o2, Trie.at.one(V, k3, x), r1, v)
        )(g1)(g2)
    case Bin{+h2, +z2, +o2} Bin{h3, +z3, +o3} Nil{}:
      Trie.keeps_trans.node(
        ~V,
        ~r,
        ~rtrans,
        Some{v},
        Tip{},
        Tip{},
        h2,
        z2,
        o2,
        h3,
        z3,
        o3,
        a1 => a2 => {==},
        a1 => a2 => {==}
      )
    case Bin{+h2, +z2, +o2} Bin{+h3, +z3, +o3} Con{False{}, +r1}:
      Trie.keeps_trans.node(
        ~V,
        ~r,
        ~rtrans,
        None{},
        Leaf{r1, v},
        Tip{},
        h2,
        z2,
        o2,
        h3,
        z3,
        o3,
        Trie.keeps_trans.leaf(~V, ~r, ~rn, ~rtrans, z2, z3, r1, v),
        a1 => a2 => {==}
      )
    case Bin{+h2, +z2, +o2} Bin{+h3, +z3, +o3} Con{True{}, +r1}:
      Trie.keeps_trans.node(
        ~V,
        ~r,
        ~rtrans,
        None{},
        Tip{},
        Leaf{r1, v},
        h2,
        z2,
        o2,
        h3,
        z3,
        o3,
        a1 => a2 => {==},
        Trie.keeps_trans.leaf(~V, ~r, ~rn, ~rtrans, o2, o3, r1, v)
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
    case Leaf{k, v} y w:
      Trie.keeps_trans.leaf(~ty, ~r, ~rn, ~rtrans, y, w, k, v)
    case Bin{h1, z1, o1} Tip{} w:
      g1 => g2 => Trie.keeps_of_all(~ty, ~r, ~rn, ~rtrans, Bin{h1, z1, o1}, w)(g1)
    case Bin{h1, z1, o1} Leaf{k2, w} Tip{}:
      g1 => g2 => Trie.all_of_keeps(~ty, ~r, ~rn, ~rtrans, Bin{h1, z1, o1}, Leaf{k2, w})(g1)(g2)
    case Bin{h1, z1, o1} Bin{h2, z2, o2} Tip{}:
      g1 => g2 => Trie.all_of_keeps(~ty, ~r, ~rn, ~rtrans, Bin{h1, z1, o1}, Bin{h2, z2, o2})(g1)(g2)
    case Bin{+h1, +z1, +o1} Leaf{+k2, +w} Leaf{+k3, +x}:
      g1 => g2 =>
        Trie.keeps_trans.node(
          ~ty,
          ~r,
          ~rtrans,
          h1,
          z1,
          o1,
          Trie.at.here(ty, k2, w),
          Trie.at.zero(ty, k2, w),
          Trie.at.one(ty, k2, w),
          Trie.at.here(ty, k3, x),
          Trie.at.zero(ty, k3, x),
          Trie.at.one(ty, k3, x),
          Trie.keeps_trans(
            ~ty,
            ~r,
            ~rn,
            ~rtrans,
            z1,
            Trie.at.zero(ty, k2, w),
            Trie.at.zero(ty, k3, x)
          ),
          Trie.keeps_trans(
            ~ty,
            ~r,
            ~rn,
            ~rtrans,
            o1,
            Trie.at.one(ty, k2, w),
            Trie.at.one(ty, k3, x)
          )
        )(
          g1
        )(
          Equal.trans(
            Bool,
            Bool.and(
              r(Trie.at.here(ty, k2, w), Trie.at.here(ty, k3, x)),
              Bool.and(
                Trie.keeps(~ty, ~r, Trie.at.zero(ty, k2, w), Trie.at.zero(ty, k3, x)),
                Trie.keeps(~ty, ~r, Trie.at.one(ty, k2, w), Trie.at.one(ty, k3, x))
              )
            ),
            Trie.keeps(~ty, ~r, Leaf{k2, w}, Leaf{k3, x}),
            True{},
            Trie.all2_node.leaf(
              ~ty,
              ~ty,
              ~r,
              ~(t => Trie.all(~ty, ~(m => r(m, None{})), t)),
              k2,
              w,
              k3,
              x
            ),
            g2
          )
        )
    case Bin{+h1, +z1, +o1} Leaf{+k2, +w} Bin{h3, +z3, +o3}:
      g1 => g2 =>
        Trie.keeps_trans.node(
          ~ty,
          ~r,
          ~rtrans,
          h1,
          z1,
          o1,
          Trie.at.here(ty, k2, w),
          Trie.at.zero(ty, k2, w),
          Trie.at.one(ty, k2, w),
          h3,
          z3,
          o3,
          Trie.keeps_trans(~ty, ~r, ~rn, ~rtrans, z1, Trie.at.zero(ty, k2, w), z3),
          Trie.keeps_trans(~ty, ~r, ~rn, ~rtrans, o1, Trie.at.one(ty, k2, w), o3)
        )(
          g1
        )(
          Equal.trans(
            Bool,
            Bool.and(
              r(Trie.at.here(ty, k2, w), h3),
              Bool.and(
                Trie.keeps(~ty, ~r, Trie.at.zero(ty, k2, w), z3),
                Trie.keeps(~ty, ~r, Trie.at.one(ty, k2, w), o3)
              )
            ),
            Trie.keeps(~ty, ~r, Leaf{k2, w}, Bin{h3, z3, o3}),
            True{},
            Trie.all2_node.bin(
              ~ty,
              ~ty,
              ~r,
              ~(t => Trie.all(~ty, ~(m => r(m, None{})), t)),
              k2,
              w,
              h3,
              z3,
              o3
            ),
            g2
          )
        )
    case Bin{+h1, +z1, +o1} Bin{+h2, +z2, +o2} Leaf{+k3, +x}:
      Trie.keeps_trans.node(
        ~ty,
        ~r,
        ~rtrans,
        h1,
        z1,
        o1,
        h2,
        z2,
        o2,
        Trie.at.here(ty, k3, x),
        Trie.at.zero(ty, k3, x),
        Trie.at.one(ty, k3, x),
        Trie.keeps_trans(~ty, ~r, ~rn, ~rtrans, z1, z2, Trie.at.zero(ty, k3, x)),
        Trie.keeps_trans(~ty, ~r, ~rn, ~rtrans, o1, o2, Trie.at.one(ty, k3, x))
      )
    case Bin{+h1, +z1, +o1} Bin{+h2, +z2, +o2} Bin{h3, +z3, +o3}:
      Trie.keeps_trans.node(
        ~ty,
        ~r,
        ~rtrans,
        h1,
        z1,
        o1,
        h2,
        z2,
        o2,
        h3,
        z3,
        o3,
        Trie.keeps_trans(~ty, ~r, ~rn, ~rtrans, z1, z2, z3),
        Trie.keeps_trans(~ty, ~r, ~rn, ~rtrans, o1, o2, o3)
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

# Trie.keeps_size at a node, from its parts
def Trie.keeps_size.node(
  ~V: Data,
  ~r: Maybe<&2, V> -> Maybe<&2, V> -> Bool,
  ~rs: @x: Maybe<
    &2,
    V> -> @y: Maybe<
    &2,
    V> -> {
    r(x, y) == True{}: Bool
  } -> {Maybe.is_some(&2, V, x) == True{}: Bool} -> {Maybe.is_some(&2, V, y) == True{}: Bool},
  h1: Maybe<&2, V>,
  h2: Maybe<&2, V>,
  +z1: Trie<V>,
  +o1: Trie<V>,
  +z2: Trie<V>,
  +o2: Trie<V>,
  ihz: {
    Trie.keeps(~V, ~r, z1, z2) == True{}: Bool
  } -> {Nat.is_le(Trie.size(V, z1), Trie.size(V, z2)) == True{}: Bool},
  iho: {
    Trie.keeps(~V, ~r, o1, o2) == True{}: Bool
  } -> {Nat.is_le(Trie.size(V, o1), Trie.size(V, o2)) == True{}: Bool}
) -> {
  Bool.and(
    r(h1, h2),
    Bool.and(Trie.keeps(~V, ~r, z1, z2), Trie.keeps(~V, ~r, o1, o2))
  )
    == True{}: Bool
} -> {Nat.is_le(Trie.size(V, Bin{h1, z1, o1}), Trie.size(V, Bin{h2, z2, o2})) == True{}: Bool}:
  match h1 h2:
    case None{} None{}:
      +e =>
        +rest = Shared.Bool.and_true_right(
          r(None{}, None{}),
          Bool.and(Trie.keeps(~V, ~r, z1, z2), Trie.keeps(~V, ~r, o1, o2))
        )(e)
        Shared.Nat.add_le(
          Trie.size(V, z1),
          Trie.size(V, z2),
          Trie.size(V, o1),
          Trie.size(V, o2)
        )(
          ihz(
            Shared.Bool.and_true_left(Trie.keeps(~V, ~r, z1, z2), Trie.keeps(~V, ~r, o1, o2))(rest)
          )
        )(
          iho(
            Shared.Bool.and_true_right(Trie.keeps(~V, ~r, z1, z2), Trie.keeps(~V, ~r, o1, o2))(rest)
          )
        )
    case None{} Some{c2}:
      +e =>
        +rest = Shared.Bool.and_true_right(
          r(None{}, Some{c2}),
          Bool.and(Trie.keeps(~V, ~r, z1, z2), Trie.keeps(~V, ~r, o1, o2))
        )(e)
        Shared.Nat.le_succ(
          Nat.add(Trie.size(V, z1), Trie.size(V, o1)),
          Nat.add(Trie.size(V, z2), Trie.size(V, o2))
        )(
          Shared.Nat.add_le(
            Trie.size(V, z1),
            Trie.size(V, z2),
            Trie.size(V, o1),
            Trie.size(V, o2)
          )(
            ihz(
              Shared.Bool.and_true_left(
                Trie.keeps(~V, ~r, z1, z2),
                Trie.keeps(~V, ~r, o1, o2)
              )(rest)
            )
          )(
            iho(
              Shared.Bool.and_true_right(
                Trie.keeps(~V, ~r, z1, z2),
                Trie.keeps(~V, ~r, o1, o2)
              )(rest)
            )
          )
        )
    case Some{+c1} Some{c2}:
      +e =>
        +rest = Shared.Bool.and_true_right(
          r(Some{c1}, Some{c2}),
          Bool.and(Trie.keeps(~V, ~r, z1, z2), Trie.keeps(~V, ~r, o1, o2))
        )(e)
        Shared.Nat.add_le(
          Trie.size(V, z1),
          Trie.size(V, z2),
          Trie.size(V, o1),
          Trie.size(V, o2)
        )(
          ihz(
            Shared.Bool.and_true_left(Trie.keeps(~V, ~r, z1, z2), Trie.keeps(~V, ~r, o1, o2))(rest)
          )
        )(
          iho(
            Shared.Bool.and_true_right(Trie.keeps(~V, ~r, z1, z2), Trie.keeps(~V, ~r, o1, o2))(rest)
          )
        )
    case Some{+c1} None{}:
      e => Empty.absurd(
        {
          Nat.is_le(
            Trie.size(V, Bin{Some{c1}, z1, o1}),
            Trie.size(V, Bin{None{}, z2, o2})
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
              Bool.and(Trie.keeps(~V, ~r, z1, z2), Trie.keeps(~V, ~r, o1, o2))
            )(e)
          )({==})
        )
      )

# the node of an entry has one entry
def Trie.size_node(
  -V: Data,
  k: List<&2, Bool>,
  -v: V
) -> {
  Trie.size(V, Bin{Trie.at.here(V, k, v), Trie.at.zero(V, k, v), Trie.at.one(V, k, v)}) == 1n: Nat
}:
  match k:
    case Nil{}:
      {==}
    case Con{False{}, q}:
      {==}
    case Con{True{}, q}:
      {==}

# a trie that keeps an entry holds one entry or more
def Trie.keeps_size.leaf(
  ~V: Data,
  ~r: Maybe<&2, V> -> Maybe<&2, V> -> Bool,
  ~rs: @x: Maybe<
    &2,
    V> -> @y: Maybe<
    &2,
    V> -> {
    r(x, y) == True{}: Bool
  } -> {Maybe.is_some(&2, V, x) == True{}: Bool} -> {Maybe.is_some(&2, V, y) == True{}: Bool},
  y: Trie<V>,
  k1: List<&2, Bool>,
  +v: V
) -> {
  Trie.keeps(~V, ~r, Leaf{k1, v}, y) == True{}: Bool
} -> {Nat.is_le(1n, Trie.size(V, y)) == True{}: Bool}:
  match y k1:
    case Tip{} r1:
      e => Empty.absurd(
        {Nat.is_le(1n, 0n) == True{}: Bool},
        Shared.Bool.false_ne_true(rs(Some{v})(None{})(e)({==}))
      )
    case Leaf{p, w} r1:
      e => {==}
    case Bin{h, +z, +o} Nil{}:
      Trie.keeps_size.node(
        ~V,
        ~r,
        ~rs,
        Some{v},
        h,
        Tip{},
        Tip{},
        z,
        o,
        e2 => Shared.Nat.le_zero(Trie.size(V, z)),
        e2 => Shared.Nat.le_zero(Trie.size(V, o))
      )
    case Bin{h, +z, +o} Con{False{}, +r1}:
      Trie.keeps_size.node(
        ~V,
        ~r,
        ~rs,
        None{},
        h,
        Leaf{r1, v},
        Tip{},
        z,
        o,
        Trie.keeps_size.leaf(~V, ~r, ~rs, z, r1, v),
        e2 => Shared.Nat.le_zero(Trie.size(V, o))
      )
    case Bin{h, +z, +o} Con{True{}, +r1}:
      Trie.keeps_size.node(
        ~V,
        ~r,
        ~rs,
        None{},
        h,
        Tip{},
        Leaf{r1, v},
        z,
        o,
        e2 => Shared.Nat.le_zero(Trie.size(V, z)),
        Trie.keeps_size.leaf(~V, ~r, ~rs, o, r1, v)
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
    case Bin{h, +z, +o} Tip{}:
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
    case Leaf{k, v} y:
      Trie.keeps_size.leaf(~ty, ~r, ~rs, y, k, v)
    case Bin{h, +z, +o} Leaf{+p, +w}:
      e =>
        %Trie.size_node(ty, p, w): {Nat.is_le(Trie.size(ty, Bin{h, z, o}), _) == True{}: Bool}
        Trie.keeps_size.node(
          ~ty,
          ~r,
          ~rs,
          h,
          Trie.at.here(ty, p, w),
          z,
          o,
          Trie.at.zero(ty, p, w),
          Trie.at.one(ty, p, w),
          Trie.keeps_size(~ty, ~r, ~rs, z, Trie.at.zero(ty, p, w)),
          Trie.keeps_size(~ty, ~r, ~rs, o, Trie.at.one(ty, p, w))
        )(e)
    case Bin{h1, +z1, +o1} Bin{h2, +z2, +o2}:
      Trie.keeps_size.node(
        ~ty,
        ~r,
        ~rs,
        h1,
        h2,
        z1,
        o1,
        z2,
        o2,
        Trie.keeps_size(~ty, ~r, ~rs, z1, z2),
        Trie.keeps_size(~ty, ~r, ~rs, o1, o2)
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

# any two tries pass the check that is True of all
def Trie.all2_true.fork(
  ~V: Data,
  k: List<&2, Bool>,
  +v: V,
  p: List<&2, Bool>,
  +w: V
) -> {Trie.all2.fork(~V, ~V, ~(x => y => True{}), ~(t => True{}), k, v, p, w) == True{}: Bool}:
  match k p:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{False{}, q}:
      {==}
    case Nil{} Con{True{}, +q}:
      {==}
    case Con{False{}, +r} Nil{}:
      {==}
    case Con{False{}, +r} Con{False{}, +q}:
      Shared.Bool.and_both(
        Trie.all2.fork(~V, ~V, ~(x => y => True{}), ~(t => True{}), r, v, q, w),
        True{}
      )(Trie.all2_true.fork(~V, r, v, q, w))({==})
    case Con{False{}, +r} Con{True{}, +q}:
      {==}
    case Con{True{}, +r} Nil{}:
      {==}
    case Con{True{}, +r} Con{False{}, +q}:
      {==}
    case Con{True{}, +r} Con{True{}, +q}:
      Shared.Bool.and_both(
        True{},
        Trie.all2.fork(~V, ~V, ~(x => y => True{}), ~(t => True{}), r, v, q, w)
      )({==})(Trie.all2_true.fork(~V, r, v, q, w))

# Trie.all2_true for an entry and a trie
def Trie.all2_true.leaf(
  ~V: Data,
  y: Trie<V>,
  k: List<&2, Bool>,
  +v: V
) -> {Trie.all2.leaf(~V, ~V, ~(x => y => True{}), ~(t => True{}), y, k, v) == True{}: Bool}:
  match y k:
    case Tip{} r:
      {==}
    case Leaf{p, w} r:
      Trie.all2_true.fork(~V, r, v, p, w)
    case Bin{h, z, o} Nil{}:
      {==}
    case Bin{h, +z, o} Con{False{}, +r}:
      Shared.Bool.and_both(
        Trie.all2.leaf(~V, ~V, ~(x => y => True{}), ~(t => True{}), z, r, v),
        True{}
      )(Trie.all2_true.leaf(~V, z, r, v))({==})
    case Bin{h, z, +o} Con{True{}, +r}:
      Shared.Bool.and_both(
        True{},
        Trie.all2.leaf(~V, ~V, ~(x => y => True{}), ~(t => True{}), o, r, v)
      )({==})(Trie.all2_true.leaf(~V, o, r, v))

# bend-lint: expect-begin bend-lint-rules/performance/missed_fork@hint -- a proof: it does not run
# Trie.all2_true for two tries
def Trie.all2_true(
  ~V: Data,
  a: Trie<V>,
  b: Trie<V>
) -> {Trie.all2(~V, ~V, ~(x => y => True{}), ~(t => True{}), a, b) == True{}: Bool}:
  match a b:
    case Tip{} y:
      {==}
    case Leaf{k, v} y:
      Trie.all2_true.leaf(~V, y, k, v)
    case Bin{h, z, o} Tip{}:
      {==}
    case Bin{h, +z, +o} Leaf{+p, +w}:
      Shared.Bool.and_both(
        Trie.all2(~V, ~V, ~(x => y => True{}), ~(t => True{}), z, Trie.at.zero(V, p, w)),
        Trie.all2(~V, ~V, ~(x => y => True{}), ~(t => True{}), o, Trie.at.one(V, p, w))
      )(Trie.all2_true(~V, z, Trie.at.zero(V, p, w)))(Trie.all2_true(~V, o, Trie.at.one(V, p, w)))
    case Bin{h1, +z1, +o1} Bin{h2, +z2, +o2}:
      Shared.Bool.and_both(
        Trie.all2(~V, ~V, ~(x => y => True{}), ~(t => True{}), z1, z2),
        Trie.all2(~V, ~V, ~(x => y => True{}), ~(t => True{}), o1, o2)
      )(Trie.all2_true(~V, z1, z2))(Trie.all2_true(~V, o1, o2))
# bend-lint: expect-end bend-lint-rules/performance/missed_fork@hint

# Trie.take_keeps, with binders to use again
def Trie.take_keeps.go(
  ~V: Data,
  ~r: Maybe<&2, V> -> Maybe<&2, V> -> Bool,
  ~left: Trie<V> -> Bool,
  ~rn: @y: Maybe<&2, V> -> {r(None{}, y) == True{}: Bool},
  ~rrefl: @m: Maybe<&2, V> -> {r(m, m) == True{}: Bool},
  +a: Trie<V>,
  +b: Trie<V>
) -> {Trie.all2(~V, ~V, ~r, ~left, a, Trie.take(~V, a, b)) == True{}: Bool}:
  Trie.all2_join(
    ~V,
    ~(x => y => x),
    ~(x => y => True{}),
    ~(t => True{}),
    ~r,
    ~left,
    ~(x => y => e => Trie.take_keeps.here(~V, ~r, ~rn, ~rrefl, x, y)),
    ~rrefl,
    a,
    b
  )(Trie.all2_true(~V, a, b))

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
  Trie.take_keeps.go(~V, ~r, ~left, ~rn, ~rrefl, a, b)

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof: it does not run
# Trie.take_union at a node, from its parts
def Trie.take_union.node(
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
  +h1: Maybe<&2, V>,
  +z1: Trie<V>,
  +o1: Trie<V>,
  +h2: Maybe<&2, V>,
  +z2: Trie<V>,
  +o2: Trie<V>,
  ihz: {
    Trie.all2(~V, ~V, ~q, ~lq, z1, z2) == True{}: Bool
  } -> {Trie.take(~V, z1, z2) == Trie.union(~V, ~join, z1, z2): Trie<V>},
  iho: {
    Trie.all2(~V, ~V, ~q, ~lq, o1, o2) == True{}: Bool
  } -> {Trie.take(~V, o1, o2) == Trie.union(~V, ~join, o1, o2): Trie<V>}
) -> {
  Bool.and(
    q(h1, h2),
    Bool.and(Trie.all2(~V, ~V, ~q, ~lq, z1, z2), Trie.all2(~V, ~V, ~q, ~lq, o1, o2))
  )
    == True{}: Bool
} -> {
  Bin{
    Shared.Maybe.join(~V, ~(c => d => c), h1, h2),
    Trie.take(~V, z1, z2),
    Trie.take(~V, o1, o2)
  }
    == Bin{
      Shared.Maybe.join(~V, ~join, h1, h2),
      Trie.union(~V, ~join, z1, z2),
      Trie.union(~V, ~join, o1, o2)
    }: Trie<V>
}:
  +e =>
    +rest = Shared.Bool.and_true_right(
      q(h1, h2),
      Bool.and(Trie.all2(~V, ~V, ~q, ~lq, z1, z2), Trie.all2(~V, ~V, ~q, ~lq, o1, o2))
    )(e)
    %ihz(
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
    %iho(
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
    %step(
      h1
    )(
      h2
    )(
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
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof: it does not run
# Trie.take_union for two entries
def Trie.take_union.fork(
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
  k1: List<&2, Bool>,
  +v: V,
  p: List<&2, Bool>,
  +w: V
) -> {
  Trie.all2.fork(~V, ~V, ~q, ~lq, k1, v, p, w) == True{}: Bool
} -> {
  Trie.union.fork(
    ~V,
    ~(x => y => x),
    k1,
    v,
    p,
    w
  )
    == Trie.union.fork(~V, ~join, k1, v, p, w): Trie<V>
}:
  match k1 p:
    case Nil{} Nil{}:
      e => Equal.cong(
        V,
        Trie<V>,
        y => Leaf{[], y},
        v,
        join(v, w),
        Shared.Maybe.some_inj(
          V,
          v,
          join(v, w),
          step(
            Some{v}
          )(Some{w})(Shared.Bool.and_true_left(q(Some{v}, Some{w}), Bool.and(True{}, True{}))(e))
        )
      )
    case Nil{} Con{False{}, rp}:
      e => {==}
    case Nil{} Con{True{}, +rp}:
      e => {==}
    case Con{False{}, +r1} Nil{}:
      e => {==}
    case Con{False{}, +r1} Con{False{}, +rp}:
      e => Equal.cong(
        Trie<V>,
        Trie<V>,
        y => Trie.bin(V, None{}, y, Tip{}),
        Trie.union.fork(~V, ~(x => y => x), r1, v, rp, w),
        Trie.union.fork(~V, ~join, r1, v, rp, w),
        Trie.take_union.fork(
          ~V,
          ~join,
          ~q,
          ~lq,
          ~step,
          r1,
          v,
          rp,
          w
        )(
          Shared.Bool.and_true_left(
            Trie.all2.fork(~V, ~V, ~q, ~lq, r1, v, rp, w),
            True{}
          )(
            Shared.Bool.and_true_right(
              q(None{}, None{}),
              Bool.and(Trie.all2.fork(~V, ~V, ~q, ~lq, r1, v, rp, w), True{})
            )(e)
          )
        )
      )
    case Con{False{}, +r1} Con{True{}, +rp}:
      e => {==}
    case Con{True{}, +r1} Nil{}:
      e => {==}
    case Con{True{}, +r1} Con{False{}, +rp}:
      e => {==}
    case Con{True{}, +r1} Con{True{}, +rp}:
      e => Equal.cong(
        Trie<V>,
        Trie<V>,
        y => Trie.bin(V, None{}, Tip{}, y),
        Trie.union.fork(~V, ~(x => y => x), r1, v, rp, w),
        Trie.union.fork(~V, ~join, r1, v, rp, w),
        Trie.take_union.fork(
          ~V,
          ~join,
          ~q,
          ~lq,
          ~step,
          r1,
          v,
          rp,
          w
        )(
          Shared.Bool.and_true_right(
            True{},
            Trie.all2.fork(~V, ~V, ~q, ~lq, r1, v, rp, w)
          )(
            Shared.Bool.and_true_right(
              q(None{}, None{}),
              Bool.and(True{}, Trie.all2.fork(~V, ~V, ~q, ~lq, r1, v, rp, w))
            )(e)
          )
        )
      )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof: it does not run
# Trie.take_union for an entry and a trie
def Trie.take_union.leaf(
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
  y: Trie<V>,
  k1: List<&2, Bool>,
  +v: V
) -> {
  Trie.all2.leaf(~V, ~V, ~q, ~lq, y, k1, v) == True{}: Bool
} -> {
  Trie.union.leaf(~V, ~(x => y => x), y, k1, v) == Trie.union.leaf(~V, ~join, y, k1, v): Trie<V>
}:
  match y k1:
    case Tip{} r1:
      e => {==}
    case Leaf{p, w} r1:
      Trie.take_union.fork(~V, ~join, ~q, ~lq, ~step, r1, v, p, w)
    case Bin{+h, +z, +o} Nil{}:
      e => Equal.cong(
        Maybe<&2, V>,
        Trie<V>,
        m => Bin{m, z, o},
        Shared.Maybe.join(~V, ~(c => d => c), Some{v}, h),
        Shared.Maybe.join(~V, ~join, Some{v}, h),
        step(Some{v})(h)(Shared.Bool.and_true_left(q(Some{v}, h), Bool.and(True{}, True{}))(e))
      )
    case Bin{+h, +z, +o} Con{False{}, +r1}:
      e => Equal.cong(
        Trie<V>,
        Trie<V>,
        t => Bin{h, t, o},
        Trie.union.leaf(~V, ~(x => y => x), z, r1, v),
        Trie.union.leaf(~V, ~join, z, r1, v),
        Trie.take_union.leaf(
          ~V,
          ~join,
          ~q,
          ~lq,
          ~step,
          z,
          r1,
          v
        )(
          Shared.Bool.and_true_left(
            Trie.all2.leaf(~V, ~V, ~q, ~lq, z, r1, v),
            True{}
          )(
            Shared.Bool.and_true_right(
              q(None{}, h),
              Bool.and(Trie.all2.leaf(~V, ~V, ~q, ~lq, z, r1, v), True{})
            )(e)
          )
        )
      )
    case Bin{+h, +z, +o} Con{True{}, +r1}:
      e => Equal.cong(
        Trie<V>,
        Trie<V>,
        t => Bin{h, z, t},
        Trie.union.leaf(~V, ~(x => y => x), o, r1, v),
        Trie.union.leaf(~V, ~join, o, r1, v),
        Trie.take_union.leaf(
          ~V,
          ~join,
          ~q,
          ~lq,
          ~step,
          o,
          r1,
          v
        )(
          Shared.Bool.and_true_right(
            True{},
            Trie.all2.leaf(~V, ~V, ~q, ~lq, o, r1, v)
          )(
            Shared.Bool.and_true_right(
              q(None{}, h),
              Bool.and(True{}, Trie.all2.leaf(~V, ~V, ~q, ~lq, o, r1, v))
            )(e)
          )
        )
      )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# bend-lint: expect-begin bend-lint-rules/performance/missed_fork@hint -- a proof: it does not run
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
    case Leaf{k, v} y:
      Trie.take_union.leaf(~V, ~join, ~q, ~lq, ~step, y, k, v)
    case Bin{h, z, o} Tip{}:
      e => {==}
    case Bin{+h, +z, +o} Leaf{+p, +w}:
      Trie.take_union.node(
        ~V,
        ~join,
        ~q,
        ~lq,
        ~step,
        h,
        z,
        o,
        Trie.at.here(V, p, w),
        Trie.at.zero(V, p, w),
        Trie.at.one(V, p, w),
        Trie.take_union(~V, ~join, ~q, ~lq, ~step, z, Trie.at.zero(V, p, w)),
        Trie.take_union(~V, ~join, ~q, ~lq, ~step, o, Trie.at.one(V, p, w))
      )
    case Bin{+h1, +z1, +o1} Bin{h2, +z2, +o2}:
      Trie.take_union.node(
        ~V,
        ~join,
        ~q,
        ~lq,
        ~step,
        h1,
        z1,
        o1,
        h2,
        z2,
        o2,
        Trie.take_union(~V, ~join, ~q, ~lq, ~step, z1, z2),
        Trie.take_union(~V, ~join, ~q, ~lq, ~step, o1, o2)
      )
# bend-lint: expect-end bend-lint-rules/performance/missed_fork@hint

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof: it does not run
# Trie.take_keeps_right at a node, from its parts
def Trie.take_keeps_right.node(
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
  +h1: Maybe<&2, V>,
  +z1: Trie<V>,
  +o1: Trie<V>,
  +h2: Maybe<&2, V>,
  +z2: Trie<V>,
  +o2: Trie<V>,
  ihz: {
    Trie.all2(~V, ~V, ~q, ~lq, z1, z2) == True{}: Bool
  } -> {Trie.all2(~V, ~V, ~r, ~lr, z2, Trie.take(~V, z1, z2)) == True{}: Bool},
  iho: {
    Trie.all2(~V, ~V, ~q, ~lq, o1, o2) == True{}: Bool
  } -> {Trie.all2(~V, ~V, ~r, ~lr, o2, Trie.take(~V, o1, o2)) == True{}: Bool}
) -> {
  Bool.and(
    q(h1, h2),
    Bool.and(Trie.all2(~V, ~V, ~q, ~lq, z1, z2), Trie.all2(~V, ~V, ~q, ~lq, o1, o2))
  )
    == True{}: Bool
} -> {
  Bool.and(
    r(h2, Shared.Maybe.join(~V, ~(c => d => c), h1, h2)),
    Bool.and(
      Trie.all2(~V, ~V, ~r, ~lr, z2, Trie.take(~V, z1, z2)),
      Trie.all2(~V, ~V, ~r, ~lr, o2, Trie.take(~V, o1, o2))
    )
  )
    == True{}: Bool
}:
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
      step(
        h1
      )(
        h2
      )(
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
        ihz(
          Shared.Bool.and_true_left(
            Trie.all2(~V, ~V, ~q, ~lq, z1, z2),
            Trie.all2(~V, ~V, ~q, ~lq, o1, o2)
          )(rest)
        )
      )(
        iho(
          Shared.Bool.and_true_right(
            Trie.all2(~V, ~V, ~q, ~lq, z1, z2),
            Trie.all2(~V, ~V, ~q, ~lq, o1, o2)
          )(rest)
        )
      )
    )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# Trie.take_keeps_right for two entries
def Trie.take_keeps_right.fork(
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
  k1: List<&2, Bool>,
  +v: V,
  p: List<&2, Bool>,
  +w: V
) -> {
  Trie.all2.fork(~V, ~V, ~q, ~lq, k1, v, p, w) == True{}: Bool
} -> {
  Trie.all2.leaf(
    ~V,
    ~V,
    ~r,
    ~lr,
    Trie.union.fork(~V, ~(x => y => x), k1, v, p, w),
    p,
    w
  )
    == True{}: Bool
}:
  match k1 p:
    case Nil{} Nil{}:
      Trie.take_keeps_right.node(
        ~V,
        ~q,
        ~lq,
        ~r,
        ~lr,
        ~step,
        ~rrefl,
        Some{v},
        Tip{},
        Tip{},
        Some{w},
        Tip{},
        Tip{},
        e2 => {==},
        e2 => {==}
      )
    case Nil{} Con{False{}, +rp}:
      Trie.take_keeps_right.node(
        ~V,
        ~q,
        ~lq,
        ~r,
        ~lr,
        ~step,
        ~rrefl,
        Some{v},
        Tip{},
        Tip{},
        None{},
        Leaf{rp, w},
        Tip{},
        e2 => Trie.all2_refl.leaf(~V, ~r, ~lr, ~rrefl, rp, w),
        e2 => {==}
      )
    case Nil{} Con{True{}, +rp}:
      Trie.take_keeps_right.node(
        ~V,
        ~q,
        ~lq,
        ~r,
        ~lr,
        ~step,
        ~rrefl,
        Some{v},
        Tip{},
        Tip{},
        None{},
        Tip{},
        Leaf{rp, w},
        e2 => {==},
        e2 => Trie.all2_refl.leaf(~V, ~r, ~lr, ~rrefl, rp, w)
      )
    case Con{False{}, +r1} Nil{}:
      Trie.take_keeps_right.node(
        ~V,
        ~q,
        ~lq,
        ~r,
        ~lr,
        ~step,
        ~rrefl,
        None{},
        Leaf{r1, v},
        Tip{},
        Some{w},
        Tip{},
        Tip{},
        e2 => {==},
        e2 => {==}
      )
    case Con{False{}, +r1} Con{False{}, +rp}:
      e =>
        %Trie.all2_bin.f(
          ~V,
          ~V,
          ~r,
          ~lr,
          Trie.union.fork(~V, ~(x => y => x), r1, v, rp, w),
          rp,
          w
        )(Trie.fork_part(~V, ~(x => y => x), r1, v, rp, w)): {_ == True{}: Bool}
        Trie.take_keeps_right.node(
          ~V,
          ~q,
          ~lq,
          ~r,
          ~lr,
          ~step,
          ~rrefl,
          None{},
          Leaf{r1, v},
          Tip{},
          None{},
          Leaf{rp, w},
          Tip{},
          Trie.take_keeps_right.fork(~V, ~q, ~lq, ~r, ~lr, ~step, ~rrefl, r1, v, rp, w),
          e2 => {==}
        )(e)
    case Con{False{}, +r1} Con{True{}, +rp}:
      Trie.take_keeps_right.node(
        ~V,
        ~q,
        ~lq,
        ~r,
        ~lr,
        ~step,
        ~rrefl,
        None{},
        Leaf{r1, v},
        Tip{},
        None{},
        Tip{},
        Leaf{rp, w},
        e2 => {==},
        e2 => Trie.all2_refl.leaf(~V, ~r, ~lr, ~rrefl, rp, w)
      )
    case Con{True{}, +r1} Nil{}:
      Trie.take_keeps_right.node(
        ~V,
        ~q,
        ~lq,
        ~r,
        ~lr,
        ~step,
        ~rrefl,
        None{},
        Tip{},
        Leaf{r1, v},
        Some{w},
        Tip{},
        Tip{},
        e2 => {==},
        e2 => {==}
      )
    case Con{True{}, +r1} Con{False{}, +rp}:
      Trie.take_keeps_right.node(
        ~V,
        ~q,
        ~lq,
        ~r,
        ~lr,
        ~step,
        ~rrefl,
        None{},
        Tip{},
        Leaf{r1, v},
        None{},
        Leaf{rp, w},
        Tip{},
        e2 => Trie.all2_refl.leaf(~V, ~r, ~lr, ~rrefl, rp, w),
        e2 => {==}
      )
    case Con{True{}, +r1} Con{True{}, +rp}:
      e =>
        %Trie.all2_bin.t(
          ~V,
          ~V,
          ~r,
          ~lr,
          Trie.union.fork(~V, ~(x => y => x), r1, v, rp, w),
          rp,
          w
        )(Trie.fork_part(~V, ~(x => y => x), r1, v, rp, w)): {_ == True{}: Bool}
        Trie.take_keeps_right.node(
          ~V,
          ~q,
          ~lq,
          ~r,
          ~lr,
          ~step,
          ~rrefl,
          None{},
          Tip{},
          Leaf{r1, v},
          None{},
          Tip{},
          Leaf{rp, w},
          e2 => {==},
          Trie.take_keeps_right.fork(~V, ~q, ~lq, ~r, ~lr, ~step, ~rrefl, r1, v, rp, w)
        )(e)

# Trie.take_keeps_right for an entry and a trie
def Trie.take_keeps_right.leaf(
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
  y: Trie<V>,
  k1: List<&2, Bool>,
  +v: V
) -> {
  Trie.all2.leaf(~V, ~V, ~q, ~lq, y, k1, v) == True{}: Bool
} -> {Trie.all2(~V, ~V, ~r, ~lr, y, Trie.union.leaf(~V, ~(x => y => x), y, k1, v)) == True{}: Bool}:
  match y k1:
    case Tip{} r1:
      e => {==}
    case Leaf{p, w} r1:
      Trie.take_keeps_right.fork(~V, ~q, ~lq, ~r, ~lr, ~step, ~rrefl, r1, v, p, w)
    case Bin{h, +z, +o} Nil{}:
      Trie.take_keeps_right.node(
        ~V,
        ~q,
        ~lq,
        ~r,
        ~lr,
        ~step,
        ~rrefl,
        Some{v},
        Tip{},
        Tip{},
        h,
        z,
        o,
        e2 => Trie.all2_refl(~V, ~r, ~lr, ~rrefl, z),
        e2 => Trie.all2_refl(~V, ~r, ~lr, ~rrefl, o)
      )
    case Bin{+h, +z, +o} Con{False{}, +r1}:
      Trie.take_keeps_right.node(
        ~V,
        ~q,
        ~lq,
        ~r,
        ~lr,
        ~step,
        ~rrefl,
        None{},
        Leaf{r1, v},
        Tip{},
        h,
        z,
        o,
        Trie.take_keeps_right.leaf(~V, ~q, ~lq, ~r, ~lr, ~step, ~rrefl, z, r1, v),
        e2 => Trie.all2_refl(~V, ~r, ~lr, ~rrefl, o)
      )
    case Bin{+h, +z, +o} Con{True{}, +r1}:
      Trie.take_keeps_right.node(
        ~V,
        ~q,
        ~lq,
        ~r,
        ~lr,
        ~step,
        ~rrefl,
        None{},
        Tip{},
        Leaf{r1, v},
        h,
        z,
        o,
        e2 => Trie.all2_refl(~V, ~r, ~lr, ~rrefl, z),
        Trie.take_keeps_right.leaf(~V, ~q, ~lq, ~r, ~lr, ~step, ~rrefl, o, r1, v)
      )

# bend-lint: expect-begin bend-lint-rules/performance/missed_fork@hint -- a proof: it does not run
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
    case Leaf{k, v} y:
      Trie.take_keeps_right.leaf(~V, ~q, ~lq, ~r, ~lr, ~step, ~rrefl, y, k, v)
    case Bin{h, z, o} Tip{}:
      e => {==}
    case Bin{+h, +z, +o} Leaf{+p, +w}:
      e =>
        %Trie.all2_node.bin(
          ~V,
          ~V,
          ~r,
          ~lr,
          p,
          w,
          Shared.Maybe.join(~V, ~(c => d => c), h, Trie.at.here(V, p, w)),
          Trie.take(~V, z, Trie.at.zero(V, p, w)),
          Trie.take(~V, o, Trie.at.one(V, p, w))
        ): {_ == True{}: Bool}
        Trie.take_keeps_right.node(
          ~V,
          ~q,
          ~lq,
          ~r,
          ~lr,
          ~step,
          ~rrefl,
          h,
          z,
          o,
          Trie.at.here(V, p, w),
          Trie.at.zero(V, p, w),
          Trie.at.one(V, p, w),
          Trie.take_keeps_right(~V, ~q, ~lq, ~r, ~lr, ~step, ~rrefl, z, Trie.at.zero(V, p, w)),
          Trie.take_keeps_right(~V, ~q, ~lq, ~r, ~lr, ~step, ~rrefl, o, Trie.at.one(V, p, w))
        )(e)
    case Bin{+h1, +z1, +o1} Bin{h2, +z2, +o2}:
      Trie.take_keeps_right.node(
        ~V,
        ~q,
        ~lq,
        ~r,
        ~lr,
        ~step,
        ~rrefl,
        h1,
        z1,
        o1,
        h2,
        z2,
        o2,
        Trie.take_keeps_right(~V, ~q, ~lq, ~r, ~lr, ~step, ~rrefl, z1, z2),
        Trie.take_keeps_right(~V, ~q, ~lq, ~r, ~lr, ~step, ~rrefl, o1, o2)
      )
# bend-lint: expect-end bend-lint-rules/performance/missed_fork@hint

# what a takes of what it lacks of b is what it takes of b: the entries that a
# sync sends are enough
def Trie.take_minus(
  ~V: Data,
  ~same: V -> V -> Bool,
  a: Trie<V>,
  b: Trie<V>
) -> {Trie.take(~V, a, Trie.minus(~V, ~same, b, a)) == Trie.take(~V, a, b): Trie<V>}:
  Trie.union_lacks(~V, ~(x => y => x), ~same, ~(w => v => e => {==}), b, a)
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# Orders
# ------
# The values of a trie come in the order of their keys, so the values around a
# key are those before it and those after it.

# the key a comes before the key b
def Trie.key_lt(a: List<&2, Bool>, b: List<&2, Bool>) -> Bool:
  match a b:
    case Nil{} Con{y, rb}:
      True{}
    case Con{False{}, ra} Con{False{}, rb}:
      Trie.key_lt(ra, rb)
    case Con{True{}, ra} Con{True{}, rb}:
      Trie.key_lt(ra, rb)
    case Con{False{}, ra} Con{True{}, rb}:
      True{}
    case _ _:
      False{}

# the values of t whose keys come before k
def Trie.before(-V: Data, t: Trie<V>, k: List<&2, Bool>) -> List<&2, V>:
  match t k:
    case Tip{} r:
      []
    case Leaf{p, v} r:
      Bool.pick(List<&2, V>, Trie.key_lt(p, r), [v], [])
    case Bin{h, z, o} Nil{}:
      []
    case Bin{None{}, z, o} Con{False{}, r}:
      Trie.before(V, z, r)
    case Bin{Some{x}, z, o} Con{False{}, r}:
      x <> Trie.before(V, z, r)
    case Bin{None{}, z, o} Con{True{}, r}:
      List.append(&2, V, Trie.values(V, z), Trie.before(V, o, r))
    case Bin{Some{x}, z, o} Con{True{}, r}:
      x <> List.append(&2, V, Trie.values(V, z), Trie.before(V, o, r))

# the values of t whose keys come after k
def Trie.after(-V: Data, t: Trie<V>, k: List<&2, Bool>) -> List<&2, V>:
  match t k:
    case Tip{} r:
      []
    case Leaf{p, v} r:
      Bool.pick(List<&2, V>, Trie.key_lt(r, p), [v], [])
    case Bin{h, z, o} Nil{}:
      List.append(&2, V, Trie.values(V, z), Trie.values(V, o))
    case Bin{h, z, o} Con{False{}, r}:
      List.append(&2, V, Trie.after(V, z, r), Trie.values(V, o))
    case Bin{h, z, o} Con{True{}, r}:
      Trie.after(V, o, r)

# lists put one after the other group either way
def Trie.append_assoc(
  -V: Data,
  xs: List<&2, V>,
  ys: List<&2, V>,
  zs: List<&2, V>
) -> {
  List.append(
    &2,
    V,
    List.append(&2, V, xs, ys),
    zs
  )
    == List.append(&2, V, xs, List.append(&2, V, ys, zs)): List<&2, V>
}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, r}:
      %Trie.append_assoc(
        V,
        r,
        ys,
        zs
      ): {x <> List.append(&2, V, List.append(&2, V, r, ys), zs) == x <> _: List<&2, V>}
      {==}

# no key comes before itself
def Trie.key_lt_same(k: List<&2, Bool>) -> {False{} == Trie.key_lt(k, k): Bool}:
  match k:
    case Nil{}:
      {==}
    case Con{False{}, r}:
      Trie.key_lt_same(r)
    case Con{True{}, r}:
      Trie.key_lt_same(r)

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Trie.values_around for an entry, by whether the key is its key (held)
def Trie.values_around.leaf(
  -V: Data,
  +p: List<&2, Bool>,
  x: V,
  k: List<&2, Bool>,
  v: V,
  held: Bool,
  e: {held == Trie.same_key(k, p): Bool}
) -> {
  Bool.pick(Maybe<&2, V>, held, Some{x}, None{}) == Some{v}: Maybe<&2, V>
} -> {
  [
    x
  ]
    == List.append(
      &2,
      V,
      Bool.pick(List<&2, V>, Trie.key_lt(p, k), [x], []),
      v <> Bool.pick(List<&2, V>, Trie.key_lt(k, p), [x], [])
    ): List<&2, V>
}:
  match held:
    case False{}:
      g => Empty.absurd(
        {
          [
            x
          ]
            == List.append(
              &2,
              V,
              Bool.pick(List<&2, V>, Trie.key_lt(p, k), [x], []),
              v <> Bool.pick(List<&2, V>, Trie.key_lt(k, p), [x], [])
            ): List<&2, V>
        },
        Shared.Maybe.none_ne_some(V, v, g)
      )
    case True{}:
      g =>
        %Equal.sym(
          List<&2, Bool>,
          k,
          p,
          Trie.same_key_sound(k, p)(Equal.sym(Bool, True{}, Trie.same_key(k, p), e))
        ): {
          [
            x
          ]
            == List.append(
              &2,
              V,
              Bool.pick(List<&2, V>, Trie.key_lt(p, _), [x], []),
              v <> Bool.pick(List<&2, V>, Trie.key_lt(_, p), [x], [])
            ): List<&2, V>
        }
        %Trie.key_lt_same(
          p
        ): {
          [
            x
          ]
            == List.append(
              &2,
              V,
              Bool.pick(List<&2, V>, _, [x], []),
              v <> Bool.pick(List<&2, V>, _, [x], [])
            ): List<&2, V>
        }
        %Shared.Maybe.some_inj(V, x, v, g): {[x] == [_]: List<&2, V>}
        {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# the values of a trie are those before a key that it holds, its value, and
# those after it
def Trie.values_around(
  -V: Data,
  t: Trie<V>,
  k: List<&2, Bool>,
  +v: V
) -> {
  Trie.get(V, t, k) == Some{v}: Maybe<&2, V>
} -> {
  Trie.values(
    V,
    t
  )
    == List.append(&2, V, Trie.before(V, t, k), v <> Trie.after(V, t, k)): List<&2, V>
}:
  match t k:
    case Tip{} r:
      e => Empty.absurd(
        {[] == List.append(&2, V, [], v <> []): List<&2, V>},
        Shared.Maybe.none_ne_some(V, v, e)
      )
    case Leaf{+p, x} +r:
      Trie.values_around.leaf(V, p, x, r, v, Trie.same_key(r, p), {==})
    case Bin{None{}, z, o} Nil{}:
      e => Empty.absurd(
        {
          List.append(
            &2,
            V,
            Trie.values(V, z),
            Trie.values(V, o)
          )
            == v
            <> List.append(&2, V, Trie.values(V, z), Trie.values(V, o)): List<&2, V>
        },
        Shared.Maybe.none_ne_some(V, v, e)
      )
    case Bin{Some{x}, z, o} Nil{}:
      e =>
        %Shared.Maybe.some_inj(
          V,
          x,
          v,
          e
        ): {
          x
            <> List.append(&2, V, Trie.values(V, z), Trie.values(V, o))
            == _
            <> List.append(&2, V, Trie.values(V, z), Trie.values(V, o)): List<&2, V>
        }
        {==}
    case Bin{None{}, +z, +o} Con{False{}, +r}:
      e =>
        %Trie.append_assoc(
          V,
          Trie.before(V, z, r),
          v <> Trie.after(V, z, r),
          Trie.values(V, o)
        ): {List.append(&2, V, Trie.values(V, z), Trie.values(V, o)) == _: List<&2, V>}
        %Trie.values_around(
          V,
          z,
          r,
          v
        )(
          e
        ): {
          List.append(
            &2,
            V,
            Trie.values(V, z),
            Trie.values(V, o)
          )
            == List.append(&2, V, _, Trie.values(V, o)): List<&2, V>
        }
        {==}
    case Bin{Some{x}, +z, +o} Con{False{}, +r}:
      e =>
        %Trie.append_assoc(
          V,
          Trie.before(V, z, r),
          v <> Trie.after(V, z, r),
          Trie.values(V, o)
        ): {x <> List.append(&2, V, Trie.values(V, z), Trie.values(V, o)) == x <> _: List<&2, V>}
        %Trie.values_around(
          V,
          z,
          r,
          v
        )(
          e
        ): {
          x
            <> List.append(&2, V, Trie.values(V, z), Trie.values(V, o))
            == x
            <> List.append(&2, V, _, Trie.values(V, o)): List<&2, V>
        }
        {==}
    case Bin{None{}, +z, +o} Con{True{}, +r}:
      e =>
        %Equal.sym(
          List<&2, V>,
          List.append(
            &2,
            V,
            List.append(&2, V, Trie.values(V, z), Trie.before(V, o, r)),
            v <> Trie.after(V, o, r)
          ),
          List.append(
            &2,
            V,
            Trie.values(V, z),
            List.append(&2, V, Trie.before(V, o, r), v <> Trie.after(V, o, r))
          ),
          Trie.append_assoc(V, Trie.values(V, z), Trie.before(V, o, r), v <> Trie.after(V, o, r))
        ): {List.append(&2, V, Trie.values(V, z), Trie.values(V, o)) == _: List<&2, V>}
        %Trie.values_around(
          V,
          o,
          r,
          v
        )(
          e
        ): {
          List.append(
            &2,
            V,
            Trie.values(V, z),
            Trie.values(V, o)
          )
            == List.append(&2, V, Trie.values(V, z), _): List<&2, V>
        }
        {==}
    case Bin{Some{x}, +z, +o} Con{True{}, +r}:
      e =>
        %Equal.sym(
          List<&2, V>,
          List.append(
            &2,
            V,
            List.append(&2, V, Trie.values(V, z), Trie.before(V, o, r)),
            v <> Trie.after(V, o, r)
          ),
          List.append(
            &2,
            V,
            Trie.values(V, z),
            List.append(&2, V, Trie.before(V, o, r), v <> Trie.after(V, o, r))
          ),
          Trie.append_assoc(V, Trie.values(V, z), Trie.before(V, o, r), v <> Trie.after(V, o, r))
        ): {x <> List.append(&2, V, Trie.values(V, z), Trie.values(V, o)) == x <> _: List<&2, V>}
        %Trie.values_around(
          V,
          o,
          r,
          v
        )(
          e
        ): {
          x
            <> List.append(&2, V, Trie.values(V, z), Trie.values(V, o))
            == x
            <> List.append(&2, V, Trie.values(V, z), _): List<&2, V>
        }
        {==}
