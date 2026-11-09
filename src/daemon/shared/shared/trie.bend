import Base
import ../../../shared.bend as Shared

# Tries
# -----
# A trie maps keys to values. A key is a list of bits, read from the first:
# a False goes to zero, a True to one. Its shape is a function of the keys and
# values it holds, so two tries that hold the same entries are the same term,
# and a union is commutative, associative and idempotent as terms.

# a trie: the value of the empty key here, then the keys that start with False
# (zero) and with True (one)
type Trie<-V: Data> is Data:
  tip{}
  bin{here: Maybe<&2, V>, zero: Trie<V>, one: Trie<V>}

# a trie with no entries
def Trie.new(-V: Data) -> Trie<V>:
  tip{}

# the value of the key k in t, or None
def Trie.get(-V: Data, t: Trie<V>, k: List<&2, Bool>) -> Maybe<&2, V>:
  match t k:
    case tip{} r:
      None{}
    case bin{h, z, o} Nil{}:
      h
    case bin{h, z, o} Con{False{}, r}:
      Trie.get(V, z, r)
    case bin{h, z, o} Con{True{}, r}:
      Trie.get(V, o, r)

# the trie with only the key k, mapped to v
def Trie.one(-V: Data, k: List<&2, Bool>, v: V) -> Trie<V>:
  match k:
    case Nil{}:
      bin{Some{v}, tip{}, tip{}}
    case Con{False{}, r}:
      bin{None{}, Trie.one(V, r, v), tip{}}
    case Con{True{}, r}:
      bin{None{}, tip{}, Trie.one(V, r, v)}

# t with the key k mapped to v
def Trie.set(-V: Data, t: Trie<V>, k: List<&2, Bool>, v: V) -> Trie<V>:
  match t k:
    case tip{} r:
      Trie.one(V, r, v)
    case bin{h, z, o} Nil{}:
      bin{Some{v}, z, o}
    case bin{h, z, o} Con{False{}, r}:
      bin{h, Trie.set(V, z, r, v), o}
    case bin{h, z, o} Con{True{}, r}:
      bin{h, z, Trie.set(V, o, r, v)}

# the values of t, in the order of their keys
def Trie.values(-V: Data, t: Trie<V>) -> List<&2, V>:
  match t:
    case tip{}:
      []
    case bin{None{}, z, o}:
      zs os = Trie.values(V, z) Trie.values(V, o)
      List.append(&2, V, zs, os)
    case bin{Some{v}, z, o}:
      zs os = Trie.values(V, z) Trie.values(V, o)
      v <> List.append(&2, V, zs, os)

# the number of entries of t
def Trie.size(-V: Data, t: Trie<V>) -> Nat:
  match t:
    case tip{}:
      0n
    case bin{None{}, z, o}:
      zs os = Trie.size(V, z) Trie.size(V, o)
      Nat.add(zs, os)
    case bin{Some{v}, z, o}:
      zs os = Trie.size(V, z) Trie.size(V, o)
      1n+Nat.add(zs, os)

# the entries of t whose keys start with k, under the rest of their keys
def Trie.under(-V: Data, t: Trie<V>, k: List<&2, Bool>) -> Trie<V>:
  match t k:
    case tip{} r:
      tip{}
    case bin{h, z, o} Nil{}:
      bin{h, z, o}
    case bin{h, z, o} Con{False{}, r}:
      Trie.under(V, z, r)
    case bin{h, z, o} Con{True{}, r}:
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

# Unions
# ------
# A union joins the values of a key that both tries hold. When join is a
# semilattice (commutative, associative, idempotent), so is the union: two
# holders that take in each other's entries, in any order and any number of
# times, end with the same trie.

# what a and b hold for a key, joined
def Trie.pick(~V: Data, ~join: V -> V -> V, a: Maybe<&2, V>, b: Maybe<&2, V>) -> Maybe<&2, V>:
  match a b:
    case None{} y:
      y
    case Some{x} None{}:
      Some{x}
    case Some{x} Some{y}:
      Some{join(x, y)}

# the entries of a and b, joined where both hold a key
def Trie.union(~V: Data, ~join: V -> V -> V, a: Trie<V>, b: Trie<V>) -> Trie<V>:
  match a b:
    case tip{} y:
      y
    case bin{h, z, o} tip{}:
      bin{h, z, o}
    case bin{h1, z1, o1} bin{h2, z2, o2}:
      zs os = Trie.union(~V, ~join, z1, z2) Trie.union(~V, ~join, o1, o2)
      bin{Trie.pick(~V, ~join, h1, h2), zs, os}

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
    case tip{} y:
      tip{}
    case bin{h, z, o} tip{}:
      bin{h, z, o}
    case bin{h1, z1, o1} bin{h2, z2, o2}:
      zs os = Trie.minus(~V, ~same, z1, z2) Trie.minus(~V, ~same, o1, o2)
      bin{Trie.minus.here(~V, ~same, h1, h2), zs, os}

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
    case tip{} p q:
      Trie.get_one_at(ty, p, v, q)
    case bin{h, z, o} Nil{} Nil{}:
      {==}
    case bin{h, z, o} Nil{} Con{False{}, r}:
      {==}
    case bin{h, z, o} Nil{} Con{True{}, r}:
      {==}
    case bin{h, z, o} Con{False{}, r0} Nil{}:
      {==}
    case bin{h, z, o} Con{True{}, r0} Nil{}:
      {==}
    case bin{h, z, o} Con{False{}, r0} Con{False{}, r}:
      Trie.get_set(ty, z, r0, v, r)
    case bin{h, z, o} Con{False{}, r0} Con{True{}, r}:
      {==}
    case bin{h, z, o} Con{True{}, r0} Con{False{}, r}:
      {==}
    case bin{h, z, o} Con{True{}, r0} Con{True{}, r}:
      Trie.get_set(ty, o, r0, v, r)

# nothing joined to a value is that value
def Trie.pick_none(
  ~V: Data,
  ~join: V -> V -> V,
  a: Maybe<&2, V>
) -> {Trie.pick(~V, ~join, a, None{}) == a: Maybe<&2, V>}:
  match a:
    case None{}:
      {==}
    case Some{x}:
      {==}

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
      == Trie.pick(~V, ~join, Trie.get(V, a, k), Trie.get(V, b, k)): Maybe<&2, V>
  }

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
def Trie.get_union(ty, join, a, b, k):
  match a b k:
    case tip{} y q:
      {==}
    case bin{h, z, o} tip{} q:
      get1 = Trie.get(ty, bin{h, z, o}, q)
      Equal.sym(
        Maybe<&2, ty>,
        Trie.pick(~ty, ~join, get1, None{}),
        get1,
        Trie.pick_none(~ty, ~join, get1)
      )
    case bin{h1, z1, o1} bin{h2, z2, o2} Nil{}:
      {==}
    case bin{h1, z1, o1} bin{h2, z2, o2} Con{False{}, r}:
      Trie.get_union(~ty, ~join, z1, z2, r)
    case bin{h1, z1, o1} bin{h2, z2, o2} Con{True{}, r}:
      Trie.get_union(~ty, ~join, o1, o2, r)
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# a pick is the same either way round, when join is
def Trie.pick_comm(
  ~V: Data,
  ~join: V -> V -> V,
  ~comm: @x: V -> @y: V -> {join(x, y) == join(y, x): V},
  a: Maybe<&2, V>,
  b: Maybe<&2, V>
) -> {Trie.pick(~V, ~join, a, b) == Trie.pick(~V, ~join, b, a): Maybe<&2, V>}:
  match a b:
    case None{} None{}:
      {==}
    case None{} Some{y}:
      {==}
    case Some{x} None{}:
      {==}
    case Some{x} Some{y}:
      %comm(x)(y): {Some{join(x, y)} == Some{_}: Maybe<&2, V>}
      {==}

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
    case tip{} tip{}:
      {==}
    case tip{} bin{h, z, o}:
      {==}
    case bin{+h, +z, +o} tip{}:
      {==}
    case bin{h1, z1, o1} bin{+h2, +z2, +o2}:
      pick1 = Trie.pick(~ty, ~join, h1, h2)
      union1 = Trie.union(~ty, ~join, z1, z2)
      union2 = Trie.union(~ty, ~join, o1, o2)
      union3 = Trie.union(~ty, ~join, o2, o1)
      %Trie.pick_comm(~ty, ~join, ~comm, h1, h2):
        {bin{pick1, union1, union2} == bin{_, Trie.union(~ty, ~join, z2, z1), union3}: Trie<ty>}
      %Trie.union_comm(~ty, ~join, ~comm, z1, z2):
        {bin{pick1, union1, union2} == bin{pick1, _, union3}: Trie<ty>}
      %Trie.union_comm(~ty, ~join, ~comm, o1, o2):
        {bin{pick1, union1, union2} == bin{pick1, union1, _}: Trie<ty>}
      {==}
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# a pick groups either way, when join does
def Trie.pick_assoc(
  ~V: Data,
  ~join: V -> V -> V,
  ~assoc: @x: V -> @y: V -> @z: V -> {join(join(x, y), z) == join(x, join(y, z)): V},
  a: Maybe<&2, V>,
  b: Maybe<&2, V>,
  c: Maybe<&2, V>
) -> {
  Trie.pick(
    ~V,
    ~join,
    Trie.pick(~V, ~join, a, b),
    c
  )
    == Trie.pick(~V, ~join, a, Trie.pick(~V, ~join, b, c)): Maybe<&2, V>
}:
  match a b c:
    case None{} y w:
      {==}
    case Some{x} None{} w:
      {==}
    case Some{x} Some{y} None{}:
      {==}
    case Some{x} Some{y} Some{w}:
      %assoc(x)(y)(w): {Some{join(join(x, y), w)} == Some{_}: Maybe<&2, V>}
      {==}

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
    case tip{} y w:
      {==}
    case bin{h, z, o} tip{} w:
      {==}
    case bin{h1, z1, o1} bin{h2, z2, o2} tip{}:
      {==}
    case bin{h1, z1, o1} bin{h2, z2, o2} bin{h3, z3, o3}:
      %Trie.pick_assoc(~ty, ~join, ~assoc, h1, h2, h3):
        {
          bin{
            Trie.pick(~ty, ~join, Trie.pick(~ty, ~join, h1, h2), h3),
            Trie.union(~ty, ~join, Trie.union(~ty, ~join, z1, z2), z3),
            Trie.union(~ty, ~join, Trie.union(~ty, ~join, o1, o2), o3)
          }
            == bin{
              _,
              Trie.union(~ty, ~join, z1, Trie.union(~ty, ~join, z2, z3)),
              Trie.union(~ty, ~join, o1, Trie.union(~ty, ~join, o2, o3))
            }: Trie<ty>
        }
      %Trie.union_assoc(~ty, ~join, ~assoc, z1, z2, z3):
        {
          bin{
            Trie.pick(~ty, ~join, Trie.pick(~ty, ~join, h1, h2), h3),
            Trie.union(~ty, ~join, Trie.union(~ty, ~join, z1, z2), z3),
            Trie.union(~ty, ~join, Trie.union(~ty, ~join, o1, o2), o3)
          }
            == bin{
              Trie.pick(~ty, ~join, Trie.pick(~ty, ~join, h1, h2), h3),
              _,
              Trie.union(~ty, ~join, o1, Trie.union(~ty, ~join, o2, o3))
            }: Trie<ty>
        }
      %Trie.union_assoc(~ty, ~join, ~assoc, o1, o2, o3):
        {
          bin{
            Trie.pick(~ty, ~join, Trie.pick(~ty, ~join, h1, h2), h3),
            Trie.union(~ty, ~join, Trie.union(~ty, ~join, z1, z2), z3),
            Trie.union(~ty, ~join, Trie.union(~ty, ~join, o1, o2), o3)
          }
            == bin{
              Trie.pick(~ty, ~join, Trie.pick(~ty, ~join, h1, h2), h3),
              Trie.union(~ty, ~join, Trie.union(~ty, ~join, z1, z2), z3),
              _
            }: Trie<ty>
        }
      {==}

# a value picked with itself is itself, when join is idempotent
def Trie.pick_idem(
  ~V: Data,
  ~join: V -> V -> V,
  ~idem: @x: V -> {join(x, x) == x: V},
  a: Maybe<&2, V>
) -> {Trie.pick(~V, ~join, a, a) == a: Maybe<&2, V>}:
  match a:
    case None{}:
      {==}
    case Some{x}:
      %Equal.sym(V, join(x, x), x, idem(x)): {Some{_} == Some{x}: Maybe<&2, V>}
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
    case tip{}:
      {==}
    case bin{h, +z, +o}:
      union1 = Trie.union(~ty, ~join, o, o)
      union2 = Trie.union(~ty, ~join, z, z)
      %Equal.sym(
        Maybe<&2, ty>,
        Trie.pick(~ty, ~join, h, h),
        h,
        Trie.pick_idem(~ty, ~join, ~idem, h)
      ):
        {bin{_, union2, union1} == bin{h, z, o}: Trie<ty>}
      %Equal.sym(Trie<ty>, union2, z, Trie.union_idem(~ty, ~join, ~idem, z)):
        {bin{h, _, union1} == bin{h, z, o}: Trie<ty>}
      %Equal.sym(
        Trie<ty>,
        union1,
        o,
        Trie.union_idem(~ty, ~join, ~idem, o)
      ): {bin{h, z, _} == bin{h, z, o}: Trie<ty>}
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
  Trie.pick(
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
  Trie.pick(
    ~V,
    ~join,
    r,
    Trie.minus.here(~V, ~same, s, r)
  )
    == Trie.pick(~V, ~join, r, s): Maybe<&2, V>
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
    case tip{} y:
      {==}
    case bin{+h, +z, +o} tip{}:
      {==}
    case bin{h1, z1, o1} bin{+h2, +z2, +o2}:
      pick1 = Trie.pick(~ty, ~join, h2, Trie.minus.here(~ty, ~same, h1, h2))
      union1 = Trie.union(~ty, ~join, z2, Trie.minus(~ty, ~same, z1, z2))
      union2 = Trie.union(~ty, ~join, o2, Trie.minus(~ty, ~same, o1, o2))
      union3 = Trie.union(~ty, ~join, o2, o1)
      %Trie.pick_minus(~ty, ~join, ~same, ~idem, ~laws, h1, h2):
        {bin{pick1, union1, union2} == bin{_, Trie.union(~ty, ~join, z2, z1), union3}: Trie<ty>}
      %Trie.union_minus(~ty, ~join, ~same, ~idem, ~laws, z1, z2):
        {bin{pick1, union1, union2} == bin{pick1, _, union3}: Trie<ty>}
      %Trie.union_minus(~ty, ~join, ~same, ~idem, ~laws, o1, o2):
        {bin{pick1, union1, union2} == bin{pick1, union1, _}: Trie<ty>}
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
) -> {Trie.union(~V, ~join, a, tip{}) == a: Trie<V>}:
  match a:
    case tip{}:
      {==}
    case bin{h, z, o}:
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
    case tip{} Con{False{}, r} Con{False{}, q}:
      Trie.under_union_apart(~ty, ~join, tip{}, r, q, v)
    case tip{} Con{True{}, r} Con{True{}, q}:
      Trie.under_union_apart(~ty, ~join, tip{}, r, q, v)
    case tip{} Con{False{}, r} Con{True{}, q}:
      h => {==}
    case tip{} Con{True{}, r} Con{False{}, q}:
      h => {==}
    case bin{h, z, o} Con{False{}, r} Con{False{}, q}:
      Trie.under_union_apart(~ty, ~join, z, r, q, v)
    case bin{h, z, +o} Con{False{}, r} Con{True{}, q}:
      e =>
        %Equal.sym(Trie<ty>, Trie.union(~ty, ~join, o, tip{}), o, Trie.union_tip(~ty, ~join, o)):
          {Trie.under(ty, _, q) == Trie.under(ty, o, q): Trie<ty>}
        {==}
    case bin{h, +z, o} Con{True{}, r} Con{False{}, q}:
      e =>
        %Equal.sym(Trie<ty>, Trie.union(~ty, ~join, z, tip{}), z, Trie.union_tip(~ty, ~join, z)):
          {Trie.under(ty, _, q) == Trie.under(ty, z, q): Trie<ty>}
        {==}
    case bin{h, z, o} Con{True{}, r} Con{True{}, q}:
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
    case tip{} y:
      Shared.Nat.le_zero(Trie.size(ty, y))
    case bin{h, z, o} tip{}:
      Shared.Nat.le_refl(Trie.size(ty, bin{h, z, o}))
    case bin{None{}, +z1, +o1} bin{None{}, +z2, +o2}:
      Shared.Nat.add_le(
        Trie.size(ty, z1),
        Trie.size(ty, Trie.union(~ty, ~join, z1, z2)),
        Trie.size(ty, o1),
        Trie.size(ty, Trie.union(~ty, ~join, o1, o2))
      )(Trie.size_union(~ty, ~join, z1, z2))(Trie.size_union(~ty, ~join, o1, o2))
    case bin{None{}, +z1, +o1} bin{Some{y}, +z2, +o2}:
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
    case bin{Some{x}, +z1, +o1} bin{None{}, +z2, +o2}:
      Shared.Nat.add_le(
        Trie.size(ty, z1),
        Trie.size(ty, Trie.union(~ty, ~join, z1, z2)),
        Trie.size(ty, o1),
        Trie.size(ty, Trie.union(~ty, ~join, o1, o2))
      )(Trie.size_union(~ty, ~join, z1, z2))(Trie.size_union(~ty, ~join, o1, o2))
    case bin{Some{x}, +z1, +o1} bin{Some{y}, +z2, +o2}:
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
    case tip{} q:
      g => Trie.size_one(ty, q, v)
    case bin{None{}, +z, +o} Nil{}:
      g =>
        +add1 = Nat.add(Trie.size(ty, z), Trie.size(ty, o))
        +union1 = Trie.union(~ty, ~join, o, tip{})
        %Equal.sym(Trie<ty>, Trie.union(~ty, ~join, z, tip{}), z, Trie.union_tip(~ty, ~join, z)):
          {1n+Nat.add(Trie.size(ty, _), Trie.size(ty, union1)) == 1n+add1: Nat}
        %Equal.sym(Trie<ty>, union1, o, Trie.union_tip(~ty, ~join, o)):
          {1n+Nat.add(Trie.size(ty, z), Trie.size(ty, _)) == 1n+add1: Nat}
        {==}
    case bin{Some{y}, z, o} Nil{}:
      g => Empty.absurd(
        {
          Trie.size(
            ty,
            Trie.union(~ty, ~join, bin{Some{y}, z, o}, Trie.one(ty, Nil{}, v))
          )
            == 1n+Trie.size(ty, bin{Some{y}, z, o}): Nat
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
    case bin{None{}, +z, +o} Con{False{}, +r}:
      g =>
        +size1 = Trie.size(ty, Trie.union(~ty, ~join, z, Trie.one(ty, r, v)))
        +add1 = Nat.add(Trie.size(ty, z), Trie.size(ty, o))
        %Equal.sym(Trie<ty>, Trie.union(~ty, ~join, o, tip{}), o, Trie.union_tip(~ty, ~join, o)):
          {Nat.add(size1, Trie.size(ty, _)) == 1n+add1: Nat}
        %Equal.sym(Nat, size1, 1n+Trie.size(ty, z), Trie.size_union_one(~ty, ~join, z, r, v)(g)):
          {Nat.add(_, Trie.size(ty, o)) == 1n+add1: Nat}
        {==}
    case bin{Some{y}, +z, +o} Con{False{}, +r}:
      g =>
        +size1 = Trie.size(ty, Trie.union(~ty, ~join, z, Trie.one(ty, r, v)))
        +add1 = Nat.add(Trie.size(ty, z), Trie.size(ty, o))
        %Equal.sym(Trie<ty>, Trie.union(~ty, ~join, o, tip{}), o, Trie.union_tip(~ty, ~join, o)):
          {1n+Nat.add(size1, Trie.size(ty, _)) == 1n+1n+add1: Nat}
        %Equal.sym(Nat, size1, 1n+Trie.size(ty, z), Trie.size_union_one(~ty, ~join, z, r, v)(g)):
          {1n+Nat.add(_, Trie.size(ty, o)) == 1n+1n+add1: Nat}
        {==}
    case bin{None{}, +z, +o} Con{True{}, +r}:
      g =>
        +size1 = Trie.size(ty, Trie.union(~ty, ~join, o, Trie.one(ty, r, v)))
        +add1 = Nat.add(Trie.size(ty, z), Trie.size(ty, o))
        %Equal.sym(Trie<ty>, Trie.union(~ty, ~join, z, tip{}), z, Trie.union_tip(~ty, ~join, z)):
          {Nat.add(Trie.size(ty, _), size1) == 1n+add1: Nat}
        %Equal.sym(Nat, size1, 1n+Trie.size(ty, o), Trie.size_union_one(~ty, ~join, o, r, v)(g)):
          {Nat.add(Trie.size(ty, z), _) == 1n+add1: Nat}
        Shared.Nat.add_succ(Trie.size(ty, z), Trie.size(ty, o))
    case bin{Some{y}, +z, +o} Con{True{}, +r}:
      g =>
        +add1 = Nat.add(Trie.size(ty, z), Trie.size(ty, o))
        +size1 = Trie.size(ty, Trie.union(~ty, ~join, o, Trie.one(ty, r, v)))
        %Equal.sym(Trie<ty>, Trie.union(~ty, ~join, z, tip{}), z, Trie.union_tip(~ty, ~join, z)):
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
    case tip{} y q:
      {==}
    case bin{h, z, o} tip{} q:
      under1 = Trie.under(V, bin{h, z, o}, q)
      Equal.sym(
        Trie<V>,
        Trie.union(~V, ~join, under1, tip{}),
        under1,
        Trie.union_tip(~V, ~join, under1)
      )
    case bin{h1, z1, o1} bin{h2, z2, o2} Nil{}:
      {==}
    case bin{h1, z1, o1} bin{h2, z2, o2} Con{False{}, r}:
      Trie.under_union(~V, ~join, z1, z2, r)
    case bin{h1, z1, o1} bin{h2, z2, o2} Con{True{}, r}:
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
    case tip{} q:
      {==}
    case bin{h, z, o} Nil{}:
      {==}
    case bin{h, z, o} Con{False{}, q}:
      Trie.get_under(V, z, q, r)
    case bin{h, z, o} Con{True{}, q}:
      Trie.get_under(V, o, q, r)

# the entries under no key are all the entries
def Trie.under_all(-V: Data, t: Trie<V>) -> {Trie.under(V, t, []) == t: Trie<V>}:
  match t:
    case tip{}:
      {==}
    case bin{h, z, o}:
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
