import Base
import ./nats.bend as Nats
import ./shared.bend as Shared

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
      List.append(&2, V, Trie.values(V, z), Trie.values(V, o))
    case Bin{Some{v}, z, o}:
      v <> List.append(&2, V, Trie.values(V, z), Trie.values(V, o))

# the number of entries of t
def Trie.size(-V: Data, t: Trie<V>) -> Nat:
  match t:
    case Tip{}:
      0n
    case Bin{None{}, z, o}:
      Nat.add(Trie.size(V, z), Trie.size(V, o))
    case Bin{Some{v}, z, o}:
      1n+Nat.add(Trie.size(V, z), Trie.size(V, o))

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

# the bits of the word w, from its first
def Trie.word(n: Nat, w: Word(n)) -> List<&2, Bool>:
  match n:
    case 0n:
      []
    case 1n+p:
      match w:
        case WCon{b, t}:
          b <> Trie.word(p, t)

# the key of the text t: each character as True and its 32 bits, then False;
# so the key of one text never starts the key of another, and keys of texts
# put one after the other never meet
def Trie.text(t: String) -> List<&2, Bool>:
  match t:
    case SNil{}:
      [False{}]
    case SCon{Chr{U32{w}}, r}:
      True{} <> List.append(&2, Bool, Trie.word(32n, w), Trie.text(r))

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
    case Tip{} y:
      y
    case Bin{h, z, o} Tip{}:
      Bin{h, z, o}
    case Bin{h1, z1, o1} Bin{h2, z2, o2}:
      zs os = Trie.union(~V, ~join, z1, z2) Trie.union(~V, ~join, o1, o2)
      Bin{Trie.pick(~V, ~join, h1, h2), zs, os}

# x, unless it is the same (held)
def Trie.minus.if(-V: Data, held: Bool, x: V) -> Maybe<&2, V>:
  match held:
    case True{}:
      None{}
    case False{}:
      Some{x}

# a, unless b holds the same value
def Trie.minus.here(~V: Data, ~same: V -> V -> Bool, a: Maybe<&2, V>, b: Maybe<&2, V>) -> Maybe<&2, V>:
  match a b:
    case None{} y:
      None{}
    case Some{x} None{}:
      Some{x}
    case Some{+x} Some{y}:
      Trie.minus.if(V, same(x, y), x)

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
def Trie.get_one(-V: Data, k: List<&2, Bool>, v: V) -> {Trie.get(V, Trie.one(V, k, v), k) == Some{v}: Maybe<&2, V>}:
  match k:
    case Nil{}:
      {==}
    case Con{False{}, r}:
      Trie.get_one(V, r, v)
    case Con{True{}, r}:
      Trie.get_one(V, r, v)

# after setting k to v, k has v
law Trie.get_after_set:
  for -V: Data
  for t: Trie<V>
  for k: List<&2, Bool>
  for v: V
  {Trie.get(V, Trie.set(V, t, k, v), k) == Some{v}: Maybe<&2, V>}

def Trie.get_after_set(V, t, k, v):
  match t k:
    case Tip{} r:
      Trie.get_one(V, r, v)
    case Bin{h, z, o} Nil{}:
      {==}
    case Bin{h, z, o} Con{False{}, r}:
      Trie.get_after_set(V, z, r, v)
    case Bin{h, z, o} Con{True{}, r}:
      Trie.get_after_set(V, o, r, v)

# nothing joined to a value is that value
def Trie.pick_none(~V: Data, ~join: V -> V -> V, a: Maybe<&2, V>) -> {Trie.pick(~V, ~join, a, None{}) == a: Maybe<&2, V>}:
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
    Trie.get(V, Trie.union(~V, ~join, a, b), k)
      == Trie.pick(~V, ~join, Trie.get(V, a, k), Trie.get(V, b, k)): Maybe<&2, V>
  }

def Trie.get_union(V, join, a, b, k):
  match a b k:
    case Tip{} y q:
      {==}
    case Bin{h, z, o} Tip{} q:
      Equal.sym(
        Maybe<&2, V>,
        Trie.pick(~V, ~join, Trie.get(V, Bin{h, z, o}, q), None{}),
        Trie.get(V, Bin{h, z, o}, q),
        Trie.pick_none(~V, ~join, Trie.get(V, Bin{h, z, o}, q))
      )
    case Bin{h1, z1, o1} Bin{h2, z2, o2} Nil{}:
      {==}
    case Bin{h1, z1, o1} Bin{h2, z2, o2} Con{False{}, r}:
      Trie.get_union(~V, ~join, z1, z2, r)
    case Bin{h1, z1, o1} Bin{h2, z2, o2} Con{True{}, r}:
      Trie.get_union(~V, ~join, o1, o2, r)

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
      %comm(x)(y) : {Some{join(x, y)} == Some{_}: Maybe<&2, V>}
      {==}

# a union is the same either way round
law Trie.union_comm:
  for ~V: Data
  for ~join: V -> V -> V
  for ~comm: @x: V -> @y: V -> {join(x, y) == join(y, x): V}
  for a: Trie<V>
  for b: Trie<V>
  {Trie.union(~V, ~join, a, b) == Trie.union(~V, ~join, b, a): Trie<V>}

def Trie.union_comm(V, join, comm, a, b):
  match a b:
    case Tip{} Tip{}:
      {==}
    case Tip{} Bin{h, z, o}:
      {==}
    case Bin{h, z, o} Tip{}:
      {==}
    case Bin{h1, z1, o1} Bin{h2, z2, o2}:
      %Trie.pick_comm(~V, ~join, ~comm, h1, h2) :
        {
          Bin{Trie.pick(~V, ~join, h1, h2), Trie.union(~V, ~join, z1, z2), Trie.union(~V, ~join, o1, o2)}
            == Bin{_, Trie.union(~V, ~join, z2, z1), Trie.union(~V, ~join, o2, o1)}: Trie<V>
        }
      %Trie.union_comm(~V, ~join, ~comm, z1, z2) :
        {
          Bin{Trie.pick(~V, ~join, h1, h2), Trie.union(~V, ~join, z1, z2), Trie.union(~V, ~join, o1, o2)}
            == Bin{Trie.pick(~V, ~join, h1, h2), _, Trie.union(~V, ~join, o2, o1)}: Trie<V>
        }
      %Trie.union_comm(~V, ~join, ~comm, o1, o2) :
        {
          Bin{Trie.pick(~V, ~join, h1, h2), Trie.union(~V, ~join, z1, z2), Trie.union(~V, ~join, o1, o2)}
            == Bin{Trie.pick(~V, ~join, h1, h2), Trie.union(~V, ~join, z1, z2), _}: Trie<V>
        }
      {==}

# a pick groups either way, when join does
def Trie.pick_assoc(
  ~V: Data,
  ~join: V -> V -> V,
  ~assoc: @x: V -> @y: V -> @z: V -> {join(join(x, y), z) == join(x, join(y, z)): V},
  a: Maybe<&2, V>,
  b: Maybe<&2, V>,
  c: Maybe<&2, V>
) -> {
  Trie.pick(~V, ~join, Trie.pick(~V, ~join, a, b), c)
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
      %assoc(x)(y)(w) : {Some{join(join(x, y), w)} == Some{_}: Maybe<&2, V>}
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
    Trie.union(~V, ~join, Trie.union(~V, ~join, a, b), c)
      == Trie.union(~V, ~join, a, Trie.union(~V, ~join, b, c)): Trie<V>
  }

def Trie.union_assoc(V, join, assoc, a, b, c):
  match a b c:
    case Tip{} y w:
      {==}
    case Bin{h, z, o} Tip{} w:
      {==}
    case Bin{h1, z1, o1} Bin{h2, z2, o2} Tip{}:
      {==}
    case Bin{h1, z1, o1} Bin{h2, z2, o2} Bin{h3, z3, o3}:
      %Trie.pick_assoc(~V, ~join, ~assoc, h1, h2, h3) :
        {
          Bin{
            Trie.pick(~V, ~join, Trie.pick(~V, ~join, h1, h2), h3),
            Trie.union(~V, ~join, Trie.union(~V, ~join, z1, z2), z3),
            Trie.union(~V, ~join, Trie.union(~V, ~join, o1, o2), o3)
          }
            == Bin{
              _,
              Trie.union(~V, ~join, z1, Trie.union(~V, ~join, z2, z3)),
              Trie.union(~V, ~join, o1, Trie.union(~V, ~join, o2, o3))
            }: Trie<V>
        }
      %Trie.union_assoc(~V, ~join, ~assoc, z1, z2, z3) :
        {
          Bin{
            Trie.pick(~V, ~join, Trie.pick(~V, ~join, h1, h2), h3),
            Trie.union(~V, ~join, Trie.union(~V, ~join, z1, z2), z3),
            Trie.union(~V, ~join, Trie.union(~V, ~join, o1, o2), o3)
          }
            == Bin{
              Trie.pick(~V, ~join, Trie.pick(~V, ~join, h1, h2), h3),
              _,
              Trie.union(~V, ~join, o1, Trie.union(~V, ~join, o2, o3))
            }: Trie<V>
        }
      %Trie.union_assoc(~V, ~join, ~assoc, o1, o2, o3) :
        {
          Bin{
            Trie.pick(~V, ~join, Trie.pick(~V, ~join, h1, h2), h3),
            Trie.union(~V, ~join, Trie.union(~V, ~join, z1, z2), z3),
            Trie.union(~V, ~join, Trie.union(~V, ~join, o1, o2), o3)
          }
            == Bin{
              Trie.pick(~V, ~join, Trie.pick(~V, ~join, h1, h2), h3),
              Trie.union(~V, ~join, Trie.union(~V, ~join, z1, z2), z3),
              _
            }: Trie<V>
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
      %Equal.sym(V, join(x, x), x, idem(x)) : {Some{_} == Some{x}: Maybe<&2, V>}
      {==}

# a trie joined with itself is itself
law Trie.union_idem:
  for ~V: Data
  for ~join: V -> V -> V
  for ~idem: @x: V -> {join(x, x) == x: V}
  for a: Trie<V>
  {Trie.union(~V, ~join, a, a) == a: Trie<V>}

def Trie.union_idem(V, join, idem, a):
  match a:
    case Tip{}:
      {==}
    case Bin{h, z, o}:
      %Equal.sym(Maybe<&2, V>, Trie.pick(~V, ~join, h, h), h, Trie.pick_idem(~V, ~join, ~idem, h)) :
        {Bin{_, Trie.union(~V, ~join, z, z), Trie.union(~V, ~join, o, o)} == Bin{h, z, o}: Trie<V>}
      %Equal.sym(Trie<V>, Trie.union(~V, ~join, z, z), z, Trie.union_idem(~V, ~join, ~idem, z)) :
        {Bin{h, _, Trie.union(~V, ~join, o, o)} == Bin{h, z, o}: Trie<V>}
      %Equal.sym(Trie<V>, Trie.union(~V, ~join, o, o), o, Trie.union_idem(~V, ~join, ~idem, o)) : {Bin{h, z, _} == Bin{h, z, o}: Trie<V>}
      {==}

# Trie.pick_minus once same(x, y) is known (held)
def Trie.pick_minus.if(
  ~V: Data,
  ~join: V -> V -> V,
  ~same: V -> V -> Bool,
  ~idem: @x: V -> {join(x, x) == x: V},
  ~sound: @x: V -> @y: V -> {same(x, y) == True{}: Bool} -> {x == y: V},
  held: Bool,
  +x: V,
  +y: V,
  e: {same(x, y) == held: Bool}
) -> {
  Trie.pick(~V, ~join, Some{y}, Trie.minus.if(V, held, x)) == Some{join(y, x)}: Maybe<&2, V>
}:
  match held:
    case True{}:
      %Equal.sym(V, x, y, sound(x)(y)(e)) : {Some{y} == Some{join(y, _)}: Maybe<&2, V>}
      %Equal.sym(V, join(y, y), y, idem(y)) : {Some{y} == Some{_}: Maybe<&2, V>}
      {==}
    case False{}:
      {==}

# what r holds for a key, joined with what r lacks of s there, is r's joined
# with s's
def Trie.pick_minus(
  ~V: Data,
  ~join: V -> V -> V,
  ~same: V -> V -> Bool,
  ~idem: @x: V -> {join(x, x) == x: V},
  ~sound: @x: V -> @y: V -> {same(x, y) == True{}: Bool} -> {x == y: V},
  s: Maybe<&2, V>,
  r: Maybe<&2, V>
) -> {
  Trie.pick(~V, ~join, r, Trie.minus.here(~V, ~same, s, r))
    == Trie.pick(~V, ~join, r, s): Maybe<&2, V>
}:
  match s r:
    case None{} y:
      {==}
    case Some{x} None{}:
      {==}
    case Some{+x} Some{+y}:
      Trie.pick_minus.if(~V, ~join, ~same, ~idem, ~sound, same(x, y), x, y, {==})

# taking in what r lacks of s is taking in s: a sync may send only that
law Trie.union_minus:
  for ~V: Data
  for ~join: V -> V -> V
  for ~same: V -> V -> Bool
  for ~idem: @x: V -> {join(x, x) == x: V}
  for ~sound: @x: V -> @y: V -> {same(x, y) == True{}: Bool} -> {x == y: V}
  for s: Trie<V>
  for r: Trie<V>
  {
    Trie.union(~V, ~join, r, Trie.minus(~V, ~same, s, r))
      == Trie.union(~V, ~join, r, s): Trie<V>
  }

def Trie.union_minus(V, join, same, idem, sound, s, r):
  match s r:
    case Tip{} y:
      {==}
    case Bin{h, z, o} Tip{}:
      {==}
    case Bin{h1, z1, o1} Bin{h2, z2, o2}:
      %Trie.pick_minus(~V, ~join, ~same, ~idem, ~sound, h1, h2) :
        {
          Bin{
            Trie.pick(~V, ~join, h2, Trie.minus.here(~V, ~same, h1, h2)),
            Trie.union(~V, ~join, z2, Trie.minus(~V, ~same, z1, z2)),
            Trie.union(~V, ~join, o2, Trie.minus(~V, ~same, o1, o2))
          }
            == Bin{_, Trie.union(~V, ~join, z2, z1), Trie.union(~V, ~join, o2, o1)}: Trie<V>
        }
      %Trie.union_minus(~V, ~join, ~same, ~idem, ~sound, z1, z2) :
        {
          Bin{
            Trie.pick(~V, ~join, h2, Trie.minus.here(~V, ~same, h1, h2)),
            Trie.union(~V, ~join, z2, Trie.minus(~V, ~same, z1, z2)),
            Trie.union(~V, ~join, o2, Trie.minus(~V, ~same, o1, o2))
          }
            == Bin{Trie.pick(~V, ~join, h2, Trie.minus.here(~V, ~same, h1, h2)), _, Trie.union(~V, ~join, o2, o1)}: Trie<V>
        }
      %Trie.union_minus(~V, ~join, ~same, ~idem, ~sound, o1, o2) :
        {
          Bin{
            Trie.pick(~V, ~join, h2, Trie.minus.here(~V, ~same, h1, h2)),
            Trie.union(~V, ~join, z2, Trie.minus(~V, ~same, z1, z2)),
            Trie.union(~V, ~join, o2, Trie.minus(~V, ~same, o1, o2))
          }
            == Bin{
              Trie.pick(~V, ~join, h2, Trie.minus.here(~V, ~same, h1, h2)),
              Trie.union(~V, ~join, z2, Trie.minus(~V, ~same, z1, z2)),
              _
            }: Trie<V>
        }
      {==}

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
def Trie.union_tip(~V: Data, ~join: V -> V -> V, a: Trie<V>) -> {Trie.union(~V, ~join, a, Tip{}) == a: Trie<V>}:
  match a:
    case Tip{}:
      {==}
    case Bin{h, z, o}:
      {==}

# the trie of one key holds nothing at a key apart from it
def Trie.get_one_apart(-V: Data, k: List<&2, Bool>, p: List<&2, Bool>, v: V) -> {Trie.apart(k, p) == True{}: Bool} -> {Trie.get(V, Trie.one(V, k, v), p) == None{}: Maybe<&2, V>}:
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
      h => Empty.absurd({Trie.get(V, Trie.one(V, Nil{}, v), q) == None{}: Maybe<&2, V>}, Shared.Bool.false_ne_true(h))
    case Con{b, r} Nil{}:
      h => Empty.absurd({Trie.get(V, Trie.one(V, b <> r, v), Nil{}) == None{}: Maybe<&2, V>}, Shared.Bool.false_ne_true(h))

# a key apart from k keeps its entries when one entry at k joins
law Trie.under_union_apart:
  for ~V: Data
  for ~join: V -> V -> V
  for s: Trie<V>
  for k: List<&2, Bool>
  for p: List<&2, Bool>
  for +v: V
  {Trie.apart(k, p) == True{}: Bool}
    -> {Trie.under(V, Trie.union(~V, ~join, s, Trie.one(V, k, v)), p) == Trie.under(V, s, p): Trie<V>}

def Trie.under_union_apart(V, join, s, k, p, v):
  match s k p:
    case Tip{} Con{False{}, r} Con{False{}, q}:
      Trie.under_union_apart(~V, ~join, Tip{}, r, q, v)
    case Tip{} Con{True{}, r} Con{True{}, q}:
      Trie.under_union_apart(~V, ~join, Tip{}, r, q, v)
    case Tip{} Con{False{}, r} Con{True{}, q}:
      h => {==}
    case Tip{} Con{True{}, r} Con{False{}, q}:
      h => {==}
    case Bin{h, z, o} Con{False{}, r} Con{False{}, q}:
      Trie.under_union_apart(~V, ~join, z, r, q, v)
    case Bin{h, z, +o} Con{False{}, r} Con{True{}, q}:
      e =>
        %Equal.sym(Trie<V>, Trie.union(~V, ~join, o, Tip{}), o, Trie.union_tip(~V, ~join, o)) :
          {Trie.under(V, _, q) == Trie.under(V, o, q): Trie<V>}
        {==}
    case Bin{h, +z, o} Con{True{}, r} Con{False{}, q}:
      e =>
        %Equal.sym(Trie<V>, Trie.union(~V, ~join, z, Tip{}), z, Trie.union_tip(~V, ~join, z)) :
          {Trie.under(V, _, q) == Trie.under(V, z, q): Trie<V>}
        {==}
    case Bin{h, z, o} Con{True{}, r} Con{True{}, q}:
      Trie.under_union_apart(~V, ~join, o, r, q, v)
    case w Nil{} q:
      e => Empty.absurd(
        {Trie.under(V, Trie.union(~V, ~join, w, Trie.one(V, Nil{}, v)), q) == Trie.under(V, w, q): Trie<V>},
        Shared.Bool.false_ne_true(e)
      )
    case w Con{b, r} Nil{}:
      e => Empty.absurd(
        {Trie.under(V, Trie.union(~V, ~join, w, Trie.one(V, b <> r, v)), Nil{}) == Trie.under(V, w, Nil{}): Trie<V>},
        Shared.Bool.false_ne_true(e)
      )

# a union holds at least the entries of its first side
law Trie.size_union:
  for ~V: Data
  for ~join: V -> V -> V
  for a: Trie<V>
  for b: Trie<V>
  {Nat.is_le(Trie.size(V, a), Trie.size(V, Trie.union(~V, ~join, a, b))) == True{}: Bool}

def Trie.size_union(V, join, a, b):
  match a b:
    case Tip{} y:
      Nats.Nat.le_zero(Trie.size(V, y))
    case Bin{h, z, o} Tip{}:
      Nats.Nat.le_refl(Trie.size(V, Bin{h, z, o}))
    case Bin{None{}, +z1, +o1} Bin{None{}, +z2, +o2}:
      Nats.Nat.add_le(
        Trie.size(V, z1),
        Trie.size(V, Trie.union(~V, ~join, z1, z2)),
        Trie.size(V, o1),
        Trie.size(V, Trie.union(~V, ~join, o1, o2))
      )(Trie.size_union(~V, ~join, z1, z2))(Trie.size_union(~V, ~join, o1, o2))
    case Bin{None{}, +z1, +o1} Bin{Some{y}, +z2, +o2}:
      Nats.Nat.le_succ(
        Nat.add(Trie.size(V, z1), Trie.size(V, o1)),
        Nat.add(Trie.size(V, Trie.union(~V, ~join, z1, z2)), Trie.size(V, Trie.union(~V, ~join, o1, o2)))
      )(
        Nats.Nat.add_le(
          Trie.size(V, z1),
          Trie.size(V, Trie.union(~V, ~join, z1, z2)),
          Trie.size(V, o1),
          Trie.size(V, Trie.union(~V, ~join, o1, o2))
        )(Trie.size_union(~V, ~join, z1, z2))(Trie.size_union(~V, ~join, o1, o2))
      )
    case Bin{Some{x}, +z1, +o1} Bin{None{}, +z2, +o2}:
      Nats.Nat.add_le(
        Trie.size(V, z1),
        Trie.size(V, Trie.union(~V, ~join, z1, z2)),
        Trie.size(V, o1),
        Trie.size(V, Trie.union(~V, ~join, o1, o2))
      )(Trie.size_union(~V, ~join, z1, z2))(Trie.size_union(~V, ~join, o1, o2))
    case Bin{Some{x}, +z1, +o1} Bin{Some{y}, +z2, +o2}:
      Nats.Nat.add_le(
        Trie.size(V, z1),
        Trie.size(V, Trie.union(~V, ~join, z1, z2)),
        Trie.size(V, o1),
        Trie.size(V, Trie.union(~V, ~join, o1, o2))
      )(Trie.size_union(~V, ~join, z1, z2))(Trie.size_union(~V, ~join, o1, o2))

# the trie of one key has one entry
def Trie.size_one(-V: Data, k: List<&2, Bool>, v: V) -> {Trie.size(V, Trie.one(V, k, v)) == 1n: Nat}:
  match k:
    case Nil{}:
      {==}
    case Con{False{}, r}:
      %Equal.sym(Nat, Trie.size(V, Trie.one(V, r, v)), 1n, Trie.size_one(V, r, v)) : {Nat.add(_, 0n) == 1n: Nat}
      {==}
    case Con{True{}, r}:
      %Equal.sym(Nat, Trie.size(V, Trie.one(V, r, v)), 1n, Trie.size_one(V, r, v)) : {Nat.add(0n, _) == 1n: Nat}
      {==}

# one entry at a key that s does not hold adds one entry
law Trie.size_union_one:
  for ~V: Data
  for ~join: V -> V -> V
  for s: Trie<V>
  for k: List<&2, Bool>
  for +v: V
  {Trie.get(V, s, k) == None{}: Maybe<&2, V>}
    -> {Trie.size(V, Trie.union(~V, ~join, s, Trie.one(V, k, v))) == 1n+Trie.size(V, s): Nat}

def Trie.size_union_one(V, join, s, k, v):
  match s k:
    case Tip{} q:
      g => Trie.size_one(V, q, v)
    case Bin{None{}, +z, +o} Nil{}:
      g =>
        %Equal.sym(Trie<V>, Trie.union(~V, ~join, z, Tip{}), z, Trie.union_tip(~V, ~join, z)) :
          {1n+Nat.add(Trie.size(V, _), Trie.size(V, Trie.union(~V, ~join, o, Tip{}))) == 1n+Nat.add(Trie.size(V, z), Trie.size(V, o)): Nat}
        %Equal.sym(Trie<V>, Trie.union(~V, ~join, o, Tip{}), o, Trie.union_tip(~V, ~join, o)) :
          {1n+Nat.add(Trie.size(V, z), Trie.size(V, _)) == 1n+Nat.add(Trie.size(V, z), Trie.size(V, o)): Nat}
        {==}
    case Bin{Some{y}, z, o} Nil{}:
      g => Empty.absurd(
        {Trie.size(V, Trie.union(~V, ~join, Bin{Some{y}, z, o}, Trie.one(V, Nil{}, v))) == 1n+Trie.size(V, Bin{Some{y}, z, o}): Nat},
        Shared.Bool.false_ne_true(Equal.cong(Maybe<&2, V>, Bool, m => Maybe.is_some(&2, V, m), None{}, Some{y}, Equal.sym(Maybe<&2, V>, Some{y}, None{}, g)))
      )
    case Bin{None{}, +z, +o} Con{False{}, +r}:
      g =>
        %Equal.sym(Trie<V>, Trie.union(~V, ~join, o, Tip{}), o, Trie.union_tip(~V, ~join, o)) :
          {Nat.add(Trie.size(V, Trie.union(~V, ~join, z, Trie.one(V, r, v))), Trie.size(V, _)) == 1n+Nat.add(Trie.size(V, z), Trie.size(V, o)): Nat}
        %Equal.sym(Nat, Trie.size(V, Trie.union(~V, ~join, z, Trie.one(V, r, v))), 1n+Trie.size(V, z), Trie.size_union_one(~V, ~join, z, r, v)(g)) :
          {Nat.add(_, Trie.size(V, o)) == 1n+Nat.add(Trie.size(V, z), Trie.size(V, o)): Nat}
        {==}
    case Bin{Some{y}, +z, +o} Con{False{}, +r}:
      g =>
        %Equal.sym(Trie<V>, Trie.union(~V, ~join, o, Tip{}), o, Trie.union_tip(~V, ~join, o)) :
          {1n+Nat.add(Trie.size(V, Trie.union(~V, ~join, z, Trie.one(V, r, v))), Trie.size(V, _)) == 1n+1n+Nat.add(Trie.size(V, z), Trie.size(V, o)): Nat}
        %Equal.sym(Nat, Trie.size(V, Trie.union(~V, ~join, z, Trie.one(V, r, v))), 1n+Trie.size(V, z), Trie.size_union_one(~V, ~join, z, r, v)(g)) :
          {1n+Nat.add(_, Trie.size(V, o)) == 1n+1n+Nat.add(Trie.size(V, z), Trie.size(V, o)): Nat}
        {==}
    case Bin{None{}, +z, +o} Con{True{}, +r}:
      g =>
        %Equal.sym(Trie<V>, Trie.union(~V, ~join, z, Tip{}), z, Trie.union_tip(~V, ~join, z)) :
          {Nat.add(Trie.size(V, _), Trie.size(V, Trie.union(~V, ~join, o, Trie.one(V, r, v)))) == 1n+Nat.add(Trie.size(V, z), Trie.size(V, o)): Nat}
        %Equal.sym(Nat, Trie.size(V, Trie.union(~V, ~join, o, Trie.one(V, r, v))), 1n+Trie.size(V, o), Trie.size_union_one(~V, ~join, o, r, v)(g)) :
          {Nat.add(Trie.size(V, z), _) == 1n+Nat.add(Trie.size(V, z), Trie.size(V, o)): Nat}
        Nats.Nat.add_succ(Trie.size(V, z), Trie.size(V, o))
    case Bin{Some{y}, +z, +o} Con{True{}, +r}:
      g =>
        %Equal.sym(Trie<V>, Trie.union(~V, ~join, z, Tip{}), z, Trie.union_tip(~V, ~join, z)) :
          {1n+Nat.add(Trie.size(V, _), Trie.size(V, Trie.union(~V, ~join, o, Trie.one(V, r, v)))) == 1n+1n+Nat.add(Trie.size(V, z), Trie.size(V, o)): Nat}
        %Equal.sym(Nat, Trie.size(V, Trie.union(~V, ~join, o, Trie.one(V, r, v))), 1n+Trie.size(V, o), Trie.size_union_one(~V, ~join, o, r, v)(g)) :
          {1n+Nat.add(Trie.size(V, z), _) == 1n+1n+Nat.add(Trie.size(V, z), Trie.size(V, o)): Nat}
        %Equal.sym(Nat, Nat.add(Trie.size(V, z), 1n+Trie.size(V, o)), 1n+Nat.add(Trie.size(V, z), Trie.size(V, o)), Nats.Nat.add_succ(Trie.size(V, z), Trie.size(V, o))) :
          {1n+_ == 1n+1n+Nat.add(Trie.size(V, z), Trie.size(V, o)): Nat}
        {==}
