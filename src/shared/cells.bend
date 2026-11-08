import Base
import ./bools.bend as Bools
import ./shared.bend as Shared
import ./tries.bend as Tries

# Cells
# -----
# A cell holds what every holder of a slot agrees on: one value, or Many when
# two holders put different values in the same slot. Joining cells is a
# semilattice, so a trie of cells is one too (Trie.union_comm and the rest):
# holders that take in each other's cells end with the same ones, and a
# contradiction is kept, not settled by an arbitrary winner.

# one value, or the mark that two values met
type Cell<-V: Data> is Data:
  One{value: V}
  Many{}

# One x, when x and y are the same (held), else Many
def Cell.join.if(-V: Data, held: Bool, x: V) -> Cell<V>:
  match held:
    case True{}:
      One{x}
    case False{}:
      Many{}

# what a and b agree on
def Cell.join(~V: Data, ~same: V -> V -> Bool, a: Cell<V>, b: Cell<V>) -> Cell<V>:
  match a b:
    case One{+x} One{y}:
      Cell.join.if(V, same(x, y), x)
    case One{x} Many{}:
      Many{}
    case Many{} y:
      Many{}

# Laws
# ----
# Each law asks of same only that it is True for a value and itself (refl),
# and only for equal values (sound).

# a cell joined with itself is itself
law Cell.join_idem:
  for ~V: Data
  for ~same: V -> V -> Bool
  for ~refl: @x: V -> {same(x, x) == True{}: Bool}
  for a: Cell<V>
  {Cell.join(~V, ~same, a, a) == a: Cell<V>}

def Cell.join_idem(V, same, refl, a):
  match a:
    case One{+x}:
      %Equal.sym(Bool, same(x, x), True{}, refl(x)) : {Cell.join.if(V, _, x) == One{x}: Cell<V>}
      {==}
    case Many{}:
      {==}

# Cell.join_comm once same(y, x) is known (back)
def Cell.join_comm.back(
  ~V: Data,
  ~same: V -> V -> Bool,
  ~refl: @x: V -> {same(x, x) == True{}: Bool},
  ~sound: @x: V -> @y: V -> {same(x, y) == True{}: Bool} -> {x == y: V},
  back: Bool,
  +x: V,
  +y: V,
  no: {same(x, y) == False{}: Bool},
  e: {same(y, x) == back: Bool}
) -> {Many{} == Cell.join.if(V, back, y): Cell<V>}:
  match back:
    case False{}:
      {==}
    case True{}:
      Empty.absurd(
        {Many{} == One{y}: Cell<V>},
        Shared.Bool.false_ne_true(
          Equal.trans(
            Bool,
            False{},
            same(x, y),
            True{},
            Equal.sym(Bool, same(x, y), False{}, no),
            Equal.trans(
              Bool,
              same(x, y),
              same(x, x),
              True{},
              Equal.cong(V, Bool, z => same(x, z), y, x, sound(y)(x)(e)),
              refl(x)
            )
          )
        )
      )

# Cell.join_comm once same(x, y) is known (held)
def Cell.join_comm.at(
  ~V: Data,
  ~same: V -> V -> Bool,
  ~refl: @x: V -> {same(x, x) == True{}: Bool},
  ~sound: @x: V -> @y: V -> {same(x, y) == True{}: Bool} -> {x == y: V},
  held: Bool,
  +x: V,
  +y: V,
  e: {same(x, y) == held: Bool}
) -> {Cell.join.if(V, held, x) == Cell.join.if(V, same(y, x), y): Cell<V>}:
  match held:
    case True{}:
      %sound(x)(y)(e) : {One{x} == Cell.join.if(V, same(_, x), _): Cell<V>}
      %Equal.sym(Bool, same(x, x), True{}, refl(x)) : {One{x} == Cell.join.if(V, _, x): Cell<V>}
      {==}
    case False{}:
      Cell.join_comm.back(~V, ~same, ~refl, ~sound, same(y, x), x, y, e, {==})

# a join is the same either way round
law Cell.join_comm:
  for ~V: Data
  for ~same: V -> V -> Bool
  for ~refl: @x: V -> {same(x, x) == True{}: Bool}
  for ~sound: @x: V -> @y: V -> {same(x, y) == True{}: Bool} -> {x == y: V}
  for a: Cell<V>
  for b: Cell<V>
  {Cell.join(~V, ~same, a, b) == Cell.join(~V, ~same, b, a): Cell<V>}

def Cell.join_comm(V, same, refl, sound, a, b):
  match a b:
    case One{+x} One{+y}:
      Cell.join_comm.at(~V, ~same, ~refl, ~sound, same(x, y), x, y, {==})
    case One{x} Many{}:
      {==}
    case Many{} One{y}:
      {==}
    case Many{} Many{}:
      {==}

# a cell that met Many is Many, whatever x and y were (held)
def Cell.join_assoc.many(
  ~V: Data,
  ~same: V -> V -> Bool,
  held: Bool,
  x: V
) -> {Cell.join(~V, ~same, Cell.join.if(V, held, x), Many{}) == Many{}: Cell<V>}:
  match held:
    case True{}:
      {==}
    case False{}:
      {==}

# Cell.join_assoc for three values, once same(x, y) (xy) and same(y, z) (yz)
# are known
def Cell.join_assoc.at(
  ~V: Data,
  ~same: V -> V -> Bool,
  ~sound: @x: V -> @y: V -> {same(x, y) == True{}: Bool} -> {x == y: V},
  xy: Bool,
  yz: Bool,
  +x: V,
  +y: V,
  +z: V,
  e1: {same(x, y) == xy: Bool},
  e2: {same(y, z) == yz: Bool}
) -> {
  Cell.join(~V, ~same, Cell.join.if(V, xy, x), One{z})
    == Cell.join(~V, ~same, One{x}, Cell.join.if(V, yz, y)): Cell<V>
}:
  match xy yz:
    case True{} True{}:
      %sound(y)(z)(e2) :
        {
          Cell.join(~V, ~same, Cell.join.if(V, True{}, x), One{_})
            == Cell.join(~V, ~same, One{x}, Cell.join.if(V, True{}, y)): Cell<V>
        }
      {==}
    case True{} False{}:
      %Equal.sym(V, x, y, sound(x)(y)(e1)) :
        {
          Cell.join(~V, ~same, Cell.join.if(V, True{}, _), One{z})
            == Cell.join(~V, ~same, One{_}, Cell.join.if(V, False{}, y)): Cell<V>
        }
      %Equal.sym(Bool, same(y, z), False{}, e2) : {Cell.join.if(V, _, y) == Many{}: Cell<V>}
      {==}
    case False{} True{}:
      %Equal.sym(Bool, same(x, y), False{}, e1) : {Many{} == Cell.join.if(V, _, x): Cell<V>}
      {==}
    case False{} False{}:
      {==}

# a join groups either way
law Cell.join_assoc:
  for ~V: Data
  for ~same: V -> V -> Bool
  for ~refl: @x: V -> {same(x, x) == True{}: Bool}
  for ~sound: @x: V -> @y: V -> {same(x, y) == True{}: Bool} -> {x == y: V}
  for a: Cell<V>
  for b: Cell<V>
  for c: Cell<V>
  {
    Cell.join(~V, ~same, Cell.join(~V, ~same, a, b), c)
      == Cell.join(~V, ~same, a, Cell.join(~V, ~same, b, c)): Cell<V>
  }

def Cell.join_assoc(V, same, refl, sound, a, b, c):
  match a b c:
    case Many{} y w:
      {==}
    case One{x} Many{} w:
      {==}
    case One{+x} One{+y} Many{}:
      Cell.join_assoc.many(~V, ~same, same(x, y), x)
    case One{+x} One{+y} One{+z}:
      Cell.join_assoc.at(~V, ~same, ~sound, same(x, y), same(y, z), x, y, z, {==}, {==})

# a and b hold the same, as same calls values the same
def Cell.same(~V: Data, ~same: V -> V -> Bool, a: Cell<V>, b: Cell<V>) -> Bool:
  match a b:
    case One{x} One{y}:
      same(x, y)
    case Many{} Many{}:
      True{}
    case _ _:
      False{}

# Cell.same is True only for equal cells
law Cell.same_sound:
  for ~V: Data
  for ~same: V -> V -> Bool
  for ~sound: @x: V -> @y: V -> {same(x, y) == True{}: Bool} -> {x == y: V}
  for a: Cell<V>
  for b: Cell<V>
  {Cell.same(~V, ~same, a, b) == True{}: Bool} -> {a == b: Cell<V>}

def Cell.same_sound(V, same, sound, a, b):
  match a b:
    case One{+x} One{+y}:
      h =>
        %sound(x)(y)(h) : {One{x} == One{_}: Cell<V>}
        {==}
    case One{x} Many{}:
      h => Empty.absurd({One{x} == Many{}: Cell<V>}, Shared.Bool.false_ne_true(h))
    case Many{} One{y}:
      h => Empty.absurd({Many{} == One{y}: Cell<V>}, Shared.Bool.false_ne_true(h))
    case Many{} Many{}:
      h => {==}

# Agreement
# ---------
# t agrees with s when no cell of t contradicts a value that s holds: then a
# holder of s that takes in t keeps every value it held.

# b does not contradict the value that a holds
def Cell.agrees.here(~V: Data, ~same: V -> V -> Bool, a: Maybe<&2, Cell<V>>, b: Maybe<&2, Cell<V>>) -> Bool:
  match a b:
    case Some{One{x}} Some{One{y}}:
      same(x, y)
    case Some{One{x}} Some{Many{}}:
      False{}
    case _ _:
      True{}

# no cell of t contradicts a value of s
def Cell.agrees(~V: Data, ~same: V -> V -> Bool, s: Tries.Trie<Cell<V>>, t: Tries.Trie<Cell<V>>) -> Bool:
  match s t:
    case Tries.Tip{} y:
      True{}
    case Tries.Bin{h, z, o} Tries.Tip{}:
      True{}
    case Tries.Bin{h1, z1, o1} Tries.Bin{h2, z2, o2}:
      Bool.and(
        Cell.agrees.here(~V, ~same, h1, h2),
        Bool.and(Cell.agrees(~V, ~same, z1, z2), Cell.agrees(~V, ~same, o1, o2))
      )

# a cell that is here, whether One or not
def Cell.is_one(-V: Data, m: Maybe<&2, Cell<V>>) -> Bool:
  match m:
    case Some{One{x}}:
      True{}
    case _:
      False{}

# both sides of an "and" are true, so it is
def Cell.and_true(a: Bool, b: Bool) -> {a == True{}: Bool} -> {b == True{}: Bool} -> {Bool.and(a, b) == True{}: Bool}:
  match a:
    case True{}:
      ha => hb => hb
    case False{}:
      ha => hb => Empty.absurd({False{} == True{}: Bool}, Shared.Bool.false_ne_true(ha))

# the value v that a holds is kept when b agrees with it
def Cell.kept.here(
  ~V: Data,
  ~same: V -> V -> Bool,
  ~sound: @x: V -> @y: V -> {same(x, y) == True{}: Bool} -> {x == y: V},
  a: Maybe<&2, Cell<V>>,
  b: Maybe<&2, Cell<V>>,
  -v: V
) -> {Cell.agrees.here(~V, ~same, a, b) == True{}: Bool} -> {a == Some{One{v}}: Maybe<&2, Cell<V>>} -> {
  Tries.Trie.pick(~Cell<V>, ~Cell.join(~V, ~same), a, b) == Some{One{v}}: Maybe<&2, Cell<V>>
}:
  match a b:
    case None{} y:
      h => g => Empty.absurd(
        {Tries.Trie.pick(~Cell<V>, ~Cell.join(~V, ~same), None{}, y) == Some{One{v}}: Maybe<&2, Cell<V>>},
        Shared.Bool.false_ne_true(Equal.cong(Maybe<&2, Cell<V>>, Bool, m => Cell.is_one(V, m), None{}, Some{One{v}}, g))
      )
    case Some{Many{}} y:
      h => g => Empty.absurd(
        {Tries.Trie.pick(~Cell<V>, ~Cell.join(~V, ~same), Some{Many{}}, y) == Some{One{v}}: Maybe<&2, Cell<V>>},
        Shared.Bool.false_ne_true(Equal.cong(Maybe<&2, Cell<V>>, Bool, m => Cell.is_one(V, m), Some{Many{}}, Some{One{v}}, g))
      )
    case Some{One{x}} None{}:
      h => g => g
    case Some{One{+x}} Some{One{+y}}:
      h => g =>
        %Equal.sym(Bool, same(x, y), True{}, h) : {Some{Cell.join.if(V, _, x)} == Some{One{v}}: Maybe<&2, Cell<V>>}
        g
    case Some{One{x}} Some{Many{}}:
      h => g => Empty.absurd(
        {Some{Many{}} == Some{One{v}}: Maybe<&2, Cell<V>>},
        Shared.Bool.false_ne_true(h)
      )

# a value that s holds is kept in s and t, when t agrees with s
law Cell.agrees_kept:
  for ~V: Data
  for ~same: V -> V -> Bool
  for ~sound: @x: V -> @y: V -> {same(x, y) == True{}: Bool} -> {x == y: V}
  for s: Tries.Trie<Cell<V>>
  for t: Tries.Trie<Cell<V>>
  for k: List<&2, Bool>
  for -v: V
  {Cell.agrees(~V, ~same, s, t) == True{}: Bool}
    -> {Tries.Trie.get(Cell<V>, s, k) == Some{One{v}}: Maybe<&2, Cell<V>>}
    -> {Tries.Trie.get(Cell<V>, Tries.Trie.union(~Cell<V>, ~Cell.join(~V, ~same), s, t), k) == Some{One{v}}: Maybe<&2, Cell<V>>}

def Cell.agrees_kept(V, same, sound, s, t, k, v):
  match s t k:
    case Tries.Tip{} y q:
      a => g => Empty.absurd(
        {Tries.Trie.get(Cell<V>, y, q) == Some{One{v}}: Maybe<&2, Cell<V>>},
        Shared.Bool.false_ne_true(Equal.cong(Maybe<&2, Cell<V>>, Bool, m => Cell.is_one(V, m), None{}, Some{One{v}}, g))
      )
    case Tries.Bin{h, z, o} Tries.Tip{} q:
      a => g => g
    case Tries.Bin{+h1, +z1, +o1} Tries.Bin{+h2, +z2, +o2} Nil{}:
      +a => g => Cell.kept.here(~V, ~same, ~sound, h1, h2, v)(
        Bools.Bool.and_true_left(
          Cell.agrees.here(~V, ~same, h1, h2),
          Bool.and(Cell.agrees(~V, ~same, z1, z2), Cell.agrees(~V, ~same, o1, o2))
        )(a)
      )(g)
    case Tries.Bin{+h1, +z1, +o1} Tries.Bin{+h2, +z2, +o2} Con{False{}, r}:
      +a => g => Cell.agrees_kept(~V, ~same, ~sound, z1, z2, r, v)(
        Bools.Bool.and_true_left(
          Cell.agrees(~V, ~same, z1, z2),
          Cell.agrees(~V, ~same, o1, o2)
        )(
          Bools.Bool.and_true_right(
            Cell.agrees.here(~V, ~same, h1, h2),
            Bool.and(Cell.agrees(~V, ~same, z1, z2), Cell.agrees(~V, ~same, o1, o2))
          )(a)
        )
      )(g)
    case Tries.Bin{+h1, +z1, +o1} Tries.Bin{+h2, +z2, +o2} Con{True{}, r}:
      +a => g => Cell.agrees_kept(~V, ~same, ~sound, o1, o2, r, v)(
        Bools.Bool.and_true_right(
          Cell.agrees(~V, ~same, z1, z2),
          Cell.agrees(~V, ~same, o1, o2)
        )(
          Bools.Bool.and_true_right(
            Cell.agrees.here(~V, ~same, h1, h2),
            Bool.and(Cell.agrees(~V, ~same, z1, z2), Cell.agrees(~V, ~same, o1, o2))
          )(a)
        )
      )(g)

# nothing contradicts a value of s
def Cell.agrees_tip(~V: Data, ~same: V -> V -> Bool, s: Tries.Trie<Cell<V>>) -> {Cell.agrees(~V, ~same, s, Tries.Tip{}) == True{}: Bool}:
  match s:
    case Tries.Tip{}:
      {==}
    case Tries.Bin{h, z, o}:
      {==}

# nothing at a key does not contradict what a holds there
def Cell.agrees_none(~V: Data, ~same: V -> V -> Bool, a: Maybe<&2, Cell<V>>) -> {Cell.agrees.here(~V, ~same, a, None{}) == True{}: Bool}:
  match a:
    case None{}:
      {==}
    case Some{One{x}}:
      {==}
    case Some{Many{}}:
      {==}

# one cell at a key that s does not hold agrees with s
law Cell.agrees_one:
  for ~V: Data
  for ~same: V -> V -> Bool
  for s: Tries.Trie<Cell<V>>
  for k: List<&2, Bool>
  for +x: Cell<V>
  {Tries.Trie.get(Cell<V>, s, k) == None{}: Maybe<&2, Cell<V>>}
    -> {Cell.agrees(~V, ~same, s, Tries.Trie.one(Cell<V>, k, x)) == True{}: Bool}

def Cell.agrees_one(V, same, s, k, x):
  match s k:
    case Tries.Tip{} q:
      g => {==}
    case Tries.Bin{+h, +z, +o} Nil{}:
      g =>
        %Equal.sym(Maybe<&2, Cell<V>>, h, None{}, g) : {Bool.and(Cell.agrees.here(~V, ~same, _, Some{x}), Bool.and(Cell.agrees(~V, ~same, z, Tries.Tip{}), Cell.agrees(~V, ~same, o, Tries.Tip{}))) == True{}: Bool}
        %Equal.sym(Bool, Cell.agrees(~V, ~same, z, Tries.Tip{}), True{}, Cell.agrees_tip(~V, ~same, z)) :
          {Bool.and(_, Cell.agrees(~V, ~same, o, Tries.Tip{})) == True{}: Bool}
        Cell.agrees_tip(~V, ~same, o)
    case Tries.Bin{+h, +z, +o} Con{False{}, +r}:
      g => Cell.and_true(
        Cell.agrees.here(~V, ~same, h, None{}),
        Bool.and(Cell.agrees(~V, ~same, z, Tries.Trie.one(Cell<V>, r, x)), Cell.agrees(~V, ~same, o, Tries.Tip{}))
      )(Cell.agrees_none(~V, ~same, h))(
        Cell.and_true(
          Cell.agrees(~V, ~same, z, Tries.Trie.one(Cell<V>, r, x)),
          Cell.agrees(~V, ~same, o, Tries.Tip{})
        )(Cell.agrees_one(~V, ~same, z, r, x)(g))(Cell.agrees_tip(~V, ~same, o))
      )
    case Tries.Bin{+h, +z, +o} Con{True{}, +r}:
      g => Cell.and_true(
        Cell.agrees.here(~V, ~same, h, None{}),
        Bool.and(Cell.agrees(~V, ~same, z, Tries.Tip{}), Cell.agrees(~V, ~same, o, Tries.Trie.one(Cell<V>, r, x)))
      )(Cell.agrees_none(~V, ~same, h))(
        Cell.and_true(
          Cell.agrees(~V, ~same, z, Tries.Tip{}),
          Cell.agrees(~V, ~same, o, Tries.Trie.one(Cell<V>, r, x))
        )(Cell.agrees_tip(~V, ~same, z))(Cell.agrees_one(~V, ~same, o, r, x)(g))
      )
