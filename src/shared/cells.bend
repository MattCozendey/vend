import Base
import ./shared.bend as Shared

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
