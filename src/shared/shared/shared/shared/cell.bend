import Base
import ./shared.bend as Shared

# Cells
# -----
# A cell holds what every source of a slot agrees on: one value, or many when
# two sources put different values in the same slot. Joining cells is a
# semilattice, so the order of the sources does not change the cell, and a
# contradiction is kept, not settled by an arbitrary winner. A slot holds a
# cell or nothing (a Maybe<Cell>): what the ballots of a voter at a place
# cast, or a voter's ballot in a quorum.

# one value, or the mark that two values met
type Cell<-V: Data> is Data:
  One{value: V}
  Many{}

# what a and b agree on
def Cell.join(~V: Data, ~same: V -> V -> Bool, a: Cell<V>, b: Cell<V>) -> Cell<V>:
  match a b:
    case One{+x} One{y}:
      Bool.pick(Cell<V>, same(x, y), One{x}, Many{})
    case One{x} Many{}:
      Many{}
    case Many{} y:
      Many{}

# the value of a slot, when every holder agrees on it
def Cell.value(-V: Data, m: Maybe<&2, Cell<V>>) -> Maybe<&2, V>:
  match m:
    case Some{One{e}}:
      Some{e}
    case _:
      None{}

# a and b hold the same, as same calls values the same
def Cell.is_eq(~V: Data, ~same: V -> V -> Bool, a: Cell<V>, b: Cell<V>) -> Bool:
  match a b:
    case One{x} One{y}:
      same(x, y)
    case Many{} Many{}:
      True{}
    case _ _:
      False{}

# the slot b keeps what the slot a holds: a value stays the value, many stays
# many, and only an empty slot may fill
def Cell.keeps(
  ~V: Data,
  ~same: V -> V -> Bool,
  a: Maybe<&2, Cell<V>>,
  b: Maybe<&2, Cell<V>>
) -> Bool:
  match a b:
    case None{} y:
      True{}
    case Some{One{x}} Some{One{y}}:
      same(x, y)
    case Some{Many{}} Some{Many{}}:
      True{}
    case Some{c} _:
      False{}

# Laws
# ----
# Each law asks of same only its laws (Shared.Eq.Laws).

# a cell joined with itself is itself
law Cell.join_idem:
  for ~V: Data
  for ~same: V -> V -> Bool
  for ~laws: Shared.Eq.Laws(V, same)
  for a: Cell<V>
  {Cell.join(~V, ~same, a, a) == a: Cell<V>}

def Cell.join_idem(ty, same, laws, a):
  match a:
    case One{x}:
      %Equal.sym(
        Bool,
        same(x, x),
        True{},
        Shared.Eq.refl(~ty, ~same, laws, x)
      ): {Bool.pick(Cell<ty>, _, One{x}, Many{}) == One{x}: Cell<ty>}
      {==}
    case Many{}:
      {==}

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Cell.join_comm once same(x, y) is known (held)
def Cell.join_comm.at(
  ~V: Data,
  ~same: V -> V -> Bool,
  ~laws: Shared.Eq.Laws(V, same),
  held: Bool,
  +x: V,
  y: V,
  e: {same(x, y) == held: Bool}
) -> {
  Bool.pick(
    Cell<V>,
    held,
    One{x},
    Many{}
  )
    == Bool.pick(Cell<V>, same(y, x), One{y}, Many{}): Cell<V>
}:
  match held:
    case True{}:
      %Shared.Eq.sound(
        ~V,
        ~same,
        laws,
        x
      )(y)(e): {One{x} == Bool.pick(Cell<V>, same(_, x), One{_}, Many{}): Cell<V>}
      %Equal.sym(
        Bool,
        same(x, x),
        True{},
        Shared.Eq.refl(~V, ~same, laws, x)
      ): {One{x} == Bool.pick(Cell<V>, _, One{x}, Many{}): Cell<V>}
      {==}
    case False{}:
      %Equal.sym(Bool, same(y, x), False{}, Shared.Eq.ne_flip(~V, ~same, ~laws, x, y, e)):
        {Many{} == Bool.pick(Cell<V>, _, One{y}, Many{}): Cell<V>}
      {==}

# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# a join is the same either way round
law Cell.join_comm:
  for ~V: Data
  for ~same: V -> V -> Bool
  for ~laws: Shared.Eq.Laws(V, same)
  for a: Cell<V>
  for b: Cell<V>
  {Cell.join(~V, ~same, a, b) == Cell.join(~V, ~same, b, a): Cell<V>}

def Cell.join_comm(ty, same, laws, a, b):
  match a b:
    case One{+x} One{+y}:
      Cell.join_comm.at(~ty, ~same, ~laws, same(x, y), x, y, {==})
    case One{x} Many{}:
      {==}
    case Many{} One{y}:
      {==}
    case Many{} Many{}:
      {==}

# a cell that met many is many, whatever x and y were (held)
def Cell.join_assoc.many(
  ~V: Data,
  ~same: V -> V -> Bool,
  held: Bool,
  x: V
) -> {Cell.join(~V, ~same, Bool.pick(Cell<V>, held, One{x}, Many{}), Many{}) == Many{}: Cell<V>}:
  match held:
    case True{}:
      {==}
    case False{}:
      {==}

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Cell.join_assoc for three values, once same(x, y) (xy) and same(y, z) (yz)
# are known
def Cell.join_assoc.at(
  ~V: Data,
  ~same: V -> V -> Bool,
  ~laws: Shared.Eq.Laws(V, same),
  xy: Bool,
  yz: Bool,
  x: V,
  y: V,
  z: V,
  e1: {same(x, y) == xy: Bool},
  e2: {same(y, z) == yz: Bool}
) -> {
  Cell.join(
    ~V,
    ~same,
    Bool.pick(Cell<V>, xy, One{x}, Many{}),
    One{z}
  )
    == Cell.join(~V, ~same, One{x}, Bool.pick(Cell<V>, yz, One{y}, Many{})): Cell<V>
}:
  match xy yz:
    case True{} True{}:
      %Shared.Eq.sound(~V, ~same, laws, y)(z)(e2):
        {
          Cell.join(
            ~V,
            ~same,
            Bool.pick(Cell<V>, True{}, One{x}, Many{}),
            One{_}
          )
            == Cell.join(~V, ~same, One{x}, Bool.pick(Cell<V>, True{}, One{y}, Many{})): Cell<V>
        }
      {==}
    case True{} False{}:
      %Equal.sym(V, x, y, Shared.Eq.sound(~V, ~same, laws, x)(y)(e1)):
        {
          Cell.join(
            ~V,
            ~same,
            Bool.pick(Cell<V>, True{}, One{_}, Many{}),
            One{z}
          )
            == Cell.join(~V, ~same, One{_}, Bool.pick(Cell<V>, False{}, One{y}, Many{})): Cell<V>
        }
      %Equal.sym(
        Bool,
        same(y, z),
        False{},
        e2
      ): {Bool.pick(Cell<V>, _, One{y}, Many{}) == Many{}: Cell<V>}
      {==}
    case False{} True{}:
      %Equal.sym(
        Bool,
        same(x, y),
        False{},
        e1
      ): {Many{} == Bool.pick(Cell<V>, _, One{x}, Many{}): Cell<V>}
      {==}
    case False{} False{}:
      {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# a join groups either way
law Cell.join_assoc:
  for ~V: Data
  for ~same: V -> V -> Bool
  for ~laws: Shared.Eq.Laws(V, same)
  for a: Cell<V>
  for b: Cell<V>
  for c: Cell<V>
  {
    Cell.join(
      ~V,
      ~same,
      Cell.join(~V, ~same, a, b),
      c
    )
      == Cell.join(~V, ~same, a, Cell.join(~V, ~same, b, c)): Cell<V>
  }

def Cell.join_assoc(ty, same, laws, a, b, c):
  match a b c:
    case Many{} y w:
      {==}
    case One{x} Many{} w:
      {==}
    case One{+x} One{+y} Many{}:
      Cell.join_assoc.many(~ty, ~same, same(x, y), x)
    case One{+x} One{+y} One{+z}:
      Cell.join_assoc.at(~ty, ~same, ~laws, same(x, y), same(y, z), x, y, z, {==}, {==})

# Cell.is_eq is True only for equal cells
law Cell.is_eq_sound:
  for ~V: Data
  for ~same: V -> V -> Bool
  for ~laws: Shared.Eq.Laws(V, same)
  for a: Cell<V>
  for b: Cell<V>
  {Cell.is_eq(~V, ~same, a, b) == True{}: Bool} -> {a == b: Cell<V>}

def Cell.is_eq_sound(ty, same, laws, a, b):
  match a b:
    case One{x} One{y}:
      h =>
        %Shared.Eq.sound(~ty, ~same, laws, x)(y)(h): {One{x} == One{_}: Cell<ty>}
        {==}
    case One{x} Many{}:
      h => Empty.absurd({One{x} == Many{}: Cell<ty>}, Shared.Bool.false_ne_true(h))
    case Many{} One{y}:
      h => Empty.absurd({Many{} == One{y}: Cell<ty>}, Shared.Bool.false_ne_true(h))
    case Many{} Many{}:
      h => {==}

# Cell.is_eq is True for a cell and itself
def Cell.is_eq_refl(
  ~V: Data,
  ~same: V -> V -> Bool,
  ~laws: Shared.Eq.Laws(V, same),
  a: Cell<V>
) -> {Cell.is_eq(~V, ~same, a, a) == True{}: Bool}:
  match a:
    case One{x}:
      Shared.Eq.refl(~V, ~same, laws, x)
    case Many{}:
      {==}

# Keeping
# -------

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# a slot that keeps the value x holds x
def Cell.keeps_value(
  ~V: Data,
  ~same: V -> V -> Bool,
  ~laws: Shared.Eq.Laws(V, same),
  x: V,
  b: Maybe<&2, Cell<V>>
) -> {
  Cell.keeps(~V, ~same, Some{One{x}}, b) == True{}: Bool
} -> {b == Some{One{x}}: Maybe<&2, Cell<V>>}:
  match b:
    case Some{One{z}}:
      h =>
        %Equal.sym(
          V,
          x,
          z,
          Shared.Eq.sound(~V, ~same, laws, x, z)(h)
        ): {Some{One{z}} == Some{One{_}}: Maybe<&2, Cell<V>>}
        {==}
    case Some{Many{}}:
      h => Empty.absurd(
        {Some{Many{}} == Some{One{x}}: Maybe<&2, Cell<V>>},
        Shared.Bool.false_ne_true(h)
      )
    case None{}:
      h => Empty.absurd({None{} == Some{One{x}}: Maybe<&2, Cell<V>>}, Shared.Bool.false_ne_true(h))

# Takes
# -----
# A holder that takes a slot in keeps its own cell where it holds one.
