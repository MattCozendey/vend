import Base
import ../../../../shared.bend as Shared

# Cells
# -----
# A cell holds what every holder of a slot agrees on: one value, or many when
# two holders put different values in the same slot. Joining cells is a
# semilattice, so a trie of cells is one too: holders that take in each
# other's cells end with the same ones, and a contradiction is kept, not
# settled by an arbitrary winner. A slot holds a cell or nothing (a
# Maybe<Cell>): a ledger's slot, or an owner's ballot in a quorum.

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

# the slot b does not contradict the value that the slot a holds
def Cell.agrees(
  ~V: Data,
  ~same: V -> V -> Bool,
  a: Maybe<&2, Cell<V>>,
  b: Maybe<&2, Cell<V>>
) -> Bool:
  match a b:
    case Some{One{x}} Some{One{y}}:
      same(x, y)
    case Some{One{x}} Some{Many{}}:
      False{}
    case _ _:
      True{}

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

# an empty slot contradicts nothing
def Cell.agrees_none(
  ~V: Data,
  ~same: V -> V -> Bool,
  a: Maybe<&2, Cell<V>>
) -> {Cell.agrees(~V, ~same, a, None{}) == True{}: Bool}:
  match a:
    case None{}:
      {==}
    case Some{One{x}}:
      {==}
    case Some{Many{}}:
      {==}

# Keeping
# -------

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# a slot keeps itself
def Cell.keeps_refl(
  ~V: Data,
  ~same: V -> V -> Bool,
  ~laws: Shared.Eq.Laws(V, same),
  a: Maybe<&2, Cell<V>>
) -> {Cell.keeps(~V, ~same, a, a) == True{}: Bool}:
  match a:
    case None{}:
      {==}
    case Some{One{x}}:
      Shared.Eq.refl(~V, ~same, laws, x)
    case Some{Many{}}:
      {==}

# an empty slot is kept by any slot
def Cell.none_kept(
  ~V: Data,
  ~same: V -> V -> Bool,
  b: Maybe<&2, Cell<V>>
) -> {Cell.keeps(~V, ~same, None{}, b) == True{}: Bool}:
  {==}

# keeping composes
def Cell.keeps_trans(
  ~V: Data,
  ~same: V -> V -> Bool,
  ~laws: Shared.Eq.Laws(V, same),
  a: Maybe<&2, Cell<V>>,
  b: Maybe<&2, Cell<V>>,
  c: Maybe<&2, Cell<V>>
) -> {
  Cell.keeps(~V, ~same, a, b) == True{}: Bool
} -> {Cell.keeps(~V, ~same, b, c) == True{}: Bool} -> {Cell.keeps(~V, ~same, a, c) == True{}: Bool}:
  match a b c:
    case None{} y w:
      h1 => h2 => {==}
    case Some{One{x}} Some{One{y}} w:
      h1 => h2 =>
        %Equal.sym(V, x, y, Shared.Eq.sound(~V, ~same, laws, x, y)(h1)):
          {Cell.keeps(~V, ~same, Some{One{_}}, w) == True{}: Bool}
        h2
    case Some{Many{}} Some{Many{}} w:
      h1 => h2 => h2
    case Some{One{x}} Some{Many{}} w:
      h1 => h2 => Empty.absurd(
        {Cell.keeps(~V, ~same, Some{One{x}}, w) == True{}: Bool},
        Shared.Bool.false_ne_true(h1)
      )
    case Some{One{x}} None{} w:
      h1 => h2 => Empty.absurd(
        {Cell.keeps(~V, ~same, Some{One{x}}, w) == True{}: Bool},
        Shared.Bool.false_ne_true(h1)
      )
    case Some{Many{}} Some{One{y}} w:
      h1 => h2 => Empty.absurd(
        {Cell.keeps(~V, ~same, Some{Many{}}, w) == True{}: Bool},
        Shared.Bool.false_ne_true(h1)
      )
    case Some{Many{}} None{} w:
      h1 => h2 => Empty.absurd(
        {Cell.keeps(~V, ~same, Some{Many{}}, w) == True{}: Bool},
        Shared.Bool.false_ne_true(h1)
      )

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

# a slot kept as empty was empty
def Cell.keeps_none(
  ~V: Data,
  ~same: V -> V -> Bool,
  a: Maybe<&2, Cell<V>>
) -> {
  Cell.keeps(~V, ~same, a, None{}) == True{}: Bool
} -> {Maybe.is_none(&2, Cell<V>, a) == True{}: Bool}:
  match a:
    case None{}:
      h => {==}
    case Some{One{x}}:
      h => h
    case Some{Many{}}:
      h => h

# a slot that keeps a full slot is full
def Cell.keeps_some(
  ~V: Data,
  ~same: V -> V -> Bool,
  a: Maybe<&2, Cell<V>>,
  b: Maybe<&2, Cell<V>>
) -> {
  Cell.keeps(~V, ~same, a, b) == True{}: Bool
} -> {
  Maybe.is_some(&2, Cell<V>, a) == True{}: Bool
} -> {Maybe.is_some(&2, Cell<V>, b) == True{}: Bool}:
  match a b:
    case None{} y:
      k => h => Empty.absurd(
        {Maybe.is_some(&2, Cell<V>, y) == True{}: Bool},
        Shared.Bool.false_ne_true(h)
      )
    case Some{x} Some{y}:
      k => h => {==}
    case Some{One{x}} None{}:
      k => h => Empty.absurd({False{} == True{}: Bool}, Shared.Bool.false_ne_true(k))
    case Some{Many{}} None{}:
      k => h => Empty.absurd({False{} == True{}: Bool}, Shared.Bool.false_ne_true(k))

# a value read through f (none from no value) stays where the slot is kept
def Cell.read_kept(
  ~V: Data,
  ~W: Data,
  ~same: V -> V -> Bool,
  ~laws: Shared.Eq.Laws(V, same),
  f: Maybe<&2, V> -> Maybe<&2, W>,
  fnone: {f(None{}) == None{}: Maybe<&2, W>},
  a: Maybe<&2, Cell<V>>,
  b: Maybe<&2, Cell<V>>,
  -w: W
) -> {
  Cell.keeps(~V, ~same, a, b) == True{}: Bool
} -> {
  f(Cell.value(V, a)) == Some{w}: Maybe<&2, W>
} -> {f(Cell.value(V, b)) == Some{w}: Maybe<&2, W>}:
  match a:
    case Some{One{x}}:
      k => h =>
        %Equal.sym(
          Maybe<&2, Cell<V>>,
          b,
          Some{One{x}},
          Cell.keeps_value(~V, ~same, ~laws, x, b)(k)
        ):
          {f(Cell.value(V, _)) == Some{w}: Maybe<&2, W>}
        h
    case Some{Many{}}:
      k => h => Empty.absurd(
        {f(Cell.value(V, b)) == Some{w}: Maybe<&2, W>},
        Shared.Maybe.none_ne_some(
          W,
          w,
          Equal.trans(
            Maybe<&2, W>,
            None{},
            f(None{}),
            Some{w},
            Equal.sym(Maybe<&2, W>, f(None{}), None{}, fnone),
            h
          )
        )
      )
    case None{}:
      k => h => Empty.absurd(
        {f(Cell.value(V, b)) == Some{w}: Maybe<&2, W>},
        Shared.Maybe.none_ne_some(
          W,
          w,
          Equal.trans(
            Maybe<&2, W>,
            None{},
            f(None{}),
            Some{w},
            Equal.sym(Maybe<&2, W>, f(None{}), None{}, fnone),
            h
          )
        )
      )

# a slot is kept in its join with one that agrees with it
def Cell.keeps_join(
  ~V: Data,
  ~same: V -> V -> Bool,
  ~laws: Shared.Eq.Laws(V, same),
  a: Maybe<&2, Cell<V>>,
  b: Maybe<&2, Cell<V>>
) -> {
  Cell.agrees(~V, ~same, a, b) == True{}: Bool
} -> {
  Cell.keeps(~V, ~same, a, Shared.Maybe.join(~Cell<V>, ~Cell.join(~V, ~same), a, b)) == True{}: Bool
}:
  match a b:
    case None{} y:
      h => {==}
    case Some{One{x}} None{}:
      h => Shared.Eq.refl(~V, ~same, laws, x)
    case Some{One{+x}} Some{One{y}}:
      h =>
        %Equal.sym(Bool, same(x, y), True{}, h):
          {
            Cell.keeps(
              ~V,
              ~same,
              Some{One{x}},
              Some{Bool.pick(Cell<V>, _, One{x}, Many{})}
            )
              == True{}: Bool
          }
        Shared.Eq.refl(~V, ~same, laws, x)
    case Some{One{x}} Some{Many{}}:
      h => Empty.absurd(
        {Cell.keeps(~V, ~same, Some{One{x}}, Some{Many{}}) == True{}: Bool},
        Shared.Bool.false_ne_true(h)
      )
    case Some{Many{}} None{}:
      h => {==}
    case Some{Many{}} Some{y}:
      h => {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
