import Base
import ./shared.bend as Shared

# Three-way choices
# -----------------
# Two changes x and y of one base b: take y when x is b, take x when y is b or
# both made the same change, else both changed. A merge of anything chooses
# so, and only both changes need the merge of a format.

# the side that a merge of x and y, two changes of b, takes
type Side is Data:
  Side.Theirs{}
  Side.Ours{}
  Side.Both{}

# the side that a merge of x and y, two changes of b, takes, as same compares
def Side.of(~A: Data, ~same: A -> A -> Bool, +b: A, +x: A, +y: A) -> Side:
  Shared.Bool.when(
    Side,
    same(x, b),
    u => Side.Theirs{},
    u => Shared.Bool.when(Side, Bool.or(same(y, b), same(x, y)), v => Side.Ours{}, v => Side.Both{})
  )

# the change that the side s takes of x and y (none: both)
def Side.take(-A: Data, s: Side, x: A, y: A) -> Maybe<&2, A>:
  match s:
    case Side.Theirs{}:
      Some{y}
    case Side.Ours{}:
      Some{x}
    case Side.Both{}:
      None{}

# the side s is Both
def Side.is_both(s: Side) -> Bool:
  match s:
    case Side.Both{}:
      True{}
    case _:
      False{}

# Laws
# ----

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Side.keeps_changes once it is known whether x is b (p) and whether y is b or
# x is y (q)
def Side.keeps_changes.at(
  ~A: Data,
  ~same: A -> A -> Bool,
  ~laws: Shared.Eq.Laws(A, same),
  +b: A,
  +x: A,
  +y: A,
  z: A,
  p: Bool,
  ep: {same(x, b) == p: Bool},
  q: Bool,
  eq: {Bool.or(same(y, b), same(x, y)) == q: Bool}
) -> {
  Side.take(
    A,
    Shared.Bool.when(
      Side,
      p,
      u => Side.Theirs{},
      u => Shared.Bool.when(Side, q, v => Side.Ours{}, v => Side.Both{})
    ),
    x,
    y
  )
    == Some{z}: Maybe<&2, A>
}
  -> ({same(x, b) == False{}: Bool} -> {z == x: A})
  & ({same(y, b) == False{}: Bool} -> {z == y: A}):
  match p q:
    case True{} q1:
      +h => (
        n => Empty.absurd(
          {z == x: A},
          Shared.Bool.true_ne_false(Equal.trans(Bool, True{}, same(x, b), False{}, Equal.sym(Bool, same(x, b), True{}, ep), n))
        ),
        m => Equal.sym(A, y, z, Shared.Maybe.some_inj(A, y, z, h))
      )
    case False{} True{}:
      +h => (
        n => Equal.sym(A, x, z, Shared.Maybe.some_inj(A, x, z, h)),
        m =>
          %Shared.Eq.sound(~A, ~same, laws, x, y)(
            %m: {Bool.or(_, same(x, y)) == True{}: Bool}
            eq
          ): {z == _: A}
          Equal.sym(A, x, z, Shared.Maybe.some_inj(A, x, z, h))
      )
    case False{} False{}:
      h => Empty.absurd(
        ({same(x, b) == False{}: Bool} -> {z == x: A}) & ({same(y, b) == False{}: Bool} -> {z == y: A}),
        Shared.Maybe.none_ne_some(A, z, h)
      )

# Side.both_changed once it is known whether x is b (p) and whether y is b or
# x is y (q)
def Side.both_changed.at(
  ~A: Data,
  ~same: A -> A -> Bool,
  +b: A,
  +x: A,
  +y: A,
  p: Bool,
  ep: {same(x, b) == p: Bool},
  q: Bool,
  eq: {Bool.or(same(y, b), same(x, y)) == q: Bool}
) -> {
  Shared.Bool.when(
    Side,
    p,
    u => Side.Theirs{},
    u => Shared.Bool.when(Side, q, v => Side.Ours{}, v => Side.Both{})
  )
    == Side.Both{}: Side
} -> {Bool.or(same(x, b), Bool.or(same(y, b), same(x, y))) == False{}: Bool}:
  match p q:
    case True{} q1:
      h => Empty.absurd(
        {Bool.or(same(x, b), Bool.or(same(y, b), same(x, y))) == False{}: Bool},
        Shared.Bool.false_ne_true(Equal.cong(Side, Bool, Side.is_both, Side.Theirs{}, Side.Both{}, h))
      )
    case False{} True{}:
      h => Empty.absurd(
        {Bool.or(same(x, b), Bool.or(same(y, b), same(x, y))) == False{}: Bool},
        Shared.Bool.false_ne_true(Equal.cong(Side, Bool, Side.is_both, Side.Ours{}, Side.Both{}, h))
      )
    case False{} False{}:
      h =>
        %Equal.sym(Bool, same(x, b), False{}, ep): {Bool.or(_, Bool.or(same(y, b), same(x, y))) == False{}: Bool}
        eq
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# a choice loses no change that only one side made: what it takes is each
# change that differs from the base
law Side.keeps_changes:
  for ~A: Data
  for ~same: A -> A -> Bool
  for ~laws: Shared.Eq.Laws(A, same)
  for +b: A
  for +x: A
  for +y: A
  for z: A
  {Side.take(A, Side.of(~A, ~same, b, x, y), x, y) == Some{z}: Maybe<&2, A>}
    -> ({same(x, b) == False{}: Bool} -> {z == x: A})
    & ({same(y, b) == False{}: Bool} -> {z == y: A})

def Side.keeps_changes(ty, same, laws, b, x, y, z):
  Side.keeps_changes.at(~ty, ~same, ~laws, b, x, y, z, same(x, b), {==}, Bool.or(same(y, b), same(x, y)), {==})

# and it leaves both only when both changed, and differently
law Side.both_changed:
  for ~A: Data
  for ~same: A -> A -> Bool
  for +b: A
  for +x: A
  for +y: A
  {Side.of(~A, ~same, b, x, y) == Side.Both{}: Side}
    -> {Bool.or(same(x, b), Bool.or(same(y, b), same(x, y))) == False{}: Bool}

def Side.both_changed(ty, same, b, x, y):
  Side.both_changed.at(~ty, ~same, b, x, y, same(x, b), {==}, Bool.or(same(y, b), same(x, y)), {==})
