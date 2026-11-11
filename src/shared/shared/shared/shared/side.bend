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

# and it leaves both only when both changed, and differently
law Side.both_changed:
  for ~A: Data
  for ~same: A -> A -> Bool
  for +b: A
  for +x: A
  for +y: A
  {Side.of(~A, ~same, b, x, y) == Side.Both{}: Side}
    -> {Bool.or(same(x, b), Bool.or(same(y, b), same(x, y))) == False{}: Bool}
