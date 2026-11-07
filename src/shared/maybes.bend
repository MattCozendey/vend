import Base
import ./shared.bend as Shared

# what holds when m is None
def Maybe.IsNone(-A: Data, m: Maybe<&2, A>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

# no None equals a Some
def Maybe.none_ne_some(-A: Data, -x: A, e: {None{} == Some{x}: Maybe<&2, A>}) -> Empty:
  %e: Maybe.IsNone(A, _)
  Unit{}

# Some is one to one
def Maybe.some_inj(-A: Data, -x: A, -y: A, e: {Some{x} == Some{y}: Maybe<&2, A>}) -> {x == y: A}:
  Equal.cong(Maybe<&2, A>, A, m => Maybe.default(&2, A, m, x), Some{x}, Some{y}, e)

# a and b are both empty, or hold values that eq calls the same
def Maybe.same(~A: Data, ~eq: A -> A -> Bool, a: Maybe<&2, A>, b: Maybe<&2, A>) -> Bool:
  match a b:
    case None{} None{}:
      True{}
    case Some{x} Some{y}:
      eq(x, y)
    case _ _:
      False{}

# Maybe.same is True only for equal values, when eq is True only for equal ones
def Maybe.same_sound(
  ~A: Data,
  ~eq: A -> A -> Bool,
  eqs: @x: A -> @y: A -> {eq(x, y) == True{}: Bool} -> {x == y: A},
  a: Maybe<&2, A>,
  b: Maybe<&2, A>
) -> {Maybe.same(~A, ~eq, a, b) == True{}: Bool} -> {a == b: Maybe<&2, A>}:
  match a b:
    case None{} None{}:
      h => {==}
    case None{} Some{y}:
      h => Empty.absurd({None{} == Some{y}: Maybe<&2, A>}, Shared.Bool.false_ne_true(h))
    case Some{x} None{}:
      h => Empty.absurd({Some{x} == None{}: Maybe<&2, A>}, Shared.Bool.false_ne_true(h))
    case Some{+x} Some{y}:
      h =>
        %eqs(x)(y)(h): {Some{x} == Some{_}: Maybe<&2, A>}
        {==}

# m, else nothing, is m
def Maybe.or_none(-A: Data, m: Maybe<&2, A>) -> {Maybe.or(&2, A, m, None{}) == m: Maybe<&2, A>}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

# taking in the same value again keeps the first pick
def Maybe.or_idem(
  -A: Data,
  x: Maybe<&2, A>,
  y: Maybe<&2, A>
) -> {Maybe.or(&2, A, Maybe.or(&2, A, x, y), y) == Maybe.or(&2, A, x, y): Maybe<&2, A>}:
  match x y:
    case None{} None{}:
      {==}
    case None{} Some{v}:
      {==}
    case Some{u} w:
      {==}

# mapping the identity changes nothing
def Maybe.map_id(-A: Data, m: Maybe<&2, A>) -> {Maybe.map(&2, A, A, y => y, m) == m: Maybe<&2, A>}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

# Maybe.same is True for a value and itself, when eq is
def Maybe.same_refl(
  ~A: Data,
  ~eq: A -> A -> Bool,
  ~refl: @x: A -> {eq(x, x) == True{}: Bool},
  m: Maybe<&2, A>
) -> {Maybe.same(~A, ~eq, m, m) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{y}:
      refl(y)
