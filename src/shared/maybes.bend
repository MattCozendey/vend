import Base
import ./bools.bend as Bools

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

# Some{x} when hit, else what rest gives; rest runs only when needed
def Maybe.if(-A: Data, x: A, rest: Unit -> Maybe<&2, A>, hit: Bool) -> Maybe<&2, A>:
  match hit:
    case True{}:
      Some{x}
    case False{}:
      rest(Unit{})

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
      h => Empty.absurd({None{} == Some{y}: Maybe<&2, A>}, Bools.Bool.false_ne_true(h))
    case Some{x} None{}:
      h => Empty.absurd({Some{x} == None{}: Maybe<&2, A>}, Bools.Bool.false_ne_true(h))
    case Some{+x} Some{y}:
      h =>
        %eqs(x)(y)(h): {Some{x} == Some{_}: Maybe<&2, A>}
        {==}
