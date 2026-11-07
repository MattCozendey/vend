import Base

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
