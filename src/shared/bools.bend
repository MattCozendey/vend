import Base

# k(), when b holds, else e(); only the chosen one runs
def Bool.when(-A: Type, b: Bool, k: Unit -> A, e: Unit -> A) -> A:
  match b:
    case False{}:
      e(Unit{})
    case True{}:
      k(Unit{})
# no False equals True
def Bool.false_ne_true(e: {False{} == True{}: Bool}) -> Empty:
  %e: Bool.pick(Type, _, Empty, Unit)
  Unit{}

# both sides of a true "and" are true
def Bool.and_true_left(a: Bool, b: Bool) -> {Bool.and(a, b) == True{}: Bool} -> {a == True{}: Bool}:
  match a:
    case False{}:
      h => Empty.absurd({False{} == True{}: Bool}, Bool.false_ne_true(h))
    case True{}:
      h => {==}

def Bool.and_true_right(
  a: Bool,
  b: Bool
) -> {Bool.and(a, b) == True{}: Bool} -> {b == True{}: Bool}:
  match a:
    case False{}:
      h => Empty.absurd({b == True{}: Bool}, Bool.false_ne_true(h))
    case True{}:
      h => h

# both sides of a false "or" are false
def Bool.or_false_left(
  a: Bool,
  b: Bool
) -> {Bool.or(a, b) == False{}: Bool} -> {a == False{}: Bool}:
  match a:
    case True{}:
      h => Empty.absurd(
        {True{} == False{}: Bool},
        Bool.false_ne_true(Equal.sym(Bool, True{}, False{}, h))
      )
    case False{}:
      h => {==}

def Bool.or_false_right(
  a: Bool,
  b: Bool
) -> {Bool.or(a, b) == False{}: Bool} -> {b == False{}: Bool}:
  match a:
    case True{}:
      h => Empty.absurd(
        {b == False{}: Bool},
        Bool.false_ne_true(Equal.sym(Bool, True{}, False{}, h))
      )
    case False{}:
      h => h

# a "not" that is false is of a true
def Bool.not_false(a: Bool) -> {Bool.not(a) == False{}: Bool} -> {a == True{}: Bool}:
  match a:
    case True{}:
      h => {==}
    case False{}:
      h => Empty.absurd(
        {False{} == True{}: Bool},
        Bool.false_ne_true(Equal.sym(Bool, True{}, False{}, h))
      )
