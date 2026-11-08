import Base
import ./shared.bend as Shared

# k(), when b holds, else e(); only the chosen one runs
def Bool.when(-A: Type, b: Bool, k: Unit -> A, e: Unit -> A) -> A:
  match b:
    case False{}:
      e(Unit{})
    case True{}:
      k(Unit{})

# both sides of a true "and" are true
def Bool.and_true_left(a: Bool, b: Bool) -> {Bool.and(a, b) == True{}: Bool} -> {a == True{}: Bool}:
  match a:
    case False{}:
      h => Empty.absurd({False{} == True{}: Bool}, Shared.Bool.false_ne_true(h))
    case True{}:
      h => {==}

def Bool.and_true_right(
  a: Bool,
  b: Bool
) -> {Bool.and(a, b) == True{}: Bool} -> {b == True{}: Bool}:
  match a:
    case False{}:
      h => Empty.absurd({b == True{}: Bool}, Shared.Bool.false_ne_true(h))
    case True{}:
      h => h

# anything or True is True
def Bool.or_true_right(a: Bool) -> {Bool.or(a, True{}) == True{}: Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

# a "not" that is True is of False
def Bool.not_true(a: Bool) -> {Bool.not(a) == True{}: Bool} -> {a == False{}: Bool}:
  match a:
    case False{}:
      h => {==}
    case True{}:
      h => Empty.absurd({True{} == False{}: Bool}, Shared.Bool.false_ne_true(h))
