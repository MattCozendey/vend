import Base
import ./shared.bend as Shared

# Comparisons
# -----------
# String.eq and Word.cmp compare by Cmp; their laws need EQ to mean equal.

# Unit when c is not EQ
def Cmp.Ne(c: Cmp) -> Type:
  match c:
    case LT{}:
      Unit
    case EQ{}:
      Empty
    case GT{}:
      Unit
# no c that is not EQ equals EQ
def Cmp.ne_eq(-c: Cmp, n: Cmp.Ne(c), e: {c == EQ{}: Cmp}) -> Empty:
  %e: Cmp.Ne(_)
  n
# Cmp.is_eq is True only for EQ
def Cmp.is_eq_sound(c: Cmp) -> {Cmp.is_eq(c) == True{}: Bool} -> {c == EQ{}: Cmp}:
  match c:
    case LT{}:
      h => Empty.absurd({LT{} == EQ{}: Cmp}, Shared.Bool.false_ne_true(h))
    case EQ{}:
      h => {==}
    case GT{}:
      h => Empty.absurd({GT{} == EQ{}: Cmp}, Shared.Bool.false_ne_true(h))
# Bool.cmp is EQ only for equal Bools
def Bool.cmp_eq(a: Bool, b: Bool) -> {Bool.cmp(a, b) == EQ{}: Cmp} -> {a == b: Bool}:
  match a b:
    case False{} False{}:
      h => {==}
    case False{} True{}:
      h => Empty.absurd({False{} == True{}: Bool}, Cmp.ne_eq(LT{}, Unit{}, h))
    case True{} False{}:
      h => Empty.absurd({True{} == False{}: Bool}, Cmp.ne_eq(GT{}, Unit{}, h))
    case True{} True{}:
      h => {==}

# c, or rest when c is EQ: an order by a first key, then a second
def Cmp.then(c: Cmp, rest: Cmp) -> Cmp:
  match c:
    case EQ{}:
      rest
    case o:
      o

# a "then" that is EQ is EQ on its first side
def Cmp.then_eq_left(c: Cmp, r: Cmp) -> {Cmp.then(c, r) == EQ{}: Cmp} -> {c == EQ{}: Cmp}:
  match c:
    case LT{}:
      h => Empty.absurd({LT{} == EQ{}: Cmp}, Cmp.ne_eq(LT{}, Unit{}, h))
    case EQ{}:
      h => {==}
    case GT{}:
      h => Empty.absurd({GT{} == EQ{}: Cmp}, Cmp.ne_eq(GT{}, Unit{}, h))
