import Base

# Comparisons
# -----------

# c, unless it is EQ: then rest
def Cmp.then(c: Cmp, rest: Cmp) -> Cmp:
  match c:
    case LT{}:
      LT{}
    case EQ{}:
      rest
    case GT{}:
      GT{}

# c seen from the other side: LT and GT swap
def Cmp.flip(c: Cmp) -> Cmp:
  match c:
    case LT{}:
      GT{}
    case EQ{}:
      EQ{}
    case GT{}:
      LT{}

# Optional values
# ---------------

# x and y combined by both when each is there, else the one that is there
def Maybe.merge(~A: Data, ~both: A -> A -> A, x: Maybe<&2, A>, y: Maybe<&2, A>) -> Maybe<&2, A>:
  match x y:
    case Some{a} Some{b}:
      Some{both(a, b)}
    case Some{a} None{}:
      Some{a}
    case None{} y:
      y

# x when c holds, else nothing
def Maybe.when(~A: Data, c: Bool, x: Maybe<&2, A>) -> Maybe<&2, A>:
  Bool.pick(Maybe<&2, A>, c, x, None{})

# Rows
# ----

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- Row is a type: it is used only in types and erased arguments, so no code that runs builds or frees its binder
# n values of A in a row
def Row(-A: Data, n: Nat) -> Data:
  match n:
    case 0n:
      Unit
    case 1n+m:
      +Sigma<A, _ => Row(A, m)>
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information
