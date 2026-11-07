import Base
import ./cmps.bend as Cmps

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run

# every number compares EQ with itself
def Nat.cmp_refl(a: Nat) -> {Nat.cmp(a, a) == EQ{}: Cmp}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Nat.cmp_refl(p)

# Nat.cmp the other way round is flipped
def Nat.cmp_swap(a: Nat, b: Nat) -> {Nat.cmp(b, a) == Cmps.Cmp.flip(Nat.cmp(a, b)): Cmp}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      Nat.cmp_swap(p, q)

# Nat.cmp is EQ only for equal numbers
def Nat.cmp_eq(a: Nat, b: Nat) -> {Nat.cmp(a, b) == EQ{}: Cmp} -> {a == b: Nat}:
  match a b:
    case 0n 0n:
      h => {==}
    case 0n 1n+q:
      h => Empty.absurd({0n == 1n+q: Nat}, Cmps.Cmp.ne_eq(LT{}, Unit{}, h))
    case 1n+p 0n:
      h => Empty.absurd({1n+p == 0n: Nat}, Cmps.Cmp.ne_eq(GT{}, Unit{}, h))
    case 1n+p 1n+q:
      h =>
        %Nat.cmp_eq(p, q)(h): {1n+p == 1n+_: Nat}
        {==}

# a number is less than the one after it
def Nat.lt_succ(e: Nat) -> {Nat.is_lt(e, 1n+e) == True{}: Bool}:
  match e:
    case 0n:
      {==}
    case 1n+p:
      Nat.lt_succ(p)
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information
