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

# Nat.cmp chains
def Nat.cmp_chain(
  a: Nat,
  b: Nat,
  c: Nat
) -> {Cmps.Cmp.chain(Nat.cmp(a, b), Nat.cmp(b, c), Nat.cmp(a, c)) == True{}: Bool}:
  match a b c:
    case 0n 0n 0n:
      {==}
    case 0n 0n 1n+z:
      {==}
    case 0n 1n+y 0n:
      {==}
    case 0n 1n+y 1n+z:
      Cmps.Cmp.chain_lt(Nat.cmp(y, z))
    case 1n+x 0n 0n:
      {==}
    case 1n+x 0n 1n+z:
      Cmps.Cmp.chain_gl(Nat.cmp(x, z))
    case 1n+x 1n+y 0n:
      Cmps.Cmp.chain_gg(Nat.cmp(x, y))
    case 1n+x 1n+y 1n+z:
      Nat.cmp_chain(x, y, z)

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# a plus one more is one more than a plus
def Nat.add_succ(a: Nat, b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b): Nat}:
  match a:
    case 0n:
      {==}
    case 1n+q:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(q, 1n+b), 1n+Nat.add(q, b), Nat.add_succ(q, b))
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
