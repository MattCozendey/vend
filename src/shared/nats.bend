import Base
import ./cmps.bend as Cmps
import ./shared.bend as Shared

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run

# a number is less than the one after it
def Nat.lt_succ(e: Nat) -> {Nat.is_lt(e, 1n+e) == True{}: Bool}:
  match e:
    case 0n:
      {==}
    case 1n+p:
      Nat.lt_succ(p)
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# a plus one more is one more than a plus
def Nat.add_succ(a: Nat, b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b): Nat}:
  match a:
    case 0n:
      {==}
    case 1n+q:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(q, 1n+b), 1n+Nat.add(q, b), Nat.add_succ(q, b))
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# Order of numbers
# ----------------

# a number is not less than itself
def Nat.lt_irrefl(a: Nat) -> {Nat.is_lt(a, a) == False{}: Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Nat.lt_irrefl(p)

# a < b and b <= c give a < c
def Nat.lt_le(a: Nat, b: Nat, c: Nat) -> {Nat.is_lt(a, b) == True{}: Bool} -> {Nat.is_le(b, c) == True{}: Bool} -> {Nat.is_lt(a, c) == True{}: Bool}:
  match a b c:
    case 0n 0n w:
      h => k => Empty.absurd({Nat.is_lt(0n, w) == True{}: Bool}, Shared.Bool.false_ne_true(h))
    case 0n 1n+q 0n:
      h => k => Empty.absurd({Nat.is_lt(0n, 0n) == True{}: Bool}, Shared.Bool.false_ne_true(k))
    case 0n 1n+q 1n+w:
      h => k => {==}
    case 1n+p 0n w:
      h => k => Empty.absurd({Nat.is_lt(1n+p, w) == True{}: Bool}, Shared.Bool.false_ne_true(h))
    case 1n+p 1n+q 0n:
      h => k => Empty.absurd({Nat.is_lt(1n+p, 0n) == True{}: Bool}, Shared.Bool.false_ne_true(k))
    case 1n+p 1n+q 1n+w:
      Nat.lt_le(p, q, w)

# a <= b and b < c give a < c
def Nat.le_lt(a: Nat, b: Nat, c: Nat) -> {Nat.is_le(a, b) == True{}: Bool} -> {Nat.is_lt(b, c) == True{}: Bool} -> {Nat.is_lt(a, c) == True{}: Bool}:
  match a b c:
    case 0n 0n 0n:
      h => k => Empty.absurd({Nat.is_lt(0n, 0n) == True{}: Bool}, Shared.Bool.false_ne_true(k))
    case 0n 1n+q 0n:
      h => k => Empty.absurd({Nat.is_lt(0n, 0n) == True{}: Bool}, Shared.Bool.false_ne_true(k))
    case 0n v 1n+w:
      h => k => {==}
    case 1n+p 0n w:
      h => k => Empty.absurd({Nat.is_lt(1n+p, w) == True{}: Bool}, Shared.Bool.false_ne_true(h))
    case 1n+p 1n+q 0n:
      h => k => Empty.absurd({Nat.is_lt(1n+p, 0n) == True{}: Bool}, Shared.Bool.false_ne_true(k))
    case 1n+p 1n+q 1n+w:
      Nat.le_lt(p, q, w)

# a < b gives a <= b
def Nat.lt_weak(a: Nat, b: Nat) -> {Nat.is_lt(a, b) == True{}: Bool} -> {Nat.is_le(a, b) == True{}: Bool}:
  match a b:
    case 0n 0n:
      h => Empty.absurd({Nat.is_le(0n, 0n) == True{}: Bool}, Shared.Bool.false_ne_true(h))
    case 0n 1n+q:
      h => {==}
    case 1n+p 0n:
      h => Empty.absurd({Nat.is_le(1n+p, 0n) == True{}: Bool}, Shared.Bool.false_ne_true(h))
    case 1n+p 1n+q:
      Nat.lt_weak(p, q)

# a <= b gives a <= b + 1
def Nat.le_succ(a: Nat, b: Nat) -> {Nat.is_le(a, b) == True{}: Bool} -> {Nat.is_le(a, 1n+b) == True{}: Bool}:
  match a b:
    case 0n w:
      h => {==}
    case 1n+p 0n:
      h => Empty.absurd({Nat.is_le(1n+p, 1n) == True{}: Bool}, Shared.Bool.false_ne_true(h))
    case 1n+p 1n+q:
      Nat.le_succ(p, q)

# n, plus one when b holds
def Nat.add_if(b: Bool, n: Nat) -> Nat:
  match b:
    case True{}:
      1n+n
    case False{}:
      n

# a <= b gives a <= b, plus one when c holds
def Nat.le_add_if(c: Bool, a: Nat, b: Nat) -> {Nat.is_le(a, b) == True{}: Bool} -> {Nat.is_le(a, Nat.add_if(c, b)) == True{}: Bool}:
  match c:
    case True{}:
      Nat.le_succ(a, b)
    case False{}:
      h => h

# a <= b gives a, plus one when c holds, <= b plus one
def Nat.add_if_le_succ(c: Bool, a: Nat, b: Nat) -> {Nat.is_le(a, b) == True{}: Bool} -> {Nat.is_le(Nat.add_if(c, a), 1n+b) == True{}: Bool}:
  match c:
    case True{}:
      h => h
    case False{}:
      Nat.le_succ(a, b)

# adding the same one keeps a <= b
def Nat.add_if_le(c: Bool, a: Nat, b: Nat) -> {Nat.is_le(a, b) == True{}: Bool} -> {Nat.is_le(Nat.add_if(c, a), Nat.add_if(c, b)) == True{}: Bool}:
  match c:
    case True{}:
      h => h
    case False{}:
      h => h

# a number below b means b is above 0
def Nat.lt_pos(a: Nat, b: Nat) -> {Nat.is_lt(a, b) == True{}: Bool} -> {Nat.is_lt(0n, b) == True{}: Bool}:
  match a:
    case 0n:
      h => h
    case 1n+p:
      Nat.le_lt(0n, 1n+p, b)({==})

# a number is at most itself
def Nat.le_refl(a: Nat) -> {Nat.is_le(a, a) == True{}: Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Nat.le_refl(p)

# no number is below 0
def Nat.le_zero(a: Nat) -> {Nat.is_le(0n, a) == True{}: Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

# a <= c gives a + b <= c + b
def Nat.add_le_right(+c: Nat, a: Nat, +b: Nat) -> {Nat.is_le(a, c) == True{}: Bool} -> {Nat.is_le(Nat.add(a, b), Nat.add(c, b)) == True{}: Bool}:
  match c a:
    case 0n 0n:
      h => Nat.le_refl(b)
    case 0n 1n+p:
      h => Empty.absurd({Nat.is_le(1n+Nat.add(p, b), b) == True{}: Bool}, Shared.Bool.false_ne_true(h))
    case 1n+q 0n:
      h => Nat.le_succ(b, Nat.add(q, b))(Nat.add_le_right(q, 0n, b)(Nat.le_zero(q)))
    case 1n+q 1n+p:
      Nat.add_le_right(q, p, b)

# b <= d gives a + b <= a + d
def Nat.add_le_left(a: Nat, b: Nat, d: Nat) -> {Nat.is_le(b, d) == True{}: Bool} -> {Nat.is_le(Nat.add(a, b), Nat.add(a, d)) == True{}: Bool}:
  match a:
    case 0n:
      h => h
    case 1n+p:
      Nat.add_le_left(p, b, d)

# a <= b and b <= c give a <= c
def Nat.le_trans(a: Nat, b: Nat, c: Nat) -> {Nat.is_le(a, b) == True{}: Bool} -> {Nat.is_le(b, c) == True{}: Bool} -> {Nat.is_le(a, c) == True{}: Bool}:
  match a b c:
    case 0n v w:
      h => k => Nat.le_zero(w)
    case 1n+p 0n w:
      h => k => Empty.absurd({Nat.is_le(1n+p, w) == True{}: Bool}, Shared.Bool.false_ne_true(h))
    case 1n+p 1n+q 0n:
      h => k => Empty.absurd({Nat.is_le(1n+p, 0n) == True{}: Bool}, Shared.Bool.false_ne_true(k))
    case 1n+p 1n+q 1n+w:
      Nat.le_trans(p, q, w)

# a <= a2 and b <= b2 give a + b <= a2 + b2
def Nat.add_le(+a: Nat, +a2: Nat, +b: Nat, +b2: Nat) -> {Nat.is_le(a, a2) == True{}: Bool} -> {Nat.is_le(b, b2) == True{}: Bool} -> {Nat.is_le(Nat.add(a, b), Nat.add(a2, b2)) == True{}: Bool}:
  h => k => Nat.le_trans(Nat.add(a, b), Nat.add(a2, b), Nat.add(a2, b2))(Nat.add_le_right(a2, a, b)(h))(Nat.add_le_left(a2, b, b2)(k))

# taking nothing away leaves a number
def Nat.sub_zero(a: Nat) -> {Nat.sub(a, 0n) == a: Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

# what is left of g after a below g is one more than what is left after a + 1
def Nat.sub_pos(a: Nat, g: Nat) -> {Nat.is_lt(a, g) == True{}: Bool} -> {Nat.sub(g, a) == 1n+Nat.sub(g, 1n+a): Nat}:
  match a g:
    case 0n 0n:
      h => Empty.absurd({0n == 1n: Nat}, Shared.Bool.false_ne_true(h))
    case 0n 1n+p:
      h =>
        %Equal.sym(Nat, Nat.sub(p, 0n), p, Nat.sub_zero(p)) : {1n+p == 1n+_: Nat}
        {==}
    case 1n+q 0n:
      h => Empty.absurd({0n == 1n+Nat.sub(0n, 1n+1n+q): Nat}, Shared.Bool.false_ne_true(h))
    case 1n+q 1n+p:
      Nat.sub_pos(q, p)
