import Base
import ./cmps.bend as Cmps

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# the last step of Word.cmp_eq, with t the comparison of the tails
def Word.cmp_eq.fin(
  -p: Nat,
  ab: Bool,
  bb: Bool,
  -at: Word(p),
  -bt: Word(p),
  t: Cmp,
  ih: {Word.cmp(p, at, bt) == EQ{}: Cmp} -> {at == bt: Word(p)}
) -> {
  Word.cmp(p, at, bt) == t: Cmp
} -> {Word.cmp.fin(ab, bb, t) == EQ{}: Cmp} -> {WCon{ab, at} == WCon{bb, bt}: Word(1n+p)}:
  match t:
    case LT{}:
      e => h => Empty.absurd(
        {WCon{ab, at} == WCon{bb, bt}: Word(1n+p)},
        Cmps.Cmp.ne_eq(LT{}, Unit{}, h)
      )
    case EQ{}:
      e => h =>
        %Cmps.Bool.cmp_eq(ab, bb)(h): {WCon{ab, at} == WCon{_, bt}: Word(1n+p)}
        %ih(e): {WCon{ab, at} == WCon{ab, _}: Word(1n+p)}
        {==}
    case GT{}:
      e => h => Empty.absurd(
        {WCon{ab, at} == WCon{bb, bt}: Word(1n+p)},
        Cmps.Cmp.ne_eq(GT{}, Unit{}, h)
      )
# Word.cmp is EQ only for equal words
def Word.cmp_eq(
  +n: Nat,
  a: Word(n),
  b: Word(n)
) -> {Word.cmp(n, a, b) == EQ{}: Cmp} -> {a == b: Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          _ => {==}
    case 1n+p:
      match a b:
        case WCon{ab, +at} WCon{bb, +bt}:
          h => Word.cmp_eq.fin(
            p,
            ab,
            bb,
            at,
            bt,
            Word.cmp(p, at, bt),
            Word.cmp_eq(p, at, bt)
          )({==}, h)
# Word.cmp of a word with itself is EQ
def Word.cmp_refl(n: Nat, a: Word(n)) -> {Word.cmp(n, a, a) == EQ{}: Cmp}:
  match n:
    case 0n:
      match a:
        case WNil{}:
          {==}
    case 1n+np:
      match a:
        case WCon{+head, tail}:
          match head:
            case False{}:
              %Equal.sym(Cmp, Word.cmp(np, tail, tail), EQ{}, Word.cmp_refl(np, tail)):
                {Word.cmp.fin(False{}, False{}, _) == EQ{}: Cmp}
              {==}
            case True{}:
              %Equal.sym(Cmp, Word.cmp(np, tail, tail), EQ{}, Word.cmp_refl(np, tail)):
                {Word.cmp.fin(True{}, True{}, _) == EQ{}: Cmp}
              {==}
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# U32.is_eq is True only for equal numbers
def U32.is_eq_sound(a: U32, b: U32) -> {U32.is_eq(a, b) == True{}: Bool} -> {a == b: U32}:
  match a b:
    case U32{+x} U32{+y}:
      h =>
        %Word.cmp_eq(
          32n,
          x,
          y
        )(Cmps.Cmp.is_eq_sound(Word.cmp(32n, x, y))(h)): {U32{x} == U32{_}: U32}
        {==}

# U32.cmp of a number with itself is EQ
def U32.cmp_refl(x: U32) -> {U32.cmp(x, x) == EQ{}: Cmp}:
  match x:
    case U32{w}:
      Word.cmp_refl(32n, w)

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# a number is equal to itself
def U32.is_eq_refl(x: U32) -> {U32.is_eq(x, x) == True{}: Bool}:
  %Equal.sym(Cmp, U32.cmp(x, x), EQ{}, U32.cmp_refl(x)): {Cmp.is_eq(_) == True{}: Bool}
  {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
