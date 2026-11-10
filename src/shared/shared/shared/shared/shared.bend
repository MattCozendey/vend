import Base

# Equality
# --------
# A check same of A is an equality when Eq.Laws(A, same) holds. A def that
# needs it takes same as a template, and its laws as one more: the code then
# runs same inlined, and the laws cost nothing at run time.

# same is True for a value and itself, and only for equal values
def Eq.Laws(-A: Data, same: A -> A -> Bool) -> Type:
  (
    @x: A -> {same(x, x) == True{}: Bool}
  )
    & (@x: A -> @y: A -> {same(x, y) == True{}: Bool} -> {x == y: A})

# same is True for x and itself, by its laws l
def Eq.refl(
  ~A: Data,
  ~same: A -> A -> Bool,
  l: Eq.Laws(A, same),
  x: A
) -> {same(x, x) == True{}: Bool}:
  (r, d) = l
  r(x)

# same is True only for equal x and y, by its laws l
def Eq.sound(
  ~A: Data,
  ~same: A -> A -> Bool,
  l: Eq.Laws(A, same),
  x: A,
  y: A
) -> {same(x, y) == True{}: Bool} -> {x == y: A}:
  (r, d) = l
  d(x, y)

# no False equals True
def Bool.false_ne_true(e: {False{} == True{}: Bool}) -> Empty:
  %e: Bool.pick(Type, _, Empty, Unit)
  Unit{}

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Eq.ne_flip once same(y, x) is known (back)
def Eq.ne_flip.at(
  ~A: Data,
  ~same: A -> A -> Bool,
  ~laws: Eq.Laws(A, same),
  back: Bool,
  +x: A,
  y: A,
  no: {same(x, y) == False{}: Bool},
  e: {same(y, x) == back: Bool}
) -> {back == False{}: Bool}:
  match back:
    case False{}:
      {==}
    case True{}:
      Empty.absurd(
        {True{} == False{}: Bool},
        Bool.false_ne_true(
          Equal.trans(
            Bool,
            False{},
            same(x, y),
            True{},
            Equal.sym(Bool, same(x, y), False{}, no),
            Equal.trans(
              Bool,
              same(x, y),
              same(x, x),
              True{},
              Equal.cong(A, Bool, z => same(x, z), y, x, Eq.sound(~A, ~same, laws, y)(x)(e)),
              Eq.refl(~A, ~same, laws, x)
            )
          )
        )
      )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# x is not y, so y is not x
def Eq.ne_flip(
  ~A: Data,
  ~same: A -> A -> Bool,
  ~laws: Eq.Laws(A, same),
  +x: A,
  +y: A,
  no: {same(x, y) == False{}: Bool}
) -> {same(y, x) == False{}: Bool}:
  Eq.ne_flip.at(~A, ~same, ~laws, same(y, x), x, y, no, {==})

# a and False is False
def Bool.and_false_right(a: Bool) -> {Bool.and(a, False{}) == False{}: Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# anything or True is True
def Bool.or_true_right(a: Bool) -> {Bool.or(a, True{}) == True{}: Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

# the hit of a true "all" is true
def List.all.if_hit(
  hit: Bool,
  rest: Unit -> Bool
) -> {List.all.if(rest, hit) == True{}: Bool} -> {hit == True{}: Bool}:
  match hit:
    case True{}:
      h => {==}
    case False{}:
      h => h

# the rest of a true "all" is true
def List.all.if_rest(
  hit: Bool,
  rest: Unit -> Bool
) -> {List.all.if(rest, hit) == True{}: Bool} -> {rest(Unit{}) == True{}: Bool}:
  match hit:
    case True{}:
      h => h
    case False{}:
      h => Empty.absurd({rest(Unit{}) == True{}: Bool}, Bool.false_ne_true(h))

# a true hit and a true rest make a true "all"
def List.all.if_both(
  hit: Bool,
  rest: Unit -> Bool
) -> {
  hit == True{}: Bool
} -> {rest(Unit{}) == True{}: Bool} -> {List.all.if(rest, hit) == True{}: Bool}:
  match hit:
    case True{}:
      h1 => h2 => h2
    case False{}:
      h1 => h2 => Empty.absurd({False{} == True{}: Bool}, Bool.false_ne_true(h1))

# ks without the values that same calls p
def List.remove(~A: Data, ~same: A -> A -> Bool, ks: List<&2, A>, +p: A) -> List<&2, A>:
  match ks:
    case Nil{}:
      []
    case Con{+k, r}:
      List.filter.put(A, k, List.remove(~A, ~same, r, p), Bool.not(same(k, p)))

# an "any" whose rest is true is true
def List.any.if_true(hit: Bool) -> {List.any.if(u => True{}, hit) == True{}: Bool}:
  match hit:
    case True{}:
      {==}
    case False{}:
      {==}

# the hit of a false "any" is false
def List.any.if_false_hit(
  hit: Bool,
  rest: Unit -> Bool
) -> {List.any.if(rest, hit) == False{}: Bool} -> {hit == False{}: Bool}:
  match hit:
    case True{}:
      h => Empty.absurd(
        {True{} == False{}: Bool},
        Bool.false_ne_true(Equal.sym(Bool, True{}, False{}, h))
      )
    case False{}:
      h => {==}

# the rest of a false "any" is false
def List.any.if_false_rest(
  hit: Bool,
  rest: Unit -> Bool
) -> {List.any.if(rest, hit) == False{}: Bool} -> {rest(Unit{}) == False{}: Bool}:
  match hit:
    case True{}:
      h => Empty.absurd(
        {rest(Unit{}) == False{}: Bool},
        Bool.false_ne_true(Equal.sym(Bool, True{}, False{}, h))
      )
    case False{}:
      h => h

# List.contains_append at the first element, by whether it is m (hit)
def List.contains_append.at(
  ~A: Data,
  ~same: A -> A -> Bool,
  hit: Bool,
  r: List<&2, A>,
  b: List<&2, A>,
  m: A,
  ih: {
    List.contains(
      ~A,
      ~same,
      List.append(&2, A, r, b),
      m
    )
      == Bool.or(List.contains(~A, ~same, r, m), List.contains(~A, ~same, b, m)): Bool
  }
) -> {
  List.any.if(
    u => List.contains(~A, ~same, List.append(&2, A, r, b), m),
    hit
  )
    == Bool.or(
      List.any.if(u => List.contains(~A, ~same, r, m), hit),
      List.contains(~A, ~same, b, m)
    ): Bool
}:
  match hit:
    case True{}:
      {==}
    case False{}:
      ih

# m is in a ++ b exactly when it is in a or in b
def List.contains_append(
  ~A: Data,
  ~same: A -> A -> Bool,
  a: List<&2, A>,
  +b: List<&2, A>,
  +m: A
) -> {
  List.contains(
    ~A,
    ~same,
    List.append(&2, A, a, b),
    m
  )
    == Bool.or(List.contains(~A, ~same, a, m), List.contains(~A, ~same, b, m)): Bool
}:
  match a:
    case Nil{}:
      {==}
    case Con{x, +r}:
      List.contains_append.at(
        ~A,
        ~same,
        same(x, m),
        r,
        b,
        m,
        List.contains_append(~A, ~same, r, b, m)
      )

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# a list holds what its front a holds
def List.contains_left(
  ~A: Data,
  ~same: A -> A -> Bool,
  a: List<&2, A>,
  b: List<&2, A>,
  m: A,
  h: {List.contains(~A, ~same, a, m) == True{}: Bool}
) -> {List.contains(~A, ~same, List.append(&2, A, a, b), m) == True{}: Bool}:
  %Equal.sym(
    Bool,
    List.contains(~A, ~same, List.append(&2, A, a, b), m),
    Bool.or(List.contains(~A, ~same, a, m), List.contains(~A, ~same, b, m)),
    List.contains_append(~A, ~same, a, b, m)
  ): {_ == True{}: Bool}
  %Equal.sym(
    Bool,
    List.contains(~A, ~same, a, m),
    True{},
    h
  ): {Bool.or(_, List.contains(~A, ~same, b, m)) == True{}: Bool}
  {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# a list holds what its back b holds
def List.contains_right(
  ~A: Data,
  ~same: A -> A -> Bool,
  +a: List<&2, A>,
  b: List<&2, A>,
  +m: A,
  h: {List.contains(~A, ~same, b, m) == True{}: Bool}
) -> {List.contains(~A, ~same, List.append(&2, A, a, b), m) == True{}: Bool}:
  %Equal.sym(
    Bool,
    List.contains(~A, ~same, List.append(&2, A, a, b), m),
    Bool.or(List.contains(~A, ~same, a, m), List.contains(~A, ~same, b, m)),
    List.contains_append(~A, ~same, a, b, m)
  ): {_ == True{}: Bool}
  %Equal.sym(
    Bool,
    List.contains(~A, ~same, b, m),
    True{},
    h
  ): {Bool.or(List.contains(~A, ~same, a, m), _) == True{}: Bool}
  Bool.or_true_right(List.contains(~A, ~same, a, m))
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# a member of r is a member of x <> r
def List.contains_cons(
  ~A: Data,
  ~same: A -> A -> Bool,
  x: A,
  r: List<&2, A>,
  y: A
) -> {
  List.contains(~A, ~same, r, y) == True{}: Bool
} -> {List.contains(~A, ~same, x <> r, y) == True{}: Bool}:
  h =>
    %Equal.sym(
      Bool,
      List.contains(~A, ~same, r, y),
      True{},
      h
    ): {List.any.if(u => _, same(x, y)) == True{}: Bool}
    List.any.if_true(same(x, y))
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# the elements of xs that p keeps, given g
def List.keep(~A: Data, ~V: Data, ~p: V -> A -> Bool, xs: List<&2, A>, +g: V) -> List<&2, A>:
  match xs:
    case Nil{}:
      []
    case Con{+x, r}:
      List.filter.put(A, x, List.keep(~A, ~V, ~p, r, g), p(g)(x))

# the lists that f gives for each element of xs, given g, one after another
def List.flat(
  ~A: Data,
  ~B: Data,
  ~V: Data,
  ~f: V -> A -> List<&2, B>,
  xs: List<&2, A>,
  +g: V
) -> List<&2, B>:
  match xs:
    case Nil{}:
      []
    case Con{x, r}:
      List.append(&2, B, f(g)(x), List.flat(~A, ~B, ~V, ~f, r, g))

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
      h => Empty.absurd({LT{} == EQ{}: Cmp}, Bool.false_ne_true(h))
    case EQ{}:
      h => {==}
    case GT{}:
      h => Empty.absurd({GT{} == EQ{}: Cmp}, Bool.false_ne_true(h))
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
      e => h => Empty.absurd({WCon{ab, at} == WCon{bb, bt}: Word(1n+p)}, Cmp.ne_eq(LT{}, Unit{}, h))
    case EQ{}:
      e => h =>
        %Bool.cmp_eq(ab, bb)(h): {WCon{ab, at} == WCon{_, bt}: Word(1n+p)}
        %ih(e): {WCon{ab, at} == WCon{ab, _}: Word(1n+p)}
        {==}
    case GT{}:
      e => h => Empty.absurd({WCon{ab, at} == WCon{bb, bt}: Word(1n+p)}, Cmp.ne_eq(GT{}, Unit{}, h))
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
        %Word.cmp_eq(32n, x, y)(Cmp.is_eq_sound(Word.cmp(32n, x, y))(h)): {U32{x} == U32{_}: U32}
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

# the laws of U32.is_eq
def U32.laws() -> Eq.Laws(U32, U32.is_eq):
  (U32.is_eq_refl, U32.is_eq_sound)

# k(), when b holds, else e(); only the chosen one runs
def Bool.when(-A: Type, b: Bool, k: Unit -> A, e: Unit -> A) -> A:
  match b:
    case False{}:
      e(Unit{})
    case True{}:
      k(Unit{})

# both sides of a true "and" are true
def Bool.and_true_left(
  a: Bool,
  -b: Bool
) -> {Bool.and(a, b) == True{}: Bool} -> {a == True{}: Bool}:
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

# a and b are the same bit
def Bool.is_eq(a: Bool, b: Bool) -> Bool:
  match a b:
    case True{} True{}:
      True{}
    case False{} False{}:
      True{}
    case _ _:
      False{}

# Bool.is_eq is True for a bit and itself
def Bool.is_eq_refl(a: Bool) -> {Bool.is_eq(a, a) == True{}: Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# Bool.is_eq is True only for equal bits
def Bool.is_eq_sound(a: Bool, b: Bool) -> {Bool.is_eq(a, b) == True{}: Bool} -> {a == b: Bool}:
  match a b:
    case True{} True{}:
      h => {==}
    case False{} False{}:
      h => {==}
    case True{} False{}:
      h => Empty.absurd({True{} == False{}: Bool}, Bool.false_ne_true(h))
    case False{} True{}:
      h => Empty.absurd({False{} == True{}: Bool}, Bool.false_ne_true(h))

# the laws of Bool.is_eq
def Bool.laws() -> Eq.Laws(Bool, Bool.is_eq):
  (Bool.is_eq_refl, Bool.is_eq_sound)

# a "not" that is True is of False
def Bool.not_true(a: Bool) -> {Bool.not(a) == True{}: Bool} -> {a == False{}: Bool}:
  match a:
    case False{}:
      h => {==}
    case True{}:
      h => Empty.absurd({True{} == False{}: Bool}, Bool.false_ne_true(h))

# a is true when its "not" is false
def Bool.not_false(a: Bool) -> {Bool.not(a) == False{}: Bool} -> {a == True{}: Bool}:
  match a:
    case True{}:
      h => {==}
    case False{}:
      h => Empty.absurd(
        {False{} == True{}: Bool},
        Bool.false_ne_true(Equal.sym(Bool, True{}, False{}, h))
      )

# both sides are true, so their "and" is
def Bool.and_both(
  a: Bool,
  b: Bool
) -> {a == True{}: Bool} -> {b == True{}: Bool} -> {Bool.and(a, b) == True{}: Bool}:
  match a:
    case True{}:
      ha => hb => hb
    case False{}:
      ha => hb => Empty.absurd({False{} == True{}: Bool}, Bool.false_ne_true(ha))

# the second of three true sides is true
def Bool.and_second(
  a: Bool,
  b: Bool,
  -c: Bool
) -> {Bool.and(a, Bool.and(b, c)) == True{}: Bool} -> {b == True{}: Bool}:
  match a b:
    case False{} y:
      h => Empty.absurd({y == True{}: Bool}, Bool.false_ne_true(h))
    case True{} False{}:
      h => h
    case True{} True{}:
      h => {==}

# the third of three true sides is true
def Bool.and_third(
  a: Bool,
  b: Bool,
  -c: Bool
) -> {Bool.and(a, Bool.and(b, c)) == True{}: Bool} -> {c == True{}: Bool}:
  match a b:
    case False{} y:
      h => Empty.absurd({c == True{}: Bool}, Bool.false_ne_true(h))
    case True{} False{}:
      h => Empty.absurd({c == True{}: Bool}, Bool.false_ne_true(h))
    case True{} True{}:
      h => h

# a, b and c are true when each follows from h: the one use of h that a proof
# has (a "for every" premise is a function) gives all three
def Bool.and_each(
  -H: Type,
  a: Bool,
  b: Bool,
  -c: Bool,
  h: H,
  fa: H -> {a == True{}: Bool},
  fb: H -> {b == True{}: Bool},
  fc: H -> {c == True{}: Bool}
) -> {Bool.and(a, Bool.and(b, c)) == True{}: Bool}:
  match a b:
    case False{} y:
      fa(h)
    case True{} False{}:
      fb(h)
    case True{} True{}:
      fc(h)

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

# no number is below 0
def Nat.lt_zero(a: Nat) -> {Nat.is_lt(a, 0n) == False{}: Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

# a number is below the number after it
def Nat.lt_succ(a: Nat) -> {Nat.is_lt(a, 1n+a) == True{}: Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Nat.lt_succ(p)

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# a < b and b <= c give a < c
def Nat.lt_le(
  a: Nat,
  b: Nat,
  c: Nat
) -> {
  Nat.is_lt(a, b) == True{}: Bool
} -> {Nat.is_le(b, c) == True{}: Bool} -> {Nat.is_lt(a, c) == True{}: Bool}:
  match a b c:
    case 0n 0n w:
      h => k => Empty.absurd({Nat.is_lt(0n, w) == True{}: Bool}, Bool.false_ne_true(h))
    case 0n 1n+q 0n:
      h => k => Empty.absurd({Nat.is_lt(0n, 0n) == True{}: Bool}, Bool.false_ne_true(k))
    case 0n 1n+q 1n+w:
      h => k => {==}
    case 1n+p 0n w:
      h => k => Empty.absurd({Nat.is_lt(1n+p, w) == True{}: Bool}, Bool.false_ne_true(h))
    case 1n+p 1n+q 0n:
      h => k => Empty.absurd({Nat.is_lt(1n+p, 0n) == True{}: Bool}, Bool.false_ne_true(k))
    case 1n+p 1n+q 1n+w:
      Nat.lt_le(p, q, w)

# a <= b and b < c give a < c
def Nat.le_lt(
  a: Nat,
  b: Nat,
  c: Nat
) -> {
  Nat.is_le(a, b) == True{}: Bool
} -> {Nat.is_lt(b, c) == True{}: Bool} -> {Nat.is_lt(a, c) == True{}: Bool}:
  match a b c:
    case 0n 0n 0n:
      h => k => Empty.absurd({Nat.is_lt(0n, 0n) == True{}: Bool}, Bool.false_ne_true(k))
    case 0n 1n+q 0n:
      h => k => Empty.absurd({Nat.is_lt(0n, 0n) == True{}: Bool}, Bool.false_ne_true(k))
    case 0n v 1n+w:
      h => k => {==}
    case 1n+p 0n w:
      h => k => Empty.absurd({Nat.is_lt(1n+p, w) == True{}: Bool}, Bool.false_ne_true(h))
    case 1n+p 1n+q 0n:
      h => k => Empty.absurd({Nat.is_lt(1n+p, 0n) == True{}: Bool}, Bool.false_ne_true(k))
    case 1n+p 1n+q 1n+w:
      Nat.le_lt(p, q, w)

# a < b gives a <= b
def Nat.lt_weak(
  a: Nat,
  b: Nat
) -> {Nat.is_lt(a, b) == True{}: Bool} -> {Nat.is_le(a, b) == True{}: Bool}:
  match a b:
    case 0n 0n:
      h => Empty.absurd({Nat.is_le(0n, 0n) == True{}: Bool}, Bool.false_ne_true(h))
    case 0n 1n+q:
      h => {==}
    case 1n+p 0n:
      h => Empty.absurd({Nat.is_le(1n+p, 0n) == True{}: Bool}, Bool.false_ne_true(h))
    case 1n+p 1n+q:
      Nat.lt_weak(p, q)

# a <= b gives a <= b + 1
def Nat.le_succ(
  a: Nat,
  b: Nat
) -> {Nat.is_le(a, b) == True{}: Bool} -> {Nat.is_le(a, 1n+b) == True{}: Bool}:
  match a b:
    case 0n w:
      h => {==}
    case 1n+p 0n:
      h => Empty.absurd({Nat.is_le(1n+p, 1n) == True{}: Bool}, Bool.false_ne_true(h))
    case 1n+p 1n+q:
      Nat.le_succ(p, q)
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# n, plus one when b holds
def Nat.add_if(b: Bool, n: Nat) -> Nat:
  match b:
    case True{}:
      1n+n
    case False{}:
      n

# a <= b gives a <= b, plus one when c holds
def Nat.le_add_if(
  c: Bool,
  a: Nat,
  b: Nat
) -> {Nat.is_le(a, b) == True{}: Bool} -> {Nat.is_le(a, Nat.add_if(c, b)) == True{}: Bool}:
  match c:
    case True{}:
      Nat.le_succ(a, b)
    case False{}:
      h => h

# a <= b gives a, plus one when c holds, <= b plus one
def Nat.add_if_le_succ(
  c: Bool,
  a: Nat,
  b: Nat
) -> {Nat.is_le(a, b) == True{}: Bool} -> {Nat.is_le(Nat.add_if(c, a), 1n+b) == True{}: Bool}:
  match c:
    case True{}:
      h => h
    case False{}:
      Nat.le_succ(a, b)

# adding the same one keeps a <= b
def Nat.add_if_le(
  c: Bool,
  a: Nat,
  b: Nat
) -> {
  Nat.is_le(a, b) == True{}: Bool
} -> {Nat.is_le(Nat.add_if(c, a), Nat.add_if(c, b)) == True{}: Bool}:
  match c:
    case True{}:
      h => h
    case False{}:
      h => h

# a number below b means b is above 0
def Nat.lt_pos(
  a: Nat,
  b: Nat
) -> {Nat.is_lt(a, b) == True{}: Bool} -> {Nat.is_lt(0n, b) == True{}: Bool}:
  match a:
    case 0n:
      h => h
    case 1n+p:
      Nat.le_lt(0n, 1n+p, b)({==})

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# Nat.is_eq is True only for equal numbers
def Nat.is_eq_sound(a: Nat, b: Nat) -> {Nat.is_eq(a, b) == True{}: Bool} -> {a == b: Nat}:
  match a b:
    case 0n 0n:
      e => {==}
    case 0n 1n+q:
      e => Empty.absurd({0n == 1n+q: Nat}, Bool.false_ne_true(e))
    case 1n+p 0n:
      e => Empty.absurd({1n+p == 0n: Nat}, Bool.false_ne_true(e))
    case 1n+p 1n+q:
      e => Equal.cong(Nat, Nat, z => 1n+z, p, q, Nat.is_eq_sound(p, q)(e))
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

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

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# a <= c gives a + b <= c + b
def Nat.add_le_right(
  +c: Nat,
  a: Nat,
  +b: Nat
) -> {Nat.is_le(a, c) == True{}: Bool} -> {Nat.is_le(Nat.add(a, b), Nat.add(c, b)) == True{}: Bool}:
  match c a:
    case 0n 0n:
      h => Nat.le_refl(b)
    case 0n 1n+p:
      h => Empty.absurd({Nat.is_le(1n+Nat.add(p, b), b) == True{}: Bool}, Bool.false_ne_true(h))
    case 1n+q 0n:
      h => Nat.le_succ(b, Nat.add(q, b))(Nat.add_le_right(q, 0n, b)(Nat.le_zero(q)))
    case 1n+q 1n+p:
      Nat.add_le_right(q, p, b)
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# b <= d gives a + b <= a + d
def Nat.add_le_left(
  a: Nat,
  b: Nat,
  d: Nat
) -> {Nat.is_le(b, d) == True{}: Bool} -> {Nat.is_le(Nat.add(a, b), Nat.add(a, d)) == True{}: Bool}:
  match a:
    case 0n:
      h => h
    case 1n+p:
      Nat.add_le_left(p, b, d)

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# a <= b and b <= c give a <= c
def Nat.le_trans(
  a: Nat,
  b: Nat,
  c: Nat
) -> {
  Nat.is_le(a, b) == True{}: Bool
} -> {Nat.is_le(b, c) == True{}: Bool} -> {Nat.is_le(a, c) == True{}: Bool}:
  match a b c:
    case 0n v w:
      h => k => Nat.le_zero(w)
    case 1n+p 0n w:
      h => k => Empty.absurd({Nat.is_le(1n+p, w) == True{}: Bool}, Bool.false_ne_true(h))
    case 1n+p 1n+q 0n:
      h => k => Empty.absurd({Nat.is_le(1n+p, 0n) == True{}: Bool}, Bool.false_ne_true(k))
    case 1n+p 1n+q 1n+w:
      Nat.le_trans(p, q, w)
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# a <= a2 and b <= b2 give a + b <= a2 + b2
def Nat.add_le(
  +a: Nat,
  +a2: Nat,
  +b: Nat,
  +b2: Nat
) -> {
  Nat.is_le(a, a2) == True{}: Bool
} -> {
  Nat.is_le(b, b2) == True{}: Bool
} -> {Nat.is_le(Nat.add(a, b), Nat.add(a2, b2)) == True{}: Bool}:
  h => k => Nat.le_trans(
    Nat.add(a, b),
    Nat.add(a2, b),
    Nat.add(a2, b2)
  )(Nat.add_le_right(a2, a, b)(h))(Nat.add_le_left(a2, b, b2)(k))

# what holds when m is None
def Maybe.IsNone(-A: Data, m: Maybe<&2, A>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

# a Maybe that is_none calls empty is None
def Maybe.is_none_sound(
  -A: Data,
  m: Maybe<&2, A>
) -> {Maybe.is_none(&2, A, m) == True{}: Bool} -> {m == None{}: Maybe<&2, A>}:
  match m:
    case None{}:
      e => {==}
    case Some{x}:
      e => Empty.absurd({Some{x} == None{}: Maybe<&2, A>}, Bool.false_ne_true(e))

# no None equals a Some
def Maybe.none_ne_some(-A: Data, -x: A, e: {None{} == Some{x}: Maybe<&2, A>}) -> Empty:
  %e: Maybe.IsNone(A, _)
  Unit{}

# Some is one to one
def Maybe.some_inj(-A: Data, -x: A, -y: A, e: {Some{x} == Some{y}: Maybe<&2, A>}) -> {x == y: A}:
  Equal.cong(Maybe<&2, A>, A, m => Maybe.default(&2, A, m, x), Some{x}, Some{y}, e)

# a and b are both empty, or hold values that eq calls the same
def Maybe.is_eq(~A: Data, ~eq: A -> A -> Bool, a: Maybe<&2, A>, b: Maybe<&2, A>) -> Bool:
  match a b:
    case None{} None{}:
      True{}
    case Some{x} Some{y}:
      eq(x, y)
    case _ _:
      False{}

# nothing taken of a list is nothing
def List.take_zero(-A: Data, xs: List<&2, A>) -> {List.take(&2, A, xs, 0n) == []: List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, r}:
      {==}

# dropping nothing keeps a list
def List.drop_zero(a, -A: Kind(a), xs: List<a, A>) -> {List.drop(a, A, xs, 0n) == xs: List<a, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# after the first n of xs come x and then r, after its first n+1 comes r
def List.drop_step(
  a,
  -A: Kind(a),
  xs: List<a, A>,
  n: Nat,
  -x: A,
  r: List<a, A>
) -> {List.drop(a, A, xs, n) == x <> r: List<a, A>} -> {List.drop(a, A, xs, 1n+n) == r: List<a, A>}:
  match xs n:
    case Nil{} m:
      e => Empty.absurd(
        {List.drop(a, A, [], 1n+m) == r: List<a, A>},
        Bool.false_ne_true(
          Equal.cong(
            List<a, A>,
            Bool,
            l => List.is_empty(a, A, l),
            x <> r,
            [],
            Equal.sym(List<a, A>, [], x <> r, e)
          )
        )
      )
    case Con{h, t} 0n:
      e =>
        %List.drop_zero(a, A, r): {List.drop(a, A, t, 0n) == _: List<a, A>}
        Equal.cong(List<a, A>, List<a, A>, l => List.drop(a, A, l, 1n), h <> t, x <> r, e)
    case Con{h, t} 1n+m:
      e => List.drop_step(a, A, t, m, x, r)(e)
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# a number plus nothing is itself
def Nat.add_zero(a: Nat) -> {Nat.add(a, 0n) == a: Nat}:
  match a:
    case 0n:
      {==}
    case 1n+ap:
      %Equal.sym(Nat, Nat.add(ap, 0n), ap, Nat.add_zero(ap)):
        {1n+_ == 1n+ap: Nat}
      {==}

# Nat.is_eq is True for a number and itself
def Nat.is_eq_refl(a: Nat) -> {Nat.is_eq(a, a) == True{}: Bool}:
  match a:
    case 0n:
      {==}
    case 1n+ap:
      %Equal.sym(Bool, Nat.is_eq(ap, ap), True{}, Nat.is_eq_refl(ap)):
        {_ == True{}: Bool}
      {==}

# Nat.is_eq does not depend on the order of its arguments
def Nat.is_eq_comm(a: Nat, b: Nat) -> {Nat.is_eq(a, b) == Nat.is_eq(b, a): Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      {==}
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      %Equal.sym(Bool, Nat.is_eq(ap, bp), Nat.is_eq(bp, ap), Nat.is_eq_comm(ap, bp)):
        {_ == Nat.is_eq(bp, ap): Bool}
      {==}

# the laws of Nat.is_eq
def Nat.laws() -> Eq.Laws(Nat, Nat.is_eq):
  (a => Nat.is_eq_refl(a), a => b => Nat.is_eq_sound(a, b))

# a list with one more item at its end is one longer
def List.length_snoc(
  -A: Data,
  xs: List<&2, A>,
  -z: A
) -> {List.length(&2, A, List.append(&2, A, xs, [z])) == 1n+List.length(&2, A, xs): Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{head, tail}:
      %Equal.sym(
        Nat,
        List.length(&2, A, List.append(&2, A, tail, [z])),
        1n+List.length(&2, A, tail),
        List.length_snoc(A, tail, z)
      ):
        {1n+_ == 2n+List.length(&2, A, tail): Nat}
      {==}

# the first item of xs, else d
def List.head_or(-A: Data, xs: List<&2, A>, d: A) -> A:
  match xs:
    case Nil{}:
      d
    case Con{x, r}:
      x

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# equal lists have equal first items
def List.head_eq(
  -A: Data,
  h: A,
  -z: A,
  -t: List<&2, A>,
  -r: List<&2, A>,
  e: {h <> t == z <> r: List<&2, A>}
) -> {h == z: A}:
  Equal.cong(List<&2, A>, A, l => List.head_or(A, l, h), h <> t, z <> r, e)

# equal lists have equal rests
def List.tail_eq(
  -A: Data,
  -h: A,
  -z: A,
  t: List<&2, A>,
  r: List<&2, A>,
  e: {h <> t == z <> r: List<&2, A>}
) -> {t == r: List<&2, A>}:
  %List.drop_zero(&2, A, t): {_ == r: List<&2, A>}
  %List.drop_zero(&2, A, r): {List.drop(&2, A, t, 0n) == _: List<&2, A>}
  Equal.cong(List<&2, A>, List<&2, A>, l => List.drop(&2, A, l, 1n), h <> t, z <> r, e)

# when q starts xs and z comes after it there, q then z starts xs
def List.take_snoc(
  -A: Data,
  xs: List<&2, A>,
  q: List<&2, A>,
  -z: A,
  -r: List<&2, A>,
  +hq: {List.take(&2, A, xs, List.length(&2, A, q)) == q: List<&2, A>},
  hz: {List.drop(&2, A, xs, List.length(&2, A, q)) == z <> r: List<&2, A>}
) -> {
  List.take(
    &2,
    A,
    xs,
    List.length(&2, A, List.append(&2, A, q, [z]))
  )
    == List.append(&2, A, q, [z]): List<&2, A>
}:
  match xs q:
    case Nil{} w:
      Empty.absurd(
        {
          List.take(
            &2,
            A,
            [],
            List.length(&2, A, List.append(&2, A, w, [z]))
          )
            == List.append(&2, A, w, [z]): List<&2, A>
        },
        Bool.false_ne_true(
          Equal.cong(
            List<&2, A>,
            Bool,
            l => List.is_empty(&2, A, l),
            z <> r,
            [],
            Equal.sym(List<&2, A>, [], z <> r, hz)
          )
        )
      )
    case Con{h, +ts} Nil{}:
      %Equal.sym(
        List<&2, A>,
        List.take(&2, A, ts, 0n),
        [],
        List.take_zero(A, ts)
      ): {h <> _ == [z]: List<&2, A>}
      %Equal.sym(A, h, z, List.head_eq(A, h, z, ts, r, hz)): {_ <> [] == [z]: List<&2, A>}
      {==}
    case Con{+h, +ts} Con{a, +qs}:
      hq2 = hq
      %Equal.sym(
        List<&2, A>,
        List.take(&2, A, ts, List.length(&2, A, List.append(&2, A, qs, [z]))),
        List.append(&2, A, qs, [z]),
        List.take_snoc(
          A,
          ts,
          qs,
          z,
          r,
          List.tail_eq(A, h, a, List.take(&2, A, ts, List.length(&2, A, qs)), qs, hq),
          hz
        )
      ): {h <> _ == a <> List.append(&2, A, qs, [z]): List<&2, A>}
      %Equal.sym(
        A,
        h,
        a,
        List.head_eq(A, h, a, List.take(&2, A, ts, List.length(&2, A, qs)), qs, hq2)
      ): {_ <> List.append(&2, A, qs, [z]) == a <> List.append(&2, A, qs, [z]): List<&2, A>}
      {==}

# when q then a starts xs, q starts xs
def List.take_shorten(
  -A: Data,
  xs: List<&2, A>,
  q: List<&2, A>,
  +a: A,
  +h: {
    List.take(
      &2,
      A,
      xs,
      List.length(&2, A, List.append(&2, A, q, [a]))
    )
      == List.append(&2, A, q, [a]): List<&2, A>
  }
) -> {List.take(&2, A, xs, List.length(&2, A, q)) == q: List<&2, A>}:
  match xs q:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{hd, tl}:
      Empty.absurd(
        {List.take(&2, A, [], List.length(&2, A, hd <> tl)) == hd <> tl: List<&2, A>},
        Bool.false_ne_true(
          Equal.cong(
            List<&2, A>,
            Bool,
            l => List.is_empty(&2, A, l),
            hd <> List.append(&2, A, tl, [a]),
            [],
            Equal.sym(List<&2, A>, [], hd <> List.append(&2, A, tl, [a]), h)
          )
        )
      )
    case Con{x, ts} Nil{}:
      {==}
    case Con{+x, +ts} Con{hd, +tl}:
      h2 = h
      %Equal.sym(
        List<&2, A>,
        List.take(&2, A, ts, List.length(&2, A, tl)),
        tl,
        List.take_shorten(
          A,
          ts,
          tl,
          a,
          List.tail_eq(
            A,
            x,
            hd,
            List.take(&2, A, ts, List.length(&2, A, List.append(&2, A, tl, [a]))),
            List.append(&2, A, tl, [a]),
            h
          )
        )
      ): {x <> _ == hd <> tl: List<&2, A>}
      %Equal.sym(
        A,
        x,
        hd,
        List.head_eq(
          A,
          x,
          hd,
          List.take(&2, A, ts, List.length(&2, A, List.append(&2, A, tl, [a]))),
          List.append(&2, A, tl, [a]),
          h2
        )
      ): {_ <> tl == hd <> tl: List<&2, A>}
      {==}

# when q then a starts xs, a comes right after q in xs
def List.drop_at(
  -A: Data,
  xs: List<&2, A>,
  q: List<&2, A>,
  +a: A,
  h: {
    List.take(
      &2,
      A,
      xs,
      List.length(&2, A, List.append(&2, A, q, [a]))
    )
      == List.append(&2, A, q, [a]): List<&2, A>
  }
) -> {
  List.drop(
    &2,
    A,
    xs,
    List.length(&2, A, q)
  )
    == a
    <> List.drop(&2, A, xs, List.length(&2, A, List.append(&2, A, q, [a]))): List<&2, A>
}:
  match xs q:
    case Nil{} Nil{}:
      h
    case Nil{} Con{hd, tl}:
      Empty.absurd(
        {
          List.drop(
            &2,
            A,
            [],
            List.length(&2, A, hd <> tl)
          )
            == a
            <> List.drop(
              &2,
              A,
              [],
              List.length(&2, A, List.append(&2, A, hd <> tl, [a]))
            ): List<&2, A>
        },
        Bool.false_ne_true(
          Equal.cong(
            List<&2, A>,
            Bool,
            l => List.is_empty(&2, A, l),
            hd <> List.append(&2, A, tl, [a]),
            [],
            Equal.sym(List<&2, A>, [], hd <> List.append(&2, A, tl, [a]), h)
          )
        )
      )
    case Con{x, +ts} Nil{}:
      %Equal.sym(
        A,
        x,
        a,
        List.head_eq(A, x, a, List.take(&2, A, ts, 0n), [], h)
      ): {_ <> ts == a <> List.drop(&2, A, ts, 0n): List<&2, A>}
      %Equal.sym(
        List<&2, A>,
        List.drop(&2, A, ts, 0n),
        ts,
        List.drop_zero(&2, A, ts)
      ): {a <> ts == a <> _: List<&2, A>}
      {==}
    case Con{+x, +ts} Con{hd, +tl}:
      List.drop_at(
        A,
        ts,
        tl,
        a,
        List.tail_eq(
          A,
          x,
          hd,
          List.take(&2, A, ts, List.length(&2, A, List.append(&2, A, tl, [a]))),
          List.append(&2, A, tl, [a]),
          h
        )
      )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# appending nothing keeps a list
def List.append_nil(-A: Data, xs: List<&2, A>) -> {List.append(&2, A, xs, []) == xs: List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %List.append_nil(A, t): {h <> List.append(&2, A, t, []) == h <> _: List<&2, A>}
      {==}

# lists with equal heads and equal tails are equal
def List.cons_eq(
  -A: Data,
  -x: A,
  -y: A,
  -xs: List<&2, A>,
  -ys: List<&2, A>,
  h: {x == y: A},
  t: {xs == ys: List<&2, A>}
) -> {x <> xs == y <> ys: List<&2, A>}:
  %Equal.sym(A, x, y, h): {_ <> xs == y <> ys: List<&2, A>}
  %Equal.sym(List<&2, A>, xs, ys, t): {y <> _ == y <> ys: List<&2, A>}
  {==}

# dropping the first list of an append leaves the second
def List.drop_after_append(
  -A: Data,
  xs: List<&2, A>,
  ys: List<&2, A>
) -> {List.drop(&2, A, List.append(&2, A, xs, ys), List.length(&2, A, xs)) == ys: List<&2, A>}:
  match xs:
    case Nil{}:
      List.drop_zero(&2, A, ys)
    case Con{h, t}:
      List.drop_after_append(A, t, ys)

# Maybe.is_eq is True only for equal values, when eq is True only for equal ones
def Maybe.is_eq_sound(
  ~A: Data,
  ~eq: A -> A -> Bool,
  eqs: @x: A -> @y: A -> {eq(x, y) == True{}: Bool} -> {x == y: A},
  a: Maybe<&2, A>,
  b: Maybe<&2, A>
) -> {Maybe.is_eq(~A, ~eq, a, b) == True{}: Bool} -> {a == b: Maybe<&2, A>}:
  match a b:
    case None{} None{}:
      h => {==}
    case None{} Some{y}:
      h => Empty.absurd({None{} == Some{y}: Maybe<&2, A>}, Bool.false_ne_true(h))
    case Some{x} None{}:
      h => Empty.absurd({Some{x} == None{}: Maybe<&2, A>}, Bool.false_ne_true(h))
    case Some{+x} Some{y}:
      h =>
        %eqs(x)(y)(h): {Some{x} == Some{_}: Maybe<&2, A>}
        {==}

# Maybe.is_eq is True for a value and itself
def Maybe.is_eq_refl(
  ~A: Data,
  ~eq: A -> A -> Bool,
  ~laws: Eq.Laws(A, eq),
  a: Maybe<&2, A>
) -> {Maybe.is_eq(~A, ~eq, a, a) == True{}: Bool}:
  match a:
    case None{}:
      {==}
    case Some{x}:
      Eq.refl(~A, ~eq, laws, x)

# a read m then k that gives x still gives x when m and each k keep what they
# give (m2 and k2): a kept read of a kept read is kept
def Maybe.bind_kept(
  -A: Data,
  -B: Data,
  m: Maybe<&2, A>,
  -m2: Maybe<&2, A>,
  -k: A -> Maybe<&2, B>,
  -k2: A -> Maybe<&2, B>,
  -x: B,
  hm: @a: A -> {m == Some{a}: Maybe<&2, A>} -> {m2 == Some{a}: Maybe<&2, A>},
  hk: @a: A -> {k(a) == Some{x}: Maybe<&2, B>} -> {k2(a) == Some{x}: Maybe<&2, B>}
) -> {
  Maybe.bind(&2, A, B, m, k) == Some{x}: Maybe<&2, B>
} -> {Maybe.bind(&2, A, B, m2, k2) == Some{x}: Maybe<&2, B>}:
  match m:
    case Some{+a}:
      h =>
        %Equal.sym(
          Maybe<&2, A>,
          m2,
          Some{a},
          hm(a)({==})
        ): {Maybe.bind(&2, A, B, _, k2) == Some{x}: Maybe<&2, B>}
        hk(a)(h)
    case None{}:
      h => Empty.absurd(
        {Maybe.bind(&2, A, B, m2, k2) == Some{x}: Maybe<&2, B>},
        Maybe.none_ne_some(B, x, h)
      )

# k when b holds, else nothing
def Maybe.when(-B: Data, b: Bool, k: Unit -> Maybe<&2, B>) -> Maybe<&2, B>:
  match b:
    case True{}:
      k(Unit{})
    case False{}:
      None{}

# a "when" that gives a value holds
def Maybe.when_hit(
  -B: Data,
  b: Bool,
  -k: Unit -> Maybe<&2, B>,
  -y: B
) -> {Maybe.when(B, b, k) == Some{y}: Maybe<&2, B>} -> {b == True{}: Bool}:
  match b:
    case True{}:
      e => {==}
    case False{}:
      e => Empty.absurd({False{} == True{}: Bool}, Maybe.none_ne_some(B, y, e))

# a "when" that gives a value gives what its rest gives
def Maybe.when_rest(
  -B: Data,
  b: Bool,
  -k: Unit -> Maybe<&2, B>,
  -y: B
) -> {Maybe.when(B, b, k) == Some{y}: Maybe<&2, B>} -> {k(Unit{}) == Some{y}: Maybe<&2, B>}:
  match b:
    case True{}:
      e => e
    case False{}:
      e => Empty.absurd({k(Unit{}) == Some{y}: Maybe<&2, B>}, Maybe.none_ne_some(B, y, e))

# a read m then k that gives x: m gives a value, and k gives x of it
def Maybe.bind_some(
  -A: Data,
  -B: Data,
  -R: Type,
  m: Maybe<&2, A>,
  -k: A -> Maybe<&2, B>,
  -x: B
) -> {
  Maybe.bind(&2, A, B, m, k) == Some{x}: Maybe<&2, B>
} -> (@a: A -> {m == Some{a}: Maybe<&2, A>} -> {k(a) == Some{x}: Maybe<&2, B>} -> R) -> R:
  match m:
    case Some{a}:
      e => f => f(a)({==})(e)
    case None{}:
      e => f => Empty.absurd(R, Maybe.none_ne_some(B, x, e))

# List equality
# -------------
# xs and ys hold the same elements in the same order, as same calls them: the
# check stops at the first difference
def List.is_eq(~A: Data, ~same: A -> A -> Bool, xs: List<&2, A>, ys: List<&2, A>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{x, xr} Con{y, yr}:
      List.all.if(u => List.is_eq(~A, ~same, xr, yr), same(x, y))
    case _ _:
      False{}

# List.is_eq is True for a list and itself
def List.is_eq_refl(
  ~Ty: Data,
  ~same: Ty -> Ty -> Bool,
  ~laws: Eq.Laws(Ty, same),
  xs: List<&2, Ty>
) -> {List.is_eq(~Ty, ~same, xs, xs) == True{}: Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, r}:
      %Equal.sym(
        Bool,
        same(x, x),
        True{},
        Eq.refl(~Ty, ~same, laws, x)
      ): {List.all.if(u => List.is_eq(~Ty, ~same, r, r), _) == True{}: Bool}
      List.is_eq_refl(~Ty, ~same, ~laws, r)

# List.is_eq is True only for equal lists
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
def List.is_eq_sound(
  ~Ty: Data,
  ~same: Ty -> Ty -> Bool,
  ~laws: Eq.Laws(Ty, same),
  xs: List<&2, Ty>,
  ys: List<&2, Ty>
) -> {List.is_eq(~Ty, ~same, xs, ys) == True{}: Bool} -> {xs == ys: List<&2, Ty>}:
  match xs ys:
    case Nil{} Nil{}:
      h => {==}
    case Nil{} Con{y, yr}:
      h => Empty.absurd({Nil{} == Con{y, yr}: List<&2, Ty>}, Bool.false_ne_true(h))
    case Con{x, xr} Nil{}:
      h => Empty.absurd({Con{x, xr} == Nil{}: List<&2, Ty>}, Bool.false_ne_true(h))
    case Con{+x, +xr} Con{+y, +yr}:
      +h =>
        +iseq1 = List.is_eq(~Ty, ~same, xr, yr)
        %Eq.sound(
          ~Ty,
          ~same,
          laws,
          x,
          y
        )(List.all.if_hit(same(x, y), u => iseq1)(h)): {x <> xr == _ <> yr: List<&2, Ty>}
        %List.is_eq_sound(~Ty, ~same, ~laws, xr, yr)(List.all.if_rest(same(x, y), u => iseq1)(h)):
          {x <> xr == x <> _: List<&2, Ty>}
        {==}
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# the laws of List.is_eq, by the laws of same
def List.laws(
  ~A: Data,
  ~same: A -> A -> Bool,
  ~laws: Eq.Laws(A, same)
) -> Eq.Laws(List<&2, A>, List.is_eq(~A, ~same)):
  (
    xs => List.is_eq_refl(~A, ~same, ~laws, xs),
    xs => ys => List.is_eq_sound(~A, ~same, ~laws, xs, ys)
  )

# Joins of Maybes
# ---------------
# None is below every value: a join keeps what either side holds, and joins
# two values with join.

# what a and b hold, joined
def Maybe.join(~V: Data, ~join: V -> V -> V, a: Maybe<&2, V>, b: Maybe<&2, V>) -> Maybe<&2, V>:
  match a b:
    case None{} y:
      y
    case Some{x} None{}:
      Some{x}
    case Some{x} Some{y}:
      Some{join(x, y)}

# nothing joined to a is a
def Maybe.join_none(
  ~V: Data,
  ~join: V -> V -> V,
  a: Maybe<&2, V>
) -> {Maybe.join(~V, ~join, a, None{}) == a: Maybe<&2, V>}:
  match a:
    case None{}:
      {==}
    case Some{x}:
      {==}

# a join is the same either way round, when join is
def Maybe.join_comm(
  ~V: Data,
  ~join: V -> V -> V,
  ~comm: @x: V -> @y: V -> {join(x, y) == join(y, x): V},
  a: Maybe<&2, V>,
  b: Maybe<&2, V>
) -> {Maybe.join(~V, ~join, a, b) == Maybe.join(~V, ~join, b, a): Maybe<&2, V>}:
  match a b:
    case None{} None{}:
      {==}
    case None{} Some{y}:
      {==}
    case Some{x} None{}:
      {==}
    case Some{x} Some{y}:
      %comm(x)(y): {Some{join(x, y)} == Some{_}: Maybe<&2, V>}
      {==}

# a join groups either way, when join does
def Maybe.join_assoc(
  ~V: Data,
  ~join: V -> V -> V,
  ~assoc: @x: V -> @y: V -> @z: V -> {join(join(x, y), z) == join(x, join(y, z)): V},
  a: Maybe<&2, V>,
  b: Maybe<&2, V>,
  c: Maybe<&2, V>
) -> {
  Maybe.join(
    ~V,
    ~join,
    Maybe.join(~V, ~join, a, b),
    c
  )
    == Maybe.join(~V, ~join, a, Maybe.join(~V, ~join, b, c)): Maybe<&2, V>
}:
  match a b c:
    case None{} y w:
      {==}
    case Some{x} None{} w:
      {==}
    case Some{x} Some{y} None{}:
      {==}
    case Some{x} Some{y} Some{w}:
      %assoc(x)(y)(w): {Some{join(join(x, y), w)} == Some{_}: Maybe<&2, V>}
      {==}

# a value joined with itself is itself, when join is idempotent
def Maybe.join_idem(
  ~V: Data,
  ~join: V -> V -> V,
  ~idem: @x: V -> {join(x, x) == x: V},
  a: Maybe<&2, V>
) -> {Maybe.join(~V, ~join, a, a) == a: Maybe<&2, V>}:
  match a:
    case None{}:
      {==}
    case Some{x}:
      %Equal.sym(V, join(x, x), x, idem(x)): {Some{_} == Some{x}: Maybe<&2, V>}
      {==}

# Pairwise checks
# ---------------

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a check that proofs split on keeps each and as one value
# r holds of each element of xs and the element of ys at its place, and the
# lists are as long
def List.all2(~A: Data, ~B: Data, ~r: A -> B -> Bool, xs: List<&2, A>, ys: List<&2, B>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{x, rx} Con{y, ry}:
      Bool.and(r(x, y), List.all2(~A, ~B, ~r, rx, ry))
    case _ _:
      False{}
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# a number at most zero is zero
def Nat.le_zero_eq(a: Nat) -> {Nat.is_le(a, 0n) == True{}: Bool} -> {a == 0n: Nat}:
  match a:
    case 0n:
      h => {==}
    case 1n+p:
      h => Empty.absurd({1n+p == 0n: Nat}, Bool.false_ne_true(h))

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# a number at most 1 + p that is not 1 + p is at most p
def Nat.le_step(
  a: Nat,
  p: Nat
) -> {
  Nat.is_le(a, 1n+p) == True{}: Bool
} -> {Nat.is_eq(a, 1n+p) == False{}: Bool} -> {Nat.is_le(a, p) == True{}: Bool}:
  match a p:
    case 0n q:
      h => k => Nat.le_zero(q)
    case 1n+0n 0n:
      h => k => Equal.sym(Bool, True{}, False{}, k)
    case 2n+b 0n:
      h => k => h
    case 1n+b 1n+q:
      h => k => Nat.le_step(b, q)(h)(k)

# a number that is at most another, and that is not below it, is that number
def Nat.le_nlt_eq(
  a: Nat,
  b: Nat
) -> {Nat.is_le(a, b) == True{}: Bool} -> {Nat.is_le(1n+a, b) == False{}: Bool} -> {a == b: Nat}:
  match a b:
    case 0n 0n:
      h => k => {==}
    case 0n 1n+q:
      h => k => Empty.absurd(
        {0n == 1n+q: Nat},
        Bool.false_ne_true(
          Equal.trans(
            Bool,
            False{},
            Nat.is_le(0n, q),
            True{},
            Equal.sym(Bool, Nat.is_le(0n, q), False{}, k),
            Nat.le_zero(q)
          )
        )
      )
    case 1n+p 0n:
      h => k => Empty.absurd({1n+p == 0n: Nat}, Bool.false_ne_true(h))
    case 1n+p 1n+q:
      h => k => Equal.cong(Nat, Nat, z => 1n+z, p, q, Nat.le_nlt_eq(p, q)(h)(k))
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# of two numbers, one is at most the other
def Nat.nle_le(
  a: Nat,
  b: Nat
) -> {Nat.is_le(a, b) == False{}: Bool} -> {Nat.is_le(b, a) == True{}: Bool}:
  match a b:
    case 0n 0n:
      h => {==}
    case 0n 1n+q:
      h => Equal.sym(Bool, True{}, False{}, h)
    case 1n+p 0n:
      h => {==}
    case 1n+p 1n+q:
      h => Nat.nle_le(p, q)(h)
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# a number not less than another is at least it
def Nat.nlt_le(
  a: Nat,
  b: Nat
) -> {Nat.is_lt(a, b) == False{}: Bool} -> {Nat.is_le(b, a) == True{}: Bool}:
  match a b:
    case 0n 0n:
      h => {==}
    case 0n 1n+q:
      h => Equal.sym(Bool, True{}, False{}, h)
    case 1n+p 0n:
      h => {==}
    case 1n+p 1n+q:
      h => Nat.nlt_le(p, q)(h)

# x is at least q exactly when it is at least p and q, when p <= q
def Nat.le_above.g1(
  +p: Nat,
  +q: Nat,
  +x: Nat,
  x1: {Nat.is_le(p, q) == True{}: Bool}
) -> {Nat.is_le(q, x) == Bool.and(Nat.is_le(p, x), Nat.is_le(q, x)): Bool}:
  match p:
    case 0n:
      match x:
        case 0n:
          {==}
        case 1n+xp:
          {==}
    case 1n+pp:
      match q:
        case 0n:
          Empty.absurd(
            {Nat.is_le(0n, x) == Bool.and(Nat.is_le(1n+pp, x), Nat.is_le(0n, x)): Bool},
            {(%x1: {\{False: Unit; \{True: Empty; \{}}}: Bool -> Type}(_); Unit{}): Empty}
          )
        case 1n+qp:
          match x:
            case 0n:
              {==}
            case 1n+xp:
              %Nat.le_above.g1(pp, qp, xp, x1):
                {Nat.is_le(qp, xp) == _: Bool}
              {==}

def Nat.le_above(
  p: Nat,
  q: Nat,
  x: Nat
) -> {
  Nat.is_le(p, q) == True{}: Bool
} -> {Nat.is_le(q, x) == Bool.and(Nat.is_le(p, x), Nat.is_le(q, x)): Bool}:
  x1 => Nat.le_above.g1(p, q, x, x1)

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# x is at least p exactly when it is at least p and q, when q < p
def Nat.le_above_not.g2(
  +p: Nat,
  +q: Nat,
  x: Nat,
  x1: {Nat.is_le(p, q) == False{}: Bool},
  +x2: Bool,
  hx2: {x2 == Nat.is_le(p, x): Bool}
) -> {x2 == Bool.and(x2, Nat.is_le(q, x)): Bool}:
  match x2:
    case False{}:
      {==}
    case True{}:
      Equal.sym(
        Bool,
        Bool.and(True{}, Nat.is_le(q, x)),
        True{},
        Nat.le_trans(
          q,
          p,
          x
        )(Nat.nle_le(p, q)(x1))(Equal.sym(Bool, True{}, Cmp.is_le(Nat.cmp(p, x)), hx2))
      )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
def Nat.le_above_not(
  +p: Nat,
  q: Nat,
  +x: Nat
) -> {
  Nat.is_le(p, q) == False{}: Bool
} -> {Nat.is_le(p, x) == Bool.and(Nat.is_le(p, x), Nat.is_le(q, x)): Bool}:
  x1 => Nat.le_above_not.g2(p, q, x, x1, Nat.is_le(p, x), {==})

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# x is at most h exactly when it is at most h and b, when h <= b
def Nat.le_upto.g2(
  h: Nat,
  b: Nat,
  x: Nat,
  x1: {Nat.is_le(h, b) == True{}: Bool},
  +x2: Bool,
  hx2: {x2 == Nat.is_le(x, h): Bool}
) -> {x2 == Bool.and(x2, Nat.is_le(x, b)): Bool}:
  match x2:
    case False{}:
      {==}
    case True{}:
      Equal.sym(
        Bool,
        Cmp.is_le(Nat.cmp(x, b)),
        True{},
        Nat.le_trans(x, h, b)(Equal.sym(Bool, True{}, Cmp.is_le(Nat.cmp(x, h)), hx2))(x1)
      )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
def Nat.le_upto(
  +h: Nat,
  b: Nat,
  +x: Nat
) -> {
  Nat.is_le(h, b) == True{}: Bool
} -> {Nat.is_le(x, h) == Bool.and(Nat.is_le(x, h), Nat.is_le(x, b)): Bool}:
  x1 => Nat.le_upto.g2(h, b, x, x1, Nat.is_le(x, h), {==})

# x is at most b exactly when it is at most h and b, when b < h
def Nat.le_upto_not.g1(
  +h: Nat,
  +b: Nat,
  +x: Nat,
  x1: {Nat.is_le(h, b) == False{}: Bool}
) -> {Nat.is_le(x, b) == Bool.and(Nat.is_le(x, h), Nat.is_le(x, b)): Bool}:
  match h:
    case 0n:
      match b:
        case 0n:
          Empty.absurd(
            {Nat.is_le(x, 0n) == Bool.and(Nat.is_le(x, 0n), Nat.is_le(x, 0n)): Bool},
            {(%x1: {\{False: Empty; \{True: Unit; \{}}}: Bool -> Type}(_); Unit{}): Empty}
          )
        case 1n+bp:
          Empty.absurd(
            {Nat.is_le(x, 1n+bp) == Bool.and(Nat.is_le(x, 0n), Nat.is_le(x, 1n+bp)): Bool},
            {(%x1: {\{False: Empty; \{True: Unit; \{}}}: Bool -> Type}(_); Unit{}): Empty}
          )
    case 1n+hp:
      match b:
        case 0n:
          match x:
            case 0n:
              {==}
            case 1n+xp:
              %Equal.sym(
                Bool,
                Bool.and(Cmp.is_le(Nat.cmp(xp, hp)), False{}),
                False{},
                Bool.and_false_right(Cmp.is_le(Nat.cmp(xp, hp)))
              ):
                {False{} == _: Bool}
              {==}
        case 1n+bp:
          match x:
            case 0n:
              {==}
            case 1n+xp:
              %Nat.le_upto_not.g1(hp, bp, xp, x1):
                {Nat.is_le(xp, bp) == _: Bool}
              {==}

def Nat.le_upto_not(
  h: Nat,
  b: Nat,
  x: Nat
) -> {
  Nat.is_le(h, b) == False{}: Bool
} -> {Nat.is_le(x, b) == Bool.and(Nat.is_le(x, h), Nat.is_le(x, b)): Bool}:
  x1 => Nat.le_upto_not.g1(h, b, x, x1)

# a number at most b is not above b
def Nat.le_nlt(
  a: Nat,
  b: Nat
) -> {Nat.is_le(a, b) == True{}: Bool} -> {Nat.is_lt(b, a) == False{}: Bool}:
  match a b:
    case 0n 0n:
      h => {==}
    case 0n 1n+q:
      h => {==}
    case 1n+p 0n:
      h => Empty.absurd({Nat.is_lt(0n, 1n+p) == False{}: Bool}, Bool.false_ne_true(h))
    case 1n+p 1n+q:
      h => Nat.le_nlt(p, q)(h)
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# a number is at most its sum with another
def Nat.le_add(y: Nat, +m: Nat) -> {Nat.is_le(m, Nat.add(y, m)) == True{}: Bool}:
  match y:
    case 0n:
      Nat.le_refl(m)
    case 1n+(+p):
      Nat.le_succ(m, Nat.add(p, m))(Nat.le_add(p, m))

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# Nat.pigeon, with the second terms of the sums apart (g and m)
def Nat.pigeon.at(
  f: Nat,
  n: Nat,
  +y: Nat,
  +t: Nat,
  +g: Nat,
  +m: Nat
) -> {Nat.is_le(f, n) == True{}: Bool}
  -> {Nat.is_lt(n, y) == True{}: Bool}
  -> {Nat.is_le(g, m) == True{}: Bool}
  -> {Nat.is_le(Nat.add(y, m), t) == True{}: Bool}
  -> {Nat.is_lt(t, Nat.add(f, g)) == True{}: Bool}
  -> Empty:
  match f n y t:
    case 0n n1 y1 t1:
      h1 => h2 => hg => h3 => h4 =>
        Bool.false_ne_true(
          Equal.trans(
            Bool,
            False{},
            Nat.is_lt(g, g),
            True{},
            Equal.sym(Bool, Nat.is_lt(g, g), False{}, Nat.lt_irrefl(g)),
            Nat.le_lt(
              g,
              t1,
              g
            )(
              Nat.le_trans(g, m, t1)(hg)(Nat.le_trans(m, Nat.add(y1, m), t1)(Nat.le_add(y1, m))(h3))
            )(h4)
          )
        )
    case 1n+p 0n y1 t1:
      h1 => h2 => hg => h3 => h4 => Bool.false_ne_true(h1)
    case 1n+p 1n+q 0n t1:
      h1 => h2 => hg => h3 => h4 => Bool.false_ne_true(h2)
    case 1n+p 1n+q 1n+z 0n:
      h1 => h2 => hg => h3 => h4 => Bool.false_ne_true(h3)
    case 1n+p 1n+q 1n+z 1n+u:
      h1 => h2 => hg => h3 => h4 => Nat.pigeon.at(p, q, z, u, g, m)(h1)(h2)(hg)(h3)(h4)
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# f is at most n, n is less than y, and y + n is at most t: t is not less
# than f + f
def Nat.pigeon(+f: Nat, +n: Nat, y: Nat, t: Nat) -> {Nat.is_le(f, n) == True{}: Bool}
  -> {Nat.is_lt(n, y) == True{}: Bool}
  -> {Nat.is_le(Nat.add(y, n), t) == True{}: Bool}
  -> {Nat.is_lt(t, Nat.add(f, f)) == True{}: Bool}
  -> Empty:
  +h1 => h2 => h3 => h4 => Nat.pigeon.at(f, n, y, t, f, n)(h1)(h2)(h1)(h3)(h4)

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# a is not at most c, and b is: a is not at most b
def Nat.nle_trans.at(a: Nat, b: Nat, c: Nat, x: Bool) -> {Nat.is_le(a, b) == x: Bool}
  -> {Nat.is_le(a, c) == False{}: Bool}
  -> {Nat.is_le(b, c) == True{}: Bool}
  -> {x == False{}: Bool}:
  match x:
    case True{}:
      ex => h => k =>
        Equal.trans(
          Bool,
          True{},
          Nat.is_le(a, c),
          False{},
          Equal.sym(Bool, Nat.is_le(a, c), True{}, Nat.le_trans(a, b, c)(ex)(k)),
          h
        )
    case False{}:
      ex => h => k => {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# a is not at most c, and b is: a is not at most b
def Nat.nle_trans(
  +a: Nat,
  +b: Nat,
  c: Nat
) -> {
  Nat.is_le(a, c) == False{}: Bool
} -> {Nat.is_le(b, c) == True{}: Bool} -> {Nat.is_le(a, b) == False{}: Bool}:
  h => k => Nat.nle_trans.at(a, b, c, Nat.is_le(a, b))({==})(h)(k)

# a number is zero
def Nat.IsZero(n: Nat) -> Type:
  match n:
    case 0n:
      Unit
    case 1n+p:
      Empty

# zero is no successor
def Nat.zero_ne_succ(-b: Nat, e: {0n == 1n+b: Nat}) -> Empty:
  %e: Nat.IsZero(_)
  Unit{}

# the number before n, 0 before 0
def Nat.before(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

# successors are the same only of the same numbers
def Nat.succ_inj(-a: Nat, -b: Nat, e: {1n+a == 1n+b: Nat}) -> {a == b: Nat}:
  Equal.cong(Nat, Nat, Nat.before, 1n+a, 1n+b, e)

# p holds of g and each element of xs
def List.holds(~A: Data, ~V: Data, ~p: V -> A -> Bool, xs: List<&2, A>, +g: V) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, r}:
      List.all.if(u => List.holds(~A, ~V, ~p, r, g), p(g)(x))

# p holds of g and some element of xs
def List.some(~A: Data, ~V: Data, ~p: V -> A -> Bool, xs: List<&2, A>, +g: V) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{x, r}:
      List.any.if(u => List.some(~A, ~V, ~p, r, g), p(g)(x))

# List.keep_holds at one element, once p is known to keep it or not (k)
def List.keep_holds.at(
  ~A: Data,
  ~V: Data,
  ~p: V -> A -> Bool,
  k: Bool,
  x: A,
  ks: List<&2, A>,
  +g: V,
  ek: {p(g)(x) == k: Bool},
  ih: {List.holds(~A, ~V, ~p, ks, g) == True{}: Bool}
) -> {List.holds(~A, ~V, ~p, List.filter.put(A, x, ks, k), g) == True{}: Bool}:
  match k:
    case True{}:
      List.all.if_both(p(g)(x), u => List.holds(~A, ~V, ~p, ks, g))(ek)(ih)
    case False{}:
      ih

# what List.keep keeps, p holds of
def List.keep_holds(
  ~A: Data,
  ~V: Data,
  ~p: V -> A -> Bool,
  xs: List<&2, A>,
  +g: V
) -> {List.holds(~A, ~V, ~p, List.keep(~A, ~V, ~p, xs, g), g) == True{}: Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      List.keep_holds.at(
        ~A,
        ~V,
        ~p,
        p(g)(x),
        x,
        List.keep(~A, ~V, ~p, r, g),
        g,
        {==},
        List.keep_holds(~A, ~V, ~p, r, g)
      )

# lists one after the other can be put together in any order
def List.append_assoc(
  -A: Data,
  xs: List<&2, A>,
  ys: List<&2, A>,
  zs: List<&2, A>
) -> {
  List.append(
    &2,
    A,
    List.append(&2, A, xs, ys),
    zs
  )
    == List.append(&2, A, xs, List.append(&2, A, ys, zs)): List<&2, A>
}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, r}:
      %List.append_assoc(
        A,
        r,
        ys,
        zs
      ): {x <> List.append(&2, A, List.append(&2, A, r, ys), zs) == x <> _: List<&2, A>}
      {==}

# Bool algebra
# ------------
# Each lemma states the simpler side first, so a rewrite with it turns a term
# into its simpler form.

# no True equals False
def Bool.true_ne_false(e: {True{} == False{}: Bool}) -> Empty:
  %e: Bool.pick(Type, _, Unit, Empty)
  Unit{}

# a or False is a
def Bool.or_false(a: Bool) -> {a == Bool.or(a, False{}): Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# the four parts of two ands, paired the other way
def Bool.and_swap(
  a: Bool,
  b: Bool,
  c: Bool,
  d: Bool
) -> {Bool.and(Bool.and(a, b), Bool.and(c, d)) == Bool.and(Bool.and(a, c), Bool.and(b, d)): Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      match b:
        case False{}:
          %Equal.sym(Bool, Bool.and(c, False{}), False{}, Bool.and_false_right(c)):
            {False{} == _: Bool}
          {==}
        case True{}:
          {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# a and True is a
def Bool.and_true(a: Bool) -> {a == Bool.and(a, True{}): Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

# or is associative
def Bool.or_assoc(
  a: Bool,
  b: Bool,
  c: Bool
) -> {Bool.or(a, Bool.or(b, c)) == Bool.or(Bool.or(a, b), c): Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

# and is associative
def Bool.and_assoc(
  a: Bool,
  b: Bool,
  c: Bool
) -> {Bool.and(a, Bool.and(b, c)) == Bool.and(Bool.and(a, b), c): Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

# and distributes over or, from the right
def Bool.and_or(
  a: Bool,
  b: Bool,
  c: Bool
) -> {Bool.or(Bool.and(a, c), Bool.and(b, c)) == Bool.and(Bool.or(a, b), c): Bool}:
  match a b c:
    case False{} False{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} True{} True{}:
      {==}

# the first two of three or-ed values can swap
def Bool.or_swap(
  a: Bool,
  b: Bool,
  c: Bool
) -> {Bool.or(a, Bool.or(b, c)) == Bool.or(b, Bool.or(a, c)): Bool}:
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

# Char equality
# -------------

# Char.is_eq is True for a character and itself
def Char.is_eq_refl(a: Char) -> {Char.is_eq(a, a) == True{}: Bool}:
  match a:
    case Chr{x}:
      U32.is_eq_refl(x)

# Char.is_eq is True only for equal characters
def Char.is_eq_sound(a: Char, b: Char) -> {Char.is_eq(a, b) == True{}: Bool} -> {a == b: Char}:
  match a b:
    case Chr{x} Chr{y}:
      h => Equal.cong(U32, Char, u => Chr{u}, x, y, U32.is_eq_sound(x, y)(h))

# the laws of Char.is_eq
def Char.laws() -> Eq.Laws(Char, Char.is_eq):
  (Char.is_eq_refl, Char.is_eq_sound)

# Comparison lemmas
# -----------------

# an EQ comparison answers True to Cmp.is_eq
def Cmp.is_eq_of(-c: Cmp, e: {EQ{} == c: Cmp}) -> {Cmp.is_eq(c) == True{}: Bool}:
  %e: {Cmp.is_eq(_) == True{}: Bool}
  {==}

# a U32 comparison is EQ both ways round or neither
# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in this proof the second use sits in a rewrite motive or an erased argument; the checker accepts it
def U32.cmp_swap_eq(
  +x: U32,
  y: U32,
  e: {EQ{} == U32.cmp(x, y): Cmp}
) -> {EQ{} == U32.cmp(y, x): Cmp}:
  %U32.is_eq_sound(x, y)(Cmp.is_eq_of(U32.cmp(x, y), e)): {EQ{} == U32.cmp(_, x): Cmp}
  Equal.sym(Cmp, U32.cmp(x, x), EQ{}, U32.cmp_refl(x))
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# Lazy "and" and "or"
# -------------------
# List.all.if and List.any.if run their rest only when it decides the answer.
# These lemmas turn them into Bool.and and Bool.or, for the Bool algebra.

# a lazy "and" is Bool.and
def List.all.if_and(
  hit: Bool,
  rest: Unit -> Bool
) -> {List.all.if(rest, hit) == Bool.and(hit, rest(Unit{})): Bool}:
  match hit:
    case False{}:
      {==}
    case True{}:
      {==}

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# List.contains as a List.some, with p the test of eq against each value
def List.contains_some(
  ~A: Data,
  ~eq: A -> A -> Bool,
  l: List<&2, A>,
  d: A
) -> {List.contains(~A, ~eq, l, d) == List.some(~A, ~A, ~(g => x => eq(x, g)), l, d): Bool}:
  match l:
    case Nil{}:
      {==}
    case Con{x, r}:
      %Equal.sym(
        Bool,
        List.contains(~A, ~eq, r, d),
        List.some(~A, ~A, ~(g => x => eq(x, g)), r, d),
        List.contains_some(~A, ~eq, r, d)
      ): {
        List.any.if(
          u => _,
          eq(x, d)
        )
          == List.any.if(u => List.some(~A, ~A, ~(g => x => eq(x, g)), r, d), eq(x, d)): Bool
      }
      {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# a lazy "or" is Bool.or
def List.any.if_or(
  hit: Bool,
  rest: Unit -> Bool
) -> {List.any.if(rest, hit) == Bool.or(hit, rest(Unit{})): Bool}:
  match hit:
    case False{}:
      {==}
    case True{}:
      {==}

# a lazy or of two ands with the same first part h
def List.any.if_and(
  h: Bool,
  x: Bool,
  t: Bool
) -> {
  List.any.if(u => Bool.and(h, t), Bool.and(h, x)) == Bool.and(h, List.any.if(u => t, x)): Bool
}:
  match h:
    case False{}:
      {==}
    case True{}:
      {==}

# Members and others
# ------------------

# List.some_append at the first element, by whether p holds of it (hit)
def List.some_append.at(
  ~A: Data,
  ~V: Data,
  ~p: V -> A -> Bool,
  hit: Bool,
  r: List<&2, A>,
  b: List<&2, A>,
  g: V,
  ih: {
    List.some(
      ~A,
      ~V,
      ~p,
      List.append(&2, A, r, b),
      g
    )
      == Bool.or(List.some(~A, ~V, ~p, r, g), List.some(~A, ~V, ~p, b, g)): Bool
  }
) -> {
  List.any.if(
    u => List.some(~A, ~V, ~p, List.append(&2, A, r, b), g),
    hit
  )
    == Bool.or(
      List.any.if(u => List.some(~A, ~V, ~p, r, g), hit),
      List.some(~A, ~V, ~p, b, g)
    ): Bool
}:
  match hit:
    case True{}:
      {==}
    case False{}:
      ih

# p holds of some element of a ++ b exactly when of some of a or of some of b
def List.some_append(
  ~A: Data,
  ~V: Data,
  ~p: V -> A -> Bool,
  a: List<&2, A>,
  +b: List<&2, A>,
  +g: V
) -> {
  List.some(
    ~A,
    ~V,
    ~p,
    List.append(&2, A, a, b),
    g
  )
    == Bool.or(List.some(~A, ~V, ~p, a, g), List.some(~A, ~V, ~p, b, g)): Bool
}:
  match a:
    case Nil{}:
      {==}
    case Con{x, +r}:
      List.some_append.at(~A, ~V, ~p, p(g)(x), r, b, g, List.some_append(~A, ~V, ~p, r, b, g))

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# List.some_member at the first element y, by whether it is x (hit)
def List.some_member.at(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~p: V -> A -> Bool,
  ~laws: Eq.Laws(A, same),
  hit: Bool,
  y: A,
  r: List<&2, A>,
  x: A,
  g: V,
  ey: {same(y, x) == hit: Bool},
  hc: {List.any.if(u => List.contains(~A, ~same, r, x), hit) == True{}: Bool},
  hp: {p(g)(x) == True{}: Bool},
  ih: {
    List.contains(~A, ~same, r, x) == True{}: Bool
  } -> {p(g)(x) == True{}: Bool} -> {List.some(~A, ~V, ~p, r, g) == True{}: Bool}
) -> {List.any.if(u => List.some(~A, ~V, ~p, r, g), p(g)(y)) == True{}: Bool}:
  match hit:
    case True{}:
      %Equal.sym(A, y, x, Eq.sound(~A, ~same, laws, y, x)(ey)):
        {List.any.if(u => List.some(~A, ~V, ~p, r, g), p(g)(_)) == True{}: Bool}
      %Equal.sym(Bool, p(g)(x), True{}, hp):
        {List.any.if(u => List.some(~A, ~V, ~p, r, g), _) == True{}: Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, List.some(~A, ~V, ~p, r, g), True{}, ih(hc)(hp)):
        {List.any.if(u => _, p(g)(y)) == True{}: Bool}
      List.any.if_true(p(g)(y))
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# p holds of some element of xs when it holds of a member of xs
def List.some_member(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~p: V -> A -> Bool,
  ~laws: Eq.Laws(A, same),
  xs: List<&2, A>,
  +x: A,
  +g: V
) -> {
  List.contains(~A, ~same, xs, x) == True{}: Bool
} -> {p(g)(x) == True{}: Bool} -> {List.some(~A, ~V, ~p, xs, g) == True{}: Bool}:
  match xs:
    case Nil{}:
      hc => Empty.absurd(
        {p(g)(x) == True{}: Bool} -> {False{} == True{}: Bool},
        Bool.false_ne_true(hc)
      )
    case Con{+y, +r}:
      hc => hp => List.some_member.at(
        ~A,
        ~V,
        ~same,
        ~p,
        ~laws,
        same(y, x),
        y,
        r,
        x,
        g,
        {==},
        hc,
        hp,
        List.some_member(~A, ~V, ~same, ~p, ~laws, r, x, g)
      )

# reversing xs onto acc holds m exactly when xs or acc holds m
def List.contains_reverse(
  ~A: Data,
  ~same: A -> A -> Bool,
  xs: List<&2, A>,
  +acc: List<&2, A>,
  +m: A
) -> {
  Bool.or(
    List.contains(~A, ~same, xs, m),
    List.contains(~A, ~same, acc, m)
  )
    == List.contains(~A, ~same, List.reverse.go(&2, A, xs, acc), m): Bool
}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      +e = same(h, m)
      +ct = List.contains(~A, ~same, t, m)
      +ca = List.contains(~A, ~same, acc, m)
      l = Bool.or(List.contains(~A, ~same, h <> t, m), ca)
      %List.contains_reverse(~A, ~same, t, h <> acc, m): {l == _: Bool}
      %Equal.sym(
        Bool,
        List.any.if(u => ca, e),
        Bool.or(e, ca),
        List.any.if_or(e, u => ca)
      ): {l == Bool.or(ct, _): Bool}
      %Equal.sym(
        Bool,
        List.any.if(u => ct, e),
        Bool.or(e, ct),
        List.any.if_or(e, u => ct)
      ): {Bool.or(_, ca) == Bool.or(ct, Bool.or(e, ca)): Bool}
      Equal.trans(
        Bool,
        Bool.or(Bool.or(e, ct), ca),
        Bool.or(e, Bool.or(ct, ca)),
        Bool.or(ct, Bool.or(e, ca)),
        Equal.sym(
          Bool,
          Bool.or(e, Bool.or(ct, ca)),
          Bool.or(Bool.or(e, ct), ca),
          Bool.or_assoc(e, ct, ca)
        ),
        Bool.or_swap(e, ct, ca)
      )

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# a number below 1 + p is at most p
def Nat.lt_succ_le(
  a: Nat,
  p: Nat
) -> {Nat.is_lt(a, 1n+p) == True{}: Bool} -> {Nat.is_le(a, p) == True{}: Bool}:
  match a p:
    case 0n q:
      h => Nat.le_zero(q)
    case 1n+0n 0n:
      h => h
    case 2n+b 0n:
      h => h
    case 1n+b 1n+q:
      h => Nat.lt_succ_le(b, q)(h)
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# a number below d is at most the number before d
def Nat.lt_before(
  a: Nat,
  d: Nat
) -> {Nat.is_lt(a, d) == True{}: Bool} -> {Nat.is_le(a, Nat.before(d)) == True{}: Bool}:
  match a d:
    case 0n 0n:
      h => {==}
    case 1n+b 0n:
      h => h
    case 0n 1n+p:
      h => Nat.le_zero(p)
    case 1n+b 1n+p:
      h => Nat.lt_succ_le(1n+b, p)(h)

# Codes of numbers
# ----------------
# U32.to_nat gives the code of a U32: its place in the order, as a Nat. These
# lemmas carry a question about the order of U32 to the Nat order lemmas above.

# a <= b and b <= a together say that a is b
def Nat.le_both(
  a: Nat,
  b: Nat
) -> {Bool.and(Nat.is_le(a, b), Nat.is_le(b, a)) == Nat.is_eq(a, b): Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      Nat.le_both(p, q)

# a number plus one is not at most the number
def Nat.succ_nle(a: Nat) -> {Nat.is_le(1n+a, a) == False{}: Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Nat.succ_nle(p)

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# a number not at most b is at least b plus one
def Nat.nle_succ_le(
  a: Nat,
  b: Nat
) -> {Nat.is_le(a, b) == False{}: Bool} -> {Nat.is_le(1n+b, a) == True{}: Bool}:
  match a b:
    case 0n 0n:
      h => Equal.sym(Bool, True{}, False{}, h)
    case 0n 1n+q:
      h => Equal.sym(Bool, True{}, False{}, h)
    case 1n+p 0n:
      h => Nat.le_zero(p)
    case 1n+p 1n+q:
      Nat.nle_succ_le(p, q)
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# the doubles of two numbers compare as the numbers do; a bit added to each
# double decides only a tie
def Nat.cmp_double(
  a: Nat,
  b: Nat,
  ab: Bool,
  bb: Bool
) -> {
  Word.cmp.fin(
    ab,
    bb,
    Nat.cmp(a, b)
  )
    == Nat.cmp(Nat.add_if(ab, Nat.double(a)), Nat.add_if(bb, Nat.double(b))): Cmp
}:
  match a b ab bb:
    case 0n 0n False{} False{}:
      {==}
    case 0n 0n False{} True{}:
      {==}
    case 0n 0n True{} False{}:
      {==}
    case 0n 0n True{} True{}:
      {==}
    case 0n 1n+q False{} False{}:
      {==}
    case 0n 1n+q False{} True{}:
      {==}
    case 0n 1n+q True{} False{}:
      {==}
    case 0n 1n+q True{} True{}:
      {==}
    case 1n+p 0n False{} False{}:
      {==}
    case 1n+p 0n False{} True{}:
      {==}
    case 1n+p 0n True{} False{}:
      {==}
    case 1n+p 0n True{} True{}:
      {==}
    case 1n+p 1n+q False{} False{}:
      Nat.cmp_double(p, q, False{}, False{})
    case 1n+p 1n+q False{} True{}:
      Nat.cmp_double(p, q, False{}, True{})
    case 1n+p 1n+q True{} False{}:
      Nat.cmp_double(p, q, True{}, False{})
    case 1n+p 1n+q True{} True{}:
      Nat.cmp_double(p, q, True{}, True{})

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Word.cmp_to_nat at the low bits ab and bb, from the same fact of the rests
def Word.cmp_to_nat.con(
  +p: Nat,
  ab: Bool,
  bb: Bool,
  at: Word(p),
  bt: Word(p),
  ih: {Word.cmp(p, at, bt) == Nat.cmp(Word.to_nat(p, at), Word.to_nat(p, bt)): Cmp}
) -> {
  Word.cmp(
    1n+p,
    WCon{ab, at},
    WCon{bb, bt}
  )
    == Nat.cmp(Word.to_nat(1n+p, WCon{ab, at}), Word.to_nat(1n+p, WCon{bb, bt})): Cmp
}:
  match ab bb:
    case False{} False{}:
      %Equal.sym(Cmp, Word.cmp(p, at, bt), Nat.cmp(Word.to_nat(p, at), Word.to_nat(p, bt)), ih):
        {
          Word.cmp.fin(
            False{},
            False{},
            _
          )
            == Nat.cmp(Nat.double(Word.to_nat(p, at)), Nat.double(Word.to_nat(p, bt))): Cmp
        }
      Nat.cmp_double(Word.to_nat(p, at), Word.to_nat(p, bt), False{}, False{})
    case False{} True{}:
      %Equal.sym(Cmp, Word.cmp(p, at, bt), Nat.cmp(Word.to_nat(p, at), Word.to_nat(p, bt)), ih):
        {
          Word.cmp.fin(
            False{},
            True{},
            _
          )
            == Nat.cmp(Nat.double(Word.to_nat(p, at)), 1n+Nat.double(Word.to_nat(p, bt))): Cmp
        }
      Nat.cmp_double(Word.to_nat(p, at), Word.to_nat(p, bt), False{}, True{})
    case True{} False{}:
      %Equal.sym(Cmp, Word.cmp(p, at, bt), Nat.cmp(Word.to_nat(p, at), Word.to_nat(p, bt)), ih):
        {
          Word.cmp.fin(
            True{},
            False{},
            _
          )
            == Nat.cmp(1n+Nat.double(Word.to_nat(p, at)), Nat.double(Word.to_nat(p, bt))): Cmp
        }
      Nat.cmp_double(Word.to_nat(p, at), Word.to_nat(p, bt), True{}, False{})
    case True{} True{}:
      %Equal.sym(Cmp, Word.cmp(p, at, bt), Nat.cmp(Word.to_nat(p, at), Word.to_nat(p, bt)), ih):
        {
          Word.cmp.fin(
            True{},
            True{},
            _
          )
            == Nat.cmp(Nat.double(Word.to_nat(p, at)), Nat.double(Word.to_nat(p, bt))): Cmp
        }
      Nat.cmp_double(Word.to_nat(p, at), Word.to_nat(p, bt), True{}, True{})
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# two words compare as their codes do
def Word.cmp_to_nat(
  +n: Nat,
  a: Word(n),
  b: Word(n)
) -> {Word.cmp(n, a, b) == Nat.cmp(Word.to_nat(n, a), Word.to_nat(n, b)): Cmp}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match a b:
        case WCon{ab, +at} WCon{bb, +bt}:
          Word.cmp_to_nat.con(p, ab, bb, at, bt, Word.cmp_to_nat(p, at, bt))

# two numbers compare as their codes do
def U32.cmp_to_nat(a: U32, b: U32) -> {U32.cmp(a, b) == Nat.cmp(U32.to_nat(a), U32.to_nat(b)): Cmp}:
  match a b:
    case U32{x} U32{y}:
      Word.cmp_to_nat(32n, x, y)

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# the order of U32 is the order of the codes
def U32.is_le_to_nat(
  a: U32,
  b: U32
) -> {U32.is_le(a, b) == Nat.is_le(U32.to_nat(a), U32.to_nat(b)): Bool}:
  Equal.cong(
    Cmp,
    Bool,
    Cmp.is_le,
    U32.cmp(a, b),
    Nat.cmp(U32.to_nat(a), U32.to_nat(b)),
    U32.cmp_to_nat(a, b)
  )

# the order of U32 as the order of codes, for is_lt
def U32.is_lt_to_nat(
  a: U32,
  b: U32
) -> {U32.is_lt(a, b) == Nat.is_lt(U32.to_nat(a), U32.to_nat(b)): Bool}:
  Equal.cong(
    Cmp,
    Bool,
    Cmp.is_lt,
    U32.cmp(a, b),
    Nat.cmp(U32.to_nat(a), U32.to_nat(b)),
    U32.cmp_to_nat(a, b)
  )

# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# Word.le_ones at the low bit b, with t the comparison of the rests
def Word.le_ones.fin(
  b: Bool,
  t: Cmp
) -> {Cmp.is_le(t) == True{}: Bool} -> {Cmp.is_le(Word.cmp.fin(b, True{}, t)) == True{}: Bool}:
  match b t:
    case x LT{}:
      h => {==}
    case False{} EQ{}:
      h => {==}
    case True{} EQ{}:
      h => {==}
    case x GT{}:
      h => h

# no word is above the word of all True bits
def Word.le_ones(
  +n: Nat,
  w: Word(n)
) -> {Cmp.is_le(Word.cmp(n, w, Word.not(n, Word.zero(n)))) == True{}: Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{b, +t}:
          Word.le_ones.fin(b, Word.cmp(p, t, Word.not(p, Word.zero(p))))(Word.le_ones(p, t))

# no number is above the last U32
def U32.le_last(x: U32) -> {U32.is_le(x, 4294967295) == True{}: Bool}:
  match x:
    case U32{w}:
      Word.le_ones(32n, w)

# Word.inc_to_nat for the rest of a word, with t its comparison: a word with a
# True low bit is the word of all True bits only when its rest is
def Word.inc_to_nat.rest(
  t: Cmp
) -> {
  Cmp.is_eq(Word.cmp.fin(True{}, True{}, t)) == False{}: Bool
} -> {Cmp.is_eq(t) == False{}: Bool}:
  match t:
    case LT{}:
      h => h
    case EQ{}:
      h => h
    case GT{}:
      h => h

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# the code of the word after w is one more than the code of w, when w is not
# the word of all True bits
def Word.inc_to_nat(
  +n: Nat,
  w: Word(n)
) -> {
  Cmp.is_eq(Word.cmp(n, w, Word.not(n, Word.zero(n)))) == False{}: Bool
} -> {Word.to_nat(n, Word.inc(n, w)) == 1n+Word.to_nat(n, w): Nat}:
  match n:
    case 0n:
      h => Empty.absurd({0n == 1n: Nat}, Bool.true_ne_false(h))
    case 1n+p:
      match w:
        case WCon{False{}, t}:
          h => {==}
        case WCon{True{}, +t}:
          h => Equal.cong(
            Nat,
            Nat,
            Nat.double,
            Word.to_nat(p, Word.inc(p, t)),
            1n+Word.to_nat(p, t),
            Word.inc_to_nat(
              p,
              t
            )(Word.inc_to_nat.rest(Word.cmp(p, t, Word.not(p, Word.zero(p))))(h))
          )
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# the code of the number after x is one more than the code of x, when x is not
# the last U32
def U32.inc_to_nat(
  x: U32
) -> {
  U32.is_eq(x, 4294967295) == False{}: Bool
} -> {U32.to_nat(U32.inc(x)) == 1n+U32.to_nat(x): Nat}:
  match x:
    case U32{w}:
      Word.inc_to_nat(32n, w)

# Two-way facts
# -------------
