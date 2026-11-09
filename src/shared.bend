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

# an "and" with False is False
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

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# List.contains_keep at the first element x, once p is known to keep it or not (k)
# and x is known to be m or not (hit)
def List.contains_keep.at(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~p: V -> A -> Bool,
  ~laws: Eq.Laws(A, same),
  k: Bool,
  hit: Bool,
  x: A,
  ks: List<&2, A>,
  r: List<&2, A>,
  g: V,
  m: A,
  ek: {p(g)(x) == k: Bool},
  +eh: {same(x, m) == hit: Bool},
  ih: {List.contains(~A, ~same, ks, m) == Bool.and(p(g)(m), List.contains(~A, ~same, r, m)): Bool}
) -> {
  List.contains(
    ~A,
    ~same,
    List.filter.put(A, x, ks, k),
    m
  )
    == Bool.and(p(g)(m), List.any.if(u => List.contains(~A, ~same, r, m), hit)): Bool
}:
  match k hit:
    case True{} True{}:
      %Equal.sym(Bool, same(x, m), True{}, eh):
        {List.any.if(u => List.contains(~A, ~same, ks, m), _) == Bool.and(p(g)(m), True{}): Bool}
      %Eq.sound(~A, ~same, laws, x, m)(eh): {True{} == Bool.and(p(g)(_), True{}): Bool}
      %Equal.sym(Bool, p(g)(x), True{}, ek): {True{} == Bool.and(_, True{}): Bool}
      {==}
    case True{} False{}:
      %Equal.sym(Bool, same(x, m), False{}, eh):
        {
          List.any.if(
            u => List.contains(~A, ~same, ks, m),
            _
          )
            == Bool.and(p(g)(m), List.contains(~A, ~same, r, m)): Bool
        }
      ih
    case False{} True{}:
      %Equal.sym(
        Bool,
        List.contains(~A, ~same, ks, m),
        Bool.and(p(g)(m), List.contains(~A, ~same, r, m)),
        ih
      ):
        {_ == Bool.and(p(g)(m), True{}): Bool}
      %Eq.sound(
        ~A,
        ~same,
        laws,
        x,
        m
      )(eh): {Bool.and(p(g)(_), List.contains(~A, ~same, r, _)) == Bool.and(p(g)(_), True{}): Bool}
      %Equal.sym(
        Bool,
        p(g)(x),
        False{},
        ek
      ): {Bool.and(_, List.contains(~A, ~same, r, x)) == Bool.and(_, True{}): Bool}
      {==}
    case False{} False{}:
      ih
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# m is kept exactly when p keeps it and xs has it
def List.contains_keep(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~p: V -> A -> Bool,
  ~laws: Eq.Laws(A, same),
  xs: List<&2, A>,
  +g: V,
  +m: A
) -> {
  List.contains(
    ~A,
    ~same,
    List.keep(~A, ~V, ~p, xs, g),
    m
  )
    == Bool.and(p(g)(m), List.contains(~A, ~same, xs, m)): Bool
}:
  match xs:
    case Nil{}:
      Equal.sym(Bool, Bool.and(p(g)(m), False{}), False{}, Bool.and_false_right(p(g)(m)))
    case Con{+x, +r}:
      List.contains_keep.at(
        ~A,
        ~V,
        ~same,
        ~p,
        ~laws,
        p(g)(x),
        same(x, m),
        x,
        List.keep(~A, ~V, ~p, r, g),
        r,
        g,
        m,
        {==},
        {==},
        List.contains_keep(~A, ~V, ~same, ~p, ~laws, r, g, m)
      )

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

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# List.contains_flat at the first element h, once it is known to be x or not (hit)
def List.contains_flat.at(
  ~A: Data,
  ~B: Data,
  ~V: Data,
  ~sa: A -> A -> Bool,
  ~sb: B -> B -> Bool,
  ~f: V -> A -> List<&2, B>,
  ~laws: Eq.Laws(A, sa),
  hit: Bool,
  h: A,
  r: List<&2, A>,
  g: V,
  x: A,
  y: B,
  eh: {sa(h, x) == hit: Bool},
  hx: {List.any.if(u => List.contains(~A, ~sa, r, x), hit) == True{}: Bool},
  hy: {List.contains(~B, ~sb, f(g)(x), y) == True{}: Bool},
  ih: {
    List.contains(~A, ~sa, r, x) == True{}: Bool
  } -> {List.contains(~B, ~sb, List.flat(~A, ~B, ~V, ~f, r, g), y) == True{}: Bool}
) -> {
  Bool.or(
    List.contains(~B, ~sb, f(g)(h), y),
    List.contains(~B, ~sb, List.flat(~A, ~B, ~V, ~f, r, g), y)
  )
    == True{}: Bool
}:
  match hit:
    case True{}:
      %Equal.sym(A, h, x, Eq.sound(~A, ~sa, laws, h, x)(eh)):
        {
          Bool.or(
            List.contains(~B, ~sb, f(g)(_), y),
            List.contains(~B, ~sb, List.flat(~A, ~B, ~V, ~f, r, g), y)
          )
            == True{}: Bool
        }
      %Equal.sym(Bool, List.contains(~B, ~sb, f(g)(x), y), True{}, hy):
        {Bool.or(_, List.contains(~B, ~sb, List.flat(~A, ~B, ~V, ~f, r, g), y)) == True{}: Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, List.contains(~B, ~sb, List.flat(~A, ~B, ~V, ~f, r, g), y), True{}, ih(hx)):
        {Bool.or(List.contains(~B, ~sb, f(g)(h), y), _) == True{}: Bool}
      Bool.or_true_right(List.contains(~B, ~sb, f(g)(h), y))
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof's statement keeps each and/or as one value for the proof to split on; a proof does not run
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# what f gives for an element of xs is in the flat list
def List.contains_flat(
  ~A: Data,
  ~B: Data,
  ~V: Data,
  ~sa: A -> A -> Bool,
  ~sb: B -> B -> Bool,
  ~f: V -> A -> List<&2, B>,
  ~laws: Eq.Laws(A, sa),
  xs: List<&2, A>,
  +g: V,
  +x: A,
  +y: B
) -> {
  List.contains(~A, ~sa, xs, x) == True{}: Bool
} -> {
  List.contains(~B, ~sb, f(g)(x), y) == True{}: Bool
} -> {List.contains(~B, ~sb, List.flat(~A, ~B, ~V, ~f, xs, g), y) == True{}: Bool}:
  match xs:
    case Nil{}:
      hx => hy => Empty.absurd(
        {List.contains(~B, ~sb, List.flat(~A, ~B, ~V, ~f, [], g), y) == True{}: Bool},
        Bool.false_ne_true(hx)
      )
    case Con{+h, +r}:
      hx => +hy =>
        %Equal.sym(
          Bool,
          List.contains(~B, ~sb, List.append(&2, B, f(g)(h), List.flat(~A, ~B, ~V, ~f, r, g)), y),
          Bool.or(
            List.contains(~B, ~sb, f(g)(h), y),
            List.contains(~B, ~sb, List.flat(~A, ~B, ~V, ~f, r, g), y)
          ),
          List.contains_append(~B, ~sb, f(g)(h), List.flat(~A, ~B, ~V, ~f, r, g), y)
        ): {_ == True{}: Bool}
        List.contains_flat.at(
          ~A,
          ~B,
          ~V,
          ~sa,
          ~sb,
          ~f,
          ~laws,
          sa(h, x),
          h,
          r,
          g,
          x,
          y,
          {==},
          hx,
          hy,
          hr => List.contains_flat(~A, ~B, ~V, ~sa, ~sb, ~f, ~laws, r, g, x, y)(hr)(hy)
        )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

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

# a "not" that is True is of False
def Bool.not_true(a: Bool) -> {Bool.not(a) == True{}: Bool} -> {a == False{}: Bool}:
  match a:
    case False{}:
      h => {==}
    case True{}:
      h => Empty.absurd({True{} == False{}: Bool}, Bool.false_ne_true(h))

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

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

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

# appends group either way
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
    case Con{h, t}:
      %List.append_assoc(A, t, ys, zs):
        {h <> List.append(&2, A, List.append(&2, A, t, ys), zs) == h <> _: List<&2, A>}
      {==}

# the first n elements, then the rest, are the list
def List.take_drop(
  -A: Data,
  xs: List<&2, A>,
  n: Nat
) -> {List.append(&2, A, List.take(&2, A, xs, n), List.drop(&2, A, xs, n)) == xs: List<&2, A>}:
  match xs n:
    case Nil{} k:
      {==}
    case Con{h, t} 0n:
      {==}
    case Con{h, t} 1n+p:
      %List.take_drop(
        A,
        t,
        p
      ): {
        h
          <> List.append(&2, A, List.take(&2, A, t, p), List.drop(&2, A, t, p))
          == h
          <> _: List<&2, A>
      }
      {==}

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
law List.is_eq_refl:
  for ~A: Data
  for ~same: A -> A -> Bool
  for ~laws: Eq.Laws(A, same)
  for xs: List<&2, A>
  {List.is_eq(~A, ~same, xs, xs) == True{}: Bool}

def List.is_eq_refl(ty, same, laws, xs):
  match xs:
    case Nil{}:
      {==}
    case Con{x, r}:
      %Equal.sym(
        Bool,
        same(x, x),
        True{},
        Eq.refl(~ty, ~same, laws, x)
      ): {List.all.if(u => List.is_eq(~ty, ~same, r, r), _) == True{}: Bool}
      List.is_eq_refl(~ty, ~same, ~laws, r)

# List.is_eq is True only for equal lists
law List.is_eq_sound:
  for ~A: Data
  for ~same: A -> A -> Bool
  for ~laws: Eq.Laws(A, same)
  for xs: List<&2, A>
  for ys: List<&2, A>
  {List.is_eq(~A, ~same, xs, ys) == True{}: Bool} -> {xs == ys: List<&2, A>}

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
def List.is_eq_sound(ty, same, laws, xs, ys):
  match xs ys:
    case Nil{} Nil{}:
      h => {==}
    case Nil{} Con{y, yr}:
      h => Empty.absurd({Nil{} == Con{y, yr}: List<&2, ty>}, Bool.false_ne_true(h))
    case Con{x, xr} Nil{}:
      h => Empty.absurd({Con{x, xr} == Nil{}: List<&2, ty>}, Bool.false_ne_true(h))
    case Con{+x, +xr} Con{+y, +yr}:
      +h =>
        %Eq.sound(
          ~ty,
          ~same,
          laws,
          x,
          y
        )(
          List.all.if_hit(same(x, y), u => List.is_eq(~ty, ~same, xr, yr))(h)
        ): {x <> xr == _ <> yr: List<&2, ty>}
        %List.is_eq_sound(
          ~ty,
          ~same,
          ~laws,
          xr,
          yr
        )(List.all.if_rest(same(x, y), u => List.is_eq(~ty, ~same, xr, yr))(h)):
          {x <> xr == x <> _: List<&2, ty>}
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

# ks, with each element of ns that ks does not hold, as same compares them
def List.union(~A: Data, ~same: A -> A -> Bool, ns: List<&2, A>, +ks: List<&2, A>) -> List<&2, A>:
  match ns:
    case Nil{}:
      ks
    case Con{+n, r}:
      List.union(~A, ~same, r, List.filter.put(A, n, ks, Bool.not(List.contains(~A, ~same, ks, n))))
