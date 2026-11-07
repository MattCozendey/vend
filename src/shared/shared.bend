import Base

# no False equals True
def Bool.false_ne_true(e: {False{} == True{}: Bool}) -> Empty:
  %e: Bool.pick(Type, _, Empty, Unit)
  Unit{}

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

# some element of xs is m, as same compares them
def List.has(~A: Data, ~same: A -> A -> Bool, xs: List<&2, A>, +m: A) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{x, r}:
      List.any.if(u => List.has(~A, ~same, r, m), same(x, m))

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

# List.has_append at the first element, by whether it is m (hit)
def List.has_append.at(
  ~A: Data,
  ~same: A -> A -> Bool,
  hit: Bool,
  r: List<&2, A>,
  b: List<&2, A>,
  m: A,
  ih: {
    List.has(
      ~A,
      ~same,
      List.append(&2, A, r, b),
      m
    )
      == Bool.or(List.has(~A, ~same, r, m), List.has(~A, ~same, b, m)): Bool
  }
) -> {
  List.any.if(
    u => List.has(~A, ~same, List.append(&2, A, r, b), m),
    hit
  )
    == Bool.or(List.any.if(u => List.has(~A, ~same, r, m), hit), List.has(~A, ~same, b, m)): Bool
}:
  match hit:
    case True{}:
      {==}
    case False{}:
      ih

# m is in a ++ b exactly when it is in a or in b
def List.has_append(
  ~A: Data,
  ~same: A -> A -> Bool,
  a: List<&2, A>,
  +b: List<&2, A>,
  +m: A
) -> {
  List.has(
    ~A,
    ~same,
    List.append(&2, A, a, b),
    m
  )
    == Bool.or(List.has(~A, ~same, a, m), List.has(~A, ~same, b, m)): Bool
}:
  match a:
    case Nil{}:
      {==}
    case Con{x, +r}:
      List.has_append.at(~A, ~same, same(x, m), r, b, m, List.has_append(~A, ~same, r, b, m))

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# a member of r is a member of x <> r
def List.has_cons(
  ~A: Data,
  ~same: A -> A -> Bool,
  x: A,
  r: List<&2, A>,
  y: A
) -> {
  List.has(~A, ~same, r, y) == True{}: Bool
} -> {List.has(~A, ~same, x <> r, y) == True{}: Bool}:
  h =>
    %Equal.sym(
      Bool,
      List.has(~A, ~same, r, y),
      True{},
      h
    ): {List.any.if(u => _, same(x, y)) == True{}: Bool}
    List.any.if_true(same(x, y))
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# a list without k has neither k first nor k after
def List.has_cons_false(
  ~A: Data,
  ~same: A -> A -> Bool,
  +i: A,
  +r: List<&2, A>,
  +k: A
) -> {
  List.has(~A, ~same, i <> r, k) == False{}: Bool
} -> {same(i, k) == False{}: Bool}
  & {List.has(~A, ~same, r, k) == False{}: Bool}:
  +h => (
    List.any.if_false_hit(same(i, k), u => List.has(~A, ~same, r, k))(h),
    List.any.if_false_rest(same(i, k), u => List.has(~A, ~same, r, k))(h)
  )

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# two lists without k, one after the other, are without k
def List.has_append_false(
  ~A: Data,
  ~same: A -> A -> Bool,
  a: List<&2, A>,
  b: List<&2, A>,
  +k: A
) -> {
  List.has(~A, ~same, a, k) == False{}: Bool
} -> {
  List.has(~A, ~same, b, k) == False{}: Bool
} -> {List.has(~A, ~same, List.append(&2, A, a, b), k) == False{}: Bool}:
  match a:
    case Nil{}:
      ha => hb => hb
    case Con{+i, +r}:
      +ha => hb =>
        %Equal.sym(
          Bool,
          same(i, k),
          False{},
          List.any.if_false_hit(same(i, k), u => List.has(~A, ~same, r, k))(ha)
        ): {List.any.if(u => List.has(~A, ~same, List.append(&2, A, r, b), k), _) == False{}: Bool}
        List.has_append_false(
          ~A,
          ~same,
          r,
          b,
          k
        )(List.any.if_false_rest(same(i, k), u => List.has(~A, ~same, r, k))(ha))(hb)
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# List.has_split, once the rest is split
def List.has_split.cons(
  ~A: Data,
  ~same: A -> A -> Bool,
  x: A,
  r: List<&2, A>,
  m: A,
  w: &ys: List<
    &2,
    A> -> &y: A -> &zs: List<
    &2,
    A> -> {r == List.append(&2, A, ys, y <> zs): List<&2, A>}
    & {same(y, m) == True{}: Bool}
) -> &ys:
  List<
    &2,
    A> -> &y: A -> &zs: List<
    &2,
    A> -> {x <> r == List.append(&2, A, ys, y <> zs): List<&2, A>}
    & {same(y, m) == True{}: Bool}:
  match w:
    case (ys, (y, (zs, (e1, e2)))):
      (
        x <> ys,
        (
          y,
          (
            zs,
            (
              Equal.cong(
                List<&2, A>,
                List<&2, A>,
                z => x <> z,
                r,
                List.append(&2, A, ys, y <> zs),
                e1
              ),
              e2
            )
          )
        )
      )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# List.has_split at the first element x, by whether it is m (hit)
def List.has_split.at(
  ~A: Data,
  ~same: A -> A -> Bool,
  hit: Bool,
  x: A,
  r: List<&2, A>,
  m: A,
  ih: {
    List.has(~A, ~same, r, m) == True{}: Bool
  } -> &ys: List<
    &2,
    A> -> &y: A -> &zs: List<
    &2,
    A> -> {r == List.append(&2, A, ys, y <> zs): List<&2, A>}
    & {same(y, m) == True{}: Bool}
) -> {
  same(x, m) == hit: Bool
} -> {List.any.if(u => List.has(~A, ~same, r, m), hit) == True{}: Bool} -> &ys:
  List<
    &2,
    A> -> &y: A -> &zs: List<
    &2,
    A> -> {x <> r == List.append(&2, A, ys, y <> zs): List<&2, A>}
    & {same(y, m) == True{}: Bool}:
  match hit:
    case True{}:
      e => h => ([], (x, (r, ({==}, e))))
    case False{}:
      e => h => List.has_split.cons(~A, ~same, x, r, m, ih(h))

# an element of xs splits it: the elements before it, it, and the ones after
def List.has_split(
  ~A: Data,
  ~same: A -> A -> Bool,
  xs: List<&2, A>,
  +m: A
) -> {List.has(~A, ~same, xs, m) == True{}: Bool} -> &ys:
  List<
    &2,
    A> -> &y: A -> &zs: List<
    &2,
    A> -> {xs == List.append(&2, A, ys, y <> zs): List<&2, A>}
    & {same(y, m) == True{}: Bool}:
  match xs:
    case Nil{}:
      h => Empty.absurd(
        &ys: List<
          &2,
          A> -> &y: A -> &zs: List<
          &2,
          A> -> {[] == List.append(&2, A, ys, y <> zs): List<&2, A>}
          & {same(y, m) == True{}: Bool},
        Bool.false_ne_true(h)
      )
    case Con{+x, +r}:
      List.has_split.at(~A, ~same, same(x, m), x, r, m, List.has_split(~A, ~same, r, m))({==})

# an element in the middle of a list is in the list
def List.has_middle(
  ~A: Data,
  ~same: A -> A -> Bool,
  ~refl: @a: A -> {same(a, a) == True{}: Bool},
  ys: List<&2, A>,
  +m: A,
  +zs: List<&2, A>
) -> {List.has(~A, ~same, List.append(&2, A, ys, m <> zs), m) == True{}: Bool}:
  match ys:
    case Nil{}:
      %Equal.sym(
        Bool,
        same(m, m),
        True{},
        refl(m)
      ): {List.any.if(u => List.has(~A, ~same, zs, m), _) == True{}: Bool}
      {==}
    case Con{x, +r}:
      List.has_cons(
        ~A,
        ~same,
        x,
        List.append(&2, A, r, m <> zs),
        m
      )(List.has_middle(~A, ~same, ~refl, r, m, zs))
