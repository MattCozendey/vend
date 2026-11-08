import Base

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

# the elements of xs that p keeps, given g
def List.keep(~A: Data, ~V: Data, ~p: V -> A -> Bool, xs: List<&2, A>, +g: V) -> List<&2, A>:
  match xs:
    case Nil{}:
      []
    case Con{+x, r}:
      List.filter.put(A, x, List.keep(~A, ~V, ~p, r, g), p(g)(x))

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof's statement keeps each and/or as one value for the proof to split on; a proof does not run
# List.has_keep at the first element x, once p is known to keep it or not (k)
# and x is known to be m or not (hit)
def List.has_keep.at(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~p: V -> A -> Bool,
  ~sound: @a: A -> @b: A -> {same(a, b) == True{}: Bool} -> {a == b: A},
  k: Bool,
  hit: Bool,
  x: A,
  ks: List<&2, A>,
  r: List<&2, A>,
  g: V,
  m: A,
  ek: {p(g)(x) == k: Bool},
  +eh: {same(x, m) == hit: Bool},
  ih: {List.has(~A, ~same, ks, m) == Bool.and(p(g)(m), List.has(~A, ~same, r, m)): Bool}
) -> {
  List.has(
    ~A,
    ~same,
    List.filter.put(A, x, ks, k),
    m
  )
    == Bool.and(p(g)(m), List.any.if(u => List.has(~A, ~same, r, m), hit)): Bool
}:
  match k hit:
    case True{} True{}:
      %Equal.sym(Bool, same(x, m), True{}, eh):
        {List.any.if(u => List.has(~A, ~same, ks, m), _) == Bool.and(p(g)(m), True{}): Bool}
      %sound(x, m)(eh): {True{} == Bool.and(p(g)(_), True{}): Bool}
      %Equal.sym(Bool, p(g)(x), True{}, ek): {True{} == Bool.and(_, True{}): Bool}
      {==}
    case True{} False{}:
      %Equal.sym(Bool, same(x, m), False{}, eh):
        {
          List.any.if(
            u => List.has(~A, ~same, ks, m),
            _
          )
            == Bool.and(p(g)(m), List.has(~A, ~same, r, m)): Bool
        }
      ih
    case False{} True{}:
      %Equal.sym(
        Bool,
        List.has(~A, ~same, ks, m),
        Bool.and(p(g)(m), List.has(~A, ~same, r, m)),
        ih
      ):
        {_ == Bool.and(p(g)(m), True{}): Bool}
      %sound(
        x,
        m
      )(eh): {Bool.and(p(g)(_), List.has(~A, ~same, r, _)) == Bool.and(p(g)(_), True{}): Bool}
      %Equal.sym(
        Bool,
        p(g)(x),
        False{},
        ek
      ): {Bool.and(_, List.has(~A, ~same, r, x)) == Bool.and(_, True{}): Bool}
      {==}
    case False{} False{}:
      ih
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# m is kept exactly when p keeps it and xs has it
def List.has_keep(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~p: V -> A -> Bool,
  ~sound: @a: A -> @b: A -> {same(a, b) == True{}: Bool} -> {a == b: A},
  xs: List<&2, A>,
  +g: V,
  +m: A
) -> {
  List.has(
    ~A,
    ~same,
    List.keep(~A, ~V, ~p, xs, g),
    m
  )
    == Bool.and(p(g)(m), List.has(~A, ~same, xs, m)): Bool
}:
  match xs:
    case Nil{}:
      Equal.sym(Bool, Bool.and(p(g)(m), False{}), False{}, Bool.and_false_right(p(g)(m)))
    case Con{+x, +r}:
      List.has_keep.at(
        ~A,
        ~V,
        ~same,
        ~p,
        ~sound,
        p(g)(x),
        same(x, m),
        x,
        List.keep(~A, ~V, ~p, r, g),
        r,
        g,
        m,
        {==},
        {==},
        List.has_keep(~A, ~V, ~same, ~p, ~sound, r, g, m)
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
# List.has_flat at the first element h, once it is known to be x or not (hit)
def List.has_flat.at(
  ~A: Data,
  ~B: Data,
  ~V: Data,
  ~sa: A -> A -> Bool,
  ~sb: B -> B -> Bool,
  ~f: V -> A -> List<&2, B>,
  ~sound: @a: A -> @b: A -> {sa(a, b) == True{}: Bool} -> {a == b: A},
  hit: Bool,
  h: A,
  r: List<&2, A>,
  g: V,
  x: A,
  y: B,
  eh: {sa(h, x) == hit: Bool},
  hx: {List.any.if(u => List.has(~A, ~sa, r, x), hit) == True{}: Bool},
  hy: {List.has(~B, ~sb, f(g)(x), y) == True{}: Bool},
  ih: {
    List.has(~A, ~sa, r, x) == True{}: Bool
  } -> {List.has(~B, ~sb, List.flat(~A, ~B, ~V, ~f, r, g), y) == True{}: Bool}
) -> {
  Bool.or(
    List.has(~B, ~sb, f(g)(h), y),
    List.has(~B, ~sb, List.flat(~A, ~B, ~V, ~f, r, g), y)
  )
    == True{}: Bool
}:
  match hit:
    case True{}:
      %Equal.sym(A, h, x, sound(h, x)(eh)):
        {
          Bool.or(
            List.has(~B, ~sb, f(g)(_), y),
            List.has(~B, ~sb, List.flat(~A, ~B, ~V, ~f, r, g), y)
          )
            == True{}: Bool
        }
      %Equal.sym(Bool, List.has(~B, ~sb, f(g)(x), y), True{}, hy):
        {Bool.or(_, List.has(~B, ~sb, List.flat(~A, ~B, ~V, ~f, r, g), y)) == True{}: Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, List.has(~B, ~sb, List.flat(~A, ~B, ~V, ~f, r, g), y), True{}, ih(hx)):
        {Bool.or(List.has(~B, ~sb, f(g)(h), y), _) == True{}: Bool}
      Bool.or_true_right(List.has(~B, ~sb, f(g)(h), y))
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof's statement keeps each and/or as one value for the proof to split on; a proof does not run
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# what f gives for an element of xs is in the flat list
def List.has_flat(
  ~A: Data,
  ~B: Data,
  ~V: Data,
  ~sa: A -> A -> Bool,
  ~sb: B -> B -> Bool,
  ~f: V -> A -> List<&2, B>,
  ~sound: @a: A -> @b: A -> {sa(a, b) == True{}: Bool} -> {a == b: A},
  xs: List<&2, A>,
  +g: V,
  +x: A,
  +y: B
) -> {
  List.has(~A, ~sa, xs, x) == True{}: Bool
} -> {
  List.has(~B, ~sb, f(g)(x), y) == True{}: Bool
} -> {List.has(~B, ~sb, List.flat(~A, ~B, ~V, ~f, xs, g), y) == True{}: Bool}:
  match xs:
    case Nil{}:
      hx => hy => Empty.absurd(
        {List.has(~B, ~sb, List.flat(~A, ~B, ~V, ~f, [], g), y) == True{}: Bool},
        Bool.false_ne_true(hx)
      )
    case Con{+h, +r}:
      hx => +hy =>
        %Equal.sym(
          Bool,
          List.has(~B, ~sb, List.append(&2, B, f(g)(h), List.flat(~A, ~B, ~V, ~f, r, g)), y),
          Bool.or(
            List.has(~B, ~sb, f(g)(h), y),
            List.has(~B, ~sb, List.flat(~A, ~B, ~V, ~f, r, g), y)
          ),
          List.has_append(~B, ~sb, f(g)(h), List.flat(~A, ~B, ~V, ~f, r, g), y)
        ): {_ == True{}: Bool}
        List.has_flat.at(
          ~A,
          ~B,
          ~V,
          ~sa,
          ~sb,
          ~f,
          ~sound,
          sa(h, x),
          h,
          r,
          g,
          x,
          y,
          {==},
          hx,
          hy,
          hr => List.has_flat(~A, ~B, ~V, ~sa, ~sb, ~f, ~sound, r, g, x, y)(hr)(hy)
        )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# k and h is k, when k makes h true
def Bool.and_implied(
  k: Bool,
  -h: Bool,
  c: {k == True{}: Bool} -> {h == True{}: Bool}
) -> {Bool.and(k, h) == k: Bool}:
  match k:
    case False{}:
      {==}
    case True{}:
      c({==})

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof's statement keeps each and/or as one value for the proof to split on; a proof does not run
# m is kept exactly when p keeps it, when p keeps only what xs has
def List.keep_exactly(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~p: V -> A -> Bool,
  ~sound: @a: A -> @b: A -> {same(a, b) == True{}: Bool} -> {a == b: A},
  xs: List<&2, A>,
  +g: V,
  +m: A,
  c: {p(g)(m) == True{}: Bool} -> {List.has(~A, ~same, xs, m) == True{}: Bool}
) -> {List.has(~A, ~same, List.keep(~A, ~V, ~p, xs, g), m) == p(g)(m): Bool}:
  Equal.trans(
    Bool,
    List.has(~A, ~same, List.keep(~A, ~V, ~p, xs, g), m),
    Bool.and(p(g)(m), List.has(~A, ~same, xs, m)),
    p(g)(m),
    List.has_keep(~A, ~V, ~same, ~p, ~sound, xs, g, m),
    Bool.and_implied(p(g)(m), List.has(~A, ~same, xs, m), c)
  )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# a lazy "and" is the "and"
def Bool.and_lazy(a: Bool, -b: Bool) -> {List.all.if(u => b, a) == Bool.and(a, b): Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# a lazy "or" is the "or"
def Bool.or_lazy(a: Bool, -b: Bool) -> {List.any.if(u => b, a) == Bool.or(a, b): Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}
