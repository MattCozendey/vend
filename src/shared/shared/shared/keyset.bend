import Base
import ./shared/shared.bend as Shared
import ./shared/crit.bend as Crits

# Sets by key
# -----------
# A set of values of A: a trie from the key of each value to the value. A
# lookup costs the length of one key and one same check, not the size of the
# set. Two different values may share a key: the set then holds the later one
# and answers False for the earlier. So no law here needs keys to differ; only
# the speed does.

# m holds a value that is x
def KeySet.has.at(~A: Data, ~same: A -> A -> Bool, m: Maybe<&2, A>, x: A) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{y}:
      same(y, x)

# t holds x
def KeySet.has(
  ~A: Data,
  ~same: A -> A -> Bool,
  ~key: A -> List<&2, U32>,
  t: Crits.Dict(A),
  +x: A
) -> Bool:
  KeySet.has.at(~A, ~same, Crits.Dict.get(A, t, key(x)), x)

# t with x
def KeySet.put(~A: Data, ~key: A -> List<&2, U32>, t: Crits.Dict(A), +x: A) -> Crits.Dict(A):
  Crits.Dict.set(~A, t, key(x), x)

# t with each value of xs
def KeySet.put_all(
  ~A: Data,
  ~key: A -> List<&2, U32>,
  xs: List<&2, A>,
  t: Crits.Dict(A)
) -> Crits.Dict(A):
  match xs:
    case Nil{}:
      t
    case Con{x, r}:
      KeySet.put_all(~A, ~key, r, KeySet.put(~A, ~key, t, x))

# xs without the values that seen holds, and each of the others once; the
# key of each value is made once, for both the lookup and the put
def KeySet.unique(
  ~A: Data,
  ~same: A -> A -> Bool,
  ~key: A -> List<&2, U32>,
  xs: List<&2, A>,
  +seen: Crits.Dict(A)
) -> List<&2, A>:
  match xs:
    case Nil{}:
      []
    case Con{+x, +r}:
      +k = key(x)
      Shared.Bool.when(
        List<&2, A>,
        KeySet.has.at(~A, ~same, Crits.Dict.get(A, seen, k), x),
        u => KeySet.unique(~A, ~same, ~key, r, seen),
        u => x <> KeySet.unique(~A, ~same, ~key, r, Crits.Dict.set(~A, seen, k, x))
      )

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# KeySet.has_put_all.go at one value y, by whether its key is the key of x (k)
def KeySet.has_put_all.at(
  ~A: Data,
  ~same: A -> A -> Bool,
  k: Bool,
  +y: A,
  m: Maybe<&2, A>,
  +x: A,
  c: Bool
) -> {
  Bool.or(KeySet.has.at(~A, ~same, Bool.pick(Maybe<&2, A>, k, Some{y}, m), x), c) == True{}: Bool
} -> {Bool.or(KeySet.has.at(~A, ~same, m, x), Bool.or(same(y, x), c)) == True{}: Bool}:
  match k:
    case True{}:
      h =>
        %Equal.sym(Bool, Bool.or(same(y, x), c), True{}, h):
          {Bool.or(KeySet.has.at(~A, ~same, m, x), _) == True{}: Bool}
        Shared.Bool.or_true_right(KeySet.has.at(~A, ~same, m, x))
    case False{}:
      h =>
        %Shared.Bool.or_swap(same(y, x), KeySet.has.at(~A, ~same, m, x), c): {_ == True{}: Bool}
        %Equal.sym(Bool, Bool.or(KeySet.has.at(~A, ~same, m, x), c), True{}, h):
          {Bool.or(same(y, x), _) == True{}: Bool}
        Shared.Bool.or_true_right(same(y, x))
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# t with each value of xs holds only values of t and of xs
def KeySet.has_put_all.go(
  ~A: Data,
  ~same: A -> A -> Bool,
  ~key: A -> List<&2, U32>,
  xs: List<&2, A>,
  +t: Crits.Dict(A),
  +x: A
) -> {
  KeySet.has(~A, ~same, ~key, KeySet.put_all(~A, ~key, xs, t), x) == True{}: Bool
} -> {Bool.or(KeySet.has(~A, ~same, ~key, t, x), List.contains(~A, ~same, xs, x)) == True{}: Bool}:
  match xs:
    case Nil{}:
      h =>
        %Shared.Bool.or_false(KeySet.has(~A, ~same, ~key, t, x)): {_ == True{}: Bool}
        h
    case Con{+y, +r}:
      h =>
        %Equal.sym(
          Bool,
          List.any.if(u => List.contains(~A, ~same, r, x), same(y, x)),
          Bool.or(same(y, x), List.contains(~A, ~same, r, x)),
          Shared.List.any.if_or(same(y, x), u => List.contains(~A, ~same, r, x))
        ): {Bool.or(KeySet.has(~A, ~same, ~key, t, x), _) == True{}: Bool}
        KeySet.has_put_all.at(
          ~A,
          ~same,
          Crits.Key.is_eq(key(x), key(y)),
          y,
          Crits.Dict.get(A, t, key(x)),
          x,
          List.contains(~A, ~same, r, x)
        )((
            %Crits.Dict.get_set(~A, t, key(y), y, key(x)):
              {Bool.or(KeySet.has.at(~A, ~same, _, x), List.contains(~A, ~same, r, x)) == True{}: Bool}
            KeySet.has_put_all.go(~A, ~same, ~key, r, KeySet.put(~A, ~key, t, y), x)(h)))

# a set made of xs holds only values of xs
law KeySet.has_put_all:
  for ~A: Data
  for ~same: A -> A -> Bool
  for ~key: A -> List<&2, U32>
  for xs: List<&2, A>
  for x: A
  {
    KeySet.has(~A, ~same, ~key, KeySet.put_all(~A, ~key, xs, Crits.Dict.new(~A)), x) == True{}: Bool
  } -> {List.contains(~A, ~same, xs, x) == True{}: Bool}

def KeySet.has_put_all(ty, same, key, xs, x):
  KeySet.has_put_all.go(~ty, ~same, ~key, xs, Crits.Dict.new(~ty), x)

# t with each value of pre and then x is t with each value of pre, with x
def KeySet.put_all_snoc(
  ~A: Data,
  ~key: A -> List<&2, U32>,
  pre: List<&2, A>,
  t: Crits.Dict(A),
  x: A
) -> {
  KeySet.put_all(
    ~A,
    ~key,
    List.append(&2, A, pre, [x]),
    t
  )
    == KeySet.put(~A, ~key, KeySet.put_all(~A, ~key, pre, t), x): Crits.Dict(A)
}:
  match pre:
    case Nil{}:
      {==}
    case Con{y, r}:
      KeySet.put_all_snoc(~A, ~key, r, KeySet.put(~A, ~key, t, y), x)

# KeySet.unique_some.at for a value that the set holds
def KeySet.unique_some.old(
  a: Bool,
  b: Bool,
  -k: Bool,
  -r: Bool
) -> ({b == True{}: Bool} -> {a == True{}: Bool})
  -> {Bool.or(a, k) == Bool.or(a, r): Bool}
  -> {Bool.or(a, k) == Bool.or(a, List.any.if(u => r, b)): Bool}:
  match a b:
    case True{} y:
      f => h => {==}
    case False{} False{}:
      f => h => h
    case False{} True{}:
      f => h => Empty.absurd({k == True{}: Bool}, Shared.Bool.false_ne_true(f({==})))

# KeySet.unique_some.at for a value that the set does not hold
def KeySet.unique_some.new(
  a: Bool,
  b: Bool,
  -k: Bool,
  -r: Bool
) -> {
  Bool.or(
    Bool.or(a, List.any.if(u => False{}, b)),
    k
  )
    == Bool.or(Bool.or(a, List.any.if(u => False{}, b)), r): Bool
} -> {Bool.or(a, List.any.if(u => k, b)) == Bool.or(a, List.any.if(u => r, b)): Bool}:
  match a b:
    case True{} y:
      h => {==}
    case False{} True{}:
      h => {==}
    case False{} False{}:
      h => h

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# KeySet.unique_some.go at one value x, by whether the set holds it (hit)
def KeySet.unique_some.at(
  ~A: Data,
  ~V: Data,
  ~p: V -> A -> Bool,
  hit: Bool,
  a: Bool,
  x: A,
  kept: List<&2, A>,
  more: List<&2, A>,
  rest: Bool,
  g: V,
  old: {hit == True{}: Bool} -> {p(g)(x) == True{}: Bool} -> {a == True{}: Bool},
  ih_kept: {Bool.or(a, Shared.List.some(~A, ~V, ~p, kept, g)) == Bool.or(a, rest): Bool},
  ih_more: {
    Bool.or(
      Bool.or(a, Shared.List.some(~A, ~V, ~p, [x], g)),
      Shared.List.some(~A, ~V, ~p, more, g)
    )
      == Bool.or(Bool.or(a, Shared.List.some(~A, ~V, ~p, [x], g)), rest): Bool
  }
) -> {
  Bool.or(
    a,
    Shared.List.some(~A, ~V, ~p, Shared.Bool.when(List<&2, A>, hit, u => kept, u => x <> more), g)
  )
    == Bool.or(a, List.any.if(u => rest, p(g)(x))): Bool
}:
  match hit:
    case True{}:
      KeySet.unique_some.old(
        a,
        p(g)(x),
        Shared.List.some(~A, ~V, ~p, kept, g),
        rest
      )(old({==}))(ih_kept)
    case False{}:
      KeySet.unique_some.new(a, p(g)(x), Shared.List.some(~A, ~V, ~p, more, g), rest)(ih_more)
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# bend-lint: expect-begin bend-lint-rules/performance/append_in_loop@warning -- a proof: it does not run
# KeySet.unique_some from the set made of pre, with p of some value of pre on both sides
def KeySet.unique_some.go(
  ~A: Data,
  ~V: Data,
  ~same: A -> A -> Bool,
  ~key: A -> List<&2, U32>,
  ~p: V -> A -> Bool,
  ~laws: Shared.Eq.Laws(A, same),
  xs: List<&2, A>,
  +pre: List<&2, A>,
  +g: V
) -> {
  Bool.or(
    Shared.List.some(~A, ~V, ~p, pre, g),
    Shared.List.some(
      ~A,
      ~V,
      ~p,
      KeySet.unique(~A, ~same, ~key, xs, KeySet.put_all(~A, ~key, pre, Crits.Dict.new(~A))),
      g
    )
  )
    == Bool.or(Shared.List.some(~A, ~V, ~p, pre, g), Shared.List.some(~A, ~V, ~p, xs, g)): Bool
}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      +seen = KeySet.put_all(~A, ~key, pre, Crits.Dict.new(~A))
      a = Shared.List.some(~A, ~V, ~p, pre, g)
      one = Shared.List.some(~A, ~V, ~p, [x], g)
      rest = Shared.List.some(~A, ~V, ~p, r, g)
      KeySet.unique_some.at(
        ~A,
        ~V,
        ~p,
        KeySet.has(~A, ~same, ~key, seen, x),
        a,
        x,
        KeySet.unique(~A, ~same, ~key, r, seen),
        KeySet.unique(~A, ~same, ~key, r, KeySet.put(~A, ~key, seen, x)),
        rest,
        g,
        hs => Shared.List.some_member(
          ~A,
          ~V,
          ~same,
          ~p,
          ~laws,
          pre,
          x,
          g
        )(KeySet.has_put_all(~A, ~same, ~key, pre, x)(hs)),
        KeySet.unique_some.go(~A, ~V, ~same, ~key, ~p, ~laws, r, pre, g),
        (
          %KeySet.put_all_snoc(~A, ~key, pre, Crits.Dict.new(~A), x):
            {Bool.or(Bool.or(a, one), Shared.List.some(~A, ~V, ~p, KeySet.unique(~A, ~same, ~key, r, _), g)) == Bool.or(Bool.or(a, one), rest): Bool}
          %Shared.List.some_append(~A, ~V, ~p, pre, [x], g):
            {Bool.or(_, Shared.List.some(~A, ~V, ~p, KeySet.unique(~A, ~same, ~key, r, KeySet.put_all(~A, ~key, List.append(&2, A, pre, [x]), Crits.Dict.new(~A))), g)) == Bool.or(_, rest): Bool}
          KeySet.unique_some.go(~A, ~V, ~same, ~key, ~p, ~laws, r, List.append(&2, A, pre, [x]), g))
      )
# bend-lint: expect-end bend-lint-rules/performance/append_in_loop@warning

# xs without its repeats has a value that p holds of exactly when xs has one
law KeySet.unique_some:
  for ~A: Data
  for ~V: Data
  for ~same: A -> A -> Bool
  for ~key: A -> List<&2, U32>
  for ~p: V -> A -> Bool
  for ~laws: Shared.Eq.Laws(A, same)
  for xs: List<&2, A>
  for +g: V
  {
    Shared.List.some(
      ~A,
      ~V,
      ~p,
      KeySet.unique(~A, ~same, ~key, xs, Crits.Dict.new(~A)),
      g
    )
      == Shared.List.some(~A, ~V, ~p, xs, g): Bool
  }

def KeySet.unique_some(ty, vt, same, key, p, laws, xs, g):
  KeySet.unique_some.go(~ty, ~vt, ~same, ~key, ~p, ~laws, xs, [], g)
