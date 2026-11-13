import Base
import ../../shared/shared/shared/shared/crit.bend as Crits
import ../../shared/shared/shared/shared/shared.bend as Shared

# Sets of values
# --------------
# A set of values of A: a crit-bit map from the key of each value to the
# value, with the proofs that the map is well formed and that each value sits
# under its own key. The map of a set is a function of its entries, and its
# entries are a function of the values it holds, so two sets that hold the
# same values are the same set (ValSet.ext).

# the end e of a fork with rep r, if any, sits under its own key
def ValSet.ok.end(~A: Data, ~key: A -> List<&2, U32>, r: List<&2, U32>, e: Maybe<&2, A>) -> Bool:
  match e:
    case None{}:
      True{}
    case Some{v}:
      Crits.Key.is_eq(r, key(v))

# each value of the map m sits under its own key
def ValSet.ok(~A: Data, ~key: A -> List<&2, U32>, m: Crits.Crit<A>) -> Bool:
  match m:
    case Crits.Crit.Tip{}:
      True{}
    case Crits.Crit.Leaf{k, v}:
      Crits.Key.is_eq(k, key(v))
    case Crits.Crit.Fork{r, p, e, z, o}:
      Bool.and(
        ValSet.ok.end(~A, ~key, r, e),
        Bool.and(ValSet.ok(~A, ~key, z), ValSet.ok(~A, ~key, o))
      )

# the proofs that the map m is well formed and checked
def ValSet.Checked(~A: Data, ~key: A -> List<&2, U32>, m: Crits.Crit<A>) -> Data:
  Sigma<
    &2,
    &2,
    {Crits.Crit.wf(~A, m, 0n) == True{}: Bool},
    _ => {ValSet.ok(~A, ~key, m) == True{}: Bool}>

# a set of values of A, each under its key
def ValSet(~A: Data, ~key: A -> List<&2, U32>) -> Data:
  Sigma<&2, &2, Crits.Crit<A>, m => ValSet.Checked(~A, ~key, m)>

# the map of the set s
def ValSet.crit(~A: Data, ~key: A -> List<&2, U32>, s: ValSet(~A, ~key)) -> Crits.Crit<A>:
  match s:
    case Tuple{m, p}:
      m

# the map m holds the key of x
def ValSet.in(~A: Data, ~key: A -> List<&2, U32>, m: Crits.Crit<A>, x: A) -> Bool:
  Crits.Crit.has(A, m, key(x))

# the map of a set is well formed
def ValSet.wf(
  ~A: Data,
  ~key: A -> List<&2, U32>,
  s: ValSet(~A, ~key)
) -> {Crits.Crit.wf(~A, ValSet.crit(~A, ~key, s), 0n) == True{}: Bool}:
  match s:
    case Tuple{m, p}:
      (w, hk) = p
      w

# each value of the map of a set sits under its own key
def ValSet.checked(
  ~A: Data,
  ~key: A -> List<&2, U32>,
  s: ValSet(~A, ~key)
) -> {ValSet.ok(~A, ~key, ValSet.crit(~A, ~key, s)) == True{}: Bool}:
  match s:
    case Tuple{m, p}:
      (w, hk) = p
      hk

# a set with no value
def ValSet.new(~A: Data, ~key: A -> List<&2, U32>) -> ValSet(~A, ~key):
  (Crits.Crit.new(A), (Crits.Crit.new_wf(~A), {==}))

# s holds x
def ValSet.has(
  ~A: Data,
  ~same: A -> A -> Bool,
  ~key: A -> List<&2, U32>,
  s: ValSet(~A, ~key),
  x: A
) -> Bool:
  ValSet.in(~A, ~key, ValSet.crit(~A, ~key, s), x)

# the values of s, each once, in the order of their keys
def ValSet.list(~A: Data, ~key: A -> List<&2, U32>, s: ValSet(~A, ~key)) -> List<&2, A>:
  Crits.Binds.values(A, Crits.Crit.entries(A, ValSet.crit(~A, ~key, s)))

# Laws of the check
# -----------------

# the first of two true sides is true
def ValSet.and_fst(a: Bool, -b: Bool) -> {Bool.and(a, b) == True{}: Bool} -> {a == True{}: Bool}:
  match a:
    case True{}:
      h => {==}
    case False{}:
      h => h

# the second of two true sides is true
def ValSet.and_snd(a: Bool, -b: Bool) -> {Bool.and(a, b) == True{}: Bool} -> {b == True{}: Bool}:
  match a:
    case True{}:
      h => h
    case False{}:
      h => Empty.absurd({b == True{}: Bool}, Shared.Bool.false_ne_true(h))

# a and b are true when each follows from h: one use of h gives both
def ValSet.and_one(
  -H: Type,
  a: Bool,
  -b: Bool,
  h: H,
  fa: H -> {a == True{}: Bool},
  fb: H -> {b == True{}: Bool}
) -> {Bool.and(a, b) == True{}: Bool}:
  match a:
    case False{}:
      fa(h)
    case True{}:
      fb(h)

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in a proof a second use sits in a rewrite motive or an erased argument, and the checker accepts it
# an entry k2, w under its own key that reads as v at k: k is the key of v
def ValSet.ok_get.at(
  ~A: Data,
  ~key: A -> List<&2, U32>,
  +k2: List<&2, U32>,
  w: A,
  +k: List<&2, U32>,
  -v: A
) -> {
  Crits.Key.is_eq(k2, key(w)) == True{}: Bool
} -> {
  Shared.Maybe.when(A, Crits.Key.is_eq(k2, k), u => Some{w}) == Some{v}: Maybe<&2, A>
} -> {Crits.Key.is_eq(k, key(v)) == True{}: Bool}:
  hk => +h =>
    %Crits.Crit.ws_key(
      A,
      k2,
      w,
      k,
      v,
      Crits.Key.is_eq(k2, k)
    )({==})(h): {Crits.Key.is_eq(_, key(v)) == True{}: Bool}
    %Crits.Crit.ws_val(
      A,
      w,
      v,
      Crits.Key.is_eq(k2, k)
    )(h): {Crits.Key.is_eq(k2, key(_)) == True{}: Bool}
    hk
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# ValSet.ok_get for the end of a fork
def ValSet.ok_get.end(
  ~A: Data,
  ~key: A -> List<&2, U32>,
  r: List<&2, U32>,
  e: Maybe<&2, A>,
  k: List<&2, U32>,
  -v: A
) -> {
  ValSet.ok.end(~A, ~key, r, e) == True{}: Bool
} -> {
  Crits.Crit.ended(A, r, e, k) == Some{v}: Maybe<&2, A>
} -> {Crits.Key.is_eq(k, key(v)) == True{}: Bool}:
  match e:
    case None{}:
      hk => h => Empty.absurd(
        {Crits.Key.is_eq(k, key(v)) == True{}: Bool},
        Shared.Maybe.none_ne_some(A, v, h)
      )
    case Some{w}:
      hk => h => ValSet.ok_get.at(~A, ~key, r, w, k, v)(hk)(h)

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof does not run
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- a proof does not run
# a value that a checked map holds under k has the key k
def ValSet.ok_get(
  ~A: Data,
  ~key: A -> List<&2, U32>,
  m: Crits.Crit<A>,
  +k: List<&2, U32>,
  -v: A
) -> {
  ValSet.ok(~A, ~key, m) == True{}: Bool
} -> {
  Crits.Crit.lookup(A, m, k) == Some{v}: Maybe<&2, A>
} -> {Crits.Key.is_eq(k, key(v)) == True{}: Bool}:
  match m:
    case Crits.Crit.Tip{}:
      hk => h => Empty.absurd(
        {Crits.Key.is_eq(k, key(v)) == True{}: Bool},
        Shared.Maybe.none_ne_some(A, v, h)
      )
    case Crits.Crit.Leaf{k2, w}:
      hk => h => ValSet.ok_get.at(~A, ~key, k2, w, k, v)(hk)(h)
    case Crits.Crit.Fork{+r, p, +e, +z, o}:
      +hk => Crits.Crit.or3_some(
        A,
        {Crits.Key.is_eq(k, key(v)) == True{}: Bool},
        Crits.Crit.ended(A, r, e, k),
        Crits.Crit.lookup(A, z, k),
        Crits.Crit.lookup(A, o, k),
        v
      )(
        h => ValSet.ok_get.end(
          ~A,
          ~key,
          r,
          e,
          k,
          v
        )(
          ValSet.and_fst(
            ValSet.ok.end(~A, ~key, r, e),
            Bool.and(ValSet.ok(~A, ~key, z), ValSet.ok(~A, ~key, o))
          )(hk)
        )(h)
      )(
        h => ValSet.ok_get(
          ~A,
          ~key,
          z,
          k,
          v
        )(
          Shared.Bool.and_second(
            ValSet.ok.end(~A, ~key, r, e),
            ValSet.ok(~A, ~key, z),
            ValSet.ok(~A, ~key, o)
          )(hk)
        )(h)
      )(
        h => ValSet.ok_get(
          ~A,
          ~key,
          o,
          k,
          v
        )(
          Shared.Bool.and_third(
            ValSet.ok.end(~A, ~key, r, e),
            ValSet.ok(~A, ~key, z),
            ValSet.ok(~A, ~key, o)
          )(hk)
        )(h)
      )

# ValSet.add_get, once the test of k and the key of x is known (b)
def ValSet.add_get.at(
  ~A: Data,
  ~key: A -> List<&2, U32>,
  m: Crits.Crit<A>,
  x: A,
  k: List<&2, U32>,
  -v: A,
  b: Bool
) -> {
  ValSet.ok(~A, ~key, m) == True{}: Bool
} -> {
  Crits.Key.is_eq(k, key(x)) == b: Bool
} -> {
  Bool.pick(Maybe<&2, A>, b, Some{x}, Crits.Crit.lookup(A, m, k)) == Some{v}: Maybe<&2, A>
} -> {Crits.Key.is_eq(k, key(v)) == True{}: Bool}:
  match b:
    case True{}:
      hk => eb => h =>
        %Shared.Maybe.some_inj(A, x, v, h): {Crits.Key.is_eq(k, key(_)) == True{}: Bool}
        eb
    case False{}:
      hk => eb => h => ValSet.ok_get(~A, ~key, m, k, v)(hk)(h)

# a value that a checked map with x under its key holds under k has the key k
def ValSet.add_get(
  ~A: Data,
  ~key: A -> List<&2, U32>,
  +m: Crits.Crit<A>,
  +x: A,
  +k: List<&2, U32>,
  -v: A
) -> {
  Crits.Crit.wf(~A, m, 0n) == True{}: Bool
} -> {
  ValSet.ok(~A, ~key, m) == True{}: Bool
} -> {
  Crits.Crit.lookup(A, Crits.Crit.set(~A, m, key(x), x), k) == Some{v}: Maybe<&2, A>
} -> {Crits.Key.is_eq(k, key(v)) == True{}: Bool}:
  +w => hk => c => ValSet.add_get.at(~A, ~key, m, x, k, v, Crits.Key.is_eq(k, key(x)))(hk)({==})((
      %Crits.Crit.get_lookup.at(~A, m, k)(w): {Bool.pick(Maybe<&2, A>, Crits.Key.is_eq(k, key(x)), Some{x}, _) == Some{v}: Maybe<&2, A>}
      %Crits.Dict.get_set.at(~A, m, key(x), x, k)(w): {_ == Some{v}: Maybe<&2, A>}
      Equal.trans(Maybe<&2, A>, Crits.Crit.get(A, Crits.Crit.set(~A, m, key(x), x), k), Crits.Crit.lookup(A, Crits.Crit.set(~A, m, key(x), x), k), Some{v}, Crits.Crit.get_lookup.at(~A, Crits.Crit.set(~A, m, key(x), x), k)(Crits.Crit.upsert_wf(~A, ~(a => b => b), m, key(x), x)(w)), c)))

# ValSet.add_ok.go for the end of a fork
def ValSet.add_ok.end(
  ~A: Data,
  ~key: A -> List<&2, U32>,
  r: List<&2, U32>,
  e: Maybe<&2, A>,
  m: Crits.Crit<A>,
  x: A
) -> {
  Crits.Crit.wf(~A, m, 0n) == True{}: Bool
} -> {
  ValSet.ok(~A, ~key, m) == True{}: Bool
} -> Crits.Crit.sub_end(
  A,
  r,
  e,
  Crits.Crit.set(~A, m, key(x), x)
) -> {ValSet.ok.end(~A, ~key, r, e) == True{}: Bool}:
  match e:
    case None{}:
      w => hk => c => {==}
    case Some{v}:
      w => hk => c => ValSet.add_get(~A, ~key, m, x, r, v)(w)(hk)(c)

# bend-lint: expect-begin bend-lint-rules/performance/missed_fork@hint -- a proof does not run
# a map n whose entries are entries of a checked map with x is checked
def ValSet.add_ok.go(
  ~A: Data,
  ~key: A -> List<&2, U32>,
  n: Crits.Crit<A>,
  +m: Crits.Crit<A>,
  +x: A
) -> {
  Crits.Crit.wf(~A, m, 0n) == True{}: Bool
} -> {
  ValSet.ok(~A, ~key, m) == True{}: Bool
} -> Crits.Crit.sub(
  A,
  n,
  Crits.Crit.set(~A, m, key(x), x)
) -> {ValSet.ok(~A, ~key, n) == True{}: Bool}:
  match n:
    case Crits.Crit.Tip{}:
      w => hk => c => {==}
    case Crits.Crit.Leaf{k, v}:
      w => hk => c => ValSet.add_get(~A, ~key, m, x, k, v)(w)(hk)(c)
    case Crits.Crit.Fork{+r, p, +e, +z, +o}:
      +w => +hk => +c => Shared.Bool.and_both(
        ValSet.ok.end(~A, ~key, r, e),
        Bool.and(ValSet.ok(~A, ~key, z), ValSet.ok(~A, ~key, o))
      )(
        ValSet.add_ok.end(
          ~A,
          ~key,
          r,
          e,
          m,
          x
        )(w)(hk)(Crits.Crit.sub.e(A, r, p, e, z, o, Crits.Crit.set(~A, m, key(x), x), c))
      )(
        Shared.Bool.and_both(
          ValSet.ok(~A, ~key, z),
          ValSet.ok(~A, ~key, o)
        )(
          ValSet.add_ok.go(
            ~A,
            ~key,
            z,
            m,
            x
          )(w)(hk)(Crits.Crit.sub.z(A, r, p, e, z, o, Crits.Crit.set(~A, m, key(x), x), c))
        )(
          ValSet.add_ok.go(
            ~A,
            ~key,
            o,
            m,
            x
          )(w)(hk)(Crits.Crit.sub.o(A, r, p, e, z, o, Crits.Crit.set(~A, m, key(x), x), c))
        )
      )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information
# bend-lint: expect-end bend-lint-rules/performance/missed_fork@hint
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# a checked map with x under its key is checked
def ValSet.add_ok(
  ~A: Data,
  ~key: A -> List<&2, U32>,
  +m: Crits.Crit<A>,
  +x: A
) -> {
  Crits.Crit.wf(~A, m, 0n) == True{}: Bool
} -> {
  ValSet.ok(~A, ~key, m) == True{}: Bool
} -> {ValSet.ok(~A, ~key, Crits.Crit.set(~A, m, key(x), x)) == True{}: Bool}:
  +w => hk => ValSet.add_ok.go(
    ~A,
    ~key,
    Crits.Crit.set(~A, m, key(x), x),
    m,
    x
  )(
    w
  )(
    hk
  )(
    Crits.Crit.sub_self(
      ~A,
      Crits.Crit.set(~A, m, key(x), x),
      0n
    )(Crits.Crit.upsert_wf(~A, ~(a => b => b), m, key(x), x)(w))
  )

# s with x
def ValSet.add(~A: Data, ~key: A -> List<&2, U32>, +s: ValSet(~A, ~key), +x: A) -> ValSet(~A, ~key):
  (
    Crits.Crit.set(~A, ValSet.crit(~A, ~key, s), key(x), x),
    (
      Crits.Crit.upsert_wf(
        ~A,
        ~(a => b => b),
        ValSet.crit(~A, ~key, s),
        key(x),
        x
      )(ValSet.wf(~A, ~key, s)),
      ValSet.add_ok(
        ~A,
        ~key,
        ValSet.crit(~A, ~key, s),
        x
      )(ValSet.wf(~A, ~key, s))(ValSet.checked(~A, ~key, s))
    )
  )

# Laws of sets
# ------------
# The laws that compare values take the laws of same (laws) and its agreement
# with the keys (agree) as templates, so they cost nothing at run time.

# a new set holds no value
def ValSet.has_new(
  ~A: Data,
  ~same: A -> A -> Bool,
  ~key: A -> List<&2, U32>,
  x: A
) -> {ValSet.has(~A, ~same, ~key, ValSet.new(~A, ~key), x) == False{}: Bool}:
  {==}

# a choice of some value, else of g, is some when b holds or g is some
def ValSet.is_some_pick(
  -A: Data,
  b: Bool,
  -y: A,
  -g: Maybe<&2, A>
) -> {
  Maybe.is_some(
    &2,
    A,
    Bool.pick(Maybe<&2, A>, b, Some{y}, g)
  )
    == Bool.or(b, Maybe.is_some(&2, A, g)): Bool
}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof does not run
# a set with y holds x when x is y, or when the set did
def ValSet.has_add(
  ~A: Data,
  ~same: A -> A -> Bool,
  ~key: A -> List<&2, U32>,
  ~agree: @x: A -> @y: A -> {same(x, y) == Crits.Key.is_eq(key(x), key(y)): Bool},
  +s: ValSet(~A, ~key),
  +y: A,
  +x: A
) -> {
  ValSet.has(
    ~A,
    ~same,
    ~key,
    ValSet.add(~A, ~key, s, y),
    x
  )
    == Bool.or(same(x, y), ValSet.has(~A, ~same, ~key, s, x)): Bool
}:
  %Equal.sym(
    Bool,
    same(x, y),
    Crits.Key.is_eq(key(x), key(y)),
    agree(x, y)
  ): {
    ValSet.has(
      ~A,
      ~same,
      ~key,
      ValSet.add(~A, ~key, s, y),
      x
    )
      == Bool.or(_, ValSet.has(~A, ~same, ~key, s, x)): Bool
  }
  Equal.trans(
    Bool,
    ValSet.has(~A, ~same, ~key, ValSet.add(~A, ~key, s, y), x),
    Maybe.is_some(
      &2,
      A,
      Bool.pick(
        Maybe<&2, A>,
        Crits.Key.is_eq(key(x), key(y)),
        Some{y},
        Crits.Crit.get(A, ValSet.crit(~A, ~key, s), key(x))
      )
    ),
    Bool.or(Crits.Key.is_eq(key(x), key(y)), ValSet.has(~A, ~same, ~key, s, x)),
    Equal.cong(
      Maybe<&2, A>,
      Bool,
      g => Maybe.is_some(&2, A, g),
      Crits.Crit.get(A, Crits.Crit.set(~A, ValSet.crit(~A, ~key, s), key(y), y), key(x)),
      Bool.pick(
        Maybe<&2, A>,
        Crits.Key.is_eq(key(x), key(y)),
        Some{y},
        Crits.Crit.get(A, ValSet.crit(~A, ~key, s), key(x))
      ),
      Crits.Dict.get_set.at(~A, ValSet.crit(~A, ~key, s), key(y), y, key(x))(ValSet.wf(~A, ~key, s))
    ),
    ValSet.is_some_pick(
      A,
      Crits.Key.is_eq(key(x), key(y)),
      y,
      Crits.Crit.get(A, ValSet.crit(~A, ~key, s), key(x))
    )
  )

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in a proof a second use sits in a rewrite motive or an erased argument, and the checker accepts it
# a set with x holds x
def ValSet.add_has(
  ~A: Data,
  ~same: A -> A -> Bool,
  ~key: A -> List<&2, U32>,
  ~agree: @x: A -> @y: A -> {same(x, y) == Crits.Key.is_eq(key(x), key(y)): Bool},
  s: ValSet(~A, ~key),
  +x: A
) -> {ValSet.has(~A, ~same, ~key, ValSet.add(~A, ~key, s, x), x) == True{}: Bool}:
  %Equal.sym(
    Bool,
    ValSet.has(~A, ~same, ~key, ValSet.add(~A, ~key, s, x), x),
    Bool.or(same(x, x), ValSet.has(~A, ~same, ~key, s, x)),
    ValSet.has_add(~A, ~same, ~key, ~agree, s, x, x)
  ): {_ == True{}: Bool}
  %Equal.sym(
    Bool,
    same(x, x),
    Crits.Key.is_eq(key(x), key(x)),
    agree(x, x)
  ): {Bool.or(_, ValSet.has(~A, ~same, ~key, s, x)) == True{}: Bool}
  %Equal.sym(
    Bool,
    Crits.Key.is_eq(key(x), key(x)),
    True{},
    Crits.Key.is_eq_refl(key(x))
  ): {Bool.or(_, ValSet.has(~A, ~same, ~key, s, x)) == True{}: Bool}
  {==}

# a set with y holds each value that the set held
def ValSet.add_keeps(
  ~A: Data,
  ~same: A -> A -> Bool,
  ~key: A -> List<&2, U32>,
  ~agree: @x: A -> @y: A -> {same(x, y) == Crits.Key.is_eq(key(x), key(y)): Bool},
  s: ValSet(~A, ~key),
  +y: A,
  +x: A
) -> {
  ValSet.has(~A, ~same, ~key, s, x) == True{}: Bool
} -> {ValSet.has(~A, ~same, ~key, ValSet.add(~A, ~key, s, y), x) == True{}: Bool}:
  h =>
    %Equal.sym(
      Bool,
      ValSet.has(~A, ~same, ~key, ValSet.add(~A, ~key, s, y), x),
      Bool.or(same(x, y), ValSet.has(~A, ~same, ~key, s, x)),
      ValSet.has_add(~A, ~same, ~key, ~agree, s, y, x)
    ): {_ == True{}: Bool}
    %Equal.sym(
      Bool,
      ValSet.has(~A, ~same, ~key, s, x),
      True{},
      h
    ): {Bool.or(same(x, y), _) == True{}: Bool}
    Shared.Bool.or_true_right(same(x, y))

# a hit, else the rest, is the hit or the rest
def ValSet.any_or(k: Unit -> Bool, b: Bool) -> {List.any.if(k, b) == Bool.or(b, k(Unit{})): Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# a test is the test that its choice of some value is some
def ValSet.when_some(
  -A: Data,
  b: Bool,
  -v: A
) -> {b == Maybe.is_some(&2, A, Shared.Maybe.when(A, b, u => Some{v})): Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# a value v under its key k is x exactly when it is read at the key of x
def ValSet.hit(
  ~A: Data,
  ~same: A -> A -> Bool,
  ~key: A -> List<&2, U32>,
  ~agree: @x: A -> @y: A -> {same(x, y) == Crits.Key.is_eq(key(x), key(y)): Bool},
  k: List<&2, U32>,
  +v: A,
  +x: A
) -> {
  Crits.Key.is_eq(k, key(v)) == True{}: Bool
} -> {
  same(
    v,
    x
  )
    == Maybe.is_some(&2, A, Shared.Maybe.when(A, Crits.Key.is_eq(k, key(x)), u => Some{v})): Bool
}:
  hk =>
    %Equal.sym(
      List<&2, U32>,
      k,
      key(v),
      Crits.Key.is_eq_sound(k, key(v))(hk)
    ): {
      same(
        v,
        x
      )
        == Maybe.is_some(
          &2,
          A,
          Shared.Maybe.when(A, Crits.Key.is_eq(_, key(x)), u => Some{v})
        ): Bool
    }
    Equal.trans(
      Bool,
      same(v, x),
      Crits.Key.is_eq(key(v), key(x)),
      Maybe.is_some(&2, A, Shared.Maybe.when(A, Crits.Key.is_eq(key(v), key(x)), u => Some{v})),
      agree(v, x),
      ValSet.when_some(A, Crits.Key.is_eq(key(v), key(x)), v)
    )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# one of three reads, or c, is some: the read of a fork
def ValSet.or3(
  -A: Data,
  e: Maybe<&2, A>,
  lz: Maybe<&2, A>,
  -lo: Maybe<&2, A>,
  -c: Bool
) -> {
  Bool.or(
    Maybe.is_some(&2, A, e),
    Bool.or(Maybe.is_some(&2, A, lz), Bool.or(Maybe.is_some(&2, A, lo), c))
  )
    == Bool.or(Maybe.is_some(&2, A, Maybe.or(&2, A, e, Maybe.or(&2, A, lz, lo))), c): Bool
}:
  match e lz:
    case Some{x} y:
      {==}
    case None{} Some{y}:
      {==}
    case None{} None{}:
      {==}

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- a proof does not run
# the values of a checked map n, then rest, hold x when n holds its key or
# the values of rest hold x
def ValSet.list_go(
  ~A: Data,
  ~same: A -> A -> Bool,
  ~key: A -> List<&2, U32>,
  ~agree: @x: A -> @y: A -> {same(x, y) == Crits.Key.is_eq(key(x), key(y)): Bool},
  n: Crits.Crit<A>,
  +rest: List<&2, Crits.Bind<A>>,
  +x: A
) -> {
  ValSet.ok(~A, ~key, n) == True{}: Bool
} -> {
  List.contains(
    ~A,
    ~same,
    Crits.Binds.values(A, Crits.Crit.entries.go(A, n, rest)),
    x
  )
    == Bool.or(
      Maybe.is_some(&2, A, Crits.Crit.lookup(A, n, key(x))),
      List.contains(~A, ~same, Crits.Binds.values(A, rest), x)
    ): Bool
}:
  match n:
    case Crits.Crit.Tip{}:
      hk => {==}
    case Crits.Crit.Leaf{k, +v}:
      hk =>
        %ValSet.hit(
          ~A,
          ~same,
          ~key,
          ~agree,
          k,
          v,
          x
        )(
          hk
        ): {
          List.any.if(
            u => List.contains(~A, ~same, Crits.Binds.values(A, rest), x),
            same(v, x)
          )
            == Bool.or(_, List.contains(~A, ~same, Crits.Binds.values(A, rest), x)): Bool
        }
        ValSet.any_or(u => List.contains(~A, ~same, Crits.Binds.values(A, rest), x), same(v, x))
    case Crits.Crit.Fork{+r, p, None{}, +z, +o}:
      +hk =>
        %ValSet.or3(
          A,
          None{},
          Crits.Crit.lookup(A, z, key(x)),
          Crits.Crit.lookup(A, o, key(x)),
          List.contains(~A, ~same, Crits.Binds.values(A, rest), x)
        ): {
          List.contains(
            ~A,
            ~same,
            Crits.Binds.values(A, Crits.Crit.entries.go(A, z, Crits.Crit.entries.go(A, o, rest))),
            x
          )
            == _: Bool
        }
        %ValSet.list_go(
          ~A,
          ~same,
          ~key,
          ~agree,
          o,
          rest,
          x
        )(
          Shared.Bool.and_third(
            ValSet.ok.end(~A, ~key, r, None{}),
            ValSet.ok(~A, ~key, z),
            ValSet.ok(~A, ~key, o)
          )(hk)
        ): {
          List.contains(
            ~A,
            ~same,
            Crits.Binds.values(A, Crits.Crit.entries.go(A, z, Crits.Crit.entries.go(A, o, rest))),
            x
          )
            == Bool.or(Maybe.is_some(&2, A, Crits.Crit.lookup(A, z, key(x))), _): Bool
        }
        ValSet.list_go(
          ~A,
          ~same,
          ~key,
          ~agree,
          z,
          Crits.Crit.entries.go(A, o, rest),
          x
        )(
          Shared.Bool.and_second(
            ValSet.ok.end(~A, ~key, r, None{}),
            ValSet.ok(~A, ~key, z),
            ValSet.ok(~A, ~key, o)
          )(hk)
        )
    case Crits.Crit.Fork{+r, +p, Some{+v}, +z, +o}:
      +hk =>
        %ValSet.or3(
          A,
          Shared.Maybe.when(A, Crits.Key.is_eq(r, key(x)), u => Some{v}),
          Crits.Crit.lookup(A, z, key(x)),
          Crits.Crit.lookup(A, o, key(x)),
          List.contains(~A, ~same, Crits.Binds.values(A, rest), x)
        ): {
          List.any.if(
            u => List.contains(
              ~A,
              ~same,
              Crits.Binds.values(A, Crits.Crit.entries.go(A, z, Crits.Crit.entries.go(A, o, rest))),
              x
            ),
            same(v, x)
          )
            == _: Bool
        }
        %ValSet.list_go(
          ~A,
          ~same,
          ~key,
          ~agree,
          o,
          rest,
          x
        )(
          Shared.Bool.and_third(
            ValSet.ok.end(~A, ~key, r, Some{v}),
            ValSet.ok(~A, ~key, z),
            ValSet.ok(~A, ~key, o)
          )(hk)
        ): {
          List.any.if(
            u => List.contains(
              ~A,
              ~same,
              Crits.Binds.values(A, Crits.Crit.entries.go(A, z, Crits.Crit.entries.go(A, o, rest))),
              x
            ),
            same(v, x)
          )
            == Bool.or(
              Maybe.is_some(&2, A, Shared.Maybe.when(A, Crits.Key.is_eq(r, key(x)), u => Some{v})),
              Bool.or(Maybe.is_some(&2, A, Crits.Crit.lookup(A, z, key(x))), _)
            ): Bool
        }
        %ValSet.list_go(
          ~A,
          ~same,
          ~key,
          ~agree,
          z,
          Crits.Crit.entries.go(A, o, rest),
          x
        )(
          Shared.Bool.and_second(
            ValSet.ok.end(~A, ~key, r, Some{v}),
            ValSet.ok(~A, ~key, z),
            ValSet.ok(~A, ~key, o)
          )(hk)
        ): {
          List.any.if(
            u => List.contains(
              ~A,
              ~same,
              Crits.Binds.values(A, Crits.Crit.entries.go(A, z, Crits.Crit.entries.go(A, o, rest))),
              x
            ),
            same(v, x)
          )
            == Bool.or(
              Maybe.is_some(&2, A, Shared.Maybe.when(A, Crits.Key.is_eq(r, key(x)), u => Some{v})),
              _
            ): Bool
        }
        %ValSet.hit(
          ~A,
          ~same,
          ~key,
          ~agree,
          r,
          v,
          x
        )(
          ValSet.and_fst(
            ValSet.ok.end(~A, ~key, r, Some{v}),
            Bool.and(ValSet.ok(~A, ~key, z), ValSet.ok(~A, ~key, o))
          )(hk)
        ): {
          List.any.if(
            u => List.contains(
              ~A,
              ~same,
              Crits.Binds.values(A, Crits.Crit.entries.go(A, z, Crits.Crit.entries.go(A, o, rest))),
              x
            ),
            same(v, x)
          )
            == Bool.or(
              _,
              List.contains(
                ~A,
                ~same,
                Crits.Binds.values(
                  A,
                  Crits.Crit.entries.go(A, z, Crits.Crit.entries.go(A, o, rest))
                ),
                x
              )
            ): Bool
        }
        ValSet.any_or(
          u => List.contains(
            ~A,
            ~same,
            Crits.Binds.values(A, Crits.Crit.entries.go(A, z, Crits.Crit.entries.go(A, o, rest))),
            x
          ),
          same(v, x)
        )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# a set holds x exactly when the list of its values does
def ValSet.has_list(
  ~A: Data,
  ~same: A -> A -> Bool,
  ~key: A -> List<&2, U32>,
  ~agree: @x: A -> @y: A -> {same(x, y) == Crits.Key.is_eq(key(x), key(y)): Bool},
  +s: ValSet(~A, ~key),
  +x: A
) -> {
  ValSet.has(~A, ~same, ~key, s, x) == List.contains(~A, ~same, ValSet.list(~A, ~key, s), x): Bool
}:
  %Equal.sym(
    Bool,
    List.contains(~A, ~same, ValSet.list(~A, ~key, s), x),
    Bool.or(Maybe.is_some(&2, A, Crits.Crit.lookup(A, ValSet.crit(~A, ~key, s), key(x))), False{}),
    ValSet.list_go(
      ~A,
      ~same,
      ~key,
      ~agree,
      ValSet.crit(~A, ~key, s),
      [],
      x
    )(ValSet.checked(~A, ~key, s))
  ): {ValSet.has(~A, ~same, ~key, s, x) == _: Bool}
  %Shared.Bool.or_false(
    Maybe.is_some(&2, A, Crits.Crit.lookup(A, ValSet.crit(~A, ~key, s), key(x)))
  ): {ValSet.has(~A, ~same, ~key, s, x) == _: Bool}
  Crits.Crit.has_lookup(~A, ValSet.crit(~A, ~key, s), 0n, key(x))(ValSet.wf(~A, ~key, s))

# the values of n, then rest, are as many as the size of n and rest
def ValSet.len_go(
  -A: Data,
  n: Crits.Crit<A>,
  +rest: List<&2, Crits.Bind<A>>
) -> {
  List.length(
    &2,
    A,
    Crits.Binds.values(A, Crits.Crit.entries.go(A, n, rest))
  )
    == Nat.add(Crits.Crit.size(A, n), List.length(&2, A, Crits.Binds.values(A, rest))): Nat
}:
  match n:
    case Crits.Crit.Tip{}:
      {==}
    case Crits.Crit.Leaf{k, v}:
      {==}
    case Crits.Crit.Fork{r, p, None{}, +z, +o}:
      %Equal.sym(
        Nat,
        Nat.add(
          Nat.add(Crits.Crit.size(A, z), Crits.Crit.size(A, o)),
          List.length(&2, A, Crits.Binds.values(A, rest))
        ),
        Nat.add(
          Crits.Crit.size(A, z),
          Nat.add(Crits.Crit.size(A, o), List.length(&2, A, Crits.Binds.values(A, rest)))
        ),
        Shared.Nat.add_assoc(
          Crits.Crit.size(A, z),
          Crits.Crit.size(A, o),
          List.length(&2, A, Crits.Binds.values(A, rest))
        )
      ): {
        List.length(
          &2,
          A,
          Crits.Binds.values(A, Crits.Crit.entries.go(A, z, Crits.Crit.entries.go(A, o, rest)))
        )
          == _: Nat
      }
      %ValSet.len_go(
        A,
        o,
        rest
      ): {
        List.length(
          &2,
          A,
          Crits.Binds.values(A, Crits.Crit.entries.go(A, z, Crits.Crit.entries.go(A, o, rest)))
        )
          == Nat.add(Crits.Crit.size(A, z), _): Nat
      }
      ValSet.len_go(A, z, Crits.Crit.entries.go(A, o, rest))
    case Crits.Crit.Fork{r, p, Some{v}, +z, +o}:
      %Equal.sym(
        Nat,
        Nat.add(
          Nat.add(Crits.Crit.size(A, z), Crits.Crit.size(A, o)),
          List.length(&2, A, Crits.Binds.values(A, rest))
        ),
        Nat.add(
          Crits.Crit.size(A, z),
          Nat.add(Crits.Crit.size(A, o), List.length(&2, A, Crits.Binds.values(A, rest)))
        ),
        Shared.Nat.add_assoc(
          Crits.Crit.size(A, z),
          Crits.Crit.size(A, o),
          List.length(&2, A, Crits.Binds.values(A, rest))
        )
      ): {
        1n+List.length(
          &2,
          A,
          Crits.Binds.values(A, Crits.Crit.entries.go(A, z, Crits.Crit.entries.go(A, o, rest)))
        )
          == 1n+_: Nat
      }
      %ValSet.len_go(
        A,
        o,
        rest
      ): {
        1n+List.length(
          &2,
          A,
          Crits.Binds.values(A, Crits.Crit.entries.go(A, z, Crits.Crit.entries.go(A, o, rest)))
        )
          == 1n+Nat.add(Crits.Crit.size(A, z), _): Nat
      }
      Equal.cong(
        Nat,
        Nat,
        i => 1n+i,
        List.length(
          &2,
          A,
          Crits.Binds.values(A, Crits.Crit.entries.go(A, z, Crits.Crit.entries.go(A, o, rest)))
        ),
        Nat.add(
          Crits.Crit.size(A, z),
          List.length(&2, A, Crits.Binds.values(A, Crits.Crit.entries.go(A, o, rest)))
        ),
        ValSet.len_go(A, z, Crits.Crit.entries.go(A, o, rest))
      )

# the values of a set are as many as the size of its map
def ValSet.size_list(
  ~A: Data,
  ~key: A -> List<&2, U32>,
  +s: ValSet(~A, ~key)
) -> {
  List.length(&2, A, ValSet.list(~A, ~key, s)) == Crits.Crit.size(A, ValSet.crit(~A, ~key, s)): Nat
}:
  %Shared.Nat.add_zero(
    Crits.Crit.size(A, ValSet.crit(~A, ~key, s))
  ): {List.length(&2, A, ValSet.list(~A, ~key, s)) == _: Nat}
  ValSet.len_go(A, ValSet.crit(~A, ~key, s), [])

# a set with x has no fewer values
def ValSet.size_add(
  ~A: Data,
  ~key: A -> List<&2, U32>,
  +s: ValSet(~A, ~key),
  +x: A
) -> {
  Nat.is_le(
    List.length(&2, A, ValSet.list(~A, ~key, s)),
    List.length(&2, A, ValSet.list(~A, ~key, ValSet.add(~A, ~key, s, x)))
  )
    == True{}: Bool
}:
  %Equal.sym(
    Nat,
    List.length(&2, A, ValSet.list(~A, ~key, s)),
    Crits.Crit.size(A, ValSet.crit(~A, ~key, s)),
    ValSet.size_list(~A, ~key, s)
  ): {
    Nat.is_le(
      _,
      List.length(&2, A, ValSet.list(~A, ~key, ValSet.add(~A, ~key, s, x)))
    )
      == True{}: Bool
  }
  %Equal.sym(
    Nat,
    List.length(&2, A, ValSet.list(~A, ~key, ValSet.add(~A, ~key, s, x))),
    Crits.Crit.size(A, ValSet.crit(~A, ~key, ValSet.add(~A, ~key, s, x))),
    ValSet.size_list(~A, ~key, ValSet.add(~A, ~key, s, x))
  ): {Nat.is_le(Crits.Crit.size(A, ValSet.crit(~A, ~key, s)), _) == True{}: Bool}
  %Equal.sym(
    Nat,
    Crits.Crit.size(A, Crits.Crit.set(~A, ValSet.crit(~A, ~key, s), key(x), x)),
    Shared.Nat.add_if(
      Bool.not(Maybe.is_some(&2, A, Crits.Crit.get(A, ValSet.crit(~A, ~key, s), key(x)))),
      Crits.Crit.size(A, ValSet.crit(~A, ~key, s))
    ),
    Crits.Dict.size_set.at(~A, ValSet.crit(~A, ~key, s), key(x), x)(ValSet.wf(~A, ~key, s))
  ): {Nat.is_le(Crits.Crit.size(A, ValSet.crit(~A, ~key, s)), _) == True{}: Bool}
  Shared.Nat.le_add_if(
    Bool.not(Maybe.is_some(&2, A, Crits.Crit.get(A, ValSet.crit(~A, ~key, s), key(x)))),
    Crits.Crit.size(A, ValSet.crit(~A, ~key, s)),
    Crits.Crit.size(A, ValSet.crit(~A, ~key, s))
  )(Shared.Nat.le_refl(Crits.Crit.size(A, ValSet.crit(~A, ~key, s))))

# Sets are their values
# ---------------------

# the end e of a fork, if any, is held by both of p and q or by neither
def ValSet.fits.end(
  ~A: Data,
  ~key: A -> List<&2, U32>,
  e: Maybe<&2, A>,
  p: Crits.Crit<A>,
  q: Crits.Crit<A>
) -> Bool:
  match e:
    case None{}:
      True{}
    case Some{+v}:
      Shared.Bool.is_eq(ValSet.in(~A, ~key, p, v), ValSet.in(~A, ~key, q, v))

# each value of n is held by both of p and q or by neither
def ValSet.fits(
  ~A: Data,
  ~key: A -> List<&2, U32>,
  n: Crits.Crit<A>,
  +p: Crits.Crit<A>,
  +q: Crits.Crit<A>
) -> Bool:
  match n:
    case Crits.Crit.Tip{}:
      True{}
    case Crits.Crit.Leaf{k, +v}:
      Shared.Bool.is_eq(ValSet.in(~A, ~key, p, v), ValSet.in(~A, ~key, q, v))
    case Crits.Crit.Fork{r, pos, e, z, o}:
      Bool.and(
        ValSet.fits.end(~A, ~key, e, p, q),
        Bool.and(ValSet.fits(~A, ~key, z, p, q), ValSet.fits(~A, ~key, o, p, q))
      )

# p and q, which hold the same values, both hold v or neither does
def ValSet.fits_at(
  ~A: Data,
  ~key: A -> List<&2, U32>,
  p: Crits.Crit<A>,
  q: Crits.Crit<A>,
  +v: A,
  h: (@x: A -> {ValSet.in(~A, ~key, p, x) == ValSet.in(~A, ~key, q, x): Bool})
) -> {Shared.Bool.is_eq(ValSet.in(~A, ~key, p, v), ValSet.in(~A, ~key, q, v)) == True{}: Bool}:
  %h(v): {Shared.Bool.is_eq(ValSet.in(~A, ~key, p, v), _) == True{}: Bool}
  Shared.Bool.is_eq_refl(ValSet.in(~A, ~key, p, v))

# ValSet.fits_all for the end of a fork
def ValSet.fits_all.end(
  ~A: Data,
  ~key: A -> List<&2, U32>,
  e: Maybe<&2, A>,
  p: Crits.Crit<A>,
  q: Crits.Crit<A>,
  h: (@x: A -> {ValSet.in(~A, ~key, p, x) == ValSet.in(~A, ~key, q, x): Bool})
) -> {ValSet.fits.end(~A, ~key, e, p, q) == True{}: Bool}:
  match e:
    case None{}:
      {==}
    case Some{v}:
      ValSet.fits_at(~A, ~key, p, q, v, h)

# p and q, which hold the same values, both hold each value of n or neither
# does: the one use of the premise that a proof has gives it for all of n
def ValSet.fits_all(
  ~A: Data,
  ~key: A -> List<&2, U32>,
  n: Crits.Crit<A>,
  +p: Crits.Crit<A>,
  +q: Crits.Crit<A>,
  h: (@x: A -> {ValSet.in(~A, ~key, p, x) == ValSet.in(~A, ~key, q, x): Bool})
) -> {ValSet.fits(~A, ~key, n, p, q) == True{}: Bool}:
  match n:
    case Crits.Crit.Tip{}:
      {==}
    case Crits.Crit.Leaf{k, v}:
      ValSet.fits_at(~A, ~key, p, q, v, h)
    case Crits.Crit.Fork{r, pos, +e, +z, o}:
      Shared.Bool.and_each(
        (@x: A -> {ValSet.in(~A, ~key, p, x) == ValSet.in(~A, ~key, q, x): Bool}),
        ValSet.fits.end(~A, ~key, e, p, q),
        ValSet.fits(~A, ~key, z, p, q),
        ValSet.fits(~A, ~key, o, p, q),
        h,
        g => ValSet.fits_all.end(~A, ~key, e, p, q, g),
        g => ValSet.fits_all(~A, ~key, z, p, q, g),
        g => ValSet.fits_all(~A, ~key, o, p, q, g)
      )

# a checked map q that reads some value at the key of v reads v there
def ValSet.found(
  ~A: Data,
  ~same: A -> A -> Bool,
  ~key: A -> List<&2, U32>,
  ~laws: Shared.Eq.Laws(A, same),
  ~agree: @x: A -> @y: A -> {same(x, y) == Crits.Key.is_eq(key(x), key(y)): Bool},
  q: Crits.Crit<A>,
  +v: A,
  mv: Maybe<&2, A>
) -> {
  ValSet.ok(~A, ~key, q) == True{}: Bool
} -> {
  Crits.Crit.lookup(A, q, key(v)) == mv: Maybe<&2, A>
} -> {
  Maybe.is_some(&2, A, mv) == True{}: Bool
} -> {Crits.Crit.lookup(A, q, key(v)) == Some{v}: Maybe<&2, A>}:
  match mv:
    case None{}:
      hk => e => i => Empty.absurd(
        {Crits.Crit.lookup(A, q, key(v)) == Some{v}: Maybe<&2, A>},
        Shared.Bool.false_ne_true(i)
      )
    case Some{+w}:
      hk => +e => i =>
        %Equal.sym(
          A,
          v,
          w,
          Shared.Eq.sound(
            ~A,
            ~same,
            laws,
            v,
            w
          )(
            Equal.trans(
              Bool,
              same(v, w),
              Crits.Key.is_eq(key(v), key(w)),
              True{},
              agree(v, w),
              ValSet.ok_get(~A, ~key, q, key(v), w)(hk)(e)
            )
          )
        ): {Crits.Crit.lookup(A, q, key(v)) == Some{_}: Maybe<&2, A>}
        e

# an entry k, v of a checked map p is an entry of a checked map q, when both
# hold v or neither does
def ValSet.move(
  ~A: Data,
  ~same: A -> A -> Bool,
  ~key: A -> List<&2, U32>,
  ~laws: Shared.Eq.Laws(A, same),
  ~agree: @x: A -> @y: A -> {same(x, y) == Crits.Key.is_eq(key(x), key(y)): Bool},
  +p: Crits.Crit<A>,
  +q: Crits.Crit<A>,
  +k: List<&2, U32>,
  +v: A
) -> {
  Crits.Crit.wf(~A, p, 0n) == True{}: Bool
} -> {
  ValSet.ok(~A, ~key, p) == True{}: Bool
} -> {
  Crits.Crit.wf(~A, q, 0n) == True{}: Bool
} -> {
  ValSet.ok(~A, ~key, q) == True{}: Bool
} -> {
  Shared.Bool.is_eq(ValSet.in(~A, ~key, p, v), ValSet.in(~A, ~key, q, v)) == True{}: Bool
} -> {
  Crits.Crit.lookup(A, p, k) == Some{v}: Maybe<&2, A>
} -> {Crits.Crit.lookup(A, q, k) == Some{v}: Maybe<&2, A>}:
  wp => hp => wq => hq => f => +c =>
    +kk = Crits.Key.is_eq_sound(k, key(v))(ValSet.ok_get(~A, ~key, p, k, v)(hp)(c))
    %Equal.sym(List<&2, U32>, k, key(v), kk): {Crits.Crit.lookup(A, q, _) == Some{v}: Maybe<&2, A>}
    ValSet.found(~A, ~same, ~key, ~laws, ~agree, q, v, Crits.Crit.lookup(A, q, key(v)))(hq)({==})((
        %Crits.Crit.has_lookup(~A, q, 0n, key(v))(wq): {_ == True{}: Bool}
        %Shared.Bool.is_eq_sound(ValSet.in(~A, ~key, p, v), ValSet.in(~A, ~key, q, v))(f): {_ == True{}: Bool}
        %Equal.sym(Bool, ValSet.in(~A, ~key, p, v), Maybe.is_some(&2, A, Crits.Crit.lookup(A, p, key(v))), Crits.Crit.has_lookup(~A, p, 0n, key(v))(wp)): {_ == True{}: Bool}
        %kk: {Maybe.is_some(&2, A, Crits.Crit.lookup(A, p, _)) == True{}: Bool}
        %Equal.sym(Maybe<&2, A>, Crits.Crit.lookup(A, p, k), Some{v}, c): {Maybe.is_some(&2, A, _) == True{}: Bool}
        {==}))

# ValSet.sub_move for the end of a fork
def ValSet.sub_move.end(
  ~A: Data,
  ~same: A -> A -> Bool,
  ~key: A -> List<&2, U32>,
  ~laws: Shared.Eq.Laws(A, same),
  ~agree: @x: A -> @y: A -> {same(x, y) == Crits.Key.is_eq(key(x), key(y)): Bool},
  r: List<&2, U32>,
  e: Maybe<&2, A>,
  p: Crits.Crit<A>,
  q: Crits.Crit<A>
) -> {
  Crits.Crit.wf(~A, p, 0n) == True{}: Bool
} -> {
  ValSet.ok(~A, ~key, p) == True{}: Bool
} -> {
  Crits.Crit.wf(~A, q, 0n) == True{}: Bool
} -> {
  ValSet.ok(~A, ~key, q) == True{}: Bool
} -> {
  ValSet.fits.end(~A, ~key, e, p, q) == True{}: Bool
} -> Crits.Crit.sub_end(A, r, e, p) -> Crits.Crit.sub_end(A, r, e, q):
  match e:
    case None{}:
      wp => hp => wq => hq => f => c => Unit{}
    case Some{v}:
      wp => hp => wq => hq => f => c => ValSet.move(
        ~A,
        ~same,
        ~key,
        ~laws,
        ~agree,
        p,
        q,
        r,
        v
      )(wp)(hp)(wq)(hq)(f)(c)

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof does not run
# bend-lint: expect-begin bend-lint-rules/performance/missed_fork@hint -- a proof does not run
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- a proof does not run
# the entries of n that are entries of a checked map p are entries of a
# checked map q, when both hold each value of n or neither does
def ValSet.sub_move(
  ~A: Data,
  ~same: A -> A -> Bool,
  ~key: A -> List<&2, U32>,
  ~laws: Shared.Eq.Laws(A, same),
  ~agree: @x: A -> @y: A -> {same(x, y) == Crits.Key.is_eq(key(x), key(y)): Bool},
  n: Crits.Crit<A>,
  +p: Crits.Crit<A>,
  +q: Crits.Crit<A>
) -> {
  Crits.Crit.wf(~A, p, 0n) == True{}: Bool
} -> {
  ValSet.ok(~A, ~key, p) == True{}: Bool
} -> {
  Crits.Crit.wf(~A, q, 0n) == True{}: Bool
} -> {
  ValSet.ok(~A, ~key, q) == True{}: Bool
} -> {
  ValSet.fits(~A, ~key, n, p, q) == True{}: Bool
} -> Crits.Crit.sub(A, n, p) -> Crits.Crit.sub(A, n, q):
  match n:
    case Crits.Crit.Tip{}:
      wp => hp => wq => hq => f => c => Unit{}
    case Crits.Crit.Leaf{k, v}:
      wp => hp => wq => hq => f => c => ValSet.move(
        ~A,
        ~same,
        ~key,
        ~laws,
        ~agree,
        p,
        q,
        k,
        v
      )(wp)(hp)(wq)(hq)(f)(c)
    case Crits.Crit.Fork{r, pos, +e, +z, o}:
      +wp => +hp => +wq => +hq => +f => +c => (
        ValSet.sub_move.end(
          ~A,
          ~same,
          ~key,
          ~laws,
          ~agree,
          r,
          e,
          p,
          q
        )(
          wp
        )(
          hp
        )(
          wq
        )(
          hq
        )(
          ValSet.and_fst(
            ValSet.fits.end(~A, ~key, e, p, q),
            Bool.and(ValSet.fits(~A, ~key, z, p, q), ValSet.fits(~A, ~key, o, p, q))
          )(f)
        )(Crits.Crit.sub.e(A, r, pos, e, z, o, p, c)),
        (
          ValSet.sub_move(
            ~A,
            ~same,
            ~key,
            ~laws,
            ~agree,
            z,
            p,
            q
          )(
            wp
          )(
            hp
          )(
            wq
          )(
            hq
          )(
            Shared.Bool.and_second(
              ValSet.fits.end(~A, ~key, e, p, q),
              ValSet.fits(~A, ~key, z, p, q),
              ValSet.fits(~A, ~key, o, p, q)
            )(f)
          )(Crits.Crit.sub.z(A, r, pos, e, z, o, p, c)),
          ValSet.sub_move(
            ~A,
            ~same,
            ~key,
            ~laws,
            ~agree,
            o,
            p,
            q
          )(
            wp
          )(
            hp
          )(
            wq
          )(
            hq
          )(
            Shared.Bool.and_third(
              ValSet.fits.end(~A, ~key, e, p, q),
              ValSet.fits(~A, ~key, z, p, q),
              ValSet.fits(~A, ~key, o, p, q)
            )(f)
          )(Crits.Crit.sub.o(A, r, pos, e, z, o, p, c))
        )
      )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information
# bend-lint: expect-end bend-lint-rules/performance/missed_fork@hint
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# the entries of a checked map p are entries of a checked map q, when both
# hold each value of p or neither does
def ValSet.sub_of(
  ~A: Data,
  ~same: A -> A -> Bool,
  ~key: A -> List<&2, U32>,
  ~laws: Shared.Eq.Laws(A, same),
  ~agree: @x: A -> @y: A -> {same(x, y) == Crits.Key.is_eq(key(x), key(y)): Bool},
  +p: Crits.Crit<A>,
  q: Crits.Crit<A>
) -> {
  Crits.Crit.wf(~A, p, 0n) == True{}: Bool
} -> {
  ValSet.ok(~A, ~key, p) == True{}: Bool
} -> {
  Crits.Crit.wf(~A, q, 0n) == True{}: Bool
} -> {
  ValSet.ok(~A, ~key, q) == True{}: Bool
} -> {ValSet.fits(~A, ~key, p, p, q) == True{}: Bool} -> Crits.Crit.sub(A, p, q):
  +wp => hp => wq => hq => f => ValSet.sub_move(
    ~A,
    ~same,
    ~key,
    ~laws,
    ~agree,
    p,
    p,
    q
  )(wp)(hp)(wq)(hq)(f)(Crits.Crit.sub_self(~A, p, 0n)(wp))

# two sets on one map are equal: the proofs are
def ValSet.of_eq.same(
  ~A: Data,
  ~key: A -> List<&2, U32>,
  +m: Crits.Crit<A>,
  pa: ValSet.Checked(~A, ~key, m),
  pb: ValSet.Checked(~A, ~key, m)
) -> {Tuple{m, pa} == Tuple{m, pb}: ValSet(~A, ~key)}:
  match pa pb:
    case Tuple{wa, ha} Tuple{wb, hb}:
      %Crits.Bool.eq_one(
        Crits.Crit.wf(~A, m, 0n),
        True{},
        wa,
        wb
      ): {Tuple{m, Tuple{wa, ha}} == Tuple{m, Tuple{_, hb}}: ValSet(~A, ~key)}
      %Crits.Bool.eq_one(
        ValSet.ok(~A, ~key, m),
        True{},
        ha,
        hb
      ): {Tuple{m, Tuple{wa, ha}} == Tuple{m, Tuple{wa, _}}: ValSet(~A, ~key)}
      {==}

# two sets on equal maps are equal
def ValSet.of_eq(
  ~A: Data,
  ~key: A -> List<&2, U32>,
  ma: Crits.Crit<A>,
  mb: Crits.Crit<A>,
  e: {ma == mb: Crits.Crit<A>}
) -> @pa:
  ValSet.Checked(
    ~A,
    ~key,
    ma
  ) -> @pb: ValSet.Checked(~A, ~key, mb) -> {Tuple{ma, pa} == Tuple{mb, pb}: ValSet(~A, ~key)}:
  %e: @pa: ValSet.Checked(
    ~A,
    ~key,
    ma
  ) -> @pb: ValSet.Checked(~A, ~key, _) -> {Tuple{ma, pa} == Tuple{_, pb}: ValSet(~A, ~key)}
  pa => pb => ValSet.of_eq.same(~A, ~key, ma, pa, pb)

# ValSet.ext on the maps of two sets, with their proofs
def ValSet.ext.at(
  ~A: Data,
  ~same: A -> A -> Bool,
  ~key: A -> List<&2, U32>,
  ~laws: Shared.Eq.Laws(A, same),
  ~agree: @x: A -> @y: A -> {same(x, y) == Crits.Key.is_eq(key(x), key(y)): Bool},
  +ma: Crits.Crit<A>,
  +mb: Crits.Crit<A>,
  pa: ValSet.Checked(~A, ~key, ma),
  pb: ValSet.Checked(~A, ~key, mb)
) -> (
  @x: A -> {ValSet.in(~A, ~key, ma, x) == ValSet.in(~A, ~key, mb, x): Bool}
) -> {Tuple{ma, pa} == Tuple{mb, pb}: ValSet(~A, ~key)}:
  match pa pb:
    case Tuple{+wa, +ha} Tuple{+wb, +hb}:
      h =>
        +ff = ValSet.and_one(
          (@x: A -> {ValSet.in(~A, ~key, ma, x) == ValSet.in(~A, ~key, mb, x): Bool}),
          ValSet.fits(~A, ~key, ma, ma, mb),
          ValSet.fits(~A, ~key, mb, mb, ma),
          h,
          g => ValSet.fits_all(~A, ~key, ma, ma, mb, g),
          g => ValSet.fits_all(
            ~A,
            ~key,
            mb,
            mb,
            ma,
            x => Equal.sym(Bool, ValSet.in(~A, ~key, ma, x), ValSet.in(~A, ~key, mb, x), g(x))
          )
        )
        ValSet.of_eq(
          ~A,
          ~key,
          ma,
          mb,
          Crits.Crit.det(
            ~A,
            ma,
            mb,
            0n,
            0n
          )(
            wa
          )(
            wb
          )(
            ValSet.sub_of(
              ~A,
              ~same,
              ~key,
              ~laws,
              ~agree,
              ma,
              mb
            )(
              wa
            )(
              ha
            )(
              wb
            )(
              hb
            )(
              ValSet.and_fst(
                ValSet.fits(~A, ~key, ma, ma, mb),
                ValSet.fits(~A, ~key, mb, mb, ma)
              )(ff)
            )
          )(
            ValSet.sub_of(
              ~A,
              ~same,
              ~key,
              ~laws,
              ~agree,
              mb,
              ma
            )(
              wb
            )(
              hb
            )(
              wa
            )(
              ha
            )(
              ValSet.and_snd(
                ValSet.fits(~A, ~key, ma, ma, mb),
                ValSet.fits(~A, ~key, mb, mb, ma)
              )(ff)
            )
          )
        )(Tuple{wa, ha})(Tuple{wb, hb})

# a set is its values: two sets that hold the same values are the same set
def ValSet.ext(
  ~A: Data,
  ~same: A -> A -> Bool,
  ~key: A -> List<&2, U32>,
  ~laws: Shared.Eq.Laws(A, same),
  ~agree: @x: A -> @y: A -> {same(x, y) == Crits.Key.is_eq(key(x), key(y)): Bool},
  a: ValSet(~A, ~key),
  b: ValSet(~A, ~key)
) -> (
  @x: A -> {ValSet.has(~A, ~same, ~key, a, x) == ValSet.has(~A, ~same, ~key, b, x): Bool}
) -> {a == b: ValSet(~A, ~key)}:
  match a b:
    case Tuple{ma, pa} Tuple{mb, pb}:
      h => ValSet.ext.at(~A, ~same, ~key, ~laws, ~agree, ma, mb, pa, pb)(h)
