import Base
import ../../shared/shared/shared/shared/shared.bend as Shared

# Generic lists
# -------------
# Definitions and lemmas on lists that the proofs of the node are built on:
# prefixes, the first hit of a test, the greatest element, majorities.

# Small helpers
# -------------

# a holds exactly when b holds: they are the same Bool
def Bool.iff(
  a: Bool,
  b: Bool
) -> ({a == True{}: Bool} -> {b == True{}: Bool}) -> ({b == True{}: Bool} -> {a == True{}: Bool}) -> {a == b: Bool}:
  match a b:
    case True{} True{}:
      f => g => {==}
    case True{} False{}:
      f => g => Equal.sym(Bool, False{}, True{}, f({==}))
    case False{} True{}:
      f => g => g({==})
    case False{} False{}:
      f => g => {==}

# a Bool is True or False
def Bool.cases(b: Bool) -> {b == True{}: Bool} | {b == False{}: Bool}:
  match b:
    case True{}:
      Inl{{==}}
    case False{}:
      Inr{{==}}

# Prefixes
# --------

# ys extends xs: ys is xs and then some more
def List.Ext(-A: Data, xs: List<&2, A>, ys: List<&2, A>) -> Type:
  Exists(List<&2, A>, zs => {ys == List.append(&2, A, xs, zs): List<&2, A>})

# a list extends itself
def List.ext_refl(-A: Data, xs: List<&2, A>) -> List.Ext(A, xs, xs):
  ([], Equal.sym(List<&2, A>, List.append(&2, A, xs, []), xs, Shared.List.append_nil(A, xs)))

# List.ext_trans, with the two extensions as arguments
def List.ext_trans.of(
  -A: Data,
  xs: List<&2, A>,
  -ys: List<&2, A>,
  -zs: List<&2, A>,
  p: List.Ext(A, xs, ys),
  q: List.Ext(A, ys, zs)
) -> List.Ext(A, xs, zs):
  match p q:
    case Tuple{+a, ea} Tuple{+b, eb}:
      (
        List.append(&2, A, a, b),
        Equal.trans(
          List<&2, A>,
          zs,
          List.append(&2, A, List.append(&2, A, xs, a), b),
          List.append(&2, A, xs, List.append(&2, A, a, b)),
          Equal.trans(
            List<&2, A>,
            zs,
            List.append(&2, A, ys, b),
            List.append(&2, A, List.append(&2, A, xs, a), b),
            eb,
            Equal.cong(List<&2, A>, List<&2, A>, l => List.append(&2, A, l, b), ys, List.append(&2, A, xs, a), ea)
          ),
          Shared.List.append_assoc(A, xs, a, b)
        )
      )

# what extends an extension of xs extends xs
def List.ext_trans(
  -A: Data,
  xs: List<&2, A>,
  -ys: List<&2, A>,
  -zs: List<&2, A>
) -> List.Ext(A, xs, ys) -> List.Ext(A, ys, zs) -> List.Ext(A, xs, zs):
  p => q => List.ext_trans.of(A, xs, ys, zs, p, q)

# a list with one more item at its end extends it
def List.ext_snoc(-A: Data, -xs: List<&2, A>, x: A) -> List.Ext(A, xs, List.append(&2, A, xs, [x])):
  ([x], {==})

# every list extends the empty list
def List.ext_nil(-A: Data, ys: List<&2, A>) -> List.Ext(A, [], ys):
  (ys, {==})

# what xs holds at k, xs and then zs holds at k
def List.get_append(
  -A: Data,
  xs: List<&2, A>,
  -zs: List<&2, A>,
  k: Nat,
  -x: A
) -> {List.get(&2, A, xs, k) == Some{x}: Maybe<&2, A>} -> {List.get(&2, A, List.append(&2, A, xs, zs), k) == Some{x}: Maybe<&2, A>}:
  match xs k:
    case Nil{} j:
      h => Empty.absurd(
        {List.get(&2, A, zs, j) == Some{x}: Maybe<&2, A>},
        Shared.Maybe.none_ne_some(A, x, h)
      )
    case Con{h, t} 0n:
      e => e
    case Con{h, t} 1n+p:
      List.get_append(A, t, zs, p, x)

# List.ext_get, with its premises as arguments
def List.ext_get.of(
  -A: Data,
  xs: List<&2, A>,
  -ys: List<&2, A>,
  k: Nat,
  -x: A,
  p: List.Ext(A, xs, ys),
  h: {List.get(&2, A, xs, k) == Some{x}: Maybe<&2, A>}
) -> {List.get(&2, A, ys, k) == Some{x}: Maybe<&2, A>}:
  (zs, e) = p
    %Equal.sym(List<&2, A>, ys, List.append(&2, A, xs, zs), e): {List.get(&2, A, _, k) == Some{x}: Maybe<&2, A>}
    List.get_append(A, xs, zs, k, x)(h)

# what xs holds at k, an extension of xs holds at k
def List.ext_get(
  -A: Data,
  xs: List<&2, A>,
  -ys: List<&2, A>,
  k: Nat,
  -x: A
) -> List.Ext(A, xs, ys) -> {List.get(&2, A, xs, k) == Some{x}: Maybe<&2, A>} -> {List.get(&2, A, ys, k) == Some{x}: Maybe<&2, A>}:
  p => h => List.ext_get.of(A, xs, ys, k, x, p, h)

# xs is no longer than xs and then zs
def List.length_append_le(
  -A: Data,
  xs: List<&2, A>,
  zs: List<&2, A>
) -> {Nat.is_le(List.length(&2, A, xs), List.length(&2, A, List.append(&2, A, xs, zs))) == True{}: Bool}:
  match xs:
    case Nil{}:
      Shared.Nat.le_zero(List.length(&2, A, zs))
    case Con{h, t}:
      List.length_append_le(A, t, zs)

# List.ext_length, with its premises as arguments
def List.ext_length.of(
  -A: Data,
  xs: List<&2, A>,
  -ys: List<&2, A>,
  p: List.Ext(A, xs, ys)
) -> {Nat.is_le(List.length(&2, A, xs), List.length(&2, A, ys)) == True{}: Bool}:
  (zs, e) = p
    %Equal.sym(List<&2, A>, ys, List.append(&2, A, xs, zs), e): {Nat.is_le(List.length(&2, A, xs), List.length(&2, A, _)) == True{}: Bool}
    List.length_append_le(A, xs, zs)

# a list is no longer than its extension
def List.ext_length(
  -A: Data,
  xs: List<&2, A>,
  -ys: List<&2, A>
) -> List.Ext(A, xs, ys) -> {Nat.is_le(List.length(&2, A, xs), List.length(&2, A, ys)) == True{}: Bool}:
  p => List.ext_length.of(A, xs, ys, p)

# the first n of xs and then zs are the first n of xs, when xs has n
def List.take_append(
  -A: Data,
  xs: List<&2, A>,
  zs: List<&2, A>,
  n: Nat
) -> {Nat.is_le(n, List.length(&2, A, xs)) == True{}: Bool} -> {List.take(&2, A, List.append(&2, A, xs, zs), n) == List.take(&2, A, xs, n): List<&2, A>}:
  match xs n:
    case Nil{} 0n:
      h => Shared.List.take_zero(A, zs)
    case Nil{} 1n+p:
      h => Empty.absurd(
        {List.take(&2, A, zs, 1n+p) == []: List<&2, A>},
        Shared.Bool.false_ne_true(h)
      )
    case Con{h, t} 0n:
      e => {==}
    case Con{h, t} 1n+p:
      e => Equal.cong(
        List<&2, A>,
        List<&2, A>,
        l => h <> l,
        List.take(&2, A, List.append(&2, A, t, zs), p),
        List.take(&2, A, t, p),
        List.take_append(A, t, zs, p)(e)
      )

# List.ext_take, with its premises as arguments
def List.ext_take.of(
  -A: Data,
  xs: List<&2, A>,
  -ys: List<&2, A>,
  n: Nat,
  p: List.Ext(A, xs, ys),
  h: {Nat.is_le(n, List.length(&2, A, xs)) == True{}: Bool}
) -> {List.take(&2, A, ys, n) == List.take(&2, A, xs, n): List<&2, A>}:
  (zs, e) = p
    %Equal.sym(List<&2, A>, ys, List.append(&2, A, xs, zs), e): {List.take(&2, A, _, n) == List.take(&2, A, xs, n): List<&2, A>}
    List.take_append(A, xs, zs, n)(h)

# an extension of xs starts as xs does, up to the length of xs
def List.ext_take(
  -A: Data,
  xs: List<&2, A>,
  -ys: List<&2, A>,
  n: Nat
) -> List.Ext(A, xs, ys) -> {Nat.is_le(n, List.length(&2, A, xs)) == True{}: Bool} -> {List.take(&2, A, ys, n) == List.take(&2, A, xs, n): List<&2, A>}:
  p => h => List.ext_take.of(A, xs, ys, n, p, h)

# List.ext_contains, with its premises as arguments
def List.ext_contains.of(
  ~A: Data,
  ~same: A -> A -> Bool,
  xs: List<&2, A>,
  -ys: List<&2, A>,
  x: A,
  p: List.Ext(A, xs, ys),
  h: {List.contains(~A, ~same, xs, x) == True{}: Bool}
) -> {List.contains(~A, ~same, ys, x) == True{}: Bool}:
  (zs, e) = p
    %Equal.sym(List<&2, A>, ys, List.append(&2, A, xs, zs), e): {List.contains(~A, ~same, _, x) == True{}: Bool}
    Shared.List.contains_left(~A, ~same, xs, zs, x, h)

# a member of xs is a member of an extension of xs
def List.ext_contains(
  ~A: Data,
  ~same: A -> A -> Bool,
  xs: List<&2, A>,
  -ys: List<&2, A>,
  x: A
) -> List.Ext(A, xs, ys) -> {List.contains(~A, ~same, xs, x) == True{}: Bool} -> {List.contains(~A, ~same, ys, x) == True{}: Bool}:
  p => h => List.ext_contains.of(~A, ~same, xs, ys, x, p, h)

# an index that xs holds a value at is below the length of xs
def List.get_lt(
  -A: Data,
  xs: List<&2, A>,
  k: Nat,
  -x: A
) -> {List.get(&2, A, xs, k) == Some{x}: Maybe<&2, A>} -> {Nat.is_lt(k, List.length(&2, A, xs)) == True{}: Bool}:
  match xs k:
    case Nil{} j:
      h => Empty.absurd(
        {Nat.is_lt(j, 0n) == True{}: Bool},
        Shared.Maybe.none_ne_some(A, x, h)
      )
    case Con{h, t} 0n:
      e => {==}
    case Con{h, t} 1n+p:
      List.get_lt(A, t, p, x)

# xs holds a value at each index below its length
def List.get_some(
  -A: Data,
  xs: List<&2, A>,
  k: Nat
) -> {Nat.is_lt(k, List.length(&2, A, xs)) == True{}: Bool} -> Exists(A, x => {List.get(&2, A, xs, k) == Some{x}: Maybe<&2, A>}):
  match xs k:
    case Nil{} 0n:
      h => Empty.absurd(
        Exists(A, x => {None{} == Some{x}: Maybe<&2, A>}),
        Shared.Bool.false_ne_true(h)
      )
    case Nil{} 1n+p:
      h => Empty.absurd(
        Exists(A, x => {None{} == Some{x}: Maybe<&2, A>}),
        Shared.Bool.false_ne_true(h)
      )
    case Con{h, t} 0n:
      e => (h, {==})
    case Con{h, t} 1n+p:
      List.get_some(A, t, p)

# the item added at the end of xs is at the index that is the length of xs
def List.get_snoc(
  -A: Data,
  xs: List<&2, A>,
  -x: A
) -> {List.get(&2, A, List.append(&2, A, xs, [x]), List.length(&2, A, xs)) == Some{x}: Maybe<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      List.get_snoc(A, t, x)

# a list holds its first item
def List.contains_head(
  ~A: Data,
  ~same: A -> A -> Bool,
  ~laws: Shared.Eq.Laws(A, same),
  h: A,
  -t: List<&2, A>
) -> {List.contains(~A, ~same, h <> t, h) == True{}: Bool}:
  %Equal.sym(Bool, same(h, h), True{}, Shared.Eq.refl(~A, ~same, laws, h)): {List.any.if(u => List.contains(~A, ~same, t, h), _) == True{}: Bool}
  {==}

# what xs holds at an index is a member of xs
def List.get_contains(
  ~A: Data,
  ~same: A -> A -> Bool,
  ~laws: Shared.Eq.Laws(A, same),
  xs: List<&2, A>,
  k: Nat,
  +x: A
) -> {List.get(&2, A, xs, k) == Some{x}: Maybe<&2, A>} -> {List.contains(~A, ~same, xs, x) == True{}: Bool}:
  match xs k:
    case Nil{} j:
      h => Empty.absurd(
        {False{} == True{}: Bool},
        Shared.Maybe.none_ne_some(A, x, h)
      )
    case Con{+h, +t} 0n:
      e =>
        %Shared.Maybe.some_inj(A, h, x, e): {List.contains(~A, ~same, h <> t, _) == True{}: Bool}
        List.contains_head(~A, ~same, ~laws, h, t)
    case Con{+h, +t} 1n+p:
      e => Shared.List.contains_cons(~A, ~same, h, t, x)(List.get_contains(~A, ~same, ~laws, t, p, x)(e))

# what xs holds at k, its first n hold at k, when k is below n
def List.take_get(
  -A: Data,
  xs: List<&2, A>,
  k: Nat,
  n: Nat,
  -x: A
) -> {List.get(&2, A, xs, k) == Some{x}: Maybe<&2, A>} -> {Nat.is_lt(k, n) == True{}: Bool} -> {List.get(&2, A, List.take(&2, A, xs, n), k) == Some{x}: Maybe<&2, A>}:
  match xs k n:
    case Nil{} j m:
      h => l => Empty.absurd(
        {None{} == Some{x}: Maybe<&2, A>},
        Shared.Maybe.none_ne_some(A, x, h)
      )
    case Con{+h, +t} 0n 0n:
      e => l => Empty.absurd({None{} == Some{x}: Maybe<&2, A>}, Shared.Bool.false_ne_true(l))
    case Con{+h, +t} 0n 1n+m:
      e => l => e
    case Con{+h, +t} 1n+p 0n:
      e => l => Empty.absurd({None{} == Some{x}: Maybe<&2, A>}, Shared.Bool.false_ne_true(l))
    case Con{+h, +t} 1n+p 1n+m:
      List.take_get(A, t, p, m, x)

# what the first n of xs hold at k, xs holds at k, and k is below n
def List.get_take(
  -A: Data,
  xs: List<&2, A>,
  k: Nat,
  n: Nat,
  -x: A
) -> {List.get(&2, A, List.take(&2, A, xs, n), k) == Some{x}: Maybe<&2, A>} -> {List.get(&2, A, xs, k) == Some{x}: Maybe<&2, A>} & {Nat.is_lt(k, n) == True{}: Bool}:
  match xs k n:
    case Nil{} j m:
      h => Empty.absurd(
        {None{} == Some{x}: Maybe<&2, A>} & {Nat.is_lt(j, m) == True{}: Bool},
        Shared.Maybe.none_ne_some(A, x, h)
      )
    case Con{+h, +t} 0n 0n:
      e => Empty.absurd(
        {Some{h} == Some{x}: Maybe<&2, A>} & {False{} == True{}: Bool},
        Shared.Maybe.none_ne_some(A, x, e)
      )
    case Con{+h, +t} 0n 1n+m:
      e => (e, {==})
    case Con{+h, +t} 1n+p 0n:
      e => Empty.absurd(
        {List.get(&2, A, t, p) == Some{x}: Maybe<&2, A>} & {False{} == True{}: Bool},
        Shared.Maybe.none_ne_some(A, x, e)
      )
    case Con{+h, +t} 1n+p 1n+m:
      List.get_take(A, t, p, m, x)

# the first n of xs and then the rest are xs
def List.take_drop(
  -A: Data,
  xs: List<&2, A>,
  n: Nat
) -> {xs == List.append(&2, A, List.take(&2, A, xs, n), List.drop(&2, A, xs, n)): List<&2, A>}:
  match xs n:
    case Nil{} m:
      {==}
    case Con{+h, +t} 0n:
      {==}
    case Con{+h, +t} 1n+p:
      Equal.cong(
        List<&2, A>,
        List<&2, A>,
        l => h <> l,
        t,
        List.append(&2, A, List.take(&2, A, t, p), List.drop(&2, A, t, p)),
        List.take_drop(A, t, p)
      )

# a list extends each of its starts
def List.take_ext(-A: Data, +xs: List<&2, A>, +n: Nat) -> List.Ext(A, List.take(&2, A, xs, n), xs):
  (List.drop(&2, A, xs, n), List.take_drop(A, xs, n))

# Cases
# -----

# what holds of True when b is True, and of False when b is False, holds of b
def Bool.by(
  -P: Bool -> Type,
  b: Bool,
  t: {b == True{}: Bool} -> P(True{}),
  f: {b == False{}: Bool} -> P(False{})
) -> P(b):
  match b:
    case True{}:
      t({==})
    case False{}:
      f({==})

# what holds of None when m is None, and of Some{x} when m is Some{x}, holds of m
def Maybe.by(
  -A: Data,
  -P: Maybe<&2, A> -> Type,
  m: Maybe<&2, A>,
  n: {m == None{}: Maybe<&2, A>} -> P(None{}),
  s: @x: A -> {m == Some{x}: Maybe<&2, A>} -> P(Some{x})
) -> P(m):
  match m:
    case None{}:
      n({==})
    case Some{x}:
      s(x)({==})

# no Some equals None
def Maybe.some_ne_none(-A: Data, -x: A, e: {Some{x} == None{}: Maybe<&2, A>}) -> Empty:
  Shared.Maybe.none_ne_some(A, x, Equal.sym(Maybe<&2, A>, Some{x}, None{}, e))

# The first index of a hit
# ------------------------

# the index after the one that m holds
def List.index.up(m: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      None{}
    case Some{k}:
      Some{1n+k}

# 0 on a hit, else the index after the one that rest gives
def List.index.if(rest: Unit -> Maybe<&2, Nat>, hit: Bool) -> Maybe<&2, Nat>:
  match hit:
    case False{}:
      List.index.up(rest(Unit{}))
    case True{}:
      Some{0n}

# the index of the first element x of xs with p(g)(x)
def List.index(~A: Data, ~V: Data, ~p: V -> A -> Bool, xs: List<&2, A>, +g: V) -> Maybe<&2, Nat>:
  match xs:
    case Nil{}:
      None{}
    case Con{x, r}:
      List.index.if(u => List.index(~A, ~V, ~p, r, g), p(g)(x))

# an index after none is none
def List.index.up_none(m: Maybe<&2, Nat>) -> {List.index.up(m) == None{}: Maybe<&2, Nat>} -> {m == None{}: Maybe<&2, Nat>}:
  match m:
    case None{}:
      h => {==}
    case Some{k}:
      h => Empty.absurd({Some{k} == None{}: Maybe<&2, Nat>}, Maybe.some_ne_none(Nat, 1n+k, h))

# at the index that List.index gives, xs holds an element that p holds of
def List.index_get(
  ~A: Data,
  ~V: Data,
  ~p: V -> A -> Bool,
  xs: List<&2, A>,
  +g: V,
  -k: Nat
) -> {List.index(~A, ~V, ~p, xs, g) == Some{k}: Maybe<&2, Nat>} -> Exists(A, x => {List.get(&2, A, xs, k) == Some{x}: Maybe<&2, A>} & {p(g)(x) == True{}: Bool}):
  match xs:
    case Nil{}:
      h => Empty.absurd(Exists(A, x => {None{} == Some{x}: Maybe<&2, A>} & {p(g)(x) == True{}: Bool}), Shared.Maybe.none_ne_some(Nat, k, h))
    case Con{+x, +r}:
      Bool.by(
        hit => {List.index.if(u => List.index(~A, ~V, ~p, r, g), hit) == Some{k}: Maybe<&2, Nat>} -> Exists(A, y => {List.get(&2, A, x <> r, k) == Some{y}: Maybe<&2, A>} & {p(g)(y) == True{}: Bool}),
        p(g)(x),
        et => h => (
          %Shared.Maybe.some_inj(Nat, 0n, k, h): Exists(A, y => {List.get(&2, A, x <> r, _) == Some{y}: Maybe<&2, A>} & {p(g)(y) == True{}: Bool})
          (x, ({==}, et))
        ),
        ef => Maybe.by(
          Nat,
          m => {List.index.up(m) == Some{k}: Maybe<&2, Nat>} -> Exists(A, y => {List.get(&2, A, x <> r, k) == Some{y}: Maybe<&2, A>} & {p(g)(y) == True{}: Bool}),
          List.index(~A, ~V, ~p, r, g),
          en => h => Empty.absurd(Exists(A, y => {List.get(&2, A, x <> r, k) == Some{y}: Maybe<&2, A>} & {p(g)(y) == True{}: Bool}), Shared.Maybe.none_ne_some(Nat, k, h)),
          j => ej => h => (
            %Shared.Maybe.some_inj(Nat, 1n+j, k, h): Exists(A, y => {List.get(&2, A, x <> r, _) == Some{y}: Maybe<&2, A>} & {p(g)(y) == True{}: Bool})
            List.index_get(~A, ~V, ~p, r, g, j)(ej)
          )
        )
      )


# from False = True on one Bool, anything
def Bool.clash(-P: Type, -b: Bool, f: {b == False{}: Bool}, t: {b == True{}: Bool}) -> P:
  Empty.absurd(P, Shared.Bool.false_ne_true(Equal.trans(Bool, False{}, b, True{}, Equal.sym(Bool, b, False{}, f), t)))

# no element of xs that p holds of comes before the index that List.index gives
def List.index_first(
  ~A: Data,
  ~V: Data,
  ~p: V -> A -> Bool,
  xs: List<&2, A>,
  +g: V,
  -k: Nat,
  j: Nat,
  -y: A
) -> {List.index(~A, ~V, ~p, xs, g) == Some{k}: Maybe<&2, Nat>} -> {List.get(&2, A, xs, j) == Some{y}: Maybe<&2, A>} -> {p(g)(y) == True{}: Bool} -> {Nat.is_le(k, j) == True{}: Bool}:
  match xs j:
    case Nil{} i:
      h1 => h2 => h3 => Empty.absurd({Nat.is_le(k, i) == True{}: Bool}, Shared.Maybe.none_ne_some(A, y, h2))
    case Con{+x, +r} 0n:
      h1 => +h2 => +h3 => Bool.by(
        hit => {List.index.if(u => List.index(~A, ~V, ~p, r, g), hit) == Some{k}: Maybe<&2, Nat>} -> {Nat.is_le(k, 0n) == True{}: Bool},
        p(g)(x),
        et => h => (
          %Shared.Maybe.some_inj(Nat, 0n, k, h): {Nat.is_le(_, 0n) == True{}: Bool}
          {==}
        ),
        ef => h => Bool.clash(
          {Nat.is_le(k, 0n) == True{}: Bool},
          p(g)(x),
          ef,
          (
            %Equal.sym(A, x, y, Shared.Maybe.some_inj(A, x, y, h2)): {p(g)(_) == True{}: Bool}
            h3
          )
        )
      )(h1)
    case Con{+x, +r} 1n+i:
      h1 => +h2 => +h3 => Bool.by(
        hit => {List.index.if(u => List.index(~A, ~V, ~p, r, g), hit) == Some{k}: Maybe<&2, Nat>} -> {Nat.is_le(k, 1n+i) == True{}: Bool},
        p(g)(x),
        et => h => (
          %Shared.Maybe.some_inj(Nat, 0n, k, h): {Nat.is_le(_, 1n+i) == True{}: Bool}
          {==}
        ),
        ef => Maybe.by(
          Nat,
          m => {List.index.up(m) == Some{k}: Maybe<&2, Nat>} -> {Nat.is_le(k, 1n+i) == True{}: Bool},
          List.index(~A, ~V, ~p, r, g),
          en => h => Empty.absurd({Nat.is_le(k, 1n+i) == True{}: Bool}, Shared.Maybe.none_ne_some(Nat, k, h)),
          n => ej => h => (
            %Shared.Maybe.some_inj(Nat, 1n+n, k, h): {Nat.is_le(_, 1n+i) == True{}: Bool}
            List.index_first(~A, ~V, ~p, r, g, n, i, y)(ej)(h2)(h3)
          )
        )
      )(h1)

# the first hit of xs is the first hit of xs and then zs
def List.index_append(
  ~A: Data,
  ~V: Data,
  ~p: V -> A -> Bool,
  xs: List<&2, A>,
  -zs: List<&2, A>,
  +g: V,
  -k: Nat
) -> {List.index(~A, ~V, ~p, xs, g) == Some{k}: Maybe<&2, Nat>} -> {List.index(~A, ~V, ~p, List.append(&2, A, xs, zs), g) == Some{k}: Maybe<&2, Nat>}:
  match xs:
    case Nil{}:
      h => Empty.absurd({List.index(~A, ~V, ~p, zs, g) == Some{k}: Maybe<&2, Nat>}, Shared.Maybe.none_ne_some(Nat, k, h))
    case Con{+x, +r}:
      Bool.by(
        hit => {List.index.if(u => List.index(~A, ~V, ~p, r, g), hit) == Some{k}: Maybe<&2, Nat>} -> {List.index.if(u => List.index(~A, ~V, ~p, List.append(&2, A, r, zs), g), hit) == Some{k}: Maybe<&2, Nat>},
        p(g)(x),
        et => h => h,
        ef => Maybe.by(
          Nat,
          m => {List.index.up(m) == Some{k}: Maybe<&2, Nat>} -> {List.index.up(List.index(~A, ~V, ~p, List.append(&2, A, r, zs), g)) == Some{k}: Maybe<&2, Nat>},
          List.index(~A, ~V, ~p, r, g),
          en => h => Empty.absurd({List.index.up(List.index(~A, ~V, ~p, List.append(&2, A, r, zs), g)) == Some{k}: Maybe<&2, Nat>}, Shared.Maybe.none_ne_some(Nat, k, h)),
          n => ej => h => (
            %Equal.sym(Maybe<&2, Nat>, List.index(~A, ~V, ~p, List.append(&2, A, r, zs), g), Some{n}, List.index_append(~A, ~V, ~p, r, zs, g, n)(ej)): {List.index.up(_) == Some{k}: Maybe<&2, Nat>}
            h
          )
        )
      )

# List.index_ext, with its premises as arguments
def List.index_ext.of(
  ~A: Data,
  ~V: Data,
  ~p: V -> A -> Bool,
  xs: List<&2, A>,
  -ys: List<&2, A>,
  +g: V,
  -k: Nat,
  e: List.Ext(A, xs, ys),
  h: {List.index(~A, ~V, ~p, xs, g) == Some{k}: Maybe<&2, Nat>}
) -> {List.index(~A, ~V, ~p, ys, g) == Some{k}: Maybe<&2, Nat>}:
  (zs, ez) = e
  %Equal.sym(List<&2, A>, ys, List.append(&2, A, xs, zs), ez): {List.index(~A, ~V, ~p, _, g) == Some{k}: Maybe<&2, Nat>}
  List.index_append(~A, ~V, ~p, xs, zs, g, k)(h)

# the first hit of xs is the first hit of an extension of xs
def List.index_ext(
  ~A: Data,
  ~V: Data,
  ~p: V -> A -> Bool,
  xs: List<&2, A>,
  -ys: List<&2, A>,
  +g: V,
  -k: Nat
) -> List.Ext(A, xs, ys) -> {List.index(~A, ~V, ~p, xs, g) == Some{k}: Maybe<&2, Nat>} -> {List.index(~A, ~V, ~p, ys, g) == Some{k}: Maybe<&2, Nat>}:
  e => h => List.index_ext.of(~A, ~V, ~p, xs, ys, g, k, e, h)

# when List.index gives nothing, p holds of no element of xs
def List.index_none(
  ~A: Data,
  ~V: Data,
  ~p: V -> A -> Bool,
  xs: List<&2, A>,
  +g: V,
  j: Nat,
  -y: A
) -> {List.index(~A, ~V, ~p, xs, g) == None{}: Maybe<&2, Nat>} -> {List.get(&2, A, xs, j) == Some{y}: Maybe<&2, A>} -> {p(g)(y) == False{}: Bool}:
  match xs j:
    case Nil{} i:
      h1 => h2 => Empty.absurd({p(g)(y) == False{}: Bool}, Shared.Maybe.none_ne_some(A, y, h2))
    case Con{+x, +r} 0n:
      h1 => +h2 => Bool.by(
        hit => {List.index.if(u => List.index(~A, ~V, ~p, r, g), hit) == None{}: Maybe<&2, Nat>} -> {p(g)(y) == False{}: Bool},
        p(g)(x),
        et => h => Empty.absurd({p(g)(y) == False{}: Bool}, Maybe.some_ne_none(Nat, 0n, h)),
        ef => h => (
          %Shared.Maybe.some_inj(A, x, y, h2): {p(g)(_) == False{}: Bool}
          ef
        )
      )(h1)
    case Con{+x, +r} 1n+i:
      h1 => +h2 => Bool.by(
        hit => {List.index.if(u => List.index(~A, ~V, ~p, r, g), hit) == None{}: Maybe<&2, Nat>} -> {p(g)(y) == False{}: Bool},
        p(g)(x),
        et => h => Empty.absurd({p(g)(y) == False{}: Bool}, Maybe.some_ne_none(Nat, 0n, h)),
        ef => h => List.index_none(~A, ~V, ~p, r, g, i, y)(List.index.up_none(List.index(~A, ~V, ~p, r, g))(h))(h2)
      )(h1)

# when p holds of an element of xs, List.index gives an index
def List.index_some(
  ~A: Data,
  ~V: Data,
  ~p: V -> A -> Bool,
  +xs: List<&2, A>,
  +g: V,
  +j: Nat,
  -y: A
) -> {List.get(&2, A, xs, j) == Some{y}: Maybe<&2, A>} -> {p(g)(y) == True{}: Bool} -> Exists(Nat, k => {List.index(~A, ~V, ~p, xs, g) == Some{k}: Maybe<&2, Nat>}):
  +h2 => +h3 => Maybe.by(
    Nat,
    m => Exists(Nat, k => {m == Some{k}: Maybe<&2, Nat>}),
    List.index(~A, ~V, ~p, xs, g),
    en => Bool.clash(
      Exists(Nat, k => {None{} == Some{k}: Maybe<&2, Nat>}),
      p(g)(y),
      List.index_none(~A, ~V, ~p, xs, g, j, y)(en)(h2),
      h3
    ),
    k => ek => (k, {==})
  )

# when p holds of no element of xs and of x, the first hit of xs and then x is x
def List.index_snoc(
  ~A: Data,
  ~V: Data,
  ~p: V -> A -> Bool,
  xs: List<&2, A>,
  +x: A,
  +g: V
) -> {List.index(~A, ~V, ~p, xs, g) == None{}: Maybe<&2, Nat>} -> {p(g)(x) == True{}: Bool} -> {List.index(~A, ~V, ~p, List.append(&2, A, xs, [x]), g) == Some{List.length(&2, A, xs)}: Maybe<&2, Nat>}:
  match xs:
    case Nil{}:
      h1 => h2 => (
        %Equal.sym(Bool, p(g)(x), True{}, h2): {List.index.if(u => None{}, _) == Some{0n}: Maybe<&2, Nat>}
        {==}
      )
    case Con{+y, +r}:
      h1 => +h2 => Bool.by(
        hit => {List.index.if(u => List.index(~A, ~V, ~p, r, g), hit) == None{}: Maybe<&2, Nat>} -> {List.index.if(u => List.index(~A, ~V, ~p, List.append(&2, A, r, [x]), g), hit) == Some{1n+List.length(&2, A, r)}: Maybe<&2, Nat>},
        p(g)(y),
        et => h => Empty.absurd({Some{0n} == Some{1n+List.length(&2, A, r)}: Maybe<&2, Nat>}, Maybe.some_ne_none(Nat, 0n, h)),
        ef => h => Equal.cong(
          Maybe<&2, Nat>,
          Maybe<&2, Nat>,
          m => List.index.up(m),
          List.index(~A, ~V, ~p, List.append(&2, A, r, [x]), g),
          Some{List.length(&2, A, r)},
          List.index_snoc(~A, ~V, ~p, r, x, g)(List.index.up_none(List.index(~A, ~V, ~p, r, g))(h))(h2)
        )
      )(h1)


# Members
# -------

# a member of h <> t is h or a member of t: what follows from each follows
def List.contains_cons_by(
  ~A: Data,
  ~same: A -> A -> Bool,
  ~laws: Shared.Eq.Laws(A, same),
  -P: Type,
  +h: A,
  -t: List<&2, A>,
  +x: A,
  hin: {List.contains(~A, ~same, h <> t, x) == True{}: Bool},
  a: {h == x: A} -> P,
  b: {List.contains(~A, ~same, t, x) == True{}: Bool} -> P
) -> P:
  Bool.by(
    s => {List.any.if(u => List.contains(~A, ~same, t, x), s) == True{}: Bool} -> P,
    same(h, x),
    es => c => a(Shared.Eq.sound(~A, ~same, laws, h, x)(es)),
    es => c => b(c)
  )(hin)

# x is in b <> s, so it is in b <> y <> s
def List.contains_skip(
  ~A: Data,
  ~same: A -> A -> Bool,
  +b: A,
  +y: A,
  +s: List<&2, A>,
  +x: A
) -> {List.contains(~A, ~same, b <> s, x) == True{}: Bool} -> {List.contains(~A, ~same, b <> y <> s, x) == True{}: Bool}:
  Bool.by(
    c => {List.any.if(u => List.contains(~A, ~same, s, x), c) == True{}: Bool} -> {List.any.if(u => List.contains(~A, ~same, y <> s, x), c) == True{}: Bool},
    same(b, x),
    es => h => {==},
    es => h => Shared.List.contains_cons(~A, ~same, y, s, x)(h)
  )

# a member of t that Q holds of is a member of h <> t that Q holds of
def List.exists_cons(
  ~A: Data,
  ~same: A -> A -> Bool,
  -Q: A -> Type,
  h: A,
  t: List<&2, A>,
  r: Exists(A, x => {List.contains(~A, ~same, t, x) == True{}: Bool} & Q(x))
) -> Exists(A, x => {List.contains(~A, ~same, h <> t, x) == True{}: Bool} & Q(x)):
  (+x, w) = r
  (c, q) = w
  (x, (Shared.List.contains_cons(~A, ~same, h, t, x)(c), q))

# The one hit
# -----------

# f holds of what List.find gives
def List.find_hit(
  ~A: Data,
  ~f: A -> Bool,
  xs: List<&2, A>,
  -x: A
) -> {List.find(~A, ~f, xs) == Some{x}: Maybe<&2, A>} -> {f(x) == True{}: Bool}:
  match xs:
    case Nil{}:
      h => Empty.absurd({f(x) == True{}: Bool}, Shared.Maybe.none_ne_some(A, x, h))
    case Con{+h, +r}:
      Bool.by(
        hit => {List.find.if(A, h, u => List.find(~A, ~f, r), hit) == Some{x}: Maybe<&2, A>} -> {f(x) == True{}: Bool},
        f(h),
        et => e => (
          %Shared.Maybe.some_inj(A, h, x, e): {f(_) == True{}: Bool}
          et
        ),
        ef => e => List.find_hit(~A, ~f, r, x)(e)
      )

# what List.find gives is a member of xs
def List.find_in(
  ~A: Data,
  ~f: A -> Bool,
  ~same: A -> A -> Bool,
  ~laws: Shared.Eq.Laws(A, same),
  xs: List<&2, A>,
  +x: A
) -> {List.find(~A, ~f, xs) == Some{x}: Maybe<&2, A>} -> {List.contains(~A, ~same, xs, x) == True{}: Bool}:
  match xs:
    case Nil{}:
      h => Empty.absurd({False{} == True{}: Bool}, Shared.Maybe.none_ne_some(A, x, h))
    case Con{+h, +r}:
      Bool.by(
        hit => {List.find.if(A, h, u => List.find(~A, ~f, r), hit) == Some{x}: Maybe<&2, A>} -> {List.contains(~A, ~same, h <> r, x) == True{}: Bool},
        f(h),
        et => e => (
          %Shared.Maybe.some_inj(A, h, x, e): {List.contains(~A, ~same, h <> r, _) == True{}: Bool}
          List.contains_head(~A, ~same, ~laws, h, r)
        ),
        ef => e => Shared.List.contains_cons(~A, ~same, h, r, x)(List.find_in(~A, ~f, ~same, ~laws, r, x)(e))
      )

# List.find gives x, when x is the one member of xs that f holds of
def List.find_one(
  ~A: Data,
  ~f: A -> Bool,
  ~same: A -> A -> Bool,
  ~laws: Shared.Eq.Laws(A, same),
  xs: List<&2, A>,
  +x: A
) -> {List.contains(~A, ~same, xs, x) == True{}: Bool} -> {f(x) == True{}: Bool} -> (@y: A -> {List.contains(~A, ~same, xs, y) == True{}: Bool} -> {f(y) == True{}: Bool} -> {y == x: A}) -> {List.find(~A, ~f, xs) == Some{x}: Maybe<&2, A>}:
  match xs:
    case Nil{}:
      hin => ht => uniq => Empty.absurd({None{} == Some{x}: Maybe<&2, A>}, Shared.Bool.false_ne_true(hin))
    case Con{+h, +r}:
      Bool.by(
        hit => {List.contains(~A, ~same, h <> r, x) == True{}: Bool} -> {f(x) == True{}: Bool} -> (@y: A -> {List.contains(~A, ~same, h <> r, y) == True{}: Bool} -> {f(y) == True{}: Bool} -> {y == x: A}) -> {List.find.if(A, h, u => List.find(~A, ~f, r), hit) == Some{x}: Maybe<&2, A>},
        f(h),
        +et => hin => ht => uniq => Equal.cong(
          A,
          Maybe<&2, A>,
          z => Some{z},
          h,
          x,
          uniq(h)(List.contains_head(~A, ~same, ~laws, h, r))(et)
        ),
        +ef => hin => +ht => uniq => List.find_one(~A, ~f, ~same, ~laws, r, x)(
          List.contains_cons_by(
            ~A,
            ~same,
            ~laws,
            {List.contains(~A, ~same, r, x) == True{}: Bool},
            h,
            r,
            x,
            hin,
            exh => Bool.clash(
              {List.contains(~A, ~same, r, x) == True{}: Bool},
              f(h),
              ef,
              (
                %Equal.sym(A, h, x, exh): {f(_) == True{}: Bool}
                ht
              )
            ),
            c => c
          )
        )(ht)(+y => hy => ty => uniq(y)(Shared.List.contains_cons(~A, ~same, h, r, y)(hy))(ty))
      )

# List.find gives nothing, when f holds of no member of xs
def List.find_none(
  ~A: Data,
  ~f: A -> Bool,
  ~same: A -> A -> Bool,
  ~laws: Shared.Eq.Laws(A, same),
  xs: List<&2, A>
) -> (@y: A -> {List.contains(~A, ~same, xs, y) == True{}: Bool} -> {f(y) == True{}: Bool} -> Empty) -> {List.find(~A, ~f, xs) == None{}: Maybe<&2, A>}:
  match xs:
    case Nil{}:
      no => {==}
    case Con{+h, +r}:
      Bool.by(
        hit => (@y: A -> {List.contains(~A, ~same, h <> r, y) == True{}: Bool} -> {f(y) == True{}: Bool} -> Empty) -> {List.find.if(A, h, u => List.find(~A, ~f, r), hit) == None{}: Maybe<&2, A>},
        f(h),
        et => no => Empty.absurd({Some{h} == None{}: Maybe<&2, A>}, no(h)(List.contains_head(~A, ~same, ~laws, h, r))(et)),
        ef => no => List.find_none(~A, ~f, ~same, ~laws, r)(+y => hy => ty => no(y)(Shared.List.contains_cons(~A, ~same, h, r, y)(hy))(ty))
      )

# the first element x of xs with p(g)(x)
def List.pick(~A: Data, ~V: Data, ~p: V -> A -> Bool, xs: List<&2, A>, +g: V) -> Maybe<&2, A>:
  match xs:
    case Nil{}:
      None{}
    case Con{+x, r}:
      List.find.if(A, x, u => List.pick(~A, ~V, ~p, r, g), p(g)(x))

# p(g) holds of what List.pick gives
def List.pick_hit(
  ~A: Data,
  ~V: Data,
  ~p: V -> A -> Bool,
  xs: List<&2, A>,
  +g: V,
  -x: A
) -> {List.pick(~A, ~V, ~p, xs, g) == Some{x}: Maybe<&2, A>} -> {p(g)(x) == True{}: Bool}:
  match xs:
    case Nil{}:
      h => Empty.absurd({p(g)(x) == True{}: Bool}, Shared.Maybe.none_ne_some(A, x, h))
    case Con{+h, +r}:
      Bool.by(
        hit => {List.find.if(A, h, u => List.pick(~A, ~V, ~p, r, g), hit) == Some{x}: Maybe<&2, A>} -> {p(g)(x) == True{}: Bool},
        p(g)(h),
        et => e => (
          %Shared.Maybe.some_inj(A, h, x, e): {p(g)(_) == True{}: Bool}
          et
        ),
        ef => e => List.pick_hit(~A, ~V, ~p, r, g, x)(e)
      )

# what List.pick gives is a member of xs
def List.pick_in(
  ~A: Data,
  ~V: Data,
  ~p: V -> A -> Bool,
  ~same: A -> A -> Bool,
  ~laws: Shared.Eq.Laws(A, same),
  xs: List<&2, A>,
  +g: V,
  +x: A
) -> {List.pick(~A, ~V, ~p, xs, g) == Some{x}: Maybe<&2, A>} -> {List.contains(~A, ~same, xs, x) == True{}: Bool}:
  match xs:
    case Nil{}:
      h => Empty.absurd({False{} == True{}: Bool}, Shared.Maybe.none_ne_some(A, x, h))
    case Con{+h, +r}:
      Bool.by(
        hit => {List.find.if(A, h, u => List.pick(~A, ~V, ~p, r, g), hit) == Some{x}: Maybe<&2, A>} -> {List.contains(~A, ~same, h <> r, x) == True{}: Bool},
        p(g)(h),
        et => e => (
          %Shared.Maybe.some_inj(A, h, x, e): {List.contains(~A, ~same, h <> r, _) == True{}: Bool}
          List.contains_head(~A, ~same, ~laws, h, r)
        ),
        ef => e => Shared.List.contains_cons(~A, ~same, h, r, x)(List.pick_in(~A, ~V, ~p, ~same, ~laws, r, g, x)(e))
      )

# List.pick gives x, when x is the one member of xs that p(g) holds of
def List.pick_one(
  ~A: Data,
  ~V: Data,
  ~p: V -> A -> Bool,
  ~same: A -> A -> Bool,
  ~laws: Shared.Eq.Laws(A, same),
  xs: List<&2, A>,
  +g: V,
  +x: A
) -> {List.contains(~A, ~same, xs, x) == True{}: Bool} -> {p(g)(x) == True{}: Bool} -> (@y: A -> {List.contains(~A, ~same, xs, y) == True{}: Bool} -> {p(g)(y) == True{}: Bool} -> {y == x: A}) -> {List.pick(~A, ~V, ~p, xs, g) == Some{x}: Maybe<&2, A>}:
  match xs:
    case Nil{}:
      hin => ht => uniq => Empty.absurd({None{} == Some{x}: Maybe<&2, A>}, Shared.Bool.false_ne_true(hin))
    case Con{+h, +r}:
      Bool.by(
        hit => {List.contains(~A, ~same, h <> r, x) == True{}: Bool} -> {p(g)(x) == True{}: Bool} -> (@y: A -> {List.contains(~A, ~same, h <> r, y) == True{}: Bool} -> {p(g)(y) == True{}: Bool} -> {y == x: A}) -> {List.find.if(A, h, u => List.pick(~A, ~V, ~p, r, g), hit) == Some{x}: Maybe<&2, A>},
        p(g)(h),
        +et => hin => ht => uniq => Equal.cong(
          A,
          Maybe<&2, A>,
          z => Some{z},
          h,
          x,
          uniq(h)(List.contains_head(~A, ~same, ~laws, h, r))(et)
        ),
        +ef => hin => +ht => uniq => List.pick_one(~A, ~V, ~p, ~same, ~laws, r, g, x)(
          List.contains_cons_by(
            ~A,
            ~same,
            ~laws,
            {List.contains(~A, ~same, r, x) == True{}: Bool},
            h,
            r,
            x,
            hin,
            exh => Bool.clash(
              {List.contains(~A, ~same, r, x) == True{}: Bool},
              p(g)(h),
              ef,
              (
                %Equal.sym(A, h, x, exh): {p(g)(_) == True{}: Bool}
                ht
              )
            ),
            c => c
          )
        )(ht)(+y => hy => ty => uniq(y)(Shared.List.contains_cons(~A, ~same, h, r, y)(hy))(ty))
      )

# List.pick gives nothing, when p(g) holds of no member of xs
def List.pick_none(
  ~A: Data,
  ~V: Data,
  ~p: V -> A -> Bool,
  ~same: A -> A -> Bool,
  ~laws: Shared.Eq.Laws(A, same),
  xs: List<&2, A>,
  +g: V
) -> (@y: A -> {List.contains(~A, ~same, xs, y) == True{}: Bool} -> {p(g)(y) == True{}: Bool} -> Empty) -> {List.pick(~A, ~V, ~p, xs, g) == None{}: Maybe<&2, A>}:
  match xs:
    case Nil{}:
      no => {==}
    case Con{+h, +r}:
      Bool.by(
        hit => (@y: A -> {List.contains(~A, ~same, h <> r, y) == True{}: Bool} -> {p(g)(y) == True{}: Bool} -> Empty) -> {List.find.if(A, h, u => List.pick(~A, ~V, ~p, r, g), hit) == None{}: Maybe<&2, A>},
        p(g)(h),
        et => no => Empty.absurd({Some{h} == None{}: Maybe<&2, A>}, no(h)(List.contains_head(~A, ~same, ~laws, h, r))(et)),
        ef => no => List.pick_none(~A, ~V, ~p, ~same, ~laws, r, g)(+y => hy => ty => no(y)(Shared.List.contains_cons(~A, ~same, h, r, y)(hy))(ty))
      )


# Majorities
# ----------

# how many elements x of xs have p(g)(x)
def List.count(~A: Data, ~V: Data, ~p: V -> A -> Bool, xs: List<&2, A>, +g: V) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{x, r}:
      Shared.Nat.add_if(p(g)(x), List.count(~A, ~V, ~p, r, g))

# k is more than half of n
def Nat.most(n: Nat, +k: Nat) -> Bool:
  Nat.is_lt(n, Nat.add(k, k))

# a list has no more hits than elements
def List.count_le(
  ~A: Data,
  ~V: Data,
  ~p: V -> A -> Bool,
  xs: List<&2, A>,
  +g: V
) -> {Nat.is_le(List.count(~A, ~V, ~p, xs, g), List.length(&2, A, xs)) == True{}: Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      Shared.Nat.add_if_le_succ(p(g)(x), List.count(~A, ~V, ~p, r, g), List.length(&2, A, r))(List.count_le(~A, ~V, ~p, r, g))

# two numbers that are each more than half of n add up to more than n
def Nat.most_apart(
  +n: Nat,
  +a: Nat,
  +b: Nat
) -> {Nat.is_le(Nat.add(a, b), n) == True{}: Bool} -> {Nat.most(n, a) == True{}: Bool} -> {Nat.most(n, b) == True{}: Bool} -> Empty:
  +h1 => +h2 => +h3 => Bool.by(
    c => Empty,
    Nat.is_le(a, b),
    et => Bool.clash(
      Empty,
      Nat.is_lt(Nat.add(a, a), Nat.add(a, a)),
      Shared.Nat.lt_irrefl(Nat.add(a, a)),
      Shared.Nat.le_lt(Nat.add(a, a), n, Nat.add(a, a))(
        Shared.Nat.le_trans(Nat.add(a, a), Nat.add(a, b), n)(Shared.Nat.add_le_left(a, a, b)(et))(h1)
      )(h2)
    ),
    ef => Bool.clash(
      Empty,
      Nat.is_lt(Nat.add(b, b), Nat.add(b, b)),
      Shared.Nat.lt_irrefl(Nat.add(b, b)),
      Shared.Nat.le_lt(Nat.add(b, b), n, Nat.add(b, b))(
        Shared.Nat.le_trans(Nat.add(b, b), Nat.add(a, b), n)(Shared.Nat.add_le_right(a, b, b)(Shared.Nat.nle_le(a, b)(ef)))(h1)
      )(h3)
    )
  )

# List.most_meet.go at the first element h, by whether p and q hold of it (a and b)
def List.most_meet.at(
  ~A: Data,
  ~V: Data,
  ~W: Data,
  ~p: V -> A -> Bool,
  ~q: W -> A -> Bool,
  ~same: A -> A -> Bool,
  ~laws: Shared.Eq.Laws(A, same),
  +h: A,
  +t: List<&2, A>,
  +g1: V,
  +g2: W,
  ih: Exists(A, x => {List.contains(~A, ~same, t, x) == True{}: Bool} & ({p(g1)(x) == True{}: Bool} & {q(g2)(x) == True{}: Bool})) | {Nat.is_le(Nat.add(List.count(~A, ~V, ~p, t, g1), List.count(~A, ~W, ~q, t, g2)), List.length(&2, A, t)) == True{}: Bool},
  a: Bool,
  b: Bool,
  ea: {p(g1)(h) == a: Bool},
  eb: {q(g2)(h) == b: Bool}
) -> Exists(A, x => {List.contains(~A, ~same, h <> t, x) == True{}: Bool} & ({p(g1)(x) == True{}: Bool} & {q(g2)(x) == True{}: Bool})) | {Nat.is_le(Nat.add(Shared.Nat.add_if(a, List.count(~A, ~V, ~p, t, g1)), Shared.Nat.add_if(b, List.count(~A, ~W, ~q, t, g2))), 1n+List.length(&2, A, t)) == True{}: Bool}:
  match ih a b:
    case Inl{m} a0 b0:
      Inl{List.exists_cons(~A, ~same, x => {p(g1)(x) == True{}: Bool} & {q(g2)(x) == True{}: Bool}, h, t, m)}
    case Inr{l} True{} True{}:
      Inl{(h, (List.contains_head(~A, ~same, ~laws, h, t), (ea, eb)))}
    case Inr{l} True{} False{}:
      Inr{l}
    case Inr{l} False{} True{}:
      Inr{(
        %Equal.sym(Nat, Nat.add(List.count(~A, ~V, ~p, t, g1), 1n+List.count(~A, ~W, ~q, t, g2)), 1n+Nat.add(List.count(~A, ~V, ~p, t, g1), List.count(~A, ~W, ~q, t, g2)), Shared.Nat.add_succ(List.count(~A, ~V, ~p, t, g1), List.count(~A, ~W, ~q, t, g2))): {Nat.is_le(_, 1n+List.length(&2, A, t)) == True{}: Bool}
        l
      )}
    case Inr{l} False{} False{}:
      Inr{Shared.Nat.le_succ(Nat.add(List.count(~A, ~V, ~p, t, g1), List.count(~A, ~W, ~q, t, g2)), List.length(&2, A, t))(l)}

# xs has a member that p and q both hold of, or their hits together are no more than xs
def List.most_meet.go(
  ~A: Data,
  ~V: Data,
  ~W: Data,
  ~p: V -> A -> Bool,
  ~q: W -> A -> Bool,
  ~same: A -> A -> Bool,
  ~laws: Shared.Eq.Laws(A, same),
  xs: List<&2, A>,
  +g1: V,
  +g2: W
) -> Exists(A, x => {List.contains(~A, ~same, xs, x) == True{}: Bool} & ({p(g1)(x) == True{}: Bool} & {q(g2)(x) == True{}: Bool})) | {Nat.is_le(Nat.add(List.count(~A, ~V, ~p, xs, g1), List.count(~A, ~W, ~q, xs, g2)), List.length(&2, A, xs)) == True{}: Bool}:
  match xs:
    case Nil{}:
      Inr{{==}}
    case Con{+h, +t}:
      List.most_meet.at(~A, ~V, ~W, ~p, ~q, ~same, ~laws, h, t, g1, g2, List.most_meet.go(~A, ~V, ~W, ~p, ~q, ~same, ~laws, t, g1, g2), p(g1)(h), q(g2)(h), {==}, {==})

# List.most_meet, with r what List.most_meet.go gives
def List.most_meet.of(
  ~A: Data,
  ~V: Data,
  ~W: Data,
  ~p: V -> A -> Bool,
  ~q: W -> A -> Bool,
  ~same: A -> A -> Bool,
  ~laws: Shared.Eq.Laws(A, same),
  +xs: List<&2, A>,
  +g1: V,
  +g2: W,
  r: Exists(A, x => {List.contains(~A, ~same, xs, x) == True{}: Bool} & ({p(g1)(x) == True{}: Bool} & {q(g2)(x) == True{}: Bool})) | {Nat.is_le(Nat.add(List.count(~A, ~V, ~p, xs, g1), List.count(~A, ~W, ~q, xs, g2)), List.length(&2, A, xs)) == True{}: Bool},
  m1: {Nat.most(List.length(&2, A, xs), List.count(~A, ~V, ~p, xs, g1)) == True{}: Bool},
  m2: {Nat.most(List.length(&2, A, xs), List.count(~A, ~W, ~q, xs, g2)) == True{}: Bool}
) -> Exists(A, x => {List.contains(~A, ~same, xs, x) == True{}: Bool} & ({p(g1)(x) == True{}: Bool} & {q(g2)(x) == True{}: Bool})):
  match r:
    case Inl{m}:
      m
    case Inr{l}:
      Empty.absurd(Exists(A, x => {List.contains(~A, ~same, xs, x) == True{}: Bool} & ({p(g1)(x) == True{}: Bool} & {q(g2)(x) == True{}: Bool})), Nat.most_apart(List.length(&2, A, xs), List.count(~A, ~V, ~p, xs, g1), List.count(~A, ~W, ~q, xs, g2))(l)(m1)(m2))

# two majorities of one list share a member
def List.most_meet(
  ~A: Data,
  ~V: Data,
  ~W: Data,
  ~p: V -> A -> Bool,
  ~q: W -> A -> Bool,
  ~same: A -> A -> Bool,
  ~laws: Shared.Eq.Laws(A, same),
  +xs: List<&2, A>,
  +g1: V,
  +g2: W
) -> {Nat.most(List.length(&2, A, xs), List.count(~A, ~V, ~p, xs, g1)) == True{}: Bool} -> {Nat.most(List.length(&2, A, xs), List.count(~A, ~W, ~q, xs, g2)) == True{}: Bool} -> Exists(A, x => {List.contains(~A, ~same, xs, x) == True{}: Bool} & ({p(g1)(x) == True{}: Bool} & {q(g2)(x) == True{}: Bool})):
  m1 => m2 => List.most_meet.of(~A, ~V, ~W, ~p, ~q, ~same, ~laws, xs, g1, g2, List.most_meet.go(~A, ~V, ~W, ~p, ~q, ~same, ~laws, xs, g1, g2), m1, m2)

# a test q that holds wherever p holds has no fewer hits; imp, the reason, is a
# closed lemma, and h what it needs to know of g1 and g2
def List.count_mono(
  ~A: Data,
  ~V: Data,
  ~W: Data,
  ~p: V -> A -> Bool,
  ~q: W -> A -> Bool,
  ~H: V -> W -> Data,
  ~imp: @g1: V -> @g2: W -> H(g1)(g2) -> @x: A -> {p(g1)(x) == True{}: Bool} -> {q(g2)(x) == True{}: Bool},
  xs: List<&2, A>,
  +g1: V,
  +g2: W,
  +h: H(g1)(g2)
) -> {Nat.is_le(List.count(~A, ~V, ~p, xs, g1), List.count(~A, ~W, ~q, xs, g2)) == True{}: Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      Bool.by(
        c => {Nat.is_le(Shared.Nat.add_if(c, List.count(~A, ~V, ~p, r, g1)), Shared.Nat.add_if(q(g2)(x), List.count(~A, ~W, ~q, r, g2))) == True{}: Bool},
        p(g1)(x),
        et => (
          %Equal.sym(Bool, q(g2)(x), True{}, imp(g1)(g2)(h)(x)(et)): {Nat.is_le(1n+List.count(~A, ~V, ~p, r, g1), Shared.Nat.add_if(_, List.count(~A, ~W, ~q, r, g2))) == True{}: Bool}
          List.count_mono(~A, ~V, ~W, ~p, ~q, ~H, ~imp, r, g1, g2, h)
        ),
        ef => Shared.Nat.le_add_if(q(g2)(x), List.count(~A, ~V, ~p, r, g1), List.count(~A, ~W, ~q, r, g2))(List.count_mono(~A, ~V, ~W, ~p, ~q, ~H, ~imp, r, g1, g2, h))
      )

# more than half stays more than half as it grows
def Nat.most_mono(
  n: Nat,
  +a: Nat,
  +b: Nat
) -> {Nat.is_le(a, b) == True{}: Bool} -> {Nat.most(n, a) == True{}: Bool} -> {Nat.most(n, b) == True{}: Bool}:
  +h => m => Shared.Nat.lt_le(n, Nat.add(a, a), Nat.add(b, b))(m)(Shared.Nat.add_le(a, b, a, b)(h)(h))

# a list with a hit has a member that p holds of
def List.count_pos(
  ~A: Data,
  ~V: Data,
  ~p: V -> A -> Bool,
  ~same: A -> A -> Bool,
  ~laws: Shared.Eq.Laws(A, same),
  xs: List<&2, A>,
  +g: V
) -> {Nat.is_lt(0n, List.count(~A, ~V, ~p, xs, g)) == True{}: Bool} -> Exists(A, x => {List.contains(~A, ~same, xs, x) == True{}: Bool} & {p(g)(x) == True{}: Bool}):
  match xs:
    case Nil{}:
      h => Empty.absurd(Exists(A, x => {List.contains(~A, ~same, [], x) == True{}: Bool} & {p(g)(x) == True{}: Bool}), Shared.Bool.false_ne_true(h))
    case Con{+z, +r}:
      Bool.by(
        c => {Nat.is_lt(0n, Shared.Nat.add_if(c, List.count(~A, ~V, ~p, r, g))) == True{}: Bool} -> Exists(A, x => {List.contains(~A, ~same, z <> r, x) == True{}: Bool} & {p(g)(x) == True{}: Bool}),
        p(g)(z),
        et => h => (z, (List.contains_head(~A, ~same, ~laws, z, r), et)),
        ef => h => List.exists_cons(~A, ~same, y => {p(g)(y) == True{}: Bool}, z, r, List.count_pos(~A, ~V, ~p, ~same, ~laws, r, g)(h))
      )

# more than half of anything is more than nothing
def Nat.most_pos(n: Nat, k: Nat) -> {Nat.most(n, k) == True{}: Bool} -> {Nat.is_lt(0n, k) == True{}: Bool}:
  match n k:
    case 0n 0n:
      h => h
    case 1n+m 0n:
      h => h
    case 0n 1n+j:
      h => {==}
    case 1n+m 1n+j:
      h => {==}

# half of n, rounded down
def Nat.half(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+0n:
      0n
    case 2n+m:
      1n+Nat.half(m)

# one more than half of n is more than half of n
def Nat.half_most(n: Nat) -> {Nat.most(n, 1n+Nat.half(n)) == True{}: Bool}:
  match n:
    case 0n:
      {==}
    case 1n+0n:
      {==}
    case 2n+(+m):
      %Equal.sym(Nat, Nat.add(Nat.half(m), 2n+Nat.half(m)), 1n+Nat.add(Nat.half(m), 1n+Nat.half(m)), Shared.Nat.add_succ(Nat.half(m), 1n+Nat.half(m))): {Nat.is_lt(m, _) == True{}: Bool}
      Nat.half_most(m)

# half of a number above 0 is below it
def Nat.half_lt(m: Nat) -> {Nat.is_le(Nat.half(1n+m), m) == True{}: Bool}:
  match m:
    case 0n:
      {==}
    case 1n+0n:
      {==}
    case 2n+(+k):
      Shared.Nat.le_succ(Nat.half(1n+k), k)(Nat.half_lt(k))

# the first majority of xs: its shortest start that is more than half of it
def List.lead(-A: Data, +xs: List<&2, A>) -> List<&2, A>:
  List.take(&2, A, xs, 1n+Nat.half(List.length(&2, A, xs)))

# the first n of a list that has n are n
def List.length_take(
  -A: Data,
  xs: List<&2, A>,
  n: Nat
) -> {Nat.is_le(n, List.length(&2, A, xs)) == True{}: Bool} -> {List.length(&2, A, List.take(&2, A, xs, n)) == n: Nat}:
  match xs n:
    case Nil{} 0n:
      h => {==}
    case Nil{} 1n+p:
      h => Empty.absurd({0n == 1n+p: Nat}, Shared.Bool.false_ne_true(h))
    case Con{x, r} 0n:
      h => {==}
    case Con{x, r} 1n+p:
      h => Equal.cong(Nat, Nat, z => 1n+z, List.length(&2, A, List.take(&2, A, r, p)), p, List.length_take(A, r, p)(h))

# what is within ks is within h <> ks
def List.within_cons(
  ~A: Data,
  ~same: A -> A -> Bool,
  ps: List<&2, A>,
  +h: A,
  +ks: List<&2, A>
) -> {Shared.List.within(~A, ~same, ps, ks) == True{}: Bool} -> {Shared.List.within(~A, ~same, ps, h <> ks) == True{}: Bool}:
  match ps:
    case Nil{}:
      e => {==}
    case Con{+x, +r}:
      +e => Shared.Bool.and_both(List.contains(~A, ~same, h <> ks, x), Shared.List.within(~A, ~same, r, h <> ks))(
        Shared.List.contains_cons(~A, ~same, h, ks, x)(Shared.Bool.and_true_left(List.contains(~A, ~same, ks, x), Shared.List.within(~A, ~same, r, ks))(e))
      )(
        List.within_cons(~A, ~same, r, h, ks)(Shared.Bool.and_true_right(List.contains(~A, ~same, ks, x), Shared.List.within(~A, ~same, r, ks))(e))
      )

# each start of a list is within it
def List.take_within(
  ~A: Data,
  ~same: A -> A -> Bool,
  ~laws: Shared.Eq.Laws(A, same),
  xs: List<&2, A>,
  n: Nat
) -> {Shared.List.within(~A, ~same, List.take(&2, A, xs, n), xs) == True{}: Bool}:
  match xs n:
    case Nil{} m:
      {==}
    case Con{x, r} 0n:
      {==}
    case Con{+x, +r} 1n+(+m):
      Shared.Bool.and_both(List.contains(~A, ~same, x <> r, x), Shared.List.within(~A, ~same, List.take(&2, A, r, m), x <> r))(
        List.contains_head(~A, ~same, ~laws, x, r)
      )(
        List.within_cons(~A, ~same, List.take(&2, A, r, m), x, r)(List.take_within(~A, ~same, ~laws, r, m))
      )

# the first majority of xs is within xs
def List.lead_within(
  ~A: Data,
  ~same: A -> A -> Bool,
  ~laws: Shared.Eq.Laws(A, same),
  +xs: List<&2, A>
) -> {Shared.List.within(~A, ~same, List.lead(A, xs), xs) == True{}: Bool}:
  List.take_within(~A, ~same, ~laws, xs, 1n+Nat.half(List.length(&2, A, xs)))

# the first majority of a list that is not empty is more than half of it
def List.lead_most(
  -A: Data,
  xs: List<&2, A>
) -> {List.is_empty(&2, A, xs) == False{}: Bool} -> {Nat.most(List.length(&2, A, xs), List.length(&2, A, List.lead(A, xs))) == True{}: Bool}:
  match xs:
    case Nil{}:
      h => Empty.absurd({Nat.most(0n, 0n) == True{}: Bool}, Shared.Bool.true_ne_false(h))
    case Con{+x, +r}:
      h => (
        %Equal.sym(Nat, List.length(&2, A, List.take(&2, A, r, Nat.half(1n+List.length(&2, A, r)))), Nat.half(1n+List.length(&2, A, r)), List.length_take(A, r, Nat.half(1n+List.length(&2, A, r)))(Nat.half_lt(List.length(&2, A, r)))): {Nat.most(1n+List.length(&2, A, r), 1n+_) == True{}: Bool}
        Nat.half_most(1n+List.length(&2, A, r))
      )

# p holds of each member of a list that it holds of
def List.holds_in(
  ~A: Data,
  ~V: Data,
  ~p: V -> A -> Bool,
  ~same: A -> A -> Bool,
  ~laws: Shared.Eq.Laws(A, same),
  xs: List<&2, A>,
  +g: V,
  +x: A
) -> {Shared.List.holds(~A, ~V, ~p, xs, g) == True{}: Bool} -> {List.contains(~A, ~same, xs, x) == True{}: Bool} -> {p(g)(x) == True{}: Bool}:
  match xs:
    case Nil{}:
      hh => hin => Empty.absurd({p(g)(x) == True{}: Bool}, Shared.Bool.false_ne_true(hin))
    case Con{+h, +r}:
      +hh => hin => List.contains_cons_by(
        ~A,
        ~same,
        ~laws,
        {p(g)(x) == True{}: Bool},
        h,
        r,
        x,
        hin,
        exh => (
          %exh: {p(g)(_) == True{}: Bool}
          Shared.List.all.if_hit(p(g)(h), u => Shared.List.holds(~A, ~V, ~p, r, g))(hh)
        ),
        c => List.holds_in(~A, ~V, ~p, ~same, ~laws, r, g, x)(Shared.List.all.if_rest(p(g)(h), u => Shared.List.holds(~A, ~V, ~p, r, g))(hh))(c)
      )

# a list that p holds of some element of has a member that p holds of
def List.some_in(
  ~A: Data,
  ~V: Data,
  ~p: V -> A -> Bool,
  ~same: A -> A -> Bool,
  ~laws: Shared.Eq.Laws(A, same),
  xs: List<&2, A>,
  +g: V
) -> {Shared.List.some(~A, ~V, ~p, xs, g) == True{}: Bool} -> Exists(A, x => {List.contains(~A, ~same, xs, x) == True{}: Bool} & {p(g)(x) == True{}: Bool}):
  match xs:
    case Nil{}:
      h => Empty.absurd(Exists(A, x => {List.contains(~A, ~same, [], x) == True{}: Bool} & {p(g)(x) == True{}: Bool}), Shared.Bool.false_ne_true(h))
    case Con{+z, +r}:
      Bool.by(
        c => {List.any.if(u => Shared.List.some(~A, ~V, ~p, r, g), c) == True{}: Bool} -> Exists(A, x => {List.contains(~A, ~same, z <> r, x) == True{}: Bool} & {p(g)(x) == True{}: Bool}),
        p(g)(z),
        et => h => (z, (List.contains_head(~A, ~same, ~laws, z, r), et)),
        ef => h => List.exists_cons(~A, ~same, y => {p(g)(y) == True{}: Bool}, z, r, List.some_in(~A, ~V, ~p, ~same, ~laws, r, g)(h))
      )

# p holds of some element of a list when it holds of a member of it
def List.in_some(
  ~A: Data,
  ~V: Data,
  ~p: V -> A -> Bool,
  ~same: A -> A -> Bool,
  ~laws: Shared.Eq.Laws(A, same),
  xs: List<&2, A>,
  +g: V,
  +x: A
) -> {List.contains(~A, ~same, xs, x) == True{}: Bool} -> {p(g)(x) == True{}: Bool} -> {Shared.List.some(~A, ~V, ~p, xs, g) == True{}: Bool}:
  Shared.List.some_member(~A, ~V, ~same, ~p, ~laws, xs, x, g)


# The greatest
# ------------

# the first of b and the elements of xs with the greatest f
def List.top.go(~A: Data, ~f: A -> Nat, xs: List<&2, A>, +b: A) -> A:
  match xs:
    case Nil{}:
      b
    case Con{+y, s}:
      List.top.go(~A, ~f, s, Bool.pick(A, Nat.is_lt(f(b), f(y)), y, b))

# the first element of xs with the greatest f; nothing for []
def List.top(~A: Data, ~f: A -> Nat, xs: List<&2, A>) -> Maybe<&2, A>:
  match xs:
    case Nil{}:
      None{}
    case Con{x, r}:
      Some{List.top.go(~A, ~f, r, x)}

# what List.top.go gives is no less than b
def List.top.go_best(
  ~A: Data,
  ~f: A -> Nat,
  xs: List<&2, A>,
  +b: A
) -> {Nat.is_le(f(b), f(List.top.go(~A, ~f, xs, b))) == True{}: Bool}:
  match xs:
    case Nil{}:
      Shared.Nat.le_refl(f(b))
    case Con{+y, +s}:
      Bool.by(
        c => {Nat.is_le(f(b), f(List.top.go(~A, ~f, s, Bool.pick(A, c, y, b)))) == True{}: Bool},
        Nat.is_lt(f(b), f(y)),
        et => Shared.Nat.le_trans(f(b), f(y), f(List.top.go(~A, ~f, s, y)))(Shared.Nat.lt_weak(f(b), f(y))(et))(List.top.go_best(~A, ~f, s, y)),
        ef => List.top.go_best(~A, ~f, s, b)
      )

# what List.top.go gives is no less than a member of xs
def List.top.go_ge(
  ~A: Data,
  ~f: A -> Nat,
  ~same: A -> A -> Bool,
  ~laws: Shared.Eq.Laws(A, same),
  xs: List<&2, A>,
  +b: A,
  +x: A
) -> {List.contains(~A, ~same, xs, x) == True{}: Bool} -> {Nat.is_le(f(x), f(List.top.go(~A, ~f, xs, b))) == True{}: Bool}:
  match xs:
    case Nil{}:
      hin => Empty.absurd({Nat.is_le(f(x), f(b)) == True{}: Bool}, Shared.Bool.false_ne_true(hin))
    case Con{+y, +s}:
      hin => List.contains_cons_by(
        ~A,
        ~same,
        ~laws,
        {Nat.is_le(f(x), f(List.top.go(~A, ~f, s, Bool.pick(A, Nat.is_lt(f(b), f(y)), y, b)))) == True{}: Bool},
        y,
        s,
        x,
        hin,
        e => (
          %e: {Nat.is_le(f(_), f(List.top.go(~A, ~f, s, Bool.pick(A, Nat.is_lt(f(b), f(y)), y, b)))) == True{}: Bool}
          Bool.by(
            c => {Nat.is_le(f(y), f(List.top.go(~A, ~f, s, Bool.pick(A, c, y, b)))) == True{}: Bool},
            Nat.is_lt(f(b), f(y)),
            et => List.top.go_best(~A, ~f, s, y),
            ef => Shared.Nat.le_trans(f(y), f(b), f(List.top.go(~A, ~f, s, b)))(Shared.Nat.nlt_le(f(b), f(y))(ef))(List.top.go_best(~A, ~f, s, b))
          )
        ),
        c => List.top.go_ge(~A, ~f, ~same, ~laws, s, Bool.pick(A, Nat.is_lt(f(b), f(y)), y, b), x)(c)
      )

# what List.top.go gives is b or a member of xs
def List.top.go_in(
  ~A: Data,
  ~f: A -> Nat,
  ~same: A -> A -> Bool,
  ~laws: Shared.Eq.Laws(A, same),
  xs: List<&2, A>,
  +b: A
) -> {List.contains(~A, ~same, b <> xs, List.top.go(~A, ~f, xs, b)) == True{}: Bool}:
  match xs:
    case Nil{}:
      List.contains_head(~A, ~same, ~laws, b, [])
    case Con{+y, +s}:
      Bool.by(
        c => {List.contains(~A, ~same, b <> y <> s, List.top.go(~A, ~f, s, Bool.pick(A, c, y, b))) == True{}: Bool},
        Nat.is_lt(f(b), f(y)),
        et => Shared.List.contains_cons(~A, ~same, b, y <> s, List.top.go(~A, ~f, s, y))(List.top.go_in(~A, ~f, ~same, ~laws, s, y)),
        ef => List.contains_skip(~A, ~same, b, y, s, List.top.go(~A, ~f, s, b))(List.top.go_in(~A, ~f, ~same, ~laws, s, b))
      )

# what List.top gives is a member of xs
def List.top_in(
  ~A: Data,
  ~f: A -> Nat,
  ~same: A -> A -> Bool,
  ~laws: Shared.Eq.Laws(A, same),
  xs: List<&2, A>,
  -x: A
) -> {List.top(~A, ~f, xs) == Some{x}: Maybe<&2, A>} -> {List.contains(~A, ~same, xs, x) == True{}: Bool}:
  match xs:
    case Nil{}:
      e => Empty.absurd({False{} == True{}: Bool}, Shared.Maybe.none_ne_some(A, x, e))
    case Con{+h, +t}:
      e => (
        %Shared.Maybe.some_inj(A, List.top.go(~A, ~f, t, h), x, e): {List.contains(~A, ~same, h <> t, _) == True{}: Bool}
        List.top.go_in(~A, ~f, ~same, ~laws, t, h)
      )

# what List.top gives is no less than a member of xs
def List.top_ge(
  ~A: Data,
  ~f: A -> Nat,
  ~same: A -> A -> Bool,
  ~laws: Shared.Eq.Laws(A, same),
  xs: List<&2, A>,
  -x: A,
  +y: A
) -> {List.top(~A, ~f, xs) == Some{x}: Maybe<&2, A>} -> {List.contains(~A, ~same, xs, y) == True{}: Bool} -> {Nat.is_le(f(y), f(x)) == True{}: Bool}:
  match xs:
    case Nil{}:
      e => hin => Empty.absurd({Nat.is_le(f(y), f(x)) == True{}: Bool}, Shared.Bool.false_ne_true(hin))
    case Con{+h, +t}:
      e => hin => (
        %Shared.Maybe.some_inj(A, List.top.go(~A, ~f, t, h), x, e): {Nat.is_le(f(y), f(_)) == True{}: Bool}
        List.contains_cons_by(
          ~A,
          ~same,
          ~laws,
          {Nat.is_le(f(y), f(List.top.go(~A, ~f, t, h))) == True{}: Bool},
          h,
          t,
          y,
          hin,
          ey => (
            %ey: {Nat.is_le(f(_), f(List.top.go(~A, ~f, t, h))) == True{}: Bool}
            List.top.go_best(~A, ~f, t, h)
          ),
          c => List.top.go_ge(~A, ~f, ~same, ~laws, t, h, y)(c)
        )
      )

# List.top gives x, when x is the one member of xs with the greatest f
def List.top_one(
  ~A: Data,
  ~f: A -> Nat,
  ~same: A -> A -> Bool,
  ~laws: Shared.Eq.Laws(A, same),
  xs: List<&2, A>,
  +x: A
) -> {List.contains(~A, ~same, xs, x) == True{}: Bool} -> (@y: A -> {List.contains(~A, ~same, xs, y) == True{}: Bool} -> ({y == x: A} -> Empty) -> {Nat.is_lt(f(y), f(x)) == True{}: Bool}) -> {List.top(~A, ~f, xs) == Some{x}: Maybe<&2, A>}:
  match xs:
    case Nil{}:
      hin => hyp => Empty.absurd({None{} == Some{x}: Maybe<&2, A>}, Shared.Bool.false_ne_true(hin))
    case Con{+h, +t}:
      hin => hyp => Bool.by(
        c => {Some{List.top.go(~A, ~f, t, h)} == Some{x}: Maybe<&2, A>},
        same(List.top.go(~A, ~f, t, h), x),
        es => Equal.cong(A, Maybe<&2, A>, z => Some{z}, List.top.go(~A, ~f, t, h), x, Shared.Eq.sound(~A, ~same, laws, List.top.go(~A, ~f, t, h), x)(es)),
        es => Bool.clash(
          {Some{List.top.go(~A, ~f, t, h)} == Some{x}: Maybe<&2, A>},
          Nat.is_lt(f(List.top.go(~A, ~f, t, h)), f(List.top.go(~A, ~f, t, h))),
          Shared.Nat.lt_irrefl(f(List.top.go(~A, ~f, t, h))),
          Shared.Nat.lt_le(f(List.top.go(~A, ~f, t, h)), f(x), f(List.top.go(~A, ~f, t, h)))(
            hyp(List.top.go(~A, ~f, t, h))(List.top.go_in(~A, ~f, ~same, ~laws, t, h))(
              ez => Bool.clash(
                Empty,
                same(List.top.go(~A, ~f, t, h), x),
                es,
                (
                  %ez: {same(List.top.go(~A, ~f, t, h), _) == True{}: Bool}
                  Shared.Eq.refl(~A, ~same, laws, List.top.go(~A, ~f, t, h))
                )
              )
            )
          )(List.top_ge(~A, ~f, ~same, ~laws, h <> t, List.top.go(~A, ~f, t, h), x)({==})(hin))
        )
      )

# List.top gives an element of a list that has a member
def List.top_some(
  ~A: Data,
  ~f: A -> Nat,
  ~same: A -> A -> Bool,
  ~laws: Shared.Eq.Laws(A, same),
  xs: List<&2, A>,
  -y: A
) -> {List.contains(~A, ~same, xs, y) == True{}: Bool} -> Exists(A, x => {List.top(~A, ~f, xs) == Some{x}: Maybe<&2, A>}):
  match xs:
    case Nil{}:
      hin => Empty.absurd(Exists(A, x => {None{} == Some{x}: Maybe<&2, A>}), Shared.Bool.false_ne_true(hin))
    case Con{+h, +t}:
      hin => (List.top.go(~A, ~f, t, h), {==})

# a number is at most the greater of it and another
def Nat.le_max_left(a: Nat, b: Nat) -> {Nat.is_le(a, Nat.max(a, b)) == True{}: Bool}:
  match a b:
    case 0n c:
      Shared.Nat.le_zero(c)
    case 1n+p 0n:
      Shared.Nat.le_refl(p)
    case 1n+p 1n+q:
      Nat.le_max_left(p, q)

# a number is at most the greater of another and it
def Nat.le_max_right(a: Nat, b: Nat) -> {Nat.is_le(b, Nat.max(a, b)) == True{}: Bool}:
  match a b:
    case 0n c:
      Shared.Nat.le_refl(c)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      Nat.le_max_right(p, q)

# the greatest f of the elements of xs; 0 for []
def List.peak(~A: Data, ~f: A -> Nat, xs: List<&2, A>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{x, r}:
      Nat.max(f(x), List.peak(~A, ~f, r))

# the f of a member of xs is at most the greatest
def List.peak_ge(
  ~A: Data,
  ~f: A -> Nat,
  ~same: A -> A -> Bool,
  ~laws: Shared.Eq.Laws(A, same),
  xs: List<&2, A>,
  +y: A
) -> {List.contains(~A, ~same, xs, y) == True{}: Bool} -> {Nat.is_le(f(y), List.peak(~A, ~f, xs)) == True{}: Bool}:
  match xs:
    case Nil{}:
      hin => Empty.absurd({Nat.is_le(f(y), 0n) == True{}: Bool}, Shared.Bool.false_ne_true(hin))
    case Con{+h, +t}:
      hin => List.contains_cons_by(
        ~A,
        ~same,
        ~laws,
        {Nat.is_le(f(y), Nat.max(f(h), List.peak(~A, ~f, t))) == True{}: Bool},
        h,
        t,
        y,
        hin,
        e => (
          %e: {Nat.is_le(f(_), Nat.max(f(h), List.peak(~A, ~f, t))) == True{}: Bool}
          Nat.le_max_left(f(h), List.peak(~A, ~f, t))
        ),
        c => Shared.Nat.le_trans(f(y), List.peak(~A, ~f, t), Nat.max(f(h), List.peak(~A, ~f, t)))(List.peak_ge(~A, ~f, ~same, ~laws, t, y)(c))(Nat.le_max_right(f(h), List.peak(~A, ~f, t)))
      )


# Empty lists and kept values
# ---------------------------

# a list with no member is empty
def List.nil_none(
  ~A: Data,
  ~same: A -> A -> Bool,
  ~laws: Shared.Eq.Laws(A, same),
  xs: List<&2, A>
) -> (@x: A -> {List.contains(~A, ~same, xs, x) == True{}: Bool} -> Empty) -> {xs == []: List<&2, A>}:
  match xs:
    case Nil{}:
      no => {==}
    case Con{+h, +t}:
      no => Empty.absurd({h <> t == []: List<&2, A>}, no(h)(List.contains_head(~A, ~same, ~laws, h, t)))

# List.in_not_nil, as the False = True that it comes to
def List.in_not_nil.at(
  ~A: Data,
  ~same: A -> A -> Bool,
  -xs: List<&2, A>,
  -x: A,
  hin: {List.contains(~A, ~same, xs, x) == True{}: Bool},
  e: {xs == []: List<&2, A>}
) -> {False{} == True{}: Bool}:
  %e: {List.contains(~A, ~same, _, x) == True{}: Bool}
  hin

# a list with a member is not empty
def List.in_not_nil(
  ~A: Data,
  ~same: A -> A -> Bool,
  -xs: List<&2, A>,
  -x: A
) -> {List.contains(~A, ~same, xs, x) == True{}: Bool} -> {xs == []: List<&2, A>} -> Empty:
  hin => e => Shared.Bool.false_ne_true(List.in_not_nil.at(~A, ~same, xs, x, hin, e))

# a member of r is a member of r with what m holds before it
def List.contains_maybe_cons(
  ~A: Data,
  ~same: A -> A -> Bool,
  m: Maybe<&2, A>,
  r: List<&2, A>,
  y: A
) -> {List.contains(~A, ~same, r, y) == True{}: Bool} -> {List.contains(~A, ~same, Shared.Maybe.cons(A, m, r), y) == True{}: Bool}:
  match m:
    case None{}:
      h => h
    case Some{z}:
      Shared.List.contains_cons(~A, ~same, z, r, y)

# what f gives for a member of xs is a member of the values that f gives for xs
def List.contains_filter_map(
  ~A: Data,
  ~B: Data,
  ~f: A -> Maybe<&2, B>,
  ~sameA: A -> A -> Bool,
  ~sameB: B -> B -> Bool,
  ~lawsA: Shared.Eq.Laws(A, sameA),
  ~lawsB: Shared.Eq.Laws(B, sameB),
  xs: List<&2, A>,
  +x: A,
  +y: B
) -> {List.contains(~A, ~sameA, xs, x) == True{}: Bool} -> {f(x) == Some{y}: Maybe<&2, B>} -> {List.contains(~B, ~sameB, Shared.List.filter_map(~A, ~B, ~f, xs), y) == True{}: Bool}:
  match xs:
    case Nil{}:
      hin => e => Empty.absurd({False{} == True{}: Bool}, Shared.Bool.false_ne_true(hin))
    case Con{+h, +t}:
      hin => +e => List.contains_cons_by(
        ~A,
        ~sameA,
        ~lawsA,
        {List.contains(~B, ~sameB, Shared.Maybe.cons(B, f(h), Shared.List.filter_map(~A, ~B, ~f, t)), y) == True{}: Bool},
        h,
        t,
        x,
        hin,
        exh => (
          %Equal.sym(Maybe<&2, B>, f(h), Some{y}, Equal.trans(Maybe<&2, B>, f(h), f(x), Some{y}, Equal.cong(A, Maybe<&2, B>, z => f(z), h, x, exh), e)): {List.contains(~B, ~sameB, Shared.Maybe.cons(B, _, Shared.List.filter_map(~A, ~B, ~f, t)), y) == True{}: Bool}
          List.contains_head(~B, ~sameB, ~lawsB, y, Shared.List.filter_map(~A, ~B, ~f, t))
        ),
        c => List.contains_maybe_cons(~B, ~sameB, f(h), Shared.List.filter_map(~A, ~B, ~f, t), y)(List.contains_filter_map(~A, ~B, ~f, ~sameA, ~sameB, ~lawsA, ~lawsB, t, x, y)(c)(e))
      )

# a member of the values that f gives for xs is what f gives for a member of xs
def List.contains_filter_map_inv(
  ~A: Data,
  ~B: Data,
  ~f: A -> Maybe<&2, B>,
  ~sameA: A -> A -> Bool,
  ~sameB: B -> B -> Bool,
  ~lawsA: Shared.Eq.Laws(A, sameA),
  xs: List<&2, A>,
  +y: B
) -> {List.contains(~B, ~sameB, Shared.List.filter_map(~A, ~B, ~f, xs), y) == True{}: Bool} -> Exists(A, x => {List.contains(~A, ~sameA, xs, x) == True{}: Bool} & Exists(B, y2 => {f(x) == Some{y2}: Maybe<&2, B>} & {sameB(y2, y) == True{}: Bool})):
  match xs:
    case Nil{}:
      hin => Empty.absurd(Exists(A, x => {List.contains(~A, ~sameA, [], x) == True{}: Bool} & Exists(B, y2 => {f(x) == Some{y2}: Maybe<&2, B>} & {sameB(y2, y) == True{}: Bool})), Shared.Bool.false_ne_true(hin))
    case Con{+h, +t}:
      Maybe.by(
        B,
        m => {List.contains(~B, ~sameB, Shared.Maybe.cons(B, m, Shared.List.filter_map(~A, ~B, ~f, t)), y) == True{}: Bool} -> Exists(A, x => {List.contains(~A, ~sameA, h <> t, x) == True{}: Bool} & Exists(B, y2 => {f(x) == Some{y2}: Maybe<&2, B>} & {sameB(y2, y) == True{}: Bool})),
        f(h),
        en => c => List.exists_cons(~A, ~sameA, x => Exists(B, y2 => {f(x) == Some{y2}: Maybe<&2, B>} & {sameB(y2, y) == True{}: Bool}), h, t, List.contains_filter_map_inv(~A, ~B, ~f, ~sameA, ~sameB, ~lawsA, t, y)(c)),
        +z => ez => Bool.by(
          s => {List.any.if(u => List.contains(~B, ~sameB, Shared.List.filter_map(~A, ~B, ~f, t), y), s) == True{}: Bool} -> Exists(A, x => {List.contains(~A, ~sameA, h <> t, x) == True{}: Bool} & Exists(B, y2 => {f(x) == Some{y2}: Maybe<&2, B>} & {sameB(y2, y) == True{}: Bool})),
          sameB(z, y),
          es => c => (h, (List.contains_head(~A, ~sameA, ~lawsA, h, t), (z, (ez, es)))),
          es => c => List.exists_cons(~A, ~sameA, x => Exists(B, y2 => {f(x) == Some{y2}: Maybe<&2, B>} & {sameB(y2, y) == True{}: Bool}), h, t, List.contains_filter_map_inv(~A, ~B, ~f, ~sameA, ~sameB, ~lawsA, t, y)(c))
        )
      )

