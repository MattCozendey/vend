import Base
import ./shared/keyset.bend as KeySets
import ./shared/shared/shared.bend as Shared
import ./shared/shared/trie.bend as Tries

# Regular expressions
# -------------------
# An expression over symbols of A. An atom t of T accepts the symbol c when
# hit(t)(c). Re.matches is the meaning: it takes the derivative of the
# expression by each symbol of the word (Re.step), and asks at the end if what
# is left matches the empty word.

# Void: no word. Eps: only the empty word. One: one symbol that the atom
# accepts. All: every word. Star: r, any number of times. Cat: a, then b.
# Alt: a or b.
type Re<-T: Data> is Data:
  Void{}
  Eps{}
  One{t: T}
  All{}
  Star{r: Re<T>}
  Cat{a: Re<T>, b: Re<T>}
  Alt{a: Re<T>, b: Re<T>}

# Eps for True, Void for False
def Re.of_bool(-T: Data, b: Bool) -> Re<T>:
  match b:
    case False{}:
      Void{}
    case True{}:
      Eps{}

# r matches the empty word
def Re.is_nullable(-T: Data, r: Re<T>) -> Bool:
  match r:
    case Void{}:
      False{}
    case Eps{}:
      True{}
    case One{t}:
      False{}
    case All{}:
      True{}
    case Star{x}:
      True{}
    case Cat{a, b}:
      List.all.if(u => Re.is_nullable(T, b), Re.is_nullable(T, a))
    case Alt{a, b}:
      List.any.if(u => Re.is_nullable(T, b), Re.is_nullable(T, a))

# what r must still match after it reads c
# bend-lint: expect-begin bend-lint-rules/performance/missed_fork@hint -- an expression is a few nodes, where a fork costs more than it saves
def Re.step(~A: Data, ~T: Data, ~hit: T -> A -> Bool, r: Re<T>, +c: A) -> Re<T>:
  match r:
    case Void{}:
      Void{}
    case Eps{}:
      Void{}
    case One{t}:
      Re.of_bool(T, hit(t)(c))
    case All{}:
      All{}
    case Star{+x}:
      Cat{Re.step(~A, ~T, ~hit, x, c), Star{x}}
    case Cat{+a, +b}:
      Alt{
        Cat{Re.step(~A, ~T, ~hit, a, c), b},
        Cat{Re.of_bool(T, Re.is_nullable(T, a)), Re.step(~A, ~T, ~hit, b, c)}
      }
    case Alt{a, b}:
      Alt{Re.step(~A, ~T, ~hit, a, c), Re.step(~A, ~T, ~hit, b, c)}
# bend-lint: expect-end bend-lint-rules/performance/missed_fork@hint

# r matches all of w
def Re.matches(~A: Data, ~T: Data, ~hit: T -> A -> Bool, w: List<&2, A>, r: Re<T>) -> Bool:
  match w:
    case Nil{}:
      Re.is_nullable(T, r)
    case Con{c, t}:
      Re.matches(~A, ~T, ~hit, t, Re.step(~A, ~T, ~hit, r, c))

# Equality and keys
# -----------------

# a and b are the same expression, when same compares their atoms
def Re.is_eq(~T: Data, ~same: T -> T -> Bool, a: Re<T>, b: Re<T>) -> Bool:
  match a b:
    case Void{} Void{}:
      True{}
    case Eps{} Eps{}:
      True{}
    case One{x} One{y}:
      same(x, y)
    case All{} All{}:
      True{}
    case Star{x} Star{y}:
      Re.is_eq(~T, ~same, x, y)
    case Cat{a1, b1} Cat{a2, b2}:
      List.all.if(u => Re.is_eq(~T, ~same, b1, b2), Re.is_eq(~T, ~same, a1, a2))
    case Alt{a1, b1} Alt{a2, b2}:
      List.all.if(u => Re.is_eq(~T, ~same, b1, b2), Re.is_eq(~T, ~same, a1, a2))
    case _ _:
      False{}

# the key of r, then rest: three bits for the shape of r, then its parts
def Re.key(~T: Data, ~key: T -> List<&2, Bool>, r: Re<T>, rest: List<&2, Bool>) -> List<&2, Bool>:
  match r:
    case Void{}:
      False{} <> False{} <> False{} <> rest
    case Eps{}:
      False{} <> False{} <> True{} <> rest
    case One{t}:
      False{} <> True{} <> False{} <> List.append(&2, Bool, key(t), rest)
    case All{}:
      False{} <> True{} <> True{} <> rest
    case Star{x}:
      True{} <> False{} <> False{} <> Re.key(~T, ~key, x, rest)
    case Cat{a, b}:
      True{} <> False{} <> True{} <> Re.key(~T, ~key, a, Re.key(~T, ~key, b, rest))
    case Alt{a, b}:
      True{} <> True{} <> False{} <> Re.key(~T, ~key, a, Re.key(~T, ~key, b, rest))

# Partial derivatives
# -------------------
# Re.step puts what is left of an expression in one expression that grows
# with each symbol. A Seq is expressions one after another, and a list of
# Seqs matches what any of them matches. After a symbol, a Seq becomes a list
# of Seqs whose parts are parts of the first expression, so the lists stay
# small, and a search over them meets a finite number.

# the expression of the parts of s, one after another
def Seq.re(-T: Data, s: List<&2, Re<T>>) -> Re<T>:
  match s:
    case Nil{}:
      Eps{}
    case Con{h, t}:
      Cat{h, Seq.re(T, t)}

# the parts of s, one after another, match all of w
def Seq.matches(
  ~A: Data,
  ~T: Data,
  ~hit: T -> A -> Bool,
  w: List<&2, A>,
  s: List<&2, Re<T>>
) -> Bool:
  Re.matches(~A, ~T, ~hit, w, Seq.re(T, s))

# some Seq of xs matches all of w
def Seqs.matches(
  ~A: Data,
  ~T: Data,
  ~hit: T -> A -> Bool,
  xs: List<&2, List<&2, Re<T>>>,
  w: List<&2, A>
) -> Bool:
  Shared.List.some(~List<&2, Re<T>>, ~List<&2, A>, ~Seq.matches(~A, ~T, ~hit), xs, w)

# a and b are the same Seq
def Seq.is_eq(~T: Data, ~same: T -> T -> Bool, a: List<&2, Re<T>>, b: List<&2, Re<T>>) -> Bool:
  Shared.List.is_eq(~Re<T>, ~Re.is_eq(~T, ~same), a, b)

# the key of s, then rest: True before each part, False after the last
def Seq.key.go(
  ~T: Data,
  ~key: T -> List<&2, Bool>,
  s: List<&2, Re<T>>,
  rest: List<&2, Bool>
) -> List<&2, Bool>:
  match s:
    case Nil{}:
      False{} <> rest
    case Con{h, t}:
      True{} <> Re.key(~T, ~key, h, Seq.key.go(~T, ~key, t, rest))

# the key of s
def Seq.key(~T: Data, ~key: T -> List<&2, Bool>, s: List<&2, Re<T>>) -> List<&2, Bool>:
  Seq.key.go(~T, ~key, s, [])

# acc, with r in front when hit
def Seq.step.keep(
  -T: Data,
  hit: Bool,
  r: List<&2, Re<T>>,
  acc: List<&2, List<&2, Re<T>>>
) -> List<&2, List<&2, Re<T>>>:
  match hit:
    case False{}:
      acc
    case True{}:
      r <> acc

# the Seqs that h then r becomes when h reads c, in front of acc
def Seq.step.part(
  ~A: Data,
  ~T: Data,
  ~hit: T -> A -> Bool,
  h: Re<T>,
  +r: List<&2, Re<T>>,
  +c: A,
  +acc: List<&2, List<&2, Re<T>>>
) -> List<&2, List<&2, Re<T>>>:
  match h:
    case Void{}:
      acc
    case Eps{}:
      acc
    case One{t}:
      Seq.step.keep(T, hit(t)(c), r, acc)
    case All{}:
      (All{} <> r) <> acc
    case Star{+x}:
      Seq.step.part(~A, ~T, ~hit, x, Star{x} <> r, c, acc)
    case Cat{+a, +b}:
      Seq.step.part(
        ~A,
        ~T,
        ~hit,
        a,
        b <> r,
        c,
        Shared.Bool.when(
          List<&2, List<&2, Re<T>>>,
          Re.is_nullable(T, a),
          u => Seq.step.part(~A, ~T, ~hit, b, r, c, acc),
          u => acc
        )
      )
    case Alt{a, b}:
      Seq.step.part(~A, ~T, ~hit, a, r, c, Seq.step.part(~A, ~T, ~hit, b, r, c, acc))

# the Seqs that s becomes after c, in front of acc
def Seq.step(
  ~A: Data,
  ~T: Data,
  ~hit: T -> A -> Bool,
  s: List<&2, Re<T>>,
  +c: A,
  +acc: List<&2, List<&2, Re<T>>>
) -> List<&2, List<&2, Re<T>>>:
  match s:
    case Nil{}:
      acc
    case Con{+h, +t}:
      Seq.step.part(
        ~A,
        ~T,
        ~hit,
        h,
        t,
        c,
        Shared.Bool.when(
          List<&2, List<&2, Re<T>>>,
          Re.is_nullable(T, h),
          u => Seq.step(~A, ~T, ~hit, t, c, acc),
          u => acc
        )
      )

# the Seqs that each Seq of xs becomes after c, repeats included
def Seqs.step.all(
  ~A: Data,
  ~T: Data,
  ~hit: T -> A -> Bool,
  xs: List<&2, List<&2, Re<T>>>,
  +c: A
) -> List<&2, List<&2, Re<T>>>:
  match xs:
    case Nil{}:
      []
    case Con{x, r}:
      Seq.step(~A, ~T, ~hit, x, c, Seqs.step.all(~A, ~T, ~hit, r, c))

# the Seqs that xs becomes after c, each once: same compares atoms, and key
# gives the key of one
def Seqs.step(
  ~A: Data,
  ~T: Data,
  ~hit: T -> A -> Bool,
  ~same: T -> T -> Bool,
  ~key: T -> List<&2, Bool>,
  xs: List<&2, List<&2, Re<T>>>,
  c: A
) -> List<&2, List<&2, Re<T>>>:
  KeySets.KeySet.unique(
    ~List<&2, Re<T>>,
    ~Seq.is_eq(~T, ~same),
    ~Seq.key(~T, ~key),
    Seqs.step.all(~A, ~T, ~hit, xs, c),
    Tries.Trie.new(List<&2, Re<T>>)
  )

# the Seqs that xs becomes after the word w
def Seqs.walk(
  ~A: Data,
  ~T: Data,
  ~hit: T -> A -> Bool,
  ~same: T -> T -> Bool,
  ~key: T -> List<&2, Bool>,
  w: List<&2, A>,
  xs: List<&2, List<&2, Re<T>>>
) -> List<&2, List<&2, Re<T>>>:
  match w:
    case Nil{}:
      xs
    case Con{c, t}:
      Seqs.walk(~A, ~T, ~hit, ~same, ~key, t, Seqs.step(~A, ~T, ~hit, ~same, ~key, xs, c))

# r matches all of w: Re.matches, at a cost that does not grow with each
# symbol, as the Seqs stay small
def Re.accepts(
  ~A: Data,
  ~T: Data,
  ~hit: T -> A -> Bool,
  ~same: T -> T -> Bool,
  ~key: T -> List<&2, Bool>,
  w: List<&2, A>,
  r: Re<T>
) -> Bool:
  Seqs.matches(~A, ~T, ~hit, Seqs.walk(~A, ~T, ~hit, ~same, ~key, w, [[r]]), [])

# Atoms
# -----

# p holds of g and each atom of r
def Re.holds(~T: Data, ~V: Data, ~p: V -> T -> Bool, +g: V, r: Re<T>) -> Bool:
  match r:
    case Void{}:
      True{}
    case Eps{}:
      True{}
    case One{t}:
      p(g)(t)
    case All{}:
      True{}
    case Star{x}:
      Re.holds(~T, ~V, ~p, g, x)
    case Cat{a, b}:
      List.all.if(u => Re.holds(~T, ~V, ~p, g, b), Re.holds(~T, ~V, ~p, g, a))
    case Alt{a, b}:
      List.all.if(u => Re.holds(~T, ~V, ~p, g, b), Re.holds(~T, ~V, ~p, g, a))

# p holds of g and each atom of s
def Seq.holds(~T: Data, ~V: Data, ~p: V -> T -> Bool, g: V, s: List<&2, Re<T>>) -> Bool:
  Shared.List.holds(~Re<T>, ~V, ~(e => r => Re.holds(~T, ~V, ~p, e, r)), s, g)

# p holds of g and each atom of xs
def Seqs.holds(~T: Data, ~V: Data, ~p: V -> T -> Bool, xs: List<&2, List<&2, Re<T>>>, g: V) -> Bool:
  Shared.List.holds(~List<&2, Re<T>>, ~V, ~Seq.holds(~T, ~V, ~p), xs, g)

# Laws of matching
# ----------------
# Each lemma states the simpler side first, so a rewrite with it turns an
# expression into its simpler meaning.

# Cat matches the empty word when both sides do
def Re.cat_nullable(
  -T: Data,
  a: Re<T>,
  b: Re<T>
) -> {Bool.and(Re.is_nullable(T, a), Re.is_nullable(T, b)) == Re.is_nullable(T, Cat{a, b}): Bool}:
  %Shared.List.all.if_and(
    Re.is_nullable(T, a),
    u => Re.is_nullable(T, b)
  ): {_ == Re.is_nullable(T, Cat{a, b}): Bool}
  {==}

# Alt matches the empty word when a side does
def Re.alt_nullable(
  -T: Data,
  a: Re<T>,
  b: Re<T>
) -> {Bool.or(Re.is_nullable(T, a), Re.is_nullable(T, b)) == Re.is_nullable(T, Alt{a, b}): Bool}:
  %Shared.List.any.if_or(
    Re.is_nullable(T, a),
    u => Re.is_nullable(T, b)
  ): {_ == Re.is_nullable(T, Alt{a, b}): Bool}
  {==}

# Void matches nothing
def Re.void_never(
  ~A: Data,
  ~T: Data,
  ~hit: T -> A -> Bool,
  w: List<&2, A>
) -> {False{} == Re.matches(~A, ~T, ~hit, w, Void{}): Bool}:
  match w:
    case Nil{}:
      {==}
    case Con{c, t}:
      Re.void_never(~A, ~T, ~hit, t)

# Alt matches what either side matches
def Re.alt_or(
  ~A: Data,
  ~T: Data,
  ~hit: T -> A -> Bool,
  w: List<&2, A>,
  a: Re<T>,
  b: Re<T>
) -> {
  Bool.or(
    Re.matches(~A, ~T, ~hit, w, a),
    Re.matches(~A, ~T, ~hit, w, b)
  )
    == Re.matches(~A, ~T, ~hit, w, Alt{a, b}): Bool
}:
  match w:
    case Nil{}:
      Re.alt_nullable(T, a, b)
    case Con{+c, t}:
      Re.alt_or(~A, ~T, ~hit, t, Re.step(~A, ~T, ~hit, a, c), Re.step(~A, ~T, ~hit, b, c))

# Cat after Void matches nothing
def Re.cat_void_l(
  ~A: Data,
  ~T: Data,
  ~hit: T -> A -> Bool,
  w: List<&2, A>,
  +x: Re<T>
) -> {False{} == Re.matches(~A, ~T, ~hit, w, Cat{Void{}, x}): Bool}:
  match w:
    case Nil{}:
      {==}
    case Con{c, +t}:
      +x2 = Re.step(~A, ~T, ~hit, x, c)
      %Re.alt_or(~A, ~T, ~hit, t, Cat{Void{}, x}, Cat{Void{}, x2}): {False{} == _: Bool}
      %Re.cat_void_l(
        ~A,
        ~T,
        ~hit,
        t,
        x
      ): {False{} == Bool.or(_, Re.matches(~A, ~T, ~hit, t, Cat{Void{}, x2})): Bool}
      Re.cat_void_l(~A, ~T, ~hit, t, x2)

# Cat before Void matches nothing
def Re.cat_void_r(
  ~A: Data,
  ~T: Data,
  ~hit: T -> A -> Bool,
  w: List<&2, A>,
  +x: Re<T>
) -> {False{} == Re.matches(~A, ~T, ~hit, w, Cat{x, Void{}}): Bool}:
  match w:
    case Nil{}:
      %Re.cat_nullable(T, x, Void{}): {False{} == _: Bool}
      Equal.sym(
        Bool,
        Bool.and(Re.is_nullable(T, x), False{}),
        False{},
        Shared.Bool.and_false_right(Re.is_nullable(T, x))
      )
    case Con{c, +t}:
      +x2 = Re.step(~A, ~T, ~hit, x, c)
      +n = Re.of_bool(T, Re.is_nullable(T, x))
      %Re.alt_or(~A, ~T, ~hit, t, Cat{x2, Void{}}, Cat{n, Void{}}): {False{} == _: Bool}
      %Re.cat_void_r(
        ~A,
        ~T,
        ~hit,
        t,
        x2
      ): {False{} == Bool.or(_, Re.matches(~A, ~T, ~hit, t, Cat{n, Void{}})): Bool}
      Re.cat_void_r(~A, ~T, ~hit, t, n)

# Cat after Eps matches what its right side matches
def Re.cat_eps_l(
  ~A: Data,
  ~T: Data,
  ~hit: T -> A -> Bool,
  w: List<&2, A>,
  +x: Re<T>
) -> {Re.matches(~A, ~T, ~hit, w, x) == Re.matches(~A, ~T, ~hit, w, Cat{Eps{}, x}): Bool}:
  match w:
    case Nil{}:
      {==}
    case Con{c, +t}:
      +x2 = Re.step(~A, ~T, ~hit, x, c)
      %Re.alt_or(
        ~A,
        ~T,
        ~hit,
        t,
        Cat{Void{}, x},
        Cat{Eps{}, x2}
      ): {Re.matches(~A, ~T, ~hit, t, x2) == _: Bool}
      %Re.cat_void_l(
        ~A,
        ~T,
        ~hit,
        t,
        x
      ): {
        Re.matches(
          ~A,
          ~T,
          ~hit,
          t,
          x2
        )
          == Bool.or(_, Re.matches(~A, ~T, ~hit, t, Cat{Eps{}, x2})): Bool
      }
      Re.cat_eps_l(~A, ~T, ~hit, t, x2)

# Cat before Eps matches what its left side matches
def Re.cat_eps_r(
  ~A: Data,
  ~T: Data,
  ~hit: T -> A -> Bool,
  w: List<&2, A>,
  +x: Re<T>
) -> {Re.matches(~A, ~T, ~hit, w, x) == Re.matches(~A, ~T, ~hit, w, Cat{x, Eps{}}): Bool}:
  match w:
    case Nil{}:
      %Re.cat_nullable(T, x, Eps{}): {Re.is_nullable(T, x) == _: Bool}
      Shared.Bool.and_true(Re.is_nullable(T, x))
    case Con{c, +t}:
      +x2 = Re.step(~A, ~T, ~hit, x, c)
      +n = Re.of_bool(T, Re.is_nullable(T, x))
      %Re.alt_or(
        ~A,
        ~T,
        ~hit,
        t,
        Cat{x2, Eps{}},
        Cat{n, Void{}}
      ): {Re.matches(~A, ~T, ~hit, t, x2) == _: Bool}
      %Re.cat_void_r(
        ~A,
        ~T,
        ~hit,
        t,
        n
      ): {
        Re.matches(
          ~A,
          ~T,
          ~hit,
          t,
          x2
        )
          == Bool.or(Re.matches(~A, ~T, ~hit, t, Cat{x2, Eps{}}), _): Bool
      }
      %Shared.Bool.or_false(
        Re.matches(~A, ~T, ~hit, t, Cat{x2, Eps{}})
      ): {Re.matches(~A, ~T, ~hit, t, x2) == _: Bool}
      Re.cat_eps_r(~A, ~T, ~hit, t, x2)

# Cat after of_bool(b) matches what its right side matches, when b holds
def Re.cat_of_bool(
  ~A: Data,
  ~T: Data,
  ~hit: T -> A -> Bool,
  w: List<&2, A>,
  b: Bool,
  r: Re<T>
) -> {
  Bool.and(
    b,
    Re.matches(~A, ~T, ~hit, w, r)
  )
    == Re.matches(~A, ~T, ~hit, w, Cat{Re.of_bool(T, b), r}): Bool
}:
  match b:
    case False{}:
      Re.cat_void_l(~A, ~T, ~hit, w, r)
    case True{}:
      Re.cat_eps_l(~A, ~T, ~hit, w, r)

# the Bool shape of one step of Re.cat_alt
def Re.cat_alt.bools(
  x: Bool,
  y: Bool,
  a: Bool,
  b: Bool,
  z: Bool
) -> {
  Bool.or(
    Bool.or(x, Bool.and(a, z)),
    Bool.or(y, Bool.and(b, z))
  )
    == Bool.or(Bool.or(x, y), Bool.and(Bool.or(a, b), z)): Bool
}:
  match x y a b z:
    case True{} y1 a1 b1 z1:
      {==}
    case False{} True{} False{} b1 z1:
      {==}
    case False{} True{} True{} b1 False{}:
      {==}
    case False{} True{} True{} b1 True{}:
      {==}
    case False{} False{} False{} b1 z1:
      {==}
    case False{} False{} True{} b1 True{}:
      {==}
    case False{} False{} True{} False{} False{}:
      {==}
    case False{} False{} True{} True{} False{}:
      {==}

# the Bool shape of one step of Re.cat_assoc
def Re.cat_assoc.bools(
  x: Bool,
  y: Bool,
  a: Bool,
  b: Bool,
  z: Bool
) -> {
  Bool.or(
    x,
    Bool.and(a, Bool.or(y, Bool.and(b, z)))
  )
    == Bool.or(Bool.or(x, Bool.and(a, y)), Bool.and(Bool.and(a, b), z)): Bool
}:
  match x y a:
    case True{} y1 a1:
      {==}
    case False{} y1 False{}:
      {==}
    case False{} y1 True{}:
      {==}

# Cat after Alt matches what either Cat matches
def Re.cat_alt(
  ~A: Data,
  ~T: Data,
  ~hit: T -> A -> Bool,
  w: List<&2, A>,
  +a: Re<T>,
  +b: Re<T>,
  +r: Re<T>
) -> {
  Bool.or(
    Re.matches(~A, ~T, ~hit, w, Cat{a, r}),
    Re.matches(~A, ~T, ~hit, w, Cat{b, r})
  )
    == Re.matches(~A, ~T, ~hit, w, Cat{Alt{a, b}, r}): Bool
}:
  match w:
    case Nil{}:
      +na = Re.is_nullable(T, a)
      +nb = Re.is_nullable(T, b)
      +nr = Re.is_nullable(T, r)
      rhs = Re.is_nullable(T, Cat{Alt{a, b}, r})
      %Re.cat_nullable(T, a, r): {Bool.or(_, Re.is_nullable(T, Cat{b, r})) == rhs: Bool}
      %Re.cat_nullable(T, b, r): {Bool.or(Bool.and(na, nr), _) == rhs: Bool}
      +l = Bool.or(Bool.and(na, nr), Bool.and(nb, nr))
      %Re.cat_nullable(T, Alt{a, b}, r): {l == _: Bool}
      %Re.alt_nullable(T, a, b): {l == Bool.and(_, nr): Bool}
      Shared.Bool.and_or(na, nb, nr)
    case Con{+c, +t}:
      +a2 = Re.step(~A, ~T, ~hit, a, c)
      +b2 = Re.step(~A, ~T, ~hit, b, c)
      +r2 = Re.step(~A, ~T, ~hit, r, c)
      +na = Re.is_nullable(T, a)
      +nb = Re.is_nullable(T, b)
      +p1 = {Cat{a2, r}: Re<T>}
      q1 = {Cat{Re.of_bool(T, na), r2}: Re<T>}
      +p2 = {Cat{b2, r}: Re<T>}
      q2 = {Cat{Re.of_bool(T, nb), r2}: Re<T>}
      +ab = {Cat{Alt{a2, b2}, r}: Re<T>}
      +qab = {Cat{Re.of_bool(T, Bool.or(na, nb)), r2}: Re<T>}
      +x = Re.matches(~A, ~T, ~hit, t, p1)
      +y = Re.matches(~A, ~T, ~hit, t, p2)
      +z = Re.matches(~A, ~T, ~hit, t, r2)
      %Re.alt_nullable(
        T,
        a,
        b
      ): {
        Bool.or(
          Re.matches(~A, ~T, ~hit, t, Alt{p1, q1}),
          Re.matches(~A, ~T, ~hit, t, Alt{p2, q2})
        )
          == Re.matches(~A, ~T, ~hit, t, Alt{ab, Cat{Re.of_bool(T, _), r2}}): Bool
      }
      +rhs = Re.matches(~A, ~T, ~hit, t, Alt{ab, qab})
      %Re.alt_or(
        ~A,
        ~T,
        ~hit,
        t,
        p1,
        q1
      ): {Bool.or(_, Re.matches(~A, ~T, ~hit, t, Alt{p2, q2})) == rhs: Bool}
      %Re.alt_or(
        ~A,
        ~T,
        ~hit,
        t,
        p2,
        q2
      ): {Bool.or(Bool.or(x, Re.matches(~A, ~T, ~hit, t, q1)), _) == rhs: Bool}
      %Re.cat_of_bool(
        ~A,
        ~T,
        ~hit,
        t,
        na,
        r2
      ): {Bool.or(Bool.or(x, _), Bool.or(y, Re.matches(~A, ~T, ~hit, t, q2))) == rhs: Bool}
      +l = Bool.or(Bool.or(x, Bool.and(na, z)), Bool.or(y, Bool.and(nb, z)))
      %Re.cat_of_bool(
        ~A,
        ~T,
        ~hit,
        t,
        nb,
        r2
      ): {Bool.or(Bool.or(x, Bool.and(na, z)), Bool.or(y, _)) == rhs: Bool}
      %Re.alt_or(~A, ~T, ~hit, t, ab, qab): {l == _: Bool}
      %Re.cat_alt(
        ~A,
        ~T,
        ~hit,
        t,
        a2,
        b2,
        r
      ): {l == Bool.or(_, Re.matches(~A, ~T, ~hit, t, qab)): Bool}
      %Re.cat_of_bool(~A, ~T, ~hit, t, Bool.or(na, nb), r2): {l == Bool.or(Bool.or(x, y), _): Bool}
      Re.cat_alt.bools(x, y, na, nb, z)

# Cat is associative
def Re.cat_assoc(
  ~A: Data,
  ~T: Data,
  ~hit: T -> A -> Bool,
  w: List<&2, A>,
  +a: Re<T>,
  +b: Re<T>,
  +r: Re<T>
) -> {
  Re.matches(
    ~A,
    ~T,
    ~hit,
    w,
    Cat{a, Cat{b, r}}
  )
    == Re.matches(~A, ~T, ~hit, w, Cat{Cat{a, b}, r}): Bool
}:
  match w:
    case Nil{}:
      +na = Re.is_nullable(T, a)
      +nb = Re.is_nullable(T, b)
      +nr = Re.is_nullable(T, r)
      rhs = Re.is_nullable(T, Cat{Cat{a, b}, r})
      %Re.cat_nullable(T, a, Cat{b, r}): {_ == rhs: Bool}
      %Re.cat_nullable(T, b, r): {Bool.and(na, _) == rhs: Bool}
      +l = Bool.and(na, Bool.and(nb, nr))
      %Re.cat_nullable(T, Cat{a, b}, r): {l == _: Bool}
      %Re.cat_nullable(T, a, b): {l == Bool.and(_, nr): Bool}
      Shared.Bool.and_assoc(na, nb, nr)
    case Con{+c, +t}:
      +a2 = Re.step(~A, ~T, ~hit, a, c)
      +b2 = Re.step(~A, ~T, ~hit, b, c)
      +r2 = Re.step(~A, ~T, ~hit, r, c)
      +na = Re.is_nullable(T, a)
      +nb = Re.is_nullable(T, b)
      +x1 = {Cat{a2, Cat{b, r}}: Re<T>}
      +br = {Cat{b2, r}: Re<T>}
      +inner = {Alt{br, Cat{Re.of_bool(T, nb), r2}}: Re<T>}
      q = {Cat{Re.of_bool(T, na), inner}: Re<T>}
      +c1 = {Cat{a2, b}: Re<T>}
      +c2 = {Cat{Re.of_bool(T, na), b2}: Re<T>}
      +qn = {Cat{Re.of_bool(T, Bool.and(na, nb)), r2}: Re<T>}
      +x = Re.matches(~A, ~T, ~hit, t, x1)
      +y = Re.matches(~A, ~T, ~hit, t, br)
      +z = Re.matches(~A, ~T, ~hit, t, r2)
      %Re.cat_nullable(
        T,
        a,
        b
      ): {
        Re.matches(
          ~A,
          ~T,
          ~hit,
          t,
          Alt{x1, q}
        )
          == Re.matches(~A, ~T, ~hit, t, Alt{Cat{Alt{c1, c2}, r}, Cat{Re.of_bool(T, _), r2}}): Bool
      }
      +rhs = Re.matches(~A, ~T, ~hit, t, Alt{Cat{Alt{c1, c2}, r}, qn})
      %Re.alt_or(~A, ~T, ~hit, t, x1, q): {_ == rhs: Bool}
      %Re.cat_of_bool(~A, ~T, ~hit, t, na, inner): {Bool.or(x, _) == rhs: Bool}
      %Re.alt_or(
        ~A,
        ~T,
        ~hit,
        t,
        br,
        Cat{Re.of_bool(T, nb), r2}
      ): {Bool.or(x, Bool.and(na, _)) == rhs: Bool}
      %Re.cat_of_bool(
        ~A,
        ~T,
        ~hit,
        t,
        nb,
        r2
      ): {Bool.or(x, Bool.and(na, Bool.or(y, _))) == rhs: Bool}
      +l = Bool.or(x, Bool.and(na, Bool.or(y, Bool.and(nb, z))))
      %Re.alt_or(~A, ~T, ~hit, t, Cat{Alt{c1, c2}, r}, qn): {l == _: Bool}
      %Re.cat_alt(
        ~A,
        ~T,
        ~hit,
        t,
        c1,
        c2,
        r
      ): {l == Bool.or(_, Re.matches(~A, ~T, ~hit, t, qn)): Bool}
      %Re.cat_assoc(
        ~A,
        ~T,
        ~hit,
        t,
        a2,
        b,
        r
      ): {
        l
          == Bool.or(
            Bool.or(_, Re.matches(~A, ~T, ~hit, t, Cat{c2, r})),
            Re.matches(~A, ~T, ~hit, t, qn)
          ): Bool
      }
      %Re.cat_assoc(
        ~A,
        ~T,
        ~hit,
        t,
        Re.of_bool(T, na),
        b2,
        r
      ): {l == Bool.or(Bool.or(x, _), Re.matches(~A, ~T, ~hit, t, qn)): Bool}
      %Re.cat_of_bool(
        ~A,
        ~T,
        ~hit,
        t,
        na,
        br
      ): {l == Bool.or(Bool.or(x, _), Re.matches(~A, ~T, ~hit, t, qn)): Bool}
      %Re.cat_of_bool(
        ~A,
        ~T,
        ~hit,
        t,
        Bool.and(na, nb),
        r2
      ): {l == Bool.or(Bool.or(x, Bool.and(na, y)), _): Bool}
      Re.cat_assoc.bools(x, y, na, nb, z)

# Cat congruence
# --------------
# A proof that two expressions match the same words is a function, which Bend
# may use only once. So Cat congruence takes the equalities that it needs for
# one word as data: the left sides agree on each prefix of the word, the right
# sides on each suffix.

# what x must still match after it reads w
def Re.walk(~A: Data, ~T: Data, ~hit: T -> A -> Bool, w: List<&2, A>, x: Re<T>) -> Re<T>:
  match w:
    case Nil{}:
      x
    case Con{c, t}:
      Re.walk(~A, ~T, ~hit, t, Re.step(~A, ~T, ~hit, x, c))

# x matches w exactly when what x must match after w matches the empty word
def Re.walk_null(
  ~A: Data,
  ~T: Data,
  ~hit: T -> A -> Bool,
  w: List<&2, A>,
  x: Re<T>
) -> {Re.matches(~A, ~T, ~hit, w, x) == Re.is_nullable(T, Re.walk(~A, ~T, ~hit, w, x)): Bool}:
  match w:
    case Nil{}:
      {==}
    case Con{c, t}:
      Re.walk_null(~A, ~T, ~hit, t, Re.step(~A, ~T, ~hit, x, c))

# a walk of pre, then c, is a step by c after a walk of pre
def Re.walk_snoc(
  ~A: Data,
  ~T: Data,
  ~hit: T -> A -> Bool,
  pre: List<&2, A>,
  c: A,
  x: Re<T>
) -> {
  Re.walk(
    ~A,
    ~T,
    ~hit,
    List.append(&2, A, pre, [c]),
    x
  )
    == Re.step(~A, ~T, ~hit, Re.walk(~A, ~T, ~hit, pre, x), c): Re<T>
}:
  match pre:
    case Nil{}:
      {==}
    case Con{d, t}:
      Re.walk_snoc(~A, ~T, ~hit, t, c, Re.step(~A, ~T, ~hit, x, d))

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof: it does not run
# Cat{x after pre, y} matches c, then t, when Cat{x after pre and c, y}
# matches t, or x matches pre and y matches c, then t
def Re.cat_walk(
  ~A: Data,
  ~T: Data,
  ~hit: T -> A -> Bool,
  +t: List<&2, A>,
  +c: A,
  +pre: List<&2, A>,
  +x: Re<T>,
  +y: Re<T>
) -> {
  Bool.or(
    Re.matches(~A, ~T, ~hit, t, Cat{Re.walk(~A, ~T, ~hit, List.append(&2, A, pre, [c]), x), y}),
    Bool.and(Re.matches(~A, ~T, ~hit, pre, x), Re.matches(~A, ~T, ~hit, c <> t, y))
  )
    == Re.matches(~A, ~T, ~hit, c <> t, Cat{Re.walk(~A, ~T, ~hit, pre, x), y}): Bool
}:
  +wx = Re.walk(~A, ~T, ~hit, pre, x)
  +ny = Re.step(~A, ~T, ~hit, y, c)
  wc = Re.walk(~A, ~T, ~hit, List.append(&2, A, pre, [c]), x)
  my = Re.matches(~A, ~T, ~hit, t, ny)
  l = Bool.or(
    Re.matches(~A, ~T, ~hit, t, Cat{wc, y}),
    Bool.and(Re.matches(~A, ~T, ~hit, pre, x), my)
  )
  %Re.alt_or(
    ~A,
    ~T,
    ~hit,
    t,
    Cat{Re.step(~A, ~T, ~hit, wx, c), y},
    Cat{Re.of_bool(T, Re.is_nullable(T, wx)), ny}
  ): {l == _: Bool}
  %Re.cat_of_bool(
    ~A,
    ~T,
    ~hit,
    t,
    Re.is_nullable(T, wx),
    ny
  ): {l == Bool.or(Re.matches(~A, ~T, ~hit, t, Cat{Re.step(~A, ~T, ~hit, wx, c), y}), _): Bool}
  %Re.walk_snoc(
    ~A,
    ~T,
    ~hit,
    pre,
    c,
    x
  ): {
    l == Bool.or(Re.matches(~A, ~T, ~hit, t, Cat{_, y}), Bool.and(Re.is_nullable(T, wx), my)): Bool
  }
  %Re.walk_null(
    ~A,
    ~T,
    ~hit,
    pre,
    x
  ): {l == Bool.or(Re.matches(~A, ~T, ~hit, t, Cat{wc, y}), Bool.and(_, my)): Bool}
  {==}
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# bend-lint: expect-begin bend-lint-rules/performance/append_in_loop@warning -- a proof's statement; a proof does not run
# x and x2 agree on pre, and on pre followed by each prefix of suf
def Re.AgreePre(
  ~A: Data,
  ~T: Data,
  ~hit: T -> A -> Bool,
  x: Re<T>,
  x2: Re<T>,
  pre: List<&2, A>,
  suf: List<&2, A>
) -> Type:
  match suf:
    case Nil{}:
      {Re.matches(~A, ~T, ~hit, pre, x) == Re.matches(~A, ~T, ~hit, pre, x2): Bool}
    case Con{c, t}:
      (
        {
          Re.matches(~A, ~T, ~hit, pre, x) == Re.matches(~A, ~T, ~hit, pre, x2): Bool
        }
          & Re.AgreePre(~A, ~T, ~hit, x, x2, List.append(&2, A, pre, [c]), t)
      )
# bend-lint: expect-end bend-lint-rules/performance/append_in_loop@warning

# y and y2 agree on each suffix of suf
def Re.AgreeSuf(
  ~A: Data,
  ~T: Data,
  ~hit: T -> A -> Bool,
  y: Re<T>,
  y2: Re<T>,
  suf: List<&2, A>
) -> Type:
  match suf:
    case Nil{}:
      {Re.matches(~A, ~T, ~hit, [], y) == Re.matches(~A, ~T, ~hit, [], y2): Bool}
    case Con{c, t}:
      (
        {
          Re.matches(~A, ~T, ~hit, c <> t, y) == Re.matches(~A, ~T, ~hit, c <> t, y2): Bool
        }
          & Re.AgreeSuf(~A, ~T, ~hit, y, y2, t)
      )

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof: it does not run
# Re.cat_agree after pre: Cat of the parts, the left ones after pre, matches
# suf the same way
def Re.cat_agree.go(
  ~A: Data,
  ~T: Data,
  ~hit: T -> A -> Bool,
  suf: List<&2, A>,
  +pre: List<&2, A>,
  +x: Re<T>,
  +x2: Re<T>,
  +y: Re<T>,
  +y2: Re<T>,
  ea: Re.AgreePre(~A, ~T, ~hit, x, x2, pre, suf),
  eb: Re.AgreeSuf(~A, ~T, ~hit, y, y2, suf)
) -> {
  Re.matches(
    ~A,
    ~T,
    ~hit,
    suf,
    Cat{Re.walk(~A, ~T, ~hit, pre, x), y}
  )
    == Re.matches(~A, ~T, ~hit, suf, Cat{Re.walk(~A, ~T, ~hit, pre, x2), y2}): Bool
}:
  match suf:
    case Nil{}:
      l = Re.is_nullable(T, Cat{Re.walk(~A, ~T, ~hit, pre, x), y})
      mx = Re.matches(~A, ~T, ~hit, pre, x)
      ny = Re.is_nullable(T, y)
      %Re.walk_null(~A, ~T, ~hit, pre, x2): {l == List.all.if(u => Re.is_nullable(T, y2), _): Bool}
      %ea: {l == List.all.if(u => Re.is_nullable(T, y2), _): Bool}
      %eb: {l == List.all.if(u => _, mx): Bool}
      %Re.walk_null(
        ~A,
        ~T,
        ~hit,
        pre,
        x
      ): {List.all.if(u => ny, _) == List.all.if(u => ny, mx): Bool}
      {==}
    case Con{+c, +t}:
      (e1, ra) = ea
      (e2, rb) = eb
      +pc = List.append(&2, A, pre, [c])
      mx = Re.matches(~A, ~T, ~hit, pre, x)
      r2 = Re.matches(~A, ~T, ~hit, t, Cat{Re.walk(~A, ~T, ~hit, pc, x2), y2})
      l = Bool.or(
        Re.matches(~A, ~T, ~hit, t, Cat{Re.walk(~A, ~T, ~hit, pc, x), y}),
        Bool.and(mx, Re.matches(~A, ~T, ~hit, c <> t, y))
      )
      %Re.cat_walk(
        ~A,
        ~T,
        ~hit,
        t,
        c,
        pre,
        x,
        y
      ): {_ == Re.matches(~A, ~T, ~hit, c <> t, Cat{Re.walk(~A, ~T, ~hit, pre, x2), y2}): Bool}
      %Re.cat_walk(~A, ~T, ~hit, t, c, pre, x2, y2): {l == _: Bool}
      %e1: {l == Bool.or(r2, Bool.and(_, Re.matches(~A, ~T, ~hit, c <> t, y2))): Bool}
      %e2: {l == Bool.or(r2, Bool.and(mx, _)): Bool}
      %Re.cat_agree.go(
        ~A,
        ~T,
        ~hit,
        t,
        pc,
        x,
        x2,
        y,
        y2,
        ra,
        rb
      ): {l == Bool.or(_, Bool.and(mx, Re.matches(~A, ~T, ~hit, c <> t, y))): Bool}
      {==}
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# Cat of parts that agree matches w the same way: x and x2 agree on each
# prefix of w (ea), and y and y2 on each suffix (eb)
law Re.cat_agree:
  for ~A: Data
  for ~T: Data
  for ~hit: T -> A -> Bool
  for w: List<&2, A>
  for x: Re<T>
  for x2: Re<T>
  for y: Re<T>
  for y2: Re<T>
  for ea: Re.AgreePre(~A, ~T, ~hit, x, x2, [], w)
  for eb: Re.AgreeSuf(~A, ~T, ~hit, y, y2, w)
  {Re.matches(~A, ~T, ~hit, w, Cat{x, y}) == Re.matches(~A, ~T, ~hit, w, Cat{x2, y2}): Bool}

def Re.cat_agree(aty, tty, hit, w, x, x2, y, y2, ea, eb):
  Re.cat_agree.go(~aty, ~tty, ~hit, w, [], x, x2, y, y2, ea, eb)

# Laws of equality
# ----------------

# bend-lint: expect-begin bend-lint-rules/performance/missed_fork@hint -- a proof: it does not run
# Re.is_eq is True for an expression and itself
def Re.is_eq_refl(
  ~T: Data,
  ~same: T -> T -> Bool,
  ~laws: Shared.Eq.Laws(T, same),
  a: Re<T>
) -> {Re.is_eq(~T, ~same, a, a) == True{}: Bool}:
  match a:
    case Void{}:
      {==}
    case Eps{}:
      {==}
    case One{x}:
      Shared.Eq.refl(~T, ~same, laws, x)
    case All{}:
      {==}
    case Star{x}:
      Re.is_eq_refl(~T, ~same, ~laws, x)
    case Cat{+a1, +b1}:
      Shared.List.all.if_both(
        Re.is_eq(~T, ~same, a1, a1),
        u => Re.is_eq(~T, ~same, b1, b1)
      )(Re.is_eq_refl(~T, ~same, ~laws, a1))(Re.is_eq_refl(~T, ~same, ~laws, b1))
    case Alt{+a1, +b1}:
      Shared.List.all.if_both(
        Re.is_eq(~T, ~same, a1, a1),
        u => Re.is_eq(~T, ~same, b1, b1)
      )(Re.is_eq_refl(~T, ~same, ~laws, a1))(Re.is_eq_refl(~T, ~same, ~laws, b1))
# bend-lint: expect-end bend-lint-rules/performance/missed_fork@hint

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# Re.is_eq is True only for equal expressions
def Re.is_eq_sound(
  ~T: Data,
  ~same: T -> T -> Bool,
  ~laws: Shared.Eq.Laws(T, same),
  a: Re<T>,
  b: Re<T>
) -> {Re.is_eq(~T, ~same, a, b) == True{}: Bool} -> {a == b: Re<T>}:
  match a b:
    case Void{} Void{}:
      _ => {==}
    case Void{} Eps{}:
      h => Empty.absurd({Void{} == Eps{}: Re<T>}, Shared.Bool.false_ne_true(h))
    case Void{} One{x2}:
      h => Empty.absurd({Void{} == One{x2}: Re<T>}, Shared.Bool.false_ne_true(h))
    case Void{} All{}:
      h => Empty.absurd({Void{} == All{}: Re<T>}, Shared.Bool.false_ne_true(h))
    case Void{} Star{x2}:
      h => Empty.absurd({Void{} == Star{x2}: Re<T>}, Shared.Bool.false_ne_true(h))
    case Void{} Cat{a2, b2}:
      h => Empty.absurd({Void{} == Cat{a2, b2}: Re<T>}, Shared.Bool.false_ne_true(h))
    case Void{} Alt{a2, b2}:
      h => Empty.absurd({Void{} == Alt{a2, b2}: Re<T>}, Shared.Bool.false_ne_true(h))
    case Eps{} Void{}:
      h => Empty.absurd({Eps{} == Void{}: Re<T>}, Shared.Bool.false_ne_true(h))
    case Eps{} Eps{}:
      _ => {==}
    case Eps{} One{x2}:
      h => Empty.absurd({Eps{} == One{x2}: Re<T>}, Shared.Bool.false_ne_true(h))
    case Eps{} All{}:
      h => Empty.absurd({Eps{} == All{}: Re<T>}, Shared.Bool.false_ne_true(h))
    case Eps{} Star{x2}:
      h => Empty.absurd({Eps{} == Star{x2}: Re<T>}, Shared.Bool.false_ne_true(h))
    case Eps{} Cat{a2, b2}:
      h => Empty.absurd({Eps{} == Cat{a2, b2}: Re<T>}, Shared.Bool.false_ne_true(h))
    case Eps{} Alt{a2, b2}:
      h => Empty.absurd({Eps{} == Alt{a2, b2}: Re<T>}, Shared.Bool.false_ne_true(h))
    case One{x1} Void{}:
      h => Empty.absurd({One{x1} == Void{}: Re<T>}, Shared.Bool.false_ne_true(h))
    case One{x1} Eps{}:
      h => Empty.absurd({One{x1} == Eps{}: Re<T>}, Shared.Bool.false_ne_true(h))
    case One{+x1} One{x2}:
      h =>
        %Shared.Eq.sound(~T, ~same, laws, x1, x2)(h): {One{x1} == One{_}: Re<T>}
        {==}
    case One{x1} All{}:
      h => Empty.absurd({One{x1} == All{}: Re<T>}, Shared.Bool.false_ne_true(h))
    case One{x1} Star{x2}:
      h => Empty.absurd({One{x1} == Star{x2}: Re<T>}, Shared.Bool.false_ne_true(h))
    case One{x1} Cat{a2, b2}:
      h => Empty.absurd({One{x1} == Cat{a2, b2}: Re<T>}, Shared.Bool.false_ne_true(h))
    case One{x1} Alt{a2, b2}:
      h => Empty.absurd({One{x1} == Alt{a2, b2}: Re<T>}, Shared.Bool.false_ne_true(h))
    case All{} Void{}:
      h => Empty.absurd({All{} == Void{}: Re<T>}, Shared.Bool.false_ne_true(h))
    case All{} Eps{}:
      h => Empty.absurd({All{} == Eps{}: Re<T>}, Shared.Bool.false_ne_true(h))
    case All{} One{x2}:
      h => Empty.absurd({All{} == One{x2}: Re<T>}, Shared.Bool.false_ne_true(h))
    case All{} All{}:
      _ => {==}
    case All{} Star{x2}:
      h => Empty.absurd({All{} == Star{x2}: Re<T>}, Shared.Bool.false_ne_true(h))
    case All{} Cat{a2, b2}:
      h => Empty.absurd({All{} == Cat{a2, b2}: Re<T>}, Shared.Bool.false_ne_true(h))
    case All{} Alt{a2, b2}:
      h => Empty.absurd({All{} == Alt{a2, b2}: Re<T>}, Shared.Bool.false_ne_true(h))
    case Star{x1} Void{}:
      h => Empty.absurd({Star{x1} == Void{}: Re<T>}, Shared.Bool.false_ne_true(h))
    case Star{x1} Eps{}:
      h => Empty.absurd({Star{x1} == Eps{}: Re<T>}, Shared.Bool.false_ne_true(h))
    case Star{x1} One{x2}:
      h => Empty.absurd({Star{x1} == One{x2}: Re<T>}, Shared.Bool.false_ne_true(h))
    case Star{x1} All{}:
      h => Empty.absurd({Star{x1} == All{}: Re<T>}, Shared.Bool.false_ne_true(h))
    case Star{+x1} Star{x2}:
      h =>
        %Re.is_eq_sound(~T, ~same, ~laws, x1, x2)(h): {Star{x1} == Star{_}: Re<T>}
        {==}
    case Star{x1} Cat{a2, b2}:
      h => Empty.absurd({Star{x1} == Cat{a2, b2}: Re<T>}, Shared.Bool.false_ne_true(h))
    case Star{x1} Alt{a2, b2}:
      h => Empty.absurd({Star{x1} == Alt{a2, b2}: Re<T>}, Shared.Bool.false_ne_true(h))
    case Cat{a1, b1} Void{}:
      h => Empty.absurd({Cat{a1, b1} == Void{}: Re<T>}, Shared.Bool.false_ne_true(h))
    case Cat{a1, b1} Eps{}:
      h => Empty.absurd({Cat{a1, b1} == Eps{}: Re<T>}, Shared.Bool.false_ne_true(h))
    case Cat{a1, b1} One{x2}:
      h => Empty.absurd({Cat{a1, b1} == One{x2}: Re<T>}, Shared.Bool.false_ne_true(h))
    case Cat{a1, b1} All{}:
      h => Empty.absurd({Cat{a1, b1} == All{}: Re<T>}, Shared.Bool.false_ne_true(h))
    case Cat{a1, b1} Star{x2}:
      h => Empty.absurd({Cat{a1, b1} == Star{x2}: Re<T>}, Shared.Bool.false_ne_true(h))
    case Cat{+a1, +b1} Cat{+a2, +b2}:
      +h =>
        %Re.is_eq_sound(
          ~T,
          ~same,
          ~laws,
          a1,
          a2
        )(
          Shared.List.all.if_hit(Re.is_eq(~T, ~same, a1, a2), u => Re.is_eq(~T, ~same, b1, b2))(h)
        ): {Cat{a1, b1} == Cat{_, b2}: Re<T>}
        %Re.is_eq_sound(
          ~T,
          ~same,
          ~laws,
          b1,
          b2
        )(
          Shared.List.all.if_rest(Re.is_eq(~T, ~same, a1, a2), u => Re.is_eq(~T, ~same, b1, b2))(h)
        ): {Cat{a1, b1} == Cat{a1, _}: Re<T>}
        {==}
    case Cat{a1, b1} Alt{a2, b2}:
      h => Empty.absurd({Cat{a1, b1} == Alt{a2, b2}: Re<T>}, Shared.Bool.false_ne_true(h))
    case Alt{a1, b1} Void{}:
      h => Empty.absurd({Alt{a1, b1} == Void{}: Re<T>}, Shared.Bool.false_ne_true(h))
    case Alt{a1, b1} Eps{}:
      h => Empty.absurd({Alt{a1, b1} == Eps{}: Re<T>}, Shared.Bool.false_ne_true(h))
    case Alt{a1, b1} One{x2}:
      h => Empty.absurd({Alt{a1, b1} == One{x2}: Re<T>}, Shared.Bool.false_ne_true(h))
    case Alt{a1, b1} All{}:
      h => Empty.absurd({Alt{a1, b1} == All{}: Re<T>}, Shared.Bool.false_ne_true(h))
    case Alt{a1, b1} Star{x2}:
      h => Empty.absurd({Alt{a1, b1} == Star{x2}: Re<T>}, Shared.Bool.false_ne_true(h))
    case Alt{a1, b1} Cat{a2, b2}:
      h => Empty.absurd({Alt{a1, b1} == Cat{a2, b2}: Re<T>}, Shared.Bool.false_ne_true(h))
    case Alt{+a1, +b1} Alt{+a2, +b2}:
      +h =>
        %Re.is_eq_sound(
          ~T,
          ~same,
          ~laws,
          a1,
          a2
        )(
          Shared.List.all.if_hit(Re.is_eq(~T, ~same, a1, a2), u => Re.is_eq(~T, ~same, b1, b2))(h)
        ): {Alt{a1, b1} == Alt{_, b2}: Re<T>}
        %Re.is_eq_sound(
          ~T,
          ~same,
          ~laws,
          b1,
          b2
        )(
          Shared.List.all.if_rest(Re.is_eq(~T, ~same, a1, a2), u => Re.is_eq(~T, ~same, b1, b2))(h)
        ): {Alt{a1, b1} == Alt{a1, _}: Re<T>}
        {==}
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# the laws of Re.is_eq, by the laws of same
def Re.laws(
  ~T: Data,
  ~same: T -> T -> Bool,
  ~laws: Shared.Eq.Laws(T, same)
) -> Shared.Eq.Laws(Re<T>, Re.is_eq(~T, ~same)):
  (a => Re.is_eq_refl(~T, ~same, ~laws, a), a => b => Re.is_eq_sound(~T, ~same, ~laws, a, b))

# the laws of Seq.is_eq, by the laws of same
def Seq.laws(
  ~T: Data,
  ~same: T -> T -> Bool,
  ~laws: Shared.Eq.Laws(T, same)
) -> Shared.Eq.Laws(List<&2, Re<T>>, Seq.is_eq(~T, ~same)):
  Shared.List.laws(~Re<T>, ~Re.is_eq(~T, ~same), ~Re.laws(~T, ~same, ~laws))

# Laws of partial derivatives
# ---------------------------

# a list of Seqs matches what its first Seq matches, or its rest
def Seqs.matches_cons(
  ~A: Data,
  ~T: Data,
  ~hit: T -> A -> Bool,
  s: List<&2, Re<T>>,
  xs: List<&2, List<&2, Re<T>>>,
  +w: List<&2, A>
) -> {
  Bool.or(
    Re.matches(~A, ~T, ~hit, w, Seq.re(T, s)),
    Seqs.matches(~A, ~T, ~hit, xs, w)
  )
    == Seqs.matches(~A, ~T, ~hit, s <> xs, w): Bool
}:
  %Shared.List.any.if_or(
    Re.matches(~A, ~T, ~hit, w, Seq.re(T, s)),
    u => Seqs.matches(~A, ~T, ~hit, xs, w)
  ): {_ == Seqs.matches(~A, ~T, ~hit, s <> xs, w): Bool}
  {==}

# the one-Seq list of r matches what r matches
def Seqs.matches_one(
  ~A: Data,
  ~T: Data,
  ~hit: T -> A -> Bool,
  +w: List<&2, A>,
  +r: Re<T>
) -> {Seqs.matches(~A, ~T, ~hit, [[r]], w) == Re.matches(~A, ~T, ~hit, w, r): Bool}:
  m = Re.matches(~A, ~T, ~hit, w, r)
  %Seqs.matches_cons(~A, ~T, ~hit, [r], [], w): {_ == m: Bool}
  %Re.cat_eps_r(~A, ~T, ~hit, w, r): {Bool.or(_, False{}) == m: Bool}
  %Shared.Bool.or_false(m): {_ == m: Bool}
  {==}

# the Seqs of Seq.step.keep match what r matches when b holds, or acc
def Seq.step.keep_matches(
  ~A: Data,
  ~T: Data,
  ~hit: T -> A -> Bool,
  b: Bool,
  +r: List<&2, Re<T>>,
  acc: List<&2, List<&2, Re<T>>>,
  +t: List<&2, A>
) -> {
  Bool.or(
    Re.matches(~A, ~T, ~hit, t, Cat{Re.of_bool(T, b), Seq.re(T, r)}),
    Seqs.matches(~A, ~T, ~hit, acc, t)
  )
    == Seqs.matches(~A, ~T, ~hit, Seq.step.keep(T, b, r, acc), t): Bool
}:
  match b:
    case False{}:
      sa = Seqs.matches(~A, ~T, ~hit, acc, t)
      %Re.cat_void_l(~A, ~T, ~hit, t, Seq.re(T, r)): {Bool.or(_, sa) == sa: Bool}
      {==}
    case True{}:
      %Re.cat_eps_l(
        ~A,
        ~T,
        ~hit,
        t,
        Seq.re(T, r)
      ): {
        Bool.or(
          _,
          Seqs.matches(~A, ~T, ~hit, acc, t)
        )
          == Seqs.matches(~A, ~T, ~hit, r <> acc, t): Bool
      }
      Seqs.matches_cons(~A, ~T, ~hit, r, acc, t)

# the Seqs that Bool.when picks match what p matches when n holds, or acc
def Seqs.matches_when(
  ~A: Data,
  ~T: Data,
  ~hit: T -> A -> Bool,
  n: Bool,
  -y: Bool,
  -p: List<&2, List<&2, Re<T>>>,
  -acc: List<&2, List<&2, Re<T>>>,
  -t: List<&2, A>,
  e: {Bool.or(y, Seqs.matches(~A, ~T, ~hit, acc, t)) == Seqs.matches(~A, ~T, ~hit, p, t): Bool}
) -> {
  Bool.or(
    Bool.and(n, y),
    Seqs.matches(~A, ~T, ~hit, acc, t)
  )
    == Seqs.matches(
      ~A,
      ~T,
      ~hit,
      Shared.Bool.when(List<&2, List<&2, Re<T>>>, n, u => p, u => acc),
      t
    ): Bool
}:
  match n:
    case False{}:
      {==}
    case True{}:
      e

# the Seqs of Seq.step.part match what h after c, then r, matches, or acc
def Seq.step.part_matches(
  ~A: Data,
  ~T: Data,
  ~hit: T -> A -> Bool,
  h: Re<T>,
  +r: List<&2, Re<T>>,
  +c: A,
  +acc: List<&2, List<&2, Re<T>>>,
  +t: List<&2, A>
) -> {
  Bool.or(
    Re.matches(~A, ~T, ~hit, t, Cat{Re.step(~A, ~T, ~hit, h, c), Seq.re(T, r)}),
    Seqs.matches(~A, ~T, ~hit, acc, t)
  )
    == Seqs.matches(~A, ~T, ~hit, Seq.step.part(~A, ~T, ~hit, h, r, c, acc), t): Bool
}:
  match h:
    case Void{}:
      sa = Seqs.matches(~A, ~T, ~hit, acc, t)
      %Re.cat_void_l(~A, ~T, ~hit, t, Seq.re(T, r)): {Bool.or(_, sa) == sa: Bool}
      {==}
    case Eps{}:
      sa = Seqs.matches(~A, ~T, ~hit, acc, t)
      %Re.cat_void_l(~A, ~T, ~hit, t, Seq.re(T, r)): {Bool.or(_, sa) == sa: Bool}
      {==}
    case One{a}:
      Seq.step.keep_matches(~A, ~T, ~hit, hit(a)(c), r, acc, t)
    case All{}:
      Seqs.matches_cons(~A, ~T, ~hit, All{} <> r, acc, t)
    case Star{+x}:
      %Re.cat_assoc(
        ~A,
        ~T,
        ~hit,
        t,
        Re.step(~A, ~T, ~hit, x, c),
        Star{x},
        Seq.re(T, r)
      ): {
        Bool.or(
          _,
          Seqs.matches(~A, ~T, ~hit, acc, t)
        )
          == Seqs.matches(
            ~A,
            ~T,
            ~hit,
            Seq.step.part(~A, ~T, ~hit, x, Star{x} <> r, c, acc),
            t
          ): Bool
      }
      Seq.step.part_matches(~A, ~T, ~hit, x, Star{x} <> r, c, acc, t)
    case Cat{+a, +b}:
      +a2 = Re.step(~A, ~T, ~hit, a, c)
      +b2 = Re.step(~A, ~T, ~hit, b, c)
      +na = Re.is_nullable(T, a)
      +rr = Seq.re(T, r)
      +sa = Seqs.matches(~A, ~T, ~hit, acc, t)
      wh = Shared.Bool.when(
        List<&2, List<&2, Re<T>>>,
        na,
        u => Seq.step.part(~A, ~T, ~hit, b, r, c, acc),
        u => acc
      )
      +x = Re.matches(~A, ~T, ~hit, t, Cat{a2, Cat{b, rr}})
      +y = Re.matches(~A, ~T, ~hit, t, Cat{b2, rr})
      +nb2 = {Cat{Re.of_bool(T, na), b2}: Re<T>}
      l = Bool.or(Re.matches(~A, ~T, ~hit, t, Cat{Alt{Cat{a2, b}, nb2}, rr}), sa)
      %Seq.step.part_matches(~A, ~T, ~hit, a, b <> r, c, wh, t): {l == _: Bool}
      %Seqs.matches_when(
        ~A,
        ~T,
        ~hit,
        na,
        y,
        Seq.step.part(~A, ~T, ~hit, b, r, c, acc),
        acc,
        t,
        Seq.step.part_matches(~A, ~T, ~hit, b, r, c, acc, t)
      ): {l == Bool.or(x, _): Bool}
      +rhs = Bool.or(x, Bool.or(Bool.and(na, y), sa))
      %Re.cat_alt(~A, ~T, ~hit, t, Cat{a2, b}, nb2, rr): {Bool.or(_, sa) == rhs: Bool}
      %Re.cat_assoc(
        ~A,
        ~T,
        ~hit,
        t,
        a2,
        b,
        rr
      ): {Bool.or(Bool.or(_, Re.matches(~A, ~T, ~hit, t, Cat{nb2, rr})), sa) == rhs: Bool}
      %Re.cat_assoc(
        ~A,
        ~T,
        ~hit,
        t,
        Re.of_bool(T, na),
        b2,
        rr
      ): {Bool.or(Bool.or(x, _), sa) == rhs: Bool}
      %Re.cat_of_bool(~A, ~T, ~hit, t, na, Cat{b2, rr}): {Bool.or(Bool.or(x, _), sa) == rhs: Bool}
      %Shared.Bool.or_assoc(x, Bool.and(na, y), sa): {_ == rhs: Bool}
      {==}
    case Alt{+a, +b}:
      +a2 = Re.step(~A, ~T, ~hit, a, c)
      +b2 = Re.step(~A, ~T, ~hit, b, c)
      +rr = Seq.re(T, r)
      +sa = Seqs.matches(~A, ~T, ~hit, acc, t)
      pb = Seq.step.part(~A, ~T, ~hit, b, r, c, acc)
      +xa = Re.matches(~A, ~T, ~hit, t, Cat{a2, rr})
      +xb = Re.matches(~A, ~T, ~hit, t, Cat{b2, rr})
      l = Bool.or(Re.matches(~A, ~T, ~hit, t, Cat{Alt{a2, b2}, rr}), sa)
      %Seq.step.part_matches(~A, ~T, ~hit, a, r, c, pb, t): {l == _: Bool}
      %Seq.step.part_matches(~A, ~T, ~hit, b, r, c, acc, t): {l == Bool.or(xa, _): Bool}
      +rhs = Bool.or(xa, Bool.or(xb, sa))
      %Re.cat_alt(~A, ~T, ~hit, t, a2, b2, rr): {Bool.or(_, sa) == rhs: Bool}
      %Shared.Bool.or_assoc(xa, xb, sa): {_ == rhs: Bool}
      {==}

# the Seqs of Seq.step match t exactly when s matches c, then t; or acc does
def Seq.step_matches(
  ~A: Data,
  ~T: Data,
  ~hit: T -> A -> Bool,
  s: List<&2, Re<T>>,
  +c: A,
  +acc: List<&2, List<&2, Re<T>>>,
  +t: List<&2, A>
) -> {
  Bool.or(
    Re.matches(~A, ~T, ~hit, c <> t, Seq.re(T, s)),
    Seqs.matches(~A, ~T, ~hit, acc, t)
  )
    == Seqs.matches(~A, ~T, ~hit, Seq.step(~A, ~T, ~hit, s, c, acc), t): Bool
}:
  match s:
    case Nil{}:
      sa = Seqs.matches(~A, ~T, ~hit, acc, t)
      %Re.void_never(~A, ~T, ~hit, t): {Bool.or(_, sa) == sa: Bool}
      {==}
    case Con{+h, +g}:
      +h2 = Re.step(~A, ~T, ~hit, h, c)
      +nh = Re.is_nullable(T, h)
      +gg = Seq.re(T, g)
      +g2 = Re.step(~A, ~T, ~hit, gg, c)
      +sa = Seqs.matches(~A, ~T, ~hit, acc, t)
      wh = Shared.Bool.when(
        List<&2, List<&2, Re<T>>>,
        nh,
        u => Seq.step(~A, ~T, ~hit, g, c, acc),
        u => acc
      )
      +x = Re.matches(~A, ~T, ~hit, t, Cat{h2, gg})
      +y = Re.matches(~A, ~T, ~hit, t, g2)
      +ng2 = {Cat{Re.of_bool(T, nh), g2}: Re<T>}
      l = Bool.or(Re.matches(~A, ~T, ~hit, t, Alt{Cat{h2, gg}, ng2}), sa)
      %Seq.step.part_matches(~A, ~T, ~hit, h, g, c, wh, t): {l == _: Bool}
      %Seqs.matches_when(
        ~A,
        ~T,
        ~hit,
        nh,
        y,
        Seq.step(~A, ~T, ~hit, g, c, acc),
        acc,
        t,
        Seq.step_matches(~A, ~T, ~hit, g, c, acc, t)
      ): {l == Bool.or(x, _): Bool}
      +rhs = Bool.or(x, Bool.or(Bool.and(nh, y), sa))
      %Re.alt_or(~A, ~T, ~hit, t, Cat{h2, gg}, ng2): {Bool.or(_, sa) == rhs: Bool}
      %Re.cat_of_bool(~A, ~T, ~hit, t, nh, g2): {Bool.or(Bool.or(x, _), sa) == rhs: Bool}
      %Shared.Bool.or_assoc(x, Bool.and(nh, y), sa): {_ == rhs: Bool}
      {==}

# the Seqs of Seqs.step.all match t exactly when xs matches c, then t
def Seqs.step.all_matches(
  ~A: Data,
  ~T: Data,
  ~hit: T -> A -> Bool,
  xs: List<&2, List<&2, Re<T>>>,
  +c: A,
  +t: List<&2, A>
) -> {
  Seqs.matches(
    ~A,
    ~T,
    ~hit,
    Seqs.step.all(~A, ~T, ~hit, xs, c),
    t
  )
    == Seqs.matches(~A, ~T, ~hit, xs, c <> t): Bool
}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      m = Re.matches(~A, ~T, ~hit, c <> t, Seq.re(T, x))
      +ra = Seqs.step.all(~A, ~T, ~hit, r, c)
      l = Seqs.matches(~A, ~T, ~hit, Seq.step(~A, ~T, ~hit, x, c, ra), t)
      %Seqs.matches_cons(~A, ~T, ~hit, x, r, c <> t): {l == _: Bool}
      %Seqs.step.all_matches(~A, ~T, ~hit, r, c, t): {l == Bool.or(m, _): Bool}
      %Seq.step_matches(
        ~A,
        ~T,
        ~hit,
        x,
        c,
        ra,
        t
      ): {_ == Bool.or(m, Seqs.matches(~A, ~T, ~hit, ra, t)): Bool}
      {==}

# the Seqs after c match t exactly when the Seqs match c, then t
law Seqs.matches_step:
  for ~A: Data
  for ~T: Data
  for ~hit: T -> A -> Bool
  for ~same: T -> T -> Bool
  for ~key: T -> List<&2, Bool>
  for ~laws: Shared.Eq.Laws(T, same)
  for +xs: List<&2, List<&2, Re<T>>>
  for +c: A
  for +t: List<&2, A>
  {
    Seqs.matches(
      ~A,
      ~T,
      ~hit,
      Seqs.step(~A, ~T, ~hit, ~same, ~key, xs, c),
      t
    )
      == Seqs.matches(~A, ~T, ~hit, xs, c <> t): Bool
  }

def Seqs.matches_step(aty, tty, hit, same, key, laws, xs, c, t):
  %Seqs.step.all_matches(
    ~aty,
    ~tty,
    ~hit,
    xs,
    c,
    t
  ): {Seqs.matches(~aty, ~tty, ~hit, Seqs.step(~aty, ~tty, ~hit, ~same, ~key, xs, c), t) == _: Bool}
  KeySets.KeySet.unique_some(
    ~List<&2, Re<tty>>,
    ~List<&2, aty>,
    ~Seq.is_eq(~tty, ~same),
    ~Seq.key(~tty, ~key),
    ~Seq.matches(~aty, ~tty, ~hit),
    ~Seq.laws(~tty, ~same, ~laws),
    Seqs.step.all(~aty, ~tty, ~hit, xs, c),
    t
  )

# the Seqs after the word w match the empty word exactly when the Seqs match w
def Seqs.walk_matches(
  ~A: Data,
  ~T: Data,
  ~hit: T -> A -> Bool,
  ~same: T -> T -> Bool,
  ~key: T -> List<&2, Bool>,
  ~laws: Shared.Eq.Laws(T, same),
  w: List<&2, A>,
  +xs: List<&2, List<&2, Re<T>>>
) -> {
  Seqs.matches(
    ~A,
    ~T,
    ~hit,
    Seqs.walk(~A, ~T, ~hit, ~same, ~key, w, xs),
    []
  )
    == Seqs.matches(~A, ~T, ~hit, xs, w): Bool
}:
  match w:
    case Nil{}:
      {==}
    case Con{+c, +t}:
      xc = Seqs.step(~A, ~T, ~hit, ~same, ~key, xs, c)
      %Seqs.matches_step(
        ~A,
        ~T,
        ~hit,
        ~same,
        ~key,
        ~laws,
        xs,
        c,
        t
      ): {Seqs.matches(~A, ~T, ~hit, Seqs.walk(~A, ~T, ~hit, ~same, ~key, t, xc), []) == _: Bool}
      Seqs.walk_matches(~A, ~T, ~hit, ~same, ~key, ~laws, t, xc)

# the fast matcher gives the answer of the clear one
law Re.accepts_matches:
  for ~A: Data
  for ~T: Data
  for ~hit: T -> A -> Bool
  for ~same: T -> T -> Bool
  for ~key: T -> List<&2, Bool>
  for ~laws: Shared.Eq.Laws(T, same)
  for +w: List<&2, A>
  for +r: Re<T>
  {Re.accepts(~A, ~T, ~hit, ~same, ~key, w, r) == Re.matches(~A, ~T, ~hit, w, r): Bool}

def Re.accepts_matches(aty, tty, hit, same, key, laws, w, r):
  %Seqs.matches_one(
    ~aty,
    ~tty,
    ~hit,
    w,
    r
  ): {Re.accepts(~aty, ~tty, ~hit, ~same, ~key, w, r) == _: Bool}
  Seqs.walk_matches(~aty, ~tty, ~hit, ~same, ~key, ~laws, w, [[r]])

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# Seq.step.part moves h, then r, alike under c and f
def Seq.step.part_alike(
  ~A: Data,
  ~T: Data,
  ~V: Data,
  ~hit: T -> A -> Bool,
  ~p: V -> T -> Bool,
  ~near: V -> A -> A -> Bool,
  ~alike: @g: V -> @c: A -> @f: A -> @t: T -> {
    near(g)(c)(f) == True{}: Bool
  } -> {p(g)(t) == True{}: Bool} -> {hit(t)(c) == hit(t)(f): Bool},
  h: Re<T>,
  +r: List<&2, Re<T>>,
  +g: V,
  +c: A,
  +f: A,
  +acc: List<&2, List<&2, Re<T>>>,
  +en: {near(g)(c)(f) == True{}: Bool}
) -> {
  Re.holds(~T, ~V, ~p, g, h) == True{}: Bool
} -> {
  Seq.step.part(
    ~A,
    ~T,
    ~hit,
    h,
    r,
    c,
    acc
  )
    == Seq.step.part(~A, ~T, ~hit, h, r, f, acc): List<&2, List<&2, Re<T>>>
}:
  match h:
    case Void{}:
      _ => {==}
    case Eps{}:
      _ => {==}
    case One{a}:
      eh =>
        %alike(
          g
        )(
          c
        )(
          f
        )(
          a
        )(
          en
        )(
          eh
        ): {
          Seq.step.keep(
            T,
            hit(a)(c),
            r,
            acc
          )
            == Seq.step.keep(T, _, r, acc): List<&2, List<&2, Re<T>>>
        }
        {==}
    case All{}:
      _ => {==}
    case Star{+x}:
      Seq.step.part_alike(~A, ~T, ~V, ~hit, ~p, ~near, ~alike, x, Star{x} <> r, g, c, f, acc, en)
    case Cat{+a, +b}:
      +eh =>
        +ha = Re.holds(~T, ~V, ~p, g, a)
        +na = Re.is_nullable(T, a)
        +wc = Shared.Bool.when(
          List<&2, List<&2, Re<T>>>,
          na,
          u => Seq.step.part(~A, ~T, ~hit, b, r, c, acc),
          u => acc
        )
        %Seq.step.part_alike(
          ~A,
          ~T,
          ~V,
          ~hit,
          ~p,
          ~near,
          ~alike,
          b,
          r,
          g,
          c,
          f,
          acc,
          en
        )(
          Shared.List.all.if_rest(ha, u => Re.holds(~T, ~V, ~p, g, b))(eh)
        ): {
          Seq.step.part(
            ~A,
            ~T,
            ~hit,
            a,
            b <> r,
            c,
            wc
          )
            == Seq.step.part(
              ~A,
              ~T,
              ~hit,
              a,
              b <> r,
              f,
              Shared.Bool.when(List<&2, List<&2, Re<T>>>, na, u => _, u => acc)
            ): List<&2, List<&2, Re<T>>>
        }
        Seq.step.part_alike(
          ~A,
          ~T,
          ~V,
          ~hit,
          ~p,
          ~near,
          ~alike,
          a,
          b <> r,
          g,
          c,
          f,
          wc,
          en
        )(Shared.List.all.if_hit(ha, u => Re.holds(~T, ~V, ~p, g, b))(eh))
    case Alt{+a, +b}:
      +eh =>
        +ha = Re.holds(~T, ~V, ~p, g, a)
        +pc = Seq.step.part(~A, ~T, ~hit, b, r, c, acc)
        %Seq.step.part_alike(
          ~A,
          ~T,
          ~V,
          ~hit,
          ~p,
          ~near,
          ~alike,
          b,
          r,
          g,
          c,
          f,
          acc,
          en
        )(
          Shared.List.all.if_rest(ha, u => Re.holds(~T, ~V, ~p, g, b))(eh)
        ): {
          Seq.step.part(
            ~A,
            ~T,
            ~hit,
            a,
            r,
            c,
            pc
          )
            == Seq.step.part(~A, ~T, ~hit, a, r, f, _): List<&2, List<&2, Re<T>>>
        }
        Seq.step.part_alike(
          ~A,
          ~T,
          ~V,
          ~hit,
          ~p,
          ~near,
          ~alike,
          a,
          r,
          g,
          c,
          f,
          pc,
          en
        )(Shared.List.all.if_hit(ha, u => Re.holds(~T, ~V, ~p, g, b))(eh))

# Seq.step moves s alike under c and f
def Seq.step_alike(
  ~A: Data,
  ~T: Data,
  ~V: Data,
  ~hit: T -> A -> Bool,
  ~p: V -> T -> Bool,
  ~near: V -> A -> A -> Bool,
  ~alike: @g: V -> @c: A -> @f: A -> @t: T -> {
    near(g)(c)(f) == True{}: Bool
  } -> {p(g)(t) == True{}: Bool} -> {hit(t)(c) == hit(t)(f): Bool},
  s: List<&2, Re<T>>,
  +g: V,
  +c: A,
  +f: A,
  +acc: List<&2, List<&2, Re<T>>>,
  +en: {near(g)(c)(f) == True{}: Bool}
) -> {
  Seq.holds(~T, ~V, ~p, g, s) == True{}: Bool
} -> {
  Seq.step(~A, ~T, ~hit, s, c, acc) == Seq.step(~A, ~T, ~hit, s, f, acc): List<&2, List<&2, Re<T>>>
}:
  match s:
    case Nil{}:
      _ => {==}
    case Con{+h, +t}:
      +es =>
        +hh = Re.holds(~T, ~V, ~p, g, h)
        +nh = Re.is_nullable(T, h)
        +wc = Shared.Bool.when(
          List<&2, List<&2, Re<T>>>,
          nh,
          u => Seq.step(~A, ~T, ~hit, t, c, acc),
          u => acc
        )
        %Seq.step_alike(
          ~A,
          ~T,
          ~V,
          ~hit,
          ~p,
          ~near,
          ~alike,
          t,
          g,
          c,
          f,
          acc,
          en
        )(
          Shared.List.all.if_rest(hh, u => Seq.holds(~T, ~V, ~p, g, t))(es)
        ): {
          Seq.step.part(
            ~A,
            ~T,
            ~hit,
            h,
            t,
            c,
            wc
          )
            == Seq.step.part(
              ~A,
              ~T,
              ~hit,
              h,
              t,
              f,
              Shared.Bool.when(List<&2, List<&2, Re<T>>>, nh, u => _, u => acc)
            ): List<&2, List<&2, Re<T>>>
        }
        Seq.step.part_alike(
          ~A,
          ~T,
          ~V,
          ~hit,
          ~p,
          ~near,
          ~alike,
          h,
          t,
          g,
          c,
          f,
          wc,
          en
        )(Shared.List.all.if_hit(hh, u => Seq.holds(~T, ~V, ~p, g, t))(es))

# Seqs.step.all moves xs alike under c and f
def Seqs.step.all_alike(
  ~A: Data,
  ~T: Data,
  ~V: Data,
  ~hit: T -> A -> Bool,
  ~p: V -> T -> Bool,
  ~near: V -> A -> A -> Bool,
  ~alike: @g: V -> @c: A -> @f: A -> @t: T -> {
    near(g)(c)(f) == True{}: Bool
  } -> {p(g)(t) == True{}: Bool} -> {hit(t)(c) == hit(t)(f): Bool},
  xs: List<&2, List<&2, Re<T>>>,
  +g: V,
  +c: A,
  +f: A,
  +en: {near(g)(c)(f) == True{}: Bool}
) -> {
  Seqs.holds(~T, ~V, ~p, xs, g) == True{}: Bool
} -> {
  Seqs.step.all(
    ~A,
    ~T,
    ~hit,
    xs,
    c
  )
    == Seqs.step.all(~A, ~T, ~hit, xs, f): List<&2, List<&2, Re<T>>>
}:
  match xs:
    case Nil{}:
      _ => {==}
    case Con{+x, +r}:
      +ev =>
        +hx = Seq.holds(~T, ~V, ~p, g, x)
        +rc = Seqs.step.all(~A, ~T, ~hit, r, c)
        %Seqs.step.all_alike(
          ~A,
          ~T,
          ~V,
          ~hit,
          ~p,
          ~near,
          ~alike,
          r,
          g,
          c,
          f,
          en
        )(
          Shared.List.all.if_rest(hx, u => Seqs.holds(~T, ~V, ~p, r, g))(ev)
        ): {
          Seq.step(
            ~A,
            ~T,
            ~hit,
            x,
            c,
            rc
          )
            == Seq.step(~A, ~T, ~hit, x, f, _): List<&2, List<&2, Re<T>>>
        }
        Seq.step_alike(
          ~A,
          ~T,
          ~V,
          ~hit,
          ~p,
          ~near,
          ~alike,
          x,
          g,
          c,
          f,
          rc,
          en
        )(Shared.List.all.if_hit(hx, u => Seqs.holds(~T, ~V, ~p, r, g))(ev))
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# Two symbols that every atom of the Seqs treats alike move the Seqs alike.
# near(g)(c)(f) says that c and f are such symbols, when p holds of g and each
# atom; alike is its proof.
law Seqs.step_alike:
  for ~A: Data
  for ~T: Data
  for ~V: Data
  for ~hit: T -> A -> Bool
  for ~same: T -> T -> Bool
  for ~key: T -> List<&2, Bool>
  for ~p: V -> T -> Bool
  for ~near: V -> A -> A -> Bool
  for ~alike: @g: V -> @c: A -> @f: A -> @t: T -> {
    near(g)(c)(f) == True{}: Bool
  } -> {p(g)(t) == True{}: Bool} -> {hit(t)(c) == hit(t)(f): Bool}
  for +xs: List<&2, List<&2, Re<T>>>
  for +g: V
  for +c: A
  for +f: A
  {
    near(g)(c)(f) == True{}: Bool
  } -> {
    Seqs.holds(~T, ~V, ~p, xs, g) == True{}: Bool
  } -> {
    Seqs.step(
      ~A,
      ~T,
      ~hit,
      ~same,
      ~key,
      xs,
      c
    )
      == Seqs.step(~A, ~T, ~hit, ~same, ~key, xs, f): List<&2, List<&2, Re<T>>>
  }

def Seqs.step_alike(aty, tty, vty, hit, same, key, p, near, alike, xs, g, c, f):
  en => ev => Equal.cong(
    List<&2, List<&2, Re<tty>>>,
    List<&2, List<&2, Re<tty>>>,
    l => KeySets.KeySet.unique(
      ~List<&2, Re<tty>>,
      ~Seq.is_eq(~tty, ~same),
      ~Seq.key(~tty, ~key),
      l,
      Tries.Trie.new(List<&2, Re<tty>>)
    ),
    Seqs.step.all(~aty, ~tty, ~hit, xs, c),
    Seqs.step.all(~aty, ~tty, ~hit, xs, f),
    Seqs.step.all_alike(~aty, ~tty, ~vty, ~hit, ~p, ~near, ~alike, xs, g, c, f, en)(ev)
  )
