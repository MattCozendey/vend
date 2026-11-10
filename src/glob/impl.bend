import Base
import ../shared.bend as Shared
import ./spec.bend as Spec

# Equality
# --------
# Each is_eq answers True only for equal values (its is_eq_sound), so a
# membership test can stand for the member itself.

# Char.is_eq is True only for equal characters
def Char.is_eq_sound(a: Char, b: Char) -> {Char.is_eq(a, b) == True{}: Bool} -> {a == b: Char}:
  match a b:
    case Chr{x} Chr{y}:
      h => Equal.cong(U32, Char, u => Chr{u}, x, y, Shared.U32.is_eq_sound(x, y)(h))

# xs and ys are the same characters
# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- it works on a glob, a search state or a character list of a few items, so the extra call is short
def Chars.is_eq(xs: List<&2, Char>, ys: List<&2, Char>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{x, xt} Con{y, yt}:
      Bool.and(Char.is_eq(x, y), Chars.is_eq(xt, yt))
    case _ _:
      False{}
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# Chars.is_eq is True only for the same characters
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- only proofs use it; no program runs it
def Chars.is_eq_sound(
  xs: List<&2, Char>,
  ys: List<&2, Char>
) -> {Chars.is_eq(xs, ys) == True{}: Bool} -> {xs == ys: List<&2, Char>}:
  match xs ys:
    case Nil{} Nil{}:
      _ => {==}
    case Nil{} Con{y, yt}:
      h => Empty.absurd({Nil{} == Con{y, yt}: List<&2, Char>}, Shared.Bool.false_ne_true(h))
    case Con{x, xt} Nil{}:
      h => Empty.absurd({Con{x, xt} == Nil{}: List<&2, Char>}, Shared.Bool.false_ne_true(h))
    case Con{+x, +xt} Con{+y, +yt}:
      +h =>
        %Char.is_eq_sound(
          x,
          y
        )(
          Shared.Bool.and_true_left(Char.is_eq(x, y), Chars.is_eq(xt, yt))(h)
        ): {Con{x, xt} == Con{_, yt}: List<&2, Char>}
        %Chars.is_eq_sound(
          xt,
          yt
        )(
          Shared.Bool.and_true_right(Char.is_eq(x, y), Chars.is_eq(xt, yt))(h)
        ): {Con{x, xt} == Con{x, _}: List<&2, Char>}
        {==}
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# a and b are the same glob
# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- it works on a glob, a search state or a character list of a few items, so the extra call is short
def Glob.is_eq(a: Spec.Glob, b: Spec.Glob) -> Bool:
  match a b:
    case Spec.Void{} Spec.Void{}:
      True{}
    case Spec.Eps{} Spec.Eps{}:
      True{}
    case Spec.Lit{x1} Spec.Lit{x2}:
      Char.is_eq(x1, x2)
    case Spec.Any{} Spec.Any{}:
      True{}
    case Spec.Star{} Spec.Star{}:
      True{}
    case Spec.Class{n1, cs1} Spec.Class{n2, cs2}:
      Bool.and(Shared.Bool.is_eq(n1, n2), Chars.is_eq(cs1, cs2))
    case Spec.Deep{} Spec.Deep{}:
      True{}
    case Spec.Cat{a1, b1} Spec.Cat{a2, b2}:
      Bool.and(Glob.is_eq(a1, a2), Glob.is_eq(b1, b2))
    case Spec.Alt{a1, b1} Spec.Alt{a2, b2}:
      Bool.and(Glob.is_eq(a1, a2), Glob.is_eq(b1, b2))
    case _ _:
      False{}
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# Glob.is_eq is True only for the same glob
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- only proofs use it; no program runs it
def Glob.is_eq_sound(
  a: Spec.Glob,
  b: Spec.Glob
) -> {Glob.is_eq(a, b) == True{}: Bool} -> {a == b: Spec.Glob}:
  match a b:
    case Spec.Void{} Spec.Void{}:
      _ => {==}
    case Spec.Void{} Spec.Eps{}:
      h => Empty.absurd({Spec.Void{} == Spec.Eps{}: Spec.Glob}, Shared.Bool.false_ne_true(h))
    case Spec.Void{} Spec.Lit{x2}:
      h => Empty.absurd({Spec.Void{} == Spec.Lit{x2}: Spec.Glob}, Shared.Bool.false_ne_true(h))
    case Spec.Void{} Spec.Any{}:
      h => Empty.absurd({Spec.Void{} == Spec.Any{}: Spec.Glob}, Shared.Bool.false_ne_true(h))
    case Spec.Void{} Spec.Star{}:
      h => Empty.absurd({Spec.Void{} == Spec.Star{}: Spec.Glob}, Shared.Bool.false_ne_true(h))
    case Spec.Void{} Spec.Class{n2, cs2}:
      h => Empty.absurd(
        {Spec.Void{} == Spec.Class{n2, cs2}: Spec.Glob},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Void{} Spec.Deep{}:
      h => Empty.absurd({Spec.Void{} == Spec.Deep{}: Spec.Glob}, Shared.Bool.false_ne_true(h))
    case Spec.Void{} Spec.Cat{a2, b2}:
      h => Empty.absurd({Spec.Void{} == Spec.Cat{a2, b2}: Spec.Glob}, Shared.Bool.false_ne_true(h))
    case Spec.Void{} Spec.Alt{a2, b2}:
      h => Empty.absurd({Spec.Void{} == Spec.Alt{a2, b2}: Spec.Glob}, Shared.Bool.false_ne_true(h))
    case Spec.Eps{} Spec.Void{}:
      h => Empty.absurd({Spec.Eps{} == Spec.Void{}: Spec.Glob}, Shared.Bool.false_ne_true(h))
    case Spec.Eps{} Spec.Eps{}:
      _ => {==}
    case Spec.Eps{} Spec.Lit{x2}:
      h => Empty.absurd({Spec.Eps{} == Spec.Lit{x2}: Spec.Glob}, Shared.Bool.false_ne_true(h))
    case Spec.Eps{} Spec.Any{}:
      h => Empty.absurd({Spec.Eps{} == Spec.Any{}: Spec.Glob}, Shared.Bool.false_ne_true(h))
    case Spec.Eps{} Spec.Star{}:
      h => Empty.absurd({Spec.Eps{} == Spec.Star{}: Spec.Glob}, Shared.Bool.false_ne_true(h))
    case Spec.Eps{} Spec.Class{n2, cs2}:
      h => Empty.absurd(
        {Spec.Eps{} == Spec.Class{n2, cs2}: Spec.Glob},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Eps{} Spec.Deep{}:
      h => Empty.absurd({Spec.Eps{} == Spec.Deep{}: Spec.Glob}, Shared.Bool.false_ne_true(h))
    case Spec.Eps{} Spec.Cat{a2, b2}:
      h => Empty.absurd({Spec.Eps{} == Spec.Cat{a2, b2}: Spec.Glob}, Shared.Bool.false_ne_true(h))
    case Spec.Eps{} Spec.Alt{a2, b2}:
      h => Empty.absurd({Spec.Eps{} == Spec.Alt{a2, b2}: Spec.Glob}, Shared.Bool.false_ne_true(h))
    case Spec.Lit{x1} Spec.Void{}:
      h => Empty.absurd({Spec.Lit{x1} == Spec.Void{}: Spec.Glob}, Shared.Bool.false_ne_true(h))
    case Spec.Lit{+x1} Spec.Eps{}:
      h => Empty.absurd({Spec.Lit{x1} == Spec.Eps{}: Spec.Glob}, Shared.Bool.false_ne_true(h))
    case Spec.Lit{+x1} Spec.Lit{x2}:
      h => Equal.cong(Char, Spec.Glob, c => Spec.Lit{c}, x1, x2, Char.is_eq_sound(x1, x2)(h))
    case Spec.Lit{+x1} Spec.Any{}:
      h => Empty.absurd({Spec.Lit{x1} == Spec.Any{}: Spec.Glob}, Shared.Bool.false_ne_true(h))
    case Spec.Lit{+x1} Spec.Star{}:
      h => Empty.absurd({Spec.Lit{x1} == Spec.Star{}: Spec.Glob}, Shared.Bool.false_ne_true(h))
    case Spec.Lit{+x1} Spec.Class{n2, cs2}:
      h => Empty.absurd(
        {Spec.Lit{x1} == Spec.Class{n2, cs2}: Spec.Glob},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Lit{+x1} Spec.Deep{}:
      h => Empty.absurd({Spec.Lit{x1} == Spec.Deep{}: Spec.Glob}, Shared.Bool.false_ne_true(h))
    case Spec.Lit{+x1} Spec.Cat{a2, b2}:
      h => Empty.absurd({Spec.Lit{x1} == Spec.Cat{a2, b2}: Spec.Glob}, Shared.Bool.false_ne_true(h))
    case Spec.Lit{+x1} Spec.Alt{a2, b2}:
      h => Empty.absurd({Spec.Lit{x1} == Spec.Alt{a2, b2}: Spec.Glob}, Shared.Bool.false_ne_true(h))
    case Spec.Any{} Spec.Void{}:
      h => Empty.absurd({Spec.Any{} == Spec.Void{}: Spec.Glob}, Shared.Bool.false_ne_true(h))
    case Spec.Any{} Spec.Eps{}:
      h => Empty.absurd({Spec.Any{} == Spec.Eps{}: Spec.Glob}, Shared.Bool.false_ne_true(h))
    case Spec.Any{} Spec.Lit{x2}:
      h => Empty.absurd({Spec.Any{} == Spec.Lit{x2}: Spec.Glob}, Shared.Bool.false_ne_true(h))
    case Spec.Any{} Spec.Any{}:
      _ => {==}
    case Spec.Any{} Spec.Star{}:
      h => Empty.absurd({Spec.Any{} == Spec.Star{}: Spec.Glob}, Shared.Bool.false_ne_true(h))
    case Spec.Any{} Spec.Class{n2, cs2}:
      h => Empty.absurd(
        {Spec.Any{} == Spec.Class{n2, cs2}: Spec.Glob},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Any{} Spec.Deep{}:
      h => Empty.absurd({Spec.Any{} == Spec.Deep{}: Spec.Glob}, Shared.Bool.false_ne_true(h))
    case Spec.Any{} Spec.Cat{a2, b2}:
      h => Empty.absurd({Spec.Any{} == Spec.Cat{a2, b2}: Spec.Glob}, Shared.Bool.false_ne_true(h))
    case Spec.Any{} Spec.Alt{a2, b2}:
      h => Empty.absurd({Spec.Any{} == Spec.Alt{a2, b2}: Spec.Glob}, Shared.Bool.false_ne_true(h))
    case Spec.Star{} Spec.Void{}:
      h => Empty.absurd({Spec.Star{} == Spec.Void{}: Spec.Glob}, Shared.Bool.false_ne_true(h))
    case Spec.Star{} Spec.Eps{}:
      h => Empty.absurd({Spec.Star{} == Spec.Eps{}: Spec.Glob}, Shared.Bool.false_ne_true(h))
    case Spec.Star{} Spec.Lit{x2}:
      h => Empty.absurd({Spec.Star{} == Spec.Lit{x2}: Spec.Glob}, Shared.Bool.false_ne_true(h))
    case Spec.Star{} Spec.Any{}:
      h => Empty.absurd({Spec.Star{} == Spec.Any{}: Spec.Glob}, Shared.Bool.false_ne_true(h))
    case Spec.Star{} Spec.Star{}:
      _ => {==}
    case Spec.Star{} Spec.Class{n2, cs2}:
      h => Empty.absurd(
        {Spec.Star{} == Spec.Class{n2, cs2}: Spec.Glob},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Star{} Spec.Deep{}:
      h => Empty.absurd({Spec.Star{} == Spec.Deep{}: Spec.Glob}, Shared.Bool.false_ne_true(h))
    case Spec.Star{} Spec.Cat{a2, b2}:
      h => Empty.absurd({Spec.Star{} == Spec.Cat{a2, b2}: Spec.Glob}, Shared.Bool.false_ne_true(h))
    case Spec.Star{} Spec.Alt{a2, b2}:
      h => Empty.absurd({Spec.Star{} == Spec.Alt{a2, b2}: Spec.Glob}, Shared.Bool.false_ne_true(h))
    case Spec.Class{+n1, +cs1} Spec.Void{}:
      +h => Empty.absurd(
        {Spec.Class{n1, cs1} == Spec.Void{}: Spec.Glob},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Class{+n1, +cs1} Spec.Eps{}:
      +h => Empty.absurd(
        {Spec.Class{n1, cs1} == Spec.Eps{}: Spec.Glob},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Class{+n1, +cs1} Spec.Lit{x2}:
      +h => Empty.absurd(
        {Spec.Class{n1, cs1} == Spec.Lit{x2}: Spec.Glob},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Class{+n1, +cs1} Spec.Any{}:
      +h => Empty.absurd(
        {Spec.Class{n1, cs1} == Spec.Any{}: Spec.Glob},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Class{+n1, +cs1} Spec.Star{}:
      +h => Empty.absurd(
        {Spec.Class{n1, cs1} == Spec.Star{}: Spec.Glob},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Class{+n1, +cs1} Spec.Class{+n2, +cs2}:
      +h =>
        %Shared.Bool.is_eq_sound(
          n1,
          n2
        )(
          Shared.Bool.and_true_left(Shared.Bool.is_eq(n1, n2), Chars.is_eq(cs1, cs2))(h)
        ): {Spec.Class{n1, cs1} == Spec.Class{_, cs2}: Spec.Glob}
        %Chars.is_eq_sound(
          cs1,
          cs2
        )(
          Shared.Bool.and_true_right(Shared.Bool.is_eq(n1, n2), Chars.is_eq(cs1, cs2))(h)
        ): {Spec.Class{n1, cs1} == Spec.Class{n1, _}: Spec.Glob}
        {==}
    case Spec.Class{+n1, +cs1} Spec.Deep{}:
      +h => Empty.absurd(
        {Spec.Class{n1, cs1} == Spec.Deep{}: Spec.Glob},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Class{+n1, +cs1} Spec.Cat{a2, b2}:
      +h => Empty.absurd(
        {Spec.Class{n1, cs1} == Spec.Cat{a2, b2}: Spec.Glob},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Class{+n1, +cs1} Spec.Alt{a2, b2}:
      +h => Empty.absurd(
        {Spec.Class{n1, cs1} == Spec.Alt{a2, b2}: Spec.Glob},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Deep{} Spec.Void{}:
      h => Empty.absurd({Spec.Deep{} == Spec.Void{}: Spec.Glob}, Shared.Bool.false_ne_true(h))
    case Spec.Deep{} Spec.Eps{}:
      h => Empty.absurd({Spec.Deep{} == Spec.Eps{}: Spec.Glob}, Shared.Bool.false_ne_true(h))
    case Spec.Deep{} Spec.Lit{x2}:
      h => Empty.absurd({Spec.Deep{} == Spec.Lit{x2}: Spec.Glob}, Shared.Bool.false_ne_true(h))
    case Spec.Deep{} Spec.Any{}:
      h => Empty.absurd({Spec.Deep{} == Spec.Any{}: Spec.Glob}, Shared.Bool.false_ne_true(h))
    case Spec.Deep{} Spec.Star{}:
      h => Empty.absurd({Spec.Deep{} == Spec.Star{}: Spec.Glob}, Shared.Bool.false_ne_true(h))
    case Spec.Deep{} Spec.Class{n2, cs2}:
      h => Empty.absurd(
        {Spec.Deep{} == Spec.Class{n2, cs2}: Spec.Glob},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Deep{} Spec.Deep{}:
      _ => {==}
    case Spec.Deep{} Spec.Cat{a2, b2}:
      h => Empty.absurd({Spec.Deep{} == Spec.Cat{a2, b2}: Spec.Glob}, Shared.Bool.false_ne_true(h))
    case Spec.Deep{} Spec.Alt{a2, b2}:
      h => Empty.absurd({Spec.Deep{} == Spec.Alt{a2, b2}: Spec.Glob}, Shared.Bool.false_ne_true(h))
    case Spec.Cat{+a1, +b1} Spec.Void{}:
      +h => Empty.absurd({Spec.Cat{a1, b1} == Spec.Void{}: Spec.Glob}, Shared.Bool.false_ne_true(h))
    case Spec.Cat{+a1, +b1} Spec.Eps{}:
      +h => Empty.absurd({Spec.Cat{a1, b1} == Spec.Eps{}: Spec.Glob}, Shared.Bool.false_ne_true(h))
    case Spec.Cat{+a1, +b1} Spec.Lit{x2}:
      +h => Empty.absurd(
        {Spec.Cat{a1, b1} == Spec.Lit{x2}: Spec.Glob},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Cat{+a1, +b1} Spec.Any{}:
      +h => Empty.absurd({Spec.Cat{a1, b1} == Spec.Any{}: Spec.Glob}, Shared.Bool.false_ne_true(h))
    case Spec.Cat{+a1, +b1} Spec.Star{}:
      +h => Empty.absurd({Spec.Cat{a1, b1} == Spec.Star{}: Spec.Glob}, Shared.Bool.false_ne_true(h))
    case Spec.Cat{+a1, +b1} Spec.Class{n2, cs2}:
      +h => Empty.absurd(
        {Spec.Cat{a1, b1} == Spec.Class{n2, cs2}: Spec.Glob},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Cat{+a1, +b1} Spec.Deep{}:
      +h => Empty.absurd({Spec.Cat{a1, b1} == Spec.Deep{}: Spec.Glob}, Shared.Bool.false_ne_true(h))
    case Spec.Cat{+a1, +b1} Spec.Cat{+a2, +b2}:
      +h =>
        %Glob.is_eq_sound(
          a1,
          a2
        )(
          Shared.Bool.and_true_left(Glob.is_eq(a1, a2), Glob.is_eq(b1, b2))(h)
        ): {Spec.Cat{a1, b1} == Spec.Cat{_, b2}: Spec.Glob}
        %Glob.is_eq_sound(
          b1,
          b2
        )(
          Shared.Bool.and_true_right(Glob.is_eq(a1, a2), Glob.is_eq(b1, b2))(h)
        ): {Spec.Cat{a1, b1} == Spec.Cat{a1, _}: Spec.Glob}
        {==}
    case Spec.Cat{+a1, +b1} Spec.Alt{a2, b2}:
      +h => Empty.absurd(
        {Spec.Cat{a1, b1} == Spec.Alt{a2, b2}: Spec.Glob},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Alt{+a1, +b1} Spec.Void{}:
      +h => Empty.absurd({Spec.Alt{a1, b1} == Spec.Void{}: Spec.Glob}, Shared.Bool.false_ne_true(h))
    case Spec.Alt{+a1, +b1} Spec.Eps{}:
      +h => Empty.absurd({Spec.Alt{a1, b1} == Spec.Eps{}: Spec.Glob}, Shared.Bool.false_ne_true(h))
    case Spec.Alt{+a1, +b1} Spec.Lit{x2}:
      +h => Empty.absurd(
        {Spec.Alt{a1, b1} == Spec.Lit{x2}: Spec.Glob},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Alt{+a1, +b1} Spec.Any{}:
      +h => Empty.absurd({Spec.Alt{a1, b1} == Spec.Any{}: Spec.Glob}, Shared.Bool.false_ne_true(h))
    case Spec.Alt{+a1, +b1} Spec.Star{}:
      +h => Empty.absurd({Spec.Alt{a1, b1} == Spec.Star{}: Spec.Glob}, Shared.Bool.false_ne_true(h))
    case Spec.Alt{+a1, +b1} Spec.Class{n2, cs2}:
      +h => Empty.absurd(
        {Spec.Alt{a1, b1} == Spec.Class{n2, cs2}: Spec.Glob},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Alt{+a1, +b1} Spec.Deep{}:
      +h => Empty.absurd({Spec.Alt{a1, b1} == Spec.Deep{}: Spec.Glob}, Shared.Bool.false_ne_true(h))
    case Spec.Alt{+a1, +b1} Spec.Cat{a2, b2}:
      +h => Empty.absurd(
        {Spec.Alt{a1, b1} == Spec.Cat{a2, b2}: Spec.Glob},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Alt{+a1, +b1} Spec.Alt{+a2, +b2}:
      +h =>
        %Glob.is_eq_sound(
          a1,
          a2
        )(
          Shared.Bool.and_true_left(Glob.is_eq(a1, a2), Glob.is_eq(b1, b2))(h)
        ): {Spec.Alt{a1, b1} == Spec.Alt{_, b2}: Spec.Glob}
        %Glob.is_eq_sound(
          b1,
          b2
        )(
          Shared.Bool.and_true_right(Glob.is_eq(a1, a2), Glob.is_eq(b1, b2))(h)
        ): {Spec.Alt{a1, b1} == Spec.Alt{a1, _}: Spec.Glob}
        {==}
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# Matching algebra
# ----------------
# Each lemma states the simpler side first, so a rewrite with it turns a
# glob into its simpler meaning.

# a or False is a
def Bool.or_false(a: Bool) -> {a == Bool.or(a, False{}): Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

# a and True is a
def Bool.and_true(a: Bool) -> {a == Bool.and(a, True{}): Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

# a and False is False
def Bool.and_false(a: Bool) -> {False{} == Bool.and(a, False{}): Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

# Void matches nothing
def Glob.void_never(p: String) -> {False{} == Spec.Glob.matches(p, Spec.Void{}): Bool}:
  match p:
    case SNil{}:
      {==}
    case SCon{c, t}:
      Glob.void_never(t)

# Alt matches what either side matches
def Glob.alt_or(
  p: String,
  a: Spec.Glob,
  b: Spec.Glob
) -> {
  Bool.or(
    Spec.Glob.matches(p, a),
    Spec.Glob.matches(p, b)
  )
    == Spec.Glob.matches(p, Spec.Alt{a, b}): Bool
}:
  match p:
    case SNil{}:
      {==}
    case SCon{+c, t}:
      Glob.alt_or(t, Spec.Glob.step(a, c), Spec.Glob.step(b, c))

# Cat after Void matches nothing
def Glob.cat_void_l(
  p: String,
  +x: Spec.Glob
) -> {False{} == Spec.Glob.matches(p, Spec.Cat{Spec.Void{}, x}): Bool}:
  match p:
    case SNil{}:
      {==}
    case SCon{c, +t}:
      +x2 = Spec.Glob.step(x, c)
      %Glob.alt_or(t, Spec.Cat{Spec.Void{}, x}, Spec.Cat{Spec.Void{}, x2}): {False{} == _: Bool}
      %Glob.cat_void_l(
        t,
        x
      ): {False{} == Bool.or(_, Spec.Glob.matches(t, Spec.Cat{Spec.Void{}, x2})): Bool}
      Glob.cat_void_l(t, x2)

# Cat before Void matches nothing
def Glob.cat_void_r(
  p: String,
  +x: Spec.Glob
) -> {False{} == Spec.Glob.matches(p, Spec.Cat{x, Spec.Void{}}): Bool}:
  match p:
    case SNil{}:
      Bool.and_false(Spec.Glob.is_nullable(x))
    case SCon{c, +t}:
      +x2 = Spec.Glob.step(x, c)
      +n = Spec.Glob.of_bool(Spec.Glob.is_nullable(x))
      %Glob.alt_or(t, Spec.Cat{x2, Spec.Void{}}, Spec.Cat{n, Spec.Void{}}): {False{} == _: Bool}
      %Glob.cat_void_r(
        t,
        x2
      ): {False{} == Bool.or(_, Spec.Glob.matches(t, Spec.Cat{n, Spec.Void{}})): Bool}
      Glob.cat_void_r(t, n)

# Cat after Eps matches what its right side matches
def Glob.cat_eps_l(
  p: String,
  +x: Spec.Glob
) -> {Spec.Glob.matches(p, x) == Spec.Glob.matches(p, Spec.Cat{Spec.Eps{}, x}): Bool}:
  match p:
    case SNil{}:
      {==}
    case SCon{c, +t}:
      +x2 = Spec.Glob.step(x, c)
      %Glob.alt_or(
        t,
        Spec.Cat{Spec.Void{}, x},
        Spec.Cat{Spec.Eps{}, x2}
      ): {Spec.Glob.matches(t, x2) == _: Bool}
      %Glob.cat_void_l(
        t,
        x
      ): {
        Spec.Glob.matches(t, x2) == Bool.or(_, Spec.Glob.matches(t, Spec.Cat{Spec.Eps{}, x2})): Bool
      }
      Glob.cat_eps_l(t, x2)

# Cat before Eps matches what its left side matches
def Glob.cat_eps_r(
  p: String,
  +x: Spec.Glob
) -> {Spec.Glob.matches(p, x) == Spec.Glob.matches(p, Spec.Cat{x, Spec.Eps{}}): Bool}:
  match p:
    case SNil{}:
      Bool.and_true(Spec.Glob.is_nullable(x))
    case SCon{c, +t}:
      +x2 = Spec.Glob.step(x, c)
      +n = Spec.Glob.of_bool(Spec.Glob.is_nullable(x))
      %Glob.alt_or(
        t,
        Spec.Cat{x2, Spec.Eps{}},
        Spec.Cat{n, Spec.Void{}}
      ): {Spec.Glob.matches(t, x2) == _: Bool}
      %Glob.cat_void_r(
        t,
        n
      ): {
        Spec.Glob.matches(t, x2) == Bool.or(Spec.Glob.matches(t, Spec.Cat{x2, Spec.Eps{}}), _): Bool
      }
      %Bool.or_false(
        Spec.Glob.matches(t, Spec.Cat{x2, Spec.Eps{}})
      ): {Spec.Glob.matches(t, x2) == _: Bool}
      Glob.cat_eps_r(t, x2)

# and distributes over or, from the right
def Bool.distrib_r(
  a: Bool,
  b: Bool,
  r: Bool
) -> {Bool.or(Bool.and(a, r), Bool.and(b, r)) == Bool.and(Bool.or(a, b), r): Bool}:
  match a b r:
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

# and is associative
def Bool.and_assoc(
  a: Bool,
  b: Bool,
  r: Bool
) -> {Bool.and(a, Bool.and(b, r)) == Bool.and(Bool.and(a, b), r): Bool}:
  match a b r:
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

# the Bool shape of one step of Glob.cat_alt
def Bool.cat_alt_step(
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
    case False{} False{} False{} False{} False{}:
      {==}
    case False{} False{} False{} False{} True{}:
      {==}
    case False{} False{} False{} True{} False{}:
      {==}
    case False{} False{} False{} True{} True{}:
      {==}
    case False{} False{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{} False{}:
      {==}
    case False{} False{} True{} True{} True{}:
      {==}
    case False{} True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{} False{}:
      {==}
    case False{} True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} False{} False{}:
      {==}
    case False{} True{} True{} False{} True{}:
      {==}
    case False{} True{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{} True{}:
      {==}
    case True{} False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{} False{}:
      {==}
    case True{} False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} False{} False{}:
      {==}
    case True{} False{} True{} False{} True{}:
      {==}
    case True{} False{} True{} True{} False{}:
      {==}
    case True{} False{} True{} True{} True{}:
      {==}
    case True{} True{} False{} False{} False{}:
      {==}
    case True{} True{} False{} False{} True{}:
      {==}
    case True{} True{} False{} True{} False{}:
      {==}
    case True{} True{} False{} True{} True{}:
      {==}
    case True{} True{} True{} False{} False{}:
      {==}
    case True{} True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{} True{}:
      {==}

# the Bool shape of one step of Glob.cat_assoc
def Bool.cat_assoc_step(
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
  match x y a b z:
    case False{} False{} False{} False{} False{}:
      {==}
    case False{} False{} False{} False{} True{}:
      {==}
    case False{} False{} False{} True{} False{}:
      {==}
    case False{} False{} False{} True{} True{}:
      {==}
    case False{} False{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{} False{}:
      {==}
    case False{} False{} True{} True{} True{}:
      {==}
    case False{} True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{} False{}:
      {==}
    case False{} True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} False{} False{}:
      {==}
    case False{} True{} True{} False{} True{}:
      {==}
    case False{} True{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{} True{}:
      {==}
    case True{} False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{} False{}:
      {==}
    case True{} False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} False{} False{}:
      {==}
    case True{} False{} True{} False{} True{}:
      {==}
    case True{} False{} True{} True{} False{}:
      {==}
    case True{} False{} True{} True{} True{}:
      {==}
    case True{} True{} False{} False{} False{}:
      {==}
    case True{} True{} False{} False{} True{}:
      {==}
    case True{} True{} False{} True{} False{}:
      {==}
    case True{} True{} False{} True{} True{}:
      {==}
    case True{} True{} True{} False{} False{}:
      {==}
    case True{} True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{} True{}:
      {==}

# Cat after of_bool(b) matches what its right side matches, when b holds
def Glob.cat_of_bool(
  p: String,
  b: Bool,
  r: Spec.Glob
) -> {
  Bool.and(
    b,
    Spec.Glob.matches(p, r)
  )
    == Spec.Glob.matches(p, Spec.Cat{Spec.Glob.of_bool(b), r}): Bool
}:
  match b:
    case False{}:
      Glob.cat_void_l(p, r)
    case True{}:
      Glob.cat_eps_l(p, r)

# Cat after Alt matches what either Cat matches
def Glob.cat_alt(
  p: String,
  +a: Spec.Glob,
  +b: Spec.Glob,
  +r: Spec.Glob
) -> {
  Bool.or(
    Spec.Glob.matches(p, Spec.Cat{a, r}),
    Spec.Glob.matches(p, Spec.Cat{b, r})
  )
    == Spec.Glob.matches(p, Spec.Cat{Spec.Alt{a, b}, r}): Bool
}:
  match p:
    case SNil{}:
      Bool.distrib_r(Spec.Glob.is_nullable(a), Spec.Glob.is_nullable(b), Spec.Glob.is_nullable(r))
    case SCon{+c, +t}:
      +a2 = Spec.Glob.step(a, c)
      +b2 = Spec.Glob.step(b, c)
      +r2 = Spec.Glob.step(r, c)
      +na = Spec.Glob.is_nullable(a)
      +nb = Spec.Glob.is_nullable(b)
      +p1 = {Spec.Cat{a2, r}: Spec.Glob}
      q1 = {Spec.Cat{Spec.Glob.of_bool(na), r2}: Spec.Glob}
      +p2 = {Spec.Cat{b2, r}: Spec.Glob}
      q2 = {Spec.Cat{Spec.Glob.of_bool(nb), r2}: Spec.Glob}
      +ab = {Spec.Cat{Spec.Alt{a2, b2}, r}: Spec.Glob}
      +qab = {Spec.Cat{Spec.Glob.of_bool(Bool.or(na, nb)), r2}: Spec.Glob}
      +x = Spec.Glob.matches(t, p1)
      +y = Spec.Glob.matches(t, p2)
      +z = Spec.Glob.matches(t, r2)
      rhs = Spec.Glob.matches(t, Spec.Alt{ab, qab})
      %Glob.alt_or(t, p1, q1): {Bool.or(_, Spec.Glob.matches(t, Spec.Alt{p2, q2})) == rhs: Bool}
      %Glob.alt_or(t, p2, q2): {Bool.or(Bool.or(x, Spec.Glob.matches(t, q1)), _) == rhs: Bool}
      %Glob.cat_of_bool(
        t,
        na,
        r2
      ): {Bool.or(Bool.or(x, _), Bool.or(y, Spec.Glob.matches(t, q2))) == rhs: Bool}
      +l = Bool.or(Bool.or(x, Bool.and(na, z)), Bool.or(y, Bool.and(nb, z)))
      %Glob.cat_of_bool(
        t,
        nb,
        r2
      ): {Bool.or(Bool.or(x, Bool.and(na, z)), Bool.or(y, _)) == rhs: Bool}
      %Glob.alt_or(t, ab, qab): {l == _: Bool}
      %Glob.cat_alt(t, a2, b2, r): {l == Bool.or(_, Spec.Glob.matches(t, qab)): Bool}
      %Glob.cat_of_bool(t, Bool.or(na, nb), r2): {l == Bool.or(Bool.or(x, y), _): Bool}
      Bool.cat_alt_step(x, y, na, nb, z)

# Cat is associative
def Glob.cat_assoc(
  p: String,
  +a: Spec.Glob,
  +b: Spec.Glob,
  +r: Spec.Glob
) -> {
  Spec.Glob.matches(
    p,
    Spec.Cat{a, Spec.Cat{b, r}}
  )
    == Spec.Glob.matches(p, Spec.Cat{Spec.Cat{a, b}, r}): Bool
}:
  match p:
    case SNil{}:
      Bool.and_assoc(Spec.Glob.is_nullable(a), Spec.Glob.is_nullable(b), Spec.Glob.is_nullable(r))
    case SCon{+c, +t}:
      +a2 = Spec.Glob.step(a, c)
      +b2 = Spec.Glob.step(b, c)
      +r2 = Spec.Glob.step(r, c)
      +na = Spec.Glob.is_nullable(a)
      +nb = Spec.Glob.is_nullable(b)
      +x1 = {Spec.Cat{a2, Spec.Cat{b, r}}: Spec.Glob}
      +br = {Spec.Cat{b2, r}: Spec.Glob}
      +inner = {Spec.Alt{br, Spec.Cat{Spec.Glob.of_bool(nb), r2}}: Spec.Glob}
      q = {Spec.Cat{Spec.Glob.of_bool(na), inner}: Spec.Glob}
      +c1 = {Spec.Cat{a2, b}: Spec.Glob}
      +c2 = {Spec.Cat{Spec.Glob.of_bool(na), b2}: Spec.Glob}
      +qn = {Spec.Cat{Spec.Glob.of_bool(Bool.and(na, nb)), r2}: Spec.Glob}
      +x = Spec.Glob.matches(t, x1)
      +y = Spec.Glob.matches(t, br)
      +z = Spec.Glob.matches(t, r2)
      rhs = Spec.Glob.matches(t, Spec.Alt{Spec.Cat{Spec.Alt{c1, c2}, r}, qn})
      %Glob.alt_or(t, x1, q): {_ == rhs: Bool}
      %Glob.cat_of_bool(t, na, inner): {Bool.or(x, _) == rhs: Bool}
      %Glob.alt_or(
        t,
        br,
        Spec.Cat{Spec.Glob.of_bool(nb), r2}
      ): {Bool.or(x, Bool.and(na, _)) == rhs: Bool}
      %Glob.cat_of_bool(t, nb, r2): {Bool.or(x, Bool.and(na, Bool.or(y, _))) == rhs: Bool}
      +l = Bool.or(x, Bool.and(na, Bool.or(y, Bool.and(nb, z))))
      %Glob.alt_or(t, Spec.Cat{Spec.Alt{c1, c2}, r}, qn): {l == _: Bool}
      %Glob.cat_alt(t, c1, c2, r): {l == Bool.or(_, Spec.Glob.matches(t, qn)): Bool}
      %Glob.cat_assoc(
        t,
        a2,
        b,
        r
      ): {
        l
          == Bool.or(
            Bool.or(_, Spec.Glob.matches(t, Spec.Cat{c2, r})),
            Spec.Glob.matches(t, qn)
          ): Bool
      }
      %Glob.cat_assoc(
        t,
        Spec.Glob.of_bool(na),
        b2,
        r
      ): {l == Bool.or(Bool.or(x, _), Spec.Glob.matches(t, qn)): Bool}
      %Glob.cat_of_bool(t, na, br): {l == Bool.or(Bool.or(x, _), Spec.Glob.matches(t, qn)): Bool}
      %Glob.cat_of_bool(
        t,
        Bool.and(na, nb),
        r2
      ): {l == Bool.or(Bool.or(x, Bool.and(na, y)), _): Bool}
      Bool.cat_assoc_step(x, y, na, nb, z)

# or is associative
def Bool.or_assoc(
  a: Bool,
  b: Bool,
  c: Bool
) -> {Bool.or(a, Bool.or(b, c)) == Bool.or(Bool.or(a, b), c): Bool}:
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

# Partial derivatives
# -------------------
# A Seq is globs one after another; a set of Seqs matches what any of them
# matches. After a character, a Seq becomes a set of Seqs whose parts are
# parts of the original glob, so a search over them meets finitely many.

# the glob of the parts of s, one after another
def Seq.glob(s: List<&2, Spec.Glob>) -> Spec.Glob:
  match s:
    case Nil{}:
      Spec.Eps{}
    case Con{h, t}:
      Spec.Cat{h, Seq.glob(t)}

# some Seq of xs matches p
# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- it works on a glob, a search state or a character list of a few items, so the extra call is short
def Seqs.matches(+p: String, xs: List<&2, List<&2, Spec.Glob>>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(Spec.Glob.matches(p, Seq.glob(h)), Seqs.matches(p, t))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# xs then ys matches what xs or ys matches
# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- a false positive, as the rule notes: the other use is an erased argument (of Equal.sym or a motive)
# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- only proofs use it; no program runs it
def Seqs.matches_append(
  +p: String,
  xs: List<&2, List<&2, Spec.Glob>>,
  +ys: List<&2, List<&2, Spec.Glob>>
) -> {
  Bool.or(
    Seqs.matches(p, xs),
    Seqs.matches(p, ys)
  )
    == Seqs.matches(p, List.append(&2, List<&2, Spec.Glob>, xs, ys)): Bool
}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, +t}:
      m = Spec.Glob.matches(p, Seq.glob(h))
      %Seqs.matches_append(
        p,
        t,
        ys
      ): {Bool.or(Bool.or(m, Seqs.matches(p, t)), Seqs.matches(p, ys)) == Bool.or(m, _): Bool}
      Equal.sym(
        Bool,
        Bool.or(m, Bool.or(Seqs.matches(p, t), Seqs.matches(p, ys))),
        Bool.or(Bool.or(m, Seqs.matches(p, t)), Seqs.matches(p, ys)),
        Bool.or_assoc(m, Seqs.matches(p, t), Seqs.matches(p, ys))
      )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# [r] when hit, else []
def Seq.keep(hit: Bool, r: List<&2, Spec.Glob>) -> List<&2, List<&2, Spec.Glob>>:
  match hit:
    case False{}:
      []
    case True{}:
      [r]

# the Seqs that h then r becomes after c, given k: what r becomes after c
# bend-lint: expect-begin bend-lint-rules/performance/missed_fork@hint -- a glob tree is a few nodes, where a fork costs more than it saves
def Seq.step.head(
  h: Spec.Glob,
  +r: List<&2, Spec.Glob>,
  +c: Char,
  +k: List<&2, List<&2, Spec.Glob>>
) -> List<&2, List<&2, Spec.Glob>>:
  match h:
    case Spec.Void{}:
      []
    case Spec.Eps{}:
      k
    case Spec.Lit{x}:
      Seq.keep(Char.is_eq(x, c), r)
    case Spec.Any{}:
      Seq.keep(Spec.is_inner(c), r)
    case Spec.Star{}:
      List.append(&2, List<&2, Spec.Glob>, Seq.keep(Spec.is_inner(c), Con{Spec.Star{}, r}), k)
    case Spec.Class{neg, cs}:
      hit = Bool.xor(neg, List.contains(~Char, ~Char.is_eq, cs, c))
      Seq.keep(Bool.and(Spec.is_inner(c), hit), r)
    case Spec.Deep{}:
      Con{Con{Spec.Deep{}, r}, k}
    case Spec.Cat{a, +b}:
      Seq.step.head(a, Con{b, r}, c, Seq.step.head(b, r, c, k))
    case Spec.Alt{a, b}:
      List.append(&2, List<&2, Spec.Glob>, Seq.step.head(a, r, c, k), Seq.step.head(b, r, c, k))
# bend-lint: expect-end bend-lint-rules/performance/missed_fork@hint

# the Seqs that s becomes after c
def Seq.step(s: List<&2, Spec.Glob>, +c: Char) -> List<&2, List<&2, Spec.Glob>>:
  match s:
    case Nil{}:
      []
    case Con{h, +t}:
      Seq.step.head(h, t, c, Seq.step(t, c))

# Seq.keep(hit, r) matches t when hit holds and r matches t
def Seq.keep_ok(
  +hit: Bool,
  t: String,
  r: List<&2, Spec.Glob>
) -> {
  Seqs.matches(
    t,
    Seq.keep(hit, r)
  )
    == Bool.or(Bool.and(hit, Spec.Glob.matches(t, Seq.glob(r))), False{}): Bool
}:
  match hit:
    case False{}:
      {==}
    case True{}:
      {==}

# a head that reads one character: after c it is of_bool(hit), then r
def Seq.step_head_one(
  +hit: Bool,
  +r: List<&2, Spec.Glob>,
  c: Char,
  +t: String
) -> {
  Seqs.matches(
    t,
    Seq.keep(hit, r)
  )
    == Spec.Glob.matches(
      t,
      Spec.Alt{
        Spec.Cat{Spec.Glob.of_bool(hit), Seq.glob(r)},
        Spec.Cat{Spec.Void{}, Spec.Glob.step(Seq.glob(r), c)}
      }
    ): Bool
}:
  +g = Seq.glob(r)
  +g2 = Spec.Glob.step(g, c)
  l = Seqs.matches(t, Seq.keep(hit, r))
  %Glob.alt_or(t, Spec.Cat{Spec.Glob.of_bool(hit), g}, Spec.Cat{Spec.Void{}, g2}): {l == _: Bool}
  %Glob.cat_of_bool(
    t,
    hit,
    g
  ): {l == Bool.or(_, Spec.Glob.matches(t, Spec.Cat{Spec.Void{}, g2})): Bool}
  %Glob.cat_void_l(t, g2): {l == Bool.or(Bool.and(hit, Spec.Glob.matches(t, g)), _): Bool}
  Seq.keep_ok(hit, t, r)

# Seq.step.head(h, r, c, k) matches t when h then r matches c then t,
# given that k matches t when r matches c then t
# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- only proofs use it; no program runs it
def Seq.step_head_ok(
  h: Spec.Glob,
  +r: List<&2, Spec.Glob>,
  +c: Char,
  +t: String,
  +k: List<&2, List<&2, Spec.Glob>>,
  +hk: {Seqs.matches(t, k) == Spec.Glob.matches(SCon{c, t}, Seq.glob(r)): Bool}
) -> {
  Seqs.matches(
    t,
    Seq.step.head(h, r, c, k)
  )
    == Spec.Glob.matches(SCon{c, t}, Spec.Cat{h, Seq.glob(r)}): Bool
}:
  match h:
    case Spec.Void{}:
      g = Seq.glob(r)
      Glob.cat_void_l(SCon{c, t}, g)
    case Spec.Eps{}:
      g = Seq.glob(r)
      %Glob.cat_eps_l(SCon{c, t}, g): {Seqs.matches(t, k) == _: Bool}
      hk
    case Spec.Lit{x}:
      Seq.step_head_one(Char.is_eq(x, c), r, c, t)
    case Spec.Any{}:
      Seq.step_head_one(Spec.is_inner(c), r, c, t)
    case Spec.Star{}:
      +i = Spec.is_inner(c)
      +s = {Con{Spec.Star{}, r}: List<&2, Spec.Glob>}
      +g = Seq.glob(r)
      +g2 = Spec.Glob.step(g, c)
      +m = Spec.Glob.matches(t, Spec.Cat{Spec.Star{}, g})
      sk = Seqs.matches(t, k)
      +cs = {Spec.Cat{Spec.Cat{Spec.Glob.of_bool(i), Spec.Star{}}, g}: Spec.Glob}
      rhs = Spec.Glob.matches(t, Spec.Alt{cs, Spec.Cat{Spec.Eps{}, g2}})
      %Seqs.matches_append(t, Seq.keep(i, s), k): {_ == rhs: Bool}
      %Equal.sym(
        Bool,
        Seqs.matches(t, Seq.keep(i, s)),
        Bool.or(Bool.and(i, m), False{}),
        Seq.keep_ok(i, t, s)
      ): {Bool.or(_, sk) == rhs: Bool}
      %Bool.or_false(Bool.and(i, m)): {Bool.or(_, sk) == rhs: Bool}
      +l = Bool.or(Bool.and(i, m), sk)
      %Glob.alt_or(t, cs, Spec.Cat{Spec.Eps{}, g2}): {l == _: Bool}
      %Glob.cat_assoc(
        t,
        Spec.Glob.of_bool(i),
        Spec.Star{},
        g
      ): {l == Bool.or(_, Spec.Glob.matches(t, Spec.Cat{Spec.Eps{}, g2})): Bool}
      %Glob.cat_of_bool(
        t,
        i,
        Spec.Cat{Spec.Star{}, g}
      ): {l == Bool.or(_, Spec.Glob.matches(t, Spec.Cat{Spec.Eps{}, g2})): Bool}
      %Glob.cat_eps_l(t, g2): {l == Bool.or(Bool.and(i, m), _): Bool}
      %hk: {l == Bool.or(Bool.and(i, m), _): Bool}
      {==}
    case Spec.Class{neg, cs}:
      hit = Bool.xor(neg, List.contains(~Char, ~Char.is_eq, cs, c))
      Seq.step_head_one(Bool.and(Spec.is_inner(c), hit), r, c, t)
    case Spec.Deep{}:
      +g = Seq.glob(r)
      +g2 = Spec.Glob.step(g, c)
      l = Seqs.matches(t, Con{Con{Spec.Deep{}, r}, k})
      %Glob.alt_or(t, Spec.Cat{Spec.Deep{}, g}, Spec.Cat{Spec.Eps{}, g2}): {l == _: Bool}
      %Glob.cat_eps_l(
        t,
        g2
      ): {l == Bool.or(Spec.Glob.matches(t, Spec.Cat{Spec.Deep{}, g}), _): Bool}
      %hk: {l == Bool.or(Spec.Glob.matches(t, Spec.Cat{Spec.Deep{}, g}), _): Bool}
      {==}
    case Spec.Cat{+a, +b}:
      g = Seq.glob(r)
      kb = Seq.step.head(b, r, c, k)
      hb = Seq.step_head_ok(b, r, c, t, k, hk)
      %Glob.cat_assoc(
        SCon{c, t},
        a,
        b,
        g
      ): {Seqs.matches(t, Seq.step.head(a, Con{b, r}, c, kb)) == _: Bool}
      Seq.step_head_ok(a, Con{b, r}, c, t, kb, hb)
    case Spec.Alt{+a, +b}:
      g = Seq.glob(r)
      +ka = Seq.step.head(a, r, c, k)
      +kb = Seq.step.head(b, r, c, k)
      l = Bool.or(Seqs.matches(t, ka), Seqs.matches(t, kb))
      %Seqs.matches_append(
        t,
        ka,
        kb
      ): {_ == Spec.Glob.matches(SCon{c, t}, Spec.Cat{Spec.Alt{a, b}, g}): Bool}
      %Glob.cat_alt(SCon{c, t}, a, b, g): {l == _: Bool}
      %Seq.step_head_ok(
        a,
        r,
        c,
        t,
        k,
        hk
      ): {l == Bool.or(_, Spec.Glob.matches(SCon{c, t}, Spec.Cat{b, g})): Bool}
      %Seq.step_head_ok(b, r, c, t, k, hk): {l == Bool.or(Seqs.matches(t, ka), _): Bool}
      {==}
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# a second a changes nothing
def Bool.or_absorb(a: Bool, r: Bool) -> {Bool.or(a, Bool.or(a, r)) == Bool.or(a, r): Bool}:
  match a r:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

# the first two of three or-ed values can swap
def Bool.or_swap(
  a: Bool,
  b: Bool,
  r: Bool
) -> {Bool.or(a, Bool.or(b, r)) == Bool.or(b, Bool.or(a, r)): Bool}:
  match a b r:
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

# Seq.step(s, c) matches t when s matches c then t
def Seq.step_ok(
  s: List<&2, Spec.Glob>,
  +c: Char,
  +t: String
) -> {Seqs.matches(t, Seq.step(s, c)) == Spec.Glob.matches(SCon{c, t}, Seq.glob(s)): Bool}:
  match s:
    case Nil{}:
      Glob.void_never(t)
    case Con{h, +r}:
      Seq.step_head_ok(h, r, c, t, Seq.step(r, c), Seq.step_ok(r, c, t))

# xs and ys are the same globs
# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- it works on a glob, a search state or a character list of a few items, so the extra call is short
def Seq.is_eq(xs: List<&2, Spec.Glob>, ys: List<&2, Spec.Glob>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{x, xt} Con{y, yt}:
      Bool.and(Glob.is_eq(x, y), Seq.is_eq(xt, yt))
    case _ _:
      False{}
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# Seq.is_eq is True only for the same globs
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- only proofs use it; no program runs it
def Seq.is_eq_sound(
  xs: List<&2, Spec.Glob>,
  ys: List<&2, Spec.Glob>
) -> {Seq.is_eq(xs, ys) == True{}: Bool} -> {xs == ys: List<&2, Spec.Glob>}:
  match xs ys:
    case Nil{} Nil{}:
      _ => {==}
    case Nil{} Con{y, yt}:
      h => Empty.absurd({Nil{} == Con{y, yt}: List<&2, Spec.Glob>}, Shared.Bool.false_ne_true(h))
    case Con{x, xt} Nil{}:
      h => Empty.absurd({Con{x, xt} == Nil{}: List<&2, Spec.Glob>}, Shared.Bool.false_ne_true(h))
    case Con{+x, +xt} Con{+y, +yt}:
      +h =>
        %Glob.is_eq_sound(x, y)(Shared.Bool.and_true_left(Glob.is_eq(x, y), Seq.is_eq(xt, yt))(h)):
          {Con{x, xt} == Con{_, yt}: List<&2, Spec.Glob>}
        %Seq.is_eq_sound(
          xt,
          yt
        )(Shared.Bool.and_true_right(Glob.is_eq(x, y), Seq.is_eq(xt, yt))(h)):
          {Con{x, xt} == Con{x, _}: List<&2, Spec.Glob>}
        {==}
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# xs holds x
# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- it works on a glob, a search state or a character list of a few items, so the extra call is short
def Seqs.has(xs: List<&2, List<&2, Spec.Glob>>, +x: List<&2, Spec.Glob>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(Seq.is_eq(h, x), Seqs.has(t, x))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# one step of Seqs.has_absorb, with e the answer of Seq.is_eq(hd, x)
def Seqs.has_absorb.at(
  +hd: List<&2, Spec.Glob>,
  r: List<&2, List<&2, Spec.Glob>>,
  x: List<&2, Spec.Glob>,
  +t: String,
  e: Bool,
  ih: {
    Seqs.has(r, x) == True{}: Bool
  } -> {Seqs.matches(t, r) == Bool.or(Spec.Glob.matches(t, Seq.glob(x)), Seqs.matches(t, r)): Bool}
) -> {
  Seq.is_eq(hd, x) == e: Bool
} -> {
  Bool.or(e, Seqs.has(r, x)) == True{}: Bool
} -> {
  Seqs.matches(
    t,
    Con{hd, r}
  )
    == Bool.or(Spec.Glob.matches(t, Seq.glob(x)), Seqs.matches(t, Con{hd, r})): Bool
}:
  match e:
    case True{}:
      eq => h =>
        +mh = Spec.Glob.matches(t, Seq.glob(hd))
        +sr = Seqs.matches(t, r)
        %Seq.is_eq_sound(
          hd,
          x
        )(
          eq
        ): {Bool.or(mh, sr) == Bool.or(Spec.Glob.matches(t, Seq.glob(_)), Bool.or(mh, sr)): Bool}
        Equal.sym(Bool, Bool.or(mh, Bool.or(mh, sr)), Bool.or(mh, sr), Bool.or_absorb(mh, sr))
    case False{}:
      eq => h =>
        +mh = Spec.Glob.matches(t, Seq.glob(hd))
        +sr = Seqs.matches(t, r)
        +mx = Spec.Glob.matches(t, Seq.glob(x))
        %Bool.or_swap(mh, mx, sr): {Bool.or(mh, sr) == _: Bool}
        %ih(h): {Bool.or(mh, sr) == Bool.or(mh, _): Bool}
        {==}

# a Seq that xs holds adds nothing to what xs matches
def Seqs.has_absorb(
  xs: List<&2, List<&2, Spec.Glob>>,
  +x: List<&2, Spec.Glob>,
  +t: String
) -> {
  Seqs.has(xs, x) == True{}: Bool
} -> {Seqs.matches(t, xs) == Bool.or(Spec.Glob.matches(t, Seq.glob(x)), Seqs.matches(t, xs)): Bool}:
  match xs:
    case Nil{}:
      h => Empty.absurd(
        {False{} == Bool.or(Spec.Glob.matches(t, Seq.glob(x)), False{}): Bool},
        Shared.Bool.false_ne_true(h)
      )
    case Con{+hd, +r}:
      h => Seqs.has_absorb.at(hd, r, x, t, Seq.is_eq(hd, x), Seqs.has_absorb(r, x, t))({==}, h)

# xs when has, else x before xs
def Seqs.add.if(
  x: List<&2, Spec.Glob>,
  xs: List<&2, List<&2, Spec.Glob>>,
  has: Bool
) -> List<&2, List<&2, Spec.Glob>>:
  match has:
    case False{}:
      Con{x, xs}
    case True{}:
      xs

# xs with x, once
def Seqs.add(
  +x: List<&2, Spec.Glob>,
  +xs: List<&2, List<&2, Spec.Glob>>
) -> List<&2, List<&2, Spec.Glob>>:
  Seqs.add.if(x, xs, Seqs.has(xs, x))

# Seqs.add_ok, given b, the answer of Seqs.has(xs, x)
# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- a false positive, as the rule notes: the other use is an erased argument (of Equal.sym or a motive)
# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- only proofs use it; no program runs it
def Seqs.add_ok.at(
  x: List<&2, Spec.Glob>,
  xs: List<&2, List<&2, Spec.Glob>>,
  t: String,
  b: Bool
) -> {
  Seqs.has(xs, x) == b: Bool
} -> {
  Bool.or(
    Spec.Glob.matches(t, Seq.glob(x)),
    Seqs.matches(t, xs)
  )
    == Seqs.matches(t, Seqs.add.if(x, xs, b)): Bool
}:
  match b:
    case False{}:
      e => {==}
    case True{}:
      e => Equal.sym(
        Bool,
        Seqs.matches(t, xs),
        Bool.or(Spec.Glob.matches(t, Seq.glob(x)), Seqs.matches(t, xs)),
        Seqs.has_absorb(xs, x, t)(e)
      )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# Seqs.add(x, xs) matches what x or xs matches
def Seqs.add_ok(
  +x: List<&2, Spec.Glob>,
  +xs: List<&2, List<&2, Spec.Glob>>,
  t: String
) -> {
  Bool.or(
    Spec.Glob.matches(t, Seq.glob(x)),
    Seqs.matches(t, xs)
  )
    == Seqs.matches(t, Seqs.add(x, xs)): Bool
}:
  Seqs.add_ok.at(x, xs, t, Seqs.has(xs, x))({==})

# acc with each Seq of ys, once
def Seqs.add_all(
  ys: List<&2, List<&2, Spec.Glob>>,
  acc: List<&2, List<&2, Spec.Glob>>
) -> List<&2, List<&2, Spec.Glob>>:
  match ys:
    case Nil{}:
      acc
    case Con{y, r}:
      Seqs.add(y, Seqs.add_all(r, acc))

# Seqs.add_all(ys, acc) matches what ys or acc matches
# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- only proofs use it; no program runs it
def Seqs.add_all_ok(
  ys: List<&2, List<&2, Spec.Glob>>,
  +acc: List<&2, List<&2, Spec.Glob>>,
  +t: String
) -> {
  Bool.or(Seqs.matches(t, ys), Seqs.matches(t, acc)) == Seqs.matches(t, Seqs.add_all(ys, acc)): Bool
}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +r}:
      +my = Spec.Glob.matches(t, Seq.glob(y))
      l = Bool.or(Bool.or(my, Seqs.matches(t, r)), Seqs.matches(t, acc))
      %Seqs.add_ok(y, Seqs.add_all(r, acc), t): {l == _: Bool}
      %Seqs.add_all_ok(r, acc, t): {l == Bool.or(my, _): Bool}
      Equal.sym(
        Bool,
        Bool.or(my, Bool.or(Seqs.matches(t, r), Seqs.matches(t, acc))),
        l,
        Bool.or_assoc(my, Seqs.matches(t, r), Seqs.matches(t, acc))
      )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the Seqs that xs become after c
def Seqs.step(xs: List<&2, List<&2, Spec.Glob>>, +c: Char) -> List<&2, List<&2, Spec.Glob>>:
  match xs:
    case Nil{}:
      []
    case Con{x, r}:
      Seqs.add_all(Seq.step(x, c), Seqs.step(r, c))

# Seqs.step(xs, c) matches t when xs matches c then t
# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- only proofs use it; no program runs it
def Seqs.step_ok(
  xs: List<&2, List<&2, Spec.Glob>>,
  +c: Char,
  +t: String
) -> {Seqs.matches(t, Seqs.step(xs, c)) == Seqs.matches(SCon{c, t}, xs): Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      +a = Seq.step(x, c)
      +b = Seqs.step(r, c)
      %Seqs.add_all_ok(a, b, t): {_ == Seqs.matches(SCon{c, t}, Con{x, r}): Bool}
      +l = Bool.or(Seqs.matches(t, a), Seqs.matches(t, b))
      %Seq.step_ok(x, c, t): {l == Bool.or(_, Seqs.matches(SCon{c, t}, r)): Bool}
      %Seqs.step_ok(r, c, t): {l == Bool.or(Seqs.matches(t, a), _): Bool}
      {==}
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# Rules as derivative sets
# ------------------------

# bend-lint: expect-begin bend-lint-rules/layout/case@warning -- a constructor is PascalCase, as in Base (Some, Con): the rule reads a constructor as a law
# A rule whose glob is a set of Seqs.
type Slot is Data:
  Inc{xs: List<&2, List<&2, Spec.Glob>>}
  Exc{xs: List<&2, List<&2, Spec.Glob>>}
# bend-lint: expect-end bend-lint-rules/layout/case@warning

# the answer for p after slots, given the answer acc before them
def Slot.selects.go(slots: List<&2, Slot>, +p: String, acc: Bool) -> Bool:
  match slots acc:
    case Nil{} _:
      acc
    case Con{Inc{xs}, t} False{}:
      Slot.selects.go(t, p, Seqs.matches(p, xs))
    case Con{Inc{xs}, t} True{}:
      Slot.selects.go(t, p, True{})
    case Con{Exc{xs}, t} False{}:
      Slot.selects.go(t, p, False{})
    case Con{Exc{xs}, t} True{}:
      Slot.selects.go(t, p, Bool.not(Seqs.matches(p, xs)))

# the slots of rules
def Slot.of_rules(rules: List<&2, Spec.Rule>) -> List<&2, Slot>:
  match rules:
    case Nil{}:
      Nil{}
    case Con{Spec.Include{g}, t}:
      Con{Inc{[[g]]}, Slot.of_rules(t)}
    case Con{Spec.Exclude{g}, t}:
      Con{Exc{[[g]]}, Slot.of_rules(t)}

# the slots after c
def Slot.step(slots: List<&2, Slot>, +c: Char) -> List<&2, Slot>:
  match slots:
    case Nil{}:
      Nil{}
    case Con{Inc{xs}, t}:
      Con{Inc{Seqs.step(xs, c)}, Slot.step(t, c)}
    case Con{Exc{xs}, t}:
      Con{Exc{Seqs.step(xs, c)}, Slot.step(t, c)}

# the one-Seq set of g matches what g matches
def Seqs.single_ok(
  +p: String,
  +g: Spec.Glob
) -> {Spec.Glob.matches(p, g) == Seqs.matches(p, [[g]]): Bool}:
  %Bool.or_false(
    Spec.Glob.matches(p, Spec.Cat{g, Spec.Eps{}})
  ): {Spec.Glob.matches(p, g) == _: Bool}
  Glob.cat_eps_r(p, g)

# rules and their slots select the same paths
def Slot.of_rules_ok(
  rules: List<&2, Spec.Rule>,
  +p: String,
  acc: Bool
) -> {Spec.Rule.selects.go(rules, p, acc) == Slot.selects.go(Slot.of_rules(rules), p, acc): Bool}:
  match rules acc:
    case Nil{} _:
      {==}
    case Con{Spec.Include{+g}, t} False{}:
      %Seqs.single_ok(
        p,
        g
      ): {
        Spec.Rule.selects.go(
          t,
          p,
          Spec.Glob.matches(p, g)
        )
          == Slot.selects.go(Slot.of_rules(t), p, _): Bool
      }
      Slot.of_rules_ok(t, p, Spec.Glob.matches(p, g))
    case Con{Spec.Include{g}, t} True{}:
      Slot.of_rules_ok(t, p, True{})
    case Con{Spec.Exclude{g}, t} False{}:
      Slot.of_rules_ok(t, p, False{})
    case Con{Spec.Exclude{+g}, +t} True{}:
      %Seqs.single_ok(
        p,
        g
      ): {
        Spec.Rule.selects.go(
          t,
          p,
          Bool.not(Spec.Glob.matches(p, g))
        )
          == Slot.selects.go(Slot.of_rules(t), p, Bool.not(_)): Bool
      }
      Slot.of_rules_ok(t, p, Bool.not(Spec.Glob.matches(p, g)))

# slots select c then t when their step after c selects t
def Slot.step_ok(
  slots: List<&2, Slot>,
  +c: Char,
  +t: String,
  acc: Bool
) -> {
  Slot.selects.go(Slot.step(slots, c), t, acc) == Slot.selects.go(slots, SCon{c, t}, acc): Bool
}:
  match slots acc:
    case Nil{} _:
      {==}
    case Con{Inc{+xs}, r} False{}:
      %Seqs.step_ok(
        xs,
        c,
        t
      ): {
        Slot.selects.go(
          Slot.step(r, c),
          t,
          Seqs.matches(t, Seqs.step(xs, c))
        )
          == Slot.selects.go(r, SCon{c, t}, _): Bool
      }
      Slot.step_ok(r, c, t, Seqs.matches(t, Seqs.step(xs, c)))
    case Con{Inc{xs}, r} True{}:
      Slot.step_ok(r, c, t, True{})
    case Con{Exc{xs}, r} False{}:
      Slot.step_ok(r, c, t, False{})
    case Con{Exc{+xs}, +r} True{}:
      %Seqs.step_ok(
        xs,
        c,
        t
      ): {
        Slot.selects.go(
          Slot.step(r, c),
          t,
          Bool.not(Seqs.matches(t, Seqs.step(xs, c)))
        )
          == Slot.selects.go(r, SCon{c, t}, Bool.not(_)): Bool
      }
      Slot.step_ok(r, c, t, Bool.not(Seqs.matches(t, Seqs.step(xs, c))))

# Search states
# -------------

# xs and ys are the same Seqs
# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- it works on a glob, a search state or a character list of a few items, so the extra call is short
def Seqs.is_eq(xs: List<&2, List<&2, Spec.Glob>>, ys: List<&2, List<&2, Spec.Glob>>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{x, xt} Con{y, yt}:
      Bool.and(Seq.is_eq(x, y), Seqs.is_eq(xt, yt))
    case _ _:
      False{}
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# Seqs.is_eq is True only for the same Seqs
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- only proofs use it; no program runs it
def Seqs.is_eq_sound(
  xs: List<&2, List<&2, Spec.Glob>>,
  ys: List<&2, List<&2, Spec.Glob>>
) -> {Seqs.is_eq(xs, ys) == True{}: Bool} -> {xs == ys: List<&2, List<&2, Spec.Glob>>}:
  match xs ys:
    case Nil{} Nil{}:
      _ => {==}
    case Nil{} Con{y, yt}:
      h => Empty.absurd(
        {Nil{} == Con{y, yt}: List<&2, List<&2, Spec.Glob>>},
        Shared.Bool.false_ne_true(h)
      )
    case Con{x, xt} Nil{}:
      h => Empty.absurd(
        {Con{x, xt} == Nil{}: List<&2, List<&2, Spec.Glob>>},
        Shared.Bool.false_ne_true(h)
      )
    case Con{+x, +xt} Con{+y, +yt}:
      +h =>
        %Seq.is_eq_sound(x, y)(Shared.Bool.and_true_left(Seq.is_eq(x, y), Seqs.is_eq(xt, yt))(h)):
          {Con{x, xt} == Con{_, yt}: List<&2, List<&2, Spec.Glob>>}
        %Seqs.is_eq_sound(
          xt,
          yt
        )(Shared.Bool.and_true_right(Seq.is_eq(x, y), Seqs.is_eq(xt, yt))(h)):
          {Con{x, xt} == Con{x, _}: List<&2, List<&2, Spec.Glob>>}
        {==}
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# a and b are the same slots
# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- it works on a glob, a search state or a character list of a few items, so the extra call is short
def Slots.is_eq(a: List<&2, Slot>, b: List<&2, Slot>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Con{Inc{x}, at} Con{Inc{y}, bt}:
      Bool.and(Seqs.is_eq(x, y), Slots.is_eq(at, bt))
    case Con{Exc{x}, at} Con{Exc{y}, bt}:
      Bool.and(Seqs.is_eq(x, y), Slots.is_eq(at, bt))
    case _ _:
      False{}
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# Slots.is_eq is True only for the same slots
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- only proofs use it; no program runs it
def Slots.is_eq_sound(
  a: List<&2, Slot>,
  b: List<&2, Slot>
) -> {Slots.is_eq(a, b) == True{}: Bool} -> {a == b: List<&2, Slot>}:
  match a b:
    case Nil{} Nil{}:
      _ => {==}
    case Nil{} Con{y, bt}:
      h => Empty.absurd({Nil{} == Con{y, bt}: List<&2, Slot>}, Shared.Bool.false_ne_true(h))
    case Con{x, at} Nil{}:
      h => Empty.absurd({Con{x, at} == Nil{}: List<&2, Slot>}, Shared.Bool.false_ne_true(h))
    case Con{Inc{x}, at} Con{Exc{y}, bt}:
      h => Empty.absurd(
        {Con{Inc{x}, at} == Con{Exc{y}, bt}: List<&2, Slot>},
        Shared.Bool.false_ne_true(h)
      )
    case Con{Exc{x}, at} Con{Inc{y}, bt}:
      h => Empty.absurd(
        {Con{Exc{x}, at} == Con{Inc{y}, bt}: List<&2, Slot>},
        Shared.Bool.false_ne_true(h)
      )
    case Con{Inc{+x}, +at} Con{Inc{+y}, +bt}:
      +h =>
        %Seqs.is_eq_sound(
          x,
          y
        )(Shared.Bool.and_true_left(Seqs.is_eq(x, y), Slots.is_eq(at, bt))(h)):
          {Con{Inc{x}, at} == Con{Inc{_}, bt}: List<&2, Slot>}
        %Slots.is_eq_sound(
          at,
          bt
        )(Shared.Bool.and_true_right(Seqs.is_eq(x, y), Slots.is_eq(at, bt))(h)):
          {Con{Inc{x}, at} == Con{Inc{x}, _}: List<&2, Slot>}
        {==}
    case Con{Exc{+x}, +at} Con{Exc{+y}, +bt}:
      +h =>
        %Seqs.is_eq_sound(
          x,
          y
        )(Shared.Bool.and_true_left(Seqs.is_eq(x, y), Slots.is_eq(at, bt))(h)):
          {Con{Exc{x}, at} == Con{Exc{_}, bt}: List<&2, Slot>}
        %Slots.is_eq_sound(
          at,
          bt
        )(Shared.Bool.and_true_right(Seqs.is_eq(x, y), Slots.is_eq(at, bt))(h)):
          {Con{Exc{x}, at} == Con{Exc{x}, _}: List<&2, Slot>}
        {==}
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# A search state: the slots of both rule lists. both: the query asks for a
# path that b selects too; else, one that b does not select.
type St is Data:
  St{both: Bool, a: List<&2, Slot>, b: List<&2, Slot>}

# v when both, else not v
def St.side(both: Bool, v: Bool) -> Bool:
  match both:
    case False{}:
      Bool.not(v)
    case True{}:
      v

# p answers the query of state x
# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- it works on a glob, a search state or a character list of a few items, so the extra call is short
def St.holds(x: St, +p: String) -> Bool:
  match x:
    case St{both, a, b}:
      Bool.and(Slot.selects.go(a, p, False{}), St.side(both, Slot.selects.go(b, p, False{})))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the state that a query starts in
def St.of(q: Spec.Query) -> St:
  match q:
    case Spec.Both{a, b}:
      St{True{}, Slot.of_rules(a), Slot.of_rules(b)}
    case Spec.Only{a, b}:
      St{False{}, Slot.of_rules(a), Slot.of_rules(b)}

# the state after c
def St.step(x: St, +c: Char) -> St:
  match x:
    case St{both, a, b}:
      St{both, Slot.step(a, c), Slot.step(b, c)}

# x and y are the same state
# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- it works on a glob, a search state or a character list of a few items, so the extra call is short
def St.is_eq(x: St, y: St) -> Bool:
  match x y:
    case St{n, a, b} St{m, c, d}:
      Bool.and(Shared.Bool.is_eq(n, m), Bool.and(Slots.is_eq(a, c), Slots.is_eq(b, d)))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# St.is_eq is True only for the same state
def St.is_eq_sound(x: St, y: St) -> {St.is_eq(x, y) == True{}: Bool} -> {x == y: St}:
  match x y:
    case St{+n, +a, +b} St{+m, +c, +d}:
      +h =>
        +sa = Slots.is_eq(a, c)
        +sb = Slots.is_eq(b, d)
        +rest = Shared.Bool.and_true_right(Shared.Bool.is_eq(n, m), Bool.and(sa, sb))(h)
        %Shared.Bool.is_eq_sound(
          n,
          m
        )(
          Shared.Bool.and_true_left(Shared.Bool.is_eq(n, m), Bool.and(sa, sb))(h)
        ): {St{n, a, b} == St{_, c, d}: St}
        %Slots.is_eq_sound(
          a,
          c
        )(Shared.Bool.and_true_left(sa, sb)(rest)): {St{n, a, b} == St{n, _, d}: St}
        %Slots.is_eq_sound(
          b,
          d
        )(Shared.Bool.and_true_right(sa, sb)(rest)): {St{n, a, b} == St{n, a, _}: St}
        {==}

# xs holds x
# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- it works on a glob, a search state or a character list of a few items, so the extra call is short
def St.has(xs: List<&2, St>, +x: St) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(St.is_eq(h, x), St.has(t, x))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the state after c holds for t when the state holds for c then t
# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- only proofs use it; no program runs it
def St.step_ok(
  x: St,
  +c: Char,
  +t: String
) -> {St.holds(St.step(x, c), t) == St.holds(x, SCon{c, t}): Bool}:
  match x:
    case St{both, +a, +b}:
      l = Bool.and(
        Slot.selects.go(Slot.step(a, c), t, False{}),
        St.side(both, Slot.selects.go(Slot.step(b, c), t, False{}))
      )
      %Slot.step_ok(
        a,
        c,
        t,
        False{}
      ): {l == Bool.and(_, St.side(both, Slot.selects.go(b, SCon{c, t}, False{}))): Bool}
      %Slot.step_ok(
        b,
        c,
        t,
        False{}
      ): {l == Bool.and(Slot.selects.go(Slot.step(a, c), t, False{}), St.side(both, _)): Bool}
      {==}
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# a query holds for p when p is a valid path and its start state holds
def St.of_ok(
  q: Spec.Query,
  +p: String
) -> {Bool.and(Spec.is_path(p), St.holds(St.of(q), p)) == Spec.Query.holds(q, p): Bool}:
  match q:
    case Spec.Both{+a, +b}:
      r = Spec.Query.holds(Spec.Both{a, b}, p)
      %Slot.of_rules_ok(
        a,
        p,
        False{}
      ): {
        Bool.and(
          Spec.is_path(p),
          Bool.and(_, Slot.selects.go(Slot.of_rules(b), p, False{}))
        )
          == r: Bool
      }
      %Slot.of_rules_ok(
        b,
        p,
        False{}
      ): {Bool.and(Spec.is_path(p), Bool.and(Spec.Rule.selects.go(a, p, False{}), _)) == r: Bool}
      {==}
    case Spec.Only{+a, +b}:
      r = Spec.Query.holds(Spec.Only{a, b}, p)
      %Slot.of_rules_ok(
        a,
        p,
        False{}
      ): {
        Bool.and(
          Spec.is_path(p),
          Bool.and(_, Bool.not(Slot.selects.go(Slot.of_rules(b), p, False{})))
        )
          == r: Bool
      }
      %Slot.of_rules_ok(
        b,
        p,
        False{}
      ): {
        Bool.and(
          Spec.is_path(p),
          Bool.and(Spec.Rule.selects.go(a, p, False{}), Bool.not(_))
        )
          == r: Bool
      }
      {==}

# Representative characters
# -------------------------
# A character that no glob of a state names, and that is not '/', moves the
# state like any other such character.

# cs holds c
# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- it works on a glob, a search state or a character list of a few items, so the extra call is short
def Chars.has(cs: List<&2, Char>, +c: Char) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(Char.is_eq(h, c), Chars.has(t, c))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# every character of xs is in cs
# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- it works on a glob, a search state or a character list of a few items, so the extra call is short
def Chars.all_in(xs: List<&2, Char>, +cs: List<&2, Char>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      Bool.and(Chars.has(cs, h), Chars.all_in(t, cs))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# every character that g names is in cs
# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- it works on a glob, a search state or a character list of a few items, so the extra call is short
def Glob.within(g: Spec.Glob, +cs: List<&2, Char>) -> Bool:
  match g:
    case Spec.Void{}:
      True{}
    case Spec.Eps{}:
      True{}
    case Spec.Lit{x}:
      Chars.has(cs, x)
    case Spec.Any{}:
      True{}
    case Spec.Star{}:
      True{}
    case Spec.Class{n, xs}:
      Chars.all_in(xs, cs)
    case Spec.Deep{}:
      True{}
    case Spec.Cat{a, b}:
      Bool.and(Glob.within(a, cs), Glob.within(b, cs))
    case Spec.Alt{a, b}:
      Bool.and(Glob.within(a, cs), Glob.within(b, cs))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# every character that s names is in cs
# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- it works on a glob, a search state or a character list of a few items, so the extra call is short
def Seq.within(s: List<&2, Spec.Glob>, +cs: List<&2, Char>) -> Bool:
  match s:
    case Nil{}:
      True{}
    case Con{h, t}:
      Bool.and(Glob.within(h, cs), Seq.within(t, cs))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# every character that xs names is in cs
# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- it works on a glob, a search state or a character list of a few items, so the extra call is short
def Seqs.within(xs: List<&2, List<&2, Spec.Glob>>, +cs: List<&2, Char>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      Bool.and(Seq.within(h, cs), Seqs.within(t, cs))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# every character that slots name is in cs
# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- it works on a glob, a search state or a character list of a few items, so the extra call is short
def Slots.within(slots: List<&2, Slot>, +cs: List<&2, Char>) -> Bool:
  match slots:
    case Nil{}:
      True{}
    case Con{Inc{xs}, t}:
      Bool.and(Seqs.within(xs, cs), Slots.within(t, cs))
    case Con{Exc{xs}, t}:
      Bool.and(Seqs.within(xs, cs), Slots.within(t, cs))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# every character that x names is in cs
# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- it works on a glob, a search state or a character list of a few items, so the extra call is short
def St.within(x: St, +cs: List<&2, Char>) -> Bool:
  match x:
    case St{both, a, b}:
      Bool.and(Slots.within(a, cs), Slots.within(b, cs))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# a character x of cs is not c when c is not in cs, given b: Char.is_eq(x, c)
# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- a false positive, as the rule notes: the other use is an erased argument (of Equal.sym or a motive)
def Char.ne_in.at(
  cs: List<&2, Char>,
  x: Char,
  c: Char,
  b: Bool,
  hx: {Chars.has(cs, x) == True{}: Bool},
  hc: {Chars.has(cs, c) == False{}: Bool}
) -> {Char.is_eq(x, c) == b: Bool} -> {False{} == b: Bool}:
  match b:
    case False{}:
      e => {==}
    case True{}:
      e =>
        in_c = {
          %Char.is_eq_sound(x, c)(e): {Chars.has(cs, _) == True{}: Bool}
          hx
          : {Chars.has(cs, c) == True{}: Bool}}
        Empty.absurd(
          {False{} == True{}: Bool},
          Shared.Bool.false_ne_true(
            Equal.trans(
              Bool,
              False{},
              Chars.has(cs, c),
              True{},
              Equal.sym(Bool, Chars.has(cs, c), False{}, hc),
              in_c
            )
          )
        )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# a character x of cs is not c when c is not in cs
def Char.ne_in(
  cs: List<&2, Char>,
  +x: Char,
  +c: Char,
  hx: {Chars.has(cs, x) == True{}: Bool},
  hc: {Chars.has(cs, c) == False{}: Bool}
) -> {False{} == Char.is_eq(x, c): Bool}:
  Char.ne_in.at(cs, x, c, Char.is_eq(x, c), hx, hc)({==})

# c is not a character x of cs when c is not in cs, given b: Char.is_eq(c, x)
# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- a false positive, as the rule notes: the other use is an erased argument (of Equal.sym or a motive)
def Char.ne_in_r.at(
  cs: List<&2, Char>,
  x: Char,
  c: Char,
  b: Bool,
  hx: {Chars.has(cs, x) == True{}: Bool},
  hc: {Chars.has(cs, c) == False{}: Bool}
) -> {Char.is_eq(c, x) == b: Bool} -> {False{} == b: Bool}:
  match b:
    case False{}:
      e => {==}
    case True{}:
      e =>
        in_c = {
          %Equal.sym(Char, c, x, Char.is_eq_sound(c, x)(e)): {Chars.has(cs, _) == True{}: Bool}
          hx
          : {Chars.has(cs, c) == True{}: Bool}}
        Empty.absurd(
          {False{} == True{}: Bool},
          Shared.Bool.false_ne_true(
            Equal.trans(
              Bool,
              False{},
              Chars.has(cs, c),
              True{},
              Equal.sym(Bool, Chars.has(cs, c), False{}, hc),
              in_c
            )
          )
        )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# c is not a character x of cs when c is not in cs
def Char.ne_in_r(
  cs: List<&2, Char>,
  +x: Char,
  +c: Char,
  hx: {Chars.has(cs, x) == True{}: Bool},
  hc: {Chars.has(cs, c) == False{}: Bool}
) -> {False{} == Char.is_eq(c, x): Bool}:
  Char.ne_in_r.at(cs, x, c, Char.is_eq(c, x), hx, hc)({==})

# a class whose characters are all in cs does not hold c when cs does not
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- only proofs use it; no program runs it
def Chars.contains_out(
  xs: List<&2, Char>,
  +cs: List<&2, Char>,
  +c: Char,
  +hc: {Chars.has(cs, c) == False{}: Bool}
) -> {
  Chars.all_in(xs, cs) == True{}: Bool
} -> {False{} == List.contains(~Char, ~Char.is_eq, xs, c): Bool}:
  match xs:
    case Nil{}:
      _ => {==}
    case Con{+x, +t}:
      +h =>
        %Char.ne_in(
          cs,
          x,
          c,
          Shared.Bool.and_true_left(Chars.has(cs, x), Chars.all_in(t, cs))(h),
          hc
        ):
          {False{} == List.any.if(u => List.contains(~Char, ~Char.is_eq, t, c), _): Bool}
        Chars.contains_out(
          t,
          cs,
          c,
          hc
        )(Shared.Bool.and_true_right(Chars.has(cs, x), Chars.all_in(t, cs))(h))
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# Seq.step.head moves h the same under c and f, two characters that h does
# not name and that are not '/'
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- only proofs use it; no program runs it
def Seq.step.head_rep(
  h: Spec.Glob,
  +r: List<&2, Spec.Glob>,
  +c: Char,
  +f: Char,
  +kc: List<&2, List<&2, Spec.Glob>>,
  +kf: List<&2, List<&2, Spec.Glob>>,
  +cs: List<&2, Char>,
  +hc: {Chars.has(cs, c) == False{}: Bool},
  +hf: {Chars.has(cs, f) == False{}: Bool},
  +hs: {Chars.has(cs, '/') == True{}: Bool},
  +ek: {kc == kf: List<&2, List<&2, Spec.Glob>>}
) -> {
  Glob.within(h, cs) == True{}: Bool
} -> {Seq.step.head(h, r, c, kc) == Seq.step.head(h, r, f, kf): List<&2, List<&2, Spec.Glob>>}:
  match h:
    case Spec.Void{}:
      _ => {==}
    case Spec.Eps{}:
      _ => ek
    case Spec.Lit{+x}:
      +hw =>
        %Char.ne_in(
          cs,
          x,
          c,
          hw,
          hc
        ): {Seq.keep(_, r) == Seq.keep(Char.is_eq(x, f), r): List<&2, List<&2, Spec.Glob>>}
        %Char.ne_in(
          cs,
          x,
          f,
          hw,
          hf
        ): {Seq.keep(False{}, r) == Seq.keep(_, r): List<&2, List<&2, Spec.Glob>>}
        {==}
    case Spec.Any{}:
      _ =>
        %Char.ne_in_r(
          cs,
          '/',
          c,
          hs,
          hc
        ): {
          Seq.keep(Bool.not(_), r) == Seq.keep(Spec.is_inner(f), r): List<&2, List<&2, Spec.Glob>>
        }
        %Char.ne_in_r(
          cs,
          '/',
          f,
          hs,
          hf
        ): {Seq.keep(True{}, r) == Seq.keep(Bool.not(_), r): List<&2, List<&2, Spec.Glob>>}
        {==}
    case Spec.Star{}:
      _ =>
        +s = {Con{Spec.Star{}, r}: List<&2, Spec.Glob>}
        %Char.ne_in_r(
          cs,
          '/',
          c,
          hs,
          hc
        ): {
          List.append(
            &2,
            List<&2, Spec.Glob>,
            Seq.keep(Bool.not(_), s),
            kc
          )
            == List.append(
              &2,
              List<&2, Spec.Glob>,
              Seq.keep(Spec.is_inner(f), s),
              kf
            ): List<&2, List<&2, Spec.Glob>>
        }
        %Char.ne_in_r(
          cs,
          '/',
          f,
          hs,
          hf
        ): {
          List.append(
            &2,
            List<&2, Spec.Glob>,
            Seq.keep(True{}, s),
            kc
          )
            == List.append(
              &2,
              List<&2, Spec.Glob>,
              Seq.keep(Bool.not(_), s),
              kf
            ): List<&2, List<&2, Spec.Glob>>
        }
        %ek: {
          List.append(
            &2,
            List<&2, Spec.Glob>,
            Seq.keep(True{}, s),
            kc
          )
            == List.append(
              &2,
              List<&2, Spec.Glob>,
              Seq.keep(True{}, s),
              _
            ): List<&2, List<&2, Spec.Glob>>
        }
        {==}
    case Spec.Class{n, +xs}:
      +hw =>
        +cc = List.contains(~Char, ~Char.is_eq, xs, c)
        +cf = List.contains(~Char, ~Char.is_eq, xs, f)
        %Char.ne_in_r(
          cs,
          '/',
          c,
          hs,
          hc
        ): {
          Seq.keep(
            Bool.and(Bool.not(_), Bool.xor(n, cc)),
            r
          )
            == Seq.keep(
              Bool.and(Spec.is_inner(f), Bool.xor(n, cf)),
              r
            ): List<&2, List<&2, Spec.Glob>>
        }
        %Char.ne_in_r(
          cs,
          '/',
          f,
          hs,
          hf
        ): {
          Seq.keep(
            Bool.and(True{}, Bool.xor(n, cc)),
            r
          )
            == Seq.keep(Bool.and(Bool.not(_), Bool.xor(n, cf)), r): List<&2, List<&2, Spec.Glob>>
        }
        %Chars.contains_out(
          xs,
          cs,
          c,
          hc
        )(
          hw
        ): {
          Seq.keep(
            Bool.and(True{}, Bool.xor(n, _)),
            r
          )
            == Seq.keep(Bool.and(True{}, Bool.xor(n, cf)), r): List<&2, List<&2, Spec.Glob>>
        }
        %Chars.contains_out(
          xs,
          cs,
          f,
          hf
        )(
          hw
        ): {
          Seq.keep(
            Bool.and(True{}, Bool.xor(n, False{})),
            r
          )
            == Seq.keep(Bool.and(True{}, Bool.xor(n, _)), r): List<&2, List<&2, Spec.Glob>>
        }
        {==}
    case Spec.Deep{}:
      _ =>
        %ek: {
          Con{Con{Spec.Deep{}, r}, kc} == Con{Con{Spec.Deep{}, r}, _}: List<&2, List<&2, Spec.Glob>>
        }
        {==}
    case Spec.Cat{+a, +b}:
      +hw =>
        +wa = Glob.within(a, cs)
        +wb = Glob.within(b, cs)
        eb = Seq.step.head_rep(
          b,
          r,
          c,
          f,
          kc,
          kf,
          cs,
          hc,
          hf,
          hs,
          ek
        )(Shared.Bool.and_true_right(wa, wb)(hw))
        Seq.step.head_rep(
          a,
          Con{b, r},
          c,
          f,
          Seq.step.head(b, r, c, kc),
          Seq.step.head(b, r, f, kf),
          cs,
          hc,
          hf,
          hs,
          eb
        )(Shared.Bool.and_true_left(wa, wb)(hw))
    case Spec.Alt{+a, +b}:
      +hw =>
        +wa = Glob.within(a, cs)
        +wb = Glob.within(b, cs)
        +ac = Seq.step.head(a, r, c, kc)
        +bc = Seq.step.head(b, r, c, kc)
        %Seq.step.head_rep(
          a,
          r,
          c,
          f,
          kc,
          kf,
          cs,
          hc,
          hf,
          hs,
          ek
        )(Shared.Bool.and_true_left(wa, wb)(hw)):
          {
            List.append(
              &2,
              List<&2, Spec.Glob>,
              ac,
              bc
            )
              == List.append(
                &2,
                List<&2, Spec.Glob>,
                _,
                Seq.step.head(b, r, f, kf)
              ): List<&2, List<&2, Spec.Glob>>
          }
        %Seq.step.head_rep(
          b,
          r,
          c,
          f,
          kc,
          kf,
          cs,
          hc,
          hf,
          hs,
          ek
        )(Shared.Bool.and_true_right(wa, wb)(hw)):
          {
            List.append(
              &2,
              List<&2, Spec.Glob>,
              ac,
              bc
            )
              == List.append(&2, List<&2, Spec.Glob>, ac, _): List<&2, List<&2, Spec.Glob>>
          }
        {==}
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# Seq.step moves s the same under c and f
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- only proofs use it; no program runs it
def Seq.step_rep(
  s: List<&2, Spec.Glob>,
  +c: Char,
  +f: Char,
  +cs: List<&2, Char>,
  +hc: {Chars.has(cs, c) == False{}: Bool},
  +hf: {Chars.has(cs, f) == False{}: Bool},
  +hs: {Chars.has(cs, '/') == True{}: Bool}
) -> {
  Seq.within(s, cs) == True{}: Bool
} -> {Seq.step(s, c) == Seq.step(s, f): List<&2, List<&2, Spec.Glob>>}:
  match s:
    case Nil{}:
      _ => {==}
    case Con{+h, +t}:
      +hw =>
        +wh = Glob.within(h, cs)
        +wt = Seq.within(t, cs)
        et = Seq.step_rep(t, c, f, cs, hc, hf, hs)(Shared.Bool.and_true_right(wh, wt)(hw))
        Seq.step.head_rep(
          h,
          t,
          c,
          f,
          Seq.step(t, c),
          Seq.step(t, f),
          cs,
          hc,
          hf,
          hs,
          et
        )(Shared.Bool.and_true_left(wh, wt)(hw))
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# Seqs.step moves xs the same under c and f
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- only proofs use it; no program runs it
def Seqs.step_rep(
  xs: List<&2, List<&2, Spec.Glob>>,
  +c: Char,
  +f: Char,
  +cs: List<&2, Char>,
  +hc: {Chars.has(cs, c) == False{}: Bool},
  +hf: {Chars.has(cs, f) == False{}: Bool},
  +hs: {Chars.has(cs, '/') == True{}: Bool}
) -> {
  Seqs.within(xs, cs) == True{}: Bool
} -> {Seqs.step(xs, c) == Seqs.step(xs, f): List<&2, List<&2, Spec.Glob>>}:
  match xs:
    case Nil{}:
      _ => {==}
    case Con{+x, +r}:
      +hw =>
        +wx = Seq.within(x, cs)
        +wr = Seqs.within(r, cs)
        +sc = Seq.step(x, c)
        +rc = Seqs.step(r, c)
        %Seq.step_rep(x, c, f, cs, hc, hf, hs)(Shared.Bool.and_true_left(wx, wr)(hw)):
          {Seqs.add_all(sc, rc) == Seqs.add_all(_, Seqs.step(r, f)): List<&2, List<&2, Spec.Glob>>}
        %Seqs.step_rep(r, c, f, cs, hc, hf, hs)(Shared.Bool.and_true_right(wx, wr)(hw)):
          {Seqs.add_all(sc, rc) == Seqs.add_all(sc, _): List<&2, List<&2, Spec.Glob>>}
        {==}
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# Slot.step moves slots the same under c and f
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- only proofs use it; no program runs it
def Slot.step_rep(
  slots: List<&2, Slot>,
  +c: Char,
  +f: Char,
  +cs: List<&2, Char>,
  +hc: {Chars.has(cs, c) == False{}: Bool},
  +hf: {Chars.has(cs, f) == False{}: Bool},
  +hs: {Chars.has(cs, '/') == True{}: Bool}
) -> {
  Slots.within(slots, cs) == True{}: Bool
} -> {Slot.step(slots, c) == Slot.step(slots, f): List<&2, Slot>}:
  match slots:
    case Nil{}:
      _ => {==}
    case Con{Inc{+xs}, +t}:
      +hw =>
        +wx = Seqs.within(xs, cs)
        +wt = Slots.within(t, cs)
        +xc = Seqs.step(xs, c)
        +tc = Slot.step(t, c)
        %Seqs.step_rep(xs, c, f, cs, hc, hf, hs)(Shared.Bool.and_true_left(wx, wt)(hw)):
          {Con{Inc{xc}, tc} == Con{Inc{_}, Slot.step(t, f)}: List<&2, Slot>}
        %Slot.step_rep(t, c, f, cs, hc, hf, hs)(Shared.Bool.and_true_right(wx, wt)(hw)):
          {Con{Inc{xc}, tc} == Con{Inc{xc}, _}: List<&2, Slot>}
        {==}
    case Con{Exc{+xs}, +t}:
      +hw =>
        +wx = Seqs.within(xs, cs)
        +wt = Slots.within(t, cs)
        +xc = Seqs.step(xs, c)
        +tc = Slot.step(t, c)
        %Seqs.step_rep(xs, c, f, cs, hc, hf, hs)(Shared.Bool.and_true_left(wx, wt)(hw)):
          {Con{Exc{xc}, tc} == Con{Exc{_}, Slot.step(t, f)}: List<&2, Slot>}
        %Slot.step_rep(t, c, f, cs, hc, hf, hs)(Shared.Bool.and_true_right(wx, wt)(hw)):
          {Con{Exc{xc}, tc} == Con{Exc{xc}, _}: List<&2, Slot>}
        {==}
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# St.step moves x the same under c and f
def St.step_rep(
  x: St,
  +c: Char,
  +f: Char,
  +cs: List<&2, Char>,
  +hc: {Chars.has(cs, c) == False{}: Bool},
  +hf: {Chars.has(cs, f) == False{}: Bool},
  +hs: {Chars.has(cs, '/') == True{}: Bool}
) -> {St.within(x, cs) == True{}: Bool} -> {St.step(x, c) == St.step(x, f): St}:
  match x:
    case St{both, +a, +b}:
      +hw =>
        +wa = Slots.within(a, cs)
        +wb = Slots.within(b, cs)
        +ac = Slot.step(a, c)
        +bc = Slot.step(b, c)
        %Slot.step_rep(a, c, f, cs, hc, hf, hs)(Shared.Bool.and_true_left(wa, wb)(hw)):
          {St{both, ac, bc} == St{both, _, Slot.step(b, f)}: St}
        %Slot.step_rep(b, c, f, cs, hc, hf, hs)(Shared.Bool.and_true_right(wa, wb)(hw)):
          {St{both, ac, bc} == St{both, ac, _}: St}
        {==}

# Certificates
# ------------
# A certificate is a list of states xs, the characters cs that its globs
# name (with '/'), and one more character f outside cs. When every state of
# xs fails on "" and steps into xs under f and each character of cs, no
# state of xs holds for any string.

# no True equals False
def Bool.true_ne_false(e: {True{} == False{}: Bool}) -> Empty:
  %e: Bool.pick(Type, _, Unit, Empty)
  Unit{}

# the right side of a False disjunction is False
def Bool.or_false_r(a: Bool, -b: Bool) -> {Bool.or(a, b) == False{}: Bool} -> {b == False{}: Bool}:
  match a:
    case False{}:
      h => h
    case True{}:
      h => Empty.absurd({b == False{}: Bool}, Bool.true_ne_false(h))

# each step of x under a character of ds lands in xs
# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- it works on a glob, a search state or a character list of a few items, so the extra call is short
def St.closed(+x: St, ds: List<&2, Char>, +xs: List<&2, St>) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case Con{d, t}:
      Bool.and(St.has(xs, St.step(x, d)), St.closed(x, t, xs))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# x fails on "", names only characters of cs, and steps into xs
# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- it works on a glob, a search state or a character list of a few items, so the extra call is short
def St.ok(+x: St, +cs: List<&2, Char>, f: Char, xs: List<&2, St>) -> Bool:
  Bool.and(Bool.not(St.holds(x, SNil{})), Bool.and(St.within(x, cs), St.closed(x, Con{f, cs}, xs)))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# every state of ys is ok
# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- it works on a glob, a search state or a character list of a few items, so the extra call is short
def St.all_ok(ys: List<&2, St>, +cs: List<&2, Char>, +f: Char, +xs: List<&2, St>) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case Con{y, t}:
      Bool.and(St.ok(y, cs, f, xs), St.all_ok(t, cs, f, xs))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# (xs, cs, f) is a certificate
# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- it works on a glob, a search state or a character list of a few items, so the extra call is short
def Cert.check(+xs: List<&2, St>, +cs: List<&2, Char>, +f: Char) -> Bool:
  Bool.and(Chars.has(cs, '/'), Bool.and(Bool.not(Chars.has(cs, f)), St.all_ok(xs, cs, f, xs)))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# one step of St.all_ok_has, given b: St.is_eq(y, x)
def St.all_ok_has.at(
  +y: St,
  t: List<&2, St>,
  x: St,
  +cs: List<&2, Char>,
  +f: Char,
  +xs: List<&2, St>,
  b: Bool,
  ih: {
    St.all_ok(t, cs, f, xs) == True{}: Bool
  } -> {St.has(t, x) == True{}: Bool} -> {St.ok(x, cs, f, xs) == True{}: Bool},
  ha: {Bool.and(St.ok(y, cs, f, xs), St.all_ok(t, cs, f, xs)) == True{}: Bool}
) -> {
  St.is_eq(y, x) == b: Bool
} -> {Bool.or(b, St.has(t, x)) == True{}: Bool} -> {St.ok(x, cs, f, xs) == True{}: Bool}:
  match b:
    case False{}:
      e => hh => ih(
        Shared.Bool.and_true_right(St.ok(y, cs, f, xs), St.all_ok(t, cs, f, xs))(ha)
      )(hh)
    case True{}:
      e => hh =>
        %St.is_eq_sound(y, x)(e): {St.ok(_, cs, f, xs) == True{}: Bool}
        Shared.Bool.and_true_left(St.ok(y, cs, f, xs), St.all_ok(t, cs, f, xs))(ha)

# a state that ys holds is ok when all of ys are
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- only proofs use it; no program runs it
def St.all_ok_has(
  ys: List<&2, St>,
  +x: St,
  +cs: List<&2, Char>,
  +f: Char,
  +xs: List<&2, St>
) -> {
  St.all_ok(ys, cs, f, xs) == True{}: Bool
} -> {St.has(ys, x) == True{}: Bool} -> {St.ok(x, cs, f, xs) == True{}: Bool}:
  match ys:
    case Nil{}:
      _ => hh => Empty.absurd({St.ok(x, cs, f, xs) == True{}: Bool}, Shared.Bool.false_ne_true(hh))
    case Con{+y, +t}:
      ha => St.all_ok_has.at(
        y,
        t,
        x,
        cs,
        f,
        xs,
        St.is_eq(y, x),
        St.all_ok_has(t, x, cs, f, xs),
        ha
      )({==})
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# one step of St.closed_has, given b: Char.is_eq(d, c)
def St.closed_has.at(
  +x: St,
  +d: Char,
  t: List<&2, Char>,
  +xs: List<&2, St>,
  c: Char,
  b: Bool,
  ih: {
    St.closed(x, t, xs) == True{}: Bool
  } -> {Chars.has(t, c) == True{}: Bool} -> {St.has(xs, St.step(x, c)) == True{}: Bool},
  hcl: {Bool.and(St.has(xs, St.step(x, d)), St.closed(x, t, xs)) == True{}: Bool}
) -> {
  Char.is_eq(d, c) == b: Bool
} -> {Bool.or(b, Chars.has(t, c)) == True{}: Bool} -> {St.has(xs, St.step(x, c)) == True{}: Bool}:
  match b:
    case False{}:
      e => hh => ih(
        Shared.Bool.and_true_right(St.has(xs, St.step(x, d)), St.closed(x, t, xs))(hcl)
      )(hh)
    case True{}:
      e => hh =>
        %Char.is_eq_sound(d, c)(e): {St.has(xs, St.step(x, _)) == True{}: Bool}
        Shared.Bool.and_true_left(St.has(xs, St.step(x, d)), St.closed(x, t, xs))(hcl)

# x steps into xs under each character of ds when it is closed for ds
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- only proofs use it; no program runs it
def St.closed_has(
  +x: St,
  ds: List<&2, Char>,
  +xs: List<&2, St>,
  +c: Char
) -> {
  St.closed(x, ds, xs) == True{}: Bool
} -> {Chars.has(ds, c) == True{}: Bool} -> {St.has(xs, St.step(x, c)) == True{}: Bool}:
  match ds:
    case Nil{}:
      _ => hh => Empty.absurd(
        {St.has(xs, St.step(x, c)) == True{}: Bool},
        Shared.Bool.false_ne_true(hh)
      )
    case Con{+d, +t}:
      hcl => St.closed_has.at(
        x,
        d,
        t,
        xs,
        c,
        Char.is_eq(d, c),
        St.closed_has(x, t, xs, c),
        hcl
      )({==})
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# St.next_in, given b: Chars.has(Con{f, cs}, c)
# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- a false positive, as the rule notes: the other use is an erased argument (of Equal.sym or a motive)
def St.next_in.at(
  +x: St,
  +c: Char,
  cs: List<&2, Char>,
  +f: Char,
  xs: List<&2, St>,
  b: Bool,
  hs: {Chars.has(cs, '/') == True{}: Bool},
  hf: {Chars.has(cs, f) == False{}: Bool},
  hw: {St.within(x, cs) == True{}: Bool},
  hcl: {St.closed(x, Con{f, cs}, xs) == True{}: Bool}
) -> {Chars.has(Con{f, cs}, c) == b: Bool} -> {St.has(xs, St.step(x, c)) == True{}: Bool}:
  match b:
    case True{}:
      e => St.closed_has(x, Con{f, cs}, xs, c)(hcl)(e)
    case False{}:
      e =>
        hc = Bool.or_false_r(Char.is_eq(f, c), Chars.has(cs, c))(e)
        rep = St.step_rep(x, c, f, cs, hc, hf, hs)(hw)
        %Equal.sym(St, St.step(x, c), St.step(x, f), rep): {St.has(xs, _) == True{}: Bool}
        Shared.Bool.and_true_left(St.has(xs, St.step(x, f)), St.closed(x, cs, xs))(hcl)
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# an ok state of a certificate steps into it under any character
def St.next_in(
  +x: St,
  +c: Char,
  +cs: List<&2, Char>,
  +f: Char,
  +xs: List<&2, St>,
  hs: {Chars.has(cs, '/') == True{}: Bool},
  hf: {Chars.has(cs, f) == False{}: Bool},
  hok: {St.ok(x, cs, f, xs) == True{}: Bool}
) -> {St.has(xs, St.step(x, c)) == True{}: Bool}:
  nh = Bool.not(St.holds(x, SNil{}))
  +wi = St.within(x, cs)
  +cl = St.closed(x, Con{f, cs}, xs)
  +rest = Shared.Bool.and_true_right(nh, Bool.and(wi, cl))(hok)
  hw = Shared.Bool.and_true_left(wi, cl)(rest)
  hcl = Shared.Bool.and_true_right(wi, cl)(rest)
  St.next_in.at(x, c, cs, f, xs, Chars.has(Con{f, cs}, c), hs, hf, hw, hcl)({==})

# a valid certificate names '/'
# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- a false positive, as the rule notes: the other use is an erased argument (of Equal.sym or a motive)
# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- only proofs use it; no program runs it
def Cert.slash(
  cs: List<&2, Char>,
  f: Char,
  xs: List<&2, St>,
  hcert: {Cert.check(xs, cs, f) == True{}: Bool}
) -> {Chars.has(cs, '/') == True{}: Bool}:
  Shared.Bool.and_true_left(
    Chars.has(cs, '/'),
    Bool.and(Bool.not(Chars.has(cs, f)), St.all_ok(xs, cs, f, xs))
  )(hcert)
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# a valid certificate does not name f
# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- a false positive, as the rule notes: the other use is an erased argument (of Equal.sym or a motive)
def Cert.fresh(
  +cs: List<&2, Char>,
  +f: Char,
  +xs: List<&2, St>,
  hcert: {Cert.check(xs, cs, f) == True{}: Bool}
) -> {Chars.has(cs, f) == False{}: Bool}:
  +nf = Bool.not(Chars.has(cs, f))
  al = St.all_ok(xs, cs, f, xs)
  rest = Shared.Bool.and_true_right(Chars.has(cs, '/'), Bool.and(nf, al))(hcert)
  Shared.Bool.not_true(Chars.has(cs, f))(Shared.Bool.and_true_left(nf, al)(rest))
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# every state of a valid certificate is ok
def Cert.ok_of(
  x: St,
  +cs: List<&2, Char>,
  +f: Char,
  +xs: List<&2, St>,
  hcert: {Cert.check(xs, cs, f) == True{}: Bool},
  hx: {St.has(xs, x) == True{}: Bool}
) -> {St.ok(x, cs, f, xs) == True{}: Bool}:
  +nf = Bool.not(Chars.has(cs, f))
  +al = St.all_ok(xs, cs, f, xs)
  rest = Shared.Bool.and_true_right(Chars.has(cs, '/'), Bool.and(nf, al))(hcert)
  St.all_ok_has(xs, x, cs, f, xs)(Shared.Bool.and_true_right(nf, al)(rest))(hx)

# no state of a certificate holds for any string
# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- only proofs use it; no program runs it
def Cert.sound(
  w: String,
  +x: St,
  +cs: List<&2, Char>,
  +f: Char,
  +xs: List<&2, St>,
  +hcert: {Cert.check(xs, cs, f) == True{}: Bool},
  hx: {St.has(xs, x) == True{}: Bool}
) -> {St.holds(x, w) == False{}: Bool}:
  match w:
    case SNil{}:
      nh = Bool.not(St.holds(x, SNil{}))
      rest = Bool.and(St.within(x, cs), St.closed(x, Con{f, cs}, xs))
      Shared.Bool.not_true(
        St.holds(x, SNil{})
      )(Shared.Bool.and_true_left(nh, rest)(Cert.ok_of(x, cs, f, xs, hcert, hx)))
    case SCon{+c, +t}:
      hs = Cert.slash(cs, f, xs, hcert)
      hf = Cert.fresh(cs, f, xs, hcert)
      hn = St.next_in(x, c, cs, f, xs, hs, hf, Cert.ok_of(x, cs, f, xs, hcert, hx))
      %St.step_ok(x, c, t): {_ == False{}: Bool}
      Cert.sound(t, St.step(x, c), cs, f, xs, hcert, hn)
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# Search
# ------
# The search needs no proof: `decide` checks what it returns. Phase one
# collects the states reachable from the start; when none holds on "", they
# are a certificate. Else phase two looks for a valid path that holds,
# guided by an automaton of valid paths.

# the characters that g names
# bend-lint: expect-begin bend-lint-rules/performance/missed_fork@hint -- a glob tree is a few nodes, where a fork costs more than it saves
def Glob.chars(g: Spec.Glob) -> List<&2, Char>:
  match g:
    case Spec.Void{}:
      []
    case Spec.Eps{}:
      []
    case Spec.Lit{x}:
      [x]
    case Spec.Any{}:
      []
    case Spec.Star{}:
      []
    case Spec.Class{n, xs}:
      xs
    case Spec.Deep{}:
      []
    case Spec.Cat{a, b}:
      List.append(&2, Char, Glob.chars(a), Glob.chars(b))
    case Spec.Alt{a, b}:
      List.append(&2, Char, Glob.chars(a), Glob.chars(b))
# bend-lint: expect-end bend-lint-rules/performance/missed_fork@hint

# the characters that the globs of rules name
def Rules.chars(rules: List<&2, Spec.Rule>) -> List<&2, Char>:
  match rules:
    case Nil{}:
      []
    case Con{Spec.Include{g}, t}:
      List.append(&2, Char, Glob.chars(g), Rules.chars(t))
    case Con{Spec.Exclude{g}, t}:
      List.append(&2, Char, Glob.chars(g), Rules.chars(t))

# '/' and the characters that the globs of q name
def Query.chars(q: Spec.Query) -> List<&2, Char>:
  match q:
    case Spec.Both{a, b}:
      Con{'/', List.append(&2, Char, Rules.chars(a), Rules.chars(b))}
    case Spec.Only{a, b}:
      Con{'/', List.append(&2, Char, Rules.chars(a), Rules.chars(b))}

# the largest code in cs, or acc
def Chars.max(cs: List<&2, Char>, +acc: U32) -> U32:
  match cs:
    case Nil{}:
      acc
    case Con{Chr{+x}, t}:
      Chars.max(t, Bool.pick(U32, U32.is_gt(x, acc), x, acc))

# a character after every character of cs
def Chars.fresh(cs: List<&2, Char>) -> Char:
  Chr{(Chars.max(cs, 0) + 1: U32)}

# acc with y, unless known
def Search.add_new(y: St, acc: List<&2, St>, known: Bool) -> List<&2, St>:
  match known:
    case False{}:
      Con{y, acc}
    case True{}:
      acc

# the steps of x under ds that neither seen nor acc holds
# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- it works on a glob, a search state or a character list of a few items, so the extra call is short
def Search.fresh(
  +x: St,
  ds: List<&2, Char>,
  +seen: List<&2, St>,
  +acc: List<&2, St>
) -> List<&2, St>:
  match ds:
    case Nil{}:
      acc
    case Con{d, t}:
      +y = St.step(x, d)
      Search.fresh(x, t, seen, Search.add_new(y, acc, Bool.or(St.has(seen, y), St.has(acc, y))))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# k(), or None when x holds on ""
def Search.close.if(hit: Bool, k: Unit -> Maybe<&2, List<&2, St>>) -> Maybe<&2, List<&2, St>>:
  match hit:
    case False{}:
      k(Unit{})
    case True{}:
      None{}

# every state reachable from todo, with seen; None when one holds on "" or
# fuel runs out
def Search.close(
  fuel: Nat,
  todo: List<&2, St>,
  +seen: List<&2, St>,
  +ds: List<&2, Char>
) -> Maybe<&2, List<&2, St>>:
  match fuel todo:
    case 0n _:
      None{}
    case 1n+n Nil{}:
      Some{seen}
    case 1n+n Con{+x, t}:
      +new = Search.fresh(x, ds, seen, [])
      next = List.append(&2, St, t, new)
      Search.close.if(
        St.holds(x, SNil{}),
        u => Search.close(n, next, List.append(&2, St, new, seen), ds)
      )

# bend-lint: expect-begin bend-lint-rules/layout/case@warning -- a constructor is PascalCase, as in Base (Some, Con): the rule reads a constructor as a law
# Where a valid path is: at a segment start, after "." or "..", inside a
# valid segment, or past a mistake.
type Path is Data:
  PStart{}
  PDot{}
  PDots{}
  PSeg{}
  PDead{}
# bend-lint: expect-end bend-lint-rules/layout/case@warning

# bend-lint: expect-begin bend-lint-rules/layout/case@warning -- a constructor is PascalCase, as in Base (Some, Con): the rule reads a constructor as a law
# What a character is to a path: '/', '.', a banned character, or another.
type Role is Data:
  KSlash{}
  KDot{}
  KBad{}
  KOther{}
# bend-lint: expect-end bend-lint-rules/layout/case@warning

# what c is to a path
def Role.of(c: Char) -> Role:
  match c:
    case Chr{+x}:
      Bool.pick(
        Role,
        U32.is_eq(x, 47),
        KSlash{},
        Bool.pick(
          Role,
          U32.is_eq(x, 46),
          KDot{},
          Bool.pick(Role, Bool.or(U32.is_eq(x, 0), U32.is_eq(x, 92)), KBad{}, KOther{})
        )
      )

# where a path is after a character of kind k
def Path.step(s: Path, k: Role) -> Path:
  match s k:
    case PSeg{} KSlash{}:
      PStart{}
    case _ KSlash{}:
      PDead{}
    case _ KBad{}:
      PDead{}
    case PDead{} _:
      PDead{}
    case PStart{} KDot{}:
      PDot{}
    case PDot{} KDot{}:
      PDots{}
    case _ _:
      PSeg{}

# a and b are the same place
def Path.is_eq(a: Path, b: Path) -> Bool:
  match a b:
    case PStart{} PStart{}:
      True{}
    case PDot{} PDot{}:
      True{}
    case PDots{} PDots{}:
      True{}
    case PSeg{} PSeg{}:
      True{}
    case PDead{} PDead{}:
      True{}
    case _ _:
      False{}

# a valid path can end here
def Path.is_end(s: Path) -> Bool:
  match s:
    case PSeg{}:
      True{}
    case _:
      False{}

# A node of phase two: where the path is, the state, and the characters so
# far, last first.
type Node is Data:
  Node{at: Path, x: St, rev: String}

# a node with the same place and state as n is in ns
# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- it works on a glob, a search state or a character list of a few items, so the extra call is short
def Node.seen(ns: List<&2, Node>, +n: Node) -> Bool:
  match ns:
    case Nil{}:
      False{}
    case Con{Node{a, x, r}, t}:
      match n:
        case Node{+b, +y, s}:
          Bool.or(Bool.and(Path.is_eq(a, b), St.is_eq(x, y)), Node.seen(t, Node{b, y, s}))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# acc with n, unless known or its path went wrong
def Node.add(known: Bool, n: Node, acc: List<&2, Node>) -> List<&2, Node>:
  match known n:
    case True{} _:
      acc
    case False{} Node{PDead{}, x, r}:
      acc
    case False{} n:
      Con{n, acc}

# the steps of n under ds that neither seen nor acc holds
# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- it works on a glob, a search state or a character list of a few items, so the extra call is short
def Node.fresh(
  ds: List<&2, Char>,
  +n: Node,
  +seen: List<&2, Node>,
  +acc: List<&2, Node>
) -> List<&2, Node>:
  match ds:
    case Nil{}:
      acc
    case Con{+d, t}:
      match n:
        case Node{+a, +x, +r}:
          +m = {Node{Path.step(a, Role.of(d)), St.step(x, d), SCon{d, r}}: Node}
          Node.fresh(
            t,
            Node{a, x, r},
            seen,
            Node.add(Bool.or(Node.seen(seen, m), Node.seen(acc, m)), m, acc)
          )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the path of n when it is a valid path that holds, else k()
def Search.witness.if(hit: Bool, n: Node, k: Unit -> Maybe<&2, String>) -> Maybe<&2, String>:
  match hit n:
    case True{} Node{a, x, r}:
      Some{String.reverse(r)}
    case False{} _:
      k(Unit{})

# a valid path that some node reachable from todo holds for, or None
# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- it works on a glob, a search state or a character list of a few items, so the extra call is short
def Search.witness(
  fuel: Nat,
  todo: List<&2, Node>,
  +seen: List<&2, Node>,
  +ds: List<&2, Char>
) -> Maybe<&2, String>:
  match fuel todo:
    case 0n _:
      None{}
    case 1n+n Nil{}:
      None{}
    case 1n+n Con{Node{+a, +x, r}, t}:
      +m = {Node{a, x, r}: Node}
      +new = Node.fresh(ds, m, seen, [])
      next = List.append(&2, Node, t, new)
      hit = Bool.and(Path.is_end(a), St.holds(x, SNil{}))
      Search.witness.if(hit, m, u => Search.witness(n, next, List.append(&2, Node, new, seen), ds))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# bend-lint: expect-begin bend-lint-rules/layout/case@warning -- a constructor is PascalCase, as in Base (Some, Con): the rule reads a constructor as a law
# What the search found: a path to check, a certificate to check, or neither.
type Outcome is Data:
  Witness{path: String}
  Proof{xs: List<&2, St>, cs: List<&2, Char>, f: Char}
  NoAnswer{}
# bend-lint: expect-end bend-lint-rules/layout/case@warning

# the states a search may visit before it gives up
def Search.fuel() -> Nat:
  4096n

# phase two, after phase one found no certificate
def Search.run.witness(found: Maybe<&2, String>) -> Outcome:
  match found:
    case None{}:
      NoAnswer{}
    case Some{p}:
      Witness{p}

# the certificate of phase one, or phase two when there is none
def Search.run.closed(
  x0: St,
  cs: List<&2, Char>,
  f: Char,
  closed: Maybe<&2, List<&2, St>>
) -> Outcome:
  match closed:
    case Some{xs}:
      Proof{xs, cs, f}
    case None{}:
      ds = {Con{'x', Con{f, cs}}: List<&2, Char>}
      +start = {Node{PStart{}, x0, SNil{}}: Node}
      Search.run.witness(Search.witness(Search.fuel(), [start], [start], ds))

# what the search finds for q
def Search.run(+q: Spec.Query) -> Outcome:
  +x0 = St.of(q)
  +cs = Query.chars(q)
  +f = Chars.fresh(cs)
  Search.run.closed(x0, cs, f, Search.close(Search.fuel(), [x0], [x0], Con{f, cs}))

# Found{p} when ok, else Unknown
def Search.found_if(p: String, ok: Bool) -> Spec.Search:
  match ok:
    case False{}:
      Spec.Unknown{}
    case True{}:
      Spec.Found{p}

# Absent when ok, else Unknown
def Search.absent_if(ok: Bool) -> Spec.Search:
  match ok:
    case False{}:
      Spec.Unknown{}
    case True{}:
      Spec.Absent{}

# the answer to q, from what the search found, once checked
# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- it works on a glob, a search state or a character list of a few items, so the extra call is short
def Search.decide(q: Spec.Query, r: Outcome) -> Spec.Search:
  match r:
    case Witness{+p}:
      Search.found_if(p, Spec.Query.holds(q, p))
    case Proof{+xs, cs, f}:
      Search.absent_if(Bool.and(Cert.check(xs, cs, f), St.has(xs, St.of(q))))
    case NoAnswer{}:
      Spec.Unknown{}
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information
def Spec.Query.search(q):
  +q = q
  Search.decide(q, Search.run(q))

# Empty when s is Found
def Search.NotFound(s: Spec.Search) -> Type:
  match s:
    case Spec.Found{p}:
      Empty
    case Spec.Absent{}:
      Unit
    case Spec.Unknown{}:
      Unit

# Empty when s is Absent
def Search.NotAbsent(s: Spec.Search) -> Type:
  match s:
    case Spec.Found{p}:
      Unit
    case Spec.Absent{}:
      Empty
    case Spec.Unknown{}:
      Unit

# no s that is not Found equals Found{p}
def Search.ne_found(
  -s: Spec.Search,
  -p: String,
  n: Search.NotFound(s),
  e: {s == Spec.Found{p}: Spec.Search}
) -> Empty:
  %e: Search.NotFound(_)
  n

# no s that is not Absent equals Absent
def Search.ne_absent(
  -s: Spec.Search,
  n: Search.NotAbsent(s),
  e: {s == Spec.Absent{}: Spec.Search}
) -> Empty:
  %e: Search.NotAbsent(_)
  n

# the path of a Found answer
def Search.path(s: Spec.Search) -> String:
  match s:
    case Spec.Found{p}:
      p
    case Spec.Absent{}:
      SNil{}
    case Spec.Unknown{}:
      SNil{}

# found_if answers Found{p} only for a path that holds, given b: holds(q, p0)
def Search.found_if_found(
  q: Spec.Query,
  p0: String,
  p: String,
  b: Bool
) -> {
  Spec.Query.holds(q, p0) == b: Bool
} -> {
  Search.found_if(p0, b) == Spec.Found{p}: Spec.Search
} -> {Spec.Query.holds(q, p) == True{}: Bool}:
  match b:
    case False{}:
      e => h => Empty.absurd(
        {Spec.Query.holds(q, p) == True{}: Bool},
        Search.ne_found(Spec.Unknown{}, p, Unit{}, h)
      )
    case True{}:
      e => h =>
        same = Equal.cong(
          Spec.Search,
          String,
          s => Search.path(s),
          Spec.Found{p0},
          Spec.Found{p},
          h
        )
        %same: {Spec.Query.holds(q, _) == True{}: Bool}
        e

# absent_if never answers Found
def Search.absent_if_found(
  b: Bool,
  -p: String
) -> {Search.absent_if(b) == Spec.Found{p}: Spec.Search} -> Empty:
  match b:
    case False{}:
      h => Search.ne_found(Spec.Unknown{}, p, Unit{}, h)
    case True{}:
      h => Search.ne_found(Spec.Absent{}, p, Unit{}, h)

# found_if never answers Absent
def Search.found_if_absent(
  -p: String,
  b: Bool
) -> {Search.found_if(p, b) == Spec.Absent{}: Spec.Search} -> Empty:
  match b:
    case False{}:
      h => Search.ne_absent(Spec.Unknown{}, Unit{}, h)
    case True{}:
      h => Search.ne_absent(Spec.Found{p}, Unit{}, h)

# a Found answer of decide names a path that holds
# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- only proofs use it; no program runs it
def Search.decide_found(
  +q: Spec.Query,
  r: Outcome,
  p: String
) -> {
  Search.decide(q, r) == Spec.Found{p}: Spec.Search
} -> {Spec.Query.holds(q, p) == True{}: Bool}:
  match r:
    case Witness{+p0}:
      h => Search.found_if_found(q, p0, p, Spec.Query.holds(q, p0))({==}, h)
    case Proof{+xs, cs, f}:
      h => Empty.absurd(
        {Spec.Query.holds(q, p) == True{}: Bool},
        Search.absent_if_found(Bool.and(Cert.check(xs, cs, f), St.has(xs, St.of(q))), p)(h)
      )
    case NoAnswer{}:
      h => Empty.absurd(
        {Spec.Query.holds(q, p) == True{}: Bool},
        Search.ne_found(Spec.Unknown{}, p, Unit{}, h)
      )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# absent_if answers Absent only for a valid certificate that holds the start
def Search.absent_if_absent(
  +q: Spec.Query,
  +xs: List<&2, St>,
  +cs: List<&2, Char>,
  +f: Char,
  +p: String,
  b: Bool
) -> {
  Bool.and(Cert.check(xs, cs, f), St.has(xs, St.of(q))) == b: Bool
} -> {
  Search.absent_if(b) == Spec.Absent{}: Spec.Search
} -> {Spec.Query.holds(q, p) == False{}: Bool}:
  match b:
    case False{}:
      e => h => Empty.absurd(
        {Spec.Query.holds(q, p) == False{}: Bool},
        Search.ne_absent(Spec.Unknown{}, Unit{}, h)
      )
    case True{}:
      +e => h =>
        +ck = Cert.check(xs, cs, f)
        +hs = St.has(xs, St.of(q))
        none = Cert.sound(
          p,
          St.of(q),
          cs,
          f,
          xs,
          Shared.Bool.and_true_left(ck, hs)(e),
          Shared.Bool.and_true_right(ck, hs)(e)
        )
        %St.of_ok(q, p): {_ == False{}: Bool}
        %Equal.sym(
          Bool,
          St.holds(St.of(q), p),
          False{},
          none
        ): {Bool.and(Spec.is_path(p), _) == False{}: Bool}
        Equal.sym(
          Bool,
          False{},
          Bool.and(Spec.is_path(p), False{}),
          Bool.and_false(Spec.is_path(p))
        )

# an Absent answer of decide means no path holds
# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- only proofs use it; no program runs it
def Search.decide_absent(
  +q: Spec.Query,
  r: Outcome,
  p: String
) -> {
  Search.decide(q, r) == Spec.Absent{}: Spec.Search
} -> {Spec.Query.holds(q, p) == False{}: Bool}:
  match r:
    case Witness{p0}:
      h => Empty.absurd(
        {Spec.Query.holds(q, p) == False{}: Bool},
        Search.found_if_absent(p0, Spec.Query.holds(q, p0))(h)
      )
    case Proof{+xs, +cs, +f}:
      h => Search.absent_if_absent(
        q,
        xs,
        cs,
        f,
        p,
        Bool.and(Cert.check(xs, cs, f), St.has(xs, St.of(q)))
      )({==}, h)
    case NoAnswer{}:
      h => Empty.absurd(
        {Spec.Query.holds(q, p) == False{}: Bool},
        Search.ne_absent(Spec.Unknown{}, Unit{}, h)
      )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information
def Spec.search_found(q, p, h):
  +q = q
  Search.decide_found(q, Search.run(q), p)(h)

def Spec.search_absent(q, p, h):
  +q = q
  Search.decide_absent(q, Search.run(q), p)(h)

# Text
# ----
# Glob.show writes each glob as text that Spec.Glob.read reads back as one
# atom: Show.glob(g), which matches what g matches. Compound globs go in
# braces, so a text never depends on what follows it.

# a character is the character of its role
# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- a false positive, as the rule notes: the other use is an erased argument (of Equal.sym or a motive)
def Sym.of.go_char.at(
  s: Spec.Sym,
  t: List<&2, Spec.Sym>,
  c: Char,
  hit: Bool,
  ih: {c == Spec.Sym.char(Spec.Sym.of.go(t, c)): Char}
) -> {
  Char.is_eq(Spec.Sym.char(s), c) == hit: Bool
} -> {c == Spec.Sym.char(Spec.Sym.of.if(s, u => Spec.Sym.of.go(t, c), hit)): Char}:
  match hit:
    case False{}:
      e => ih
    case True{}:
      e => Equal.sym(Char, Spec.Sym.char(s), c, Char.is_eq_sound(Spec.Sym.char(s), c)(e))
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# the role that Sym.of.go finds for c has c as its character
def Sym.of.go_char(
  xs: List<&2, Spec.Sym>,
  +c: Char
) -> {c == Spec.Sym.char(Spec.Sym.of.go(xs, c)): Char}:
  match xs:
    case Nil{}:
      {==}
    case Con{+s, +t}:
      Sym.of.go_char.at(s, t, c, Char.is_eq(Spec.Sym.char(s), c), Sym.of.go_char(t, c))({==})

# the role of c has c as its character
def Sym.char_of(c: Char) -> {c == Spec.Sym.char(Spec.Sym.of(c)): Char}:
  Sym.of.go_char(Spec.Sym.specials(), c)

# c is the character of k, the role of c
# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- a false positive, as the rule notes: the other use is an erased argument (of Equal.sym or a motive)
def Sym.char_is(
  c: Char,
  k: Spec.Sym,
  e: {k == Spec.Sym.of(c): Spec.Sym}
) -> {c == Spec.Sym.char(k): Char}:
  %Equal.sym(Spec.Sym, k, Spec.Sym.of(c), e): {c == Spec.Sym.char(_): Char}
  Sym.char_of(c)
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# the text of c before rest: a character with a role is escaped
def Glob.show.char(c: Char, k: Spec.Sym, rest: String) -> String:
  match k:
    case Spec.SChar{x}:
      SCon{c, rest}
    case _:
      SCon{Chr{92}, SCon{c, rest}}

# each character of cs, escaped, before rest
def Glob.show.chars(cs: List<&2, Char>, rest: String) -> String:
  match cs:
    case Nil{}:
      rest
    case Con{h, t}:
      SCon{Chr{92}, SCon{h, Glob.show.chars(t, rest)}}

# `!` before text when neg
def Glob.show.neg(neg: Bool, text: String) -> String:
  match neg:
    case False{}:
      text
    case True{}:
      SCon{'!', text}

# the text of g before rest
def Glob.show.go(g: Spec.Glob, rest: String) -> String:
  match g:
    case Spec.Void{}:
      "[]" ++ rest
    case Spec.Eps{}:
      "{}" ++ rest
    case Spec.Lit{+c}:
      Glob.show.char(c, Spec.Sym.of(c), rest)
    case Spec.Any{}:
      "?" ++ rest
    case Spec.Star{}:
      "{*}" ++ rest
    case Spec.Class{neg, cs}:
      "[" ++ Glob.show.neg(neg, Glob.show.chars(cs, "]" ++ rest))
    case Spec.Deep{}:
      "{*{,/**}}" ++ rest
    case Spec.Cat{a, b}:
      "{" ++ Glob.show.go(a, Glob.show.go(b, "}" ++ rest))
    case Spec.Alt{a, b}:
      "{" ++ Glob.show.go(a, "," ++ Glob.show.go(b, "}" ++ rest))

def Spec.Glob.show(g):
  Glob.show.go(g, "")

# the glob that the text of Deep reads back as
def Show.deep() -> Spec.Glob:
  dirs = {
    Spec.Alt{
      Spec.Eps{},
      Spec.Alt{Spec.Cat{Spec.Lit{Chr{47}}, Spec.Cat{Spec.Deep{}, Spec.Eps{}}}, Spec.Void{}}
    }: Spec.Glob
  }
  Spec.Alt{Spec.Cat{Spec.Star{}, Spec.Cat{dirs, Spec.Eps{}}}, Spec.Void{}}

# the glob that the text of g reads back as
# bend-lint: expect-begin bend-lint-rules/performance/missed_fork@hint -- a glob tree is a few nodes, where a fork costs more than it saves
def Show.glob(g: Spec.Glob) -> Spec.Glob:
  match g:
    case Spec.Void{}:
      Spec.Class{False{}, []}
    case Spec.Eps{}:
      Spec.Alt{Spec.Eps{}, Spec.Void{}}
    case Spec.Lit{c}:
      Spec.Lit{c}
    case Spec.Any{}:
      Spec.Any{}
    case Spec.Star{}:
      Spec.Alt{Spec.Cat{Spec.Star{}, Spec.Eps{}}, Spec.Void{}}
    case Spec.Class{neg, cs}:
      Spec.Class{neg, List.reverse(&2, Char, cs)}
    case Spec.Deep{}:
      Show.deep()
    case Spec.Cat{a, b}:
      Spec.Alt{Spec.Cat{Show.glob(a), Spec.Cat{Show.glob(b), Spec.Eps{}}}, Spec.Void{}}
    case Spec.Alt{a, b}:
      Spec.Alt{
        Spec.Cat{Show.glob(a), Spec.Eps{}},
        Spec.Alt{Spec.Cat{Show.glob(b), Spec.Eps{}}, Spec.Void{}}
      }
# bend-lint: expect-end bend-lint-rules/performance/missed_fork@hint

# Parser steps
# ------------
# The parser looks up to three symbols ahead, so each step lemma splits the
# unknown symbols it looks at.

# a plain character is a Lit
def Step.char(
  x: Char,
  l: List<&2, Spec.Sym>,
  st: List<&2, Spec.Frame>,
  seg: Bool
) -> {
  Spec.Glob.read.go(
    l,
    Spec.Out{},
    Spec.Frame.add(st, Spec.Lit{x}),
    False{}
  )
    == Spec.Glob.read.go(Con{Spec.SChar{x}, l}, Spec.Out{}, st, seg): Maybe<&2, Spec.Glob>
}:
  match l:
    case Nil{}:
      {==}
    case Con{y1, l2}:
      match y1:
        case Spec.SEsc{}:
          {==}
        case Spec.SAny{}:
          {==}
        case Spec.SStar{}:
          match l2:
            case Nil{}:
              {==}
            case Con{y6, l7}:
              match y6:
                case Spec.SEsc{}:
                  {==}
                case Spec.SAny{}:
                  {==}
                case Spec.SStar{}:
                  {==}
                case Spec.SSlash{}:
                  {==}
                case Spec.SOpen{}:
                  {==}
                case Spec.SComma{}:
                  {==}
                case Spec.SClose{}:
                  {==}
                case Spec.SLeft{}:
                  {==}
                case Spec.SRight{}:
                  {==}
                case Spec.SBang{}:
                  {==}
                case Spec.SDash{}:
                  {==}
                case Spec.SChar{ch19}:
                  {==}
        case Spec.SSlash{}:
          {==}
        case Spec.SOpen{}:
          {==}
        case Spec.SComma{}:
          {==}
        case Spec.SClose{}:
          {==}
        case Spec.SLeft{}:
          {==}
        case Spec.SRight{}:
          {==}
        case Spec.SBang{}:
          {==}
        case Spec.SDash{}:
          match l2:
            case Nil{}:
              {==}
            case Con{y28, l29}:
              match y28:
                case Spec.SEsc{}:
                  {==}
                case Spec.SAny{}:
                  {==}
                case Spec.SStar{}:
                  {==}
                case Spec.SSlash{}:
                  {==}
                case Spec.SOpen{}:
                  {==}
                case Spec.SComma{}:
                  {==}
                case Spec.SClose{}:
                  {==}
                case Spec.SLeft{}:
                  {==}
                case Spec.SRight{}:
                  {==}
                case Spec.SBang{}:
                  {==}
                case Spec.SDash{}:
                  {==}
                case Spec.SChar{ch41}:
                  {==}
        case Spec.SChar{ch42}:
          {==}

# an escaped symbol is a Lit of its character
def Step.esc(
  y: Spec.Sym,
  l: List<&2, Spec.Sym>,
  st: List<&2, Spec.Frame>,
  seg: Bool
) -> {
  Spec.Glob.read.go(
    l,
    Spec.Out{},
    Spec.Frame.add(st, Spec.Lit{Spec.Sym.char(y)}),
    False{}
  )
    == Spec.Glob.read.go(Con{Spec.SEsc{}, Con{y, l}}, Spec.Out{}, st, seg): Maybe<&2, Spec.Glob>
}:
  match y:
    case Spec.SEsc{}:
      {==}
    case Spec.SAny{}:
      {==}
    case Spec.SStar{}:
      match l:
        case Nil{}:
          {==}
        case Con{y4, l5}:
          match y4:
            case Spec.SEsc{}:
              {==}
            case Spec.SAny{}:
              {==}
            case Spec.SStar{}:
              {==}
            case Spec.SSlash{}:
              {==}
            case Spec.SOpen{}:
              {==}
            case Spec.SComma{}:
              {==}
            case Spec.SClose{}:
              {==}
            case Spec.SLeft{}:
              {==}
            case Spec.SRight{}:
              {==}
            case Spec.SBang{}:
              {==}
            case Spec.SDash{}:
              {==}
            case Spec.SChar{ch17}:
              {==}
    case Spec.SSlash{}:
      {==}
    case Spec.SOpen{}:
      {==}
    case Spec.SComma{}:
      {==}
    case Spec.SClose{}:
      {==}
    case Spec.SLeft{}:
      {==}
    case Spec.SRight{}:
      {==}
    case Spec.SBang{}:
      {==}
    case Spec.SDash{}:
      match l:
        case Nil{}:
          {==}
        case Con{y26, l27}:
          match y26:
            case Spec.SEsc{}:
              {==}
            case Spec.SAny{}:
              {==}
            case Spec.SStar{}:
              {==}
            case Spec.SSlash{}:
              {==}
            case Spec.SOpen{}:
              {==}
            case Spec.SComma{}:
              {==}
            case Spec.SClose{}:
              {==}
            case Spec.SLeft{}:
              {==}
            case Spec.SRight{}:
              {==}
            case Spec.SBang{}:
              {==}
            case Spec.SDash{}:
              {==}
            case Spec.SChar{ch39}:
              {==}
    case Spec.SChar{ch40}:
      {==}

# `?` is Any
def Step.any(
  l: List<&2, Spec.Sym>,
  st: List<&2, Spec.Frame>,
  seg: Bool
) -> {
  Spec.Glob.read.go(
    l,
    Spec.Out{},
    Spec.Frame.add(st, Spec.Any{}),
    False{}
  )
    == Spec.Glob.read.go(Con{Spec.SAny{}, l}, Spec.Out{}, st, seg): Maybe<&2, Spec.Glob>
}:
  match l:
    case Nil{}:
      {==}
    case Con{y1, l2}:
      match y1:
        case Spec.SEsc{}:
          {==}
        case Spec.SAny{}:
          {==}
        case Spec.SStar{}:
          match l2:
            case Nil{}:
              {==}
            case Con{y6, l7}:
              match y6:
                case Spec.SEsc{}:
                  {==}
                case Spec.SAny{}:
                  {==}
                case Spec.SStar{}:
                  {==}
                case Spec.SSlash{}:
                  {==}
                case Spec.SOpen{}:
                  {==}
                case Spec.SComma{}:
                  {==}
                case Spec.SClose{}:
                  {==}
                case Spec.SLeft{}:
                  {==}
                case Spec.SRight{}:
                  {==}
                case Spec.SBang{}:
                  {==}
                case Spec.SDash{}:
                  {==}
                case Spec.SChar{ch19}:
                  {==}
        case Spec.SSlash{}:
          {==}
        case Spec.SOpen{}:
          {==}
        case Spec.SComma{}:
          {==}
        case Spec.SClose{}:
          {==}
        case Spec.SLeft{}:
          {==}
        case Spec.SRight{}:
          {==}
        case Spec.SBang{}:
          {==}
        case Spec.SDash{}:
          match l2:
            case Nil{}:
              {==}
            case Con{y28, l29}:
              match y28:
                case Spec.SEsc{}:
                  {==}
                case Spec.SAny{}:
                  {==}
                case Spec.SStar{}:
                  {==}
                case Spec.SSlash{}:
                  {==}
                case Spec.SOpen{}:
                  {==}
                case Spec.SComma{}:
                  {==}
                case Spec.SClose{}:
                  {==}
                case Spec.SLeft{}:
                  {==}
                case Spec.SRight{}:
                  {==}
                case Spec.SBang{}:
                  {==}
                case Spec.SDash{}:
                  {==}
                case Spec.SChar{ch41}:
                  {==}
        case Spec.SChar{ch42}:
          {==}

# `{` opens a frame
def Step.open(
  l: List<&2, Spec.Sym>,
  st: List<&2, Spec.Frame>,
  seg: Bool
) -> {
  Spec.Glob.read.go(
    l,
    Spec.Out{},
    Con{Spec.Frame{[], [], seg}, st},
    seg
  )
    == Spec.Glob.read.go(Con{Spec.SOpen{}, l}, Spec.Out{}, st, seg): Maybe<&2, Spec.Glob>
}:
  match l:
    case Nil{}:
      {==}
    case Con{y1, l2}:
      match y1:
        case Spec.SEsc{}:
          {==}
        case Spec.SAny{}:
          {==}
        case Spec.SStar{}:
          match l2:
            case Nil{}:
              {==}
            case Con{y6, l7}:
              match y6:
                case Spec.SEsc{}:
                  {==}
                case Spec.SAny{}:
                  {==}
                case Spec.SStar{}:
                  {==}
                case Spec.SSlash{}:
                  {==}
                case Spec.SOpen{}:
                  {==}
                case Spec.SComma{}:
                  {==}
                case Spec.SClose{}:
                  {==}
                case Spec.SLeft{}:
                  {==}
                case Spec.SRight{}:
                  {==}
                case Spec.SBang{}:
                  {==}
                case Spec.SDash{}:
                  {==}
                case Spec.SChar{ch19}:
                  {==}
        case Spec.SSlash{}:
          {==}
        case Spec.SOpen{}:
          {==}
        case Spec.SComma{}:
          {==}
        case Spec.SClose{}:
          {==}
        case Spec.SLeft{}:
          {==}
        case Spec.SRight{}:
          {==}
        case Spec.SBang{}:
          {==}
        case Spec.SDash{}:
          match l2:
            case Nil{}:
              {==}
            case Con{y28, l29}:
              match y28:
                case Spec.SEsc{}:
                  {==}
                case Spec.SAny{}:
                  {==}
                case Spec.SStar{}:
                  {==}
                case Spec.SSlash{}:
                  {==}
                case Spec.SOpen{}:
                  {==}
                case Spec.SComma{}:
                  {==}
                case Spec.SClose{}:
                  {==}
                case Spec.SLeft{}:
                  {==}
                case Spec.SRight{}:
                  {==}
                case Spec.SBang{}:
                  {==}
                case Spec.SDash{}:
                  {==}
                case Spec.SChar{ch41}:
                  {==}
        case Spec.SChar{ch42}:
          {==}

# `}` closes a frame into one Alt
def Step.close(
  l: List<&2, Spec.Sym>,
  a: List<&2, Spec.Glob>,
  s: List<&2, Spec.Glob>,
  b: Bool,
  f: Spec.Frame,
  r: List<&2, Spec.Frame>,
  seg: Bool
) -> {
  Spec.Glob.read.go(
    l,
    Spec.Out{},
    Spec.Frame.add(
      Con{f, r},
      Spec.Glob.of_alts(Con{Spec.Glob.of_seq(s, Spec.Eps{}), a}, Spec.Void{})
    ),
    False{}
  )
    == Spec.Glob.read.go(
      Con{Spec.SClose{}, l},
      Spec.Out{},
      Con{Spec.Frame{a, s, b}, Con{f, r}},
      seg
    ): Maybe<&2, Spec.Glob>
}:
  match l:
    case Nil{}:
      {==}
    case Con{y1, l2}:
      match y1:
        case Spec.SEsc{}:
          {==}
        case Spec.SAny{}:
          {==}
        case Spec.SStar{}:
          match l2:
            case Nil{}:
              {==}
            case Con{y6, l7}:
              match y6:
                case Spec.SEsc{}:
                  {==}
                case Spec.SAny{}:
                  {==}
                case Spec.SStar{}:
                  {==}
                case Spec.SSlash{}:
                  {==}
                case Spec.SOpen{}:
                  {==}
                case Spec.SComma{}:
                  {==}
                case Spec.SClose{}:
                  {==}
                case Spec.SLeft{}:
                  {==}
                case Spec.SRight{}:
                  {==}
                case Spec.SBang{}:
                  {==}
                case Spec.SDash{}:
                  {==}
                case Spec.SChar{ch19}:
                  {==}
        case Spec.SSlash{}:
          {==}
        case Spec.SOpen{}:
          {==}
        case Spec.SComma{}:
          {==}
        case Spec.SClose{}:
          {==}
        case Spec.SLeft{}:
          {==}
        case Spec.SRight{}:
          {==}
        case Spec.SBang{}:
          {==}
        case Spec.SDash{}:
          match l2:
            case Nil{}:
              {==}
            case Con{y28, l29}:
              match y28:
                case Spec.SEsc{}:
                  {==}
                case Spec.SAny{}:
                  {==}
                case Spec.SStar{}:
                  {==}
                case Spec.SSlash{}:
                  {==}
                case Spec.SOpen{}:
                  {==}
                case Spec.SComma{}:
                  {==}
                case Spec.SClose{}:
                  {==}
                case Spec.SLeft{}:
                  {==}
                case Spec.SRight{}:
                  {==}
                case Spec.SBang{}:
                  {==}
                case Spec.SDash{}:
                  {==}
                case Spec.SChar{ch41}:
                  {==}
        case Spec.SChar{ch42}:
          {==}

# `,` starts the next alternative
def Step.comma(
  l: List<&2, Spec.Sym>,
  a: List<&2, Spec.Glob>,
  s: List<&2, Spec.Glob>,
  b: Bool,
  f: Spec.Frame,
  r: List<&2, Spec.Frame>,
  seg: Bool
) -> {
  Spec.Glob.read.go(
    l,
    Spec.Out{},
    Con{Spec.Frame{Con{Spec.Glob.of_seq(s, Spec.Eps{}), a}, [], b}, Con{f, r}},
    b
  )
    == Spec.Glob.read.go(
      Con{Spec.SComma{}, l},
      Spec.Out{},
      Con{Spec.Frame{a, s, b}, Con{f, r}},
      seg
    ): Maybe<&2, Spec.Glob>
}:
  match l:
    case Nil{}:
      {==}
    case Con{y1, l2}:
      match y1:
        case Spec.SEsc{}:
          {==}
        case Spec.SAny{}:
          {==}
        case Spec.SStar{}:
          match l2:
            case Nil{}:
              {==}
            case Con{y6, l7}:
              match y6:
                case Spec.SEsc{}:
                  {==}
                case Spec.SAny{}:
                  {==}
                case Spec.SStar{}:
                  {==}
                case Spec.SSlash{}:
                  {==}
                case Spec.SOpen{}:
                  {==}
                case Spec.SComma{}:
                  {==}
                case Spec.SClose{}:
                  {==}
                case Spec.SLeft{}:
                  {==}
                case Spec.SRight{}:
                  {==}
                case Spec.SBang{}:
                  {==}
                case Spec.SDash{}:
                  {==}
                case Spec.SChar{ch19}:
                  {==}
        case Spec.SSlash{}:
          {==}
        case Spec.SOpen{}:
          {==}
        case Spec.SComma{}:
          {==}
        case Spec.SClose{}:
          {==}
        case Spec.SLeft{}:
          {==}
        case Spec.SRight{}:
          {==}
        case Spec.SBang{}:
          {==}
        case Spec.SDash{}:
          match l2:
            case Nil{}:
              {==}
            case Con{y28, l29}:
              match y28:
                case Spec.SEsc{}:
                  {==}
                case Spec.SAny{}:
                  {==}
                case Spec.SStar{}:
                  {==}
                case Spec.SSlash{}:
                  {==}
                case Spec.SOpen{}:
                  {==}
                case Spec.SComma{}:
                  {==}
                case Spec.SClose{}:
                  {==}
                case Spec.SLeft{}:
                  {==}
                case Spec.SRight{}:
                  {==}
                case Spec.SBang{}:
                  {==}
                case Spec.SDash{}:
                  {==}
                case Spec.SChar{ch41}:
                  {==}
        case Spec.SChar{ch42}:
          {==}

# `*` before `}` is Star
def Step.star(
  l: List<&2, Spec.Sym>,
  st: List<&2, Spec.Frame>,
  seg: Bool
) -> {
  Spec.Glob.read.go(
    Con{Spec.SClose{}, l},
    Spec.Out{},
    Spec.Frame.add(st, Spec.Star{}),
    False{}
  )
    == Spec.Glob.read.go(
      Con{Spec.SStar{}, Con{Spec.SClose{}, l}},
      Spec.Out{},
      st,
      seg
    ): Maybe<&2, Spec.Glob>
}:
  match l:
    case Nil{}:
      {==}
    case Con{y1, l2}:
      match y1:
        case Spec.SEsc{}:
          {==}
        case Spec.SAny{}:
          {==}
        case Spec.SStar{}:
          match l2:
            case Nil{}:
              {==}
            case Con{y6, l7}:
              match y6:
                case Spec.SEsc{}:
                  {==}
                case Spec.SAny{}:
                  {==}
                case Spec.SStar{}:
                  {==}
                case Spec.SSlash{}:
                  {==}
                case Spec.SOpen{}:
                  {==}
                case Spec.SComma{}:
                  {==}
                case Spec.SClose{}:
                  {==}
                case Spec.SLeft{}:
                  {==}
                case Spec.SRight{}:
                  {==}
                case Spec.SBang{}:
                  {==}
                case Spec.SDash{}:
                  {==}
                case Spec.SChar{ch19}:
                  {==}
        case Spec.SSlash{}:
          {==}
        case Spec.SOpen{}:
          {==}
        case Spec.SComma{}:
          {==}
        case Spec.SClose{}:
          {==}
        case Spec.SLeft{}:
          {==}
        case Spec.SRight{}:
          {==}
        case Spec.SBang{}:
          {==}
        case Spec.SDash{}:
          match l2:
            case Nil{}:
              {==}
            case Con{y28, l29}:
              match y28:
                case Spec.SEsc{}:
                  {==}
                case Spec.SAny{}:
                  {==}
                case Spec.SStar{}:
                  {==}
                case Spec.SSlash{}:
                  {==}
                case Spec.SOpen{}:
                  {==}
                case Spec.SComma{}:
                  {==}
                case Spec.SClose{}:
                  {==}
                case Spec.SLeft{}:
                  {==}
                case Spec.SRight{}:
                  {==}
                case Spec.SBang{}:
                  {==}
                case Spec.SDash{}:
                  {==}
                case Spec.SChar{ch41}:
                  {==}
        case Spec.SChar{ch42}:
          {==}

# `[` before an escape opens a class
def Step.left_esc(
  l: List<&2, Spec.Sym>,
  st: List<&2, Spec.Frame>,
  seg: Bool
) -> {
  Spec.Glob.read.go(
    Con{Spec.SEsc{}, l},
    Spec.In{False{}, []},
    st,
    seg
  )
    == Spec.Glob.read.go(
      Con{Spec.SLeft{}, Con{Spec.SEsc{}, l}},
      Spec.Out{},
      st,
      seg
    ): Maybe<&2, Spec.Glob>
}:
  match l:
    case Nil{}:
      {==}
    case Con{y1, l2}:
      match y1:
        case Spec.SEsc{}:
          {==}
        case Spec.SAny{}:
          {==}
        case Spec.SStar{}:
          match l2:
            case Nil{}:
              {==}
            case Con{y6, l7}:
              match y6:
                case Spec.SEsc{}:
                  {==}
                case Spec.SAny{}:
                  {==}
                case Spec.SStar{}:
                  {==}
                case Spec.SSlash{}:
                  {==}
                case Spec.SOpen{}:
                  {==}
                case Spec.SComma{}:
                  {==}
                case Spec.SClose{}:
                  {==}
                case Spec.SLeft{}:
                  {==}
                case Spec.SRight{}:
                  {==}
                case Spec.SBang{}:
                  {==}
                case Spec.SDash{}:
                  {==}
                case Spec.SChar{ch19}:
                  {==}
        case Spec.SSlash{}:
          {==}
        case Spec.SOpen{}:
          {==}
        case Spec.SComma{}:
          {==}
        case Spec.SClose{}:
          {==}
        case Spec.SLeft{}:
          {==}
        case Spec.SRight{}:
          {==}
        case Spec.SBang{}:
          {==}
        case Spec.SDash{}:
          match l2:
            case Nil{}:
              {==}
            case Con{y28, l29}:
              match y28:
                case Spec.SEsc{}:
                  {==}
                case Spec.SAny{}:
                  {==}
                case Spec.SStar{}:
                  {==}
                case Spec.SSlash{}:
                  {==}
                case Spec.SOpen{}:
                  {==}
                case Spec.SComma{}:
                  {==}
                case Spec.SClose{}:
                  {==}
                case Spec.SLeft{}:
                  {==}
                case Spec.SRight{}:
                  {==}
                case Spec.SBang{}:
                  {==}
                case Spec.SDash{}:
                  {==}
                case Spec.SChar{ch41}:
                  {==}
        case Spec.SChar{ch42}:
          {==}

# `[` before `]` opens a class
def Step.left_right(
  l: List<&2, Spec.Sym>,
  st: List<&2, Spec.Frame>,
  seg: Bool
) -> {
  Spec.Glob.read.go(
    Con{Spec.SRight{}, l},
    Spec.In{False{}, []},
    st,
    seg
  )
    == Spec.Glob.read.go(
      Con{Spec.SLeft{}, Con{Spec.SRight{}, l}},
      Spec.Out{},
      st,
      seg
    ): Maybe<&2, Spec.Glob>
}:
  match l:
    case Nil{}:
      {==}
    case Con{y1, l2}:
      match y1:
        case Spec.SEsc{}:
          {==}
        case Spec.SAny{}:
          {==}
        case Spec.SStar{}:
          match l2:
            case Nil{}:
              {==}
            case Con{y6, l7}:
              match y6:
                case Spec.SEsc{}:
                  {==}
                case Spec.SAny{}:
                  {==}
                case Spec.SStar{}:
                  {==}
                case Spec.SSlash{}:
                  {==}
                case Spec.SOpen{}:
                  {==}
                case Spec.SComma{}:
                  {==}
                case Spec.SClose{}:
                  {==}
                case Spec.SLeft{}:
                  {==}
                case Spec.SRight{}:
                  {==}
                case Spec.SBang{}:
                  {==}
                case Spec.SDash{}:
                  {==}
                case Spec.SChar{ch19}:
                  {==}
        case Spec.SSlash{}:
          {==}
        case Spec.SOpen{}:
          {==}
        case Spec.SComma{}:
          {==}
        case Spec.SClose{}:
          {==}
        case Spec.SLeft{}:
          {==}
        case Spec.SRight{}:
          {==}
        case Spec.SBang{}:
          {==}
        case Spec.SDash{}:
          match l2:
            case Nil{}:
              {==}
            case Con{y28, l29}:
              match y28:
                case Spec.SEsc{}:
                  {==}
                case Spec.SAny{}:
                  {==}
                case Spec.SStar{}:
                  {==}
                case Spec.SSlash{}:
                  {==}
                case Spec.SOpen{}:
                  {==}
                case Spec.SComma{}:
                  {==}
                case Spec.SClose{}:
                  {==}
                case Spec.SLeft{}:
                  {==}
                case Spec.SRight{}:
                  {==}
                case Spec.SBang{}:
                  {==}
                case Spec.SDash{}:
                  {==}
                case Spec.SChar{ch41}:
                  {==}
        case Spec.SChar{ch42}:
          {==}

# `[!` opens a negated class
def Step.left_bang(
  l: List<&2, Spec.Sym>,
  st: List<&2, Spec.Frame>,
  seg: Bool
) -> {
  Spec.Glob.read.go(
    l,
    Spec.In{True{}, []},
    st,
    seg
  )
    == Spec.Glob.read.go(
      Con{Spec.SLeft{}, Con{Spec.SBang{}, l}},
      Spec.Out{},
      st,
      seg
    ): Maybe<&2, Spec.Glob>
}:
  match l:
    case Nil{}:
      {==}
    case Con{y1, l2}:
      match y1:
        case Spec.SEsc{}:
          {==}
        case Spec.SAny{}:
          {==}
        case Spec.SStar{}:
          match l2:
            case Nil{}:
              {==}
            case Con{y6, l7}:
              match y6:
                case Spec.SEsc{}:
                  {==}
                case Spec.SAny{}:
                  {==}
                case Spec.SStar{}:
                  {==}
                case Spec.SSlash{}:
                  {==}
                case Spec.SOpen{}:
                  {==}
                case Spec.SComma{}:
                  {==}
                case Spec.SClose{}:
                  {==}
                case Spec.SLeft{}:
                  {==}
                case Spec.SRight{}:
                  {==}
                case Spec.SBang{}:
                  {==}
                case Spec.SDash{}:
                  {==}
                case Spec.SChar{ch19}:
                  {==}
        case Spec.SSlash{}:
          {==}
        case Spec.SOpen{}:
          {==}
        case Spec.SComma{}:
          {==}
        case Spec.SClose{}:
          {==}
        case Spec.SLeft{}:
          {==}
        case Spec.SRight{}:
          {==}
        case Spec.SBang{}:
          {==}
        case Spec.SDash{}:
          match l2:
            case Nil{}:
              {==}
            case Con{y28, l29}:
              match y28:
                case Spec.SEsc{}:
                  {==}
                case Spec.SAny{}:
                  {==}
                case Spec.SStar{}:
                  {==}
                case Spec.SSlash{}:
                  {==}
                case Spec.SOpen{}:
                  {==}
                case Spec.SComma{}:
                  {==}
                case Spec.SClose{}:
                  {==}
                case Spec.SLeft{}:
                  {==}
                case Spec.SRight{}:
                  {==}
                case Spec.SBang{}:
                  {==}
                case Spec.SDash{}:
                  {==}
                case Spec.SChar{ch41}:
                  {==}
        case Spec.SChar{ch42}:
          {==}

# an escaped symbol in a class adds its character
def Step.esc_in(
  y: Spec.Sym,
  l: List<&2, Spec.Sym>,
  n: Bool,
  cs: List<&2, Char>,
  st: List<&2, Spec.Frame>,
  seg: Bool
) -> {
  Spec.Glob.read.go(
    l,
    Spec.In{n, Con{Spec.Sym.char(y), cs}},
    st,
    seg
  )
    == Spec.Glob.read.go(Con{Spec.SEsc{}, Con{y, l}}, Spec.In{n, cs}, st, seg): Maybe<&2, Spec.Glob>
}:
  match y:
    case Spec.SEsc{}:
      {==}
    case Spec.SAny{}:
      {==}
    case Spec.SStar{}:
      match l:
        case Nil{}:
          {==}
        case Con{y4, l5}:
          match y4:
            case Spec.SEsc{}:
              {==}
            case Spec.SAny{}:
              {==}
            case Spec.SStar{}:
              {==}
            case Spec.SSlash{}:
              {==}
            case Spec.SOpen{}:
              {==}
            case Spec.SComma{}:
              {==}
            case Spec.SClose{}:
              {==}
            case Spec.SLeft{}:
              {==}
            case Spec.SRight{}:
              {==}
            case Spec.SBang{}:
              {==}
            case Spec.SDash{}:
              {==}
            case Spec.SChar{ch17}:
              {==}
    case Spec.SSlash{}:
      {==}
    case Spec.SOpen{}:
      {==}
    case Spec.SComma{}:
      {==}
    case Spec.SClose{}:
      {==}
    case Spec.SLeft{}:
      {==}
    case Spec.SRight{}:
      {==}
    case Spec.SBang{}:
      {==}
    case Spec.SDash{}:
      match l:
        case Nil{}:
          {==}
        case Con{y26, l27}:
          match y26:
            case Spec.SEsc{}:
              {==}
            case Spec.SAny{}:
              {==}
            case Spec.SStar{}:
              {==}
            case Spec.SSlash{}:
              {==}
            case Spec.SOpen{}:
              {==}
            case Spec.SComma{}:
              {==}
            case Spec.SClose{}:
              {==}
            case Spec.SLeft{}:
              {==}
            case Spec.SRight{}:
              {==}
            case Spec.SBang{}:
              {==}
            case Spec.SDash{}:
              {==}
            case Spec.SChar{ch39}:
              {==}
    case Spec.SChar{ch40}:
      {==}

# `]` closes a class
def Step.right(
  l: List<&2, Spec.Sym>,
  n: Bool,
  cs: List<&2, Char>,
  st: List<&2, Spec.Frame>,
  seg: Bool
) -> {
  Spec.Glob.read.go(
    l,
    Spec.Out{},
    Spec.Frame.add(st, Spec.Class{n, cs}),
    False{}
  )
    == Spec.Glob.read.go(Con{Spec.SRight{}, l}, Spec.In{n, cs}, st, seg): Maybe<&2, Spec.Glob>
}:
  match l:
    case Nil{}:
      {==}
    case Con{y1, l2}:
      match y1:
        case Spec.SEsc{}:
          {==}
        case Spec.SAny{}:
          {==}
        case Spec.SStar{}:
          match l2:
            case Nil{}:
              {==}
            case Con{y6, l7}:
              match y6:
                case Spec.SEsc{}:
                  {==}
                case Spec.SAny{}:
                  {==}
                case Spec.SStar{}:
                  {==}
                case Spec.SSlash{}:
                  {==}
                case Spec.SOpen{}:
                  {==}
                case Spec.SComma{}:
                  {==}
                case Spec.SClose{}:
                  {==}
                case Spec.SLeft{}:
                  {==}
                case Spec.SRight{}:
                  {==}
                case Spec.SBang{}:
                  {==}
                case Spec.SDash{}:
                  {==}
                case Spec.SChar{ch19}:
                  {==}
        case Spec.SSlash{}:
          {==}
        case Spec.SOpen{}:
          {==}
        case Spec.SComma{}:
          {==}
        case Spec.SClose{}:
          {==}
        case Spec.SLeft{}:
          {==}
        case Spec.SRight{}:
          {==}
        case Spec.SBang{}:
          {==}
        case Spec.SDash{}:
          match l2:
            case Nil{}:
              {==}
            case Con{y28, l29}:
              match y28:
                case Spec.SEsc{}:
                  {==}
                case Spec.SAny{}:
                  {==}
                case Spec.SStar{}:
                  {==}
                case Spec.SSlash{}:
                  {==}
                case Spec.SOpen{}:
                  {==}
                case Spec.SComma{}:
                  {==}
                case Spec.SClose{}:
                  {==}
                case Spec.SLeft{}:
                  {==}
                case Spec.SRight{}:
                  {==}
                case Spec.SBang{}:
                  {==}
                case Spec.SDash{}:
                  {==}
                case Spec.SChar{ch41}:
                  {==}
        case Spec.SChar{ch42}:
          {==}

# `/` is a Lit that starts a segment
def Step.slash(
  l: List<&2, Spec.Sym>,
  st: List<&2, Spec.Frame>,
  seg: Bool
) -> {
  Spec.Glob.read.go(
    l,
    Spec.Out{},
    Spec.Frame.add(st, Spec.Lit{Chr{47}}),
    True{}
  )
    == Spec.Glob.read.go(Con{Spec.SSlash{}, l}, Spec.Out{}, st, seg): Maybe<&2, Spec.Glob>
}:
  match l:
    case Nil{}:
      {==}
    case Con{y1, l2}:
      match y1:
        case Spec.SEsc{}:
          {==}
        case Spec.SAny{}:
          {==}
        case Spec.SStar{}:
          match l2:
            case Nil{}:
              {==}
            case Con{y6, l7}:
              match y6:
                case Spec.SEsc{}:
                  {==}
                case Spec.SAny{}:
                  {==}
                case Spec.SStar{}:
                  {==}
                case Spec.SSlash{}:
                  {==}
                case Spec.SOpen{}:
                  {==}
                case Spec.SComma{}:
                  {==}
                case Spec.SClose{}:
                  {==}
                case Spec.SLeft{}:
                  {==}
                case Spec.SRight{}:
                  {==}
                case Spec.SBang{}:
                  {==}
                case Spec.SDash{}:
                  {==}
                case Spec.SChar{ch19}:
                  {==}
        case Spec.SSlash{}:
          {==}
        case Spec.SOpen{}:
          {==}
        case Spec.SComma{}:
          {==}
        case Spec.SClose{}:
          {==}
        case Spec.SLeft{}:
          {==}
        case Spec.SRight{}:
          {==}
        case Spec.SBang{}:
          {==}
        case Spec.SDash{}:
          match l2:
            case Nil{}:
              {==}
            case Con{y28, l29}:
              match y28:
                case Spec.SEsc{}:
                  {==}
                case Spec.SAny{}:
                  {==}
                case Spec.SStar{}:
                  {==}
                case Spec.SSlash{}:
                  {==}
                case Spec.SOpen{}:
                  {==}
                case Spec.SComma{}:
                  {==}
                case Spec.SClose{}:
                  {==}
                case Spec.SLeft{}:
                  {==}
                case Spec.SRight{}:
                  {==}
                case Spec.SBang{}:
                  {==}
                case Spec.SDash{}:
                  {==}
                case Spec.SChar{ch41}:
                  {==}
        case Spec.SChar{ch42}:
          {==}

# the text of Deep is one atom
def Step.deep(
  l: List<&2, Spec.Sym>,
  a: List<&2, Spec.Glob>,
  s: List<&2, Spec.Glob>,
  b: Bool,
  r: List<&2, Spec.Frame>,
  seg: Bool
) -> {
  Spec.Glob.read.go(
    l,
    Spec.Out{},
    Con{Spec.Frame{a, Con{Show.deep(), s}, b}, r},
    False{}
  )
    == Spec.Glob.read.go(
      Con{
        Spec.SOpen{},
        Con{
          Spec.SStar{},
          Con{
            Spec.SOpen{},
            Con{
              Spec.SComma{},
              Con{
                Spec.SSlash{},
                Con{Spec.SStar{}, Con{Spec.SStar{}, Con{Spec.SClose{}, Con{Spec.SClose{}, l}}}}
              }
            }
          }
        }
      },
      Spec.Out{},
      Con{Spec.Frame{a, s, b}, r},
      seg
    ): Maybe<&2, Spec.Glob>
}:
  match l:
    case Nil{}:
      {==}
    case Con{y1, l2}:
      match y1:
        case Spec.SEsc{}:
          {==}
        case Spec.SAny{}:
          {==}
        case Spec.SStar{}:
          match l2:
            case Nil{}:
              {==}
            case Con{y6, l7}:
              match y6:
                case Spec.SEsc{}:
                  {==}
                case Spec.SAny{}:
                  {==}
                case Spec.SStar{}:
                  {==}
                case Spec.SSlash{}:
                  {==}
                case Spec.SOpen{}:
                  {==}
                case Spec.SComma{}:
                  {==}
                case Spec.SClose{}:
                  {==}
                case Spec.SLeft{}:
                  {==}
                case Spec.SRight{}:
                  {==}
                case Spec.SBang{}:
                  {==}
                case Spec.SDash{}:
                  {==}
                case Spec.SChar{ch19}:
                  {==}
        case Spec.SSlash{}:
          {==}
        case Spec.SOpen{}:
          {==}
        case Spec.SComma{}:
          {==}
        case Spec.SClose{}:
          {==}
        case Spec.SLeft{}:
          {==}
        case Spec.SRight{}:
          {==}
        case Spec.SBang{}:
          {==}
        case Spec.SDash{}:
          match l2:
            case Nil{}:
              {==}
            case Con{y28, l29}:
              match y28:
                case Spec.SEsc{}:
                  {==}
                case Spec.SAny{}:
                  {==}
                case Spec.SStar{}:
                  {==}
                case Spec.SSlash{}:
                  {==}
                case Spec.SOpen{}:
                  {==}
                case Spec.SComma{}:
                  {==}
                case Spec.SClose{}:
                  {==}
                case Spec.SLeft{}:
                  {==}
                case Spec.SRight{}:
                  {==}
                case Spec.SBang{}:
                  {==}
                case Spec.SDash{}:
                  {==}
                case Spec.SChar{ch41}:
                  {==}
        case Spec.SChar{ch42}:
          {==}

# Parsing shown text
# ------------------

# reading escaped characters in a class conses each onto the class
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- only proofs use it; no program runs it
def Show.parse_chars(
  cs: List<&2, Char>,
  +rest: String,
  +n: Bool,
  +acc: List<&2, Char>,
  +st: List<&2, Spec.Frame>,
  +seg: Bool
) -> {
  Spec.Glob.read.go(
    Spec.Sym.list(rest),
    Spec.In{n, List.reverse.go(&2, Char, cs, acc)},
    st,
    seg
  )
    == Spec.Glob.read.go(
      Spec.Sym.list(Glob.show.chars(cs, rest)),
      Spec.In{n, acc},
      st,
      seg
    ): Maybe<&2, Spec.Glob>
}:
  match cs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      l = Spec.Sym.list(Glob.show.chars(t, rest))
      -tgt = Spec.Glob.read.go(
        Spec.Sym.list(rest),
        Spec.In{n, List.reverse.go(&2, Char, t, Con{h, acc})},
        st,
        seg
      )
      %Step.esc_in(Spec.Sym.of(h), l, n, acc, st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
      %Sym.char_of(
        h
      ): {tgt == Spec.Glob.read.go(l, Spec.In{n, Con{_, acc}}, st, seg): Maybe<&2, Spec.Glob>}
      Show.parse_chars(t, rest, n, Con{h, acc}, st, seg)
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# the text of Lit{c} reads back as Lit{c}, given k, the role of c
def Show.parse_lit(
  +c: Char,
  k: Spec.Sym,
  rest: String,
  +a: List<&2, Spec.Glob>,
  +s: List<&2, Spec.Glob>,
  +b: Bool,
  +r: List<&2, Spec.Frame>,
  seg: Bool
) -> {
  k == Spec.Sym.of(c): Spec.Sym
} -> {
  Spec.Glob.read.go(
    Spec.Sym.list(rest),
    Spec.Out{},
    Con{Spec.Frame{a, Con{Spec.Lit{c}, s}, b}, r},
    False{}
  )
    == Spec.Glob.read.go(
      Spec.Sym.list(Glob.show.char(c, k, rest)),
      Spec.Out{},
      Con{Spec.Frame{a, s, b}, r},
      seg
    ): Maybe<&2, Spec.Glob>
}:
  match k:
    case Spec.SChar{+x}:
      +e =>
        +l = Spec.Sym.list(rest)
        +st = {Con{Spec.Frame{a, s, b}, r}: List<&2, Spec.Frame>}
        +tgt = Spec.Glob.read.go(
          l,
          Spec.Out{},
          Con{Spec.Frame{a, Con{Spec.Lit{c}, s}, b}, r},
          False{}
        )
        %e: {tgt == Spec.Glob.read.go(Con{_, l}, Spec.Out{}, st, seg): Maybe<&2, Spec.Glob>}
        %Step.char(x, l, st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_is(
          c,
          Spec.SChar{x},
          e
        ): {
          tgt
            == Spec.Glob.read.go(
              l,
              Spec.Out{},
              Spec.Frame.add(st, Spec.Lit{_}),
              False{}
            ): Maybe<&2, Spec.Glob>
        }
        {==}
    case Spec.SEsc{}:
      e =>
        +l = Spec.Sym.list(rest)
        +st = {Con{Spec.Frame{a, s, b}, r}: List<&2, Spec.Frame>}
        +tgt = Spec.Glob.read.go(
          l,
          Spec.Out{},
          Con{Spec.Frame{a, Con{Spec.Lit{c}, s}, b}, r},
          False{}
        )
        %Step.esc(Spec.Sym.of(c), l, st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(
          c
        ): {
          tgt
            == Spec.Glob.read.go(
              l,
              Spec.Out{},
              Spec.Frame.add(st, Spec.Lit{_}),
              False{}
            ): Maybe<&2, Spec.Glob>
        }
        {==}
    case Spec.SAny{}:
      e =>
        +l = Spec.Sym.list(rest)
        +st = {Con{Spec.Frame{a, s, b}, r}: List<&2, Spec.Frame>}
        +tgt = Spec.Glob.read.go(
          l,
          Spec.Out{},
          Con{Spec.Frame{a, Con{Spec.Lit{c}, s}, b}, r},
          False{}
        )
        %Step.esc(Spec.Sym.of(c), l, st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(
          c
        ): {
          tgt
            == Spec.Glob.read.go(
              l,
              Spec.Out{},
              Spec.Frame.add(st, Spec.Lit{_}),
              False{}
            ): Maybe<&2, Spec.Glob>
        }
        {==}
    case Spec.SStar{}:
      e =>
        +l = Spec.Sym.list(rest)
        +st = {Con{Spec.Frame{a, s, b}, r}: List<&2, Spec.Frame>}
        +tgt = Spec.Glob.read.go(
          l,
          Spec.Out{},
          Con{Spec.Frame{a, Con{Spec.Lit{c}, s}, b}, r},
          False{}
        )
        %Step.esc(Spec.Sym.of(c), l, st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(
          c
        ): {
          tgt
            == Spec.Glob.read.go(
              l,
              Spec.Out{},
              Spec.Frame.add(st, Spec.Lit{_}),
              False{}
            ): Maybe<&2, Spec.Glob>
        }
        {==}
    case Spec.SSlash{}:
      e =>
        +l = Spec.Sym.list(rest)
        +st = {Con{Spec.Frame{a, s, b}, r}: List<&2, Spec.Frame>}
        +tgt = Spec.Glob.read.go(
          l,
          Spec.Out{},
          Con{Spec.Frame{a, Con{Spec.Lit{c}, s}, b}, r},
          False{}
        )
        %Step.esc(Spec.Sym.of(c), l, st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(
          c
        ): {
          tgt
            == Spec.Glob.read.go(
              l,
              Spec.Out{},
              Spec.Frame.add(st, Spec.Lit{_}),
              False{}
            ): Maybe<&2, Spec.Glob>
        }
        {==}
    case Spec.SOpen{}:
      e =>
        +l = Spec.Sym.list(rest)
        +st = {Con{Spec.Frame{a, s, b}, r}: List<&2, Spec.Frame>}
        +tgt = Spec.Glob.read.go(
          l,
          Spec.Out{},
          Con{Spec.Frame{a, Con{Spec.Lit{c}, s}, b}, r},
          False{}
        )
        %Step.esc(Spec.Sym.of(c), l, st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(
          c
        ): {
          tgt
            == Spec.Glob.read.go(
              l,
              Spec.Out{},
              Spec.Frame.add(st, Spec.Lit{_}),
              False{}
            ): Maybe<&2, Spec.Glob>
        }
        {==}
    case Spec.SComma{}:
      e =>
        +l = Spec.Sym.list(rest)
        +st = {Con{Spec.Frame{a, s, b}, r}: List<&2, Spec.Frame>}
        +tgt = Spec.Glob.read.go(
          l,
          Spec.Out{},
          Con{Spec.Frame{a, Con{Spec.Lit{c}, s}, b}, r},
          False{}
        )
        %Step.esc(Spec.Sym.of(c), l, st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(
          c
        ): {
          tgt
            == Spec.Glob.read.go(
              l,
              Spec.Out{},
              Spec.Frame.add(st, Spec.Lit{_}),
              False{}
            ): Maybe<&2, Spec.Glob>
        }
        {==}
    case Spec.SClose{}:
      e =>
        +l = Spec.Sym.list(rest)
        +st = {Con{Spec.Frame{a, s, b}, r}: List<&2, Spec.Frame>}
        +tgt = Spec.Glob.read.go(
          l,
          Spec.Out{},
          Con{Spec.Frame{a, Con{Spec.Lit{c}, s}, b}, r},
          False{}
        )
        %Step.esc(Spec.Sym.of(c), l, st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(
          c
        ): {
          tgt
            == Spec.Glob.read.go(
              l,
              Spec.Out{},
              Spec.Frame.add(st, Spec.Lit{_}),
              False{}
            ): Maybe<&2, Spec.Glob>
        }
        {==}
    case Spec.SLeft{}:
      e =>
        +l = Spec.Sym.list(rest)
        +st = {Con{Spec.Frame{a, s, b}, r}: List<&2, Spec.Frame>}
        +tgt = Spec.Glob.read.go(
          l,
          Spec.Out{},
          Con{Spec.Frame{a, Con{Spec.Lit{c}, s}, b}, r},
          False{}
        )
        %Step.esc(Spec.Sym.of(c), l, st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(
          c
        ): {
          tgt
            == Spec.Glob.read.go(
              l,
              Spec.Out{},
              Spec.Frame.add(st, Spec.Lit{_}),
              False{}
            ): Maybe<&2, Spec.Glob>
        }
        {==}
    case Spec.SRight{}:
      e =>
        +l = Spec.Sym.list(rest)
        +st = {Con{Spec.Frame{a, s, b}, r}: List<&2, Spec.Frame>}
        +tgt = Spec.Glob.read.go(
          l,
          Spec.Out{},
          Con{Spec.Frame{a, Con{Spec.Lit{c}, s}, b}, r},
          False{}
        )
        %Step.esc(Spec.Sym.of(c), l, st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(
          c
        ): {
          tgt
            == Spec.Glob.read.go(
              l,
              Spec.Out{},
              Spec.Frame.add(st, Spec.Lit{_}),
              False{}
            ): Maybe<&2, Spec.Glob>
        }
        {==}
    case Spec.SBang{}:
      e =>
        +l = Spec.Sym.list(rest)
        +st = {Con{Spec.Frame{a, s, b}, r}: List<&2, Spec.Frame>}
        +tgt = Spec.Glob.read.go(
          l,
          Spec.Out{},
          Con{Spec.Frame{a, Con{Spec.Lit{c}, s}, b}, r},
          False{}
        )
        %Step.esc(Spec.Sym.of(c), l, st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(
          c
        ): {
          tgt
            == Spec.Glob.read.go(
              l,
              Spec.Out{},
              Spec.Frame.add(st, Spec.Lit{_}),
              False{}
            ): Maybe<&2, Spec.Glob>
        }
        {==}
    case Spec.SDash{}:
      e =>
        +l = Spec.Sym.list(rest)
        +st = {Con{Spec.Frame{a, s, b}, r}: List<&2, Spec.Frame>}
        +tgt = Spec.Glob.read.go(
          l,
          Spec.Out{},
          Con{Spec.Frame{a, Con{Spec.Lit{c}, s}, b}, r},
          False{}
        )
        %Step.esc(Spec.Sym.of(c), l, st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(
          c
        ): {
          tgt
            == Spec.Glob.read.go(
              l,
              Spec.Out{},
              Spec.Frame.add(st, Spec.Lit{_}),
              False{}
            ): Maybe<&2, Spec.Glob>
        }
        {==}

# the text of a class reads back as the class, its characters reversed
def Show.parse_class(
  neg: Bool,
  cs: List<&2, Char>,
  +rest: String,
  +a: List<&2, Spec.Glob>,
  +s: List<&2, Spec.Glob>,
  +b: Bool,
  +r: List<&2, Spec.Frame>,
  +seg: Bool
) -> {
  Spec.Glob.read.go(
    Spec.Sym.list(rest),
    Spec.Out{},
    Con{Spec.Frame{a, Con{Show.glob(Spec.Class{neg, cs}), s}, b}, r},
    False{}
  )
    == Spec.Glob.read.go(
      Spec.Sym.list(Glob.show.go(Spec.Class{neg, cs}, rest)),
      Spec.Out{},
      Con{Spec.Frame{a, s, b}, r},
      seg
    ): Maybe<&2, Spec.Glob>
}:
  match neg cs:
    case True{} +cs:
      +l = Spec.Sym.list(rest)
      +st = {Con{Spec.Frame{a, s, b}, r}: List<&2, Spec.Frame>}
      tgt = Spec.Glob.read.go(
        l,
        Spec.Out{},
        Con{Spec.Frame{a, Con{Spec.Class{True{}, List.reverse(&2, Char, cs)}, s}, b}, r},
        False{}
      )
      lc = Spec.Sym.list(Glob.show.chars(cs, "]" ++ rest))
      %Step.left_bang(lc, st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
      %Show.parse_chars(cs, "]" ++ rest, True{}, [], st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
      %Step.right(l, True{}, List.reverse(&2, Char, cs), st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
      {==}
    case False{} Nil{}:
      +l = Spec.Sym.list(rest)
      +st = {Con{Spec.Frame{a, s, b}, r}: List<&2, Spec.Frame>}
      tgt = Spec.Glob.read.go(
        l,
        Spec.Out{},
        Con{Spec.Frame{a, Con{Spec.Class{False{}, []}, s}, b}, r},
        False{}
      )
      %Step.left_right(l, st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
      %Step.right(l, False{}, [], st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
      {==}
    case False{} Con{+h, +t}:
      +l = Spec.Sym.list(rest)
      +st = {Con{Spec.Frame{a, s, b}, r}: List<&2, Spec.Frame>}
      +rv = List.reverse(&2, Char, Con{h, t})
      tgt = Spec.Glob.read.go(
        l,
        Spec.Out{},
        Con{Spec.Frame{a, Con{Spec.Class{False{}, rv}, s}, b}, r},
        False{}
      )
      lc = Spec.Sym.list(SCon{h, Glob.show.chars(t, "]" ++ rest)})
      %Step.left_esc(lc, st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
      %Show.parse_chars(
        Con{h, t},
        "]" ++ rest,
        False{},
        [],
        st,
        seg
      ): {tgt == _: Maybe<&2, Spec.Glob>}
      %Step.right(l, False{}, rv, st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
      {==}

# the text of g, before rest, reads back as the one atom Show.glob(g)
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- only proofs use it; no program runs it
def Show.parse(
  g: Spec.Glob,
  +rest: String,
  +a: List<&2, Spec.Glob>,
  +s: List<&2, Spec.Glob>,
  +b: Bool,
  +r: List<&2, Spec.Frame>,
  +seg: Bool
) -> {
  Spec.Glob.read.go(
    Spec.Sym.list(rest),
    Spec.Out{},
    Con{Spec.Frame{a, Con{Show.glob(g), s}, b}, r},
    False{}
  )
    == Spec.Glob.read.go(
      Spec.Sym.list(Glob.show.go(g, rest)),
      Spec.Out{},
      Con{Spec.Frame{a, s, b}, r},
      seg
    ): Maybe<&2, Spec.Glob>
}:
  match g:
    case Spec.Void{}:
      +l = Spec.Sym.list(rest)
      +st = {Con{Spec.Frame{a, s, b}, r}: List<&2, Spec.Frame>}
      -tgt = Spec.Glob.read.go(
        l,
        Spec.Out{},
        Con{Spec.Frame{a, Con{Spec.Class{False{}, []}, s}, b}, r},
        False{}
      )
      %Step.left_right(l, st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
      %Step.right(l, False{}, [], st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
      {==}
    case Spec.Eps{}:
      +l = Spec.Sym.list(rest)
      st = {Con{Spec.Frame{a, s, b}, r}: List<&2, Spec.Frame>}
      -tgt = Spec.Glob.read.go(
        l,
        Spec.Out{},
        Con{Spec.Frame{a, Con{Spec.Alt{Spec.Eps{}, Spec.Void{}}, s}, b}, r},
        False{}
      )
      %Step.open(Con{Spec.SClose{}, l}, st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
      %Step.close(l, [], [], seg, Spec.Frame{a, s, b}, r, seg): {tgt == _: Maybe<&2, Spec.Glob>}
      {==}
    case Spec.Lit{+c}:
      Show.parse_lit(c, Spec.Sym.of(c), rest, a, s, b, r, seg)({==})
    case Spec.Any{}:
      Step.any(Spec.Sym.list(rest), Con{Spec.Frame{a, s, b}, r}, seg)
    case Spec.Star{}:
      +l = Spec.Sym.list(rest)
      +st = {Con{Spec.Frame{a, s, b}, r}: List<&2, Spec.Frame>}
      -tgt = Spec.Glob.read.go(
        l,
        Spec.Out{},
        Con{Spec.Frame{a, Con{Show.glob(Spec.Star{}), s}, b}, r},
        False{}
      )
      %Step.open(
        Con{Spec.SStar{}, Con{Spec.SClose{}, l}},
        st,
        seg
      ): {tgt == _: Maybe<&2, Spec.Glob>}
      %Step.star(l, Con{Spec.Frame{[], [], seg}, st}, seg): {tgt == _: Maybe<&2, Spec.Glob>}
      %Step.close(
        l,
        [],
        [Spec.Star{}],
        seg,
        Spec.Frame{a, s, b},
        r,
        False{}
      ): {tgt == _: Maybe<&2, Spec.Glob>}
      {==}
    case Spec.Class{neg, cs}:
      Show.parse_class(neg, cs, rest, a, s, b, r, seg)
    case Spec.Deep{}:
      Step.deep(Spec.Sym.list(rest), a, s, b, r, seg)
    case Spec.Cat{+x, +y}:
      +st = {Con{Spec.Frame{a, s, b}, r}: List<&2, Spec.Frame>}
      +ty = Glob.show.go(y, "}" ++ rest)
      tx = Glob.show.go(x, ty)
      +gx = Show.glob(x)
      gy = Show.glob(y)
      -tgt = Spec.Glob.read.go(
        Spec.Sym.list(rest),
        Spec.Out{},
        Con{Spec.Frame{a, Con{Show.glob(Spec.Cat{x, y}), s}, b}, r},
        False{}
      )
      %Step.open(Spec.Sym.list(tx), st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
      %Show.parse(x, ty, [], [], seg, st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
      %Show.parse(y, "}" ++ rest, [], [gx], seg, st, False{}): {tgt == _: Maybe<&2, Spec.Glob>}
      %Step.close(
        Spec.Sym.list(rest),
        [],
        [gy, gx],
        seg,
        Spec.Frame{a, s, b},
        r,
        False{}
      ): {tgt == _: Maybe<&2, Spec.Glob>}
      {==}
    case Spec.Alt{+x, +y}:
      +st = {Con{Spec.Frame{a, s, b}, r}: List<&2, Spec.Frame>}
      +ty = Glob.show.go(y, "}" ++ rest)
      tx = Glob.show.go(x, "," ++ ty)
      +gx = Show.glob(x)
      gy = Show.glob(y)
      +ax = {Spec.Cat{gx, Spec.Eps{}}: Spec.Glob}
      -tgt = Spec.Glob.read.go(
        Spec.Sym.list(rest),
        Spec.Out{},
        Con{Spec.Frame{a, Con{Show.glob(Spec.Alt{x, y}), s}, b}, r},
        False{}
      )
      %Step.open(Spec.Sym.list(tx), st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
      %Show.parse(x, "," ++ ty, [], [], seg, st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
      %Step.comma(
        Spec.Sym.list(ty),
        [],
        [gx],
        seg,
        Spec.Frame{a, s, b},
        r,
        False{}
      ): {tgt == _: Maybe<&2, Spec.Glob>}
      %Show.parse(y, "}" ++ rest, [ax], [], seg, st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
      %Step.close(
        Spec.Sym.list(rest),
        [ax],
        [gy],
        seg,
        Spec.Frame{a, s, b},
        r,
        False{}
      ): {tgt == _: Maybe<&2, Spec.Glob>}
      {==}
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# or is commutative
def Bool.or_comm(a: Bool, b: Bool) -> {Bool.or(a, b) == Bool.or(b, a): Bool}:
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

# Cat congruence
# --------------
# A proof that two globs match the same strings is a function, which Bend
# may use only once. So Cat congruence takes the finitely many equalities it
# needs for one string as data: the left sides agree on each prefix, the
# right sides on each suffix.

# what x must still match after it reads w
def Glob.walk(w: String, x: Spec.Glob) -> Spec.Glob:
  match w:
    case SNil{}:
      x
    case SCon{c, t}:
      Glob.walk(t, Spec.Glob.step(x, c))

# x matches w when what x must match after w matches ""
def Glob.walk_null(
  w: String,
  x: Spec.Glob
) -> {Spec.Glob.matches(w, x) == Spec.Glob.is_nullable(Glob.walk(w, x)): Bool}:
  match w:
    case SNil{}:
      {==}
    case SCon{c, t}:
      Glob.walk_null(t, Spec.Glob.step(x, c))

# walking pre then c is stepping by c after walking pre
def Glob.walk_snoc(
  pre: String,
  c: Char,
  x: Spec.Glob
) -> {
  Glob.walk(
    String.append(pre, SCon{c, SNil{}}),
    x
  )
    == Spec.Glob.step(Glob.walk(pre, x), c): Spec.Glob
}:
  match pre:
    case SNil{}:
      {==}
    case SCon{d, t}:
      Glob.walk_snoc(t, c, Spec.Glob.step(x, d))

# x matches pre and y matches what follows, at some cut of suf after pre
# bend-lint: expect-begin bend-lint-rules/performance/append_in_loop@warning -- only proofs use it; no program runs it
# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- only proofs use it; no program runs it
def Glob.split(suf: String, +pre: String, +x: Spec.Glob, +y: Spec.Glob) -> Bool:
  match suf:
    case SNil{}:
      Bool.or(Bool.and(Spec.Glob.matches(pre, x), Spec.Glob.matches(SNil{}, y)), False{})
    case SCon{+c, +t}:
      here = Bool.and(Spec.Glob.matches(pre, x), Spec.Glob.matches(SCon{c, t}, y))
      Bool.or(here, Glob.split(t, String.append(pre, SCon{c, SNil{}}), x, y))
# bend-lint: expect-end bend-lint-rules/performance/append_in_loop@warning
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# Cat{x after pre, y} matches suf exactly when some cut does
# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- only proofs use it; no program runs it
def Glob.cat_split(
  suf: String,
  +pre: String,
  +x: Spec.Glob,
  +y: Spec.Glob
) -> {Glob.split(suf, pre, x, y) == Spec.Glob.matches(suf, Spec.Cat{Glob.walk(pre, x), y}): Bool}:
  match suf:
    case SNil{}:
      l = Glob.split(SNil{}, pre, x, y)
      %Glob.walk_null(pre, x): {l == Bool.and(_, Spec.Glob.is_nullable(y)): Bool}
      +m = Bool.and(Spec.Glob.matches(pre, x), Spec.Glob.is_nullable(y))
      Equal.sym(Bool, m, Bool.or(m, False{}), Bool.or_false(m))
    case SCon{+c, +t}:
      +wx = Glob.walk(pre, x)
      +pc = String.append(pre, SCon{c, SNil{}})
      +ny = Spec.Glob.step(y, c)
      l = Glob.split(SCon{c, t}, pre, x, y)
      %Glob.alt_or(
        t,
        Spec.Cat{Spec.Glob.step(wx, c), y},
        Spec.Cat{Spec.Glob.of_bool(Spec.Glob.is_nullable(wx)), ny}
      ): {l == _: Bool}
      %Glob.cat_of_bool(
        t,
        Spec.Glob.is_nullable(wx),
        ny
      ): {l == Bool.or(Spec.Glob.matches(t, Spec.Cat{Spec.Glob.step(wx, c), y}), _): Bool}
      %Glob.walk_snoc(
        pre,
        c,
        x
      ): {
        l
          == Bool.or(
            Spec.Glob.matches(t, Spec.Cat{_, y}),
            Bool.and(Spec.Glob.is_nullable(wx), Spec.Glob.matches(t, ny))
          ): Bool
      }
      %Glob.cat_split(
        t,
        pc,
        x,
        y
      ): {l == Bool.or(_, Bool.and(Spec.Glob.is_nullable(wx), Spec.Glob.matches(t, ny))): Bool}
      %Glob.walk_null(
        pre,
        x
      ): {l == Bool.or(Glob.split(t, pc, x, y), Bool.and(_, Spec.Glob.matches(t, ny))): Bool}
      Bool.or_comm(
        Bool.and(Spec.Glob.matches(pre, x), Spec.Glob.matches(SCon{c, t}, y)),
        Glob.split(t, pc, x, y)
      )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# x and x2 agree on pre, and on pre followed by each prefix of suf
# bend-lint: expect-begin bend-lint-rules/performance/append_in_loop@warning -- only proofs use it; no program runs it
def Glob.AgreePre(x: Spec.Glob, x2: Spec.Glob, pre: String, suf: String) -> Type:
  match suf:
    case SNil{}:
      ({Spec.Glob.matches(pre, x) == Spec.Glob.matches(pre, x2): Bool} & Unit)
    case SCon{c, t}:
      (
        {
          Spec.Glob.matches(pre, x) == Spec.Glob.matches(pre, x2): Bool
        }
          & Glob.AgreePre(x, x2, String.append(pre, SCon{c, SNil{}}), t)
      )
# bend-lint: expect-end bend-lint-rules/performance/append_in_loop@warning

# y and y2 agree on each suffix of suf
def Glob.AgreeSuf(y: Spec.Glob, y2: Spec.Glob, suf: String) -> Type:
  match suf:
    case SNil{}:
      ({Spec.Glob.matches(SNil{}, y) == Spec.Glob.matches(SNil{}, y2): Bool} & Unit)
    case SCon{c, t}:
      (
        {
          Spec.Glob.matches(SCon{c, t}, y) == Spec.Glob.matches(SCon{c, t}, y2): Bool
        }
          & Glob.AgreeSuf(y, y2, t)
      )

# the cuts agree when the parts agree
def Glob.split_agree(
  suf: String,
  +pre: String,
  +x: Spec.Glob,
  x2: Spec.Glob,
  +y: Spec.Glob,
  y2: Spec.Glob,
  ea: Glob.AgreePre(x, x2, pre, suf),
  eb: Glob.AgreeSuf(y, y2, suf)
) -> {Glob.split(suf, pre, x, y) == Glob.split(suf, pre, x2, y2): Bool}:
  match suf:
    case SNil{}:
      (e1, u1) = ea
      (e2, u2) = eb
      l = Glob.split(SNil{}, pre, x, y)
      %e1: {l == Bool.or(Bool.and(_, Spec.Glob.matches(SNil{}, y2)), False{}): Bool}
      %e2: {l == Bool.or(Bool.and(Spec.Glob.matches(pre, x), _), False{}): Bool}
      {==}
    case SCon{+c, +t}:
      (e1, ra) = ea
      (e2, rb) = eb
      pc = String.append(pre, SCon{c, SNil{}})
      l = Glob.split(SCon{c, t}, pre, x, y)
      %e1: {
        l
          == Bool.or(
            Bool.and(_, Spec.Glob.matches(SCon{c, t}, y2)),
            Glob.split(t, pc, x2, y2)
          ): Bool
      }
      %e2: {l == Bool.or(Bool.and(Spec.Glob.matches(pre, x), _), Glob.split(t, pc, x2, y2)): Bool}
      %Glob.split_agree(
        t,
        pc,
        x,
        x2,
        y,
        y2,
        ra,
        rb
      ): {
        l == Bool.or(Bool.and(Spec.Glob.matches(pre, x), Spec.Glob.matches(SCon{c, t}, y)), _): Bool
      }
      {==}

# Cat of agreeing parts matches p the same way
def Glob.cat_agree(
  p: String,
  +x: Spec.Glob,
  +x2: Spec.Glob,
  +y: Spec.Glob,
  +y2: Spec.Glob,
  ea: Glob.AgreePre(x, x2, SNil{}, p),
  eb: Glob.AgreeSuf(y, y2, p)
) -> {Spec.Glob.matches(p, Spec.Cat{x, y}) == Spec.Glob.matches(p, Spec.Cat{x2, y2}): Bool}:
  +p = p
  %Glob.cat_split(p, SNil{}, x, y): {_ == Spec.Glob.matches(p, Spec.Cat{x2, y2}): Bool}
  %Glob.cat_split(p, SNil{}, x2, y2): {Glob.split(p, SNil{}, x, y) == _: Bool}
  Glob.split_agree(p, SNil{}, x, x2, y, y2, ea, eb)

# the Bool shape of one step of Chars.contains_rev
def Bool.contains_rev_step(
  e: Bool,
  t: Bool,
  a: Bool
) -> {Bool.or(Bool.or(e, t), a) == Bool.or(t, Bool.or(e, a)): Bool}:
  match e t a:
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

# Alt with Void matches what its left side matches
def Glob.alt_void(
  +p: String,
  +x: Spec.Glob
) -> {Spec.Glob.matches(p, x) == Spec.Glob.matches(p, Spec.Alt{x, Spec.Void{}}): Bool}:
  %Glob.alt_or(p, x, Spec.Void{}): {Spec.Glob.matches(p, x) == _: Bool}
  %Glob.void_never(p): {Spec.Glob.matches(p, x) == Bool.or(Spec.Glob.matches(p, x), _): Bool}
  Bool.or_false(Spec.Glob.matches(p, x))

# an empty class matches nothing, as Void
def Show.void_point(
  p: String
) -> {Spec.Glob.matches(p, Spec.Class{False{}, []}) == Spec.Glob.matches(p, Spec.Void{}): Bool}:
  match p:
    case SNil{}:
      {==}
    case SCon{c, t}:
      %Bool.and_false(
        Spec.is_inner(c)
      ): {Spec.Glob.matches(t, Spec.Glob.of_bool(_)) == Spec.Glob.matches(t, Spec.Void{}): Bool}
      {==}

# the text of Eps reads back as Eps
# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- a false positive, as the rule notes: the other use is an erased argument (of Equal.sym or a motive)
def Show.eps_point(
  p: String
) -> {
  Spec.Glob.matches(p, Spec.Alt{Spec.Eps{}, Spec.Void{}}) == Spec.Glob.matches(p, Spec.Eps{}): Bool
}:
  Equal.sym(
    Bool,
    Spec.Glob.matches(p, Spec.Eps{}),
    Spec.Glob.matches(p, Spec.Alt{Spec.Eps{}, Spec.Void{}}),
    Glob.alt_void(p, Spec.Eps{})
  )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# the text of Star reads back as Star
def Show.star_point(
  +p: String
) -> {
  Spec.Glob.matches(
    p,
    Spec.Alt{Spec.Cat{Spec.Star{}, Spec.Eps{}}, Spec.Void{}}
  )
    == Spec.Glob.matches(p, Spec.Star{}): Bool
}:
  %Glob.alt_void(
    p,
    Spec.Cat{Spec.Star{}, Spec.Eps{}}
  ): {_ == Spec.Glob.matches(p, Spec.Star{}): Bool}
  %Glob.cat_eps_r(p, Spec.Star{}): {_ == Spec.Glob.matches(p, Spec.Star{}): Bool}
  {==}

# a list holds c when its head is c or its tail holds c, given b, the first
def Chars.contains_con.at(
  h: Char,
  t: List<&2, Char>,
  c: Char,
  b: Bool
) -> {
  b == Char.is_eq(h, c): Bool
} -> {
  Bool.or(
    Char.is_eq(h, c),
    List.contains(~Char, ~Char.is_eq, t, c)
  )
    == List.contains(~Char, ~Char.is_eq, Con{h, t}, c): Bool
}:
  match b:
    case False{}:
      e =>
        %e: {
          Bool.or(
            _,
            List.contains(~Char, ~Char.is_eq, t, c)
          )
            == List.any.if(u => List.contains(~Char, ~Char.is_eq, t, c), _): Bool
        }
        {==}
    case True{}:
      e =>
        %e: {
          Bool.or(
            _,
            List.contains(~Char, ~Char.is_eq, t, c)
          )
            == List.any.if(u => List.contains(~Char, ~Char.is_eq, t, c), _): Bool
        }
        {==}

# a list holds c when its head is c or its tail holds c
def Chars.contains_con(
  +h: Char,
  t: List<&2, Char>,
  +c: Char
) -> {
  Bool.or(
    Char.is_eq(h, c),
    List.contains(~Char, ~Char.is_eq, t, c)
  )
    == List.contains(~Char, ~Char.is_eq, Con{h, t}, c): Bool
}:
  Chars.contains_con.at(h, t, c, Char.is_eq(h, c))({==})

# reversing xs onto acc holds c when xs or acc holds c
def Chars.contains_rev(
  xs: List<&2, Char>,
  +acc: List<&2, Char>,
  +c: Char
) -> {
  Bool.or(
    List.contains(~Char, ~Char.is_eq, xs, c),
    List.contains(~Char, ~Char.is_eq, acc, c)
  )
    == List.contains(~Char, ~Char.is_eq, List.reverse.go(&2, Char, xs, acc), c): Bool
}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      e = Char.is_eq(h, c)
      ct = List.contains(~Char, ~Char.is_eq, t, c)
      +ca = List.contains(~Char, ~Char.is_eq, acc, c)
      l = Bool.or(List.contains(~Char, ~Char.is_eq, Con{h, t}, c), ca)
      %Chars.contains_rev(t, Con{h, acc}, c): {l == _: Bool}
      %Chars.contains_con(h, acc, c): {l == Bool.or(ct, _): Bool}
      %Chars.contains_con(h, t, c): {Bool.or(_, ca) == Bool.or(ct, Bool.or(e, ca)): Bool}
      Bool.contains_rev_step(e, ct, ca)

# a class with its characters reversed matches the same strings
def Show.class_point(
  p: String,
  n: Bool,
  +cs: List<&2, Char>
) -> {
  Spec.Glob.matches(
    p,
    Spec.Class{n, List.reverse(&2, Char, cs)}
  )
    == Spec.Glob.matches(p, Spec.Class{n, cs}): Bool
}:
  match p:
    case SNil{}:
      {==}
    case SCon{+c, t}:
      i = Spec.is_inner(c)
      +k = List.contains(~Char, ~Char.is_eq, cs, c)
      r = Spec.Glob.matches(t, Spec.Glob.of_bool(Bool.and(i, Bool.xor(n, k))))
      %Chars.contains_rev(
        cs,
        [],
        c
      ): {Spec.Glob.matches(t, Spec.Glob.of_bool(Bool.and(i, Bool.xor(n, _)))) == r: Bool}
      %Bool.or_false(
        k
      ): {Spec.Glob.matches(t, Spec.Glob.of_bool(Bool.and(i, Bool.xor(n, _)))) == r: Bool}
      {==}

# Deep matches everything
def Glob.deep_true(p: String) -> {True{} == Spec.Glob.matches(p, Spec.Deep{}): Bool}:
  match p:
    case SNil{}:
      {==}
    case SCon{c, t}:
      Glob.deep_true(t)

# `/**` matches '/' and then anything
def Show.slash_deep(
  +t: String
) -> {
  True{}
    == Spec.Glob.matches(
      SCon{Chr{47}, t},
      Spec.Cat{Spec.Lit{Chr{47}}, Spec.Cat{Spec.Deep{}, Spec.Eps{}}}
    ): Bool
}:
  +de = {Spec.Cat{Spec.Deep{}, Spec.Eps{}}: Spec.Glob}
  x = Spec.Glob.step(de, Chr{47})
  %Glob.alt_or(t, Spec.Cat{Spec.Eps{}, de}, Spec.Cat{Spec.Void{}, x}): {True{} == _: Bool}
  %Glob.cat_eps_l(
    t,
    de
  ): {True{} == Bool.or(_, Spec.Glob.matches(t, Spec.Cat{Spec.Void{}, x})): Bool}
  %Glob.cat_eps_r(
    t,
    Spec.Deep{}
  ): {True{} == Bool.or(_, Spec.Glob.matches(t, Spec.Cat{Spec.Void{}, x})): Bool}
  %Glob.deep_true(t): {True{} == Bool.or(_, Spec.Glob.matches(t, Spec.Cat{Spec.Void{}, x})): Bool}
  {==}

# Show.star_k, one step, given b, the answer of c == '/'
# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- a false positive, as the rule notes: the other use is an erased argument (of Equal.sym or a motive)
def Show.star_k.at(
  c: Char,
  +t: String,
  b: Bool,
  ih: {
    True{}
      == Spec.Glob.matches(
        t,
        Spec.Cat{
          Spec.Star{},
          Spec.Cat{
            Spec.Alt{
              Spec.Eps{},
              Spec.Alt{Spec.Cat{Spec.Lit{Chr{47}}, Spec.Cat{Spec.Deep{}, Spec.Eps{}}}, Spec.Void{}}
            },
            Spec.Eps{}
          }
        }
      ): Bool
  }
) -> {
  b == Char.is_eq(c, Chr{47}): Bool
} -> {
  True{}
    == Spec.Glob.matches(
      SCon{c, t},
      Spec.Cat{
        Spec.Star{},
        Spec.Cat{
          Spec.Alt{
            Spec.Eps{},
            Spec.Alt{Spec.Cat{Spec.Lit{Chr{47}}, Spec.Cat{Spec.Deep{}, Spec.Eps{}}}, Spec.Void{}}
          },
          Spec.Eps{}
        }
      }
    ): Bool
}:
  match b:
    case False{}:
      e =>
        +ke = {
          Spec.Cat{
            Spec.Alt{
              Spec.Eps{},
              Spec.Alt{Spec.Cat{Spec.Lit{Chr{47}}, Spec.Cat{Spec.Deep{}, Spec.Eps{}}}, Spec.Void{}}
            },
            Spec.Eps{}
          }: Spec.Glob
        }
        +sk = {
          Spec.Cat{
            Spec.Star{},
            Spec.Cat{
              Spec.Alt{
                Spec.Eps{},
                Spec.Alt{
                  Spec.Cat{Spec.Lit{Chr{47}}, Spec.Cat{Spec.Deep{}, Spec.Eps{}}},
                  Spec.Void{}
                }
              },
              Spec.Eps{}
            }
          }: Spec.Glob
        }
        %e: {
          True{}
            == Spec.Glob.matches(
              t,
              Spec.Alt{
                Spec.Cat{Spec.Cat{Spec.Glob.of_bool(Bool.not(_)), Spec.Star{}}, ke},
                Spec.Cat{Spec.Eps{}, Spec.Glob.step(ke, c)}
              }
            ): Bool
        }
        %Glob.alt_or(
          t,
          Spec.Cat{Spec.Cat{Spec.Eps{}, Spec.Star{}}, ke},
          Spec.Cat{Spec.Eps{}, Spec.Glob.step(ke, c)}
        ):
          {True{} == _: Bool}
        %Glob.cat_assoc(t, Spec.Eps{}, Spec.Star{}, ke):
          {
            True{}
              == Bool.or(_, Spec.Glob.matches(t, Spec.Cat{Spec.Eps{}, Spec.Glob.step(ke, c)})): Bool
          }
        %Glob.cat_eps_l(
          t,
          sk
        ): {
          True{}
            == Bool.or(_, Spec.Glob.matches(t, Spec.Cat{Spec.Eps{}, Spec.Glob.step(ke, c)})): Bool
        }
        %ih: {
          True{}
            == Bool.or(_, Spec.Glob.matches(t, Spec.Cat{Spec.Eps{}, Spec.Glob.step(ke, c)})): Bool
        }
        {==}
    case True{}:
      e =>
        +ke = {
          Spec.Cat{
            Spec.Alt{
              Spec.Eps{},
              Spec.Alt{Spec.Cat{Spec.Lit{Chr{47}}, Spec.Cat{Spec.Deep{}, Spec.Eps{}}}, Spec.Void{}}
            },
            Spec.Eps{}
          }: Spec.Glob
        }
        +sk = {
          Spec.Cat{
            Spec.Star{},
            Spec.Cat{
              Spec.Alt{
                Spec.Eps{},
                Spec.Alt{
                  Spec.Cat{Spec.Lit{Chr{47}}, Spec.Cat{Spec.Deep{}, Spec.Eps{}}},
                  Spec.Void{}
                }
              },
              Spec.Eps{}
            }
          }: Spec.Glob
        }
        +ec = Char.is_eq_sound(c, Chr{47})(Equal.sym(Bool, True{}, Char.is_eq(c, Chr{47}), e))
        %Equal.sym(Char, c, Chr{47}, ec): {True{} == Spec.Glob.matches(SCon{_, t}, sk): Bool}
        +st = {Spec.Cat{Spec.Cat{Spec.Void{}, Spec.Star{}}, ke}: Spec.Glob}
        +x = Spec.Glob.step(ke, Chr{47})
        +p = {SCon{Chr{47}, t}: String}
        %Glob.alt_or(t, st, Spec.Cat{Spec.Eps{}, x}): {True{} == _: Bool}
        %Glob.cat_eps_l(t, x): {True{} == Bool.or(Spec.Glob.matches(t, st), _): Bool}
        %Glob.cat_eps_r(
          p,
          Spec.Alt{
            Spec.Eps{},
            Spec.Alt{Spec.Cat{Spec.Lit{Chr{47}}, Spec.Cat{Spec.Deep{}, Spec.Eps{}}}, Spec.Void{}}
          }
        ): {True{} == Bool.or(Spec.Glob.matches(t, st), _): Bool}
        %Glob.alt_or(
          p,
          Spec.Eps{},
          Spec.Alt{Spec.Cat{Spec.Lit{Chr{47}}, Spec.Cat{Spec.Deep{}, Spec.Eps{}}}, Spec.Void{}}
        ): {True{} == Bool.or(Spec.Glob.matches(t, st), _): Bool}
        %Glob.alt_void(
          p,
          Spec.Cat{Spec.Lit{Chr{47}}, Spec.Cat{Spec.Deep{}, Spec.Eps{}}}
        ): {
          True{}
            == Bool.or(Spec.Glob.matches(t, st), Bool.or(Spec.Glob.matches(p, Spec.Eps{}), _)): Bool
        }
        %Show.slash_deep(
          t
        ): {
          True{}
            == Bool.or(Spec.Glob.matches(t, st), Bool.or(Spec.Glob.matches(p, Spec.Eps{}), _)): Bool
        }
        %Equal.sym(
          Bool,
          Bool.or(Spec.Glob.matches(p, Spec.Eps{}), True{}),
          True{},
          Shared.Bool.or_true_right(Spec.Glob.matches(p, Spec.Eps{}))
        ): {True{} == Bool.or(Spec.Glob.matches(t, st), _): Bool}
        Equal.sym(
          Bool,
          Bool.or(Spec.Glob.matches(t, st), True{}),
          True{},
          Shared.Bool.or_true_right(Spec.Glob.matches(t, st))
        )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# `*` then optionally `/` and anything matches everything
def Show.star_k(
  p: String
) -> {
  True{}
    == Spec.Glob.matches(
      p,
      Spec.Cat{
        Spec.Star{},
        Spec.Cat{
          Spec.Alt{
            Spec.Eps{},
            Spec.Alt{Spec.Cat{Spec.Lit{Chr{47}}, Spec.Cat{Spec.Deep{}, Spec.Eps{}}}, Spec.Void{}}
          },
          Spec.Eps{}
        }
      }
    ): Bool
}:
  match p:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      Show.star_k.at(c, t, Char.is_eq(c, Chr{47}), Show.star_k(t))({==})

# the text of Deep reads back as Deep
def Show.deep_point(
  +p: String
) -> {Spec.Glob.matches(p, Show.deep()) == Spec.Glob.matches(p, Spec.Deep{}): Bool}:
  %Glob.alt_void(
    p,
    Spec.Cat{
      Spec.Star{},
      Spec.Cat{
        Spec.Alt{
          Spec.Eps{},
          Spec.Alt{Spec.Cat{Spec.Lit{Chr{47}}, Spec.Cat{Spec.Deep{}, Spec.Eps{}}}, Spec.Void{}}
        },
        Spec.Eps{}
      }
    }
  ): {_ == Spec.Glob.matches(p, Spec.Deep{}): Bool}
  %Show.star_k(p): {_ == Spec.Glob.matches(p, Spec.Deep{}): Bool}
  Glob.deep_true(p)

# the facts Show.ok gives about g at rank: 0, Show.glob(g) and g agree on suf;
# 1, they agree on pre and each longer prefix within suf; 2, on each suffix
def Show.Ok(+g: Spec.Glob, rank: Nat, suf: String, pre: String) -> Type:
  match rank:
    case 0n:
      {Spec.Glob.matches(suf, Show.glob(g)) == Spec.Glob.matches(suf, g): Bool}
    case 1n+k:
      match k:
        case 0n:
          Glob.AgreePre(Show.glob(g), g, pre, suf)
        case 1n+j:
          match j:
            case 0n:
              Glob.AgreeSuf(Show.glob(g), g, suf)
            case 1n+i:
              Unit

# Show.glob(g) matches what g matches. One def gives all three ranks, so the
# Cat case can ask for its parts' agreement chains as often as it needs.
# bend-lint: expect-begin bend-lint-rules/performance/append_in_loop@warning -- only proofs use it; no program runs it
# bend-lint: expect-begin bend-lint-rules/performance/missed_fork@hint -- only proofs use it; no program runs it
def Show.ok(+g: Spec.Glob, +rank: Nat, +suf: String, +pre: String) -> Show.Ok(g, rank, suf, pre):
  match g:
    case Spec.Void{}:
      match rank:
        case 0n:
          Show.void_point(suf)
        case 1n+k:
          match k:
            case 0n:
              match suf:
                case SNil{}:
                  (Show.ok(g, 0n, pre, SNil{}), Unit{})
                case SCon{c2, t}:
                  (
                    Show.ok(g, 0n, pre, SNil{}),
                    Show.ok(g, 1n, t, String.append(pre, SCon{c2, SNil{}}))
                  )
            case 1n+j:
              match j:
                case 0n:
                  match suf:
                    case SNil{}:
                      (Show.ok(g, 0n, SNil{}, pre), Unit{})
                    case SCon{c2, +t}:
                      (Show.ok(g, 0n, SCon{c2, t}, pre), Show.ok(g, 2n, t, pre))
                case 1n+i:
                  Unit{}
    case Spec.Eps{}:
      match rank:
        case 0n:
          Show.eps_point(suf)
        case 1n+k:
          match k:
            case 0n:
              match suf:
                case SNil{}:
                  (Show.ok(g, 0n, pre, SNil{}), Unit{})
                case SCon{c2, t}:
                  (
                    Show.ok(g, 0n, pre, SNil{}),
                    Show.ok(g, 1n, t, String.append(pre, SCon{c2, SNil{}}))
                  )
            case 1n+j:
              match j:
                case 0n:
                  match suf:
                    case SNil{}:
                      (Show.ok(g, 0n, SNil{}, pre), Unit{})
                    case SCon{c2, +t}:
                      (Show.ok(g, 0n, SCon{c2, t}, pre), Show.ok(g, 2n, t, pre))
                case 1n+i:
                  Unit{}
    case Spec.Lit{c}:
      match rank:
        case 0n:
          {==}
        case 1n+k:
          match k:
            case 0n:
              match suf:
                case SNil{}:
                  (Show.ok(g, 0n, pre, SNil{}), Unit{})
                case SCon{c2, t}:
                  (
                    Show.ok(g, 0n, pre, SNil{}),
                    Show.ok(g, 1n, t, String.append(pre, SCon{c2, SNil{}}))
                  )
            case 1n+j:
              match j:
                case 0n:
                  match suf:
                    case SNil{}:
                      (Show.ok(g, 0n, SNil{}, pre), Unit{})
                    case SCon{c2, +t}:
                      (Show.ok(g, 0n, SCon{c2, t}, pre), Show.ok(g, 2n, t, pre))
                case 1n+i:
                  Unit{}
    case Spec.Any{}:
      match rank:
        case 0n:
          {==}
        case 1n+k:
          match k:
            case 0n:
              match suf:
                case SNil{}:
                  (Show.ok(g, 0n, pre, SNil{}), Unit{})
                case SCon{c2, t}:
                  (
                    Show.ok(g, 0n, pre, SNil{}),
                    Show.ok(g, 1n, t, String.append(pre, SCon{c2, SNil{}}))
                  )
            case 1n+j:
              match j:
                case 0n:
                  match suf:
                    case SNil{}:
                      (Show.ok(g, 0n, SNil{}, pre), Unit{})
                    case SCon{c2, +t}:
                      (Show.ok(g, 0n, SCon{c2, t}, pre), Show.ok(g, 2n, t, pre))
                case 1n+i:
                  Unit{}
    case Spec.Star{}:
      match rank:
        case 0n:
          Show.star_point(suf)
        case 1n+k:
          match k:
            case 0n:
              match suf:
                case SNil{}:
                  (Show.ok(g, 0n, pre, SNil{}), Unit{})
                case SCon{c2, t}:
                  (
                    Show.ok(g, 0n, pre, SNil{}),
                    Show.ok(g, 1n, t, String.append(pre, SCon{c2, SNil{}}))
                  )
            case 1n+j:
              match j:
                case 0n:
                  match suf:
                    case SNil{}:
                      (Show.ok(g, 0n, SNil{}, pre), Unit{})
                    case SCon{c2, +t}:
                      (Show.ok(g, 0n, SCon{c2, t}, pre), Show.ok(g, 2n, t, pre))
                case 1n+i:
                  Unit{}
    case Spec.Class{+n, +cs}:
      match rank:
        case 0n:
          Show.class_point(suf, n, cs)
        case 1n+k:
          match k:
            case 0n:
              match suf:
                case SNil{}:
                  (Show.ok(g, 0n, pre, SNil{}), Unit{})
                case SCon{c2, t}:
                  (
                    Show.ok(g, 0n, pre, SNil{}),
                    Show.ok(g, 1n, t, String.append(pre, SCon{c2, SNil{}}))
                  )
            case 1n+j:
              match j:
                case 0n:
                  match suf:
                    case SNil{}:
                      (Show.ok(g, 0n, SNil{}, pre), Unit{})
                    case SCon{c2, +t}:
                      (Show.ok(g, 0n, SCon{c2, t}, pre), Show.ok(g, 2n, t, pre))
                case 1n+i:
                  Unit{}
    case Spec.Deep{}:
      match rank:
        case 0n:
          Show.deep_point(suf)
        case 1n+k:
          match k:
            case 0n:
              match suf:
                case SNil{}:
                  (Show.ok(g, 0n, pre, SNil{}), Unit{})
                case SCon{c2, t}:
                  (
                    Show.ok(g, 0n, pre, SNil{}),
                    Show.ok(g, 1n, t, String.append(pre, SCon{c2, SNil{}}))
                  )
            case 1n+j:
              match j:
                case 0n:
                  match suf:
                    case SNil{}:
                      (Show.ok(g, 0n, SNil{}, pre), Unit{})
                    case SCon{c2, +t}:
                      (Show.ok(g, 0n, SCon{c2, t}, pre), Show.ok(g, 2n, t, pre))
                case 1n+i:
                  Unit{}
    case Spec.Cat{+a, +b}:
      match rank:
        case 0n:
          +ta = Show.glob(a)
          +tb = Show.glob(b)
          r = Spec.Glob.matches(suf, Spec.Cat{a, b})
          %Glob.alt_void(suf, Spec.Cat{ta, Spec.Cat{tb, Spec.Eps{}}}): {_ == r: Bool}
          %Equal.sym(
            Bool,
            Spec.Glob.matches(suf, Spec.Cat{ta, Spec.Cat{tb, Spec.Eps{}}}),
            Spec.Glob.matches(suf, Spec.Cat{Spec.Cat{ta, tb}, Spec.Eps{}}),
            Glob.cat_assoc(suf, ta, tb, Spec.Eps{})
          ): {_ == r: Bool}
          %Glob.cat_eps_r(suf, Spec.Cat{ta, tb}): {_ == r: Bool}
          Glob.cat_agree(
            suf,
            ta,
            a,
            tb,
            b,
            Show.ok(a, 1n, suf, SNil{}),
            Show.ok(b, 2n, suf, SNil{})
          )
        case 1n+k:
          match k:
            case 0n:
              match suf:
                case SNil{}:
                  (Show.ok(g, 0n, pre, SNil{}), Unit{})
                case SCon{c2, t}:
                  (
                    Show.ok(g, 0n, pre, SNil{}),
                    Show.ok(g, 1n, t, String.append(pre, SCon{c2, SNil{}}))
                  )
            case 1n+j:
              match j:
                case 0n:
                  match suf:
                    case SNil{}:
                      (Show.ok(g, 0n, SNil{}, pre), Unit{})
                    case SCon{c2, +t}:
                      (Show.ok(g, 0n, SCon{c2, t}, pre), Show.ok(g, 2n, t, pre))
                case 1n+i:
                  Unit{}
    case Spec.Alt{+a, +b}:
      match rank:
        case 0n:
          +ta = Show.glob(a)
          +tb = Show.glob(b)
          r = Spec.Glob.matches(suf, Spec.Alt{a, b})
          ma = Spec.Glob.matches(suf, ta)
          mb = Spec.Glob.matches(suf, tb)
          %Glob.alt_or(
            suf,
            Spec.Cat{ta, Spec.Eps{}},
            Spec.Alt{Spec.Cat{tb, Spec.Eps{}}, Spec.Void{}}
          ): {_ == r: Bool}
          %Glob.alt_void(
            suf,
            Spec.Cat{tb, Spec.Eps{}}
          ): {Bool.or(Spec.Glob.matches(suf, Spec.Cat{ta, Spec.Eps{}}), _) == r: Bool}
          %Glob.cat_eps_r(
            suf,
            ta
          ): {Bool.or(_, Spec.Glob.matches(suf, Spec.Cat{tb, Spec.Eps{}})) == r: Bool}
          %Glob.cat_eps_r(suf, tb): {Bool.or(ma, _) == r: Bool}
          %Glob.alt_or(suf, a, b): {Bool.or(ma, mb) == _: Bool}
          %Show.ok(
            a,
            0n,
            suf,
            SNil{}
          ): {Bool.or(ma, mb) == Bool.or(_, Spec.Glob.matches(suf, b)): Bool}
          %Show.ok(b, 0n, suf, SNil{}): {Bool.or(ma, mb) == Bool.or(ma, _): Bool}
          {==}
        case 1n+k:
          match k:
            case 0n:
              match suf:
                case SNil{}:
                  (Show.ok(g, 0n, pre, SNil{}), Unit{})
                case SCon{c2, t}:
                  (
                    Show.ok(g, 0n, pre, SNil{}),
                    Show.ok(g, 1n, t, String.append(pre, SCon{c2, SNil{}}))
                  )
            case 1n+j:
              match j:
                case 0n:
                  match suf:
                    case SNil{}:
                      (Show.ok(g, 0n, SNil{}, pre), Unit{})
                    case SCon{c2, +t}:
                      (Show.ok(g, 0n, SCon{c2, t}, pre), Show.ok(g, 2n, t, pre))
                case 1n+i:
                  Unit{}
# bend-lint: expect-end bend-lint-rules/performance/append_in_loop@warning
# bend-lint: expect-end bend-lint-rules/performance/missed_fork@hint

# the text of Lit{c} reads back, given k, the role of c
def Show.read_lit(
  +c: Char,
  k: Spec.Sym
) -> {
  k == Spec.Sym.of(c): Spec.Sym
} -> {
  Some{
    Spec.Cat{Spec.Lit{c}, Spec.Eps{}}
  }
    == Spec.Glob.read.syms(Spec.Sym.list(Glob.show.char(c, k, ""))): Maybe<&2, Spec.Glob>
}:
  match k:
    case Spec.SChar{x}:
      +e =>
        +tgt = {Some{Spec.Cat{Spec.Lit{c}, Spec.Eps{}}}: Maybe<&2, Spec.Glob>}
        %e: {tgt == Spec.Glob.read.syms(Con{_, Nil{}}): Maybe<&2, Spec.Glob>}
        %Sym.char_is(
          c,
          Spec.SChar{x},
          e
        ): {tgt == Some{Spec.Cat{Spec.Lit{_}, Spec.Eps{}}}: Maybe<&2, Spec.Glob>}
        {==}
    case Spec.SEsc{}:
      e =>
        +tgt = {Some{Spec.Cat{Spec.Lit{c}, Spec.Eps{}}}: Maybe<&2, Spec.Glob>}
        +f = {[Spec.Frame{[], [], True{}}]: List<&2, Spec.Frame>}
        %Step.esc(Spec.Sym.of(c), Nil{}, f, True{}): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(c): {tgt == Some{Spec.Cat{Spec.Lit{_}, Spec.Eps{}}}: Maybe<&2, Spec.Glob>}
        {==}
    case Spec.SAny{}:
      e =>
        +tgt = {Some{Spec.Cat{Spec.Lit{c}, Spec.Eps{}}}: Maybe<&2, Spec.Glob>}
        +f = {[Spec.Frame{[], [], True{}}]: List<&2, Spec.Frame>}
        %Step.esc(Spec.Sym.of(c), Nil{}, f, True{}): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(c): {tgt == Some{Spec.Cat{Spec.Lit{_}, Spec.Eps{}}}: Maybe<&2, Spec.Glob>}
        {==}
    case Spec.SStar{}:
      e =>
        +tgt = {Some{Spec.Cat{Spec.Lit{c}, Spec.Eps{}}}: Maybe<&2, Spec.Glob>}
        +f = {[Spec.Frame{[], [], True{}}]: List<&2, Spec.Frame>}
        %Step.esc(Spec.Sym.of(c), Nil{}, f, True{}): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(c): {tgt == Some{Spec.Cat{Spec.Lit{_}, Spec.Eps{}}}: Maybe<&2, Spec.Glob>}
        {==}
    case Spec.SSlash{}:
      e =>
        +tgt = {Some{Spec.Cat{Spec.Lit{c}, Spec.Eps{}}}: Maybe<&2, Spec.Glob>}
        +f = {[Spec.Frame{[], [], True{}}]: List<&2, Spec.Frame>}
        %Step.esc(Spec.Sym.of(c), Nil{}, f, True{}): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(c): {tgt == Some{Spec.Cat{Spec.Lit{_}, Spec.Eps{}}}: Maybe<&2, Spec.Glob>}
        {==}
    case Spec.SOpen{}:
      e =>
        +tgt = {Some{Spec.Cat{Spec.Lit{c}, Spec.Eps{}}}: Maybe<&2, Spec.Glob>}
        +f = {[Spec.Frame{[], [], True{}}]: List<&2, Spec.Frame>}
        %Step.esc(Spec.Sym.of(c), Nil{}, f, True{}): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(c): {tgt == Some{Spec.Cat{Spec.Lit{_}, Spec.Eps{}}}: Maybe<&2, Spec.Glob>}
        {==}
    case Spec.SComma{}:
      e =>
        +tgt = {Some{Spec.Cat{Spec.Lit{c}, Spec.Eps{}}}: Maybe<&2, Spec.Glob>}
        +f = {[Spec.Frame{[], [], True{}}]: List<&2, Spec.Frame>}
        %Step.esc(Spec.Sym.of(c), Nil{}, f, True{}): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(c): {tgt == Some{Spec.Cat{Spec.Lit{_}, Spec.Eps{}}}: Maybe<&2, Spec.Glob>}
        {==}
    case Spec.SClose{}:
      e =>
        +tgt = {Some{Spec.Cat{Spec.Lit{c}, Spec.Eps{}}}: Maybe<&2, Spec.Glob>}
        +f = {[Spec.Frame{[], [], True{}}]: List<&2, Spec.Frame>}
        %Step.esc(Spec.Sym.of(c), Nil{}, f, True{}): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(c): {tgt == Some{Spec.Cat{Spec.Lit{_}, Spec.Eps{}}}: Maybe<&2, Spec.Glob>}
        {==}
    case Spec.SLeft{}:
      e =>
        +tgt = {Some{Spec.Cat{Spec.Lit{c}, Spec.Eps{}}}: Maybe<&2, Spec.Glob>}
        +f = {[Spec.Frame{[], [], True{}}]: List<&2, Spec.Frame>}
        %Step.esc(Spec.Sym.of(c), Nil{}, f, True{}): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(c): {tgt == Some{Spec.Cat{Spec.Lit{_}, Spec.Eps{}}}: Maybe<&2, Spec.Glob>}
        {==}
    case Spec.SRight{}:
      e =>
        +tgt = {Some{Spec.Cat{Spec.Lit{c}, Spec.Eps{}}}: Maybe<&2, Spec.Glob>}
        +f = {[Spec.Frame{[], [], True{}}]: List<&2, Spec.Frame>}
        %Step.esc(Spec.Sym.of(c), Nil{}, f, True{}): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(c): {tgt == Some{Spec.Cat{Spec.Lit{_}, Spec.Eps{}}}: Maybe<&2, Spec.Glob>}
        {==}
    case Spec.SBang{}:
      e =>
        +tgt = {Some{Spec.Cat{Spec.Lit{c}, Spec.Eps{}}}: Maybe<&2, Spec.Glob>}
        +f = {[Spec.Frame{[], [], True{}}]: List<&2, Spec.Frame>}
        %Step.esc(Spec.Sym.of(c), Nil{}, f, True{}): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(c): {tgt == Some{Spec.Cat{Spec.Lit{_}, Spec.Eps{}}}: Maybe<&2, Spec.Glob>}
        {==}
    case Spec.SDash{}:
      e =>
        +tgt = {Some{Spec.Cat{Spec.Lit{c}, Spec.Eps{}}}: Maybe<&2, Spec.Glob>}
        +f = {[Spec.Frame{[], [], True{}}]: List<&2, Spec.Frame>}
        %Step.esc(Spec.Sym.of(c), Nil{}, f, True{}): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(c): {tgt == Some{Spec.Cat{Spec.Lit{_}, Spec.Eps{}}}: Maybe<&2, Spec.Glob>}
        {==}

# the text of g reads back as Show.glob(g)
def Show.read(
  g: Spec.Glob
) -> {
  Some{
    Spec.Cat{Show.glob(g), Spec.Eps{}}
  }
    == Spec.Glob.read(Spec.Glob.show(g)): Maybe<&2, Spec.Glob>
}:
  match g:
    case Spec.Void{}:
      Show.parse(Spec.Void{}, "", [], [], True{}, [], True{})
    case Spec.Eps{}:
      Show.parse(Spec.Eps{}, "", [], [], True{}, [], True{})
    case Spec.Any{}:
      Show.parse(Spec.Any{}, "", [], [], True{}, [], True{})
    case Spec.Star{}:
      Show.parse(Spec.Star{}, "", [], [], True{}, [], True{})
    case Spec.Class{n, cs}:
      Show.parse(Spec.Class{n, cs}, "", [], [], True{}, [], True{})
    case Spec.Deep{}:
      Show.parse(Spec.Deep{}, "", [], [], True{}, [], True{})
    case Spec.Cat{x, y}:
      Show.parse(Spec.Cat{x, y}, "", [], [], True{}, [], True{})
    case Spec.Alt{x, y}:
      Show.parse(Spec.Alt{x, y}, "", [], [], True{}, [], True{})
    case Spec.Lit{+c}:
      Show.read_lit(c, Spec.Sym.of(c))({==})

# g matches what the glob its text reads back as matches
def Show.same(
  +g: Spec.Glob,
  +p: String
) -> {Spec.Glob.matches(p, g) == Spec.Glob.matches(p, Spec.Cat{Show.glob(g), Spec.Eps{}}): Bool}:
  %Glob.cat_eps_r(p, Show.glob(g)): {Spec.Glob.matches(p, g) == _: Bool}
  Equal.sym(
    Bool,
    Spec.Glob.matches(p, Show.glob(g)),
    Spec.Glob.matches(p, g),
    Show.ok(g, 0n, p, SNil{})
  )

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- a false positive, as the rule notes: the other use is an erased argument (of Equal.sym or a motive)
def Spec.read_after_show(g):
  +g = g
  h = {Spec.Cat{Show.glob(g), Spec.Eps{}}: Spec.Glob}
  read = Equal.sym(Maybe<&2, Spec.Glob>, Some{h}, Spec.Glob.read(Spec.Glob.show(g)), Show.read(g))
  (h, (read, p => Show.same(g, p)))
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
def Spec.read_rejects_root(s):
  {==}

# Escaped paths
# -------------

# the text of c in an escaped path: a character with a role is escaped,
# except '/', which stays a separator
def Glob.escape.char(c: Char, k: Spec.Sym, rest: String) -> String:
  match k:
    case Spec.SChar{x}:
      SCon{c, rest}
    case Spec.SSlash{}:
      SCon{c, rest}
    case _:
      SCon{Chr{92}, SCon{c, rest}}

def Spec.Glob.escape(p):
  match p:
    case SNil{}:
      SNil{}
    case SCon{+c, t}:
      Glob.escape.char(c, Spec.Sym.of(c), Spec.Glob.escape(t))

# the glob of exactly the text p
def Glob.lits(p: String) -> Spec.Glob:
  match p:
    case SNil{}:
      Spec.Eps{}
    case SCon{c, t}:
      Spec.Cat{Spec.Lit{c}, Glob.lits(t)}

# Esc.parse, one character c, given k, the role of c
def Esc.parse_at(
  +c: Char,
  +t: String,
  k: Spec.Sym,
  +s: List<&2, Spec.Glob>,
  seg: Bool,
  ih: @s2: List<
    &2,
    Spec.Glob> -> @seg2: Bool -> {
    Some{
      Spec.Glob.of_seq(s2, Glob.lits(t))
    }
      == Spec.Glob.read.go(
        Spec.Sym.list(Spec.Glob.escape(t)),
        Spec.Out{},
        [Spec.Frame{[], s2, True{}}],
        seg2
      ): Maybe<&2, Spec.Glob>
  }
) -> {
  k == Spec.Sym.of(c): Spec.Sym
} -> {
  Some{
    Spec.Glob.of_seq(s, Spec.Cat{Spec.Lit{c}, Glob.lits(t)})
  }
    == Spec.Glob.read.go(
      Spec.Sym.list(Glob.escape.char(c, k, Spec.Glob.escape(t))),
      Spec.Out{},
      [Spec.Frame{[], s, True{}}],
      seg
    ): Maybe<&2, Spec.Glob>
}:
  match k:
    case Spec.SChar{+x}:
      +e =>
        +l = Spec.Sym.list(Spec.Glob.escape(t))
        +f = {[Spec.Frame{[], s, True{}}]: List<&2, Spec.Frame>}
        +tgt = {
          Some{Spec.Glob.of_seq(s, Spec.Cat{Spec.Lit{c}, Glob.lits(t)})}: Maybe<&2, Spec.Glob>
        }
        %e: {tgt == Spec.Glob.read.go(Con{_, l}, Spec.Out{}, f, seg): Maybe<&2, Spec.Glob>}
        %Step.char(x, l, f, seg): {tgt == _: Maybe<&2, Spec.Glob>}
        %ih(Con{Spec.Lit{x}, s}, False{}): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_is(
          c,
          Spec.SChar{x},
          e
        ): {
          tgt
            == Some{Spec.Glob.of_seq(s, Spec.Cat{Spec.Lit{_}, Glob.lits(t)})}: Maybe<&2, Spec.Glob>
        }
        {==}
    case Spec.SSlash{}:
      +e =>
        +l = Spec.Sym.list(Spec.Glob.escape(t))
        +f = {[Spec.Frame{[], s, True{}}]: List<&2, Spec.Frame>}
        +tgt = {
          Some{Spec.Glob.of_seq(s, Spec.Cat{Spec.Lit{c}, Glob.lits(t)})}: Maybe<&2, Spec.Glob>
        }
        %e: {tgt == Spec.Glob.read.go(Con{_, l}, Spec.Out{}, f, seg): Maybe<&2, Spec.Glob>}
        %Step.slash(l, f, seg): {tgt == _: Maybe<&2, Spec.Glob>}
        %ih(Con{Spec.Lit{Chr{47}}, s}, True{}): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_is(
          c,
          Spec.SSlash{},
          e
        ): {
          tgt
            == Some{Spec.Glob.of_seq(s, Spec.Cat{Spec.Lit{_}, Glob.lits(t)})}: Maybe<&2, Spec.Glob>
        }
        {==}
    case Spec.SEsc{}:
      e =>
        +l = Spec.Sym.list(Spec.Glob.escape(t))
        +f = {[Spec.Frame{[], s, True{}}]: List<&2, Spec.Frame>}
        +tgt = {
          Some{Spec.Glob.of_seq(s, Spec.Cat{Spec.Lit{c}, Glob.lits(t)})}: Maybe<&2, Spec.Glob>
        }
        %Step.esc(Spec.Sym.of(c), l, f, seg): {tgt == _: Maybe<&2, Spec.Glob>}
        %ih(
          Con{Spec.Lit{Spec.Sym.char(Spec.Sym.of(c))}, s},
          False{}
        ): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(
          c
        ): {
          tgt
            == Some{Spec.Glob.of_seq(s, Spec.Cat{Spec.Lit{_}, Glob.lits(t)})}: Maybe<&2, Spec.Glob>
        }
        {==}
    case Spec.SAny{}:
      e =>
        +l = Spec.Sym.list(Spec.Glob.escape(t))
        +f = {[Spec.Frame{[], s, True{}}]: List<&2, Spec.Frame>}
        +tgt = {
          Some{Spec.Glob.of_seq(s, Spec.Cat{Spec.Lit{c}, Glob.lits(t)})}: Maybe<&2, Spec.Glob>
        }
        %Step.esc(Spec.Sym.of(c), l, f, seg): {tgt == _: Maybe<&2, Spec.Glob>}
        %ih(
          Con{Spec.Lit{Spec.Sym.char(Spec.Sym.of(c))}, s},
          False{}
        ): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(
          c
        ): {
          tgt
            == Some{Spec.Glob.of_seq(s, Spec.Cat{Spec.Lit{_}, Glob.lits(t)})}: Maybe<&2, Spec.Glob>
        }
        {==}
    case Spec.SStar{}:
      e =>
        +l = Spec.Sym.list(Spec.Glob.escape(t))
        +f = {[Spec.Frame{[], s, True{}}]: List<&2, Spec.Frame>}
        +tgt = {
          Some{Spec.Glob.of_seq(s, Spec.Cat{Spec.Lit{c}, Glob.lits(t)})}: Maybe<&2, Spec.Glob>
        }
        %Step.esc(Spec.Sym.of(c), l, f, seg): {tgt == _: Maybe<&2, Spec.Glob>}
        %ih(
          Con{Spec.Lit{Spec.Sym.char(Spec.Sym.of(c))}, s},
          False{}
        ): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(
          c
        ): {
          tgt
            == Some{Spec.Glob.of_seq(s, Spec.Cat{Spec.Lit{_}, Glob.lits(t)})}: Maybe<&2, Spec.Glob>
        }
        {==}
    case Spec.SOpen{}:
      e =>
        +l = Spec.Sym.list(Spec.Glob.escape(t))
        +f = {[Spec.Frame{[], s, True{}}]: List<&2, Spec.Frame>}
        +tgt = {
          Some{Spec.Glob.of_seq(s, Spec.Cat{Spec.Lit{c}, Glob.lits(t)})}: Maybe<&2, Spec.Glob>
        }
        %Step.esc(Spec.Sym.of(c), l, f, seg): {tgt == _: Maybe<&2, Spec.Glob>}
        %ih(
          Con{Spec.Lit{Spec.Sym.char(Spec.Sym.of(c))}, s},
          False{}
        ): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(
          c
        ): {
          tgt
            == Some{Spec.Glob.of_seq(s, Spec.Cat{Spec.Lit{_}, Glob.lits(t)})}: Maybe<&2, Spec.Glob>
        }
        {==}
    case Spec.SComma{}:
      e =>
        +l = Spec.Sym.list(Spec.Glob.escape(t))
        +f = {[Spec.Frame{[], s, True{}}]: List<&2, Spec.Frame>}
        +tgt = {
          Some{Spec.Glob.of_seq(s, Spec.Cat{Spec.Lit{c}, Glob.lits(t)})}: Maybe<&2, Spec.Glob>
        }
        %Step.esc(Spec.Sym.of(c), l, f, seg): {tgt == _: Maybe<&2, Spec.Glob>}
        %ih(
          Con{Spec.Lit{Spec.Sym.char(Spec.Sym.of(c))}, s},
          False{}
        ): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(
          c
        ): {
          tgt
            == Some{Spec.Glob.of_seq(s, Spec.Cat{Spec.Lit{_}, Glob.lits(t)})}: Maybe<&2, Spec.Glob>
        }
        {==}
    case Spec.SClose{}:
      e =>
        +l = Spec.Sym.list(Spec.Glob.escape(t))
        +f = {[Spec.Frame{[], s, True{}}]: List<&2, Spec.Frame>}
        +tgt = {
          Some{Spec.Glob.of_seq(s, Spec.Cat{Spec.Lit{c}, Glob.lits(t)})}: Maybe<&2, Spec.Glob>
        }
        %Step.esc(Spec.Sym.of(c), l, f, seg): {tgt == _: Maybe<&2, Spec.Glob>}
        %ih(
          Con{Spec.Lit{Spec.Sym.char(Spec.Sym.of(c))}, s},
          False{}
        ): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(
          c
        ): {
          tgt
            == Some{Spec.Glob.of_seq(s, Spec.Cat{Spec.Lit{_}, Glob.lits(t)})}: Maybe<&2, Spec.Glob>
        }
        {==}
    case Spec.SLeft{}:
      e =>
        +l = Spec.Sym.list(Spec.Glob.escape(t))
        +f = {[Spec.Frame{[], s, True{}}]: List<&2, Spec.Frame>}
        +tgt = {
          Some{Spec.Glob.of_seq(s, Spec.Cat{Spec.Lit{c}, Glob.lits(t)})}: Maybe<&2, Spec.Glob>
        }
        %Step.esc(Spec.Sym.of(c), l, f, seg): {tgt == _: Maybe<&2, Spec.Glob>}
        %ih(
          Con{Spec.Lit{Spec.Sym.char(Spec.Sym.of(c))}, s},
          False{}
        ): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(
          c
        ): {
          tgt
            == Some{Spec.Glob.of_seq(s, Spec.Cat{Spec.Lit{_}, Glob.lits(t)})}: Maybe<&2, Spec.Glob>
        }
        {==}
    case Spec.SRight{}:
      e =>
        +l = Spec.Sym.list(Spec.Glob.escape(t))
        +f = {[Spec.Frame{[], s, True{}}]: List<&2, Spec.Frame>}
        +tgt = {
          Some{Spec.Glob.of_seq(s, Spec.Cat{Spec.Lit{c}, Glob.lits(t)})}: Maybe<&2, Spec.Glob>
        }
        %Step.esc(Spec.Sym.of(c), l, f, seg): {tgt == _: Maybe<&2, Spec.Glob>}
        %ih(
          Con{Spec.Lit{Spec.Sym.char(Spec.Sym.of(c))}, s},
          False{}
        ): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(
          c
        ): {
          tgt
            == Some{Spec.Glob.of_seq(s, Spec.Cat{Spec.Lit{_}, Glob.lits(t)})}: Maybe<&2, Spec.Glob>
        }
        {==}
    case Spec.SBang{}:
      e =>
        +l = Spec.Sym.list(Spec.Glob.escape(t))
        +f = {[Spec.Frame{[], s, True{}}]: List<&2, Spec.Frame>}
        +tgt = {
          Some{Spec.Glob.of_seq(s, Spec.Cat{Spec.Lit{c}, Glob.lits(t)})}: Maybe<&2, Spec.Glob>
        }
        %Step.esc(Spec.Sym.of(c), l, f, seg): {tgt == _: Maybe<&2, Spec.Glob>}
        %ih(
          Con{Spec.Lit{Spec.Sym.char(Spec.Sym.of(c))}, s},
          False{}
        ): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(
          c
        ): {
          tgt
            == Some{Spec.Glob.of_seq(s, Spec.Cat{Spec.Lit{_}, Glob.lits(t)})}: Maybe<&2, Spec.Glob>
        }
        {==}
    case Spec.SDash{}:
      e =>
        +l = Spec.Sym.list(Spec.Glob.escape(t))
        +f = {[Spec.Frame{[], s, True{}}]: List<&2, Spec.Frame>}
        +tgt = {
          Some{Spec.Glob.of_seq(s, Spec.Cat{Spec.Lit{c}, Glob.lits(t)})}: Maybe<&2, Spec.Glob>
        }
        %Step.esc(Spec.Sym.of(c), l, f, seg): {tgt == _: Maybe<&2, Spec.Glob>}
        %ih(
          Con{Spec.Lit{Spec.Sym.char(Spec.Sym.of(c))}, s},
          False{}
        ): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(
          c
        ): {
          tgt
            == Some{Spec.Glob.of_seq(s, Spec.Cat{Spec.Lit{_}, Glob.lits(t)})}: Maybe<&2, Spec.Glob>
        }
        {==}

# the escaped text of p, after the atoms s, reads back as s then the Lits of p
def Esc.parse(
  p: String,
  s: List<&2, Spec.Glob>,
  seg: Bool
) -> {
  Some{
    Spec.Glob.of_seq(s, Glob.lits(p))
  }
    == Spec.Glob.read.go(
      Spec.Sym.list(Spec.Glob.escape(p)),
      Spec.Out{},
      [Spec.Frame{[], s, True{}}],
      seg
    ): Maybe<&2, Spec.Glob>
}:
  match p:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      Esc.parse_at(c, t, Spec.Sym.of(c), s, seg, s2 => seg2 => Esc.parse(t, s2, seg2))({==})

# syms start with '/'
def Sym.starts_slash(syms: List<&2, Spec.Sym>) -> Bool:
  match syms:
    case Con{Spec.SSlash{}, t}:
      True{}
    case _:
      False{}

# text that does not start with '/' is read from a fresh frame
def Read.syms_go(
  syms: List<&2, Spec.Sym>
) -> {
  Sym.starts_slash(syms) == False{}: Bool
} -> {
  Spec.Glob.read.go(
    syms,
    Spec.Out{},
    [Spec.Frame{[], [], True{}}],
    True{}
  )
    == Spec.Glob.read.syms(syms): Maybe<&2, Spec.Glob>
}:
  match syms:
    case Nil{}:
      h => {==}
    case Con{y, l}:
      match y:
        case Spec.SEsc{}:
          h => {==}
        case Spec.SAny{}:
          h => {==}
        case Spec.SStar{}:
          h => {==}
        case Spec.SSlash{}:
          h => Empty.absurd(
            {
              Spec.Glob.read.go(
                Con{Spec.SSlash{}, l},
                Spec.Out{},
                [Spec.Frame{[], [], True{}}],
                True{}
              )
                == Spec.Glob.read.syms(Con{Spec.SSlash{}, l}): Maybe<&2, Spec.Glob>
            },
            Bool.true_ne_false(h)
          )
        case Spec.SOpen{}:
          h => {==}
        case Spec.SComma{}:
          h => {==}
        case Spec.SClose{}:
          h => {==}
        case Spec.SLeft{}:
          h => {==}
        case Spec.SRight{}:
          h => {==}
        case Spec.SBang{}:
          h => {==}
        case Spec.SDash{}:
          h => {==}
        case Spec.SChar{x}:
          h => {==}

# a text that starts with '/' is no valid path
def Esc.no_root.path(
  c: Char,
  t: String,
  ec: {Chr{47} == c: Char}
) -> {False{} == Spec.is_path(SCon{c, t}): Bool}:
  %ec: {False{} == Spec.is_path(SCon{_, t}): Bool}
  {==}

# no valid path starts with '/'
# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- a false positive, as the rule notes: the other use is an erased argument (of Equal.sym or a motive)
def Esc.no_root(
  c: Char,
  t: String,
  ec: {Chr{47} == c: Char},
  v: {Spec.is_path(SCon{c, t}) == True{}: Bool}
) -> Empty:
  Shared.Bool.false_ne_true(
    Equal.trans(Bool, False{}, Spec.is_path(SCon{c, t}), True{}, Esc.no_root.path(c, t, ec), v)
  )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# the escaped text of a valid path starting with c does not start with '/',
# given k, the role of c
def Esc.no_slash_at(
  +c: Char,
  t: String,
  k: Spec.Sym,
  v: {Spec.is_path(SCon{c, t}) == True{}: Bool}
) -> {
  k == Spec.Sym.of(c): Spec.Sym
} -> {
  Sym.starts_slash(Spec.Sym.list(Glob.escape.char(c, k, Spec.Glob.escape(t)))) == False{}: Bool
}:
  match k:
    case Spec.SEsc{}:
      e => {==}
    case Spec.SAny{}:
      e => {==}
    case Spec.SStar{}:
      e => {==}
    case Spec.SSlash{}:
      +e =>
        ec = Equal.sym(Char, c, Chr{47}, Sym.char_is(c, Spec.SSlash{}, e))
        Empty.absurd(
          {
            Sym.starts_slash(
              Spec.Sym.list(Glob.escape.char(c, Spec.SSlash{}, Spec.Glob.escape(t)))
            )
              == False{}: Bool
          },
          Esc.no_root(c, t, ec, v)
        )
    case Spec.SOpen{}:
      e => {==}
    case Spec.SComma{}:
      e => {==}
    case Spec.SClose{}:
      e => {==}
    case Spec.SLeft{}:
      e => {==}
    case Spec.SRight{}:
      e => {==}
    case Spec.SBang{}:
      e => {==}
    case Spec.SDash{}:
      e => {==}
    case Spec.SChar{x}:
      +e =>
        %e: {Sym.starts_slash(Con{_, Spec.Sym.list(Spec.Glob.escape(t))}) == False{}: Bool}
        {==}

# the escaped text of a valid path does not start with '/'
def Esc.no_slash(
  p: String,
  v: {Spec.is_path(p) == True{}: Bool}
) -> {Sym.starts_slash(Spec.Sym.list(Spec.Glob.escape(p))) == False{}: Bool}:
  match p:
    case SNil{}:
      Empty.absurd({False{} == False{}: Bool}, Shared.Bool.false_ne_true(v))
    case SCon{+c, t}:
      Esc.no_slash_at(c, t, Spec.Sym.of(c), v)({==})

# the escaped text of a valid path reads back as its Lits
def Esc.read(
  +p: String,
  v: {Spec.is_path(p) == True{}: Bool}
) -> {Some{Glob.lits(p)} == Spec.Glob.read(Spec.Glob.escape(p)): Maybe<&2, Spec.Glob>}:
  syms = Spec.Sym.list(Spec.Glob.escape(p))
  %Read.syms_go(syms)(Esc.no_slash(p, v)): {Some{Glob.lits(p)} == _: Maybe<&2, Spec.Glob>}
  Esc.parse(p, [], True{})

# an EQ comparison answers True to Cmp.is_eq
def Cmp.is_eq_of(-c: Cmp, e: {EQ{} == c: Cmp}) -> {Cmp.is_eq(c) == True{}: Bool}:
  %e: {Cmp.is_eq(_) == True{}: Bool}
  {==}

# a U32 comparison is EQ both ways round or neither
# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- a false positive, as the rule notes: the other use is an erased argument (of Equal.sym or a motive)
def U32.cmp_swap_eq(
  +x: U32,
  y: U32,
  e: {EQ{} == U32.cmp(x, y): Cmp}
) -> {EQ{} == U32.cmp(y, x): Cmp}:
  %Shared.U32.is_eq_sound(x, y)(Cmp.is_eq_of(U32.cmp(x, y), e)): {EQ{} == U32.cmp(_, x): Cmp}
  Equal.sym(Cmp, U32.cmp(x, x), EQ{}, Shared.U32.cmp_refl(x))
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# a decided comparison stays decided: it is never EQ
def String.order_ne_lt(
  qt: String,
  pt: String
) -> {Cmp.is_eq(String.order.go(qt, pt, LT{})) == False{}: Bool}:
  match qt pt:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{h2, t2}:
      {==}
    case SCon{h1, t1} SNil{}:
      {==}
    case SCon{Chr{a1}, t1} SCon{Chr{a2}, t2}:
      {==}

# a decided comparison stays decided: it is never EQ
def String.order_ne_gt(
  qt: String,
  pt: String
) -> {Cmp.is_eq(String.order.go(qt, pt, GT{})) == False{}: Bool}:
  match qt pt:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{h2, t2}:
      {==}
    case SCon{h1, t1} SNil{}:
      {==}
    case SCon{Chr{a1}, t1} SCon{Chr{a2}, t2}:
      {==}

# Lits.cons, given o1 and o2, the comparisons of the two characters
# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- a false positive, as the rule notes: the other use is an erased argument (of Equal.sym or a motive)
def Lits.cmp_case(
  cx: U32,
  dx: U32,
  o1: Cmp,
  o2: Cmp,
  qt: String,
  pt: String
) -> {
  o1 == U32.cmp(cx, dx): Cmp
} -> {
  o2 == U32.cmp(dx, cx): Cmp
} -> {
  Cmp.is_eq(
    String.order.go(qt, pt, U32.cmp(dx, cx))
  )
    == Bool.and(Cmp.is_eq(U32.cmp(cx, dx)), String.eq(qt, pt)): Bool
}:
  match o1 o2:
    case LT{} LT{}:
      e1 => e2 =>
        %e1: {
          Cmp.is_eq(
            String.order.go(qt, pt, U32.cmp(dx, cx))
          )
            == Bool.and(Cmp.is_eq(_), String.eq(qt, pt)): Bool
        }
        %e2: {
          Cmp.is_eq(
            String.order.go(qt, pt, _)
          )
            == Bool.and(Cmp.is_eq(LT{}), String.eq(qt, pt)): Bool
        }
        String.order_ne_lt(qt, pt)
    case LT{} EQ{}:
      e1 => e2 =>
        z = Shared.Cmp.ne_eq(
          LT{},
          Unit{},
          Equal.trans(
            Cmp,
            LT{},
            U32.cmp(cx, dx),
            EQ{},
            e1,
            Equal.sym(Cmp, EQ{}, U32.cmp(cx, dx), U32.cmp_swap_eq(dx, cx, e2))
          )
        )
        Empty.absurd(
          {
            Cmp.is_eq(
              String.order.go(qt, pt, U32.cmp(dx, cx))
            )
              == Bool.and(Cmp.is_eq(U32.cmp(cx, dx)), String.eq(qt, pt)): Bool
          },
          z
        )
    case LT{} GT{}:
      e1 => e2 =>
        %e1: {
          Cmp.is_eq(
            String.order.go(qt, pt, U32.cmp(dx, cx))
          )
            == Bool.and(Cmp.is_eq(_), String.eq(qt, pt)): Bool
        }
        %e2: {
          Cmp.is_eq(
            String.order.go(qt, pt, _)
          )
            == Bool.and(Cmp.is_eq(LT{}), String.eq(qt, pt)): Bool
        }
        String.order_ne_gt(qt, pt)
    case EQ{} LT{}:
      e1 => e2 =>
        z = Shared.Cmp.ne_eq(
          LT{},
          Unit{},
          Equal.trans(
            Cmp,
            LT{},
            U32.cmp(dx, cx),
            EQ{},
            e2,
            Equal.sym(Cmp, EQ{}, U32.cmp(dx, cx), U32.cmp_swap_eq(cx, dx, e1))
          )
        )
        Empty.absurd(
          {
            Cmp.is_eq(
              String.order.go(qt, pt, U32.cmp(dx, cx))
            )
              == Bool.and(Cmp.is_eq(U32.cmp(cx, dx)), String.eq(qt, pt)): Bool
          },
          z
        )
    case EQ{} EQ{}:
      e1 => e2 =>
        %e1: {
          Cmp.is_eq(
            String.order.go(qt, pt, U32.cmp(dx, cx))
          )
            == Bool.and(Cmp.is_eq(_), String.eq(qt, pt)): Bool
        }
        %e2: {
          Cmp.is_eq(
            String.order.go(qt, pt, _)
          )
            == Bool.and(Cmp.is_eq(EQ{}), String.eq(qt, pt)): Bool
        }
        {==}
    case EQ{} GT{}:
      e1 => e2 =>
        z = Shared.Cmp.ne_eq(
          GT{},
          Unit{},
          Equal.trans(
            Cmp,
            GT{},
            U32.cmp(dx, cx),
            EQ{},
            e2,
            Equal.sym(Cmp, EQ{}, U32.cmp(dx, cx), U32.cmp_swap_eq(cx, dx, e1))
          )
        )
        Empty.absurd(
          {
            Cmp.is_eq(
              String.order.go(qt, pt, U32.cmp(dx, cx))
            )
              == Bool.and(Cmp.is_eq(U32.cmp(cx, dx)), String.eq(qt, pt)): Bool
          },
          z
        )
    case GT{} LT{}:
      e1 => e2 =>
        %e1: {
          Cmp.is_eq(
            String.order.go(qt, pt, U32.cmp(dx, cx))
          )
            == Bool.and(Cmp.is_eq(_), String.eq(qt, pt)): Bool
        }
        %e2: {
          Cmp.is_eq(
            String.order.go(qt, pt, _)
          )
            == Bool.and(Cmp.is_eq(GT{}), String.eq(qt, pt)): Bool
        }
        String.order_ne_lt(qt, pt)
    case GT{} EQ{}:
      e1 => e2 =>
        z = Shared.Cmp.ne_eq(
          GT{},
          Unit{},
          Equal.trans(
            Cmp,
            GT{},
            U32.cmp(cx, dx),
            EQ{},
            e1,
            Equal.sym(Cmp, EQ{}, U32.cmp(cx, dx), U32.cmp_swap_eq(dx, cx, e2))
          )
        )
        Empty.absurd(
          {
            Cmp.is_eq(
              String.order.go(qt, pt, U32.cmp(dx, cx))
            )
              == Bool.and(Cmp.is_eq(U32.cmp(cx, dx)), String.eq(qt, pt)): Bool
          },
          z
        )
    case GT{} GT{}:
      e1 => e2 =>
        %e1: {
          Cmp.is_eq(
            String.order.go(qt, pt, U32.cmp(dx, cx))
          )
            == Bool.and(Cmp.is_eq(_), String.eq(qt, pt)): Bool
        }
        %e2: {
          Cmp.is_eq(
            String.order.go(qt, pt, _)
          )
            == Bool.and(Cmp.is_eq(GT{}), String.eq(qt, pt)): Bool
        }
        String.order_ne_gt(qt, pt)
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# one character of Lits.match
# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- only proofs use it; no program runs it
def Lits.cons(
  +dx: U32,
  +qt: String,
  +cx: U32,
  +pt: String,
  ih: {String.eq(qt, pt) == Spec.Glob.matches(qt, Glob.lits(pt)): Bool}
) -> {
  String.eq(
    SCon{Chr{dx}, qt},
    SCon{Chr{cx}, pt}
  )
    == Spec.Glob.matches(SCon{Chr{dx}, qt}, Glob.lits(SCon{Chr{cx}, pt})): Bool
}:
  +l = Glob.lits(pt)
  +e1 = Cmp.is_eq(U32.cmp(cx, dx))
  +x = Spec.Glob.step(l, Chr{dx})
  s = String.eq(SCon{Chr{dx}, qt}, SCon{Chr{cx}, pt})
  %Glob.alt_or(qt, Spec.Cat{Spec.Glob.of_bool(e1), l}, Spec.Cat{Spec.Void{}, x}): {s == _: Bool}
  %Glob.cat_of_bool(
    qt,
    e1,
    l
  ): {s == Bool.or(_, Spec.Glob.matches(qt, Spec.Cat{Spec.Void{}, x})): Bool}
  %Glob.cat_void_l(qt, x): {s == Bool.or(Bool.and(e1, Spec.Glob.matches(qt, l)), _): Bool}
  %Bool.or_false(Bool.and(e1, Spec.Glob.matches(qt, l))): {s == _: Bool}
  %ih: {s == Bool.and(e1, _): Bool}
  Lits.cmp_case(cx, dx, U32.cmp(cx, dx), U32.cmp(dx, cx), qt, pt)({==}, {==})
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the Lits of p match exactly p
def Lits.match(
  q: String,
  p: String
) -> {String.eq(q, p) == Spec.Glob.matches(q, Glob.lits(p)): Bool}:
  match q p:
    case SNil{} SNil{}:
      {==}
    case SCon{d, +qt} SNil{}:
      Glob.void_never(qt)
    case SNil{} SCon{c, pt}:
      {==}
    case SCon{Chr{dx}, +qt} SCon{Chr{cx}, +pt}:
      Lits.cons(dx, qt, cx, pt, Lits.match(qt, pt))

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- a false positive, as the rule notes: the other use is an erased argument (of Equal.sym or a motive)
def Spec.read_after_escape(p, v):
  +p = p
  h = Glob.lits(p)
  read = Equal.sym(
    Maybe<&2, Spec.Glob>,
    Some{h},
    Spec.Glob.read(Spec.Glob.escape(p)),
    Esc.read(p, v)
  )
  (h, (read, q => Equal.sym(Bool, String.eq(q, p), Spec.Glob.matches(q, h), Lits.match(q, p))))
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# Fast selection
# --------------
# Spec.Rule.selects asks each glob through Spec.Glob.matches, whose
# derivatives are not normalized, so a '*' makes its cost grow fast with the
# path. The slots step the deduplicated derivative sets one character at a
# time and ask only "" at the end, for the same answer.

# the slots after they read p
def Slot.walk(p: String, slots: List<&2, Slot>) -> List<&2, Slot>:
  match p:
    case SNil{}:
      slots
    case SCon{c, t}:
      Slot.walk(t, Slot.step(slots, c))

# walking p, then selecting "", selects what the slots select for p
def Slot.walk_ok(
  p: String,
  +slots: List<&2, Slot>,
  +acc: Bool
) -> {Slot.selects.go(Slot.walk(p, slots), SNil{}, acc) == Slot.selects.go(slots, p, acc): Bool}:
  match p:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Slot.step_ok(
        slots,
        c,
        t,
        acc
      ): {Slot.selects.go(Slot.walk(t, Slot.step(slots, c)), SNil{}, acc) == _: Bool}
      Slot.walk_ok(t, Slot.step(slots, c), acc)

# rules select p: Spec.Rule.selects, through the slots
def Rule.selects.fast(rules: List<&2, Spec.Rule>, p: String) -> Bool:
  Slot.selects.go(Slot.walk(p, Slot.of_rules(rules)), SNil{}, False{})

# the fast selection gives the answer of Spec.Rule.selects
def Rule.selects_fast_ok(
  +rules: List<&2, Spec.Rule>,
  +p: String
) -> {Rule.selects.fast(rules, p) == Spec.Rule.selects(rules, p): Bool}:
  Equal.trans(
    Bool,
    Rule.selects.fast(rules, p),
    Slot.selects.go(Slot.of_rules(rules), p, False{}),
    Spec.Rule.selects(rules, p),
    Slot.walk_ok(p, Slot.of_rules(rules), False{}),
    Equal.sym(
      Bool,
      Spec.Rule.selects.go(rules, p, False{}),
      Slot.selects.go(Slot.of_rules(rules), p, False{}),
      Slot.of_rules_ok(rules, p, False{})
    )
  )
