import Base
import ./spec.bend as Spec

# Equality
# --------
# Each is_eq answers True only for equal values (its is_eq_sound), so a
# membership test can stand for the member itself.

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
  %e : Cmp.Ne(_)
  n

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

# the last step of Word.cmp_eq, with t the comparison of the tails
def Word.cmp_eq.fin(
  -p: Nat, ab: Bool, bb: Bool, -at: Word(p), -bt: Word(p), t: Cmp,
  ih: {Word.cmp(p, at, bt) == EQ{}: Cmp} -> {at == bt: Word(p)}
) -> {Word.cmp(p, at, bt) == t: Cmp} -> {Word.cmp.fin(ab, bb, t) == EQ{}: Cmp} ->
  {WCon{ab, at} == WCon{bb, bt}: Word(1n+p)}:
  match t:
    case LT{}:
      e => h => Empty.absurd({WCon{ab, at} == WCon{bb, bt}: Word(1n+p)}, Cmp.ne_eq(LT{}, Unit{}, h))
    case EQ{}:
      e => h =>
        %Bool.cmp_eq(ab, bb)(h) : {WCon{ab, at} == WCon{_, bt}: Word(1n+p)}
        %ih(e) : {WCon{ab, at} == WCon{ab, _}: Word(1n+p)}
        {==}
    case GT{}:
      e => h => Empty.absurd({WCon{ab, at} == WCon{bb, bt}: Word(1n+p)}, Cmp.ne_eq(GT{}, Unit{}, h))

# Word.cmp is EQ only for equal words
def Word.cmp_eq(+n: Nat, a: Word(n), b: Word(n)) -> {Word.cmp(n, a, b) == EQ{}: Cmp} -> {a == b: Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          h => {==}
    case 1n+p:
      match a b:
        case WCon{ab, +at} WCon{bb, +bt}:
          h => Word.cmp_eq.fin(p, ab, bb, at, bt, Word.cmp(p, at, bt), Word.cmp_eq(p, at, bt))({==}, h)

# no False equals True
def Bool.false_ne_true(e: {False{} == True{}: Bool}) -> Empty:
  %e : Bool.pick(Type, _, Empty, Unit)
  Unit{}

# Cmp.is_eq is True only for EQ
def Cmp.is_eq_sound(c: Cmp) -> {Cmp.is_eq(c) == True{}: Bool} -> {c == EQ{}: Cmp}:
  match c:
    case LT{}:
      h => Empty.absurd({LT{} == EQ{}: Cmp}, Bool.false_ne_true(h))
    case EQ{}:
      h => {==}
    case GT{}:
      h => Empty.absurd({GT{} == EQ{}: Cmp}, Bool.false_ne_true(h))

# U32.is_eq is True only for equal numbers
def U32.is_eq_sound(a: U32, b: U32) -> {U32.is_eq(a, b) == True{}: Bool} -> {a == b: U32}:
  match a b:
    case U32{+x} U32{+y}:
      h =>
        e = Word.cmp_eq(32n, x, y)(Cmp.is_eq_sound(Word.cmp(32n, x, y))(h))
        Equal.cong(Word(32n), U32, w => U32{w}, x, y, e)

# Char.is_eq is True only for equal characters
def Char.is_eq_sound(a: Char, b: Char) -> {Char.is_eq(a, b) == True{}: Bool} -> {a == b: Char}:
  match a b:
    case Chr{+x} Chr{+y}:
      h => Equal.cong(U32, Char, u => Chr{u}, x, y, U32.is_eq_sound(x, y)(h))

# a and b are the same Bool
def Bool.is_eq(a: Bool, b: Bool) -> Bool:
  Bool.not(Bool.xor(a, b))

# Bool.is_eq is True only for the same Bool
def Bool.is_eq_sound(a: Bool, b: Bool) -> {Bool.is_eq(a, b) == True{}: Bool} -> {a == b: Bool}:
  match a b:
    case False{} False{}:
      h => {==}
    case False{} True{}:
      h => Empty.absurd({False{} == True{}: Bool}, Bool.false_ne_true(h))
    case True{} False{}:
      h => Empty.absurd({True{} == False{}: Bool}, Bool.false_ne_true(h))
    case True{} True{}:
      h => {==}

# the left side of a True conjunction is True
def Bool.and_left(a: Bool, -b: Bool) -> {Bool.and(a, b) == True{}: Bool} -> {a == True{}: Bool}:
  match a:
    case False{}:
      h => h
    case True{}:
      h => {==}

# the right side of a True conjunction is True
def Bool.and_right(a: Bool, b: Bool) -> {Bool.and(a, b) == True{}: Bool} -> {b == True{}: Bool}:
  match a:
    case False{}:
      h => Empty.absurd({b == True{}: Bool}, Bool.false_ne_true(h))
    case True{}:
      h => h

# xs and ys are the same characters
def Chars.is_eq(xs: List<&2, Char>, ys: List<&2, Char>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{x, xt} Con{y, yt}:
      Bool.and(Char.is_eq(x, y), Chars.is_eq(xt, yt))
    case _ _:
      False{}

# Chars.is_eq is True only for the same characters
def Chars.is_eq_sound(xs: List<&2, Char>, ys: List<&2, Char>) ->
  {Chars.is_eq(xs, ys) == True{}: Bool} -> {xs == ys: List<&2, Char>}:
  match xs ys:
    case Nil{} Nil{}:
      h => {==}
    case Nil{} Con{y, yt}:
      h => Empty.absurd({Nil{} == Con{y, yt}: List<&2, Char>}, Bool.false_ne_true(h))
    case Con{x, xt} Nil{}:
      h => Empty.absurd({Con{x, xt} == Nil{}: List<&2, Char>}, Bool.false_ne_true(h))
    case Con{+x, +xt} Con{+y, +yt}:
      +h =>
        %Char.is_eq_sound(x, y)(Bool.and_left(Char.is_eq(x, y), Chars.is_eq(xt, yt))(h)) : {Con{x, xt} == Con{_, yt}: List<&2, Char>}
        %Chars.is_eq_sound(xt, yt)(Bool.and_right(Char.is_eq(x, y), Chars.is_eq(xt, yt))(h)) : {Con{x, xt} == Con{x, _}: List<&2, Char>}
        {==}

# a and b are the same glob
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
      Bool.and(Bool.is_eq(n1, n2), Chars.is_eq(cs1, cs2))
    case Spec.Deep{} Spec.Deep{}:
      True{}
    case Spec.Cat{a1, b1} Spec.Cat{a2, b2}:
      Bool.and(Glob.is_eq(a1, a2), Glob.is_eq(b1, b2))
    case Spec.Alt{a1, b1} Spec.Alt{a2, b2}:
      Bool.and(Glob.is_eq(a1, a2), Glob.is_eq(b1, b2))
    case _ _:
      False{}

# Glob.is_eq is True only for the same glob
def Glob.is_eq_sound(a: Spec.Glob, b: Spec.Glob) ->
  {Glob.is_eq(a, b) == True{}: Bool} -> {a == b: Spec.Glob}:
  match a b:
    case Spec.Void{} Spec.Void{}:
      h => {==}
    case Spec.Void{} Spec.Eps{}:
      h => Empty.absurd({Spec.Void{} == Spec.Eps{}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Void{} Spec.Lit{+x2}:
      h => Empty.absurd({Spec.Void{} == Spec.Lit{x2}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Void{} Spec.Any{}:
      h => Empty.absurd({Spec.Void{} == Spec.Any{}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Void{} Spec.Star{}:
      h => Empty.absurd({Spec.Void{} == Spec.Star{}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Void{} Spec.Class{+n2, +cs2}:
      h => Empty.absurd({Spec.Void{} == Spec.Class{n2, cs2}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Void{} Spec.Deep{}:
      h => Empty.absurd({Spec.Void{} == Spec.Deep{}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Void{} Spec.Cat{+a2, +b2}:
      h => Empty.absurd({Spec.Void{} == Spec.Cat{a2, b2}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Void{} Spec.Alt{+a2, +b2}:
      h => Empty.absurd({Spec.Void{} == Spec.Alt{a2, b2}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Eps{} Spec.Void{}:
      h => Empty.absurd({Spec.Eps{} == Spec.Void{}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Eps{} Spec.Eps{}:
      h => {==}
    case Spec.Eps{} Spec.Lit{+x2}:
      h => Empty.absurd({Spec.Eps{} == Spec.Lit{x2}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Eps{} Spec.Any{}:
      h => Empty.absurd({Spec.Eps{} == Spec.Any{}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Eps{} Spec.Star{}:
      h => Empty.absurd({Spec.Eps{} == Spec.Star{}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Eps{} Spec.Class{+n2, +cs2}:
      h => Empty.absurd({Spec.Eps{} == Spec.Class{n2, cs2}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Eps{} Spec.Deep{}:
      h => Empty.absurd({Spec.Eps{} == Spec.Deep{}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Eps{} Spec.Cat{+a2, +b2}:
      h => Empty.absurd({Spec.Eps{} == Spec.Cat{a2, b2}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Eps{} Spec.Alt{+a2, +b2}:
      h => Empty.absurd({Spec.Eps{} == Spec.Alt{a2, b2}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Lit{+x1} Spec.Void{}:
      h => Empty.absurd({Spec.Lit{x1} == Spec.Void{}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Lit{+x1} Spec.Eps{}:
      h => Empty.absurd({Spec.Lit{x1} == Spec.Eps{}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Lit{+x1} Spec.Lit{+x2}:
      h => Equal.cong(Char, Spec.Glob, c => Spec.Lit{c}, x1, x2, Char.is_eq_sound(x1, x2)(h))
    case Spec.Lit{+x1} Spec.Any{}:
      h => Empty.absurd({Spec.Lit{x1} == Spec.Any{}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Lit{+x1} Spec.Star{}:
      h => Empty.absurd({Spec.Lit{x1} == Spec.Star{}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Lit{+x1} Spec.Class{+n2, +cs2}:
      h => Empty.absurd({Spec.Lit{x1} == Spec.Class{n2, cs2}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Lit{+x1} Spec.Deep{}:
      h => Empty.absurd({Spec.Lit{x1} == Spec.Deep{}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Lit{+x1} Spec.Cat{+a2, +b2}:
      h => Empty.absurd({Spec.Lit{x1} == Spec.Cat{a2, b2}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Lit{+x1} Spec.Alt{+a2, +b2}:
      h => Empty.absurd({Spec.Lit{x1} == Spec.Alt{a2, b2}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Any{} Spec.Void{}:
      h => Empty.absurd({Spec.Any{} == Spec.Void{}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Any{} Spec.Eps{}:
      h => Empty.absurd({Spec.Any{} == Spec.Eps{}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Any{} Spec.Lit{+x2}:
      h => Empty.absurd({Spec.Any{} == Spec.Lit{x2}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Any{} Spec.Any{}:
      h => {==}
    case Spec.Any{} Spec.Star{}:
      h => Empty.absurd({Spec.Any{} == Spec.Star{}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Any{} Spec.Class{+n2, +cs2}:
      h => Empty.absurd({Spec.Any{} == Spec.Class{n2, cs2}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Any{} Spec.Deep{}:
      h => Empty.absurd({Spec.Any{} == Spec.Deep{}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Any{} Spec.Cat{+a2, +b2}:
      h => Empty.absurd({Spec.Any{} == Spec.Cat{a2, b2}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Any{} Spec.Alt{+a2, +b2}:
      h => Empty.absurd({Spec.Any{} == Spec.Alt{a2, b2}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Star{} Spec.Void{}:
      h => Empty.absurd({Spec.Star{} == Spec.Void{}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Star{} Spec.Eps{}:
      h => Empty.absurd({Spec.Star{} == Spec.Eps{}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Star{} Spec.Lit{+x2}:
      h => Empty.absurd({Spec.Star{} == Spec.Lit{x2}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Star{} Spec.Any{}:
      h => Empty.absurd({Spec.Star{} == Spec.Any{}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Star{} Spec.Star{}:
      h => {==}
    case Spec.Star{} Spec.Class{+n2, +cs2}:
      h => Empty.absurd({Spec.Star{} == Spec.Class{n2, cs2}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Star{} Spec.Deep{}:
      h => Empty.absurd({Spec.Star{} == Spec.Deep{}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Star{} Spec.Cat{+a2, +b2}:
      h => Empty.absurd({Spec.Star{} == Spec.Cat{a2, b2}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Star{} Spec.Alt{+a2, +b2}:
      h => Empty.absurd({Spec.Star{} == Spec.Alt{a2, b2}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Class{+n1, +cs1} Spec.Void{}:
      +h => Empty.absurd({Spec.Class{n1, cs1} == Spec.Void{}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Class{+n1, +cs1} Spec.Eps{}:
      +h => Empty.absurd({Spec.Class{n1, cs1} == Spec.Eps{}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Class{+n1, +cs1} Spec.Lit{+x2}:
      +h => Empty.absurd({Spec.Class{n1, cs1} == Spec.Lit{x2}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Class{+n1, +cs1} Spec.Any{}:
      +h => Empty.absurd({Spec.Class{n1, cs1} == Spec.Any{}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Class{+n1, +cs1} Spec.Star{}:
      +h => Empty.absurd({Spec.Class{n1, cs1} == Spec.Star{}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Class{+n1, +cs1} Spec.Class{+n2, +cs2}:
      +h =>
        %Bool.is_eq_sound(n1, n2)(Bool.and_left(Bool.is_eq(n1, n2), Chars.is_eq(cs1, cs2))(h)) : {Spec.Class{n1, cs1} == Spec.Class{_, cs2}: Spec.Glob}
        %Chars.is_eq_sound(cs1, cs2)(Bool.and_right(Bool.is_eq(n1, n2), Chars.is_eq(cs1, cs2))(h)) : {Spec.Class{n1, cs1} == Spec.Class{n1, _}: Spec.Glob}
        {==}
    case Spec.Class{+n1, +cs1} Spec.Deep{}:
      +h => Empty.absurd({Spec.Class{n1, cs1} == Spec.Deep{}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Class{+n1, +cs1} Spec.Cat{+a2, +b2}:
      +h => Empty.absurd({Spec.Class{n1, cs1} == Spec.Cat{a2, b2}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Class{+n1, +cs1} Spec.Alt{+a2, +b2}:
      +h => Empty.absurd({Spec.Class{n1, cs1} == Spec.Alt{a2, b2}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Deep{} Spec.Void{}:
      h => Empty.absurd({Spec.Deep{} == Spec.Void{}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Deep{} Spec.Eps{}:
      h => Empty.absurd({Spec.Deep{} == Spec.Eps{}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Deep{} Spec.Lit{+x2}:
      h => Empty.absurd({Spec.Deep{} == Spec.Lit{x2}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Deep{} Spec.Any{}:
      h => Empty.absurd({Spec.Deep{} == Spec.Any{}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Deep{} Spec.Star{}:
      h => Empty.absurd({Spec.Deep{} == Spec.Star{}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Deep{} Spec.Class{+n2, +cs2}:
      h => Empty.absurd({Spec.Deep{} == Spec.Class{n2, cs2}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Deep{} Spec.Deep{}:
      h => {==}
    case Spec.Deep{} Spec.Cat{+a2, +b2}:
      h => Empty.absurd({Spec.Deep{} == Spec.Cat{a2, b2}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Deep{} Spec.Alt{+a2, +b2}:
      h => Empty.absurd({Spec.Deep{} == Spec.Alt{a2, b2}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Cat{+a1, +b1} Spec.Void{}:
      +h => Empty.absurd({Spec.Cat{a1, b1} == Spec.Void{}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Cat{+a1, +b1} Spec.Eps{}:
      +h => Empty.absurd({Spec.Cat{a1, b1} == Spec.Eps{}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Cat{+a1, +b1} Spec.Lit{+x2}:
      +h => Empty.absurd({Spec.Cat{a1, b1} == Spec.Lit{x2}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Cat{+a1, +b1} Spec.Any{}:
      +h => Empty.absurd({Spec.Cat{a1, b1} == Spec.Any{}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Cat{+a1, +b1} Spec.Star{}:
      +h => Empty.absurd({Spec.Cat{a1, b1} == Spec.Star{}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Cat{+a1, +b1} Spec.Class{+n2, +cs2}:
      +h => Empty.absurd({Spec.Cat{a1, b1} == Spec.Class{n2, cs2}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Cat{+a1, +b1} Spec.Deep{}:
      +h => Empty.absurd({Spec.Cat{a1, b1} == Spec.Deep{}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Cat{+a1, +b1} Spec.Cat{+a2, +b2}:
      +h =>
        %Glob.is_eq_sound(a1, a2)(Bool.and_left(Glob.is_eq(a1, a2), Glob.is_eq(b1, b2))(h)) : {Spec.Cat{a1, b1} == Spec.Cat{_, b2}: Spec.Glob}
        %Glob.is_eq_sound(b1, b2)(Bool.and_right(Glob.is_eq(a1, a2), Glob.is_eq(b1, b2))(h)) : {Spec.Cat{a1, b1} == Spec.Cat{a1, _}: Spec.Glob}
        {==}
    case Spec.Cat{+a1, +b1} Spec.Alt{+a2, +b2}:
      +h => Empty.absurd({Spec.Cat{a1, b1} == Spec.Alt{a2, b2}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Alt{+a1, +b1} Spec.Void{}:
      +h => Empty.absurd({Spec.Alt{a1, b1} == Spec.Void{}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Alt{+a1, +b1} Spec.Eps{}:
      +h => Empty.absurd({Spec.Alt{a1, b1} == Spec.Eps{}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Alt{+a1, +b1} Spec.Lit{+x2}:
      +h => Empty.absurd({Spec.Alt{a1, b1} == Spec.Lit{x2}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Alt{+a1, +b1} Spec.Any{}:
      +h => Empty.absurd({Spec.Alt{a1, b1} == Spec.Any{}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Alt{+a1, +b1} Spec.Star{}:
      +h => Empty.absurd({Spec.Alt{a1, b1} == Spec.Star{}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Alt{+a1, +b1} Spec.Class{+n2, +cs2}:
      +h => Empty.absurd({Spec.Alt{a1, b1} == Spec.Class{n2, cs2}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Alt{+a1, +b1} Spec.Deep{}:
      +h => Empty.absurd({Spec.Alt{a1, b1} == Spec.Deep{}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Alt{+a1, +b1} Spec.Cat{+a2, +b2}:
      +h => Empty.absurd({Spec.Alt{a1, b1} == Spec.Cat{a2, b2}: Spec.Glob}, Bool.false_ne_true(h))
    case Spec.Alt{+a1, +b1} Spec.Alt{+a2, +b2}:
      +h =>
        %Glob.is_eq_sound(a1, a2)(Bool.and_left(Glob.is_eq(a1, a2), Glob.is_eq(b1, b2))(h)) : {Spec.Alt{a1, b1} == Spec.Alt{_, b2}: Spec.Glob}
        %Glob.is_eq_sound(b1, b2)(Bool.and_right(Glob.is_eq(a1, a2), Glob.is_eq(b1, b2))(h)) : {Spec.Alt{a1, b1} == Spec.Alt{a1, _}: Spec.Glob}
        {==}

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
def Glob.alt_or(p: String, a: Spec.Glob, b: Spec.Glob) ->
  {Bool.or(Spec.Glob.matches(p, a), Spec.Glob.matches(p, b))
    == Spec.Glob.matches(p, Spec.Alt{a, b}): Bool}:
  match p:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      Glob.alt_or(t, Spec.Glob.step(a, c), Spec.Glob.step(b, c))

# Cat after Void matches nothing
def Glob.cat_void_l(p: String, +x: Spec.Glob) ->
  {False{} == Spec.Glob.matches(p, Spec.Cat{Spec.Void{}, x}): Bool}:
  match p:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      +x2 = Spec.Glob.step(x, c)
      %Glob.alt_or(t, Spec.Cat{Spec.Void{}, x}, Spec.Cat{Spec.Void{}, x2}) : {False{} == _: Bool}
      %Glob.cat_void_l(t, x) : {False{} == Bool.or(_, Spec.Glob.matches(t, Spec.Cat{Spec.Void{}, x2})): Bool}
      Glob.cat_void_l(t, x2)

# Cat before Void matches nothing
def Glob.cat_void_r(p: String, +x: Spec.Glob) ->
  {False{} == Spec.Glob.matches(p, Spec.Cat{x, Spec.Void{}}): Bool}:
  match p:
    case SNil{}:
      Bool.and_false(Spec.Glob.is_nullable(x))
    case SCon{+c, +t}:
      +x2 = Spec.Glob.step(x, c)
      +n = Spec.Glob.of_bool(Spec.Glob.is_nullable(x))
      %Glob.alt_or(t, Spec.Cat{x2, Spec.Void{}}, Spec.Cat{n, Spec.Void{}}) : {False{} == _: Bool}
      %Glob.cat_void_r(t, x2) : {False{} == Bool.or(_, Spec.Glob.matches(t, Spec.Cat{n, Spec.Void{}})): Bool}
      Glob.cat_void_r(t, n)

# Cat after Eps matches what its right side matches
def Glob.cat_eps_l(p: String, +x: Spec.Glob) ->
  {Spec.Glob.matches(p, x) == Spec.Glob.matches(p, Spec.Cat{Spec.Eps{}, x}): Bool}:
  match p:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      +x2 = Spec.Glob.step(x, c)
      %Glob.alt_or(t, Spec.Cat{Spec.Void{}, x}, Spec.Cat{Spec.Eps{}, x2}) : {Spec.Glob.matches(t, x2) == _: Bool}
      %Glob.cat_void_l(t, x) : {Spec.Glob.matches(t, x2) == Bool.or(_, Spec.Glob.matches(t, Spec.Cat{Spec.Eps{}, x2})): Bool}
      Glob.cat_eps_l(t, x2)

# Cat before Eps matches what its left side matches
def Glob.cat_eps_r(p: String, +x: Spec.Glob) ->
  {Spec.Glob.matches(p, x) == Spec.Glob.matches(p, Spec.Cat{x, Spec.Eps{}}): Bool}:
  match p:
    case SNil{}:
      Bool.and_true(Spec.Glob.is_nullable(x))
    case SCon{+c, +t}:
      +x2 = Spec.Glob.step(x, c)
      +n = Spec.Glob.of_bool(Spec.Glob.is_nullable(x))
      %Glob.alt_or(t, Spec.Cat{x2, Spec.Eps{}}, Spec.Cat{n, Spec.Void{}}) : {Spec.Glob.matches(t, x2) == _: Bool}
      %Glob.cat_void_r(t, n) : {Spec.Glob.matches(t, x2) == Bool.or(Spec.Glob.matches(t, Spec.Cat{x2, Spec.Eps{}}), _): Bool}
      %Bool.or_false(Spec.Glob.matches(t, Spec.Cat{x2, Spec.Eps{}})) : {Spec.Glob.matches(t, x2) == _: Bool}
      Glob.cat_eps_r(t, x2)

# and distributes over or, from the right
def Bool.distrib_r(a: Bool, b: Bool, r: Bool) -> {Bool.or(Bool.and(a, r), Bool.and(b, r)) == Bool.and(Bool.or(a, b), r): Bool}:
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
def Bool.and_assoc(a: Bool, b: Bool, r: Bool) -> {Bool.and(a, Bool.and(b, r)) == Bool.and(Bool.and(a, b), r): Bool}:
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
def Bool.cat_alt_step(x: Bool, y: Bool, a: Bool, b: Bool, z: Bool) -> {Bool.or(Bool.or(x, Bool.and(a, z)), Bool.or(y, Bool.and(b, z))) == Bool.or(Bool.or(x, y), Bool.and(Bool.or(a, b), z)): Bool}:
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
def Bool.cat_assoc_step(x: Bool, y: Bool, a: Bool, b: Bool, z: Bool) -> {Bool.or(x, Bool.and(a, Bool.or(y, Bool.and(b, z)))) == Bool.or(Bool.or(x, Bool.and(a, y)), Bool.and(Bool.and(a, b), z)): Bool}:
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
def Glob.cat_of_bool(p: String, b: Bool, +r: Spec.Glob) ->
  {Bool.and(b, Spec.Glob.matches(p, r)) == Spec.Glob.matches(p, Spec.Cat{Spec.Glob.of_bool(b), r}): Bool}:
  match b:
    case False{}:
      Glob.cat_void_l(p, r)
    case True{}:
      Glob.cat_eps_l(p, r)

# Cat after Alt matches what either Cat matches
def Glob.cat_alt(p: String, +a: Spec.Glob, +b: Spec.Glob, +r: Spec.Glob) ->
  {Bool.or(Spec.Glob.matches(p, Spec.Cat{a, r}), Spec.Glob.matches(p, Spec.Cat{b, r}))
    == Spec.Glob.matches(p, Spec.Cat{Spec.Alt{a, b}, r}): Bool}:
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
      +q1 = {Spec.Cat{Spec.Glob.of_bool(na), r2}: Spec.Glob}
      +p2 = {Spec.Cat{b2, r}: Spec.Glob}
      +q2 = {Spec.Cat{Spec.Glob.of_bool(nb), r2}: Spec.Glob}
      +ab = {Spec.Cat{Spec.Alt{a2, b2}, r}: Spec.Glob}
      +qab = {Spec.Cat{Spec.Glob.of_bool(Bool.or(na, nb)), r2}: Spec.Glob}
      +x = Spec.Glob.matches(t, p1)
      +y = Spec.Glob.matches(t, p2)
      +z = Spec.Glob.matches(t, r2)
      +rhs = Spec.Glob.matches(t, Spec.Alt{ab, qab})
      %Glob.alt_or(t, p1, q1) : {Bool.or(_, Spec.Glob.matches(t, Spec.Alt{p2, q2})) == rhs: Bool}
      %Glob.alt_or(t, p2, q2) : {Bool.or(Bool.or(x, Spec.Glob.matches(t, q1)), _) == rhs: Bool}
      %Glob.cat_of_bool(t, na, r2) : {Bool.or(Bool.or(x, _), Bool.or(y, Spec.Glob.matches(t, q2))) == rhs: Bool}
      +l = Bool.or(Bool.or(x, Bool.and(na, z)), Bool.or(y, Bool.and(nb, z)))
      %Glob.cat_of_bool(t, nb, r2) : {Bool.or(Bool.or(x, Bool.and(na, z)), Bool.or(y, _)) == rhs: Bool}
      %Glob.alt_or(t, ab, qab) : {l == _: Bool}
      %Glob.cat_alt(t, a2, b2, r) : {l == Bool.or(_, Spec.Glob.matches(t, qab)): Bool}
      %Glob.cat_of_bool(t, Bool.or(na, nb), r2) : {l == Bool.or(Bool.or(x, y), _): Bool}
      Bool.cat_alt_step(x, y, na, nb, z)

# Cat is associative
def Glob.cat_assoc(p: String, +a: Spec.Glob, +b: Spec.Glob, +r: Spec.Glob) ->
  {Spec.Glob.matches(p, Spec.Cat{a, Spec.Cat{b, r}})
    == Spec.Glob.matches(p, Spec.Cat{Spec.Cat{a, b}, r}): Bool}:
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
      +q = {Spec.Cat{Spec.Glob.of_bool(na), inner}: Spec.Glob}
      +c1 = {Spec.Cat{a2, b}: Spec.Glob}
      +c2 = {Spec.Cat{Spec.Glob.of_bool(na), b2}: Spec.Glob}
      +qn = {Spec.Cat{Spec.Glob.of_bool(Bool.and(na, nb)), r2}: Spec.Glob}
      +x = Spec.Glob.matches(t, x1)
      +y = Spec.Glob.matches(t, br)
      +z = Spec.Glob.matches(t, r2)
      +rhs = Spec.Glob.matches(t, Spec.Alt{Spec.Cat{Spec.Alt{c1, c2}, r}, qn})
      %Glob.alt_or(t, x1, q) : {_ == rhs: Bool}
      %Glob.cat_of_bool(t, na, inner) : {Bool.or(x, _) == rhs: Bool}
      %Glob.alt_or(t, br, Spec.Cat{Spec.Glob.of_bool(nb), r2}) : {Bool.or(x, Bool.and(na, _)) == rhs: Bool}
      %Glob.cat_of_bool(t, nb, r2) : {Bool.or(x, Bool.and(na, Bool.or(y, _))) == rhs: Bool}
      +l = Bool.or(x, Bool.and(na, Bool.or(y, Bool.and(nb, z))))
      %Glob.alt_or(t, Spec.Cat{Spec.Alt{c1, c2}, r}, qn) : {l == _: Bool}
      %Glob.cat_alt(t, c1, c2, r) : {l == Bool.or(_, Spec.Glob.matches(t, qn)): Bool}
      %Glob.cat_assoc(t, a2, b, r) : {l == Bool.or(Bool.or(_, Spec.Glob.matches(t, Spec.Cat{c2, r})), Spec.Glob.matches(t, qn)): Bool}
      %Glob.cat_assoc(t, Spec.Glob.of_bool(na), b2, r) : {l == Bool.or(Bool.or(x, _), Spec.Glob.matches(t, qn)): Bool}
      %Glob.cat_of_bool(t, na, br) : {l == Bool.or(Bool.or(x, _), Spec.Glob.matches(t, qn)): Bool}
      %Glob.cat_of_bool(t, Bool.and(na, nb), r2) : {l == Bool.or(Bool.or(x, Bool.and(na, y)), _): Bool}
      Bool.cat_assoc_step(x, y, na, nb, z)

# or is associative
def Bool.or_assoc(a: Bool, b: Bool, c: Bool) -> {Bool.or(a, Bool.or(b, c)) == Bool.or(Bool.or(a, b), c): Bool}:
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
def Seqs.matches(+p: String, xs: List<&2, List<&2, Spec.Glob>>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(Spec.Glob.matches(p, Seq.glob(h)), Seqs.matches(p, t))

# xs then ys matches what xs or ys matches
def Seqs.matches_append(
  +p: String, xs: List<&2, List<&2, Spec.Glob>>, +ys: List<&2, List<&2, Spec.Glob>>
) -> {Bool.or(Seqs.matches(p, xs), Seqs.matches(p, ys))
  == Seqs.matches(p, List.append(&2, List<&2, Spec.Glob>, xs, ys)): Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      +m = Spec.Glob.matches(p, Seq.glob(h))
      %Seqs.matches_append(p, t, ys) : {Bool.or(Bool.or(m, Seqs.matches(p, t)), Seqs.matches(p, ys)) == Bool.or(m, _): Bool}
      Equal.sym(Bool, Bool.or(m, Bool.or(Seqs.matches(p, t), Seqs.matches(p, ys))),
        Bool.or(Bool.or(m, Seqs.matches(p, t)), Seqs.matches(p, ys)),
        Bool.or_assoc(m, Seqs.matches(p, t), Seqs.matches(p, ys)))

# [r] when hit, else []
def Seq.keep(hit: Bool, r: List<&2, Spec.Glob>) -> List<&2, List<&2, Spec.Glob>>:
  match hit:
    case False{}:
      []
    case True{}:
      [r]

# the Seqs that h then r becomes after c, given k: what r becomes after c
def Seq.step.head(
  h: Spec.Glob, +r: List<&2, Spec.Glob>, +c: Char, +k: List<&2, List<&2, Spec.Glob>>
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

# the Seqs that s becomes after c
def Seq.step(s: List<&2, Spec.Glob>, +c: Char) -> List<&2, List<&2, Spec.Glob>>:
  match s:
    case Nil{}:
      []
    case Con{h, +t}:
      Seq.step.head(h, t, c, Seq.step(t, c))

# Seq.keep(hit, r) matches t when hit holds and r matches t
def Seq.keep_ok(+hit: Bool, +t: String, +r: List<&2, Spec.Glob>) ->
  {Seqs.matches(t, Seq.keep(hit, r))
    == Bool.or(Bool.and(hit, Spec.Glob.matches(t, Seq.glob(r))), False{}): Bool}:
  match hit:
    case False{}:
      {==}
    case True{}:
      {==}

# a head that reads one character: after c it is of_bool(hit), then r
def Seq.step_head_one(+hit: Bool, +r: List<&2, Spec.Glob>, +c: Char, +t: String) ->
  {Seqs.matches(t, Seq.keep(hit, r)) == Spec.Glob.matches(t, Spec.Alt{
    Spec.Cat{Spec.Glob.of_bool(hit), Seq.glob(r)},
    Spec.Cat{Spec.Void{}, Spec.Glob.step(Seq.glob(r), c)}
  }): Bool}:
  +g = Seq.glob(r)
  +g2 = Spec.Glob.step(g, c)
  +l = Seqs.matches(t, Seq.keep(hit, r))
  %Glob.alt_or(t, Spec.Cat{Spec.Glob.of_bool(hit), g}, Spec.Cat{Spec.Void{}, g2}) : {l == _: Bool}
  %Glob.cat_of_bool(t, hit, g) : {l == Bool.or(_, Spec.Glob.matches(t, Spec.Cat{Spec.Void{}, g2})): Bool}
  %Glob.cat_void_l(t, g2) : {l == Bool.or(Bool.and(hit, Spec.Glob.matches(t, g)), _): Bool}
  Seq.keep_ok(hit, t, r)

# Seq.step.head(h, r, c, k) matches t when h then r matches c then t,
# given that k matches t when r matches c then t
def Seq.step_head_ok(
  h: Spec.Glob, +r: List<&2, Spec.Glob>, +c: Char, +t: String,
  +k: List<&2, List<&2, Spec.Glob>>,
  +hk: {Seqs.matches(t, k) == Spec.Glob.matches(SCon{c, t}, Seq.glob(r)): Bool}
) -> {Seqs.matches(t, Seq.step.head(h, r, c, k))
  == Spec.Glob.matches(SCon{c, t}, Spec.Cat{h, Seq.glob(r)}): Bool}:
  match h:
    case Spec.Void{}:
      +g = Seq.glob(r)
      Glob.cat_void_l(SCon{c, t}, g)
    case Spec.Eps{}:
      +g = Seq.glob(r)
      %Glob.cat_eps_l(SCon{c, t}, g) : {Seqs.matches(t, k) == _: Bool}
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
      +sk = Seqs.matches(t, k)
      +cs = {Spec.Cat{Spec.Cat{Spec.Glob.of_bool(i), Spec.Star{}}, g}: Spec.Glob}
      +rhs = Spec.Glob.matches(t, Spec.Alt{cs, Spec.Cat{Spec.Eps{}, g2}})
      %Seqs.matches_append(t, Seq.keep(i, s), k) : {_ == rhs: Bool}
      %Equal.sym(Bool, Seqs.matches(t, Seq.keep(i, s)), Bool.or(Bool.and(i, m), False{}), Seq.keep_ok(i, t, s)) : {Bool.or(_, sk) == rhs: Bool}
      %Bool.or_false(Bool.and(i, m)) : {Bool.or(_, sk) == rhs: Bool}
      +l = Bool.or(Bool.and(i, m), sk)
      %Glob.alt_or(t, cs, Spec.Cat{Spec.Eps{}, g2}) : {l == _: Bool}
      %Glob.cat_assoc(t, Spec.Glob.of_bool(i), Spec.Star{}, g) : {l == Bool.or(_, Spec.Glob.matches(t, Spec.Cat{Spec.Eps{}, g2})): Bool}
      %Glob.cat_of_bool(t, i, Spec.Cat{Spec.Star{}, g}) : {l == Bool.or(_, Spec.Glob.matches(t, Spec.Cat{Spec.Eps{}, g2})): Bool}
      %Glob.cat_eps_l(t, g2) : {l == Bool.or(Bool.and(i, m), _): Bool}
      %hk : {l == Bool.or(Bool.and(i, m), _): Bool}
      {==}
    case Spec.Class{neg, cs}:
      hit = Bool.xor(neg, List.contains(~Char, ~Char.is_eq, cs, c))
      Seq.step_head_one(Bool.and(Spec.is_inner(c), hit), r, c, t)
    case Spec.Deep{}:
      +g = Seq.glob(r)
      +g2 = Spec.Glob.step(g, c)
      +l = Seqs.matches(t, Con{Con{Spec.Deep{}, r}, k})
      %Glob.alt_or(t, Spec.Cat{Spec.Deep{}, g}, Spec.Cat{Spec.Eps{}, g2}) : {l == _: Bool}
      %Glob.cat_eps_l(t, g2) : {l == Bool.or(Spec.Glob.matches(t, Spec.Cat{Spec.Deep{}, g}), _): Bool}
      %hk : {l == Bool.or(Spec.Glob.matches(t, Spec.Cat{Spec.Deep{}, g}), _): Bool}
      {==}
    case Spec.Cat{+a, +b}:
      +g = Seq.glob(r)
      +kb = Seq.step.head(b, r, c, k)
      hb = Seq.step_head_ok(b, r, c, t, k, hk)
      %Glob.cat_assoc(SCon{c, t}, a, b, g) : {Seqs.matches(t, Seq.step.head(a, Con{b, r}, c, kb)) == _: Bool}
      Seq.step_head_ok(a, Con{b, r}, c, t, kb, hb)
    case Spec.Alt{+a, +b}:
      +g = Seq.glob(r)
      +ka = Seq.step.head(a, r, c, k)
      +kb = Seq.step.head(b, r, c, k)
      +l = Bool.or(Seqs.matches(t, ka), Seqs.matches(t, kb))
      %Seqs.matches_append(t, ka, kb) : {_ == Spec.Glob.matches(SCon{c, t}, Spec.Cat{Spec.Alt{a, b}, g}): Bool}
      %Glob.cat_alt(SCon{c, t}, a, b, g) : {l == _: Bool}
      %Seq.step_head_ok(a, r, c, t, k, hk) : {l == Bool.or(_, Spec.Glob.matches(SCon{c, t}, Spec.Cat{b, g})): Bool}
      %Seq.step_head_ok(b, r, c, t, k, hk) : {l == Bool.or(Seqs.matches(t, ka), _): Bool}
      {==}

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
def Bool.or_swap(a: Bool, b: Bool, r: Bool) -> {Bool.or(a, Bool.or(b, r)) == Bool.or(b, Bool.or(a, r)): Bool}:
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
def Seq.step_ok(s: List<&2, Spec.Glob>, +c: Char, +t: String) ->
  {Seqs.matches(t, Seq.step(s, c)) == Spec.Glob.matches(SCon{c, t}, Seq.glob(s)): Bool}:
  match s:
    case Nil{}:
      Glob.void_never(t)
    case Con{h, +r}:
      Seq.step_head_ok(h, r, c, t, Seq.step(r, c), Seq.step_ok(r, c, t))

# xs and ys are the same globs
def Seq.is_eq(xs: List<&2, Spec.Glob>, ys: List<&2, Spec.Glob>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{x, xt} Con{y, yt}:
      Bool.and(Glob.is_eq(x, y), Seq.is_eq(xt, yt))
    case _ _:
      False{}

# Seq.is_eq is True only for the same globs
def Seq.is_eq_sound(xs: List<&2, Spec.Glob>, ys: List<&2, Spec.Glob>) ->
  {Seq.is_eq(xs, ys) == True{}: Bool} -> {xs == ys: List<&2, Spec.Glob>}:
  match xs ys:
    case Nil{} Nil{}:
      h => {==}
    case Nil{} Con{y, yt}:
      h => Empty.absurd({Nil{} == Con{y, yt}: List<&2, Spec.Glob>}, Bool.false_ne_true(h))
    case Con{x, xt} Nil{}:
      h => Empty.absurd({Con{x, xt} == Nil{}: List<&2, Spec.Glob>}, Bool.false_ne_true(h))
    case Con{+x, +xt} Con{+y, +yt}:
      +h =>
        %Glob.is_eq_sound(x, y)(Bool.and_left(Glob.is_eq(x, y), Seq.is_eq(xt, yt))(h)) :
          {Con{x, xt} == Con{_, yt}: List<&2, Spec.Glob>}
        %Seq.is_eq_sound(xt, yt)(Bool.and_right(Glob.is_eq(x, y), Seq.is_eq(xt, yt))(h)) :
          {Con{x, xt} == Con{x, _}: List<&2, Spec.Glob>}
        {==}

# xs holds x
def Seqs.has(xs: List<&2, List<&2, Spec.Glob>>, +x: List<&2, Spec.Glob>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(Seq.is_eq(h, x), Seqs.has(t, x))

# one step of Seqs.has_absorb, with e the answer of Seq.is_eq(hd, x)
def Seqs.has_absorb.at(
  +hd: List<&2, Spec.Glob>, +r: List<&2, List<&2, Spec.Glob>>, +x: List<&2, Spec.Glob>,
  +t: String, e: Bool,
  ih: {Seqs.has(r, x) == True{}: Bool} ->
    {Seqs.matches(t, r) == Bool.or(Spec.Glob.matches(t, Seq.glob(x)), Seqs.matches(t, r)): Bool}
) -> {Seq.is_eq(hd, x) == e: Bool} -> {Bool.or(e, Seqs.has(r, x)) == True{}: Bool} ->
  {Seqs.matches(t, Con{hd, r})
    == Bool.or(Spec.Glob.matches(t, Seq.glob(x)), Seqs.matches(t, Con{hd, r})): Bool}:
  match e:
    case True{}:
      eq => h =>
        +mh = Spec.Glob.matches(t, Seq.glob(hd))
        +sr = Seqs.matches(t, r)
        %Seq.is_eq_sound(hd, x)(eq) : {Bool.or(mh, sr) == Bool.or(Spec.Glob.matches(t, Seq.glob(_)), Bool.or(mh, sr)): Bool}
        Equal.sym(Bool, Bool.or(mh, Bool.or(mh, sr)), Bool.or(mh, sr), Bool.or_absorb(mh, sr))
    case False{}:
      eq => h =>
        +mh = Spec.Glob.matches(t, Seq.glob(hd))
        +sr = Seqs.matches(t, r)
        +mx = Spec.Glob.matches(t, Seq.glob(x))
        %Bool.or_swap(mh, mx, sr) : {Bool.or(mh, sr) == _: Bool}
        %ih(h) : {Bool.or(mh, sr) == Bool.or(mh, _): Bool}
        {==}

# a Seq that xs holds adds nothing to what xs matches
def Seqs.has_absorb(xs: List<&2, List<&2, Spec.Glob>>, +x: List<&2, Spec.Glob>, +t: String) ->
  {Seqs.has(xs, x) == True{}: Bool} ->
  {Seqs.matches(t, xs) == Bool.or(Spec.Glob.matches(t, Seq.glob(x)), Seqs.matches(t, xs)): Bool}:
  match xs:
    case Nil{}:
      h => Empty.absurd(
        {False{} == Bool.or(Spec.Glob.matches(t, Seq.glob(x)), False{}): Bool},
        Bool.false_ne_true(h)
      )
    case Con{+hd, +r}:
      h => Seqs.has_absorb.at(hd, r, x, t, Seq.is_eq(hd, x), Seqs.has_absorb(r, x, t))({==}, h)

# xs when has, else x before xs
def Seqs.add.if(x: List<&2, Spec.Glob>, xs: List<&2, List<&2, Spec.Glob>>, has: Bool) ->
  List<&2, List<&2, Spec.Glob>>:
  match has:
    case False{}:
      Con{x, xs}
    case True{}:
      xs

# xs with x, once
def Seqs.add(+x: List<&2, Spec.Glob>, +xs: List<&2, List<&2, Spec.Glob>>) ->
  List<&2, List<&2, Spec.Glob>>:
  Seqs.add.if(x, xs, Seqs.has(xs, x))

# Seqs.add_ok, given b, the answer of Seqs.has(xs, x)
def Seqs.add_ok.at(+x: List<&2, Spec.Glob>, +xs: List<&2, List<&2, Spec.Glob>>, +t: String, b: Bool) ->
  {Seqs.has(xs, x) == b: Bool} ->
  {Bool.or(Spec.Glob.matches(t, Seq.glob(x)), Seqs.matches(t, xs))
    == Seqs.matches(t, Seqs.add.if(x, xs, b)): Bool}:
  match b:
    case False{}:
      e => {==}
    case True{}:
      e => Equal.sym(
        Bool, Seqs.matches(t, xs), Bool.or(Spec.Glob.matches(t, Seq.glob(x)), Seqs.matches(t, xs)),
        Seqs.has_absorb(xs, x, t)(e)
      )

# Seqs.add(x, xs) matches what x or xs matches
def Seqs.add_ok(+x: List<&2, Spec.Glob>, +xs: List<&2, List<&2, Spec.Glob>>, +t: String) ->
  {Bool.or(Spec.Glob.matches(t, Seq.glob(x)), Seqs.matches(t, xs)) == Seqs.matches(t, Seqs.add(x, xs)): Bool}:
  Seqs.add_ok.at(x, xs, t, Seqs.has(xs, x))({==})

# acc with each Seq of ys, once
def Seqs.add_all(ys: List<&2, List<&2, Spec.Glob>>, acc: List<&2, List<&2, Spec.Glob>>) ->
  List<&2, List<&2, Spec.Glob>>:
  match ys:
    case Nil{}:
      acc
    case Con{y, r}:
      Seqs.add(y, Seqs.add_all(r, acc))

# Seqs.add_all(ys, acc) matches what ys or acc matches
def Seqs.add_all_ok(ys: List<&2, List<&2, Spec.Glob>>, +acc: List<&2, List<&2, Spec.Glob>>, +t: String) ->
  {Bool.or(Seqs.matches(t, ys), Seqs.matches(t, acc)) == Seqs.matches(t, Seqs.add_all(ys, acc)): Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +r}:
      +my = Spec.Glob.matches(t, Seq.glob(y))
      +l = Bool.or(Bool.or(my, Seqs.matches(t, r)), Seqs.matches(t, acc))
      %Seqs.add_ok(y, Seqs.add_all(r, acc), t) : {l == _: Bool}
      %Seqs.add_all_ok(r, acc, t) : {l == Bool.or(my, _): Bool}
      Equal.sym(
        Bool, Bool.or(my, Bool.or(Seqs.matches(t, r), Seqs.matches(t, acc))), l,
        Bool.or_assoc(my, Seqs.matches(t, r), Seqs.matches(t, acc))
      )

# the Seqs that xs become after c
def Seqs.step(xs: List<&2, List<&2, Spec.Glob>>, +c: Char) -> List<&2, List<&2, Spec.Glob>>:
  match xs:
    case Nil{}:
      []
    case Con{x, r}:
      Seqs.add_all(Seq.step(x, c), Seqs.step(r, c))

# Seqs.step(xs, c) matches t when xs matches c then t
def Seqs.step_ok(xs: List<&2, List<&2, Spec.Glob>>, +c: Char, +t: String) ->
  {Seqs.matches(t, Seqs.step(xs, c)) == Seqs.matches(SCon{c, t}, xs): Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      +a = Seq.step(x, c)
      +b = Seqs.step(r, c)
      %Seqs.add_all_ok(a, b, t) : {_ == Seqs.matches(SCon{c, t}, Con{x, r}): Bool}
      +l = Bool.or(Seqs.matches(t, a), Seqs.matches(t, b))
      %Seq.step_ok(x, c, t) : {l == Bool.or(_, Seqs.matches(SCon{c, t}, r)): Bool}
      %Seqs.step_ok(r, c, t) : {l == Bool.or(Seqs.matches(t, a), _): Bool}
      {==}

# Rules as derivative sets
# ------------------------

# A rule whose glob is a set of Seqs.
type Slot is Data:
  Inc{xs: List<&2, List<&2, Spec.Glob>>}
  Exc{xs: List<&2, List<&2, Spec.Glob>>}

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
def Seqs.single_ok(+p: String, +g: Spec.Glob) ->
  {Spec.Glob.matches(p, g) == Seqs.matches(p, [[g]]): Bool}:
  %Bool.or_false(Spec.Glob.matches(p, Spec.Cat{g, Spec.Eps{}})) : {Spec.Glob.matches(p, g) == _: Bool}
  Glob.cat_eps_r(p, g)

# rules and their slots select the same paths
def Slot.of_rules_ok(rules: List<&2, Spec.Rule>, +p: String, acc: Bool) ->
  {Spec.Rule.selects.go(rules, p, acc) == Slot.selects.go(Slot.of_rules(rules), p, acc): Bool}:
  match rules acc:
    case Nil{} _:
      {==}
    case Con{Spec.Include{+g}, +t} False{}:
      %Seqs.single_ok(p, g) : {Spec.Rule.selects.go(t, p, Spec.Glob.matches(p, g))
        == Slot.selects.go(Slot.of_rules(t), p, _): Bool}
      Slot.of_rules_ok(t, p, Spec.Glob.matches(p, g))
    case Con{Spec.Include{g}, t} True{}:
      Slot.of_rules_ok(t, p, True{})
    case Con{Spec.Exclude{g}, t} False{}:
      Slot.of_rules_ok(t, p, False{})
    case Con{Spec.Exclude{+g}, +t} True{}:
      %Seqs.single_ok(p, g) : {Spec.Rule.selects.go(t, p, Bool.not(Spec.Glob.matches(p, g)))
        == Slot.selects.go(Slot.of_rules(t), p, Bool.not(_)): Bool}
      Slot.of_rules_ok(t, p, Bool.not(Spec.Glob.matches(p, g)))

# slots select c then t when their step after c selects t
def Slot.step_ok(slots: List<&2, Slot>, +c: Char, +t: String, acc: Bool) ->
  {Slot.selects.go(Slot.step(slots, c), t, acc) == Slot.selects.go(slots, SCon{c, t}, acc): Bool}:
  match slots acc:
    case Nil{} _:
      {==}
    case Con{Inc{+xs}, +r} False{}:
      %Seqs.step_ok(xs, c, t) : {Slot.selects.go(Slot.step(r, c), t, Seqs.matches(t, Seqs.step(xs, c)))
        == Slot.selects.go(r, SCon{c, t}, _): Bool}
      Slot.step_ok(r, c, t, Seqs.matches(t, Seqs.step(xs, c)))
    case Con{Inc{xs}, r} True{}:
      Slot.step_ok(r, c, t, True{})
    case Con{Exc{xs}, r} False{}:
      Slot.step_ok(r, c, t, False{})
    case Con{Exc{+xs}, +r} True{}:
      %Seqs.step_ok(xs, c, t) : {Slot.selects.go(Slot.step(r, c), t, Bool.not(Seqs.matches(t, Seqs.step(xs, c))))
        == Slot.selects.go(r, SCon{c, t}, Bool.not(_)): Bool}
      Slot.step_ok(r, c, t, Bool.not(Seqs.matches(t, Seqs.step(xs, c))))

# Search states
# -------------

# xs and ys are the same Seqs
def Seqs.is_eq(xs: List<&2, List<&2, Spec.Glob>>, ys: List<&2, List<&2, Spec.Glob>>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{x, xt} Con{y, yt}:
      Bool.and(Seq.is_eq(x, y), Seqs.is_eq(xt, yt))
    case _ _:
      False{}

# Seqs.is_eq is True only for the same Seqs
def Seqs.is_eq_sound(xs: List<&2, List<&2, Spec.Glob>>, ys: List<&2, List<&2, Spec.Glob>>) ->
  {Seqs.is_eq(xs, ys) == True{}: Bool} -> {xs == ys: List<&2, List<&2, Spec.Glob>>}:
  match xs ys:
    case Nil{} Nil{}:
      h => {==}
    case Nil{} Con{y, yt}:
      h => Empty.absurd({Nil{} == Con{y, yt}: List<&2, List<&2, Spec.Glob>>}, Bool.false_ne_true(h))
    case Con{x, xt} Nil{}:
      h => Empty.absurd({Con{x, xt} == Nil{}: List<&2, List<&2, Spec.Glob>>}, Bool.false_ne_true(h))
    case Con{+x, +xt} Con{+y, +yt}:
      +h =>
        %Seq.is_eq_sound(x, y)(Bool.and_left(Seq.is_eq(x, y), Seqs.is_eq(xt, yt))(h)) :
          {Con{x, xt} == Con{_, yt}: List<&2, List<&2, Spec.Glob>>}
        %Seqs.is_eq_sound(xt, yt)(Bool.and_right(Seq.is_eq(x, y), Seqs.is_eq(xt, yt))(h)) :
          {Con{x, xt} == Con{x, _}: List<&2, List<&2, Spec.Glob>>}
        {==}

# a and b are the same slots
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

# Slots.is_eq is True only for the same slots
def Slots.is_eq_sound(a: List<&2, Slot>, b: List<&2, Slot>) ->
  {Slots.is_eq(a, b) == True{}: Bool} -> {a == b: List<&2, Slot>}:
  match a b:
    case Nil{} Nil{}:
      h => {==}
    case Nil{} Con{y, bt}:
      h => Empty.absurd({Nil{} == Con{y, bt}: List<&2, Slot>}, Bool.false_ne_true(h))
    case Con{x, at} Nil{}:
      h => Empty.absurd({Con{x, at} == Nil{}: List<&2, Slot>}, Bool.false_ne_true(h))
    case Con{Inc{x}, at} Con{Exc{y}, bt}:
      h => Empty.absurd({Con{Inc{x}, at} == Con{Exc{y}, bt}: List<&2, Slot>}, Bool.false_ne_true(h))
    case Con{Exc{x}, at} Con{Inc{y}, bt}:
      h => Empty.absurd({Con{Exc{x}, at} == Con{Inc{y}, bt}: List<&2, Slot>}, Bool.false_ne_true(h))
    case Con{Inc{+x}, +at} Con{Inc{+y}, +bt}:
      +h =>
        %Seqs.is_eq_sound(x, y)(Bool.and_left(Seqs.is_eq(x, y), Slots.is_eq(at, bt))(h)) :
          {Con{Inc{x}, at} == Con{Inc{_}, bt}: List<&2, Slot>}
        %Slots.is_eq_sound(at, bt)(Bool.and_right(Seqs.is_eq(x, y), Slots.is_eq(at, bt))(h)) :
          {Con{Inc{x}, at} == Con{Inc{x}, _}: List<&2, Slot>}
        {==}
    case Con{Exc{+x}, +at} Con{Exc{+y}, +bt}:
      +h =>
        %Seqs.is_eq_sound(x, y)(Bool.and_left(Seqs.is_eq(x, y), Slots.is_eq(at, bt))(h)) :
          {Con{Exc{x}, at} == Con{Exc{_}, bt}: List<&2, Slot>}
        %Slots.is_eq_sound(at, bt)(Bool.and_right(Seqs.is_eq(x, y), Slots.is_eq(at, bt))(h)) :
          {Con{Exc{x}, at} == Con{Exc{x}, _}: List<&2, Slot>}
        {==}

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
def St.holds(x: St, +p: String) -> Bool:
  match x:
    case St{both, a, b}:
      Bool.and(Slot.selects.go(a, p, False{}), St.side(both, Slot.selects.go(b, p, False{})))

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
def St.is_eq(x: St, y: St) -> Bool:
  match x y:
    case St{n, a, b} St{m, c, d}:
      Bool.and(Bool.is_eq(n, m), Bool.and(Slots.is_eq(a, c), Slots.is_eq(b, d)))

# St.is_eq is True only for the same state
def St.is_eq_sound(x: St, y: St) -> {St.is_eq(x, y) == True{}: Bool} -> {x == y: St}:
  match x y:
    case St{+n, +a, +b} St{+m, +c, +d}:
      +h =>
        +sa = Slots.is_eq(a, c)
        +sb = Slots.is_eq(b, d)
        +rest = Bool.and_right(Bool.is_eq(n, m), Bool.and(sa, sb))(h)
        %Bool.is_eq_sound(n, m)(Bool.and_left(Bool.is_eq(n, m), Bool.and(sa, sb))(h)) : {St{n, a, b} == St{_, c, d}: St}
        %Slots.is_eq_sound(a, c)(Bool.and_left(sa, sb)(rest)) : {St{n, a, b} == St{n, _, d}: St}
        %Slots.is_eq_sound(b, d)(Bool.and_right(sa, sb)(rest)) : {St{n, a, b} == St{n, a, _}: St}
        {==}

# xs holds x
def St.has(xs: List<&2, St>, +x: St) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(St.is_eq(h, x), St.has(t, x))

# the state after c holds for t when the state holds for c then t
def St.step_ok(x: St, +c: Char, +t: String) ->
  {St.holds(St.step(x, c), t) == St.holds(x, SCon{c, t}): Bool}:
  match x:
    case St{+both, +a, +b}:
      +l = Bool.and(
        Slot.selects.go(Slot.step(a, c), t, False{}),
        St.side(both, Slot.selects.go(Slot.step(b, c), t, False{}))
      )
      %Slot.step_ok(a, c, t, False{}) : {l == Bool.and(_, St.side(both, Slot.selects.go(b, SCon{c, t}, False{}))): Bool}
      %Slot.step_ok(b, c, t, False{}) : {l == Bool.and(Slot.selects.go(Slot.step(a, c), t, False{}), St.side(both, _)): Bool}
      {==}

# a query holds for p when p is a valid path and its start state holds
def St.of_ok(q: Spec.Query, +p: String) ->
  {Bool.and(Spec.is_path(p), St.holds(St.of(q), p)) == Spec.Query.holds(q, p): Bool}:
  match q:
    case Spec.Both{+a, +b}:
      +r = Spec.Query.holds(Spec.Both{a, b}, p)
      %Slot.of_rules_ok(a, p, False{}) : {Bool.and(Spec.is_path(p),
        Bool.and(_, Slot.selects.go(Slot.of_rules(b), p, False{}))) == r: Bool}
      %Slot.of_rules_ok(b, p, False{}) : {Bool.and(Spec.is_path(p),
        Bool.and(Spec.Rule.selects.go(a, p, False{}), _)) == r: Bool}
      {==}
    case Spec.Only{+a, +b}:
      +r = Spec.Query.holds(Spec.Only{a, b}, p)
      %Slot.of_rules_ok(a, p, False{}) : {Bool.and(Spec.is_path(p),
        Bool.and(_, Bool.not(Slot.selects.go(Slot.of_rules(b), p, False{})))) == r: Bool}
      %Slot.of_rules_ok(b, p, False{}) : {Bool.and(Spec.is_path(p),
        Bool.and(Spec.Rule.selects.go(a, p, False{}), Bool.not(_))) == r: Bool}
      {==}

# Representative characters
# -------------------------
# A character that no glob of a state names, and that is not '/', moves the
# state like any other such character.

# cs holds c
def Chars.has(cs: List<&2, Char>, +c: Char) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(Char.is_eq(h, c), Chars.has(t, c))

# every character of xs is in cs
def Chars.all_in(xs: List<&2, Char>, +cs: List<&2, Char>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      Bool.and(Chars.has(cs, h), Chars.all_in(t, cs))

# every character that g names is in cs
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

# every character that s names is in cs
def Seq.within(s: List<&2, Spec.Glob>, +cs: List<&2, Char>) -> Bool:
  match s:
    case Nil{}:
      True{}
    case Con{h, t}:
      Bool.and(Glob.within(h, cs), Seq.within(t, cs))

# every character that xs names is in cs
def Seqs.within(xs: List<&2, List<&2, Spec.Glob>>, +cs: List<&2, Char>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      Bool.and(Seq.within(h, cs), Seqs.within(t, cs))

# every character that slots name is in cs
def Slots.within(slots: List<&2, Slot>, +cs: List<&2, Char>) -> Bool:
  match slots:
    case Nil{}:
      True{}
    case Con{Inc{xs}, t}:
      Bool.and(Seqs.within(xs, cs), Slots.within(t, cs))
    case Con{Exc{xs}, t}:
      Bool.and(Seqs.within(xs, cs), Slots.within(t, cs))

# every character that x names is in cs
def St.within(x: St, +cs: List<&2, Char>) -> Bool:
  match x:
    case St{both, a, b}:
      Bool.and(Slots.within(a, cs), Slots.within(b, cs))

# a character x of cs is not c when c is not in cs, given b: Char.is_eq(x, c)
def Char.ne_in.at(
  +cs: List<&2, Char>, +x: Char, +c: Char, b: Bool,
  hx: {Chars.has(cs, x) == True{}: Bool}, hc: {Chars.has(cs, c) == False{}: Bool}
) -> {Char.is_eq(x, c) == b: Bool} -> {False{} == b: Bool}:
  match b:
    case False{}:
      e => {==}
    case True{}:
      e =>
        in_c = {
          %Char.is_eq_sound(x, c)(e) : {Chars.has(cs, _) == True{}: Bool}
          hx
          : {Chars.has(cs, c) == True{}: Bool}
        }
        Empty.absurd({False{} == True{}: Bool},
          Bool.false_ne_true(Equal.trans(Bool, False{}, Chars.has(cs, c), True{},
            Equal.sym(Bool, Chars.has(cs, c), False{}, hc), in_c)))

# a character x of cs is not c when c is not in cs
def Char.ne_in(
  +cs: List<&2, Char>, +x: Char, +c: Char,
  hx: {Chars.has(cs, x) == True{}: Bool}, hc: {Chars.has(cs, c) == False{}: Bool}
) -> {False{} == Char.is_eq(x, c): Bool}:
  Char.ne_in.at(cs, x, c, Char.is_eq(x, c), hx, hc)({==})

# c is not a character x of cs when c is not in cs, given b: Char.is_eq(c, x)
def Char.ne_in_r.at(
  +cs: List<&2, Char>, +x: Char, +c: Char, b: Bool,
  hx: {Chars.has(cs, x) == True{}: Bool}, hc: {Chars.has(cs, c) == False{}: Bool}
) -> {Char.is_eq(c, x) == b: Bool} -> {False{} == b: Bool}:
  match b:
    case False{}:
      e => {==}
    case True{}:
      e =>
        in_c = {
          %Equal.sym(Char, c, x, Char.is_eq_sound(c, x)(e)) : {Chars.has(cs, _) == True{}: Bool}
          hx
          : {Chars.has(cs, c) == True{}: Bool}
        }
        Empty.absurd({False{} == True{}: Bool},
          Bool.false_ne_true(Equal.trans(Bool, False{}, Chars.has(cs, c), True{},
            Equal.sym(Bool, Chars.has(cs, c), False{}, hc), in_c)))

# c is not a character x of cs when c is not in cs
def Char.ne_in_r(
  +cs: List<&2, Char>, +x: Char, +c: Char,
  hx: {Chars.has(cs, x) == True{}: Bool}, hc: {Chars.has(cs, c) == False{}: Bool}
) -> {False{} == Char.is_eq(c, x): Bool}:
  Char.ne_in_r.at(cs, x, c, Char.is_eq(c, x), hx, hc)({==})

# a class whose characters are all in cs does not hold c when cs does not
def Chars.contains_out(xs: List<&2, Char>, +cs: List<&2, Char>, +c: Char, +hc: {Chars.has(cs, c) == False{}: Bool}) ->
  {Chars.all_in(xs, cs) == True{}: Bool} -> {False{} == List.contains(~Char, ~Char.is_eq, xs, c): Bool}:
  match xs:
    case Nil{}:
      h => {==}
    case Con{+x, +t}:
      +h =>
        %Char.ne_in(cs, x, c, Bool.and_left(Chars.has(cs, x), Chars.all_in(t, cs))(h), hc) :
          {False{} == List.any.if(u => List.contains(~Char, ~Char.is_eq, t, c), _): Bool}
        Chars.contains_out(t, cs, c, hc)(Bool.and_right(Chars.has(cs, x), Chars.all_in(t, cs))(h))

# Seq.step.head moves h the same under c and f, two characters that h does
# not name and that are not '/'
def Seq.step.head_rep(
  h: Spec.Glob, +r: List<&2, Spec.Glob>, +c: Char, +f: Char,
  +kc: List<&2, List<&2, Spec.Glob>>, +kf: List<&2, List<&2, Spec.Glob>>, +cs: List<&2, Char>,
  +hc: {Chars.has(cs, c) == False{}: Bool}, +hf: {Chars.has(cs, f) == False{}: Bool},
  +hs: {Chars.has(cs, '/') == True{}: Bool}, +ek: {kc == kf: List<&2, List<&2, Spec.Glob>>}
) -> {Glob.within(h, cs) == True{}: Bool} ->
  {Seq.step.head(h, r, c, kc) == Seq.step.head(h, r, f, kf): List<&2, List<&2, Spec.Glob>>}:
  match h:
    case Spec.Void{}:
      hw => {==}
    case Spec.Eps{}:
      hw => ek
    case Spec.Lit{+x}:
      +hw =>
        %Char.ne_in(cs, x, c, hw, hc) : {Seq.keep(_, r) == Seq.keep(Char.is_eq(x, f), r): List<&2, List<&2, Spec.Glob>>}
        %Char.ne_in(cs, x, f, hw, hf) : {Seq.keep(False{}, r) == Seq.keep(_, r): List<&2, List<&2, Spec.Glob>>}
        {==}
    case Spec.Any{}:
      hw =>
        %Char.ne_in_r(cs, '/', c, hs, hc) : {Seq.keep(Bool.not(_), r) == Seq.keep(Spec.is_inner(f), r): List<&2, List<&2, Spec.Glob>>}
        %Char.ne_in_r(cs, '/', f, hs, hf) : {Seq.keep(True{}, r) == Seq.keep(Bool.not(_), r): List<&2, List<&2, Spec.Glob>>}
        {==}
    case Spec.Star{}:
      hw =>
        +s = {Con{Spec.Star{}, r}: List<&2, Spec.Glob>}
        %Char.ne_in_r(cs, '/', c, hs, hc) : {List.append(&2, List<&2, Spec.Glob>, Seq.keep(Bool.not(_), s), kc)
          == List.append(&2, List<&2, Spec.Glob>, Seq.keep(Spec.is_inner(f), s), kf): List<&2, List<&2, Spec.Glob>>}
        %Char.ne_in_r(cs, '/', f, hs, hf) : {List.append(&2, List<&2, Spec.Glob>, Seq.keep(True{}, s), kc)
          == List.append(&2, List<&2, Spec.Glob>, Seq.keep(Bool.not(_), s), kf): List<&2, List<&2, Spec.Glob>>}
        %ek : {List.append(&2, List<&2, Spec.Glob>, Seq.keep(True{}, s), kc)
          == List.append(&2, List<&2, Spec.Glob>, Seq.keep(True{}, s), _): List<&2, List<&2, Spec.Glob>>}
        {==}
    case Spec.Class{+n, +xs}:
      +hw =>
        +cc = List.contains(~Char, ~Char.is_eq, xs, c)
        +cf = List.contains(~Char, ~Char.is_eq, xs, f)
        %Char.ne_in_r(cs, '/', c, hs, hc) : {Seq.keep(Bool.and(Bool.not(_), Bool.xor(n, cc)), r)
          == Seq.keep(Bool.and(Spec.is_inner(f), Bool.xor(n, cf)), r): List<&2, List<&2, Spec.Glob>>}
        %Char.ne_in_r(cs, '/', f, hs, hf) : {Seq.keep(Bool.and(True{}, Bool.xor(n, cc)), r)
          == Seq.keep(Bool.and(Bool.not(_), Bool.xor(n, cf)), r): List<&2, List<&2, Spec.Glob>>}
        %Chars.contains_out(xs, cs, c, hc)(hw) : {Seq.keep(Bool.and(True{}, Bool.xor(n, _)), r)
          == Seq.keep(Bool.and(True{}, Bool.xor(n, cf)), r): List<&2, List<&2, Spec.Glob>>}
        %Chars.contains_out(xs, cs, f, hf)(hw) : {Seq.keep(Bool.and(True{}, Bool.xor(n, False{})), r)
          == Seq.keep(Bool.and(True{}, Bool.xor(n, _)), r): List<&2, List<&2, Spec.Glob>>}
        {==}
    case Spec.Deep{}:
      hw =>
        %ek : {Con{Con{Spec.Deep{}, r}, kc} == Con{Con{Spec.Deep{}, r}, _}: List<&2, List<&2, Spec.Glob>>}
        {==}
    case Spec.Cat{+a, +b}:
      +hw =>
        +wa = Glob.within(a, cs)
        +wb = Glob.within(b, cs)
        eb = Seq.step.head_rep(b, r, c, f, kc, kf, cs, hc, hf, hs, ek)(Bool.and_right(wa, wb)(hw))
        Seq.step.head_rep(
          a, Con{b, r}, c, f, Seq.step.head(b, r, c, kc), Seq.step.head(b, r, f, kf), cs, hc, hf, hs, eb
        )(Bool.and_left(wa, wb)(hw))
    case Spec.Alt{+a, +b}:
      +hw =>
        +wa = Glob.within(a, cs)
        +wb = Glob.within(b, cs)
        +ac = Seq.step.head(a, r, c, kc)
        +bc = Seq.step.head(b, r, c, kc)
        %Seq.step.head_rep(a, r, c, f, kc, kf, cs, hc, hf, hs, ek)(Bool.and_left(wa, wb)(hw)) :
          {List.append(&2, List<&2, Spec.Glob>, ac, bc)
            == List.append(&2, List<&2, Spec.Glob>, _, Seq.step.head(b, r, f, kf)): List<&2, List<&2, Spec.Glob>>}
        %Seq.step.head_rep(b, r, c, f, kc, kf, cs, hc, hf, hs, ek)(Bool.and_right(wa, wb)(hw)) :
          {List.append(&2, List<&2, Spec.Glob>, ac, bc)
            == List.append(&2, List<&2, Spec.Glob>, ac, _): List<&2, List<&2, Spec.Glob>>}
        {==}

# Seq.step moves s the same under c and f
def Seq.step_rep(
  s: List<&2, Spec.Glob>, +c: Char, +f: Char, +cs: List<&2, Char>,
  +hc: {Chars.has(cs, c) == False{}: Bool}, +hf: {Chars.has(cs, f) == False{}: Bool},
  +hs: {Chars.has(cs, '/') == True{}: Bool}
) -> {Seq.within(s, cs) == True{}: Bool} -> {Seq.step(s, c) == Seq.step(s, f): List<&2, List<&2, Spec.Glob>>}:
  match s:
    case Nil{}:
      hw => {==}
    case Con{+h, +t}:
      +hw =>
        +wh = Glob.within(h, cs)
        +wt = Seq.within(t, cs)
        et = Seq.step_rep(t, c, f, cs, hc, hf, hs)(Bool.and_right(wh, wt)(hw))
        Seq.step.head_rep(h, t, c, f, Seq.step(t, c), Seq.step(t, f), cs, hc, hf, hs, et)(Bool.and_left(wh, wt)(hw))

# Seqs.step moves xs the same under c and f
def Seqs.step_rep(
  xs: List<&2, List<&2, Spec.Glob>>, +c: Char, +f: Char, +cs: List<&2, Char>,
  +hc: {Chars.has(cs, c) == False{}: Bool}, +hf: {Chars.has(cs, f) == False{}: Bool},
  +hs: {Chars.has(cs, '/') == True{}: Bool}
) -> {Seqs.within(xs, cs) == True{}: Bool} ->
  {Seqs.step(xs, c) == Seqs.step(xs, f): List<&2, List<&2, Spec.Glob>>}:
  match xs:
    case Nil{}:
      hw => {==}
    case Con{+x, +r}:
      +hw =>
        +wx = Seq.within(x, cs)
        +wr = Seqs.within(r, cs)
        +sc = Seq.step(x, c)
        +rc = Seqs.step(r, c)
        %Seq.step_rep(x, c, f, cs, hc, hf, hs)(Bool.and_left(wx, wr)(hw)) :
          {Seqs.add_all(sc, rc) == Seqs.add_all(_, Seqs.step(r, f)): List<&2, List<&2, Spec.Glob>>}
        %Seqs.step_rep(r, c, f, cs, hc, hf, hs)(Bool.and_right(wx, wr)(hw)) :
          {Seqs.add_all(sc, rc) == Seqs.add_all(sc, _): List<&2, List<&2, Spec.Glob>>}
        {==}

# Slot.step moves slots the same under c and f
def Slot.step_rep(
  slots: List<&2, Slot>, +c: Char, +f: Char, +cs: List<&2, Char>,
  +hc: {Chars.has(cs, c) == False{}: Bool}, +hf: {Chars.has(cs, f) == False{}: Bool},
  +hs: {Chars.has(cs, '/') == True{}: Bool}
) -> {Slots.within(slots, cs) == True{}: Bool} -> {Slot.step(slots, c) == Slot.step(slots, f): List<&2, Slot>}:
  match slots:
    case Nil{}:
      hw => {==}
    case Con{Inc{+xs}, +t}:
      +hw =>
        +wx = Seqs.within(xs, cs)
        +wt = Slots.within(t, cs)
        +xc = Seqs.step(xs, c)
        +tc = Slot.step(t, c)
        %Seqs.step_rep(xs, c, f, cs, hc, hf, hs)(Bool.and_left(wx, wt)(hw)) :
          {Con{Inc{xc}, tc} == Con{Inc{_}, Slot.step(t, f)}: List<&2, Slot>}
        %Slot.step_rep(t, c, f, cs, hc, hf, hs)(Bool.and_right(wx, wt)(hw)) :
          {Con{Inc{xc}, tc} == Con{Inc{xc}, _}: List<&2, Slot>}
        {==}
    case Con{Exc{+xs}, +t}:
      +hw =>
        +wx = Seqs.within(xs, cs)
        +wt = Slots.within(t, cs)
        +xc = Seqs.step(xs, c)
        +tc = Slot.step(t, c)
        %Seqs.step_rep(xs, c, f, cs, hc, hf, hs)(Bool.and_left(wx, wt)(hw)) :
          {Con{Exc{xc}, tc} == Con{Exc{_}, Slot.step(t, f)}: List<&2, Slot>}
        %Slot.step_rep(t, c, f, cs, hc, hf, hs)(Bool.and_right(wx, wt)(hw)) :
          {Con{Exc{xc}, tc} == Con{Exc{xc}, _}: List<&2, Slot>}
        {==}

# St.step moves x the same under c and f
def St.step_rep(
  x: St, +c: Char, +f: Char, +cs: List<&2, Char>,
  +hc: {Chars.has(cs, c) == False{}: Bool}, +hf: {Chars.has(cs, f) == False{}: Bool},
  +hs: {Chars.has(cs, '/') == True{}: Bool}
) -> {St.within(x, cs) == True{}: Bool} -> {St.step(x, c) == St.step(x, f): St}:
  match x:
    case St{+both, +a, +b}:
      +hw =>
        +wa = Slots.within(a, cs)
        +wb = Slots.within(b, cs)
        +ac = Slot.step(a, c)
        +bc = Slot.step(b, c)
        %Slot.step_rep(a, c, f, cs, hc, hf, hs)(Bool.and_left(wa, wb)(hw)) :
          {St{both, ac, bc} == St{both, _, Slot.step(b, f)}: St}
        %Slot.step_rep(b, c, f, cs, hc, hf, hs)(Bool.and_right(wa, wb)(hw)) :
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
  %e : Bool.pick(Type, _, Unit, Empty)
  Unit{}

# b is False when not b is True
def Bool.not_true(b: Bool) -> {Bool.not(b) == True{}: Bool} -> {b == False{}: Bool}:
  match b:
    case False{}:
      h => {==}
    case True{}:
      h => Empty.absurd({True{} == False{}: Bool}, Bool.false_ne_true(h))

# the right side of a False disjunction is False
def Bool.or_false_r(a: Bool, -b: Bool) -> {Bool.or(a, b) == False{}: Bool} -> {b == False{}: Bool}:
  match a:
    case False{}:
      h => h
    case True{}:
      h => Empty.absurd({b == False{}: Bool}, Bool.true_ne_false(h))

# each step of x under a character of ds lands in xs
def St.closed(+x: St, ds: List<&2, Char>, +xs: List<&2, St>) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case Con{d, t}:
      Bool.and(St.has(xs, St.step(x, d)), St.closed(x, t, xs))

# x fails on "", names only characters of cs, and steps into xs
def St.ok(+x: St, +cs: List<&2, Char>, +f: Char, +xs: List<&2, St>) -> Bool:
  Bool.and(Bool.not(St.holds(x, SNil{})), Bool.and(St.within(x, cs), St.closed(x, Con{f, cs}, xs)))

# every state of ys is ok
def St.all_ok(ys: List<&2, St>, +cs: List<&2, Char>, +f: Char, +xs: List<&2, St>) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case Con{y, t}:
      Bool.and(St.ok(y, cs, f, xs), St.all_ok(t, cs, f, xs))

# (xs, cs, f) is a certificate
def Cert.check(+xs: List<&2, St>, +cs: List<&2, Char>, +f: Char) -> Bool:
  Bool.and(Chars.has(cs, '/'), Bool.and(Bool.not(Chars.has(cs, f)), St.all_ok(xs, cs, f, xs)))

# one step of St.all_ok_has, given b: St.is_eq(y, x)
def St.all_ok_has.at(
  +y: St, +t: List<&2, St>, +x: St, +cs: List<&2, Char>, +f: Char, +xs: List<&2, St>, b: Bool,
  ih: {St.all_ok(t, cs, f, xs) == True{}: Bool} -> {St.has(t, x) == True{}: Bool} ->
    {St.ok(x, cs, f, xs) == True{}: Bool},
  +ha: {Bool.and(St.ok(y, cs, f, xs), St.all_ok(t, cs, f, xs)) == True{}: Bool}
) -> {St.is_eq(y, x) == b: Bool} -> {Bool.or(b, St.has(t, x)) == True{}: Bool} ->
  {St.ok(x, cs, f, xs) == True{}: Bool}:
  match b:
    case False{}:
      e => hh => ih(Bool.and_right(St.ok(y, cs, f, xs), St.all_ok(t, cs, f, xs))(ha))(hh)
    case True{}:
      e => hh =>
        %St.is_eq_sound(y, x)(e) : {St.ok(_, cs, f, xs) == True{}: Bool}
        Bool.and_left(St.ok(y, cs, f, xs), St.all_ok(t, cs, f, xs))(ha)

# a state that ys holds is ok when all of ys are
def St.all_ok_has(ys: List<&2, St>, +x: St, +cs: List<&2, Char>, +f: Char, +xs: List<&2, St>) ->
  {St.all_ok(ys, cs, f, xs) == True{}: Bool} -> {St.has(ys, x) == True{}: Bool} ->
  {St.ok(x, cs, f, xs) == True{}: Bool}:
  match ys:
    case Nil{}:
      ha => hh => Empty.absurd({St.ok(x, cs, f, xs) == True{}: Bool}, Bool.false_ne_true(hh))
    case Con{+y, +t}:
      ha => St.all_ok_has.at(y, t, x, cs, f, xs, St.is_eq(y, x), St.all_ok_has(t, x, cs, f, xs), ha)({==})

# one step of St.closed_has, given b: Char.is_eq(d, c)
def St.closed_has.at(
  +x: St, +d: Char, +t: List<&2, Char>, +xs: List<&2, St>, +c: Char, b: Bool,
  ih: {St.closed(x, t, xs) == True{}: Bool} -> {Chars.has(t, c) == True{}: Bool} ->
    {St.has(xs, St.step(x, c)) == True{}: Bool},
  +hcl: {Bool.and(St.has(xs, St.step(x, d)), St.closed(x, t, xs)) == True{}: Bool}
) -> {Char.is_eq(d, c) == b: Bool} -> {Bool.or(b, Chars.has(t, c)) == True{}: Bool} ->
  {St.has(xs, St.step(x, c)) == True{}: Bool}:
  match b:
    case False{}:
      e => hh => ih(Bool.and_right(St.has(xs, St.step(x, d)), St.closed(x, t, xs))(hcl))(hh)
    case True{}:
      e => hh =>
        %Char.is_eq_sound(d, c)(e) : {St.has(xs, St.step(x, _)) == True{}: Bool}
        Bool.and_left(St.has(xs, St.step(x, d)), St.closed(x, t, xs))(hcl)

# x steps into xs under each character of ds when it is closed for ds
def St.closed_has(+x: St, ds: List<&2, Char>, +xs: List<&2, St>, +c: Char) ->
  {St.closed(x, ds, xs) == True{}: Bool} -> {Chars.has(ds, c) == True{}: Bool} ->
  {St.has(xs, St.step(x, c)) == True{}: Bool}:
  match ds:
    case Nil{}:
      hcl => hh => Empty.absurd({St.has(xs, St.step(x, c)) == True{}: Bool}, Bool.false_ne_true(hh))
    case Con{+d, +t}:
      hcl => St.closed_has.at(x, d, t, xs, c, Char.is_eq(d, c), St.closed_has(x, t, xs, c), hcl)({==})

# St.next_in, given b: Chars.has(Con{f, cs}, c)
def St.next_in.at(
  +x: St, +c: Char, +cs: List<&2, Char>, +f: Char, +xs: List<&2, St>, b: Bool,
  +hs: {Chars.has(cs, '/') == True{}: Bool}, +hf: {Chars.has(cs, f) == False{}: Bool},
  +hw: {St.within(x, cs) == True{}: Bool}, +hcl: {St.closed(x, Con{f, cs}, xs) == True{}: Bool}
) -> {Chars.has(Con{f, cs}, c) == b: Bool} -> {St.has(xs, St.step(x, c)) == True{}: Bool}:
  match b:
    case True{}:
      e => St.closed_has(x, Con{f, cs}, xs, c)(hcl)(e)
    case False{}:
      e =>
        hc = Bool.or_false_r(Char.is_eq(f, c), Chars.has(cs, c))(e)
        rep = St.step_rep(x, c, f, cs, hc, hf, hs)(hw)
        %Equal.sym(St, St.step(x, c), St.step(x, f), rep) : {St.has(xs, _) == True{}: Bool}
        Bool.and_left(St.has(xs, St.step(x, f)), St.closed(x, cs, xs))(hcl)

# an ok state of a certificate steps into it under any character
def St.next_in(
  +x: St, +c: Char, +cs: List<&2, Char>, +f: Char, +xs: List<&2, St>,
  +hs: {Chars.has(cs, '/') == True{}: Bool}, +hf: {Chars.has(cs, f) == False{}: Bool},
  +hok: {St.ok(x, cs, f, xs) == True{}: Bool}
) -> {St.has(xs, St.step(x, c)) == True{}: Bool}:
  +nh = Bool.not(St.holds(x, SNil{}))
  +wi = St.within(x, cs)
  +cl = St.closed(x, Con{f, cs}, xs)
  +rest = Bool.and_right(nh, Bool.and(wi, cl))(hok)
  hw = Bool.and_left(wi, cl)(rest)
  hcl = Bool.and_right(wi, cl)(rest)
  St.next_in.at(x, c, cs, f, xs, Chars.has(Con{f, cs}, c), hs, hf, hw, hcl)({==})

# a valid certificate names '/'
def Cert.slash(+cs: List<&2, Char>, +f: Char, +xs: List<&2, St>, hcert: {Cert.check(xs, cs, f) == True{}: Bool}) ->
  {Chars.has(cs, '/') == True{}: Bool}:
  Bool.and_left(Chars.has(cs, '/'), Bool.and(Bool.not(Chars.has(cs, f)), St.all_ok(xs, cs, f, xs)))(hcert)

# a valid certificate does not name f
def Cert.fresh(+cs: List<&2, Char>, +f: Char, +xs: List<&2, St>, hcert: {Cert.check(xs, cs, f) == True{}: Bool}) ->
  {Chars.has(cs, f) == False{}: Bool}:
  +nf = Bool.not(Chars.has(cs, f))
  +al = St.all_ok(xs, cs, f, xs)
  rest = Bool.and_right(Chars.has(cs, '/'), Bool.and(nf, al))(hcert)
  Bool.not_true(Chars.has(cs, f))(Bool.and_left(nf, al)(rest))

# every state of a valid certificate is ok
def Cert.ok_of(
  +x: St, +cs: List<&2, Char>, +f: Char, +xs: List<&2, St>,
  hcert: {Cert.check(xs, cs, f) == True{}: Bool}, hx: {St.has(xs, x) == True{}: Bool}
) -> {St.ok(x, cs, f, xs) == True{}: Bool}:
  +nf = Bool.not(Chars.has(cs, f))
  +al = St.all_ok(xs, cs, f, xs)
  rest = Bool.and_right(Chars.has(cs, '/'), Bool.and(nf, al))(hcert)
  St.all_ok_has(xs, x, cs, f, xs)(Bool.and_right(nf, al)(rest))(hx)

# no state of a certificate holds for any string
def Cert.sound(
  w: String, +x: St, +cs: List<&2, Char>, +f: Char, +xs: List<&2, St>,
  +hcert: {Cert.check(xs, cs, f) == True{}: Bool}, +hx: {St.has(xs, x) == True{}: Bool}
) -> {St.holds(x, w) == False{}: Bool}:
  match w:
    case SNil{}:
      +nh = Bool.not(St.holds(x, SNil{}))
      +rest = Bool.and(St.within(x, cs), St.closed(x, Con{f, cs}, xs))
      Bool.not_true(St.holds(x, SNil{}))(Bool.and_left(nh, rest)(Cert.ok_of(x, cs, f, xs, hcert, hx)))
    case SCon{+c, +t}:
      hs = Cert.slash(cs, f, xs, hcert)
      hf = Cert.fresh(cs, f, xs, hcert)
      hn = St.next_in(x, c, cs, f, xs, hs, hf, Cert.ok_of(x, cs, f, xs, hcert, hx))
      %St.step_ok(x, c, t) : {_ == False{}: Bool}
      Cert.sound(t, St.step(x, c), cs, f, xs, hcert, hn)

# Search
# ------
# The search needs no proof: `decide` checks what it returns. Phase one
# collects the states reachable from the start; when none holds on "", they
# are a certificate. Else phase two looks for a valid path that holds,
# guided by an automaton of valid paths.

# the characters that g names
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
def Search.fresh(+x: St, ds: List<&2, Char>, +seen: List<&2, St>, +acc: List<&2, St>) -> List<&2, St>:
  match ds:
    case Nil{}:
      acc
    case Con{d, t}:
      +y = St.step(x, d)
      Search.fresh(x, t, seen, Search.add_new(y, acc, Bool.or(St.has(seen, y), St.has(acc, y))))

# k(), or None when x holds on ""
def Search.close.if(hit: Bool, k: Unit -> Maybe<&2, List<&2, St>>) -> Maybe<&2, List<&2, St>>:
  match hit:
    case False{}:
      k(Unit{})
    case True{}:
      None{}

# every state reachable from todo, with seen; None when one holds on "" or
# fuel runs out
def Search.close(fuel: Nat, todo: List<&2, St>, +seen: List<&2, St>, +ds: List<&2, Char>) ->
  Maybe<&2, List<&2, St>>:
  match fuel todo:
    case 0n _:
      None{}
    case 1n+n Nil{}:
      Some{seen}
    case 1n+n Con{+x, t}:
      +new = Search.fresh(x, ds, seen, [])
      next = List.append(&2, St, t, new)
      Search.close.if(
        St.holds(x, SNil{}), u => Search.close(n, next, List.append(&2, St, new, seen), ds)
      )

# Where a valid path is: at a segment start, after "." or "..", inside a
# valid segment, or past a mistake.
type Path is Data:
  PStart{}
  PDot{}
  PDots{}
  PSeg{}
  PDead{}

# What a character is to a path: '/', '.', a banned character, or another.
type Role is Data:
  KSlash{}
  KDot{}
  KBad{}
  KOther{}

# what c is to a path
def Role.of(c: Char) -> Role:
  match c:
    case Chr{+x}:
      Bool.pick(Role, U32.is_eq(x, 47), KSlash{},
        Bool.pick(Role, U32.is_eq(x, 46), KDot{},
          Bool.pick(Role, Bool.or(U32.is_eq(x, 0), U32.is_eq(x, 92)), KBad{}, KOther{})))

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

# a number for each place, to compare them
def Path.code(s: Path) -> U32:
  match s:
    case PStart{}:
      0
    case PDot{}:
      1
    case PDots{}:
      2
    case PSeg{}:
      3
    case PDead{}:
      4

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
def Node.seen(ns: List<&2, Node>, +n: Node) -> Bool:
  match ns:
    case Nil{}:
      False{}
    case Con{Node{a, x, r}, t}:
      match n:
        case Node{+b, +y, s}:
          Bool.or(
            Bool.and(U32.is_eq(Path.code(a), Path.code(b)), St.is_eq(x, y)),
            Node.seen(t, Node{b, y, s})
          )

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
def Node.fresh(ds: List<&2, Char>, +n: Node, +seen: List<&2, Node>, +acc: List<&2, Node>) -> List<&2, Node>:
  match ds:
    case Nil{}:
      acc
    case Con{+d, t}:
      match n:
        case Node{+a, +x, +r}:
          +m = {Node{Path.step(a, Role.of(d)), St.step(x, d), SCon{d, r}}: Node}
          Node.fresh(t, Node{a, x, r}, seen, Node.add(Bool.or(Node.seen(seen, m), Node.seen(acc, m)), m, acc))

# the path of n when it is a valid path that holds, else k()
def Search.witness.if(hit: Bool, n: Node, k: Unit -> Maybe<&2, String>) -> Maybe<&2, String>:
  match hit n:
    case True{} Node{a, x, r}:
      Some{String.reverse(r)}
    case False{} _:
      k(Unit{})

# a valid path that some node reachable from todo holds for, or None
def Search.witness(fuel: Nat, todo: List<&2, Node>, +seen: List<&2, Node>, +ds: List<&2, Char>) ->
  Maybe<&2, String>:
  match fuel todo:
    case 0n _:
      None{}
    case 1n+n Nil{}:
      None{}
    case 1n+n Con{Node{+a, +x, +r}, t}:
      +m = {Node{a, x, r}: Node}
      +new = Node.fresh(ds, m, seen, [])
      next = List.append(&2, Node, t, new)
      hit = Bool.and(Path.is_end(a), St.holds(x, SNil{}))
      Search.witness.if(hit, m, u => Search.witness(n, next, List.append(&2, Node, new, seen), ds))

# What the search found: a path to check, a certificate to check, or neither.
type Outcome is Data:
  Witness{path: String}
  Proof{xs: List<&2, St>, cs: List<&2, Char>, f: Char}
  NoAnswer{}

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
  +x0: St, +cs: List<&2, Char>, +f: Char, closed: Maybe<&2, List<&2, St>>
) -> Outcome:
  match closed:
    case Some{xs}:
      Proof{xs, cs, f}
    case None{}:
      +ds = {Con{'x', Con{f, cs}}: List<&2, Char>}
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
def Search.decide(+q: Spec.Query, r: Outcome) -> Spec.Search:
  match r:
    case Witness{+p}:
      Search.found_if(p, Spec.Query.holds(q, p))
    case Proof{+xs, +cs, +f}:
      Search.absent_if(Bool.and(Cert.check(xs, cs, f), St.has(xs, St.of(q))))
    case NoAnswer{}:
      Spec.Unknown{}

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
def Search.ne_found(-s: Spec.Search, -p: String, n: Search.NotFound(s), e: {s == Spec.Found{p}: Spec.Search}) -> Empty:
  %e : Search.NotFound(_)
  n

# no s that is not Absent equals Absent
def Search.ne_absent(-s: Spec.Search, n: Search.NotAbsent(s), e: {s == Spec.Absent{}: Spec.Search}) -> Empty:
  %e : Search.NotAbsent(_)
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
def Search.found_if_found(+q: Spec.Query, +p0: String, +p: String, b: Bool) ->
  {Spec.Query.holds(q, p0) == b: Bool} -> {Search.found_if(p0, b) == Spec.Found{p}: Spec.Search} ->
  {Spec.Query.holds(q, p) == True{}: Bool}:
  match b:
    case False{}:
      e => h => Empty.absurd({Spec.Query.holds(q, p) == True{}: Bool}, Search.ne_found(Spec.Unknown{}, p, Unit{}, h))
    case True{}:
      e => h =>
        same = Equal.cong(Spec.Search, String, s => Search.path(s), Spec.Found{p0}, Spec.Found{p}, h)
        %same : {Spec.Query.holds(q, _) == True{}: Bool}
        e

# absent_if never answers Found
def Search.absent_if_found(b: Bool, -p: String) -> {Search.absent_if(b) == Spec.Found{p}: Spec.Search} -> Empty:
  match b:
    case False{}:
      h => Search.ne_found(Spec.Unknown{}, p, Unit{}, h)
    case True{}:
      h => Search.ne_found(Spec.Absent{}, p, Unit{}, h)

# found_if never answers Absent
def Search.found_if_absent(-p: String, b: Bool) -> {Search.found_if(p, b) == Spec.Absent{}: Spec.Search} -> Empty:
  match b:
    case False{}:
      h => Search.ne_absent(Spec.Unknown{}, Unit{}, h)
    case True{}:
      h => Search.ne_absent(Spec.Found{p}, Unit{}, h)

# a Found answer of decide names a path that holds
def Search.decide_found(+q: Spec.Query, r: Outcome, +p: String) ->
  {Search.decide(q, r) == Spec.Found{p}: Spec.Search} -> {Spec.Query.holds(q, p) == True{}: Bool}:
  match r:
    case Witness{+p0}:
      h => Search.found_if_found(q, p0, p, Spec.Query.holds(q, p0))({==}, h)
    case Proof{+xs, +cs, +f}:
      h => Empty.absurd({Spec.Query.holds(q, p) == True{}: Bool},
        Search.absent_if_found(Bool.and(Cert.check(xs, cs, f), St.has(xs, St.of(q))), p)(h))
    case NoAnswer{}:
      h => Empty.absurd({Spec.Query.holds(q, p) == True{}: Bool}, Search.ne_found(Spec.Unknown{}, p, Unit{}, h))

# absent_if answers Absent only for a valid certificate that holds the start
def Search.absent_if_absent(
  +q: Spec.Query, +xs: List<&2, St>, +cs: List<&2, Char>, +f: Char, +p: String, b: Bool
) -> {Bool.and(Cert.check(xs, cs, f), St.has(xs, St.of(q))) == b: Bool} ->
  {Search.absent_if(b) == Spec.Absent{}: Spec.Search} -> {Spec.Query.holds(q, p) == False{}: Bool}:
  match b:
    case False{}:
      e => h => Empty.absurd({Spec.Query.holds(q, p) == False{}: Bool}, Search.ne_absent(Spec.Unknown{}, Unit{}, h))
    case True{}:
      +e => h =>
        +ck = Cert.check(xs, cs, f)
        +hs = St.has(xs, St.of(q))
        none = Cert.sound(p, St.of(q), cs, f, xs, Bool.and_left(ck, hs)(e), Bool.and_right(ck, hs)(e))
        %St.of_ok(q, p) : {_ == False{}: Bool}
        %Equal.sym(Bool, St.holds(St.of(q), p), False{}, none) : {Bool.and(Spec.is_path(p), _) == False{}: Bool}
        Equal.sym(Bool, False{}, Bool.and(Spec.is_path(p), False{}), Bool.and_false(Spec.is_path(p)))

# an Absent answer of decide means no path holds
def Search.decide_absent(+q: Spec.Query, r: Outcome, +p: String) ->
  {Search.decide(q, r) == Spec.Absent{}: Spec.Search} -> {Spec.Query.holds(q, p) == False{}: Bool}:
  match r:
    case Witness{+p0}:
      h => Empty.absurd({Spec.Query.holds(q, p) == False{}: Bool},
        Search.found_if_absent(p0, Spec.Query.holds(q, p0))(h))
    case Proof{+xs, +cs, +f}:
      h => Search.absent_if_absent(q, xs, cs, f, p, Bool.and(Cert.check(xs, cs, f), St.has(xs, St.of(q))))({==}, h)
    case NoAnswer{}:
      h => Empty.absurd({Spec.Query.holds(q, p) == False{}: Bool}, Search.ne_absent(Spec.Unknown{}, Unit{}, h))

def Spec.search_found(q, p, h):
  +q = q
  Search.decide_found(q, Search.run(q), p)(h)

def Spec.search_absent(q, p, h):
  +q = q
  Search.decide_absent(q, Search.run(q), p)(h)
