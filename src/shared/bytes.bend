import Base
import ./shared.bend as Shared
import ./words.bend as Words

# a resource's content: one byte per U32, as Base's File effects use
def Bytes() -> Data:
  List<&2, U32>
# the codes of the characters of s, one per byte: for ASCII text
def Bytes.of_text(s: String) -> Bytes():
  match s:
    case SNil{}:
      []
    case SCon{Chr{c}, r}:
      c <> Bytes.of_text(r)

# a and b are the same bytes
def Bytes.is_eq(a: Bytes(), b: Bytes()) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Con{x, at} Con{y, bt}:
      List.all.if(u => Bytes.is_eq(at, bt), U32.is_eq(x, y))
    case _ _:
      False{}

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run

# Bytes.is_eq is True only for equal bytes
def Bytes.is_eq_sound(
  a: Bytes(),
  b: Bytes()
) -> {Bytes.is_eq(a, b) == True{}: Bool} -> {a == b: Bytes()}:
  match a b:
    case Nil{} Nil{}:
      h => {==}
    case Nil{} Con{y, ys}:
      h => Empty.absurd({Nil{} == y <> ys: Bytes()}, Shared.Bool.false_ne_true(h))
    case Con{x, xs} Nil{}:
      h => Empty.absurd({x <> xs == Nil{}: Bytes()}, Shared.Bool.false_ne_true(h))
    case Con{+x, +xs} Con{+y, +ys}:
      +h =>
        %Words.U32.is_eq_sound(
          x,
          y
        )(
          Shared.List.all.if_hit(U32.is_eq(x, y), u => Bytes.is_eq(xs, ys))(h)
        ): {x <> xs == _ <> ys: Bytes()}
        %Bytes.is_eq_sound(
          xs,
          ys
        )(
          Shared.List.all.if_rest(U32.is_eq(x, y), u => Bytes.is_eq(xs, ys))(h)
        ): {x <> xs == x <> _: Bytes()}
        {==}
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# bytes are equal to themselves
def Bytes.is_eq_refl(a: Bytes()) -> {Bytes.is_eq(a, a) == True{}: Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{x, t}:
      %Equal.sym(
        Bool,
        U32.is_eq(x, x),
        True{},
        Words.U32.is_eq_refl(x)
      ): {List.all.if(u => Bytes.is_eq(t, t), _) == True{}: Bool}
      Bytes.is_eq_refl(t)
