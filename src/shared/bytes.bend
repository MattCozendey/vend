import Base
import ./shared.bend as Shared
import ./words.bend as Words

# a resource's content: one byte per U32, as Base's File effects use
def Bytes() -> Data:
  List<&2, U32>
# x is a byte: below 256
def is_byte(x: U32) -> Bool:
  (x < 256: U32)
# every value of b is a byte
def is_bytes(b: Bytes()) -> Bool:
  List.all(~&2, ~U32, ~is_byte, b)
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
      match x:
        case U32{w}:
          %Equal.sym(
            Cmp,
            Word.cmp(32n, w, w),
            EQ{},
            Words.Word.cmp_refl(32n, w)
          ): {List.all.if(u => Bytes.is_eq(t, t), Cmp.is_eq(_)) == True{}: Bool}
          Bytes.is_eq_refl(t)
