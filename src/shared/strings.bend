import Base
import ./cmps.bend as Cmps
import ./words.bend as Words

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# String.order.go of a string with itself, from EQ, is EQ
def String.order_refl(a: String) -> {String.order.go(a, a, EQ{}) == EQ{}: Cmp}:
  match a:
    case SNil{}:
      {==}
    case SCon{c, t}:
      match c:
        case Chr{x}:
          match x:
            case U32{w}:
              %Equal.sym(Cmp, Word.cmp(32n, w, w), EQ{}, Words.Word.cmp_refl(32n, w)):
                {String.order.go(t, t, _) == EQ{}: Cmp}
              String.order_refl(t)
# String.order.go ends at EQ only if it started at EQ
def String.order_keeps(
  c: Cmp,
  a: String,
  b: String
) -> {String.order.go(a, b, c) == EQ{}: Cmp} -> {c == EQ{}: Cmp}:
  match c:
    case EQ{}:
      h => {==}
    case LT{}:
      match a b:
        case SNil{} SNil{}:
          h => Empty.absurd({LT{} == EQ{}: Cmp}, Cmps.Cmp.ne_eq(LT{}, Unit{}, h))
        case SNil{} SCon{y, t2}:
          h => Empty.absurd({LT{} == EQ{}: Cmp}, Cmps.Cmp.ne_eq(LT{}, Unit{}, h))
        case SCon{x, t1} SNil{}:
          h => Empty.absurd({LT{} == EQ{}: Cmp}, Cmps.Cmp.ne_eq(LT{}, Unit{}, h))
        case SCon{Chr{x}, t1} SCon{Chr{y}, t2}:
          h => Empty.absurd({LT{} == EQ{}: Cmp}, Cmps.Cmp.ne_eq(LT{}, Unit{}, h))
    case GT{}:
      match a b:
        case SNil{} SNil{}:
          h => Empty.absurd({GT{} == EQ{}: Cmp}, Cmps.Cmp.ne_eq(GT{}, Unit{}, h))
        case SNil{} SCon{y, t2}:
          h => Empty.absurd({GT{} == EQ{}: Cmp}, Cmps.Cmp.ne_eq(GT{}, Unit{}, h))
        case SCon{x, t1} SNil{}:
          h => Empty.absurd({GT{} == EQ{}: Cmp}, Cmps.Cmp.ne_eq(GT{}, Unit{}, h))
        case SCon{Chr{x}, t1} SCon{Chr{y}, t2}:
          h => Empty.absurd({GT{} == EQ{}: Cmp}, Cmps.Cmp.ne_eq(GT{}, Unit{}, h))
# String.order.go from c is String.order.go from EQ, when c is EQ
def String.order_at(
  -c: Cmp,
  -t1: String,
  -t2: String,
  e: {c == EQ{}: Cmp}
) -> {String.order.go(t1, t2, c) == EQ{}: Cmp} -> {String.order.go(t1, t2, EQ{}) == EQ{}: Cmp}:
  %e: {String.order.go(t1, t2, c) == EQ{}: Cmp} -> {String.order.go(t1, t2, _) == EQ{}: Cmp}
  h => h
# String.order.go from EQ ends at EQ only for equal strings
def String.order_sound(
  a: String,
  b: String
) -> {String.order.go(a, b, EQ{}) == EQ{}: Cmp} -> {a == b: String}:
  match a b:
    case SNil{} SNil{}:
      _ => {==}
    case SNil{} SCon{y, t2}:
      h => Empty.absurd({SNil{} == SCon{y, t2}: String}, Cmps.Cmp.ne_eq(LT{}, Unit{}, h))
    case SCon{x, t1} SNil{}:
      h => Empty.absurd({SCon{x, t1} == SNil{}: String}, Cmps.Cmp.ne_eq(GT{}, Unit{}, h))
    case SCon{Chr{U32{+w1}}, +t1} SCon{Chr{U32{+w2}}, +t2}:
      +h =>
        +e = String.order_keeps(Word.cmp(32n, w1, w2), t1, t2)(h)
        h2 = String.order_at(Word.cmp(32n, w1, w2), t1, t2, e)(h)
        %Words.Word.cmp_eq(
          32n,
          w1,
          w2
        )(e): {SCon{Chr{U32{w1}}, t1} == SCon{Chr{U32{_}}, t2}: String}
        %String.order_sound(t1, t2)(h2): {SCon{Chr{U32{w1}}, t1} == SCon{Chr{U32{w1}}, _}: String}
        {==}
# every string equals itself
def String.eq_refl(a: String) -> {String.eq(a, a) == True{}: Bool}:
  %Equal.sym(
    Cmp,
    String.order.go(a, a, EQ{}),
    EQ{},
    String.order_refl(a)
  ): {Cmp.is_eq(_) == True{}: Bool}
  {==}
# String.eq is True only for equal strings
def String.eq_sound(
  +a: String,
  +b: String
) -> {String.eq(a, b) == True{}: Bool} -> {a == b: String}:
  h => String.order_sound(a, b)(Cmps.Cmp.is_eq_sound(String.order.go(a, b, EQ{}))(h))
# String.eq answers False the same way round, with c the answer of
# String.eq(b, a)
def String.eq_flip.at(
  +a: String,
  b: String,
  c: Bool
) -> {String.eq(b, a) == c: Bool} -> {String.eq(a, b) == False{}: Bool} -> {c == False{}: Bool}:
  match c:
    case False{}:
      _ => _ => {==}
    case True{}:
      e => d =>
        ab = Equal.sym(String, b, a, String.eq_sound(b, a)(e))
        same = Equal.cong(String, Bool, z => String.eq(a, z), a, b, ab)
        aa = Equal.sym(Bool, String.eq(a, a), True{}, String.eq_refl(a))
        Equal.trans(
          Bool,
          True{},
          String.eq(a, b),
          False{},
          Equal.trans(Bool, True{}, String.eq(a, a), String.eq(a, b), aa, same),
          d
        )
# String.eq is False the other way round too
def String.eq_flip(
  +a: String,
  +b: String
) -> {String.eq(a, b) == False{}: Bool} -> {String.eq(b, a) == False{}: Bool}:
  String.eq_flip.at(a, b, String.eq(b, a), {==})
# String.order.go the other way round, from the flipped start, is flipped
def String.order_swap(
  a: String,
  b: String,
  c: Cmp
) -> {String.order.go(b, a, Cmps.Cmp.flip(c)) == Cmps.Cmp.flip(String.order.go(a, b, c)): Cmp}:
  match a b c:
    case SNil{} SNil{} LT{}:
      {==}
    case SNil{} SNil{} EQ{}:
      {==}
    case SNil{} SNil{} GT{}:
      {==}
    case SNil{} SCon{Chr{x}, t} LT{}:
      {==}
    case SNil{} SCon{Chr{x}, t} EQ{}:
      {==}
    case SNil{} SCon{Chr{x}, t} GT{}:
      {==}
    case SCon{Chr{x}, t} SNil{} LT{}:
      {==}
    case SCon{Chr{x}, t} SNil{} EQ{}:
      {==}
    case SCon{Chr{x}, t} SNil{} GT{}:
      {==}
    case SCon{Chr{x}, t1} SCon{Chr{y}, t2} LT{}:
      {==}
    case SCon{Chr{x}, t1} SCon{Chr{y}, t2} GT{}:
      {==}
    case SCon{Chr{+x}, +t1} SCon{Chr{+y}, +t2} EQ{}:
      %Equal.sym(Cmp, U32.cmp(y, x), Cmps.Cmp.flip(U32.cmp(x, y)), Words.U32.cmp_swap(x, y)):
        {String.order.go(t2, t1, _) == Cmps.Cmp.flip(String.order.go(t1, t2, U32.cmp(x, y))): Cmp}
      String.order_swap(t1, t2, U32.cmp(x, y))

# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information
