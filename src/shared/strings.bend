import Base
import ./cmps.bend as Cmps
import ./shared.bend as Shared
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
          %Equal.sym(
            Cmp,
            U32.cmp(x, x),
            EQ{},
            Words.U32.cmp_refl(x)
          ): {String.order.go(t, t, _) == EQ{}: Cmp}
          String.order_refl(t)
# String.order.go from c is c, then the order from EQ
def String.order_then(
  c: Cmp,
  a: String,
  b: String
) -> {String.order.go(a, b, c) == Cmps.Cmp.then(c, String.order.go(a, b, EQ{})): Cmp}:
  match c a b:
    case EQ{} x y:
      {==}
    case LT{} SNil{} SNil{}:
      {==}
    case LT{} SNil{} SCon{y, t}:
      {==}
    case LT{} SCon{x, t} SNil{}:
      {==}
    case LT{} SCon{Chr{x}, t1} SCon{Chr{y}, t2}:
      {==}
    case GT{} SNil{} SNil{}:
      {==}
    case GT{} SNil{} SCon{y, t}:
      {==}
    case GT{} SCon{x, t} SNil{}:
      {==}
    case GT{} SCon{Chr{x}, t1} SCon{Chr{y}, t2}:
      {==}

# String.order.go ends at EQ only if it started at EQ
def String.order_keeps(
  +c: Cmp,
  +a: String,
  +b: String
) -> {String.order.go(a, b, c) == EQ{}: Cmp} -> {c == EQ{}: Cmp}:
  h => Cmps.Cmp.then_eq_left(
    c,
    String.order.go(a, b, EQ{})
  )(
    Equal.trans(
      Cmp,
      Cmps.Cmp.then(c, String.order.go(a, b, EQ{})),
      String.order.go(a, b, c),
      EQ{},
      Equal.sym(
        Cmp,
        String.order.go(a, b, c),
        Cmps.Cmp.then(c, String.order.go(a, b, EQ{})),
        String.order_then(c, a, b)
      ),
      h
    )
  )
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

# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# ks, with each key of ns that ks does not hold
def union(ns: List<&2, String>, +ks: List<&2, String>) -> List<&2, String>:
  match ns:
    case Nil{}:
      ks
    case Con{+n, r}:
      union(
        r,
        List.filter.put(String, n, ks, Bool.not(Shared.List.has(~String, ~String.eq, ks, n)))
      )
