import Base
import ./bools.bend as Bools
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

# the text t, unless it is empty
def String.nonempty(t: String) -> Maybe<&2, String>:
  match t:
    case SNil{}:
      None{}
    case SCon{c, r}:
      Some{SCon{c, r}}

# i then rest, unless i is the one dropped (hit)
def drop.put(i: String, rest: List<&2, String>, hit: Bool) -> List<&2, String>:
  match hit:
    case True{}:
      rest
    case False{}:
      i <> rest

# ks, with n unless ks holds it (held)
def drop.keep(n: String, ks: List<&2, String>, held: Bool) -> List<&2, String>:
  match held:
    case True{}:
      ks
    case False{}:
      n <> ks

# ks holds k
def has(ks: List<&2, String>, +k: String) -> Bool:
  match ks:
    case Nil{}:
      False{}
    case Con{i, r}:
      List.any.if(u => has(r, k), String.eq(i, k))

# ks, without k
def drop(ks: List<&2, String>, +k: String) -> List<&2, String>:
  match ks:
    case Nil{}:
      Nil{}
    case Con{+i, r}:
      drop.put(i, drop(r, k), String.eq(i, k))

# ks, with each key of ns that ks does not hold
def union(ns: List<&2, String>, +ks: List<&2, String>) -> List<&2, String>:
  match ns:
    case Nil{}:
      ks
    case Con{+n, r}:
      union(r, drop.keep(n, ks, has(ks, n)))

# an "any" with a true rest is true
def keep_has.any(c: Bool) -> {List.any.if(u => True{}, c) == True{}: Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

# a key of ks is in ks after keep adds n or not (held)
def keep_has(+n: String, ks: List<&2, String>, held: Bool, +k: String) -> {has(ks, k) == True{}: Bool} -> {has(drop.keep(n, ks, held), k) == True{}: Bool}:
  match held:
    case True{}:
      h => h
    case False{}:
      h =>
        %Equal.sym(Bool, has(ks, k), True{}, h): {List.any.if(u => _, String.eq(n, k)) == True{}: Bool}
        keep_has.any(String.eq(n, k))

# a key of ks is in the union of ns and ks
def union_right(ns: List<&2, String>, +ks: List<&2, String>, +k: String) -> {has(ks, k) == True{}: Bool} -> {has(union(ns, ks), k) == True{}: Bool}:
  match ns:
    case Nil{}:
      h => h
    case Con{+n, r}:
      h => union_right(r, drop.keep(n, ks, has(ks, n)), k)(keep_has(n, ks, has(ks, n), k)(h))

# n is in ks after keep adds it, when ks holds n (held) or not
def keep_self(+n: String, +ks: List<&2, String>, held: Bool) -> {has(ks, n) == held: Bool} -> {has(drop.keep(n, ks, held), n) == True{}: Bool}:
  match held:
    case True{}:
      h => h
    case False{}:
      h =>
        %Equal.sym(Bool, String.eq(n, n), True{}, String.eq_refl(n)): {List.any.if(u => has(ks, n), _) == True{}: Bool}
        {==}

# union_left at the first key n of ns, by whether n is k (hit)
def union_left.at(
  +n: String,
  r: List<&2, String>,
  +ks: List<&2, String>,
  +k: String,
  hit: Bool,
  ih: @js: List<&2, String> -> {has(r, k) == True{}: Bool} -> {has(union(r, js), k) == True{}: Bool}
) -> {String.eq(n, k) == hit: Bool} -> {List.any.if(u => has(r, k), hit) == True{}: Bool} -> {has(union(r, drop.keep(n, ks, has(ks, n))), k) == True{}: Bool}:
  match hit:
    case False{}:
      e => h => ih(drop.keep(n, ks, has(ks, n)))(h)
    case True{}:
      +e => h =>
        %String.eq_sound(n, k)(e): {has(union(r, drop.keep(n, ks, has(ks, n))), _) == True{}: Bool}
        union_right(r, drop.keep(n, ks, has(ks, n)), n)(keep_self(n, ks, has(ks, n))({==}))

# a key of ns is in the union of ns and ks
def union_left(ns: List<&2, String>, +ks: List<&2, String>, +k: String) -> {has(ns, k) == True{}: Bool} -> {has(union(ns, ks), k) == True{}: Bool}:
  match ns:
    case Nil{}:
      h => Empty.absurd({has(union(Nil{}, ks), k) == True{}: Bool}, Bools.Bool.false_ne_true(h))
    case Con{+n, +r}:
      +h => union_left.at(n, r, ks, k, String.eq(n, k), js => union_left(r, js, k))({==})(
        %Equal.sym(Bool, has(n <> r, k), True{}, h): {_ == True{}: Bool}
        {==}
      )
