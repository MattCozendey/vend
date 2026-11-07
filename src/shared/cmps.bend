import Base
import ./shared.bend as Shared

# Equality of strings
# -------------------
# Tables compare keys with String.eq, so their laws need it to be
# reflexive and sound.

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
  %e: Cmp.Ne(_)
  n
# Cmp.is_eq is True only for EQ
def Cmp.is_eq_sound(c: Cmp) -> {Cmp.is_eq(c) == True{}: Bool} -> {c == EQ{}: Cmp}:
  match c:
    case LT{}:
      h => Empty.absurd({LT{} == EQ{}: Cmp}, Shared.Bool.false_ne_true(h))
    case EQ{}:
      h => {==}
    case GT{}:
      h => Empty.absurd({GT{} == EQ{}: Cmp}, Shared.Bool.false_ne_true(h))
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

# the order the other way round
def Cmp.flip(c: Cmp) -> Cmp:
  match c:
    case LT{}:
      GT{}
    case EQ{}:
      EQ{}
    case GT{}:
      LT{}

# c, or rest when c is EQ: an order by a first key, then a second
def Cmp.then(c: Cmp, rest: Cmp) -> Cmp:
  match c:
    case EQ{}:
      rest
    case o:
      o

# "then" commutes with flipping both orders
def Cmp.then_flip(
  c: Cmp,
  r: Cmp
) -> {Cmp.then(Cmp.flip(c), Cmp.flip(r)) == Cmp.flip(Cmp.then(c, r)): Cmp}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

# a "then" that is EQ is EQ on both sides
def Cmp.then_eq_left(c: Cmp, r: Cmp) -> {Cmp.then(c, r) == EQ{}: Cmp} -> {c == EQ{}: Cmp}:
  match c:
    case LT{}:
      h => Empty.absurd({LT{} == EQ{}: Cmp}, Cmp.ne_eq(LT{}, Unit{}, h))
    case EQ{}:
      h => {==}
    case GT{}:
      h => Empty.absurd({GT{} == EQ{}: Cmp}, Cmp.ne_eq(GT{}, Unit{}, h))

def Cmp.then_eq_right(c: Cmp, r: Cmp) -> {Cmp.then(c, r) == EQ{}: Cmp} -> {r == EQ{}: Cmp}:
  match c:
    case LT{}:
      h => Empty.absurd({r == EQ{}: Cmp}, Cmp.ne_eq(LT{}, Unit{}, h))
    case EQ{}:
      h => h
    case GT{}:
      h => Empty.absurd({r == EQ{}: Cmp}, Cmp.ne_eq(GT{}, Unit{}, h))

# Bool.cmp the other way round is flipped
def Bool.cmp_swap(a: Bool, b: Bool) -> {Bool.cmp(b, a) == Cmp.flip(Bool.cmp(a, b)): Cmp}:
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

# Chains of comparisons
# ---------------------
# The comparisons ab, bc and ac of three values a, b and c fit one order when
# ac is what ab and bc force: an order is transitive when all its comparisons
# chain.

# ab, bc and ac fit one order
def Cmp.chain(ab: Cmp, bc: Cmp, ac: Cmp) -> Bool:
  match ab bc ac:
    case LT{} LT{} LT{}:
      True{}
    case LT{} LT{} EQ{}:
      False{}
    case LT{} LT{} GT{}:
      False{}
    case LT{} EQ{} LT{}:
      True{}
    case LT{} EQ{} EQ{}:
      False{}
    case LT{} EQ{} GT{}:
      False{}
    case LT{} GT{} LT{}:
      True{}
    case LT{} GT{} EQ{}:
      True{}
    case LT{} GT{} GT{}:
      True{}
    case EQ{} LT{} LT{}:
      True{}
    case EQ{} LT{} EQ{}:
      False{}
    case EQ{} LT{} GT{}:
      False{}
    case EQ{} EQ{} LT{}:
      False{}
    case EQ{} EQ{} EQ{}:
      True{}
    case EQ{} EQ{} GT{}:
      False{}
    case EQ{} GT{} LT{}:
      False{}
    case EQ{} GT{} EQ{}:
      False{}
    case EQ{} GT{} GT{}:
      True{}
    case GT{} LT{} LT{}:
      True{}
    case GT{} LT{} EQ{}:
      True{}
    case GT{} LT{} GT{}:
      True{}
    case GT{} EQ{} LT{}:
      False{}
    case GT{} EQ{} EQ{}:
      False{}
    case GT{} EQ{} GT{}:
      True{}
    case GT{} GT{} LT{}:
      False{}
    case GT{} GT{} EQ{}:
      False{}
    case GT{} GT{} GT{}:
      True{}

# LT, then anything, then LT fit one order
def Cmp.chain_lt(x: Cmp) -> {Cmp.chain(LT{}, x, LT{}) == True{}: Bool}:
  match x:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

# GT, then LT, then anything fit one order
def Cmp.chain_gl(x: Cmp) -> {Cmp.chain(GT{}, LT{}, x) == True{}: Bool}:
  match x:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

# anything, then GT, then GT fit one order
def Cmp.chain_gg(x: Cmp) -> {Cmp.chain(x, GT{}, GT{}) == True{}: Bool}:
  match x:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

# a chain read the other way round
def Cmp.chain_swap(
  ab: Cmp,
  bc: Cmp,
  ac: Cmp
) -> {Cmp.chain(bc, ab, ac) == Cmp.chain(ab, bc, ac): Bool}:
  match ab bc ac:
    case LT{} LT{} LT{}:
      {==}
    case LT{} LT{} EQ{}:
      {==}
    case LT{} LT{} GT{}:
      {==}
    case LT{} EQ{} LT{}:
      {==}
    case LT{} EQ{} EQ{}:
      {==}
    case LT{} EQ{} GT{}:
      {==}
    case LT{} GT{} LT{}:
      {==}
    case LT{} GT{} EQ{}:
      {==}
    case LT{} GT{} GT{}:
      {==}
    case EQ{} LT{} LT{}:
      {==}
    case EQ{} LT{} EQ{}:
      {==}
    case EQ{} LT{} GT{}:
      {==}
    case EQ{} EQ{} LT{}:
      {==}
    case EQ{} EQ{} EQ{}:
      {==}
    case EQ{} EQ{} GT{}:
      {==}
    case EQ{} GT{} LT{}:
      {==}
    case EQ{} GT{} EQ{}:
      {==}
    case EQ{} GT{} GT{}:
      {==}
    case GT{} LT{} LT{}:
      {==}
    case GT{} LT{} EQ{}:
      {==}
    case GT{} LT{} GT{}:
      {==}
    case GT{} EQ{} LT{}:
      {==}
    case GT{} EQ{} EQ{}:
      {==}
    case GT{} EQ{} GT{}:
      {==}
    case GT{} GT{} LT{}:
      {==}
    case GT{} GT{} EQ{}:
      {==}
    case GT{} GT{} GT{}:
      {==}

# an order by a first key, then a second, chains when both orders chain
def Cmp.then_chain(
  pa: Cmp,
  pb: Cmp,
  pc: Cmp,
  sa: Cmp,
  sb: Cmp,
  sc: Cmp
) -> {
  Cmp.chain(pa, pb, pc) == True{}: Bool
} -> {
  Cmp.chain(sa, sb, sc) == True{}: Bool
} -> {Cmp.chain(Cmp.then(pa, sa), Cmp.then(pb, sb), Cmp.then(pc, sc)) == True{}: Bool}:
  match pa pb pc:
    case LT{} LT{} LT{}:
      hp => hs => {==}
    case LT{} LT{} EQ{}:
      hp => hs => Empty.absurd(
        {Cmp.chain(Cmp.then(LT{}, sa), Cmp.then(LT{}, sb), Cmp.then(EQ{}, sc)) == True{}: Bool},
        Shared.Bool.false_ne_true(hp)
      )
    case LT{} LT{} GT{}:
      hp => hs => Empty.absurd(
        {Cmp.chain(Cmp.then(LT{}, sa), Cmp.then(LT{}, sb), Cmp.then(GT{}, sc)) == True{}: Bool},
        Shared.Bool.false_ne_true(hp)
      )
    case LT{} EQ{} LT{}:
      match sb:
        case LT{}:
          hp => hs => {==}
        case EQ{}:
          hp => hs => {==}
        case GT{}:
          hp => hs => {==}
    case LT{} EQ{} EQ{}:
      hp => hs => Empty.absurd(
        {Cmp.chain(Cmp.then(LT{}, sa), Cmp.then(EQ{}, sb), Cmp.then(EQ{}, sc)) == True{}: Bool},
        Shared.Bool.false_ne_true(hp)
      )
    case LT{} EQ{} GT{}:
      hp => hs => Empty.absurd(
        {Cmp.chain(Cmp.then(LT{}, sa), Cmp.then(EQ{}, sb), Cmp.then(GT{}, sc)) == True{}: Bool},
        Shared.Bool.false_ne_true(hp)
      )
    case LT{} GT{} LT{}:
      hp => hs => {==}
    case LT{} GT{} EQ{}:
      match sc:
        case LT{}:
          hp => hs => {==}
        case EQ{}:
          hp => hs => {==}
        case GT{}:
          hp => hs => {==}
    case LT{} GT{} GT{}:
      hp => hs => {==}
    case EQ{} LT{} LT{}:
      match sa:
        case LT{}:
          hp => hs => {==}
        case EQ{}:
          hp => hs => {==}
        case GT{}:
          hp => hs => {==}
    case EQ{} LT{} EQ{}:
      hp => hs => Empty.absurd(
        {Cmp.chain(Cmp.then(EQ{}, sa), Cmp.then(LT{}, sb), Cmp.then(EQ{}, sc)) == True{}: Bool},
        Shared.Bool.false_ne_true(hp)
      )
    case EQ{} LT{} GT{}:
      hp => hs => Empty.absurd(
        {Cmp.chain(Cmp.then(EQ{}, sa), Cmp.then(LT{}, sb), Cmp.then(GT{}, sc)) == True{}: Bool},
        Shared.Bool.false_ne_true(hp)
      )
    case EQ{} EQ{} LT{}:
      hp => hs => Empty.absurd(
        {Cmp.chain(Cmp.then(EQ{}, sa), Cmp.then(EQ{}, sb), Cmp.then(LT{}, sc)) == True{}: Bool},
        Shared.Bool.false_ne_true(hp)
      )
    case EQ{} EQ{} EQ{}:
      hp => hs => hs
    case EQ{} EQ{} GT{}:
      hp => hs => Empty.absurd(
        {Cmp.chain(Cmp.then(EQ{}, sa), Cmp.then(EQ{}, sb), Cmp.then(GT{}, sc)) == True{}: Bool},
        Shared.Bool.false_ne_true(hp)
      )
    case EQ{} GT{} LT{}:
      hp => hs => Empty.absurd(
        {Cmp.chain(Cmp.then(EQ{}, sa), Cmp.then(GT{}, sb), Cmp.then(LT{}, sc)) == True{}: Bool},
        Shared.Bool.false_ne_true(hp)
      )
    case EQ{} GT{} EQ{}:
      hp => hs => Empty.absurd(
        {Cmp.chain(Cmp.then(EQ{}, sa), Cmp.then(GT{}, sb), Cmp.then(EQ{}, sc)) == True{}: Bool},
        Shared.Bool.false_ne_true(hp)
      )
    case EQ{} GT{} GT{}:
      match sa:
        case LT{}:
          hp => hs => {==}
        case EQ{}:
          hp => hs => {==}
        case GT{}:
          hp => hs => {==}
    case GT{} LT{} LT{}:
      hp => hs => {==}
    case GT{} LT{} EQ{}:
      match sc:
        case LT{}:
          hp => hs => {==}
        case EQ{}:
          hp => hs => {==}
        case GT{}:
          hp => hs => {==}
    case GT{} LT{} GT{}:
      hp => hs => {==}
    case GT{} EQ{} LT{}:
      hp => hs => Empty.absurd(
        {Cmp.chain(Cmp.then(GT{}, sa), Cmp.then(EQ{}, sb), Cmp.then(LT{}, sc)) == True{}: Bool},
        Shared.Bool.false_ne_true(hp)
      )
    case GT{} EQ{} EQ{}:
      hp => hs => Empty.absurd(
        {Cmp.chain(Cmp.then(GT{}, sa), Cmp.then(EQ{}, sb), Cmp.then(EQ{}, sc)) == True{}: Bool},
        Shared.Bool.false_ne_true(hp)
      )
    case GT{} EQ{} GT{}:
      match sb:
        case LT{}:
          hp => hs => {==}
        case EQ{}:
          hp => hs => {==}
        case GT{}:
          hp => hs => {==}
    case GT{} GT{} LT{}:
      hp => hs => Empty.absurd(
        {Cmp.chain(Cmp.then(GT{}, sa), Cmp.then(GT{}, sb), Cmp.then(LT{}, sc)) == True{}: Bool},
        Shared.Bool.false_ne_true(hp)
      )
    case GT{} GT{} EQ{}:
      hp => hs => Empty.absurd(
        {Cmp.chain(Cmp.then(GT{}, sa), Cmp.then(GT{}, sb), Cmp.then(EQ{}, sc)) == True{}: Bool},
        Shared.Bool.false_ne_true(hp)
      )
    case GT{} GT{} GT{}:
      hp => hs => {==}

# Bool.cmp chains
def Bool.cmp_chain(
  a: Bool,
  b: Bool,
  c: Bool
) -> {Cmp.chain(Bool.cmp(a, b), Bool.cmp(b, c), Bool.cmp(a, c)) == True{}: Bool}:
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

# Orders of lists
# ---------------
# Two lists compare element by element by an order cmp; a list that ends first
# is the smaller.

# xs and ys by cmp
def List.order(~A: Data, ~cmp: A -> A -> Cmp, xs: List<&2, A>, ys: List<&2, A>) -> Cmp:
  match xs ys:
    case Nil{} Nil{}:
      EQ{}
    case Nil{} Con{y, t}:
      LT{}
    case Con{x, r} Nil{}:
      GT{}
    case Con{x, r} Con{y, t}:
      Cmp.then(cmp(x, y), List.order(~A, ~cmp, r, t))

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# a list is EQ to itself
def List.order_refl(
  ~A: Data,
  ~cmp: A -> A -> Cmp,
  ~refl: @a: A -> {cmp(a, a) == EQ{}: Cmp},
  xs: List<&2, A>
) -> {List.order(~A, ~cmp, xs, xs) == EQ{}: Cmp}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, r}:
      %Equal.sym(
        Cmp,
        cmp(x, x),
        EQ{},
        refl(x)
      ): {Cmp.then(_, List.order(~A, ~cmp, r, r)) == EQ{}: Cmp}
      List.order_refl(~A, ~cmp, ~refl, r)

# comparing lists the other way round flips the order
def List.order_swap(
  ~A: Data,
  ~cmp: A -> A -> Cmp,
  ~swap: @a: A -> @b: A -> {cmp(b, a) == Cmp.flip(cmp(a, b)): Cmp},
  xs: List<&2, A>,
  ys: List<&2, A>
) -> {List.order(~A, ~cmp, ys, xs) == Cmp.flip(List.order(~A, ~cmp, xs, ys)): Cmp}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, t}:
      {==}
    case Con{x, r} Nil{}:
      {==}
    case Con{+x, +r} Con{+y, +t}:
      %Equal.sym(
        Cmp,
        List.order(~A, ~cmp, t, r),
        Cmp.flip(List.order(~A, ~cmp, r, t)),
        List.order_swap(~A, ~cmp, ~swap, r, t)
      ): {Cmp.then(cmp(y, x), _) == Cmp.flip(Cmp.then(cmp(x, y), List.order(~A, ~cmp, r, t))): Cmp}
      %Equal.sym(
        Cmp,
        cmp(y, x),
        Cmp.flip(cmp(x, y)),
        swap(x)(y)
      ): {
        Cmp.then(
          _,
          Cmp.flip(List.order(~A, ~cmp, r, t))
        )
          == Cmp.flip(Cmp.then(cmp(x, y), List.order(~A, ~cmp, r, t))): Cmp
      }
      Cmp.then_flip(cmp(x, y), List.order(~A, ~cmp, r, t))

# lists that compare EQ are the same, for an order whose EQ means the same
def List.order_sound(
  ~A: Data,
  ~cmp: A -> A -> Cmp,
  ~sound: @a: A -> @b: A -> {cmp(a, b) == EQ{}: Cmp} -> {a == b: A},
  xs: List<&2, A>,
  ys: List<&2, A>
) -> {List.order(~A, ~cmp, xs, ys) == EQ{}: Cmp} -> {xs == ys: List<&2, A>}:
  match xs ys:
    case Nil{} Nil{}:
      h => {==}
    case Nil{} Con{y, t}:
      h => Empty.absurd({[] == y <> t: List<&2, A>}, Cmp.ne_eq(LT{}, Unit{}, h))
    case Con{x, r} Nil{}:
      h => Empty.absurd({x <> r == []: List<&2, A>}, Cmp.ne_eq(GT{}, Unit{}, h))
    case Con{+x, +r} Con{+y, +t}:
      +h =>
        %sound(
          x,
          y
        )(
          Cmp.then_eq_left(cmp(x, y), List.order(~A, ~cmp, r, t))(h)
        ): {x <> r == _ <> t: List<&2, A>}
        Equal.cong(
          List<&2, A>,
          List<&2, A>,
          z => x <> z,
          r,
          t,
          List.order_sound(
            ~A,
            ~cmp,
            ~sound,
            r,
            t
          )(Cmp.then_eq_right(cmp(x, y), List.order(~A, ~cmp, r, t))(h))
        )
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information
