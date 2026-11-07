import Base
import ./cmps.bend as Cmps

# Picks by an order
# -----------------
# A pick between the own value and another one, by an order cmp: the other
# wins when it is greater (cmp gives LT), else the own value stays. A join
# meets what a lookup found (m) with what another holder has (f).

# t when c is LT, else mine
def Order.by(-A: Data, c: Cmp, mine: A, t: A) -> A:
  match c:
    case LT{}:
      t
    case EQ{}:
      mine
    case GT{}:
      mine

# the winner between the value that m holds and t
def Order.pick(~A: Data, ~cmp: A -> A -> Cmp, m: Maybe<&2, A>, +t: A) -> A:
  match m:
    case None{}:
      t
    case Some{+x}:
      Order.by(A, cmp(x, t), x, t)

# what m holds after the value that f holds met it
def Order.join(~A: Data, ~cmp: A -> A -> Cmp, m: Maybe<&2, A>, f: Maybe<&2, A>) -> Maybe<&2, A>:
  match f:
    case None{}:
      m
    case Some{t}:
      Some{Order.pick(~A, ~cmp, m, t)}

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run

# Order.pick_idem, by the order c0 of the own value x and t
def Order.pick_idem.by(
  ~A: Data,
  ~cmp: A -> A -> Cmp,
  refl: @y: A -> {cmp(y, y) == EQ{}: Cmp},
  c0: Cmp,
  +x: A,
  +t: A
) -> {cmp(x, t) == c0: Cmp} -> {Order.pick(~A, ~cmp, Some{Order.by(A, c0, x, t)}, t) == Order.by(A, c0, x, t): A}:
  match c0:
    case LT{}:
      h =>
        %Equal.sym(Cmp, cmp(t, t), EQ{}, refl(t)): {Order.by(A, _, t, t) == t: A}
        {==}
    case EQ{}:
      h =>
        %Equal.sym(Cmp, cmp(x, t), EQ{}, h): {Order.by(A, _, x, t) == x: A}
        {==}
    case GT{}:
      h =>
        %Equal.sym(Cmp, cmp(x, t), GT{}, h): {Order.by(A, _, x, t) == x: A}
        {==}

# picking t again against the winner of a pick with t keeps that winner
def Order.pick_idem(
  ~A: Data,
  ~cmp: A -> A -> Cmp,
  refl: @y: A -> {cmp(y, y) == EQ{}: Cmp},
  m: Maybe<&2, A>,
  +t: A
) -> {Order.pick(~A, ~cmp, Some{Order.pick(~A, ~cmp, m, t)}, t) == Order.pick(~A, ~cmp, m, t): A}:
  match m:
    case None{}:
      %Equal.sym(Cmp, cmp(t, t), EQ{}, refl(t)): {Order.by(A, _, t, t) == t: A}
      {==}
    case Some{+x}:
      Order.pick_idem.by(~A, ~cmp, refl, cmp(x, t), x, t)({==})

# joining the same value twice is joining it once
def Order.join_idem(
  ~A: Data,
  ~cmp: A -> A -> Cmp,
  refl: @y: A -> {cmp(y, y) == EQ{}: Cmp},
  m: Maybe<&2, A>,
  f: Maybe<&2, A>
) -> {Order.join(~A, ~cmp, Order.join(~A, ~cmp, m, f), f) == Order.join(~A, ~cmp, m, f): Maybe<&2, A>}:
  match f:
    case None{}:
      {==}
    case Some{+t}:
      %Equal.sym(A, Order.pick(~A, ~cmp, Some{Order.pick(~A, ~cmp, m, t)}, t), Order.pick(~A, ~cmp, m, t), Order.pick_idem(~A, ~cmp, refl, m, t)):
        {Some{_} == Some{Order.pick(~A, ~cmp, m, t)}: Maybe<&2, A>}
      {==}

# Order.join_conv, when both hold a value: by the order c0 of the own value x
# and the other's t
def Order.join_conv.by(
  ~A: Data,
  ~B: Data,
  ~cmp: A -> A -> Cmp,
  ~key: A -> B,
  refl: @y: A -> {cmp(y, y) == EQ{}: Cmp},
  swap: @a: A -> @b: A -> {cmp(b, a) == Cmps.Cmp.flip(cmp(a, b)): Cmp},
  same: @a: A -> @b: A -> {cmp(a, b) == EQ{}: Cmp} -> {key(a) == key(b): B},
  c0: Cmp,
  +x: A,
  +t: A
) -> {cmp(x, t) == c0: Cmp} -> {key(Order.by(A, c0, x, t)) == key(Order.pick(~A, ~cmp, Some{t}, Order.by(A, c0, x, t))): B}:
  match c0:
    case LT{}:
      h =>
        %Equal.sym(Cmp, cmp(t, t), EQ{}, refl(t)): {key(t) == key(Order.by(A, _, t, t)): B}
        {==}
    case EQ{}:
      +h =>
        %Equal.sym(Cmp, cmp(t, x), Cmps.Cmp.flip(cmp(x, t)), swap(x)(t)): {key(x) == key(Order.by(A, _, t, x)): B}
        %Equal.sym(Cmp, cmp(x, t), EQ{}, h): {key(x) == key(Order.by(A, Cmps.Cmp.flip(_), t, x)): B}
        same(x)(t)(h)
    case GT{}:
      +h =>
        %Equal.sym(Cmp, cmp(t, x), Cmps.Cmp.flip(cmp(x, t)), swap(x)(t)): {key(x) == key(Order.by(A, _, t, x)): B}
        %Equal.sym(Cmp, cmp(x, t), GT{}, h): {key(x) == key(Order.by(A, Cmps.Cmp.flip(_), t, x)): B}
        {==}

# after a takes in b's value, and b takes in that, both hold values with the
# same key
def Order.join_conv(
  ~A: Data,
  ~B: Data,
  ~cmp: A -> A -> Cmp,
  ~key: A -> B,
  refl: @y: A -> {cmp(y, y) == EQ{}: Cmp},
  swap: @a: A -> @b: A -> {cmp(b, a) == Cmps.Cmp.flip(cmp(a, b)): Cmp},
  same: @a: A -> @b: A -> {cmp(a, b) == EQ{}: Cmp} -> {key(a) == key(b): B},
  ma: Maybe<&2, A>,
  mb: Maybe<&2, A>
) -> {Maybe.map(&2, A, B, y => key(y), Order.join(~A, ~cmp, ma, mb)) == Maybe.map(&2, A, B, y => key(y), Order.join(~A, ~cmp, mb, Order.join(~A, ~cmp, ma, mb))): Maybe<&2, B>}:
  match ma mb:
    case None{} None{}:
      {==}
    case Some{x} None{}:
      {==}
    case None{} Some{+t}:
      %Equal.sym(Cmp, cmp(t, t), EQ{}, refl(t)): {Some{key(t)} == Some{key(Order.by(A, _, t, t))}: Maybe<&2, B>}
      {==}
    case Some{+x} Some{+t}:
      %Order.join_conv.by(~A, ~B, ~cmp, ~key, refl, swap, same, cmp(x, t), x, t)({==}):
        {Some{key(Order.by(A, cmp(x, t), x, t))} == Some{_}: Maybe<&2, B>}
      {==}
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information
