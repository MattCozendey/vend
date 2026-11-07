import Base
import ./cmps.bend as Cmps
import ./shared.bend as Shared
import ./strings.bend as Strings

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

# the value under c after the key k met m, when k is c (hit); f holds k's value
def Order.step(
  ~A: Data,
  ~cmp: A -> A -> Cmp,
  hit: Bool,
  f: Maybe<&2, A>,
  m: Maybe<&2, A>
) -> Maybe<&2, A>:
  match hit:
    case False{}:
      m
    case True{}:
      Order.join(~A, ~cmp, m, f)

# the value under c after each key of ks met m; at gives each key's value in t
def Order.fold(
  ~A: Data,
  ~V: Data,
  ~cmp: A -> A -> Cmp,
  ~at: V -> String -> Maybe<&2, A>,
  ks: List<&2, String>,
  +t: V,
  +c: String,
  m: Maybe<&2, A>
) -> Maybe<&2, A>:
  match ks:
    case Nil{}:
      m
    case Con{+k, r}:
      Order.fold(~A, ~V, ~cmp, ~at, r, t, c, Order.step(~A, ~cmp, String.eq(k, c), at(t)(k), m))

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Order.pick_idem, by the order c0 of the own value x and t
def Order.pick_idem.by(
  ~A: Data,
  ~cmp: A -> A -> Cmp,
  refl: @y: A -> {cmp(y, y) == EQ{}: Cmp},
  c0: Cmp,
  x: A,
  t: A
) -> {
  cmp(x, t) == c0: Cmp
} -> {Order.pick(~A, ~cmp, Some{Order.by(A, c0, x, t)}, t) == Order.by(A, c0, x, t): A}:
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
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

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

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# joining the same value twice is joining it once
def Order.join_idem(
  ~A: Data,
  ~cmp: A -> A -> Cmp,
  refl: @y: A -> {cmp(y, y) == EQ{}: Cmp},
  m: Maybe<&2, A>,
  f: Maybe<&2, A>
) -> {
  Order.join(~A, ~cmp, Order.join(~A, ~cmp, m, f), f) == Order.join(~A, ~cmp, m, f): Maybe<&2, A>
}:
  match f:
    case None{}:
      {==}
    case Some{t}:
      %Equal.sym(
        A,
        Order.pick(~A, ~cmp, Some{Order.pick(~A, ~cmp, m, t)}, t),
        Order.pick(~A, ~cmp, m, t),
        Order.pick_idem(~A, ~cmp, refl, m, t)
      ):
        {Some{_} == Some{Order.pick(~A, ~cmp, m, t)}: Maybe<&2, A>}
      {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

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
) -> {
  cmp(x, t) == c0: Cmp
} -> {key(Order.by(A, c0, x, t)) == key(Order.pick(~A, ~cmp, Some{t}, Order.by(A, c0, x, t))): B}:
  match c0:
    case LT{}:
      h =>
        %Equal.sym(Cmp, cmp(t, t), EQ{}, refl(t)): {key(t) == key(Order.by(A, _, t, t)): B}
        {==}
    case EQ{}:
      +h =>
        %Equal.sym(
          Cmp,
          cmp(t, x),
          Cmps.Cmp.flip(cmp(x, t)),
          swap(x)(t)
        ): {key(x) == key(Order.by(A, _, t, x)): B}
        %Equal.sym(Cmp, cmp(x, t), EQ{}, h): {key(x) == key(Order.by(A, Cmps.Cmp.flip(_), t, x)): B}
        same(x)(t)(h)
    case GT{}:
      +h =>
        %Equal.sym(
          Cmp,
          cmp(t, x),
          Cmps.Cmp.flip(cmp(x, t)),
          swap(x)(t)
        ): {key(x) == key(Order.by(A, _, t, x)): B}
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
) -> {
  Maybe.map(
    &2,
    A,
    B,
    y => key(y),
    Order.join(~A, ~cmp, ma, mb)
  )
    == Maybe.map(
      &2,
      A,
      B,
      y => key(y),
      Order.join(~A, ~cmp, mb, Order.join(~A, ~cmp, ma, mb))
    ): Maybe<&2, B>
}:
  match ma mb:
    case None{} None{}:
      {==}
    case Some{x} None{}:
      {==}
    case None{} Some{t}:
      %Equal.sym(
        Cmp,
        cmp(t, t),
        EQ{},
        refl(t)
      ): {Some{key(t)} == Some{key(Order.by(A, _, t, t))}: Maybe<&2, B>}
      {==}
    case Some{+x} Some{+t}:
      %Order.join_conv.by(~A, ~B, ~cmp, ~key, refl, swap, same, cmp(x, t), x, t)({==}):
        {Some{key(Order.by(A, cmp(x, t), x, t))} == Some{_}: Maybe<&2, B>}
      {==}
# a step with no value found changes nothing
def Order.step_none(
  ~A: Data,
  ~cmp: A -> A -> Cmp,
  hit: Bool,
  m: Maybe<&2, A>
) -> {Order.step(~A, ~cmp, hit, None{}, m) == m: Maybe<&2, A>}:
  match hit:
    case False{}:
      {==}
    case True{}:
      {==}

# Order.fold_none at the first key k, by whether k is c (hit)
def Order.fold_none.at(
  ~A: Data,
  ~V: Data,
  ~cmp: A -> A -> Cmp,
  ~at: V -> String -> Maybe<&2, A>,
  hit: Bool,
  k: String,
  r: List<&2, String>,
  t: V,
  c: String,
  m: Maybe<&2, A>,
  ih: {
    Shared.List.has(~String, ~String.eq, r, c) == False{}: Bool
  } -> {Order.fold(~A, ~V, ~cmp, ~at, r, t, c, m) == m: Maybe<&2, A>}
) -> {
  String.eq(k, c) == hit: Bool
} -> {
  List.any.if(u => Shared.List.has(~String, ~String.eq, r, c), hit) == False{}: Bool
} -> {
  Order.fold(~A, ~V, ~cmp, ~at, r, t, c, Order.step(~A, ~cmp, hit, at(t)(k), m)) == m: Maybe<&2, A>
}:
  match hit:
    case False{}:
      he => hn => ih(hn)
    case True{}:
      he => hn => Empty.absurd(
        {
          Order.fold(
            ~A,
            ~V,
            ~cmp,
            ~at,
            r,
            t,
            c,
            Order.step(~A, ~cmp, True{}, at(t)(k), m)
          )
            == m: Maybe<&2, A>
        },
        Shared.Bool.false_ne_true(Equal.sym(Bool, True{}, False{}, hn))
      )

# a fold over keys without c changes nothing
def Order.fold_none(
  ~A: Data,
  ~V: Data,
  ~cmp: A -> A -> Cmp,
  ~at: V -> String -> Maybe<&2, A>,
  ks: List<&2, String>,
  +t: V,
  +c: String,
  +m: Maybe<&2, A>
) -> {
  Shared.List.has(~String, ~String.eq, ks, c) == False{}: Bool
} -> {Order.fold(~A, ~V, ~cmp, ~at, ks, t, c, m) == m: Maybe<&2, A>}:
  match ks:
    case Nil{}:
      h => {==}
    case Con{+k, +r}:
      Order.fold_none.at(
        ~A,
        ~V,
        ~cmp,
        ~at,
        String.eq(k, c),
        k,
        r,
        t,
        c,
        m,
        Order.fold_none(~A, ~V, ~cmp, ~at, r, t, c, m)
      )({==})

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Order.fold_idem at the first key k, by whether k is c (hit)
def Order.fold_idem.at(
  ~A: Data,
  ~V: Data,
  ~cmp: A -> A -> Cmp,
  ~at: V -> String -> Maybe<&2, A>,
  hit: Bool,
  k: String,
  r: List<&2, String>,
  t: V,
  c: String,
  m: Maybe<&2, A>,
  idem: {
    Order.join(
      ~A,
      ~cmp,
      Order.join(~A, ~cmp, m, at(t)(c)),
      at(t)(c)
    )
      == Order.join(~A, ~cmp, m, at(t)(c)): Maybe<&2, A>
  },
  ih: {
    Order.fold(
      ~A,
      ~V,
      ~cmp,
      ~at,
      r,
      t,
      c,
      Order.join(~A, ~cmp, m, at(t)(c))
    )
      == Order.join(~A, ~cmp, m, at(t)(c)): Maybe<&2, A>
  }
) -> {
  String.eq(k, c) == hit: Bool
} -> {
  Order.fold(
    ~A,
    ~V,
    ~cmp,
    ~at,
    r,
    t,
    c,
    Order.step(~A, ~cmp, hit, at(t)(k), Order.join(~A, ~cmp, m, at(t)(c)))
  )
    == Order.join(~A, ~cmp, m, at(t)(c)): Maybe<&2, A>
}:
  match hit:
    case False{}:
      he => ih
    case True{}:
      he =>
        %Equal.sym(
          String,
          k,
          c,
          Strings.String.eq_sound(k, c)(he)
        ): {
          Order.fold(
            ~A,
            ~V,
            ~cmp,
            ~at,
            r,
            t,
            c,
            Order.join(~A, ~cmp, Order.join(~A, ~cmp, m, at(t)(c)), at(t)(_))
          )
            == Order.join(~A, ~cmp, m, at(t)(c)): Maybe<&2, A>
        }
        %Equal.sym(
          Maybe<&2, A>,
          Order.join(~A, ~cmp, Order.join(~A, ~cmp, m, at(t)(c)), at(t)(c)),
          Order.join(~A, ~cmp, m, at(t)(c)),
          idem
        ): {
          Order.fold(
            ~A,
            ~V,
            ~cmp,
            ~at,
            r,
            t,
            c,
            _
          )
            == Order.join(~A, ~cmp, m, at(t)(c)): Maybe<&2, A>
        }
        ih
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# once joined, a fold keeps the join
def Order.fold_idem(
  ~A: Data,
  ~V: Data,
  ~cmp: A -> A -> Cmp,
  ~at: V -> String -> Maybe<&2, A>,
  ks: List<&2, String>,
  +t: V,
  +c: String,
  +m: Maybe<&2, A>,
  +idem: {
    Order.join(
      ~A,
      ~cmp,
      Order.join(~A, ~cmp, m, at(t)(c)),
      at(t)(c)
    )
      == Order.join(~A, ~cmp, m, at(t)(c)): Maybe<&2, A>
  }
) -> {
  Order.fold(
    ~A,
    ~V,
    ~cmp,
    ~at,
    ks,
    t,
    c,
    Order.join(~A, ~cmp, m, at(t)(c))
  )
    == Order.join(~A, ~cmp, m, at(t)(c)): Maybe<&2, A>
}:
  match ks:
    case Nil{}:
      {==}
    case Con{+k, +r}:
      Order.fold_idem.at(
        ~A,
        ~V,
        ~cmp,
        ~at,
        String.eq(k, c),
        k,
        r,
        t,
        c,
        m,
        idem,
        Order.fold_idem(~A, ~V, ~cmp, ~at, r, t, c, m, idem)
      )({==})

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Order.fold_some at the first key k, by whether k is c (hit)
def Order.fold_some.at(
  ~A: Data,
  ~V: Data,
  ~cmp: A -> A -> Cmp,
  ~at: V -> String -> Maybe<&2, A>,
  hit: Bool,
  k: String,
  r: List<&2, String>,
  t: V,
  +c: String,
  m: Maybe<&2, A>,
  idem: {
    Order.join(
      ~A,
      ~cmp,
      Order.join(~A, ~cmp, m, at(t)(c)),
      at(t)(c)
    )
      == Order.join(~A, ~cmp, m, at(t)(c)): Maybe<&2, A>
  },
  ih: {
    Shared.List.has(~String, ~String.eq, r, c) == True{}: Bool
  } -> {
    Order.fold(~A, ~V, ~cmp, ~at, r, t, c, m) == Order.join(~A, ~cmp, m, at(t)(c)): Maybe<&2, A>
  }
) -> {
  String.eq(k, c) == hit: Bool
} -> {
  List.any.if(u => Shared.List.has(~String, ~String.eq, r, c), hit) == True{}: Bool
} -> {
  Order.fold(
    ~A,
    ~V,
    ~cmp,
    ~at,
    r,
    t,
    c,
    Order.step(~A, ~cmp, hit, at(t)(k), m)
  )
    == Order.join(~A, ~cmp, m, at(t)(c)): Maybe<&2, A>
}:
  match hit:
    case False{}:
      he => hn => ih(hn)
    case True{}:
      he => hn =>
        %Equal.sym(
          String,
          k,
          c,
          Strings.String.eq_sound(k, c)(he)
        ): {
          Order.fold(
            ~A,
            ~V,
            ~cmp,
            ~at,
            r,
            t,
            c,
            Order.join(~A, ~cmp, m, at(t)(_))
          )
            == Order.join(~A, ~cmp, m, at(t)(c)): Maybe<&2, A>
        }
        Order.fold_idem(~A, ~V, ~cmp, ~at, r, t, c, m, idem)
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# a fold over keys with c joins the value of c
def Order.fold_some(
  ~A: Data,
  ~V: Data,
  ~cmp: A -> A -> Cmp,
  ~at: V -> String -> Maybe<&2, A>,
  ks: List<&2, String>,
  +t: V,
  +c: String,
  +m: Maybe<&2, A>,
  +idem: {
    Order.join(
      ~A,
      ~cmp,
      Order.join(~A, ~cmp, m, at(t)(c)),
      at(t)(c)
    )
      == Order.join(~A, ~cmp, m, at(t)(c)): Maybe<&2, A>
  }
) -> {
  Shared.List.has(~String, ~String.eq, ks, c) == True{}: Bool
} -> {
  Order.fold(~A, ~V, ~cmp, ~at, ks, t, c, m) == Order.join(~A, ~cmp, m, at(t)(c)): Maybe<&2, A>
}:
  match ks:
    case Nil{}:
      h => Empty.absurd(
        {
          Order.fold(
            ~A,
            ~V,
            ~cmp,
            ~at,
            Nil{},
            t,
            c,
            m
          )
            == Order.join(~A, ~cmp, m, at(t)(c)): Maybe<&2, A>
        },
        Shared.Bool.false_ne_true(h)
      )
    case Con{+k, +r}:
      Order.fold_some.at(
        ~A,
        ~V,
        ~cmp,
        ~at,
        String.eq(k, c),
        k,
        r,
        t,
        c,
        m,
        idem,
        Order.fold_some(~A, ~V, ~cmp, ~at, r, t, c, m, idem)
      )({==})

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Order.fold_all, by whether ks holds c (held)
def Order.fold_all.at(
  ~A: Data,
  ~V: Data,
  ~cmp: A -> A -> Cmp,
  ~at: V -> String -> Maybe<&2, A>,
  refl: @y: A -> {cmp(y, y) == EQ{}: Cmp},
  held: Bool,
  ks: List<&2, String>,
  +t: V,
  +c: String,
  +m: Maybe<&2, A>,
  out: {
    Shared.List.has(~String, ~String.eq, ks, c) == False{}: Bool
  } -> {at(t)(c) == None{}: Maybe<&2, A>}
) -> {
  Shared.List.has(~String, ~String.eq, ks, c) == held: Bool
} -> {
  Order.fold(~A, ~V, ~cmp, ~at, ks, t, c, m) == Order.join(~A, ~cmp, m, at(t)(c)): Maybe<&2, A>
}:
  match held:
    case True{}:
      h => Order.fold_some(
        ~A,
        ~V,
        ~cmp,
        ~at,
        ks,
        t,
        c,
        m,
        Order.join_idem(~A, ~cmp, refl, m, at(t)(c))
      )(h)
    case False{}:
      +h =>
        Equal.trans(
          Maybe<&2, A>,
          Order.fold(~A, ~V, ~cmp, ~at, ks, t, c, m),
          m,
          Order.join(~A, ~cmp, m, at(t)(c)),
          Order.fold_none(~A, ~V, ~cmp, ~at, ks, t, c, m)(h),
          (
            %Equal.sym(Maybe<&2, A>, at(t)(c), None{}, out(h)): {m == Order.join(~A, ~cmp, m, _): Maybe<&2, A>}
            {==})
        )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# a fold over keys that hold every key with a value joins the value of c
def Order.fold_all(
  ~A: Data,
  ~V: Data,
  ~cmp: A -> A -> Cmp,
  ~at: V -> String -> Maybe<&2, A>,
  refl: @y: A -> {cmp(y, y) == EQ{}: Cmp},
  +ks: List<&2, String>,
  t: V,
  +c: String,
  m: Maybe<&2, A>,
  out: {
    Shared.List.has(~String, ~String.eq, ks, c) == False{}: Bool
  } -> {at(t)(c) == None{}: Maybe<&2, A>}
) -> {
  Order.fold(~A, ~V, ~cmp, ~at, ks, t, c, m) == Order.join(~A, ~cmp, m, at(t)(c)): Maybe<&2, A>
}:
  Order.fold_all.at(
    ~A,
    ~V,
    ~cmp,
    ~at,
    refl,
    Shared.List.has(~String, ~String.eq, ks, c),
    ks,
    t,
    c,
    m,
    out
  )({==})
# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Order.join_comm when all three hold a value: by the orders c1 of o and p, c2
# of o and q, and c3 of p and q
def Order.comm3(
  ~A: Data,
  ~B: Data,
  ~cmp: A -> A -> Cmp,
  ~key: A -> B,
  swap: @a: A -> @b: A -> {cmp(b, a) == Cmps.Cmp.flip(cmp(a, b)): Cmp},
  same: @a: A -> @b: A -> {cmp(a, b) == EQ{}: Cmp} -> {key(a) == key(b): B},
  c1: Cmp,
  c2: Cmp,
  c3: Cmp,
  o: A,
  +p: A,
  +q: A
) -> {
  cmp(o, p) == c1: Cmp
} -> {
  cmp(o, q) == c2: Cmp
} -> {
  cmp(p, q) == c3: Cmp
} -> {
  Cmps.Cmp.chain(c1, c3, c2) == True{}: Bool
} -> {
  key(
    Order.by(A, cmp(Order.by(A, c1, o, p), q), Order.by(A, c1, o, p), q)
  )
    == key(Order.by(A, cmp(Order.by(A, c2, o, q), p), Order.by(A, c2, o, q), p)): B
}:
  match c1 c2 c3:
    case LT{} LT{} LT{}:
      +e1 => +e2 => +e3 => h =>
        %Equal.sym(
          Cmp,
          cmp(p, q),
          LT{},
          e3
        ): {key(Order.by(A, _, p, q)) == key(Order.by(A, cmp(q, p), q, p)): B}
        %Equal.sym(
          Cmp,
          cmp(q, p),
          Cmps.Cmp.flip(cmp(p, q)),
          swap(p)(q)
        ): {key(Order.by(A, LT{}, p, q)) == key(Order.by(A, _, q, p)): B}
        %Equal.sym(
          Cmp,
          cmp(p, q),
          LT{},
          e3
        ): {key(Order.by(A, LT{}, p, q)) == key(Order.by(A, Cmps.Cmp.flip(_), q, p)): B}
        {==}
    case LT{} LT{} EQ{}:
      +e1 => +e2 => +e3 => h =>
        %Equal.sym(
          Cmp,
          cmp(p, q),
          EQ{},
          e3
        ): {key(Order.by(A, _, p, q)) == key(Order.by(A, cmp(q, p), q, p)): B}
        %Equal.sym(
          Cmp,
          cmp(q, p),
          Cmps.Cmp.flip(cmp(p, q)),
          swap(p)(q)
        ): {key(Order.by(A, EQ{}, p, q)) == key(Order.by(A, _, q, p)): B}
        %Equal.sym(
          Cmp,
          cmp(p, q),
          EQ{},
          e3
        ): {key(Order.by(A, EQ{}, p, q)) == key(Order.by(A, Cmps.Cmp.flip(_), q, p)): B}
        same(p)(q)(e3)
    case LT{} LT{} GT{}:
      +e1 => +e2 => +e3 => h =>
        %Equal.sym(
          Cmp,
          cmp(p, q),
          GT{},
          e3
        ): {key(Order.by(A, _, p, q)) == key(Order.by(A, cmp(q, p), q, p)): B}
        %Equal.sym(
          Cmp,
          cmp(q, p),
          Cmps.Cmp.flip(cmp(p, q)),
          swap(p)(q)
        ): {key(Order.by(A, GT{}, p, q)) == key(Order.by(A, _, q, p)): B}
        %Equal.sym(
          Cmp,
          cmp(p, q),
          GT{},
          e3
        ): {key(Order.by(A, GT{}, p, q)) == key(Order.by(A, Cmps.Cmp.flip(_), q, p)): B}
        {==}
    case LT{} EQ{} LT{}:
      e1 => e2 => e3 => h => Empty.absurd(
        {
          key(
            Order.by(A, cmp(Order.by(A, LT{}, o, p), q), Order.by(A, LT{}, o, p), q)
          )
            == key(Order.by(A, cmp(Order.by(A, EQ{}, o, q), p), Order.by(A, EQ{}, o, q), p)): B
        },
        Shared.Bool.false_ne_true(h)
      )
    case LT{} EQ{} EQ{}:
      e1 => e2 => e3 => h => Empty.absurd(
        {
          key(
            Order.by(A, cmp(Order.by(A, LT{}, o, p), q), Order.by(A, LT{}, o, p), q)
          )
            == key(Order.by(A, cmp(Order.by(A, EQ{}, o, q), p), Order.by(A, EQ{}, o, q), p)): B
        },
        Shared.Bool.false_ne_true(h)
      )
    case LT{} EQ{} GT{}:
      +e1 => +e2 => +e3 => h =>
        %Equal.sym(
          Cmp,
          cmp(p, q),
          GT{},
          e3
        ): {key(Order.by(A, _, p, q)) == key(Order.by(A, cmp(o, p), o, p)): B}
        %Equal.sym(
          Cmp,
          cmp(o, p),
          LT{},
          e1
        ): {key(Order.by(A, GT{}, p, q)) == key(Order.by(A, _, o, p)): B}
        {==}
    case LT{} GT{} LT{}:
      e1 => e2 => e3 => h => Empty.absurd(
        {
          key(
            Order.by(A, cmp(Order.by(A, LT{}, o, p), q), Order.by(A, LT{}, o, p), q)
          )
            == key(Order.by(A, cmp(Order.by(A, GT{}, o, q), p), Order.by(A, GT{}, o, q), p)): B
        },
        Shared.Bool.false_ne_true(h)
      )
    case LT{} GT{} EQ{}:
      e1 => e2 => e3 => h => Empty.absurd(
        {
          key(
            Order.by(A, cmp(Order.by(A, LT{}, o, p), q), Order.by(A, LT{}, o, p), q)
          )
            == key(Order.by(A, cmp(Order.by(A, GT{}, o, q), p), Order.by(A, GT{}, o, q), p)): B
        },
        Shared.Bool.false_ne_true(h)
      )
    case LT{} GT{} GT{}:
      +e1 => +e2 => +e3 => h =>
        %Equal.sym(
          Cmp,
          cmp(p, q),
          GT{},
          e3
        ): {key(Order.by(A, _, p, q)) == key(Order.by(A, cmp(o, p), o, p)): B}
        %Equal.sym(
          Cmp,
          cmp(o, p),
          LT{},
          e1
        ): {key(Order.by(A, GT{}, p, q)) == key(Order.by(A, _, o, p)): B}
        {==}
    case EQ{} LT{} LT{}:
      +e1 => +e2 => +e3 => h =>
        %Equal.sym(
          Cmp,
          cmp(o, q),
          LT{},
          e2
        ): {key(Order.by(A, _, o, q)) == key(Order.by(A, cmp(q, p), q, p)): B}
        %Equal.sym(
          Cmp,
          cmp(q, p),
          Cmps.Cmp.flip(cmp(p, q)),
          swap(p)(q)
        ): {key(Order.by(A, LT{}, o, q)) == key(Order.by(A, _, q, p)): B}
        %Equal.sym(
          Cmp,
          cmp(p, q),
          LT{},
          e3
        ): {key(Order.by(A, LT{}, o, q)) == key(Order.by(A, Cmps.Cmp.flip(_), q, p)): B}
        {==}
    case EQ{} LT{} EQ{}:
      e1 => e2 => e3 => h => Empty.absurd(
        {
          key(
            Order.by(A, cmp(Order.by(A, EQ{}, o, p), q), Order.by(A, EQ{}, o, p), q)
          )
            == key(Order.by(A, cmp(Order.by(A, LT{}, o, q), p), Order.by(A, LT{}, o, q), p)): B
        },
        Shared.Bool.false_ne_true(h)
      )
    case EQ{} LT{} GT{}:
      e1 => e2 => e3 => h => Empty.absurd(
        {
          key(
            Order.by(A, cmp(Order.by(A, EQ{}, o, p), q), Order.by(A, EQ{}, o, p), q)
          )
            == key(Order.by(A, cmp(Order.by(A, LT{}, o, q), p), Order.by(A, LT{}, o, q), p)): B
        },
        Shared.Bool.false_ne_true(h)
      )
    case EQ{} EQ{} LT{}:
      e1 => e2 => e3 => h => Empty.absurd(
        {
          key(
            Order.by(A, cmp(Order.by(A, EQ{}, o, p), q), Order.by(A, EQ{}, o, p), q)
          )
            == key(Order.by(A, cmp(Order.by(A, EQ{}, o, q), p), Order.by(A, EQ{}, o, q), p)): B
        },
        Shared.Bool.false_ne_true(h)
      )
    case EQ{} EQ{} EQ{}:
      +e1 => +e2 => +e3 => h =>
        %Equal.sym(
          Cmp,
          cmp(o, q),
          EQ{},
          e2
        ): {key(Order.by(A, _, o, q)) == key(Order.by(A, cmp(o, p), o, p)): B}
        %Equal.sym(
          Cmp,
          cmp(o, p),
          EQ{},
          e1
        ): {key(Order.by(A, EQ{}, o, q)) == key(Order.by(A, _, o, p)): B}
        {==}
    case EQ{} EQ{} GT{}:
      e1 => e2 => e3 => h => Empty.absurd(
        {
          key(
            Order.by(A, cmp(Order.by(A, EQ{}, o, p), q), Order.by(A, EQ{}, o, p), q)
          )
            == key(Order.by(A, cmp(Order.by(A, EQ{}, o, q), p), Order.by(A, EQ{}, o, q), p)): B
        },
        Shared.Bool.false_ne_true(h)
      )
    case EQ{} GT{} LT{}:
      e1 => e2 => e3 => h => Empty.absurd(
        {
          key(
            Order.by(A, cmp(Order.by(A, EQ{}, o, p), q), Order.by(A, EQ{}, o, p), q)
          )
            == key(Order.by(A, cmp(Order.by(A, GT{}, o, q), p), Order.by(A, GT{}, o, q), p)): B
        },
        Shared.Bool.false_ne_true(h)
      )
    case EQ{} GT{} EQ{}:
      e1 => e2 => e3 => h => Empty.absurd(
        {
          key(
            Order.by(A, cmp(Order.by(A, EQ{}, o, p), q), Order.by(A, EQ{}, o, p), q)
          )
            == key(Order.by(A, cmp(Order.by(A, GT{}, o, q), p), Order.by(A, GT{}, o, q), p)): B
        },
        Shared.Bool.false_ne_true(h)
      )
    case EQ{} GT{} GT{}:
      +e1 => +e2 => +e3 => h =>
        %Equal.sym(
          Cmp,
          cmp(o, q),
          GT{},
          e2
        ): {key(Order.by(A, _, o, q)) == key(Order.by(A, cmp(o, p), o, p)): B}
        %Equal.sym(
          Cmp,
          cmp(o, p),
          EQ{},
          e1
        ): {key(Order.by(A, GT{}, o, q)) == key(Order.by(A, _, o, p)): B}
        {==}
    case GT{} LT{} LT{}:
      +e1 => +e2 => +e3 => h =>
        %Equal.sym(
          Cmp,
          cmp(o, q),
          LT{},
          e2
        ): {key(Order.by(A, _, o, q)) == key(Order.by(A, cmp(q, p), q, p)): B}
        %Equal.sym(
          Cmp,
          cmp(q, p),
          Cmps.Cmp.flip(cmp(p, q)),
          swap(p)(q)
        ): {key(Order.by(A, LT{}, o, q)) == key(Order.by(A, _, q, p)): B}
        %Equal.sym(
          Cmp,
          cmp(p, q),
          LT{},
          e3
        ): {key(Order.by(A, LT{}, o, q)) == key(Order.by(A, Cmps.Cmp.flip(_), q, p)): B}
        {==}
    case GT{} LT{} EQ{}:
      e1 => e2 => e3 => h => Empty.absurd(
        {
          key(
            Order.by(A, cmp(Order.by(A, GT{}, o, p), q), Order.by(A, GT{}, o, p), q)
          )
            == key(Order.by(A, cmp(Order.by(A, LT{}, o, q), p), Order.by(A, LT{}, o, q), p)): B
        },
        Shared.Bool.false_ne_true(h)
      )
    case GT{} LT{} GT{}:
      e1 => e2 => e3 => h => Empty.absurd(
        {
          key(
            Order.by(A, cmp(Order.by(A, GT{}, o, p), q), Order.by(A, GT{}, o, p), q)
          )
            == key(Order.by(A, cmp(Order.by(A, LT{}, o, q), p), Order.by(A, LT{}, o, q), p)): B
        },
        Shared.Bool.false_ne_true(h)
      )
    case GT{} EQ{} LT{}:
      +e1 => +e2 => +e3 => h =>
        %Equal.sym(
          Cmp,
          cmp(o, q),
          EQ{},
          e2
        ): {key(Order.by(A, _, o, q)) == key(Order.by(A, cmp(o, p), o, p)): B}
        %Equal.sym(
          Cmp,
          cmp(o, p),
          GT{},
          e1
        ): {key(Order.by(A, EQ{}, o, q)) == key(Order.by(A, _, o, p)): B}
        {==}
    case GT{} EQ{} EQ{}:
      e1 => e2 => e3 => h => Empty.absurd(
        {
          key(
            Order.by(A, cmp(Order.by(A, GT{}, o, p), q), Order.by(A, GT{}, o, p), q)
          )
            == key(Order.by(A, cmp(Order.by(A, EQ{}, o, q), p), Order.by(A, EQ{}, o, q), p)): B
        },
        Shared.Bool.false_ne_true(h)
      )
    case GT{} EQ{} GT{}:
      e1 => e2 => e3 => h => Empty.absurd(
        {
          key(
            Order.by(A, cmp(Order.by(A, GT{}, o, p), q), Order.by(A, GT{}, o, p), q)
          )
            == key(Order.by(A, cmp(Order.by(A, EQ{}, o, q), p), Order.by(A, EQ{}, o, q), p)): B
        },
        Shared.Bool.false_ne_true(h)
      )
    case GT{} GT{} LT{}:
      +e1 => +e2 => +e3 => h =>
        %Equal.sym(
          Cmp,
          cmp(o, q),
          GT{},
          e2
        ): {key(Order.by(A, _, o, q)) == key(Order.by(A, cmp(o, p), o, p)): B}
        %Equal.sym(
          Cmp,
          cmp(o, p),
          GT{},
          e1
        ): {key(Order.by(A, GT{}, o, q)) == key(Order.by(A, _, o, p)): B}
        {==}
    case GT{} GT{} EQ{}:
      +e1 => +e2 => +e3 => h =>
        %Equal.sym(
          Cmp,
          cmp(o, q),
          GT{},
          e2
        ): {key(Order.by(A, _, o, q)) == key(Order.by(A, cmp(o, p), o, p)): B}
        %Equal.sym(
          Cmp,
          cmp(o, p),
          GT{},
          e1
        ): {key(Order.by(A, GT{}, o, q)) == key(Order.by(A, _, o, p)): B}
        {==}
    case GT{} GT{} GT{}:
      +e1 => +e2 => +e3 => h =>
        %Equal.sym(
          Cmp,
          cmp(o, q),
          GT{},
          e2
        ): {key(Order.by(A, _, o, q)) == key(Order.by(A, cmp(o, p), o, p)): B}
        %Equal.sym(
          Cmp,
          cmp(o, p),
          GT{},
          e1
        ): {key(Order.by(A, GT{}, o, q)) == key(Order.by(A, _, o, p)): B}
        {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# Order.join_comm when only the two others hold a value: by the order c of p
# and q
def Order.comm2(
  ~A: Data,
  ~B: Data,
  ~cmp: A -> A -> Cmp,
  ~key: A -> B,
  swap: @a: A -> @b: A -> {cmp(b, a) == Cmps.Cmp.flip(cmp(a, b)): Cmp},
  same: @a: A -> @b: A -> {cmp(a, b) == EQ{}: Cmp} -> {key(a) == key(b): B},
  c: Cmp,
  +p: A,
  +q: A
) -> {cmp(p, q) == c: Cmp} -> {key(Order.by(A, c, p, q)) == key(Order.by(A, cmp(q, p), q, p)): B}:
  match c:
    case LT{}:
      +e =>
        %Equal.sym(
          Cmp,
          cmp(q, p),
          Cmps.Cmp.flip(cmp(p, q)),
          swap(p)(q)
        ): {key(q) == key(Order.by(A, _, q, p)): B}
        %Equal.sym(Cmp, cmp(p, q), LT{}, e): {key(q) == key(Order.by(A, Cmps.Cmp.flip(_), q, p)): B}
        {==}
    case EQ{}:
      +e =>
        %Equal.sym(
          Cmp,
          cmp(q, p),
          Cmps.Cmp.flip(cmp(p, q)),
          swap(p)(q)
        ): {key(p) == key(Order.by(A, _, q, p)): B}
        %Equal.sym(Cmp, cmp(p, q), EQ{}, e): {key(p) == key(Order.by(A, Cmps.Cmp.flip(_), q, p)): B}
        same(p)(q)(e)
    case GT{}:
      +e =>
        %Equal.sym(
          Cmp,
          cmp(q, p),
          Cmps.Cmp.flip(cmp(p, q)),
          swap(p)(q)
        ): {key(p) == key(Order.by(A, _, q, p)): B}
        %Equal.sym(Cmp, cmp(p, q), GT{}, e): {key(p) == key(Order.by(A, Cmps.Cmp.flip(_), q, p)): B}
        {==}

# taking in x then y holds a value with the same key as taking in y then x,
# for an order whose comparisons chain
def Order.join_comm(
  ~A: Data,
  ~B: Data,
  ~cmp: A -> A -> Cmp,
  ~key: A -> B,
  swap: @a: A -> @b: A -> {cmp(b, a) == Cmps.Cmp.flip(cmp(a, b)): Cmp},
  same: @a: A -> @b: A -> {cmp(a, b) == EQ{}: Cmp} -> {key(a) == key(b): B},
  chain: @a: A -> @b: A -> @c: A -> {
    Cmps.Cmp.chain(cmp(a, b), cmp(b, c), cmp(a, c)) == True{}: Bool
  },
  m: Maybe<&2, A>,
  x: Maybe<&2, A>,
  y: Maybe<&2, A>
) -> {
  Maybe.map(
    &2,
    A,
    B,
    z => key(z),
    Order.join(~A, ~cmp, Order.join(~A, ~cmp, m, x), y)
  )
    == Maybe.map(
      &2,
      A,
      B,
      z => key(z),
      Order.join(~A, ~cmp, Order.join(~A, ~cmp, m, y), x)
    ): Maybe<&2, B>
}:
  match m x y:
    case w None{} v:
      {==}
    case w Some{t} None{}:
      {==}
    case None{} Some{+p} Some{+q}:
      Equal.cong(
        B,
        Maybe<&2, B>,
        z => Some{z},
        key(Order.by(A, cmp(p, q), p, q)),
        key(Order.by(A, cmp(q, p), q, p)),
        Order.comm2(~A, ~B, ~cmp, ~key, swap, same, cmp(p, q), p, q)({==})
      )
    case Some{+o} Some{+p} Some{+q}:
      Equal.cong(
        B,
        Maybe<&2, B>,
        z => Some{z},
        key(Order.by(A, cmp(Order.by(A, cmp(o, p), o, p), q), Order.by(A, cmp(o, p), o, p), q)),
        key(Order.by(A, cmp(Order.by(A, cmp(o, q), o, q), p), Order.by(A, cmp(o, q), o, q), p)),
        Order.comm3(
          ~A,
          ~B,
          ~cmp,
          ~key,
          swap,
          same,
          cmp(o, p),
          cmp(o, q),
          cmp(p, q),
          o,
          p,
          q
        )({==})({==})({==})(chain(o)(p)(q))
      )
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information
