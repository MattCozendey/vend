import Base
import ./shared/shared.bend as Shared

# Quorums
# -------
# The owners of a decision each cast at most one ballot. A choice has a
# majority when more ballots are for it than are not. A bucket is decided by a
# majority only (Quorum.major). A decision only gains information as ballots
# arrive, so it never changes (Quorum.major_kept).

# the ballot v is for x
def Quorum.hit(~B: Data, ~same: B -> B -> Bool, v: Maybe<&2, B>, x: B) -> Bool:
  match v:
    case Some{b}:
      same(b, x)
    case None{}:
      False{}

# the number of ballots of bs for x
def Quorum.yes(
  ~B: Data,
  ~same: B -> B -> Bool,
  bs: List<&2, Maybe<&2, B>>,
  +x: B
) -> Nat:
  match bs:
    case Nil{}:
      0n
    case Con{v, r}:
      Shared.Nat.add_if(Quorum.hit(~B, ~same, v, x), Quorum.yes(~B, ~same, r, x))

# the number of ballots of bs that are not for x (none counts)
def Quorum.no(
  ~B: Data,
  ~same: B -> B -> Bool,
  bs: List<&2, Maybe<&2, B>>,
  +x: B
) -> Nat:
  match bs:
    case Nil{}:
      0n
    case Con{v, r}:
      Shared.Nat.add_if(Bool.not(Quorum.hit(~B, ~same, v, x)), Quorum.no(~B, ~same, r, x))

# x has a majority of bs
def Quorum.has(
  ~B: Data,
  ~same: B -> B -> Bool,
  +bs: List<&2, Maybe<&2, B>>,
  +x: B
) -> Bool:
  Nat.is_lt(Quorum.no(~B, ~same, bs, x), Quorum.yes(~B, ~same, bs, x))

# the vote of v when it has a majority of bs, else rest
def Quorum.winner.at(
  ~B: Data,
  ~same: B -> B -> Bool,
  v: Maybe<&2, B>,
  rest: Maybe<&2, B>,
  bs: List<&2, Maybe<&2, B>>
) -> Maybe<&2, B>:
  match v:
    case Some{+b}:
      Bool.pick(Maybe<&2, B>, Quorum.has(~B, ~same, bs, b), Some{b}, rest)
    case None{}:
      rest

# the first vote of ks that has a majority of bs
def Quorum.winner(
  ~B: Data,
  ~same: B -> B -> Bool,
  ks: List<&2, Maybe<&2, B>>,
  +bs: List<&2, Maybe<&2, B>>
) -> Maybe<&2, B>:
  match ks:
    case Nil{}:
      None{}
    case Con{k, r}:
      Quorum.winner.at(~B, ~same, k, Quorum.winner(~B, ~same, r, bs), bs)

# a candidate and its count
type Pass<-B: Data> is Data:
  Pass{cand: Maybe<&2, B>, count: Nat}

# the candidate of the pass p
def Pass.cand(-B: Data, p: Pass<B>) -> Maybe<&2, B>:
  match p:
    case Pass{c, k}:
      c

# the pass after the vote b, from the candidate c and the count 1 + j
def Quorum.step.vote(~B: Data, ~same: B -> B -> Bool, b: B, c: Maybe<&2, B>, +j: Nat) -> Pass<B>:
  match c:
    case Some{+a}:
      Bool.pick(Pass<B>, same(a, b), Pass{Some{a}, 2n+j}, Pass{Some{a}, j})
    case None{}:
      Pass{None{}, j}

# the pass after the ballot v, from the candidate c and the count k
def Quorum.step.of(
  ~B: Data,
  ~same: B -> B -> Bool,
  v: Maybe<&2, B>,
  c: Maybe<&2, B>,
  k: Nat
) -> Pass<B>:
  match v k:
    case Some{b} 0n:
      Pass{Some{b}, 1n}
    case Some{+b} 1n+j:
      Quorum.step.vote(~B, ~same, b, c, j)
    case None{} 0n:
      Pass{c, 0n}
    case None{} 1n+j:
      Pass{c, j}

# the pass after the ballot v
def Quorum.step(
  ~B: Data,
  ~same: B -> B -> Bool,
  v: Maybe<&2, B>,
  p: Pass<B>
) -> Pass<B>:
  match p:
    case Pass{c, k}:
      Quorum.step.of(~B, ~same, v, c, k)

# the pass over the ballots bs, the last first
def Quorum.pass(~B: Data, ~same: B -> B -> Bool, bs: List<&2, Maybe<&2, B>>) -> Pass<B>:
  match bs:
    case Nil{}:
      Pass{None{}, 0n}
    case Con{v, r}:
      Quorum.step(~B, ~same, v, Quorum.pass(~B, ~same, r))

# Laws
# ----
# Each law asks of same only its laws (Shared.Eq.Laws).

# a ballot for y is not for x, when x is not y
def Quorum.hit_excl(
  ~B: Data,
  ~same: B -> B -> Bool,
  ~laws: Shared.Eq.Laws(B, same),
  v: Maybe<&2, B>,
  x: B,
  +y: B,
  no: {same(x, y) == False{}: Bool}
) -> {
  Quorum.hit(~B, ~same, v, y) == True{}: Bool
} -> {Quorum.hit(~B, ~same, v, x) == False{}: Bool}:
  match v:
    case Some{b}:
      h =>
        %Equal.sym(
          B,
          b,
          y,
          Shared.Eq.sound(~B, ~same, laws, b)(y)(h)
        ): {same(_, x) == False{}: Bool}
        Shared.Eq.ne_flip(~B, ~same, ~laws, x, y, no)
    case None{}:
      h => {==}

# Quorum.yes_le_no for one ballot, by whether it is for y (hy) and x (hx)
def Quorum.yes_le_no.at(
  hy: Bool,
  hx: Bool,
  excl: {hy == True{}: Bool} -> {hx == False{}: Bool},
  y: Nat,
  n: Nat,
  ih: {Nat.is_le(y, n) == True{}: Bool}
) -> {Nat.is_le(Shared.Nat.add_if(hy, y), Shared.Nat.add_if(Bool.not(hx), n)) == True{}: Bool}:
  match hy hx:
    case True{} True{}:
      Empty.absurd(
        {Nat.is_le(1n+y, n) == True{}: Bool},
        Shared.Bool.false_ne_true(Equal.sym(Bool, True{}, False{}, excl({==})))
      )
    case True{} False{}:
      ih
    case False{} True{}:
      ih
    case False{} False{}:
      Shared.Nat.le_succ(y, n)(ih)

# no more ballots are for y than are not for x, when x is not y
def Quorum.yes_le_no(
  ~B: Data,
  ~same: B -> B -> Bool,
  ~laws: Shared.Eq.Laws(B, same),
  bs: List<&2, Maybe<&2, B>>,
  +x: B,
  +y: B,
  +no: {same(x, y) == False{}: Bool}
) -> {Nat.is_le(Quorum.yes(~B, ~same, bs, y), Quorum.no(~B, ~same, bs, x)) == True{}: Bool}:
  match bs:
    case Nil{}:
      {==}
    case Con{+v, +r}:
      Quorum.yes_le_no.at(
        Quorum.hit(~B, ~same, v, y),
        Quorum.hit(~B, ~same, v, x),
        Quorum.hit_excl(~B, ~same, ~laws, v, x, y, no),
        Quorum.yes(~B, ~same, r, y),
        Quorum.no(~B, ~same, r, x),
        Quorum.yes_le_no(~B, ~same, ~laws, r, x, y, no)
      )

# Quorum.unique once same(x, y) is known (held)
def Quorum.unique.at(
  ~B: Data,
  ~same: B -> B -> Bool,
  ~laws: Shared.Eq.Laws(B, same),
  held: Bool,
  +bs: List<&2, Maybe<&2, B>>,
  +x: B,
  +y: B,
  +e: {same(x, y) == held: Bool},
  hx: {Quorum.has(~B, ~same, bs, x) == True{}: Bool},
  hy: {Quorum.has(~B, ~same, bs, y) == True{}: Bool}
) -> {x == y: B}:
  match held:
    case True{}:
      Shared.Eq.sound(~B, ~same, laws, x)(y)(e)
    case False{}:
      +yx = Quorum.yes(~B, ~same, bs, x)
      +yy = Quorum.yes(~B, ~same, bs, y)
      +nx = Quorum.no(~B, ~same, bs, x)
      ny = Quorum.no(~B, ~same, bs, y)
      a = Shared.Nat.le_lt(
        yx,
        ny,
        yy
      )(
        Quorum.yes_le_no(~B, ~same, ~laws, bs, y, x, Shared.Eq.ne_flip(~B, ~same, ~laws, x, y, e))
      )(hy)
      b = Shared.Nat.lt_le(yx, yy, nx)(a)(Quorum.yes_le_no(~B, ~same, ~laws, bs, x, y, e))
      c = Shared.Nat.lt_le(yx, nx, yx)(b)(Shared.Nat.lt_weak(nx, yx)(hx))
      Empty.absurd(
        {x == y: B},
        Shared.Bool.false_ne_true(
          Equal.trans(
            Bool,
            False{},
            Nat.is_lt(yx, yx),
            True{},
            Equal.sym(Bool, Nat.is_lt(yx, yx), False{}, Shared.Nat.lt_irrefl(yx)),
            c
          )
        )
      )

# two choices with a majority of the same ballots are the same
def Quorum.unique(
  ~Ty: Data,
  ~same: Ty -> Ty -> Bool,
  ~laws: Shared.Eq.Laws(Ty, same),
  bs: List<&2, Maybe<&2, Ty>>,
  +x: Ty,
  +y: Ty
) -> {Quorum.has(~Ty, ~same, bs, x) == True{}: Bool}
  -> {Quorum.has(~Ty, ~same, bs, y) == True{}: Bool}
  -> {x == y: Ty}:
  hx => hy => Quorum.unique.at(~Ty, ~same, ~laws, same(x, y), bs, x, y, {==}, hx, hy)

# Quorum.yes_more for one ballot v, kept as w
def Quorum.yes_more.at(
  ~B: Data,
  ~same: B -> B -> Bool,
  ~laws: Shared.Eq.Laws(B, same),
  v: Maybe<&2, B>,
  w: Maybe<&2, B>,
  x: B,
  y: Nat,
  y2: Nat,
  k: {Shared.Maybe.keeps(~B, ~same, v, w) == True{}: Bool},
  ih: {Nat.is_le(y, y2) == True{}: Bool}
) -> {
  Nat.is_le(
    Shared.Nat.add_if(Quorum.hit(~B, ~same, v, x), y),
    Shared.Nat.add_if(Quorum.hit(~B, ~same, w, x), y2)
  )
    == True{}: Bool
}:
  match v w:
    case None{} u:
      Shared.Nat.le_add_if(Quorum.hit(~B, ~same, u, x), y, y2)(ih)
    case Some{b} None{}:
      Empty.absurd(
        {Nat.is_le(Shared.Nat.add_if(same(b, x), y), y2) == True{}: Bool},
        Shared.Bool.false_ne_true(k)
      )
    case Some{+b} Some{c}:
      %Shared.Eq.sound(~B, ~same, laws, b)(c)(k):
        {
          Nat.is_le(
            Shared.Nat.add_if(same(b, x), y),
            Shared.Nat.add_if(same(_, x), y2)
          )
            == True{}: Bool
        }
      Shared.Nat.add_if_le(same(b, x), y, y2)(ih)

# Quorum.no_less for one ballot v, kept as w
def Quorum.no_less.at(
  ~B: Data,
  ~same: B -> B -> Bool,
  ~laws: Shared.Eq.Laws(B, same),
  v: Maybe<&2, B>,
  w: Maybe<&2, B>,
  x: B,
  n: Nat,
  n2: Nat,
  k: {Shared.Maybe.keeps(~B, ~same, v, w) == True{}: Bool},
  ih: {Nat.is_le(n2, n) == True{}: Bool}
) -> {
  Nat.is_le(
    Shared.Nat.add_if(Bool.not(Quorum.hit(~B, ~same, w, x)), n2),
    Shared.Nat.add_if(Bool.not(Quorum.hit(~B, ~same, v, x)), n)
  )
    == True{}: Bool
}:
  match v w:
    case None{} u:
      Shared.Nat.add_if_le_succ(Bool.not(Quorum.hit(~B, ~same, u, x)), n2, n)(ih)
    case Some{b} None{}:
      Empty.absurd(
        {Nat.is_le(1n+n2, Shared.Nat.add_if(Bool.not(same(b, x)), n)) == True{}: Bool},
        Shared.Bool.false_ne_true(k)
      )
    case Some{+b} Some{c}:
      not1 = Bool.not(same(b, x))
      %Shared.Eq.sound(~B, ~same, laws, b)(c)(k):
        {
          Nat.is_le(
            Shared.Nat.add_if(Bool.not(same(_, x)), n2),
            Shared.Nat.add_if(not1, n)
          )
            == True{}: Bool
        }
      Shared.Nat.add_if_le(not1, n2, n)(ih)

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# kept ballots keep the ballots for x
def Quorum.yes_more(
  ~B: Data,
  ~same: B -> B -> Bool,
  ~laws: Shared.Eq.Laws(B, same),
  bs: List<&2, Maybe<&2, B>>,
  bs2: List<&2, Maybe<&2, B>>,
  +x: B
) -> {
  Shared.List.all2(
    ~Maybe<&2, B>,
    ~Maybe<&2, B>,
    ~Shared.Maybe.keeps(~B, ~same),
    bs,
    bs2
  )
    == True{}: Bool
} -> {Nat.is_le(Quorum.yes(~B, ~same, bs, x), Quorum.yes(~B, ~same, bs2, x)) == True{}: Bool}:
  match bs bs2:
    case Nil{} Nil{}:
      k => {==}
    case Con{+v, +r} Con{+w, +r2}:
      +k =>
        +kh = Shared.Maybe.keeps(~B, ~same, v, w)
        kr = Shared.List.all2(
          ~Maybe<&2, B>,
          ~Maybe<&2, B>,
          ~Shared.Maybe.keeps(~B, ~same),
          r,
          r2
        )
        Quorum.yes_more.at(
          ~B,
          ~same,
          ~laws,
          v,
          w,
          x,
          Quorum.yes(~B, ~same, r, x),
          Quorum.yes(~B, ~same, r2, x),
          Shared.Bool.and_true_left(kh, kr)(k),
          Quorum.yes_more(~B, ~same, ~laws, r, r2, x)(Shared.Bool.and_true_right(kh, kr)(k))
        )
    case Nil{} Con{w, r2}:
      k => Empty.absurd(
        {Nat.is_le(0n, Quorum.yes(~B, ~same, w <> r2, x)) == True{}: Bool},
        Shared.Bool.false_ne_true(k)
      )
    case Con{v, r} Nil{}:
      k => Empty.absurd(
        {Nat.is_le(Quorum.yes(~B, ~same, v <> r, x), 0n) == True{}: Bool},
        Shared.Bool.false_ne_true(k)
      )
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# kept ballots keep the ballots not for x from growing
def Quorum.no_less(
  ~B: Data,
  ~same: B -> B -> Bool,
  ~laws: Shared.Eq.Laws(B, same),
  bs: List<&2, Maybe<&2, B>>,
  bs2: List<&2, Maybe<&2, B>>,
  +x: B
) -> {
  Shared.List.all2(
    ~Maybe<&2, B>,
    ~Maybe<&2, B>,
    ~Shared.Maybe.keeps(~B, ~same),
    bs,
    bs2
  )
    == True{}: Bool
} -> {Nat.is_le(Quorum.no(~B, ~same, bs2, x), Quorum.no(~B, ~same, bs, x)) == True{}: Bool}:
  match bs bs2:
    case Nil{} Nil{}:
      k => {==}
    case Con{+v, +r} Con{+w, +r2}:
      +k =>
        +kh = Shared.Maybe.keeps(~B, ~same, v, w)
        kr = Shared.List.all2(
          ~Maybe<&2, B>,
          ~Maybe<&2, B>,
          ~Shared.Maybe.keeps(~B, ~same),
          r,
          r2
        )
        Quorum.no_less.at(
          ~B,
          ~same,
          ~laws,
          v,
          w,
          x,
          Quorum.no(~B, ~same, r, x),
          Quorum.no(~B, ~same, r2, x),
          Shared.Bool.and_true_left(kh, kr)(k),
          Quorum.no_less(~B, ~same, ~laws, r, r2, x)(Shared.Bool.and_true_right(kh, kr)(k))
        )
    case Nil{} Con{w, r2}:
      k => Empty.absurd(
        {Nat.is_le(Quorum.no(~B, ~same, w <> r2, x), 0n) == True{}: Bool},
        Shared.Bool.false_ne_true(k)
      )
    case Con{v, r} Nil{}:
      k => Empty.absurd(
        {Nat.is_le(0n, Quorum.no(~B, ~same, v <> r, x)) == True{}: Bool},
        Shared.Bool.false_ne_true(k)
      )
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# Quorum.has_winner when the vote b was picked or not (held)
def Quorum.has_winner.if(
  ~B: Data,
  ~same: B -> B -> Bool,
  held: Bool,
  b: B,
  rest: Maybe<&2, B>,
  bs: List<&2, Maybe<&2, B>>,
  x: B,
  eb: {Quorum.has(~B, ~same, bs, b) == held: Bool},
  ih: {rest == Some{x}: Maybe<&2, B>} -> {Quorum.has(~B, ~same, bs, x) == True{}: Bool}
) -> {
  Bool.pick(Maybe<&2, B>, held, Some{b}, rest) == Some{x}: Maybe<&2, B>
} -> {Quorum.has(~B, ~same, bs, x) == True{}: Bool}:
  match held:
    case True{}:
      h =>
        %Shared.Maybe.some_inj(B, b, x, h): {Quorum.has(~B, ~same, bs, _) == True{}: Bool}
        eb
    case False{}:
      ih

# Quorum.has_winner at the ballot v, with rest the winner after it
def Quorum.has_winner.at(
  ~B: Data,
  ~same: B -> B -> Bool,
  v: Maybe<&2, B>,
  rest: Maybe<&2, B>,
  +bs: List<&2, Maybe<&2, B>>,
  x: B,
  ih: {rest == Some{x}: Maybe<&2, B>} -> {Quorum.has(~B, ~same, bs, x) == True{}: Bool}
) -> {
  Quorum.winner.at(~B, ~same, v, rest, bs) == Some{x}: Maybe<&2, B>
} -> {Quorum.has(~B, ~same, bs, x) == True{}: Bool}:
  match v:
    case Some{+b}:
      Quorum.has_winner.if(~B, ~same, Quorum.has(~B, ~same, bs, b), b, rest, bs, x, {==}, ih)
    case None{}:
      ih

# the winner has a majority
def Quorum.has_winner(
  ~Ty: Data,
  ~same: Ty -> Ty -> Bool,
  ks: List<&2, Maybe<&2, Ty>>,
  +bs: List<&2, Maybe<&2, Ty>>,
  +x: Ty
) -> {Quorum.winner(~Ty, ~same, ks, bs) == Some{x}: Maybe<&2, Ty>}
  -> {Quorum.has(~Ty, ~same, bs, x) == True{}: Bool}:
  match ks:
    case Nil{}:
      h => Empty.absurd(
        {Quorum.has(~Ty, ~same, bs, x) == True{}: Bool},
        Shared.Maybe.none_ne_some(Ty, x, h)
      )
    case Con{k, +r}:
      Quorum.has_winner.at(
        ~Ty,
        ~same,
        k,
        Quorum.winner(~Ty, ~same, r, bs),
        bs,
        x,
        Quorum.has_winner(~Ty, ~same, r, bs, x)
      )

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# the scan goes past a vote b without a majority: b is not x (c)
def Quorum.scan.past(
  ~B: Data,
  ~same: B -> B -> Bool,
  ~laws: Shared.Eq.Laws(B, same),
  c: Bool,
  +b: B,
  bs: List<&2, Maybe<&2, B>>,
  x: B,
  yr: Nat,
  ec: {same(b, x) == c: Bool},
  eb: {Quorum.has(~B, ~same, bs, b) == False{}: Bool},
  hx: {Quorum.has(~B, ~same, bs, x) == True{}: Bool},
  pos: {Nat.is_lt(0n, Shared.Nat.add_if(c, yr)) == True{}: Bool}
) -> {Nat.is_lt(0n, yr) == True{}: Bool}:
  match c:
    case True{}:
      has1 = Quorum.has(~B, ~same, bs, b)
      Empty.absurd({Nat.is_lt(0n, yr) == True{}: Bool}, Shared.Bool.false_ne_true(Equal.trans(
            Bool,
            False{},
            has1,
            True{},
            Equal.sym(Bool, has1, False{}, eb),
            %Equal.sym(B, b, x, Shared.Eq.sound(~B, ~same, laws, b)(x)(ec)):
              {Quorum.has(~B, ~same, bs, _) == True{}: Bool}
            hx)))
    case False{}:
      pos
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# Quorum.scan at a vote b, picked or not (held)
def Quorum.scan.if(
  ~B: Data,
  ~same: B -> B -> Bool,
  ~laws: Shared.Eq.Laws(B, same),
  held: Bool,
  +b: B,
  rest: Maybe<&2, B>,
  bs: List<&2, Maybe<&2, B>>,
  +x: B,
  yr: Nat,
  eb: {Quorum.has(~B, ~same, bs, b) == held: Bool},
  hx: {Quorum.has(~B, ~same, bs, x) == True{}: Bool},
  pos: {Nat.is_lt(0n, Shared.Nat.add_if(same(b, x), yr)) == True{}: Bool},
  ih: {Nat.is_lt(0n, yr) == True{}: Bool} -> {rest == Some{x}: Maybe<&2, B>}
) -> {Bool.pick(Maybe<&2, B>, held, Some{b}, rest) == Some{x}: Maybe<&2, B>}:
  match held:
    case True{}:
      %Quorum.unique(~B, ~same, ~laws, bs, b, x)(eb)(hx): {Some{b} == Some{_}: Maybe<&2, B>}
      {==}
    case False{}:
      ih(Quorum.scan.past(~B, ~same, ~laws, same(b, x), b, bs, x, yr, {==}, eb, hx, pos))

# Quorum.scan at the ballot v, with rest the winner after it
def Quorum.scan.at(
  ~B: Data,
  ~same: B -> B -> Bool,
  ~laws: Shared.Eq.Laws(B, same),
  v: Maybe<&2, B>,
  rest: Maybe<&2, B>,
  +bs: List<&2, Maybe<&2, B>>,
  x: B,
  yr: Nat,
  hx: {Quorum.has(~B, ~same, bs, x) == True{}: Bool},
  pos: {Nat.is_lt(0n, Shared.Nat.add_if(Quorum.hit(~B, ~same, v, x), yr)) == True{}: Bool},
  ih: {Nat.is_lt(0n, yr) == True{}: Bool} -> {rest == Some{x}: Maybe<&2, B>}
) -> {Quorum.winner.at(~B, ~same, v, rest, bs) == Some{x}: Maybe<&2, B>}:
  match v:
    case Some{+b}:
      Quorum.scan.if(
        ~B,
        ~same,
        ~laws,
        Quorum.has(~B, ~same, bs, b),
        b,
        rest,
        bs,
        x,
        yr,
        {==},
        hx,
        pos,
        ih
      )
    case None{}:
      ih(pos)

# a scan of ballots of which some are for x finds x, when x has a majority
def Quorum.scan(
  ~B: Data,
  ~same: B -> B -> Bool,
  ~laws: Shared.Eq.Laws(B, same),
  ks: List<&2, Maybe<&2, B>>,
  +bs: List<&2, Maybe<&2, B>>,
  +x: B,
  +hx: {Quorum.has(~B, ~same, bs, x) == True{}: Bool}
) -> {
  Nat.is_lt(0n, Quorum.yes(~B, ~same, ks, x)) == True{}: Bool
} -> {Quorum.winner(~B, ~same, ks, bs) == Some{x}: Maybe<&2, B>}:
  match ks:
    case Nil{}:
      pos => Empty.absurd({None{} == Some{x}: Maybe<&2, B>}, Shared.Bool.false_ne_true(pos))
    case Con{k, +r}:
      pos => Quorum.scan.at(
        ~B,
        ~same,
        ~laws,
        k,
        Quorum.winner(~B, ~same, r, bs),
        bs,
        x,
        Quorum.yes(~B, ~same, r, x),
        hx,
        pos,
        Quorum.scan(~B, ~same, ~laws, r, bs, x, hx)
      )

# a choice with a majority is the winner
def Quorum.winner_of(
  ~Ty: Data,
  ~same: Ty -> Ty -> Bool,
  ~laws: Shared.Eq.Laws(Ty, same),
  +bs: List<&2, Maybe<&2, Ty>>,
  +x: Ty
) -> {Quorum.has(~Ty, ~same, bs, x) == True{}: Bool}
  -> {Quorum.winner(~Ty, ~same, bs, bs) == Some{x}: Maybe<&2, Ty>}:
  +hx =>
    Quorum.scan(
      ~Ty,
      ~same,
      ~laws,
      bs,
      bs,
      x,
      hx
    )(Shared.Nat.lt_pos(Quorum.no(~Ty, ~same, bs, x), Quorum.yes(~Ty, ~same, bs, x))(hx))

# One pass
# --------
# Quorum.winner tries each ballot against all: n^2 for n owners. A pass in the
# manner of Boyer and Moore keeps one candidate and a count: a ballot for it
# raises the count, any other ballot lowers it, and a ballot for another vote
# takes over a count of zero. A choice with a majority is the candidate at the
# end, so one more count tells whether it won (Quorum.winner_fast_eq).

# the candidate of p, when it has a majority of bs
def Quorum.winner_fast.of(
  ~B: Data,
  ~same: B -> B -> Bool,
  bs: List<&2, Maybe<&2, B>>,
  p: Pass<B>
) -> Maybe<&2, B>:
  match p:
    case Pass{Some{+y}, k}:
      Bool.pick(Maybe<&2, B>, Quorum.has(~B, ~same, bs, y), Some{y}, None{})
    case Pass{None{}, k}:
      None{}

# the vote with a majority of bs, if any, in one pass and one count
def Quorum.winner_fast(
  ~B: Data,
  ~same: B -> B -> Bool,
  +bs: List<&2, Maybe<&2, B>>
) -> Maybe<&2, B>:
  Quorum.winner_fast.of(~B, ~same, bs, Quorum.pass(~B, ~same, bs))

# The pass's bound
# ----------------
# Of a choice x, a pass with q ballots for it and r against keeps a bound: q
# is at most r plus the count when the candidate is x, and q plus the count is
# at most r when not.

# the candidate c is x
def Quorum.is_cand(~B: Data, ~same: B -> B -> Bool, c: Maybe<&2, B>, x: B) -> Bool:
  match c:
    case Some{a}:
      same(a, x)
    case None{}:
      False{}

# the bound for a count k, q ballots for x and r against, when the candidate
# is x (h) or not
def Quorum.bound(h: Bool, k: Nat, q: Nat, r: Nat) -> Bool:
  match h:
    case True{}:
      Nat.is_le(q, Nat.add(k, r))
    case False{}:
      Nat.is_le(Nat.add(k, q), r)

# the bound of the pass p
def Quorum.inv(~B: Data, ~same: B -> B -> Bool, x: B, p: Pass<B>, q: Nat, r: Nat) -> Bool:
  match p:
    case Pass{c, k}:
      Quorum.bound(Quorum.is_cand(~B, ~same, c, x), k, q, r)

# a bound with no count: q is at most r
def Quorum.bound_zero(
  h: Bool,
  q: Nat,
  r: Nat
) -> {Quorum.bound(h, 0n, q, r) == True{}: Bool} -> {Nat.is_le(q, r) == True{}: Bool}:
  match h:
    case True{}:
      e => e
    case False{}:
      e => e

# one more than a is at most r: a is at most one more than r
def Quorum.le_down(
  +a: Nat,
  +r: Nat
) -> {Nat.is_le(1n+a, r) == True{}: Bool} -> {Nat.is_le(a, 1n+r) == True{}: Bool}:
  e => Shared.Nat.le_succ(
    a,
    r
  )(Shared.Nat.le_trans(a, 1n+a, r)(Shared.Nat.le_succ(a, a)(Shared.Nat.le_refl(a)))(e))

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# a bound kept when the count falls by one and the ballot is against x
def Quorum.bound_fall(
  h: Bool,
  j: Nat,
  q: Nat,
  r: Nat
) -> {Quorum.bound(h, 1n+j, q, r) == True{}: Bool} -> {Quorum.bound(h, j, q, 1n+r) == True{}: Bool}:
  match h:
    case True{}:
      e =>
        %Equal.sym(
          Nat,
          Nat.add(j, 1n+r),
          1n+Nat.add(j, r),
          Shared.Nat.add_succ(j, r)
        ): {Nat.is_le(q, _) == True{}: Bool}
        e
    case False{}:
      e => Quorum.le_down(Nat.add(j, q), r)(e)

# a bound kept when the count falls by one and the ballot is for x, whose
# candidate is not x
def Quorum.bound_fall_for(
  j: Nat,
  q: Nat,
  r: Nat
) -> {
  Quorum.bound(False{}, 1n+j, q, r) == True{}: Bool
} -> {Quorum.bound(False{}, j, 1n+q, r) == True{}: Bool}:
  e =>
    %Equal.sym(
      Nat,
      Nat.add(j, 1n+q),
      1n+Nat.add(j, q),
      Shared.Nat.add_succ(j, q)
    ): {Nat.is_le(_, r) == True{}: Bool}
    e

# the bound after the first vote b, of a count of zero, once same(b, x) is
# known (hb)
def Quorum.step_inv.first.at(
  hb: Bool,
  q: Nat,
  r: Nat
) -> {
  Nat.is_le(q, r) == True{}: Bool
} -> {
  Quorum.bound(hb, 1n, Shared.Nat.add_if(hb, q), Shared.Nat.add_if(Bool.not(hb), r)) == True{}: Bool
}:
  match hb:
    case True{}:
      e => e
    case False{}:
      e => e

# the bound after the first vote b, of a count of zero
def Quorum.step_inv.first(
  ~B: Data,
  ~same: B -> B -> Bool,
  x: B,
  b: B,
  q: Nat,
  r: Nat,
  hb: Bool,
  ehb: {same(b, x) == hb: Bool}
) -> {
  Nat.is_le(q, r) == True{}: Bool
} -> {
  Quorum.inv(
    ~B,
    ~same,
    x,
    Pass{Some{b}, 1n},
    Shared.Nat.add_if(same(b, x), q),
    Shared.Nat.add_if(Bool.not(same(b, x)), r)
  )
    == True{}: Bool
}:
  %Equal.sym(Bool, same(b, x), hb, ehb):
    {Nat.is_le(q, r) == True{}: Bool}
      -> {
        Quorum.bound(
          _,
          1n,
          Shared.Nat.add_if(_, q),
          Shared.Nat.add_if(Bool.not(_), r)
        )
          == True{}: Bool
      }
  Quorum.step_inv.first.at(hb, q, r)

# the bound after a vote b against no candidate, from a count 1 + j, once
# same(b, x) is known (hb)
def Quorum.step_inv.none.at(
  hb: Bool,
  j: Nat,
  q: Nat,
  r: Nat
) -> {
  Quorum.bound(False{}, 1n+j, q, r) == True{}: Bool
} -> {
  Quorum.bound(
    False{},
    j,
    Shared.Nat.add_if(hb, q),
    Shared.Nat.add_if(Bool.not(hb), r)
  )
    == True{}: Bool
}:
  match hb:
    case True{}:
      Quorum.bound_fall_for(j, q, r)
    case False{}:
      Quorum.bound_fall(False{}, j, q, r)

# the bound after a vote b against no candidate, from a count 1 + j
def Quorum.step_inv.none(
  ~B: Data,
  ~same: B -> B -> Bool,
  x: B,
  b: B,
  j: Nat,
  q: Nat,
  r: Nat,
  hb: Bool,
  ehb: {same(b, x) == hb: Bool}
) -> {
  Quorum.bound(False{}, 1n+j, q, r) == True{}: Bool
} -> {
  Quorum.inv(
    ~B,
    ~same,
    x,
    Pass{None{}, j},
    Shared.Nat.add_if(same(b, x), q),
    Shared.Nat.add_if(Bool.not(same(b, x)), r)
  )
    == True{}: Bool
}:
  %Equal.sym(Bool, same(b, x), hb, ehb):
    {Quorum.bound(False{}, 1n+j, q, r) == True{}: Bool}
      -> {
        Quorum.bound(
          False{},
          j,
          Shared.Nat.add_if(_, q),
          Shared.Nat.add_if(Bool.not(_), r)
        )
          == True{}: Bool
      }
  Quorum.step_inv.none.at(hb, j, q, r)

# the bound after a ballot that is not a vote, of a count of zero
def Quorum.step_inv.idle(
  h: Bool,
  q: Nat,
  r: Nat
) -> {Nat.is_le(q, r) == True{}: Bool} -> {Quorum.bound(h, 0n, q, 1n+r) == True{}: Bool}:
  match h:
    case True{}:
      e => Shared.Nat.le_succ(q, r)(e)
    case False{}:
      e => Shared.Nat.le_succ(q, r)(e)

# the bound after a vote b, from a count 1 + j, once same(a, b) (sab), same(a,
# x) (hax) and same(b, x) (hb) are known
def Quorum.step_inv.vote(
  ~B: Data,
  ~same: B -> B -> Bool,
  ~laws: Shared.Eq.Laws(B, same),
  +x: B,
  a: B,
  b: B,
  j: Nat,
  q: Nat,
  r: Nat,
  sab: Bool,
  hax: Bool,
  hb: Bool,
  esab: {same(a, b) == sab: Bool},
  ehax: {same(a, x) == hax: Bool},
  ehb: {same(b, x) == hb: Bool}
) -> {
  Quorum.bound(hax, 1n+j, q, r) == True{}: Bool
} -> {
  Quorum.inv(
    ~B,
    ~same,
    x,
    Bool.pick(Pass<B>, sab, Pass{Some{a}, 2n+j}, Pass{Some{a}, j}),
    Shared.Nat.add_if(hb, q),
    Shared.Nat.add_if(Bool.not(hb), r)
  )
    == True{}: Bool
}:
  match sab hax hb:
    case True{} True{} True{}:
      e =>
        %Equal.sym(Bool, same(a, x), True{}, ehax): {Quorum.bound(_, 2n+j, 1n+q, r) == True{}: Bool}
        e
    case True{} False{} False{}:
      e =>
        %Equal.sym(
          Bool,
          same(a, x),
          False{},
          ehax
        ): {Quorum.bound(_, 2n+j, q, 1n+r) == True{}: Bool}
        e
    case True{} True{} False{}:
      e => Empty.absurd(
        {Quorum.inv(~B, ~same, x, Pass{Some{a}, 2n+j}, q, 1n+r) == True{}: Bool},
        Shared.Bool.false_ne_true(
          Equal.trans(
            Bool,
            False{},
            same(b, x),
            True{},
            Equal.sym(Bool, same(b, x), False{}, ehb),
            Equal.trans(
              Bool,
              same(b, x),
              same(a, x),
              True{},
              Equal.sym(
                Bool,
                same(a, x),
                same(b, x),
                Equal.cong(
                  B,
                  Bool,
                  z => same(z, x),
                  a,
                  b,
                  Shared.Eq.sound(~B, ~same, laws, a, b)(esab)
                )
              ),
              ehax
            )
          )
        )
      )
    case True{} False{} True{}:
      e => Empty.absurd(
        {Quorum.inv(~B, ~same, x, Pass{Some{a}, 2n+j}, 1n+q, r) == True{}: Bool},
        Shared.Bool.false_ne_true(
          Equal.trans(
            Bool,
            False{},
            same(a, x),
            True{},
            Equal.sym(Bool, same(a, x), False{}, ehax),
            Equal.trans(
              Bool,
              same(a, x),
              same(b, x),
              True{},
              Equal.cong(
                B,
                Bool,
                z => same(z, x),
                a,
                b,
                Shared.Eq.sound(~B, ~same, laws, a, b)(esab)
              ),
              ehb
            )
          )
        )
      )
    case False{} True{} True{}:
      e => Empty.absurd(
        {Quorum.inv(~B, ~same, x, Pass{Some{a}, j}, 1n+q, r) == True{}: Bool},
        Shared.Bool.false_ne_true(
          Equal.trans(
            Bool,
            False{},
            same(a, b),
            True{},
            Equal.sym(Bool, same(a, b), False{}, esab),
            Equal.trans(
              Bool,
              same(a, b),
              same(x, b),
              True{},
              Equal.cong(
                B,
                Bool,
                z => same(z, b),
                a,
                x,
                Shared.Eq.sound(~B, ~same, laws, a, x)(ehax)
              ),
              Equal.trans(
                Bool,
                same(x, b),
                same(x, x),
                True{},
                Equal.cong(
                  B,
                  Bool,
                  z => same(x, z),
                  b,
                  x,
                  Shared.Eq.sound(~B, ~same, laws, b, x)(ehb)
                ),
                Shared.Eq.refl(~B, ~same, laws, x)
              )
            )
          )
        )
      )
    case False{} True{} False{}:
      e =>
        %Equal.sym(Bool, same(a, x), True{}, ehax): {Quorum.bound(_, j, q, 1n+r) == True{}: Bool}
        Quorum.bound_fall(True{}, j, q, r)(e)
    case False{} False{} True{}:
      e =>
        %Equal.sym(Bool, same(a, x), False{}, ehax): {Quorum.bound(_, j, 1n+q, r) == True{}: Bool}
        Quorum.bound_fall_for(j, q, r)(e)
    case False{} False{} False{}:
      e =>
        %Equal.sym(Bool, same(a, x), False{}, ehax): {Quorum.bound(_, j, q, 1n+r) == True{}: Bool}
        Quorum.bound_fall(False{}, j, q, r)(e)

# the bound after a ballot v, from the candidate c and the count k
def Quorum.step_inv(
  ~B: Data,
  ~same: B -> B -> Bool,
  ~laws: Shared.Eq.Laws(B, same),
  +x: B,
  v: Maybe<&2, B>,
  +c: Maybe<&2, B>,
  k: Nat,
  +q: Nat,
  +r: Nat
) -> {
  Quorum.inv(~B, ~same, x, Pass{c, k}, q, r) == True{}: Bool
} -> {
  Quorum.inv(
    ~B,
    ~same,
    x,
    Quorum.step(~B, ~same, v, Pass{c, k}),
    Shared.Nat.add_if(Quorum.hit(~B, ~same, v, x), q),
    Shared.Nat.add_if(Bool.not(Quorum.hit(~B, ~same, v, x)), r)
  )
    == True{}: Bool
}:
  match v c k:
    case Some{+b} w 0n:
      e => Quorum.step_inv.first(
        ~B,
        ~same,
        x,
        b,
        q,
        r,
        same(b, x),
        {==}
      )(Quorum.bound_zero(Quorum.is_cand(~B, ~same, w, x), q, r)(e))
    case Some{+b} Some{+a} 1n+j:
      Quorum.step_inv.vote(
        ~B,
        ~same,
        ~laws,
        x,
        a,
        b,
        j,
        q,
        r,
        same(a, b),
        same(a, x),
        same(b, x),
        {==},
        {==},
        {==}
      )
    case Some{+b} None{} 1n+j:
      Quorum.step_inv.none(~B, ~same, x, b, j, q, r, same(b, x), {==})
    case None{} w 0n:
      e => Quorum.step_inv.idle(
        Quorum.is_cand(~B, ~same, w, x),
        q,
        r
      )(Quorum.bound_zero(Quorum.is_cand(~B, ~same, w, x), q, r)(e))
    case None{} w 1n+j:
      Quorum.bound_fall(Quorum.is_cand(~B, ~same, w, x), j, q, r)
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# the bound after the ballot v, from the pass p
def Quorum.pass_inv.at(
  ~B: Data,
  ~same: B -> B -> Bool,
  ~laws: Shared.Eq.Laws(B, same),
  x: B,
  v: Maybe<&2, B>,
  p: Pass<B>,
  q: Nat,
  r: Nat
) -> {
  Quorum.inv(~B, ~same, x, p, q, r) == True{}: Bool
} -> {
  Quorum.inv(
    ~B,
    ~same,
    x,
    Quorum.step(~B, ~same, v, p),
    Shared.Nat.add_if(Quorum.hit(~B, ~same, v, x), q),
    Shared.Nat.add_if(Bool.not(Quorum.hit(~B, ~same, v, x)), r)
  )
    == True{}: Bool
}:
  match p:
    case Pass{c, k}:
      Quorum.step_inv(~B, ~same, ~laws, x, v, c, k, q, r)

# the bound holds after the pass over bs, with the ballots of bs for x and
# against it
def Quorum.pass_inv(
  ~B: Data,
  ~same: B -> B -> Bool,
  ~laws: Shared.Eq.Laws(B, same),
  +x: B,
  bs: List<&2, Maybe<&2, B>>
) -> {
  Quorum.inv(
    ~B,
    ~same,
    x,
    Quorum.pass(~B, ~same, bs),
    Quorum.yes(~B, ~same, bs, x),
    Quorum.no(~B, ~same, bs, x)
  )
    == True{}: Bool
}:
  match bs:
    case Nil{}:
      {==}
    case Con{v, +r}:
      Quorum.pass_inv.at(
        ~B,
        ~same,
        ~laws,
        x,
        v,
        Quorum.pass(~B, ~same, r),
        Quorum.yes(~B, ~same, r, x),
        Quorum.no(~B, ~same, r, x)
      )(Quorum.pass_inv(~B, ~same, ~laws, x, r))

# a bound for a choice that is not the candidate leaves it no majority
def Quorum.bound_no_has(
  +k: Nat,
  +q: Nat,
  +r: Nat
) -> {Quorum.bound(False{}, k, q, r) == True{}: Bool} -> {Nat.is_lt(r, q) == True{}: Bool} -> Empty:
  e => h => Shared.Bool.false_ne_true(
    Equal.trans(
      Bool,
      False{},
      Nat.is_lt(q, q),
      True{},
      Equal.sym(Bool, Nat.is_lt(q, q), False{}, Shared.Nat.lt_irrefl(q)),
      Shared.Nat.le_lt(
        q,
        r,
        q
      )(
        Shared.Nat.le_trans(
          q,
          Nat.add(k, q),
          r
        )(Shared.Nat.add_le_right(k, 0n, q)(Shared.Nat.le_zero(k)))(e)
      )(h)
    )
  )

# the candidate c of a pass, of a choice x with a majority, once whether it
# is x is known (h)
def Quorum.cand_of.at(
  h: Bool,
  k: Nat,
  q: Nat,
  r: Nat
) -> {
  Quorum.bound(h, k, q, r) == True{}: Bool
} -> {Nat.is_lt(r, q) == True{}: Bool} -> {h == True{}: Bool}:
  match h:
    case True{}:
      e => g => {==}
    case False{}:
      e => g => Empty.absurd({False{} == True{}: Bool}, Quorum.bound_no_has(k, q, r)(e)(g))

# a choice with a majority is the candidate of the pass p, whose bound holds
def Quorum.cand_of(
  ~B: Data,
  ~same: B -> B -> Bool,
  x: B,
  p: Pass<B>,
  q: Nat,
  r: Nat
) -> {
  Quorum.inv(~B, ~same, x, p, q, r) == True{}: Bool
} -> {
  Nat.is_lt(r, q) == True{}: Bool
} -> {Quorum.is_cand(~B, ~same, Pass.cand(B, p), x) == True{}: Bool}:
  match p:
    case Pass{c, k}:
      Quorum.cand_of.at(Quorum.is_cand(~B, ~same, c, x), k, q, r)

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# a choice x with a majority of bs is the candidate of their pass, p
def Quorum.cand_is(
  ~B: Data,
  ~same: B -> B -> Bool,
  ~laws: Shared.Eq.Laws(B, same),
  +bs: List<&2, Maybe<&2, B>>,
  +x: B,
  p: Pass<B>,
  ep: {Quorum.pass(~B, ~same, bs) == p: Pass<B>}
) -> {
  Quorum.has(~B, ~same, bs, x) == True{}: Bool
} -> {Quorum.is_cand(~B, ~same, Pass.cand(B, p), x) == True{}: Bool}:
  hx => Equal.trans(
    Bool,
    Quorum.is_cand(~B, ~same, Pass.cand(B, p), x),
    Quorum.is_cand(~B, ~same, Pass.cand(B, Quorum.pass(~B, ~same, bs)), x),
    True{},
    Equal.cong(
      Pass<B>,
      Bool,
      z => Quorum.is_cand(~B, ~same, Pass.cand(B, z), x),
      p,
      Quorum.pass(~B, ~same, bs),
      Equal.sym(Pass<B>, Quorum.pass(~B, ~same, bs), p, ep)
    ),
    Quorum.cand_of(
      ~B,
      ~same,
      x,
      Quorum.pass(~B, ~same, bs),
      Quorum.yes(~B, ~same, bs, x),
      Quorum.no(~B, ~same, bs, x)
    )(Quorum.pass_inv(~B, ~same, ~laws, x, bs))(hx)
  )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# no winner, and the candidate y of the pass: no majority for y, once
# whether it has one is known (h)
def Quorum.winner_fast_eq.none(
  ~B: Data,
  ~same: B -> B -> Bool,
  ~laws: Shared.Eq.Laws(B, same),
  bs: List<&2, Maybe<&2, B>>,
  y: B,
  ew: {Quorum.winner(~B, ~same, bs, bs) == None{}: Maybe<&2, B>},
  h: Bool,
  eh: {Quorum.has(~B, ~same, bs, y) == h: Bool}
) -> {
  Bool.pick(Maybe<&2, B>, Quorum.has(~B, ~same, bs, y), Some{y}, None{}) == None{}: Maybe<&2, B>
}:
  match h:
    case True{}:
      Empty.absurd(
        {
          Bool.pick(
            Maybe<&2, B>,
            Quorum.has(~B, ~same, bs, y),
            Some{y},
            None{}
          )
            == None{}: Maybe<&2, B>
        },
        Shared.Maybe.none_ne_some(
          B,
          y,
          Equal.trans(
            Maybe<&2, B>,
            None{},
            Quorum.winner(~B, ~same, bs, bs),
            Some{y},
            Equal.sym(Maybe<&2, B>, Quorum.winner(~B, ~same, bs, bs), None{}, ew),
            Quorum.winner_of(~B, ~same, ~laws, bs, y)(eh)
          )
        )
      )
    case False{}:
      %Equal.sym(Bool, Quorum.has(~B, ~same, bs, y), False{}, eh):
        {Bool.pick(Maybe<&2, B>, _, Some{y}, None{}) == None{}: Maybe<&2, B>}
      {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# the fast winner of bs is the winner, once the winner w and the pass p are
# known
def Quorum.winner_fast_eq.at(
  ~B: Data,
  ~same: B -> B -> Bool,
  ~laws: Shared.Eq.Laws(B, same),
  +bs: List<&2, Maybe<&2, B>>,
  w: Maybe<&2, B>,
  ew: {Quorum.winner(~B, ~same, bs, bs) == w: Maybe<&2, B>},
  p: Pass<B>,
  ep: {Quorum.pass(~B, ~same, bs) == p: Pass<B>}
) -> {Quorum.winner_fast.of(~B, ~same, bs, p) == w: Maybe<&2, B>}:
  match w p:
    case Some{+x} Pass{Some{+y}, k}:
      +hx = Quorum.has_winner(~B, ~same, bs, bs, x)(ew)
      %Equal.sym(
        B,
        y,
        x,
        Shared.Eq.sound(
          ~B,
          ~same,
          laws,
          y,
          x
        )(Quorum.cand_is(~B, ~same, ~laws, bs, x, Pass{Some{y}, k}, ep)(hx))
      ):
        {
          Bool.pick(
            Maybe<&2, B>,
            Quorum.has(~B, ~same, bs, _),
            Some{_},
            None{}
          )
            == Some{x}: Maybe<&2, B>
        }
      %Equal.sym(Bool, Quorum.has(~B, ~same, bs, x), True{}, hx):
        {Bool.pick(Maybe<&2, B>, _, Some{x}, None{}) == Some{x}: Maybe<&2, B>}
      {==}
    case Some{+x} Pass{None{}, +k}:
      Empty.absurd(
        {None{} == Some{x}: Maybe<&2, B>},
        Shared.Bool.false_ne_true(
          Quorum.cand_is(
            ~B,
            ~same,
            ~laws,
            bs,
            x,
            Pass{None{}, k},
            ep
          )(Quorum.has_winner(~B, ~same, bs, bs, x)(ew))
        )
      )
    case None{} Pass{Some{+y}, k}:
      Quorum.winner_fast_eq.none(~B, ~same, ~laws, bs, y, ew, Quorum.has(~B, ~same, bs, y), {==})
    case None{} Pass{None{}, k}:
      {==}

# the fast winner of bs is the winner
def Quorum.winner_fast_eq(
  ~B: Data,
  ~same: B -> B -> Bool,
  ~laws: Shared.Eq.Laws(B, same),
  +bs: List<&2, Maybe<&2, B>>
) -> {Quorum.winner_fast(~B, ~same, bs) == Quorum.winner(~B, ~same, bs, bs): Maybe<&2, B>}:
  Quorum.winner_fast_eq.at(
    ~B,
    ~same,
    ~laws,
    bs,
    Quorum.winner(~B, ~same, bs, bs),
    {==},
    Quorum.pass(~B, ~same, bs),
    {==}
  )

# Majority
# --------
# A step is what a majority of the owners cast. Nothing else decides: a split
# decides nothing, and a later round does.

# the vote with a majority of bs, if any
def Quorum.major(
  ~B: Data,
  ~same: B -> B -> Bool,
  bs: List<&2, Maybe<&2, B>>
) -> Maybe<&2, B>:
  Quorum.winner_fast(~B, ~same, bs)

# a majority stays a majority when every ballot is kept
def Quorum.has_more(
  ~Ty: Data,
  ~same: Ty -> Ty -> Bool,
  ~laws: Shared.Eq.Laws(Ty, same),
  +bs: List<&2, Maybe<&2, Ty>>,
  +bs2: List<&2, Maybe<&2, Ty>>,
  +x: Ty
) -> {
  Shared.List.all2(
    ~Maybe<&2, Ty>,
    ~Maybe<&2, Ty>,
    ~Shared.Maybe.keeps(~Ty, ~same),
    bs,
    bs2
  )
    == True{}: Bool
}
  -> {Quorum.has(~Ty, ~same, bs, x) == True{}: Bool}
  -> {Quorum.has(~Ty, ~same, bs2, x) == True{}: Bool}:
  +k => h =>
    Shared.Nat.lt_le(
      Quorum.no(~Ty, ~same, bs2, x),
      Quorum.yes(~Ty, ~same, bs, x),
      Quorum.yes(~Ty, ~same, bs2, x)
    )(
      Shared.Nat.le_lt(
        Quorum.no(~Ty, ~same, bs2, x),
        Quorum.no(~Ty, ~same, bs, x),
        Quorum.yes(~Ty, ~same, bs, x)
      )(Quorum.no_less(~Ty, ~same, ~laws, bs, bs2, x)(k))(h)
    )(Quorum.yes_more(~Ty, ~same, ~laws, bs, bs2, x)(k))

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# what a majority cast has a majority
def Quorum.major_has(
  ~B: Data,
  ~same: B -> B -> Bool,
  ~laws: Shared.Eq.Laws(B, same),
  +bs: List<&2, Maybe<&2, B>>,
  x: B
) -> {Quorum.major(~B, ~same, bs) == Some{x}: Maybe<&2, B>}
  -> {Quorum.has(~B, ~same, bs, x) == True{}: Bool}:
  h =>
    Quorum.has_winner(
      ~B,
      ~same,
      bs,
      bs,
      x
    )(
      Equal.trans(
        Maybe<&2, B>,
        Quorum.winner(~B, ~same, bs, bs),
        Quorum.winner_fast(~B, ~same, bs),
        Some{x},
        Equal.sym(
          Maybe<&2, B>,
          Quorum.winner_fast(~B, ~same, bs),
          Quorum.winner(~B, ~same, bs, bs),
          Quorum.winner_fast_eq(~B, ~same, ~laws, bs)
        ),
        h
      )
    )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# what a majority cast stays so when every ballot is kept
law Quorum.major_kept:
  for ~B: Data
  for ~same: B -> B -> Bool
  for ~laws: Shared.Eq.Laws(B, same)
  Shared.Read.Stable(
    List<&2, Maybe<&2, B>>,
    bs => bs2 => {
      Shared.List.all2(
        ~Maybe<&2, B>,
        ~Maybe<&2, B>,
        ~Shared.Maybe.keeps(~B, ~same),
        bs,
        bs2
      )
        == True{}: Bool
    },
    B,
    bs => Quorum.major(~B, ~same, bs)
  )

def Quorum.major_kept(ty, same, laws):
  +bs => +bs2 => +x => k => h =>
    Equal.trans(
      Maybe<&2, ty>,
      Quorum.winner_fast(~ty, ~same, bs2),
      Quorum.winner(~ty, ~same, bs2, bs2),
      Some{x},
      Quorum.winner_fast_eq(~ty, ~same, ~laws, bs2),
      Quorum.winner_of(~ty, ~same, ~laws, bs2, x)(
        Quorum.has_more(~ty, ~same, ~laws, bs, bs2, x)(k)(Quorum.major_has(~ty, ~same, ~laws, bs, x)(h))
      )
    )
