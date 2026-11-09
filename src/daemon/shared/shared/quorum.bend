import Base
import ../../../shared.bend as Shared
import ./shared/cell.bend as Cells

# Quorums
# -------
# The owners of a decision each cast at most one ballot. A choice has a
# majority when more ballots are for it than are not. A bucket is decided by a
# majority; else, once every owner cast a ballot, by the choice with the most
# ballots (the first owner's, on a tie). A decision only gains information as
# ballots arrive, so it never changes (Quorum.decide_kept), and a split stops
# no line whose owners all vote.

# the ballot v is for x
def Quorum.hit(~B: Data, ~same: B -> B -> Bool, v: Maybe<&2, Cells.Cell<B>>, x: B) -> Bool:
  match v:
    case Some{Cells.One{b}}:
      same(b, x)
    case Some{Cells.Many{}}:
      False{}
    case None{}:
      False{}

# the number of ballots of bs for x
def Quorum.yes(
  ~B: Data,
  ~same: B -> B -> Bool,
  bs: List<&2, Maybe<&2, Cells.Cell<B>>>,
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
  bs: List<&2, Maybe<&2, Cells.Cell<B>>>,
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
  +bs: List<&2, Maybe<&2, Cells.Cell<B>>>,
  +x: B
) -> Bool:
  Nat.is_lt(Quorum.no(~B, ~same, bs, x), Quorum.yes(~B, ~same, bs, x))

# the vote of v when it has a majority of bs, else rest
def Quorum.winner.at(
  ~B: Data,
  ~same: B -> B -> Bool,
  v: Maybe<&2, Cells.Cell<B>>,
  rest: Maybe<&2, B>,
  bs: List<&2, Maybe<&2, Cells.Cell<B>>>
) -> Maybe<&2, B>:
  match v:
    case Some{Cells.One{+b}}:
      Bool.pick(Maybe<&2, B>, Quorum.has(~B, ~same, bs, b), Some{b}, rest)
    case Some{Cells.Many{}}:
      rest
    case None{}:
      rest

# the first vote of ks that has a majority of bs
def Quorum.winner(
  ~B: Data,
  ~same: B -> B -> Bool,
  ks: List<&2, Maybe<&2, Cells.Cell<B>>>,
  +bs: List<&2, Maybe<&2, Cells.Cell<B>>>
) -> Maybe<&2, B>:
  match ks:
    case Nil{}:
      None{}
    case Con{k, r}:
      Quorum.winner.at(~B, ~same, k, Quorum.winner(~B, ~same, r, bs), bs)

# every ballot of bs is cast
def Quorum.full(-B: Data, bs: List<&2, Maybe<&2, Cells.Cell<B>>>) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case Con{None{}, r}:
      False{}
    case Con{Some{v}, r}:
      Quorum.full(B, r)

# the vote of ks with the most ballots of bs, the first on a tie, after best
# with n ballots
def Quorum.most(
  ~B: Data,
  ~same: B -> B -> Bool,
  ks: List<&2, Maybe<&2, Cells.Cell<B>>>,
  +bs: List<&2, Maybe<&2, Cells.Cell<B>>>,
  best: Maybe<&2, B>,
  +n: Nat
) -> Maybe<&2, B>:
  match ks:
    case Nil{}:
      best
    case Con{Some{Cells.One{+b}}, +r}:
      +c = Quorum.yes(~B, ~same, bs, b)
      Shared.Bool.when(
        Maybe<&2, B>,
        Nat.is_lt(n, c),
        u => Quorum.most(~B, ~same, r, bs, Some{b}, c),
        u => Quorum.most(~B, ~same, r, bs, best, n)
      )
    case Con{Some{Cells.Many{}}, r}:
      Quorum.most(~B, ~same, r, bs, best, n)
    case Con{None{}, r}:
      Quorum.most(~B, ~same, r, bs, best, n)

# the decision of bs once the winner w is known: w; else, when every ballot is
# cast, the vote with the most ballots
def Quorum.decide.of(
  ~B: Data,
  ~same: B -> B -> Bool,
  w: Maybe<&2, B>,
  +bs: List<&2, Maybe<&2, Cells.Cell<B>>>
) -> Maybe<&2, B>:
  match w:
    case Some{x}:
      Some{x}
    case None{}:
      Shared.Bool.when(
        Maybe<&2, B>,
        Quorum.full(B, bs),
        u => Quorum.most(~B, ~same, bs, bs, None{}, 0n),
        u => None{}
      )

# what the ballots bs decide, if anything yet
def Quorum.decide(
  ~B: Data,
  ~same: B -> B -> Bool,
  +bs: List<&2, Maybe<&2, Cells.Cell<B>>>
) -> Maybe<&2, B>:
  Quorum.decide.of(~B, ~same, Quorum.winner(~B, ~same, bs, bs), bs)

# Laws
# ----
# Each law asks of same only its laws (Shared.Eq.Laws).

# a ballot for y is not for x, when x is not y
def Quorum.hit_excl(
  ~B: Data,
  ~same: B -> B -> Bool,
  ~laws: Shared.Eq.Laws(B, same),
  v: Maybe<&2, Cells.Cell<B>>,
  x: B,
  +y: B,
  no: {same(x, y) == False{}: Bool}
) -> {
  Quorum.hit(~B, ~same, v, y) == True{}: Bool
} -> {Quorum.hit(~B, ~same, v, x) == False{}: Bool}:
  match v:
    case Some{Cells.One{b}}:
      h =>
        %Equal.sym(
          B,
          b,
          y,
          Shared.Eq.sound(~B, ~same, laws, b)(y)(h)
        ): {same(_, x) == False{}: Bool}
        Shared.Eq.ne_flip(~B, ~same, ~laws, x, y, no)
    case Some{Cells.Many{}}:
      h => {==}
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
  bs: List<&2, Maybe<&2, Cells.Cell<B>>>,
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
  +bs: List<&2, Maybe<&2, Cells.Cell<B>>>,
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
  bs: List<&2, Maybe<&2, Cells.Cell<Ty>>>,
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
  v: Maybe<&2, Cells.Cell<B>>,
  w: Maybe<&2, Cells.Cell<B>>,
  x: B,
  y: Nat,
  y2: Nat,
  k: {Cells.Cell.keeps(~B, ~same, v, w) == True{}: Bool},
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
    case Some{Cells.Many{}} u:
      Shared.Nat.le_add_if(Quorum.hit(~B, ~same, u, x), y, y2)(ih)
    case Some{Cells.One{b}} None{}:
      Empty.absurd(
        {Nat.is_le(Shared.Nat.add_if(same(b, x), y), y2) == True{}: Bool},
        Shared.Bool.false_ne_true(k)
      )
    case Some{Cells.One{b}} Some{Cells.Many{}}:
      Empty.absurd(
        {Nat.is_le(Shared.Nat.add_if(same(b, x), y), y2) == True{}: Bool},
        Shared.Bool.false_ne_true(k)
      )
    case Some{Cells.One{+b}} Some{Cells.One{c}}:
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
  v: Maybe<&2, Cells.Cell<B>>,
  w: Maybe<&2, Cells.Cell<B>>,
  x: B,
  n: Nat,
  n2: Nat,
  k: {Cells.Cell.keeps(~B, ~same, v, w) == True{}: Bool},
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
    case Some{Cells.Many{}} u:
      Shared.Nat.add_if_le_succ(Bool.not(Quorum.hit(~B, ~same, u, x)), n2, n)(ih)
    case Some{Cells.One{b}} None{}:
      Empty.absurd(
        {Nat.is_le(1n+n2, Shared.Nat.add_if(Bool.not(same(b, x)), n)) == True{}: Bool},
        Shared.Bool.false_ne_true(k)
      )
    case Some{Cells.One{b}} Some{Cells.Many{}}:
      Empty.absurd(
        {Nat.is_le(1n+n2, Shared.Nat.add_if(Bool.not(same(b, x)), n)) == True{}: Bool},
        Shared.Bool.false_ne_true(k)
      )
    case Some{Cells.One{+b}} Some{Cells.One{c}}:
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
  bs: List<&2, Maybe<&2, Cells.Cell<B>>>,
  bs2: List<&2, Maybe<&2, Cells.Cell<B>>>,
  +x: B
) -> {
  Shared.List.all2(
    ~Maybe<&2, Cells.Cell<B>>,
    ~Maybe<&2, Cells.Cell<B>>,
    ~Cells.Cell.keeps(~B, ~same),
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
        +kh = Cells.Cell.keeps(~B, ~same, v, w)
        kr = Shared.List.all2(
          ~Maybe<&2, Cells.Cell<B>>,
          ~Maybe<&2, Cells.Cell<B>>,
          ~Cells.Cell.keeps(~B, ~same),
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
  bs: List<&2, Maybe<&2, Cells.Cell<B>>>,
  bs2: List<&2, Maybe<&2, Cells.Cell<B>>>,
  +x: B
) -> {
  Shared.List.all2(
    ~Maybe<&2, Cells.Cell<B>>,
    ~Maybe<&2, Cells.Cell<B>>,
    ~Cells.Cell.keeps(~B, ~same),
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
        +kh = Cells.Cell.keeps(~B, ~same, v, w)
        kr = Shared.List.all2(
          ~Maybe<&2, Cells.Cell<B>>,
          ~Maybe<&2, Cells.Cell<B>>,
          ~Cells.Cell.keeps(~B, ~same),
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

# a majority stays a majority when every ballot is kept
def Quorum.has_more(
  ~Ty: Data,
  ~same: Ty -> Ty -> Bool,
  ~laws: Shared.Eq.Laws(Ty, same),
  +bs: List<&2, Maybe<&2, Cells.Cell<Ty>>>,
  +bs2: List<&2, Maybe<&2, Cells.Cell<Ty>>>,
  +x: Ty
) -> {
  Shared.List.all2(
    ~Maybe<&2, Cells.Cell<Ty>>,
    ~Maybe<&2, Cells.Cell<Ty>>,
    ~Cells.Cell.keeps(~Ty, ~same),
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

# Quorum.has_winner when the vote b was picked or not (held)
def Quorum.has_winner.if(
  ~B: Data,
  ~same: B -> B -> Bool,
  held: Bool,
  b: B,
  rest: Maybe<&2, B>,
  bs: List<&2, Maybe<&2, Cells.Cell<B>>>,
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
  v: Maybe<&2, Cells.Cell<B>>,
  rest: Maybe<&2, B>,
  +bs: List<&2, Maybe<&2, Cells.Cell<B>>>,
  x: B,
  ih: {rest == Some{x}: Maybe<&2, B>} -> {Quorum.has(~B, ~same, bs, x) == True{}: Bool}
) -> {
  Quorum.winner.at(~B, ~same, v, rest, bs) == Some{x}: Maybe<&2, B>
} -> {Quorum.has(~B, ~same, bs, x) == True{}: Bool}:
  match v:
    case Some{Cells.One{+b}}:
      Quorum.has_winner.if(~B, ~same, Quorum.has(~B, ~same, bs, b), b, rest, bs, x, {==}, ih)
    case Some{Cells.Many{}}:
      ih
    case None{}:
      ih

# the winner has a majority
def Quorum.has_winner(
  ~Ty: Data,
  ~same: Ty -> Ty -> Bool,
  ks: List<&2, Maybe<&2, Cells.Cell<Ty>>>,
  +bs: List<&2, Maybe<&2, Cells.Cell<Ty>>>,
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
  bs: List<&2, Maybe<&2, Cells.Cell<B>>>,
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
  bs: List<&2, Maybe<&2, Cells.Cell<B>>>,
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
  v: Maybe<&2, Cells.Cell<B>>,
  rest: Maybe<&2, B>,
  +bs: List<&2, Maybe<&2, Cells.Cell<B>>>,
  x: B,
  yr: Nat,
  hx: {Quorum.has(~B, ~same, bs, x) == True{}: Bool},
  pos: {Nat.is_lt(0n, Shared.Nat.add_if(Quorum.hit(~B, ~same, v, x), yr)) == True{}: Bool},
  ih: {Nat.is_lt(0n, yr) == True{}: Bool} -> {rest == Some{x}: Maybe<&2, B>}
) -> {Quorum.winner.at(~B, ~same, v, rest, bs) == Some{x}: Maybe<&2, B>}:
  match v:
    case Some{Cells.One{+b}}:
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
    case Some{Cells.Many{}}:
      ih(pos)
    case None{}:
      ih(pos)

# a scan of ballots of which some are for x finds x, when x has a majority
def Quorum.scan(
  ~B: Data,
  ~same: B -> B -> Bool,
  ~laws: Shared.Eq.Laws(B, same),
  ks: List<&2, Maybe<&2, Cells.Cell<B>>>,
  +bs: List<&2, Maybe<&2, Cells.Cell<B>>>,
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
  +bs: List<&2, Maybe<&2, Cells.Cell<Ty>>>,
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

# a ballot kept from a cast one is the same ballot
def Quorum.cast_eq(
  ~B: Data,
  ~same: B -> B -> Bool,
  ~laws: Shared.Eq.Laws(B, same),
  c: Cells.Cell<B>,
  w: Maybe<&2, Cells.Cell<B>>
) -> {
  Cells.Cell.keeps(~B, ~same, Some{c}, w) == True{}: Bool
} -> {w == Some{c}: Maybe<&2, Cells.Cell<B>>}:
  match c w:
    case Cells.One{b} w:
      Cells.Cell.keeps_value(~B, ~same, ~laws, b, w)
    case Cells.Many{} Some{Cells.Many{}}:
      h => {==}
    case Cells.Many{} Some{Cells.One{x}}:
      h => Empty.absurd(
        {Some{Cells.One{x}} == Some{Cells.Many{}}: Maybe<&2, Cells.Cell<B>>},
        Shared.Bool.false_ne_true(h)
      )
    case Cells.Many{} None{}:
      h => Empty.absurd(
        {None{} == Some{Cells.Many{}}: Maybe<&2, Cells.Cell<B>>},
        Shared.Bool.false_ne_true(h)
      )

# once every ballot is cast, the ballots that keep them are the same ballots
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
def Quorum.full_keeps(
  ~Ty: Data,
  ~same: Ty -> Ty -> Bool,
  ~laws: Shared.Eq.Laws(Ty, same),
  bs: List<&2, Maybe<&2, Cells.Cell<Ty>>>,
  bs2: List<&2, Maybe<&2, Cells.Cell<Ty>>>
) -> {Quorum.full(Ty, bs) == True{}: Bool}
  -> {
    Shared.List.all2(
      ~Maybe<&2, Cells.Cell<Ty>>,
      ~Maybe<&2, Cells.Cell<Ty>>,
      ~Cells.Cell.keeps(~Ty, ~same),
      bs,
      bs2
    )
      == True{}: Bool
  }
  -> {bs2 == bs: List<&2, Maybe<&2, Cells.Cell<Ty>>>}:
  match bs bs2:
    case Nil{} Nil{}:
      f => k => {==}
    case Con{None{}, r} w:
      f => k => Empty.absurd(
        {w == None{} <> r: List<&2, Maybe<&2, Cells.Cell<Ty>>>},
        Shared.Bool.false_ne_true(f)
      )
    case Con{Some{+v}, +r} Con{+w, +r2}:
      f => +k =>
        +kh = Cells.Cell.keeps(~Ty, ~same, Some{v}, w)
        kr = Shared.List.all2(
          ~Maybe<&2, Cells.Cell<Ty>>,
          ~Maybe<&2, Cells.Cell<Ty>>,
          ~Cells.Cell.keeps(~Ty, ~same),
          r,
          r2
        )
        %Quorum.cast_eq(~Ty, ~same, ~laws, v, w)(Shared.Bool.and_true_left(kh, kr)(k)):
          {w <> r2 == _ <> r: List<&2, Maybe<&2, Cells.Cell<Ty>>>}
        %Quorum.full_keeps(~Ty, ~same, ~laws, r, r2)(f)(Shared.Bool.and_true_right(kh, kr)(k)):
          {w <> r2 == w <> _: List<&2, Maybe<&2, Cells.Cell<Ty>>>}
        {==}
    case Con{Some{v}, r} Nil{}:
      f => k => Empty.absurd(
        {[] == Some{v} <> r: List<&2, Maybe<&2, Cells.Cell<Ty>>>},
        Shared.Bool.false_ne_true(k)
      )
    case Nil{} Con{w, r2}:
      f => k => Empty.absurd(
        {w <> r2 == []: List<&2, Maybe<&2, Cells.Cell<Ty>>>},
        Shared.Bool.false_ne_true(k)
      )
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Quorum.decide_kept when no vote won, by whether every ballot is cast (f)
def Quorum.decide_kept.full(
  ~B: Data,
  ~same: B -> B -> Bool,
  ~laws: Shared.Eq.Laws(B, same),
  bs: List<&2, Maybe<&2, Cells.Cell<B>>>,
  bs2: List<&2, Maybe<&2, Cells.Cell<B>>>,
  -x: B,
  f: Bool,
  +ef: {Quorum.full(B, bs) == f: Bool},
  ew: {Quorum.winner(~B, ~same, bs, bs) == None{}: Maybe<&2, B>}
) -> {
  Shared.List.all2(
    ~Maybe<&2, Cells.Cell<B>>,
    ~Maybe<&2, Cells.Cell<B>>,
    ~Cells.Cell.keeps(~B, ~same),
    bs,
    bs2
  )
    == True{}: Bool
} -> {
  Shared.Bool.when(
    Maybe<&2, B>,
    f,
    u => Quorum.most(~B, ~same, bs, bs, None{}, 0n),
    u => None{}
  )
    == Some{x}: Maybe<&2, B>
} -> {Quorum.decide(~B, ~same, bs2) == Some{x}: Maybe<&2, B>}:
  match f:
    case True{}:
      k => h =>
        %Equal.sym(
          List<&2, Maybe<&2, Cells.Cell<B>>>,
          bs2,
          bs,
          Quorum.full_keeps(~B, ~same, ~laws, bs, bs2)(ef)(k)
        ): {Quorum.decide(~B, ~same, _) == Some{x}: Maybe<&2, B>}
        %Equal.sym(Maybe<&2, B>, Quorum.winner(~B, ~same, bs, bs), None{}, ew):
          {Quorum.decide.of(~B, ~same, _, bs) == Some{x}: Maybe<&2, B>}
        %Equal.sym(Bool, Quorum.full(B, bs), True{}, ef):
          {
            Shared.Bool.when(
              Maybe<&2, B>,
              _,
              u => Quorum.most(~B, ~same, bs, bs, None{}, 0n),
              u => None{}
            )
              == Some{x}: Maybe<&2, B>
          }
        h
    case False{}:
      k => h => Empty.absurd(
        {Quorum.decide(~B, ~same, bs2) == Some{x}: Maybe<&2, B>},
        Shared.Maybe.none_ne_some(B, x, h)
      )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# Quorum.decide_kept once the winner w of bs is known
def Quorum.decide_kept.at(
  ~B: Data,
  ~same: B -> B -> Bool,
  ~laws: Shared.Eq.Laws(B, same),
  +bs: List<&2, Maybe<&2, Cells.Cell<B>>>,
  +bs2: List<&2, Maybe<&2, Cells.Cell<B>>>,
  +x: B,
  w: Maybe<&2, B>,
  ew: {Quorum.winner(~B, ~same, bs, bs) == w: Maybe<&2, B>}
) -> {
  Shared.List.all2(
    ~Maybe<&2, Cells.Cell<B>>,
    ~Maybe<&2, Cells.Cell<B>>,
    ~Cells.Cell.keeps(~B, ~same),
    bs,
    bs2
  )
    == True{}: Bool
} -> {
  Quorum.decide.of(~B, ~same, w, bs) == Some{x}: Maybe<&2, B>
} -> {Quorum.decide(~B, ~same, bs2) == Some{x}: Maybe<&2, B>}:
  match w:
    case Some{y}:
      +k => h =>
        +hy = Quorum.has_winner(~B, ~same, bs, bs, y)(ew)
        %Equal.sym(
          Maybe<&2, B>,
          Quorum.winner(~B, ~same, bs2, bs2),
          Some{x},
          Quorum.winner_of(
            ~B,
            ~same,
            ~laws,
            bs2,
            x
          )(
            Quorum.has_more(
              ~B,
              ~same,
              ~laws,
              bs,
              bs2,
              x
            )(k)(%Shared.Maybe.some_inj(B, y, x, h): {Quorum.has(~B, ~same, bs, _) == True{}: Bool}
              hy)
          )
        ): {Quorum.decide.of(~B, ~same, _, bs2) == Some{x}: Maybe<&2, B>}
        {==}
    case None{}:
      Quorum.decide_kept.full(~B, ~same, ~laws, bs, bs2, x, Quorum.full(B, bs), {==}, ew)

# a decision stays when every ballot is kept: it is final
law Quorum.decide_kept:
  for ~B: Data
  for ~same: B -> B -> Bool
  for ~laws: Shared.Eq.Laws(B, same)
  for +bs: List<&2, Maybe<&2, Cells.Cell<B>>>
  for +bs2: List<&2, Maybe<&2, Cells.Cell<B>>>
  for +x: B
  {
    Shared.List.all2(
      ~Maybe<&2, Cells.Cell<B>>,
      ~Maybe<&2, Cells.Cell<B>>,
      ~Cells.Cell.keeps(~B, ~same),
      bs,
      bs2
    )
      == True{}: Bool
  }
    -> {Quorum.decide(~B, ~same, bs) == Some{x}: Maybe<&2, B>}
    -> {Quorum.decide(~B, ~same, bs2) == Some{x}: Maybe<&2, B>}

def Quorum.decide_kept(ty, same, laws, bs, bs2, x):
  Quorum.decide_kept.at(~ty, ~same, ~laws, bs, bs2, x, Quorum.winner(~ty, ~same, bs, bs), {==})

# a sole owner's vote decides
law Quorum.decide_one:
  for ~B: Data
  for ~same: B -> B -> Bool
  for ~laws: Shared.Eq.Laws(B, same)
  for +x: B
  {Quorum.decide(~B, ~same, [Some{Cells.One{x}}]) == Some{x}: Maybe<&2, B>}

def Quorum.decide_one(ty, same, laws, x):
  %Equal.sym(Bool, same(x, x), True{}, Shared.Eq.refl(~ty, ~same, laws, x)):
    {
      Quorum.decide.of(
        ~ty,
        ~same,
        Bool.pick(
          Maybe<&2, ty>,
          Nat.is_lt(Shared.Nat.add_if(Bool.not(_), 0n), Shared.Nat.add_if(_, 0n)),
          Some{x},
          None{}
        ),
        [Some{Cells.One{x}}]
      )
        == Some{x}: Maybe<&2, ty>
    }
  {==}
