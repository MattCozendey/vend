import Base
import ./bools.bend as Bools
import ./maybes.bend as Maybes
import ./nats.bend as Nats
import ./shared.bend as Shared

# Quorums
# -------
# Each member of a list ms votes for at most one choice, as vote(g)(m) says in
# the state g. A choice has a majority when more members vote for it than do
# not. A majority is unique, new votes keep it, and a scan of the members finds
# it: so a holder that learns more votes never sees a decided choice change.

# Votes
# -----

# the vote v is for x
def Quorum.hit(~B: Data, ~same: B -> B -> Bool, v: Maybe<&2, B>, +x: B) -> Bool:
  match v:
    case None{}:
      False{}
    case Some{b}:
      same(b, x)

# the number of members of ms that vote for x
def Quorum.yes(
  ~A: Data,
  ~B: Data,
  ~V: Data,
  ~vote: V -> A -> Maybe<&2, B>,
  ~same: B -> B -> Bool,
  ms: List<&2, A>,
  +g: V,
  +x: B
) -> Nat:
  match ms:
    case Nil{}:
      0n
    case Con{m, r}:
      Nats.Nat.add_if(Quorum.hit(~B, ~same, vote(g)(m), x), Quorum.yes(~A, ~B, ~V, ~vote, ~same, r, g, x))

# the number of members of ms that do not vote for x
def Quorum.no(
  ~A: Data,
  ~B: Data,
  ~V: Data,
  ~vote: V -> A -> Maybe<&2, B>,
  ~same: B -> B -> Bool,
  ms: List<&2, A>,
  +g: V,
  +x: B
) -> Nat:
  match ms:
    case Nil{}:
      0n
    case Con{m, r}:
      Nats.Nat.add_if(Bool.not(Quorum.hit(~B, ~same, vote(g)(m), x)), Quorum.no(~A, ~B, ~V, ~vote, ~same, r, g, x))

# x has a majority of ms: more of them vote for it than do not
def Quorum.has(
  ~A: Data,
  ~B: Data,
  ~V: Data,
  ~vote: V -> A -> Maybe<&2, B>,
  ~same: B -> B -> Bool,
  +ms: List<&2, A>,
  +g: V,
  +x: B
) -> Bool:
  Nat.is_lt(Quorum.no(~A, ~B, ~V, ~vote, ~same, ms, g, x), Quorum.yes(~A, ~B, ~V, ~vote, ~same, ms, g, x))

# b when it has a majority of ms (held), else rest
def Quorum.winner.if(-B: Data, held: Bool, b: B, rest: Maybe<&2, B>) -> Maybe<&2, B>:
  match held:
    case True{}:
      Some{b}
    case False{}:
      rest

# the vote v when it has a majority of ms, else rest
def Quorum.winner.at(
  ~A: Data,
  ~B: Data,
  ~V: Data,
  ~vote: V -> A -> Maybe<&2, B>,
  ~same: B -> B -> Bool,
  v: Maybe<&2, B>,
  rest: Maybe<&2, B>,
  +ms: List<&2, A>,
  +g: V
) -> Maybe<&2, B>:
  match v:
    case None{}:
      rest
    case Some{+b}:
      Quorum.winner.if(B, Quorum.has(~A, ~B, ~V, ~vote, ~same, ms, g, b), b, rest)

# the first vote of a member of ks that has a majority of ms
def Quorum.winner(
  ~A: Data,
  ~B: Data,
  ~V: Data,
  ~vote: V -> A -> Maybe<&2, B>,
  ~same: B -> B -> Bool,
  ks: List<&2, A>,
  +ms: List<&2, A>,
  +g: V
) -> Maybe<&2, B>:
  match ks:
    case Nil{}:
      None{}
    case Con{k, r}:
      Quorum.winner.at(
        ~A,
        ~B,
        ~V,
        ~vote,
        ~same,
        vote(g)(k),
        Quorum.winner(~A, ~B, ~V, ~vote, ~same, r, ms, g),
        ms,
        g
      )

# the vote v is kept in w: when v is for b, so is w
def Quorum.kept(~B: Data, ~same: B -> B -> Bool, v: Maybe<&2, B>, w: Maybe<&2, B>) -> Bool:
  match v:
    case None{}:
      True{}
    case Some{b}:
      Quorum.hit(~B, ~same, w, b)

# every vote of a member of ms in g is kept in g2
def Quorum.keeps(
  ~A: Data,
  ~B: Data,
  ~V: Data,
  ~vote: V -> A -> Maybe<&2, B>,
  ~same: B -> B -> Bool,
  ms: List<&2, A>,
  +g: V,
  +g2: V
) -> Bool:
  match ms:
    case Nil{}:
      True{}
    case Con{+m, r}:
      Bool.and(
        Quorum.kept(~B, ~same, vote(g)(m), vote(g2)(m)),
        Quorum.keeps(~A, ~B, ~V, ~vote, ~same, r, g, g2)
      )

# Laws
# ----
# Each law asks of same only that it is True for a value and itself (refl),
# and only for equal values (sound).

# x is not y, so y is not x
def Quorum.ne_flip.at(
  ~B: Data,
  ~same: B -> B -> Bool,
  ~refl: @x: B -> {same(x, x) == True{}: Bool},
  ~sound: @x: B -> @y: B -> {same(x, y) == True{}: Bool} -> {x == y: B},
  back: Bool,
  +x: B,
  +y: B,
  no: {same(x, y) == False{}: Bool},
  e: {same(y, x) == back: Bool}
) -> {back == False{}: Bool}:
  match back:
    case False{}:
      {==}
    case True{}:
      Empty.absurd(
        {True{} == False{}: Bool},
        Shared.Bool.false_ne_true(
          Equal.trans(
            Bool,
            False{},
            same(x, y),
            True{},
            Equal.sym(Bool, same(x, y), False{}, no),
            Equal.trans(
              Bool,
              same(x, y),
              same(x, x),
              True{},
              Equal.cong(B, Bool, z => same(x, z), y, x, sound(y)(x)(e)),
              refl(x)
            )
          )
        )
      )

# x is not y, so y is not x
def Quorum.ne_flip(
  ~B: Data,
  ~same: B -> B -> Bool,
  ~refl: @x: B -> {same(x, x) == True{}: Bool},
  ~sound: @x: B -> @y: B -> {same(x, y) == True{}: Bool} -> {x == y: B},
  +x: B,
  +y: B,
  no: {same(x, y) == False{}: Bool}
) -> {same(y, x) == False{}: Bool}:
  Quorum.ne_flip.at(~B, ~same, ~refl, ~sound, same(y, x), x, y, no, {==})

# a vote for y is not a vote for x, when x is not y
def Quorum.hit_excl(
  ~B: Data,
  ~same: B -> B -> Bool,
  ~refl: @x: B -> {same(x, x) == True{}: Bool},
  ~sound: @x: B -> @y: B -> {same(x, y) == True{}: Bool} -> {x == y: B},
  v: Maybe<&2, B>,
  +x: B,
  +y: B,
  no: {same(x, y) == False{}: Bool}
) -> {Quorum.hit(~B, ~same, v, y) == True{}: Bool} -> {Quorum.hit(~B, ~same, v, x) == False{}: Bool}:
  match v:
    case None{}:
      h => {==}
    case Some{+b}:
      h =>
        %Equal.sym(B, b, y, sound(b)(y)(h)) : {same(_, x) == False{}: Bool}
        Quorum.ne_flip(~B, ~same, ~refl, ~sound, x, y, no)

# Quorum.yes_le_no for one member, by whether it votes for y (hy) and x (hx)
def Quorum.yes_le_no.at(
  hy: Bool,
  hx: Bool,
  excl: {hy == True{}: Bool} -> {hx == False{}: Bool},
  y: Nat,
  n: Nat,
  ih: {Nat.is_le(y, n) == True{}: Bool}
) -> {Nat.is_le(Nats.Nat.add_if(hy, y), Nats.Nat.add_if(Bool.not(hx), n)) == True{}: Bool}:
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
      Nats.Nat.le_succ(y, n)(ih)

# no more members vote for y than do not vote for x, when x is not y
def Quorum.yes_le_no(
  ~A: Data,
  ~B: Data,
  ~V: Data,
  ~vote: V -> A -> Maybe<&2, B>,
  ~same: B -> B -> Bool,
  ~refl: @x: B -> {same(x, x) == True{}: Bool},
  ~sound: @x: B -> @y: B -> {same(x, y) == True{}: Bool} -> {x == y: B},
  ms: List<&2, A>,
  +g: V,
  +x: B,
  +y: B,
  +no: {same(x, y) == False{}: Bool}
) -> {
  Nat.is_le(
    Quorum.yes(~A, ~B, ~V, ~vote, ~same, ms, g, y),
    Quorum.no(~A, ~B, ~V, ~vote, ~same, ms, g, x)
  )
    == True{}: Bool
}:
  match ms:
    case Nil{}:
      {==}
    case Con{+m, +r}:
      Quorum.yes_le_no.at(
        Quorum.hit(~B, ~same, vote(g)(m), y),
        Quorum.hit(~B, ~same, vote(g)(m), x),
        Quorum.hit_excl(~B, ~same, ~refl, ~sound, vote(g)(m), x, y, no),
        Quorum.yes(~A, ~B, ~V, ~vote, ~same, r, g, y),
        Quorum.no(~A, ~B, ~V, ~vote, ~same, r, g, x),
        Quorum.yes_le_no(~A, ~B, ~V, ~vote, ~same, ~refl, ~sound, r, g, x, y, no)
      )

# Quorum.unique once same(x, y) is known (held)
def Quorum.unique.at(
  ~A: Data,
  ~B: Data,
  ~V: Data,
  ~vote: V -> A -> Maybe<&2, B>,
  ~same: B -> B -> Bool,
  ~refl: @x: B -> {same(x, x) == True{}: Bool},
  ~sound: @x: B -> @y: B -> {same(x, y) == True{}: Bool} -> {x == y: B},
  held: Bool,
  +ms: List<&2, A>,
  +g: V,
  +x: B,
  +y: B,
  +e: {same(x, y) == held: Bool},
  +hx: {Quorum.has(~A, ~B, ~V, ~vote, ~same, ms, g, x) == True{}: Bool},
  +hy: {Quorum.has(~A, ~B, ~V, ~vote, ~same, ms, g, y) == True{}: Bool}
) -> {x == y: B}:
  match held:
    case True{}:
      sound(x)(y)(e)
    case False{}:
      +yx = Quorum.yes(~A, ~B, ~V, ~vote, ~same, ms, g, x)
      +yy = Quorum.yes(~A, ~B, ~V, ~vote, ~same, ms, g, y)
      +nx = Quorum.no(~A, ~B, ~V, ~vote, ~same, ms, g, x)
      +ny = Quorum.no(~A, ~B, ~V, ~vote, ~same, ms, g, y)
      +a = Nats.Nat.le_lt(yx, ny, yy)(
        Quorum.yes_le_no(~A, ~B, ~V, ~vote, ~same, ~refl, ~sound, ms, g, y, x, Quorum.ne_flip(~B, ~same, ~refl, ~sound, x, y, e))
      )(hy)
      +b = Nats.Nat.lt_le(yx, yy, nx)(a)(Quorum.yes_le_no(~A, ~B, ~V, ~vote, ~same, ~refl, ~sound, ms, g, x, y, e))
      +c = Nats.Nat.lt_le(yx, nx, yx)(b)(Nats.Nat.lt_weak(nx, yx)(hx))
      Empty.absurd(
        {x == y: B},
        Shared.Bool.false_ne_true(Equal.trans(Bool, False{}, Nat.is_lt(yx, yx), True{}, Equal.sym(Bool, Nat.is_lt(yx, yx), False{}, Nats.Nat.lt_irrefl(yx)), c))
      )

# two choices with a majority of the same members are the same
law Quorum.unique:
  for ~A: Data
  for ~B: Data
  for ~V: Data
  for ~vote: V -> A -> Maybe<&2, B>
  for ~same: B -> B -> Bool
  for ~refl: @x: B -> {same(x, x) == True{}: Bool}
  for ~sound: @x: B -> @y: B -> {same(x, y) == True{}: Bool} -> {x == y: B}
  for ms: List<&2, A>
  for g: V
  for x: B
  for y: B
  {Quorum.has(~A, ~B, ~V, ~vote, ~same, ms, g, x) == True{}: Bool}
    -> {Quorum.has(~A, ~B, ~V, ~vote, ~same, ms, g, y) == True{}: Bool}
    -> {x == y: B}

def Quorum.unique(A, B, V, vote, same, refl, sound, ms, g, x, y):
  +ms = ms
  +g = g
  +x = x
  +y = y
  hx => hy => Quorum.unique.at(~A, ~B, ~V, ~vote, ~same, ~refl, ~sound, same(x, y), ms, g, x, y, {==}, hx, hy)

# Quorum.yes_more for one member, whose vote v in g is kept as w in g2
def Quorum.yes_more.at(
  ~B: Data,
  ~same: B -> B -> Bool,
  ~sound: @x: B -> @y: B -> {same(x, y) == True{}: Bool} -> {x == y: B},
  v: Maybe<&2, B>,
  w: Maybe<&2, B>,
  +x: B,
  y: Nat,
  y2: Nat,
  k: {Quorum.kept(~B, ~same, v, w) == True{}: Bool},
  ih: {Nat.is_le(y, y2) == True{}: Bool}
) -> {
  Nat.is_le(Nats.Nat.add_if(Quorum.hit(~B, ~same, v, x), y), Nats.Nat.add_if(Quorum.hit(~B, ~same, w, x), y2))
    == True{}: Bool
}:
  match v w:
    case None{} u:
      Nats.Nat.le_add_if(Quorum.hit(~B, ~same, u, x), y, y2)(ih)
    case Some{b} None{}:
      Empty.absurd(
        {Nat.is_le(Nats.Nat.add_if(same(b, x), y), y2) == True{}: Bool},
        Shared.Bool.false_ne_true(k)
      )
    case Some{+b} Some{+c}:
      %Equal.sym(B, c, b, sound(c)(b)(k)) :
        {Nat.is_le(Nats.Nat.add_if(same(b, x), y), Nats.Nat.add_if(same(_, x), y2)) == True{}: Bool}
      Nats.Nat.add_if_le(same(b, x), y, y2)(ih)

# Quorum.no_less for one member, whose vote v in g is kept as w in g2
def Quorum.no_less.at(
  ~B: Data,
  ~same: B -> B -> Bool,
  ~sound: @x: B -> @y: B -> {same(x, y) == True{}: Bool} -> {x == y: B},
  v: Maybe<&2, B>,
  w: Maybe<&2, B>,
  +x: B,
  n: Nat,
  n2: Nat,
  k: {Quorum.kept(~B, ~same, v, w) == True{}: Bool},
  ih: {Nat.is_le(n2, n) == True{}: Bool}
) -> {
  Nat.is_le(
    Nats.Nat.add_if(Bool.not(Quorum.hit(~B, ~same, w, x)), n2),
    Nats.Nat.add_if(Bool.not(Quorum.hit(~B, ~same, v, x)), n)
  )
    == True{}: Bool
}:
  match v w:
    case None{} u:
      Nats.Nat.add_if_le_succ(Bool.not(Quorum.hit(~B, ~same, u, x)), n2, n)(ih)
    case Some{b} None{}:
      Empty.absurd(
        {Nat.is_le(1n+n2, Nats.Nat.add_if(Bool.not(same(b, x)), n)) == True{}: Bool},
        Shared.Bool.false_ne_true(k)
      )
    case Some{+b} Some{+c}:
      %Equal.sym(B, c, b, sound(c)(b)(k)) :
        {
          Nat.is_le(Nats.Nat.add_if(Bool.not(same(_, x)), n2), Nats.Nat.add_if(Bool.not(same(b, x)), n))
            == True{}: Bool
        }
      Nats.Nat.add_if_le(Bool.not(same(b, x)), n2, n)(ih)

# kept votes keep the members that vote for x
def Quorum.yes_more(
  ~A: Data,
  ~B: Data,
  ~V: Data,
  ~vote: V -> A -> Maybe<&2, B>,
  ~same: B -> B -> Bool,
  ~sound: @x: B -> @y: B -> {same(x, y) == True{}: Bool} -> {x == y: B},
  ms: List<&2, A>,
  +g: V,
  +g2: V,
  +x: B,
  +k: {Quorum.keeps(~A, ~B, ~V, ~vote, ~same, ms, g, g2) == True{}: Bool}
) -> {
  Nat.is_le(
    Quorum.yes(~A, ~B, ~V, ~vote, ~same, ms, g, x),
    Quorum.yes(~A, ~B, ~V, ~vote, ~same, ms, g2, x)
  )
    == True{}: Bool
}:
  match ms:
    case Nil{}:
      {==}
    case Con{+m, +r}:
      +kh = Quorum.kept(~B, ~same, vote(g)(m), vote(g2)(m))
      +kr = Quorum.keeps(~A, ~B, ~V, ~vote, ~same, r, g, g2)
      Quorum.yes_more.at(
        ~B,
        ~same,
        ~sound,
        vote(g)(m),
        vote(g2)(m),
        x,
        Quorum.yes(~A, ~B, ~V, ~vote, ~same, r, g, x),
        Quorum.yes(~A, ~B, ~V, ~vote, ~same, r, g2, x),
        Bools.Bool.and_true_left(kh, kr)(k),
        Quorum.yes_more(~A, ~B, ~V, ~vote, ~same, ~sound, r, g, g2, x, Bools.Bool.and_true_right(kh, kr)(k))
      )

# kept votes keep the members that do not vote for x from growing
def Quorum.no_less(
  ~A: Data,
  ~B: Data,
  ~V: Data,
  ~vote: V -> A -> Maybe<&2, B>,
  ~same: B -> B -> Bool,
  ~sound: @x: B -> @y: B -> {same(x, y) == True{}: Bool} -> {x == y: B},
  ms: List<&2, A>,
  +g: V,
  +g2: V,
  +x: B,
  +k: {Quorum.keeps(~A, ~B, ~V, ~vote, ~same, ms, g, g2) == True{}: Bool}
) -> {
  Nat.is_le(
    Quorum.no(~A, ~B, ~V, ~vote, ~same, ms, g2, x),
    Quorum.no(~A, ~B, ~V, ~vote, ~same, ms, g, x)
  )
    == True{}: Bool
}:
  match ms:
    case Nil{}:
      {==}
    case Con{+m, +r}:
      +kh = Quorum.kept(~B, ~same, vote(g)(m), vote(g2)(m))
      +kr = Quorum.keeps(~A, ~B, ~V, ~vote, ~same, r, g, g2)
      Quorum.no_less.at(
        ~B,
        ~same,
        ~sound,
        vote(g)(m),
        vote(g2)(m),
        x,
        Quorum.no(~A, ~B, ~V, ~vote, ~same, r, g, x),
        Quorum.no(~A, ~B, ~V, ~vote, ~same, r, g2, x),
        Bools.Bool.and_true_left(kh, kr)(k),
        Quorum.no_less(~A, ~B, ~V, ~vote, ~same, ~sound, r, g, g2, x, Bools.Bool.and_true_right(kh, kr)(k))
      )

# a majority stays a majority when every vote is kept
law Quorum.has_more:
  for ~A: Data
  for ~B: Data
  for ~V: Data
  for ~vote: V -> A -> Maybe<&2, B>
  for ~same: B -> B -> Bool
  for ~sound: @x: B -> @y: B -> {same(x, y) == True{}: Bool} -> {x == y: B}
  for ms: List<&2, A>
  for g: V
  for g2: V
  for x: B
  {Quorum.keeps(~A, ~B, ~V, ~vote, ~same, ms, g, g2) == True{}: Bool}
    -> {Quorum.has(~A, ~B, ~V, ~vote, ~same, ms, g, x) == True{}: Bool}
    -> {Quorum.has(~A, ~B, ~V, ~vote, ~same, ms, g2, x) == True{}: Bool}

def Quorum.has_more(A, B, V, vote, same, sound, ms, g, g2, x):
  +ms = ms
  +g = g
  +g2 = g2
  +x = x
  +k => h =>
    Nats.Nat.lt_le(
      Quorum.no(~A, ~B, ~V, ~vote, ~same, ms, g2, x),
      Quorum.yes(~A, ~B, ~V, ~vote, ~same, ms, g, x),
      Quorum.yes(~A, ~B, ~V, ~vote, ~same, ms, g2, x)
    )(
      Nats.Nat.le_lt(
        Quorum.no(~A, ~B, ~V, ~vote, ~same, ms, g2, x),
        Quorum.no(~A, ~B, ~V, ~vote, ~same, ms, g, x),
        Quorum.yes(~A, ~B, ~V, ~vote, ~same, ms, g, x)
      )(Quorum.no_less(~A, ~B, ~V, ~vote, ~same, ~sound, ms, g, g2, x, k))(h)
    )(Quorum.yes_more(~A, ~B, ~V, ~vote, ~same, ~sound, ms, g, g2, x, k))

# Quorum.has_winner when the vote b was picked or not (held)
def Quorum.has_winner.if(
  ~A: Data,
  ~B: Data,
  ~V: Data,
  ~vote: V -> A -> Maybe<&2, B>,
  ~same: B -> B -> Bool,
  held: Bool,
  b: B,
  rest: Maybe<&2, B>,
  +ms: List<&2, A>,
  +g: V,
  +x: B,
  eb: {Quorum.has(~A, ~B, ~V, ~vote, ~same, ms, g, b) == held: Bool},
  ih: {rest == Some{x}: Maybe<&2, B>} -> {Quorum.has(~A, ~B, ~V, ~vote, ~same, ms, g, x) == True{}: Bool}
) -> {
  Quorum.winner.if(B, held, b, rest) == Some{x}: Maybe<&2, B>
} -> {Quorum.has(~A, ~B, ~V, ~vote, ~same, ms, g, x) == True{}: Bool}:
  match held:
    case True{}:
      h =>
        %Maybes.Maybe.some_inj(B, b, x, h) : {Quorum.has(~A, ~B, ~V, ~vote, ~same, ms, g, _) == True{}: Bool}
        eb
    case False{}:
      ih

# Quorum.has_winner at the vote v of a member, with rest the winner after it
def Quorum.has_winner.at(
  ~A: Data,
  ~B: Data,
  ~V: Data,
  ~vote: V -> A -> Maybe<&2, B>,
  ~same: B -> B -> Bool,
  v: Maybe<&2, B>,
  rest: Maybe<&2, B>,
  +ms: List<&2, A>,
  +g: V,
  +x: B,
  ih: {rest == Some{x}: Maybe<&2, B>} -> {Quorum.has(~A, ~B, ~V, ~vote, ~same, ms, g, x) == True{}: Bool}
) -> {
  Quorum.winner.at(~A, ~B, ~V, ~vote, ~same, v, rest, ms, g) == Some{x}: Maybe<&2, B>
} -> {Quorum.has(~A, ~B, ~V, ~vote, ~same, ms, g, x) == True{}: Bool}:
  match v:
    case None{}:
      ih
    case Some{+b}:
      Quorum.has_winner.if(
        ~A,
        ~B,
        ~V,
        ~vote,
        ~same,
        Quorum.has(~A, ~B, ~V, ~vote, ~same, ms, g, b),
        b,
        rest,
        ms,
        g,
        x,
        {==},
        ih
      )

# the winner has a majority
law Quorum.has_winner:
  for ~A: Data
  for ~B: Data
  for ~V: Data
  for ~vote: V -> A -> Maybe<&2, B>
  for ~same: B -> B -> Bool
  for ks: List<&2, A>
  for +ms: List<&2, A>
  for +g: V
  for +x: B
  {Quorum.winner(~A, ~B, ~V, ~vote, ~same, ks, ms, g) == Some{x}: Maybe<&2, B>}
    -> {Quorum.has(~A, ~B, ~V, ~vote, ~same, ms, g, x) == True{}: Bool}

def Quorum.has_winner(A, B, V, vote, same, ks, ms, g, x):
  match ks:
    case Nil{}:
      h => Empty.absurd(
        {Quorum.has(~A, ~B, ~V, ~vote, ~same, ms, g, x) == True{}: Bool},
        Maybes.Maybe.none_ne_some(B, x, h)
      )
    case Con{+k, +r}:
      Quorum.has_winner.at(
        ~A,
        ~B,
        ~V,
        ~vote,
        ~same,
        vote(g)(k),
        Quorum.winner(~A, ~B, ~V, ~vote, ~same, r, ms, g),
        ms,
        g,
        x,
        Quorum.has_winner(~A, ~B, ~V, ~vote, ~same, r, ms, g, x)
      )

# the scan goes past a vote b without a majority: b is not x (c)
def Quorum.scan.past(
  ~A: Data,
  ~B: Data,
  ~V: Data,
  ~vote: V -> A -> Maybe<&2, B>,
  ~same: B -> B -> Bool,
  ~sound: @x: B -> @y: B -> {same(x, y) == True{}: Bool} -> {x == y: B},
  c: Bool,
  +b: B,
  +ms: List<&2, A>,
  +g: V,
  +x: B,
  +yr: Nat,
  ec: {same(b, x) == c: Bool},
  eb: {Quorum.has(~A, ~B, ~V, ~vote, ~same, ms, g, b) == False{}: Bool},
  hx: {Quorum.has(~A, ~B, ~V, ~vote, ~same, ms, g, x) == True{}: Bool},
  pos: {Nat.is_lt(0n, Nats.Nat.add_if(c, yr)) == True{}: Bool}
) -> {Nat.is_lt(0n, yr) == True{}: Bool}:
  match c:
    case True{}:
      Empty.absurd(
        {Nat.is_lt(0n, yr) == True{}: Bool},
        Shared.Bool.false_ne_true(
          Equal.trans(
            Bool,
            False{},
            Quorum.has(~A, ~B, ~V, ~vote, ~same, ms, g, b),
            True{},
            Equal.sym(Bool, Quorum.has(~A, ~B, ~V, ~vote, ~same, ms, g, b), False{}, eb),
            %Equal.sym(B, b, x, sound(b)(x)(ec)) : {Quorum.has(~A, ~B, ~V, ~vote, ~same, ms, g, _) == True{}: Bool}
            hx
          )
        )
      )
    case False{}:
      pos

# Quorum.scan at a vote b, picked or not (held)
def Quorum.scan.if(
  ~A: Data,
  ~B: Data,
  ~V: Data,
  ~vote: V -> A -> Maybe<&2, B>,
  ~same: B -> B -> Bool,
  ~refl: @x: B -> {same(x, x) == True{}: Bool},
  ~sound: @x: B -> @y: B -> {same(x, y) == True{}: Bool} -> {x == y: B},
  held: Bool,
  +b: B,
  rest: Maybe<&2, B>,
  +ms: List<&2, A>,
  +g: V,
  +x: B,
  +yr: Nat,
  eb: {Quorum.has(~A, ~B, ~V, ~vote, ~same, ms, g, b) == held: Bool},
  +hx: {Quorum.has(~A, ~B, ~V, ~vote, ~same, ms, g, x) == True{}: Bool},
  pos: {Nat.is_lt(0n, Nats.Nat.add_if(same(b, x), yr)) == True{}: Bool},
  ih: {Nat.is_lt(0n, yr) == True{}: Bool} -> {rest == Some{x}: Maybe<&2, B>}
) -> {Quorum.winner.if(B, held, b, rest) == Some{x}: Maybe<&2, B>}:
  match held:
    case True{}:
      %Quorum.unique(~A, ~B, ~V, ~vote, ~same, ~refl, ~sound, ms, g, b, x)(eb)(hx) : {Some{b} == Some{_}: Maybe<&2, B>}
      {==}
    case False{}:
      ih(Quorum.scan.past(~A, ~B, ~V, ~vote, ~same, ~sound, same(b, x), b, ms, g, x, yr, {==}, eb, hx, pos))

# Quorum.scan at the vote v of a member, with rest the winner after it
def Quorum.scan.at(
  ~A: Data,
  ~B: Data,
  ~V: Data,
  ~vote: V -> A -> Maybe<&2, B>,
  ~same: B -> B -> Bool,
  ~refl: @x: B -> {same(x, x) == True{}: Bool},
  ~sound: @x: B -> @y: B -> {same(x, y) == True{}: Bool} -> {x == y: B},
  v: Maybe<&2, B>,
  rest: Maybe<&2, B>,
  +ms: List<&2, A>,
  +g: V,
  +x: B,
  +yr: Nat,
  +hx: {Quorum.has(~A, ~B, ~V, ~vote, ~same, ms, g, x) == True{}: Bool},
  pos: {Nat.is_lt(0n, Nats.Nat.add_if(Quorum.hit(~B, ~same, v, x), yr)) == True{}: Bool},
  ih: {Nat.is_lt(0n, yr) == True{}: Bool} -> {rest == Some{x}: Maybe<&2, B>}
) -> {Quorum.winner.at(~A, ~B, ~V, ~vote, ~same, v, rest, ms, g) == Some{x}: Maybe<&2, B>}:
  match v:
    case None{}:
      ih(pos)
    case Some{+b}:
      Quorum.scan.if(
        ~A,
        ~B,
        ~V,
        ~vote,
        ~same,
        ~refl,
        ~sound,
        Quorum.has(~A, ~B, ~V, ~vote, ~same, ms, g, b),
        b,
        rest,
        ms,
        g,
        x,
        yr,
        {==},
        hx,
        pos,
        ih
      )

# a scan of members of which some vote for x finds x, when x has a majority
def Quorum.scan(
  ~A: Data,
  ~B: Data,
  ~V: Data,
  ~vote: V -> A -> Maybe<&2, B>,
  ~same: B -> B -> Bool,
  ~refl: @x: B -> {same(x, x) == True{}: Bool},
  ~sound: @x: B -> @y: B -> {same(x, y) == True{}: Bool} -> {x == y: B},
  ks: List<&2, A>,
  +ms: List<&2, A>,
  +g: V,
  +x: B,
  +hx: {Quorum.has(~A, ~B, ~V, ~vote, ~same, ms, g, x) == True{}: Bool}
) -> {
  Nat.is_lt(0n, Quorum.yes(~A, ~B, ~V, ~vote, ~same, ks, g, x)) == True{}: Bool
} -> {Quorum.winner(~A, ~B, ~V, ~vote, ~same, ks, ms, g) == Some{x}: Maybe<&2, B>}:
  match ks:
    case Nil{}:
      pos => Empty.absurd(
        {None{} == Some{x}: Maybe<&2, B>},
        Shared.Bool.false_ne_true(pos)
      )
    case Con{+k, +r}:
      pos => Quorum.scan.at(
        ~A,
        ~B,
        ~V,
        ~vote,
        ~same,
        ~refl,
        ~sound,
        vote(g)(k),
        Quorum.winner(~A, ~B, ~V, ~vote, ~same, r, ms, g),
        ms,
        g,
        x,
        Quorum.yes(~A, ~B, ~V, ~vote, ~same, r, g, x),
        hx,
        pos,
        Quorum.scan(~A, ~B, ~V, ~vote, ~same, ~refl, ~sound, r, ms, g, x, hx)
      )

# a choice with a majority is the winner
law Quorum.winner_of:
  for ~A: Data
  for ~B: Data
  for ~V: Data
  for ~vote: V -> A -> Maybe<&2, B>
  for ~same: B -> B -> Bool
  for ~refl: @x: B -> {same(x, x) == True{}: Bool}
  for ~sound: @x: B -> @y: B -> {same(x, y) == True{}: Bool} -> {x == y: B}
  for ms: List<&2, A>
  for g: V
  for x: B
  {Quorum.has(~A, ~B, ~V, ~vote, ~same, ms, g, x) == True{}: Bool}
    -> {Quorum.winner(~A, ~B, ~V, ~vote, ~same, ms, ms, g) == Some{x}: Maybe<&2, B>}

def Quorum.winner_of(A, B, V, vote, same, refl, sound, ms, g, x):
  +ms = ms
  +g = g
  +x = x
  +hx =>
    Quorum.scan(~A, ~B, ~V, ~vote, ~same, ~refl, ~sound, ms, ms, g, x, hx)(
      Nats.Nat.lt_pos(
        Quorum.no(~A, ~B, ~V, ~vote, ~same, ms, g, x),
        Quorum.yes(~A, ~B, ~V, ~vote, ~same, ms, g, x)
      )(hx)
    )

# One member
# ----------

# the one member of [m] decides alone: its vote wins
law Quorum.winner_one:
  for ~A: Data
  for ~B: Data
  for ~V: Data
  for ~vote: V -> A -> Maybe<&2, B>
  for ~same: B -> B -> Bool
  for ~refl: @x: B -> {same(x, x) == True{}: Bool}
  for +m: A
  for +g: V
  for +x: B
  {vote(g)(m) == Some{x}: Maybe<&2, B>}
    -> {Quorum.winner(~A, ~B, ~V, ~vote, ~same, [m], [m], g) == Some{x}: Maybe<&2, B>}

def Quorum.winner_one(A, B, V, vote, same, refl, m, g, x):
  +h =>
    %Equal.sym(Maybe<&2, B>, vote(g)(m), Some{x}, h) :
      {Quorum.winner.at(~A, ~B, ~V, ~vote, ~same, _, None{}, [m], g) == Some{x}: Maybe<&2, B>}
    %Equal.sym(Maybe<&2, B>, vote(g)(m), Some{x}, h) :
      {
        Quorum.winner.if(
          B,
          Nat.is_lt(
            Nats.Nat.add_if(Bool.not(Quorum.hit(~B, ~same, _, x)), 0n),
            Nats.Nat.add_if(Quorum.hit(~B, ~same, _, x), 0n)
          ),
          x,
          None{}
        )
          == Some{x}: Maybe<&2, B>
      }
    %Equal.sym(Bool, same(x, x), True{}, refl(x)) :
      {Quorum.winner.if(B, Nat.is_lt(Nats.Nat.add_if(Bool.not(_), 0n), Nats.Nat.add_if(_, 0n)), x, None{}) == Some{x}: Maybe<&2, B>}
    {==}

# the one member of [m] has not voted: nothing wins
law Quorum.winner_none:
  for ~A: Data
  for ~B: Data
  for ~V: Data
  for ~vote: V -> A -> Maybe<&2, B>
  for ~same: B -> B -> Bool
  for +m: A
  for +g: V
  {vote(g)(m) == None{}: Maybe<&2, B>}
    -> {Quorum.winner(~A, ~B, ~V, ~vote, ~same, [m], [m], g) == None{}: Maybe<&2, B>}

def Quorum.winner_none(A, B, V, vote, same, m, g):
  h =>
    %Equal.sym(Maybe<&2, B>, vote(g)(m), None{}, h) :
      {Quorum.winner.at(~A, ~B, ~V, ~vote, ~same, _, None{}, [m], g) == None{}: Maybe<&2, B>}
    {==}
