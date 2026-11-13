import Base
import ../shared/shared/ledger.bend as Ledgers
import ../shared/shared/shared/shared/shared.bend as Shared
import ../shared/shared/shared/text.bend as Texts
import ./codes.bend as Coded
import ./facts.bend as Facts
import ./lines.bend as Lines
import ./run/facts.bend as RFacts
import ./run/lines.bend as RLines
import ./run/rounds.bend as RRounds
import ./shared/lists.bend as Lists
import ./spec.bend as Spec
import ./types.bend as Types

# Laws of the rounds
# ------------------
# What the readers of a slot need from the rounds (run/rounds.bend): a pick
# that is decided stays decided as the facts grow, and is the only one; the
# facts hold a vote for it; and a node that decides alone decides with one
# vote. The laws are first said of lists of ballots, then of sets of facts.

# the ballots that s holds for the slot k of the line c
def Slot.ballots(s: Facts.Facts(), +c: Ledgers.Line, +k: Nat) -> List<&2, RRounds.Ballot>:
  RRounds.Slot.ballots(Facts.Facts.list(s), c, k)

# Ballots that grow
# -----------------

# two lists of ballots
type Grow is Data:
  Grow{old: List<&2, RRounds.Ballot>, new: List<&2, RRounds.Ballot>}

# the ballot b, when it is the one ballot of its voter with its number in the
# old list of g, is that in the new list too
def Ballot.sure(g: Grow, b: RRounds.Ballot) -> Bool:
  match g b:
    case Grow{bs, bs2} RRounds.Ballot{+v, +t, +x}:
      Bool.or(
        Bool.not(RRounds.Cast.is(x, RRounds.Ballots.at(bs, v, t))),
        RRounds.Cast.is(x, RRounds.Ballots.at(bs2, v, t))
      )

# each ballot that is read from bs is read from bs2
def Ballots.grown(+bs: List<&2, RRounds.Ballot>, +bs2: List<&2, RRounds.Ballot>) -> Bool:
  Shared.List.holds(~RRounds.Ballot, ~Grow, ~Ballot.sure, bs, Grow{bs, bs2})

# some facts, and a slot of a line
type Kept is Data:
  Kept{facts: RFacts.Plain(), line: Ledgers.Line, slot: Nat}

# the fact f, when it is a ballot for the slot of g, is held by the facts of g
def Fact.kept(g: Kept, f: Types.Fact) -> Bool:
  match g f:
    case Kept{m, c, k} Types.Fact.Vote{+v, Types.Step.At{+c2, +k2, +t}, +x}:
      Bool.or(
        Bool.not(Bool.and(Ledgers.Line.is_eq(c2, c), Nat.is_eq(k2, k))),
        RFacts.Facts.has(m, Types.Fact.Vote{v, Types.Step.At{c2, k2, t}, x})
      )
    case Kept{m, c, k} f2:
      True{}

# s2 holds each ballot that s holds for the slot k of the line c
def Slot.kept(s: Facts.Facts(), s2: Facts.Facts(), c: Ledgers.Line, k: Nat) -> Bool:
  Shared.List.holds(~Types.Fact, ~Kept, ~Fact.kept, Facts.Facts.list(s), Kept{Facts.Facts.crit(s2), c, k})

# Tools
# -----

# p(g) holds of each element of xs when it holds of each member of xs
def List.holds_of(
  ~A: Data,
  ~V: Data,
  ~p: V -> A -> Bool,
  ~same: A -> A -> Bool,
  ~laws: Shared.Eq.Laws(A, same),
  xs: List<&2, A>,
  +g: V,
  h: (@x: A -> {List.contains(~A, ~same, xs, x) == True{}: Bool} -> {p(g)(x) == True{}: Bool})
) -> {Shared.List.holds(~A, ~V, ~p, xs, g) == True{}: Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+y, +r}:
      Facts.Case.all_one(
        (@x: A -> {List.contains(~A, ~same, y <> r, x) == True{}: Bool} -> {p(g)(x) == True{}: Bool}),
        p(g)(y),
        u => Shared.List.holds(~A, ~V, ~p, r, g),
        h,
        f => f(y)(Lists.List.contains_head(~A, ~same, ~laws, y, r)),
        f => List.holds_of(
          ~A,
          ~V,
          ~p,
          ~same,
          ~laws,
          r,
          g,
          +x => cx => f(x)(Shared.List.contains_cons(~A, ~same, y, r, x)(cx))
        )
      )

# a list of casts with a member is not empty
def Casts.some(
  cs: List<&2, Types.Cast>,
  -x: Types.Cast
) -> {
  List.contains(~Types.Cast, ~Coded.Cast.is_eq, cs, x) == True{}: Bool
} -> {Bool.not(List.is_empty(&2, Types.Cast, cs)) == True{}: Bool}:
  match cs:
    case Nil{}:
      h => Empty.absurd({False{} == True{}: Bool}, Shared.Bool.false_ne_true(h))
    case Con{y, r}:
      h => {==}

# the casts cs agree on x, when x is one of them and each is x
def Casts.agreed(
  +cs: List<&2, Types.Cast>,
  +x: Types.Cast,
  hin: {List.contains(~Types.Cast, ~Coded.Cast.is_eq, cs, x) == True{}: Bool},
  hall: {Shared.List.holds(~Types.Cast, ~Types.Cast, ~Coded.Cast.is_eq, cs, x) == True{}: Bool}
) -> {Shared.List.agreed(~Types.Cast, ~Coded.Cast.is_eq, cs) == Some{x}: Maybe<&2, Types.Cast>}:
  Shared.List.agreed_of_holds(
    ~Types.Cast,
    ~Coded.Cast.is_eq,
    ~Coded.Cast.laws(),
    cs,
    x
  )(
    Shared.Bool.and_both(
      Bool.not(List.is_empty(&2, Types.Cast, cs)),
      Shared.List.holds(~Types.Cast, ~Types.Cast, ~Coded.Cast.is_eq, cs, x)
    )(Casts.some(cs, x)(hin))(hall)
  )

# a cast that is the cast x is x
def Cast.is_some(
  +x: Types.Cast,
  m: Maybe<&2, Types.Cast>
) -> {RRounds.Cast.is(x, m) == True{}: Bool} -> {m == Some{x}: Maybe<&2, Types.Cast>}:
  match m:
    case None{}:
      h => Empty.absurd(
        {None{} == Some{x}: Maybe<&2, Types.Cast>},
        Shared.Bool.false_ne_true(h)
      )
    case Some{+y}:
      h => Equal.cong(
        Types.Cast,
        Maybe<&2, Types.Cast>,
        z => Some{z},
        y,
        x,
        Coded.Cast.is_eq_sound(y, x)(h)
      )

# the cast x is the cast x
def Cast.is_of(
  +x: Types.Cast,
  -m: Maybe<&2, Types.Cast>,
  e: {m == Some{x}: Maybe<&2, Types.Cast>}
) -> {RRounds.Cast.is(x, m) == True{}: Bool}:
  %Equal.sym(Maybe<&2, Types.Cast>, m, Some{x}, e): {RRounds.Cast.is(x, _) == True{}: Bool}
  Coded.Cast.is_eq_refl(x)

# what follows from a witness and what holds of it follows
def Ex.by(-A: Type, -B: @-x: A -> Type, -Q: Type, r: Exists(A, B), k: @x: A -> B(x) -> Q) -> Q:
  (x, p) = r
  k(x)(p)

# Votes that count
# ----------------

# the cast that some casts agree on is one of them
def Casts.agreed_in(
  cs: List<&2, Types.Cast>,
  +x: Types.Cast
) -> {
  Shared.List.agreed(~Types.Cast, ~Coded.Cast.is_eq, cs) == Some{x}: Maybe<&2, Types.Cast>
} -> {List.contains(~Types.Cast, ~Coded.Cast.is_eq, cs, x) == True{}: Bool}:
  match cs:
    case Nil{}:
      h => Empty.absurd({False{} == True{}: Bool}, Shared.Maybe.none_ne_some(Types.Cast, x, h))
    case Con{+y, +r}:
      Lists.Bool.by(
        b => {
          Bool.pick(Maybe<&2, Types.Cast>, b, Some{y}, None{}) == Some{x}: Maybe<&2, Types.Cast>
        } -> {List.contains(~Types.Cast, ~Coded.Cast.is_eq, y <> r, x) == True{}: Bool},
        Shared.List.holds(~Types.Cast, ~Types.Cast, ~Coded.Cast.is_eq, r, y),
        et => h => (
          %Shared.Maybe.some_inj(Types.Cast, y, x, h): {List.contains(~Types.Cast, ~Coded.Cast.is_eq, y <> r, _) == True{}: Bool}
          Lists.List.contains_head(~Types.Cast, ~Coded.Cast.is_eq, ~Coded.Cast.laws(), y, r)),
        ef => h => Empty.absurd(
          {List.contains(~Types.Cast, ~Coded.Cast.is_eq, y <> r, x) == True{}: Bool},
          Shared.Maybe.none_ne_some(Types.Cast, x, h)
        )
      )

# Tally.voted_cast, once the vote m of the node is known
def Tally.voted_cast.of(
  +bs: List<&2, RRounds.Ballot>,
  +r: Nat,
  +pk: Types.Pick,
  +d: String,
  m: Maybe<&2, RRounds.Ballot>
) -> {
  RRounds.Vote.of(bs, d, r) == m: Maybe<&2, RRounds.Ballot>
} -> {RRounds.Vote.is_for(pk, m) == True{}: Bool} -> Exists(Nat, t => Exists(List<&2, Types.Ref>, b => {List.contains(~Types.Cast, ~Coded.Cast.is_eq, RRounds.Casts.of(bs, Types.Ref{d, t}), Types.Cast.Vote{r, pk, b}) == True{}: Bool})):
  match m:
    case None{}:
      e => h => Empty.absurd(Exists(Nat, t => Exists(List<&2, Types.Ref>, b => {List.contains(~Types.Cast, ~Coded.Cast.is_eq, RRounds.Casts.of(bs, Types.Ref{d, t}), Types.Cast.Vote{r, pk, b}) == True{}: Bool})), Shared.Bool.false_ne_true(h))
    case Some{RRounds.Ballot{v, t, Types.Cast.Pass{r2}}}:
      e => h => Empty.absurd(Exists(Nat, t => Exists(List<&2, Types.Ref>, b => {List.contains(~Types.Cast, ~Coded.Cast.is_eq, RRounds.Casts.of(bs, Types.Ref{d, t}), Types.Cast.Vote{r, pk, b}) == True{}: Bool})), Shared.Bool.false_ne_true(h))
    case Some{RRounds.Ballot{+v, +t, Types.Cast.Vote{+r2, +q, +basis}}}:
      +e => h => (
        t,
        (
          basis,
          (
            %Coded.Pick.is_eq_sound(q, pk)(h): {List.contains(~Types.Cast, ~Coded.Cast.is_eq, RRounds.Casts.of(bs, Types.Ref{d, t}), Types.Cast.Vote{r, _, basis}) == True{}: Bool}
            %Shared.Nat.is_eq_sound(r2, r)(Shared.Bool.and_true_right(String.eq(v, d), Nat.is_eq(r2, r))(Shared.Bool.and_true_left(Bool.and(String.eq(v, d), Nat.is_eq(r2, r)), Bool.and(
                        RRounds.Seen.takes(r2, RRounds.Chain.seen(bs, d, t)),
                        RRounds.Cast.is(Types.Cast.Vote{r2, q, basis}, RRounds.Ballots.at(bs, d, t))
                      ))(Lists.List.pick_hit(
                        ~RRounds.Ballot,
                        ~RRounds.Roll,
                        ~RRounds.Ballot.counts,
                        bs,
                        RRounds.Roll{bs, d, r},
                        RRounds.Ballot{v, t, Types.Cast.Vote{r2, q, basis}}
                      )(e)))): {List.contains(~Types.Cast, ~Coded.Cast.is_eq, RRounds.Casts.of(bs, Types.Ref{d, t}), Types.Cast.Vote{_, q, basis}) == True{}: Bool}
            Casts.agreed_in(
              RRounds.Casts.of(bs, Types.Ref{d, t}),
              Types.Cast.Vote{r2, q, basis}
            )(
              Cast.is_some(
                Types.Cast.Vote{r2, q, basis},
                RRounds.Ballots.at(bs, d, t)
              )(
                Shared.Bool.and_true_right(
                  RRounds.Seen.takes(r2, RRounds.Chain.seen(bs, d, t)),
                  RRounds.Cast.is(Types.Cast.Vote{r2, q, basis}, RRounds.Ballots.at(bs, d, t))
                )(
                  Shared.Bool.and_true_right(
                    Bool.and(String.eq(v, d), Nat.is_eq(r2, r)),
                    Bool.and(
                        RRounds.Seen.takes(r2, RRounds.Chain.seen(bs, d, t)),
                        RRounds.Cast.is(Types.Cast.Vote{r2, q, basis}, RRounds.Ballots.at(bs, d, t))
                      )
                  )(Lists.List.pick_hit(
                        ~RRounds.Ballot,
                        ~RRounds.Roll,
                        ~RRounds.Ballot.counts,
                        bs,
                        RRounds.Roll{bs, d, r},
                        RRounds.Ballot{v, t, Types.Cast.Vote{r2, q, basis}}
                      )(e))
                )
              )
            ))
        )
      )

# the ballots hold a vote of a node that voted for a pick in a round: of the
# round, for the pick
def Tally.voted_cast(
  +bs: List<&2, RRounds.Ballot>,
  +r: Nat,
  +pk: Types.Pick,
  +d: String
) -> {RRounds.Tally.voted(RRounds.Tally{bs, r, pk}, d) == True{}: Bool} -> Exists(Nat, t => Exists(List<&2, Types.Ref>, b => {List.contains(~Types.Cast, ~Coded.Cast.is_eq, RRounds.Casts.of(bs, Types.Ref{d, t}), Types.Cast.Vote{r, pk, b}) == True{}: Bool})):
  h => Tally.voted_cast.of(bs, r, pk, d, RRounds.Vote.of(bs, d, r))({==})(h)

# Round.won_cast, with a node that voted for the pick
def Round.won_cast.at(
  +bs: List<&2, RRounds.Ballot>,
  +r: Nat,
  +p: Types.Pick,
  +pk: Types.Pick,
  +d: String,
  -ds0: List<&2, String>,
  ep: {p == pk: Types.Pick},
  w: {
    List.contains(~String, ~String.eq, ds0, d) == True{}: Bool
  }
    & {RRounds.Tally.voted(RRounds.Tally{bs, r, p}, d) == True{}: Bool}
) -> Exists(String, v => Exists(Nat, t => Exists(List<&2, Types.Ref>, b => {List.contains(~Types.Cast, ~Coded.Cast.is_eq, RRounds.Casts.of(bs, Types.Ref{v, t}), Types.Cast.Vote{r, pk, b}) == True{}: Bool}))):
  (hin, hv) = w
  (
    d,
    Tally.voted_cast(bs, r, pk, d)((
        %ep: {RRounds.Tally.voted(RRounds.Tally{bs, r, _}, d) == True{}: Bool}
        hv))
  )

# the ballots hold a vote of the round r for the pick that the round decided
def Round.won_cast(
  +bs: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +r: Nat,
  +pk: Types.Pick,
  m: RRounds.Mind
) -> {RRounds.Round.won(bs, ds, r, m) == Some{pk}: Maybe<&2, Types.Pick>} -> Exists(String, v => Exists(Nat, t => Exists(List<&2, Types.Ref>, b => {List.contains(~Types.Cast, ~Coded.Cast.is_eq, RRounds.Casts.of(bs, Types.Ref{v, t}), Types.Cast.Vote{r, pk, b}) == True{}: Bool}))):
  match m:
    case RRounds.Mind.Open{}:
      h => Empty.absurd(Exists(String, v => Exists(Nat, t => Exists(List<&2, Types.Ref>, b => {List.contains(~Types.Cast, ~Coded.Cast.is_eq, RRounds.Casts.of(bs, Types.Ref{v, t}), Types.Cast.Vote{r, pk, b}) == True{}: Bool}))), Shared.Maybe.none_ne_some(Types.Pick, pk, h))
    case RRounds.Mind.Void{}:
      h => Empty.absurd(Exists(String, v => Exists(Nat, t => Exists(List<&2, Types.Ref>, b => {List.contains(~Types.Cast, ~Coded.Cast.is_eq, RRounds.Casts.of(bs, Types.Ref{v, t}), Types.Cast.Vote{r, pk, b}) == True{}: Bool}))), Shared.Maybe.none_ne_some(Types.Pick, pk, h))
    case RRounds.Mind.Sound{+p}:
      Lists.Bool.by(
        b => {
          Shared.Maybe.when(Types.Pick, b, u => Some{p}) == Some{pk}: Maybe<&2, Types.Pick>
        } -> Exists(String, v => Exists(Nat, t => Exists(List<&2, Types.Ref>, b => {List.contains(~Types.Cast, ~Coded.Cast.is_eq, RRounds.Casts.of(bs, Types.Ref{v, t}), Types.Cast.Vote{r, pk, b}) == True{}: Bool}))),
        RRounds.Tally.most(bs, ds, r, p),
        et => h => Ex.by(
          String,
          d => {
            List.contains(~String, ~String.eq, ds, d) == True{}: Bool
          }
            & {RRounds.Tally.voted(RRounds.Tally{bs, r, p}, d) == True{}: Bool},
          Exists(String, v => Exists(Nat, t => Exists(List<&2, Types.Ref>, b => {List.contains(~Types.Cast, ~Coded.Cast.is_eq, RRounds.Casts.of(bs, Types.Ref{v, t}), Types.Cast.Vote{r, pk, b}) == True{}: Bool}))),
          Lists.List.count_pos(
            ~String,
            ~RRounds.Tally,
            ~RRounds.Tally.voted,
            ~String.eq,
            ~Texts.String.laws(),
            ds,
            RRounds.Tally{bs, r, p}
          )(
            Lists.Nat.most_pos(
              List.length(&2, String, ds),
              Lists.List.count(~String, ~RRounds.Tally, ~RRounds.Tally.voted, ds, RRounds.Tally{bs, r, p})
            )(et)
          ),
          +d => w => Round.won_cast.at(bs, r, p, pk, d, ds, Shared.Maybe.some_inj(Types.Pick, p, pk, h), w)
        ),
        ef => h => Empty.absurd(Exists(String, v => Exists(Nat, t => Exists(List<&2, Types.Ref>, b => {List.contains(~Types.Cast, ~Coded.Cast.is_eq, RRounds.Casts.of(bs, Types.Ref{v, t}), Types.Cast.Vote{r, pk, b}) == True{}: Bool}))), Shared.Maybe.none_ne_some(Types.Pick, pk, h))
      )

# Rounds.won_cast, with the vote
def Rounds.won_cast.fin(
  +bs: List<&2, RRounds.Ballot>,
  +r: Nat,
  +pk: Types.Pick,
  w0: Exists(String, v => Exists(Nat, t => Exists(List<&2, Types.Ref>, b => {List.contains(~Types.Cast, ~Coded.Cast.is_eq, RRounds.Casts.of(bs, Types.Ref{v, t}), Types.Cast.Vote{r, pk, b}) == True{}: Bool})))
) -> Exists(
  String,
  v => Exists(
    Nat,
    t => Exists(
      Nat,
      r => Exists(
        List<&2, Types.Ref>,
        b => {
          List.contains(
            ~Types.Cast,
            ~Coded.Cast.is_eq,
            RRounds.Casts.of(bs, Types.Ref{v, t}),
            Types.Cast.Vote{r, pk, b}
          )
            == True{}: Bool
        }
      )
    )
  )
):
  (+v, w1) = w0
  (+t, w2) = w1
  (+b, h) = w2
  (v, (t, (r, (b, h))))

# the ballots hold a vote for the pick that one of the rounds from r on
# decided
def Rounds.won_cast(
  ms: List<&2, RRounds.Mind>,
  +bs: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +r: Nat,
  +pk: Types.Pick
) -> {RRounds.Rounds.won(ms, bs, ds, r) == Some{pk}: Maybe<&2, Types.Pick>} -> Exists(
  String,
  v => Exists(
    Nat,
    t => Exists(
      Nat,
      r => Exists(
        List<&2, Types.Ref>,
        b => {
          List.contains(
            ~Types.Cast,
            ~Coded.Cast.is_eq,
            RRounds.Casts.of(bs, Types.Ref{v, t}),
            Types.Cast.Vote{r, pk, b}
          )
            == True{}: Bool
        }
      )
    )
  )
):
  match ms:
    case Nil{}:
      h => Empty.absurd(Exists(
  String,
  v => Exists(
    Nat,
    t => Exists(
      Nat,
      r => Exists(
        List<&2, Types.Ref>,
        b => {
          List.contains(
            ~Types.Cast,
            ~Coded.Cast.is_eq,
            RRounds.Casts.of(bs, Types.Ref{v, t}),
            Types.Cast.Vote{r, pk, b}
          )
            == True{}: Bool
        }
      )
    )
  )
), Shared.Maybe.none_ne_some(Types.Pick, pk, h))
    case Con{+m, +rest}:
      Lists.Maybe.by(
        Types.Pick,
        x => {
          RRounds.Rounds.won.or(x, u => RRounds.Rounds.won(rest, bs, ds, 1n+r)) == Some{pk}: Maybe<&2, Types.Pick>
        } -> Exists(
  String,
  v => Exists(
    Nat,
    t => Exists(
      Nat,
      r => Exists(
        List<&2, Types.Ref>,
        b => {
          List.contains(
            ~Types.Cast,
            ~Coded.Cast.is_eq,
            RRounds.Casts.of(bs, Types.Ref{v, t}),
            Types.Cast.Vote{r, pk, b}
          )
            == True{}: Bool
        }
      )
    )
  )
),
        RRounds.Round.won(bs, ds, r, m),
        en => h => Rounds.won_cast(rest, bs, ds, 1n+r, pk)(h),
        +p => ep => h => Rounds.won_cast.fin(
          bs,
          r,
          pk,
          Round.won_cast(bs, ds, r, pk, m)(
            Equal.trans(
              Maybe<&2, Types.Pick>,
              RRounds.Round.won(bs, ds, r, m),
              Some{p},
              Some{pk},
              ep,
              h
            )
          )
        )
      )

# Round.backs_cast, with the vote
def Round.backs_cast.fin(
  +bs: List<&2, RRounds.Ballot>,
  +r: Nat,
  +pk: Types.Pick,
  +v: String,
  w0: Exists(Nat, t => Exists(List<&2, Types.Ref>, b => {List.contains(~Types.Cast, ~Coded.Cast.is_eq, RRounds.Casts.of(bs, Types.Ref{v, t}), Types.Cast.Vote{r, pk, b}) == True{}: Bool}))
) -> Exists(
  Nat,
  t => Exists(
    Types.Cast,
    x => {
      List.contains(~Types.Cast, ~Coded.Cast.is_eq, RRounds.Casts.of(bs, Types.Ref{v, t}), x) == True{}: Bool
    }
  )
):
  (+t, w1) = w0
  (+b, h) = w1
  (t, (Types.Cast.Vote{r, pk, b}, h))

# the ballots hold a ballot of each of the nodes that decided a pick in a
# round
def Round.backs_cast(
  +bs: List<&2, RRounds.Ballot>,
  +os: List<&2, String>,
  +pk: Types.Pick,
  +r: Nat,
  +v: String,
  m: RRounds.Mind
) -> {
  RRounds.Round.backs(bs, os, pk, r, m) == True{}: Bool
} -> {List.contains(~String, ~String.eq, os, v) == True{}: Bool} -> Exists(
  Nat,
  t => Exists(
    Types.Cast,
    x => {
      List.contains(~Types.Cast, ~Coded.Cast.is_eq, RRounds.Casts.of(bs, Types.Ref{v, t}), x) == True{}: Bool
    }
  )
):
  match m:
    case RRounds.Mind.Open{}:
      h => hin => Empty.absurd(Exists(
  Nat,
  t => Exists(
    Types.Cast,
    x => {
      List.contains(~Types.Cast, ~Coded.Cast.is_eq, RRounds.Casts.of(bs, Types.Ref{v, t}), x) == True{}: Bool
    }
  )
), Shared.Bool.false_ne_true(h))
    case RRounds.Mind.Void{}:
      h => hin => Empty.absurd(Exists(
  Nat,
  t => Exists(
    Types.Cast,
    x => {
      List.contains(~Types.Cast, ~Coded.Cast.is_eq, RRounds.Casts.of(bs, Types.Ref{v, t}), x) == True{}: Bool
    }
  )
), Shared.Bool.false_ne_true(h))
    case RRounds.Mind.Sound{q}:
      h => hin => Round.backs_cast.fin(
        bs,
        r,
        pk,
        v,
        Tally.voted_cast(
          bs,
          r,
          pk,
          v
        )(
          Lists.List.holds_in(
            ~String,
            ~RRounds.Tally,
            ~RRounds.Tally.voted,
            ~String.eq,
            ~Texts.String.laws(),
            os,
            RRounds.Tally{bs, r, pk},
            v
          )(
            Shared.Bool.and_true_right(
              Coded.Pick.is_eq(q, pk),
              Shared.List.holds(~String, ~RRounds.Tally, ~RRounds.Tally.voted, os, RRounds.Tally{bs, r, pk})
            )(h)
          )(hin)
        )
      )

# the ballots hold a ballot of each of the nodes that decided a pick in one
# of the rounds from r on
def Rounds.back_cast(
  ms: List<&2, RRounds.Mind>,
  +bs: List<&2, RRounds.Ballot>,
  +os: List<&2, String>,
  +pk: Types.Pick,
  +r: Nat,
  +v: String
) -> {
  RRounds.Rounds.back(ms, bs, os, pk, r) == True{}: Bool
} -> {List.contains(~String, ~String.eq, os, v) == True{}: Bool} -> Exists(
  Nat,
  t => Exists(
    Types.Cast,
    x => {
      List.contains(~Types.Cast, ~Coded.Cast.is_eq, RRounds.Casts.of(bs, Types.Ref{v, t}), x) == True{}: Bool
    }
  )
):
  match ms:
    case Nil{}:
      h => hin => Empty.absurd(Exists(
  Nat,
  t => Exists(
    Types.Cast,
    x => {
      List.contains(~Types.Cast, ~Coded.Cast.is_eq, RRounds.Casts.of(bs, Types.Ref{v, t}), x) == True{}: Bool
    }
  )
), Shared.Bool.false_ne_true(h))
    case Con{+m, +rest}:
      Lists.Bool.by(
        b => {
          List.any.if(u => RRounds.Rounds.back(rest, bs, os, pk, 1n+r), b) == True{}: Bool
        } -> {List.contains(~String, ~String.eq, os, v) == True{}: Bool} -> Exists(
  Nat,
  t => Exists(
    Types.Cast,
    x => {
      List.contains(~Types.Cast, ~Coded.Cast.is_eq, RRounds.Casts.of(bs, Types.Ref{v, t}), x) == True{}: Bool
    }
  )
),
        RRounds.Round.backs(bs, os, pk, r, m),
        et => h => hin => Round.backs_cast(bs, os, pk, r, v, m)(et)(hin),
        ef => h => hin => Rounds.back_cast(rest, bs, os, pk, 1n+r, v)(h)(hin)
      )

# Laws of lists of ballots
# ------------------------

# What grows with the ballots
# --------------------------

# b is true when a is, and b or not a
def Bool.or_not(
  a: Bool,
  -b: Bool
) -> {a == True{}: Bool} -> {Bool.or(Bool.not(a), b) == True{}: Bool} -> {b == True{}: Bool}:
  match a:
    case True{}:
      h1 => h2 => h2
    case False{}:
      h1 => h2 => Empty.absurd({b == True{}: Bool}, Shared.Bool.false_ne_true(h1))

# Ballots.at_grows, for a cast among the ballots xs, which are sure
def Ballots.at_grows.go(
  xs: List<&2, RRounds.Ballot>,
  +bs: List<&2, RRounds.Ballot>,
  +bs2: List<&2, RRounds.Ballot>,
  +v: String,
  +t: Nat,
  +x: Types.Cast
) -> {
  Shared.List.holds(~RRounds.Ballot, ~Grow, ~Ballot.sure, xs, Grow{bs, bs2}) == True{}: Bool
} -> {
  List.contains(~Types.Cast, ~Coded.Cast.is_eq, RRounds.Casts.of(xs, Types.Ref{v, t}), x) == True{}: Bool
} -> {RRounds.Cast.is(x, RRounds.Ballots.at(bs, v, t)) == True{}: Bool} -> {RRounds.Cast.is(x, RRounds.Ballots.at(bs2, v, t)) == True{}: Bool}:
  match xs:
    case Nil{}:
      hh => hc => his => Empty.absurd({RRounds.Cast.is(x, RRounds.Ballots.at(bs2, v, t)) == True{}: Bool}, Shared.Bool.false_ne_true(hc))
    case Con{RRounds.Ballot{+w, +u, +y}, +rest}:
      +hh => Lists.Bool.by(
        b => {
          List.contains(~Types.Cast, ~Coded.Cast.is_eq, Shared.Maybe.cons(Types.Cast, Shared.Maybe.when(Types.Cast, b, z => Some{y}), RRounds.Casts.of(rest, Types.Ref{v, t})), x) == True{}: Bool
        } -> {RRounds.Cast.is(x, RRounds.Ballots.at(bs, v, t)) == True{}: Bool} -> {RRounds.Cast.is(x, RRounds.Ballots.at(bs2, v, t)) == True{}: Bool},
        Bool.and(String.eq(w, v), Nat.is_eq(u, t)),
        +et => hc => +his => Lists.List.contains_cons_by(
          ~Types.Cast,
          ~Coded.Cast.is_eq,
          ~Coded.Cast.laws(),
          {RRounds.Cast.is(x, RRounds.Ballots.at(bs2, v, t)) == True{}: Bool},
          y,
          RRounds.Casts.of(rest, Types.Ref{v, t}),
          x,
          hc,
          e => Bool.or_not(RRounds.Cast.is(x, RRounds.Ballots.at(bs, v, t)), RRounds.Cast.is(x, RRounds.Ballots.at(bs2, v, t)))(his)((
              %Texts.String.eq_sound(w, v)(Shared.Bool.and_true_left(String.eq(w, v), Nat.is_eq(u, t))(et)): {Ballot.sure(Grow{bs, bs2}, RRounds.Ballot{_, t, x}) == True{}: Bool}
              %Shared.Nat.is_eq_sound(u, t)(Shared.Bool.and_true_right(String.eq(w, v), Nat.is_eq(u, t))(et)): {Ballot.sure(Grow{bs, bs2}, RRounds.Ballot{w, _, x}) == True{}: Bool}
              %e: {Ballot.sure(Grow{bs, bs2}, RRounds.Ballot{w, u, _}) == True{}: Bool}
              Shared.List.all.if_hit(Ballot.sure(Grow{bs, bs2}, RRounds.Ballot{w, u, y}), z0 => Shared.List.holds(~RRounds.Ballot, ~Grow, ~Ballot.sure, rest, Grow{bs, bs2}))(hh))),
          cin => Ballots.at_grows.go(rest, bs, bs2, v, t, x)(Shared.List.all.if_rest(Ballot.sure(Grow{bs, bs2}, RRounds.Ballot{w, u, y}), z0 => Shared.List.holds(~RRounds.Ballot, ~Grow, ~Ballot.sure, rest, Grow{bs, bs2}))(hh))(cin)(his)
        ),
        ef => hc => his => Ballots.at_grows.go(rest, bs, bs2, v, t, x)(Shared.List.all.if_rest(Ballot.sure(Grow{bs, bs2}, RRounds.Ballot{w, u, y}), z0 => Shared.List.holds(~RRounds.Ballot, ~Grow, ~Ballot.sure, rest, Grow{bs, bs2}))(hh))(hc)(his)
      )

# the ballot of a voter with a number that is read from the ballots is read
# from the ballots that they grew to
def Ballots.at_grows(
  +bs: List<&2, RRounds.Ballot>,
  +bs2: List<&2, RRounds.Ballot>,
  +v: String,
  +t: Nat,
  +x: Types.Cast
) -> {
  Ballots.grown(bs, bs2) == True{}: Bool
} -> {RRounds.Ballots.at(bs, v, t) == Some{x}: Maybe<&2, Types.Cast>} -> {RRounds.Ballots.at(bs2, v, t) == Some{x}: Maybe<&2, Types.Cast>}:
  hg => +e => Cast.is_some(x, RRounds.Ballots.at(bs2, v, t))(
    Ballots.at_grows.go(bs, bs, bs2, v, t, x)(hg)(
      Casts.agreed_in(RRounds.Casts.of(bs, Types.Ref{v, t}), x)(e)
    )(Cast.is_of(x, RRounds.Ballots.at(bs, v, t), e))
  )

# what is known of a voter before one of its ballots stays known as the
# ballots grow
def Chain.seen_grows(
  +bs: List<&2, RRounds.Ballot>,
  +bs2: List<&2, RRounds.Ballot>,
  +v: String,
  t: Nat,
  +m: RRounds.Seen,
  +hg: {Ballots.grown(bs, bs2) == True{}: Bool}
) -> {RRounds.Chain.seen(bs, v, t) == Some{m}: Maybe<&2, RRounds.Seen>} -> {RRounds.Chain.seen(bs2, v, t) == Some{m}: Maybe<&2, RRounds.Seen>}:
  match t:
    case 0n:
      h => h
    case 1n+(+j):
      Lists.Maybe.by(
        RRounds.Seen,
        z => {
          RRounds.Chain.seen.next(z, RRounds.Ballots.at(bs, v, j)) == Some{m}: Maybe<&2, RRounds.Seen>
        } -> {RRounds.Chain.seen.next(RRounds.Chain.seen(bs2, v, j), RRounds.Ballots.at(bs2, v, j)) == Some{m}: Maybe<&2, RRounds.Seen>},
        RRounds.Chain.seen(bs, v, j),
        en => h => Empty.absurd(
          {RRounds.Chain.seen.next(RRounds.Chain.seen(bs2, v, j), RRounds.Ballots.at(bs2, v, j)) == Some{m}: Maybe<&2, RRounds.Seen>},
          Shared.Maybe.none_ne_some(RRounds.Seen, m, h)
        ),
        +m0 => +e0 => Lists.Maybe.by(
          Types.Cast,
          y => {
            RRounds.Chain.seen.next(Some{m0}, y) == Some{m}: Maybe<&2, RRounds.Seen>
          } -> {RRounds.Chain.seen.next(RRounds.Chain.seen(bs2, v, j), RRounds.Ballots.at(bs2, v, j)) == Some{m}: Maybe<&2, RRounds.Seen>},
          RRounds.Ballots.at(bs, v, j),
          en => h => Empty.absurd(
            {RRounds.Chain.seen.next(RRounds.Chain.seen(bs2, v, j), RRounds.Ballots.at(bs2, v, j)) == Some{m}: Maybe<&2, RRounds.Seen>},
            Shared.Maybe.none_ne_some(RRounds.Seen, m, h)
          ),
          +x0 => +ex => h => (
            %Equal.sym(Maybe<&2, RRounds.Seen>, RRounds.Chain.seen(bs2, v, j), Some{m0}, Chain.seen_grows(bs, bs2, v, j, m0, hg)(e0)): {RRounds.Chain.seen.next(_, RRounds.Ballots.at(bs2, v, j)) == Some{m}: Maybe<&2, RRounds.Seen>}
            %Equal.sym(Maybe<&2, Types.Cast>, RRounds.Ballots.at(bs2, v, j), Some{x0}, Ballots.at_grows(bs, bs2, v, j, x0)(hg)(ex)): {RRounds.Chain.seen.next(Some{m0}, _) == Some{m}: Maybe<&2, RRounds.Seen>}
            h)
        )
      )

# a vote that counts after what is known of a voter still does as the
# ballots grow
def Seen.takes_grows(
  +bs: List<&2, RRounds.Ballot>,
  +bs2: List<&2, RRounds.Ballot>,
  +v: String,
  +t: Nat,
  +r2: Nat,
  +hg: {Ballots.grown(bs, bs2) == True{}: Bool}
) -> {RRounds.Seen.takes(r2, RRounds.Chain.seen(bs, v, t)) == True{}: Bool} -> {RRounds.Seen.takes(r2, RRounds.Chain.seen(bs2, v, t)) == True{}: Bool}:
  Lists.Maybe.by(
    RRounds.Seen,
    z => {RRounds.Seen.takes(r2, z) == True{}: Bool} -> {RRounds.Seen.takes(r2, RRounds.Chain.seen(bs2, v, t)) == True{}: Bool},
    RRounds.Chain.seen(bs, v, t),
    en => h => Empty.absurd({RRounds.Seen.takes(r2, RRounds.Chain.seen(bs2, v, t)) == True{}: Bool}, Shared.Bool.false_ne_true(h)),
    +m0 => e0 => h => (
      %Equal.sym(Maybe<&2, RRounds.Seen>, RRounds.Chain.seen(bs2, v, t), Some{m0}, Chain.seen_grows(bs, bs2, v, t, m0, hg)(e0)): {RRounds.Seen.takes(r2, _) == True{}: Bool}
      h)
  )

# a vote that counts among the ballots counts among the ballots that they
# grew to
def Ballot.counts_grows(
  +bs: List<&2, RRounds.Ballot>,
  +bs2: List<&2, RRounds.Ballot>,
  +v: String,
  +r: Nat,
  b: RRounds.Ballot,
  +hg: {Ballots.grown(bs, bs2) == True{}: Bool}
) -> {
  RRounds.Ballot.counts(RRounds.Roll{bs, v, r}, b) == True{}: Bool
} -> {RRounds.Ballot.counts(RRounds.Roll{bs2, v, r}, b) == True{}: Bool}:
  match b:
    case RRounds.Ballot{w, t, Types.Cast.Pass{r2}}:
      h => h
    case RRounds.Ballot{+w, +t, Types.Cast.Vote{+r2, +p, +basis}}:
      +h => Shared.Bool.and_both(
        Bool.and(String.eq(w, v), Nat.is_eq(r2, r)),
        Bool.and(RRounds.Seen.takes(r2, RRounds.Chain.seen(bs2, v, t)), RRounds.Cast.is(Types.Cast.Vote{r2, p, basis}, RRounds.Ballots.at(bs2, v, t)))
      )(
        Shared.Bool.and_true_left(Bool.and(String.eq(w, v), Nat.is_eq(r2, r)), Bool.and(RRounds.Seen.takes(r2, RRounds.Chain.seen(bs, v, t)), RRounds.Cast.is(Types.Cast.Vote{r2, p, basis}, RRounds.Ballots.at(bs, v, t))))(h)
      )(
        Shared.Bool.and_both(
          RRounds.Seen.takes(r2, RRounds.Chain.seen(bs2, v, t)),
          RRounds.Cast.is(Types.Cast.Vote{r2, p, basis}, RRounds.Ballots.at(bs2, v, t))
        )(
          Seen.takes_grows(bs, bs2, v, t, r2, hg)(Shared.Bool.and_true_left(RRounds.Seen.takes(r2, RRounds.Chain.seen(bs, v, t)), RRounds.Cast.is(Types.Cast.Vote{r2, p, basis}, RRounds.Ballots.at(bs, v, t)))(Shared.Bool.and_true_right(Bool.and(String.eq(w, v), Nat.is_eq(r2, r)), Bool.and(RRounds.Seen.takes(r2, RRounds.Chain.seen(bs, v, t)), RRounds.Cast.is(Types.Cast.Vote{r2, p, basis}, RRounds.Ballots.at(bs, v, t))))(h)))
        )(
          Cast.is_of(
            Types.Cast.Vote{r2, p, basis},
            RRounds.Ballots.at(bs2, v, t),
            Ballots.at_grows(bs, bs2, v, t, Types.Cast.Vote{r2, p, basis})(hg)(
              Cast.is_some(Types.Cast.Vote{r2, p, basis}, RRounds.Ballots.at(bs, v, t))(Shared.Bool.and_true_right(RRounds.Seen.takes(r2, RRounds.Chain.seen(bs, v, t)), RRounds.Cast.is(Types.Cast.Vote{r2, p, basis}, RRounds.Ballots.at(bs, v, t)))(Shared.Bool.and_true_right(Bool.and(String.eq(w, v), Nat.is_eq(r2, r)), Bool.and(RRounds.Seen.takes(r2, RRounds.Chain.seen(bs, v, t)), RRounds.Cast.is(Types.Cast.Vote{r2, p, basis}, RRounds.Ballots.at(bs, v, t))))(h)))
            )
          )
        )
      )

# Rounds that decide
# ------------------

# what is known of the lead of the round r of the slot k among bs, where the
# nodes ds decide
def Round.mind(
  +bs: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +r: Nat
) -> RRounds.Mind:
  RRounds.Lead.mind(bs, ds, k, r, RRounds.Rounds.minds(bs, ds, k, r))

# the round r decides the pick pk for the slot k among bs, where the nodes ds
# decide
def Round.Won(
  bs: List<&2, RRounds.Ballot>,
  ds: List<&2, String>,
  k: Nat,
  r: Nat,
  pk: Types.Pick
) -> Data:
  {RRounds.Round.won(bs, ds, r, Round.mind(bs, ds, k, r)) == Some{pk}: Maybe<&2, Types.Pick>}

# Numbers and lists
# -----------------

# a number and 0 are the number
def Nat.add_zero(a: Nat) -> {Nat.add(a, 0n) == a: Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, 0n), p, Nat.add_zero(p))

# a number and 1 are the next number
def Nat.add_one(a: Nat) -> {Nat.add(a, 1n) == 1n+a: Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, 1n), 1n+p, Nat.add_one(p))

# what t is above r, and one more than r, are one more than t
def Nat.add_sub_succ(
  r: Nat,
  t: Nat
) -> {Nat.is_le(r, t) == True{}: Bool} -> {Nat.add(Nat.sub(t, r), 1n+r) == 1n+t: Nat}:
  match r t:
    case 0n 0n:
      h => {==}
    case 0n 1n+tp:
      h => Equal.cong(Nat, Nat, z => 1n+z, Nat.add(tp, 1n), 1n+tp, Nat.add_one(tp))
    case 1n+rp 0n:
      h => Empty.absurd({Nat.add(Nat.sub(0n, 1n+rp), 1n+(1n+rp)) == 1n: Nat}, Shared.Bool.false_ne_true(h))
    case 1n+(+rp) 1n+(+tp):
      h => Equal.trans(
        Nat,
        Nat.add(Nat.sub(tp, rp), 1n+(1n+rp)),
        1n+Nat.add(Nat.sub(tp, rp), 1n+rp),
        1n+(1n+tp),
        Shared.Nat.add_succ(Nat.sub(tp, rp), 1n+rp),
        Equal.cong(
          Nat,
          Nat,
          z => 1n+z,
          Nat.add(Nat.sub(tp, rp), 1n+rp),
          1n+tp,
          Nat.add_sub_succ(rp, tp)(h)
        )
      )

# a list with one more item at its end is one longer
def Minds.length_snoc(
  xs: List<&2, RRounds.Mind>,
  -m: RRounds.Mind
) -> {List.length(&2, RRounds.Mind, List.append(&2, RRounds.Mind, xs, [m])) == 1n+List.length(&2, RRounds.Mind, xs): Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{y, rest}:
      Equal.cong(
        Nat,
        Nat,
        z => 1n+z,
        List.length(&2, RRounds.Mind, List.append(&2, RRounds.Mind, rest, [m])),
        1n+List.length(&2, RRounds.Mind, rest),
        Minds.length_snoc(rest, m)
      )

# the leads of the rounds below n are n
def Minds.length(
  +bs: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  n: Nat
) -> {List.length(&2, RRounds.Mind, RRounds.Rounds.minds(bs, ds, k, n)) == n: Nat}:
  match n:
    case 0n:
      {==}
    case 1n+(+j):
      Equal.trans(
        Nat,
        List.length(&2, RRounds.Mind, List.append(&2, RRounds.Mind, RRounds.Rounds.minds(bs, ds, k, j), [Round.mind(bs, ds, k, j)])),
        1n+List.length(&2, RRounds.Mind, RRounds.Rounds.minds(bs, ds, k, j)),
        1n+j,
        Minds.length_snoc(RRounds.Rounds.minds(bs, ds, k, j), Round.mind(bs, ds, k, j)),
        Equal.cong(Nat, Nat, z => 1n+z, List.length(&2, RRounds.Mind, RRounds.Rounds.minds(bs, ds, k, j)), j, Minds.length(bs, ds, k, j))
      )

# a pick, or else nothing, is the pick
def Won.or_none(x: Maybe<&2, Types.Pick>) -> {RRounds.Rounds.won.or(x, u => None{}) == x: Maybe<&2, Types.Pick>}:
  match x:
    case None{}:
      {==}
    case Some{p}:
      {==}

# the first of the rounds xs and then one more round that decides: the first
# of xs that does, or else that round
def Rounds.won_snoc(
  xs: List<&2, RRounds.Mind>,
  +m: RRounds.Mind,
  +bs: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +r0: Nat
) -> {
  RRounds.Rounds.won(List.append(&2, RRounds.Mind, xs, [m]), bs, ds, r0)
    == RRounds.Rounds.won.or(
      RRounds.Rounds.won(xs, bs, ds, r0),
      u => RRounds.Round.won(bs, ds, Nat.add(List.length(&2, RRounds.Mind, xs), r0), m)
    ): Maybe<&2, Types.Pick>
}:
  match xs:
    case Nil{}:
      Won.or_none(RRounds.Round.won(bs, ds, r0, m))
    case Con{+y, +rest}:
      Lists.Maybe.by(
        Types.Pick,
        z => {
          RRounds.Rounds.won.or(z, u => RRounds.Rounds.won(List.append(&2, RRounds.Mind, rest, [m]), bs, ds, 1n+r0))
            == RRounds.Rounds.won.or(
              RRounds.Rounds.won.or(z, u => RRounds.Rounds.won(rest, bs, ds, 1n+r0)),
              u => RRounds.Round.won(bs, ds, 1n+Nat.add(List.length(&2, RRounds.Mind, rest), r0), m)
            ): Maybe<&2, Types.Pick>
        },
        RRounds.Round.won(bs, ds, r0, y),
        en => (
          %Shared.Nat.add_succ(List.length(&2, RRounds.Mind, rest), r0): {RRounds.Rounds.won(List.append(&2, RRounds.Mind, rest, [m]), bs, ds, 1n+r0) == RRounds.Rounds.won.or(RRounds.Rounds.won(rest, bs, ds, 1n+r0), u => RRounds.Round.won(bs, ds, _, m)): Maybe<&2, Types.Pick>}
          Rounds.won_snoc(rest, m, bs, ds, 1n+r0)),
        +p => ep => {==}
      )

# the first of the rounds up to j that decides: the first of those below j,
# or else the round j
def Slot.won_step(
  +bs: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +j: Nat
) -> {
  RRounds.Rounds.won(RRounds.Rounds.minds(bs, ds, k, 1n+j), bs, ds, 0n) == RRounds.Rounds.won.or(RRounds.Rounds.won(RRounds.Rounds.minds(bs, ds, k, j), bs, ds, 0n), u => RRounds.Round.won(bs, ds, j, Round.mind(bs, ds, k, j))): Maybe<&2, Types.Pick>
}:
  %Nat.add_zero(j): {RRounds.Rounds.won(RRounds.Rounds.minds(bs, ds, k, 1n+j), bs, ds, 0n) == RRounds.Rounds.won.or(RRounds.Rounds.won(RRounds.Rounds.minds(bs, ds, k, j), bs, ds, 0n), u => RRounds.Round.won(bs, ds, _, Round.mind(bs, ds, k, j))): Maybe<&2, Types.Pick>}
  %Minds.length(bs, ds, k, j): {RRounds.Rounds.won(RRounds.Rounds.minds(bs, ds, k, 1n+j), bs, ds, 0n) == RRounds.Rounds.won.or(RRounds.Rounds.won(RRounds.Rounds.minds(bs, ds, k, j), bs, ds, 0n), u => RRounds.Round.won(bs, ds, Nat.add(_, 0n), Round.mind(bs, ds, k, j))): Maybe<&2, Types.Pick>}
  Rounds.won_snoc(RRounds.Rounds.minds(bs, ds, k, j), Round.mind(bs, ds, k, j), bs, ds, 0n)

# a round below n decided the pick that the first of the rounds below n
# decided
def Slot.decided_won.go(
  n: Nat,
  +bs: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +pk: Types.Pick
) -> {RRounds.Rounds.won(RRounds.Rounds.minds(bs, ds, k, n), bs, ds, 0n) == Some{pk}: Maybe<&2, Types.Pick>} -> Exists(Nat, r => Round.Won(bs, ds, k, r, pk)):
  match n:
    case 0n:
      h => Empty.absurd(
        Exists(Nat, r => Round.Won(bs, ds, k, r, pk)),
        Shared.Maybe.none_ne_some(Types.Pick, pk, h)
      )
    case 1n+(+j):
      h0 => Lists.Maybe.by(
        Types.Pick,
        z => {
          RRounds.Rounds.won.or(z, u => RRounds.Round.won(bs, ds, j, Round.mind(bs, ds, k, j))) == Some{pk}: Maybe<&2, Types.Pick>
        } -> Exists(Nat, r => Round.Won(bs, ds, k, r, pk)),
        RRounds.Rounds.won(RRounds.Rounds.minds(bs, ds, k, j), bs, ds, 0n),
        en => h => (j, h),
        +p => ep => h => Slot.decided_won.go(j, bs, ds, k, pk)(Equal.trans(Maybe<&2, Types.Pick>, RRounds.Rounds.won(RRounds.Rounds.minds(bs, ds, k, j), bs, ds, 0n), Some{p}, Some{pk}, ep, h))
      )(
        Equal.trans(
          Maybe<&2, Types.Pick>,
          RRounds.Rounds.won.or(RRounds.Rounds.won(RRounds.Rounds.minds(bs, ds, k, j), bs, ds, 0n), u => RRounds.Round.won(bs, ds, j, Round.mind(bs, ds, k, j))),
          RRounds.Rounds.won(RRounds.Rounds.minds(bs, ds, k, 1n+j), bs, ds, 0n),
          Some{pk},
          Equal.sym(
            Maybe<&2, Types.Pick>,
            RRounds.Rounds.won(RRounds.Rounds.minds(bs, ds, k, 1n+j), bs, ds, 0n),
            RRounds.Rounds.won.or(RRounds.Rounds.won(RRounds.Rounds.minds(bs, ds, k, j), bs, ds, 0n), u => RRounds.Round.won(bs, ds, j, Round.mind(bs, ds, k, j))),
            Slot.won_step(bs, ds, k, j)
          ),
          h0
        )
      )

# the round of a cast among the ballots that g names is at most the highest
# round of a ballot
def Casts.of_top(
  bs: List<&2, RRounds.Ballot>,
  +v: String,
  +t: Nat,
  +x: Types.Cast
) -> {
  List.contains(~Types.Cast, ~Coded.Cast.is_eq, RRounds.Casts.of(bs, Types.Ref{v, t}), x) == True{}: Bool
} -> {Nat.is_le(RRounds.Cast.round(x), RRounds.Rounds.top(bs)) == True{}: Bool}:
  match bs:
    case Nil{}:
      h => Empty.absurd({Nat.is_le(RRounds.Cast.round(x), 0n) == True{}: Bool}, Shared.Bool.false_ne_true(h))
    case Con{RRounds.Ballot{+w, +u, +y}, +rest}:
      Lists.Bool.by(
        b => {
          List.contains(~Types.Cast, ~Coded.Cast.is_eq, Shared.Maybe.cons(Types.Cast, Shared.Maybe.when(Types.Cast, b, z => Some{y}), RRounds.Casts.of(rest, Types.Ref{v, t})), x) == True{}: Bool
        } -> {Nat.is_le(RRounds.Cast.round(x), Nat.max(RRounds.Cast.round(y), RRounds.Rounds.top(rest))) == True{}: Bool},
        Bool.and(String.eq(w, v), Nat.is_eq(u, t)),
        et => h => Lists.List.contains_cons_by(
          ~Types.Cast,
          ~Coded.Cast.is_eq,
          ~Coded.Cast.laws(),
          {Nat.is_le(RRounds.Cast.round(x), Nat.max(RRounds.Cast.round(y), RRounds.Rounds.top(rest))) == True{}: Bool},
          y,
          RRounds.Casts.of(rest, Types.Ref{v, t}),
          x,
          h,
          e => (
            %e: {Nat.is_le(RRounds.Cast.round(_), Nat.max(RRounds.Cast.round(y), RRounds.Rounds.top(rest))) == True{}: Bool}
            Lists.Nat.le_max_left(RRounds.Cast.round(y), RRounds.Rounds.top(rest))),
          cin => Shared.Nat.le_trans(
            RRounds.Cast.round(x),
            RRounds.Rounds.top(rest),
            Nat.max(RRounds.Cast.round(y), RRounds.Rounds.top(rest))
          )(Casts.of_top(rest, v, t, x)(cin))(Lists.Nat.le_max_right(RRounds.Cast.round(y), RRounds.Rounds.top(rest)))
        ),
        ef => h => Shared.Nat.le_trans(
          RRounds.Cast.round(x),
          RRounds.Rounds.top(rest),
          Nat.max(RRounds.Cast.round(y), RRounds.Rounds.top(rest))
        )(Casts.of_top(rest, v, t, x)(h))(Lists.Nat.le_max_right(RRounds.Cast.round(y), RRounds.Rounds.top(rest)))
      )

# Round.won_top, with the vote
def Round.won_top.fin(
  +bs: List<&2, RRounds.Ballot>,
  +r: Nat,
  +pk: Types.Pick,
  w0: Exists(String, v => Exists(Nat, t => Exists(List<&2, Types.Ref>, b => {List.contains(~Types.Cast, ~Coded.Cast.is_eq, RRounds.Casts.of(bs, Types.Ref{v, t}), Types.Cast.Vote{r, pk, b}) == True{}: Bool})))
) -> {Nat.is_le(r, RRounds.Rounds.top(bs)) == True{}: Bool}:
  (+v, w1) = w0
  (+t, w2) = w1
  (+b, h) = w2
  Casts.of_top(bs, v, t, Types.Cast.Vote{r, pk, b})(h)

# a round that decides is at most the highest round of a ballot
def Round.won_top(
  +bs: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +r: Nat,
  +pk: Types.Pick,
  m: RRounds.Mind
) -> {
  RRounds.Round.won(bs, ds, r, m) == Some{pk}: Maybe<&2, Types.Pick>
} -> {Nat.is_le(r, RRounds.Rounds.top(bs)) == True{}: Bool}:
  h => Round.won_top.fin(bs, r, pk, Round.won_cast(bs, ds, r, pk, m)(h))

# Slot.won_decided.go, with the pick that the rounds before decide
def Slot.won_decided.up(
  +bs: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +j: Nat,
  w0: Exists(Types.Pick, p => {RRounds.Rounds.won(RRounds.Rounds.minds(bs, ds, k, j), bs, ds, 0n) == Some{p}: Maybe<&2, Types.Pick>})
) -> Exists(Types.Pick, p => {RRounds.Rounds.won(RRounds.Rounds.minds(bs, ds, k, 1n+j), bs, ds, 0n) == Some{p}: Maybe<&2, Types.Pick>}):
  (+p, ep) = w0
  %Equal.sym(Maybe<&2, Types.Pick>, RRounds.Rounds.won(RRounds.Rounds.minds(bs, ds, k, 1n+j), bs, ds, 0n), RRounds.Rounds.won.or(RRounds.Rounds.won(RRounds.Rounds.minds(bs, ds, k, j), bs, ds, 0n), u => RRounds.Round.won(bs, ds, j, Round.mind(bs, ds, k, j))), Slot.won_step(bs, ds, k, j)): Exists(Types.Pick, q => {_ == Some{q}: Maybe<&2, Types.Pick>})
  (
    p,
    (
      %Equal.sym(Maybe<&2, Types.Pick>, RRounds.Rounds.won(RRounds.Rounds.minds(bs, ds, k, j), bs, ds, 0n), Some{p}, ep): {RRounds.Rounds.won.or(_, u => RRounds.Round.won(bs, ds, j, Round.mind(bs, ds, k, j))) == Some{p}: Maybe<&2, Types.Pick>}
      {==})
  )

# the first of the rounds up to d above r decides a pick, when the round r
# decides one
def Slot.won_decided.go(
  d: Nat,
  +bs: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +r: Nat,
  +pk: Types.Pick
) -> Round.Won(
  bs,
  ds,
  k,
  r,
  pk
) -> Exists(Types.Pick, p => {RRounds.Rounds.won(RRounds.Rounds.minds(bs, ds, k, Nat.add(d, 1n+r)), bs, ds, 0n) == Some{p}: Maybe<&2, Types.Pick>}):
  match d:
    case 0n:
      hw => (
        %Equal.sym(Maybe<&2, Types.Pick>, RRounds.Rounds.won(RRounds.Rounds.minds(bs, ds, k, 1n+r), bs, ds, 0n), RRounds.Rounds.won.or(RRounds.Rounds.won(RRounds.Rounds.minds(bs, ds, k, r), bs, ds, 0n), u => RRounds.Round.won(bs, ds, r, Round.mind(bs, ds, k, r))), Slot.won_step(bs, ds, k, r)): Exists(Types.Pick, q => {_ == Some{q}: Maybe<&2, Types.Pick>})
        Lists.Maybe.by(
          Types.Pick,
          z => Exists(
            Types.Pick,
            q => {RRounds.Rounds.won.or(z, u => RRounds.Round.won(bs, ds, r, Round.mind(bs, ds, k, r))) == Some{q}: Maybe<&2, Types.Pick>}
          ),
          RRounds.Rounds.won(RRounds.Rounds.minds(bs, ds, k, r), bs, ds, 0n),
          en => (pk, hw),
          +p => ep => (p, {==})
        ))
    case 1n+(+e):
      hw => Slot.won_decided.up(bs, ds, k, Nat.add(e, 1n+r), Slot.won_decided.go(e, bs, ds, k, r, pk)(hw))

# a round decided the pick that is decided
def Slot.decided_won(
  +bs: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +pk: Types.Pick
) -> {
  RRounds.Slot.decided(bs, ds, k) == Some{pk}: Maybe<&2, Types.Pick>
} -> Exists(Nat, r => Round.Won(bs, ds, k, r, pk)):
  h => Slot.decided_won.go(RRounds.Rounds.count(bs), bs, ds, k, pk)(h)

# a slot with a round that decides a pick is decided
def Slot.won_decided(
  +bs: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +r: Nat,
  +pk: Types.Pick
) -> Round.Won(
  bs,
  ds,
  k,
  r,
  pk
) -> Exists(Types.Pick, p => {RRounds.Slot.decided(bs, ds, k) == Some{p}: Maybe<&2, Types.Pick>}):
  +hw => (
    %Nat.add_sub_succ(r, RRounds.Rounds.top(bs))(Round.won_top(bs, ds, r, pk, Round.mind(bs, ds, k, r))(hw)): Exists(Types.Pick, p => {RRounds.Rounds.won(RRounds.Rounds.minds(bs, ds, k, _), bs, ds, 0n) == Some{p}: Maybe<&2, Types.Pick>})
    Slot.won_decided.go(Nat.sub(RRounds.Rounds.top(bs), r), bs, ds, k, r, pk)(hw))

# what is known of a lead stays as the ballots grow: b is a, or a is open
def Mind.le(a: RRounds.Mind, b: RRounds.Mind) -> Bool:
  match a b:
    case RRounds.Mind.Open{} y:
      True{}
    case RRounds.Mind.Void{} RRounds.Mind.Void{}:
      True{}
    case RRounds.Mind.Void{} RRounds.Mind.Open{}:
      False{}
    case RRounds.Mind.Void{} RRounds.Mind.Sound{q}:
      False{}
    case RRounds.Mind.Sound{p} RRounds.Mind.Sound{q}:
      Coded.Pick.is_eq(p, q)
    case RRounds.Mind.Sound{p} RRounds.Mind.Open{}:
      False{}
    case RRounds.Mind.Sound{p} RRounds.Mind.Void{}:
      False{}

# what is known of the lead of a round stays known as the ballots grow: a
# sound lead stays sound, for the same pick, and a void lead stays void
def Round.mind_grows(
  +bs: List<&2, RRounds.Ballot>,
  +bs2: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +r: Nat
) -> {
  Ballots.grown(bs, bs2) == True{}: Bool
} -> {Mind.le(Round.mind(bs, ds, k, r), Round.mind(bs2, ds, k, r)) == True{}: Bool}:
  ?TODO

# more than half of the nodes voted for a pick in a round, with votes that
# count, among the ballots that grew, when they did before
def Tally.most_grows(
  +bs: List<&2, RRounds.Ballot>,
  +bs2: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +r: Nat,
  +p: Types.Pick
) -> {
  Ballots.grown(bs, bs2) == True{}: Bool
} -> {RRounds.Tally.most(bs, ds, r, p) == True{}: Bool} -> {RRounds.Tally.most(bs2, ds, r, p) == True{}: Bool}:
  ?TODO

# Round.won_grows, once what is known of the lead before (m) and after (m2)
# is known
def Round.won_grows.of(
  +bs: List<&2, RRounds.Ballot>,
  +bs2: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +r: Nat,
  +pk: Types.Pick,
  m: RRounds.Mind,
  m2: RRounds.Mind
) -> {
  Mind.le(m, m2) == True{}: Bool
} -> (
  @p: Types.Pick -> {
    RRounds.Tally.most(bs, ds, r, p) == True{}: Bool
  } -> {RRounds.Tally.most(bs2, ds, r, p) == True{}: Bool}
) -> {
  RRounds.Round.won(bs, ds, r, m) == Some{pk}: Maybe<&2, Types.Pick>
} -> {RRounds.Round.won(bs2, ds, r, m2) == Some{pk}: Maybe<&2, Types.Pick>}:
  match m m2:
    case RRounds.Mind.Open{} y:
      hl => hm => h => Empty.absurd(
        {RRounds.Round.won(bs2, ds, r, y) == Some{pk}: Maybe<&2, Types.Pick>},
        Shared.Maybe.none_ne_some(Types.Pick, pk, h)
      )
    case RRounds.Mind.Void{} y:
      hl => hm => h => Empty.absurd(
        {RRounds.Round.won(bs2, ds, r, y) == Some{pk}: Maybe<&2, Types.Pick>},
        Shared.Maybe.none_ne_some(Types.Pick, pk, h)
      )
    case RRounds.Mind.Sound{p} RRounds.Mind.Open{}:
      hl => hm => h => Empty.absurd({None{} == Some{pk}: Maybe<&2, Types.Pick>}, Shared.Bool.false_ne_true(hl))
    case RRounds.Mind.Sound{p} RRounds.Mind.Void{}:
      hl => hm => h => Empty.absurd({None{} == Some{pk}: Maybe<&2, Types.Pick>}, Shared.Bool.false_ne_true(hl))
    case RRounds.Mind.Sound{+p} RRounds.Mind.Sound{+q}:
      hl => hm => (
        %Coded.Pick.is_eq_sound(p, q)(hl): ({RRounds.Round.won(bs, ds, r, RRounds.Mind.Sound{p}) == Some{pk}: Maybe<&2, Types.Pick>} -> {Shared.Maybe.when(Types.Pick, RRounds.Tally.most(bs2, ds, r, _), u => Some{_}) == Some{pk}: Maybe<&2, Types.Pick>})
        Lists.Bool.by(
          b => {
            Shared.Maybe.when(Types.Pick, b, u => Some{p}) == Some{pk}: Maybe<&2, Types.Pick>
          } -> {Shared.Maybe.when(Types.Pick, RRounds.Tally.most(bs2, ds, r, p), u => Some{p}) == Some{pk}: Maybe<&2, Types.Pick>},
          RRounds.Tally.most(bs, ds, r, p),
          et => h => (
            %Equal.sym(Bool, RRounds.Tally.most(bs2, ds, r, p), True{}, hm(p)(et)): {Shared.Maybe.when(Types.Pick, _, u => Some{p}) == Some{pk}: Maybe<&2, Types.Pick>}
            h),
          ef => h => Empty.absurd(
            {Shared.Maybe.when(Types.Pick, RRounds.Tally.most(bs2, ds, r, p), u => Some{p}) == Some{pk}: Maybe<&2, Types.Pick>},
            Shared.Maybe.none_ne_some(Types.Pick, pk, h)
          )
        ))

# a round that decides a pick still does as the ballots grow: the sound votes
# stay sound, and the votes that count still count
def Round.won_grows(
  +bs: List<&2, RRounds.Ballot>,
  +bs2: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +r: Nat,
  +pk: Types.Pick
) -> {Ballots.grown(bs, bs2) == True{}: Bool} -> Round.Won(bs, ds, k, r, pk) -> Round.Won(bs2, ds, k, r, pk):
  +hg => h => Round.won_grows.of(
    bs,
    bs2,
    ds,
    r,
    pk,
    Round.mind(bs, ds, k, r),
    Round.mind(bs2, ds, k, r)
  )(Round.mind_grows(bs, bs2, ds, k, r)(hg))(+p => hm => Tally.most_grows(bs, bs2, ds, r, p)(hg)(hm))(h)

# two rounds of one slot decide one pick: once more than half of the nodes
# cast a sound vote for a pick in a round, every sound vote of a later round
# is for it
def Round.won_one(
  +bs: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +r1: Nat,
  +r2: Nat,
  +p1: Types.Pick,
  +p2: Types.Pick
) -> Round.Won(bs, ds, k, r1, p1) -> Round.Won(bs, ds, k, r2, p2) -> {p1 == p2: Types.Pick}:
  ?TODO

# Slot.decided_grows, with the pick that is decided among the wider ballots
def Slot.decided_grows.fin(
  +bs2: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +r: Nat,
  +pk: Types.Pick,
  +p: Types.Pick,
  +hw: Round.Won(bs2, ds, k, r, pk),
  +hd: {RRounds.Slot.decided(bs2, ds, k) == Some{p}: Maybe<&2, Types.Pick>}
) -> {RRounds.Slot.decided(bs2, ds, k) == Some{pk}: Maybe<&2, Types.Pick>}:
  Ex.by(
    Nat,
    r2 => Round.Won(bs2, ds, k, r2, p),
    {RRounds.Slot.decided(bs2, ds, k) == Some{pk}: Maybe<&2, Types.Pick>},
    Slot.decided_won(bs2, ds, k, p)(hd),
    +r2 => hw2 => (
      %Round.won_one(bs2, ds, k, r2, r, p, pk)(hw2)(hw): {RRounds.Slot.decided(bs2, ds, k) == Some{_}: Maybe<&2, Types.Pick>}
      hd)
  )

# a pick that is decided stays decided as the ballots grow
def Slot.decided_grows(
  +bs: List<&2, RRounds.Ballot>,
  +bs2: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +pk: Types.Pick
) -> {
  Ballots.grown(bs, bs2) == True{}: Bool
} -> {
  RRounds.Slot.decided(bs, ds, k) == Some{pk}: Maybe<&2, Types.Pick>
} -> {RRounds.Slot.decided(bs2, ds, k) == Some{pk}: Maybe<&2, Types.Pick>}:
  +hg => hd => Ex.by(
    Nat,
    r => Round.Won(bs, ds, k, r, pk),
    {RRounds.Slot.decided(bs2, ds, k) == Some{pk}: Maybe<&2, Types.Pick>},
    Slot.decided_won(bs, ds, k, pk)(hd),
    +r => +hw => Ex.by(
      Types.Pick,
      p => {RRounds.Slot.decided(bs2, ds, k) == Some{p}: Maybe<&2, Types.Pick>},
      {RRounds.Slot.decided(bs2, ds, k) == Some{pk}: Maybe<&2, Types.Pick>},
      Slot.won_decided(bs2, ds, k, r, pk)(Round.won_grows(bs, bs2, ds, k, r, pk)(hg)(hw)),
      +p => +hd2 => Slot.decided_grows.fin(
        bs2,
        ds,
        k,
        r,
        pk,
        p,
        Round.won_grows(bs, bs2, ds, k, r, pk)(hg)(hw),
        hd2
      )
    )
  )

# the nodes that decided a pick in one round stay so as the ballots grow
def Slot.backed_grows(
  +bs: List<&2, RRounds.Ballot>,
  +bs2: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +os: List<&2, String>,
  +pk: Types.Pick
) -> {
  Ballots.grown(bs, bs2) == True{}: Bool
} -> {
  RRounds.Slot.backed(bs, ds, k, os, pk) == True{}: Bool
} -> {RRounds.Slot.backed(bs2, ds, k, os, pk) == True{}: Bool}:
  ?TODO

# the ballots hold a vote for the pick that is decided
def Slot.decided_cast(
  +bs: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +pk: Types.Pick
) -> {
  RRounds.Slot.decided(bs, ds, k) == Some{pk}: Maybe<&2, Types.Pick>
} -> Exists(
  String,
  v => Exists(
    Nat,
    t => Exists(
      Nat,
      r => Exists(
        List<&2, Types.Ref>,
        b => {
          List.contains(
            ~Types.Cast,
            ~Coded.Cast.is_eq,
            RRounds.Casts.of(bs, Types.Ref{v, t}),
            Types.Cast.Vote{r, pk, b}
          )
            == True{}: Bool
        }
      )
    )
  )
):
  h => Rounds.won_cast(RRounds.Rounds.minds(bs, ds, k, RRounds.Rounds.count(bs)), bs, ds, 0n, pk)(h)

# the ballots hold a ballot of each of the nodes that decided a pick in one
# round
def Slot.backed_cast(
  +bs: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +os: List<&2, String>,
  +pk: Types.Pick,
  +v: String
) -> {
  RRounds.Slot.backed(bs, ds, k, os, pk) == True{}: Bool
} -> {
  List.contains(~String, ~String.eq, os, v) == True{}: Bool
} -> Exists(
  Nat,
  t => Exists(
    Types.Cast,
    x => {
      List.contains(~Types.Cast, ~Coded.Cast.is_eq, RRounds.Casts.of(bs, Types.Ref{v, t}), x) == True{}: Bool
    }
  )
):
  h => hin => Rounds.back_cast(RRounds.Rounds.minds(bs, ds, k, RRounds.Rounds.count(bs)), bs, os, pk, 0n, v)(h)(hin)

# Ballots and facts
# -----------------

# a ballot among the ballots of a slot, of the facts fs, is one of fs
def Casts.of_in(
  fs: List<&2, Types.Fact>,
  +c: Ledgers.Line,
  +k: Nat,
  +v: String,
  +t: Nat,
  +x: Types.Cast
) -> {
  List.contains(~Types.Cast, ~Coded.Cast.is_eq, RRounds.Casts.of(RRounds.Slot.ballots(fs, c, k), Types.Ref{v, t}), x)
    == True{}: Bool
} -> {
  List.contains(~Types.Fact, ~Coded.Fact.is_eq, fs, Types.Fact.Vote{v, Types.Step.At{c, k, t}, x}) == True{}: Bool
}:
  match fs:
    case Nil{}:
      h => h
    case Con{Types.Fact.Ask{+a}, +rest}:
      h => Shared.List.contains_cons(~Types.Fact, ~Coded.Fact.is_eq, Types.Fact.Ask{a}, rest, Types.Fact.Vote{v, Types.Step.At{c, k, t}, x})(Casts.of_in(rest, c, k, v, t, x)(h))
    case Con{Types.Fact.Vote{+w, Types.Step.Broken{}, +y}, +rest}:
      h => Shared.List.contains_cons(~Types.Fact, ~Coded.Fact.is_eq, Types.Fact.Vote{w, Types.Step.Broken{}, y}, rest, Types.Fact.Vote{v, Types.Step.At{c, k, t}, x})(Casts.of_in(rest, c, k, v, t, x)(h))
    case Con{Types.Fact.Vote{+w, Types.Step.At{+c2, +k2, +u}, +y}, +rest}:
      Lists.Bool.by(
        b => {
          List.contains(~Types.Cast, ~Coded.Cast.is_eq, RRounds.Casts.of(List.filter.put(RRounds.Ballot, RRounds.Ballot{w, u, y}, RRounds.Slot.ballots(rest, c, k), b), Types.Ref{v, t}), x) == True{}: Bool
        } -> {List.contains(~Types.Fact, ~Coded.Fact.is_eq, Types.Fact.Vote{w, Types.Step.At{c2, k2, u}, y} <> rest, Types.Fact.Vote{v, Types.Step.At{c, k, t}, x}) == True{}: Bool},
        Bool.and(Ledgers.Line.is_eq(c2, c), Nat.is_eq(k2, k)),
        +e1 => Lists.Bool.by(
          b => {
            List.contains(~Types.Cast, ~Coded.Cast.is_eq, Shared.Maybe.cons(Types.Cast, Shared.Maybe.when(Types.Cast, b, z => Some{y}), RRounds.Casts.of(RRounds.Slot.ballots(rest, c, k), Types.Ref{v, t})), x) == True{}: Bool
          } -> {List.contains(~Types.Fact, ~Coded.Fact.is_eq, Types.Fact.Vote{w, Types.Step.At{c2, k2, u}, y} <> rest, Types.Fact.Vote{v, Types.Step.At{c, k, t}, x}) == True{}: Bool},
          Bool.and(String.eq(w, v), Nat.is_eq(u, t)),
          +e2 => h => Lists.List.contains_cons_by(
            ~Types.Cast,
            ~Coded.Cast.is_eq,
            ~Coded.Cast.laws(),
            {List.contains(~Types.Fact, ~Coded.Fact.is_eq, Types.Fact.Vote{w, Types.Step.At{c2, k2, u}, y} <> rest, Types.Fact.Vote{v, Types.Step.At{c, k, t}, x}) == True{}: Bool},
            y,
            RRounds.Casts.of(RRounds.Slot.ballots(rest, c, k), Types.Ref{v, t}),
            x,
            h,
            e3 => (
              %Texts.String.eq_sound(w, v)(Shared.Bool.and_true_left(String.eq(w, v), Nat.is_eq(u, t))(e2)): {List.contains(~Types.Fact, ~Coded.Fact.is_eq, Types.Fact.Vote{w, Types.Step.At{c2, k2, u}, y} <> rest, Types.Fact.Vote{_, Types.Step.At{c, k, t}, x}) == True{}: Bool}
              %Ledgers.Line.is_eq_sound(c2, c)(Shared.Bool.and_true_left(Ledgers.Line.is_eq(c2, c), Nat.is_eq(k2, k))(e1)): {List.contains(~Types.Fact, ~Coded.Fact.is_eq, Types.Fact.Vote{w, Types.Step.At{c2, k2, u}, y} <> rest, Types.Fact.Vote{w, Types.Step.At{_, k, t}, x}) == True{}: Bool}
              %Shared.Nat.is_eq_sound(k2, k)(Shared.Bool.and_true_right(Ledgers.Line.is_eq(c2, c), Nat.is_eq(k2, k))(e1)): {List.contains(~Types.Fact, ~Coded.Fact.is_eq, Types.Fact.Vote{w, Types.Step.At{c2, k2, u}, y} <> rest, Types.Fact.Vote{w, Types.Step.At{c2, _, t}, x}) == True{}: Bool}
              %Shared.Nat.is_eq_sound(u, t)(Shared.Bool.and_true_right(String.eq(w, v), Nat.is_eq(u, t))(e2)): {List.contains(~Types.Fact, ~Coded.Fact.is_eq, Types.Fact.Vote{w, Types.Step.At{c2, k2, u}, y} <> rest, Types.Fact.Vote{w, Types.Step.At{c2, k2, _}, x}) == True{}: Bool}
              %e3: {List.contains(~Types.Fact, ~Coded.Fact.is_eq, Types.Fact.Vote{w, Types.Step.At{c2, k2, u}, y} <> rest, Types.Fact.Vote{w, Types.Step.At{c2, k2, u}, _}) == True{}: Bool}
              Lists.List.contains_head(~Types.Fact, ~Coded.Fact.is_eq, ~Coded.Fact.laws(), Types.Fact.Vote{w, Types.Step.At{c2, k2, u}, y}, rest)),
            cin => Shared.List.contains_cons(~Types.Fact, ~Coded.Fact.is_eq, Types.Fact.Vote{w, Types.Step.At{c2, k2, u}, y}, rest, Types.Fact.Vote{v, Types.Step.At{c, k, t}, x})(Casts.of_in(rest, c, k, v, t, x)(cin))
          ),
          e2 => h => Shared.List.contains_cons(~Types.Fact, ~Coded.Fact.is_eq, Types.Fact.Vote{w, Types.Step.At{c2, k2, u}, y}, rest, Types.Fact.Vote{v, Types.Step.At{c, k, t}, x})(Casts.of_in(rest, c, k, v, t, x)(h))
        ),
        e1 => h => Shared.List.contains_cons(~Types.Fact, ~Coded.Fact.is_eq, Types.Fact.Vote{w, Types.Step.At{c2, k2, u}, y}, rest, Types.Fact.Vote{v, Types.Step.At{c, k, t}, x})(Casts.of_in(rest, c, k, v, t, x)(h))
      )

# a ballot among the ballots of a slot, of the facts rest, is among those of
# one more fact and rest
def Casts.of_cons(
  f: Types.Fact,
  +rest: List<&2, Types.Fact>,
  +c: Ledgers.Line,
  +k: Nat,
  +v: String,
  +t: Nat,
  +x: Types.Cast
) -> {List.contains(~Types.Cast, ~Coded.Cast.is_eq, RRounds.Casts.of(RRounds.Slot.ballots(rest, c, k), Types.Ref{v, t}), x) == True{}: Bool} -> {List.contains(~Types.Cast, ~Coded.Cast.is_eq, RRounds.Casts.of(RRounds.Slot.ballots(f <> rest, c, k), Types.Ref{v, t}), x) == True{}: Bool}:
  match f:
    case Types.Fact.Ask{a}:
      h => h
    case Types.Fact.Vote{w, Types.Step.Broken{}, y}:
      h => h
    case Types.Fact.Vote{+w, Types.Step.At{+c2, +k2, +u}, +y}:
      Lists.Bool.by(
        b => {List.contains(~Types.Cast, ~Coded.Cast.is_eq, RRounds.Casts.of(RRounds.Slot.ballots(rest, c, k), Types.Ref{v, t}), x) == True{}: Bool} -> {
          List.contains(~Types.Cast, ~Coded.Cast.is_eq, RRounds.Casts.of(List.filter.put(RRounds.Ballot, RRounds.Ballot{w, u, y}, RRounds.Slot.ballots(rest, c, k), b), Types.Ref{v, t}), x) == True{}: Bool
        },
        Bool.and(Ledgers.Line.is_eq(c2, c), Nat.is_eq(k2, k)),
        e1 => Lists.Bool.by(
          b => {List.contains(~Types.Cast, ~Coded.Cast.is_eq, RRounds.Casts.of(RRounds.Slot.ballots(rest, c, k), Types.Ref{v, t}), x) == True{}: Bool} -> {
            List.contains(~Types.Cast, ~Coded.Cast.is_eq, Shared.Maybe.cons(Types.Cast, Shared.Maybe.when(Types.Cast, b, z => Some{y}), RRounds.Casts.of(RRounds.Slot.ballots(rest, c, k), Types.Ref{v, t})), x) == True{}: Bool
          },
          Bool.and(String.eq(w, v), Nat.is_eq(u, t)),
          e2 => h => Shared.List.contains_cons(~Types.Cast, ~Coded.Cast.is_eq, y, RRounds.Casts.of(RRounds.Slot.ballots(rest, c, k), Types.Ref{v, t}), x)(h),
          e2 => h => h
        ),
        e1 => h => h
      )

# a ballot for a slot among the facts fs is among the ballots of the slot
def Casts.in_of(
  fs: List<&2, Types.Fact>,
  +c: Ledgers.Line,
  +k: Nat,
  +v: String,
  +t: Nat,
  +x: Types.Cast
) -> {
  List.contains(~Types.Fact, ~Coded.Fact.is_eq, fs, Types.Fact.Vote{v, Types.Step.At{c, k, t}, x}) == True{}: Bool
} -> {List.contains(~Types.Cast, ~Coded.Cast.is_eq, RRounds.Casts.of(RRounds.Slot.ballots(fs, c, k), Types.Ref{v, t}), x) == True{}: Bool}:
  match fs:
    case Nil{}:
      h => h
    case Con{+f, +rest}:
      hin => Lists.List.contains_cons_by(
        ~Types.Fact,
        ~Coded.Fact.is_eq,
        ~Coded.Fact.laws(),
        {List.contains(~Types.Cast, ~Coded.Cast.is_eq, RRounds.Casts.of(RRounds.Slot.ballots(f <> rest, c, k), Types.Ref{v, t}), x) == True{}: Bool},
        f,
        rest,
        Types.Fact.Vote{v, Types.Step.At{c, k, t}, x},
        hin,
        e => (
          %Equal.sym(Types.Fact, f, Types.Fact.Vote{v, Types.Step.At{c, k, t}, x}, e): {List.contains(~Types.Cast, ~Coded.Cast.is_eq, RRounds.Casts.of(RRounds.Slot.ballots(_ <> rest, c, k), Types.Ref{v, t}), x) == True{}: Bool}
          %Equal.sym(Bool, Ledgers.Line.is_eq(c, c), True{}, Ledgers.Line.is_eq_refl(c)): {List.contains(~Types.Cast, ~Coded.Cast.is_eq, RRounds.Casts.of(List.filter.put(RRounds.Ballot, RRounds.Ballot{v, t, x}, RRounds.Slot.ballots(rest, c, k), Bool.and(_, Nat.is_eq(k, k))), Types.Ref{v, t}), x) == True{}: Bool}
          %Equal.sym(Bool, Nat.is_eq(k, k), True{}, Shared.Nat.is_eq_refl(k)): {List.contains(~Types.Cast, ~Coded.Cast.is_eq, RRounds.Casts.of(List.filter.put(RRounds.Ballot, RRounds.Ballot{v, t, x}, RRounds.Slot.ballots(rest, c, k), _), Types.Ref{v, t}), x) == True{}: Bool}
          %Equal.sym(Bool, String.eq(v, v), True{}, Texts.String.eq_refl(v)): {List.contains(~Types.Cast, ~Coded.Cast.is_eq, Shared.Maybe.cons(Types.Cast, Shared.Maybe.when(Types.Cast, Bool.and(_, Nat.is_eq(t, t)), z => Some{x}), RRounds.Casts.of(RRounds.Slot.ballots(rest, c, k), Types.Ref{v, t})), x) == True{}: Bool}
          %Equal.sym(Bool, Nat.is_eq(t, t), True{}, Shared.Nat.is_eq_refl(t)): {List.contains(~Types.Cast, ~Coded.Cast.is_eq, Shared.Maybe.cons(Types.Cast, Shared.Maybe.when(Types.Cast, _, z => Some{x}), RRounds.Casts.of(RRounds.Slot.ballots(rest, c, k), Types.Ref{v, t})), x) == True{}: Bool}
          Lists.List.contains_head(~Types.Cast, ~Coded.Cast.is_eq, ~Coded.Cast.laws(), x, RRounds.Casts.of(RRounds.Slot.ballots(rest, c, k), Types.Ref{v, t}))),
        cin => Casts.of_cons(f, rest, c, k, v, t, x)(Casts.in_of(rest, c, k, v, t, x)(cin))
      )

# a ballot among the ballots of a slot is a fact of the set
def Casts.of_has(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +v: String,
  +t: Nat,
  +x: Types.Cast
) -> {
  List.contains(~Types.Cast, ~Coded.Cast.is_eq, RRounds.Casts.of(Slot.ballots(s, c, k), Types.Ref{v, t}), x)
    == True{}: Bool
} -> {Facts.Facts.has(s, Types.Fact.Vote{v, Types.Step.At{c, k, t}, x}) == True{}: Bool}:
  h => Facts.Facts.in_has(s, Types.Fact.Vote{v, Types.Step.At{c, k, t}, x})(Casts.of_in(Facts.Facts.list(s), c, k, v, t, x)(h))

# a ballot that the set holds for a slot is among the ballots of the slot
def Casts.has_of(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +v: String,
  +t: Nat,
  +x: Types.Cast
) -> {
  Facts.Facts.has(s, Types.Fact.Vote{v, Types.Step.At{c, k, t}, x}) == True{}: Bool
} -> {
  List.contains(~Types.Cast, ~Coded.Cast.is_eq, RRounds.Casts.of(Slot.ballots(s, c, k), Types.Ref{v, t}), x)
    == True{}: Bool
}:
  h => Casts.in_of(Facts.Facts.list(s), c, k, v, t, x)(Facts.Facts.has_in(s, Types.Fact.Vote{v, Types.Step.At{c, k, t}, x})(h))

# How the ballots of a slot grow
# ------------------------------

# each ballot for the slot k of the line c among the facts fs, when it is
# read from bs0, is read from bs2
def Slot.Sure(
  fs: List<&2, Types.Fact>,
  bs0: List<&2, RRounds.Ballot>,
  bs2: List<&2, RRounds.Ballot>,
  c: Ledgers.Line,
  k: Nat
) -> Type:
  @+v: String -> @+t: Nat -> @+x: Types.Cast -> {
    List.contains(~Types.Fact, ~Coded.Fact.is_eq, fs, Types.Fact.Vote{v, Types.Step.At{c, k, t}, x}) == True{}: Bool
  } -> {Ballot.sure(Grow{bs0, bs2}, RRounds.Ballot{v, t, x}) == True{}: Bool}

# each ballot of the slot, of the facts fs, is sure, when each ballot for the
# slot among fs is
def Slot.grown.go(
  fs: List<&2, Types.Fact>,
  +bs0: List<&2, RRounds.Ballot>,
  +bs2: List<&2, RRounds.Ballot>,
  +c: Ledgers.Line,
  +k: Nat,
  g: Slot.Sure(fs, bs0, bs2, c, k)
) -> {Shared.List.holds(~RRounds.Ballot, ~Grow, ~Ballot.sure, RRounds.Slot.ballots(fs, c, k), Grow{bs0, bs2}) == True{}: Bool}:
  match fs:
    case Nil{}:
      {==}
    case Con{Types.Fact.Ask{+a}, +rest}:
      Slot.grown.go(rest, bs0, bs2, c, k, +v => +t => +x => cin => g(v)(t)(x)(Shared.List.contains_cons(~Types.Fact, ~Coded.Fact.is_eq, Types.Fact.Ask{a}, rest, Types.Fact.Vote{v, Types.Step.At{c, k, t}, x})(cin)))
    case Con{Types.Fact.Vote{+w, Types.Step.Broken{}, +y}, +rest}:
      Slot.grown.go(rest, bs0, bs2, c, k, +v => +t => +x => cin => g(v)(t)(x)(Shared.List.contains_cons(~Types.Fact, ~Coded.Fact.is_eq, Types.Fact.Vote{w, Types.Step.Broken{}, y}, rest, Types.Fact.Vote{v, Types.Step.At{c, k, t}, x})(cin)))
    case Con{Types.Fact.Vote{+w, Types.Step.At{+c2, +k2, +u}, +y}, +rest}:
      Lists.Bool.by(
        b => Slot.Sure(Types.Fact.Vote{w, Types.Step.At{c2, k2, u}, y} <> rest, bs0, bs2, c, k) -> {
          Shared.List.holds(~RRounds.Ballot, ~Grow, ~Ballot.sure, List.filter.put(RRounds.Ballot, RRounds.Ballot{w, u, y}, RRounds.Slot.ballots(rest, c, k), b), Grow{bs0, bs2}) == True{}: Bool
        },
        Bool.and(Ledgers.Line.is_eq(c2, c), Nat.is_eq(k2, k)),
        +e1 => g0 => Facts.Case.all_one(
          Slot.Sure(Types.Fact.Vote{w, Types.Step.At{c2, k2, u}, y} <> rest, bs0, bs2, c, k),
          Ballot.sure(Grow{bs0, bs2}, RRounds.Ballot{w, u, y}),
          z0 => Shared.List.holds(~RRounds.Ballot, ~Grow, ~Ballot.sure, RRounds.Slot.ballots(rest, c, k), Grow{bs0, bs2}),
          g0,
          g => g(w)(u)(y)((
              %Ledgers.Line.is_eq_sound(c2, c)(Shared.Bool.and_true_left(Ledgers.Line.is_eq(c2, c), Nat.is_eq(k2, k))(e1)): {List.contains(~Types.Fact, ~Coded.Fact.is_eq, Types.Fact.Vote{w, Types.Step.At{c2, k2, u}, y} <> rest, Types.Fact.Vote{w, Types.Step.At{_, k, u}, y}) == True{}: Bool}
              %Shared.Nat.is_eq_sound(k2, k)(Shared.Bool.and_true_right(Ledgers.Line.is_eq(c2, c), Nat.is_eq(k2, k))(e1)): {List.contains(~Types.Fact, ~Coded.Fact.is_eq, Types.Fact.Vote{w, Types.Step.At{c2, k2, u}, y} <> rest, Types.Fact.Vote{w, Types.Step.At{c2, _, u}, y}) == True{}: Bool}
              Lists.List.contains_head(~Types.Fact, ~Coded.Fact.is_eq, ~Coded.Fact.laws(), Types.Fact.Vote{w, Types.Step.At{c2, k2, u}, y}, rest))),
          g => Slot.grown.go(rest, bs0, bs2, c, k, +v => +t => +x => cin => g(v)(t)(x)(Shared.List.contains_cons(~Types.Fact, ~Coded.Fact.is_eq, Types.Fact.Vote{w, Types.Step.At{c2, k2, u}, y}, rest, Types.Fact.Vote{v, Types.Step.At{c, k, t}, x})(cin)))
        ),
        e1 => g => Slot.grown.go(rest, bs0, bs2, c, k, +v => +t => +x => cin => g(v)(t)(x)(Shared.List.contains_cons(~Types.Fact, ~Coded.Fact.is_eq, Types.Fact.Vote{w, Types.Step.At{c2, k2, u}, y}, rest, Types.Fact.Vote{v, Types.Step.At{c, k, t}, x})(cin)))
      )(g)

# a ballot that is the one of its voter with its number in bs2 is sure
def Ballot.sure_of(
  +bs: List<&2, RRounds.Ballot>,
  +bs2: List<&2, RRounds.Ballot>,
  +v: String,
  +t: Nat,
  +x: Types.Cast,
  e: {RRounds.Ballots.at(bs2, v, t) == Some{x}: Maybe<&2, Types.Cast>}
) -> {Ballot.sure(Grow{bs, bs2}, RRounds.Ballot{v, t, x}) == True{}: Bool}:
  Facts.Case.or_right(
    Bool.not(RRounds.Cast.is(x, RRounds.Ballots.at(bs, v, t))),
    RRounds.Cast.is(x, RRounds.Ballots.at(bs2, v, t))
  )(Cast.is_of(x, RRounds.Ballots.at(bs2, v, t), e))

# Slot.grown_wider, for a ballot that the wider set holds
def Slot.grown_wider.of(
  +s: Facts.Facts(),
  +s2: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +hl: {Facts.Facts.liars(s2) == []: List<&2, String>},
  +v: String,
  +t: Nat,
  +x: Types.Cast,
  +hx: {Facts.Facts.has(s2, Types.Fact.Vote{v, Types.Step.At{c, k, t}, x}) == True{}: Bool}
) -> {Ballot.sure(Grow{Slot.ballots(s, c, k), Slot.ballots(s2, c, k)}, RRounds.Ballot{v, t, x}) == True{}: Bool}:
  Ballot.sure_of(
    Slot.ballots(s, c, k),
    Slot.ballots(s2, c, k),
    v,
    t,
    x,
    Casts.agreed(
      RRounds.Casts.of(Slot.ballots(s2, c, k), Types.Ref{v, t}),
      x,
      Casts.has_of(s2, c, k, v, t, x)(hx),
      List.holds_of(
        ~Types.Cast,
        ~Types.Cast,
        ~Coded.Cast.is_eq,
        ~Coded.Cast.is_eq,
        ~Coded.Cast.laws(),
        RRounds.Casts.of(Slot.ballots(s2, c, k), Types.Ref{v, t}),
        x,
        +y => cy => (
          %Facts.Facts.honest_one(s2, v, Types.Step.At{c, k, t}, x, y)(hl)(hx)(Casts.of_has(s2, c, k, v, t, y)(cy)): {Coded.Cast.is_eq(x, _) == True{}: Bool}
          Coded.Cast.is_eq_refl(x))
      )
    )
  )

# the ballots of a slot grow as the facts grow, while the wider set names no
# liar
def Slot.grown_wider(
  +s: Facts.Facts(),
  +s2: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat
) -> {
  Facts.Facts.wider(s, s2) == True{}: Bool
} -> {
  Facts.Facts.liars(s2) == []: List<&2, String>
} -> {Ballots.grown(Slot.ballots(s, c, k), Slot.ballots(s2, c, k)) == True{}: Bool}:
  +w => +h => Slot.grown.go(
    Facts.Facts.list(s),
    Slot.ballots(s, c, k),
    Slot.ballots(s2, c, k),
    c,
    k,
    +v => +t => +x => hin => Slot.grown_wider.of(
      s,
      s2,
      c,
      k,
      h,
      v,
      t,
      x,
      Facts.Facts.wider_has(s, s2, Types.Fact.Vote{v, Types.Step.At{c, k, t}, x})(w)(Facts.Facts.in_has(s, Types.Fact.Vote{v, Types.Step.At{c, k, t}, x})(hin))
    )
  )

# a set that holds each ballot of s for a slot holds a ballot that s holds
# for it
def Slot.kept_has(
  +s: Facts.Facts(),
  +s2: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +v: String,
  +t: Nat,
  +x: Types.Cast
) -> {
  Slot.kept(s, s2, c, k) == True{}: Bool
} -> {Facts.Facts.has(s, Types.Fact.Vote{v, Types.Step.At{c, k, t}, x}) == True{}: Bool} -> {Facts.Facts.has(s2, Types.Fact.Vote{v, Types.Step.At{c, k, t}, x}) == True{}: Bool}:
  hk => hx => (
    %Ledgers.Line.is_eq_refl(c): {Bool.or(Bool.not(Bool.and(_, True{})), Facts.Facts.has(s2, Types.Fact.Vote{v, Types.Step.At{c, k, t}, x})) == True{}: Bool}
    %Shared.Nat.is_eq_refl(k): {Bool.or(Bool.not(Bool.and(Ledgers.Line.is_eq(c, c), _)), Facts.Facts.has(s2, Types.Fact.Vote{v, Types.Step.At{c, k, t}, x})) == True{}: Bool}
    Lists.List.holds_in(
      ~Types.Fact,
      ~Kept,
      ~Fact.kept,
      ~Coded.Fact.is_eq,
      ~Coded.Fact.laws(),
      Facts.Facts.list(s),
      Kept{Facts.Facts.crit(s2), c, k},
      Types.Fact.Vote{v, Types.Step.At{c, k, t}, x}
    )(hk)(Facts.Facts.has_in(s, Types.Fact.Vote{v, Types.Step.At{c, k, t}, x})(hx)))

# Slot.grown_kept, for a ballot that s holds
def Slot.grown_kept.of(
  +s: Facts.Facts(),
  +s2: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +hk1: {Slot.kept(s, s2, c, k) == True{}: Bool},
  +hk2: {Slot.kept(s2, s, c, k) == True{}: Bool},
  +v: String,
  +t: Nat,
  +x: Types.Cast,
  +hx: {Facts.Facts.has(s, Types.Fact.Vote{v, Types.Step.At{c, k, t}, x}) == True{}: Bool}
) -> {Ballot.sure(Grow{Slot.ballots(s, c, k), Slot.ballots(s2, c, k)}, RRounds.Ballot{v, t, x}) == True{}: Bool}:
  Lists.Bool.by(
    b => {
      Bool.or(Bool.not(b), RRounds.Cast.is(x, RRounds.Ballots.at(Slot.ballots(s2, c, k), v, t))) == True{}: Bool
    },
    RRounds.Cast.is(x, RRounds.Ballots.at(Slot.ballots(s, c, k), v, t)),
    et => Cast.is_of(
      x,
      RRounds.Ballots.at(Slot.ballots(s2, c, k), v, t),
      Casts.agreed(
        RRounds.Casts.of(Slot.ballots(s2, c, k), Types.Ref{v, t}),
        x,
        Casts.has_of(s2, c, k, v, t, x)(Slot.kept_has(s, s2, c, k, v, t, x)(hk1)(hx)),
        List.holds_of(
          ~Types.Cast,
          ~Types.Cast,
          ~Coded.Cast.is_eq,
          ~Coded.Cast.is_eq,
          ~Coded.Cast.laws(),
          RRounds.Casts.of(Slot.ballots(s2, c, k), Types.Ref{v, t}),
          x,
          +y => cy => Lists.List.holds_in(
            ~Types.Cast,
            ~Types.Cast,
            ~Coded.Cast.is_eq,
            ~Coded.Cast.is_eq,
            ~Coded.Cast.laws(),
            RRounds.Casts.of(Slot.ballots(s, c, k), Types.Ref{v, t}),
            x,
            y
          )(
            Shared.Bool.and_true_right(
              Bool.not(List.is_empty(&2, Types.Cast, RRounds.Casts.of(Slot.ballots(s, c, k), Types.Ref{v, t}))),
              Shared.List.holds(~Types.Cast, ~Types.Cast, ~Coded.Cast.is_eq, RRounds.Casts.of(Slot.ballots(s, c, k), Types.Ref{v, t}), x)
            )(
              Shared.List.agreed_holds(
                ~Types.Cast,
                ~Coded.Cast.is_eq,
                ~Coded.Cast.laws(),
                RRounds.Casts.of(Slot.ballots(s, c, k), Types.Ref{v, t}),
                x
              )(Cast.is_some(x, RRounds.Ballots.at(Slot.ballots(s, c, k), v, t))(et))
            )
          )(
            Casts.has_of(s, c, k, v, t, y)(
              Slot.kept_has(s2, s, c, k, v, t, y)(hk2)(Casts.of_has(s2, c, k, v, t, y)(cy))
            )
          )
        )
      )
    ),
    ef => {==}
  )

# the ballots of a slot grow, between two sets that hold the same ballots for
# the slot
def Slot.grown_kept(
  +s: Facts.Facts(),
  +s2: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat
) -> {
  Slot.kept(s, s2, c, k) == True{}: Bool
} -> {
  Slot.kept(s2, s, c, k) == True{}: Bool
} -> {Ballots.grown(Slot.ballots(s, c, k), Slot.ballots(s2, c, k)) == True{}: Bool}:
  +a => +b => Slot.grown.go(
    Facts.Facts.list(s),
    Slot.ballots(s, c, k),
    Slot.ballots(s2, c, k),
    c,
    k,
    +v => +t => +x => hin => Slot.grown_kept.of(
      s,
      s2,
      c,
      k,
      a,
      b,
      v,
      t,
      x,
      Facts.Facts.in_has(s, Types.Fact.Vote{v, Types.Step.At{c, k, t}, x})(hin)
    )
  )

# Laws of sets of facts
# ---------------------

# a decided pick stays decided as the facts grow, while the wider set names
# no liar
def Votes.decided_stays(
  +s: Facts.Facts(),
  +s2: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +ds: List<&2, String>,
  +pk: Types.Pick
) -> {
  Facts.Facts.wider(s, s2) == True{}: Bool
} -> {
  Facts.Facts.liars(s2) == []: List<&2, String>
} -> {
  Lines.Votes.decided(s, c, k, ds) == Some{pk}: Maybe<&2, Types.Pick>
} -> {Lines.Votes.decided(s2, c, k, ds) == Some{pk}: Maybe<&2, Types.Pick>}:
  w => h => e => Slot.decided_grows(
    Slot.ballots(s, c, k),
    Slot.ballots(s2, c, k),
    ds,
    k,
    pk
  )(Slot.grown_wider(s, s2, c, k)(w)(h))(e)

# Votes.decided_same, once what s decided (m) is known
def Votes.decided_same.of(
  +s: Facts.Facts(),
  +s2: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +ds: List<&2, String>,
  +g1: {Ballots.grown(Slot.ballots(s, c, k), Slot.ballots(s2, c, k)) == True{}: Bool},
  +g2: {Ballots.grown(Slot.ballots(s2, c, k), Slot.ballots(s, c, k)) == True{}: Bool}
) -> {Lines.Votes.decided(s, c, k, ds) == Lines.Votes.decided(s2, c, k, ds): Maybe<&2, Types.Pick>}:
  Lists.Maybe.by(
    Types.Pick,
    m => {m == Lines.Votes.decided(s2, c, k, ds): Maybe<&2, Types.Pick>},
    Lines.Votes.decided(s, c, k, ds),
    +en => Lists.Maybe.by(
      Types.Pick,
      m => {None{} == m: Maybe<&2, Types.Pick>},
      Lines.Votes.decided(s2, c, k, ds),
      en2 => {==},
      +y => ey => Equal.trans(
        Maybe<&2, Types.Pick>,
        None{},
        Lines.Votes.decided(s, c, k, ds),
        Some{y},
        Equal.sym(Maybe<&2, Types.Pick>, Lines.Votes.decided(s, c, k, ds), None{}, en),
        Slot.decided_grows(Slot.ballots(s2, c, k), Slot.ballots(s, c, k), ds, k, y)(g2)(ey)
      )
    ),
    +y => ey => Equal.sym(
      Maybe<&2, Types.Pick>,
      Lines.Votes.decided(s2, c, k, ds),
      Some{y},
      Slot.decided_grows(Slot.ballots(s, c, k), Slot.ballots(s2, c, k), ds, k, y)(g1)(ey)
    )
  )

# two sets that hold the same ballots for a slot decided the same for it
def Votes.decided_same(
  +s: Facts.Facts(),
  +s2: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +ds: List<&2, String>
) -> {
  Slot.kept(s, s2, c, k) == True{}: Bool
} -> {
  Slot.kept(s2, s, c, k) == True{}: Bool
} -> {Lines.Votes.decided(s, c, k, ds) == Lines.Votes.decided(s2, c, k, ds): Maybe<&2, Types.Pick>}:
  +a => +b => Votes.decided_same.of(
    s,
    s2,
    c,
    k,
    ds,
    Slot.grown_kept(s, s2, c, k)(a)(b),
    Slot.grown_kept(s2, s, c, k)(b)(a)
  )

# the facts s hold a vote for the pick pk at the slot k of the line c
def Votes.Voted(s: Facts.Facts(), c: Ledgers.Line, k: Nat, pk: Types.Pick) -> Type:
  Exists(
    String,
    v => Exists(
      Nat,
      t => Exists(
        Nat,
        r => Exists(
          List<&2, Types.Ref>,
          b => {
            Facts.Facts.has(
              s,
              Types.Fact.Vote{v, Types.Step.At{c, k, t}, Types.Cast.Vote{r, pk, b}}
            )
              == True{}: Bool
          }
        )
      )
    )
  )

# Votes.decided_voted, with the vote among the ballots of the slot
def Votes.decided_voted.of(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +pk: Types.Pick,
  w0: Exists(
    String,
    v => Exists(
      Nat,
      t => Exists(
        Nat,
        r => Exists(
          List<&2, Types.Ref>,
          b => {
            List.contains(
              ~Types.Cast,
              ~Coded.Cast.is_eq,
              RRounds.Casts.of(Slot.ballots(s, c, k), Types.Ref{v, t}),
              Types.Cast.Vote{r, pk, b}
            )
              == True{}: Bool
          }
        )
      )
    )
  )
) -> Votes.Voted(s, c, k, pk):
  (+v, w1) = w0
  (+t, w2) = w1
  (+r, w3) = w2
  (+b, h) = w3
  (v, (t, (r, (b, Casts.of_has(s, c, k, v, t, Types.Cast.Vote{r, pk, b})(h)))))

# the facts hold a vote for the pick that the nodes ds decided for a slot
def Votes.decided_voted(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +ds: List<&2, String>,
  +pk: Types.Pick
) -> {Lines.Votes.decided(s, c, k, ds) == Some{pk}: Maybe<&2, Types.Pick>} -> Votes.Voted(s, c, k, pk):
  hd => Votes.decided_voted.of(s, c, k, pk, Slot.decided_cast(Slot.ballots(s, c, k), ds, k, pk)(hd))

# Votes.backed_voted, with the ballot among the ballots of the slot
def Votes.backed_voted.of(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +v: String,
  w0: Exists(
    Nat,
    t => Exists(
      Types.Cast,
      x => {
        List.contains(
          ~Types.Cast,
          ~Coded.Cast.is_eq,
          RRounds.Casts.of(Slot.ballots(s, c, k), Types.Ref{v, t}),
          x
        )
          == True{}: Bool
      }
    )
  )
) -> Exists(
  Nat,
  t => Exists(
    Types.Cast,
    x => {Facts.Facts.has(s, Types.Fact.Vote{v, Types.Step.At{c, k, t}, x}) == True{}: Bool}
  )
):
  (+t, w) = w0
  (+x, h) = w
  (t, (x, Casts.of_has(s, c, k, v, t, x)(h)))

# the facts hold a ballot, for the slot, of each of the nodes that decided a
# pick in one round
def Votes.backed_voted(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +ds: List<&2, String>,
  +os: List<&2, String>,
  +pk: Types.Pick,
  +v: String
) -> {
  RRounds.Slot.backed(Slot.ballots(s, c, k), ds, k, os, pk) == True{}: Bool
} -> {
  List.contains(~String, ~String.eq, os, v) == True{}: Bool
} -> Exists(
  Nat,
  t => Exists(
    Types.Cast,
    x => {Facts.Facts.has(s, Types.Fact.Vote{v, Types.Step.At{c, k, t}, x}) == True{}: Bool}
  )
):
  hb => hin => Votes.backed_voted.of(
    s,
    c,
    k,
    v,
    Slot.backed_cast(Slot.ballots(s, c, k), ds, k, os, pk, v)(hb)(hin)
  )

# the nodes that decided a pick in one round stay so as the facts grow, while
# the wider set names no liar
def Votes.backed_stays(
  +s: Facts.Facts(),
  +s2: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +ds: List<&2, String>,
  +os: List<&2, String>,
  +pk: Types.Pick
) -> {
  Facts.Facts.wider(s, s2) == True{}: Bool
} -> {
  Facts.Facts.liars(s2) == []: List<&2, String>
} -> {
  RRounds.Slot.backed(Slot.ballots(s, c, k), ds, k, os, pk) == True{}: Bool
} -> {RRounds.Slot.backed(Slot.ballots(s2, c, k), ds, k, os, pk) == True{}: Bool}:
  w => h => e => Slot.backed_grows(
    Slot.ballots(s, c, k),
    Slot.ballots(s2, c, k),
    ds,
    k,
    os,
    pk
  )(Slot.grown_wider(s, s2, c, k)(w)(h))(e)

# A node that decides alone
# -------------------------

# what a node that alone decides the slot k of the line c may cast there for
# the pick pk: a vote of the number t in the round r with the basis b, that
# s holds no ballot of the node in the place of, and that decides pk
def Slot.Alone(
  s: Facts.Facts(),
  name: String,
  c: Ledgers.Line,
  k: Nat,
  pk: Types.Pick,
  t: Nat,
  r: Nat,
  b: List<&2, Types.Ref>
) -> Type:
  {
    RRounds.Slot.chance(Slot.ballots(s, c, k), [name], k, name)
      == Some{RRounds.Chance{t, r, b, RRounds.Force.Free{}}}: Maybe<&2, RRounds.Chance>
  }
    & (
      {Facts.Facts.cast(s, name, Types.Step.At{c, k, t}) == False{}: Bool}
        & {
          Lines.Votes.decided(
            Facts.Facts.add(
              s,
              Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Vote{r, pk, b}}
            ),
            c,
            k,
            [name]
          )
            == Some{pk}: Maybe<&2, Types.Pick>
        }
    )

# a node that alone decides a slot that is not decided, in a set that does
# not name it a liar, may lead a round of it for any pick, whatever ballots
# of its own the set holds; and its vote decides the pick
def Slot.alone(
  +s: Facts.Facts(),
  +name: String,
  +c: Ledgers.Line,
  +k: Nat,
  +pk: Types.Pick
) -> {
  List.contains(~String, ~String.eq, Facts.Facts.liars(s), name) == False{}: Bool
} -> {
  Lines.Votes.decided(s, c, k, [name]) == None{}: Maybe<&2, Types.Pick>
} -> Exists(
  Nat,
  t => Exists(Nat, r => Exists(List<&2, Types.Ref>, b => Slot.Alone(s, name, c, k, pk, t, r, b)))
):
  ?TODO
