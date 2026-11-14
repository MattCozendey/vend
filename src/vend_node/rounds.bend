import Base
import ../shared/shared/ledger.bend as Ledgers
import ../shared/shared/shared/shared/shared.bend as Shared
import ../shared/shared/shared/text.bend as Texts
import ./codes.bend as Coded
import ./facts.bend as Facts
import ./lines.bend as Lines
import ./run/facts.bend as RFacts
import ./run/rounds.bend as RRounds
import ./safety.bend as Safeties
import ./shared/lists.bend as Lists
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

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- only proofs use it; no program runs it
# the ballot b, when it is the one ballot of its voter with its number in the
# old list of g, is that in the new list too
def Ballot.sure(g: Grow, b: RRounds.Ballot) -> Bool:
  match g b:
    case Grow{bs, bs2} RRounds.Ballot{+v, +t, +x}:
      Bool.or(
        Bool.not(RRounds.Cast.is(x, RRounds.Ballots.at(bs, v, t))),
        RRounds.Cast.is(x, RRounds.Ballots.at(bs2, v, t))
      )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# each ballot that is read from bs is read from bs2
def Ballots.grown(+bs: List<&2, RRounds.Ballot>, +bs2: List<&2, RRounds.Ballot>) -> Bool:
  Shared.List.holds(~RRounds.Ballot, ~Grow, ~Ballot.sure, bs, Grow{bs, bs2})

# some facts, and a slot of a line
type Kept is Data:
  Kept{facts: RFacts.Plain(), line: Ledgers.Line, slot: Nat}

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- only proofs use it; no program runs it
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
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# s2 holds each ballot that s holds for the slot k of the line c
def Slot.kept(s: Facts.Facts(), s2: Facts.Facts(), c: Ledgers.Line, k: Nat) -> Bool:
  Shared.List.holds(
    ~Types.Fact,
    ~Kept,
    ~Fact.kept,
    Facts.Facts.list(s),
    Kept{Facts.Facts.crit(s2), c, k}
  )

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
        (
          @x: A -> {
            List.contains(~A, ~same, y <> r, x) == True{}: Bool
          } -> {p(g)(x) == True{}: Bool}
        ),
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
      h => Empty.absurd({None{} == Some{x}: Maybe<&2, Types.Cast>}, Shared.Bool.false_ne_true(h))
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

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof does not run
# Tally.voted_cast, once the vote m of the node is known
def Tally.voted_cast.of(
  +bs: List<&2, RRounds.Ballot>,
  +r: Nat,
  +pk: Types.Pick,
  +d: String,
  m: Maybe<&2, RRounds.Ballot>
) -> {
  RRounds.Vote.of(bs, d, r) == m: Maybe<&2, RRounds.Ballot>
} -> {
  RRounds.Vote.is_for(pk, m) == True{}: Bool
} -> Exists(
  Nat,
  t => Exists(
    List<&2, Types.Ref>,
    b => {
      List.contains(
        ~Types.Cast,
        ~Coded.Cast.is_eq,
        RRounds.Casts.of(bs, Types.Ref{d, t}),
        Types.Cast.Vote{r, pk, b}
      )
        == True{}: Bool
    }
  )
):
  match m:
    case None{}:
      e => h => Empty.absurd(
        Exists(
          Nat,
          t => Exists(
            List<&2, Types.Ref>,
            b => {
              List.contains(
                ~Types.Cast,
                ~Coded.Cast.is_eq,
                RRounds.Casts.of(bs, Types.Ref{d, t}),
                Types.Cast.Vote{r, pk, b}
              )
                == True{}: Bool
            }
          )
        ),
        Shared.Bool.false_ne_true(h)
      )
    case Some{RRounds.Ballot{v, t, Types.Cast.Pass{r2}}}:
      e => h => Empty.absurd(
        Exists(
          Nat,
          t => Exists(
            List<&2, Types.Ref>,
            b => {
              List.contains(
                ~Types.Cast,
                ~Coded.Cast.is_eq,
                RRounds.Casts.of(bs, Types.Ref{d, t}),
                Types.Cast.Vote{r, pk, b}
              )
                == True{}: Bool
            }
          )
        ),
        Shared.Bool.false_ne_true(h)
      )
    case Some{RRounds.Ballot{+v, +t, Types.Cast.Vote{+r2, +q, +basis}}}:
      +e => h => (t, (basis, (
            %Coded.Pick.is_eq_sound(q, pk)(h): {List.contains(~Types.Cast, ~Coded.Cast.is_eq, RRounds.Casts.of(bs, Types.Ref{d, t}), Types.Cast.Vote{r, _, basis}) == True{}: Bool}
            %Shared.Nat.is_eq_sound(r2, r)(Shared.Bool.and_true_right(String.eq(v, d), Nat.is_eq(r2, r))(Shared.Bool.and_true_left(Bool.and(String.eq(v, d), Nat.is_eq(r2, r)), Bool.and(RRounds.Seen.takes(r2, RRounds.Chain.seen(bs, d, t)), RRounds.Cast.is(Types.Cast.Vote{r2, q, basis}, RRounds.Ballots.at(bs, d, t))))(Safeties.Ballot.counts_true(bs, d, r, v, t, r2, q, basis)(Lists.List.pick_hit(~RRounds.Ballot, ~RRounds.Roll, ~RRounds.Ballot.counts, bs, RRounds.Roll{bs, d, r}, RRounds.Ballot{v, t, Types.Cast.Vote{r2, q, basis}})(e))))): {List.contains(~Types.Cast, ~Coded.Cast.is_eq, RRounds.Casts.of(bs, Types.Ref{d, t}), Types.Cast.Vote{_, q, basis}) == True{}: Bool}
            Casts.agreed_in(RRounds.Casts.of(bs, Types.Ref{d, t}), Types.Cast.Vote{r2, q, basis})(Cast.is_some(Types.Cast.Vote{r2, q, basis}, RRounds.Ballots.at(bs, d, t))(Shared.Bool.and_true_right(RRounds.Seen.takes(r2, RRounds.Chain.seen(bs, d, t)), RRounds.Cast.is(Types.Cast.Vote{r2, q, basis}, RRounds.Ballots.at(bs, d, t)))(Shared.Bool.and_true_right(Bool.and(String.eq(v, d), Nat.is_eq(r2, r)), Bool.and(RRounds.Seen.takes(r2, RRounds.Chain.seen(bs, d, t)), RRounds.Cast.is(Types.Cast.Vote{r2, q, basis}, RRounds.Ballots.at(bs, d, t))))(Safeties.Ballot.counts_true(bs, d, r, v, t, r2, q, basis)(Lists.List.pick_hit(~RRounds.Ballot, ~RRounds.Roll, ~RRounds.Ballot.counts, bs, RRounds.Roll{bs, d, r}, RRounds.Ballot{v, t, Types.Cast.Vote{r2, q, basis}})(e)))))))))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the ballots hold a vote of a node that voted for a pick in a round: of the
# round, for the pick
def Tally.voted_cast(
  +bs: List<&2, RRounds.Ballot>,
  +r: Nat,
  +pk: Types.Pick,
  +d: String
) -> {
  RRounds.Tally.voted(RRounds.Tally{bs, r, pk}, d) == True{}: Bool
} -> Exists(
  Nat,
  t => Exists(
    List<&2, Types.Ref>,
    b => {
      List.contains(
        ~Types.Cast,
        ~Coded.Cast.is_eq,
        RRounds.Casts.of(bs, Types.Ref{d, t}),
        Types.Cast.Vote{r, pk, b}
      )
        == True{}: Bool
    }
  )
):
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
) -> Exists(
  String,
  v => Exists(
    Nat,
    t => Exists(
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
):
  (hin, hv) = w
  (d, Tally.voted_cast(bs, r, pk, d)((
        %ep: {RRounds.Tally.voted(RRounds.Tally{bs, r, _}, d) == True{}: Bool}
        hv)))

# the ballots hold a vote of the round r for the pick that the round decided
def Round.won_cast(
  +bs: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +r: Nat,
  +pk: Types.Pick,
  m: RRounds.Mind
) -> {
  RRounds.Round.won(bs, ds, r, m) == Some{pk}: Maybe<&2, Types.Pick>
} -> Exists(
  String,
  v => Exists(
    Nat,
    t => Exists(
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
):
  match m:
    case RRounds.Mind.Open{}:
      h => Empty.absurd(
        Exists(
          String,
          v => Exists(
            Nat,
            t => Exists(
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
        ),
        Shared.Maybe.none_ne_some(Types.Pick, pk, h)
      )
    case RRounds.Mind.Void{}:
      h => Empty.absurd(
        Exists(
          String,
          v => Exists(
            Nat,
            t => Exists(
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
        ),
        Shared.Maybe.none_ne_some(Types.Pick, pk, h)
      )
    case RRounds.Mind.Sound{+p}:
      Lists.Bool.by(
        b => {
          Shared.Maybe.when(Types.Pick, b, u => Some{p}) == Some{pk}: Maybe<&2, Types.Pick>
        } -> Exists(
          String,
          v => Exists(
            Nat,
            t => Exists(
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
        ),
        RRounds.Tally.most(bs, ds, r, p),
        et => h => Ex.by(
          String,
          d => {
            List.contains(~String, ~String.eq, ds, d) == True{}: Bool
          }
            & {RRounds.Tally.voted(RRounds.Tally{bs, r, p}, d) == True{}: Bool},
          Exists(
            String,
            v => Exists(
              Nat,
              t => Exists(
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
          ),
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
              Lists.List.count(
                ~String,
                ~RRounds.Tally,
                ~RRounds.Tally.voted,
                ds,
                RRounds.Tally{bs, r, p}
              )
            )(et)
          ),
          +d => w => Round.won_cast.at(
            bs,
            r,
            p,
            pk,
            d,
            ds,
            Shared.Maybe.some_inj(Types.Pick, p, pk, h),
            w
          )
        ),
        ef => h => Empty.absurd(
          Exists(
            String,
            v => Exists(
              Nat,
              t => Exists(
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
          ),
          Shared.Maybe.none_ne_some(Types.Pick, pk, h)
        )
      )

# Rounds.won_cast, with the vote
def Rounds.won_cast.fin(
  +bs: List<&2, RRounds.Ballot>,
  +r: Nat,
  +pk: Types.Pick,
  w0: Exists(
    String,
    v => Exists(
      Nat,
      t => Exists(
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

# bend-lint: expect-begin bend-lint-rules/performance/list_index_loop@warning -- a proof does not run
# the ballots hold a vote for the pick that one of the rounds from r on
# decided
def Rounds.won_cast(
  ms: List<&2, RRounds.Mind>,
  +bs: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +r: Nat,
  +pk: Types.Pick
) -> {
  RRounds.Rounds.won(ms, bs, ds, r) == Some{pk}: Maybe<&2, Types.Pick>
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
  match ms:
    case Nil{}:
      h => Empty.absurd(
        Exists(
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
        Shared.Maybe.none_ne_some(Types.Pick, pk, h)
      )
    case Con{+m, +rest}:
      Lists.Maybe.by(
        Types.Pick,
        x => {
          RRounds.Rounds.won.or(
            x,
            u => RRounds.Rounds.won(rest, bs, ds, 1n+r)
          )
            == Some{pk}: Maybe<&2, Types.Pick>
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
          Round.won_cast(
            bs,
            ds,
            r,
            pk,
            m
          )(
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
# bend-lint: expect-end bend-lint-rules/performance/list_index_loop@warning

# a round that the code that runs finds backed by a sound lead for q: q is
# the pick pk, and each of os voted for it
def Round.backs_true(
  +bs: List<&2, RRounds.Ballot>,
  +os: List<&2, String>,
  +pk: Types.Pick,
  +r: Nat,
  +q: Types.Pick
) -> {
  RRounds.Round.backs(bs, os, pk, r, RRounds.Mind.Sound{q}) == True{}: Bool
} -> {
  Bool.and(
    Coded.Pick.is_eq(q, pk),
    Shared.List.holds(~String, ~RRounds.Tally, ~RRounds.Tally.voted, os, RRounds.Tally{bs, r, pk})
  )
    == True{}: Bool
}:
  h =>
    %Lists.Bool.when_and(
      Coded.Pick.is_eq(q, pk),
      u => Shared.List.holds(
        ~String,
        ~RRounds.Tally,
        ~RRounds.Tally.voted,
        os,
        RRounds.Tally{bs, r, pk}
      )
    ): {_ == True{}: Bool}
    h

# Round.backs_true, from right to left
def Round.backs_of(
  +bs: List<&2, RRounds.Ballot>,
  +os: List<&2, String>,
  +pk: Types.Pick,
  +r: Nat,
  +q: Types.Pick
) -> {
  Bool.and(
    Coded.Pick.is_eq(q, pk),
    Shared.List.holds(~String, ~RRounds.Tally, ~RRounds.Tally.voted, os, RRounds.Tally{bs, r, pk})
  )
    == True{}: Bool
} -> {RRounds.Round.backs(bs, os, pk, r, RRounds.Mind.Sound{q}) == True{}: Bool}:
  h =>
    %Lists.Bool.and_when(
      Coded.Pick.is_eq(q, pk),
      u => Shared.List.holds(
        ~String,
        ~RRounds.Tally,
        ~RRounds.Tally.voted,
        os,
        RRounds.Tally{bs, r, pk}
      )
    ): {_ == True{}: Bool}
    h

# Round.backs_cast, with the vote
def Round.backs_cast.fin(
  +bs: List<&2, RRounds.Ballot>,
  +r: Nat,
  +pk: Types.Pick,
  +v: String,
  w0: Exists(
    Nat,
    t => Exists(
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
) -> Exists(
  Nat,
  t => Exists(
    Types.Cast,
    x => {
      List.contains(
        ~Types.Cast,
        ~Coded.Cast.is_eq,
        RRounds.Casts.of(bs, Types.Ref{v, t}),
        x
      )
        == True{}: Bool
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
} -> {
  List.contains(~String, ~String.eq, os, v) == True{}: Bool
} -> Exists(
  Nat,
  t => Exists(
    Types.Cast,
    x => {
      List.contains(
        ~Types.Cast,
        ~Coded.Cast.is_eq,
        RRounds.Casts.of(bs, Types.Ref{v, t}),
        x
      )
        == True{}: Bool
    }
  )
):
  match m:
    case RRounds.Mind.Open{}:
      h => hin => Empty.absurd(
        Exists(
          Nat,
          t => Exists(
            Types.Cast,
            x => {
              List.contains(
                ~Types.Cast,
                ~Coded.Cast.is_eq,
                RRounds.Casts.of(bs, Types.Ref{v, t}),
                x
              )
                == True{}: Bool
            }
          )
        ),
        Shared.Bool.false_ne_true(h)
      )
    case RRounds.Mind.Void{}:
      h => hin => Empty.absurd(
        Exists(
          Nat,
          t => Exists(
            Types.Cast,
            x => {
              List.contains(
                ~Types.Cast,
                ~Coded.Cast.is_eq,
                RRounds.Casts.of(bs, Types.Ref{v, t}),
                x
              )
                == True{}: Bool
            }
          )
        ),
        Shared.Bool.false_ne_true(h)
      )
    case RRounds.Mind.Sound{+q}:
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
              Shared.List.holds(
                ~String,
                ~RRounds.Tally,
                ~RRounds.Tally.voted,
                os,
                RRounds.Tally{bs, r, pk}
              )
            )(
              %Lists.Bool.when_and(Coded.Pick.is_eq(q, pk), u => Shared.List.holds(~String, ~RRounds.Tally, ~RRounds.Tally.voted, os, RRounds.Tally{bs, r, pk})): {_ == True{}: Bool}
              h)
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
} -> {
  List.contains(~String, ~String.eq, os, v) == True{}: Bool
} -> Exists(
  Nat,
  t => Exists(
    Types.Cast,
    x => {
      List.contains(
        ~Types.Cast,
        ~Coded.Cast.is_eq,
        RRounds.Casts.of(bs, Types.Ref{v, t}),
        x
      )
        == True{}: Bool
    }
  )
):
  match ms:
    case Nil{}:
      h => hin => Empty.absurd(
        Exists(
          Nat,
          t => Exists(
            Types.Cast,
            x => {
              List.contains(
                ~Types.Cast,
                ~Coded.Cast.is_eq,
                RRounds.Casts.of(bs, Types.Ref{v, t}),
                x
              )
                == True{}: Bool
            }
          )
        ),
        Shared.Bool.false_ne_true(h)
      )
    case Con{+m, +rest}:
      Lists.Bool.by(
        b => {
          List.any.if(u => RRounds.Rounds.back(rest, bs, os, pk, 1n+r), b) == True{}: Bool
        } -> {
          List.contains(~String, ~String.eq, os, v) == True{}: Bool
        } -> Exists(
          Nat,
          t => Exists(
            Types.Cast,
            x => {
              List.contains(
                ~Types.Cast,
                ~Coded.Cast.is_eq,
                RRounds.Casts.of(bs, Types.Ref{v, t}),
                x
              )
                == True{}: Bool
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
  List.contains(
    ~Types.Cast,
    ~Coded.Cast.is_eq,
    RRounds.Casts.of(xs, Types.Ref{v, t}),
    x
  )
    == True{}: Bool
} -> {
  RRounds.Cast.is(x, RRounds.Ballots.at(bs, v, t)) == True{}: Bool
} -> {RRounds.Cast.is(x, RRounds.Ballots.at(bs2, v, t)) == True{}: Bool}:
  match xs:
    case Nil{}:
      hh => hc => his => Empty.absurd(
        {RRounds.Cast.is(x, RRounds.Ballots.at(bs2, v, t)) == True{}: Bool},
        Shared.Bool.false_ne_true(hc)
      )
    case Con{RRounds.Ballot{+w, +u, +y}, +rest}:
      +hh => Lists.Bool.by(
        b => {
          List.contains(
            ~Types.Cast,
            ~Coded.Cast.is_eq,
            Shared.Maybe.cons(
              Types.Cast,
              Shared.Maybe.when(Types.Cast, b, z => Some{y}),
              RRounds.Casts.of(rest, Types.Ref{v, t})
            ),
            x
          )
            == True{}: Bool
        } -> {
          RRounds.Cast.is(x, RRounds.Ballots.at(bs, v, t)) == True{}: Bool
        } -> {RRounds.Cast.is(x, RRounds.Ballots.at(bs2, v, t)) == True{}: Bool},
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
          e => Bool.or_not(
            RRounds.Cast.is(x, RRounds.Ballots.at(bs, v, t)),
            RRounds.Cast.is(x, RRounds.Ballots.at(bs2, v, t))
          )(his)((
              %Texts.String.eq_sound(w, v)(Shared.Bool.and_true_left(String.eq(w, v), Nat.is_eq(u, t))(et)): {Ballot.sure(Grow{bs, bs2}, RRounds.Ballot{_, t, x}) == True{}: Bool}
              %Shared.Nat.is_eq_sound(u, t)(Shared.Bool.and_true_right(String.eq(w, v), Nat.is_eq(u, t))(et)): {Ballot.sure(Grow{bs, bs2}, RRounds.Ballot{w, _, x}) == True{}: Bool}
              %e: {Ballot.sure(Grow{bs, bs2}, RRounds.Ballot{w, u, _}) == True{}: Bool}
              Shared.List.all.if_hit(Ballot.sure(Grow{bs, bs2}, RRounds.Ballot{w, u, y}), z0 => Shared.List.holds(~RRounds.Ballot, ~Grow, ~Ballot.sure, rest, Grow{bs, bs2}))(hh))),
          cin => Ballots.at_grows.go(
            rest,
            bs,
            bs2,
            v,
            t,
            x
          )(
            Shared.List.all.if_rest(
              Ballot.sure(Grow{bs, bs2}, RRounds.Ballot{w, u, y}),
              z0 => Shared.List.holds(~RRounds.Ballot, ~Grow, ~Ballot.sure, rest, Grow{bs, bs2})
            )(hh)
          )(cin)(his)
        ),
        ef => hc => his => Ballots.at_grows.go(
          rest,
          bs,
          bs2,
          v,
          t,
          x
        )(
          Shared.List.all.if_rest(
            Ballot.sure(Grow{bs, bs2}, RRounds.Ballot{w, u, y}),
            z0 => Shared.List.holds(~RRounds.Ballot, ~Grow, ~Ballot.sure, rest, Grow{bs, bs2})
          )(hh)
        )(hc)(his)
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
} -> {
  RRounds.Ballots.at(bs, v, t) == Some{x}: Maybe<&2, Types.Cast>
} -> {RRounds.Ballots.at(bs2, v, t) == Some{x}: Maybe<&2, Types.Cast>}:
  hg => +e => Cast.is_some(
    x,
    RRounds.Ballots.at(bs2, v, t)
  )(
    Ballots.at_grows.go(
      bs,
      bs,
      bs2,
      v,
      t,
      x
    )(
      hg
    )(
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
) -> {
  RRounds.Chain.seen(bs, v, t) == Some{m}: Maybe<&2, RRounds.Seen>
} -> {RRounds.Chain.seen(bs2, v, t) == Some{m}: Maybe<&2, RRounds.Seen>}:
  match t:
    case 0n:
      h => h
    case 1n+(+j):
      Lists.Maybe.by(
        RRounds.Seen,
        z => {
          RRounds.Chain.seen.next(
            z,
            RRounds.Ballots.at(bs, v, j)
          )
            == Some{m}: Maybe<&2, RRounds.Seen>
        } -> {
          RRounds.Chain.seen.next(
            RRounds.Chain.seen(bs2, v, j),
            RRounds.Ballots.at(bs2, v, j)
          )
            == Some{m}: Maybe<&2, RRounds.Seen>
        },
        RRounds.Chain.seen(bs, v, j),
        en => h => Empty.absurd(
          {
            RRounds.Chain.seen.next(
              RRounds.Chain.seen(bs2, v, j),
              RRounds.Ballots.at(bs2, v, j)
            )
              == Some{m}: Maybe<&2, RRounds.Seen>
          },
          Shared.Maybe.none_ne_some(RRounds.Seen, m, h)
        ),
        +m0 => +e0 => Lists.Maybe.by(
          Types.Cast,
          y => {
            RRounds.Chain.seen.next(Some{m0}, y) == Some{m}: Maybe<&2, RRounds.Seen>
          } -> {
            RRounds.Chain.seen.next(
              RRounds.Chain.seen(bs2, v, j),
              RRounds.Ballots.at(bs2, v, j)
            )
              == Some{m}: Maybe<&2, RRounds.Seen>
          },
          RRounds.Ballots.at(bs, v, j),
          en => h => Empty.absurd(
            {
              RRounds.Chain.seen.next(
                RRounds.Chain.seen(bs2, v, j),
                RRounds.Ballots.at(bs2, v, j)
              )
                == Some{m}: Maybe<&2, RRounds.Seen>
            },
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
) -> {
  RRounds.Seen.takes(r2, RRounds.Chain.seen(bs, v, t)) == True{}: Bool
} -> {RRounds.Seen.takes(r2, RRounds.Chain.seen(bs2, v, t)) == True{}: Bool}:
  Lists.Maybe.by(
    RRounds.Seen,
    z => {
      RRounds.Seen.takes(r2, z) == True{}: Bool
    } -> {RRounds.Seen.takes(r2, RRounds.Chain.seen(bs2, v, t)) == True{}: Bool},
    RRounds.Chain.seen(bs, v, t),
    en => h => Empty.absurd(
      {RRounds.Seen.takes(r2, RRounds.Chain.seen(bs2, v, t)) == True{}: Bool},
      Shared.Bool.false_ne_true(h)
    ),
    +m0 => e0 => h => (
      %Equal.sym(Maybe<&2, RRounds.Seen>, RRounds.Chain.seen(bs2, v, t), Some{m0}, Chain.seen_grows(bs, bs2, v, t, m0, hg)(e0)): {RRounds.Seen.takes(r2, _) == True{}: Bool}
      h)
  )

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof does not run
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
      h0 =>
        +h = Safeties.Ballot.counts_true(bs, v, r, w, t, r2, p, basis)(h0)
        %Safeties.Ballot.and_counts(bs2, v, r, w, t, r2, p, basis): {_ == True{}: Bool}
        Shared.Bool.and_both(
          Bool.and(String.eq(w, v), Nat.is_eq(r2, r)),
          Bool.and(
            RRounds.Seen.takes(r2, RRounds.Chain.seen(bs2, v, t)),
            RRounds.Cast.is(Types.Cast.Vote{r2, p, basis}, RRounds.Ballots.at(bs2, v, t))
          )
        )(
          Shared.Bool.and_true_left(
            Bool.and(String.eq(w, v), Nat.is_eq(r2, r)),
            Bool.and(
              RRounds.Seen.takes(r2, RRounds.Chain.seen(bs, v, t)),
              RRounds.Cast.is(Types.Cast.Vote{r2, p, basis}, RRounds.Ballots.at(bs, v, t))
            )
          )(h)
        )(
          Shared.Bool.and_both(
            RRounds.Seen.takes(r2, RRounds.Chain.seen(bs2, v, t)),
            RRounds.Cast.is(Types.Cast.Vote{r2, p, basis}, RRounds.Ballots.at(bs2, v, t))
          )(
            Seen.takes_grows(
              bs,
              bs2,
              v,
              t,
              r2,
              hg
            )(
              Shared.Bool.and_true_left(
                RRounds.Seen.takes(r2, RRounds.Chain.seen(bs, v, t)),
                RRounds.Cast.is(Types.Cast.Vote{r2, p, basis}, RRounds.Ballots.at(bs, v, t))
              )(
                Shared.Bool.and_true_right(
                  Bool.and(String.eq(w, v), Nat.is_eq(r2, r)),
                  Bool.and(
                    RRounds.Seen.takes(r2, RRounds.Chain.seen(bs, v, t)),
                    RRounds.Cast.is(Types.Cast.Vote{r2, p, basis}, RRounds.Ballots.at(bs, v, t))
                  )
                )(h)
              )
            )
          )(
            Cast.is_of(
              Types.Cast.Vote{r2, p, basis},
              RRounds.Ballots.at(bs2, v, t),
              Ballots.at_grows(
                bs,
                bs2,
                v,
                t,
                Types.Cast.Vote{r2, p, basis}
              )(
                hg
              )(
                Cast.is_some(
                  Types.Cast.Vote{r2, p, basis},
                  RRounds.Ballots.at(bs, v, t)
                )(
                  Shared.Bool.and_true_right(
                    RRounds.Seen.takes(r2, RRounds.Chain.seen(bs, v, t)),
                    RRounds.Cast.is(Types.Cast.Vote{r2, p, basis}, RRounds.Ballots.at(bs, v, t))
                  )(
                    Shared.Bool.and_true_right(
                      Bool.and(String.eq(w, v), Nat.is_eq(r2, r)),
                      Bool.and(
                        RRounds.Seen.takes(r2, RRounds.Chain.seen(bs, v, t)),
                        RRounds.Cast.is(Types.Cast.Vote{r2, p, basis}, RRounds.Ballots.at(bs, v, t))
                      )
                    )(h)
                  )
                )
              )
            )
          )
        )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

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
      h => Empty.absurd(
        {Nat.add(Nat.sub(0n, 1n+rp), 1n+(1n+rp)) == 1n: Nat},
        Shared.Bool.false_ne_true(h)
      )
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
) -> {
  List.length(
    &2,
    RRounds.Mind,
    List.append(&2, RRounds.Mind, xs, [m])
  )
    == 1n+List.length(&2, RRounds.Mind, xs): Nat
}:
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
        List.length(
          &2,
          RRounds.Mind,
          List.append(
            &2,
            RRounds.Mind,
            RRounds.Rounds.minds(bs, ds, k, j),
            [Round.mind(bs, ds, k, j)]
          )
        ),
        1n+List.length(&2, RRounds.Mind, RRounds.Rounds.minds(bs, ds, k, j)),
        1n+j,
        Minds.length_snoc(RRounds.Rounds.minds(bs, ds, k, j), Round.mind(bs, ds, k, j)),
        Equal.cong(
          Nat,
          Nat,
          z => 1n+z,
          List.length(&2, RRounds.Mind, RRounds.Rounds.minds(bs, ds, k, j)),
          j,
          Minds.length(bs, ds, k, j)
        )
      )

# a pick, or else nothing, is the pick
def Won.or_none(
  x: Maybe<&2, Types.Pick>
) -> {RRounds.Rounds.won.or(x, u => None{}) == x: Maybe<&2, Types.Pick>}:
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
  RRounds.Rounds.won(
    List.append(&2, RRounds.Mind, xs, [m]),
    bs,
    ds,
    r0
  )
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
          RRounds.Rounds.won.or(
            z,
            u => RRounds.Rounds.won(List.append(&2, RRounds.Mind, rest, [m]), bs, ds, 1n+r0)
          )
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
  RRounds.Rounds.won(
    RRounds.Rounds.minds(bs, ds, k, 1n+j),
    bs,
    ds,
    0n
  )
    == RRounds.Rounds.won.or(
      RRounds.Rounds.won(RRounds.Rounds.minds(bs, ds, k, j), bs, ds, 0n),
      u => RRounds.Round.won(bs, ds, j, Round.mind(bs, ds, k, j))
    ): Maybe<&2, Types.Pick>
}:
  %Nat.add_zero(
    j
  ): {
    RRounds.Rounds.won(
      RRounds.Rounds.minds(bs, ds, k, 1n+j),
      bs,
      ds,
      0n
    )
      == RRounds.Rounds.won.or(
        RRounds.Rounds.won(RRounds.Rounds.minds(bs, ds, k, j), bs, ds, 0n),
        u => RRounds.Round.won(bs, ds, _, Round.mind(bs, ds, k, j))
      ): Maybe<&2, Types.Pick>
  }
  %Minds.length(
    bs,
    ds,
    k,
    j
  ): {
    RRounds.Rounds.won(
      RRounds.Rounds.minds(bs, ds, k, 1n+j),
      bs,
      ds,
      0n
    )
      == RRounds.Rounds.won.or(
        RRounds.Rounds.won(RRounds.Rounds.minds(bs, ds, k, j), bs, ds, 0n),
        u => RRounds.Round.won(bs, ds, Nat.add(_, 0n), Round.mind(bs, ds, k, j))
      ): Maybe<&2, Types.Pick>
  }
  Rounds.won_snoc(RRounds.Rounds.minds(bs, ds, k, j), Round.mind(bs, ds, k, j), bs, ds, 0n)

# a round below n decided the pick that the first of the rounds below n
# decided
def Slot.decided_won.go(
  n: Nat,
  +bs: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +pk: Types.Pick
) -> {
  RRounds.Rounds.won(
    RRounds.Rounds.minds(bs, ds, k, n),
    bs,
    ds,
    0n
  )
    == Some{pk}: Maybe<&2, Types.Pick>
} -> Exists(Nat, r => Round.Won(bs, ds, k, r, pk)):
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
          RRounds.Rounds.won.or(
            z,
            u => RRounds.Round.won(bs, ds, j, Round.mind(bs, ds, k, j))
          )
            == Some{pk}: Maybe<&2, Types.Pick>
        } -> Exists(Nat, r => Round.Won(bs, ds, k, r, pk)),
        RRounds.Rounds.won(RRounds.Rounds.minds(bs, ds, k, j), bs, ds, 0n),
        en => h => (j, h),
        +p => ep => h => Slot.decided_won.go(
          j,
          bs,
          ds,
          k,
          pk
        )(
          Equal.trans(
            Maybe<&2, Types.Pick>,
            RRounds.Rounds.won(RRounds.Rounds.minds(bs, ds, k, j), bs, ds, 0n),
            Some{p},
            Some{pk},
            ep,
            h
          )
        )
      )(
        Equal.trans(
          Maybe<&2, Types.Pick>,
          RRounds.Rounds.won.or(
            RRounds.Rounds.won(RRounds.Rounds.minds(bs, ds, k, j), bs, ds, 0n),
            u => RRounds.Round.won(bs, ds, j, Round.mind(bs, ds, k, j))
          ),
          RRounds.Rounds.won(RRounds.Rounds.minds(bs, ds, k, 1n+j), bs, ds, 0n),
          Some{pk},
          Equal.sym(
            Maybe<&2, Types.Pick>,
            RRounds.Rounds.won(RRounds.Rounds.minds(bs, ds, k, 1n+j), bs, ds, 0n),
            RRounds.Rounds.won.or(
              RRounds.Rounds.won(RRounds.Rounds.minds(bs, ds, k, j), bs, ds, 0n),
              u => RRounds.Round.won(bs, ds, j, Round.mind(bs, ds, k, j))
            ),
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
  List.contains(
    ~Types.Cast,
    ~Coded.Cast.is_eq,
    RRounds.Casts.of(bs, Types.Ref{v, t}),
    x
  )
    == True{}: Bool
} -> {Nat.is_le(RRounds.Cast.round(x), RRounds.Rounds.top(bs)) == True{}: Bool}:
  match bs:
    case Nil{}:
      h => Empty.absurd(
        {Nat.is_le(RRounds.Cast.round(x), 0n) == True{}: Bool},
        Shared.Bool.false_ne_true(h)
      )
    case Con{RRounds.Ballot{+w, +u, +y}, +rest}:
      Lists.Bool.by(
        b => {
          List.contains(
            ~Types.Cast,
            ~Coded.Cast.is_eq,
            Shared.Maybe.cons(
              Types.Cast,
              Shared.Maybe.when(Types.Cast, b, z => Some{y}),
              RRounds.Casts.of(rest, Types.Ref{v, t})
            ),
            x
          )
            == True{}: Bool
        } -> {
          Nat.is_le(
            RRounds.Cast.round(x),
            Nat.max(RRounds.Cast.round(y), RRounds.Rounds.top(rest))
          )
            == True{}: Bool
        },
        Bool.and(String.eq(w, v), Nat.is_eq(u, t)),
        et => h => Lists.List.contains_cons_by(
          ~Types.Cast,
          ~Coded.Cast.is_eq,
          ~Coded.Cast.laws(),
          {
            Nat.is_le(
              RRounds.Cast.round(x),
              Nat.max(RRounds.Cast.round(y), RRounds.Rounds.top(rest))
            )
              == True{}: Bool
          },
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
          )(
            Casts.of_top(rest, v, t, x)(cin)
          )(Lists.Nat.le_max_right(RRounds.Cast.round(y), RRounds.Rounds.top(rest)))
        ),
        ef => h => Shared.Nat.le_trans(
          RRounds.Cast.round(x),
          RRounds.Rounds.top(rest),
          Nat.max(RRounds.Cast.round(y), RRounds.Rounds.top(rest))
        )(
          Casts.of_top(rest, v, t, x)(h)
        )(Lists.Nat.le_max_right(RRounds.Cast.round(y), RRounds.Rounds.top(rest)))
      )

# Round.won_top, with the vote
def Round.won_top.fin(
  +bs: List<&2, RRounds.Ballot>,
  +r: Nat,
  +pk: Types.Pick,
  w0: Exists(
    String,
    v => Exists(
      Nat,
      t => Exists(
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
  w0: Exists(
    Types.Pick,
    p => {
      RRounds.Rounds.won(
        RRounds.Rounds.minds(bs, ds, k, j),
        bs,
        ds,
        0n
      )
        == Some{p}: Maybe<&2, Types.Pick>
    }
  )
) -> Exists(
  Types.Pick,
  p => {
    RRounds.Rounds.won(
      RRounds.Rounds.minds(bs, ds, k, 1n+j),
      bs,
      ds,
      0n
    )
      == Some{p}: Maybe<&2, Types.Pick>
  }
):
  (+p, ep) = w0
  %Equal.sym(
    Maybe<&2, Types.Pick>,
    RRounds.Rounds.won(RRounds.Rounds.minds(bs, ds, k, 1n+j), bs, ds, 0n),
    RRounds.Rounds.won.or(
      RRounds.Rounds.won(RRounds.Rounds.minds(bs, ds, k, j), bs, ds, 0n),
      u => RRounds.Round.won(bs, ds, j, Round.mind(bs, ds, k, j))
    ),
    Slot.won_step(bs, ds, k, j)
  ): Exists(Types.Pick, q => {_ == Some{q}: Maybe<&2, Types.Pick>})
  (p, (
      %Equal.sym(Maybe<&2, Types.Pick>, RRounds.Rounds.won(RRounds.Rounds.minds(bs, ds, k, j), bs, ds, 0n), Some{p}, ep): {RRounds.Rounds.won.or(_, u => RRounds.Round.won(bs, ds, j, Round.mind(bs, ds, k, j))) == Some{p}: Maybe<&2, Types.Pick>}
      {==}))

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
) -> Exists(
  Types.Pick,
  p => {
    RRounds.Rounds.won(
      RRounds.Rounds.minds(bs, ds, k, Nat.add(d, 1n+r)),
      bs,
      ds,
      0n
    )
      == Some{p}: Maybe<&2, Types.Pick>
  }
):
  match d:
    case 0n:
      hw => (
        %Equal.sym(Maybe<&2, Types.Pick>, RRounds.Rounds.won(RRounds.Rounds.minds(bs, ds, k, 1n+r), bs, ds, 0n), RRounds.Rounds.won.or(RRounds.Rounds.won(RRounds.Rounds.minds(bs, ds, k, r), bs, ds, 0n), u => RRounds.Round.won(bs, ds, r, Round.mind(bs, ds, k, r))), Slot.won_step(bs, ds, k, r)): Exists(Types.Pick, q => {_ == Some{q}: Maybe<&2, Types.Pick>})
        Lists.Maybe.by(Types.Pick, z => Exists(Types.Pick, q => {RRounds.Rounds.won.or(z, u => RRounds.Round.won(bs, ds, r, Round.mind(bs, ds, k, r))) == Some{q}: Maybe<&2, Types.Pick>}), RRounds.Rounds.won(RRounds.Rounds.minds(bs, ds, k, r), bs, ds, 0n), en => (pk, hw), +p => ep => (p, {==})))
    case 1n+(+e):
      hw => Slot.won_decided.up(
        bs,
        ds,
        k,
        Nat.add(e, 1n+r),
        Slot.won_decided.go(e, bs, ds, k, r, pk)(hw)
      )

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

# One vote in a round
# -------------------
# The floor of a voter never goes down, and it is above a round that the
# voter voted in: so one vote of a voter counts in a round at most.

# t1 is below t2, or they are one number, or t1 is above t2
def Nat.tri(
  -Q: Type,
  t1: Nat,
  t2: Nat,
  lt: @d: Nat -> {t2 == Nat.add(d, 1n+t1): Nat} -> Q,
  eq: {t1 == t2: Nat} -> Q,
  gt: @d: Nat -> {t1 == Nat.add(d, 1n+t2): Nat} -> Q
) -> Q:
  match t1 t2:
    case 0n 0n:
      eq({==})
    case 0n 1n+(+b):
      lt(b)(Equal.sym(Nat, Nat.add(b, 1n), 1n+b, Nat.add_one(b)))
    case 1n+(+a) 0n:
      gt(a)(Equal.sym(Nat, Nat.add(a, 1n), 1n+a, Nat.add_one(a)))
    case 1n+(+a) 1n+(+b):
      Nat.tri(
        Q,
        a,
        b,
        +d => e => lt(
          d
        )(
          Equal.trans(
            Nat,
            1n+b,
            1n+Nat.add(d, 1n+a),
            Nat.add(d, 1n+(1n+a)),
            Equal.cong(Nat, Nat, z => 1n+z, b, Nat.add(d, 1n+a), e),
            Equal.sym(Nat, Nat.add(d, 1n+(1n+a)), 1n+Nat.add(d, 1n+a), Shared.Nat.add_succ(d, 1n+a))
          )
        ),
        e => eq(Equal.cong(Nat, Nat, z => 1n+z, a, b, e)),
        +d => e => gt(
          d
        )(
          Equal.trans(
            Nat,
            1n+a,
            1n+Nat.add(d, 1n+b),
            Nat.add(d, 1n+(1n+b)),
            Equal.cong(Nat, Nat, z => 1n+z, a, Nat.add(d, 1n+b), e),
            Equal.sym(Nat, Nat.add(d, 1n+(1n+b)), 1n+Nat.add(d, 1n+b), Shared.Nat.add_succ(d, 1n+b))
          )
        )
      )

# m is not known, or a voter seen as m may vote in no round below r
def Seen.above(r: Nat, m: Maybe<&2, RRounds.Seen>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{RRounds.Seen{fl, vs}}:
      Nat.is_le(r, fl)

# the floor of a voter does not go down with a cast
def Seen.step_above(
  +r: Nat,
  m: RRounds.Seen,
  x: Types.Cast
) -> {
  Seen.above(r, Some{m}) == True{}: Bool
} -> {Seen.above(r, Some{RRounds.Seen.step(m, x)}) == True{}: Bool}:
  match m x:
    case RRounds.Seen{+fl, +vs} Types.Cast.Vote{+r2, +p, +b}:
      +h => Lists.Bool.by(
        c => {
          Seen.above(
            r,
            Some{
              Bool.pick(
                RRounds.Seen,
                c,
                RRounds.Seen{1n+r2, RRounds.Voted{r2, p} <> vs},
                RRounds.Seen{fl, vs}
              )
            }
          )
            == True{}: Bool
        },
        Nat.is_le(fl, r2),
        et => Shared.Nat.le_succ(r, r2)(Shared.Nat.le_trans(r, fl, r2)(h)(et)),
        ef => h
      )
    case RRounds.Seen{+fl, +vs} Types.Cast.Pass{+r2}:
      +h => Lists.Bool.by(
        c => {
          Seen.above(
            r,
            Some{Bool.pick(RRounds.Seen, c, RRounds.Seen{r2, vs}, RRounds.Seen{fl, vs})}
          )
            == True{}: Bool
        },
        Nat.is_le(fl, r2),
        et => Shared.Nat.le_trans(r, fl, r2)(h)(et),
        ef => h
      )

# the floor of a voter does not go down with its next ballot
def Chain.next_above(
  +r: Nat,
  m: Maybe<&2, RRounds.Seen>,
  x: Maybe<&2, Types.Cast>
) -> {
  Seen.above(r, m) == True{}: Bool
} -> {Seen.above(r, RRounds.Chain.seen.next(m, x)) == True{}: Bool}:
  match m x:
    case None{} None{}:
      h => {==}
    case None{} Some{c}:
      h => {==}
    case Some{s} None{}:
      h => {==}
    case Some{s} Some{c}:
      h => Seen.step_above(r, s, c)(h)

# the floor of a voter never goes down: it is at least r after d more
# ballots, when it is before
def Chain.seen_above(
  d: Nat,
  +bs: List<&2, RRounds.Ballot>,
  +v: String,
  +t: Nat,
  +r: Nat
) -> {
  Seen.above(r, RRounds.Chain.seen(bs, v, t)) == True{}: Bool
} -> {Seen.above(r, RRounds.Chain.seen(bs, v, Nat.add(d, t))) == True{}: Bool}:
  match d:
    case 0n:
      h => h
    case 1n+(+e):
      h => Chain.next_above(
        r,
        RRounds.Chain.seen(bs, v, Nat.add(e, t)),
        RRounds.Ballots.at(bs, v, Nat.add(e, t))
      )(Chain.seen_above(e, bs, v, t, r)(h))

# Chain.voted_above, for a voter seen as m before the vote
def Chain.voted_above.at(
  +r: Nat,
  +p: Types.Pick,
  +b: List<&2, Types.Ref>,
  m: Maybe<&2, RRounds.Seen>
) -> {
  RRounds.Seen.takes(r, m) == True{}: Bool
} -> {Seen.above(1n+r, RRounds.Chain.seen.next(m, Some{Types.Cast.Vote{r, p, b}})) == True{}: Bool}:
  match m:
    case None{}:
      h => Empty.absurd({True{} == True{}: Bool}, Shared.Bool.false_ne_true(h))
    case Some{RRounds.Seen{+fl, +vs}}:
      h => (
        %Equal.sym(Bool, Nat.is_le(fl, r), True{}, h): {Seen.above(1n+r, Some{Bool.pick(RRounds.Seen, _, RRounds.Seen{1n+r, RRounds.Voted{r, p} <> vs}, RRounds.Seen{fl, vs})}) == True{}: Bool}
        Shared.Nat.le_refl(1n+r))

# the floor of a voter after a vote of the round r that counts is r + 1
def Chain.voted_above(
  +bs: List<&2, RRounds.Ballot>,
  +v: String,
  +t: Nat,
  +r: Nat,
  +p: Types.Pick,
  +b: List<&2, Types.Ref>
) -> {
  RRounds.Seen.takes(r, RRounds.Chain.seen(bs, v, t)) == True{}: Bool
} -> {
  RRounds.Ballots.at(bs, v, t) == Some{Types.Cast.Vote{r, p, b}}: Maybe<&2, Types.Cast>
} -> {Seen.above(1n+r, RRounds.Chain.seen(bs, v, 1n+t)) == True{}: Bool}:
  h => e => (
    %Equal.sym(Maybe<&2, Types.Cast>, RRounds.Ballots.at(bs, v, t), Some{Types.Cast.Vote{r, p, b}}, e): {Seen.above(1n+r, RRounds.Chain.seen.next(RRounds.Chain.seen(bs, v, t), _)) == True{}: Bool}
    Chain.voted_above.at(r, p, b, RRounds.Chain.seen(bs, v, t))(h))

# no vote of the round r counts for a voter that may vote in no round below
# r + 1
def Seen.above_takes(
  +r: Nat,
  m: Maybe<&2, RRounds.Seen>
) -> {Seen.above(1n+r, m) == True{}: Bool} -> {RRounds.Seen.takes(r, m) == True{}: Bool} -> Empty:
  match m:
    case None{}:
      h1 => h2 => Shared.Bool.false_ne_true(h2)
    case Some{RRounds.Seen{+fl, vs}}:
      h1 => h2 => Lists.Bool.clash(
        Empty,
        Nat.is_le(1n+r, r),
        Shared.Nat.succ_nle(r),
        Shared.Nat.le_trans(1n+r, fl, r)(h1)(h2)
      )

# after a vote of the round r that counts, no later vote of the round counts
def Chain.voted_last(
  +d: Nat,
  +bs: List<&2, RRounds.Ballot>,
  +v: String,
  +t: Nat,
  +r: Nat,
  +p: Types.Pick,
  +b: List<&2, Types.Ref>
) -> {
  RRounds.Seen.takes(r, RRounds.Chain.seen(bs, v, t)) == True{}: Bool
} -> {
  RRounds.Ballots.at(bs, v, t) == Some{Types.Cast.Vote{r, p, b}}: Maybe<&2, Types.Cast>
} -> {RRounds.Seen.takes(r, RRounds.Chain.seen(bs, v, Nat.add(d, 1n+t))) == True{}: Bool} -> Empty:
  h => e => h2 => Seen.above_takes(
    r,
    RRounds.Chain.seen(bs, v, Nat.add(d, 1n+t))
  )(Chain.seen_above(d, bs, v, 1n+t, 1n+r)(Chain.voted_above(bs, v, t, r, p, b)(h)(e)))(h2)

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof does not run
# what holds of each vote of the voter v in the round r that counts among bs
# holds of the ballot b, when it counts: it is such a vote
def Ballot.counts_by(
  -Q: RRounds.Ballot -> Type,
  +bs: List<&2, RRounds.Ballot>,
  +v: String,
  +r: Nat,
  b: RRounds.Ballot
) -> {
  RRounds.Ballot.counts(RRounds.Roll{bs, v, r}, b) == True{}: Bool
} -> (
  @t: Nat -> @p: Types.Pick -> @ba: List<
    &2,
    Types.Ref> -> {
    RRounds.Seen.takes(r, RRounds.Chain.seen(bs, v, t)) == True{}: Bool
  } -> {
    RRounds.Ballots.at(bs, v, t) == Some{Types.Cast.Vote{r, p, ba}}: Maybe<&2, Types.Cast>
  } -> Q(RRounds.Ballot{v, t, Types.Cast.Vote{r, p, ba}})
) -> Q(b):
  match b:
    case RRounds.Ballot{w, t, Types.Cast.Pass{r2}}:
      h => k => Empty.absurd(
        Q(RRounds.Ballot{w, t, Types.Cast.Pass{r2}}),
        Shared.Bool.false_ne_true(h)
      )
    case RRounds.Ballot{+w, +t, Types.Cast.Vote{+r2, +p, +basis}}:
      h0 => k => (
        +h = Safeties.Ballot.counts_true(bs, v, r, w, t, r2, p, basis)(h0)
        %Equal.sym(String, w, v, Texts.String.eq_sound(w, v)(Shared.Bool.and_true_left(String.eq(w, v), Nat.is_eq(r2, r))(Shared.Bool.and_true_left(Bool.and(String.eq(w, v), Nat.is_eq(r2, r)), Bool.and(RRounds.Seen.takes(r2, RRounds.Chain.seen(bs, v, t)), RRounds.Cast.is(Types.Cast.Vote{r2, p, basis}, RRounds.Ballots.at(bs, v, t))))(h)))): Q(RRounds.Ballot{_, t, Types.Cast.Vote{r2, p, basis}})
        %Equal.sym(Nat, r2, r, Shared.Nat.is_eq_sound(r2, r)(Shared.Bool.and_true_right(String.eq(w, v), Nat.is_eq(r2, r))(Shared.Bool.and_true_left(Bool.and(String.eq(w, v), Nat.is_eq(r2, r)), Bool.and(RRounds.Seen.takes(r2, RRounds.Chain.seen(bs, v, t)), RRounds.Cast.is(Types.Cast.Vote{r2, p, basis}, RRounds.Ballots.at(bs, v, t))))(h)))): Q(RRounds.Ballot{v, t, Types.Cast.Vote{_, p, basis}})
        k(t)(p)(basis)((
          %Shared.Nat.is_eq_sound(r2, r)(Shared.Bool.and_true_right(String.eq(w, v), Nat.is_eq(r2, r))(Shared.Bool.and_true_left(Bool.and(String.eq(w, v), Nat.is_eq(r2, r)), Bool.and(RRounds.Seen.takes(r2, RRounds.Chain.seen(bs, v, t)), RRounds.Cast.is(Types.Cast.Vote{r2, p, basis}, RRounds.Ballots.at(bs, v, t))))(h))): {RRounds.Seen.takes(_, RRounds.Chain.seen(bs, v, t)) == True{}: Bool}
          Shared.Bool.and_true_left(RRounds.Seen.takes(r2, RRounds.Chain.seen(bs, v, t)), RRounds.Cast.is(Types.Cast.Vote{r2, p, basis}, RRounds.Ballots.at(bs, v, t)))(Shared.Bool.and_true_right(Bool.and(String.eq(w, v), Nat.is_eq(r2, r)), Bool.and(RRounds.Seen.takes(r2, RRounds.Chain.seen(bs, v, t)), RRounds.Cast.is(Types.Cast.Vote{r2, p, basis}, RRounds.Ballots.at(bs, v, t))))(h))))((
          %Shared.Nat.is_eq_sound(r2, r)(Shared.Bool.and_true_right(String.eq(w, v), Nat.is_eq(r2, r))(Shared.Bool.and_true_left(Bool.and(String.eq(w, v), Nat.is_eq(r2, r)), Bool.and(RRounds.Seen.takes(r2, RRounds.Chain.seen(bs, v, t)), RRounds.Cast.is(Types.Cast.Vote{r2, p, basis}, RRounds.Ballots.at(bs, v, t))))(h))): {RRounds.Ballots.at(bs, v, t) == Some{Types.Cast.Vote{_, p, basis}}: Maybe<&2, Types.Cast>}
          Cast.is_some(Types.Cast.Vote{r2, p, basis}, RRounds.Ballots.at(bs, v, t))(Shared.Bool.and_true_right(RRounds.Seen.takes(r2, RRounds.Chain.seen(bs, v, t)), RRounds.Cast.is(Types.Cast.Vote{r2, p, basis}, RRounds.Ballots.at(bs, v, t)))(Shared.Bool.and_true_right(Bool.and(String.eq(w, v), Nat.is_eq(r2, r)), Bool.and(RRounds.Seen.takes(r2, RRounds.Chain.seen(bs, v, t)), RRounds.Cast.is(Types.Cast.Vote{r2, p, basis}, RRounds.Ballots.at(bs, v, t))))(h))))))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# two votes of a voter in a round that count are one ballot
def Vote.one(
  +bs: List<&2, RRounds.Ballot>,
  +v: String,
  +r: Nat,
  +t1: Nat,
  +t2: Nat,
  +p1: Types.Pick,
  +ba1: List<&2, Types.Ref>,
  +p2: Types.Pick,
  +ba2: List<&2, Types.Ref>,
  +k1: {RRounds.Seen.takes(r, RRounds.Chain.seen(bs, v, t1)) == True{}: Bool},
  +a1: {RRounds.Ballots.at(bs, v, t1) == Some{Types.Cast.Vote{r, p1, ba1}}: Maybe<&2, Types.Cast>},
  +k2: {RRounds.Seen.takes(r, RRounds.Chain.seen(bs, v, t2)) == True{}: Bool},
  +a2: {RRounds.Ballots.at(bs, v, t2) == Some{Types.Cast.Vote{r, p2, ba2}}: Maybe<&2, Types.Cast>}
) -> {
  RRounds.Ballot{
    v,
    t1,
    Types.Cast.Vote{r, p1, ba1}
  }
    == RRounds.Ballot{v, t2, Types.Cast.Vote{r, p2, ba2}}: RRounds.Ballot
}:
  Nat.tri(
    {
      RRounds.Ballot{
        v,
        t1,
        Types.Cast.Vote{r, p1, ba1}
      }
        == RRounds.Ballot{v, t2, Types.Cast.Vote{r, p2, ba2}}: RRounds.Ballot
    },
    t1,
    t2,
    +d => e => Empty.absurd(
      {
        RRounds.Ballot{
          v,
          t1,
          Types.Cast.Vote{r, p1, ba1}
        }
          == RRounds.Ballot{v, t2, Types.Cast.Vote{r, p2, ba2}}: RRounds.Ballot
      },
      Chain.voted_last(d, bs, v, t1, r, p1, ba1)(k1)(a1)((
          %e: {RRounds.Seen.takes(r, RRounds.Chain.seen(bs, v, _)) == True{}: Bool}
          k2))
    ),
    +e => (
      %e: {RRounds.Ballot{v, t1, Types.Cast.Vote{r, p1, ba1}} == RRounds.Ballot{v, _, Types.Cast.Vote{r, p2, ba2}}: RRounds.Ballot}
      Equal.cong(Types.Cast, RRounds.Ballot, z => RRounds.Ballot{v, t1, z}, Types.Cast.Vote{r, p1, ba1}, Types.Cast.Vote{r, p2, ba2}, Shared.Maybe.some_inj(Types.Cast, Types.Cast.Vote{r, p1, ba1}, Types.Cast.Vote{r, p2, ba2}, Equal.trans(Maybe<&2, Types.Cast>, Some{Types.Cast.Vote{r, p1, ba1}}, RRounds.Ballots.at(bs, v, t1), Some{Types.Cast.Vote{r, p2, ba2}}, Equal.sym(Maybe<&2, Types.Cast>, RRounds.Ballots.at(bs, v, t1), Some{Types.Cast.Vote{r, p1, ba1}}, a1), (
            %Equal.sym(Nat, t1, t2, e): {RRounds.Ballots.at(bs, v, _) == Some{Types.Cast.Vote{r, p2, ba2}}: Maybe<&2, Types.Cast>}
            a2))))),
    +d => e => Empty.absurd(
      {
        RRounds.Ballot{
          v,
          t1,
          Types.Cast.Vote{r, p1, ba1}
        }
          == RRounds.Ballot{v, t2, Types.Cast.Vote{r, p2, ba2}}: RRounds.Ballot
      },
      Chain.voted_last(d, bs, v, t2, r, p2, ba2)(k2)(a2)((
          %e: {RRounds.Seen.takes(r, RRounds.Chain.seen(bs, v, _)) == True{}: Bool}
          k1))
    )
  )

# a vote of a voter in a round that counts is the only one
def Ballot.counts_one(
  +bs: List<&2, RRounds.Ballot>,
  +v: String,
  +r: Nat,
  +b1: RRounds.Ballot,
  +b2: RRounds.Ballot
) -> {
  RRounds.Ballot.counts(RRounds.Roll{bs, v, r}, b1) == True{}: Bool
} -> {
  RRounds.Ballot.counts(RRounds.Roll{bs, v, r}, b2) == True{}: Bool
} -> {b1 == b2: RRounds.Ballot}:
  h1 => h2 => Ballot.counts_by(
    z => {z == b2: RRounds.Ballot},
    bs,
    v,
    r,
    b1
  )(
    h1
  )(
    +t1 => +p1 => +ba1 => +k1 => +a1 => Ballot.counts_by(
      z => {RRounds.Ballot{v, t1, Types.Cast.Vote{r, p1, ba1}} == z: RRounds.Ballot},
      bs,
      v,
      r,
      b2
    )(
      h2
    )(
      +t2 => +p2 => +ba2 => +k2 => +a2 => Vote.one(
        bs,
        v,
        r,
        t1,
        t2,
        p1,
        ba1,
        p2,
        ba2,
        k1,
        a1,
        k2,
        a2
      )
    )
  )

# the ballots xs hold a vote that counts among bs2, when they hold the
# ballot of the voter v with the number t that casts x, and it counts
def Vote.found(
  xs: List<&2, RRounds.Ballot>,
  +bs2: List<&2, RRounds.Ballot>,
  +v: String,
  +r: Nat,
  +t: Nat,
  +x: Types.Cast
) -> {
  List.contains(
    ~Types.Cast,
    ~Coded.Cast.is_eq,
    RRounds.Casts.of(xs, Types.Ref{v, t}),
    x
  )
    == True{}: Bool
} -> {
  RRounds.Ballot.counts(RRounds.Roll{bs2, v, r}, RRounds.Ballot{v, t, x}) == True{}: Bool
} -> {
  Lists.List.pick(
    ~RRounds.Ballot,
    ~RRounds.Roll,
    ~RRounds.Ballot.counts,
    xs,
    RRounds.Roll{bs2, v, r}
  )
    == None{}: Maybe<&2, RRounds.Ballot>
} -> Empty:
  match xs:
    case Nil{}:
      hc => hk => hn => Shared.Bool.false_ne_true(hc)
    case Con{RRounds.Ballot{+w, +u, +y}, +rest}:
      hc => +hk => Lists.Bool.by(
        c => {
          List.find.if(
            RRounds.Ballot,
            RRounds.Ballot{w, u, y},
            u0 => Lists.List.pick(
              ~RRounds.Ballot,
              ~RRounds.Roll,
              ~RRounds.Ballot.counts,
              rest,
              RRounds.Roll{bs2, v, r}
            ),
            c
          )
            == None{}: Maybe<&2, RRounds.Ballot>
        } -> Empty,
        RRounds.Ballot.counts(RRounds.Roll{bs2, v, r}, RRounds.Ballot{w, u, y}),
        et => hn => Lists.Maybe.some_ne_none(RRounds.Ballot, RRounds.Ballot{w, u, y}, hn),
        +ef => +hn => Lists.Bool.by(
          c => {
            List.contains(
              ~Types.Cast,
              ~Coded.Cast.is_eq,
              Shared.Maybe.cons(
                Types.Cast,
                Shared.Maybe.when(Types.Cast, c, z => Some{y}),
                RRounds.Casts.of(rest, Types.Ref{v, t})
              ),
              x
            )
              == True{}: Bool
          } -> Empty,
          Bool.and(String.eq(w, v), Nat.is_eq(u, t)),
          +et2 => hc2 => Lists.List.contains_cons_by(
            ~Types.Cast,
            ~Coded.Cast.is_eq,
            ~Coded.Cast.laws(),
            Empty,
            y,
            RRounds.Casts.of(rest, Types.Ref{v, t}),
            x,
            hc2,
            e => Lists.Bool.clash(
              Empty,
              RRounds.Ballot.counts(RRounds.Roll{bs2, v, r}, RRounds.Ballot{w, u, y}),
              ef,
              (
                %Equal.sym(String, w, v, Texts.String.eq_sound(w, v)(Shared.Bool.and_true_left(String.eq(w, v), Nat.is_eq(u, t))(et2))): {RRounds.Ballot.counts(RRounds.Roll{bs2, v, r}, RRounds.Ballot{_, u, y}) == True{}: Bool}
                %Equal.sym(Nat, u, t, Shared.Nat.is_eq_sound(u, t)(Shared.Bool.and_true_right(String.eq(w, v), Nat.is_eq(u, t))(et2))): {RRounds.Ballot.counts(RRounds.Roll{bs2, v, r}, RRounds.Ballot{v, _, y}) == True{}: Bool}
                %Equal.sym(Types.Cast, y, x, e): {RRounds.Ballot.counts(RRounds.Roll{bs2, v, r}, RRounds.Ballot{v, t, _}) == True{}: Bool}
                hk)
            ),
            cin => Vote.found(rest, bs2, v, r, t, x)(cin)(hk)(hn)
          ),
          ef2 => hc2 => Vote.found(rest, bs2, v, r, t, x)(hc2)(hk)(hn)
        )(hc)
      )

# the vote of a voter in a round that counts stays its vote that counts as
# the ballots grow
def Vote.of_grows(
  +bs: List<&2, RRounds.Ballot>,
  +bs2: List<&2, RRounds.Ballot>,
  +v: String,
  +r: Nat,
  +b: RRounds.Ballot
) -> {
  Ballots.grown(bs, bs2) == True{}: Bool
} -> {
  RRounds.Vote.of(bs, v, r) == Some{b}: Maybe<&2, RRounds.Ballot>
} -> {RRounds.Vote.of(bs2, v, r) == Some{b}: Maybe<&2, RRounds.Ballot>}:
  +hg => +e => Lists.Maybe.by(
    RRounds.Ballot,
    z => {z == Some{b}: Maybe<&2, RRounds.Ballot>},
    RRounds.Vote.of(bs2, v, r),
    en => Ballot.counts_by(
      z => (
        {
          RRounds.Ballot.counts(RRounds.Roll{bs2, v, r}, z) == True{}: Bool
        } -> {None{} == Some{z}: Maybe<&2, RRounds.Ballot>}
      ),
      bs2,
      v,
      r,
      b
    )(
      Ballot.counts_grows(
        bs,
        bs2,
        v,
        r,
        b,
        hg
      )(
        Lists.List.pick_hit(
          ~RRounds.Ballot,
          ~RRounds.Roll,
          ~RRounds.Ballot.counts,
          bs,
          RRounds.Roll{bs, v, r},
          b
        )(e)
      )
    )(
      +t => +p => +ba => k => a => hk => Empty.absurd(
        {
          None{} == Some{RRounds.Ballot{v, t, Types.Cast.Vote{r, p, ba}}}: Maybe<&2, RRounds.Ballot>
        },
        Vote.found(
          bs2,
          bs2,
          v,
          r,
          t,
          Types.Cast.Vote{r, p, ba}
        )(
          Casts.agreed_in(RRounds.Casts.of(bs2, Types.Ref{v, t}), Types.Cast.Vote{r, p, ba})(a)
        )(hk)(en)
      )
    )(
      Ballot.counts_grows(
        bs,
        bs2,
        v,
        r,
        b,
        hg
      )(
        Lists.List.pick_hit(
          ~RRounds.Ballot,
          ~RRounds.Roll,
          ~RRounds.Ballot.counts,
          bs,
          RRounds.Roll{bs, v, r},
          b
        )(e)
      )
    ),
    +b2 => e2 => Equal.cong(
      RRounds.Ballot,
      Maybe<&2, RRounds.Ballot>,
      z => Some{z},
      b2,
      b,
      Ballot.counts_one(
        bs2,
        v,
        r,
        b2,
        b
      )(
        Lists.List.pick_hit(
          ~RRounds.Ballot,
          ~RRounds.Roll,
          ~RRounds.Ballot.counts,
          bs2,
          RRounds.Roll{bs2, v, r},
          b2
        )(e2)
      )(
        Ballot.counts_grows(
          bs,
          bs2,
          v,
          r,
          b,
          hg
        )(
          Lists.List.pick_hit(
            ~RRounds.Ballot,
            ~RRounds.Roll,
            ~RRounds.Ballot.counts,
            bs,
            RRounds.Roll{bs, v, r},
            b
          )(e)
        )
      )
    )
  )

# a node that voted for a pick in a round, with a vote that counts, still
# did as the ballots grow
def Tally.voted_grows(
  +bs: List<&2, RRounds.Ballot>,
  +bs2: List<&2, RRounds.Ballot>,
  +r: Nat,
  +p: Types.Pick,
  +d: String,
  +hg: {Ballots.grown(bs, bs2) == True{}: Bool}
) -> {
  RRounds.Tally.voted(RRounds.Tally{bs, r, p}, d) == True{}: Bool
} -> {RRounds.Tally.voted(RRounds.Tally{bs2, r, p}, d) == True{}: Bool}:
  Lists.Maybe.by(
    RRounds.Ballot,
    z => {
      RRounds.Vote.is_for(p, z) == True{}: Bool
    } -> {RRounds.Vote.is_for(p, RRounds.Vote.of(bs2, d, r)) == True{}: Bool},
    RRounds.Vote.of(bs, d, r),
    en => h => Empty.absurd(
      {RRounds.Vote.is_for(p, RRounds.Vote.of(bs2, d, r)) == True{}: Bool},
      Shared.Bool.false_ne_true(h)
    ),
    +b => e => h => (
      %Equal.sym(Maybe<&2, RRounds.Ballot>, RRounds.Vote.of(bs2, d, r), Some{b}, Vote.of_grows(bs, bs2, d, r, b)(hg)(e)): {RRounds.Vote.is_for(p, _) == True{}: Bool}
      h)
  )

# each of the nodes os that voted for a pick in a round still did as the
# ballots grow
def Tally.holds_grows(
  os: List<&2, String>,
  +bs: List<&2, RRounds.Ballot>,
  +bs2: List<&2, RRounds.Ballot>,
  +r: Nat,
  +p: Types.Pick,
  +hg: {Ballots.grown(bs, bs2) == True{}: Bool}
) -> {
  Shared.List.holds(
    ~String,
    ~RRounds.Tally,
    ~RRounds.Tally.voted,
    os,
    RRounds.Tally{bs, r, p}
  )
    == True{}: Bool
} -> {
  Shared.List.holds(
    ~String,
    ~RRounds.Tally,
    ~RRounds.Tally.voted,
    os,
    RRounds.Tally{bs2, r, p}
  )
    == True{}: Bool
}:
  match os:
    case Nil{}:
      h => h
    case Con{+d, +rest}:
      +h => Shared.List.all.if_both(
        RRounds.Tally.voted(RRounds.Tally{bs2, r, p}, d),
        u => Shared.List.holds(
          ~String,
          ~RRounds.Tally,
          ~RRounds.Tally.voted,
          rest,
          RRounds.Tally{bs2, r, p}
        )
      )(
        Tally.voted_grows(
          bs,
          bs2,
          r,
          p,
          d,
          hg
        )(
          Shared.List.all.if_hit(
            RRounds.Tally.voted(RRounds.Tally{bs, r, p}, d),
            u => Shared.List.holds(
              ~String,
              ~RRounds.Tally,
              ~RRounds.Tally.voted,
              rest,
              RRounds.Tally{bs, r, p}
            )
          )(h)
        )
      )(
        Tally.holds_grows(
          rest,
          bs,
          bs2,
          r,
          p,
          hg
        )(
          Shared.List.all.if_rest(
            RRounds.Tally.voted(RRounds.Tally{bs, r, p}, d),
            u => Shared.List.holds(
              ~String,
              ~RRounds.Tally,
              ~RRounds.Tally.voted,
              rest,
              RRounds.Tally{bs, r, p}
            )
          )(h)
        )
      )

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- only proofs use it; no program runs it
# the tallies g1 and g2 are of one round and one pick, and the ballots of g2
# grew from those of g1
def Tally.grew(g1: RRounds.Tally, g2: RRounds.Tally) -> Bool:
  match g1 g2:
    case RRounds.Tally{+bs, r, p} RRounds.Tally{+bs2, r2, p2}:
      Bool.and(Ballots.grown(bs, bs2), Bool.and(Nat.is_eq(r, r2), Coded.Pick.is_eq(p, p2)))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof does not run
# a node that voted in a tally voted in one that it grew to
def Tally.voted_imp(
  g1: RRounds.Tally,
  g2: RRounds.Tally
) -> {Tally.grew(g1, g2) == True{}: Bool} -> @x:
  String -> {
    RRounds.Tally.voted(g1)(x) == True{}: Bool
  } -> {RRounds.Tally.voted(g2)(x) == True{}: Bool}:
  match g1 g2:
    case RRounds.Tally{+bs, +r, +p} RRounds.Tally{+bs2, +r2, +p2}:
      +h => x => (
        +x = x
        %Shared.Nat.is_eq_sound(r, r2)(Shared.Bool.and_true_left(Nat.is_eq(r, r2), Coded.Pick.is_eq(p, p2))(Shared.Bool.and_true_right(Ballots.grown(bs, bs2), Bool.and(Nat.is_eq(r, r2), Coded.Pick.is_eq(p, p2)))(h))): ({RRounds.Tally.voted(RRounds.Tally{bs, r, p}, x) == True{}: Bool} -> {RRounds.Tally.voted(RRounds.Tally{bs2, _, p2}, x) == True{}: Bool})
        %Coded.Pick.is_eq_sound(p, p2)(Shared.Bool.and_true_right(Nat.is_eq(r, r2), Coded.Pick.is_eq(p, p2))(Shared.Bool.and_true_right(Ballots.grown(bs, bs2), Bool.and(Nat.is_eq(r, r2), Coded.Pick.is_eq(p, p2)))(h))): ({RRounds.Tally.voted(RRounds.Tally{bs, r, p}, x) == True{}: Bool} -> {RRounds.Tally.voted(RRounds.Tally{bs2, r, _}, x) == True{}: Bool})
        Tally.voted_grows(bs, bs2, r, p, x, Shared.Bool.and_true_left(Ballots.grown(bs, bs2), Bool.and(Nat.is_eq(r, r2), Coded.Pick.is_eq(p, p2)))(h)))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# What is known stays known
# ------------------------
# What a reader knows of a force, a promise, a lead: open, or a value. As the
# ballots grow, an open one may get a value, and a value stays. "b is a, or a
# is open" is said with an equation: a capped by b is a.

# b, or open when a is
def Force.cap(a: RRounds.Force, b: RRounds.Force) -> RRounds.Force:
  match a:
    case RRounds.Force.Open{}:
      RRounds.Force.Open{}
    case RRounds.Force.Free{}:
      b
    case RRounds.Force.Bound{r, p}:
      b

# a force capped by itself is itself
def Force.cap_refl(a: RRounds.Force) -> {Force.cap(a, a) == a: RRounds.Force}:
  match a:
    case RRounds.Force.Open{}:
      {==}
    case RRounds.Force.Free{}:
      {==}
    case RRounds.Force.Bound{r, p}:
      {==}

# what two forces leave together stays, when each stays
def Force.join_cap(
  a: RRounds.Force,
  b: RRounds.Force,
  -a2: RRounds.Force,
  -b2: RRounds.Force
) -> {
  Force.cap(a, a2) == a: RRounds.Force
} -> {
  Force.cap(b, b2) == b: RRounds.Force
} -> {
  Force.cap(
    RRounds.Force.join(a, b),
    RRounds.Force.join(a2, b2)
  )
    == RRounds.Force.join(a, b): RRounds.Force
}:
  match a b:
    case RRounds.Force.Open{} y:
      ha => hb => {==}
    case RRounds.Force.Free{} y:
      ha => hb => (
        %Equal.sym(RRounds.Force, a2, RRounds.Force.Free{}, ha): {Force.cap(y, RRounds.Force.join(_, b2)) == y: RRounds.Force}
        hb)
    case RRounds.Force.Bound{r, p} RRounds.Force.Open{}:
      ha => hb => {==}
    case RRounds.Force.Bound{+r, +p} RRounds.Force.Free{}:
      ha => hb => (
        %Equal.sym(RRounds.Force, a2, RRounds.Force.Bound{r, p}, ha): {RRounds.Force.join(_, b2) == RRounds.Force.Bound{r, p}: RRounds.Force}
        %Equal.sym(RRounds.Force, b2, RRounds.Force.Free{}, hb): {RRounds.Force.join(RRounds.Force.Bound{r, p}, _) == RRounds.Force.Bound{r, p}: RRounds.Force}
        {==})
    case RRounds.Force.Bound{+r, +p} RRounds.Force.Bound{+r2, +p2}:
      ha => hb => (
        %Equal.sym(RRounds.Force, a2, RRounds.Force.Bound{r, p}, ha): {Force.cap(Bool.pick(RRounds.Force, Nat.is_lt(r, r2), RRounds.Force.Bound{r2, p2}, RRounds.Force.Bound{r, p}), RRounds.Force.join(_, b2)) == Bool.pick(RRounds.Force, Nat.is_lt(r, r2), RRounds.Force.Bound{r2, p2}, RRounds.Force.Bound{r, p}): RRounds.Force}
        %Equal.sym(RRounds.Force, b2, RRounds.Force.Bound{r2, p2}, hb): {Force.cap(Bool.pick(RRounds.Force, Nat.is_lt(r, r2), RRounds.Force.Bound{r2, p2}, RRounds.Force.Bound{r, p}), RRounds.Force.join(RRounds.Force.Bound{r, p}, _)) == Bool.pick(RRounds.Force, Nat.is_lt(r, r2), RRounds.Force.Bound{r2, p2}, RRounds.Force.Bound{r, p}): RRounds.Force}
        Force.cap_refl(Bool.pick(RRounds.Force, Nat.is_lt(r, r2), RRounds.Force.Bound{r2, p2}, RRounds.Force.Bound{r, p})))

# b, or open when a is
def Mind.cap(a: RRounds.Mind, b: RRounds.Mind) -> RRounds.Mind:
  match a:
    case RRounds.Mind.Open{}:
      RRounds.Mind.Open{}
    case RRounds.Mind.Void{}:
      b
    case RRounds.Mind.Sound{p}:
      b

# what is known of a lead, capped by itself, is itself
def Mind.cap_refl(a: RRounds.Mind) -> {Mind.cap(a, a) == a: RRounds.Mind}:
  match a:
    case RRounds.Mind.Open{}:
      {==}
    case RRounds.Mind.Void{}:
      {==}
    case RRounds.Mind.Sound{p}:
      {==}

# Mind.le holds of a and b, when b is a, or a is open
def Mind.le_of_cap(
  a: RRounds.Mind,
  -b: RRounds.Mind
) -> {Mind.cap(a, b) == a: RRounds.Mind} -> {Mind.le(a, b) == True{}: Bool}:
  match a:
    case RRounds.Mind.Open{}:
      h => {==}
    case RRounds.Mind.Void{}:
      h => (
        %Equal.sym(RRounds.Mind, b, RRounds.Mind.Void{}, h): {Mind.le(RRounds.Mind.Void{}, _) == True{}: Bool}
        {==})
    case RRounds.Mind.Sound{+p}:
      h => (
        %Equal.sym(RRounds.Mind, b, RRounds.Mind.Sound{p}, h): {Mind.le(RRounds.Mind.Sound{p}, _) == True{}: Bool}
        Coded.Pick.is_eq_refl(p))

# the leads ys, each open where that of xs is: xs when each lead of ys is
# that of xs, or that of xs is open (and no other list of the length of xs)
def Minds.cap(xs: List<&2, RRounds.Mind>, ys: List<&2, RRounds.Mind>) -> List<&2, RRounds.Mind>:
  match xs ys:
    case Nil{} Nil{}:
      []
    case Nil{} Con{y, yr}:
      y <> yr
    case Con{x, xr} Nil{}:
      []
    case Con{x, xr} Con{y, yr}:
      Mind.cap(x, y) <> Minds.cap(xr, yr)

# no list with a first item is empty
def Minds.cons_ne_nil(
  -P: Type,
  -y: RRounds.Mind,
  -yr: List<&2, RRounds.Mind>,
  e: {y <> yr == []: List<&2, RRounds.Mind>}
) -> P:
  Empty.absurd(
    P,
    Shared.Bool.false_ne_true(
      Equal.cong(
        List<&2, RRounds.Mind>,
        Bool,
        l => List.is_empty(&2, RRounds.Mind, l),
        y <> yr,
        [],
        e
      )
    )
  )

# no empty list has a first item
def Minds.nil_ne_cons(
  -P: Type,
  -y: RRounds.Mind,
  -yr: List<&2, RRounds.Mind>,
  e: {[] == y <> yr: List<&2, RRounds.Mind>}
) -> P:
  Minds.cons_ne_nil(P, y, yr, Equal.sym(List<&2, RRounds.Mind>, [], y <> yr, e))

# what a vote leaves a lead stays, when what is known of the lead of its
# round does
def Voted.force.at_cap(
  +r: Nat,
  +p: Types.Pick,
  x: RRounds.Mind,
  -y: RRounds.Mind
) -> {
  Mind.cap(x, y) == x: RRounds.Mind
} -> {
  Force.cap(
    RRounds.Voted.force.at(r, p, Some{x}),
    RRounds.Voted.force.at(r, p, Some{y})
  )
    == RRounds.Voted.force.at(r, p, Some{x}): RRounds.Force
}:
  match x:
    case RRounds.Mind.Open{}:
      h => {==}
    case RRounds.Mind.Void{}:
      h => (
        %Equal.sym(RRounds.Mind, y, RRounds.Mind.Void{}, h): {Force.cap(RRounds.Voted.force.at(r, p, Some{RRounds.Mind.Void{}}), RRounds.Voted.force.at(r, p, Some{_})) == RRounds.Voted.force.at(r, p, Some{RRounds.Mind.Void{}}): RRounds.Force}
        {==})
    case RRounds.Mind.Sound{+q}:
      h => (
        %Equal.sym(RRounds.Mind, y, RRounds.Mind.Sound{q}, h): {Force.cap(RRounds.Voted.force.at(r, p, Some{RRounds.Mind.Sound{q}}), RRounds.Voted.force.at(r, p, Some{_})) == RRounds.Voted.force.at(r, p, Some{RRounds.Mind.Sound{q}}): RRounds.Force}
        Force.cap_refl(RRounds.Voted.force.at(r, p, Some{RRounds.Mind.Sound{q}})))

# what a vote of the round i leaves a lead stays, when the leads of the
# rounds before do
def Voted.force_cap(
  xs: List<&2, RRounds.Mind>,
  ys: List<&2, RRounds.Mind>,
  i: Nat,
  +r: Nat,
  +p: Types.Pick
) -> {
  Minds.cap(xs, ys) == xs: List<&2, RRounds.Mind>
} -> {
  Force.cap(
    RRounds.Voted.force.at(r, p, List.get(&2, RRounds.Mind, xs, i)),
    RRounds.Voted.force.at(r, p, List.get(&2, RRounds.Mind, ys, i))
  )
    == RRounds.Voted.force.at(r, p, List.get(&2, RRounds.Mind, xs, i)): RRounds.Force
}:
  match xs ys i:
    case Nil{} Nil{} j:
      h => {==}
    case Nil{} Con{y, yr} j:
      h => Minds.cons_ne_nil(
        {
          Force.cap(
            RRounds.Voted.force.at(r, p, List.get(&2, RRounds.Mind, [], j)),
            RRounds.Voted.force.at(r, p, List.get(&2, RRounds.Mind, y <> yr, j))
          )
            == RRounds.Voted.force.at(r, p, List.get(&2, RRounds.Mind, [], j)): RRounds.Force
        },
        y,
        yr,
        h
      )
    case Con{x, xr} Nil{} j:
      h => Minds.nil_ne_cons(
        {
          Force.cap(
            RRounds.Voted.force.at(r, p, List.get(&2, RRounds.Mind, x <> xr, j)),
            RRounds.Voted.force.at(r, p, List.get(&2, RRounds.Mind, [], j))
          )
            == RRounds.Voted.force.at(r, p, List.get(&2, RRounds.Mind, x <> xr, j)): RRounds.Force
        },
        x,
        xr,
        h
      )
    case Con{+x, +xr} Con{+y, +yr} 0n:
      h => Voted.force.at_cap(
        r,
        p,
        x,
        y
      )(Shared.List.head_eq(RRounds.Mind, Mind.cap(x, y), x, Minds.cap(xr, yr), xr, h))
    case Con{+x, +xr} Con{+y, +yr} 1n+j:
      h => Voted.force_cap(
        xr,
        yr,
        j,
        r,
        p
      )(Shared.List.tail_eq(RRounds.Mind, Mind.cap(x, y), x, Minds.cap(xr, yr), xr, h))

# bend-lint: expect-begin bend-lint-rules/performance/list_index_loop@warning -- a proof does not run
# what some votes leave a lead stays, when the leads of the rounds before do
def Votes.force_cap(
  vs: List<&2, RRounds.Voted>,
  +ms: List<&2, RRounds.Mind>,
  +ms2: List<&2, RRounds.Mind>,
  +hms: {Minds.cap(ms, ms2) == ms: List<&2, RRounds.Mind>}
) -> {
  Force.cap(
    RRounds.Votes.force(ms, vs),
    RRounds.Votes.force(ms2, vs)
  )
    == RRounds.Votes.force(ms, vs): RRounds.Force
}:
  match vs:
    case Nil{}:
      {==}
    case Con{RRounds.Voted{+r, +p}, +rest}:
      Force.join_cap(
        RRounds.Voted.force.at(r, p, List.get(&2, RRounds.Mind, ms, r)),
        RRounds.Votes.force(ms, rest),
        RRounds.Voted.force.at(r, p, List.get(&2, RRounds.Mind, ms2, r)),
        RRounds.Votes.force(ms2, rest)
      )(Voted.force_cap(ms, ms2, r, r, p)(hms))(Votes.force_cap(rest, ms, ms2, hms))
# bend-lint: expect-end bend-lint-rules/performance/list_index_loop@warning

# b, or open when a is
def Promise.cap(a: RRounds.Promise, b: RRounds.Promise) -> RRounds.Promise:
  match a:
    case RRounds.Promise.Open{}:
      RRounds.Promise.Open{}
    case RRounds.Promise.None{}:
      b
    case RRounds.Promise.Held{vs}:
      b

# a promise capped by itself is itself
def Promise.cap_refl(a: RRounds.Promise) -> {Promise.cap(a, a) == a: RRounds.Promise}:
  match a:
    case RRounds.Promise.Open{}:
      {==}
    case RRounds.Promise.None{}:
      {==}
    case RRounds.Promise.Held{vs}:
      {==}

# what a promise leaves a lead stays, when the promise and the leads of the
# rounds before do
def Promise.force_cap(
  a: RRounds.Promise,
  -b: RRounds.Promise,
  +ms: List<&2, RRounds.Mind>,
  +ms2: List<&2, RRounds.Mind>,
  +hms: {Minds.cap(ms, ms2) == ms: List<&2, RRounds.Mind>}
) -> {
  Promise.cap(a, b) == a: RRounds.Promise
} -> {
  Force.cap(
    RRounds.Promise.force(ms, a),
    RRounds.Promise.force(ms2, b)
  )
    == RRounds.Promise.force(ms, a): RRounds.Force
}:
  match a:
    case RRounds.Promise.Open{}:
      h => {==}
    case RRounds.Promise.None{}:
      h => (
        %Equal.sym(RRounds.Promise, b, RRounds.Promise.None{}, h): {Force.cap(RRounds.Promise.force(ms, RRounds.Promise.None{}), RRounds.Promise.force(ms2, _)) == RRounds.Promise.force(ms, RRounds.Promise.None{}): RRounds.Force}
        {==})
    case RRounds.Promise.Held{+vs}:
      h => (
        %Equal.sym(RRounds.Promise, b, RRounds.Promise.Held{vs}, h): {Force.cap(RRounds.Promise.force(ms, RRounds.Promise.Held{vs}), RRounds.Promise.force(ms2, _)) == RRounds.Promise.force(ms, RRounds.Promise.Held{vs}): RRounds.Force}
        Votes.force_cap(vs, ms, ms2, hms))

# b, or nothing when a is
def Seen.cap(a: Maybe<&2, RRounds.Seen>, b: Maybe<&2, RRounds.Seen>) -> Maybe<&2, RRounds.Seen>:
  match a:
    case None{}:
      None{}
    case Some{s}:
      b

# what is known of a voter before one of its ballots stays as the ballots
# grow
def Chain.seen_cap(
  +bs: List<&2, RRounds.Ballot>,
  +bs2: List<&2, RRounds.Ballot>,
  +v: String,
  +t: Nat,
  +hg: {Ballots.grown(bs, bs2) == True{}: Bool}
) -> {
  Seen.cap(
    RRounds.Chain.seen(bs, v, t),
    RRounds.Chain.seen(bs2, v, t)
  )
    == RRounds.Chain.seen(bs, v, t): Maybe<&2, RRounds.Seen>
}:
  Lists.Maybe.by(
    RRounds.Seen,
    z => {Seen.cap(z, RRounds.Chain.seen(bs2, v, t)) == z: Maybe<&2, RRounds.Seen>},
    RRounds.Chain.seen(bs, v, t),
    en => {==},
    +m0 => e0 => Chain.seen_grows(bs, bs2, v, t, m0, hg)(e0)
  )

# the promise of a voter for a round stays, when what is known of it does
def Promise.of_cap(
  +r: Nat,
  m: Maybe<&2, RRounds.Seen>,
  -m2: Maybe<&2, RRounds.Seen>
) -> {
  Seen.cap(m, m2) == m: Maybe<&2, RRounds.Seen>
} -> {
  Promise.cap(
    RRounds.Promise.of(r, m),
    RRounds.Promise.of(r, m2)
  )
    == RRounds.Promise.of(r, m): RRounds.Promise
}:
  match m:
    case None{}:
      h => {==}
    case Some{+s}:
      h => (
        %Equal.sym(Maybe<&2, RRounds.Seen>, m2, Some{s}, h): {Promise.cap(RRounds.Promise.of(r, Some{s}), RRounds.Promise.of(r, _)) == RRounds.Promise.of(r, Some{s}): RRounds.Promise}
        Promise.cap_refl(RRounds.Promise.of(r, Some{s})))

# the promise of a lead itself stays, when what is known of it does
def Promise.own_cap(
  m: Maybe<&2, RRounds.Seen>,
  -m2: Maybe<&2, RRounds.Seen>
) -> {
  Seen.cap(m, m2) == m: Maybe<&2, RRounds.Seen>
} -> {
  Promise.cap(
    RRounds.Promise.own(m),
    RRounds.Promise.own(m2)
  )
    == RRounds.Promise.own(m): RRounds.Promise
}:
  match m:
    case None{}:
      h => {==}
    case Some{+s}:
      h => (
        %Equal.sym(Maybe<&2, RRounds.Seen>, m2, Some{s}, h): {Promise.cap(RRounds.Promise.own(Some{s}), RRounds.Promise.own(_)) == RRounds.Promise.own(Some{s}): RRounds.Promise}
        Promise.cap_refl(RRounds.Promise.own(Some{s})))

# what a node gave a lead stays as the ballots grow
def Promise.read_cap(
  +bs: List<&2, RRounds.Ballot>,
  +bs2: List<&2, RRounds.Ballot>,
  +r: Nat,
  +h: String,
  +t: Nat,
  +basis: List<&2, Types.Ref>,
  +ms: List<&2, RRounds.Mind>,
  +ms2: List<&2, RRounds.Mind>,
  +d: String,
  +hg: {Ballots.grown(bs, bs2) == True{}: Bool}
) -> {
  Promise.cap(
    RRounds.Promise.read(RRounds.Lead{bs, r, h, t, basis, ms}, d),
    RRounds.Promise.read(RRounds.Lead{bs2, r, h, t, basis, ms2}, d)
  )
    == RRounds.Promise.read(RRounds.Lead{bs, r, h, t, basis, ms}, d): RRounds.Promise
}:
  Lists.Bool.by(
    c => {
      Promise.cap(
        Shared.Bool.when(
          RRounds.Promise,
          c,
          u => RRounds.Promise.own(RRounds.Chain.seen(bs, h, t)),
          u => RRounds.Promise.of(r, RRounds.Chain.seen(bs, d, RRounds.Basis.find(basis, d)))
        ),
        Shared.Bool.when(
          RRounds.Promise,
          c,
          u => RRounds.Promise.own(RRounds.Chain.seen(bs2, h, t)),
          u => RRounds.Promise.of(r, RRounds.Chain.seen(bs2, d, RRounds.Basis.find(basis, d)))
        )
      )
        == Shared.Bool.when(
          RRounds.Promise,
          c,
          u => RRounds.Promise.own(RRounds.Chain.seen(bs, h, t)),
          u => RRounds.Promise.of(r, RRounds.Chain.seen(bs, d, RRounds.Basis.find(basis, d)))
        ): RRounds.Promise
    },
    String.eq(d, h),
    et => Promise.own_cap(
      RRounds.Chain.seen(bs, h, t),
      RRounds.Chain.seen(bs2, h, t)
    )(Chain.seen_cap(bs, bs2, h, t, hg)),
    ef => Promise.of_cap(
      r,
      RRounds.Chain.seen(bs, d, RRounds.Basis.find(basis, d)),
      RRounds.Chain.seen(bs2, d, RRounds.Basis.find(basis, d))
    )(Chain.seen_cap(bs, bs2, d, RRounds.Basis.find(basis, d), hg))
  )

# what some nodes leave a lead stays as the ballots grow, when the leads of
# the rounds before do
def Lead.force_cap(
  ds: List<&2, String>,
  +bs: List<&2, RRounds.Ballot>,
  +bs2: List<&2, RRounds.Ballot>,
  +r: Nat,
  +h: String,
  +t: Nat,
  +basis: List<&2, Types.Ref>,
  +ms: List<&2, RRounds.Mind>,
  +ms2: List<&2, RRounds.Mind>,
  +hg: {Ballots.grown(bs, bs2) == True{}: Bool},
  +hms: {Minds.cap(ms, ms2) == ms: List<&2, RRounds.Mind>}
) -> {
  Force.cap(
    RRounds.Lead.force(RRounds.Lead{bs, r, h, t, basis, ms}, ds),
    RRounds.Lead.force(RRounds.Lead{bs2, r, h, t, basis, ms2}, ds)
  )
    == RRounds.Lead.force(RRounds.Lead{bs, r, h, t, basis, ms}, ds): RRounds.Force
}:
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +rest}:
      Force.join_cap(
        RRounds.Promise.force(ms, RRounds.Promise.read(RRounds.Lead{bs, r, h, t, basis, ms}, d)),
        RRounds.Lead.force(RRounds.Lead{bs, r, h, t, basis, ms}, rest),
        RRounds.Promise.force(ms2, RRounds.Promise.read(RRounds.Lead{bs2, r, h, t, basis, ms2}, d)),
        RRounds.Lead.force(RRounds.Lead{bs2, r, h, t, basis, ms2}, rest)
      )(
        Promise.force_cap(
          RRounds.Promise.read(RRounds.Lead{bs, r, h, t, basis, ms}, d),
          RRounds.Promise.read(RRounds.Lead{bs2, r, h, t, basis, ms2}, d),
          ms,
          ms2,
          hms
        )(Promise.read_cap(bs, bs2, r, h, t, basis, ms, ms2, d, hg))
      )(Lead.force_cap(rest, bs, bs2, r, h, t, basis, ms, ms2, hg, hms))

# n, or 0 when the force is open
def Force.gate(f: RRounds.Force, n: Nat) -> Nat:
  match f:
    case RRounds.Force.Open{}:
      0n
    case RRounds.Force.Free{}:
      n
    case RRounds.Force.Bound{r, p}:
      n

# two counts that are one when b is not open, each plus one, are one when
# what a and b leave together is not open
def Force.gate_join(
  a: RRounds.Force,
  b: RRounds.Force,
  +n: Nat,
  +n2: Nat
) -> {
  Force.gate(b, n2) == Force.gate(b, n): Nat
} -> {
  Force.gate(RRounds.Force.join(a, b), 1n+n2) == Force.gate(RRounds.Force.join(a, b), 1n+n): Nat
}:
  match a b:
    case RRounds.Force.Open{} y:
      h => {==}
    case RRounds.Force.Free{} RRounds.Force.Open{}:
      h => {==}
    case RRounds.Force.Free{} RRounds.Force.Free{}:
      h => Equal.cong(Nat, Nat, z => 1n+z, n2, n, h)
    case RRounds.Force.Free{} RRounds.Force.Bound{r2, p2}:
      h => Equal.cong(Nat, Nat, z => 1n+z, n2, n, h)
    case RRounds.Force.Bound{r, p} RRounds.Force.Open{}:
      h => {==}
    case RRounds.Force.Bound{r, p} RRounds.Force.Free{}:
      h => Equal.cong(Nat, Nat, z => 1n+z, n2, n, h)
    case RRounds.Force.Bound{+r, +p} RRounds.Force.Bound{+r2, +p2}:
      h => (
        %Equal.sym(Nat, n2, n, h): {Force.gate(Bool.pick(RRounds.Force, Nat.is_lt(r, r2), RRounds.Force.Bound{r2, p2}, RRounds.Force.Bound{r, p}), 1n+_) == Force.gate(Bool.pick(RRounds.Force, Nat.is_lt(r, r2), RRounds.Force.Bound{r2, p2}, RRounds.Force.Bound{r, p}), 1n+n): Nat}
        {==})

# Lead.count_cap, for one more node, which gave the promise pr
def Lead.count_cap.at(
  pr: RRounds.Promise,
  -pr2: RRounds.Promise,
  +fr: RRounds.Force,
  +n: Nat,
  +n2: Nat,
  +ms: List<&2, RRounds.Mind>
) -> {
  Promise.cap(pr, pr2) == pr: RRounds.Promise
} -> {
  Force.gate(fr, n2) == Force.gate(fr, n): Nat
} -> {
  Force.gate(
    RRounds.Force.join(RRounds.Promise.force(ms, pr), fr),
    Shared.Nat.add_if(RRounds.Promise.is_held(pr2), n2)
  )
    == Force.gate(
      RRounds.Force.join(RRounds.Promise.force(ms, pr), fr),
      Shared.Nat.add_if(RRounds.Promise.is_held(pr), n)
    ): Nat
}:
  match pr:
    case RRounds.Promise.Open{}:
      hp => h => {==}
    case RRounds.Promise.None{}:
      hp => h => (
        %Equal.sym(RRounds.Promise, pr2, RRounds.Promise.None{}, hp): {Force.gate(fr, Shared.Nat.add_if(RRounds.Promise.is_held(_), n2)) == Force.gate(fr, n): Nat}
        h)
    case RRounds.Promise.Held{+vs}:
      hp => h => (
        %Equal.sym(RRounds.Promise, pr2, RRounds.Promise.Held{vs}, hp): {Force.gate(RRounds.Force.join(RRounds.Votes.force(ms, vs), fr), Shared.Nat.add_if(RRounds.Promise.is_held(_), n2)) == Force.gate(RRounds.Force.join(RRounds.Votes.force(ms, vs), fr), 1n+n): Nat}
        Force.gate_join(RRounds.Votes.force(ms, vs), fr, n, n2)(h))

# as many nodes gave a lead a promise as before, as the ballots grow, when
# what they leave it is not open
def Lead.count_cap(
  ds: List<&2, String>,
  +bs: List<&2, RRounds.Ballot>,
  +bs2: List<&2, RRounds.Ballot>,
  +r: Nat,
  +h: String,
  +t: Nat,
  +basis: List<&2, Types.Ref>,
  +ms: List<&2, RRounds.Mind>,
  +ms2: List<&2, RRounds.Mind>,
  +hg: {Ballots.grown(bs, bs2) == True{}: Bool}
) -> {
  Force.gate(
    RRounds.Lead.force(RRounds.Lead{bs, r, h, t, basis, ms}, ds),
    Lists.List.count(
      ~String,
      ~RRounds.Lead,
      ~RRounds.Promise.held,
      ds,
      RRounds.Lead{bs2, r, h, t, basis, ms2}
    )
  )
    == Force.gate(
      RRounds.Lead.force(RRounds.Lead{bs, r, h, t, basis, ms}, ds),
      Lists.List.count(
        ~String,
        ~RRounds.Lead,
        ~RRounds.Promise.held,
        ds,
        RRounds.Lead{bs, r, h, t, basis, ms}
      )
    ): Nat
}:
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +rest}:
      Lead.count_cap.at(
        RRounds.Promise.read(RRounds.Lead{bs, r, h, t, basis, ms}, d),
        RRounds.Promise.read(RRounds.Lead{bs2, r, h, t, basis, ms2}, d),
        RRounds.Lead.force(RRounds.Lead{bs, r, h, t, basis, ms}, rest),
        Lists.List.count(
          ~String,
          ~RRounds.Lead,
          ~RRounds.Promise.held,
          rest,
          RRounds.Lead{bs, r, h, t, basis, ms}
        ),
        Lists.List.count(
          ~String,
          ~RRounds.Lead,
          ~RRounds.Promise.held,
          rest,
          RRounds.Lead{bs2, r, h, t, basis, ms2}
        ),
        ms
      )(
        Promise.read_cap(bs, bs2, r, h, t, basis, ms, ms2, d, hg)
      )(Lead.count_cap(rest, bs, bs2, r, h, t, basis, ms, ms2, hg))

# nothing is known of a lead that the nodes leave open
def Lead.mind.of_open(
  +p: Types.Pick,
  b: Bool
) -> {RRounds.Lead.mind.of(p, RRounds.Force.Open{}, b) == RRounds.Mind.Open{}: RRounds.Mind}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# what is known of a lead stays, when what the nodes leave it does, and as
# many gave it a promise when that is not open
def Lead.mind.of_cap(
  +p: Types.Pick,
  f: RRounds.Force,
  -f2: RRounds.Force,
  +len: Nat,
  +c: Nat,
  -c2: Nat
) -> {
  Force.cap(f, f2) == f: RRounds.Force
} -> {
  Force.gate(f, c2) == Force.gate(f, c): Nat
} -> {
  Mind.cap(
    RRounds.Lead.mind.of(p, f, Lists.Nat.most(len, c)),
    RRounds.Lead.mind.of(p, f2, Lists.Nat.most(len, c2))
  )
    == RRounds.Lead.mind.of(p, f, Lists.Nat.most(len, c)): RRounds.Mind
}:
  match f:
    case RRounds.Force.Open{}:
      h1 => h2 => (
        %Equal.sym(RRounds.Mind, RRounds.Lead.mind.of(p, RRounds.Force.Open{}, Lists.Nat.most(len, c)), RRounds.Mind.Open{}, Lead.mind.of_open(p, Lists.Nat.most(len, c))): {Mind.cap(_, RRounds.Lead.mind.of(p, f2, Lists.Nat.most(len, c2))) == _: RRounds.Mind}
        {==})
    case RRounds.Force.Free{}:
      h1 => h2 => (
        %Equal.sym(RRounds.Force, f2, RRounds.Force.Free{}, h1): {Mind.cap(RRounds.Lead.mind.of(p, RRounds.Force.Free{}, Lists.Nat.most(len, c)), RRounds.Lead.mind.of(p, _, Lists.Nat.most(len, c2))) == RRounds.Lead.mind.of(p, RRounds.Force.Free{}, Lists.Nat.most(len, c)): RRounds.Mind}
        %Equal.sym(Nat, c2, c, h2): {Mind.cap(RRounds.Lead.mind.of(p, RRounds.Force.Free{}, Lists.Nat.most(len, c)), RRounds.Lead.mind.of(p, RRounds.Force.Free{}, Lists.Nat.most(len, _))) == RRounds.Lead.mind.of(p, RRounds.Force.Free{}, Lists.Nat.most(len, c)): RRounds.Mind}
        Mind.cap_refl(RRounds.Lead.mind.of(p, RRounds.Force.Free{}, Lists.Nat.most(len, c))))
    case RRounds.Force.Bound{+r, +q}:
      h1 => h2 => (
        %Equal.sym(RRounds.Force, f2, RRounds.Force.Bound{r, q}, h1): {Mind.cap(RRounds.Lead.mind.of(p, RRounds.Force.Bound{r, q}, Lists.Nat.most(len, c)), RRounds.Lead.mind.of(p, _, Lists.Nat.most(len, c2))) == RRounds.Lead.mind.of(p, RRounds.Force.Bound{r, q}, Lists.Nat.most(len, c)): RRounds.Mind}
        %Equal.sym(Nat, c2, c, h2): {Mind.cap(RRounds.Lead.mind.of(p, RRounds.Force.Bound{r, q}, Lists.Nat.most(len, c)), RRounds.Lead.mind.of(p, RRounds.Force.Bound{r, q}, Lists.Nat.most(len, _))) == RRounds.Lead.mind.of(p, RRounds.Force.Bound{r, q}, Lists.Nat.most(len, c)): RRounds.Mind}
        Mind.cap_refl(RRounds.Lead.mind.of(p, RRounds.Force.Bound{r, q}, Lists.Nat.most(len, c))))

# what is known of the lead of a round, whose vote is b, stays as the ballots
# grow, when the leads of the rounds before do
def Lead.mind.at_cap(
  b: RRounds.Ballot,
  +bs: List<&2, RRounds.Ballot>,
  +bs2: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +r: Nat,
  +h: String,
  +ms: List<&2, RRounds.Mind>,
  +ms2: List<&2, RRounds.Mind>,
  +hg: {Ballots.grown(bs, bs2) == True{}: Bool},
  +hms: {Minds.cap(ms, ms2) == ms: List<&2, RRounds.Mind>}
) -> {
  Mind.cap(
    RRounds.Lead.mind.at(bs, ds, ms, r, h, Some{b}),
    RRounds.Lead.mind.at(bs2, ds, ms2, r, h, Some{b})
  )
    == RRounds.Lead.mind.at(bs, ds, ms, r, h, Some{b}): RRounds.Mind
}:
  match b:
    case RRounds.Ballot{v, t, Types.Cast.Pass{r2}}:
      {==}
    case RRounds.Ballot{v, +t, Types.Cast.Vote{r2, +p, +basis}}:
      Lead.mind.of_cap(
        p,
        RRounds.Lead.force(RRounds.Lead{bs, r, h, t, basis, ms}, ds),
        RRounds.Lead.force(RRounds.Lead{bs2, r, h, t, basis, ms2}, ds),
        List.length(&2, String, ds),
        Lists.List.count(
          ~String,
          ~RRounds.Lead,
          ~RRounds.Promise.held,
          ds,
          RRounds.Lead{bs, r, h, t, basis, ms}
        ),
        Lists.List.count(
          ~String,
          ~RRounds.Lead,
          ~RRounds.Promise.held,
          ds,
          RRounds.Lead{bs2, r, h, t, basis, ms2}
        )
      )(
        Lead.force_cap(ds, bs, bs2, r, h, t, basis, ms, ms2, hg, hms)
      )(Lead.count_cap(ds, bs, bs2, r, h, t, basis, ms, ms2, hg))

# what is known of the lead of a round stays as the ballots grow, when the
# leads of the rounds before do
def Round.mind_cap(
  +bs: List<&2, RRounds.Ballot>,
  +bs2: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +r: Nat,
  +ms: List<&2, RRounds.Mind>,
  +ms2: List<&2, RRounds.Mind>,
  +hg: {Ballots.grown(bs, bs2) == True{}: Bool},
  +hms: {Minds.cap(ms, ms2) == ms: List<&2, RRounds.Mind>}
) -> {
  Mind.cap(
    RRounds.Lead.mind(bs, ds, k, r, ms),
    RRounds.Lead.mind(bs2, ds, k, r, ms2)
  )
    == RRounds.Lead.mind(bs, ds, k, r, ms): RRounds.Mind
}:
  Lists.Maybe.by(
    RRounds.Ballot,
    z => {
      Mind.cap(
        RRounds.Lead.mind.at(bs, ds, ms, r, RRounds.Turn.of(ds, Nat.add(k, r)), z),
        RRounds.Lead.mind.at(
          bs2,
          ds,
          ms2,
          r,
          RRounds.Turn.of(ds, Nat.add(k, r)),
          RRounds.Vote.of(bs2, RRounds.Turn.of(ds, Nat.add(k, r)), r)
        )
      )
        == RRounds.Lead.mind.at(bs, ds, ms, r, RRounds.Turn.of(ds, Nat.add(k, r)), z): RRounds.Mind
    },
    RRounds.Vote.of(bs, RRounds.Turn.of(ds, Nat.add(k, r)), r),
    en => {==},
    +b => e => (
      %Equal.sym(Maybe<&2, RRounds.Ballot>, RRounds.Vote.of(bs2, RRounds.Turn.of(ds, Nat.add(k, r)), r), Some{b}, Vote.of_grows(bs, bs2, RRounds.Turn.of(ds, Nat.add(k, r)), r, b)(hg)(e)): {Mind.cap(RRounds.Lead.mind.at(bs, ds, ms, r, RRounds.Turn.of(ds, Nat.add(k, r)), Some{b}), RRounds.Lead.mind.at(bs2, ds, ms2, r, RRounds.Turn.of(ds, Nat.add(k, r)), _)) == RRounds.Lead.mind.at(bs, ds, ms, r, RRounds.Turn.of(ds, Nat.add(k, r)), Some{b}): RRounds.Mind}
      Lead.mind.at_cap(b, bs, bs2, ds, r, RRounds.Turn.of(ds, Nat.add(k, r)), ms, ms2, hg, hms))
  )

# the leads xs and one more stay, when xs and the one more do
def Minds.cap_snoc(
  xs: List<&2, RRounds.Mind>,
  ys: List<&2, RRounds.Mind>,
  +m: RRounds.Mind,
  +m2: RRounds.Mind
) -> {
  Minds.cap(xs, ys) == xs: List<&2, RRounds.Mind>
} -> {
  Mind.cap(m, m2) == m: RRounds.Mind
} -> {
  Minds.cap(
    List.append(&2, RRounds.Mind, xs, [m]),
    List.append(&2, RRounds.Mind, ys, [m2])
  )
    == List.append(&2, RRounds.Mind, xs, [m]): List<&2, RRounds.Mind>
}:
  match xs ys:
    case Nil{} Nil{}:
      h => hm => Equal.cong(RRounds.Mind, List<&2, RRounds.Mind>, z => [z], Mind.cap(m, m2), m, hm)
    case Nil{} Con{y, yr}:
      h => hm => Minds.cons_ne_nil(
        {
          Minds.cap(
            List.append(&2, RRounds.Mind, [], [m]),
            List.append(&2, RRounds.Mind, y <> yr, [m2])
          )
            == List.append(&2, RRounds.Mind, [], [m]): List<&2, RRounds.Mind>
        },
        y,
        yr,
        h
      )
    case Con{x, xr} Nil{}:
      h => hm => Minds.nil_ne_cons(
        {
          Minds.cap(
            List.append(&2, RRounds.Mind, x <> xr, [m]),
            List.append(&2, RRounds.Mind, [], [m2])
          )
            == List.append(&2, RRounds.Mind, x <> xr, [m]): List<&2, RRounds.Mind>
        },
        x,
        xr,
        h
      )
    case Con{+x, +xr} Con{+y, +yr}:
      +h => hm => (
        %Equal.sym(List<&2, RRounds.Mind>, Minds.cap(List.append(&2, RRounds.Mind, xr, [m]), List.append(&2, RRounds.Mind, yr, [m2])), List.append(&2, RRounds.Mind, xr, [m]), Minds.cap_snoc(xr, yr, m, m2)(Shared.List.tail_eq(RRounds.Mind, Mind.cap(x, y), x, Minds.cap(xr, yr), xr, h))(hm)): {Mind.cap(x, y) <> _ == x <> List.append(&2, RRounds.Mind, xr, [m]): List<&2, RRounds.Mind>}
        Equal.cong(RRounds.Mind, List<&2, RRounds.Mind>, z => z <> List.append(&2, RRounds.Mind, xr, [m]), Mind.cap(x, y), x, Shared.List.head_eq(RRounds.Mind, Mind.cap(x, y), x, Minds.cap(xr, yr), xr, h)))

# what is known of the leads of the rounds below n stays as the ballots grow
def Minds.grows(
  n: Nat,
  +bs: List<&2, RRounds.Ballot>,
  +bs2: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +hg: {Ballots.grown(bs, bs2) == True{}: Bool}
) -> {
  Minds.cap(
    RRounds.Rounds.minds(bs, ds, k, n),
    RRounds.Rounds.minds(bs2, ds, k, n)
  )
    == RRounds.Rounds.minds(bs, ds, k, n): List<&2, RRounds.Mind>
}:
  match n:
    case 0n:
      {==}
    case 1n+(+j):
      Minds.cap_snoc(
        RRounds.Rounds.minds(bs, ds, k, j),
        RRounds.Rounds.minds(bs2, ds, k, j),
        RRounds.Lead.mind(bs, ds, k, j, RRounds.Rounds.minds(bs, ds, k, j)),
        RRounds.Lead.mind(bs2, ds, k, j, RRounds.Rounds.minds(bs2, ds, k, j))
      )(
        Minds.grows(j, bs, bs2, ds, k, hg)
      )(
        Round.mind_cap(
          bs,
          bs2,
          ds,
          k,
          j,
          RRounds.Rounds.minds(bs, ds, k, j),
          RRounds.Rounds.minds(bs2, ds, k, j),
          hg,
          Minds.grows(j, bs, bs2, ds, k, hg)
        )
      )

# what is known of the lead of a round stays as the ballots grow: it is what
# it was, or it was open
def Round.mind_stays(
  +bs: List<&2, RRounds.Ballot>,
  +bs2: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +r: Nat,
  +hg: {Ballots.grown(bs, bs2) == True{}: Bool}
) -> {
  Mind.cap(
    Round.mind(bs, ds, k, r),
    Round.mind(bs2, ds, k, r)
  )
    == Round.mind(bs, ds, k, r): RRounds.Mind
}:
  Round.mind_cap(
    bs,
    bs2,
    ds,
    k,
    r,
    RRounds.Rounds.minds(bs, ds, k, r),
    RRounds.Rounds.minds(bs2, ds, k, r),
    hg,
    Minds.grows(r, bs, bs2, ds, k, hg)
  )

# Nodes that decide in one round
# ------------------------------

# a check, or else false, is the check
def Any.or_false(x: Bool) -> {List.any.if(u => False{}, x) == x: Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

# the nodes decided in one of the rounds xs and then one more round: in one
# of xs, or else in that round
def Rounds.back_snoc(
  xs: List<&2, RRounds.Mind>,
  +m: RRounds.Mind,
  +bs: List<&2, RRounds.Ballot>,
  +os: List<&2, String>,
  +pk: Types.Pick,
  +r0: Nat
) -> {
  RRounds.Rounds.back(
    List.append(&2, RRounds.Mind, xs, [m]),
    bs,
    os,
    pk,
    r0
  )
    == List.any.if(
      u => RRounds.Round.backs(bs, os, pk, Nat.add(List.length(&2, RRounds.Mind, xs), r0), m),
      RRounds.Rounds.back(xs, bs, os, pk, r0)
    ): Bool
}:
  match xs:
    case Nil{}:
      Any.or_false(RRounds.Round.backs(bs, os, pk, r0, m))
    case Con{+y, +rest}:
      Lists.Bool.by(
        z => {
          List.any.if(
            u => RRounds.Rounds.back(List.append(&2, RRounds.Mind, rest, [m]), bs, os, pk, 1n+r0),
            z
          )
            == List.any.if(
              u => RRounds.Round.backs(
                bs,
                os,
                pk,
                1n+Nat.add(List.length(&2, RRounds.Mind, rest), r0),
                m
              ),
              List.any.if(u => RRounds.Rounds.back(rest, bs, os, pk, 1n+r0), z)
            ): Bool
        },
        RRounds.Round.backs(bs, os, pk, r0, y),
        et => {==},
        ef => (
          %Shared.Nat.add_succ(List.length(&2, RRounds.Mind, rest), r0): {RRounds.Rounds.back(List.append(&2, RRounds.Mind, rest, [m]), bs, os, pk, 1n+r0) == List.any.if(u => RRounds.Round.backs(bs, os, pk, _, m), RRounds.Rounds.back(rest, bs, os, pk, 1n+r0)): Bool}
          Rounds.back_snoc(rest, m, bs, os, pk, 1n+r0))
      )

# the nodes decided in one of the rounds up to j: in one of those below j, or
# else in the round j
def Slot.back_step(
  +bs: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +os: List<&2, String>,
  +pk: Types.Pick,
  +j: Nat
) -> {
  RRounds.Rounds.back(
    RRounds.Rounds.minds(bs, ds, k, 1n+j),
    bs,
    os,
    pk,
    0n
  )
    == List.any.if(
      u => RRounds.Round.backs(bs, os, pk, j, Round.mind(bs, ds, k, j)),
      RRounds.Rounds.back(RRounds.Rounds.minds(bs, ds, k, j), bs, os, pk, 0n)
    ): Bool
}:
  %Nat.add_zero(
    j
  ): {
    RRounds.Rounds.back(
      RRounds.Rounds.minds(bs, ds, k, 1n+j),
      bs,
      os,
      pk,
      0n
    )
      == List.any.if(
        u => RRounds.Round.backs(bs, os, pk, _, Round.mind(bs, ds, k, j)),
        RRounds.Rounds.back(RRounds.Rounds.minds(bs, ds, k, j), bs, os, pk, 0n)
      ): Bool
  }
  %Minds.length(
    bs,
    ds,
    k,
    j
  ): {
    RRounds.Rounds.back(
      RRounds.Rounds.minds(bs, ds, k, 1n+j),
      bs,
      os,
      pk,
      0n
    )
      == List.any.if(
        u => RRounds.Round.backs(bs, os, pk, Nat.add(_, 0n), Round.mind(bs, ds, k, j)),
        RRounds.Rounds.back(RRounds.Rounds.minds(bs, ds, k, j), bs, os, pk, 0n)
      ): Bool
  }
  Rounds.back_snoc(RRounds.Rounds.minds(bs, ds, k, j), Round.mind(bs, ds, k, j), bs, os, pk, 0n)

# the nodes decided in a round below n, when they did in one of the rounds
# below n
def Slot.backed_round.go(
  n: Nat,
  +bs: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +os: List<&2, String>,
  +pk: Types.Pick
) -> {
  RRounds.Rounds.back(RRounds.Rounds.minds(bs, ds, k, n), bs, os, pk, 0n) == True{}: Bool
} -> Exists(
  Nat,
  r => {RRounds.Round.backs(bs, os, pk, r, Round.mind(bs, ds, k, r)) == True{}: Bool}
):
  match n:
    case 0n:
      h => Empty.absurd(
        Exists(
          Nat,
          r => {RRounds.Round.backs(bs, os, pk, r, Round.mind(bs, ds, k, r)) == True{}: Bool}
        ),
        Shared.Bool.false_ne_true(h)
      )
    case 1n+(+j):
      h0 => Lists.Bool.by(
        z => {
          List.any.if(
            u => RRounds.Round.backs(bs, os, pk, j, Round.mind(bs, ds, k, j)),
            z
          )
            == True{}: Bool
        } -> Exists(
          Nat,
          r => {RRounds.Round.backs(bs, os, pk, r, Round.mind(bs, ds, k, r)) == True{}: Bool}
        ),
        RRounds.Rounds.back(RRounds.Rounds.minds(bs, ds, k, j), bs, os, pk, 0n),
        et => h => Slot.backed_round.go(j, bs, ds, k, os, pk)(et),
        ef => h => (j, h)
      )(
        Equal.trans(
          Bool,
          List.any.if(
            u => RRounds.Round.backs(bs, os, pk, j, Round.mind(bs, ds, k, j)),
            RRounds.Rounds.back(RRounds.Rounds.minds(bs, ds, k, j), bs, os, pk, 0n)
          ),
          RRounds.Rounds.back(RRounds.Rounds.minds(bs, ds, k, 1n+j), bs, os, pk, 0n),
          True{},
          Equal.sym(
            Bool,
            RRounds.Rounds.back(RRounds.Rounds.minds(bs, ds, k, 1n+j), bs, os, pk, 0n),
            List.any.if(
              u => RRounds.Round.backs(bs, os, pk, j, Round.mind(bs, ds, k, j)),
              RRounds.Rounds.back(RRounds.Rounds.minds(bs, ds, k, j), bs, os, pk, 0n)
            ),
            Slot.back_step(bs, ds, k, os, pk, j)
          ),
          h0
        )
      )

# the nodes that decided a pick in a round still did as the ballots grow,
# when what is known of its lead stays
def Round.backs_grows.of(
  +bs: List<&2, RRounds.Ballot>,
  +bs2: List<&2, RRounds.Ballot>,
  +os: List<&2, String>,
  +pk: Types.Pick,
  +r: Nat,
  m: RRounds.Mind,
  -m2: RRounds.Mind,
  +hg: {Ballots.grown(bs, bs2) == True{}: Bool}
) -> {
  Mind.cap(m, m2) == m: RRounds.Mind
} -> {
  RRounds.Round.backs(bs, os, pk, r, m) == True{}: Bool
} -> {RRounds.Round.backs(bs2, os, pk, r, m2) == True{}: Bool}:
  match m:
    case RRounds.Mind.Open{}:
      hc => h => Empty.absurd(
        {RRounds.Round.backs(bs2, os, pk, r, m2) == True{}: Bool},
        Shared.Bool.false_ne_true(h)
      )
    case RRounds.Mind.Void{}:
      hc => h => Empty.absurd(
        {RRounds.Round.backs(bs2, os, pk, r, m2) == True{}: Bool},
        Shared.Bool.false_ne_true(h)
      )
    case RRounds.Mind.Sound{+q}:
      hc => +h => (
        %Equal.sym(RRounds.Mind, m2, RRounds.Mind.Sound{q}, hc): {RRounds.Round.backs(bs2, os, pk, r, _) == True{}: Bool}
        Round.backs_of(bs2, os, pk, r, q)(Shared.Bool.and_both(Coded.Pick.is_eq(q, pk), Shared.List.holds(~String, ~RRounds.Tally, ~RRounds.Tally.voted, os, RRounds.Tally{bs2, r, pk}))(Shared.Bool.and_true_left(Coded.Pick.is_eq(q, pk), Shared.List.holds(~String, ~RRounds.Tally, ~RRounds.Tally.voted, os, RRounds.Tally{bs, r, pk}))(Round.backs_true(bs, os, pk, r, q)(h)))(Tally.holds_grows(os, bs, bs2, r, pk, hg)(Shared.Bool.and_true_right(Coded.Pick.is_eq(q, pk), Shared.List.holds(~String, ~RRounds.Tally, ~RRounds.Tally.voted, os, RRounds.Tally{bs, r, pk}))(Round.backs_true(bs, os, pk, r, q)(h))))))

# the nodes that decided a pick in a round still did as the ballots grow
def Round.backs_grows(
  +bs: List<&2, RRounds.Ballot>,
  +bs2: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +os: List<&2, String>,
  +pk: Types.Pick,
  +r: Nat,
  +hg: {Ballots.grown(bs, bs2) == True{}: Bool}
) -> {
  RRounds.Round.backs(bs, os, pk, r, Round.mind(bs, ds, k, r)) == True{}: Bool
} -> {RRounds.Round.backs(bs2, os, pk, r, Round.mind(bs2, ds, k, r)) == True{}: Bool}:
  h => Round.backs_grows.of(
    bs,
    bs2,
    os,
    pk,
    r,
    Round.mind(bs, ds, k, r),
    Round.mind(bs2, ds, k, r),
    hg
  )(Round.mind_stays(bs, bs2, ds, k, r, hg))(h)

# nothing is known of the lead m
def Mind.is_open(m: RRounds.Mind) -> Bool:
  match m:
    case RRounds.Mind.Open{}:
      True{}
    case RRounds.Mind.Void{}:
      False{}
    case RRounds.Mind.Sound{p}:
      False{}

# a round whose lead is sound is at most the highest round of a ballot: the
# ballots hold the lead
def Round.sound_top(
  +bs: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +r: Nat,
  -q: Types.Pick
) -> {
  Round.mind(bs, ds, k, r) == RRounds.Mind.Sound{q}: RRounds.Mind
} -> {Nat.is_le(r, RRounds.Rounds.top(bs)) == True{}: Bool}:
  Lists.Maybe.by(
    RRounds.Ballot,
    z => {
      RRounds.Lead.mind.at(
        bs,
        ds,
        RRounds.Rounds.minds(bs, ds, k, r),
        r,
        RRounds.Turn.of(ds, Nat.add(k, r)),
        z
      )
        == RRounds.Mind.Sound{q}: RRounds.Mind
    } -> {Nat.is_le(r, RRounds.Rounds.top(bs)) == True{}: Bool},
    RRounds.Vote.of(bs, RRounds.Turn.of(ds, Nat.add(k, r)), r),
    en => h => Empty.absurd(
      {Nat.is_le(r, RRounds.Rounds.top(bs)) == True{}: Bool},
      Shared.Bool.true_ne_false(
        Equal.cong(
          RRounds.Mind,
          Bool,
          z => Mind.is_open(z),
          RRounds.Mind.Open{},
          RRounds.Mind.Sound{q},
          h
        )
      )
    ),
    +b => e => h => Ballot.counts_by(
      z => {Nat.is_le(r, RRounds.Rounds.top(bs)) == True{}: Bool},
      bs,
      RRounds.Turn.of(ds, Nat.add(k, r)),
      r,
      b
    )(
      Lists.List.pick_hit(
        ~RRounds.Ballot,
        ~RRounds.Roll,
        ~RRounds.Ballot.counts,
        bs,
        RRounds.Roll{bs, RRounds.Turn.of(ds, Nat.add(k, r)), r},
        b
      )(e)
    )(
      +t => +p => +ba => kt => a => Casts.of_top(
        bs,
        RRounds.Turn.of(ds, Nat.add(k, r)),
        t,
        Types.Cast.Vote{r, p, ba}
      )(
        Casts.agreed_in(
          RRounds.Casts.of(bs, Types.Ref{RRounds.Turn.of(ds, Nat.add(k, r)), t}),
          Types.Cast.Vote{r, p, ba}
        )(a)
      )
    )
  )

# Round.backs_top, once what is known of the lead (m) is known
def Round.backs_top.of(
  +bs: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +os: List<&2, String>,
  +pk: Types.Pick,
  +r: Nat,
  m: RRounds.Mind
) -> {
  Round.mind(bs, ds, k, r) == m: RRounds.Mind
} -> {
  RRounds.Round.backs(bs, os, pk, r, m) == True{}: Bool
} -> {Nat.is_le(r, RRounds.Rounds.top(bs)) == True{}: Bool}:
  match m:
    case RRounds.Mind.Open{}:
      e => h => Empty.absurd(
        {Nat.is_le(r, RRounds.Rounds.top(bs)) == True{}: Bool},
        Shared.Bool.false_ne_true(h)
      )
    case RRounds.Mind.Void{}:
      e => h => Empty.absurd(
        {Nat.is_le(r, RRounds.Rounds.top(bs)) == True{}: Bool},
        Shared.Bool.false_ne_true(h)
      )
    case RRounds.Mind.Sound{q}:
      e => h => Round.sound_top(bs, ds, k, r, q)(e)

# a round that some nodes decided a pick in is at most the highest round of a
# ballot
def Round.backs_top(
  +bs: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +os: List<&2, String>,
  +pk: Types.Pick,
  +r: Nat
) -> {
  RRounds.Round.backs(bs, os, pk, r, Round.mind(bs, ds, k, r)) == True{}: Bool
} -> {Nat.is_le(r, RRounds.Rounds.top(bs)) == True{}: Bool}:
  h => Round.backs_top.of(bs, ds, k, os, pk, r, Round.mind(bs, ds, k, r))({==})(h)

# the nodes decided in one of the rounds up to d above r, when they did in
# the round r
def Slot.backed_up.go(
  d: Nat,
  +bs: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +os: List<&2, String>,
  +pk: Types.Pick,
  +r: Nat
) -> {
  RRounds.Round.backs(bs, os, pk, r, Round.mind(bs, ds, k, r)) == True{}: Bool
} -> {
  RRounds.Rounds.back(
    RRounds.Rounds.minds(bs, ds, k, Nat.add(d, 1n+r)),
    bs,
    os,
    pk,
    0n
  )
    == True{}: Bool
}:
  match d:
    case 0n:
      hw => (
        %Equal.sym(Bool, RRounds.Rounds.back(RRounds.Rounds.minds(bs, ds, k, 1n+r), bs, os, pk, 0n), List.any.if(u => RRounds.Round.backs(bs, os, pk, r, Round.mind(bs, ds, k, r)), RRounds.Rounds.back(RRounds.Rounds.minds(bs, ds, k, r), bs, os, pk, 0n)), Slot.back_step(bs, ds, k, os, pk, r)): {_ == True{}: Bool}
        %Equal.sym(Bool, RRounds.Round.backs(bs, os, pk, r, Round.mind(bs, ds, k, r)), True{}, hw): {List.any.if(u => _, RRounds.Rounds.back(RRounds.Rounds.minds(bs, ds, k, r), bs, os, pk, 0n)) == True{}: Bool}
        Shared.List.any.if_true(RRounds.Rounds.back(RRounds.Rounds.minds(bs, ds, k, r), bs, os, pk, 0n)))
    case 1n+(+e):
      hw => (
        %Equal.sym(Bool, RRounds.Rounds.back(RRounds.Rounds.minds(bs, ds, k, 1n+Nat.add(e, 1n+r)), bs, os, pk, 0n), List.any.if(u => RRounds.Round.backs(bs, os, pk, Nat.add(e, 1n+r), Round.mind(bs, ds, k, Nat.add(e, 1n+r))), RRounds.Rounds.back(RRounds.Rounds.minds(bs, ds, k, Nat.add(e, 1n+r)), bs, os, pk, 0n)), Slot.back_step(bs, ds, k, os, pk, Nat.add(e, 1n+r))): {_ == True{}: Bool}
        %Equal.sym(Bool, RRounds.Rounds.back(RRounds.Rounds.minds(bs, ds, k, Nat.add(e, 1n+r)), bs, os, pk, 0n), True{}, Slot.backed_up.go(e, bs, ds, k, os, pk, r)(hw)): {List.any.if(u => RRounds.Round.backs(bs, os, pk, Nat.add(e, 1n+r), Round.mind(bs, ds, k, Nat.add(e, 1n+r))), _) == True{}: Bool}
        {==})

# the nodes that decided a pick in a round decided it for the slot
def Slot.backed_of(
  +bs: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +os: List<&2, String>,
  +pk: Types.Pick,
  +r: Nat
) -> {
  RRounds.Round.backs(bs, os, pk, r, Round.mind(bs, ds, k, r)) == True{}: Bool
} -> {RRounds.Slot.backed(bs, ds, k, os, pk) == True{}: Bool}:
  +hw => (
    %Nat.add_sub_succ(r, RRounds.Rounds.top(bs))(Round.backs_top(bs, ds, k, os, pk, r)(hw)): {RRounds.Rounds.back(RRounds.Rounds.minds(bs, ds, k, _), bs, os, pk, 0n) == True{}: Bool}
    Slot.backed_up.go(Nat.sub(RRounds.Rounds.top(bs), r), bs, ds, k, os, pk, r)(hw))

# the nodes that decided a pick for a slot decided it in one round
def Slot.backed_round(
  +bs: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +os: List<&2, String>,
  +pk: Types.Pick
) -> {
  RRounds.Slot.backed(bs, ds, k, os, pk) == True{}: Bool
} -> Exists(
  Nat,
  r => {RRounds.Round.backs(bs, os, pk, r, Round.mind(bs, ds, k, r)) == True{}: Bool}
):
  h => Slot.backed_round.go(RRounds.Rounds.count(bs), bs, ds, k, os, pk)(h)

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
  +hg => Mind.le_of_cap(
    Round.mind(bs, ds, k, r),
    Round.mind(bs2, ds, k, r)
  )(Round.mind_stays(bs, bs2, ds, k, r, hg))

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof does not run
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
} -> {
  RRounds.Tally.most(bs, ds, r, p) == True{}: Bool
} -> {RRounds.Tally.most(bs2, ds, r, p) == True{}: Bool}:
  +hg => hm => Lists.Nat.most_mono(
    List.length(&2, String, ds),
    Lists.List.count(~String, ~RRounds.Tally, ~RRounds.Tally.voted, ds, RRounds.Tally{bs, r, p}),
    Lists.List.count(~String, ~RRounds.Tally, ~RRounds.Tally.voted, ds, RRounds.Tally{bs2, r, p})
  )(
    Lists.List.count_mono(
      ~String,
      ~RRounds.Tally,
      ~RRounds.Tally,
      ~RRounds.Tally.voted,
      ~RRounds.Tally.voted,
      ~(g1 => g2 => {Tally.grew(g1, g2) == True{}: Bool}),
      ~Tally.voted_imp,
      ds,
      RRounds.Tally{bs, r, p},
      RRounds.Tally{bs2, r, p},
      Shared.Bool.and_both(
        Ballots.grown(bs, bs2),
        Bool.and(Nat.is_eq(r, r), Coded.Pick.is_eq(p, p))
      )(
        hg
      )(
        Shared.Bool.and_both(
          Nat.is_eq(r, r),
          Coded.Pick.is_eq(p, p)
        )(Shared.Nat.is_eq_refl(r))(Coded.Pick.is_eq_refl(p))
      )
    )
  )(hm)
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

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
      hl => hm => h => Empty.absurd(
        {None{} == Some{pk}: Maybe<&2, Types.Pick>},
        Shared.Bool.false_ne_true(hl)
      )
    case RRounds.Mind.Sound{p} RRounds.Mind.Void{}:
      hl => hm => h => Empty.absurd(
        {None{} == Some{pk}: Maybe<&2, Types.Pick>},
        Shared.Bool.false_ne_true(hl)
      )
    case RRounds.Mind.Sound{+p} RRounds.Mind.Sound{+q}:
      hl => hm => (
        %Coded.Pick.is_eq_sound(p, q)(hl): ({RRounds.Round.won(bs, ds, r, RRounds.Mind.Sound{p}) == Some{pk}: Maybe<&2, Types.Pick>} -> {Shared.Maybe.when(Types.Pick, RRounds.Tally.most(bs2, ds, r, _), u => Some{_}) == Some{pk}: Maybe<&2, Types.Pick>})
        Lists.Bool.by(b => {Shared.Maybe.when(Types.Pick, b, u => Some{p}) == Some{pk}: Maybe<&2, Types.Pick>} -> {Shared.Maybe.when(Types.Pick, RRounds.Tally.most(bs2, ds, r, p), u => Some{p}) == Some{pk}: Maybe<&2, Types.Pick>}, RRounds.Tally.most(bs, ds, r, p), et => h => (
          %Equal.sym(Bool, RRounds.Tally.most(bs2, ds, r, p), True{}, hm(p)(et)): {Shared.Maybe.when(Types.Pick, _, u => Some{p}) == Some{pk}: Maybe<&2, Types.Pick>}
          h), ef => h => Empty.absurd({Shared.Maybe.when(Types.Pick, RRounds.Tally.most(bs2, ds, r, p), u => Some{p}) == Some{pk}: Maybe<&2, Types.Pick>}, Shared.Maybe.none_ne_some(Types.Pick, pk, h))))

# a round that decides a pick still does as the ballots grow: the sound votes
# stay sound, and the votes that count still count
def Round.won_grows(
  +bs: List<&2, RRounds.Ballot>,
  +bs2: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +r: Nat,
  +pk: Types.Pick
) -> {
  Ballots.grown(bs, bs2) == True{}: Bool
} -> Round.Won(bs, ds, k, r, pk) -> Round.Won(bs2, ds, k, r, pk):
  +hg => h => Round.won_grows.of(
    bs,
    bs2,
    ds,
    r,
    pk,
    Round.mind(bs, ds, k, r),
    Round.mind(bs2, ds, k, r)
  )(
    Round.mind_grows(bs, bs2, ds, k, r)(hg)
  )(+p => hm => Tally.most_grows(bs, bs2, ds, r, p)(hg)(hm))(h)

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
  Safeties.Safety.won_one(bs, ds, k, r1, r2, p1, p2)

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
  +hg => h => Ex.by(
    Nat,
    r => {RRounds.Round.backs(bs, os, pk, r, Round.mind(bs, ds, k, r)) == True{}: Bool},
    {RRounds.Slot.backed(bs2, ds, k, os, pk) == True{}: Bool},
    Slot.backed_round(bs, ds, k, os, pk)(h),
    +r => hw => Slot.backed_of(
      bs2,
      ds,
      k,
      os,
      pk,
      r
    )(Round.backs_grows(bs, bs2, ds, k, os, pk, r, hg)(hw))
  )

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
      List.contains(
        ~Types.Cast,
        ~Coded.Cast.is_eq,
        RRounds.Casts.of(bs, Types.Ref{v, t}),
        x
      )
        == True{}: Bool
    }
  )
):
  h => hin => Rounds.back_cast(
    RRounds.Rounds.minds(bs, ds, k, RRounds.Rounds.count(bs)),
    bs,
    os,
    pk,
    0n,
    v
  )(h)(hin)

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
  List.contains(
    ~Types.Cast,
    ~Coded.Cast.is_eq,
    RRounds.Casts.of(RRounds.Slot.ballots(fs, c, k), Types.Ref{v, t}),
    x
  )
    == True{}: Bool
} -> {
  List.contains(
    ~Types.Fact,
    ~Coded.Fact.is_eq,
    fs,
    Types.Fact.Vote{v, Types.Step.At{c, k, t}, x}
  )
    == True{}: Bool
}:
  match fs:
    case Nil{}:
      h => h
    case Con{Types.Fact.Ask{+a}, +rest}:
      h => Shared.List.contains_cons(
        ~Types.Fact,
        ~Coded.Fact.is_eq,
        Types.Fact.Ask{a},
        rest,
        Types.Fact.Vote{v, Types.Step.At{c, k, t}, x}
      )(Casts.of_in(rest, c, k, v, t, x)(h))
    case Con{Types.Fact.Vote{+w, Types.Step.Broken{}, +y}, +rest}:
      h => Shared.List.contains_cons(
        ~Types.Fact,
        ~Coded.Fact.is_eq,
        Types.Fact.Vote{w, Types.Step.Broken{}, y},
        rest,
        Types.Fact.Vote{v, Types.Step.At{c, k, t}, x}
      )(Casts.of_in(rest, c, k, v, t, x)(h))
    case Con{Types.Fact.Vote{+w, Types.Step.At{+c2, +k2, +u}, +y}, +rest}:
      Lists.Bool.by(
        b => {
          List.contains(
            ~Types.Cast,
            ~Coded.Cast.is_eq,
            RRounds.Casts.of(
              List.filter.put(
                RRounds.Ballot,
                RRounds.Ballot{w, u, y},
                RRounds.Slot.ballots(rest, c, k),
                b
              ),
              Types.Ref{v, t}
            ),
            x
          )
            == True{}: Bool
        } -> {
          List.contains(
            ~Types.Fact,
            ~Coded.Fact.is_eq,
            Types.Fact.Vote{w, Types.Step.At{c2, k2, u}, y} <> rest,
            Types.Fact.Vote{v, Types.Step.At{c, k, t}, x}
          )
            == True{}: Bool
        },
        Bool.and(Ledgers.Line.is_eq(c2, c), Nat.is_eq(k2, k)),
        +e1 => Lists.Bool.by(
          b => {
            List.contains(
              ~Types.Cast,
              ~Coded.Cast.is_eq,
              Shared.Maybe.cons(
                Types.Cast,
                Shared.Maybe.when(Types.Cast, b, z => Some{y}),
                RRounds.Casts.of(RRounds.Slot.ballots(rest, c, k), Types.Ref{v, t})
              ),
              x
            )
              == True{}: Bool
          } -> {
            List.contains(
              ~Types.Fact,
              ~Coded.Fact.is_eq,
              Types.Fact.Vote{w, Types.Step.At{c2, k2, u}, y} <> rest,
              Types.Fact.Vote{v, Types.Step.At{c, k, t}, x}
            )
              == True{}: Bool
          },
          Bool.and(String.eq(w, v), Nat.is_eq(u, t)),
          +e2 => h => Lists.List.contains_cons_by(
            ~Types.Cast,
            ~Coded.Cast.is_eq,
            ~Coded.Cast.laws(),
            {
              List.contains(
                ~Types.Fact,
                ~Coded.Fact.is_eq,
                Types.Fact.Vote{w, Types.Step.At{c2, k2, u}, y} <> rest,
                Types.Fact.Vote{v, Types.Step.At{c, k, t}, x}
              )
                == True{}: Bool
            },
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
            cin => Shared.List.contains_cons(
              ~Types.Fact,
              ~Coded.Fact.is_eq,
              Types.Fact.Vote{w, Types.Step.At{c2, k2, u}, y},
              rest,
              Types.Fact.Vote{v, Types.Step.At{c, k, t}, x}
            )(Casts.of_in(rest, c, k, v, t, x)(cin))
          ),
          e2 => h => Shared.List.contains_cons(
            ~Types.Fact,
            ~Coded.Fact.is_eq,
            Types.Fact.Vote{w, Types.Step.At{c2, k2, u}, y},
            rest,
            Types.Fact.Vote{v, Types.Step.At{c, k, t}, x}
          )(Casts.of_in(rest, c, k, v, t, x)(h))
        ),
        e1 => h => Shared.List.contains_cons(
          ~Types.Fact,
          ~Coded.Fact.is_eq,
          Types.Fact.Vote{w, Types.Step.At{c2, k2, u}, y},
          rest,
          Types.Fact.Vote{v, Types.Step.At{c, k, t}, x}
        )(Casts.of_in(rest, c, k, v, t, x)(h))
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
) -> {
  List.contains(
    ~Types.Cast,
    ~Coded.Cast.is_eq,
    RRounds.Casts.of(RRounds.Slot.ballots(rest, c, k), Types.Ref{v, t}),
    x
  )
    == True{}: Bool
} -> {
  List.contains(
    ~Types.Cast,
    ~Coded.Cast.is_eq,
    RRounds.Casts.of(RRounds.Slot.ballots(f <> rest, c, k), Types.Ref{v, t}),
    x
  )
    == True{}: Bool
}:
  match f:
    case Types.Fact.Ask{a}:
      h => h
    case Types.Fact.Vote{w, Types.Step.Broken{}, y}:
      h => h
    case Types.Fact.Vote{+w, Types.Step.At{+c2, +k2, +u}, +y}:
      Lists.Bool.by(
        b => {
          List.contains(
            ~Types.Cast,
            ~Coded.Cast.is_eq,
            RRounds.Casts.of(RRounds.Slot.ballots(rest, c, k), Types.Ref{v, t}),
            x
          )
            == True{}: Bool
        } -> {
          List.contains(
            ~Types.Cast,
            ~Coded.Cast.is_eq,
            RRounds.Casts.of(
              List.filter.put(
                RRounds.Ballot,
                RRounds.Ballot{w, u, y},
                RRounds.Slot.ballots(rest, c, k),
                b
              ),
              Types.Ref{v, t}
            ),
            x
          )
            == True{}: Bool
        },
        Bool.and(Ledgers.Line.is_eq(c2, c), Nat.is_eq(k2, k)),
        e1 => Lists.Bool.by(
          b => {
            List.contains(
              ~Types.Cast,
              ~Coded.Cast.is_eq,
              RRounds.Casts.of(RRounds.Slot.ballots(rest, c, k), Types.Ref{v, t}),
              x
            )
              == True{}: Bool
          } -> {
            List.contains(
              ~Types.Cast,
              ~Coded.Cast.is_eq,
              Shared.Maybe.cons(
                Types.Cast,
                Shared.Maybe.when(Types.Cast, b, z => Some{y}),
                RRounds.Casts.of(RRounds.Slot.ballots(rest, c, k), Types.Ref{v, t})
              ),
              x
            )
              == True{}: Bool
          },
          Bool.and(String.eq(w, v), Nat.is_eq(u, t)),
          e2 => h => Shared.List.contains_cons(
            ~Types.Cast,
            ~Coded.Cast.is_eq,
            y,
            RRounds.Casts.of(RRounds.Slot.ballots(rest, c, k), Types.Ref{v, t}),
            x
          )(h),
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
  List.contains(
    ~Types.Fact,
    ~Coded.Fact.is_eq,
    fs,
    Types.Fact.Vote{v, Types.Step.At{c, k, t}, x}
  )
    == True{}: Bool
} -> {
  List.contains(
    ~Types.Cast,
    ~Coded.Cast.is_eq,
    RRounds.Casts.of(RRounds.Slot.ballots(fs, c, k), Types.Ref{v, t}),
    x
  )
    == True{}: Bool
}:
  match fs:
    case Nil{}:
      h => h
    case Con{+f, +rest}:
      hin => Lists.List.contains_cons_by(
        ~Types.Fact,
        ~Coded.Fact.is_eq,
        ~Coded.Fact.laws(),
        {
          List.contains(
            ~Types.Cast,
            ~Coded.Cast.is_eq,
            RRounds.Casts.of(RRounds.Slot.ballots(f <> rest, c, k), Types.Ref{v, t}),
            x
          )
            == True{}: Bool
        },
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
  List.contains(
    ~Types.Cast,
    ~Coded.Cast.is_eq,
    RRounds.Casts.of(Slot.ballots(s, c, k), Types.Ref{v, t}),
    x
  )
    == True{}: Bool
} -> {Facts.Facts.has(s, Types.Fact.Vote{v, Types.Step.At{c, k, t}, x}) == True{}: Bool}:
  h => Facts.Facts.in_has(
    s,
    Types.Fact.Vote{v, Types.Step.At{c, k, t}, x}
  )(Casts.of_in(Facts.Facts.list(s), c, k, v, t, x)(h))

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
  List.contains(
    ~Types.Cast,
    ~Coded.Cast.is_eq,
    RRounds.Casts.of(Slot.ballots(s, c, k), Types.Ref{v, t}),
    x
  )
    == True{}: Bool
}:
  h => Casts.in_of(
    Facts.Facts.list(s),
    c,
    k,
    v,
    t,
    x
  )(Facts.Facts.has_in(s, Types.Fact.Vote{v, Types.Step.At{c, k, t}, x})(h))

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
    List.contains(
      ~Types.Fact,
      ~Coded.Fact.is_eq,
      fs,
      Types.Fact.Vote{v, Types.Step.At{c, k, t}, x}
    )
      == True{}: Bool
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
) -> {
  Shared.List.holds(
    ~RRounds.Ballot,
    ~Grow,
    ~Ballot.sure,
    RRounds.Slot.ballots(fs, c, k),
    Grow{bs0, bs2}
  )
    == True{}: Bool
}:
  match fs:
    case Nil{}:
      {==}
    case Con{Types.Fact.Ask{+a}, +rest}:
      Slot.grown.go(
        rest,
        bs0,
        bs2,
        c,
        k,
        +v => +t => +x => cin => g(
          v
        )(
          t
        )(
          x
        )(
          Shared.List.contains_cons(
            ~Types.Fact,
            ~Coded.Fact.is_eq,
            Types.Fact.Ask{a},
            rest,
            Types.Fact.Vote{v, Types.Step.At{c, k, t}, x}
          )(cin)
        )
      )
    case Con{Types.Fact.Vote{+w, Types.Step.Broken{}, +y}, +rest}:
      Slot.grown.go(
        rest,
        bs0,
        bs2,
        c,
        k,
        +v => +t => +x => cin => g(
          v
        )(
          t
        )(
          x
        )(
          Shared.List.contains_cons(
            ~Types.Fact,
            ~Coded.Fact.is_eq,
            Types.Fact.Vote{w, Types.Step.Broken{}, y},
            rest,
            Types.Fact.Vote{v, Types.Step.At{c, k, t}, x}
          )(cin)
        )
      )
    case Con{Types.Fact.Vote{+w, Types.Step.At{+c2, +k2, +u}, +y}, +rest}:
      Lists.Bool.by(
        b => Slot.Sure(
          Types.Fact.Vote{w, Types.Step.At{c2, k2, u}, y} <> rest,
          bs0,
          bs2,
          c,
          k
        ) -> {
          Shared.List.holds(
            ~RRounds.Ballot,
            ~Grow,
            ~Ballot.sure,
            List.filter.put(
              RRounds.Ballot,
              RRounds.Ballot{w, u, y},
              RRounds.Slot.ballots(rest, c, k),
              b
            ),
            Grow{bs0, bs2}
          )
            == True{}: Bool
        },
        Bool.and(Ledgers.Line.is_eq(c2, c), Nat.is_eq(k2, k)),
        +e1 => g0 => Facts.Case.all_one(
          Slot.Sure(Types.Fact.Vote{w, Types.Step.At{c2, k2, u}, y} <> rest, bs0, bs2, c, k),
          Ballot.sure(Grow{bs0, bs2}, RRounds.Ballot{w, u, y}),
          z0 => Shared.List.holds(
            ~RRounds.Ballot,
            ~Grow,
            ~Ballot.sure,
            RRounds.Slot.ballots(rest, c, k),
            Grow{bs0, bs2}
          ),
          g0,
          g => g(w)(u)(y)((
              %Ledgers.Line.is_eq_sound(c2, c)(Shared.Bool.and_true_left(Ledgers.Line.is_eq(c2, c), Nat.is_eq(k2, k))(e1)): {List.contains(~Types.Fact, ~Coded.Fact.is_eq, Types.Fact.Vote{w, Types.Step.At{c2, k2, u}, y} <> rest, Types.Fact.Vote{w, Types.Step.At{_, k, u}, y}) == True{}: Bool}
              %Shared.Nat.is_eq_sound(k2, k)(Shared.Bool.and_true_right(Ledgers.Line.is_eq(c2, c), Nat.is_eq(k2, k))(e1)): {List.contains(~Types.Fact, ~Coded.Fact.is_eq, Types.Fact.Vote{w, Types.Step.At{c2, k2, u}, y} <> rest, Types.Fact.Vote{w, Types.Step.At{c2, _, u}, y}) == True{}: Bool}
              Lists.List.contains_head(~Types.Fact, ~Coded.Fact.is_eq, ~Coded.Fact.laws(), Types.Fact.Vote{w, Types.Step.At{c2, k2, u}, y}, rest))),
          g => Slot.grown.go(
            rest,
            bs0,
            bs2,
            c,
            k,
            +v => +t => +x => cin => g(
              v
            )(
              t
            )(
              x
            )(
              Shared.List.contains_cons(
                ~Types.Fact,
                ~Coded.Fact.is_eq,
                Types.Fact.Vote{w, Types.Step.At{c2, k2, u}, y},
                rest,
                Types.Fact.Vote{v, Types.Step.At{c, k, t}, x}
              )(cin)
            )
          )
        ),
        e1 => g => Slot.grown.go(
          rest,
          bs0,
          bs2,
          c,
          k,
          +v => +t => +x => cin => g(
            v
          )(
            t
          )(
            x
          )(
            Shared.List.contains_cons(
              ~Types.Fact,
              ~Coded.Fact.is_eq,
              Types.Fact.Vote{w, Types.Step.At{c2, k2, u}, y},
              rest,
              Types.Fact.Vote{v, Types.Step.At{c, k, t}, x}
            )(cin)
          )
        )
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
) -> {
  Ballot.sure(
    Grow{Slot.ballots(s, c, k), Slot.ballots(s2, c, k)},
    RRounds.Ballot{v, t, x}
  )
    == True{}: Bool
}:
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
      Facts.Facts.wider_has(
        s,
        s2,
        Types.Fact.Vote{v, Types.Step.At{c, k, t}, x}
      )(w)(Facts.Facts.in_has(s, Types.Fact.Vote{v, Types.Step.At{c, k, t}, x})(hin))
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
} -> {
  Facts.Facts.has(s, Types.Fact.Vote{v, Types.Step.At{c, k, t}, x}) == True{}: Bool
} -> {Facts.Facts.has(s2, Types.Fact.Vote{v, Types.Step.At{c, k, t}, x}) == True{}: Bool}:
  hk => hx => (
    %Ledgers.Line.is_eq_refl(c): {Bool.or(Bool.not(Bool.and(_, True{})), Facts.Facts.has(s2, Types.Fact.Vote{v, Types.Step.At{c, k, t}, x})) == True{}: Bool}
    %Shared.Nat.is_eq_refl(k): {Bool.or(Bool.not(Bool.and(Ledgers.Line.is_eq(c, c), _)), Facts.Facts.has(s2, Types.Fact.Vote{v, Types.Step.At{c, k, t}, x})) == True{}: Bool}
    Lists.List.holds_in(~Types.Fact, ~Kept, ~Fact.kept, ~Coded.Fact.is_eq, ~Coded.Fact.laws(), Facts.Facts.list(s), Kept{Facts.Facts.crit(s2), c, k}, Types.Fact.Vote{v, Types.Step.At{c, k, t}, x})(hk)(Facts.Facts.has_in(s, Types.Fact.Vote{v, Types.Step.At{c, k, t}, x})(hx)))

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
) -> {
  Ballot.sure(
    Grow{Slot.ballots(s, c, k), Slot.ballots(s2, c, k)},
    RRounds.Ballot{v, t, x}
  )
    == True{}: Bool
}:
  Lists.Bool.by(
    b => {
      Bool.or(
        Bool.not(b),
        RRounds.Cast.is(x, RRounds.Ballots.at(Slot.ballots(s2, c, k), v, t))
      )
        == True{}: Bool
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
              Bool.not(
                List.is_empty(
                  &2,
                  Types.Cast,
                  RRounds.Casts.of(Slot.ballots(s, c, k), Types.Ref{v, t})
                )
              ),
              Shared.List.holds(
                ~Types.Cast,
                ~Types.Cast,
                ~Coded.Cast.is_eq,
                RRounds.Casts.of(Slot.ballots(s, c, k), Types.Ref{v, t}),
                x
              )
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
            Casts.has_of(
              s,
              c,
              k,
              v,
              t,
              y
            )(Slot.kept_has(s2, s, c, k, v, t, y)(hk2)(Casts.of_has(s2, c, k, v, t, y)(cy)))
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
) -> {
  Lines.Votes.decided(s, c, k, ds) == Some{pk}: Maybe<&2, Types.Pick>
} -> Votes.Voted(s, c, k, pk):
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
    RRounds.Slot.chance(
      Slot.ballots(s, c, k),
      [name],
      k,
      name
    )
      == Some{RRounds.Chance{t, r, b, RRounds.Force.Free{}}}: Maybe<&2, RRounds.Chance>
  }
    & (
      {
        Facts.Facts.cast(s, name, Types.Step.At{c, k, t}) == False{}: Bool
      }
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

# Alone: the chain of the node
# ----------------------------

# the node after as many nodes as pre holds is the one that follows them
def Turn.nth_mid(
  pre: List<&2, String>,
  -y: String,
  -rest: List<&2, String>
) -> {
  RRounds.Turn.nth(
    List.append(&2, String, pre, y <> rest),
    List.length(&2, String, pre)
  )
    == y: String
}:
  match pre:
    case Nil{}:
      {==}
    case Con{z, r}:
      Turn.nth_mid(r, y, rest)

# the number before n
def Turn.pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

# bend-lint: expect-begin bend-lint-rules/performance/append_in_loop@warning -- a proof does not run
# bend-lint: expect-begin bend-lint-rules/performance/dead_accumulator@information -- a proof does not run
# bend-lint: expect-begin bend-lint-rules/performance/list_index_loop@warning -- a proof does not run
# a walk of k steps from the node y, that follows the nodes pre in the round
# of x then ns, ends at the place that the division of k gives
def Turn.go_nth(
  k: Nat,
  +x: String,
  +ns: List<&2, String>,
  +pre: List<&2, String>,
  +y: String,
  rest: List<&2, String>,
  +d: Nat
) -> {
  x <> ns == List.append(&2, String, pre, y <> rest): List<&2, String>
} -> {
  RRounds.Turn.go(
    k,
    x,
    ns,
    y,
    rest
  )
    == RRounds.Turn.nth(
      x <> ns,
      Pair.snd(
        Nat,
        Nat,
        Nat.divmod.go(k, List.length(&2, String, rest), d, List.length(&2, String, pre))
      )
    ): String
}:
  match k rest:
    case 0n Nil{}:
      e =>
        %Equal.sym(
          List<&2, String>,
          x <> ns,
          List.append(&2, String, pre, [y]),
          e
        ): {y == RRounds.Turn.nth(_, List.length(&2, String, pre)): String}
        Equal.sym(
          String,
          RRounds.Turn.nth(List.append(&2, String, pre, [y]), List.length(&2, String, pre)),
          y,
          Turn.nth_mid(pre, y, [])
        )
    case 0n Con{+z, +r2}:
      e =>
        %Equal.sym(
          List<&2, String>,
          x <> ns,
          List.append(&2, String, pre, y <> z <> r2),
          e
        ): {y == RRounds.Turn.nth(_, List.length(&2, String, pre)): String}
        Equal.sym(
          String,
          RRounds.Turn.nth(
            List.append(&2, String, pre, y <> z <> r2),
            List.length(&2, String, pre)
          ),
          y,
          Turn.nth_mid(pre, y, z <> r2)
        )
    case 1n+j Nil{}:
      e =>
        %Equal.sym(
          Nat,
          List.length(&2, String, pre),
          List.length(&2, String, ns),
          Equal.cong(
            Nat,
            Nat,
            Turn.pred,
            1n+List.length(&2, String, pre),
            1n+List.length(&2, String, ns),
            Equal.trans(
              Nat,
              1n+List.length(&2, String, pre),
              List.length(&2, String, List.append(&2, String, pre, [y])),
              1n+List.length(&2, String, ns),
              Equal.sym(
                Nat,
                List.length(&2, String, List.append(&2, String, pre, [y])),
                1n+List.length(&2, String, pre),
                Shared.List.length_snoc(String, pre, y)
              ),
              Equal.cong(
                List<&2, String>,
                Nat,
                zs => List.length(&2, String, zs),
                List.append(&2, String, pre, [y]),
                x <> ns,
                Equal.sym(List<&2, String>, x <> ns, List.append(&2, String, pre, [y]), e)
              )
            )
          )
        ): {
          RRounds.Turn.go(
            j,
            x,
            ns,
            x,
            ns
          )
            == RRounds.Turn.nth(x <> ns, Pair.snd(Nat, Nat, Nat.divmod.go(j, _, 1n+d, 0n))): String
        }
        Turn.go_nth(j, x, ns, [], x, ns, 1n+d)({==})
    case 1n+j Con{+z, +r2}:
      e =>
        %Shared.List.length_snoc(
          String,
          pre,
          y
        ): {
          RRounds.Turn.go(
            j,
            x,
            ns,
            z,
            r2
          )
            == RRounds.Turn.nth(
              x <> ns,
              Pair.snd(Nat, Nat, Nat.divmod.go(j, List.length(&2, String, r2), d, _))
            ): String
        }
        Turn.go_nth(
          j,
          x,
          ns,
          List.append(&2, String, pre, [y]),
          z,
          r2,
          d
        )(
          Equal.trans(
            List<&2, String>,
            x <> ns,
            List.append(&2, String, pre, y <> z <> r2),
            List.append(&2, String, List.append(&2, String, pre, [y]), z <> r2),
            e,
            Equal.sym(
              List<&2, String>,
              List.append(&2, String, List.append(&2, String, pre, [y]), z <> r2),
              List.append(&2, String, pre, y <> z <> r2),
              Shared.List.append_assoc(String, pre, [y], z <> r2)
            )
          )
        )
# bend-lint: expect-end bend-lint-rules/performance/append_in_loop@warning
# bend-lint: expect-end bend-lint-rules/performance/dead_accumulator@information
# bend-lint: expect-end bend-lint-rules/performance/list_index_loop@warning

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# the node whose turn a number is, read at its place in a round, is the one
# that a walk of as many steps ends at
def Turn.of_walk(
  ns: List<&2, String>,
  k: Nat
) -> {RRounds.Turn.of(ns, k) == RRounds.Turn.walk(ns, k): String}:
  match ns:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      Equal.sym(
        String,
        RRounds.Turn.go(k, x, r, x, r),
        RRounds.Turn.nth(x <> r, Nat.mod(k, 1n+List.length(&2, String, r))),
        Turn.go_nth(k, x, r, [], x, r, 0n)({==})
      )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# the turn of each number is of the node that decides alone
def Turn.go_one(k: Nat, +name: String) -> {RRounds.Turn.go(k, name, [], name, []) == name: String}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      Turn.go_one(j, name)

# the turn of each number is of the node that decides alone, as Turn.of
# reads it
def Turn.of_one(+k: Nat, +name: String) -> {RRounds.Turn.of([name], k) == name: String}:
  Equal.trans(
    String,
    RRounds.Turn.of([name], k),
    RRounds.Turn.go(k, name, [], name, []),
    name,
    Turn.of_walk([name], k),
    Turn.go_one(k, name)
  )

# the promise that a node that leads gives itself, when it cast no vote that
# counts before
def Promise.read_own(
  +bs: List<&2, RRounds.Ballot>,
  +name: String,
  +r: Nat,
  +t: Nat,
  +fl: Nat,
  +basis: List<&2, Types.Ref>,
  +ms: List<&2, RRounds.Mind>,
  es: {RRounds.Chain.seen(bs, name, t) == Some{RRounds.Seen{fl, []}}: Maybe<&2, RRounds.Seen>}
) -> {
  RRounds.Promise.read(
    RRounds.Lead{bs, r, name, t, basis, ms},
    name
  )
    == RRounds.Promise.Held{[]}: RRounds.Promise
}:
  %Equal.sym(
    Bool,
    String.eq(name, name),
    True{},
    Texts.String.eq_refl(name)
  ): {
    Shared.Bool.when(
      RRounds.Promise,
      _,
      u => RRounds.Promise.own(RRounds.Chain.seen(bs, name, t)),
      u => RRounds.Promise.of(r, RRounds.Chain.seen(bs, name, RRounds.Basis.find(basis, name)))
    )
      == RRounds.Promise.Held{[]}: RRounds.Promise
  }
  %Equal.sym(
    Maybe<&2, RRounds.Seen>,
    RRounds.Chain.seen(bs, name, t),
    Some{RRounds.Seen{fl, []}},
    es
  ): {RRounds.Promise.own(_) == RRounds.Promise.Held{[]}: RRounds.Promise}
  {==}

# the lead of a node that decides alone is sound, when it cast no vote that
# counts before
def Lead.mind_own(
  +bs: List<&2, RRounds.Ballot>,
  +name: String,
  +r: Nat,
  +t: Nat,
  +fl: Nat,
  +p: Types.Pick,
  +basis: List<&2, Types.Ref>,
  +ms: List<&2, RRounds.Mind>,
  es: {RRounds.Chain.seen(bs, name, t) == Some{RRounds.Seen{fl, []}}: Maybe<&2, RRounds.Seen>}
) -> {
  RRounds.Lead.mind.by(
    p,
    RRounds.Lead{bs, r, name, t, basis, ms},
    [name]
  )
    == RRounds.Mind.Sound{p}: RRounds.Mind
}:
  %Equal.sym(
    RRounds.Promise,
    RRounds.Promise.read(RRounds.Lead{bs, r, name, t, basis, ms}, name),
    RRounds.Promise.Held{[]},
    Promise.read_own(bs, name, r, t, fl, basis, ms, es)
  ): {
    RRounds.Lead.mind.of(
      p,
      RRounds.Force.join(RRounds.Promise.force(ms, _), RRounds.Force.Free{}),
      Lists.Nat.most(1n, Shared.Nat.add_if(RRounds.Promise.is_held(_), 0n))
    )
      == RRounds.Mind.Sound{p}: RRounds.Mind
  }
  {==}

# the round of a vote that counts, of a node that decides alone and cast no
# vote that counts before, decides its pick
def Round.won_own(
  +bs: List<&2, RRounds.Ballot>,
  +name: String,
  +k: Nat,
  +r: Nat,
  +t: Nat,
  +fl: Nat,
  +p: Types.Pick,
  +basis: List<&2, Types.Ref>,
  +ev: {
    RRounds.Vote.of(
      bs,
      name,
      r
    )
      == Some{RRounds.Ballot{name, t, Types.Cast.Vote{r, p, basis}}}: Maybe<&2, RRounds.Ballot>
  },
  es: {RRounds.Chain.seen(bs, name, t) == Some{RRounds.Seen{fl, []}}: Maybe<&2, RRounds.Seen>}
) -> Round.Won(bs, [name], k, r, p):
  %Equal.sym(
    String,
    RRounds.Turn.of([name], Nat.add(k, r)),
    name,
    Turn.of_one(Nat.add(k, r), name)
  ): {
    RRounds.Round.won(
      bs,
      [name],
      r,
      RRounds.Lead.mind.at(
        bs,
        [name],
        RRounds.Rounds.minds(bs, [name], k, r),
        r,
        _,
        RRounds.Vote.of(bs, _, r)
      )
    )
      == Some{p}: Maybe<&2, Types.Pick>
  }
  %Equal.sym(
    Maybe<&2, RRounds.Ballot>,
    RRounds.Vote.of(bs, name, r),
    Some{RRounds.Ballot{name, t, Types.Cast.Vote{r, p, basis}}},
    ev
  ): {
    RRounds.Round.won(
      bs,
      [name],
      r,
      RRounds.Lead.mind.at(bs, [name], RRounds.Rounds.minds(bs, [name], k, r), r, name, _)
    )
      == Some{p}: Maybe<&2, Types.Pick>
  }
  %Equal.sym(
    RRounds.Mind,
    RRounds.Lead.mind.by(
      p,
      RRounds.Lead{bs, r, name, t, basis, RRounds.Rounds.minds(bs, [name], k, r)},
      [name]
    ),
    RRounds.Mind.Sound{p},
    Lead.mind_own(bs, name, r, t, fl, p, basis, RRounds.Rounds.minds(bs, [name], k, r), es)
  ): {RRounds.Round.won(bs, [name], r, _) == Some{p}: Maybe<&2, Types.Pick>}
  %Equal.sym(
    Maybe<&2, RRounds.Ballot>,
    RRounds.Vote.of(bs, name, r),
    Some{RRounds.Ballot{name, t, Types.Cast.Vote{r, p, basis}}},
    ev
  ): {
    Shared.Maybe.when(
      Types.Pick,
      Lists.Nat.most(1n, Shared.Nat.add_if(RRounds.Vote.is_for(p, _), 0n)),
      u => Some{p}
    )
      == Some{p}: Maybe<&2, Types.Pick>
  }
  %Equal.sym(
    Bool,
    Coded.Pick.is_eq(p, p),
    True{},
    Coded.Pick.is_eq_refl(p)
  ): {
    Shared.Maybe.when(
      Types.Pick,
      Lists.Nat.most(1n, Shared.Nat.add_if(_, 0n)),
      u => Some{p}
    )
      == Some{p}: Maybe<&2, Types.Pick>
  }
  {==}

# Vote.of_counted, once the ballot counts
def Vote.of_counted.fin(
  +bs: List<&2, RRounds.Ballot>,
  +v: String,
  +r: Nat,
  +t: Nat,
  +p: Types.Pick,
  +basis: List<&2, Types.Ref>,
  +ha: {RRounds.Ballots.at(bs, v, t) == Some{Types.Cast.Vote{r, p, basis}}: Maybe<&2, Types.Cast>},
  +hc: {
    RRounds.Ballot.counts(
      RRounds.Roll{bs, v, r},
      RRounds.Ballot{v, t, Types.Cast.Vote{r, p, basis}}
    )
      == True{}: Bool
  }
) -> {
  RRounds.Vote.of(
    bs,
    v,
    r
  )
    == Some{RRounds.Ballot{v, t, Types.Cast.Vote{r, p, basis}}}: Maybe<&2, RRounds.Ballot>
}:
  Lists.Maybe.by(
    RRounds.Ballot,
    z => {z == Some{RRounds.Ballot{v, t, Types.Cast.Vote{r, p, basis}}}: Maybe<&2, RRounds.Ballot>},
    RRounds.Vote.of(bs, v, r),
    en => Empty.absurd(
      {
        None{}
          == Some{RRounds.Ballot{v, t, Types.Cast.Vote{r, p, basis}}}: Maybe<&2, RRounds.Ballot>
      },
      Vote.found(
        bs,
        bs,
        v,
        r,
        t,
        Types.Cast.Vote{r, p, basis}
      )(
        Casts.agreed_in(RRounds.Casts.of(bs, Types.Ref{v, t}), Types.Cast.Vote{r, p, basis})(ha)
      )(hc)(en)
    ),
    +b2 => e2 => Equal.cong(
      RRounds.Ballot,
      Maybe<&2, RRounds.Ballot>,
      z => Some{z},
      b2,
      RRounds.Ballot{v, t, Types.Cast.Vote{r, p, basis}},
      Ballot.counts_one(
        bs,
        v,
        r,
        b2,
        RRounds.Ballot{v, t, Types.Cast.Vote{r, p, basis}}
      )(
        Lists.List.pick_hit(
          ~RRounds.Ballot,
          ~RRounds.Roll,
          ~RRounds.Ballot.counts,
          bs,
          RRounds.Roll{bs, v, r},
          b2
        )(e2)
      )(hc)
    )
  )

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof does not run
# the vote of a voter in a round that counts is its ballot that casts a vote
# of the round, where a vote of the round counts
def Vote.of_counted(
  +bs: List<&2, RRounds.Ballot>,
  +v: String,
  +r: Nat,
  +t: Nat,
  +p: Types.Pick,
  +basis: List<&2, Types.Ref>,
  +hk: {RRounds.Seen.takes(r, RRounds.Chain.seen(bs, v, t)) == True{}: Bool},
  +ha: {RRounds.Ballots.at(bs, v, t) == Some{Types.Cast.Vote{r, p, basis}}: Maybe<&2, Types.Cast>}
) -> {
  RRounds.Vote.of(
    bs,
    v,
    r
  )
    == Some{RRounds.Ballot{v, t, Types.Cast.Vote{r, p, basis}}}: Maybe<&2, RRounds.Ballot>
}:
  Vote.of_counted.fin(bs, v, r, t, p, basis, ha, (
      %Safeties.Ballot.and_counts(bs, v, r, v, t, r, p, basis): {_ == True{}: Bool}
      Shared.Bool.and_both(Bool.and(String.eq(v, v), Nat.is_eq(r, r)), Bool.and(RRounds.Seen.takes(r, RRounds.Chain.seen(bs, v, t)), RRounds.Cast.is(Types.Cast.Vote{r, p, basis}, RRounds.Ballots.at(bs, v, t))))(Shared.Bool.and_both(String.eq(v, v), Nat.is_eq(r, r))(Texts.String.eq_refl(v))(Shared.Nat.is_eq_refl(r)))(Shared.Bool.and_both(RRounds.Seen.takes(r, RRounds.Chain.seen(bs, v, t)), RRounds.Cast.is(Types.Cast.Vote{r, p, basis}, RRounds.Ballots.at(bs, v, t)))(hk)(Cast.is_of(Types.Cast.Vote{r, p, basis}, RRounds.Ballots.at(bs, v, t), ha)))))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# Chain.quiet, for one more ballot of the node, which casts x after it is
# seen as m0
def Chain.quiet.step(
  m0: RRounds.Seen,
  x: Types.Cast,
  +bs: List<&2, RRounds.Ballot>,
  +name: String,
  +k: Nat,
  +j: Nat
) -> {
  RRounds.Chain.seen(bs, name, j) == Some{m0}: Maybe<&2, RRounds.Seen>
} -> {
  RRounds.Ballots.at(bs, name, j) == Some{x}: Maybe<&2, Types.Cast>
} -> {
  RRounds.Seen.votes(m0) == []: List<&2, RRounds.Voted>
} -> {
  RRounds.Slot.decided(bs, [name], k) == None{}: Maybe<&2, Types.Pick>
} -> {RRounds.Seen.votes(RRounds.Seen.step(m0, x)) == []: List<&2, RRounds.Voted>}:
  match m0 x:
    case RRounds.Seen{+fl, +vs} Types.Cast.Pass{+r}:
      es => ea => +ev => hu => Lists.Bool.by(
        c => {
          RRounds.Seen.votes(
            Bool.pick(RRounds.Seen, c, RRounds.Seen{r, vs}, RRounds.Seen{fl, vs})
          )
            == []: List<&2, RRounds.Voted>
        },
        Nat.is_le(fl, r),
        et => ev,
        ef => ev
      )
    case RRounds.Seen{+fl, +vs} Types.Cast.Vote{+r, +p, +b}:
      +es => +ea => +ev => +hu => Lists.Bool.by(
        c => {
          RRounds.Seen.votes(
            Bool.pick(
              RRounds.Seen,
              c,
              RRounds.Seen{1n+r, RRounds.Voted{r, p} <> vs},
              RRounds.Seen{fl, vs}
            )
          )
            == []: List<&2, RRounds.Voted>
        },
        Nat.is_le(fl, r),
        et => Empty.absurd(
          {RRounds.Voted{r, p} <> vs == []: List<&2, RRounds.Voted>},
          Ex.by(
            Types.Pick,
            q => {RRounds.Slot.decided(bs, [name], k) == Some{q}: Maybe<&2, Types.Pick>},
            Empty,
            Slot.won_decided(
              bs,
              [name],
              k,
              r,
              p
            )(Round.won_own(bs, name, k, r, j, fl, p, b, Vote.of_counted(bs, name, r, j, p, b, (
                    %Equal.sym(Maybe<&2, RRounds.Seen>, RRounds.Chain.seen(bs, name, j), Some{RRounds.Seen{fl, vs}}, es): {RRounds.Seen.takes(r, _) == True{}: Bool}
                    et), ea), (
                  %ev: {RRounds.Chain.seen(bs, name, j) == Some{RRounds.Seen{fl, _}}: Maybe<&2, RRounds.Seen>}
                  es))),
            q => e => Shared.Maybe.none_ne_some(
              Types.Pick,
              q,
              Equal.trans(
                Maybe<&2, Types.Pick>,
                None{},
                RRounds.Slot.decided(bs, [name], k),
                Some{q},
                Equal.sym(Maybe<&2, Types.Pick>, RRounds.Slot.decided(bs, [name], k), None{}, hu),
                e
              )
            )
          )
        ),
        ef => ev
      )

# no vote of a node that alone decides a slot counts, while the slot is not
# decided: each such vote is sound, and decides
def Chain.quiet(
  t: Nat,
  +bs: List<&2, RRounds.Ballot>,
  +name: String,
  +k: Nat,
  +m: RRounds.Seen,
  +hu: {RRounds.Slot.decided(bs, [name], k) == None{}: Maybe<&2, Types.Pick>}
) -> {
  RRounds.Chain.seen(bs, name, t) == Some{m}: Maybe<&2, RRounds.Seen>
} -> {RRounds.Seen.votes(m) == []: List<&2, RRounds.Voted>}:
  match t:
    case 0n:
      e => (
        %Shared.Maybe.some_inj(RRounds.Seen, RRounds.Seen{0n, []}, m, e): {RRounds.Seen.votes(_) == []: List<&2, RRounds.Voted>}
        {==})
    case 1n++j:
      Lists.Maybe.by(
        RRounds.Seen,
        z => {
          RRounds.Chain.seen.next(
            z,
            RRounds.Ballots.at(bs, name, j)
          )
            == Some{m}: Maybe<&2, RRounds.Seen>
        } -> {RRounds.Seen.votes(m) == []: List<&2, RRounds.Voted>},
        RRounds.Chain.seen(bs, name, j),
        en => e => Empty.absurd(
          {RRounds.Seen.votes(m) == []: List<&2, RRounds.Voted>},
          Shared.Maybe.none_ne_some(RRounds.Seen, m, e)
        ),
        +m0 => +e0 => Lists.Maybe.by(
          Types.Cast,
          z => {
            RRounds.Chain.seen.next(Some{m0}, z) == Some{m}: Maybe<&2, RRounds.Seen>
          } -> {RRounds.Seen.votes(m) == []: List<&2, RRounds.Voted>},
          RRounds.Ballots.at(bs, name, j),
          en2 => e => Empty.absurd(
            {RRounds.Seen.votes(m) == []: List<&2, RRounds.Voted>},
            Shared.Maybe.none_ne_some(RRounds.Seen, m, e)
          ),
          +x => ea => e => (
            %Shared.Maybe.some_inj(RRounds.Seen, RRounds.Seen.step(m0, x), m, e): {RRounds.Seen.votes(_) == []: List<&2, RRounds.Voted>}
            Chain.quiet.step(m0, x, bs, name, k, j)(e0)(ea)(Chain.quiet(j, bs, name, k, m0, hu)(e0))(hu))
        )
      )

# no number is above the next number
def Nat.succ_not_le(a: Nat) -> {Nat.is_le(1n+a, a) == True{}: Bool} -> Empty:
  match a:
    case 0n:
      h => Shared.Bool.false_ne_true(h)
    case 1n+p:
      h => Nat.succ_not_le(p)(h)

# the number of a cast among the ballots that g names is at most the
# greatest number of a ballot
def Casts.of_turn(
  bs: List<&2, RRounds.Ballot>,
  +v: String,
  +t: Nat,
  +x: Types.Cast
) -> {
  List.contains(
    ~Types.Cast,
    ~Coded.Cast.is_eq,
    RRounds.Casts.of(bs, Types.Ref{v, t}),
    x
  )
    == True{}: Bool
} -> {Nat.is_le(t, Lists.List.peak(~RRounds.Ballot, ~RRounds.Ballot.turn, bs)) == True{}: Bool}:
  match bs:
    case Nil{}:
      h => Empty.absurd({Nat.is_le(t, 0n) == True{}: Bool}, Shared.Bool.false_ne_true(h))
    case Con{RRounds.Ballot{+w, +u, +y}, +rest}:
      Lists.Bool.by(
        b => {
          List.contains(
            ~Types.Cast,
            ~Coded.Cast.is_eq,
            Shared.Maybe.cons(
              Types.Cast,
              Shared.Maybe.when(Types.Cast, b, z => Some{y}),
              RRounds.Casts.of(rest, Types.Ref{v, t})
            ),
            x
          )
            == True{}: Bool
        } -> {
          Nat.is_le(
            t,
            Nat.max(u, Lists.List.peak(~RRounds.Ballot, ~RRounds.Ballot.turn, rest))
          )
            == True{}: Bool
        },
        Bool.and(String.eq(w, v), Nat.is_eq(u, t)),
        et => h => (
          %Shared.Nat.is_eq_sound(u, t)(Shared.Bool.and_true_right(String.eq(w, v), Nat.is_eq(u, t))(et)): {Nat.is_le(_, Nat.max(u, Lists.List.peak(~RRounds.Ballot, ~RRounds.Ballot.turn, rest))) == True{}: Bool}
          Lists.Nat.le_max_left(u, Lists.List.peak(~RRounds.Ballot, ~RRounds.Ballot.turn, rest))),
        ef => h => Shared.Nat.le_trans(
          t,
          Lists.List.peak(~RRounds.Ballot, ~RRounds.Ballot.turn, rest),
          Nat.max(u, Lists.List.peak(~RRounds.Ballot, ~RRounds.Ballot.turn, rest))
        )(
          Casts.of_turn(rest, v, t, x)(h)
        )(Lists.Nat.le_max_right(u, Lists.List.peak(~RRounds.Ballot, ~RRounds.Ballot.turn, rest)))
      )

# the ballots hold no ballot with a number above each of their numbers
def Ballots.at_past(
  +bs: List<&2, RRounds.Ballot>,
  +v: String,
  +t: Nat
) -> {
  Nat.is_le(RRounds.Turns.count(bs), t) == True{}: Bool
} -> {RRounds.Ballots.at(bs, v, t) == None{}: Maybe<&2, Types.Cast>}:
  h => Lists.Maybe.by(
    Types.Cast,
    z => {z == None{}: Maybe<&2, Types.Cast>},
    RRounds.Ballots.at(bs, v, t),
    en => {==},
    +x => ex => Empty.absurd(
      {Some{x} == None{}: Maybe<&2, Types.Cast>},
      Nat.succ_not_le(
        Lists.List.peak(~RRounds.Ballot, ~RRounds.Ballot.turn, bs)
      )(
        Shared.Nat.le_trans(
          1n+Lists.List.peak(~RRounds.Ballot, ~RRounds.Ballot.turn, bs),
          t,
          Lists.List.peak(~RRounds.Ballot, ~RRounds.Ballot.turn, bs)
        )(
          h
        )(Casts.of_turn(bs, v, t, x)(Casts.agreed_in(RRounds.Casts.of(bs, Types.Ref{v, t}), x)(ex)))
      )
    )
  )

# the ballots of the voter v are held among bs as far as m: each one before,
# and not the one of its number
def Reach.Held(bs: List<&2, RRounds.Ballot>, v: String, m: RRounds.Reach) -> Type:
  match m:
    case RRounds.Reach{t, sn}:
      {
        RRounds.Chain.seen(bs, v, t) == Some{sn}: Maybe<&2, RRounds.Seen>
      }
        & {RRounds.Ballots.at(bs, v, t) == None{}: Maybe<&2, Types.Cast>}

# Chain.reach_held, from the number t on
def Chain.reach_held.go(
  fuel: Nat,
  x: Maybe<&2, Types.Cast>,
  +bs: List<&2, RRounds.Ballot>,
  +v: String,
  +t: Nat,
  +m: RRounds.Seen
) -> {
  RRounds.Ballots.at(bs, v, t) == x: Maybe<&2, Types.Cast>
} -> {
  RRounds.Chain.seen(bs, v, t) == Some{m}: Maybe<&2, RRounds.Seen>
} -> {
  Nat.is_le(RRounds.Turns.count(bs), Nat.add(fuel, t)) == True{}: Bool
} -> Reach.Held(bs, v, RRounds.Chain.reach.go(fuel, bs, v, t, m, x)):
  match fuel x:
    case 0n None{}:
      ex => es => eb => (es, ex)
    case 0n Some{c}:
      ex => es => eb => (es, Ballots.at_past(bs, v, t)(eb))
    case 1n++f None{}:
      ex => es => eb => (es, ex)
    case 1n++f Some{+c}:
      +ex => +es => eb => Chain.reach_held.go(
        f,
        RRounds.Ballots.at(bs, v, 1n+t),
        bs,
        v,
        1n+t,
        RRounds.Seen.step(m, c)
      )({==})((
          %Equal.sym(Maybe<&2, RRounds.Seen>, RRounds.Chain.seen(bs, v, t), Some{m}, es): {RRounds.Chain.seen.next(_, RRounds.Ballots.at(bs, v, t)) == Some{RRounds.Seen.step(m, c)}: Maybe<&2, RRounds.Seen>}
          %Equal.sym(Maybe<&2, Types.Cast>, RRounds.Ballots.at(bs, v, t), Some{c}, ex): {RRounds.Chain.seen.next(Some{m}, _) == Some{RRounds.Seen.step(m, c)}: Maybe<&2, RRounds.Seen>}
          {==}))((
          %Equal.sym(Nat, Nat.add(f, 1n+t), 1n+Nat.add(f, t), Shared.Nat.add_succ(f, t)): {Nat.is_le(RRounds.Turns.count(bs), _) == True{}: Bool}
          eb))

# the ballots of a voter are held as far as Chain.reach says
def Chain.reach_held(
  +bs: List<&2, RRounds.Ballot>,
  +v: String
) -> Reach.Held(bs, v, RRounds.Chain.reach(bs, v)):
  Chain.reach_held.go(
    RRounds.Turns.count(bs),
    RRounds.Ballots.at(bs, v, 0n),
    bs,
    v,
    0n,
    RRounds.Seen{0n, []}
  )({==})({==})(Shared.Nat.le_add_first(RRounds.Turns.count(bs), 0n))

# Alone: the facts of the node
# ----------------------------

# the voter of the fact f ("" for an ask)
def Fact.voter(f: Types.Fact) -> String:
  match f:
    case Types.Fact.Ask{a}:
      ""
    case Types.Fact.Vote{v, st, x}:
      v

# the step of the fact f (broken for an ask)
def Fact.step(f: Types.Fact) -> Types.Step:
  match f:
    case Types.Fact.Ask{a}:
      Types.Step.Broken{}
    case Types.Fact.Vote{v, st, x}:
      st

# what the fact f casts (a pass for an ask)
def Fact.cast(f: Types.Fact) -> Types.Cast:
  match f:
    case Types.Fact.Ask{a}:
      Types.Cast.Pass{0n}
    case Types.Fact.Vote{v, st, x}:
      x

# a voter that a set does not name a liar has one cast for a step in it
def Slot.one_cast(
  +s: Facts.Facts(),
  +v: String,
  +st: Types.Step,
  +p: Types.Cast,
  +q: Types.Cast
) -> {
  List.contains(~String, ~String.eq, Facts.Facts.liars(s), v) == False{}: Bool
} -> {
  Facts.Facts.has(s, Types.Fact.Vote{v, st, p}) == True{}: Bool
} -> {Facts.Facts.has(s, Types.Fact.Vote{v, st, q}) == True{}: Bool} -> {p == q: Types.Cast}:
  hn => hp => hq => Coded.Cast.words_inj(
    p,
    q
  )(
    Facts.Words.is_eq_sound(
      Coded.Cast.words(p),
      Coded.Cast.words(q)
    )(
      Facts.Case.true_of(
        RFacts.Words.is_eq(Coded.Cast.words(p), Coded.Cast.words(q))
      )(
        ef => Lists.Bool.clash(
          Empty,
          List.contains(~String, ~String.eq, Facts.Facts.liars(s), v),
          hn,
          Facts.Facts.liars_in(
            s,
            Types.Fact.Vote{v, st, p},
            Types.Fact.Vote{v, st, q},
            v,
            Coded.Step.words(st),
            Coded.Cast.words(p),
            Coded.Cast.words(q)
          )(
            hp
          )(
            hq
          )(
            {==}
          )(
            {==}
          )(Facts.Case.not_of(RFacts.Words.is_eq(Coded.Cast.words(p), Coded.Cast.words(q)))(ef))
        )
      )
    )
  )

# a set that does not name a voter a liar, and gives no ballot of its for a
# number of a slot, holds none
def Casts.none(
  +s: Facts.Facts(),
  +name: String,
  +c: Ledgers.Line,
  +k: Nat,
  +t: Nat,
  +x: Types.Cast,
  +hl: {List.contains(~String, ~String.eq, Facts.Facts.liars(s), name) == False{}: Bool},
  hn: {RRounds.Ballots.at(Slot.ballots(s, c, k), name, t) == None{}: Maybe<&2, Types.Cast>}
) -> {
  List.contains(
    ~Types.Cast,
    ~Coded.Cast.is_eq,
    RRounds.Casts.of(Slot.ballots(s, c, k), Types.Ref{name, t}),
    x
  )
    == True{}: Bool
} -> Empty:
  +hin => Shared.Maybe.none_ne_some(
    Types.Cast,
    x,
    Equal.trans(
      Maybe<&2, Types.Cast>,
      None{},
      RRounds.Ballots.at(Slot.ballots(s, c, k), name, t),
      Some{x},
      Equal.sym(
        Maybe<&2, Types.Cast>,
        RRounds.Ballots.at(Slot.ballots(s, c, k), name, t),
        None{},
        hn
      ),
      Casts.agreed(
        RRounds.Casts.of(Slot.ballots(s, c, k), Types.Ref{name, t}),
        x,
        hin,
        List.holds_of(
          ~Types.Cast,
          ~Types.Cast,
          ~Coded.Cast.is_eq,
          ~Coded.Cast.is_eq,
          ~Coded.Cast.laws(),
          RRounds.Casts.of(Slot.ballots(s, c, k), Types.Ref{name, t}),
          x,
          +y => cy => (
            %Slot.one_cast(s, name, Types.Step.At{c, k, t}, x, y)(hl)(Casts.of_has(s, c, k, name, t, x)(hin))(Casts.of_has(s, c, k, name, t, y)(cy)): {Coded.Cast.is_eq(x, _) == True{}: Bool}
            Coded.Cast.is_eq_refl(x))
        )
      )
    )
  )

# Slot.cast_none, for a vote g of the node for the step
def Slot.cast_none.at(
  g: Types.Fact,
  +s: Facts.Facts(),
  +name: String,
  +c: Ledgers.Line,
  +k: Nat,
  +t: Nat,
  +hl: {List.contains(~String, ~String.eq, Facts.Facts.liars(s), name) == False{}: Bool},
  +hn: {RRounds.Ballots.at(Slot.ballots(s, c, k), name, t) == None{}: Maybe<&2, Types.Cast>}
) -> {
  List.contains(~Types.Fact, ~Coded.Fact.is_eq, Facts.Facts.list(s), g) == True{}: Bool
} -> {RFacts.Fact.is_cast(RFacts.Seat{name, Types.Step.At{c, k, t}}, g) == True{}: Bool} -> Empty:
  match g:
    case Types.Fact.Ask{a}:
      cin => h => Shared.Bool.false_ne_true(h)
    case Types.Fact.Vote{+v, +st2, +x}:
      cin => +h => Casts.none(
        s,
        name,
        c,
        k,
        t,
        x,
        hl,
        hn
      )(Casts.in_of(Facts.Facts.list(s), c, k, name, t, x)((
            %Texts.String.eq_sound(v, name)(Shared.Bool.and_true_left(String.eq(v, name), Coded.Step.is_eq(st2, Types.Step.At{c, k, t}))(h)): {List.contains(~Types.Fact, ~Coded.Fact.is_eq, Facts.Facts.list(s), Types.Fact.Vote{_, Types.Step.At{c, k, t}, x}) == True{}: Bool}
            %Coded.Step.is_eq_sound(st2, Types.Step.At{c, k, t})(Shared.Bool.and_true_right(String.eq(v, name), Coded.Step.is_eq(st2, Types.Step.At{c, k, t}))(h)): {List.contains(~Types.Fact, ~Coded.Fact.is_eq, Facts.Facts.list(s), Types.Fact.Vote{v, _, x}) == True{}: Bool}
            cin)))

# Slot.cast_none, with the vote of the node for the step
def Slot.cast_none.of(
  +s: Facts.Facts(),
  +name: String,
  +c: Ledgers.Line,
  +k: Nat,
  +t: Nat,
  +hl: {List.contains(~String, ~String.eq, Facts.Facts.liars(s), name) == False{}: Bool},
  +hn: {RRounds.Ballots.at(Slot.ballots(s, c, k), name, t) == None{}: Maybe<&2, Types.Cast>},
  +g: Types.Fact,
  w: {
    List.contains(~Types.Fact, ~Coded.Fact.is_eq, Facts.Facts.list(s), g) == True{}: Bool
  }
    & {RFacts.Fact.is_cast(RFacts.Seat{name, Types.Step.At{c, k, t}}, g) == True{}: Bool}
) -> Empty:
  (cin, h) = w
  Slot.cast_none.at(g, s, name, c, k, t, hl, hn)(cin)(h)

# a set that does not name a node a liar, and gives no ballot of its for a
# number of a slot, holds no vote of the node for the step
def Slot.cast_none(
  +s: Facts.Facts(),
  +name: String,
  +c: Ledgers.Line,
  +k: Nat,
  +t: Nat,
  +hl: {List.contains(~String, ~String.eq, Facts.Facts.liars(s), name) == False{}: Bool},
  +hn: {RRounds.Ballots.at(Slot.ballots(s, c, k), name, t) == None{}: Maybe<&2, Types.Cast>}
) -> {Facts.Facts.cast(s, name, Types.Step.At{c, k, t}) == False{}: Bool}:
  Facts.Case.false_of(
    Facts.Facts.cast(s, name, Types.Step.At{c, k, t})
  )(
    tr => Ex.by(
      Types.Fact,
      g => {
        List.contains(~Types.Fact, ~Coded.Fact.is_eq, Facts.Facts.list(s), g) == True{}: Bool
      }
        & {RFacts.Fact.is_cast(RFacts.Seat{name, Types.Step.At{c, k, t}}, g) == True{}: Bool},
      Empty,
      Lists.List.some_in(
        ~Types.Fact,
        ~RFacts.Seat,
        ~RFacts.Fact.is_cast,
        ~Coded.Fact.is_eq,
        ~Coded.Fact.laws(),
        Facts.Facts.list(s),
        RFacts.Seat{name, Types.Step.At{c, k, t}}
      )(tr),
      +g => w => Slot.cast_none.of(s, name, c, k, t, hl, hn, g, w)
    )
  )

# a set that holds a vote of a node for a step holds a vote of the node for
# the step
def Slot.cast_has(
  +s: Facts.Facts(),
  +name: String,
  +st: Types.Step,
  +x: Types.Cast
) -> {
  Facts.Facts.has(s, Types.Fact.Vote{name, st, x}) == True{}: Bool
} -> {Facts.Facts.cast(s, name, st) == True{}: Bool}:
  h => Lists.List.in_some(
    ~Types.Fact,
    ~RFacts.Seat,
    ~RFacts.Fact.is_cast,
    ~Coded.Fact.is_eq,
    ~Coded.Fact.laws(),
    Facts.Facts.list(s),
    RFacts.Seat{name, st},
    Types.Fact.Vote{name, st, x}
  )(
    Facts.Facts.has_in(s, Types.Fact.Vote{name, st, x})(h)
  )(
    Shared.Bool.and_both(
      String.eq(name, name),
      Coded.Step.is_eq(st, st)
    )(Texts.String.eq_refl(name))(Coded.Step.is_eq_refl(st))
  )

# no ballot that a set holds for a slot is the first vote of a node for a
# step of the slot
def Slot.added_new(
  -Q: Type,
  +s: Facts.Facts(),
  +name: String,
  +c: Ledgers.Line,
  +k: Nat,
  +t: Nat,
  +z: Types.Cast,
  +v: String,
  +u: Nat,
  +x: Types.Cast,
  +y: Types.Cast,
  hc: {Facts.Facts.cast(s, name, Types.Step.At{c, k, t}) == False{}: Bool},
  hin: {Facts.Facts.has(s, Types.Fact.Vote{v, Types.Step.At{c, k, u}, x}) == True{}: Bool},
  +e: {
    Types.Fact.Vote{
      v,
      Types.Step.At{c, k, u},
      y
    }
      == Types.Fact.Vote{name, Types.Step.At{c, k, t}, z}: Types.Fact
  }
) -> Q:
  Lists.Bool.clash(
    Q,
    Facts.Facts.cast(s, name, Types.Step.At{c, k, t}),
    hc,
    Slot.cast_has(s, name, Types.Step.At{c, k, t}, x)((
        %Equal.cong(Types.Fact, String, Fact.voter, Types.Fact.Vote{v, Types.Step.At{c, k, u}, y}, Types.Fact.Vote{name, Types.Step.At{c, k, t}, z}, e): {Facts.Facts.has(s, Types.Fact.Vote{_, Types.Step.At{c, k, t}, x}) == True{}: Bool}
        %Equal.cong(Types.Fact, Types.Step, Fact.step, Types.Fact.Vote{v, Types.Step.At{c, k, u}, y}, Types.Fact.Vote{name, Types.Step.At{c, k, t}, z}, e): {Facts.Facts.has(s, Types.Fact.Vote{v, _, x}) == True{}: Bool}
        hin))
  )

# Slot.added_grown, for a ballot that the set holds
def Slot.added_sure(
  +s: Facts.Facts(),
  +name: String,
  +c: Ledgers.Line,
  +k: Nat,
  +t: Nat,
  +z: Types.Cast,
  +hc: {Facts.Facts.cast(s, name, Types.Step.At{c, k, t}) == False{}: Bool},
  +v: String,
  +u: Nat,
  +x: Types.Cast,
  +hin: {Facts.Facts.has(s, Types.Fact.Vote{v, Types.Step.At{c, k, u}, x}) == True{}: Bool}
) -> {
  Ballot.sure(
    Grow{
      Slot.ballots(s, c, k),
      Slot.ballots(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, z}), c, k)
    },
    RRounds.Ballot{v, u, x}
  )
    == True{}: Bool
}:
  Lists.Bool.by(
    w => {
      Bool.or(
        Bool.not(w),
        RRounds.Cast.is(
          x,
          RRounds.Ballots.at(
            Slot.ballots(
              Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, z}),
              c,
              k
            ),
            v,
            u
          )
        )
      )
        == True{}: Bool
    },
    RRounds.Cast.is(x, RRounds.Ballots.at(Slot.ballots(s, c, k), v, u)),
    +et => Cast.is_of(
      x,
      RRounds.Ballots.at(
        Slot.ballots(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, z}), c, k),
        v,
        u
      ),
      Casts.agreed(
        RRounds.Casts.of(
          Slot.ballots(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, z}), c, k),
          Types.Ref{v, u}
        ),
        x,
        Casts.has_of(
          Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, z}),
          c,
          k,
          v,
          u,
          x
        )(
          Facts.Facts.add_keeps(
            s,
            Types.Fact.Vote{name, Types.Step.At{c, k, t}, z},
            Types.Fact.Vote{v, Types.Step.At{c, k, u}, x}
          )(hin)
        ),
        List.holds_of(
          ~Types.Cast,
          ~Types.Cast,
          ~Coded.Cast.is_eq,
          ~Coded.Cast.is_eq,
          ~Coded.Cast.laws(),
          RRounds.Casts.of(
            Slot.ballots(
              Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, z}),
              c,
              k
            ),
            Types.Ref{v, u}
          ),
          x,
          +y => cy => Facts.Facts.add_cases(
            {Coded.Cast.is_eq(x, y) == True{}: Bool},
            s,
            Types.Fact.Vote{name, Types.Step.At{c, k, t}, z},
            Types.Fact.Vote{v, Types.Step.At{c, k, u}, y},
            Casts.of_has(
              Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, z}),
              c,
              k,
              v,
              u,
              y
            )(cy),
            e => Slot.added_new(
              {Coded.Cast.is_eq(x, y) == True{}: Bool},
              s,
              name,
              c,
              k,
              t,
              z,
              v,
              u,
              x,
              y,
              hc,
              hin,
              e
            ),
            hy => Lists.List.holds_in(
              ~Types.Cast,
              ~Types.Cast,
              ~Coded.Cast.is_eq,
              ~Coded.Cast.is_eq,
              ~Coded.Cast.laws(),
              RRounds.Casts.of(Slot.ballots(s, c, k), Types.Ref{v, u}),
              x,
              y
            )(
              Shared.Bool.and_true_right(
                Bool.not(
                  List.is_empty(
                    &2,
                    Types.Cast,
                    RRounds.Casts.of(Slot.ballots(s, c, k), Types.Ref{v, u})
                  )
                ),
                Shared.List.holds(
                  ~Types.Cast,
                  ~Types.Cast,
                  ~Coded.Cast.is_eq,
                  RRounds.Casts.of(Slot.ballots(s, c, k), Types.Ref{v, u}),
                  x
                )
              )(
                Shared.List.agreed_holds(
                  ~Types.Cast,
                  ~Coded.Cast.is_eq,
                  ~Coded.Cast.laws(),
                  RRounds.Casts.of(Slot.ballots(s, c, k), Types.Ref{v, u}),
                  x
                )(Cast.is_some(x, RRounds.Ballots.at(Slot.ballots(s, c, k), v, u))(et))
              )
            )(Casts.has_of(s, c, k, v, u, y)(hy))
          )
        )
      )
    ),
    ef => {==}
  )

# the ballots of a slot grow with the first vote of a node for a step of it
def Slot.added_grown(
  +s: Facts.Facts(),
  +name: String,
  +c: Ledgers.Line,
  +k: Nat,
  +t: Nat,
  +z: Types.Cast,
  +hc: {Facts.Facts.cast(s, name, Types.Step.At{c, k, t}) == False{}: Bool}
) -> {
  Ballots.grown(
    Slot.ballots(s, c, k),
    Slot.ballots(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, z}), c, k)
  )
    == True{}: Bool
}:
  Slot.grown.go(
    Facts.Facts.list(s),
    Slot.ballots(s, c, k),
    Slot.ballots(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, z}), c, k),
    c,
    k,
    +v => +u => +x => hin => Slot.added_sure(
      s,
      name,
      c,
      k,
      t,
      z,
      hc,
      v,
      u,
      x,
      Facts.Facts.in_has(s, Types.Fact.Vote{v, Types.Step.At{c, k, u}, x})(hin)
    )
  )

# the first vote of a node for a step of a slot is its ballot of the number,
# among the ballots of the slot with it
def Slot.added_at(
  +s: Facts.Facts(),
  +name: String,
  +c: Ledgers.Line,
  +k: Nat,
  +t: Nat,
  +z: Types.Cast,
  +hc: {Facts.Facts.cast(s, name, Types.Step.At{c, k, t}) == False{}: Bool}
) -> {
  RRounds.Ballots.at(
    Slot.ballots(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, z}), c, k),
    name,
    t
  )
    == Some{z}: Maybe<&2, Types.Cast>
}:
  Casts.agreed(
    RRounds.Casts.of(
      Slot.ballots(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, z}), c, k),
      Types.Ref{name, t}
    ),
    z,
    Casts.has_of(
      Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, z}),
      c,
      k,
      name,
      t,
      z
    )(Facts.Facts.add_has(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, z})),
    List.holds_of(
      ~Types.Cast,
      ~Types.Cast,
      ~Coded.Cast.is_eq,
      ~Coded.Cast.is_eq,
      ~Coded.Cast.laws(),
      RRounds.Casts.of(
        Slot.ballots(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, z}), c, k),
        Types.Ref{name, t}
      ),
      z,
      +y => cy => Facts.Facts.add_cases(
        {Coded.Cast.is_eq(z, y) == True{}: Bool},
        s,
        Types.Fact.Vote{name, Types.Step.At{c, k, t}, z},
        Types.Fact.Vote{name, Types.Step.At{c, k, t}, y},
        Casts.of_has(
          Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, z}),
          c,
          k,
          name,
          t,
          y
        )(cy),
        e => (
          %Equal.cong(Types.Fact, Types.Cast, Fact.cast, Types.Fact.Vote{name, Types.Step.At{c, k, t}, y}, Types.Fact.Vote{name, Types.Step.At{c, k, t}, z}, e): {Coded.Cast.is_eq(_, y) == True{}: Bool}
          Coded.Cast.is_eq_refl(y)),
        hy => Lists.Bool.clash(
          {Coded.Cast.is_eq(z, y) == True{}: Bool},
          Facts.Facts.cast(s, name, Types.Step.At{c, k, t}),
          hc,
          Slot.cast_has(s, name, Types.Step.At{c, k, t}, y)(hy)
        )
      )
    )
  )

# Alone: the vote that decides
# ----------------------------

# Slot.voted_decides, with the round that decides
def Slot.voted_decides.fin(
  +bs: List<&2, RRounds.Ballot>,
  +name: String,
  +k: Nat,
  +r: Nat,
  +pk: Types.Pick,
  +w: Round.Won(bs, [name], k, r, pk)
) -> {RRounds.Slot.decided(bs, [name], k) == Some{pk}: Maybe<&2, Types.Pick>}:
  Ex.by(
    Types.Pick,
    p => {RRounds.Slot.decided(bs, [name], k) == Some{p}: Maybe<&2, Types.Pick>},
    {RRounds.Slot.decided(bs, [name], k) == Some{pk}: Maybe<&2, Types.Pick>},
    Slot.won_decided(bs, [name], k, r, pk)(w),
    +p => +hd => Slot.decided_grows.fin(bs, [name], k, r, pk, p, w, hd)
  )

# a slot that a node decides alone is decided for the pick of its ballot that
# casts a vote, where a vote of the round counts and it cast none that counts
# before
def Slot.voted_decides(
  +bs: List<&2, RRounds.Ballot>,
  +name: String,
  +k: Nat,
  +t: Nat,
  +fl: Nat,
  +r: Nat,
  +pk: Types.Pick,
  +b: List<&2, Types.Ref>,
  +es: {RRounds.Chain.seen(bs, name, t) == Some{RRounds.Seen{fl, []}}: Maybe<&2, RRounds.Seen>},
  ha: {RRounds.Ballots.at(bs, name, t) == Some{Types.Cast.Vote{r, pk, b}}: Maybe<&2, Types.Cast>},
  hr: {Nat.is_le(fl, r) == True{}: Bool}
) -> {RRounds.Slot.decided(bs, [name], k) == Some{pk}: Maybe<&2, Types.Pick>}:
  Slot.voted_decides.fin(
    bs,
    name,
    k,
    r,
    pk,
    Round.won_own(bs, name, k, r, t, fl, pk, b, Vote.of_counted(bs, name, r, t, pk, b, (
          %Equal.sym(Maybe<&2, RRounds.Seen>, RRounds.Chain.seen(bs, name, t), Some{RRounds.Seen{fl, []}}, es): {RRounds.Seen.takes(r, _) == True{}: Bool}
          hr), ha), es)
  )

# the first vote of a node for a step of a slot that it decides alone decides
# its pick, when a vote of its round counts and the node cast none that counts
# before
def Slot.added_decides(
  +s: Facts.Facts(),
  +name: String,
  +c: Ledgers.Line,
  +k: Nat,
  +pk: Types.Pick,
  +t: Nat,
  +fl: Nat,
  +r: Nat,
  +hc: {Facts.Facts.cast(s, name, Types.Step.At{c, k, t}) == False{}: Bool},
  es: {
    RRounds.Chain.seen(
      Slot.ballots(s, c, k),
      name,
      t
    )
      == Some{RRounds.Seen{fl, []}}: Maybe<&2, RRounds.Seen>
  },
  hr: {Nat.is_le(fl, r) == True{}: Bool}
) -> {
  Lines.Votes.decided(
    Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Vote{r, pk, []}}),
    c,
    k,
    [name]
  )
    == Some{pk}: Maybe<&2, Types.Pick>
}:
  Slot.voted_decides(
    Slot.ballots(
      Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Vote{r, pk, []}}),
      c,
      k
    ),
    name,
    k,
    t,
    fl,
    r,
    pk,
    [],
    Chain.seen_grows(
      Slot.ballots(s, c, k),
      Slot.ballots(
        Facts.Facts.add(
          s,
          Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Vote{r, pk, []}}
        ),
        c,
        k
      ),
      name,
      t,
      RRounds.Seen{fl, []},
      Slot.added_grown(s, name, c, k, t, Types.Cast.Vote{r, pk, []}, hc)
    )(es),
    Slot.added_at(s, name, c, k, t, Types.Cast.Vote{r, pk, []}, hc),
    hr
  )

# the chance of a node that decides alone and cast no vote that counts: a
# free one, with no basis
def Slot.chance_own(
  +bs: List<&2, RRounds.Ballot>,
  +name: String,
  +k: Nat,
  +t: Nat,
  +fl: Nat,
  er: {RRounds.Chain.reach(bs, name) == RRounds.Reach{t, RRounds.Seen{fl, []}}: RRounds.Reach},
  es: {RRounds.Chain.seen(bs, name, t) == Some{RRounds.Seen{fl, []}}: Maybe<&2, RRounds.Seen>}
) -> {
  RRounds.Slot.chance(
    bs,
    [name],
    k,
    name
  )
    == Some{
      RRounds.Chance{t, Nat.max(fl, RRounds.Rounds.top(bs)), [], RRounds.Force.Free{}}
    }: Maybe<&2, RRounds.Chance>
}:
  %Equal.sym(
    RRounds.Reach,
    RRounds.Chain.reach(bs, name),
    RRounds.Reach{t, RRounds.Seen{fl, []}},
    er
  ): {
    RRounds.Slot.chance.at(
      bs,
      [name],
      k,
      name,
      _
    )
      == Some{
        RRounds.Chance{t, Nat.max(fl, RRounds.Rounds.top(bs)), [], RRounds.Force.Free{}}
      }: Maybe<&2, RRounds.Chance>
  }
  %Equal.sym(
    String,
    RRounds.Turn.of([name], Nat.add(k, Nat.max(fl, RRounds.Rounds.top(bs)))),
    name,
    Turn.of_one(Nat.add(k, Nat.max(fl, RRounds.Rounds.top(bs))), name)
  ): {
    Shared.Maybe.when(
      RRounds.Chance,
      String.eq(_, name),
      u => RRounds.Slot.chance.of(
        RRounds.Lead{
          bs,
          Nat.max(fl, RRounds.Rounds.top(bs)),
          name,
          t,
          RRounds.Basis.make(bs, name, Nat.max(fl, RRounds.Rounds.top(bs)), [name]),
          RRounds.Rounds.minds(bs, [name], k, Nat.max(fl, RRounds.Rounds.top(bs)))
        },
        [name]
      )
    )
      == Some{
        RRounds.Chance{t, Nat.max(fl, RRounds.Rounds.top(bs)), [], RRounds.Force.Free{}}
      }: Maybe<&2, RRounds.Chance>
  }
  %Equal.sym(
    Bool,
    String.eq(name, name),
    True{},
    Texts.String.eq_refl(name)
  ): {
    Shared.Maybe.when(
      RRounds.Chance,
      _,
      u => RRounds.Slot.chance.of(
        RRounds.Lead{
          bs,
          Nat.max(fl, RRounds.Rounds.top(bs)),
          name,
          t,
          RRounds.Basis.make.at(
            name,
            Nat.max(fl, RRounds.Rounds.top(bs)),
            _,
            RRounds.Chain.reach(bs, name),
            []
          ),
          RRounds.Rounds.minds(bs, [name], k, Nat.max(fl, RRounds.Rounds.top(bs)))
        },
        [name]
      )
    )
      == Some{
        RRounds.Chance{t, Nat.max(fl, RRounds.Rounds.top(bs)), [], RRounds.Force.Free{}}
      }: Maybe<&2, RRounds.Chance>
  }
  %Equal.sym(
    RRounds.Promise,
    RRounds.Promise.read(
      RRounds.Lead{
        bs,
        Nat.max(fl, RRounds.Rounds.top(bs)),
        name,
        t,
        [],
        RRounds.Rounds.minds(bs, [name], k, Nat.max(fl, RRounds.Rounds.top(bs)))
      },
      name
    ),
    RRounds.Promise.Held{[]},
    Promise.read_own(
      bs,
      name,
      Nat.max(fl, RRounds.Rounds.top(bs)),
      t,
      fl,
      [],
      RRounds.Rounds.minds(bs, [name], k, Nat.max(fl, RRounds.Rounds.top(bs))),
      es
    )
  ): {
    Shared.Maybe.when(
      RRounds.Chance,
      Lists.Nat.most(1n, Shared.Nat.add_if(RRounds.Promise.is_held(_), 0n)),
      u => Some{
        RRounds.Chance{
          t,
          Nat.max(fl, RRounds.Rounds.top(bs)),
          [],
          RRounds.Force.join(
            RRounds.Promise.force(
              RRounds.Rounds.minds(bs, [name], k, Nat.max(fl, RRounds.Rounds.top(bs))),
              _
            ),
            RRounds.Force.Free{}
          )
        }
      }
    )
      == Some{
        RRounds.Chance{t, Nat.max(fl, RRounds.Rounds.top(bs)), [], RRounds.Force.Free{}}
      }: Maybe<&2, RRounds.Chance>
  }
  {==}

# a voter that cast no vote that counts is seen with its floor and no vote
def Seen.quiet_is(
  m: RRounds.Seen
) -> {
  RRounds.Seen.votes(m) == []: List<&2, RRounds.Voted>
} -> {m == RRounds.Seen{RRounds.Seen.floor(m), []}: RRounds.Seen}:
  match m:
    case RRounds.Seen{fl, vs}:
      e => (
        %e: {RRounds.Seen{fl, vs} == RRounds.Seen{fl, _}: RRounds.Seen}
        {==})

# Slot.alone, with the number of the next ballot of the node, and the lowest
# round that it may vote in
def Slot.alone.fin(
  +s: Facts.Facts(),
  +name: String,
  +c: Ledgers.Line,
  +k: Nat,
  +pk: Types.Pick,
  +t: Nat,
  +fl: Nat,
  er: {
    RRounds.Chain.reach(
      Slot.ballots(s, c, k),
      name
    )
      == RRounds.Reach{t, RRounds.Seen{fl, []}}: RRounds.Reach
  },
  +es: {
    RRounds.Chain.seen(
      Slot.ballots(s, c, k),
      name,
      t
    )
      == Some{RRounds.Seen{fl, []}}: Maybe<&2, RRounds.Seen>
  },
  +hc: {Facts.Facts.cast(s, name, Types.Step.At{c, k, t}) == False{}: Bool}
) -> Exists(
  Nat,
  t => Exists(Nat, r => Exists(List<&2, Types.Ref>, b => Slot.Alone(s, name, c, k, pk, t, r, b)))
):
  (
    t,
    (
      Nat.max(fl, RRounds.Rounds.top(Slot.ballots(s, c, k))),
      (
        [],
        (
          Slot.chance_own(Slot.ballots(s, c, k), name, k, t, fl, er, es),
          (
            hc,
            Slot.added_decides(
              s,
              name,
              c,
              k,
              pk,
              t,
              fl,
              Nat.max(fl, RRounds.Rounds.top(Slot.ballots(s, c, k))),
              hc,
              es,
              Lists.Nat.le_max_left(fl, RRounds.Rounds.top(Slot.ballots(s, c, k)))
            )
          )
        )
      )
    )
  )

# Slot.alone, with how far the ballots of the node are held
def Slot.alone.seen(
  +s: Facts.Facts(),
  +name: String,
  +c: Ledgers.Line,
  +k: Nat,
  +pk: Types.Pick,
  +t: Nat,
  +sn: RRounds.Seen,
  er: {RRounds.Chain.reach(Slot.ballots(s, c, k), name) == RRounds.Reach{t, sn}: RRounds.Reach},
  held: {
    RRounds.Chain.seen(Slot.ballots(s, c, k), name, t) == Some{sn}: Maybe<&2, RRounds.Seen>
  }
    & {RRounds.Ballots.at(Slot.ballots(s, c, k), name, t) == None{}: Maybe<&2, Types.Cast>},
  +hl: {List.contains(~String, ~String.eq, Facts.Facts.liars(s), name) == False{}: Bool},
  +hu: {RRounds.Slot.decided(Slot.ballots(s, c, k), [name], k) == None{}: Maybe<&2, Types.Pick>}
) -> Exists(
  Nat,
  t => Exists(Nat, r => Exists(List<&2, Types.Ref>, b => Slot.Alone(s, name, c, k, pk, t, r, b)))
):
  (+es, +hn) = held
  Slot.alone.fin(s, name, c, k, pk, t, RRounds.Seen.floor(sn), (
      %Seen.quiet_is(sn)(Chain.quiet(t, Slot.ballots(s, c, k), name, k, sn, hu)(es)): {RRounds.Chain.reach(Slot.ballots(s, c, k), name) == RRounds.Reach{t, _}: RRounds.Reach}
      er), (
      %Seen.quiet_is(sn)(Chain.quiet(t, Slot.ballots(s, c, k), name, k, sn, hu)(es)): {RRounds.Chain.seen(Slot.ballots(s, c, k), name, t) == Some{_}: Maybe<&2, RRounds.Seen>}
      es), Slot.cast_none(s, name, c, k, t, hl, hn))

# Slot.alone, once how far the ballots of the node are held (m) is known
def Slot.alone.at(
  m: RRounds.Reach,
  +s: Facts.Facts(),
  +name: String,
  +c: Ledgers.Line,
  +k: Nat,
  +pk: Types.Pick
) -> {
  RRounds.Chain.reach(Slot.ballots(s, c, k), name) == m: RRounds.Reach
} -> Reach.Held(
  Slot.ballots(s, c, k),
  name,
  m
) -> {
  List.contains(~String, ~String.eq, Facts.Facts.liars(s), name) == False{}: Bool
} -> {
  RRounds.Slot.decided(Slot.ballots(s, c, k), [name], k) == None{}: Maybe<&2, Types.Pick>
} -> Exists(
  Nat,
  t => Exists(Nat, r => Exists(List<&2, Types.Ref>, b => Slot.Alone(s, name, c, k, pk, t, r, b)))
):
  match m:
    case RRounds.Reach{+t, +sn}:
      er => held => +hl => +hu => Slot.alone.seen(s, name, c, k, pk, t, sn, er, held, hl, hu)

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
  hl => hu => Slot.alone.at(
    RRounds.Chain.reach(Slot.ballots(s, c, k), name),
    s,
    name,
    c,
    k,
    pk
  )({==})(Chain.reach_held(Slot.ballots(s, c, k), name))(hl)(hu)

# Passes
# ------
# A node passes once for the same ballots: after a pass it has promised the
# highest round of a ballot, and that round is alive, so it waits.

# a round that Rounds.mine gives is the turn of the node
def Rounds.mine_turn(
  n: Nat,
  +ds: List<&2, String>,
  +k: Nat,
  +name: String,
  +r: Nat,
  +to: Nat
) -> {
  RRounds.Rounds.mine(n, ds, k, name, r) == Some{to}: Maybe<&2, Nat>
} -> {String.eq(RRounds.Turn.of(ds, Nat.add(k, to)), name) == True{}: Bool}:
  match n:
    case 0n:
      e => Empty.absurd(
        {String.eq(RRounds.Turn.of(ds, Nat.add(k, to)), name) == True{}: Bool},
        Shared.Maybe.none_ne_some(Nat, to, e)
      )
    case 1n+m:
      Lists.Bool.by(
        z => {
          Shared.Bool.when(
            Maybe<&2, Nat>,
            z,
            u => Some{1n+r},
            u => RRounds.Rounds.mine(m, ds, k, name, 1n+r)
          )
            == Some{to}: Maybe<&2, Nat>
        } -> {String.eq(RRounds.Turn.of(ds, Nat.add(k, to)), name) == True{}: Bool},
        String.eq(RRounds.Turn.of(ds, Nat.add(k, 1n+r)), name),
        et => e => (
          %Shared.Maybe.some_inj(Nat, 1n+r, to, e): {String.eq(RRounds.Turn.of(ds, Nat.add(k, _)), name) == True{}: Bool}
          et),
        ef => e => Rounds.mine_turn(m, ds, k, name, 1n+r, to)(e)
      )

# a round that Rounds.mine gives is above the round that it starts after
def Rounds.mine_above(
  n: Nat,
  +ds: List<&2, String>,
  +k: Nat,
  +name: String,
  +r: Nat,
  +to: Nat
) -> {
  RRounds.Rounds.mine(n, ds, k, name, r) == Some{to}: Maybe<&2, Nat>
} -> {Nat.is_lt(r, to) == True{}: Bool}:
  match n:
    case 0n:
      e => Empty.absurd({Nat.is_lt(r, to) == True{}: Bool}, Shared.Maybe.none_ne_some(Nat, to, e))
    case 1n+m:
      Lists.Bool.by(
        z => {
          Shared.Bool.when(
            Maybe<&2, Nat>,
            z,
            u => Some{1n+r},
            u => RRounds.Rounds.mine(m, ds, k, name, 1n+r)
          )
            == Some{to}: Maybe<&2, Nat>
        } -> {Nat.is_lt(r, to) == True{}: Bool},
        String.eq(RRounds.Turn.of(ds, Nat.add(k, 1n+r)), name),
        et => e => (
          %Shared.Maybe.some_inj(Nat, 1n+r, to, e): {Nat.is_lt(r, _) == True{}: Bool}
          Shared.Nat.lt_succ(r)),
        ef => e => Shared.Nat.le_lt(
          r,
          1n+r,
          to
        )(
          Shared.Nat.lt_weak(r, 1n+r)(Shared.Nat.lt_succ(r))
        )(Rounds.mine_above(m, ds, k, name, 1n+r, to)(e))
      )

# a number that is not at most another is not below it
def Nat.nle_nlt(
  a: Nat,
  b: Nat
) -> {Nat.is_le(a, b) == False{}: Bool} -> {Nat.is_lt(a, b) == False{}: Bool}:
  +a = a
  +b = b
  ef => Lists.Bool.by(
    z => {Nat.is_lt(a, b) == z: Bool} -> {Nat.is_lt(a, b) == False{}: Bool},
    Nat.is_lt(a, b),
    et => e => Empty.absurd(
      {Nat.is_lt(a, b) == False{}: Bool},
      Shared.Bool.true_ne_false(
        Equal.trans(
          Bool,
          True{},
          Nat.is_le(a, b),
          False{},
          Equal.sym(Bool, Nat.is_le(a, b), True{}, Shared.Nat.lt_weak(a, b)(et)),
          ef
        )
      )
    ),
    ef2 => e => e
  )({==})

# after a pass to a round, a voter may vote in no round below it
def Seen.passed_floor(
  m: RRounds.Seen,
  +to: Nat
) -> {
  Nat.is_lt(RRounds.Seen.floor(RRounds.Seen.step(m, Types.Cast.Pass{to})), to) == False{}: Bool
}:
  match m:
    case RRounds.Seen{+fl, +vs}:
      Lists.Bool.by(
        z => {
          Nat.is_lt(
            RRounds.Seen.floor(
              Bool.pick(RRounds.Seen, z, RRounds.Seen{to, vs}, RRounds.Seen{fl, vs})
            ),
            to
          )
            == False{}: Bool
        },
        Nat.is_le(fl, to),
        et => Shared.Nat.lt_irrefl(to),
        ef => Nat.nle_nlt(fl, to)(ef)
      )

# a voter that promised the highest round casts no pass while it is alive
def Slot.pass.at_waits(
  +top: Nat,
  alive: Bool,
  own: Unit -> Maybe<&2, Nat>,
  t: Nat,
  m: RRounds.Seen
) -> {
  alive == True{}: Bool
} -> {
  Nat.is_lt(RRounds.Seen.floor(m), top) == False{}: Bool
} -> {
  RRounds.Slot.pass.at(top, alive, own, RRounds.Reach{t, m}) == None{}: Maybe<&2, RRounds.Draft>
}:
  match m:
    case RRounds.Seen{floor, votes}:
      ea => x => (
        %Equal.sym(Bool, alive, True{}, ea): {RRounds.Slot.pass.of(t, floor, top, _, own) == None{}: Maybe<&2, RRounds.Draft>}
        %Equal.sym(Bool, Nat.is_lt(floor, top), False{}, x): {RRounds.Slot.pass.to(t, Shared.Maybe.when(Nat, _, u => Some{top})) == None{}: Maybe<&2, RRounds.Draft>}
        {==})

# the node h, that came to the round r, came to it with one more ballot
def Rounds.heard_grows(
  b: RRounds.Ballot,
  bs: List<&2, RRounds.Ballot>,
  +h: String,
  +r: Nat
) -> {
  RRounds.Rounds.heard(bs, h, r) == True{}: Bool
} -> {RRounds.Rounds.heard(b <> bs, h, r) == True{}: Bool}:
  +b = b
  +bs = bs
  e => Lists.Bool.by(
    z => {List.any.if(u => RRounds.Rounds.heard(bs, h, r), z) == True{}: Bool},
    RRounds.Ballot.reaches(RRounds.Call{h, r}, b),
    et => {==},
    ef => e
  )

# a round that is alive stays alive with one more ballot
def Round.alive_grows(
  b: RRounds.Ballot,
  bs: List<&2, RRounds.Ballot>,
  ds: List<&2, String>,
  k: Nat,
  +name: String,
  +top: Nat
) -> {
  RRounds.Round.alive(bs, ds, k, name, top) == True{}: Bool
} -> {RRounds.Round.alive(b <> bs, ds, k, name, top) == True{}: Bool}:
  +b = b
  +bs = bs
  +ds = ds
  +k = k
  Lists.Bool.by(
    z => {
      Shared.Bool.when(
        Bool,
        z,
        u => True{},
        u => RRounds.Rounds.heard(bs, RRounds.Turn.of(ds, Nat.add(k, top)), top)
      )
        == True{}: Bool
    } -> {
      Shared.Bool.when(
        Bool,
        z,
        u => True{},
        u => RRounds.Rounds.heard(b <> bs, RRounds.Turn.of(ds, Nat.add(k, top)), top)
      )
        == True{}: Bool
    },
    String.eq(RRounds.Turn.of(ds, Nat.add(k, top)), name),
    et => e => {==},
    ef => e => Rounds.heard_grows(b, bs, RRounds.Turn.of(ds, Nat.add(k, top)), top)(e)
  )

# the greater of a and b is a, when b is at most a
def Nat.max_above(a: Nat, b: Nat) -> {Nat.is_le(b, a) == True{}: Bool} -> {Nat.max(a, b) == a: Nat}:
  match a b:
    case 0n 0n:
      h => {==}
    case 0n 1n+q:
      h => Empty.absurd({Nat.max(0n, 1n+q) == 0n: Nat}, Shared.Bool.false_ne_true(h))
    case 1n+p 0n:
      h => {==}
    case 1n+p 1n+q:
      h => Equal.cong(Nat, Nat, n => 1n+n, Nat.max(p, q), p, Nat.max_above(p, q)(h))

# the greater of a and a is a
def Nat.max_same(+a: Nat) -> {Nat.max(a, a) == a: Nat}:
  Nat.max_above(a, a)(Shared.Nat.le_refl(a))

# what the draft d casts
def Draft.cast(d: RRounds.Draft) -> Types.Cast:
  match d:
    case RRounds.Draft{t, x}:
      x

# the next pass of a node, read from the ballots bs, where its ballots are
# held as far as m
def Pass.next(
  +bs: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +name: String,
  m: RRounds.Reach
) -> Maybe<&2, RRounds.Draft>:
  RRounds.Slot.pass.at(
    RRounds.Rounds.top(bs),
    RRounds.Round.alive(bs, ds, k, name, RRounds.Rounds.top(bs)),
    u => RRounds.Rounds.mine(List.length(&2, String, ds), ds, k, name, RRounds.Rounds.top(bs)),
    m
  )

# no pass follows a pass to the highest round of a ballot, which is alive
def Pass.next_top(
  +bs: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +name: String,
  +t: Nat,
  +m: RRounds.Seen
) -> {
  RRounds.Round.alive(bs, ds, k, name, RRounds.Rounds.top(bs)) == True{}: Bool
} -> {
  Pass.next(
    (RRounds.Ballot{name, t, Types.Cast.Pass{RRounds.Rounds.top(bs)}} <> bs),
    ds,
    k,
    name,
    RRounds.Reach{1n+t, RRounds.Seen.step(m, Types.Cast.Pass{RRounds.Rounds.top(bs)})}
  )
    == None{}: Maybe<&2, RRounds.Draft>
}:
  ea => Lists.Equal.to(
    Nat,
    top2 => {
      RRounds.Slot.pass.at(
        top2,
        RRounds.Round.alive(
          (RRounds.Ballot{name, t, Types.Cast.Pass{RRounds.Rounds.top(bs)}} <> bs),
          ds,
          k,
          name,
          top2
        ),
        u => RRounds.Rounds.mine(List.length(&2, String, ds), ds, k, name, top2),
        RRounds.Reach{1n+t, RRounds.Seen.step(m, Types.Cast.Pass{RRounds.Rounds.top(bs)})}
      )
        == None{}: Maybe<&2, RRounds.Draft>
    },
    RRounds.Rounds.top(bs),
    Nat.max(RRounds.Rounds.top(bs), RRounds.Rounds.top(bs)),
    Equal.sym(
      Nat,
      Nat.max(RRounds.Rounds.top(bs), RRounds.Rounds.top(bs)),
      RRounds.Rounds.top(bs),
      Nat.max_same(RRounds.Rounds.top(bs))
    ),
    Slot.pass.at_waits(
      RRounds.Rounds.top(bs),
      RRounds.Round.alive(
        (RRounds.Ballot{name, t, Types.Cast.Pass{RRounds.Rounds.top(bs)}} <> bs),
        ds,
        k,
        name,
        RRounds.Rounds.top(bs)
      ),
      u => RRounds.Rounds.mine(List.length(&2, String, ds), ds, k, name, RRounds.Rounds.top(bs)),
      1n+t,
      RRounds.Seen.step(m, Types.Cast.Pass{RRounds.Rounds.top(bs)})
    )(
      Round.alive_grows(
        RRounds.Ballot{name, t, Types.Cast.Pass{RRounds.Rounds.top(bs)}},
        bs,
        ds,
        k,
        name,
        RRounds.Rounds.top(bs)
      )(ea)
    )(Seen.passed_floor(m, RRounds.Rounds.top(bs)))
  )

# no pass follows a pass of a node to its own next round
def Pass.next_own(
  +bs: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +name: String,
  +t: Nat,
  +m: RRounds.Seen,
  +to: Nat
) -> {
  RRounds.Rounds.mine(
    List.length(&2, String, ds),
    ds,
    k,
    name,
    RRounds.Rounds.top(bs)
  )
    == Some{to}: Maybe<&2, Nat>
} -> {
  Pass.next(
    (RRounds.Ballot{name, t, Types.Cast.Pass{to}} <> bs),
    ds,
    k,
    name,
    RRounds.Reach{1n+t, RRounds.Seen.step(m, Types.Cast.Pass{to})}
  )
    == None{}: Maybe<&2, RRounds.Draft>
}:
  +em => Lists.Equal.to(
    Nat,
    top2 => {
      RRounds.Slot.pass.at(
        top2,
        RRounds.Round.alive(
          (RRounds.Ballot{name, t, Types.Cast.Pass{to}} <> bs),
          ds,
          k,
          name,
          top2
        ),
        u => RRounds.Rounds.mine(List.length(&2, String, ds), ds, k, name, top2),
        RRounds.Reach{1n+t, RRounds.Seen.step(m, Types.Cast.Pass{to})}
      )
        == None{}: Maybe<&2, RRounds.Draft>
    },
    to,
    Nat.max(to, RRounds.Rounds.top(bs)),
    Equal.sym(
      Nat,
      Nat.max(to, RRounds.Rounds.top(bs)),
      to,
      Nat.max_above(
        to,
        RRounds.Rounds.top(bs)
      )(
        Shared.Nat.lt_weak(
          RRounds.Rounds.top(bs),
          to
        )(
          Rounds.mine_above(
            List.length(&2, String, ds),
            ds,
            k,
            name,
            RRounds.Rounds.top(bs),
            to
          )(em)
        )
      )
    ),
    Slot.pass.at_waits(
      to,
      RRounds.Round.alive((RRounds.Ballot{name, t, Types.Cast.Pass{to}} <> bs), ds, k, name, to),
      u => RRounds.Rounds.mine(List.length(&2, String, ds), ds, k, name, to),
      1n+t,
      RRounds.Seen.step(m, Types.Cast.Pass{to})
    )(
      %Equal.sym(Bool, String.eq(RRounds.Turn.of(ds, Nat.add(k, to)), name), True{}, Rounds.mine_turn(List.length(&2, String, ds), ds, k, name, RRounds.Rounds.top(bs), to)(em)): {Shared.Bool.when(Bool, _, u => True{}, u => RRounds.Rounds.heard((RRounds.Ballot{name, t, Types.Cast.Pass{to}} <> bs), RRounds.Turn.of(ds, Nat.add(k, to)), to)) == True{}: Bool}
      {==})(Seen.passed_floor(m, to))
  )

# the next pass of a node after the cast y, as its ballot of the number t,
# where its ballots were held as far as that number and it was seen as m
def Pass.after(
  +bs: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +name: String,
  +t: Nat,
  +m: RRounds.Seen,
  +y: Types.Cast
) -> Maybe<&2, RRounds.Draft>:
  Pass.next(
    RRounds.Ballot{name, t, y} <> bs,
    ds,
    k,
    name,
    RRounds.Reach{1n+t, RRounds.Seen.step(m, y)}
  )

# what the draft d casts is x, when d is a draft of x
def Draft.cast_of(
  -t: Nat,
  -t2: Nat,
  -y: Types.Cast,
  -x: Types.Cast,
  e: {Some{RRounds.Draft{t, y}} == Some{RRounds.Draft{t2, x}}: Maybe<&2, RRounds.Draft>}
) -> {y == x: Types.Cast}:
  Equal.cong(
    RRounds.Draft,
    Types.Cast,
    Draft.cast,
    RRounds.Draft{t, y},
    RRounds.Draft{t2, x},
    Shared.Maybe.some_inj(RRounds.Draft, RRounds.Draft{t, y}, RRounds.Draft{t2, x}, e)
  )

# no pass follows the pass of a node, where its ballots are held as far as
# the pass
def Pass.next_once(
  +bs: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +name: String,
  +t: Nat,
  +x: Types.Cast,
  m: RRounds.Seen
) -> {
  Pass.next(
    bs,
    ds,
    k,
    name,
    RRounds.Reach{t, m}
  )
    == Some{RRounds.Draft{t, x}}: Maybe<&2, RRounds.Draft>
} -> {Pass.after(bs, ds, k, name, t, m, x) == None{}: Maybe<&2, RRounds.Draft>}:
  match m:
    case RRounds.Seen{+fl, +vs}:
      Lists.Bool.by(
        z => {
          RRounds.Slot.pass.of(
            t,
            fl,
            RRounds.Rounds.top(bs),
            z,
            u => RRounds.Rounds.mine(
              List.length(&2, String, ds),
              ds,
              k,
              name,
              RRounds.Rounds.top(bs)
            )
          )
            == Some{RRounds.Draft{t, x}}: Maybe<&2, RRounds.Draft>
        } -> {
          Pass.after(
            bs,
            ds,
            k,
            name,
            t,
            RRounds.Seen{fl, vs},
            x
          )
            == None{}: Maybe<&2, RRounds.Draft>
        },
        RRounds.Round.alive(bs, ds, k, name, RRounds.Rounds.top(bs)),
        +et => Lists.Bool.by(
          z => {
            RRounds.Slot.pass.to(
              t,
              Shared.Maybe.when(Nat, z, u => Some{RRounds.Rounds.top(bs)})
            )
              == Some{RRounds.Draft{t, x}}: Maybe<&2, RRounds.Draft>
          } -> {
            Pass.after(
              bs,
              ds,
              k,
              name,
              t,
              RRounds.Seen{fl, vs},
              x
            )
              == None{}: Maybe<&2, RRounds.Draft>
          },
          Nat.is_lt(fl, RRounds.Rounds.top(bs)),
          el => e => Lists.Equal.to(
            Types.Cast,
            y => {
              Pass.after(
                bs,
                ds,
                k,
                name,
                t,
                RRounds.Seen{fl, vs},
                y
              )
                == None{}: Maybe<&2, RRounds.Draft>
            },
            Types.Cast.Pass{RRounds.Rounds.top(bs)},
            x,
            Draft.cast_of(t, t, Types.Cast.Pass{RRounds.Rounds.top(bs)}, x, e),
            Pass.next_top(bs, ds, k, name, t, RRounds.Seen{fl, vs})(et)
          ),
          el => e => Empty.absurd(
            {
              Pass.after(
                bs,
                ds,
                k,
                name,
                t,
                RRounds.Seen{fl, vs},
                x
              )
                == None{}: Maybe<&2, RRounds.Draft>
            },
            Shared.Maybe.none_ne_some(RRounds.Draft, RRounds.Draft{t, x}, e)
          )
        ),
        ef => Lists.Maybe.by(
          Nat,
          z => {
            RRounds.Slot.pass.to(t, z) == Some{RRounds.Draft{t, x}}: Maybe<&2, RRounds.Draft>
          } -> {
            Pass.after(
              bs,
              ds,
              k,
              name,
              t,
              RRounds.Seen{fl, vs},
              x
            )
              == None{}: Maybe<&2, RRounds.Draft>
          },
          RRounds.Rounds.mine(List.length(&2, String, ds), ds, k, name, RRounds.Rounds.top(bs)),
          en => e => Empty.absurd(
            {
              Pass.after(
                bs,
                ds,
                k,
                name,
                t,
                RRounds.Seen{fl, vs},
                x
              )
                == None{}: Maybe<&2, RRounds.Draft>
            },
            Shared.Maybe.none_ne_some(RRounds.Draft, RRounds.Draft{t, x}, e)
          ),
          +to => +em => e => Lists.Equal.to(
            Types.Cast,
            y => {
              Pass.after(
                bs,
                ds,
                k,
                name,
                t,
                RRounds.Seen{fl, vs},
                y
              )
                == None{}: Maybe<&2, RRounds.Draft>
            },
            Types.Cast.Pass{to},
            x,
            Draft.cast_of(t, t, Types.Cast.Pass{to}, x, e),
            Pass.next_own(bs, ds, k, name, t, RRounds.Seen{fl, vs}, to)(em)
          )
        )
      )

# a node passes once for the same ballots: after its pass x, read as its
# next ballot, it casts no other pass, whatever the ballots are
def Slot.pass_once(
  +bs: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +name: String,
  +t: Nat,
  +x: Types.Cast,
  +m: RRounds.Seen
) -> {
  RRounds.Slot.pass(bs, ds, k, name) == Some{RRounds.Draft{t, x}}: Maybe<&2, RRounds.Draft>
} -> {
  RRounds.Chain.reach(bs, name) == RRounds.Reach{t, m}: RRounds.Reach
} -> {
  RRounds.Chain.reach(
    RRounds.Ballot{name, t, x} <> bs,
    name
  )
    == RRounds.Reach{1n+t, RRounds.Seen.step(m, x)}: RRounds.Reach
} -> {
  RRounds.Slot.pass(
    RRounds.Ballot{name, t, x} <> bs,
    ds,
    k,
    name
  )
    == None{}: Maybe<&2, RRounds.Draft>
}:
  ep => er => er2 => Lists.Equal.to(
    RRounds.Reach,
    z => {
      Pass.next(
        RRounds.Ballot{name, t, x} <> bs,
        ds,
        k,
        name,
        z
      )
        == None{}: Maybe<&2, RRounds.Draft>
    },
    RRounds.Reach{1n+t, RRounds.Seen.step(m, x)},
    RRounds.Chain.reach(RRounds.Ballot{name, t, x} <> bs, name),
    Equal.sym(
      RRounds.Reach,
      RRounds.Chain.reach(RRounds.Ballot{name, t, x} <> bs, name),
      RRounds.Reach{1n+t, RRounds.Seen.step(m, x)},
      er2
    ),
    Pass.next_once(
      bs,
      ds,
      k,
      name,
      t,
      x,
      m
    )(
      Lists.Equal.to(
        RRounds.Reach,
        z => {Pass.next(bs, ds, k, name, z) == Some{RRounds.Draft{t, x}}: Maybe<&2, RRounds.Draft>},
        RRounds.Chain.reach(bs, name),
        RRounds.Reach{t, m},
        er,
        ep
      )
    )
  )
