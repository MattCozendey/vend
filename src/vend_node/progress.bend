import Base
import ../shared/shared/ledger.bend as Ledgers
import ../shared/shared/shared/shared/shared.bend as Shared
import ../shared/shared/shared/text.bend as Texts
import ./codes.bend as Coded
import ./facts.bend as Facts
import ./lines.bend as Lines
import ./rounds.bend as Laws
import ./run/rounds.bend as RRounds
import ./run/work.bend as RWorks
import ./safety.bend as Safeties
import ./shared/lists.bend as Lists
import ./types.bend as Types
import ./work.bend as Works

# Progress of the rounds
# ----------------------
# What a node casts next for a slot, read from the ballots that it holds
# (run/rounds.bend), and what its ballot changes: a node passes once, waits
# after its vote, votes as a sound lead that it may follow, and calls its own
# round when the node whose turn the highest round is cast no ballot there.
# The laws are said of a list of ballots, and of the facts of a node with one
# more ballot (Facts.add), which is what a work does (run/work.bend).

# Numbers
# -------

# a number that is not at most another is above it
def Nat.nle_above(
  a: Nat,
  b: Nat
) -> {Nat.is_le(a, b) == False{}: Bool} -> {Nat.is_le(1n+b, a) == True{}: Bool}:
  match a b:
    case 0n 0n:
      h => Equal.sym(Bool, True{}, False{}, h)
    case 0n 1n+q:
      h => Equal.sym(Bool, True{}, False{}, h)
    case 1n+p 0n:
      h => Shared.Nat.le_zero(p)
    case 1n+p 1n+q:
      h => Nat.nle_above(p, q)(h)

# two numbers, each at most the other, are one
def Nat.le_same(
  a: Nat,
  b: Nat
) -> {Nat.is_le(a, b) == True{}: Bool} -> {Nat.is_le(b, a) == True{}: Bool} -> {a == b: Nat}:
  match a b:
    case 0n 0n:
      h => g => {==}
    case 0n 1n+q:
      h => g => Empty.absurd({0n == 1n+q: Nat}, Shared.Bool.false_ne_true(g))
    case 1n+p 0n:
      h => g => Empty.absurd({1n+p == 0n: Nat}, Shared.Bool.false_ne_true(h))
    case 1n+p 1n+q:
      h => g => Equal.cong(Nat, Nat, n => 1n+n, p, q, Nat.le_same(p, q)(h)(g))

# the greater of a and b is b, when a is at most b
def Nat.max_under(a: Nat, b: Nat) -> {Nat.is_le(a, b) == True{}: Bool} -> {Nat.max(a, b) == b: Nat}:
  match a b:
    case 0n 0n:
      h => {==}
    case 0n 1n+q:
      h => {==}
    case 1n+p 0n:
      h => Empty.absurd({Nat.max(1n+p, 0n) == 0n: Nat}, Shared.Bool.false_ne_true(h))
    case 1n+p 1n+q:
      h => Equal.cong(Nat, Nat, n => 1n+n, Nat.max(p, q), q, Nat.max_under(p, q)(h))

# Chains
# ------

# what a voter is seen as after a ballot is known only when the voter was
# known before it, and the ballot is held
def Chain.seen.next_by(
  -Q: Type,
  m: Maybe<&2, RRounds.Seen>,
  x: Maybe<&2, Types.Cast>,
  -s: RRounds.Seen
) -> {
  RRounds.Chain.seen.next(m, x) == Some{s}: Maybe<&2, RRounds.Seen>
} -> (
  @m0: RRounds.Seen -> @c: Types.Cast -> {
    m == Some{m0}: Maybe<&2, RRounds.Seen>
  } -> {x == Some{c}: Maybe<&2, Types.Cast>} -> {RRounds.Seen.step(m0, c) == s: RRounds.Seen} -> Q
) -> Q:
  match m x:
    case None{} None{}:
      e => k => Empty.absurd(Q, Shared.Maybe.none_ne_some(RRounds.Seen, s, e))
    case None{} Some{c}:
      e => k => Empty.absurd(Q, Shared.Maybe.none_ne_some(RRounds.Seen, s, e))
    case Some{m0} None{}:
      e => k => Empty.absurd(Q, Shared.Maybe.none_ne_some(RRounds.Seen, s, e))
    case Some{+m0} Some{+c}:
      e => k => k(
        m0
      )(c)({==})({==})(Shared.Maybe.some_inj(RRounds.Seen, RRounds.Seen.step(m0, c), s, e))

# a voter that is known before its ballot of a number cast each ballot below
# that number
def Chain.seen_whole(
  b: Nat,
  +a: Nat,
  +bs: List<&2, RRounds.Ballot>,
  +v: String,
  -m: RRounds.Seen
) -> {
  RRounds.Chain.seen(bs, v, b) == Some{m}: Maybe<&2, RRounds.Seen>
} -> {
  Nat.is_le(1n+a, b) == True{}: Bool
} -> {RRounds.Ballots.at(bs, v, a) == None{}: Maybe<&2, Types.Cast>} -> Empty:
  match b:
    case 0n:
      es => hl => hn => Shared.Bool.false_ne_true(hl)
    case 1n++j:
      es => +hl => +hn => Chain.seen.next_by(
        Empty,
        RRounds.Chain.seen(bs, v, j),
        RRounds.Ballots.at(bs, v, j),
        m
      )(
        es
      )(
        m0 => +c => es0 => +ex => e2 => Lists.Bool.by(
          z => {Nat.is_le(1n+a, j) == z: Bool} -> Empty,
          Nat.is_le(1n+a, j),
          et => e => Chain.seen_whole(j, a, bs, v, m0)(es0)(et)(hn),
          ef => e => Shared.Maybe.none_ne_some(
            Types.Cast,
            c,
            Equal.trans(Maybe<&2, Types.Cast>, None{}, RRounds.Ballots.at(bs, v, j), Some{c}, (
                %Shared.Nat.le_nlt_eq(a, j)(hl)(ef): {None{} == RRounds.Ballots.at(bs, v, _): Maybe<&2, Types.Cast>}
                Equal.sym(Maybe<&2, Types.Cast>, RRounds.Ballots.at(bs, v, a), None{}, hn)), ex)
          )
        )({==})
      )

# the lowest round that a voter seen as m may vote in is above fl, when the
# mark of fl is true of it
def Seen.marks_floor(
  +fl: Nat,
  m: RRounds.Seen
) -> {
  Safeties.Seen.marks(
    Safeties.Mark.Floor{fl},
    Some{m}
  )
    == Nat.is_le(fl, RRounds.Seen.floor(m)): Bool
}:
  match m:
    case RRounds.Seen{f, vs}:
      {==}

# the lowest round that a voter may vote in does not go down along its
# ballots: it is no lower where its ballots end than at a number before
def Chain.floor_last(
  +bs: List<&2, RRounds.Ballot>,
  +v: String,
  +a: Nat,
  +ma: RRounds.Seen,
  +t: Nat,
  +m: RRounds.Seen
) -> {
  RRounds.Chain.seen(bs, v, a) == Some{ma}: Maybe<&2, RRounds.Seen>
} -> {
  RRounds.Chain.seen(bs, v, t) == Some{m}: Maybe<&2, RRounds.Seen>
} -> {
  RRounds.Ballots.at(bs, v, t) == None{}: Maybe<&2, Types.Cast>
} -> {Nat.is_le(RRounds.Seen.floor(ma), RRounds.Seen.floor(m)) == True{}: Bool}:
  +ea => +et => hn => Lists.Bool.by(
    z => {
      Nat.is_le(a, t) == z: Bool
    } -> {Nat.is_le(RRounds.Seen.floor(ma), RRounds.Seen.floor(m)) == True{}: Bool},
    Nat.is_le(a, t),
    hle => e => (
      %Seen.marks_floor(RRounds.Seen.floor(ma), m): {_ == True{}: Bool}
      %et: {Safeties.Seen.marks(Safeties.Mark.Floor{RRounds.Seen.floor(ma)}, _) == True{}: Bool}
      Safeties.Chain.marks_on(t, a, bs, v, Safeties.Mark.Floor{RRounds.Seen.floor(ma)})(hle)((
        %Equal.sym(Maybe<&2, RRounds.Seen>, RRounds.Chain.seen(bs, v, a), Some{ma}, ea): {Safeties.Seen.marks(Safeties.Mark.Floor{RRounds.Seen.floor(ma)}, _) == True{}: Bool}
        %Equal.sym(Bool, Safeties.Seen.marks(Safeties.Mark.Floor{RRounds.Seen.floor(ma)}, Some{ma}), Nat.is_le(RRounds.Seen.floor(ma), RRounds.Seen.floor(ma)), Seen.marks_floor(RRounds.Seen.floor(ma), ma)): {_ == True{}: Bool}
        Shared.Nat.le_refl(RRounds.Seen.floor(ma))))),
    hnl => e => Empty.absurd(
      {Nat.is_le(RRounds.Seen.floor(ma), RRounds.Seen.floor(m)) == True{}: Bool},
      Chain.seen_whole(a, t, bs, v, ma)(ea)(Nat.nle_above(a, t)(hnl))(hn)
    )
  )({==})

# Ballots that are held
# ---------------------

# the greater of a and b is at most m, when both are
def Nat.max_le(
  +a: Nat,
  +b: Nat,
  +m: Nat
) -> {
  Nat.is_le(a, m) == True{}: Bool
} -> {Nat.is_le(b, m) == True{}: Bool} -> {Nat.is_le(Nat.max(a, b), m) == True{}: Bool}:
  ha => hb => Lists.Bool.by(
    z => {Nat.is_le(a, b) == z: Bool} -> {Nat.is_le(Nat.max(a, b), m) == True{}: Bool},
    Nat.is_le(a, b),
    et => e => (
      %Equal.sym(Nat, Nat.max(a, b), b, Nat.max_under(a, b)(et)): {Nat.is_le(_, m) == True{}: Bool}
      hb),
    ef => e => (
      %Equal.sym(Nat, Nat.max(a, b), a, Laws.Nat.max_above(a, b)(Shared.Nat.nle_le(a, b)(ef))): {Nat.is_le(_, m) == True{}: Bool}
      ha)
  )({==})

# the round of the ballot b is at most m
def Ballot.under(m: Nat, b: RRounds.Ballot) -> Bool:
  Nat.is_le(RRounds.Ballot.round(b), m)

# the highest round of a ballot among bs is at most m, when the round of each
# is
def Rounds.top_le(
  bs: List<&2, RRounds.Ballot>,
  +m: Nat
) -> {
  Shared.List.holds(~RRounds.Ballot, ~Nat, ~Ballot.under, bs, m) == True{}: Bool
} -> {Nat.is_le(RRounds.Rounds.top(bs), m) == True{}: Bool}:
  match bs:
    case Nil{}:
      h => Shared.Nat.le_zero(m)
    case Con{+b, +rest}:
      +h => Nat.max_le(
        RRounds.Ballot.round(b),
        RRounds.Rounds.top(rest),
        m
      )(
        Shared.List.all.if_hit(
          Ballot.under(m, b),
          u => Shared.List.holds(~RRounds.Ballot, ~Nat, ~Ballot.under, rest, m)
        )(h)
      )(
        Rounds.top_le(
          rest,
          m
        )(
          Shared.List.all.if_rest(
            Ballot.under(m, b),
            u => Shared.List.holds(~RRounds.Ballot, ~Nat, ~Ballot.under, rest, m)
          )(h)
        )
      )

# p holds of each ballot of the slot k of the line c among the facts fs, when
# it holds of each ballot for the slot among fs
def Slot.holds_of(
  ~V: Data,
  ~p: V -> RRounds.Ballot -> Bool,
  fs: List<&2, Types.Fact>,
  +c: Ledgers.Line,
  +k: Nat,
  +g: V,
  h: (
    @+v: String -> @+t: Nat -> @+x: Types.Cast -> {
      List.contains(
        ~Types.Fact,
        ~Coded.Fact.is_eq,
        fs,
        Types.Fact.Vote{v, Types.Step.At{c, k, t}, x}
      )
        == True{}: Bool
    } -> {p(g)(RRounds.Ballot{v, t, x}) == True{}: Bool}
  )
) -> {
  Shared.List.holds(~RRounds.Ballot, ~V, ~p, RRounds.Slot.ballots(fs, c, k), g) == True{}: Bool
}:
  match fs:
    case Nil{}:
      {==}
    case Con{Types.Fact.Ask{+a}, +rest}:
      Slot.holds_of(
        ~V,
        ~p,
        rest,
        c,
        k,
        g,
        +v => +t => +x => cin => h(
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
      Slot.holds_of(
        ~V,
        ~p,
        rest,
        c,
        k,
        g,
        +v => +t => +x => cin => h(
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
        b => (
          @+v: String -> @+t: Nat -> @+x: Types.Cast -> {
            List.contains(
              ~Types.Fact,
              ~Coded.Fact.is_eq,
              Types.Fact.Vote{w, Types.Step.At{c2, k2, u}, y} <> rest,
              Types.Fact.Vote{v, Types.Step.At{c, k, t}, x}
            )
              == True{}: Bool
          } -> {p(g)(RRounds.Ballot{v, t, x}) == True{}: Bool}
        ) -> {
          Shared.List.holds(
            ~RRounds.Ballot,
            ~V,
            ~p,
            List.filter.put(
              RRounds.Ballot,
              RRounds.Ballot{w, u, y},
              RRounds.Slot.ballots(rest, c, k),
              b
            ),
            g
          )
            == True{}: Bool
        },
        Bool.and(Ledgers.Line.is_eq(c2, c), Nat.is_eq(k2, k)),
        +e1 => h0 => Facts.Case.all_one(
          (
            @+v: String -> @+t: Nat -> @+x: Types.Cast -> {
              List.contains(
                ~Types.Fact,
                ~Coded.Fact.is_eq,
                Types.Fact.Vote{w, Types.Step.At{c2, k2, u}, y} <> rest,
                Types.Fact.Vote{v, Types.Step.At{c, k, t}, x}
              )
                == True{}: Bool
            } -> {p(g)(RRounds.Ballot{v, t, x}) == True{}: Bool}
          ),
          p(g)(RRounds.Ballot{w, u, y}),
          z0 => Shared.List.holds(~RRounds.Ballot, ~V, ~p, RRounds.Slot.ballots(rest, c, k), g),
          h0,
          h => h(w)(u)(y)((
              %Ledgers.Line.is_eq_sound(c2, c)(Shared.Bool.and_true_left(Ledgers.Line.is_eq(c2, c), Nat.is_eq(k2, k))(e1)): {List.contains(~Types.Fact, ~Coded.Fact.is_eq, Types.Fact.Vote{w, Types.Step.At{c2, k2, u}, y} <> rest, Types.Fact.Vote{w, Types.Step.At{_, k, u}, y}) == True{}: Bool}
              %Shared.Nat.is_eq_sound(k2, k)(Shared.Bool.and_true_right(Ledgers.Line.is_eq(c2, c), Nat.is_eq(k2, k))(e1)): {List.contains(~Types.Fact, ~Coded.Fact.is_eq, Types.Fact.Vote{w, Types.Step.At{c2, k2, u}, y} <> rest, Types.Fact.Vote{w, Types.Step.At{c2, _, u}, y}) == True{}: Bool}
              Lists.List.contains_head(~Types.Fact, ~Coded.Fact.is_eq, ~Coded.Fact.laws(), Types.Fact.Vote{w, Types.Step.At{c2, k2, u}, y}, rest))),
          h => Slot.holds_of(
            ~V,
            ~p,
            rest,
            c,
            k,
            g,
            +v => +t => +x => cin => h(
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
        e1 => h => Slot.holds_of(
          ~V,
          ~p,
          rest,
          c,
          k,
          g,
          +v => +t => +x => cin => h(
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
      )(h)

# a voter that cast a ballot of a round that is no lower than r came to r
def Rounds.heard_of(
  bs: List<&2, RRounds.Ballot>,
  +h: String,
  +r: Nat,
  +t: Nat,
  +x: Types.Cast
) -> {
  List.contains(
    ~Types.Cast,
    ~Coded.Cast.is_eq,
    RRounds.Casts.of(bs, Types.Ref{h, t}),
    x
  )
    == True{}: Bool
} -> {
  Nat.is_le(r, RRounds.Cast.round(x)) == True{}: Bool
} -> {RRounds.Rounds.heard(bs, h, r) == True{}: Bool}:
  match bs:
    case Nil{}:
      hin => hle => Empty.absurd(
        {RRounds.Rounds.heard([], h, r) == True{}: Bool},
        Shared.Bool.false_ne_true(hin)
      )
    case Con{RRounds.Ballot{+w, +u, +y}, +rest}:
      Lists.Bool.by(
        z => {
          List.contains(
            ~Types.Cast,
            ~Coded.Cast.is_eq,
            Shared.Maybe.cons(
              Types.Cast,
              Shared.Maybe.when(Types.Cast, z, q => Some{y}),
              RRounds.Casts.of(rest, Types.Ref{h, t})
            ),
            x
          )
            == True{}: Bool
        } -> {
          Nat.is_le(r, RRounds.Cast.round(x)) == True{}: Bool
        } -> {RRounds.Rounds.heard(RRounds.Ballot{w, u, y} <> rest, h, r) == True{}: Bool},
        Bool.and(String.eq(w, h), Nat.is_eq(u, t)),
        et => hin => +hle => Lists.List.contains_cons_by(
          ~Types.Cast,
          ~Coded.Cast.is_eq,
          ~Coded.Cast.laws(),
          {RRounds.Rounds.heard(RRounds.Ballot{w, u, y} <> rest, h, r) == True{}: Bool},
          y,
          RRounds.Casts.of(rest, Types.Ref{h, t}),
          x,
          hin,
          ey => (
            %Equal.sym(Bool, String.eq(w, h), True{}, Shared.Bool.and_true_left(String.eq(w, h), Nat.is_eq(u, t))(et)): {List.any.if(u0 => RRounds.Rounds.heard(rest, h, r), Shared.Bool.when(Bool, _, u1 => Nat.is_le(r, RRounds.Cast.round(y)), u1 => False{})) == True{}: Bool}
            %Equal.sym(Types.Cast, y, x, ey): {List.any.if(u0 => RRounds.Rounds.heard(rest, h, r), Nat.is_le(r, RRounds.Cast.round(_))) == True{}: Bool}
            %Equal.sym(Bool, Nat.is_le(r, RRounds.Cast.round(x)), True{}, hle): {List.any.if(u0 => RRounds.Rounds.heard(rest, h, r), _) == True{}: Bool}
            {==}),
          hrest => Laws.Rounds.heard_grows(
            RRounds.Ballot{w, u, y},
            rest,
            h,
            r
          )(Rounds.heard_of(rest, h, r, t, x)(hrest)(hle))
        ),
        ef => hin => hle => Laws.Rounds.heard_grows(
          RRounds.Ballot{w, u, y},
          rest,
          h,
          r
        )(Rounds.heard_of(rest, h, r, t, x)(hin)(hle))
      )

# the voter h cast a ballot among bs of the round r or of a round above
def Rounds.Heard(bs: List<&2, RRounds.Ballot>, h: String, r: Nat) -> Type:
  Exists(
    Nat,
    t => Exists(
      Types.Cast,
      x => {
        List.contains(
          ~Types.Cast,
          ~Coded.Cast.is_eq,
          RRounds.Casts.of(bs, Types.Ref{h, t}),
          x
        )
          == True{}: Bool
      }
        & {Nat.is_le(r, RRounds.Cast.round(x)) == True{}: Bool}
    )
  )

# Rounds.heard_cast.more, with the ballot
def Rounds.heard_cast.fin(
  b: RRounds.Ballot,
  +rest: List<&2, RRounds.Ballot>,
  +h: String,
  +r: Nat,
  +t: Nat,
  +x: Types.Cast,
  w: {
    List.contains(
      ~Types.Cast,
      ~Coded.Cast.is_eq,
      RRounds.Casts.of(rest, Types.Ref{h, t}),
      x
    )
      == True{}: Bool
  }
    & {Nat.is_le(r, RRounds.Cast.round(x)) == True{}: Bool}
) -> Rounds.Heard(b <> rest, h, r):
  (hin, hle) = w
  (
    t,
    (
      x,
      (
        Lists.List.contains_maybe_cons(
          ~Types.Cast,
          ~Coded.Cast.is_eq,
          RRounds.Ballot.casts(Types.Ref{h, t}, b),
          RRounds.Casts.of(rest, Types.Ref{h, t}),
          x
        )(hin),
        hle
      )
    )
  )

# a ballot that the voter h cast among rest, it cast among rest with one more
# ballot
def Rounds.heard_cast.more(
  +b: RRounds.Ballot,
  +rest: List<&2, RRounds.Ballot>,
  +h: String,
  +r: Nat,
  w: Rounds.Heard(rest, h, r)
) -> Rounds.Heard(b <> rest, h, r):
  Laws.Ex.by(
    Nat,
    t => Exists(
      Types.Cast,
      x => {
        List.contains(
          ~Types.Cast,
          ~Coded.Cast.is_eq,
          RRounds.Casts.of(rest, Types.Ref{h, t}),
          x
        )
          == True{}: Bool
      }
        & {Nat.is_le(r, RRounds.Cast.round(x)) == True{}: Bool}
    ),
    Rounds.Heard(b <> rest, h, r),
    w,
    +t => w2 => Laws.Ex.by(
      Types.Cast,
      x => {
        List.contains(
          ~Types.Cast,
          ~Coded.Cast.is_eq,
          RRounds.Casts.of(rest, Types.Ref{h, t}),
          x
        )
          == True{}: Bool
      }
        & {Nat.is_le(r, RRounds.Cast.round(x)) == True{}: Bool},
      Rounds.Heard(b <> rest, h, r),
      w2,
      +x => w3 => Rounds.heard_cast.fin(b, rest, h, r, t, x, w3)
    )
  )

# a voter that came to the round r cast a ballot of r or of a round above
def Rounds.heard_cast(
  bs: List<&2, RRounds.Ballot>,
  +h: String,
  +r: Nat
) -> {RRounds.Rounds.heard(bs, h, r) == True{}: Bool} -> Rounds.Heard(bs, h, r):
  match bs:
    case Nil{}:
      hh => Empty.absurd(Rounds.Heard([], h, r), Shared.Bool.false_ne_true(hh))
    case Con{RRounds.Ballot{+w, +u, +y}, +rest}:
      Lists.Bool.by(
        z => {
          String.eq(w, h) == z: Bool
        } -> {
          List.any.if(
            u0 => RRounds.Rounds.heard(rest, h, r),
            Shared.Bool.when(Bool, z, u1 => Nat.is_le(r, RRounds.Cast.round(y)), u1 => False{})
          )
            == True{}: Bool
        } -> Rounds.Heard(RRounds.Ballot{w, u, y} <> rest, h, r),
        String.eq(w, h),
        ew => e0 => Lists.Bool.by(
          z => {
            List.any.if(u0 => RRounds.Rounds.heard(rest, h, r), z) == True{}: Bool
          } -> Rounds.Heard(RRounds.Ballot{w, u, y} <> rest, h, r),
          Nat.is_le(r, RRounds.Cast.round(y)),
          el => hh => (u, (y, ((
                  %Equal.sym(Bool, String.eq(w, h), True{}, ew): {List.contains(~Types.Cast, ~Coded.Cast.is_eq, Shared.Maybe.cons(Types.Cast, Shared.Maybe.when(Types.Cast, Bool.and(_, Nat.is_eq(u, u)), q => Some{y}), RRounds.Casts.of(rest, Types.Ref{h, u})), y) == True{}: Bool}
                  %Equal.sym(Bool, Nat.is_eq(u, u), True{}, Shared.Nat.is_eq_refl(u)): {List.contains(~Types.Cast, ~Coded.Cast.is_eq, Shared.Maybe.cons(Types.Cast, Shared.Maybe.when(Types.Cast, _, q => Some{y}), RRounds.Casts.of(rest, Types.Ref{h, u})), y) == True{}: Bool}
                  Lists.List.contains_head(~Types.Cast, ~Coded.Cast.is_eq, ~Coded.Cast.laws(), y, RRounds.Casts.of(rest, Types.Ref{h, u}))), el))),
          el => hh => Rounds.heard_cast.more(
            RRounds.Ballot{w, u, y},
            rest,
            h,
            r,
            Rounds.heard_cast(rest, h, r)(hh)
          )
        ),
        ew => e0 => hh => Rounds.heard_cast.more(
          RRounds.Ballot{w, u, y},
          rest,
          h,
          r,
          Rounds.heard_cast(rest, h, r)(hh)
        )
      )({==})

# One more ballot
# ---------------
# What the ballots of a slot are after a node cast one more (Facts.add).

# the highest round of a ballot, after one more ballot of a round to that is
# no lower than each round before, is to
def Slot.added_top(
  +s: Facts.Facts(),
  +name: String,
  +c: Ledgers.Line,
  +k: Nat,
  +t: Nat,
  +x: Types.Cast
) -> {
  Nat.is_le(RRounds.Rounds.top(Laws.Slot.ballots(s, c, k)), RRounds.Cast.round(x)) == True{}: Bool
} -> {
  RRounds.Rounds.top(
    Laws.Slot.ballots(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}), c, k)
  )
    == RRounds.Cast.round(x): Nat
}:
  +hle => Nat.le_same(
    RRounds.Rounds.top(
      Laws.Slot.ballots(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}), c, k)
    ),
    RRounds.Cast.round(x)
  )(
    Rounds.top_le(
      Laws.Slot.ballots(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}), c, k),
      RRounds.Cast.round(x)
    )(
      Slot.holds_of(
        ~Nat,
        ~Ballot.under,
        Facts.Facts.list(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})),
        c,
        k,
        RRounds.Cast.round(x),
        +v => +u => +y => cin => Facts.Facts.add_cases(
          {Nat.is_le(RRounds.Cast.round(y), RRounds.Cast.round(x)) == True{}: Bool},
          s,
          Types.Fact.Vote{name, Types.Step.At{c, k, t}, x},
          Types.Fact.Vote{v, Types.Step.At{c, k, u}, y},
          Facts.Facts.in_has(
            Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}),
            Types.Fact.Vote{v, Types.Step.At{c, k, u}, y}
          )(cin),
          e => (
            %Equal.sym(Types.Cast, y, x, Equal.cong(Types.Fact, Types.Cast, Laws.Fact.cast, Types.Fact.Vote{v, Types.Step.At{c, k, u}, y}, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}, e)): {Nat.is_le(RRounds.Cast.round(_), RRounds.Cast.round(x)) == True{}: Bool}
            Shared.Nat.le_refl(RRounds.Cast.round(x))),
          hs => Shared.Nat.le_trans(
            RRounds.Cast.round(y),
            RRounds.Rounds.top(Laws.Slot.ballots(s, c, k)),
            RRounds.Cast.round(x)
          )(
            Laws.Casts.of_top(
              Laws.Slot.ballots(s, c, k),
              v,
              u,
              y
            )(Laws.Casts.has_of(s, c, k, v, u, y)(hs))
          )(hle)
        )
      )
    )
  )(
    Laws.Casts.of_top(
      Laws.Slot.ballots(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}), c, k),
      name,
      t,
      x
    )(
      Laws.Casts.has_of(
        Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}),
        c,
        k,
        name,
        t,
        x
      )(Facts.Facts.add_has(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))
    )
  )

# Slot.added_heard, with the ballot of the voter
def Slot.added_heard.fin(
  +s: Facts.Facts(),
  +f: Types.Fact,
  +c: Ledgers.Line,
  +k: Nat,
  +h: String,
  +r: Nat,
  +t: Nat,
  +x: Types.Cast,
  w: {
    List.contains(
      ~Types.Cast,
      ~Coded.Cast.is_eq,
      RRounds.Casts.of(Laws.Slot.ballots(s, c, k), Types.Ref{h, t}),
      x
    )
      == True{}: Bool
  }
    & {Nat.is_le(r, RRounds.Cast.round(x)) == True{}: Bool}
) -> {RRounds.Rounds.heard(Laws.Slot.ballots(Facts.Facts.add(s, f), c, k), h, r) == True{}: Bool}:
  (hin, hle) = w
  Rounds.heard_of(
    Laws.Slot.ballots(Facts.Facts.add(s, f), c, k),
    h,
    r,
    t,
    x
  )(
    Laws.Casts.has_of(
      Facts.Facts.add(s, f),
      c,
      k,
      h,
      t,
      x
    )(
      Facts.Facts.add_keeps(
        s,
        f,
        Types.Fact.Vote{h, Types.Step.At{c, k, t}, x}
      )(Laws.Casts.of_has(s, c, k, h, t, x)(hin))
    )
  )(hle)

# a voter that came to a round came to it in the facts with one more fact
def Slot.added_heard(
  +s: Facts.Facts(),
  +f: Types.Fact,
  +c: Ledgers.Line,
  +k: Nat,
  +h: String,
  +r: Nat
) -> {
  RRounds.Rounds.heard(Laws.Slot.ballots(s, c, k), h, r) == True{}: Bool
} -> {RRounds.Rounds.heard(Laws.Slot.ballots(Facts.Facts.add(s, f), c, k), h, r) == True{}: Bool}:
  hh => Laws.Ex.by(
    Nat,
    t => Exists(
      Types.Cast,
      x => {
        List.contains(
          ~Types.Cast,
          ~Coded.Cast.is_eq,
          RRounds.Casts.of(Laws.Slot.ballots(s, c, k), Types.Ref{h, t}),
          x
        )
          == True{}: Bool
      }
        & {Nat.is_le(r, RRounds.Cast.round(x)) == True{}: Bool}
    ),
    {RRounds.Rounds.heard(Laws.Slot.ballots(Facts.Facts.add(s, f), c, k), h, r) == True{}: Bool},
    Rounds.heard_cast(Laws.Slot.ballots(s, c, k), h, r)(hh),
    +t => w2 => Laws.Ex.by(
      Types.Cast,
      x => {
        List.contains(
          ~Types.Cast,
          ~Coded.Cast.is_eq,
          RRounds.Casts.of(Laws.Slot.ballots(s, c, k), Types.Ref{h, t}),
          x
        )
          == True{}: Bool
      }
        & {Nat.is_le(r, RRounds.Cast.round(x)) == True{}: Bool},
      {RRounds.Rounds.heard(Laws.Slot.ballots(Facts.Facts.add(s, f), c, k), h, r) == True{}: Bool},
      w2,
      +x => w3 => Slot.added_heard.fin(s, f, c, k, h, r, t, x, w3)
    )
  )

# a round that is alive for a node is alive for it in the facts with one more
# fact
def Slot.added_alive(
  +s: Facts.Facts(),
  +f: Types.Fact,
  +c: Ledgers.Line,
  +k: Nat,
  +ds: List<&2, String>,
  +name: String,
  +top: Nat
) -> {
  RRounds.Round.alive(Laws.Slot.ballots(s, c, k), ds, k, name, top) == True{}: Bool
} -> {
  RRounds.Round.alive(
    Laws.Slot.ballots(Facts.Facts.add(s, f), c, k),
    ds,
    k,
    name,
    top
  )
    == True{}: Bool
}:
  Lists.Bool.by(
    z => {
      Shared.Bool.when(
        Bool,
        z,
        u => True{},
        u => RRounds.Rounds.heard(
          Laws.Slot.ballots(s, c, k),
          RRounds.Turn.of(ds, Nat.add(k, top)),
          top
        )
      )
        == True{}: Bool
    } -> {
      Shared.Bool.when(
        Bool,
        z,
        u => True{},
        u => RRounds.Rounds.heard(
          Laws.Slot.ballots(Facts.Facts.add(s, f), c, k),
          RRounds.Turn.of(ds, Nat.add(k, top)),
          top
        )
      )
        == True{}: Bool
    },
    String.eq(RRounds.Turn.of(ds, Nat.add(k, top)), name),
    et => e => {==},
    ef => e => Slot.added_heard(s, f, c, k, RRounds.Turn.of(ds, Nat.add(k, top)), top)(e)
  )

# Passes
# ------

# the number of the draft d
def Draft.turn(d: RRounds.Draft) -> Nat:
  match d:
    case RRounds.Draft{t, x}:
      t

# after a pass to a round, the lowest round that a voter may vote in is that
# round or a round above
def Seen.passed_above(
  m: RRounds.Seen,
  +to: Nat
) -> {Nat.is_le(to, RRounds.Seen.floor(RRounds.Seen.step(m, Types.Cast.Pass{to}))) == True{}: Bool}:
  match m:
    case RRounds.Seen{+fl, +vs}:
      Lists.Bool.by(
        z => {
          Nat.is_le(
            to,
            RRounds.Seen.floor(
              Bool.pick(RRounds.Seen, z, RRounds.Seen{to, vs}, RRounds.Seen{fl, vs})
            )
          )
            == True{}: Bool
        },
        Nat.is_le(fl, to),
        et => Shared.Nat.le_refl(to),
        ef => Shared.Nat.nle_le(fl, to)(ef)
      )

# the cast x of the number t2 is a pass of a node whose next ballot is of the
# number t: to a round that is no lower than each round of a ballot among bs,
# and is alive for the node
def Pass.To(
  bs: List<&2, RRounds.Ballot>,
  ds: List<&2, String>,
  k: Nat,
  name: String,
  t: Nat,
  t2: Nat,
  x: Types.Cast
) -> Type:
  Exists(
    Nat,
    to => {
      x == Types.Cast.Pass{to}: Types.Cast
    }
      & (
        {
          t2 == t: Nat
        }
          & (
            {
              Nat.is_le(RRounds.Rounds.top(bs), to) == True{}: Bool
            }
              & {RRounds.Round.alive(bs, ds, k, name, to) == True{}: Bool}
          )
      )
  )

# the pass of a node is of the number of its next ballot, to a round that is
# no lower than each round of a ballot, and is alive for the node
def Pass.next_to(
  +bs: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +name: String,
  +t: Nat,
  +t2: Nat,
  +x: Types.Cast,
  m: RRounds.Seen
) -> {
  Laws.Pass.next(
    bs,
    ds,
    k,
    name,
    RRounds.Reach{t, m}
  )
    == Some{RRounds.Draft{t2, x}}: Maybe<&2, RRounds.Draft>
} -> Pass.To(bs, ds, k, name, t, t2, x):
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
            == Some{RRounds.Draft{t2, x}}: Maybe<&2, RRounds.Draft>
        } -> Pass.To(bs, ds, k, name, t, t2, x),
        RRounds.Round.alive(bs, ds, k, name, RRounds.Rounds.top(bs)),
        +et => Lists.Bool.by(
          z => {
            RRounds.Slot.pass.to(
              t,
              Shared.Maybe.when(Nat, z, u => Some{RRounds.Rounds.top(bs)})
            )
              == Some{RRounds.Draft{t2, x}}: Maybe<&2, RRounds.Draft>
          } -> Pass.To(bs, ds, k, name, t, t2, x),
          Nat.is_lt(fl, RRounds.Rounds.top(bs)),
          el => +e => (
            RRounds.Rounds.top(bs),
            (
              Equal.sym(
                Types.Cast,
                Types.Cast.Pass{RRounds.Rounds.top(bs)},
                x,
                Laws.Draft.cast_of(t, t2, Types.Cast.Pass{RRounds.Rounds.top(bs)}, x, e)
              ),
              (
                Equal.sym(
                  Nat,
                  t,
                  t2,
                  Equal.cong(
                    RRounds.Draft,
                    Nat,
                    Draft.turn,
                    RRounds.Draft{t, Types.Cast.Pass{RRounds.Rounds.top(bs)}},
                    RRounds.Draft{t2, x},
                    Shared.Maybe.some_inj(
                      RRounds.Draft,
                      RRounds.Draft{t, Types.Cast.Pass{RRounds.Rounds.top(bs)}},
                      RRounds.Draft{t2, x},
                      e
                    )
                  )
                ),
                (Shared.Nat.le_refl(RRounds.Rounds.top(bs)), et)
              )
            )
          ),
          el => e => Empty.absurd(
            Pass.To(bs, ds, k, name, t, t2, x),
            Shared.Maybe.none_ne_some(RRounds.Draft, RRounds.Draft{t2, x}, e)
          )
        ),
        ef => Lists.Maybe.by(
          Nat,
          z => {
            RRounds.Slot.pass.to(t, z) == Some{RRounds.Draft{t2, x}}: Maybe<&2, RRounds.Draft>
          } -> Pass.To(bs, ds, k, name, t, t2, x),
          RRounds.Rounds.mine(List.length(&2, String, ds), ds, k, name, RRounds.Rounds.top(bs)),
          en => e => Empty.absurd(
            Pass.To(bs, ds, k, name, t, t2, x),
            Shared.Maybe.none_ne_some(RRounds.Draft, RRounds.Draft{t2, x}, e)
          ),
          +to => +em => +e => (
            to,
            (
              Equal.sym(
                Types.Cast,
                Types.Cast.Pass{to},
                x,
                Laws.Draft.cast_of(t, t2, Types.Cast.Pass{to}, x, e)
              ),
              (
                Equal.sym(
                  Nat,
                  t,
                  t2,
                  Equal.cong(
                    RRounds.Draft,
                    Nat,
                    Draft.turn,
                    RRounds.Draft{t, Types.Cast.Pass{to}},
                    RRounds.Draft{t2, x},
                    Shared.Maybe.some_inj(
                      RRounds.Draft,
                      RRounds.Draft{t, Types.Cast.Pass{to}},
                      RRounds.Draft{t2, x},
                      e
                    )
                  )
                ),
                (
                  Shared.Nat.lt_weak(
                    RRounds.Rounds.top(bs),
                    to
                  )(
                    Laws.Rounds.mine_above(
                      List.length(&2, String, ds),
                      ds,
                      k,
                      name,
                      RRounds.Rounds.top(bs),
                      to
                    )(em)
                  ),
                  (
                    %Equal.sym(Bool, String.eq(RRounds.Turn.of(ds, Nat.add(k, to)), name), True{}, Laws.Rounds.mine_turn(List.length(&2, String, ds), ds, k, name, RRounds.Rounds.top(bs), to)(em)): {Shared.Bool.when(Bool, _, u => True{}, u => RRounds.Rounds.heard(bs, RRounds.Turn.of(ds, Nat.add(k, to)), to)) == True{}: Bool}
                    {==})
                )
              )
            )
          )
        )
      )

# Slot.passed_waits, with how far the ballots of the node are held after its
# pass
def Slot.passed_waits.end(
  +s: Facts.Facts(),
  +name: String,
  +c: Ledgers.Line,
  +k: Nat,
  +ds: List<&2, String>,
  +t: Nat,
  +to: Nat,
  +m: RRounds.Seen,
  +t2: Nat,
  +sn2: RRounds.Seen,
  +hc: {Facts.Facts.cast(s, name, Types.Step.At{c, k, t}) == False{}: Bool},
  es: {RRounds.Chain.seen(Laws.Slot.ballots(s, c, k), name, t) == Some{m}: Maybe<&2, RRounds.Seen>},
  hle: {Nat.is_le(RRounds.Rounds.top(Laws.Slot.ballots(s, c, k)), to) == True{}: Bool},
  ha: {RRounds.Round.alive(Laws.Slot.ballots(s, c, k), ds, k, name, to) == True{}: Bool},
  er2: {
    RRounds.Chain.reach(
      Laws.Slot.ballots(
        Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Pass{to}}),
        c,
        k
      ),
      name
    )
      == RRounds.Reach{t2, sn2}: RRounds.Reach
  },
  held: Laws.Reach.Held(
    Laws.Slot.ballots(
      Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Pass{to}}),
      c,
      k
    ),
    name,
    RRounds.Reach{t2, sn2}
  )
) -> {
  RRounds.Slot.pass(
    Laws.Slot.ballots(
      Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Pass{to}}),
      c,
      k
    ),
    ds,
    k,
    name
  )
    == None{}: Maybe<&2, RRounds.Draft>
}:
  (es2, hn2) = held
  Lists.Equal.to(
    RRounds.Reach,
    z => {
      Laws.Pass.next(
        Laws.Slot.ballots(
          Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Pass{to}}),
          c,
          k
        ),
        ds,
        k,
        name,
        z
      )
        == None{}: Maybe<&2, RRounds.Draft>
    },
    RRounds.Reach{t2, sn2},
    RRounds.Chain.reach(
      Laws.Slot.ballots(
        Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Pass{to}}),
        c,
        k
      ),
      name
    ),
    Equal.sym(
      RRounds.Reach,
      RRounds.Chain.reach(
        Laws.Slot.ballots(
          Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Pass{to}}),
          c,
          k
        ),
        name
      ),
      RRounds.Reach{t2, sn2},
      er2
    ),
    Lists.Equal.to(
      Nat,
      top2 => {
        RRounds.Slot.pass.at(
          top2,
          RRounds.Round.alive(
            Laws.Slot.ballots(
              Facts.Facts.add(
                s,
                Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Pass{to}}
              ),
              c,
              k
            ),
            ds,
            k,
            name,
            top2
          ),
          u => RRounds.Rounds.mine(List.length(&2, String, ds), ds, k, name, top2),
          RRounds.Reach{t2, sn2}
        )
          == None{}: Maybe<&2, RRounds.Draft>
      },
      to,
      RRounds.Rounds.top(
        Laws.Slot.ballots(
          Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Pass{to}}),
          c,
          k
        )
      ),
      Equal.sym(
        Nat,
        RRounds.Rounds.top(
          Laws.Slot.ballots(
            Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Pass{to}}),
            c,
            k
          )
        ),
        to,
        Slot.added_top(s, name, c, k, t, Types.Cast.Pass{to})(hle)
      ),
      Laws.Slot.pass.at_waits(
        to,
        RRounds.Round.alive(
          Laws.Slot.ballots(
            Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Pass{to}}),
            c,
            k
          ),
          ds,
          k,
          name,
          to
        ),
        u => RRounds.Rounds.mine(List.length(&2, String, ds), ds, k, name, to),
        t2,
        sn2
      )(
        Slot.added_alive(
          s,
          Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Pass{to}},
          c,
          k,
          ds,
          name,
          to
        )(ha)
      )(
        Shared.Nat.le_nlt(
          to,
          RRounds.Seen.floor(sn2)
        )(
          Shared.Nat.le_trans(
            to,
            RRounds.Seen.floor(RRounds.Seen.step(m, Types.Cast.Pass{to})),
            RRounds.Seen.floor(sn2)
          )(
            Seen.passed_above(m, to)
          )(
            Chain.floor_last(
              Laws.Slot.ballots(
                Facts.Facts.add(
                  s,
                  Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Pass{to}}
                ),
                c,
                k
              ),
              name,
              1n+t,
              RRounds.Seen.step(m, Types.Cast.Pass{to}),
              t2,
              sn2
            )((
                %Equal.sym(Maybe<&2, RRounds.Seen>, RRounds.Chain.seen(Laws.Slot.ballots(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Pass{to}}), c, k), name, t), Some{m}, Laws.Chain.seen_grows(Laws.Slot.ballots(s, c, k), Laws.Slot.ballots(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Pass{to}}), c, k), name, t, m, Laws.Slot.added_grown(s, name, c, k, t, Types.Cast.Pass{to}, hc))(es)): {RRounds.Chain.seen.next(_, RRounds.Ballots.at(Laws.Slot.ballots(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Pass{to}}), c, k), name, t)) == Some{RRounds.Seen.step(m, Types.Cast.Pass{to})}: Maybe<&2, RRounds.Seen>}
                %Equal.sym(Maybe<&2, Types.Cast>, RRounds.Ballots.at(Laws.Slot.ballots(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Pass{to}}), c, k), name, t), Some{Types.Cast.Pass{to}}, Laws.Slot.added_at(s, name, c, k, t, Types.Cast.Pass{to}, hc)): {RRounds.Chain.seen.next(Some{m}, _) == Some{RRounds.Seen.step(m, Types.Cast.Pass{to})}: Maybe<&2, RRounds.Seen>}
                {==}))(es2)(hn2)
          )
        )
      )
    )
  )

# Slot.passed_waits, once how far the ballots of the node are held after its
# pass (m2) is known
def Slot.passed_waits.fin(
  m2: RRounds.Reach,
  +s: Facts.Facts(),
  +name: String,
  +c: Ledgers.Line,
  +k: Nat,
  +ds: List<&2, String>,
  +t: Nat,
  +to: Nat,
  +m: RRounds.Seen
) -> {
  Facts.Facts.cast(s, name, Types.Step.At{c, k, t}) == False{}: Bool
} -> {
  RRounds.Chain.seen(Laws.Slot.ballots(s, c, k), name, t) == Some{m}: Maybe<&2, RRounds.Seen>
} -> {
  Nat.is_le(RRounds.Rounds.top(Laws.Slot.ballots(s, c, k)), to) == True{}: Bool
} -> {
  RRounds.Round.alive(Laws.Slot.ballots(s, c, k), ds, k, name, to) == True{}: Bool
} -> {
  RRounds.Chain.reach(
    Laws.Slot.ballots(
      Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Pass{to}}),
      c,
      k
    ),
    name
  )
    == m2: RRounds.Reach
} -> Laws.Reach.Held(
  Laws.Slot.ballots(
    Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Pass{to}}),
    c,
    k
  ),
  name,
  m2
) -> {
  RRounds.Slot.pass(
    Laws.Slot.ballots(
      Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Pass{to}}),
      c,
      k
    ),
    ds,
    k,
    name
  )
    == None{}: Maybe<&2, RRounds.Draft>
}:
  match m2:
    case RRounds.Reach{+t2, +sn2}:
      +hc => es => hle => ha => er2 => held => Slot.passed_waits.end(
        s,
        name,
        c,
        k,
        ds,
        t,
        to,
        m,
        t2,
        sn2,
        hc,
        es,
        hle,
        ha,
        er2,
        held
      )

# Slot.passed_waits, with the round that the node passes to
def Slot.passed_waits.to(
  +s: Facts.Facts(),
  +name: String,
  +c: Ledgers.Line,
  +k: Nat,
  +ds: List<&2, String>,
  +t2: Nat,
  +x: Types.Cast,
  +t: Nat,
  +sn: RRounds.Seen,
  +to: Nat,
  +hl: {List.contains(~String, ~String.eq, Facts.Facts.liars(s), name) == False{}: Bool},
  held: Laws.Reach.Held(Laws.Slot.ballots(s, c, k), name, RRounds.Reach{t, sn}),
  w: {
    x == Types.Cast.Pass{to}: Types.Cast
  }
    & (
      {
        t2 == t: Nat
      }
        & (
          {
            Nat.is_le(RRounds.Rounds.top(Laws.Slot.ballots(s, c, k)), to) == True{}: Bool
          }
            & {RRounds.Round.alive(Laws.Slot.ballots(s, c, k), ds, k, name, to) == True{}: Bool}
        )
    )
) -> {
  RRounds.Slot.pass(
    Laws.Slot.ballots(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t2}, x}), c, k),
    ds,
    k,
    name
  )
    == None{}: Maybe<&2, RRounds.Draft>
}:
  (es, hn) = held
  (ex, w2) = w
  (et, w3) = w2
  (hle, ha) = w3
  %Equal.sym(
    Types.Cast,
    x,
    Types.Cast.Pass{to},
    ex
  ): {
    RRounds.Slot.pass(
      Laws.Slot.ballots(
        Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t2}, _}),
        c,
        k
      ),
      ds,
      k,
      name
    )
      == None{}: Maybe<&2, RRounds.Draft>
  }
  %Equal.sym(
    Nat,
    t2,
    t,
    et
  ): {
    RRounds.Slot.pass(
      Laws.Slot.ballots(
        Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, _}, Types.Cast.Pass{to}}),
        c,
        k
      ),
      ds,
      k,
      name
    )
      == None{}: Maybe<&2, RRounds.Draft>
  }
  Slot.passed_waits.fin(
    RRounds.Chain.reach(
      Laws.Slot.ballots(
        Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Pass{to}}),
        c,
        k
      ),
      name
    ),
    s,
    name,
    c,
    k,
    ds,
    t,
    to,
    sn
  )(
    Laws.Slot.cast_none(s, name, c, k, t, hl, hn)
  )(
    es
  )(
    hle
  )(
    ha
  )(
    {==}
  )(
    Laws.Chain.reach_held(
      Laws.Slot.ballots(
        Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Pass{to}}),
        c,
        k
      ),
      name
    )
  )

# Slot.passed_waits, once how far the ballots of the node are held (m) is
# known
def Slot.passed_waits.at(
  m: RRounds.Reach,
  +s: Facts.Facts(),
  +name: String,
  +c: Ledgers.Line,
  +k: Nat,
  +ds: List<&2, String>,
  +t2: Nat,
  +x: Types.Cast
) -> {
  List.contains(~String, ~String.eq, Facts.Facts.liars(s), name) == False{}: Bool
} -> Laws.Reach.Held(
  Laws.Slot.ballots(s, c, k),
  name,
  m
) -> {
  Laws.Pass.next(
    Laws.Slot.ballots(s, c, k),
    ds,
    k,
    name,
    m
  )
    == Some{RRounds.Draft{t2, x}}: Maybe<&2, RRounds.Draft>
} -> {
  RRounds.Slot.pass(
    Laws.Slot.ballots(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t2}, x}), c, k),
    ds,
    k,
    name
  )
    == None{}: Maybe<&2, RRounds.Draft>
}:
  match m:
    case RRounds.Reach{+t, +sn}:
      +hl => held => ep => Laws.Ex.by(
        Nat,
        to => {
          x == Types.Cast.Pass{to}: Types.Cast
        }
          & (
            {
              t2 == t: Nat
            }
              & (
                {
                  Nat.is_le(RRounds.Rounds.top(Laws.Slot.ballots(s, c, k)), to) == True{}: Bool
                }
                  & {
                    RRounds.Round.alive(Laws.Slot.ballots(s, c, k), ds, k, name, to) == True{}: Bool
                  }
              )
          ),
        {
          RRounds.Slot.pass(
            Laws.Slot.ballots(
              Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t2}, x}),
              c,
              k
            ),
            ds,
            k,
            name
          )
            == None{}: Maybe<&2, RRounds.Draft>
        },
        Pass.next_to(Laws.Slot.ballots(s, c, k), ds, k, name, t, t2, x, sn)(ep),
        +to => w => Slot.passed_waits.to(s, name, c, k, ds, t2, x, t, sn, to, hl, held, w)
      )

# a node passes once: in the facts with its pass, read from the ballots of a
# slot, it casts no other pass for the slot, when the facts do not name it a
# liar. The pass is what Slot.pass gives, of the number that it gives
def Slot.passed_waits(
  +s: Facts.Facts(),
  +name: String,
  +c: Ledgers.Line,
  +k: Nat,
  +ds: List<&2, String>,
  +t: Nat,
  +x: Types.Cast
) -> {
  List.contains(~String, ~String.eq, Facts.Facts.liars(s), name) == False{}: Bool
} -> {
  RRounds.Slot.pass(
    Laws.Slot.ballots(s, c, k),
    ds,
    k,
    name
  )
    == Some{RRounds.Draft{t, x}}: Maybe<&2, RRounds.Draft>
} -> {
  RRounds.Slot.pass(
    Laws.Slot.ballots(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}), c, k),
    ds,
    k,
    name
  )
    == None{}: Maybe<&2, RRounds.Draft>
}:
  hl => ep => Slot.passed_waits.at(
    RRounds.Chain.reach(Laws.Slot.ballots(s, c, k), name),
    s,
    name,
    c,
    k,
    ds,
    t,
    x
  )(hl)(Laws.Chain.reach_held(Laws.Slot.ballots(s, c, k), name))(ep)

# After a vote
# ------------
# A node that cast a vote that counts in a round, and holds no ballot of a
# round above, waits: it passes to no round, and follows no lead. It may only
# lead the next round, when that is its turn.

# Chain.voted_floor, once what is known of the voter before its vote (sm) is
# known
def Chain.voted_floor.at(
  sm: Maybe<&2, RRounds.Seen>,
  +bs: List<&2, RRounds.Ballot>,
  +v: String,
  +u: Nat,
  +r: Nat,
  +p: Types.Pick,
  +ba: List<&2, Types.Ref>,
  +t: Nat,
  +m: RRounds.Seen
) -> {
  RRounds.Chain.seen(bs, v, u) == sm: Maybe<&2, RRounds.Seen>
} -> {
  RRounds.Seen.takes(r, sm) == True{}: Bool
} -> {
  RRounds.Ballots.at(bs, v, u) == Some{Types.Cast.Vote{r, p, ba}}: Maybe<&2, Types.Cast>
} -> {
  RRounds.Chain.seen(bs, v, t) == Some{m}: Maybe<&2, RRounds.Seen>
} -> {
  RRounds.Ballots.at(bs, v, t) == None{}: Maybe<&2, Types.Cast>
} -> {Nat.is_le(1n+r, RRounds.Seen.floor(m)) == True{}: Bool}:
  match sm:
    case None{}:
      es0 => hk => ha => es => hn => Empty.absurd(
        {Nat.is_le(1n+r, RRounds.Seen.floor(m)) == True{}: Bool},
        Shared.Bool.false_ne_true(hk)
      )
    case Some{RRounds.Seen{+fl, +vs}}:
      es0 => +hk => ha => es => hn => Shared.Nat.le_trans(
        1n+r,
        RRounds.Seen.floor(RRounds.Seen.step(RRounds.Seen{fl, vs}, Types.Cast.Vote{r, p, ba})),
        RRounds.Seen.floor(m)
      )((
          %Equal.sym(Bool, Nat.is_le(fl, r), True{}, hk): {Nat.is_le(1n+r, RRounds.Seen.floor(Bool.pick(RRounds.Seen, _, RRounds.Seen{1n+r, RRounds.Voted{r, p} <> vs}, RRounds.Seen{fl, vs}))) == True{}: Bool}
          Shared.Nat.le_refl(1n+r)))(
        Chain.floor_last(
          bs,
          v,
          1n+u,
          RRounds.Seen.step(RRounds.Seen{fl, vs}, Types.Cast.Vote{r, p, ba}),
          t,
          m
        )((
            %Equal.sym(Maybe<&2, RRounds.Seen>, RRounds.Chain.seen(bs, v, u), Some{RRounds.Seen{fl, vs}}, es0): {RRounds.Chain.seen.next(_, RRounds.Ballots.at(bs, v, u)) == Some{RRounds.Seen.step(RRounds.Seen{fl, vs}, Types.Cast.Vote{r, p, ba})}: Maybe<&2, RRounds.Seen>}
            %Equal.sym(Maybe<&2, Types.Cast>, RRounds.Ballots.at(bs, v, u), Some{Types.Cast.Vote{r, p, ba}}, ha): {RRounds.Chain.seen.next(Some{RRounds.Seen{fl, vs}}, _) == Some{RRounds.Seen.step(RRounds.Seen{fl, vs}, Types.Cast.Vote{r, p, ba})}: Maybe<&2, RRounds.Seen>}
            {==}))(es)(hn)
      )

# a voter with a vote that counts in the round r may vote in no round below
# the next one, where its ballots end
def Chain.voted_floor(
  +bs: List<&2, RRounds.Ballot>,
  +v: String,
  +r: Nat,
  +b: RRounds.Ballot,
  +t: Nat,
  +m: RRounds.Seen
) -> {
  RRounds.Vote.of(bs, v, r) == Some{b}: Maybe<&2, RRounds.Ballot>
} -> {
  RRounds.Chain.seen(bs, v, t) == Some{m}: Maybe<&2, RRounds.Seen>
} -> {
  RRounds.Ballots.at(bs, v, t) == None{}: Maybe<&2, Types.Cast>
} -> {Nat.is_le(1n+r, RRounds.Seen.floor(m)) == True{}: Bool}:
  e => es => hn => Laws.Ballot.counts_by(
    bb => {Nat.is_le(1n+r, RRounds.Seen.floor(m)) == True{}: Bool},
    bs,
    v,
    r,
    b
  )(
    Lists.List.pick_hit(
      ~RRounds.Ballot,
      ~RRounds.Roll,
      ~RRounds.Ballot.counts,
      bs,
      RRounds.Roll{bs, v, r},
      b
    )(e)
  )(
    +u => +p => +ba => hk => ha => Chain.voted_floor.at(
      RRounds.Chain.seen(bs, v, u),
      bs,
      v,
      u,
      r,
      p,
      ba,
      t,
      m
    )({==})(hk)(ha)(es)(hn)
  )

# Slot.voted_waits, once how far the ballots of the node are held (m) is
# known
def Slot.voted_waits.at(
  m: RRounds.Reach,
  +bs: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +name: String,
  +r: Nat,
  +b: RRounds.Ballot,
  e: {RRounds.Vote.of(bs, name, r) == Some{b}: Maybe<&2, RRounds.Ballot>},
  hle: {Nat.is_le(RRounds.Rounds.top(bs), r) == True{}: Bool},
  ha: {RRounds.Round.alive(bs, ds, k, name, RRounds.Rounds.top(bs)) == True{}: Bool},
  held: Laws.Reach.Held(bs, name, m)
) -> {Laws.Pass.next(bs, ds, k, name, m) == None{}: Maybe<&2, RRounds.Draft>}:
  match m:
    case RRounds.Reach{+t, +sn}:
      (es, hn) = held
      Laws.Slot.pass.at_waits(
        RRounds.Rounds.top(bs),
        RRounds.Round.alive(bs, ds, k, name, RRounds.Rounds.top(bs)),
        u => RRounds.Rounds.mine(List.length(&2, String, ds), ds, k, name, RRounds.Rounds.top(bs)),
        t,
        sn
      )(
        ha
      )(
        Shared.Nat.le_nlt(
          RRounds.Rounds.top(bs),
          RRounds.Seen.floor(sn)
        )(
          Shared.Nat.le_trans(
            RRounds.Rounds.top(bs),
            1n+r,
            RRounds.Seen.floor(sn)
          )(
            Shared.Nat.le_succ(RRounds.Rounds.top(bs), r)(hle)
          )(Chain.voted_floor(bs, name, r, b, t, sn)(e)(es)(hn))
        )
      )

# a node with a vote that counts in the round r casts no pass, while it holds
# no ballot of a round above r and the highest round is alive for it
def Slot.voted_waits(
  +bs: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +name: String,
  +r: Nat,
  +b: RRounds.Ballot
) -> {
  RRounds.Vote.of(bs, name, r) == Some{b}: Maybe<&2, RRounds.Ballot>
} -> {
  Nat.is_le(RRounds.Rounds.top(bs), r) == True{}: Bool
} -> {
  RRounds.Round.alive(bs, ds, k, name, RRounds.Rounds.top(bs)) == True{}: Bool
} -> {RRounds.Slot.pass(bs, ds, k, name) == None{}: Maybe<&2, RRounds.Draft>}:
  e => hle => ha => Slot.voted_waits.at(
    RRounds.Chain.reach(bs, name),
    bs,
    ds,
    k,
    name,
    r,
    b,
    e,
    hle,
    ha,
    Laws.Chain.reach_held(bs, name)
  )

# no sound lead of a round below r is followed by a voter that may vote in
# no round below fl, when r is below fl
def Minds.last.at_none(
  m: RRounds.Mind,
  +fl: Nat,
  +r: Nat
) -> {
  Nat.is_le(1n+r, fl) == True{}: Bool
} -> {RRounds.Minds.last.at(fl, r, None{}, m) == None{}: Maybe<&2, RRounds.Voted>}:
  match m:
    case RRounds.Mind.Open{}:
      h => {==}
    case RRounds.Mind.Void{}:
      h => {==}
    case RRounds.Mind.Sound{+p}:
      h => Lists.Bool.by(
        z => {
          Shared.Maybe.when(
            RRounds.Voted,
            z,
            u => Some{RRounds.Voted{r, p}}
          )
            == None{}: Maybe<&2, RRounds.Voted>
        },
        Nat.is_le(fl, r),
        et => Empty.absurd(
          {Some{RRounds.Voted{r, p}} == None{}: Maybe<&2, RRounds.Voted>},
          Safeties.Nat.above_not(r, fl)(h)(et)
        ),
        ef => {==}
      )

# a voter follows no lead of the rounds from r on, of the leads ms, when it
# may vote in none of them
def Minds.last_none(
  ms: List<&2, RRounds.Mind>,
  +fl: Nat,
  +r: Nat
) -> {
  Nat.is_le(Nat.add(List.length(&2, RRounds.Mind, ms), r), fl) == True{}: Bool
} -> {RRounds.Minds.last(ms, fl, r) == None{}: Maybe<&2, RRounds.Voted>}:
  match ms:
    case Nil{}:
      h => {==}
    case Con{m, +rest}:
      +h => (
        %Equal.sym(Maybe<&2, RRounds.Voted>, RRounds.Minds.last(rest, fl, 1n+r), None{}, Minds.last_none(rest, fl, 1n+r)((
            %Equal.sym(Nat, Nat.add(List.length(&2, RRounds.Mind, rest), 1n+r), 1n+Nat.add(List.length(&2, RRounds.Mind, rest), r), Shared.Nat.add_succ(List.length(&2, RRounds.Mind, rest), r)): {Nat.is_le(_, fl) == True{}: Bool}
            h))): {RRounds.Minds.last.at(fl, r, _, m) == None{}: Maybe<&2, RRounds.Voted>}
        Minds.last.at_none(m, fl, r)(Shared.Nat.le_trans(1n+r, 1n+Nat.add(List.length(&2, RRounds.Mind, rest), r), fl)(Shared.Nat.le_add(List.length(&2, RRounds.Mind, rest), r))(h)))

# a voter that may vote in no round of a ballot follows no sound lead: it
# votes only as its own chance to lead binds it
def Slot.follow.at_above(
  +bs: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +name: String,
  +t: Nat,
  +fl: Nat,
  +vs: List<&2, RRounds.Voted>
) -> {
  Nat.is_le(RRounds.Rounds.count(bs), fl) == True{}: Bool
} -> {
  RRounds.Slot.follow.at(
    bs,
    ds,
    k,
    name,
    RRounds.Reach{t, RRounds.Seen{fl, vs}}
  )
    == RRounds.Slot.follow.bound(
      RRounds.Slot.chance.at(bs, ds, k, name, RRounds.Reach{t, RRounds.Seen{fl, vs}})
    ): Maybe<&2, RRounds.Draft>
}:
  h => (
    %Equal.sym(Maybe<&2, RRounds.Voted>, RRounds.Minds.last(RRounds.Rounds.minds(bs, ds, k, RRounds.Rounds.count(bs)), fl, 0n), None{}, Minds.last_none(RRounds.Rounds.minds(bs, ds, k, RRounds.Rounds.count(bs)), fl, 0n)((
        %Equal.sym(Nat, Nat.add(List.length(&2, RRounds.Mind, RRounds.Rounds.minds(bs, ds, k, RRounds.Rounds.count(bs))), 0n), List.length(&2, RRounds.Mind, RRounds.Rounds.minds(bs, ds, k, RRounds.Rounds.count(bs))), Laws.Nat.add_zero(List.length(&2, RRounds.Mind, RRounds.Rounds.minds(bs, ds, k, RRounds.Rounds.count(bs))))): {Nat.is_le(_, fl) == True{}: Bool}
        %Equal.sym(Nat, List.length(&2, RRounds.Mind, RRounds.Rounds.minds(bs, ds, k, RRounds.Rounds.count(bs))), RRounds.Rounds.count(bs), Safeties.Minds.length(bs, ds, k, RRounds.Rounds.count(bs))): {Nat.is_le(_, fl) == True{}: Bool}
        h))): {RRounds.Slot.follow.of(t, _, u => RRounds.Slot.chance.at(bs, ds, k, name, RRounds.Reach{t, RRounds.Seen{fl, vs}})) == RRounds.Slot.follow.bound(RRounds.Slot.chance.at(bs, ds, k, name, RRounds.Reach{t, RRounds.Seen{fl, vs}})): Maybe<&2, RRounds.Draft>}
    {==})

# the lowest round that a voter may vote in after a cast is at most the round
# after m, when it was before, and the cast is of a round that is at most m
def Seen.step_under(
  m0: RRounds.Seen,
  c: Types.Cast,
  +m: Nat
) -> {
  Nat.is_le(RRounds.Seen.floor(m0), 1n+m) == True{}: Bool
} -> {
  Nat.is_le(RRounds.Cast.round(c), m) == True{}: Bool
} -> {Nat.is_le(RRounds.Seen.floor(RRounds.Seen.step(m0, c)), 1n+m) == True{}: Bool}:
  match m0 c:
    case RRounds.Seen{+fl, +vs} Types.Cast.Vote{+r, +p, b}:
      h => hr => Lists.Bool.by(
        z => {
          Nat.is_le(
            RRounds.Seen.floor(
              Bool.pick(
                RRounds.Seen,
                z,
                RRounds.Seen{1n+r, RRounds.Voted{r, p} <> vs},
                RRounds.Seen{fl, vs}
              )
            ),
            1n+m
          )
            == True{}: Bool
        },
        Nat.is_le(fl, r),
        et => hr,
        ef => h
      )
    case RRounds.Seen{+fl, +vs} Types.Cast.Pass{+r}:
      h => hr => Lists.Bool.by(
        z => {
          Nat.is_le(
            RRounds.Seen.floor(
              Bool.pick(RRounds.Seen, z, RRounds.Seen{r, vs}, RRounds.Seen{fl, vs})
            ),
            1n+m
          )
            == True{}: Bool
        },
        Nat.is_le(fl, r),
        et => Shared.Nat.le_succ(r, m)(hr),
        ef => h
      )

# the lowest round that a voter may vote in is at most the round after the
# highest round of a ballot
def Chain.floor_under(
  t: Nat,
  +bs: List<&2, RRounds.Ballot>,
  +v: String,
  -m: RRounds.Seen
) -> {
  RRounds.Chain.seen(bs, v, t) == Some{m}: Maybe<&2, RRounds.Seen>
} -> {Nat.is_le(RRounds.Seen.floor(m), 1n+RRounds.Rounds.top(bs)) == True{}: Bool}:
  match t:
    case 0n:
      e => (
        %Shared.Maybe.some_inj(RRounds.Seen, RRounds.Seen{0n, []}, m, e): {Nat.is_le(RRounds.Seen.floor(_), 1n+RRounds.Rounds.top(bs)) == True{}: Bool}
        {==})
    case 1n++j:
      e => Chain.seen.next_by(
        {Nat.is_le(RRounds.Seen.floor(m), 1n+RRounds.Rounds.top(bs)) == True{}: Bool},
        RRounds.Chain.seen(bs, v, j),
        RRounds.Ballots.at(bs, v, j),
        m
      )(e)(+m0 => +c => es0 => ex => e2 => (
          %e2: {Nat.is_le(RRounds.Seen.floor(_), 1n+RRounds.Rounds.top(bs)) == True{}: Bool}
          Seen.step_under(m0, c, RRounds.Rounds.top(bs))(Chain.floor_under(j, bs, v, m0)(es0))(Laws.Casts.of_top(bs, v, j, c)(Laws.Casts.agreed_in(RRounds.Casts.of(bs, Types.Ref{v, j}), c)(ex)))))

# Slot.voted_chance, where the ballots of the node are held as far as the
# number t
def Slot.voted_chance.at(
  +bs: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +name: String,
  +r: Nat,
  +b: RRounds.Ballot,
  +t: Nat,
  +fl: Nat,
  +vs: List<&2, RRounds.Voted>,
  +e: {RRounds.Vote.of(bs, name, r) == Some{b}: Maybe<&2, RRounds.Ballot>},
  +hle: {Nat.is_le(RRounds.Rounds.top(bs), r) == True{}: Bool},
  ht: {String.eq(RRounds.Turn.of(ds, Nat.add(k, 1n+r)), name) == False{}: Bool},
  held: Laws.Reach.Held(bs, name, RRounds.Reach{t, RRounds.Seen{fl, vs}})
) -> {
  RRounds.Slot.chance.at(
    bs,
    ds,
    k,
    name,
    RRounds.Reach{t, RRounds.Seen{fl, vs}}
  )
    == None{}: Maybe<&2, RRounds.Chance>
}
  & {Nat.is_le(1n+r, fl) == True{}: Bool}:
  (+es, +hn) = held
  ((
      %Equal.sym(Nat, Nat.max(fl, RRounds.Rounds.top(bs)), 1n+r, Equal.trans(Nat, Nat.max(fl, RRounds.Rounds.top(bs)), fl, 1n+r, Laws.Nat.max_above(fl, RRounds.Rounds.top(bs))(Shared.Nat.le_trans(RRounds.Rounds.top(bs), 1n+r, fl)(Shared.Nat.le_succ(RRounds.Rounds.top(bs), r)(hle))(Chain.voted_floor(bs, name, r, b, t, RRounds.Seen{fl, vs})(e)(es)(hn))), Nat.le_same(fl, 1n+r)(Shared.Nat.le_trans(fl, 1n+RRounds.Rounds.top(bs), 1n+r)(Chain.floor_under(t, bs, name, RRounds.Seen{fl, vs})(es))(hle))(Chain.voted_floor(bs, name, r, b, t, RRounds.Seen{fl, vs})(e)(es)(hn)))): {RRounds.Slot.chance.in(bs, ds, k, name, t, _) == None{}: Maybe<&2, RRounds.Chance>}
      %Equal.sym(Bool, String.eq(RRounds.Turn.of(ds, Nat.add(k, 1n+r)), name), False{}, ht): {Shared.Maybe.when(RRounds.Chance, _, u => RRounds.Slot.chance.of(RRounds.Lead{bs, 1n+r, name, t, RRounds.Basis.make(bs, name, 1n+r, ds), RRounds.Rounds.minds(bs, ds, k, 1n+r)}, ds)) == None{}: Maybe<&2, RRounds.Chance>}
      {==}), Chain.voted_floor(bs, name, r, b, t, RRounds.Seen{fl, vs})(e)(es)(hn))

# Slot.voted_quiet, with no chance to lead
def Slot.voted_quiet.fin(
  +bs: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +name: String,
  +r: Nat,
  +t: Nat,
  +fl: Nat,
  +vs: List<&2, RRounds.Voted>,
  hle: {Nat.is_le(RRounds.Rounds.top(bs), r) == True{}: Bool},
  w: {
    RRounds.Slot.chance.at(
      bs,
      ds,
      k,
      name,
      RRounds.Reach{t, RRounds.Seen{fl, vs}}
    )
      == None{}: Maybe<&2, RRounds.Chance>
  }
    & {Nat.is_le(1n+r, fl) == True{}: Bool}
) -> {
  RRounds.Slot.follow.at(
    bs,
    ds,
    k,
    name,
    RRounds.Reach{t, RRounds.Seen{fl, vs}}
  )
    == None{}: Maybe<&2, RRounds.Draft>
}
  & {
    RRounds.Slot.chance.at(
      bs,
      ds,
      k,
      name,
      RRounds.Reach{t, RRounds.Seen{fl, vs}}
    )
      == None{}: Maybe<&2, RRounds.Chance>
  }:
  (+ec, hf) = w
  (
    Equal.trans(
      Maybe<&2, RRounds.Draft>,
      RRounds.Slot.follow.at(bs, ds, k, name, RRounds.Reach{t, RRounds.Seen{fl, vs}}),
      RRounds.Slot.follow.bound(
        RRounds.Slot.chance.at(bs, ds, k, name, RRounds.Reach{t, RRounds.Seen{fl, vs}})
      ),
      None{},
      Slot.follow.at_above(
        bs,
        ds,
        k,
        name,
        t,
        fl,
        vs
      )(Shared.Nat.le_trans(1n+RRounds.Rounds.top(bs), 1n+r, fl)(hle)(hf)),
      (
        %Equal.sym(Maybe<&2, RRounds.Chance>, RRounds.Slot.chance.at(bs, ds, k, name, RRounds.Reach{t, RRounds.Seen{fl, vs}}), None{}, ec): {RRounds.Slot.follow.bound(_) == None{}: Maybe<&2, RRounds.Draft>}
        {==})
    ),
    ec
  )

# Slot.voted_quiet, once how far the ballots of the node are held (m) is
# known
def Slot.voted_quiet.at(
  m: RRounds.Reach,
  +bs: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +name: String,
  +r: Nat,
  +b: RRounds.Ballot,
  +e: {RRounds.Vote.of(bs, name, r) == Some{b}: Maybe<&2, RRounds.Ballot>},
  +hle: {Nat.is_le(RRounds.Rounds.top(bs), r) == True{}: Bool},
  ht: {String.eq(RRounds.Turn.of(ds, Nat.add(k, 1n+r)), name) == False{}: Bool},
  held: Laws.Reach.Held(bs, name, m)
) -> {
  RRounds.Slot.follow.at(bs, ds, k, name, m) == None{}: Maybe<&2, RRounds.Draft>
}
  & {RRounds.Slot.chance.at(bs, ds, k, name, m) == None{}: Maybe<&2, RRounds.Chance>}:
  match m:
    case RRounds.Reach{+t, RRounds.Seen{+fl, +vs}}:
      Slot.voted_quiet.fin(
        bs,
        ds,
        k,
        name,
        r,
        t,
        fl,
        vs,
        hle,
        Slot.voted_chance.at(bs, ds, k, name, r, b, t, fl, vs, e, hle, ht, held)
      )

# a node with a vote that counts in the round r, that holds no ballot of a
# round above r, casts no ballot for the slot while the highest round is
# alive for it, when the next round is not its turn: no pass, no vote as a
# lead, and it has no chance to lead
def Slot.voted_quiet(
  +bs: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +name: String,
  +r: Nat,
  +b: RRounds.Ballot
) -> {
  RRounds.Vote.of(bs, name, r) == Some{b}: Maybe<&2, RRounds.Ballot>
} -> {
  Nat.is_le(RRounds.Rounds.top(bs), r) == True{}: Bool
} -> {
  RRounds.Round.alive(bs, ds, k, name, RRounds.Rounds.top(bs)) == True{}: Bool
} -> {
  String.eq(RRounds.Turn.of(ds, Nat.add(k, 1n+r)), name) == False{}: Bool
} -> {
  RRounds.Slot.pass(bs, ds, k, name) == None{}: Maybe<&2, RRounds.Draft>
}
  & (
    {
      RRounds.Slot.follow(bs, ds, k, name) == None{}: Maybe<&2, RRounds.Draft>
    }
      & {RRounds.Slot.chance(bs, ds, k, name) == None{}: Maybe<&2, RRounds.Chance>}
  ):
  +e => +hle => ha => ht => (
    Slot.voted_waits(bs, ds, k, name, r, b)(e)(hle)(ha),
    Slot.voted_quiet.at(
      RRounds.Chain.reach(bs, name),
      bs,
      ds,
      k,
      name,
      r,
      b,
      e,
      hle,
      ht,
      Laws.Chain.reach_held(bs, name)
    )
  )

# Following
# ---------
# A node votes as the sound lead of the highest round, when it may still
# vote in that round; its vote then counts, and the lead stays sound.

# a voter that may vote in the round of the last of the leads, a sound one,
# follows it
def Minds.last_top(
  ms: List<&2, RRounds.Mind>,
  +p: Types.Pick,
  +fl: Nat,
  +r0: Nat
) -> {
  Nat.is_le(fl, Nat.add(List.length(&2, RRounds.Mind, ms), r0)) == True{}: Bool
} -> {
  RRounds.Minds.last(
    List.append(&2, RRounds.Mind, ms, [RRounds.Mind.Sound{p}]),
    fl,
    r0
  )
    == Some{
      RRounds.Voted{Nat.add(List.length(&2, RRounds.Mind, ms), r0), p}
    }: Maybe<&2, RRounds.Voted>
}:
  match ms:
    case Nil{}:
      h => (
        %Equal.sym(Bool, Nat.is_le(fl, r0), True{}, h): {Shared.Maybe.when(RRounds.Voted, _, u => Some{RRounds.Voted{r0, p}}) == Some{RRounds.Voted{r0, p}}: Maybe<&2, RRounds.Voted>}
        {==})
    case Con{m, +rest}:
      h => (
        %Equal.sym(Maybe<&2, RRounds.Voted>, RRounds.Minds.last(List.append(&2, RRounds.Mind, rest, [RRounds.Mind.Sound{p}]), fl, 1n+r0), Some{RRounds.Voted{Nat.add(List.length(&2, RRounds.Mind, rest), 1n+r0), p}}, Minds.last_top(rest, p, fl, 1n+r0)((
            %Equal.sym(Nat, Nat.add(List.length(&2, RRounds.Mind, rest), 1n+r0), 1n+Nat.add(List.length(&2, RRounds.Mind, rest), r0), Shared.Nat.add_succ(List.length(&2, RRounds.Mind, rest), r0)): {Nat.is_le(fl, _) == True{}: Bool}
            h))): {RRounds.Minds.last.at(fl, r0, _, m) == Some{RRounds.Voted{1n+Nat.add(List.length(&2, RRounds.Mind, rest), r0), p}}: Maybe<&2, RRounds.Voted>}
        %Equal.sym(Nat, Nat.add(List.length(&2, RRounds.Mind, rest), 1n+r0), 1n+Nat.add(List.length(&2, RRounds.Mind, rest), r0), Shared.Nat.add_succ(List.length(&2, RRounds.Mind, rest), r0)): {Some{RRounds.Voted{_, p}} == Some{RRounds.Voted{1n+Nat.add(List.length(&2, RRounds.Mind, rest), r0), p}}: Maybe<&2, RRounds.Voted>}
        {==})

# a voter that may vote in the highest round r of a ballot follows its lead,
# when that is sound
def Minds.last_lead(
  +bs: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +r: Nat,
  +p: Types.Pick,
  +fl: Nat
) -> {
  RRounds.Rounds.top(bs) == r: Nat
} -> {
  Laws.Round.mind(bs, ds, k, r) == RRounds.Mind.Sound{p}: RRounds.Mind
} -> {
  Nat.is_le(fl, r) == True{}: Bool
} -> {
  RRounds.Minds.last(
    RRounds.Rounds.minds(bs, ds, k, RRounds.Rounds.count(bs)),
    fl,
    0n
  )
    == Some{RRounds.Voted{r, p}}: Maybe<&2, RRounds.Voted>
}:
  etop => em => h => (
    %Equal.sym(Nat, RRounds.Rounds.top(bs), r, etop): {RRounds.Minds.last(RRounds.Rounds.minds(bs, ds, k, 1n+_), fl, 0n) == Some{RRounds.Voted{r, p}}: Maybe<&2, RRounds.Voted>}
    %Equal.sym(RRounds.Mind, Laws.Round.mind(bs, ds, k, r), RRounds.Mind.Sound{p}, em): {RRounds.Minds.last(List.append(&2, RRounds.Mind, RRounds.Rounds.minds(bs, ds, k, r), [_]), fl, 0n) == Some{RRounds.Voted{r, p}}: Maybe<&2, RRounds.Voted>}
    Lists.Equal.to(Nat, n => {RRounds.Minds.last(List.append(&2, RRounds.Mind, RRounds.Rounds.minds(bs, ds, k, r), [RRounds.Mind.Sound{p}]), fl, 0n) == Some{RRounds.Voted{n, p}}: Maybe<&2, RRounds.Voted>}, Nat.add(List.length(&2, RRounds.Mind, RRounds.Rounds.minds(bs, ds, k, r)), 0n), r, Equal.trans(Nat, Nat.add(List.length(&2, RRounds.Mind, RRounds.Rounds.minds(bs, ds, k, r)), 0n), List.length(&2, RRounds.Mind, RRounds.Rounds.minds(bs, ds, k, r)), r, Laws.Nat.add_zero(List.length(&2, RRounds.Mind, RRounds.Rounds.minds(bs, ds, k, r))), Safeties.Minds.length(bs, ds, k, r)), Minds.last_top(RRounds.Rounds.minds(bs, ds, k, r), p, fl, 0n)(Lists.Equal.to(Nat, n => {Nat.is_le(fl, n) == True{}: Bool}, r, Nat.add(List.length(&2, RRounds.Mind, RRounds.Rounds.minds(bs, ds, k, r)), 0n), Equal.sym(Nat, Nat.add(List.length(&2, RRounds.Mind, RRounds.Rounds.minds(bs, ds, k, r)), 0n), r, Equal.trans(Nat, Nat.add(List.length(&2, RRounds.Mind, RRounds.Rounds.minds(bs, ds, k, r)), 0n), List.length(&2, RRounds.Mind, RRounds.Rounds.minds(bs, ds, k, r)), r, Laws.Nat.add_zero(List.length(&2, RRounds.Mind, RRounds.Rounds.minds(bs, ds, k, r))), Safeties.Minds.length(bs, ds, k, r))), h))))

# a node votes as the sound lead of the highest round r of a ballot, when it
# may still vote in r: with its next ballot, for the pick of the lead
def Slot.follow_lead(
  +bs: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +name: String,
  +r: Nat,
  +p: Types.Pick,
  +t: Nat,
  +fl: Nat,
  +vs: List<&2, RRounds.Voted>
) -> {
  RRounds.Rounds.top(bs) == r: Nat
} -> {
  Laws.Round.mind(bs, ds, k, r) == RRounds.Mind.Sound{p}: RRounds.Mind
} -> {
  RRounds.Chain.reach(bs, name) == RRounds.Reach{t, RRounds.Seen{fl, vs}}: RRounds.Reach
} -> {
  Nat.is_le(fl, r) == True{}: Bool
} -> {
  RRounds.Slot.follow(
    bs,
    ds,
    k,
    name
  )
    == Some{RRounds.Draft{t, Types.Cast.Vote{r, p, []}}}: Maybe<&2, RRounds.Draft>
}:
  etop => em => er => h => (
    %Equal.sym(RRounds.Reach, RRounds.Chain.reach(bs, name), RRounds.Reach{t, RRounds.Seen{fl, vs}}, er): {RRounds.Slot.follow.at(bs, ds, k, name, _) == Some{RRounds.Draft{t, Types.Cast.Vote{r, p, []}}}: Maybe<&2, RRounds.Draft>}
    %Equal.sym(Maybe<&2, RRounds.Voted>, RRounds.Minds.last(RRounds.Rounds.minds(bs, ds, k, RRounds.Rounds.count(bs)), fl, 0n), Some{RRounds.Voted{r, p}}, Minds.last_lead(bs, ds, k, r, p, fl)(etop)(em)(h)): {RRounds.Slot.follow.of(t, _, u => RRounds.Slot.chance.at(bs, ds, k, name, RRounds.Reach{t, RRounds.Seen{fl, vs}})) == Some{RRounds.Draft{t, Types.Cast.Vote{r, p, []}}}: Maybe<&2, RRounds.Draft>}
    {==})

# a lead that is no less known than a sound one is sound for the same pick
def Mind.sound_le(
  b: RRounds.Mind,
  +p: Types.Pick
) -> {
  Laws.Mind.le(RRounds.Mind.Sound{p}, b) == True{}: Bool
} -> {b == RRounds.Mind.Sound{p}: RRounds.Mind}:
  match b:
    case RRounds.Mind.Open{}:
      h => Empty.absurd(
        {RRounds.Mind.Open{} == RRounds.Mind.Sound{p}: RRounds.Mind},
        Shared.Bool.false_ne_true(h)
      )
    case RRounds.Mind.Void{}:
      h => Empty.absurd(
        {RRounds.Mind.Void{} == RRounds.Mind.Sound{p}: RRounds.Mind},
        Shared.Bool.false_ne_true(h)
      )
    case RRounds.Mind.Sound{+q}:
      h => (
        %Coded.Pick.is_eq_sound(p, q)(h): {RRounds.Mind.Sound{_} == RRounds.Mind.Sound{p}: RRounds.Mind}
        {==})

# a sound lead stays sound, for its pick, as the ballots grow
def Round.sound_grows(
  +bs: List<&2, RRounds.Ballot>,
  +bs2: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +r: Nat,
  +p: Types.Pick
) -> {
  Laws.Ballots.grown(bs, bs2) == True{}: Bool
} -> {
  Laws.Round.mind(bs, ds, k, r) == RRounds.Mind.Sound{p}: RRounds.Mind
} -> {Laws.Round.mind(bs2, ds, k, r) == RRounds.Mind.Sound{p}: RRounds.Mind}:
  hg => em => Mind.sound_le(Laws.Round.mind(bs2, ds, k, r), p)((
      %em: {Laws.Mind.le(_, Laws.Round.mind(bs2, ds, k, r)) == True{}: Bool}
      Laws.Round.mind_grows(bs, bs2, ds, k, r)(hg)))

# the first vote of a node for a step of a slot counts for its pick, when
# the node may vote in its round
def Slot.added_counts(
  +s: Facts.Facts(),
  +name: String,
  +c: Ledgers.Line,
  +k: Nat,
  +r: Nat,
  +p: Types.Pick,
  +t: Nat,
  +fl: Nat,
  +vs: List<&2, RRounds.Voted>,
  +hc: {Facts.Facts.cast(s, name, Types.Step.At{c, k, t}) == False{}: Bool},
  es: {
    RRounds.Chain.seen(
      Laws.Slot.ballots(s, c, k),
      name,
      t
    )
      == Some{RRounds.Seen{fl, vs}}: Maybe<&2, RRounds.Seen>
  },
  h: {Nat.is_le(fl, r) == True{}: Bool}
) -> {
  RRounds.Tally.voted(
    RRounds.Tally{
      Laws.Slot.ballots(
        Facts.Facts.add(
          s,
          Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Vote{r, p, []}}
        ),
        c,
        k
      ),
      r,
      p
    },
    name
  )
    == True{}: Bool
}:
  %Equal.sym(
    Maybe<&2, RRounds.Ballot>,
    RRounds.Vote.of(
      Laws.Slot.ballots(
        Facts.Facts.add(
          s,
          Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Vote{r, p, []}}
        ),
        c,
        k
      ),
      name,
      r
    ),
    Some{RRounds.Ballot{name, t, Types.Cast.Vote{r, p, []}}},
    Laws.Vote.of_counted(
      Laws.Slot.ballots(
        Facts.Facts.add(
          s,
          Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Vote{r, p, []}}
        ),
        c,
        k
      ),
      name,
      r,
      t,
      p,
      [],
      (
        %Equal.sym(Maybe<&2, RRounds.Seen>, RRounds.Chain.seen(Laws.Slot.ballots(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Vote{r, p, []}}), c, k), name, t), Some{RRounds.Seen{fl, vs}}, Laws.Chain.seen_grows(Laws.Slot.ballots(s, c, k), Laws.Slot.ballots(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Vote{r, p, []}}), c, k), name, t, RRounds.Seen{fl, vs}, Laws.Slot.added_grown(s, name, c, k, t, Types.Cast.Vote{r, p, []}, hc))(es)): {RRounds.Seen.takes(r, _) == True{}: Bool}
        h),
      Laws.Slot.added_at(s, name, c, k, t, Types.Cast.Vote{r, p, []}, hc)
    )
  ): {RRounds.Vote.is_for(p, _) == True{}: Bool}
  Coded.Pick.is_eq_refl(p)

# Slot.follower_votes, where the ballots of the node are held as far as the
# number t
def Slot.follower_votes.fin(
  +s: Facts.Facts(),
  +name: String,
  +c: Ledgers.Line,
  +k: Nat,
  +ds: List<&2, String>,
  +r: Nat,
  +p: Types.Pick,
  +t: Nat,
  +fl: Nat,
  +vs: List<&2, RRounds.Voted>,
  +hl: {List.contains(~String, ~String.eq, Facts.Facts.liars(s), name) == False{}: Bool},
  etop: {RRounds.Rounds.top(Laws.Slot.ballots(s, c, k)) == r: Nat},
  +em: {
    Laws.Round.mind(Laws.Slot.ballots(s, c, k), ds, k, r) == RRounds.Mind.Sound{p}: RRounds.Mind
  },
  er: {
    RRounds.Chain.reach(
      Laws.Slot.ballots(s, c, k),
      name
    )
      == RRounds.Reach{t, RRounds.Seen{fl, vs}}: RRounds.Reach
  },
  +h: {Nat.is_le(fl, r) == True{}: Bool},
  held: Laws.Reach.Held(Laws.Slot.ballots(s, c, k), name, RRounds.Reach{t, RRounds.Seen{fl, vs}})
) -> {
  RRounds.Slot.follow(
    Laws.Slot.ballots(s, c, k),
    ds,
    k,
    name
  )
    == Some{RRounds.Draft{t, Types.Cast.Vote{r, p, []}}}: Maybe<&2, RRounds.Draft>
}
  & (
    {
      RRounds.Tally.voted(
        RRounds.Tally{
          Laws.Slot.ballots(
            Facts.Facts.add(
              s,
              Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Vote{r, p, []}}
            ),
            c,
            k
          ),
          r,
          p
        },
        name
      )
        == True{}: Bool
    }
      & {
        Laws.Round.mind(
          Laws.Slot.ballots(
            Facts.Facts.add(
              s,
              Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Vote{r, p, []}}
            ),
            c,
            k
          ),
          ds,
          k,
          r
        )
          == RRounds.Mind.Sound{p}: RRounds.Mind
      }
  ):
  (es, +hn) = held
  (
    Slot.follow_lead(Laws.Slot.ballots(s, c, k), ds, k, name, r, p, t, fl, vs)(etop)(em)(er)(h),
    (
      Slot.added_counts(
        s,
        name,
        c,
        k,
        r,
        p,
        t,
        fl,
        vs,
        Laws.Slot.cast_none(s, name, c, k, t, hl, hn),
        es,
        h
      ),
      Round.sound_grows(
        Laws.Slot.ballots(s, c, k),
        Laws.Slot.ballots(
          Facts.Facts.add(
            s,
            Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Vote{r, p, []}}
          ),
          c,
          k
        ),
        ds,
        k,
        r,
        p
      )(
        Laws.Slot.added_grown(
          s,
          name,
          c,
          k,
          t,
          Types.Cast.Vote{r, p, []},
          Laws.Slot.cast_none(s, name, c, k, t, hl, hn)
        )
      )(em)
    )
  )

# a follower votes, and its vote counts: where the facts of a node hold a
# sound lead of the highest round r of a ballot of a slot, for the pick p, and
# the node may still vote in r (it cast no vote in r, and no pass to a round
# above), it votes for p in r with its next ballot; in the facts with that
# vote, the vote counts for p, and the lead is still sound, when the facts do
# not name the node a liar
def Slot.follower_votes(
  +s: Facts.Facts(),
  +name: String,
  +c: Ledgers.Line,
  +k: Nat,
  +ds: List<&2, String>,
  +r: Nat,
  +p: Types.Pick,
  +t: Nat,
  +fl: Nat,
  +vs: List<&2, RRounds.Voted>
) -> {
  List.contains(~String, ~String.eq, Facts.Facts.liars(s), name) == False{}: Bool
} -> {
  RRounds.Rounds.top(Laws.Slot.ballots(s, c, k)) == r: Nat
} -> {
  Laws.Round.mind(Laws.Slot.ballots(s, c, k), ds, k, r) == RRounds.Mind.Sound{p}: RRounds.Mind
} -> {
  RRounds.Chain.reach(
    Laws.Slot.ballots(s, c, k),
    name
  )
    == RRounds.Reach{t, RRounds.Seen{fl, vs}}: RRounds.Reach
} -> {
  Nat.is_le(fl, r) == True{}: Bool
} -> {
  RRounds.Slot.follow(
    Laws.Slot.ballots(s, c, k),
    ds,
    k,
    name
  )
    == Some{RRounds.Draft{t, Types.Cast.Vote{r, p, []}}}: Maybe<&2, RRounds.Draft>
}
  & (
    {
      RRounds.Tally.voted(
        RRounds.Tally{
          Laws.Slot.ballots(
            Facts.Facts.add(
              s,
              Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Vote{r, p, []}}
            ),
            c,
            k
          ),
          r,
          p
        },
        name
      )
        == True{}: Bool
    }
      & {
        Laws.Round.mind(
          Laws.Slot.ballots(
            Facts.Facts.add(
              s,
              Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Vote{r, p, []}}
            ),
            c,
            k
          ),
          ds,
          k,
          r
        )
          == RRounds.Mind.Sound{p}: RRounds.Mind
      }
  ):
  hl => etop => em => +er => h => Slot.follower_votes.fin(
    s,
    name,
    c,
    k,
    ds,
    r,
    p,
    t,
    fl,
    vs,
    hl,
    etop,
    em,
    er,
    h,
    Lists.Equal.to(
      RRounds.Reach,
      z => Laws.Reach.Held(Laws.Slot.ballots(s, c, k), name, z),
      RRounds.Chain.reach(Laws.Slot.ballots(s, c, k), name),
      RRounds.Reach{t, RRounds.Seen{fl, vs}},
      er,
      Laws.Chain.reach_held(Laws.Slot.ballots(s, c, k), name)
    )
  )

# Leading
# -------
# The vote that a node casts from its chance to lead a round is a sound lead
# in its facts: the others may follow it.

# the chance ch of the node name to lead a round of the slot k among bs,
# where the nodes ds decide, is sure: the round is its turn, more than half
# of the nodes gave it a promise, the force is what they leave it, a vote of
# the round counts as its next ballot, and bs holds no ballot of its with
# that number
def Chance.Sure(
  bs: List<&2, RRounds.Ballot>,
  ds: List<&2, String>,
  k: Nat,
  name: String,
  ch: RRounds.Chance
) -> Type:
  match ch:
    case RRounds.Chance{t, r, basis, f}:
      {
        String.eq(RRounds.Turn.of(ds, Nat.add(k, r)), name) == True{}: Bool
      }
        & (
          {
            RRounds.Lead.most(
              RRounds.Lead{bs, r, name, t, basis, RRounds.Rounds.minds(bs, ds, k, r)},
              ds
            )
              == True{}: Bool
          }
            & (
              {
                RRounds.Lead.force(
                  RRounds.Lead{bs, r, name, t, basis, RRounds.Rounds.minds(bs, ds, k, r)},
                  ds
                )
                  == f: RRounds.Force
              }
                & (
                  {
                    RRounds.Seen.takes(r, RRounds.Chain.seen(bs, name, t)) == True{}: Bool
                  }
                    & {RRounds.Ballots.at(bs, name, t) == None{}: Maybe<&2, Types.Cast>}
                )
            )
        )

# Slot.chance_sure, for the chance that the code builds
def Slot.chance_sure.fin(
  +bs: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +name: String,
  +t0: Nat,
  +fl: Nat,
  +vs: List<&2, RRounds.Voted>,
  et: {
    String.eq(
      RRounds.Turn.of(ds, Nat.add(k, Nat.max(fl, RRounds.Rounds.top(bs)))),
      name
    )
      == True{}: Bool
  },
  em: {
    RRounds.Lead.most(
      RRounds.Lead{
        bs,
        Nat.max(fl, RRounds.Rounds.top(bs)),
        name,
        t0,
        RRounds.Basis.make(bs, name, Nat.max(fl, RRounds.Rounds.top(bs)), ds),
        RRounds.Rounds.minds(bs, ds, k, Nat.max(fl, RRounds.Rounds.top(bs)))
      },
      ds
    )
      == True{}: Bool
  },
  held: Laws.Reach.Held(bs, name, RRounds.Reach{t0, RRounds.Seen{fl, vs}})
) -> Chance.Sure(
  bs,
  ds,
  k,
  name,
  RRounds.Chance{
    t0,
    Nat.max(fl, RRounds.Rounds.top(bs)),
    RRounds.Basis.make(bs, name, Nat.max(fl, RRounds.Rounds.top(bs)), ds),
    RRounds.Lead.force(
      RRounds.Lead{
        bs,
        Nat.max(fl, RRounds.Rounds.top(bs)),
        name,
        t0,
        RRounds.Basis.make(bs, name, Nat.max(fl, RRounds.Rounds.top(bs)), ds),
        RRounds.Rounds.minds(bs, ds, k, Nat.max(fl, RRounds.Rounds.top(bs)))
      },
      ds
    )
  }
):
  (es, hn) = held
  (et, (em, ({==}, ((
            %Equal.sym(Maybe<&2, RRounds.Seen>, RRounds.Chain.seen(bs, name, t0), Some{RRounds.Seen{fl, vs}}, es): {RRounds.Seen.takes(Nat.max(fl, RRounds.Rounds.top(bs)), _) == True{}: Bool}
            Lists.Nat.le_max_left(fl, RRounds.Rounds.top(bs))), hn))))

# Slot.chance_sure, once how far the ballots of the node are held (m) is
# known
def Slot.chance_sure.at(
  m: RRounds.Reach,
  +bs: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +name: String,
  +ch: RRounds.Chance
) -> Laws.Reach.Held(
  bs,
  name,
  m
) -> {
  RRounds.Slot.chance.at(bs, ds, k, name, m) == Some{ch}: Maybe<&2, RRounds.Chance>
} -> Chance.Sure(bs, ds, k, name, ch):
  match m:
    case RRounds.Reach{+t0, RRounds.Seen{+fl, +vs}}:
      held => Lists.Bool.by(
        z => {
          Shared.Maybe.when(
            RRounds.Chance,
            z,
            u => RRounds.Slot.chance.of(
              RRounds.Lead{
                bs,
                Nat.max(fl, RRounds.Rounds.top(bs)),
                name,
                t0,
                RRounds.Basis.make(bs, name, Nat.max(fl, RRounds.Rounds.top(bs)), ds),
                RRounds.Rounds.minds(bs, ds, k, Nat.max(fl, RRounds.Rounds.top(bs)))
              },
              ds
            )
          )
            == Some{ch}: Maybe<&2, RRounds.Chance>
        } -> Chance.Sure(bs, ds, k, name, ch),
        String.eq(RRounds.Turn.of(ds, Nat.add(k, Nat.max(fl, RRounds.Rounds.top(bs)))), name),
        et => Lists.Bool.by(
          z => {
            Shared.Maybe.when(
              RRounds.Chance,
              z,
              u => Some{
                RRounds.Chance{
                  t0,
                  Nat.max(fl, RRounds.Rounds.top(bs)),
                  RRounds.Basis.make(bs, name, Nat.max(fl, RRounds.Rounds.top(bs)), ds),
                  RRounds.Lead.force(
                    RRounds.Lead{
                      bs,
                      Nat.max(fl, RRounds.Rounds.top(bs)),
                      name,
                      t0,
                      RRounds.Basis.make(bs, name, Nat.max(fl, RRounds.Rounds.top(bs)), ds),
                      RRounds.Rounds.minds(bs, ds, k, Nat.max(fl, RRounds.Rounds.top(bs)))
                    },
                    ds
                  )
                }
              }
            )
              == Some{ch}: Maybe<&2, RRounds.Chance>
          } -> Chance.Sure(bs, ds, k, name, ch),
          RRounds.Lead.most(
            RRounds.Lead{
              bs,
              Nat.max(fl, RRounds.Rounds.top(bs)),
              name,
              t0,
              RRounds.Basis.make(bs, name, Nat.max(fl, RRounds.Rounds.top(bs)), ds),
              RRounds.Rounds.minds(bs, ds, k, Nat.max(fl, RRounds.Rounds.top(bs)))
            },
            ds
          ),
          em => e => Lists.Equal.to(
            RRounds.Chance,
            z => Chance.Sure(bs, ds, k, name, z),
            RRounds.Chance{
              t0,
              Nat.max(fl, RRounds.Rounds.top(bs)),
              RRounds.Basis.make(bs, name, Nat.max(fl, RRounds.Rounds.top(bs)), ds),
              RRounds.Lead.force(
                RRounds.Lead{
                  bs,
                  Nat.max(fl, RRounds.Rounds.top(bs)),
                  name,
                  t0,
                  RRounds.Basis.make(bs, name, Nat.max(fl, RRounds.Rounds.top(bs)), ds),
                  RRounds.Rounds.minds(bs, ds, k, Nat.max(fl, RRounds.Rounds.top(bs)))
                },
                ds
              )
            },
            ch,
            Shared.Maybe.some_inj(
              RRounds.Chance,
              RRounds.Chance{
                t0,
                Nat.max(fl, RRounds.Rounds.top(bs)),
                RRounds.Basis.make(bs, name, Nat.max(fl, RRounds.Rounds.top(bs)), ds),
                RRounds.Lead.force(
                  RRounds.Lead{
                    bs,
                    Nat.max(fl, RRounds.Rounds.top(bs)),
                    name,
                    t0,
                    RRounds.Basis.make(bs, name, Nat.max(fl, RRounds.Rounds.top(bs)), ds),
                    RRounds.Rounds.minds(bs, ds, k, Nat.max(fl, RRounds.Rounds.top(bs)))
                  },
                  ds
                )
              },
              ch,
              e
            ),
            Slot.chance_sure.fin(bs, ds, k, name, t0, fl, vs, et, em, held)
          ),
          em => e => Empty.absurd(
            Chance.Sure(bs, ds, k, name, ch),
            Shared.Maybe.none_ne_some(RRounds.Chance, ch, e)
          )
        ),
        et => e => Empty.absurd(
          Chance.Sure(bs, ds, k, name, ch),
          Shared.Maybe.none_ne_some(RRounds.Chance, ch, e)
        )
      )

# the chance that a node has to lead a round is sure
def Slot.chance_sure(
  +bs: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +name: String,
  +ch: RRounds.Chance
) -> {
  RRounds.Slot.chance(bs, ds, k, name) == Some{ch}: Maybe<&2, RRounds.Chance>
} -> Chance.Sure(bs, ds, k, name, ch):
  e => Slot.chance_sure.at(
    RRounds.Chain.reach(bs, name),
    bs,
    ds,
    k,
    name,
    ch
  )(Laws.Chain.reach_held(bs, name))(e)

# Slot.lead_sound, before the vote: the lead is sound among the ballots
# that the node holds
def Slot.lead_sound.was(
  +s: Facts.Facts(),
  +name: String,
  +c: Ledgers.Line,
  +k: Nat,
  +ds: List<&2, String>,
  +t: Nat,
  +r: Nat,
  +basis: List<&2, Types.Ref>,
  +f: RRounds.Force,
  +p: Types.Pick,
  ef: {RRounds.Lead.mind.of(p, f, True{}) == RRounds.Mind.Sound{p}: RRounds.Mind},
  em: {
    RRounds.Lead.most(
      RRounds.Lead{
        Laws.Slot.ballots(s, c, k),
        r,
        name,
        t,
        basis,
        RRounds.Rounds.minds(Laws.Slot.ballots(s, c, k), ds, k, r)
      },
      ds
    )
      == True{}: Bool
  },
  efo: {
    RRounds.Lead.force(
      RRounds.Lead{
        Laws.Slot.ballots(s, c, k),
        r,
        name,
        t,
        basis,
        RRounds.Rounds.minds(Laws.Slot.ballots(s, c, k), ds, k, r)
      },
      ds
    )
      == f: RRounds.Force
  }
) -> {
  RRounds.Lead.mind.at(
    Laws.Slot.ballots(s, c, k),
    ds,
    RRounds.Rounds.minds(Laws.Slot.ballots(s, c, k), ds, k, r),
    r,
    name,
    Some{RRounds.Ballot{name, t, Types.Cast.Vote{r, p, basis}}}
  )
    == RRounds.Mind.Sound{p}: RRounds.Mind
}:
  %Equal.sym(
    Bool,
    RRounds.Lead.most(
      RRounds.Lead{
        Laws.Slot.ballots(s, c, k),
        r,
        name,
        t,
        basis,
        RRounds.Rounds.minds(Laws.Slot.ballots(s, c, k), ds, k, r)
      },
      ds
    ),
    True{},
    em
  ): {
    RRounds.Lead.mind.of(
      p,
      RRounds.Lead.force(
        RRounds.Lead{
          Laws.Slot.ballots(s, c, k),
          r,
          name,
          t,
          basis,
          RRounds.Rounds.minds(Laws.Slot.ballots(s, c, k), ds, k, r)
        },
        ds
      ),
      _
    )
      == RRounds.Mind.Sound{p}: RRounds.Mind
  }
  %Equal.sym(
    RRounds.Force,
    RRounds.Lead.force(
      RRounds.Lead{
        Laws.Slot.ballots(s, c, k),
        r,
        name,
        t,
        basis,
        RRounds.Rounds.minds(Laws.Slot.ballots(s, c, k), ds, k, r)
      },
      ds
    ),
    f,
    efo
  ): {RRounds.Lead.mind.of(p, _, True{}) == RRounds.Mind.Sound{p}: RRounds.Mind}
  ef

# Slot.lead_sound, with what makes the chance sure
def Slot.lead_sound.end(
  +s: Facts.Facts(),
  +name: String,
  +c: Ledgers.Line,
  +k: Nat,
  +ds: List<&2, String>,
  +t: Nat,
  +r: Nat,
  +basis: List<&2, Types.Ref>,
  +f: RRounds.Force,
  +p: Types.Pick,
  +hl: {List.contains(~String, ~String.eq, Facts.Facts.liars(s), name) == False{}: Bool},
  ef: {RRounds.Lead.mind.of(p, f, True{}) == RRounds.Mind.Sound{p}: RRounds.Mind},
  et: {String.eq(RRounds.Turn.of(ds, Nat.add(k, r)), name) == True{}: Bool},
  em: {
    RRounds.Lead.most(
      RRounds.Lead{
        Laws.Slot.ballots(s, c, k),
        r,
        name,
        t,
        basis,
        RRounds.Rounds.minds(Laws.Slot.ballots(s, c, k), ds, k, r)
      },
      ds
    )
      == True{}: Bool
  },
  efo: {
    RRounds.Lead.force(
      RRounds.Lead{
        Laws.Slot.ballots(s, c, k),
        r,
        name,
        t,
        basis,
        RRounds.Rounds.minds(Laws.Slot.ballots(s, c, k), ds, k, r)
      },
      ds
    )
      == f: RRounds.Force
  },
  +hk: {
    RRounds.Seen.takes(r, RRounds.Chain.seen(Laws.Slot.ballots(s, c, k), name, t)) == True{}: Bool
  },
  +hn: {RRounds.Ballots.at(Laws.Slot.ballots(s, c, k), name, t) == None{}: Maybe<&2, Types.Cast>}
) -> {
  Laws.Round.mind(
    Laws.Slot.ballots(
      Facts.Facts.add(
        s,
        Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Vote{r, p, basis}}
      ),
      c,
      k
    ),
    ds,
    k,
    r
  )
    == RRounds.Mind.Sound{p}: RRounds.Mind
}
  & {
    RRounds.Tally.voted(
      RRounds.Tally{
        Laws.Slot.ballots(
          Facts.Facts.add(
            s,
            Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Vote{r, p, basis}}
          ),
          c,
          k
        ),
        r,
        p
      },
      name
    )
      == True{}: Bool
  }:
  (
    Lists.Equal.to(
      String,
      h => {
        RRounds.Lead.mind.at(
          Laws.Slot.ballots(
            Facts.Facts.add(
              s,
              Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Vote{r, p, basis}}
            ),
            c,
            k
          ),
          ds,
          RRounds.Rounds.minds(
            Laws.Slot.ballots(
              Facts.Facts.add(
                s,
                Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Vote{r, p, basis}}
              ),
              c,
              k
            ),
            ds,
            k,
            r
          ),
          r,
          h,
          RRounds.Vote.of(
            Laws.Slot.ballots(
              Facts.Facts.add(
                s,
                Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Vote{r, p, basis}}
              ),
              c,
              k
            ),
            h,
            r
          )
        )
          == RRounds.Mind.Sound{p}: RRounds.Mind
      },
      name,
      RRounds.Turn.of(ds, Nat.add(k, r)),
      Equal.sym(
        String,
        RRounds.Turn.of(ds, Nat.add(k, r)),
        name,
        Texts.String.eq_sound(RRounds.Turn.of(ds, Nat.add(k, r)), name)(et)
      ),
      (
        %Equal.sym(Maybe<&2, RRounds.Ballot>, RRounds.Vote.of(Laws.Slot.ballots(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Vote{r, p, basis}}), c, k), name, r), Some{RRounds.Ballot{name, t, Types.Cast.Vote{r, p, basis}}}, Laws.Vote.of_counted(Laws.Slot.ballots(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Vote{r, p, basis}}), c, k), name, r, t, p, basis, Laws.Seen.takes_grows(Laws.Slot.ballots(s, c, k), Laws.Slot.ballots(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Vote{r, p, basis}}), c, k), name, t, r, Laws.Slot.added_grown(s, name, c, k, t, Types.Cast.Vote{r, p, basis}, Laws.Slot.cast_none(s, name, c, k, t, hl, hn)))(hk), Laws.Slot.added_at(s, name, c, k, t, Types.Cast.Vote{r, p, basis}, Laws.Slot.cast_none(s, name, c, k, t, hl, hn)))): {RRounds.Lead.mind.at(Laws.Slot.ballots(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Vote{r, p, basis}}), c, k), ds, RRounds.Rounds.minds(Laws.Slot.ballots(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Vote{r, p, basis}}), c, k), ds, k, r), r, name, _) == RRounds.Mind.Sound{p}: RRounds.Mind}
        Mind.sound_le(RRounds.Lead.mind.at(Laws.Slot.ballots(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Vote{r, p, basis}}), c, k), ds, RRounds.Rounds.minds(Laws.Slot.ballots(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Vote{r, p, basis}}), c, k), ds, k, r), r, name, Some{RRounds.Ballot{name, t, Types.Cast.Vote{r, p, basis}}}), p)((
          %Slot.lead_sound.was(s, name, c, k, ds, t, r, basis, f, p, ef, em, efo): {Laws.Mind.le(_, RRounds.Lead.mind.at(Laws.Slot.ballots(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Vote{r, p, basis}}), c, k), ds, RRounds.Rounds.minds(Laws.Slot.ballots(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Vote{r, p, basis}}), c, k), ds, k, r), r, name, Some{RRounds.Ballot{name, t, Types.Cast.Vote{r, p, basis}}})) == True{}: Bool}
          Laws.Mind.le_of_cap(RRounds.Lead.mind.at(Laws.Slot.ballots(s, c, k), ds, RRounds.Rounds.minds(Laws.Slot.ballots(s, c, k), ds, k, r), r, name, Some{RRounds.Ballot{name, t, Types.Cast.Vote{r, p, basis}}}), RRounds.Lead.mind.at(Laws.Slot.ballots(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Vote{r, p, basis}}), c, k), ds, RRounds.Rounds.minds(Laws.Slot.ballots(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Vote{r, p, basis}}), c, k), ds, k, r), r, name, Some{RRounds.Ballot{name, t, Types.Cast.Vote{r, p, basis}}}))(Laws.Lead.mind.at_cap(RRounds.Ballot{name, t, Types.Cast.Vote{r, p, basis}}, Laws.Slot.ballots(s, c, k), Laws.Slot.ballots(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Vote{r, p, basis}}), c, k), ds, r, name, RRounds.Rounds.minds(Laws.Slot.ballots(s, c, k), ds, k, r), RRounds.Rounds.minds(Laws.Slot.ballots(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Vote{r, p, basis}}), c, k), ds, k, r), Laws.Slot.added_grown(s, name, c, k, t, Types.Cast.Vote{r, p, basis}, Laws.Slot.cast_none(s, name, c, k, t, hl, hn)), Laws.Minds.grows(r, Laws.Slot.ballots(s, c, k), Laws.Slot.ballots(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Vote{r, p, basis}}), c, k), ds, k, Laws.Slot.added_grown(s, name, c, k, t, Types.Cast.Vote{r, p, basis}, Laws.Slot.cast_none(s, name, c, k, t, hl, hn))))))))
    ),
    (
      %Equal.sym(Maybe<&2, RRounds.Ballot>, RRounds.Vote.of(Laws.Slot.ballots(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Vote{r, p, basis}}), c, k), name, r), Some{RRounds.Ballot{name, t, Types.Cast.Vote{r, p, basis}}}, Laws.Vote.of_counted(Laws.Slot.ballots(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Vote{r, p, basis}}), c, k), name, r, t, p, basis, Laws.Seen.takes_grows(Laws.Slot.ballots(s, c, k), Laws.Slot.ballots(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Vote{r, p, basis}}), c, k), name, t, r, Laws.Slot.added_grown(s, name, c, k, t, Types.Cast.Vote{r, p, basis}, Laws.Slot.cast_none(s, name, c, k, t, hl, hn)))(hk), Laws.Slot.added_at(s, name, c, k, t, Types.Cast.Vote{r, p, basis}, Laws.Slot.cast_none(s, name, c, k, t, hl, hn)))): {RRounds.Vote.is_for(p, _) == True{}: Bool}
      Coded.Pick.is_eq_refl(p))
  )

# Slot.lead_sound, for a chance that is sure
def Slot.lead_sound.fin(
  +s: Facts.Facts(),
  +name: String,
  +c: Ledgers.Line,
  +k: Nat,
  +ds: List<&2, String>,
  +t: Nat,
  +r: Nat,
  +basis: List<&2, Types.Ref>,
  +f: RRounds.Force,
  +p: Types.Pick,
  +hl: {List.contains(~String, ~String.eq, Facts.Facts.liars(s), name) == False{}: Bool},
  ef: {RRounds.Lead.mind.of(p, f, True{}) == RRounds.Mind.Sound{p}: RRounds.Mind},
  w: Chance.Sure(Laws.Slot.ballots(s, c, k), ds, k, name, RRounds.Chance{t, r, basis, f})
) -> {
  Laws.Round.mind(
    Laws.Slot.ballots(
      Facts.Facts.add(
        s,
        Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Vote{r, p, basis}}
      ),
      c,
      k
    ),
    ds,
    k,
    r
  )
    == RRounds.Mind.Sound{p}: RRounds.Mind
}
  & {
    RRounds.Tally.voted(
      RRounds.Tally{
        Laws.Slot.ballots(
          Facts.Facts.add(
            s,
            Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Vote{r, p, basis}}
          ),
          c,
          k
        ),
        r,
        p
      },
      name
    )
      == True{}: Bool
  }:
  (et, w2) = w
  (em, w3) = w2
  (efo, w4) = w3
  (hk, hn) = w4
  Slot.lead_sound.end(s, name, c, k, ds, t, r, basis, f, p, hl, ef, et, em, efo, hk, hn)

# a lead is sound: where a node has the chance to lead the round r of a slot
# with the basis and the force f, and f leaves it the pick p (f is free, or
# binds to p), then in the facts with its vote for p in r, with that basis, as
# its next ballot, the lead of r is sound for p, and the vote counts for p,
# when the facts do not name the node a liar
def Slot.lead_sound(
  +s: Facts.Facts(),
  +name: String,
  +c: Ledgers.Line,
  +k: Nat,
  +ds: List<&2, String>,
  +t: Nat,
  +r: Nat,
  +basis: List<&2, Types.Ref>,
  +f: RRounds.Force,
  +p: Types.Pick
) -> {
  List.contains(~String, ~String.eq, Facts.Facts.liars(s), name) == False{}: Bool
} -> {
  RRounds.Slot.chance(
    Laws.Slot.ballots(s, c, k),
    ds,
    k,
    name
  )
    == Some{RRounds.Chance{t, r, basis, f}}: Maybe<&2, RRounds.Chance>
} -> {
  RRounds.Lead.mind.of(p, f, True{}) == RRounds.Mind.Sound{p}: RRounds.Mind
} -> {
  Laws.Round.mind(
    Laws.Slot.ballots(
      Facts.Facts.add(
        s,
        Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Vote{r, p, basis}}
      ),
      c,
      k
    ),
    ds,
    k,
    r
  )
    == RRounds.Mind.Sound{p}: RRounds.Mind
}
  & {
    RRounds.Tally.voted(
      RRounds.Tally{
        Laws.Slot.ballots(
          Facts.Facts.add(
            s,
            Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Vote{r, p, basis}}
          ),
          c,
          k
        ),
        r,
        p
      },
      name
    )
      == True{}: Bool
  }:
  hl => ec => ef => Slot.lead_sound.fin(
    s,
    name,
    c,
    k,
    ds,
    t,
    r,
    basis,
    f,
    p,
    hl,
    ef,
    Slot.chance_sure(Laws.Slot.ballots(s, c, k), ds, k, name, RRounds.Chance{t, r, basis, f})(ec)
  )

# A lost node
# -----------
# When the node whose turn the highest round is cast no ballot there, a node
# calls its own next round; the round is then alive for each node that holds
# the call, and each passes to it.

# a node calls its own next round, when the highest round of a ballot is not
# alive for it
def Slot.lost_calls(
  +bs: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +name: String,
  +t: Nat,
  +fl: Nat,
  +vs: List<&2, RRounds.Voted>,
  +to: Nat
) -> {
  RRounds.Round.alive(bs, ds, k, name, RRounds.Rounds.top(bs)) == False{}: Bool
} -> {
  RRounds.Chain.reach(bs, name) == RRounds.Reach{t, RRounds.Seen{fl, vs}}: RRounds.Reach
} -> {
  RRounds.Rounds.mine(
    List.length(&2, String, ds),
    ds,
    k,
    name,
    RRounds.Rounds.top(bs)
  )
    == Some{to}: Maybe<&2, Nat>
} -> {
  RRounds.Slot.pass(
    bs,
    ds,
    k,
    name
  )
    == Some{RRounds.Draft{t, Types.Cast.Pass{to}}}: Maybe<&2, RRounds.Draft>
}:
  ea => er => em => (
    %Equal.sym(RRounds.Reach, RRounds.Chain.reach(bs, name), RRounds.Reach{t, RRounds.Seen{fl, vs}}, er): {RRounds.Slot.pass.at(RRounds.Rounds.top(bs), RRounds.Round.alive(bs, ds, k, name, RRounds.Rounds.top(bs)), u => RRounds.Rounds.mine(List.length(&2, String, ds), ds, k, name, RRounds.Rounds.top(bs)), _) == Some{RRounds.Draft{t, Types.Cast.Pass{to}}}: Maybe<&2, RRounds.Draft>}
    %Equal.sym(Bool, RRounds.Round.alive(bs, ds, k, name, RRounds.Rounds.top(bs)), False{}, ea): {RRounds.Slot.pass.of(t, fl, RRounds.Rounds.top(bs), _, u => RRounds.Rounds.mine(List.length(&2, String, ds), ds, k, name, RRounds.Rounds.top(bs))) == Some{RRounds.Draft{t, Types.Cast.Pass{to}}}: Maybe<&2, RRounds.Draft>}
    %Equal.sym(Maybe<&2, Nat>, RRounds.Rounds.mine(List.length(&2, String, ds), ds, k, name, RRounds.Rounds.top(bs)), Some{to}, em): {RRounds.Slot.pass.to(t, _) == Some{RRounds.Draft{t, Types.Cast.Pass{to}}}: Maybe<&2, RRounds.Draft>}
    {==})

# a node passes to the highest round of a ballot, when the round is alive for
# it and it may still vote in a round below
def Slot.joins(
  +bs: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +name: String,
  +t: Nat,
  +fl: Nat,
  +vs: List<&2, RRounds.Voted>
) -> {
  RRounds.Round.alive(bs, ds, k, name, RRounds.Rounds.top(bs)) == True{}: Bool
} -> {
  RRounds.Chain.reach(bs, name) == RRounds.Reach{t, RRounds.Seen{fl, vs}}: RRounds.Reach
} -> {
  Nat.is_lt(fl, RRounds.Rounds.top(bs)) == True{}: Bool
} -> {
  RRounds.Slot.pass(
    bs,
    ds,
    k,
    name
  )
    == Some{RRounds.Draft{t, Types.Cast.Pass{RRounds.Rounds.top(bs)}}}: Maybe<&2, RRounds.Draft>
}:
  ea => er => el => (
    %Equal.sym(RRounds.Reach, RRounds.Chain.reach(bs, name), RRounds.Reach{t, RRounds.Seen{fl, vs}}, er): {RRounds.Slot.pass.at(RRounds.Rounds.top(bs), RRounds.Round.alive(bs, ds, k, name, RRounds.Rounds.top(bs)), u => RRounds.Rounds.mine(List.length(&2, String, ds), ds, k, name, RRounds.Rounds.top(bs)), _) == Some{RRounds.Draft{t, Types.Cast.Pass{RRounds.Rounds.top(bs)}}}: Maybe<&2, RRounds.Draft>}
    %Equal.sym(Bool, RRounds.Round.alive(bs, ds, k, name, RRounds.Rounds.top(bs)), True{}, ea): {RRounds.Slot.pass.of(t, fl, RRounds.Rounds.top(bs), _, u => RRounds.Rounds.mine(List.length(&2, String, ds), ds, k, name, RRounds.Rounds.top(bs))) == Some{RRounds.Draft{t, Types.Cast.Pass{RRounds.Rounds.top(bs)}}}: Maybe<&2, RRounds.Draft>}
    %Equal.sym(Bool, Nat.is_lt(fl, RRounds.Rounds.top(bs)), True{}, el): {RRounds.Slot.pass.to(t, Shared.Maybe.when(Nat, _, u => Some{RRounds.Rounds.top(bs)})) == Some{RRounds.Draft{t, Types.Cast.Pass{RRounds.Rounds.top(bs)}}}: Maybe<&2, RRounds.Draft>}
    {==})

# a round is alive for each node, in facts that hold a ballot, of that round
# or of a round above, of the node whose turn it is
def Slot.called_alive(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +ds: List<&2, String>,
  +h: String,
  +t: Nat,
  +x: Types.Cast,
  +to: Nat,
  +d: String
) -> {
  String.eq(RRounds.Turn.of(ds, Nat.add(k, to)), h) == True{}: Bool
} -> {
  Facts.Facts.has(s, Types.Fact.Vote{h, Types.Step.At{c, k, t}, x}) == True{}: Bool
} -> {
  Nat.is_le(to, RRounds.Cast.round(x)) == True{}: Bool
} -> {RRounds.Round.alive(Laws.Slot.ballots(s, c, k), ds, k, d, to) == True{}: Bool}:
  eh => hin => hle => Lists.Bool.by(
    z => {
      Shared.Bool.when(
        Bool,
        z,
        u => True{},
        u => RRounds.Rounds.heard(
          Laws.Slot.ballots(s, c, k),
          RRounds.Turn.of(ds, Nat.add(k, to)),
          to
        )
      )
        == True{}: Bool
    },
    String.eq(RRounds.Turn.of(ds, Nat.add(k, to)), d),
    et => {==},
    ef => (
      %Equal.sym(String, RRounds.Turn.of(ds, Nat.add(k, to)), h, Texts.String.eq_sound(RRounds.Turn.of(ds, Nat.add(k, to)), h)(eh)): {RRounds.Rounds.heard(Laws.Slot.ballots(s, c, k), _, to) == True{}: Bool}
      Rounds.heard_of(Laws.Slot.ballots(s, c, k), h, to, t, x)(Laws.Casts.has_of(s, c, k, h, t, x)(hin))(hle))
  )

# Many nodes
# ----------
# What one node holds, the facts of all hold: a sound lead, and the votes
# for it. So a slot is decided once more than half of the nodes followed.

# a vote that counts in the facts s counts in wider facts that name no liar
def Tally.voted_wider(
  +s: Facts.Facts(),
  +s2: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +r: Nat,
  +p: Types.Pick,
  +d: String
) -> {
  Facts.Facts.wider(s, s2) == True{}: Bool
} -> {
  Facts.Facts.liars(s2) == []: List<&2, String>
} -> {
  RRounds.Tally.voted(RRounds.Tally{Laws.Slot.ballots(s, c, k), r, p}, d) == True{}: Bool
} -> {RRounds.Tally.voted(RRounds.Tally{Laws.Slot.ballots(s2, c, k), r, p}, d) == True{}: Bool}:
  hw => hl => hv => Laws.Tally.voted_grows(
    Laws.Slot.ballots(s, c, k),
    Laws.Slot.ballots(s2, c, k),
    r,
    p,
    d,
    Laws.Slot.grown_wider(s, s2, c, k)(hw)(hl)
  )(hv)

# a slot is decided for the pick of a sound lead that the facts s hold, in
# wider facts that name no liar, where more than half of the nodes cast a
# vote for it that counts
def Votes.lead_decides(
  +s: Facts.Facts(),
  +s2: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +ds: List<&2, String>,
  +r: Nat,
  +p: Types.Pick
) -> {
  Facts.Facts.wider(s, s2) == True{}: Bool
} -> {
  Facts.Facts.liars(s2) == []: List<&2, String>
} -> {
  Laws.Round.mind(Laws.Slot.ballots(s, c, k), ds, k, r) == RRounds.Mind.Sound{p}: RRounds.Mind
} -> {
  RRounds.Tally.most(Laws.Slot.ballots(s2, c, k), ds, r, p) == True{}: Bool
} -> {Lines.Votes.decided(s2, c, k, ds) == Some{p}: Maybe<&2, Types.Pick>}:
  hw => hl => em => hm => Laws.Slot.most_decides(
    Laws.Slot.ballots(s2, c, k),
    ds,
    k,
    r,
    p
  )(
    Round.sound_grows(
      Laws.Slot.ballots(s, c, k),
      Laws.Slot.ballots(s2, c, k),
      ds,
      k,
      r,
      p
    )(Laws.Slot.grown_wider(s, s2, c, k)(hw)(hl))(em)
  )(hm)

# Where the ballots of a voter end
# --------------------------------

# Reach.held_one, for one number
def Reach.held_one.same(
  +bs: List<&2, RRounds.Ballot>,
  +v: String,
  +t1: Nat,
  +m1: RRounds.Seen,
  +t2: Nat,
  +m2: RRounds.Seen,
  +et: {t1 == t2: Nat},
  es1: {RRounds.Chain.seen(bs, v, t1) == Some{m1}: Maybe<&2, RRounds.Seen>},
  es2: {RRounds.Chain.seen(bs, v, t2) == Some{m2}: Maybe<&2, RRounds.Seen>}
) -> {RRounds.Reach{t1, m1} == RRounds.Reach{t2, m2}: RRounds.Reach}:
  %et: {RRounds.Reach{t1, m1} == RRounds.Reach{_, m2}: RRounds.Reach}
  %Shared.Maybe.some_inj(
    RRounds.Seen,
    m1,
    m2,
    Equal.trans(
      Maybe<&2, RRounds.Seen>,
      Some{m1},
      RRounds.Chain.seen(bs, v, t1),
      Some{m2},
      Equal.sym(Maybe<&2, RRounds.Seen>, RRounds.Chain.seen(bs, v, t1), Some{m1}, es1),
      (
        %Equal.sym(Nat, t1, t2, et): {RRounds.Chain.seen(bs, v, _) == Some{m2}: Maybe<&2, RRounds.Seen>}
        es2)
    )
  ): {RRounds.Reach{t1, m1} == RRounds.Reach{t1, _}: RRounds.Reach}
  {==}

# the ballots of a voter end at one number: where it is known and its ballot
# of that number is not held
def Reach.held_one(
  +bs: List<&2, RRounds.Ballot>,
  +v: String,
  +t1: Nat,
  +m1: RRounds.Seen,
  +t2: Nat,
  +m2: RRounds.Seen,
  +es1: {RRounds.Chain.seen(bs, v, t1) == Some{m1}: Maybe<&2, RRounds.Seen>},
  hn1: {RRounds.Ballots.at(bs, v, t1) == None{}: Maybe<&2, Types.Cast>},
  +es2: {RRounds.Chain.seen(bs, v, t2) == Some{m2}: Maybe<&2, RRounds.Seen>},
  hn2: {RRounds.Ballots.at(bs, v, t2) == None{}: Maybe<&2, Types.Cast>}
) -> {RRounds.Reach{t1, m1} == RRounds.Reach{t2, m2}: RRounds.Reach}:
  Lists.Bool.by(
    z => {
      Nat.is_le(1n+t1, t2) == z: Bool
    } -> {RRounds.Reach{t1, m1} == RRounds.Reach{t2, m2}: RRounds.Reach},
    Nat.is_le(1n+t1, t2),
    et => e => Empty.absurd(
      {RRounds.Reach{t1, m1} == RRounds.Reach{t2, m2}: RRounds.Reach},
      Chain.seen_whole(t2, t1, bs, v, m2)(es2)(et)(hn1)
    ),
    ef => e => Lists.Bool.by(
      z => {
        Nat.is_le(1n+t2, t1) == z: Bool
      } -> {RRounds.Reach{t1, m1} == RRounds.Reach{t2, m2}: RRounds.Reach},
      Nat.is_le(1n+t2, t1),
      et2 => e2 => Empty.absurd(
        {RRounds.Reach{t1, m1} == RRounds.Reach{t2, m2}: RRounds.Reach},
        Chain.seen_whole(t1, t2, bs, v, m1)(es1)(et2)(hn2)
      ),
      ef2 => e2 => Reach.held_one.same(
        bs,
        v,
        t1,
        m1,
        t2,
        m2,
        Nat.le_same(t1, t2)(Nat.nle_above(1n+t2, t1)(ef2))(Nat.nle_above(1n+t1, t2)(ef)),
        es1,
        es2
      )
    )({==})
  )({==})

# Chain.reach_next, once how far the ballots of the voter are held among bs2
# (m2) is known
def Chain.reach_next.at(
  m2: RRounds.Reach,
  +bs2: List<&2, RRounds.Ballot>,
  +v: String,
  +t: Nat,
  +m: RRounds.Seen,
  +x: Types.Cast,
  er2: {RRounds.Chain.reach(bs2, v) == m2: RRounds.Reach},
  es: {RRounds.Chain.seen(bs2, v, t) == Some{m}: Maybe<&2, RRounds.Seen>},
  ha: {RRounds.Ballots.at(bs2, v, t) == Some{x}: Maybe<&2, Types.Cast>},
  hn: {RRounds.Ballots.at(bs2, v, 1n+t) == None{}: Maybe<&2, Types.Cast>},
  held: Laws.Reach.Held(bs2, v, m2)
) -> {RRounds.Chain.reach(bs2, v) == RRounds.Reach{1n+t, RRounds.Seen.step(m, x)}: RRounds.Reach}:
  match m2:
    case RRounds.Reach{+t2, +sn2}:
      (es2, hn2) = held
      Equal.trans(
        RRounds.Reach,
        RRounds.Chain.reach(bs2, v),
        RRounds.Reach{t2, sn2},
        RRounds.Reach{1n+t, RRounds.Seen.step(m, x)},
        er2,
        Reach.held_one(bs2, v, t2, sn2, 1n+t, RRounds.Seen.step(m, x), es2, hn2, (
            %Equal.sym(Maybe<&2, RRounds.Seen>, RRounds.Chain.seen(bs2, v, t), Some{m}, es): {RRounds.Chain.seen.next(_, RRounds.Ballots.at(bs2, v, t)) == Some{RRounds.Seen.step(m, x)}: Maybe<&2, RRounds.Seen>}
            %Equal.sym(Maybe<&2, Types.Cast>, RRounds.Ballots.at(bs2, v, t), Some{x}, ha): {RRounds.Chain.seen.next(Some{m}, _) == Some{RRounds.Seen.step(m, x)}: Maybe<&2, RRounds.Seen>}
            {==}), hn)
      )

# Chain.reach_next, with what is known of the voter where its ballots end
def Chain.reach_next.of(
  +bs: List<&2, RRounds.Ballot>,
  +bs2: List<&2, RRounds.Ballot>,
  +v: String,
  +t: Nat,
  +m: RRounds.Seen,
  +x: Types.Cast,
  hg: {Laws.Ballots.grown(bs, bs2) == True{}: Bool},
  ha: {RRounds.Ballots.at(bs2, v, t) == Some{x}: Maybe<&2, Types.Cast>},
  hn: {RRounds.Ballots.at(bs2, v, 1n+t) == None{}: Maybe<&2, Types.Cast>},
  held: Laws.Reach.Held(bs, v, RRounds.Reach{t, m})
) -> {RRounds.Chain.reach(bs2, v) == RRounds.Reach{1n+t, RRounds.Seen.step(m, x)}: RRounds.Reach}:
  (es, hn0) = held
  Chain.reach_next.at(
    RRounds.Chain.reach(bs2, v),
    bs2,
    v,
    t,
    m,
    x,
    {==},
    Laws.Chain.seen_grows(bs, bs2, v, t, m, hg)(es),
    ha,
    hn,
    Laws.Chain.reach_held(bs2, v)
  )

# the next ballot of a voter moves the end of its ballots by one: where the
# ballots of a voter are held among bs as far as the number t, and bs2, which
# reads each ballot that bs reads, holds its ballot x of the number t and none
# of the next number, they are held among bs2 as far as the next number, and
# the voter is seen after x. This is the third premise of Slot.pass_once
def Chain.reach_next(
  +bs: List<&2, RRounds.Ballot>,
  +bs2: List<&2, RRounds.Ballot>,
  +v: String,
  +t: Nat,
  +m: RRounds.Seen,
  +x: Types.Cast
) -> {
  Laws.Ballots.grown(bs, bs2) == True{}: Bool
} -> {
  RRounds.Chain.reach(bs, v) == RRounds.Reach{t, m}: RRounds.Reach
} -> {
  RRounds.Ballots.at(bs2, v, t) == Some{x}: Maybe<&2, Types.Cast>
} -> {
  RRounds.Ballots.at(bs2, v, 1n+t) == None{}: Maybe<&2, Types.Cast>
} -> {RRounds.Chain.reach(bs2, v) == RRounds.Reach{1n+t, RRounds.Seen.step(m, x)}: RRounds.Reach}:
  hg => er => ha => hn => Chain.reach_next.of(
    bs,
    bs2,
    v,
    t,
    m,
    x,
    hg,
    ha,
    hn,
    Lists.Equal.to(
      RRounds.Reach,
      z => Laws.Reach.Held(bs, v, z),
      RRounds.Chain.reach(bs, v),
      RRounds.Reach{t, m},
      er,
      Laws.Chain.reach_held(bs, v)
    )
  )

# A work
# ------
# What a work does (work.bend) is one more ballot: the laws above, said of
# the facts with one more ballot, are laws of the facts after a work.

# Slot.pass_new, with the round that the node passes to
def Slot.pass_new.to(
  +s: Facts.Facts(),
  +name: String,
  +c: Ledgers.Line,
  +k: Nat,
  +ds: List<&2, String>,
  +t2: Nat,
  +x: Types.Cast,
  +t: Nat,
  +sn: RRounds.Seen,
  +to: Nat,
  +hl: {List.contains(~String, ~String.eq, Facts.Facts.liars(s), name) == False{}: Bool},
  held: Laws.Reach.Held(Laws.Slot.ballots(s, c, k), name, RRounds.Reach{t, sn}),
  w: {
    x == Types.Cast.Pass{to}: Types.Cast
  }
    & (
      {
        t2 == t: Nat
      }
        & (
          {
            Nat.is_le(RRounds.Rounds.top(Laws.Slot.ballots(s, c, k)), to) == True{}: Bool
          }
            & {RRounds.Round.alive(Laws.Slot.ballots(s, c, k), ds, k, name, to) == True{}: Bool}
        )
    )
) -> {Facts.Facts.cast(s, name, Types.Step.At{c, k, t2}) == False{}: Bool}:
  (es, hn) = held
  (ex, w2) = w
  (et, w3) = w2
  %Equal.sym(Nat, t2, t, et): {Facts.Facts.cast(s, name, Types.Step.At{c, k, _}) == False{}: Bool}
  Laws.Slot.cast_none(s, name, c, k, t, hl, hn)

# Slot.pass_new, once how far the ballots of the node are held (m) is known
def Slot.pass_new.at(
  m: RRounds.Reach,
  +s: Facts.Facts(),
  +name: String,
  +c: Ledgers.Line,
  +k: Nat,
  +ds: List<&2, String>,
  +t2: Nat,
  +x: Types.Cast
) -> {
  List.contains(~String, ~String.eq, Facts.Facts.liars(s), name) == False{}: Bool
} -> Laws.Reach.Held(
  Laws.Slot.ballots(s, c, k),
  name,
  m
) -> {
  Laws.Pass.next(
    Laws.Slot.ballots(s, c, k),
    ds,
    k,
    name,
    m
  )
    == Some{RRounds.Draft{t2, x}}: Maybe<&2, RRounds.Draft>
} -> {Facts.Facts.cast(s, name, Types.Step.At{c, k, t2}) == False{}: Bool}:
  match m:
    case RRounds.Reach{+t, +sn}:
      +hl => held => ep => Laws.Ex.by(
        Nat,
        to => {
          x == Types.Cast.Pass{to}: Types.Cast
        }
          & (
            {
              t2 == t: Nat
            }
              & (
                {
                  Nat.is_le(RRounds.Rounds.top(Laws.Slot.ballots(s, c, k)), to) == True{}: Bool
                }
                  & {
                    RRounds.Round.alive(Laws.Slot.ballots(s, c, k), ds, k, name, to) == True{}: Bool
                  }
              )
          ),
        {Facts.Facts.cast(s, name, Types.Step.At{c, k, t2}) == False{}: Bool},
        Pass.next_to(Laws.Slot.ballots(s, c, k), ds, k, name, t, t2, x, sn)(ep),
        +to => w => Slot.pass_new.to(s, name, c, k, ds, t2, x, t, sn, to, hl, held, w)
      )

# the pass of a node is a new ballot: the facts hold no ballot of the node
# with its number, when they do not name the node a liar
def Slot.pass_new(
  +s: Facts.Facts(),
  +name: String,
  +c: Ledgers.Line,
  +k: Nat,
  +ds: List<&2, String>,
  +t: Nat,
  +x: Types.Cast
) -> {
  List.contains(~String, ~String.eq, Facts.Facts.liars(s), name) == False{}: Bool
} -> {
  RRounds.Slot.pass(
    Laws.Slot.ballots(s, c, k),
    ds,
    k,
    name
  )
    == Some{RRounds.Draft{t, x}}: Maybe<&2, RRounds.Draft>
} -> {Facts.Facts.cast(s, name, Types.Step.At{c, k, t}) == False{}: Bool}:
  hl => ep => Slot.pass_new.at(
    RRounds.Chain.reach(Laws.Slot.ballots(s, c, k), name),
    s,
    name,
    c,
    k,
    ds,
    t,
    x
  )(hl)(Laws.Chain.reach_held(Laws.Slot.ballots(s, c, k), name))(ep)

# Slot.reach_new, with what is known where the ballots of the node end
def Slot.reach_new.of(
  +s: Facts.Facts(),
  +name: String,
  +c: Ledgers.Line,
  +k: Nat,
  +t: Nat,
  +m: RRounds.Seen,
  +hl: {List.contains(~String, ~String.eq, Facts.Facts.liars(s), name) == False{}: Bool},
  held: Laws.Reach.Held(Laws.Slot.ballots(s, c, k), name, RRounds.Reach{t, m})
) -> {Facts.Facts.cast(s, name, Types.Step.At{c, k, t}) == False{}: Bool}:
  (es, hn) = held
  Laws.Slot.cast_none(s, name, c, k, t, hl, hn)

# the next ballot of a node is a new one: the facts hold no ballot of the
# node with the number where its ballots end, when they do not name the node
# a liar
def Slot.reach_new(
  +s: Facts.Facts(),
  +name: String,
  +c: Ledgers.Line,
  +k: Nat,
  +t: Nat,
  +m: RRounds.Seen
) -> {
  List.contains(~String, ~String.eq, Facts.Facts.liars(s), name) == False{}: Bool
} -> {
  RRounds.Chain.reach(Laws.Slot.ballots(s, c, k), name) == RRounds.Reach{t, m}: RRounds.Reach
} -> {Facts.Facts.cast(s, name, Types.Step.At{c, k, t}) == False{}: Bool}:
  hl => er => Slot.reach_new.of(
    s,
    name,
    c,
    k,
    t,
    m,
    hl,
    Lists.Equal.to(
      RRounds.Reach,
      z => Laws.Reach.Held(Laws.Slot.ballots(s, c, k), name, z),
      RRounds.Chain.reach(Laws.Slot.ballots(s, c, k), name),
      RRounds.Reach{t, m},
      er,
      Laws.Chain.reach_held(Laws.Slot.ballots(s, c, k), name)
    )
  )

# a work with nothing to cast changes no fact
def Work.idle(
  +s: Facts.Facts(),
  +name: String
) -> {
  Works.Work.plan(s, name) == None{}: Maybe<&2, RWorks.Plan>
} -> {Works.Work.does(s, name) == s: Facts.Facts()}:
  e => (
    %Equal.sym(Maybe<&2, RWorks.Plan>, Works.Work.plan(s, name), None{}, e): {Works.Work.cast(s, name, _) == s: Facts.Facts()}
    {==})

# a work adds the ballot of its plan, when that is a new ballot
def Work.does_cast(
  +s: Facts.Facts(),
  +name: String,
  +st: Types.Step,
  +x: Types.Cast
) -> {
  Works.Work.plan(s, name) == Some{RWorks.Plan{st, x}}: Maybe<&2, RWorks.Plan>
} -> {
  Facts.Facts.cast(s, name, st) == False{}: Bool
} -> {Works.Work.does(s, name) == Facts.Facts.add(s, Types.Fact.Vote{name, st, x}): Facts.Facts()}:
  e => hc => (
    %Equal.sym(Maybe<&2, RWorks.Plan>, Works.Work.plan(s, name), Some{RWorks.Plan{st, x}}, e): {Works.Work.cast(s, name, _) == Facts.Facts.add(s, Types.Fact.Vote{name, st, x}): Facts.Facts()}
    %Equal.sym(Bool, Facts.Facts.cast(s, name, st), False{}, hc): {Shared.Bool.when(Facts.Facts(), _, u => s, u => Facts.Facts.add(s, Types.Fact.Vote{name, st, x})) == Facts.Facts.add(s, Types.Fact.Vote{name, st, x}): Facts.Facts()}
    {==})

# a work passes once: after a work whose plan is the pass of a slot, the node
# has no other pass for the slot, when the facts do not name it a liar
def Work.passed_waits(
  +s: Facts.Facts(),
  +name: String,
  +c: Ledgers.Line,
  +k: Nat,
  +ds: List<&2, String>,
  +t: Nat,
  +x: Types.Cast
) -> {
  List.contains(~String, ~String.eq, Facts.Facts.liars(s), name) == False{}: Bool
} -> {
  Works.Work.plan(s, name) == Some{RWorks.Plan{Types.Step.At{c, k, t}, x}}: Maybe<&2, RWorks.Plan>
} -> {
  RRounds.Slot.pass(
    Laws.Slot.ballots(s, c, k),
    ds,
    k,
    name
  )
    == Some{RRounds.Draft{t, x}}: Maybe<&2, RRounds.Draft>
} -> {
  RRounds.Slot.pass(
    Laws.Slot.ballots(Works.Work.does(s, name), c, k),
    ds,
    k,
    name
  )
    == None{}: Maybe<&2, RRounds.Draft>
}:
  +hl => epl => +ep => (
    %Equal.sym(Facts.Facts(), Works.Work.does(s, name), Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}), Work.does_cast(s, name, Types.Step.At{c, k, t}, x)(epl)(Slot.pass_new(s, name, c, k, ds, t, x)(hl)(ep))): {RRounds.Slot.pass(Laws.Slot.ballots(_, c, k), ds, k, name) == None{}: Maybe<&2, RRounds.Draft>}
    Slot.passed_waits(s, name, c, k, ds, t, x)(hl)(ep))
