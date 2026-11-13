import Base
import ../shared/shared/shared/shared/shared.bend as Shared
import ../shared/shared/shared/text.bend as Texts
import ./codes.bend as Coded
import ./run/rounds.bend as RRounds
import ./shared/lists.bend as Lists
import ./types.bend as Types

# The rounds decide one pick
# --------------------------
# Two rounds of one slot decide one pick (run/rounds.bend). Once more than
# half of the nodes cast a counted vote for the pick of the sound lead of a
# round, the lead of each later round that is sound is for that pick: more
# than half of the nodes gave it a promise, so one of them voted in the first
# round, before its promise; so the votes that the lead rests on bind it, to
# the pick of the sound lead of a round between the two, which is that pick.

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

# Tools
# -----

# a or b is true when b is
def Bool.or_right(a: Bool, -b: Bool) -> {b == True{}: Bool} -> {Bool.or(a, b) == True{}: Bool}:
  match a:
    case False{}:
      h => h
    case True{}:
      h => {==}

# b is true when a or b is, and a is not
def Bool.or_rest(
  a: Bool,
  -b: Bool
) -> {a == False{}: Bool} -> {Bool.or(a, b) == True{}: Bool} -> {b == True{}: Bool}:
  match a:
    case False{}:
      f => h => h
    case True{}:
      f => h => Empty.absurd({b == True{}: Bool}, Shared.Bool.true_ne_false(f))

# no number above a number is at most it
def Nat.above_not(
  +a: Nat,
  +b: Nat
) -> {Nat.is_le(1n+a, b) == True{}: Bool} -> {Nat.is_le(b, a) == True{}: Bool} -> Empty:
  h1 => h2 => Shared.Bool.false_ne_true(
    Equal.trans(
      Bool,
      False{},
      Nat.is_le(1n+a, a),
      True{},
      Equal.sym(Bool, Nat.is_le(1n+a, a), False{}, Shared.Nat.succ_nle(a)),
      Shared.Nat.le_trans(1n+a, b, a)(h1)(h2)
    )
  )

# a number at most 0 is 0
def Nat.le_zero_eq(+a: Nat) -> {Nat.is_le(a, 0n) == True{}: Bool} -> {a == 0n: Nat}:
  match a:
    case 0n:
      h => {==}
    case 1n+p:
      h => Empty.absurd({1n+p == 0n: Nat}, Shared.Bool.false_ne_true(h))

# a number above a number is not that number
def Nat.above_ne(
  +a: Nat,
  +b: Nat
) -> {Nat.is_le(1n+a, b) == True{}: Bool} -> {Nat.is_eq(b, a) == False{}: Bool}:
  h => Lists.Bool.by(
    c => {c == False{}: Bool},
    Nat.is_eq(b, a),
    et => Empty.absurd(
      {True{} == False{}: Bool},
      Nat.above_not(a, b)(h)((
          %Shared.Nat.is_eq_sound(b, a)(et): {Nat.is_le(b, _) == True{}: Bool}
          Shared.Nat.le_refl(b)))
    ),
    ef => {==}
  )

# Chains
# ------

# the votes vs hold a vote of the round r for the pick p
def Votes.has(vs: List<&2, RRounds.Voted>, +r: Nat, +p: Types.Pick) -> Bool:
  match vs:
    case Nil{}:
      False{}
    case Con{RRounds.Voted{r2, p2}, rest}:
      Bool.or(Bool.and(Nat.is_eq(r2, r), Coded.Pick.is_eq(p2, p)), Votes.has(rest, r, p))

# what stays true of a voter along its chain. Floor: it may vote in no round
# below fl. Vote: it cast a counted vote of the round r for the pick p
type Mark is Data:
  Mark.Floor{fl: Nat}
  Mark.Vote{round: Nat, pick: Types.Pick}

# g is true of a voter seen as m, or m is not known
def Seen.marks(g: Mark, m: Maybe<&2, RRounds.Seen>) -> Bool:
  match g m:
    case Mark.Floor{fl} None{}:
      True{}
    case Mark.Vote{r, p} None{}:
      True{}
    case Mark.Floor{fl} Some{RRounds.Seen{f, vs}}:
      Nat.is_le(fl, f)
    case Mark.Vote{r, p} Some{RRounds.Seen{f, vs}}:
      Votes.has(vs, r, p)

# what is true of a voter stays true after its next ballot
def Seen.marks_next(
  g: Mark,
  m: Maybe<&2, RRounds.Seen>,
  x: Maybe<&2, Types.Cast>
) -> {Seen.marks(g, m) == True{}: Bool} -> {Seen.marks(g, RRounds.Chain.seen.next(m, x)) == True{}: Bool}:
  match g m x:
    case Mark.Floor{fl} None{} None{}:
      h => {==}
    case Mark.Floor{fl} None{} Some{c}:
      h => {==}
    case Mark.Floor{fl} Some{s} None{}:
      h => {==}
    case Mark.Vote{r, p} None{} None{}:
      h => {==}
    case Mark.Vote{r, p} None{} Some{c}:
      h => {==}
    case Mark.Vote{r, p} Some{s} None{}:
      h => {==}
    case Mark.Floor{+fl} Some{RRounds.Seen{+f, +vs}} Some{Types.Cast.Vote{+r2, +p2, b}}:
      +h => Lists.Bool.by(
        c => {
          Seen.marks(Mark.Floor{fl}, Some{Bool.pick(RRounds.Seen, c, RRounds.Seen{1n+r2, RRounds.Voted{r2, p2} <> vs}, RRounds.Seen{f, vs})}) == True{}: Bool
        },
        Nat.is_le(f, r2),
        et => Shared.Nat.le_succ(fl, r2)(Shared.Nat.le_trans(fl, f, r2)(h)(et)),
        ef => h
      )
    case Mark.Floor{+fl} Some{RRounds.Seen{+f, +vs}} Some{Types.Cast.Pass{+r2}}:
      +h => Lists.Bool.by(
        c => {
          Seen.marks(Mark.Floor{fl}, Some{Bool.pick(RRounds.Seen, c, RRounds.Seen{r2, vs}, RRounds.Seen{f, vs})}) == True{}: Bool
        },
        Nat.is_le(f, r2),
        et => Shared.Nat.le_trans(fl, f, r2)(h)(et),
        ef => h
      )
    case Mark.Vote{+r, +p} Some{RRounds.Seen{+f, +vs}} Some{Types.Cast.Vote{+r2, +p2, b}}:
      +h => Lists.Bool.by(
        c => {
          Seen.marks(Mark.Vote{r, p}, Some{Bool.pick(RRounds.Seen, c, RRounds.Seen{1n+r2, RRounds.Voted{r2, p2} <> vs}, RRounds.Seen{f, vs})}) == True{}: Bool
        },
        Nat.is_le(f, r2),
        et => Bool.or_right(Bool.and(Nat.is_eq(r2, r), Coded.Pick.is_eq(p2, p)), Votes.has(vs, r, p))(h),
        ef => h
      )
    case Mark.Vote{+r, +p} Some{RRounds.Seen{+f, +vs}} Some{Types.Cast.Pass{+r2}}:
      +h => Lists.Bool.by(
        c => {
          Seen.marks(Mark.Vote{r, p}, Some{Bool.pick(RRounds.Seen, c, RRounds.Seen{r2, vs}, RRounds.Seen{f, vs})}) == True{}: Bool
        },
        Nat.is_le(f, r2),
        et => h,
        ef => h
      )

# what is true of a voter before one of its ballots is true before each later
# one
def Chain.marks_on(
  b: Nat,
  +a: Nat,
  +bs: List<&2, RRounds.Ballot>,
  +v: String,
  +g: Mark
) -> {
  Nat.is_le(a, b) == True{}: Bool
} -> {
  Seen.marks(g, RRounds.Chain.seen(bs, v, a)) == True{}: Bool
} -> {Seen.marks(g, RRounds.Chain.seen(bs, v, b)) == True{}: Bool}:
  match b:
    case 0n:
      hl => h => (
        %Nat.le_zero_eq(a)(hl): {Seen.marks(g, RRounds.Chain.seen(bs, v, _)) == True{}: Bool}
        h)
    case 1n+(+j):
      +hl => +h => Lists.Bool.by(
        c => {Seen.marks(g, RRounds.Chain.seen(bs, v, 1n+j)) == True{}: Bool},
        Nat.is_le(1n+a, 1n+j),
        et => Seen.marks_next(g, RRounds.Chain.seen(bs, v, j), RRounds.Ballots.at(bs, v, j))(
          Chain.marks_on(j, a, bs, v, g)(et)(h)
        ),
        ef => (
          %Shared.Nat.le_nlt_eq(a, 1n+j)(hl)(ef): {Seen.marks(g, RRounds.Chain.seen(bs, v, _)) == True{}: Bool}
          h)
      )

# no voter that may vote in the round r may vote in no round below 1n+r
def Seen.takes_not(
  m: Maybe<&2, RRounds.Seen>,
  +r: Nat
) -> {RRounds.Seen.takes(r, m) == True{}: Bool} -> {Seen.marks(Mark.Floor{1n+r}, m) == True{}: Bool} -> Empty:
  match m:
    case None{}:
      ht => ha => Shared.Bool.false_ne_true(ht)
    case Some{RRounds.Seen{+f, vs}}:
      ht => ha => Nat.above_not(r, f)(ha)(ht)

# a voter is seen with its vote of the round r after it, when the vote counts
def Seen.takes_vote(
  m: Maybe<&2, RRounds.Seen>,
  +r: Nat,
  +p: Types.Pick,
  +b: List<&2, Types.Ref>
) -> {
  RRounds.Seen.takes(r, m) == True{}: Bool
} -> {Seen.marks(Mark.Vote{r, p}, RRounds.Chain.seen.next(m, Some{Types.Cast.Vote{r, p, b}})) == True{}: Bool}:
  match m:
    case None{}:
      h => Empty.absurd({True{} == True{}: Bool}, Shared.Bool.false_ne_true(h))
    case Some{RRounds.Seen{+f, +vs}}:
      h => (
        %Equal.sym(Bool, Nat.is_le(f, r), True{}, h): {Seen.marks(Mark.Vote{r, p}, Some{Bool.pick(RRounds.Seen, _, RRounds.Seen{1n+r, RRounds.Voted{r, p} <> vs}, RRounds.Seen{f, vs})}) == True{}: Bool}
        %Equal.sym(Bool, Nat.is_eq(r, r), True{}, Shared.Nat.is_eq_refl(r)): {Bool.or(Bool.and(_, Coded.Pick.is_eq(p, p)), Votes.has(vs, r, p)) == True{}: Bool}
        %Equal.sym(Bool, Coded.Pick.is_eq(p, p), True{}, Coded.Pick.is_eq_refl(p)): {Bool.or(Bool.and(True{}, _), Votes.has(vs, r, p)) == True{}: Bool}
        {==})

# a counted vote of a voter, of the round r, is among its votes wherever it is
# seen to vote in no round below 1n+r: it cast the vote before
def Chain.vote_seen(
  +bs: List<&2, RRounds.Ballot>,
  +v: String,
  +t: Nat,
  +r: Nat,
  +p: Types.Pick,
  +b: List<&2, Types.Ref>,
  +n: Nat
) -> {
  RRounds.Seen.takes(r, RRounds.Chain.seen(bs, v, t)) == True{}: Bool
} -> {
  RRounds.Ballots.at(bs, v, t) == Some{Types.Cast.Vote{r, p, b}}: Maybe<&2, Types.Cast>
} -> {
  Seen.marks(Mark.Floor{1n+r}, RRounds.Chain.seen(bs, v, n)) == True{}: Bool
} -> {Seen.marks(Mark.Vote{r, p}, RRounds.Chain.seen(bs, v, n)) == True{}: Bool}:
  +ht => +ha => +hf => Lists.Bool.by(
    c => {Seen.marks(Mark.Vote{r, p}, RRounds.Chain.seen(bs, v, n)) == True{}: Bool},
    Nat.is_le(n, t),
    et => Empty.absurd(
      {Seen.marks(Mark.Vote{r, p}, RRounds.Chain.seen(bs, v, n)) == True{}: Bool},
      Seen.takes_not(RRounds.Chain.seen(bs, v, t), r)(ht)(
        Chain.marks_on(t, n, bs, v, Mark.Floor{1n+r})(et)(hf)
      )
    ),
    ef => Chain.marks_on(n, 1n+t, bs, v, Mark.Vote{r, p})(Shared.Nat.nle_succ_le(n, t)(ef))((
        %Equal.sym(Maybe<&2, Types.Cast>, RRounds.Ballots.at(bs, v, t), Some{Types.Cast.Vote{r, p, b}}, ha): {Seen.marks(Mark.Vote{r, p}, RRounds.Chain.seen.next(RRounds.Chain.seen(bs, v, t), _)) == True{}: Bool}
        Seen.takes_vote(RRounds.Chain.seen(bs, v, t), r, p, b)(ht)))
  )

# Votes that count
# ----------------

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

# what follows from a vote that counts for the voter v in the round r: the
# voter may vote in the round before the vote, and the ballots hold the vote
def Ballot.counts_by(
  -Q: Type,
  +bs: List<&2, RRounds.Ballot>,
  +v: String,
  +r: Nat,
  +w: String,
  +t: Nat,
  +r2: Nat,
  +p: Types.Pick,
  +basis: List<&2, Types.Ref>,
  +h: {
    RRounds.Ballot.counts(RRounds.Roll{bs, v, r}, RRounds.Ballot{w, t, Types.Cast.Vote{r2, p, basis}}) == True{}: Bool
  },
  k: {
    RRounds.Seen.takes(r, RRounds.Chain.seen(bs, v, t)) == True{}: Bool
  } -> {RRounds.Ballots.at(bs, v, t) == Some{Types.Cast.Vote{r, p, basis}}: Maybe<&2, Types.Cast>} -> Q
) -> Q:
  k((
      %Shared.Nat.is_eq_sound(r2, r)(Shared.Bool.and_true_right(String.eq(w, v), Nat.is_eq(r2, r))(Shared.Bool.and_true_left(Bool.and(String.eq(w, v), Nat.is_eq(r2, r)), Bool.and(RRounds.Seen.takes(r2, RRounds.Chain.seen(bs, v, t)), RRounds.Cast.is(Types.Cast.Vote{r2, p, basis}, RRounds.Ballots.at(bs, v, t))))(h))): {RRounds.Seen.takes(_, RRounds.Chain.seen(bs, v, t)) == True{}: Bool}
      Shared.Bool.and_true_left(RRounds.Seen.takes(r2, RRounds.Chain.seen(bs, v, t)), RRounds.Cast.is(Types.Cast.Vote{r2, p, basis}, RRounds.Ballots.at(bs, v, t)))(Shared.Bool.and_true_right(Bool.and(String.eq(w, v), Nat.is_eq(r2, r)), Bool.and(RRounds.Seen.takes(r2, RRounds.Chain.seen(bs, v, t)), RRounds.Cast.is(Types.Cast.Vote{r2, p, basis}, RRounds.Ballots.at(bs, v, t))))(h))))((
      %Shared.Nat.is_eq_sound(r2, r)(Shared.Bool.and_true_right(String.eq(w, v), Nat.is_eq(r2, r))(Shared.Bool.and_true_left(Bool.and(String.eq(w, v), Nat.is_eq(r2, r)), Bool.and(RRounds.Seen.takes(r2, RRounds.Chain.seen(bs, v, t)), RRounds.Cast.is(Types.Cast.Vote{r2, p, basis}, RRounds.Ballots.at(bs, v, t))))(h))): {RRounds.Ballots.at(bs, v, t) == Some{Types.Cast.Vote{_, p, basis}}: Maybe<&2, Types.Cast>}
      Cast.is_some(Types.Cast.Vote{r2, p, basis}, RRounds.Ballots.at(bs, v, t))(Shared.Bool.and_true_right(RRounds.Seen.takes(r2, RRounds.Chain.seen(bs, v, t)), RRounds.Cast.is(Types.Cast.Vote{r2, p, basis}, RRounds.Ballots.at(bs, v, t)))(Shared.Bool.and_true_right(Bool.and(String.eq(w, v), Nat.is_eq(r2, r)), Bool.and(RRounds.Seen.takes(r2, RRounds.Chain.seen(bs, v, t)), RRounds.Cast.is(Types.Cast.Vote{r2, p, basis}, RRounds.Ballots.at(bs, v, t))))(h)))))

# What binds a lead
# -----------------

# f leaves a lead open, or binds it to a round that is r or above
def Force.above(+r: Nat, f: RRounds.Force) -> Bool:
  match f:
    case RRounds.Force.Open{}:
      True{}
    case RRounds.Force.Free{}:
      False{}
    case RRounds.Force.Bound{r2, p}:
      Nat.is_le(r, r2)

# what a and b leave together binds to r or above when a does
def Force.join_left(
  a: RRounds.Force,
  b: RRounds.Force,
  +r: Nat
) -> {Force.above(r, a) == True{}: Bool} -> {Force.above(r, RRounds.Force.join(a, b)) == True{}: Bool}:
  match a b:
    case RRounds.Force.Open{} RRounds.Force.Open{}:
      h => {==}
    case RRounds.Force.Open{} RRounds.Force.Free{}:
      h => {==}
    case RRounds.Force.Open{} RRounds.Force.Bound{rb, pb}:
      h => {==}
    case RRounds.Force.Free{} RRounds.Force.Open{}:
      h => {==}
    case RRounds.Force.Free{} RRounds.Force.Free{}:
      h => h
    case RRounds.Force.Free{} RRounds.Force.Bound{rb, pb}:
      h => Empty.absurd({Nat.is_le(r, rb) == True{}: Bool}, Shared.Bool.false_ne_true(h))
    case RRounds.Force.Bound{ra, pa} RRounds.Force.Open{}:
      h => {==}
    case RRounds.Force.Bound{ra, pa} RRounds.Force.Free{}:
      h => h
    case RRounds.Force.Bound{+ra, +pa} RRounds.Force.Bound{+rb, +pb}:
      +h => Lists.Bool.by(
        c => {
          Force.above(r, Bool.pick(RRounds.Force, c, RRounds.Force.Bound{rb, pb}, RRounds.Force.Bound{ra, pa})) == True{}: Bool
        },
        Nat.is_lt(ra, rb),
        et => Shared.Nat.lt_weak(r, rb)(Shared.Nat.le_lt(r, ra, rb)(h)(et)),
        ef => h
      )

# what a and b leave together binds to r or above when b does
def Force.join_right(
  a: RRounds.Force,
  b: RRounds.Force,
  +r: Nat
) -> {Force.above(r, b) == True{}: Bool} -> {Force.above(r, RRounds.Force.join(a, b)) == True{}: Bool}:
  match a b:
    case RRounds.Force.Open{} RRounds.Force.Open{}:
      h => {==}
    case RRounds.Force.Open{} RRounds.Force.Free{}:
      h => {==}
    case RRounds.Force.Open{} RRounds.Force.Bound{rb, pb}:
      h => {==}
    case RRounds.Force.Free{} RRounds.Force.Open{}:
      h => {==}
    case RRounds.Force.Free{} RRounds.Force.Free{}:
      h => h
    case RRounds.Force.Free{} RRounds.Force.Bound{rb, pb}:
      h => h
    case RRounds.Force.Bound{ra, pa} RRounds.Force.Open{}:
      h => {==}
    case RRounds.Force.Bound{ra, pa} RRounds.Force.Free{}:
      h => Empty.absurd({Nat.is_le(r, ra) == True{}: Bool}, Shared.Bool.false_ne_true(h))
    case RRounds.Force.Bound{+ra, +pa} RRounds.Force.Bound{+rb, +pb}:
      +h => Lists.Bool.by(
        c => {
          Force.above(r, Bool.pick(RRounds.Force, c, RRounds.Force.Bound{rb, pb}, RRounds.Force.Bound{ra, pa})) == True{}: Bool
        },
        Nat.is_lt(ra, rb),
        et => h,
        ef => Shared.Nat.le_trans(r, rb, ra)(h)(Shared.Nat.nlt_le(ra, rb)(ef))
      )

# m is a sound lead for the pick p
def Mind.is(+p: Types.Pick, m: Maybe<&2, RRounds.Mind>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{RRounds.Mind.Open{}}:
      False{}
    case Some{RRounds.Mind.Void{}}:
      False{}
    case Some{RRounds.Mind.Sound{q}}:
      Coded.Pick.is_eq(q, p)

# f binds a lead only to the pick of a sound lead among ms, of its round
def Force.fits(+ms: List<&2, RRounds.Mind>, f: RRounds.Force) -> Bool:
  match f:
    case RRounds.Force.Open{}:
      True{}
    case RRounds.Force.Free{}:
      True{}
    case RRounds.Force.Bound{r, p}:
      Mind.is(p, List.get(&2, RRounds.Mind, ms, r))

# what a and b leave together fits ms when both do
def Force.join_fits(
  a: RRounds.Force,
  b: RRounds.Force,
  +ms: List<&2, RRounds.Mind>
) -> {
  Force.fits(ms, a) == True{}: Bool
} -> {Force.fits(ms, b) == True{}: Bool} -> {Force.fits(ms, RRounds.Force.join(a, b)) == True{}: Bool}:
  match a b:
    case RRounds.Force.Open{} RRounds.Force.Open{}:
      ha => hb => {==}
    case RRounds.Force.Open{} RRounds.Force.Free{}:
      ha => hb => {==}
    case RRounds.Force.Open{} RRounds.Force.Bound{rb, pb}:
      ha => hb => {==}
    case RRounds.Force.Free{} RRounds.Force.Open{}:
      ha => hb => {==}
    case RRounds.Force.Free{} RRounds.Force.Free{}:
      ha => hb => {==}
    case RRounds.Force.Free{} RRounds.Force.Bound{rb, pb}:
      ha => hb => hb
    case RRounds.Force.Bound{ra, pa} RRounds.Force.Open{}:
      ha => hb => {==}
    case RRounds.Force.Bound{ra, pa} RRounds.Force.Free{}:
      ha => hb => ha
    case RRounds.Force.Bound{+ra, +pa} RRounds.Force.Bound{+rb, +pb}:
      ha => hb => Lists.Bool.by(
        c => {
          Force.fits(ms, Bool.pick(RRounds.Force, c, RRounds.Force.Bound{rb, pb}, RRounds.Force.Bound{ra, pa})) == True{}: Bool
        },
        Nat.is_lt(ra, rb),
        et => hb,
        ef => ha
      )

# what a vote of the round r for the pick p leaves a lead fits ms, where m is
# the lead of the round r among ms
def Voted.force_fits.at(
  +ms: List<&2, RRounds.Mind>,
  +r: Nat,
  +p: Types.Pick,
  m: Maybe<&2, RRounds.Mind>
) -> {
  List.get(&2, RRounds.Mind, ms, r) == m: Maybe<&2, RRounds.Mind>
} -> {Force.fits(ms, RRounds.Voted.force.at(r, p, m)) == True{}: Bool}:
  match m:
    case None{}:
      e => {==}
    case Some{RRounds.Mind.Open{}}:
      e => {==}
    case Some{RRounds.Mind.Void{}}:
      e => {==}
    case Some{RRounds.Mind.Sound{+q}}:
      e => Lists.Bool.by(
        c => {
          Force.fits(ms, Bool.pick(RRounds.Force, c, RRounds.Force.Bound{r, p}, RRounds.Force.Free{})) == True{}: Bool
        },
        Coded.Pick.is_eq(q, p),
        et => (
          %Equal.sym(Maybe<&2, RRounds.Mind>, List.get(&2, RRounds.Mind, ms, r), Some{RRounds.Mind.Sound{q}}, e): {Mind.is(p, _) == True{}: Bool}
          et),
        ef => {==}
      )

# what the votes vs leave a lead fits ms
def Votes.force_fits(
  vs: List<&2, RRounds.Voted>,
  +ms: List<&2, RRounds.Mind>
) -> {Force.fits(ms, RRounds.Votes.force(ms, vs)) == True{}: Bool}:
  match vs:
    case Nil{}:
      {==}
    case Con{RRounds.Voted{+r, +p}, +rest}:
      Force.join_fits(
        RRounds.Voted.force.at(r, p, List.get(&2, RRounds.Mind, ms, r)),
        RRounds.Votes.force(ms, rest),
        ms
      )(Voted.force_fits.at(ms, r, p, List.get(&2, RRounds.Mind, ms, r))({==}))(
        Votes.force_fits(rest, ms)
      )

# what the promise m leaves a lead fits ms
def Promise.force_fits(
  m: RRounds.Promise,
  +ms: List<&2, RRounds.Mind>
) -> {Force.fits(ms, RRounds.Promise.force(ms, m)) == True{}: Bool}:
  match m:
    case RRounds.Promise.Open{}:
      {==}
    case RRounds.Promise.None{}:
      {==}
    case RRounds.Promise.Held{vs}:
      Votes.force_fits(vs, ms)

# what the nodes ds leave the lead g fits the leads of the rounds before it
def Lead.force_fits(
  ds: List<&2, String>,
  +g: RRounds.Lead
) -> {Force.fits(RRounds.Lead.minds(g), RRounds.Lead.force(g, ds)) == True{}: Bool}:
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +rest}:
      Force.join_fits(
        RRounds.Promise.force(RRounds.Lead.minds(g), RRounds.Promise.read(g, d)),
        RRounds.Lead.force(g, rest),
        RRounds.Lead.minds(g)
      )(Promise.force_fits(RRounds.Promise.read(g, d), RRounds.Lead.minds(g)))(
        Lead.force_fits(rest, g)
      )

# votes with a vote of the round r for the pick p, of the sound lead of the
# round, bind a lead to r or above
def Votes.force_above(
  vs: List<&2, RRounds.Voted>,
  +ms: List<&2, RRounds.Mind>,
  +r: Nat,
  +p: Types.Pick
) -> {
  Votes.has(vs, r, p) == True{}: Bool
} -> {
  List.get(&2, RRounds.Mind, ms, r) == Some{RRounds.Mind.Sound{p}}: Maybe<&2, RRounds.Mind>
} -> {Force.above(r, RRounds.Votes.force(ms, vs)) == True{}: Bool}:
  match vs:
    case Nil{}:
      h => hm => Empty.absurd({False{} == True{}: Bool}, Shared.Bool.false_ne_true(h))
    case Con{RRounds.Voted{+r2, +p2}, +rest}:
      h => +hm => Lists.Bool.by(
        c => {
          Bool.or(c, Votes.has(rest, r, p)) == True{}: Bool
        } -> {Force.above(r, RRounds.Force.join(RRounds.Voted.force.at(r2, p2, List.get(&2, RRounds.Mind, ms, r2)), RRounds.Votes.force(ms, rest))) == True{}: Bool},
        Bool.and(Nat.is_eq(r2, r), Coded.Pick.is_eq(p2, p)),
        +et => h2 => Force.join_left(
          RRounds.Voted.force.at(r2, p2, List.get(&2, RRounds.Mind, ms, r2)),
          RRounds.Votes.force(ms, rest),
          r
        )((
            %Equal.sym(Nat, r2, r, Shared.Nat.is_eq_sound(r2, r)(Shared.Bool.and_true_left(Nat.is_eq(r2, r), Coded.Pick.is_eq(p2, p))(et))): {Force.above(r, RRounds.Voted.force.at(_, p2, List.get(&2, RRounds.Mind, ms, _))) == True{}: Bool}
            %Equal.sym(Types.Pick, p2, p, Coded.Pick.is_eq_sound(p2, p)(Shared.Bool.and_true_right(Nat.is_eq(r2, r), Coded.Pick.is_eq(p2, p))(et))): {Force.above(r, RRounds.Voted.force.at(r, _, List.get(&2, RRounds.Mind, ms, r))) == True{}: Bool}
            %Equal.sym(Maybe<&2, RRounds.Mind>, List.get(&2, RRounds.Mind, ms, r), Some{RRounds.Mind.Sound{p}}, hm): {Force.above(r, RRounds.Voted.force.at(r, p, _)) == True{}: Bool}
            %Equal.sym(Bool, Coded.Pick.is_eq(p, p), True{}, Coded.Pick.is_eq_refl(p)): {Force.above(r, Bool.pick(RRounds.Force, _, RRounds.Force.Bound{r, p}, RRounds.Force.Free{})) == True{}: Bool}
            Shared.Nat.le_refl(r))),
        ef => h2 => Force.join_right(
          RRounds.Voted.force.at(r2, p2, List.get(&2, RRounds.Mind, ms, r2)),
          RRounds.Votes.force(ms, rest),
          r
        )(Votes.force_above(rest, ms, r, p)(h2)(hm))
      )(h)

# Promises
# --------

# a voter that promised the round r2 is seen to vote in no round below it
def Promise.of_floor(
  m: Maybe<&2, RRounds.Seen>,
  +r1: Nat,
  +r2: Nat
) -> {
  Nat.is_le(1n+r1, r2) == True{}: Bool
} -> {
  RRounds.Promise.is_held(RRounds.Promise.of(r2, m)) == True{}: Bool
} -> {Seen.marks(Mark.Floor{1n+r1}, m) == True{}: Bool}:
  match m:
    case None{}:
      hl => h => {==}
    case Some{RRounds.Seen{+f, +vs}}:
      +hl => Lists.Bool.by(
        c => {
          RRounds.Promise.is_held(Bool.pick(RRounds.Promise, c, RRounds.Promise.Held{vs}, RRounds.Promise.None{})) == True{}: Bool
        } -> {Nat.is_le(1n+r1, f) == True{}: Bool},
        Nat.is_le(r2, f),
        et => h => Shared.Nat.le_trans(1n+r1, r2, f)(hl)(et),
        ef => h => Empty.absurd({Nat.is_le(1n+r1, f) == True{}: Bool}, Shared.Bool.false_ne_true(h))
      )

# the promise of a voter seen with a vote of the round r1 for the pick p, of
# the sound lead of the round, binds a lead to r1 or above
def Promise.of_above(
  m: Maybe<&2, RRounds.Seen>,
  +ms: List<&2, RRounds.Mind>,
  +r1: Nat,
  +p: Types.Pick,
  +r2: Nat
) -> {
  RRounds.Promise.is_held(RRounds.Promise.of(r2, m)) == True{}: Bool
} -> {
  Seen.marks(Mark.Vote{r1, p}, m) == True{}: Bool
} -> {
  List.get(&2, RRounds.Mind, ms, r1) == Some{RRounds.Mind.Sound{p}}: Maybe<&2, RRounds.Mind>
} -> {Force.above(r1, RRounds.Promise.force(ms, RRounds.Promise.of(r2, m))) == True{}: Bool}:
  match m:
    case None{}:
      h => hv => hm => Empty.absurd({True{} == True{}: Bool}, Shared.Bool.false_ne_true(h))
    case Some{RRounds.Seen{+f, +vs}}:
      Lists.Bool.by(
        c => {
          RRounds.Promise.is_held(Bool.pick(RRounds.Promise, c, RRounds.Promise.Held{vs}, RRounds.Promise.None{})) == True{}: Bool
        } -> {
          Votes.has(vs, r1, p) == True{}: Bool
        } -> {
          List.get(&2, RRounds.Mind, ms, r1) == Some{RRounds.Mind.Sound{p}}: Maybe<&2, RRounds.Mind>
        } -> {Force.above(r1, RRounds.Promise.force(ms, Bool.pick(RRounds.Promise, c, RRounds.Promise.Held{vs}, RRounds.Promise.None{}))) == True{}: Bool},
        Nat.is_le(r2, f),
        et => h => hv => hm => Votes.force_above(vs, ms, r1, p)(hv)(hm),
        ef => h => hv => hm => Empty.absurd({False{} == True{}: Bool}, Shared.Bool.false_ne_true(h))
      )

# a lead of the round r2 is seen, after its vote, to vote in no round below
# 1n+r1, where r1 is below r2
def Promise.own_floor(
  m: Maybe<&2, RRounds.Seen>,
  +r1: Nat,
  +r2: Nat,
  +p2: Types.Pick,
  +b2: List<&2, Types.Ref>
) -> {
  RRounds.Seen.takes(r2, m) == True{}: Bool
} -> {
  Nat.is_le(1n+r1, r2) == True{}: Bool
} -> {Seen.marks(Mark.Floor{1n+r1}, RRounds.Chain.seen.next(m, Some{Types.Cast.Vote{r2, p2, b2}})) == True{}: Bool}:
  match m:
    case None{}:
      ht => hl => {==}
    case Some{RRounds.Seen{+f, +vs}}:
      ht => hl => (
        %Equal.sym(Bool, Nat.is_le(f, r2), True{}, ht): {Seen.marks(Mark.Floor{1n+r1}, Some{Bool.pick(RRounds.Seen, _, RRounds.Seen{1n+r2, RRounds.Voted{r2, p2} <> vs}, RRounds.Seen{f, vs})}) == True{}: Bool}
        Shared.Nat.le_succ(1n+r1, r2)(hl))

# the own promise of a lead of the round r2, seen after its vote with a vote
# of a round r1 below for the pick p, of the sound lead of the round, binds
# it to r1 or above
def Promise.own_above(
  m: Maybe<&2, RRounds.Seen>,
  +ms: List<&2, RRounds.Mind>,
  +r1: Nat,
  +p: Types.Pick,
  +r2: Nat,
  +p2: Types.Pick,
  +b2: List<&2, Types.Ref>
) -> {
  RRounds.Seen.takes(r2, m) == True{}: Bool
} -> {
  Nat.is_le(1n+r1, r2) == True{}: Bool
} -> {
  Seen.marks(Mark.Vote{r1, p}, RRounds.Chain.seen.next(m, Some{Types.Cast.Vote{r2, p2, b2}})) == True{}: Bool
} -> {
  List.get(&2, RRounds.Mind, ms, r1) == Some{RRounds.Mind.Sound{p}}: Maybe<&2, RRounds.Mind>
} -> {Force.above(r1, RRounds.Promise.force(ms, RRounds.Promise.own(m))) == True{}: Bool}:
  match m:
    case None{}:
      ht => hl => hv => hm => Empty.absurd({True{} == True{}: Bool}, Shared.Bool.false_ne_true(ht))
    case Some{RRounds.Seen{+f, +vs}}:
      ht => hl => hv => hm => Votes.force_above(vs, ms, r1, p)(
        Bool.or_rest(Bool.and(Nat.is_eq(r2, r1), Coded.Pick.is_eq(p2, p)), Votes.has(vs, r1, p))((
            %Equal.sym(Bool, Nat.is_eq(r2, r1), False{}, Nat.above_ne(r1, r2)(hl)): {Bool.and(_, Coded.Pick.is_eq(p2, p)) == False{}: Bool}
            {==}))((
            %ht: {Seen.marks(Mark.Vote{r1, p}, Some{Bool.pick(RRounds.Seen, _, RRounds.Seen{1n+r2, RRounds.Voted{r2, p2} <> vs}, RRounds.Seen{f, vs})}) == True{}: Bool}
            hv))
      )(hm)

# what a node d gave a lead of the round r2 binds the lead to r1 or above,
# when d gave a promise and cast a counted vote of the round r1, below r2,
# for the pick of the sound lead of the round: the vote is before the promise
def Promise.read_above(
  +bs: List<&2, RRounds.Ballot>,
  +h: String,
  +t: Nat,
  +r2: Nat,
  +p2: Types.Pick,
  +basis: List<&2, Types.Ref>,
  +ms: List<&2, RRounds.Mind>,
  +d: String,
  +t1: Nat,
  +r1: Nat,
  +p: Types.Pick,
  +b: List<&2, Types.Ref>
) -> {
  RRounds.Seen.takes(r2, RRounds.Chain.seen(bs, h, t)) == True{}: Bool
} -> {
  RRounds.Ballots.at(bs, h, t) == Some{Types.Cast.Vote{r2, p2, basis}}: Maybe<&2, Types.Cast>
} -> {
  Nat.is_le(1n+r1, r2) == True{}: Bool
} -> {
  List.get(&2, RRounds.Mind, ms, r1) == Some{RRounds.Mind.Sound{p}}: Maybe<&2, RRounds.Mind>
} -> {
  RRounds.Seen.takes(r1, RRounds.Chain.seen(bs, d, t1)) == True{}: Bool
} -> {
  RRounds.Ballots.at(bs, d, t1) == Some{Types.Cast.Vote{r1, p, b}}: Maybe<&2, Types.Cast>
} -> {
  RRounds.Promise.held(RRounds.Lead{bs, r2, h, t, basis, ms}, d) == True{}: Bool
} -> {Force.above(r1, RRounds.Promise.force(ms, RRounds.Promise.read(RRounds.Lead{bs, r2, h, t, basis, ms}, d))) == True{}: Bool}:
  +hlt => +hla => +hl => +hm => Lists.Bool.by(
    c => {
      RRounds.Seen.takes(r1, RRounds.Chain.seen(bs, d, t1)) == True{}: Bool
    } -> {
      RRounds.Ballots.at(bs, d, t1) == Some{Types.Cast.Vote{r1, p, b}}: Maybe<&2, Types.Cast>
    } -> {
      RRounds.Promise.is_held(Shared.Bool.when(RRounds.Promise, c, u => RRounds.Promise.own(RRounds.Chain.seen(bs, h, t)), u => RRounds.Promise.of(r2, RRounds.Chain.seen(bs, d, RRounds.Basis.find(basis, d))))) == True{}: Bool
    } -> {Force.above(r1, RRounds.Promise.force(ms, Shared.Bool.when(RRounds.Promise, c, u => RRounds.Promise.own(RRounds.Chain.seen(bs, h, t)), u => RRounds.Promise.of(r2, RRounds.Chain.seen(bs, d, RRounds.Basis.find(basis, d)))))) == True{}: Bool},
    String.eq(d, h),
    et => (
      %Equal.sym(String, d, h, Texts.String.eq_sound(d, h)(et)): ({
        RRounds.Seen.takes(r1, RRounds.Chain.seen(bs, _, t1)) == True{}: Bool
      } -> {
        RRounds.Ballots.at(bs, _, t1) == Some{Types.Cast.Vote{r1, p, b}}: Maybe<&2, Types.Cast>
      } -> {
        RRounds.Promise.is_held(RRounds.Promise.own(RRounds.Chain.seen(bs, h, t))) == True{}: Bool
      } -> {Force.above(r1, RRounds.Promise.force(ms, RRounds.Promise.own(RRounds.Chain.seen(bs, h, t)))) == True{}: Bool})
      +hdt => +hda => hh => Promise.own_above(RRounds.Chain.seen(bs, h, t), ms, r1, p, r2, p2, basis)(hlt)(hl)((
          %hla: {Seen.marks(Mark.Vote{r1, p}, RRounds.Chain.seen.next(RRounds.Chain.seen(bs, h, t), _)) == True{}: Bool}
          Chain.vote_seen(bs, h, t1, r1, p, b, 1n+t)(hdt)(hda)((
              %Equal.sym(Maybe<&2, Types.Cast>, RRounds.Ballots.at(bs, h, t), Some{Types.Cast.Vote{r2, p2, basis}}, hla): {Seen.marks(Mark.Floor{1n+r1}, RRounds.Chain.seen.next(RRounds.Chain.seen(bs, h, t), _)) == True{}: Bool}
              Promise.own_floor(RRounds.Chain.seen(bs, h, t), r1, r2, p2, basis)(hlt)(hl)))))(hm)),
    ef => +hdt => +hda => +hh => Promise.of_above(
      RRounds.Chain.seen(bs, d, RRounds.Basis.find(basis, d)),
      ms,
      r1,
      p,
      r2
    )(hh)(
      Chain.vote_seen(bs, d, t1, r1, p, b, RRounds.Basis.find(basis, d))(hdt)(hda)(
        Promise.of_floor(RRounds.Chain.seen(bs, d, RRounds.Basis.find(basis, d)), r1, r2)(hl)(hh)
      )
    )(hm)
  )

# the nodes ds bind the lead g to r or above when one of them does
def Lead.force_above(
  ds: List<&2, String>,
  +g: RRounds.Lead,
  +d: String,
  +r: Nat
) -> {
  List.contains(~String, ~String.eq, ds, d) == True{}: Bool
} -> {
  Force.above(r, RRounds.Promise.force(RRounds.Lead.minds(g), RRounds.Promise.read(g, d))) == True{}: Bool
} -> {Force.above(r, RRounds.Lead.force(g, ds)) == True{}: Bool}:
  match ds:
    case Nil{}:
      hin => ha => Empty.absurd({False{} == True{}: Bool}, Shared.Bool.false_ne_true(hin))
    case Con{+x, +rest}:
      hin => +ha => Lists.List.contains_cons_by(
        ~String,
        ~String.eq,
        ~Texts.String.laws(),
        {Force.above(r, RRounds.Force.join(RRounds.Promise.force(RRounds.Lead.minds(g), RRounds.Promise.read(g, x)), RRounds.Lead.force(g, rest))) == True{}: Bool},
        x,
        rest,
        d,
        hin,
        e => Force.join_left(
          RRounds.Promise.force(RRounds.Lead.minds(g), RRounds.Promise.read(g, x)),
          RRounds.Lead.force(g, rest),
          r
        )((
            %Equal.sym(String, x, d, e): {Force.above(r, RRounds.Promise.force(RRounds.Lead.minds(g), RRounds.Promise.read(g, _))) == True{}: Bool}
            ha)),
        cin => Force.join_right(
          RRounds.Promise.force(RRounds.Lead.minds(g), RRounds.Promise.read(g, x)),
          RRounds.Lead.force(g, rest),
          r
        )(Lead.force_above(rest, g, d, r)(cin)(ha))
      )

# The leads of the rounds before
# ------------------------------

# an index that xs holds a value at is below the length of xs
def List.get_under(
  -A: Data,
  xs: List<&2, A>,
  k: Nat,
  -x: A
) -> {
  List.get(&2, A, xs, k) == Some{x}: Maybe<&2, A>
} -> {Nat.is_le(1n+k, List.length(&2, A, xs)) == True{}: Bool}:
  match xs k:
    case Nil{} j:
      h => Empty.absurd({False{} == True{}: Bool}, Shared.Maybe.none_ne_some(A, x, h))
    case Con{h, t} 0n:
      e => Shared.Nat.le_zero(List.length(&2, A, t))
    case Con{h, t} 1n+p:
      List.get_under(A, t, p, x)

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

# the leads of the rounds below n hold the lead of each round below n
def Minds.get(
  n: Nat,
  +bs: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +r: Nat
) -> {
  Nat.is_le(1n+r, n) == True{}: Bool
} -> {List.get(&2, RRounds.Mind, RRounds.Rounds.minds(bs, ds, k, n), r) == Some{Round.mind(bs, ds, k, r)}: Maybe<&2, RRounds.Mind>}:
  match n:
    case 0n:
      hl => Empty.absurd(
        {None{} == Some{Round.mind(bs, ds, k, r)}: Maybe<&2, RRounds.Mind>},
        Shared.Bool.false_ne_true(hl)
      )
    case 1n+(+j):
      +hl => Lists.Bool.by(
        c => {
          List.get(&2, RRounds.Mind, List.append(&2, RRounds.Mind, RRounds.Rounds.minds(bs, ds, k, j), [Round.mind(bs, ds, k, j)]), r) == Some{Round.mind(bs, ds, k, r)}: Maybe<&2, RRounds.Mind>
        },
        Nat.is_le(1n+r, j),
        et => Lists.List.get_append(
          RRounds.Mind,
          RRounds.Rounds.minds(bs, ds, k, j),
          [Round.mind(bs, ds, k, j)],
          r,
          Round.mind(bs, ds, k, r)
        )(Minds.get(j, bs, ds, k, r)(et)),
        ef => (
          %Equal.sym(Nat, r, j, Shared.Nat.le_nlt_eq(r, j)(hl)(ef)): {List.get(&2, RRounds.Mind, List.append(&2, RRounds.Mind, RRounds.Rounds.minds(bs, ds, k, j), [Round.mind(bs, ds, k, j)]), _) == Some{Round.mind(bs, ds, k, _)}: Maybe<&2, RRounds.Mind>}
          %Minds.length(bs, ds, k, j): {List.get(&2, RRounds.Mind, List.append(&2, RRounds.Mind, RRounds.Rounds.minds(bs, ds, k, j), [Round.mind(bs, ds, k, j)]), _) == Some{Round.mind(bs, ds, k, j)}: Maybe<&2, RRounds.Mind>}
          Lists.List.get_snoc(RRounds.Mind, RRounds.Rounds.minds(bs, ds, k, j), Round.mind(bs, ds, k, j)))
      )

# a lead that is a sound lead for the pick p is one
def Mind.is_sound(
  m: Maybe<&2, RRounds.Mind>,
  +p: Types.Pick
) -> {Mind.is(p, m) == True{}: Bool} -> {m == Some{RRounds.Mind.Sound{p}}: Maybe<&2, RRounds.Mind>}:
  match m:
    case None{}:
      h => Empty.absurd(
        {None{} == Some{RRounds.Mind.Sound{p}}: Maybe<&2, RRounds.Mind>},
        Shared.Bool.false_ne_true(h)
      )
    case Some{RRounds.Mind.Open{}}:
      h => Empty.absurd(
        {Some{RRounds.Mind.Open{}} == Some{RRounds.Mind.Sound{p}}: Maybe<&2, RRounds.Mind>},
        Shared.Bool.false_ne_true(h)
      )
    case Some{RRounds.Mind.Void{}}:
      h => Empty.absurd(
        {Some{RRounds.Mind.Void{}} == Some{RRounds.Mind.Sound{p}}: Maybe<&2, RRounds.Mind>},
        Shared.Bool.false_ne_true(h)
      )
    case Some{RRounds.Mind.Sound{+q}}:
      h => Equal.cong(
        Types.Pick,
        Maybe<&2, RRounds.Mind>,
        z => Some{RRounds.Mind.Sound{z}},
        q,
        p,
        Coded.Pick.is_eq_sound(q, p)(h)
      )

# the pick of the lead m when it is sound, else d
def Mind.pick_or(m: RRounds.Mind, d: Types.Pick) -> Types.Pick:
  match m:
    case RRounds.Mind.Open{}:
      d
    case RRounds.Mind.Void{}:
      d
    case RRounds.Mind.Sound{p}:
      p

# the lead m is sound
def Mind.sound(m: RRounds.Mind) -> Bool:
  match m:
    case RRounds.Mind.Open{}:
      False{}
    case RRounds.Mind.Void{}:
      False{}
    case RRounds.Mind.Sound{p}:
      True{}

# two sound leads that are one are for one pick
def Mind.sound_inj(
  +p: Types.Pick,
  -q: Types.Pick,
  e: {RRounds.Mind.Sound{p} == RRounds.Mind.Sound{q}: RRounds.Mind}
) -> {p == q: Types.Pick}:
  Equal.cong(
    RRounds.Mind,
    Types.Pick,
    m => Mind.pick_or(m, p),
    RRounds.Mind.Sound{p},
    RRounds.Mind.Sound{q},
    e
  )

# a lead that is a sound lead is sound
def Mind.sound_of(
  -m: RRounds.Mind,
  -p: Types.Pick,
  e: {m == RRounds.Mind.Sound{p}: RRounds.Mind}
) -> {Mind.sound(m) == True{}: Bool}:
  Equal.cong(RRounds.Mind, Bool, z => Mind.sound(z), m, RRounds.Mind.Sound{p}, e)

# a sound lead among the leads of the rounds below n is of a round below n
def Minds.got_under(
  +bs: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +n: Nat,
  +r: Nat,
  +q: Types.Pick
) -> {
  Mind.is(q, List.get(&2, RRounds.Mind, RRounds.Rounds.minds(bs, ds, k, n), r)) == True{}: Bool
} -> {Nat.is_le(1n+r, n) == True{}: Bool}:
  h => (
    %Minds.length(bs, ds, k, n): {Nat.is_le(1n+r, _) == True{}: Bool}
    List.get_under(
      RRounds.Mind,
      RRounds.Rounds.minds(bs, ds, k, n),
      r,
      RRounds.Mind.Sound{q}
    )(Mind.is_sound(List.get(&2, RRounds.Mind, RRounds.Rounds.minds(bs, ds, k, n), r), q)(h)))

# a sound lead among the leads of the rounds below n is the lead of its round
def Minds.got_mind(
  +bs: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +n: Nat,
  +r: Nat,
  +q: Types.Pick
) -> {
  Mind.is(q, List.get(&2, RRounds.Mind, RRounds.Rounds.minds(bs, ds, k, n), r)) == True{}: Bool
} -> {Round.mind(bs, ds, k, r) == RRounds.Mind.Sound{q}: RRounds.Mind}:
  +h => Shared.Maybe.some_inj(
    RRounds.Mind,
    Round.mind(bs, ds, k, r),
    RRounds.Mind.Sound{q},
    Equal.trans(
      Maybe<&2, RRounds.Mind>,
      Some{Round.mind(bs, ds, k, r)},
      List.get(&2, RRounds.Mind, RRounds.Rounds.minds(bs, ds, k, n), r),
      Some{RRounds.Mind.Sound{q}},
      Equal.sym(
        Maybe<&2, RRounds.Mind>,
        List.get(&2, RRounds.Mind, RRounds.Rounds.minds(bs, ds, k, n), r),
        Some{Round.mind(bs, ds, k, r)},
        Minds.get(n, bs, ds, k, r)(Minds.got_under(bs, ds, k, n, r, q)(h))
      ),
      Mind.is_sound(List.get(&2, RRounds.Mind, RRounds.Rounds.minds(bs, ds, k, n), r), q)(h)
    )
  )

# Rounds that decide
# ------------------

# the lead of a round that decides the pick p is sound, for p
def Round.won_sound(
  m: RRounds.Mind,
  +bs: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +r: Nat,
  +p: Types.Pick
) -> {
  RRounds.Round.won(bs, ds, r, m) == Some{p}: Maybe<&2, Types.Pick>
} -> {m == RRounds.Mind.Sound{p}: RRounds.Mind}:
  match m:
    case RRounds.Mind.Open{}:
      h => Empty.absurd(
        {RRounds.Mind.Open{} == RRounds.Mind.Sound{p}: RRounds.Mind},
        Shared.Maybe.none_ne_some(Types.Pick, p, h)
      )
    case RRounds.Mind.Void{}:
      h => Empty.absurd(
        {RRounds.Mind.Void{} == RRounds.Mind.Sound{p}: RRounds.Mind},
        Shared.Maybe.none_ne_some(Types.Pick, p, h)
      )
    case RRounds.Mind.Sound{+q}:
      Lists.Bool.by(
        c => {
          Shared.Maybe.when(Types.Pick, c, u => Some{q}) == Some{p}: Maybe<&2, Types.Pick>
        } -> {RRounds.Mind.Sound{q} == RRounds.Mind.Sound{p}: RRounds.Mind},
        RRounds.Tally.most(bs, ds, r, q),
        et => h => Equal.cong(
          Types.Pick,
          RRounds.Mind,
          z => RRounds.Mind.Sound{z},
          q,
          p,
          Shared.Maybe.some_inj(Types.Pick, q, p, h)
        ),
        ef => h => Empty.absurd(
          {RRounds.Mind.Sound{q} == RRounds.Mind.Sound{p}: RRounds.Mind},
          Shared.Maybe.none_ne_some(Types.Pick, p, h)
        )
      )

# more than half of the nodes voted, with votes that count, for the pick that
# a round decides
def Round.won_most(
  m: RRounds.Mind,
  +bs: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +r: Nat,
  +p: Types.Pick
) -> {
  RRounds.Round.won(bs, ds, r, m) == Some{p}: Maybe<&2, Types.Pick>
} -> {RRounds.Tally.most(bs, ds, r, p) == True{}: Bool}:
  match m:
    case RRounds.Mind.Open{}:
      h => Empty.absurd(
        {RRounds.Tally.most(bs, ds, r, p) == True{}: Bool},
        Shared.Maybe.none_ne_some(Types.Pick, p, h)
      )
    case RRounds.Mind.Void{}:
      h => Empty.absurd(
        {RRounds.Tally.most(bs, ds, r, p) == True{}: Bool},
        Shared.Maybe.none_ne_some(Types.Pick, p, h)
      )
    case RRounds.Mind.Sound{+q}:
      Lists.Bool.by(
        c => {
          Shared.Maybe.when(Types.Pick, c, u => Some{q}) == Some{p}: Maybe<&2, Types.Pick>
        } -> {RRounds.Tally.most(bs, ds, r, p) == True{}: Bool},
        RRounds.Tally.most(bs, ds, r, q),
        et => h => (
          %Shared.Maybe.some_inj(Types.Pick, q, p, h): {RRounds.Tally.most(bs, ds, r, _) == True{}: Bool}
          et),
        ef => h => Empty.absurd(
          {RRounds.Tally.most(bs, ds, r, p) == True{}: Bool},
          Shared.Maybe.none_ne_some(Types.Pick, p, h)
        )
      )

# Sound leads
# -----------

# more than half of the nodes gave a lead that is sound a promise
def Mind.of_most(
  f: RRounds.Force,
  most: Bool,
  +p: Types.Pick,
  -p2: Types.Pick
) -> {RRounds.Lead.mind.of(p, f, most) == RRounds.Mind.Sound{p2}: RRounds.Mind} -> {most == True{}: Bool}:
  match f most:
    case RRounds.Force.Open{} True{}:
      hs => {==}
    case RRounds.Force.Open{} False{}:
      hs => Empty.absurd({False{} == True{}: Bool}, Shared.Bool.false_ne_true(Mind.sound_of(RRounds.Mind.Open{}, p2, hs)))
    case RRounds.Force.Free{} True{}:
      hs => {==}
    case RRounds.Force.Free{} False{}:
      hs => Empty.absurd({False{} == True{}: Bool}, Shared.Bool.false_ne_true(Mind.sound_of(RRounds.Mind.Void{}, p2, hs)))
    case RRounds.Force.Bound{r, q} True{}:
      hs => {==}
    case RRounds.Force.Bound{r, q} False{}:
      hs => Empty.absurd({False{} == True{}: Bool}, Shared.Bool.false_ne_true(Mind.sound_of(RRounds.Mind.Void{}, p2, hs)))

# what follows of a sound lead for the pick p2 that the nodes bind to r1 or
# above, with what fits ms: it is bound to the pick p2, of a sound lead among
# ms, of a round that is r1 or above
def Mind.of_bound(
  f: RRounds.Force,
  most: Bool,
  +ms: List<&2, RRounds.Mind>,
  +p: Types.Pick,
  +p2: Types.Pick,
  +r1: Nat,
  -Q: Type,
  k: (@r3: Nat -> {Nat.is_le(r1, r3) == True{}: Bool} -> {Mind.is(p2, List.get(&2, RRounds.Mind, ms, r3)) == True{}: Bool} -> Q)
) -> {RRounds.Lead.mind.of(p, f, most) == RRounds.Mind.Sound{p2}: RRounds.Mind} -> {Force.above(r1, f) == True{}: Bool} -> {Force.fits(ms, f) == True{}: Bool} -> Q:
  match f most:
    case RRounds.Force.Open{} True{}:
      hs => ha => hf => Empty.absurd(Q, Shared.Bool.false_ne_true(Mind.sound_of(RRounds.Mind.Open{}, p2, hs)))
    case RRounds.Force.Open{} False{}:
      hs => ha => hf => Empty.absurd(Q, Shared.Bool.false_ne_true(Mind.sound_of(RRounds.Mind.Open{}, p2, hs)))
    case RRounds.Force.Free{} True{}:
      hs => ha => hf => Empty.absurd(Q, Shared.Bool.false_ne_true(ha))
    case RRounds.Force.Free{} False{}:
      hs => ha => hf => Empty.absurd(Q, Shared.Bool.false_ne_true(ha))
    case RRounds.Force.Bound{r3, q} False{}:
      hs => ha => hf => Empty.absurd(Q, Shared.Bool.false_ne_true(Mind.sound_of(RRounds.Mind.Void{}, p2, hs)))
    case RRounds.Force.Bound{+r3, +q} True{}:
      hs => ha => hf => Lists.Bool.by(
        c => {
          Bool.pick(RRounds.Mind, c, RRounds.Mind.Sound{p}, RRounds.Mind.Void{}) == RRounds.Mind.Sound{p2}: RRounds.Mind
        } -> Q,
        Coded.Pick.is_eq(q, p),
        et => hs => k(r3)(ha)((
            %Mind.sound_inj(p, p2, hs): {Mind.is(_, List.get(&2, RRounds.Mind, ms, r3)) == True{}: Bool}
            %Coded.Pick.is_eq_sound(q, p)(et): {Mind.is(_, List.get(&2, RRounds.Mind, ms, r3)) == True{}: Bool}
            hf)),
        ef => hs => Empty.absurd(Q, Shared.Bool.false_ne_true(Mind.sound_of(RRounds.Mind.Void{}, p2, hs)))
      )(hs)

# what a node d gave a lead of the round r2 binds the lead to r1 or above,
# when d gave a promise and m, its counted vote of the round r1, below r2, is
# for the pick of the sound lead of the round
def Vote.read_above(
  m: Maybe<&2, RRounds.Ballot>,
  +bs: List<&2, RRounds.Ballot>,
  +h: String,
  +t: Nat,
  +r2: Nat,
  +p2: Types.Pick,
  +basis: List<&2, Types.Ref>,
  +ms: List<&2, RRounds.Mind>,
  +d: String,
  +r1: Nat,
  +p1: Types.Pick
) -> {
  RRounds.Vote.of(bs, d, r1) == m: Maybe<&2, RRounds.Ballot>
} -> {
  RRounds.Vote.is_for(p1, m) == True{}: Bool
} -> {RRounds.Seen.takes(r2, RRounds.Chain.seen(bs, h, t)) == True{}: Bool} -> {RRounds.Ballots.at(bs, h, t) == Some{Types.Cast.Vote{r2, p2, basis}}: Maybe<&2, Types.Cast>} -> {Nat.is_le(1n+r1, r2) == True{}: Bool} -> {List.get(&2, RRounds.Mind, ms, r1) == Some{RRounds.Mind.Sound{p1}}: Maybe<&2, RRounds.Mind>} -> {RRounds.Promise.held(RRounds.Lead{bs, r2, h, t, basis, ms}, d) == True{}: Bool} -> {Force.above(r1, RRounds.Promise.force(ms, RRounds.Promise.read(RRounds.Lead{bs, r2, h, t, basis, ms}, d))) == True{}: Bool}:
  match m:
    case None{}:
      e => hv => hlt => hla => hl => hm => hh => Empty.absurd(
        {Force.above(r1, RRounds.Promise.force(ms, RRounds.Promise.read(RRounds.Lead{bs, r2, h, t, basis, ms}, d))) == True{}: Bool},
        Shared.Bool.false_ne_true(hv)
      )
    case Some{RRounds.Ballot{w, t1, Types.Cast.Pass{r}}}:
      e => hv => hlt => hla => hl => hm => hh => Empty.absurd(
        {Force.above(r1, RRounds.Promise.force(ms, RRounds.Promise.read(RRounds.Lead{bs, r2, h, t, basis, ms}, d))) == True{}: Bool},
        Shared.Bool.false_ne_true(hv)
      )
    case Some{RRounds.Ballot{+w, +t1, Types.Cast.Vote{+r, +q, +b}}}:
      e => hv => hlt => hla => hl => hm => hh => Ballot.counts_by(
        {Force.above(r1, RRounds.Promise.force(ms, RRounds.Promise.read(RRounds.Lead{bs, r2, h, t, basis, ms}, d))) == True{}: Bool},
        bs,
        d,
        r1,
        w,
        t1,
        r,
        q,
        b,
        Lists.List.pick_hit(
          ~RRounds.Ballot,
          ~RRounds.Roll,
          ~RRounds.Ballot.counts,
          bs,
          RRounds.Roll{bs, d, r1},
          RRounds.Ballot{w, t1, Types.Cast.Vote{r, q, b}}
        )(e),
        hdt => hda => Promise.read_above(bs, h, t, r2, p2, basis, ms, d, t1, r1, p1, b)(hlt)(hla)(hl)(hm)(hdt)((
            %Coded.Pick.is_eq_sound(q, p1)(hv): {RRounds.Ballots.at(bs, d, t1) == Some{Types.Cast.Vote{r1, _, b}}: Maybe<&2, Types.Cast>}
            hda))(hh)
      )

# Lead.met, with the node x and what holds of it apart
def Lead.met.of(
  +bs: List<&2, RRounds.Ballot>,
  +h: String,
  +t: Nat,
  +r2: Nat,
  +p2: Types.Pick,
  +basis: List<&2, Types.Ref>,
  +ms: List<&2, RRounds.Mind>,
  +ds: List<&2, String>,
  +r1: Nat,
  +p1: Types.Pick,
  +x: String,
  hin: {List.contains(~String, ~String.eq, ds, x) == True{}: Bool},
  w: {RRounds.Tally.voted(RRounds.Tally{bs, r1, p1}, x) == True{}: Bool} & {RRounds.Promise.held(RRounds.Lead{bs, r2, h, t, basis, ms}, x) == True{}: Bool},
  hlt: {RRounds.Seen.takes(r2, RRounds.Chain.seen(bs, h, t)) == True{}: Bool},
  hla: {RRounds.Ballots.at(bs, h, t) == Some{Types.Cast.Vote{r2, p2, basis}}: Maybe<&2, Types.Cast>},
  hl: {Nat.is_le(1n+r1, r2) == True{}: Bool},
  hm: {List.get(&2, RRounds.Mind, ms, r1) == Some{RRounds.Mind.Sound{p1}}: Maybe<&2, RRounds.Mind>}
) -> {Force.above(r1, RRounds.Lead.force(RRounds.Lead{bs, r2, h, t, basis, ms}, ds)) == True{}: Bool}:
  (hv, hp) = w
  Lead.force_above(ds, RRounds.Lead{bs, r2, h, t, basis, ms}, x, r1)(hin)(
    Vote.read_above(RRounds.Vote.of(bs, x, r1), bs, h, t, r2, p2, basis, ms, x, r1, p1)({==})(hv)(hlt)(hla)(hl)(hm)(hp)
  )

# Lead.met, with the node x apart
def Lead.met.at(
  +bs: List<&2, RRounds.Ballot>,
  +h: String,
  +t: Nat,
  +r2: Nat,
  +p2: Types.Pick,
  +basis: List<&2, Types.Ref>,
  +ms: List<&2, RRounds.Mind>,
  +ds: List<&2, String>,
  +r1: Nat,
  +p1: Types.Pick,
  +x: String,
  w: {List.contains(~String, ~String.eq, ds, x) == True{}: Bool} & ({RRounds.Tally.voted(RRounds.Tally{bs, r1, p1}, x) == True{}: Bool} & {RRounds.Promise.held(RRounds.Lead{bs, r2, h, t, basis, ms}, x) == True{}: Bool}),
  hlt: {RRounds.Seen.takes(r2, RRounds.Chain.seen(bs, h, t)) == True{}: Bool},
  hla: {RRounds.Ballots.at(bs, h, t) == Some{Types.Cast.Vote{r2, p2, basis}}: Maybe<&2, Types.Cast>},
  hl: {Nat.is_le(1n+r1, r2) == True{}: Bool},
  hm: {List.get(&2, RRounds.Mind, ms, r1) == Some{RRounds.Mind.Sound{p1}}: Maybe<&2, RRounds.Mind>}
) -> {Force.above(r1, RRounds.Lead.force(RRounds.Lead{bs, r2, h, t, basis, ms}, ds)) == True{}: Bool}:
  (hin, hvp) = w
  Lead.met.of(bs, h, t, r2, p2, basis, ms, ds, r1, p1, x, hin, hvp, hlt, hla, hl, hm)

# the nodes ds bind a lead of the round r2 to r1 or above, when one of them
# (w) gave it a promise and cast a counted vote of the round r1, below r2,
# for the pick of the sound lead of the round
def Lead.met(
  +bs: List<&2, RRounds.Ballot>,
  +h: String,
  +t: Nat,
  +r2: Nat,
  +p2: Types.Pick,
  +basis: List<&2, Types.Ref>,
  +ms: List<&2, RRounds.Mind>,
  +ds: List<&2, String>,
  +r1: Nat,
  +p1: Types.Pick,
  w: Exists(String, x => {List.contains(~String, ~String.eq, ds, x) == True{}: Bool} & ({RRounds.Tally.voted(RRounds.Tally{bs, r1, p1}, x) == True{}: Bool} & {RRounds.Promise.held(RRounds.Lead{bs, r2, h, t, basis, ms}, x) == True{}: Bool})),
  hlt: {RRounds.Seen.takes(r2, RRounds.Chain.seen(bs, h, t)) == True{}: Bool},
  hla: {RRounds.Ballots.at(bs, h, t) == Some{Types.Cast.Vote{r2, p2, basis}}: Maybe<&2, Types.Cast>},
  hl: {Nat.is_le(1n+r1, r2) == True{}: Bool},
  hm: {List.get(&2, RRounds.Mind, ms, r1) == Some{RRounds.Mind.Sound{p1}}: Maybe<&2, RRounds.Mind>}
) -> {Force.above(r1, RRounds.Lead.force(RRounds.Lead{bs, r2, h, t, basis, ms}, ds)) == True{}: Bool}:
  (x, pr) = w
  Lead.met.at(bs, h, t, r2, p2, basis, ms, ds, r1, p1, x, pr, hlt, hla, hl, hm)

# One pick
# --------

# Round.sound_one.at, once the lead of the round r2 is known to be bound to
# the pick p2 of a sound lead of a round r3 that is r1 or above
def Round.sound_one.end(
  +bs: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +r1: Nat,
  +r2: Nat,
  +p1: Types.Pick,
  +p2: Types.Pick,
  +r3: Nat,
  ih: (@r: Nat -> @q: Types.Pick -> {Nat.is_le(1n+r1, r) == True{}: Bool} -> {Nat.is_le(1n+r, r2) == True{}: Bool} -> {Round.mind(bs, ds, k, r) == RRounds.Mind.Sound{q}: RRounds.Mind} -> {p1 == q: Types.Pick})
) -> {Round.mind(bs, ds, k, r1) == RRounds.Mind.Sound{p1}: RRounds.Mind} -> {Nat.is_le(r1, r3) == True{}: Bool} -> {Mind.is(p2, List.get(&2, RRounds.Mind, RRounds.Rounds.minds(bs, ds, k, r2), r3)) == True{}: Bool} -> {p1 == p2: Types.Pick}:
  h1 => +ha => +hmi => Lists.Bool.by(
    c => {p1 == p2: Types.Pick},
    Nat.is_le(1n+r1, r3),
    et => ih(r3)(p2)(et)(Minds.got_under(bs, ds, k, r2, r3, p2)(hmi))(Minds.got_mind(bs, ds, k, r2, r3, p2)(hmi)),
    ef => Mind.sound_inj(
      p1,
      p2,
      Equal.trans(
        RRounds.Mind,
        RRounds.Mind.Sound{p1},
        Round.mind(bs, ds, k, r3),
        RRounds.Mind.Sound{p2},
        Equal.sym(RRounds.Mind, Round.mind(bs, ds, k, r3), RRounds.Mind.Sound{p1}, (
            %Shared.Nat.le_nlt_eq(r1, r3)(ha)(ef): {Round.mind(bs, ds, k, _) == RRounds.Mind.Sound{p1}: RRounds.Mind}
            h1)),
        Minds.got_mind(bs, ds, k, r2, r3, p2)(hmi)
      )
    )
  )

# Round.sound_one.go, where m is the vote of the round r2 of the node h whose
# turn it is, and ih the same of each round between r1 and r2
def Round.sound_one.at(
  m: Maybe<&2, RRounds.Ballot>,
  +bs: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +r1: Nat,
  +r2: Nat,
  +p1: Types.Pick,
  +p2: Types.Pick,
  +h: String,
  ih: (@r: Nat -> @q: Types.Pick -> {Nat.is_le(1n+r1, r) == True{}: Bool} -> {Nat.is_le(1n+r, r2) == True{}: Bool} -> {Round.mind(bs, ds, k, r) == RRounds.Mind.Sound{q}: RRounds.Mind} -> {p1 == q: Types.Pick})
) -> {
  RRounds.Vote.of(bs, h, r2) == m: Maybe<&2, RRounds.Ballot>
} -> {Round.mind(bs, ds, k, r1) == RRounds.Mind.Sound{p1}: RRounds.Mind} -> {
  RRounds.Tally.most(bs, ds, r1, p1) == True{}: Bool
} -> {Nat.is_le(1n+r1, r2) == True{}: Bool} -> {
  RRounds.Lead.mind.at(bs, ds, RRounds.Rounds.minds(bs, ds, k, r2), r2, h, m) == RRounds.Mind.Sound{p2}: RRounds.Mind
} -> {p1 == p2: Types.Pick}:
  match m:
    case None{}:
      e => h1 => hm => hl => hs => Empty.absurd({p1 == p2: Types.Pick}, Shared.Bool.false_ne_true(Mind.sound_of(RRounds.Mind.Open{}, p2, hs)))
    case Some{RRounds.Ballot{v, t, Types.Cast.Pass{r}}}:
      e => h1 => hm => hl => hs => Empty.absurd({p1 == p2: Types.Pick}, Shared.Bool.false_ne_true(Mind.sound_of(RRounds.Mind.Open{}, p2, hs)))
    case Some{RRounds.Ballot{+v, +t, Types.Cast.Vote{+r, +p, +basis}}}:
      e => +h1 => hm => +hl => +hs => Ballot.counts_by(
        {p1 == p2: Types.Pick},
        bs,
        h,
        r2,
        v,
        t,
        r,
        p,
        basis,
        Lists.List.pick_hit(
          ~RRounds.Ballot,
          ~RRounds.Roll,
          ~RRounds.Ballot.counts,
          bs,
          RRounds.Roll{bs, h, r2},
          RRounds.Ballot{v, t, Types.Cast.Vote{r, p, basis}}
        )(e),
        hlt => hla => Mind.of_bound(
          RRounds.Lead.force(RRounds.Lead{bs, r2, h, t, basis, RRounds.Rounds.minds(bs, ds, k, r2)}, ds),
          RRounds.Lead.most(RRounds.Lead{bs, r2, h, t, basis, RRounds.Rounds.minds(bs, ds, k, r2)}, ds),
          RRounds.Rounds.minds(bs, ds, k, r2),
          p,
          p2,
          r1,
          {p1 == p2: Types.Pick},
          +r3 => ha3 => hmi => Round.sound_one.end(bs, ds, k, r1, r2, p1, p2, r3, ih)(h1)(ha3)(hmi)
        )(hs)(
          Lead.met(
            bs,
            h,
            t,
            r2,
            p,
            basis,
            RRounds.Rounds.minds(bs, ds, k, r2),
            ds,
            r1,
            p1,
            Lists.List.most_meet(
              ~String,
              ~RRounds.Tally,
              ~RRounds.Lead,
              ~RRounds.Tally.voted,
              ~RRounds.Promise.held,
              ~String.eq,
              ~Texts.String.laws(),
              ds,
              RRounds.Tally{bs, r1, p1},
              RRounds.Lead{bs, r2, h, t, basis, RRounds.Rounds.minds(bs, ds, k, r2)}
            )(hm)(
              Mind.of_most(
                RRounds.Lead.force(RRounds.Lead{bs, r2, h, t, basis, RRounds.Rounds.minds(bs, ds, k, r2)}, ds),
                RRounds.Lead.most(RRounds.Lead{bs, r2, h, t, basis, RRounds.Rounds.minds(bs, ds, k, r2)}, ds),
                p,
                p2
              )(hs)
            ),
            hlt,
            hla,
            hl,
            (
              %h1: {List.get(&2, RRounds.Mind, RRounds.Rounds.minds(bs, ds, k, r2), r1) == Some{_}: Maybe<&2, RRounds.Mind>}
              Minds.get(r2, bs, ds, k, r1)(hl))
          )
        )(Lead.force_fits(ds, RRounds.Lead{bs, r2, h, t, basis, RRounds.Rounds.minds(bs, ds, k, r2)}))
      )

# Round.sound_one, for a round r2 that is n at most
def Round.sound_one.go(
  n: Nat,
  +bs: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +r1: Nat,
  +r2: Nat,
  +p1: Types.Pick,
  +p2: Types.Pick
) -> {
  Nat.is_le(r2, n) == True{}: Bool
} -> {Round.mind(bs, ds, k, r1) == RRounds.Mind.Sound{p1}: RRounds.Mind} -> {
  RRounds.Tally.most(bs, ds, r1, p1) == True{}: Bool
} -> {Nat.is_le(1n+r1, r2) == True{}: Bool} -> {Round.mind(bs, ds, k, r2) == RRounds.Mind.Sound{p2}: RRounds.Mind} -> {p1 == p2: Types.Pick}:
  match n:
    case 0n:
      hn => h1 => hm => hl => hs => Empty.absurd(
        {p1 == p2: Types.Pick},
        Nat.above_not(r1, r2)(hl)(
          Shared.Nat.le_trans(r2, 0n, r1)(hn)(Shared.Nat.le_zero(r1))
        )
      )
    case 1n+(+j):
      +hn => +h1 => +hm => +hl => hs => Round.sound_one.at(
        RRounds.Vote.of(bs, RRounds.Turn.of(ds, Nat.add(k, r2)), r2),
        bs,
        ds,
        k,
        r1,
        r2,
        p1,
        p2,
        RRounds.Turn.of(ds, Nat.add(k, r2)),
        +r3 => +q => ha => hu => hmi => Round.sound_one.go(j, bs, ds, k, r1, r3, p1, q)(
          Shared.Nat.le_trans(1n+r3, r2, 1n+j)(hu)(hn)
        )(h1)(hm)(ha)(hmi)
      )({==})(h1)(hm)(hl)(hs)

# once more than half of the nodes cast a counted vote for the pick p1 of the
# sound lead of a round r1, the sound lead of each later round r2 is for it
def Round.sound_one(
  +bs: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +r1: Nat,
  +r2: Nat,
  +p1: Types.Pick,
  +p2: Types.Pick
) -> {Round.mind(bs, ds, k, r1) == RRounds.Mind.Sound{p1}: RRounds.Mind} -> {
  RRounds.Tally.most(bs, ds, r1, p1) == True{}: Bool
} -> {Nat.is_le(1n+r1, r2) == True{}: Bool} -> {Round.mind(bs, ds, k, r2) == RRounds.Mind.Sound{p2}: RRounds.Mind} -> {p1 == p2: Types.Pick}:
  Round.sound_one.go(r2, bs, ds, k, r1, r2, p1, p2)(Shared.Nat.le_refl(r2))

# two rounds of one slot decide one pick: once more than half of the nodes
# cast a sound vote for a pick in a round, every sound vote of a later round
# is for it
def Safety.won_one(
  +bs: List<&2, RRounds.Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +r1: Nat,
  +r2: Nat,
  +p1: Types.Pick,
  +p2: Types.Pick
) -> Round.Won(bs, ds, k, r1, p1) -> Round.Won(bs, ds, k, r2, p2) -> {p1 == p2: Types.Pick}:
  +w1 => +w2 => Lists.Bool.by(
    c => {p1 == p2: Types.Pick},
    Nat.is_le(1n+r1, r2),
    et => Round.sound_one(bs, ds, k, r1, r2, p1, p2)(
      Round.won_sound(Round.mind(bs, ds, k, r1), bs, ds, r1, p1)(w1)
    )(Round.won_most(Round.mind(bs, ds, k, r1), bs, ds, r1, p1)(w1))(et)(
      Round.won_sound(Round.mind(bs, ds, k, r2), bs, ds, r2, p2)(w2)
    ),
    ef => Lists.Bool.by(
      c => {p1 == p2: Types.Pick},
      Nat.is_le(1n+r2, r1),
      et2 => Equal.sym(
        Types.Pick,
        p2,
        p1,
        Round.sound_one(bs, ds, k, r2, r1, p2, p1)(
          Round.won_sound(Round.mind(bs, ds, k, r2), bs, ds, r2, p2)(w2)
        )(Round.won_most(Round.mind(bs, ds, k, r2), bs, ds, r2, p2)(w2))(et2)(
          Round.won_sound(Round.mind(bs, ds, k, r1), bs, ds, r1, p1)(w1)
        )
      ),
      ef2 => Mind.sound_inj(
        p1,
        p2,
        Equal.trans(
          RRounds.Mind,
          RRounds.Mind.Sound{p1},
          Round.mind(bs, ds, k, r1),
          RRounds.Mind.Sound{p2},
          Equal.sym(
            RRounds.Mind,
            Round.mind(bs, ds, k, r1),
            RRounds.Mind.Sound{p1},
            Round.won_sound(Round.mind(bs, ds, k, r1), bs, ds, r1, p1)(w1)
          ),
          (
            %Shared.Nat.le_nlt_eq(r2, r1)(Shared.Nat.nle_succ_le(1n+r1, r2)(ef))(ef2): {Round.mind(bs, ds, k, _) == RRounds.Mind.Sound{p2}: RRounds.Mind}
            Round.won_sound(Round.mind(bs, ds, k, r2), bs, ds, r2, p2)(w2))
        )
      )
    )
  )
