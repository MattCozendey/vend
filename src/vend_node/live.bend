import Base
import ../shared/shared/ledger.bend as Ledgers
import ../shared/shared/shared/shared/shared.bend as Shared
import ../shared/shared/shared/text.bend as Texts
import ./answers.bend as Answers
import ./codes.bend as Coded
import ./facts.bend as Facts
import ./lines.bend as Lines
import ./moves.bend as Moves
import ./rounds.bend as Rounds
import ./run/answers.bend as RAnswers
import ./run/facts.bend as RFacts
import ./run/lines.bend as RLines
import ./run/rounds.bend as RRounds
import ./run/known.bend as RKnown
import ./run/work.bend as RWorks
import ./shared/lists.bend as Lists
import ./spec.bend as Spec
import ./types.bend as Types
import ./versions.bend as Versions
import ./work.bend as Works

# What a node does for sure
# -------------------------

# the facts s with the ballot m, if any, of the node name are wider
def Work.does_wider.of(
  +name: String,
  +s: Facts.Facts(),
  m: Maybe<&2, RWorks.Plan>
) -> {Facts.Facts.wider(s, Works.Work.cast(s, name, m)) == True{}: Bool}:
  match m:
    case None{}:
      Facts.Facts.wider_refl(s)
    case Some{RWorks.Plan{+st, +x}}:
      Lists.Bool.by(
        b => {
          Facts.Facts.wider(
            s,
            Shared.Bool.when(
              Facts.Facts(),
              b,
              u => s,
              u => Facts.Facts.add(s, Types.Fact.Vote{name, st, x})
            )
          )
            == True{}: Bool
        },
        Facts.Facts.cast(s, name, st),
        et => Facts.Facts.wider_refl(s),
        ef => Facts.Facts.add_wider(s, Types.Fact.Vote{name, st, x})
      )

# the facts of a node are wider after it works
def Work.does_wider(
  +name: String,
  +s: Facts.Facts()
) -> {Facts.Facts.wider(s, Works.Work.does(s, name)) == True{}: Bool}:
  Work.does_wider.of(name, s, Works.Work.plan(s, name))

# the facts stay sound with the ballot m, if any, of the node name: it is cast
# only where the node holds no ballot of its own
def Work.does_ok.of(
  +name: String,
  +s: Facts.Facts(),
  m: Maybe<&2, RWorks.Plan>
) -> {
  Facts.Facts.ok(name, s) == True{}: Bool
} -> {Facts.Facts.ok(name, Works.Work.cast(s, name, m)) == True{}: Bool}:
  match m:
    case None{}:
      ok => ok
    case Some{RWorks.Plan{+st, +x}}:
      Lists.Bool.by(
        b => {
          Facts.Facts.cast(s, name, st) == b: Bool
        } -> {
          Facts.Facts.ok(name, s) == True{}: Bool
        } -> {
          Facts.Facts.ok(
            name,
            Shared.Bool.when(
              Facts.Facts(),
              b,
              u => s,
              u => Facts.Facts.add(s, Types.Fact.Vote{name, st, x})
            )
          )
            == True{}: Bool
        },
        Facts.Facts.cast(s, name, st),
        et => ec => ok => ok,
        ef => ec => ok => Facts.Facts.add_cast_ok(name, s, st, x)(ok)(ec)
      )({==})

# the facts of a node stay sound when it works
def Work.does_ok(
  +name: String,
  +s: Facts.Facts()
) -> {
  Facts.Facts.ok(name, s) == True{}: Bool
} -> {Facts.Facts.ok(name, Works.Work.does(s, name)) == True{}: Bool}:
  ok => Work.does_ok.of(name, s, Works.Work.plan(s, name))(ok)

# Tools
# -----

# what follows from a witness and what holds of it follows
def Ex.by(-A: Type, -B: @-x: A -> Type, -Q: Type, r: Exists(A, B), k: @x: A -> B(x) -> Q) -> Q:
  (x, p) = r
  k(x)(p)

# the first of two
def And.left(-A: Type, -B: Type, r: A & B) -> A:
  (a, b) = r
  a

# what follows from two follows
def And.by(-A: Type, -B: Type, -Q: Type, r: A & B, k: A -> B -> Q) -> Q:
  (a, b) = r
  k(a)(b)

# y is true when it is x, and x is true
def Bool.via(-x: Bool, -y: Bool, e: {x == y: Bool}, h: {x == True{}: Bool}) -> {y == True{}: Bool}:
  Equal.trans(Bool, y, x, True{}, Equal.sym(Bool, x, y, e), h)

# x is true when it is y, and y is true
def Bool.back(-x: Bool, -y: Bool, e: {x == y: Bool}, h: {y == True{}: Bool}) -> {x == True{}: Bool}:
  Equal.trans(Bool, x, y, True{}, e, h)

# no number is below 0
def Nat.lt_zero(n: Nat) -> {Nat.is_lt(n, 0n) == True{}: Bool} -> Empty:
  match n:
    case 0n:
      h => Shared.Bool.false_ne_true(h)
    case 1n+p:
      h => Shared.Bool.false_ne_true(h)

# List.some_at for h <> r, from an element of r
def List.some_at.up(
  ~A: Data,
  ~V: Data,
  ~p: V -> A -> Bool,
  -h: A,
  -r: List<&2, A>,
  -g: V,
  w: Exists(
    Nat,
    k => Exists(
      A,
      x => {List.get(&2, A, r, k) == Some{x}: Maybe<&2, A>} & {p(g)(x) == True{}: Bool}
    )
  )
) -> Exists(
  Nat,
  k => Exists(
    A,
    x => {List.get(&2, A, h <> r, k) == Some{x}: Maybe<&2, A>} & {p(g)(x) == True{}: Bool}
  )
):
  (k, w2) = w
  (x, q) = w2
  (1n+k, (x, q))

# a list that p holds of some element of holds, at an index, an element that
# p holds of
def List.some_at(
  ~A: Data,
  ~V: Data,
  ~p: V -> A -> Bool,
  xs: List<&2, A>,
  +g: V
) -> {
  Shared.List.some(~A, ~V, ~p, xs, g) == True{}: Bool
} -> Exists(
  Nat,
  k => Exists(A, x => {List.get(&2, A, xs, k) == Some{x}: Maybe<&2, A>} & {p(g)(x) == True{}: Bool})
):
  match xs:
    case Nil{}:
      h => Empty.absurd(
        Exists(
          Nat,
          k => Exists(A, x => {None{} == Some{x}: Maybe<&2, A>} & {p(g)(x) == True{}: Bool})
        ),
        Shared.Bool.false_ne_true(h)
      )
    case Con{+z, +r}:
      Lists.Bool.by(
        c => {
          List.any.if(u => Shared.List.some(~A, ~V, ~p, r, g), c) == True{}: Bool
        } -> Exists(
          Nat,
          k => Exists(
            A,
            x => {List.get(&2, A, z <> r, k) == Some{x}: Maybe<&2, A>} & {p(g)(x) == True{}: Bool}
          )
        ),
        p(g)(z),
        et => h => (0n, (z, ({==}, et))),
        ef => h => List.some_at.up(~A, ~V, ~p, z, r, g, List.some_at(~A, ~V, ~p, r, g)(h))
      )

# what follows from an index and an element that p holds of follows
def List.some_at.by(
  -A: Data,
  -V: Data,
  -p: V -> A -> Bool,
  -xs: List<&2, A>,
  -g: V,
  -Q: Type,
  w: Exists(
    Nat,
    k => Exists(
      A,
      x => {List.get(&2, A, xs, k) == Some{x}: Maybe<&2, A>} & {p(g)(x) == True{}: Bool}
    )
  ),
  f: @k: Nat -> @x: A -> {
    List.get(&2, A, xs, k) == Some{x}: Maybe<&2, A>
  } -> {p(g)(x) == True{}: Bool} -> Q
) -> Q:
  (k, w2) = w
  (x, q) = w2
  (a, b) = q
  f(k)(x)(a)(b)

# the ask of the fact f, or d when f is a vote
def Fact.ask_or(d: Types.Ask, f: Types.Fact) -> Types.Ask:
  match f:
    case Types.Fact.Ask{a}:
      a
    case Types.Fact.Vote{v, st, pk}:
      d

# two equal facts that are asks are of one ask
def Fact.ask_inj(
  +a: Types.Ask,
  +b: Types.Ask
) -> {Types.Fact.Ask{a} == Types.Fact.Ask{b}: Types.Fact} -> {a == b: Types.Ask}:
  e => Equal.cong(
    Types.Fact,
    Types.Ask,
    f => Fact.ask_or(a, f),
    Types.Fact.Ask{a},
    Types.Fact.Ask{b},
    e
  )

# a vote is no ask
def Fact.vote_not_ask(
  -P: Type,
  +v: String,
  +st: Types.Step,
  +pk: Types.Cast,
  +a: Types.Ask
) -> {Types.Fact.Vote{v, st, pk} == Types.Fact.Ask{a}: Types.Fact} -> P:
  e => Empty.absurd(
    P,
    Shared.Bool.false_ne_true(
      Equal.cong(
        Types.Fact,
        Bool,
        f => Moves.Fact.is_ask(f),
        Types.Fact.Vote{v, st, pk},
        Types.Fact.Ask{a},
        e
      )
    )
  )

# an ask that is kept is among the kept
def Asks.put_head(
  +a: Types.Ask,
  -r: List<&2, Types.Ask>,
  keep: Bool
) -> {
  keep == True{}: Bool
} -> {
  List.contains(
    ~Types.Ask,
    ~Coded.Ask.is_eq,
    List.filter.put(Types.Ask, a, r, keep),
    a
  )
    == True{}: Bool
}:
  match keep:
    case True{}:
      h => Lists.List.contains_head(~Types.Ask, ~Coded.Ask.is_eq, ~Coded.Ask.laws(), a, r)
    case False{}:
      h => Empty.absurd(
        {List.contains(~Types.Ask, ~Coded.Ask.is_eq, r, a) == True{}: Bool},
        Shared.Bool.false_ne_true(h)
      )

# an ask of the rest is among the kept
def Asks.put_rest(
  +a: Types.Ask,
  +r: List<&2, Types.Ask>,
  keep: Bool,
  +x: Types.Ask
) -> {
  List.contains(~Types.Ask, ~Coded.Ask.is_eq, r, x) == True{}: Bool
} -> {
  List.contains(
    ~Types.Ask,
    ~Coded.Ask.is_eq,
    List.filter.put(Types.Ask, a, r, keep),
    x
  )
    == True{}: Bool
}:
  match keep:
    case True{}:
      h => Shared.List.contains_cons(~Types.Ask, ~Coded.Ask.is_eq, a, r, x)(h)
    case False{}:
      h => h

# an ask among the kept is the first, which was kept, or one of the rest
def Asks.put_by(
  -P: Type,
  +a: Types.Ask,
  +r: List<&2, Types.Ask>,
  keep: Bool,
  +x: Types.Ask,
  hin: {
    List.contains(
      ~Types.Ask,
      ~Coded.Ask.is_eq,
      List.filter.put(Types.Ask, a, r, keep),
      x
    )
      == True{}: Bool
  },
  fa: {a == x: Types.Ask} -> {keep == True{}: Bool} -> P,
  fb: {List.contains(~Types.Ask, ~Coded.Ask.is_eq, r, x) == True{}: Bool} -> P
) -> P:
  match keep:
    case True{}:
      Lists.List.contains_cons_by(
        ~Types.Ask,
        ~Coded.Ask.is_eq,
        ~Coded.Ask.laws(),
        P,
        a,
        r,
        x,
        hin,
        e => fa(e)({==}),
        fb
      )
    case False{}:
      fb(hin)

# Views
# -----

# an ask among fs that writes as g says is one of the writes of fs
def Writes.of_in(
  fs: List<&2, Types.Fact>,
  +g: RAnswers.Place,
  +a: Types.Ask
) -> {
  List.contains(~Types.Fact, ~Coded.Fact.is_eq, fs, Types.Fact.Ask{a}) == True{}: Bool
} -> {
  RAnswers.Ask.writes(g, a) == True{}: Bool
} -> {List.contains(~Types.Ask, ~Coded.Ask.is_eq, RAnswers.Writes.of(fs, g), a) == True{}: Bool}:
  match fs:
    case Nil{}:
      hin => hw => Empty.absurd({False{} == True{}: Bool}, Shared.Bool.false_ne_true(hin))
    case Con{Types.Fact.Vote{+v, +st, +pk}, +rest}:
      hin => hw => Lists.List.contains_cons_by(
        ~Types.Fact,
        ~Coded.Fact.is_eq,
        ~Coded.Fact.laws(),
        {
          List.contains(~Types.Ask, ~Coded.Ask.is_eq, RAnswers.Writes.of(rest, g), a) == True{}: Bool
        },
        Types.Fact.Vote{v, st, pk},
        rest,
        Types.Fact.Ask{a},
        hin,
        e => Fact.vote_not_ask(
          {
            List.contains(
              ~Types.Ask,
              ~Coded.Ask.is_eq,
              RAnswers.Writes.of(rest, g),
              a
            )
              == True{}: Bool
          },
          v,
          st,
          pk,
          a
        )(e),
        c => Writes.of_in(rest, g, a)(c)(hw)
      )
    case Con{Types.Fact.Ask{+b}, +rest}:
      hin => +hw => Lists.List.contains_cons_by(
        ~Types.Fact,
        ~Coded.Fact.is_eq,
        ~Coded.Fact.laws(),
        {
          List.contains(
            ~Types.Ask,
            ~Coded.Ask.is_eq,
            List.filter.put(Types.Ask, b, RAnswers.Writes.of(rest, g), RAnswers.Ask.writes(g, b)),
            a
          )
            == True{}: Bool
        },
        Types.Fact.Ask{b},
        rest,
        Types.Fact.Ask{a},
        hin,
        e => (
          %Equal.sym(Types.Ask, b, a, Fact.ask_inj(b, a)(e)): {List.contains(~Types.Ask, ~Coded.Ask.is_eq, List.filter.put(Types.Ask, _, RAnswers.Writes.of(rest, g), RAnswers.Ask.writes(g, _)), a) == True{}: Bool}
          Asks.put_head(a, RAnswers.Writes.of(rest, g), RAnswers.Ask.writes(g, a))(hw)),
        c => Asks.put_rest(
          b,
          RAnswers.Writes.of(rest, g),
          RAnswers.Ask.writes(g, b),
          a
        )(Writes.of_in(rest, g, a)(c)(hw))
      )

# each of the writes of fs is an ask among fs
def Writes.of_from(
  fs: List<&2, Types.Fact>,
  +g: RAnswers.Place,
  +y: Types.Ask
) -> {
  List.contains(~Types.Ask, ~Coded.Ask.is_eq, RAnswers.Writes.of(fs, g), y) == True{}: Bool
} -> {List.contains(~Types.Fact, ~Coded.Fact.is_eq, fs, Types.Fact.Ask{y}) == True{}: Bool}:
  match fs:
    case Nil{}:
      h => h
    case Con{Types.Fact.Vote{+v, +st, +pk}, +rest}:
      h => Shared.List.contains_cons(
        ~Types.Fact,
        ~Coded.Fact.is_eq,
        Types.Fact.Vote{v, st, pk},
        rest,
        Types.Fact.Ask{y}
      )(Writes.of_from(rest, g, y)(h))
    case Con{Types.Fact.Ask{+b}, +rest}:
      h => Asks.put_by(
        {
          List.contains(
            ~Types.Fact,
            ~Coded.Fact.is_eq,
            Types.Fact.Ask{b} <> rest,
            Types.Fact.Ask{y}
          )
            == True{}: Bool
        },
        b,
        RAnswers.Writes.of(rest, g),
        RAnswers.Ask.writes(g, b),
        y,
        h,
        e => k => (
          %e: {List.contains(~Types.Fact, ~Coded.Fact.is_eq, Types.Fact.Ask{b} <> rest, Types.Fact.Ask{_}) == True{}: Bool}
          Lists.List.contains_head(~Types.Fact, ~Coded.Fact.is_eq, ~Coded.Fact.laws(), Types.Fact.Ask{b}, rest)),
        c => Shared.List.contains_cons(
          ~Types.Fact,
          ~Coded.Fact.is_eq,
          Types.Fact.Ask{b},
          rest,
          Types.Fact.Ask{y}
        )(Writes.of_from(rest, g, y)(c))
      )

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof does not run
# an ask that a node holds after it took in the ask a of a number above every
# number that it held, and that is not a, is of a lesser number
def Ask.newer(
  +name: String,
  +s: Facts.Facts(),
  +a: Types.Ask,
  +y: Types.Ask
) -> {
  Nat.is_lt(RFacts.Seq.peak(Facts.Facts.list(s)), RFacts.Ask.seq(a)) == True{}: Bool
} -> {
  Facts.Facts.has(Facts.Facts.take(name, s, Types.Fact.Ask{a}), Types.Fact.Ask{y}) == True{}: Bool
} -> (
  {y == a: Types.Ask} -> Empty
) -> {Nat.is_lt(RFacts.Ask.seq(y), RFacts.Ask.seq(a)) == True{}: Bool}:
  hlt => hy => ne => Facts.Case.or_by(
    {Nat.is_lt(RFacts.Ask.seq(y), RFacts.Ask.seq(a)) == True{}: Bool},
    Coded.Ask.is_eq(y, a),
    Facts.Facts.has(s, Types.Fact.Ask{y}),
    Bool.via(
      Facts.Facts.has(Facts.Facts.take(name, s, Types.Fact.Ask{a}), Types.Fact.Ask{y}),
      Bool.or(Coded.Ask.is_eq(y, a), Facts.Facts.has(s, Types.Fact.Ask{y})),
      Facts.Facts.take_ask_asks(name, s, a, y),
      hy
    ),
    et => Empty.absurd(
      {Nat.is_lt(RFacts.Ask.seq(y), RFacts.Ask.seq(a)) == True{}: Bool},
      ne(Coded.Ask.is_eq_sound(y, a)(et))
    ),
    hs => Shared.Nat.le_lt(
      RFacts.Ask.seq(y),
      RFacts.Seq.peak(Facts.Facts.list(s)),
      RFacts.Ask.seq(a)
    )(Facts.Facts.seq_ask(s, y)(hs))(hlt)
  )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the last write of a writer at a place, after a node took in a write of it
# there with a number above every number that it held, is that write
def Writes.top(
  +name: String,
  +s: Facts.Facts(),
  +a: Types.Ask,
  +g: RAnswers.Place
) -> {
  Nat.is_lt(RFacts.Seq.peak(Facts.Facts.list(s)), RFacts.Ask.seq(a)) == True{}: Bool
} -> {
  RAnswers.Ask.writes(g, a) == True{}: Bool
} -> {
  Lists.List.top(
    ~Types.Ask,
    ~RFacts.Ask.seq,
    RAnswers.Writes.of(Facts.Facts.list(Facts.Facts.take(name, s, Types.Fact.Ask{a})), g)
  )
    == Some{a}: Maybe<&2, Types.Ask>
}:
  +hlt => hw => Lists.List.top_one(
    ~Types.Ask,
    ~RFacts.Ask.seq,
    ~Coded.Ask.is_eq,
    ~Coded.Ask.laws(),
    RAnswers.Writes.of(Facts.Facts.list(Facts.Facts.take(name, s, Types.Fact.Ask{a})), g),
    a
  )(
    Writes.of_in(
      Facts.Facts.list(Facts.Facts.take(name, s, Types.Fact.Ask{a})),
      g,
      a
    )(
      Facts.Facts.has_in(
        Facts.Facts.take(name, s, Types.Fact.Ask{a}),
        Types.Fact.Ask{a}
      )(Facts.Facts.take_ask_has(name, s, a))
    )(hw)
  )(
    +y => hy => ne => Ask.newer(
      name,
      s,
      a,
      y
    )(
      hlt
    )(
      Facts.Facts.in_has(
        Facts.Facts.take(name, s, Types.Fact.Ask{a}),
        Types.Fact.Ask{y}
      )(Writes.of_from(Facts.Facts.list(Facts.Facts.take(name, s, Types.Fact.Ask{a})), g, y)(hy))
    )(ne)
  )

# Ask.fresh.vote, with the vote
def Ask.fresh.vote.of(
  +name: String,
  +s: Facts.Facts(),
  +a: Types.Ask,
  +c: Ledgers.Line,
  +a2: Types.Ask,
  +pins: Types.Pins,
  +k: Nat,
  hlt: {Nat.is_lt(RFacts.Seq.peak(Facts.Facts.list(s)), RFacts.Ask.seq(a)) == True{}: Bool},
  he: {Coded.Ask.is_eq(a2, a) == True{}: Bool},
  w0: Rounds.Votes.Voted(Facts.Facts.take(name, s, Types.Fact.Ask{a}), c, k, Types.Pick{a2, pins})
) -> Empty:
  (+v, w1) = w0
  (+t, w2) = w1
  (+r, w3) = w2
  (+b, hv) = w3
  Lists.Bool.clash(
    Empty,
    Nat.is_lt(RFacts.Ask.seq(a), RFacts.Ask.seq(a)),
    Shared.Nat.lt_irrefl(RFacts.Ask.seq(a)),
    Shared.Nat.le_lt(RFacts.Ask.seq(a), RFacts.Seq.peak(Facts.Facts.list(s)), RFacts.Ask.seq(a))((
        %Coded.Ask.is_eq_sound(a2, a)(he): {Nat.is_le(RFacts.Ask.seq(_), RFacts.Seq.peak(Facts.Facts.list(s))) == True{}: Bool}
        Facts.Facts.seq_vote(s, v, Types.Step.At{c, k, t}, r, a2, pins, b)(Bool.via(Facts.Facts.has(Facts.Facts.take(name, s, Types.Fact.Ask{a}), Types.Fact.Vote{v, Types.Step.At{c, k, t}, Types.Cast.Vote{r, Types.Pick{a2, pins}, b}}), Facts.Facts.has(s, Types.Fact.Vote{v, Types.Step.At{c, k, t}, Types.Cast.Vote{r, Types.Pick{a2, pins}, b}}), Facts.Facts.take_ask_votes(name, s, a, v, c, k, t, Types.Cast.Vote{r, Types.Pick{a2, pins}, b}), hv))))(hlt)
  )

# no vote that a node holds after it took in the ask a, of a number above
# every number that it held, is for the entry e made by a
def Ask.fresh.vote(
  +name: String,
  +s: Facts.Facts(),
  +a: Types.Ask,
  +c: Ledgers.Line,
  e: Types.Entry
) -> {
  Nat.is_lt(RFacts.Seq.peak(Facts.Facts.list(s)), RFacts.Ask.seq(a)) == True{}: Bool
} -> {
  Coded.Ask.is_eq(RLines.Entry.ask(e), a) == True{}: Bool
} -> Rounds.Votes.Voted(
  Facts.Facts.take(name, s, Types.Fact.Ask{a}),
  c,
  RLines.Entry.slot(e),
  RLines.Entry.pick(e)
) -> Empty:
  match e:
    case Types.Entry{Types.Pick{+a2, +pins}, +k}:
      hlt => he => w0 => Ask.fresh.vote.of(name, s, a, c, a2, pins, k, hlt, he, w0)

# an entry of the number 0 is not made by an ask of a number above n
def Ask.fresh.zero(
  +a: Types.Ask,
  +e: Types.Entry,
  +n: Nat
) -> {
  Nat.is_lt(n, RFacts.Ask.seq(a)) == True{}: Bool
} -> {
  RFacts.Ask.seq(RLines.Entry.ask(e)) == 0n: Nat
} -> {Coded.Ask.is_eq(RLines.Entry.ask(e), a) == True{}: Bool} -> Empty:
  hlt => hz => he => Nat.lt_zero(n)((
      %Equal.trans(Nat, RFacts.Ask.seq(a), RFacts.Ask.seq(RLines.Entry.ask(e)), 0n, Equal.sym(Nat, RFacts.Ask.seq(RLines.Entry.ask(e)), RFacts.Ask.seq(a), Equal.cong(Types.Ask, Nat, x => RFacts.Ask.seq(x), RLines.Entry.ask(e), a, Coded.Ask.is_eq_sound(RLines.Entry.ask(e), a)(he))), hz): {Nat.is_lt(n, _) == True{}: Bool}
      hlt))

# no version of a line, after a node took in the ask a of a number above every
# number that it held, was made by a
def View.fresh.at(
  +name: String,
  +s: Facts.Facts(),
  +a: Types.Ask,
  +c: Ledgers.Line,
  +vs: List<&2, Types.Entry>,
  k: Nat,
  +e: Types.Entry
) -> {
  Nat.is_lt(RFacts.Seq.peak(Facts.Facts.list(s)), RFacts.Ask.seq(a)) == True{}: Bool
} -> {
  Lines.Line.versions(
    Facts.Facts.take(name, s, Types.Fact.Ask{a}),
    c
  )
    == Some{vs}: Maybe<&2, List<&2, Types.Entry>>
} -> {
  List.get(&2, Types.Entry, vs, k) == Some{e}: Maybe<&2, Types.Entry>
} -> {RAnswers.Entry.made_by(a, e) == True{}: Bool} -> Empty:
  match k:
    case 0n:
      hlt => hv => hg => he => Ask.fresh.zero(
        a,
        e,
        RFacts.Seq.peak(Facts.Facts.list(s))
      )(
        hlt
      )(
        And.left(
          {RFacts.Ask.seq(RLines.Entry.ask(e)) == 0n: Nat},
          {RLines.Request.opens(RLines.Ask.request(RLines.Entry.ask(e))) == True{}: Bool},
          Versions.Line.versions_zero(
            Facts.Facts.take(name, s, Types.Fact.Ask{a}),
            c,
            vs,
            e
          )(hv)(hg)
        )
      )(he)
    case 1n+(+j):
      hlt => hv => hg => he => Ask.fresh.vote(name, s, a, c, e)(hlt)(he)(
        Versions.Line.versions_voted(
          Facts.Facts.take(name, s, Types.Fact.Ask{a}),
          c,
          vs,
          j,
          e
        )(hv)(hg)
      )

# no version of a line, of the versions m after a node took in the ask a of a
# number above every number that it held, was made by a
def View.fresh(
  +name: String,
  +s: Facts.Facts(),
  +a: Types.Ask,
  +c: Ledgers.Line,
  m: Maybe<&2, List<&2, Types.Entry>>
) -> {
  Nat.is_lt(RFacts.Seq.peak(Facts.Facts.list(s)), RFacts.Ask.seq(a)) == True{}: Bool
} -> {
  Lines.Line.versions(
    Facts.Facts.take(name, s, Types.Fact.Ask{a}),
    c
  )
    == m: Maybe<&2, List<&2, Types.Entry>>
} -> {RAnswers.View.decided(a, m) == False{}: Bool}:
  match m:
    case None{}:
      hlt => hv => {==}
    case Some{+vs}:
      hlt => hv => Facts.Case.false_of(
        Shared.List.some(~Types.Entry, ~Types.Ask, ~RAnswers.Entry.made_by, vs, a)
      )(
        ht => List.some_at.by(
          Types.Entry,
          Types.Ask,
          RAnswers.Entry.made_by,
          vs,
          a,
          Empty,
          List.some_at(~Types.Entry, ~Types.Ask, ~RAnswers.Entry.made_by, vs, a)(ht),
          +k => +e => hg => he => View.fresh.at(name, s, a, c, vs, k, e)(hlt)(hv)(hg)(he)
        )
      )

# a writer reads its own write a at once, when the number of a is above every
# number that the node held
def View.reads_own.at(
  +name: String,
  +s: Facts.Facts(),
  +a: Types.Ask,
  +b: Ledgers.Line,
  +p: String,
  +w: String
) -> {
  Nat.is_lt(RFacts.Seq.peak(Facts.Facts.list(s)), RFacts.Ask.seq(a)) == True{}: Bool
} -> {
  RAnswers.Ask.writes(RAnswers.Place{w, b, p}, a) == True{}: Bool
} -> {
  Answers.View.at(
    Facts.Facts.take(name, s, Types.Fact.Ask{a}),
    w,
    b,
    p
  )
    == Some{RAnswers.Request.words(RLines.Ask.request(a))}: Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  +hlt => hw => (
    %Equal.sym(Maybe<&2, Types.Ask>, Lists.List.top(~Types.Ask, ~RFacts.Ask.seq, RAnswers.Writes.of(Facts.Facts.list(Facts.Facts.take(name, s, Types.Fact.Ask{a})), RAnswers.Place{w, b, p})), Some{a}, Writes.top(name, s, a, RAnswers.Place{w, b, p})(hlt)(hw)): {Answers.View.of(Facts.Facts.take(name, s, Types.Fact.Ask{a}), b, p, _) == Some{RAnswers.Request.words(RLines.Ask.request(a))}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
    %Equal.sym(Bool, RAnswers.View.decided(a, Lines.Line.versions(Facts.Facts.take(name, s, Types.Fact.Ask{a}), b)), False{}, View.fresh(name, s, a, b, Lines.Line.versions(Facts.Facts.take(name, s, Types.Fact.Ask{a}), b))(hlt)({==})): {Shared.Bool.when(Maybe<&2, Maybe<&2, List<&2, U32>>>, _, u => Answers.View.newest(Facts.Facts.take(name, s, Types.Fact.Ask{a}), b, p, Lines.Line.versions(Facts.Facts.take(name, s, Types.Fact.Ask{a}), b)), u => Some{RAnswers.Request.words(RLines.Ask.request(a))}) == Some{RAnswers.Request.words(RLines.Ask.request(a))}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
    {==})

# a writer reads its own write at once
def View.reads_own(
  +name: String,
  +s: Facts.Facts(),
  +i: Ledgers.Id,
  +b: Ledgers.Line,
  +p: String,
  +ws: Maybe<&2, List<&2, U32>>
) -> {
  Answers.View.at(
    Facts.Facts.ask(name, s, i, Spec.Request.Write{b, p, ws}),
    Spec.Id.writer(i),
    b,
    p
  )
    == Some{ws}: Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  match i:
    case Ledgers.Id{+w, +rq}:
      View.reads_own.at(
        name,
        s,
        Types.Ask{
          Ledgers.Id{w, rq},
          1n+RFacts.Seq.peak(Facts.Facts.list(s)),
          Spec.Request.Write{b, p, ws}
        },
        b,
        p,
        w
      )(
        Shared.Nat.lt_succ(RFacts.Seq.peak(Facts.Facts.list(s)))
      )(
        Shared.Bool.and_both(
          String.eq(w, w),
          Bool.and(Ledgers.Line.is_eq(b, b), String.eq(p, p))
        )(
          Texts.String.eq_refl(w)
        )(
          Shared.Bool.and_both(
            Ledgers.Line.is_eq(b, b),
            String.eq(p, p)
          )(Ledgers.Line.is_eq_refl(b))(Texts.String.eq_refl(p))
        )
      )

# A node that decides alone
# -------------------------

# the first of the items of a list, as many as it has, are the list
def List.take_all(
  -A: Data,
  xs: List<&2, A>
) -> {List.take(&2, A, xs, List.length(&2, A, xs)) == xs: List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.cong(
        List<&2, A>,
        List<&2, A>,
        z => h <> z,
        List.take(&2, A, t, List.length(&2, A, t)),
        t,
        List.take_all(A, t)
      )

# when List.pick gives nothing, p holds of no member of xs
def List.pick_miss(
  ~A: Data,
  ~V: Data,
  ~p: V -> A -> Bool,
  ~same: A -> A -> Bool,
  ~laws: Shared.Eq.Laws(A, same),
  xs: List<&2, A>,
  +g: V,
  +x: A
) -> {
  Lists.List.pick(~A, ~V, ~p, xs, g) == None{}: Maybe<&2, A>
} -> {List.contains(~A, ~same, xs, x) == True{}: Bool} -> {p(g)(x) == True{}: Bool} -> Empty:
  match xs:
    case Nil{}:
      hn => hin => hp => Shared.Bool.false_ne_true(hin)
    case Con{+h, +r}:
      Lists.Bool.by(
        hit => {
          List.find.if(A, h, u => Lists.List.pick(~A, ~V, ~p, r, g), hit) == None{}: Maybe<&2, A>
        } -> {
          List.contains(~A, ~same, h <> r, x) == True{}: Bool
        } -> {p(g)(x) == True{}: Bool} -> Empty,
        p(g)(h),
        et => hn => hin => hp => Lists.Maybe.some_ne_none(A, h, hn),
        ef => hn => hin => +hp => Lists.List.contains_cons_by(
          ~A,
          ~same,
          ~laws,
          Empty,
          h,
          r,
          x,
          hin,
          e => Lists.Bool.clash(Empty, p(g)(h), ef, (
              %Equal.sym(A, h, x, e): {p(g)(_) == True{}: Bool}
              hp)),
          c => List.pick_miss(~A, ~V, ~p, ~same, ~laws, r, g, x)(hn)(c)(hp)
        )
      )

# p holds of g and each element of a list when it holds of each member
def List.holds_all(
  ~A: Data,
  ~V: Data,
  ~p: V -> A -> Bool,
  ~same: A -> A -> Bool,
  ~laws: Shared.Eq.Laws(A, same),
  xs: List<&2, A>,
  +g: V
) -> (
  @y: A -> {List.contains(~A, ~same, xs, y) == True{}: Bool} -> {p(g)(y) == True{}: Bool}
) -> {Shared.List.holds(~A, ~V, ~p, xs, g) == True{}: Bool}:
  match xs:
    case Nil{}:
      all => {==}
    case Con{+h, +r}:
      all => Facts.Case.all_one(
        @y: A -> {List.contains(~A, ~same, h <> r, y) == True{}: Bool} -> {p(g)(y) == True{}: Bool},
        p(g)(h),
        u => Shared.List.holds(~A, ~V, ~p, r, g),
        all,
        f => f(h)(Lists.List.contains_head(~A, ~same, ~laws, h, r)),
        f => List.holds_all(
          ~A,
          ~V,
          ~p,
          ~same,
          ~laws,
          r,
          g
        )(+y => hy => f(y)(Shared.List.contains_cons(~A, ~same, h, r, y)(hy)))
      )

# when List.index gives nothing, p holds of no element of xs
def List.index_miss(
  ~A: Data,
  ~V: Data,
  ~p: V -> A -> Bool,
  +xs: List<&2, A>,
  +g: V
) -> {
  Lists.List.index(~A, ~V, ~p, xs, g) == None{}: Maybe<&2, Nat>
} -> {Shared.List.some(~A, ~V, ~p, xs, g) == False{}: Bool}:
  +en => Facts.Case.false_of(
    Shared.List.some(~A, ~V, ~p, xs, g)
  )(
    ht => List.some_at.by(
      A,
      V,
      p,
      xs,
      g,
      Empty,
      List.some_at(~A, ~V, ~p, xs, g)(ht),
      +j => +y => hg => hp => Lists.Bool.clash(
        Empty,
        p(g)(y),
        Lists.List.index_none(~A, ~V, ~p, xs, g, j, y)(en)(hg),
        hp
      )
    )
  )

# a slot that makes no next state has no decided pick
def Step.of_none(
  -vs: List<&2, Types.Entry>,
  -k: Nat,
  d: Maybe<&2, Types.Pick>
) -> {
  RLines.Line.step.of(RLines.State{vs, k}, d) == None{}: Maybe<&2, RLines.State>
} -> {d == None{}: Maybe<&2, Types.Pick>}:
  match d:
    case None{}:
      h => {==}
    case Some{pk}:
      h => Empty.absurd(
        {Some{pk} == None{}: Maybe<&2, Types.Pick>},
        Lists.Maybe.some_ne_none(RLines.State, RLines.State.put(vs, k, pk), h)
      )

# an ask among fs that the node may vote for is one of the ready asks of fs
def Ready.in(
  fs: List<&2, Types.Fact>,
  +s: Facts.Facts(),
  +name: String,
  +a: Types.Ask
) -> {
  List.contains(~Types.Fact, ~Coded.Fact.is_eq, fs, Types.Fact.Ask{a}) == True{}: Bool
} -> {
  Maybe.is_some(&2, RWorks.Plan, Works.Work.offer(s, name, a)) == True{}: Bool
} -> {
  List.contains(~Types.Ask, ~Coded.Ask.is_eq, Works.Work.ready(s, name, fs), a) == True{}: Bool
}:
  match fs:
    case Nil{}:
      hin => hw => Empty.absurd({False{} == True{}: Bool}, Shared.Bool.false_ne_true(hin))
    case Con{Types.Fact.Vote{+v, +st, +pk}, +rest}:
      hin => hw => Lists.List.contains_cons_by(
        ~Types.Fact,
        ~Coded.Fact.is_eq,
        ~Coded.Fact.laws(),
        {
          List.contains(
            ~Types.Ask,
            ~Coded.Ask.is_eq,
            Works.Work.ready(s, name, rest),
            a
          )
            == True{}: Bool
        },
        Types.Fact.Vote{v, st, pk},
        rest,
        Types.Fact.Ask{a},
        hin,
        e => Fact.vote_not_ask(
          {
            List.contains(
              ~Types.Ask,
              ~Coded.Ask.is_eq,
              Works.Work.ready(s, name, rest),
              a
            )
              == True{}: Bool
          },
          v,
          st,
          pk,
          a
        )(e),
        c => Ready.in(rest, s, name, a)(c)(hw)
      )
    case Con{Types.Fact.Ask{+b}, +rest}:
      hin => +hw => Lists.List.contains_cons_by(
        ~Types.Fact,
        ~Coded.Fact.is_eq,
        ~Coded.Fact.laws(),
        {
          List.contains(
            ~Types.Ask,
            ~Coded.Ask.is_eq,
            List.filter.put(
              Types.Ask,
              b,
              Works.Work.ready(s, name, rest),
              Maybe.is_some(&2, RWorks.Plan, Works.Work.offer(s, name, b))
            ),
            a
          )
            == True{}: Bool
        },
        Types.Fact.Ask{b},
        rest,
        Types.Fact.Ask{a},
        hin,
        e => (
          %Equal.sym(Types.Ask, b, a, Fact.ask_inj(b, a)(e)): {List.contains(~Types.Ask, ~Coded.Ask.is_eq, List.filter.put(Types.Ask, _, Works.Work.ready(s, name, rest), Maybe.is_some(&2, RWorks.Plan, Works.Work.offer(s, name, _))), a) == True{}: Bool}
          Asks.put_head(a, Works.Work.ready(s, name, rest), Maybe.is_some(&2, RWorks.Plan, Works.Work.offer(s, name, a)))(hw)),
        c => Asks.put_rest(
          b,
          Works.Work.ready(s, name, rest),
          Maybe.is_some(&2, RWorks.Plan, Works.Work.offer(s, name, b)),
          a
        )(Ready.in(rest, s, name, a)(c)(hw))
      )

# each of the ready asks of fs is an ask among fs
def Ready.from(
  fs: List<&2, Types.Fact>,
  +s: Facts.Facts(),
  +name: String,
  +y: Types.Ask
) -> {
  List.contains(~Types.Ask, ~Coded.Ask.is_eq, Works.Work.ready(s, name, fs), y) == True{}: Bool
} -> {List.contains(~Types.Fact, ~Coded.Fact.is_eq, fs, Types.Fact.Ask{y}) == True{}: Bool}:
  match fs:
    case Nil{}:
      h => h
    case Con{Types.Fact.Vote{+v, +st, +pk}, +rest}:
      h => Shared.List.contains_cons(
        ~Types.Fact,
        ~Coded.Fact.is_eq,
        Types.Fact.Vote{v, st, pk},
        rest,
        Types.Fact.Ask{y}
      )(Ready.from(rest, s, name, y)(h))
    case Con{Types.Fact.Ask{+b}, +rest}:
      h => Asks.put_by(
        {
          List.contains(
            ~Types.Fact,
            ~Coded.Fact.is_eq,
            Types.Fact.Ask{b} <> rest,
            Types.Fact.Ask{y}
          )
            == True{}: Bool
        },
        b,
        Works.Work.ready(s, name, rest),
        Maybe.is_some(&2, RWorks.Plan, Works.Work.offer(s, name, b)),
        y,
        h,
        e => k => (
          %e: {List.contains(~Types.Fact, ~Coded.Fact.is_eq, Types.Fact.Ask{b} <> rest, Types.Fact.Ask{_}) == True{}: Bool}
          Lists.List.contains_head(~Types.Fact, ~Coded.Fact.is_eq, ~Coded.Fact.laws(), Types.Fact.Ask{b}, rest)),
        c => Shared.List.contains_cons(
          ~Types.Fact,
          ~Coded.Fact.is_eq,
          Types.Fact.Ask{b},
          rest,
          Types.Fact.Ask{y}
        )(Ready.from(rest, s, name, y)(c))
      )

# the last ask that a node may vote for, after it took in an ask of a number
# above every number that it held and may vote for it, is that ask
def Ready.top(
  +name: String,
  +s: Facts.Facts(),
  +a: Types.Ask
) -> {
  Nat.is_lt(RFacts.Seq.peak(Facts.Facts.list(s)), RFacts.Ask.seq(a)) == True{}: Bool
} -> {
  Maybe.is_some(
    &2,
    RWorks.Plan,
    Works.Work.offer(Facts.Facts.take(name, s, Types.Fact.Ask{a}), name, a)
  )
    == True{}: Bool
} -> {
  Lists.List.top(
    ~Types.Ask,
    ~RFacts.Ask.seq,
    Works.Work.ready(
      Facts.Facts.take(name, s, Types.Fact.Ask{a}),
      name,
      Facts.Facts.list(Facts.Facts.take(name, s, Types.Fact.Ask{a}))
    )
  )
    == Some{a}: Maybe<&2, Types.Ask>
}:
  +hlt => hw => Lists.List.top_one(
    ~Types.Ask,
    ~RFacts.Ask.seq,
    ~Coded.Ask.is_eq,
    ~Coded.Ask.laws(),
    Works.Work.ready(
      Facts.Facts.take(name, s, Types.Fact.Ask{a}),
      name,
      Facts.Facts.list(Facts.Facts.take(name, s, Types.Fact.Ask{a}))
    ),
    a
  )(
    Ready.in(
      Facts.Facts.list(Facts.Facts.take(name, s, Types.Fact.Ask{a})),
      Facts.Facts.take(name, s, Types.Fact.Ask{a}),
      name,
      a
    )(
      Facts.Facts.has_in(
        Facts.Facts.take(name, s, Types.Fact.Ask{a}),
        Types.Fact.Ask{a}
      )(Facts.Facts.take_ask_has(name, s, a))
    )(hw)
  )(
    +y => hy => ne => Ask.newer(
      name,
      s,
      a,
      y
    )(
      hlt
    )(
      Facts.Facts.in_has(
        Facts.Facts.take(name, s, Types.Fact.Ask{a}),
        Types.Fact.Ask{y}
      )(
        Ready.from(
          Facts.Facts.list(Facts.Facts.take(name, s, Types.Fact.Ask{a})),
          Facts.Facts.take(name, s, Types.Fact.Ask{a}),
          name,
          y
        )(hy)
      )
    )(ne)
  )

# the next slot of a line, for a node that alone decides it
def Work.open_alone(
  +s: Facts.Facts(),
  +name: String,
  +c: Ledgers.Line,
  +vs: List<&2, Types.Entry>,
  +k: Nat,
  +g: Maybe<&2, String>
) -> {
  Lines.Line.state(s, c) == Some{RLines.State{vs, k}}: Maybe<&2, RLines.State>
} -> {
  Lines.Rule.after(s, c, vs) == Some{RLines.Rule{g, [name]}}: Maybe<&2, RLines.Rule>
} -> {Works.Work.open(s, name, c) == Some{RWorks.Open{vs, k, [name]}}: Maybe<&2, RWorks.Open>}:
  hst => hr => (
    %Equal.sym(Maybe<&2, RLines.State>, Lines.Line.state(s, c), Some{RLines.State{vs, k}}, hst): {RWorks.Work.open.at(name, _, Works.Work.rule(s, c, _)) == Some{RWorks.Open{vs, k, [name]}}: Maybe<&2, RWorks.Open>}
    %Equal.sym(Maybe<&2, RLines.Rule>, Lines.Rule.after(s, c, vs), Some{RLines.Rule{g, [name]}}, hr): {RWorks.Work.open.at(name, Some{RLines.State{vs, k}}, _) == Some{RWorks.Open{vs, k, [name]}}: Maybe<&2, RWorks.Open>}
    %Equal.sym(Bool, String.eq(name, name), True{}, Texts.String.eq_refl(name)): {Shared.Maybe.when(RWorks.Open, List.any.if(u => List.contains(~String, ~String.eq, [], name), _), u2 => Some{RWorks.Open{vs, k, [name]}}) == Some{RWorks.Open{vs, k, [name]}}: Maybe<&2, RWorks.Open>}
    {==})

# the vote that a node offers for an ask at the next slot of its line, when
# it may lead a round of the slot freely, and the ask made no version
def Work.offer_alone(
  +s: Facts.Facts(),
  +name: String,
  +c: Ledgers.Line,
  +a: Types.Ask,
  +vs: List<&2, Types.Entry>,
  +k: Nat,
  +ns: List<&2, String>,
  +t: Nat,
  +r: Nat,
  +b: List<&2, Types.Ref>
) -> {
  RWorks.Request.line(Facts.Facts.list(s), RLines.Ask.request(a)) == Some{c}: Maybe<&2, Ledgers.Line>
} -> {
  Works.Work.open(s, name, c) == Some{RWorks.Open{vs, k, ns}}: Maybe<&2, RWorks.Open>
} -> {
  Shared.List.some(
    ~Types.Entry,
    ~Ledgers.Id,
    ~RLines.Entry.is_of,
    vs,
    RLines.Ask.id(a)
  )
    == False{}: Bool
} -> {
  RRounds.Slot.chance(Rounds.Slot.ballots(s, c, k), ns, k, name)
    == Some{RRounds.Chance{t, r, b, RRounds.Force.Free{}}}: Maybe<&2, RRounds.Chance>
} -> {
  Works.Work.offer(s, name, a) == Some{RWorks.Plan{Types.Step.At{c, k, t}, Types.Cast.Vote{r, Types.Pick{a, Works.Pins.for(s, c, vs, Works.Era.now(s, c), RLines.Ask.request(a))}, b}}}: Maybe<&2, RWorks.Plan>
}:
  hl => ho => hn => hch => (
    %Equal.sym(Maybe<&2, Ledgers.Line>, RWorks.Request.line(Facts.Facts.list(s), RLines.Ask.request(a)), Some{c}, hl): {Works.Work.offer.on(s, name, a, _) == Some{RWorks.Plan{Types.Step.At{c, k, t}, Types.Cast.Vote{r, Types.Pick{a, Works.Pins.for(s, c, vs, Works.Era.now(s, c), RLines.Ask.request(a))}, b}}}: Maybe<&2, RWorks.Plan>}
    %Equal.sym(Maybe<&2, RWorks.Open>, Works.Work.open(s, name, c), Some{RWorks.Open{vs, k, ns}}, ho): {Works.Work.offer.at(s, name, c, a, _) == Some{RWorks.Plan{Types.Step.At{c, k, t}, Types.Cast.Vote{r, Types.Pick{a, Works.Pins.for(s, c, vs, Works.Era.now(s, c), RLines.Ask.request(a))}, b}}}: Maybe<&2, RWorks.Plan>}
    %Equal.sym(Bool, Shared.List.some(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, vs, RLines.Ask.id(a)), False{}, hn): {Shared.Maybe.when(RWorks.Plan, Bool.not(_), u => RWorks.Plan.of(c, k, RWorks.Work.offer.of(u2 => Types.Pick{a, Works.Pins.for(s, c, vs, Works.Era.now(s, c), RLines.Ask.request(a))}, RRounds.Slot.chance(Rounds.Slot.ballots(s, c, k), ns, k, name)))) == Some{RWorks.Plan{Types.Step.At{c, k, t}, Types.Cast.Vote{r, Types.Pick{a, Works.Pins.for(s, c, vs, Works.Era.now(s, c), RLines.Ask.request(a))}, b}}}: Maybe<&2, RWorks.Plan>}
    %Equal.sym(Maybe<&2, RRounds.Chance>, RRounds.Slot.chance(Rounds.Slot.ballots(s, c, k), ns, k, name), Some{RRounds.Chance{t, r, b, RRounds.Force.Free{}}}, hch): {RWorks.Plan.of(c, k, RWorks.Work.offer.of(u2 => Types.Pick{a, Works.Pins.for(s, c, vs, Works.Era.now(s, c), RLines.Ask.request(a))}, _)) == Some{RWorks.Plan{Types.Step.At{c, k, t}, Types.Cast.Vote{r, Types.Pick{a, Works.Pins.for(s, c, vs, Works.Era.now(s, c), RLines.Ask.request(a))}, b}}}: Maybe<&2, RWorks.Plan>}
    {==})

# a node whose last ready ask is a, that offers a ballot for it where it
# holds none of its own, casts that ballot
def Work.does_alone(
  +s: Facts.Facts(),
  +name: String,
  +a: Types.Ask,
  +st: Types.Step,
  +x: Types.Cast
) -> {
  Lists.List.top(
    ~Types.Ask,
    ~RFacts.Ask.seq,
    Works.Work.ready(s, name, Facts.Facts.list(s))
  )
    == Some{a}: Maybe<&2, Types.Ask>
} -> {
  Works.Work.offer(s, name, a) == Some{RWorks.Plan{st, x}}: Maybe<&2, RWorks.Plan>
} -> {
  Facts.Facts.cast(s, name, st) == False{}: Bool
} -> {Works.Work.does(s, name) == Facts.Facts.add(s, Types.Fact.Vote{name, st, x}): Facts.Facts()}:
  ht => ho => hc => (
    %Equal.sym(Maybe<&2, Types.Ask>, Lists.List.top(~Types.Ask, ~RFacts.Ask.seq, Works.Work.ready(s, name, Facts.Facts.list(s))), Some{a}, ht): {Works.Work.cast(s, name, RWorks.Work.follow.or(Works.Work.propose.of(s, name, _), u => RWorks.Work.follow.or(RWorks.Work.follow(RKnown.Known.none(), Facts.Facts.crit(s), name, Facts.Facts.list(s)), u2 => RWorks.Work.pass(RKnown.Known.none(), Facts.Facts.crit(s), name, Facts.Facts.list(s))))) == Facts.Facts.add(s, Types.Fact.Vote{name, st, x}): Facts.Facts()}
    %Equal.sym(Maybe<&2, RWorks.Plan>, Works.Work.offer(s, name, a), Some{RWorks.Plan{st, x}}, ho): {Works.Work.cast(s, name, RWorks.Work.follow.or(_, u => RWorks.Work.follow.or(RWorks.Work.follow(RKnown.Known.none(), Facts.Facts.crit(s), name, Facts.Facts.list(s)), u2 => RWorks.Work.pass(RKnown.Known.none(), Facts.Facts.crit(s), name, Facts.Facts.list(s))))) == Facts.Facts.add(s, Types.Fact.Vote{name, st, x}): Facts.Facts()}
    %Equal.sym(Bool, Facts.Facts.cast(s, name, st), False{}, hc): {Shared.Bool.when(Facts.Facts(), _, u => s, u => Facts.Facts.add(s, Types.Fact.Vote{name, st, x})) == Facts.Facts.add(s, Types.Fact.Vote{name, st, x}): Facts.Facts()}
    {==})


# taking in an ask that starts no store leaves the rule after the versions of
# every line as it was
def Rule.after_asked(
  +name: String,
  +s: Facts.Facts(),
  +a: Types.Ask,
  c: Ledgers.Line,
  +vs: List<&2, Types.Entry>
) -> {
  RFacts.Request.is_start(RLines.Ask.request(a)) == False{}: Bool
} -> {
  Lines.Rule.after(
    Facts.Facts.take(name, s, Types.Fact.Ask{a}),
    c,
    vs
  )
    == Lines.Rule.after(s, c, vs): Maybe<&2, RLines.Rule>
}:
  match c:
    case Ledgers.Line{+h, None{}}:
      e => {==}
    case Ledgers.Line{+h, Some{+bb}}:
      e => Equal.cong(
        Maybe<&2, RLines.State>,
        Maybe<&2, RLines.Rule>,
        m => RLines.Rule.after.of(
          Ledgers.Line{h, Some{bb}},
          vs,
          Maybe.map(&2, RLines.State, List<&2, Types.Entry>, RLines.State.versions, m)
        ),
        Lines.Store.state(Facts.Facts.take(name, s, Types.Fact.Ask{a}), h),
        Lines.Store.state(s, h),
        Moves.Line.state_asked(name, s, a, Ledgers.Line{h, None{}})(e)
      )

# Work.alone_does, with the vote that the node offers
def Work.alone_does.end(
  +s: Facts.Facts(),
  +name: String,
  +c: Ledgers.Line,
  +a: Types.Ask,
  +vs: List<&2, Types.Entry>,
  +k: Nat,
  +g: Maybe<&2, String>,
  +t: Nat,
  +r: Nat,
  +b: List<&2, Types.Ref>,
  hst: {Lines.Line.state(s, c) == Some{RLines.State{vs, k}}: Maybe<&2, RLines.State>},
  hr: {Lines.Rule.after(s, c, vs) == Some{RLines.Rule{g, [name]}}: Maybe<&2, RLines.Rule>},
  hn: {
    Shared.List.some(
      ~Types.Entry,
      ~Ledgers.Id,
      ~RLines.Entry.is_of,
      vs,
      RLines.Ask.id(a)
    )
      == False{}: Bool
  },
  hc: {Facts.Facts.cast(s, name, Types.Step.At{c, k, t}) == False{}: Bool},
  hd: {
    Lines.Votes.decided(
      Facts.Facts.add(
        s,
        Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Vote{r, Types.Pick{a, Works.Pins.for(s, c, vs, Works.Era.now(s, c), RLines.Ask.request(a))}, b}}
      ),
      c,
      k,
      [name]
    )
      == Some{Types.Pick{a, Works.Pins.for(s, c, vs, Works.Era.now(s, c), RLines.Ask.request(a))}}: Maybe<&2, Types.Pick>
  },
  +ho: {Works.Work.offer(s, name, a) == Some{RWorks.Plan{Types.Step.At{c, k, t}, Types.Cast.Vote{r, Types.Pick{a, Works.Pins.for(s, c, vs, Works.Era.now(s, c), RLines.Ask.request(a))}, b}}}: Maybe<&2, RWorks.Plan>},
  ht: {
    Maybe.is_some(&2, RWorks.Plan, Works.Work.offer(s, name, a)) == True{}: Bool
  } -> {
    Lists.List.top(
      ~Types.Ask,
      ~RFacts.Ask.seq,
      Works.Work.ready(s, name, Facts.Facts.list(s))
    )
      == Some{a}: Maybe<&2, Types.Ask>
  }
) -> Exists(
  List<&2, Types.Entry>,
  vs2 => {
    Lines.Line.versions(Works.Work.does(s, name), c) == Some{vs2}: Maybe<&2, List<&2, Types.Entry>>
  }
    & {
      List.get(
        &2,
        Types.Entry,
        vs2,
        List.length(&2, Types.Entry, vs)
      )
        == Some{
          Types.Entry{
            Types.Pick{a, Works.Pins.for(s, c, vs, Works.Era.now(s, c), RLines.Ask.request(a))},
            k
          }
        }: Maybe<&2, Types.Entry>
    }
):
  %Equal.sym(
    Facts.Facts(),
    Works.Work.does(s, name),
    Facts.Facts.add(
      s,
      Types.Fact.Vote{name, Types.Step.At{c, k, t}, Types.Cast.Vote{r, Types.Pick{a, Works.Pins.for(s, c, vs, Works.Era.now(s, c), RLines.Ask.request(a))}, b}}
    ),
    Work.does_alone(
      s,
      name,
      a,
      Types.Step.At{c, k, t},
      Types.Cast.Vote{r, Types.Pick{a, Works.Pins.for(s, c, vs, Works.Era.now(s, c), RLines.Ask.request(a))}, b}
    )(ht((
          %Equal.sym(Maybe<&2, RWorks.Plan>, Works.Work.offer(s, name, a), Some{RWorks.Plan{Types.Step.At{c, k, t}, Types.Cast.Vote{r, Types.Pick{a, Works.Pins.for(s, c, vs, Works.Era.now(s, c), RLines.Ask.request(a))}, b}}}, ho): {Maybe.is_some(&2, RWorks.Plan, _) == True{}: Bool}
          {==})))(ho)(hc)
  ): Exists(
  List<&2, Types.Entry>,
  vs2 => {
    Lines.Line.versions(_, c) == Some{vs2}: Maybe<&2, List<&2, Types.Entry>>
  }
    & {
      List.get(
        &2,
        Types.Entry,
        vs2,
        List.length(&2, Types.Entry, vs)
      )
        == Some{
          Types.Entry{
            Types.Pick{a, Works.Pins.for(s, c, vs, Works.Era.now(s, c), RLines.Ask.request(a))},
            k
          }
        }: Maybe<&2, Types.Entry>
    }
)
  Moves.Line.voted_alone(
    s,
    name,
    c,
    vs,
    k,
    g,
    Types.Pick{a, Works.Pins.for(s, c, vs, Works.Era.now(s, c), RLines.Ask.request(a))},
    Moves.Seat{t, r, b}
  )(hst)(hr)(hn)(hd)

# Work.alone_does, with what the node may cast alone
def Work.alone_does.fin(
  +s: Facts.Facts(),
  +name: String,
  +c: Ledgers.Line,
  +a: Types.Ask,
  +vs: List<&2, Types.Entry>,
  +k: Nat,
  +g: Maybe<&2, String>,
  +hst: {Lines.Line.state(s, c) == Some{RLines.State{vs, k}}: Maybe<&2, RLines.State>},
  +hr: {Lines.Rule.after(s, c, vs) == Some{RLines.Rule{g, [name]}}: Maybe<&2, RLines.Rule>},
  +hn: {
    Shared.List.some(
      ~Types.Entry,
      ~Ledgers.Id,
      ~RLines.Entry.is_of,
      vs,
      RLines.Ask.id(a)
    )
      == False{}: Bool
  },
  hl: {
    RWorks.Request.line(
      Facts.Facts.list(s),
      RLines.Ask.request(a)
    )
      == Some{c}: Maybe<&2, Ledgers.Line>
  },
  ht: {
    Maybe.is_some(&2, RWorks.Plan, Works.Work.offer(s, name, a)) == True{}: Bool
  } -> {
    Lists.List.top(
      ~Types.Ask,
      ~RFacts.Ask.seq,
      Works.Work.ready(s, name, Facts.Facts.list(s))
    )
      == Some{a}: Maybe<&2, Types.Ask>
  },
  w0: Exists(
    Nat,
    t => Exists(
      Nat,
      r => Exists(List<&2, Types.Ref>, b => Rounds.Slot.Alone(s, name, c, k, Types.Pick{a, Works.Pins.for(s, c, vs, Works.Era.now(s, c), RLines.Ask.request(a))}, t, r, b))
    )
  )
) -> Exists(
  List<&2, Types.Entry>,
  vs2 => {
    Lines.Line.versions(Works.Work.does(s, name), c) == Some{vs2}: Maybe<&2, List<&2, Types.Entry>>
  }
    & {
      List.get(
        &2,
        Types.Entry,
        vs2,
        List.length(&2, Types.Entry, vs)
      )
        == Some{
          Types.Entry{
            Types.Pick{a, Works.Pins.for(s, c, vs, Works.Era.now(s, c), RLines.Ask.request(a))},
            k
          }
        }: Maybe<&2, Types.Entry>
    }
):
  (+t, w1) = w0
  (+r, w2) = w1
  (+b, w3) = w2
  (hch, w4) = w3
  (hc, hd) = w4
  Work.alone_does.end(
    s,
    name,
    c,
    a,
    vs,
    k,
    g,
    t,
    r,
    b,
    hst,
    hr,
    hn,
    hc,
    hd,
    Work.offer_alone(s, name, c, a, vs, k, [name], t, r, b)(hl)(Work.open_alone(s, name, c, vs, k, g)(hst)(hr))(hn)(hch),
    ht
  )

# a node that alone decides the next slot of a line, in facts that are sound
# for it, and whose last ready ask is an ask for the line that made no
# version of it, makes the next version of the line from it once it works
def Work.alone_does(
  +name: String,
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +a: Types.Ask,
  +vs: List<&2, Types.Entry>,
  +k: Nat,
  +g: Maybe<&2, String>
) -> {
  Facts.Facts.ok(name, s) == True{}: Bool
} -> {
  Lines.Line.state(s, c) == Some{RLines.State{vs, k}}: Maybe<&2, RLines.State>
} -> {
  Lines.Rule.after(s, c, vs) == Some{RLines.Rule{g, [name]}}: Maybe<&2, RLines.Rule>
} -> {
  RWorks.Request.line(Facts.Facts.list(s), RLines.Ask.request(a)) == Some{c}: Maybe<&2, Ledgers.Line>
} -> {
  Shared.List.some(
    ~Types.Entry,
    ~Ledgers.Id,
    ~RLines.Entry.is_of,
    vs,
    RLines.Ask.id(a)
  )
    == False{}: Bool
} -> (
  {
    Maybe.is_some(&2, RWorks.Plan, Works.Work.offer(s, name, a)) == True{}: Bool
  } -> {
    Lists.List.top(
      ~Types.Ask,
      ~RFacts.Ask.seq,
      Works.Work.ready(s, name, Facts.Facts.list(s))
    )
      == Some{a}: Maybe<&2, Types.Ask>
  }
) -> Exists(
  List<&2, Types.Entry>,
  vs2 => {
    Lines.Line.versions(Works.Work.does(s, name), c) == Some{vs2}: Maybe<&2, List<&2, Types.Entry>>
  }
    & {
      List.get(
        &2,
        Types.Entry,
        vs2,
        List.length(&2, Types.Entry, vs)
      )
        == Some{
          Types.Entry{
            Types.Pick{a, Works.Pins.for(s, c, vs, Works.Era.now(s, c), RLines.Ask.request(a))},
            k
          }
        }: Maybe<&2, Types.Entry>
    }
):
  ok => +hst => +hr => hl => hn => ht => Work.alone_does.fin(
    s,
    name,
    c,
    a,
    vs,
    k,
    g,
    hst,
    hr,
    hn,
    hl,
    ht,
    Rounds.Slot.alone(
      s,
      name,
      c,
      k,
      Types.Pick{a, Works.Pins.for(s, c, vs, Works.Era.now(s, c), RLines.Ask.request(a))}
    )(Facts.Facts.ok_never(name, s)(ok))(Step.of_none(vs, k, Lines.Votes.decided(s, c, k, [name]))((
          %hr: {Lines.Line.step.at(s, c, RLines.State{vs, k}, _) == None{}: Maybe<&2, RLines.State>}
          Versions.Line.state_open(s, c, RLines.State{vs, k})(hst))))
  )


# the status of a write that made a version of its branch is Written
def Status.written(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +vs2: List<&2, Types.Entry>,
  +n: Nat,
  +i: Ledgers.Id,
  +q: Nat,
  +b2: Ledgers.Line,
  +p: String,
  +ws: Maybe<&2, List<&2, U32>>,
  +pins: Types.Pins,
  +slot: Nat
) -> {
  Lines.Line.versions(s, c) == Some{vs2}: Maybe<&2, List<&2, Types.Entry>>
} -> {
  List.get(
    &2,
    Types.Entry,
    vs2,
    n
  )
    == Some{
      Types.Entry{Types.Pick{Types.Ask{i, q, Spec.Request.Write{b2, p, ws}}, pins}, slot}
    }: Maybe<&2, Types.Entry>
} -> {
  Answers.Answer.of(
    s,
    Spec.Question.Status{c, i}
  )
    == Some{Spec.Reply.Status{Spec.Status.Written{}}}: Maybe<&2, Spec.Reply>
}:
  +hv => +hg => (
    %Equal.sym(Maybe<&2, List<&2, Types.Entry>>, Lines.Line.versions(s, c), Some{vs2}, hv): {Answers.Reply.status(s, c, _, RAnswers.Line.find.of(i, _)) == Some{Spec.Reply.Status{Spec.Status.Written{}}}: Maybe<&2, Spec.Reply>}
    %Equal.sym(Maybe<&2, Nat>, Lists.List.index(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, vs2, i), Some{n}, Versions.Line.versions_index(s, c, vs2, n, Types.Entry{Types.Pick{Types.Ask{i, q, Spec.Request.Write{b2, p, ws}}, pins}, slot})(hv)(hg)): {Answers.Reply.status(s, c, Some{vs2}, RAnswers.Versions.find.at(vs2, _)) == Some{Spec.Reply.Status{Spec.Status.Written{}}}: Maybe<&2, Spec.Reply>}
    %Equal.sym(Maybe<&2, Types.Entry>, List.get(&2, Types.Entry, vs2, n), Some{Types.Entry{Types.Pick{Types.Ask{i, q, Spec.Request.Write{b2, p, ws}}, pins}, slot}}, hg): {Answers.Reply.status(s, c, Some{vs2}, Maybe.map(&2, Types.Entry, RAnswers.Found, e => RAnswers.Found{n, e}, _)) == Some{Spec.Reply.Status{Spec.Status.Written{}}}: Maybe<&2, Spec.Reply>}
    {==})

# the number of the reply m, or d
def Reply.number_or(d: Nat, m: Maybe<&2, Spec.Reply>) -> Nat:
  match m:
    case Some{Spec.Reply.Number{k}}:
      k
    case _:
      d

# the names of the reply m, or d
def Reply.names_or(d: List<&2, String>, m: Maybe<&2, Spec.Reply>) -> List<&2, String>:
  match m:
    case Some{Spec.Reply.Names{ns}}:
      ns
    case _:
      d

# a rule whose group reply is the names ns is of an owner group and of ns
def Group.inv(
  m: Maybe<&2, RLines.Rule>,
  +ns: List<&2, String>
) -> {
  Maybe.bind(
    &2,
    RLines.Rule,
    Spec.Reply,
    m,
    RAnswers.Rule.group
  )
    == Some{Spec.Reply.Names{ns}}: Maybe<&2, Spec.Reply>
} -> Exists(String, g => {m == Some{RLines.Rule{Some{g}, ns}}: Maybe<&2, RLines.Rule>}):
  match m:
    case None{}:
      h => Empty.absurd(
        Exists(String, g => {None{} == Some{RLines.Rule{Some{g}, ns}}: Maybe<&2, RLines.Rule>}),
        Shared.Maybe.none_ne_some(Spec.Reply, Spec.Reply.Names{ns}, h)
      )
    case Some{RLines.Rule{None{}, +ns2}}:
      h => Empty.absurd(
        Exists(
          String,
          g => {
            Some{RLines.Rule{None{}, ns2}} == Some{RLines.Rule{Some{g}, ns}}: Maybe<&2, RLines.Rule>
          }
        ),
        Shared.Maybe.none_ne_some(Spec.Reply, Spec.Reply.Names{ns}, h)
      )
    case Some{RLines.Rule{Some{+g}, +ns2}}:
      h => (
        g,
        Equal.cong(
          Maybe<&2, Spec.Reply>,
          Maybe<&2, RLines.Rule>,
          r => Some{RLines.Rule{Some{g}, Reply.names_or(ns2, r)}},
          Some{Spec.Reply.Names{ns2}},
          Some{Spec.Reply.Names{ns}},
          h
        )
      )

# the rule of the version that comes after all the versions of a line is the
# rule after them
def Rule.for_last(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +e: Types.Entry,
  +r: List<&2, Types.Entry>
) -> {
  Lines.Line.versions(s, c) == Some{e <> r}: Maybe<&2, List<&2, Types.Entry>>
} -> {
  Answers.Rule.for(
    s,
    c,
    1n+List.length(&2, Types.Entry, r)
  )
    == Lines.Rule.after(s, c, e <> r): Maybe<&2, RLines.Rule>
}:
  hv => (
    %Equal.sym(Maybe<&2, List<&2, Types.Entry>>, Lines.Line.versions(s, c), Some{e <> r}, hv): {Answers.Rule.for.of(s, c, RAnswers.Line.before.of(List.length(&2, Types.Entry, r), _)) == Lines.Rule.after(s, c, e <> r): Maybe<&2, RLines.Rule>}
    %Equal.sym(Bool, Nat.is_lt(List.length(&2, Types.Entry, r), 1n+List.length(&2, Types.Entry, r)), True{}, Shared.Nat.lt_succ(List.length(&2, Types.Entry, r))): {Answers.Rule.for.of(s, c, Shared.Maybe.when(List<&2, Types.Entry>, _, u => Some{e <> List.take(&2, Types.Entry, r, List.length(&2, Types.Entry, r))})) == Lines.Rule.after(s, c, e <> r): Maybe<&2, RLines.Rule>}
    %Equal.sym(List<&2, Types.Entry>, List.take(&2, Types.Entry, r, List.length(&2, Types.Entry, r)), r, List.take_all(Types.Entry, r)): {Lines.Rule.after(s, c, e <> _) == Lines.Rule.after(s, c, e <> r): Maybe<&2, RLines.Rule>}
    {==})

# when the group reply of the version that comes after all the versions vs of
# a line is the names ns, the rule after vs is of an owner group and of ns
def Group.last(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  vs: List<&2, Types.Entry>,
  +ns: List<&2, String>
) -> {
  Lines.Line.versions(s, c) == Some{vs}: Maybe<&2, List<&2, Types.Entry>>
} -> {
  Maybe.bind(
    &2,
    RLines.Rule,
    Spec.Reply,
    Answers.Rule.for(s, c, List.length(&2, Types.Entry, vs)),
    RAnswers.Rule.group
  )
    == Some{Spec.Reply.Names{ns}}: Maybe<&2, Spec.Reply>
} -> Exists(
  String,
  g => {Lines.Rule.after(s, c, vs) == Some{RLines.Rule{Some{g}, ns}}: Maybe<&2, RLines.Rule>}
):
  match vs:
    case Nil{}:
      hv => h => Empty.absurd(
        Exists(
          String,
          g => {Lines.Rule.after(s, c, []) == Some{RLines.Rule{Some{g}, ns}}: Maybe<&2, RLines.Rule>}
        ),
        Shared.Maybe.none_ne_some(Spec.Reply, Spec.Reply.Names{ns}, h)
      )
    case Con{+e, +r}:
      hv => h => Group.inv(Lines.Rule.after(s, c, e <> r), ns)((
          %Rule.for_last(s, c, e, r)(hv): {Maybe.bind(&2, RLines.Rule, Spec.Reply, _, RAnswers.Rule.group) == Some{Spec.Reply.Names{ns}}: Maybe<&2, Spec.Reply>}
          h))

# Status.none, once the index m of the id among the versions is known
def Status.none.at(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +vs: List<&2, Types.Entry>,
  +i: Ledgers.Id,
  m: Maybe<&2, Nat>
) -> {
  Lists.List.index(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, vs, i) == m: Maybe<&2, Nat>
} -> {
  Answers.Reply.status(
    s,
    c,
    Some{vs},
    RAnswers.Versions.find.at(vs, m)
  )
    == None{}: Maybe<&2, Spec.Reply>
} -> {Shared.List.some(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, vs, i) == False{}: Bool}:
  match m:
    case None{}:
      em => h => List.index_miss(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, vs, i)(em)
    case Some{+k2}:
      em => h => Empty.absurd(
        {Shared.List.some(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, vs, i) == False{}: Bool},
        Ex.by(
          Types.Entry,
          x => {
            List.get(&2, Types.Entry, vs, k2) == Some{x}: Maybe<&2, Types.Entry>
          }
            & {RLines.Entry.is_of(i)(x) == True{}: Bool},
          Empty,
          Lists.List.index_get(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, vs, i, k2)(em),
          +x => w => And.by(
            {List.get(&2, Types.Entry, vs, k2) == Some{x}: Maybe<&2, Types.Entry>},
            {RLines.Entry.is_of(i)(x) == True{}: Bool},
            Empty,
            w,
            hgx => hpx => Lists.Maybe.some_ne_none(
              Spec.Reply,
              Spec.Reply.Status{Answers.Status.of(s, c, vs, k2, x)},
              (
                %hgx: {Answers.Reply.status(s, c, Some{vs}, Maybe.map(&2, Types.Entry, RAnswers.Found, e => RAnswers.Found{k2, e}, _)) == None{}: Maybe<&2, Spec.Reply>}
                h)
            )
          )
        )
      )

# a line of the versions vs whose status reply for an id is nothing has no
# version of the id
def Status.none(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +vs: List<&2, Types.Entry>,
  +i: Ledgers.Id
) -> {
  Answers.Reply.status(
    s,
    c,
    Some{vs},
    RAnswers.Versions.find(vs, i)
  )
    == None{}: Maybe<&2, Spec.Reply>
} -> {Shared.List.some(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, vs, i) == False{}: Bool}:
  h => Status.none.at(
    s,
    c,
    vs,
    i,
    Lists.List.index(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, vs, i)
  )({==})(h)

# Work.decides, from the state of the branch, the rule of its next version,
# and that the request made no version of it
def Work.decides.fin(
  +name: String,
  +s: Facts.Facts(),
  +b: Ledgers.Line,
  +i: Ledgers.Id,
  +p: String,
  +ws: Maybe<&2, List<&2, U32>>,
  +vs: List<&2, Types.Entry>,
  +slot: Nat,
  +g: String
) -> {
  Facts.Facts.ok(name, s) == True{}: Bool
} -> {
  Lines.Line.state(s, b) == Some{RLines.State{vs, slot}}: Maybe<&2, RLines.State>
} -> {
  Lines.Rule.after(s, b, vs) == Some{RLines.Rule{Some{g}, [name]}}: Maybe<&2, RLines.Rule>
} -> {
  Shared.List.some(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, vs, i) == False{}: Bool
} -> {
  Answers.Answer.of(
    Works.Work.does(
      Facts.Facts.take(
        name,
        s,
        Types.Fact.Ask{
          Types.Ask{i, 1n+RFacts.Seq.peak(Facts.Facts.list(s)), Spec.Request.Write{b, p, ws}}
        }
      ),
      name
    ),
    Spec.Question.Status{b, i}
  )
    == Some{Spec.Reply.Status{Spec.Status.Written{}}}: Maybe<&2, Spec.Reply>
}:
  ok => hst => hr => hn => Ex.by(
    List<&2, Types.Entry>,
    vs2 => {
      Lines.Line.versions(
        Works.Work.does(
          Facts.Facts.take(
            name,
            s,
            Types.Fact.Ask{
              Types.Ask{i, 1n+RFacts.Seq.peak(Facts.Facts.list(s)), Spec.Request.Write{b, p, ws}}
            }
          ),
          name
        ),
        b
      )
        == Some{vs2}: Maybe<&2, List<&2, Types.Entry>>
    }
      & {
        List.get(
          &2,
          Types.Entry,
          vs2,
          List.length(&2, Types.Entry, vs)
        )
          == Some{
            Types.Entry{
              Types.Pick{
                Types.Ask{i, 1n+RFacts.Seq.peak(Facts.Facts.list(s)), Spec.Request.Write{b, p, ws}},
                Works.Pins.for(
                  Facts.Facts.take(
                    name,
                    s,
                    Types.Fact.Ask{
                      Types.Ask{
                        i,
                        1n+RFacts.Seq.peak(Facts.Facts.list(s)),
                        Spec.Request.Write{b, p, ws}
                      }
                    }
                  ),
                  b,
                  vs,
                  Works.Era.now(
                    Facts.Facts.take(
                      name,
                      s,
                      Types.Fact.Ask{
                        Types.Ask{
                          i,
                          1n+RFacts.Seq.peak(Facts.Facts.list(s)),
                          Spec.Request.Write{b, p, ws}
                        }
                      }
                    ),
                    b
                  ),
                  Spec.Request.Write{b, p, ws}
                )
              },
              slot
            }
          }: Maybe<&2, Types.Entry>
      },
    {
      Answers.Answer.of(
        Works.Work.does(
          Facts.Facts.take(
            name,
            s,
            Types.Fact.Ask{
              Types.Ask{i, 1n+RFacts.Seq.peak(Facts.Facts.list(s)), Spec.Request.Write{b, p, ws}}
            }
          ),
          name
        ),
        Spec.Question.Status{b, i}
      )
        == Some{Spec.Reply.Status{Spec.Status.Written{}}}: Maybe<&2, Spec.Reply>
    },
    Work.alone_does(
      name,
      Facts.Facts.take(
        name,
        s,
        Types.Fact.Ask{
          Types.Ask{i, 1n+RFacts.Seq.peak(Facts.Facts.list(s)), Spec.Request.Write{b, p, ws}}
        }
      ),
      b,
      Types.Ask{i, 1n+RFacts.Seq.peak(Facts.Facts.list(s)), Spec.Request.Write{b, p, ws}},
      vs,
      slot,
      Some{g}
    )(
      Facts.Facts.take_ok(
        name,
        s,
        Types.Fact.Ask{
          Types.Ask{i, 1n+RFacts.Seq.peak(Facts.Facts.list(s)), Spec.Request.Write{b, p, ws}}
        }
      )(ok)
    )(
      Equal.trans(
        Maybe<&2, RLines.State>,
        Lines.Line.state(
          Facts.Facts.take(
            name,
            s,
            Types.Fact.Ask{
              Types.Ask{i, 1n+RFacts.Seq.peak(Facts.Facts.list(s)), Spec.Request.Write{b, p, ws}}
            }
          ),
          b
        ),
        Lines.Line.state(s, b),
        Some{RLines.State{vs, slot}},
        Moves.Line.state_asked(
          name,
          s,
          Types.Ask{i, 1n+RFacts.Seq.peak(Facts.Facts.list(s)), Spec.Request.Write{b, p, ws}},
          b
        )({==}),
        hst
      )
    )(
      Equal.trans(
        Maybe<&2, RLines.Rule>,
        Lines.Rule.after(
          Facts.Facts.take(
            name,
            s,
            Types.Fact.Ask{
              Types.Ask{i, 1n+RFacts.Seq.peak(Facts.Facts.list(s)), Spec.Request.Write{b, p, ws}}
            }
          ),
          b,
          vs
        ),
        Lines.Rule.after(s, b, vs),
        Some{RLines.Rule{Some{g}, [name]}},
        Rule.after_asked(
          name,
          s,
          Types.Ask{i, 1n+RFacts.Seq.peak(Facts.Facts.list(s)), Spec.Request.Write{b, p, ws}},
          b,
          vs
        )({==}),
        hr
      )
    )(
      {==}
    )(
      hn
    )(
      hsome => Ready.top(
        name,
        s,
        Types.Ask{i, 1n+RFacts.Seq.peak(Facts.Facts.list(s)), Spec.Request.Write{b, p, ws}}
      )(Shared.Nat.lt_succ(RFacts.Seq.peak(Facts.Facts.list(s))))(hsome)
    ),
    +vs2 => w => And.by(
      {
        Lines.Line.versions(
          Works.Work.does(
            Facts.Facts.take(
              name,
              s,
              Types.Fact.Ask{
                Types.Ask{i, 1n+RFacts.Seq.peak(Facts.Facts.list(s)), Spec.Request.Write{b, p, ws}}
              }
            ),
            name
          ),
          b
        )
          == Some{vs2}: Maybe<&2, List<&2, Types.Entry>>
      },
      {
        List.get(
          &2,
          Types.Entry,
          vs2,
          List.length(&2, Types.Entry, vs)
        )
          == Some{
            Types.Entry{
              Types.Pick{
                Types.Ask{i, 1n+RFacts.Seq.peak(Facts.Facts.list(s)), Spec.Request.Write{b, p, ws}},
                Works.Pins.for(
                  Facts.Facts.take(
                    name,
                    s,
                    Types.Fact.Ask{
                      Types.Ask{
                        i,
                        1n+RFacts.Seq.peak(Facts.Facts.list(s)),
                        Spec.Request.Write{b, p, ws}
                      }
                    }
                  ),
                  b,
                  vs,
                  Works.Era.now(
                    Facts.Facts.take(
                      name,
                      s,
                      Types.Fact.Ask{
                        Types.Ask{
                          i,
                          1n+RFacts.Seq.peak(Facts.Facts.list(s)),
                          Spec.Request.Write{b, p, ws}
                        }
                      }
                    ),
                    b
                  ),
                  Spec.Request.Write{b, p, ws}
                )
              },
              slot
            }
          }: Maybe<&2, Types.Entry>
      },
      {
        Answers.Answer.of(
          Works.Work.does(
            Facts.Facts.take(
              name,
              s,
              Types.Fact.Ask{
                Types.Ask{i, 1n+RFacts.Seq.peak(Facts.Facts.list(s)), Spec.Request.Write{b, p, ws}}
              }
            ),
            name
          ),
          Spec.Question.Status{b, i}
        )
          == Some{Spec.Reply.Status{Spec.Status.Written{}}}: Maybe<&2, Spec.Reply>
      },
      w,
      hv => hg => Status.written(
        Works.Work.does(
          Facts.Facts.take(
            name,
            s,
            Types.Fact.Ask{
              Types.Ask{i, 1n+RFacts.Seq.peak(Facts.Facts.list(s)), Spec.Request.Write{b, p, ws}}
            }
          ),
          name
        ),
        b,
        vs2,
        List.length(&2, Types.Entry, vs),
        i,
        1n+RFacts.Seq.peak(Facts.Facts.list(s)),
        b,
        p,
        ws,
        Works.Pins.for(
          Facts.Facts.take(
            name,
            s,
            Types.Fact.Ask{
              Types.Ask{i, 1n+RFacts.Seq.peak(Facts.Facts.list(s)), Spec.Request.Write{b, p, ws}}
            }
          ),
          b,
          vs,
          Works.Era.now(
            Facts.Facts.take(
              name,
              s,
              Types.Fact.Ask{
                Types.Ask{i, 1n+RFacts.Seq.peak(Facts.Facts.list(s)), Spec.Request.Write{b, p, ws}}
              }
            ),
            b
          ),
          Spec.Request.Write{b, p, ws}
        ),
        slot
      )(hv)(hg)
    )
  )

# Work.decides, once the versions of the branch are known
def Work.decides.of(
  +name: String,
  +s: Facts.Facts(),
  +b: Ledgers.Line,
  +i: Ledgers.Id,
  +p: String,
  +ws: Maybe<&2, List<&2, U32>>,
  +vs: List<&2, Types.Entry>,
  +slot: Nat,
  ok: {Facts.Facts.ok(name, s) == True{}: Bool},
  hst: {Lines.Line.state(s, b) == Some{RLines.State{vs, slot}}: Maybe<&2, RLines.State>},
  +hv: {Lines.Line.versions(s, b) == Some{vs}: Maybe<&2, List<&2, Types.Entry>>},
  hg: {
    Maybe.bind(
      &2,
      RLines.Rule,
      Spec.Reply,
      Answers.Rule.for(s, b, List.length(&2, Types.Entry, vs)),
      RAnswers.Rule.group
    )
      == Some{Spec.Reply.Names{[name]}}: Maybe<&2, Spec.Reply>
  },
  hs: {Answers.Answer.of(s, Spec.Question.Status{b, i}) == None{}: Maybe<&2, Spec.Reply>}
) -> {
  Answers.Answer.of(
    Works.Work.does(
      Facts.Facts.take(
        name,
        s,
        Types.Fact.Ask{
          Types.Ask{i, 1n+RFacts.Seq.peak(Facts.Facts.list(s)), Spec.Request.Write{b, p, ws}}
        }
      ),
      name
    ),
    Spec.Question.Status{b, i}
  )
    == Some{Spec.Reply.Status{Spec.Status.Written{}}}: Maybe<&2, Spec.Reply>
}:
  Ex.by(
    String,
    g => {Lines.Rule.after(s, b, vs) == Some{RLines.Rule{Some{g}, [name]}}: Maybe<&2, RLines.Rule>},
    {
      Answers.Answer.of(
        Works.Work.does(
          Facts.Facts.take(
            name,
            s,
            Types.Fact.Ask{
              Types.Ask{i, 1n+RFacts.Seq.peak(Facts.Facts.list(s)), Spec.Request.Write{b, p, ws}}
            }
          ),
          name
        ),
        Spec.Question.Status{b, i}
      )
        == Some{Spec.Reply.Status{Spec.Status.Written{}}}: Maybe<&2, Spec.Reply>
    },
    Group.last(s, b, vs, [name])(hv)(hg),
    +g => hr => Work.decides.fin(
      name,
      s,
      b,
      i,
      p,
      ws,
      vs,
      slot,
      g
    )(ok)(hst)(hr)(Status.none(s, b, vs, i)((
          %hv: {Answers.Reply.status(s, b, _, RAnswers.Line.find.of(i, _)) == None{}: Maybe<&2, Spec.Reply>}
          hs)))
  )

# Work.decides, once the state m of the branch is known
def Work.decides.at(
  +name: String,
  +s: Facts.Facts(),
  +b: Ledgers.Line,
  +k: Nat,
  +i: Ledgers.Id,
  +p: String,
  +ws: Maybe<&2, List<&2, U32>>,
  m: Maybe<&2, RLines.State>
) -> {
  Lines.Line.state(s, b) == m: Maybe<&2, RLines.State>
} -> {
  Facts.Facts.ok(name, s) == True{}: Bool
} -> {
  Answers.Answer.of(s, Spec.Question.Count{b}) == Some{Spec.Reply.Number{k}}: Maybe<&2, Spec.Reply>
} -> {
  Answers.Answer.of(
    s,
    Spec.Question.Group{b, k}
  )
    == Some{Spec.Reply.Names{[name]}}: Maybe<&2, Spec.Reply>
} -> {
  Answers.Answer.of(s, Spec.Question.Status{b, i}) == None{}: Maybe<&2, Spec.Reply>
} -> {
  Answers.Answer.of(
    Works.Work.does(
      Facts.Facts.take(
        name,
        s,
        Types.Fact.Ask{
          Types.Ask{i, 1n+RFacts.Seq.peak(Facts.Facts.list(s)), Spec.Request.Write{b, p, ws}}
        }
      ),
      name
    ),
    Spec.Question.Status{b, i}
  )
    == Some{Spec.Reply.Status{Spec.Status.Written{}}}: Maybe<&2, Spec.Reply>
}:
  match m:
    case None{}:
      em => ok => hc => hg => hs => Empty.absurd(
        {
          Answers.Answer.of(
            Works.Work.does(
              Facts.Facts.take(
                name,
                s,
                Types.Fact.Ask{
                  Types.Ask{i, 1n+RFacts.Seq.peak(Facts.Facts.list(s)), Spec.Request.Write{b, p, ws}}
                }
              ),
              name
            ),
            Spec.Question.Status{b, i}
          )
            == Some{Spec.Reply.Status{Spec.Status.Written{}}}: Maybe<&2, Spec.Reply>
        },
        Shared.Maybe.none_ne_some(Spec.Reply, Spec.Reply.Number{k}, (
            %em: {RAnswers.Reply.count(Maybe.map(&2, RLines.State, List<&2, Types.Entry>, RLines.State.versions, _)) == Some{Spec.Reply.Number{k}}: Maybe<&2, Spec.Reply>}
            hc))
      )
    case Some{RLines.State{+vs, +slot}}:
      +em => ok => hc => hg => hs => Work.decides.of(
        name,
        s,
        b,
        i,
        p,
        ws,
        vs,
        slot,
        ok,
        em,
        Equal.cong(
          Maybe<&2, RLines.State>,
          Maybe<&2, List<&2, Types.Entry>>,
          x => Maybe.map(&2, RLines.State, List<&2, Types.Entry>, RLines.State.versions, x),
          Lines.Line.state(s, b),
          Some{RLines.State{vs, slot}},
          em
        ),
        (
          %Equal.sym(Nat, List.length(&2, Types.Entry, vs), k, Equal.cong(Maybe<&2, Spec.Reply>, Nat, x => Reply.number_or(0n, x), Some{Spec.Reply.Number{List.length(&2, Types.Entry, vs)}}, Some{Spec.Reply.Number{k}}, (
              %em: {RAnswers.Reply.count(Maybe.map(&2, RLines.State, List<&2, Types.Entry>, RLines.State.versions, _)) == Some{Spec.Reply.Number{k}}: Maybe<&2, Spec.Reply>}
              hc))): {Maybe.bind(&2, RLines.Rule, Spec.Reply, Answers.Rule.for(s, b, _), RAnswers.Rule.group) == Some{Spec.Reply.Names{[name]}}: Maybe<&2, Spec.Reply>}
          hg),
        hs
      )

# a node that alone decides the next version of a branch writes a new request
# once it works
def Work.decides(
  +name: String,
  +s: Facts.Facts(),
  +b: Ledgers.Line,
  +k: Nat,
  +i: Ledgers.Id,
  +p: String,
  +ws: Maybe<&2, List<&2, U32>>
) -> {
  Facts.Facts.ok(name, s) == True{}: Bool
} -> {
  Answers.Answer.of(s, Spec.Question.Count{b}) == Some{Spec.Reply.Number{k}}: Maybe<&2, Spec.Reply>
} -> {
  Answers.Answer.of(
    s,
    Spec.Question.Group{b, k}
  )
    == Some{Spec.Reply.Names{[name]}}: Maybe<&2, Spec.Reply>
} -> {
  Answers.Answer.of(s, Spec.Question.Status{b, i}) == None{}: Maybe<&2, Spec.Reply>
} -> {
  Answers.Answer.of(
    Works.Work.does(Facts.Facts.ask(name, s, i, Spec.Request.Write{b, p, ws}), name),
    Spec.Question.Status{b, i}
  )
    == Some{Spec.Reply.Status{Spec.Status.Written{}}}: Maybe<&2, Spec.Reply>
}:
  ok => hc => hg => hs => Work.decides.at(
    name,
    s,
    b,
    k,
    i,
    p,
    ws,
    Lines.Line.state(s, b)
  )({==})(ok)(hc)(hg)(hs)
