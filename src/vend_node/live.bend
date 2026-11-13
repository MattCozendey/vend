import Base
import ../shared/shared/ledger.bend as Ledgers
import ../shared/shared/shared/shared/hash.bend as Hashes
import ../shared/shared/shared/shared/shared.bend as Shared
import ../shared/shared/shared/text.bend as Texts
import ./answers.bend as Answers
import ./codes.bend as Coded
import ./content.bend as Contents
import ./facts.bend as Facts
import ./lines.bend as Lines
import ./moves.bend as Moves
import ./shared/lists.bend as Lists
import ./spec.bend as Spec
import ./types.bend as Types
import ./versions.bend as Versions
import ./work.bend as Works

# What a node does for sure
# -------------------------

# the facts s after a work that casts the vote m, if any, are wider
def Work.does_wider.of(+s: Facts.Facts(), m: Maybe<&2, Types.Fact>) -> {
  Facts.Facts.wider(s, Works.Work.does.of(s, m)) == True{}: Bool
}:
  match m:
    case None{}:
      Facts.Facts.wider_refl(s)
    case Some{+f}:
      Facts.Facts.add_wider(s, f)

# the facts of a node are wider after it works
def Work.does_wider(+name: String, +s: Facts.Facts()) -> {
  Facts.Facts.wider(s, Works.Work.does(s, name)) == True{}: Bool
}:
  Work.does_wider.of(s, Works.Work.vote(s, name))

# the vote m, if any, is a vote of the node name for a step that it holds no
# vote for
def Vote.Free(s: Facts.Facts(), name: String, m: Maybe<&2, Types.Fact>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{f}:
      Exists(
        Types.Step,
        st => Exists(
          Types.Pick,
          pk => {f == Types.Fact.Vote{name, st, pk}: Types.Fact} & {Facts.Facts.cast(s, name, st) == False{}: Bool}
        )
      )

# a node that may vote for a slot holds no vote for it
def Work.free_cast(+s: Facts.Facts(), +name: String, +c: Ledgers.Line, +k: Nat, +ns: List<&2, String>) -> {
  Works.Work.free(s, name, c, k, ns) == True{}: Bool
} -> {Facts.Facts.cast(s, name, Types.Step.At{c, k}) == False{}: Bool}:
  h => Shared.Bool.not_true(Facts.Facts.cast(s, name, Types.Step.At{c, k}))(
    Shared.Bool.and_true_right(
      List.contains(~String, ~String.eq, ns, name),
      Bool.not(Facts.Facts.cast(s, name, Types.Step.At{c, k}))
    )(h)
  )

# the vote that a node offers is free
def Work.offer.at_free(+s: Facts.Facts(), +name: String, +c: Ledgers.Line, +a: Types.Ask, m: Maybe<&2, Lines.State>, u: Maybe<&2, Lines.Rule>) -> Vote.Free(
  s,
  name,
  Works.Work.offer.at(s, name, c, a, m, u)
):
  match m u:
    case Some{Lines.State{+vs, +k}} Some{Lines.Rule{g, +ns}}:
      Lists.Bool.by(
        t => Vote.Free(
          s,
          name,
          Shared.Maybe.when(
            Types.Fact,
            t,
            u2 => Some{
              Types.Fact.Vote{
                name,
                Types.Step.At{c, k},
                Types.Pick{a, Works.Pins.for(s, c, vs, Works.Era.now(s, c), Lines.Ask.request(a))}
              }
            }
          )
        ),
        Bool.and(
          Bool.and(String.eq(Works.Turn.of(ns, k), name), Works.Work.free(s, name, c, k, ns)),
          Bool.not(Shared.List.some(~Types.Entry, ~Ledgers.Id, ~Lines.Entry.is_of, vs, Lines.Ask.id(a)))
        ),
        et => (
          Types.Step.At{c, k},
          (
            Types.Pick{a, Works.Pins.for(s, c, vs, Works.Era.now(s, c), Lines.Ask.request(a))},
            (
              {==},
              Work.free_cast(s, name, c, k, ns)(
                Shared.Bool.and_true_right(String.eq(Works.Turn.of(ns, k), name), Works.Work.free(s, name, c, k, ns))(
                  Shared.Bool.and_true_left(
                    Bool.and(String.eq(Works.Turn.of(ns, k), name), Works.Work.free(s, name, c, k, ns)),
                    Bool.not(Shared.List.some(~Types.Entry, ~Ledgers.Id, ~Lines.Entry.is_of, vs, Lines.Ask.id(a)))
                  )(et)
                )
              )
            )
          )
        ),
        ef => Unit{}
      )
    case Some{st} None{}:
      Unit{}
    case None{} u:
      Unit{}

# the vote that a node offers on a line is free
def Work.offer.on_free(+s: Facts.Facts(), +name: String, +a: Types.Ask, m: Maybe<&2, Ledgers.Line>) -> Vote.Free(
  s,
  name,
  Works.Work.offer.on(s, name, a, m)
):
  match m:
    case None{}:
      Unit{}
    case Some{+c}:
      Work.offer.at_free(s, name, c, a, Lines.Line.state(s, c), Works.Work.rule(s, c, Lines.Line.state(s, c)))

# the vote that a node proposes for an ask is free
def Work.propose.of_free(+s: Facts.Facts(), +name: String, m: Maybe<&2, Types.Ask>) -> Vote.Free(
  s,
  name,
  Works.Work.propose.of(s, name, m)
):
  match m:
    case None{}:
      Unit{}
    case Some{+a}:
      Work.offer.on_free(s, name, a, Works.Request.line(Facts.Facts.list(s), Lines.Ask.request(a)))

# the vote of a node that follows a vote at a slot is free
def Work.follow.at_free(
  +s: Facts.Facts(),
  +name: String,
  +v: String,
  +c: Ledgers.Line,
  +k: Nat,
  +pk: Types.Pick,
  m: Maybe<&2, Lines.State>,
  u: Maybe<&2, Lines.Rule>
) -> Vote.Free(s, name, Works.Work.follow.at(s, name, v, c, k, pk, m, u)):
  match m u:
    case Some{Lines.State{vs, +k2}} Some{Lines.Rule{g, +ns}}:
      Lists.Bool.by(
        t => Vote.Free(
          s,
          name,
          Shared.Maybe.when(Types.Fact, t, u2 => Some{Types.Fact.Vote{name, Types.Step.At{c, k}, pk}})
        ),
        Bool.and(
          Bool.and(Nat.is_eq(k2, k), String.eq(Works.Turn.of(ns, k), v)),
          Works.Work.free(s, name, c, k, ns)
        ),
        et => (
          Types.Step.At{c, k},
          (
            pk,
            (
              {==},
              Work.free_cast(s, name, c, k, ns)(
                Shared.Bool.and_true_right(
                  Bool.and(Nat.is_eq(k2, k), String.eq(Works.Turn.of(ns, k), v)),
                  Works.Work.free(s, name, c, k, ns)
                )(et)
              )
            )
          )
        ),
        ef => Unit{}
      )
    case Some{st} None{}:
      Unit{}
    case None{} u:
      Unit{}

# the vote of a node that follows a fact is free
def Work.follow.of_free(+s: Facts.Facts(), +name: String, f: Types.Fact) -> Vote.Free(
  s,
  name,
  Works.Work.follow.of(s, name, f)
):
  match f:
    case Types.Fact.Vote{+v, Types.Step.At{+c, +k}, +pk}:
      Work.follow.at_free(
        s,
        name,
        v,
        c,
        k,
        pk,
        Lines.Line.state(s, c),
        Works.Work.rule(s, c, Lines.Line.state(s, c))
      )
    case Types.Fact.Vote{v, Types.Step.Broken{}, pk}:
      Unit{}
    case Types.Fact.Ask{a}:
      Unit{}

# the first of two free votes is free
def Work.follow.or_free(-s: Facts.Facts(), -name: String, m: Maybe<&2, Types.Fact>, -r: Maybe<&2, Types.Fact>) -> Vote.Free(
  s,
  name,
  m
) -> Vote.Free(s, name, r) -> Vote.Free(s, name, Works.Work.follow.or(m, u => r)):
  match m:
    case None{}:
      a => b => b
    case Some{f}:
      a => b => a

# the vote of a node that follows a vote among fs is free
def Work.follow_free(+s: Facts.Facts(), +name: String, fs: List<&2, Types.Fact>) -> Vote.Free(
  s,
  name,
  Works.Work.follow(s, name, fs)
):
  match fs:
    case Nil{}:
      Unit{}
    case Con{+f, +rest}:
      Work.follow.or_free(s, name, Works.Work.follow.of(s, name, f), Works.Work.follow(s, name, rest))(
        Work.follow.of_free(s, name, f)
      )(Work.follow_free(s, name, rest))

# the vote that a node casts next is free
def Work.vote_free(+s: Facts.Facts(), +name: String) -> Vote.Free(s, name, Works.Work.vote(s, name)):
  Work.follow.or_free(
    s,
    name,
    Works.Work.propose(s, name),
    Works.Work.follow(s, name, Facts.Facts.list(s))
  )(
    Work.propose.of_free(
      s,
      name,
      Lists.List.top(~Types.Ask, ~Facts.Ask.seq, Works.Work.ready(s, name, Facts.Facts.list(s)))
    )
  )(Work.follow_free(s, name, Facts.Facts.list(s)))

# the facts stay sound with the free vote f
def Work.does_ok.at(
  +name: String,
  +s: Facts.Facts(),
  -f: Types.Fact,
  ok: {Facts.Facts.ok(name, s) == True{}: Bool},
  fr: Exists(
    Types.Step,
    st => Exists(
      Types.Pick,
      pk => {f == Types.Fact.Vote{name, st, pk}: Types.Fact} & {Facts.Facts.cast(s, name, st) == False{}: Bool}
    )
  )
) -> {Facts.Facts.ok(name, Facts.Facts.add(s, f)) == True{}: Bool}:
  (+st, r1) = fr
  (+pk, r2) = r1
  (ef, ec) = r2
  %Equal.sym(Types.Fact, f, Types.Fact.Vote{name, st, pk}, ef): {Facts.Facts.ok(name, Facts.Facts.add(s, _)) == True{}: Bool}
  Facts.Facts.add_cast_ok(name, s, st, pk)(ok)(ec)

# the facts stay sound with a free vote
def Work.does_ok.of(+name: String, +s: Facts.Facts(), m: Maybe<&2, Types.Fact>) -> {Facts.Facts.ok(name, s) == True{}: Bool} -> Vote.Free(
  s,
  name,
  m
) -> {Facts.Facts.ok(name, Works.Work.does.of(s, m)) == True{}: Bool}:
  match m:
    case None{}:
      ok => fr => ok
    case Some{+f}:
      ok => fr => Work.does_ok.at(name, s, f, ok, fr)

# the facts of a node stay sound when it works
def Work.does_ok(+name: String, +s: Facts.Facts()) -> {Facts.Facts.ok(name, s) == True{}: Bool} -> {
  Facts.Facts.ok(name, Works.Work.does(s, name)) == True{}: Bool
}:
  ok => Work.does_ok.of(name, s, Works.Work.vote(s, name))(ok)(Work.vote_free(s, name))

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
  w: Exists(Nat, k => Exists(A, x => {List.get(&2, A, r, k) == Some{x}: Maybe<&2, A>} & {p(g)(x) == True{}: Bool}))
) -> Exists(Nat, k => Exists(A, x => {List.get(&2, A, h <> r, k) == Some{x}: Maybe<&2, A>} & {p(g)(x) == True{}: Bool})):
  (k, w2) = w
  (x, q) = w2
  (1n+k, (x, q))

# a list that p holds of some element of holds, at an index, an element that
# p holds of
def List.some_at(~A: Data, ~V: Data, ~p: V -> A -> Bool, xs: List<&2, A>, +g: V) -> {
  Shared.List.some(~A, ~V, ~p, xs, g) == True{}: Bool
} -> Exists(Nat, k => Exists(A, x => {List.get(&2, A, xs, k) == Some{x}: Maybe<&2, A>} & {p(g)(x) == True{}: Bool})):
  match xs:
    case Nil{}:
      h => Empty.absurd(
        Exists(Nat, k => Exists(A, x => {None{} == Some{x}: Maybe<&2, A>} & {p(g)(x) == True{}: Bool})),
        Shared.Bool.false_ne_true(h)
      )
    case Con{+z, +r}:
      Lists.Bool.by(
        c => {List.any.if(u => Shared.List.some(~A, ~V, ~p, r, g), c) == True{}: Bool} -> Exists(
          Nat,
          k => Exists(A, x => {List.get(&2, A, z <> r, k) == Some{x}: Maybe<&2, A>} & {p(g)(x) == True{}: Bool})
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
  w: Exists(Nat, k => Exists(A, x => {List.get(&2, A, xs, k) == Some{x}: Maybe<&2, A>} & {p(g)(x) == True{}: Bool})),
  f: @k: Nat -> @x: A -> {List.get(&2, A, xs, k) == Some{x}: Maybe<&2, A>} -> {p(g)(x) == True{}: Bool} -> Q
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
def Fact.ask_inj(+a: Types.Ask, +b: Types.Ask) -> {Types.Fact.Ask{a} == Types.Fact.Ask{b}: Types.Fact} -> {a == b: Types.Ask}:
  e => Equal.cong(Types.Fact, Types.Ask, f => Fact.ask_or(a, f), Types.Fact.Ask{a}, Types.Fact.Ask{b}, e)

# a vote is no ask
def Fact.vote_not_ask(-P: Type, +v: String, +st: Types.Step, +pk: Types.Pick, +a: Types.Ask) -> {
  Types.Fact.Vote{v, st, pk} == Types.Fact.Ask{a}: Types.Fact
} -> P:
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
def Asks.put_head(+a: Types.Ask, -r: List<&2, Types.Ask>, keep: Bool) -> {keep == True{}: Bool} -> {
  List.contains(~Types.Ask, ~Coded.Ask.is_eq, List.filter.put(Types.Ask, a, r, keep), a) == True{}: Bool
}:
  match keep:
    case True{}:
      h => Lists.List.contains_head(~Types.Ask, ~Coded.Ask.is_eq, ~Coded.Ask.laws(), a, r)
    case False{}:
      h => Empty.absurd({List.contains(~Types.Ask, ~Coded.Ask.is_eq, r, a) == True{}: Bool}, Shared.Bool.false_ne_true(h))

# an ask of the rest is among the kept
def Asks.put_rest(+a: Types.Ask, +r: List<&2, Types.Ask>, keep: Bool, +x: Types.Ask) -> {
  List.contains(~Types.Ask, ~Coded.Ask.is_eq, r, x) == True{}: Bool
} -> {List.contains(~Types.Ask, ~Coded.Ask.is_eq, List.filter.put(Types.Ask, a, r, keep), x) == True{}: Bool}:
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
  hin: {List.contains(~Types.Ask, ~Coded.Ask.is_eq, List.filter.put(Types.Ask, a, r, keep), x) == True{}: Bool},
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
def Writes.of_in(fs: List<&2, Types.Fact>, +g: Answers.Place, +a: Types.Ask) -> {
  List.contains(~Types.Fact, ~Coded.Fact.is_eq, fs, Types.Fact.Ask{a}) == True{}: Bool
} -> {Answers.Ask.writes(g, a) == True{}: Bool} -> {
  List.contains(~Types.Ask, ~Coded.Ask.is_eq, Answers.Writes.of(fs, g), a) == True{}: Bool
}:
  match fs:
    case Nil{}:
      hin => hw => Empty.absurd({False{} == True{}: Bool}, Shared.Bool.false_ne_true(hin))
    case Con{Types.Fact.Vote{+v, +st, +pk}, +rest}:
      hin => hw => Lists.List.contains_cons_by(
        ~Types.Fact,
        ~Coded.Fact.is_eq,
        ~Coded.Fact.laws(),
        {List.contains(~Types.Ask, ~Coded.Ask.is_eq, Answers.Writes.of(rest, g), a) == True{}: Bool},
        Types.Fact.Vote{v, st, pk},
        rest,
        Types.Fact.Ask{a},
        hin,
        e => Fact.vote_not_ask(
          {List.contains(~Types.Ask, ~Coded.Ask.is_eq, Answers.Writes.of(rest, g), a) == True{}: Bool},
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
            List.filter.put(Types.Ask, b, Answers.Writes.of(rest, g), Answers.Ask.writes(g, b)),
            a
          )
            == True{}: Bool
        },
        Types.Fact.Ask{b},
        rest,
        Types.Fact.Ask{a},
        hin,
        e => (
          %Equal.sym(Types.Ask, b, a, Fact.ask_inj(b, a)(e)): {
            List.contains(
              ~Types.Ask,
              ~Coded.Ask.is_eq,
              List.filter.put(Types.Ask, _, Answers.Writes.of(rest, g), Answers.Ask.writes(g, _)),
              a
            )
              == True{}: Bool
          }
          Asks.put_head(a, Answers.Writes.of(rest, g), Answers.Ask.writes(g, a))(hw)
        ),
        c => Asks.put_rest(b, Answers.Writes.of(rest, g), Answers.Ask.writes(g, b), a)(Writes.of_in(rest, g, a)(c)(hw))
      )

# each of the writes of fs is an ask among fs
def Writes.of_from(fs: List<&2, Types.Fact>, +g: Answers.Place, +y: Types.Ask) -> {
  List.contains(~Types.Ask, ~Coded.Ask.is_eq, Answers.Writes.of(fs, g), y) == True{}: Bool
} -> {List.contains(~Types.Fact, ~Coded.Fact.is_eq, fs, Types.Fact.Ask{y}) == True{}: Bool}:
  match fs:
    case Nil{}:
      h => h
    case Con{Types.Fact.Vote{+v, +st, +pk}, +rest}:
      h => Shared.List.contains_cons(~Types.Fact, ~Coded.Fact.is_eq, Types.Fact.Vote{v, st, pk}, rest, Types.Fact.Ask{y})(
        Writes.of_from(rest, g, y)(h)
      )
    case Con{Types.Fact.Ask{+b}, +rest}:
      h => Asks.put_by(
        {List.contains(~Types.Fact, ~Coded.Fact.is_eq, Types.Fact.Ask{b} <> rest, Types.Fact.Ask{y}) == True{}: Bool},
        b,
        Answers.Writes.of(rest, g),
        Answers.Ask.writes(g, b),
        y,
        h,
        e => k => (
          %e: {List.contains(~Types.Fact, ~Coded.Fact.is_eq, Types.Fact.Ask{b} <> rest, Types.Fact.Ask{_}) == True{}: Bool}
          Lists.List.contains_head(~Types.Fact, ~Coded.Fact.is_eq, ~Coded.Fact.laws(), Types.Fact.Ask{b}, rest)
        ),
        c => Shared.List.contains_cons(~Types.Fact, ~Coded.Fact.is_eq, Types.Fact.Ask{b}, rest, Types.Fact.Ask{y})(
          Writes.of_from(rest, g, y)(c)
        )
      )

# an ask that a node holds after it took in the ask a of a number above every
# number that it held, and that is not a, is of a lesser number
def Ask.newer(+name: String, +s: Facts.Facts(), +a: Types.Ask, +y: Types.Ask) -> {
  Nat.is_lt(Facts.Seq.peak(Facts.Facts.list(s)), Facts.Ask.seq(a)) == True{}: Bool
} -> {Facts.Facts.has(Facts.Facts.take(name, s, Types.Fact.Ask{a}), Types.Fact.Ask{y}) == True{}: Bool} -> (
  {y == a: Types.Ask} -> Empty
) -> {Nat.is_lt(Facts.Ask.seq(y), Facts.Ask.seq(a)) == True{}: Bool}:
  hlt => hy => ne => Facts.Case.or_by(
    {Nat.is_lt(Facts.Ask.seq(y), Facts.Ask.seq(a)) == True{}: Bool},
    Coded.Ask.is_eq(y, a),
    Facts.Facts.has(s, Types.Fact.Ask{y}),
    Bool.via(
      Facts.Facts.has(Facts.Facts.take(name, s, Types.Fact.Ask{a}), Types.Fact.Ask{y}),
      Bool.or(Coded.Ask.is_eq(y, a), Facts.Facts.has(s, Types.Fact.Ask{y})),
      Facts.Facts.take_ask_asks(name, s, a, y),
      hy
    ),
    et => Empty.absurd(
      {Nat.is_lt(Facts.Ask.seq(y), Facts.Ask.seq(a)) == True{}: Bool},
      ne(Coded.Ask.is_eq_sound(y, a)(et))
    ),
    hs => Shared.Nat.le_lt(Facts.Ask.seq(y), Facts.Seq.peak(Facts.Facts.list(s)), Facts.Ask.seq(a))(
      Facts.Facts.seq_ask(s, y)(hs)
    )(hlt)
  )

# the last write of a writer at a place, after a node took in a write of it
# there with a number above every number that it held, is that write
def Writes.top(+name: String, +s: Facts.Facts(), +a: Types.Ask, +g: Answers.Place) -> {
  Nat.is_lt(Facts.Seq.peak(Facts.Facts.list(s)), Facts.Ask.seq(a)) == True{}: Bool
} -> {Answers.Ask.writes(g, a) == True{}: Bool} -> {
  Lists.List.top(
    ~Types.Ask,
    ~Facts.Ask.seq,
    Answers.Writes.of(Facts.Facts.list(Facts.Facts.take(name, s, Types.Fact.Ask{a})), g)
  )
    == Some{a}: Maybe<&2, Types.Ask>
}:
  +hlt => hw => Lists.List.top_one(
    ~Types.Ask,
    ~Facts.Ask.seq,
    ~Coded.Ask.is_eq,
    ~Coded.Ask.laws(),
    Answers.Writes.of(Facts.Facts.list(Facts.Facts.take(name, s, Types.Fact.Ask{a})), g),
    a
  )(
    Writes.of_in(Facts.Facts.list(Facts.Facts.take(name, s, Types.Fact.Ask{a})), g, a)(
      Facts.Facts.has_in(Facts.Facts.take(name, s, Types.Fact.Ask{a}), Types.Fact.Ask{a})(
        Facts.Facts.take_ask_has(name, s, a)
      )
    )(hw)
  )(
    +y => hy => ne => Ask.newer(name, s, a, y)(hlt)(
      Facts.Facts.in_has(Facts.Facts.take(name, s, Types.Fact.Ask{a}), Types.Fact.Ask{y})(
        Writes.of_from(Facts.Facts.list(Facts.Facts.take(name, s, Types.Fact.Ask{a})), g, y)(hy)
      )
    )(ne)
  )

# no vote that a node holds after it took in the ask a, of a number above
# every number that it held, is for the entry e made by a
def Ask.fresh.vote(+name: String, +s: Facts.Facts(), +a: Types.Ask, +c: Ledgers.Line, e: Types.Entry, +v: String) -> {
  Nat.is_lt(Facts.Seq.peak(Facts.Facts.list(s)), Facts.Ask.seq(a)) == True{}: Bool
} -> {
  Facts.Facts.has(
    Facts.Facts.take(name, s, Types.Fact.Ask{a}),
    Types.Fact.Vote{v, Types.Step.At{c, Lines.Entry.slot(e)}, Lines.Entry.pick(e)}
  )
    == True{}: Bool
} -> {Coded.Ask.is_eq(Lines.Entry.ask(e), a) == True{}: Bool} -> Empty:
  match e:
    case Types.Entry{Types.Pick{+a2, +pins}, +k}:
      hlt => hv => he => Lists.Bool.clash(
        Empty,
        Nat.is_lt(Facts.Ask.seq(a), Facts.Ask.seq(a)),
        Shared.Nat.lt_irrefl(Facts.Ask.seq(a)),
        Shared.Nat.le_lt(Facts.Ask.seq(a), Facts.Seq.peak(Facts.Facts.list(s)), Facts.Ask.seq(a))(
          (
            %Coded.Ask.is_eq_sound(a2, a)(he): {
              Nat.is_le(Facts.Ask.seq(_), Facts.Seq.peak(Facts.Facts.list(s))) == True{}: Bool
            }
            Facts.Facts.seq_vote(s, v, Types.Step.At{c, k}, a2, pins)(
              Bool.via(
                Facts.Facts.has(
                  Facts.Facts.take(name, s, Types.Fact.Ask{a}),
                  Types.Fact.Vote{v, Types.Step.At{c, k}, Types.Pick{a2, pins}}
                ),
                Facts.Facts.has(s, Types.Fact.Vote{v, Types.Step.At{c, k}, Types.Pick{a2, pins}}),
                Facts.Facts.take_ask_votes(name, s, a, v, c, k, Types.Pick{a2, pins}),
                hv
              )
            )
          )
        )(hlt)
      )

# an entry of the number 0 is not made by an ask of a number above n
def Ask.fresh.zero(+a: Types.Ask, +e: Types.Entry, +n: Nat) -> {Nat.is_lt(n, Facts.Ask.seq(a)) == True{}: Bool} -> {
  Facts.Ask.seq(Lines.Entry.ask(e)) == 0n: Nat
} -> {Coded.Ask.is_eq(Lines.Entry.ask(e), a) == True{}: Bool} -> Empty:
  hlt => hz => he => Nat.lt_zero(n)(
    (
      %Equal.trans(
        Nat,
        Facts.Ask.seq(a),
        Facts.Ask.seq(Lines.Entry.ask(e)),
        0n,
        Equal.sym(
          Nat,
          Facts.Ask.seq(Lines.Entry.ask(e)),
          Facts.Ask.seq(a),
          Equal.cong(
            Types.Ask,
            Nat,
            x => Facts.Ask.seq(x),
            Lines.Entry.ask(e),
            a,
            Coded.Ask.is_eq_sound(Lines.Entry.ask(e), a)(he)
          )
        ),
        hz
      ): {Nat.is_lt(n, _) == True{}: Bool}
      hlt
    )
  )

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
) -> {Nat.is_lt(Facts.Seq.peak(Facts.Facts.list(s)), Facts.Ask.seq(a)) == True{}: Bool} -> {
  Lines.Line.versions(Facts.Facts.take(name, s, Types.Fact.Ask{a}), c) == Some{vs}: Maybe<&2, List<&2, Types.Entry>>
} -> {List.get(&2, Types.Entry, vs, k) == Some{e}: Maybe<&2, Types.Entry>} -> {
  Answers.Entry.made_by(a, e) == True{}: Bool
} -> Empty:
  match k:
    case 0n:
      hlt => hv => hg => he => Ask.fresh.zero(a, e, Facts.Seq.peak(Facts.Facts.list(s)))(hlt)(
        And.left(
          {Facts.Ask.seq(Lines.Entry.ask(e)) == 0n: Nat},
          {Lines.Request.opens(Lines.Ask.request(Lines.Entry.ask(e))) == True{}: Bool},
          Versions.Line.versions_zero(Facts.Facts.take(name, s, Types.Fact.Ask{a}), c, vs, e)(hv)(hg)
        )
      )(he)
    case 1n+(+j):
      hlt => hv => hg => he => Ex.by(
        String,
        v => {
          Facts.Facts.has(
            Facts.Facts.take(name, s, Types.Fact.Ask{a}),
            Types.Fact.Vote{v, Types.Step.At{c, Lines.Entry.slot(e)}, Lines.Entry.pick(e)}
          )
            == True{}: Bool
        },
        Empty,
        Versions.Line.versions_voted(Facts.Facts.take(name, s, Types.Fact.Ask{a}), c, vs, j, e)(hv)(hg),
        +v => hvote => Ask.fresh.vote(name, s, a, c, e, v)(hlt)(hvote)(he)
      )

# no version of a line, of the versions m after a node took in the ask a of a
# number above every number that it held, was made by a
def View.fresh(+name: String, +s: Facts.Facts(), +a: Types.Ask, +c: Ledgers.Line, m: Maybe<&2, List<&2, Types.Entry>>) -> {
  Nat.is_lt(Facts.Seq.peak(Facts.Facts.list(s)), Facts.Ask.seq(a)) == True{}: Bool
} -> {
  Lines.Line.versions(Facts.Facts.take(name, s, Types.Fact.Ask{a}), c) == m: Maybe<&2, List<&2, Types.Entry>>
} -> {Answers.View.decided(a, m) == False{}: Bool}:
  match m:
    case None{}:
      hlt => hv => {==}
    case Some{+vs}:
      hlt => hv => Facts.Case.false_of(Shared.List.some(~Types.Entry, ~Types.Ask, ~Answers.Entry.made_by, vs, a))(
        ht => List.some_at.by(
          Types.Entry,
          Types.Ask,
          Answers.Entry.made_by,
          vs,
          a,
          Empty,
          List.some_at(~Types.Entry, ~Types.Ask, ~Answers.Entry.made_by, vs, a)(ht),
          +k => +e => hg => he => View.fresh.at(name, s, a, c, vs, k, e)(hlt)(hv)(hg)(he)
        )
      )

# a writer reads its own write a at once, when the number of a is above every
# number that the node held
def View.reads_own.at(+name: String, +s: Facts.Facts(), +a: Types.Ask, +b: Ledgers.Line, +p: String, +w: String) -> {
  Nat.is_lt(Facts.Seq.peak(Facts.Facts.list(s)), Facts.Ask.seq(a)) == True{}: Bool
} -> {Answers.Ask.writes(Answers.Place{w, b, p}, a) == True{}: Bool} -> {
  Answers.View.at(Facts.Facts.take(name, s, Types.Fact.Ask{a}), w, b, p)
    == Some{Answers.Request.words(Lines.Ask.request(a))}: Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  +hlt => hw => (
    %Equal.sym(
      Maybe<&2, Types.Ask>,
      Lists.List.top(
        ~Types.Ask,
        ~Facts.Ask.seq,
        Answers.Writes.of(Facts.Facts.list(Facts.Facts.take(name, s, Types.Fact.Ask{a})), Answers.Place{w, b, p})
      ),
      Some{a},
      Writes.top(name, s, a, Answers.Place{w, b, p})(hlt)(hw)
    ): {
      Answers.View.of(Facts.Facts.take(name, s, Types.Fact.Ask{a}), b, p, _)
        == Some{Answers.Request.words(Lines.Ask.request(a))}: Maybe<&2, Maybe<&2, List<&2, U32>>>
    }
    %Equal.sym(
      Bool,
      Answers.View.decided(a, Lines.Line.versions(Facts.Facts.take(name, s, Types.Fact.Ask{a}), b)),
      False{},
      View.fresh(name, s, a, b, Lines.Line.versions(Facts.Facts.take(name, s, Types.Fact.Ask{a}), b))(hlt)({==})
    ): {
      Shared.Bool.when(
        Maybe<&2, Maybe<&2, List<&2, U32>>>,
        _,
        u => Answers.View.newest(
          Facts.Facts.take(name, s, Types.Fact.Ask{a}),
          b,
          p,
          Lines.Line.versions(Facts.Facts.take(name, s, Types.Fact.Ask{a}), b)
        ),
        u => Some{Answers.Request.words(Lines.Ask.request(a))}
      )
        == Some{Answers.Request.words(Lines.Ask.request(a))}: Maybe<&2, Maybe<&2, List<&2, U32>>>
    }
    {==}
  )

# a writer reads its own write at once
def View.reads_own(
  +name: String,
  +s: Facts.Facts(),
  +i: Ledgers.Id,
  +b: Ledgers.Line,
  +p: String,
  +ws: Maybe<&2, List<&2, U32>>
) -> {
  Answers.View.at(Facts.Facts.ask(name, s, i, Spec.Request.Write{b, p, ws}), Spec.Id.writer(i), b, p)
    == Some{ws}: Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  match i:
    case Ledgers.Id{+w, +rq}:
      View.reads_own.at(
        name,
        s,
        Types.Ask{Ledgers.Id{w, rq}, 1n+Facts.Seq.peak(Facts.Facts.list(s)), Spec.Request.Write{b, p, ws}},
        b,
        p,
        w
      )(Shared.Nat.lt_succ(Facts.Seq.peak(Facts.Facts.list(s))))(
        Shared.Bool.and_both(String.eq(w, w), Bool.and(Ledgers.Line.is_eq(b, b), String.eq(p, p)))(
          Texts.String.eq_refl(w)
        )(
          Shared.Bool.and_both(Ledgers.Line.is_eq(b, b), String.eq(p, p))(Ledgers.Line.is_eq_refl(b))(
            Texts.String.eq_refl(p)
          )
        )
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
) -> {Facts.Facts.ok(name, s) == True{}: Bool} -> {
  Answers.Answer.of(s, Spec.Question.Count{b}) == Some{Spec.Reply.Number{k}}: Maybe<&2, Spec.Reply>
} -> {
  Answers.Answer.of(s, Spec.Question.Group{b, k}) == Some{Spec.Reply.Names{[name]}}: Maybe<&2, Spec.Reply>
} -> {Answers.Answer.of(s, Spec.Question.Status{b, i}) == None{}: Maybe<&2, Spec.Reply>} -> {
  Answers.Answer.of(
    Works.Work.does(Facts.Facts.ask(name, s, i, Spec.Request.Write{b, p, ws}), name),
    Spec.Question.Status{b, i}
  )
    == Some{Spec.Reply.Status{Spec.Status.Written{}}}: Maybe<&2, Spec.Reply>
}:
  ?TODO

