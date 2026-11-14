import Base
import ../shared/shared/ledger.bend as Ledgers
import ../shared/shared/shared/shared/crit.bend as Crits
import ../shared/shared/shared/shared/crit_order.bend as Orders
import ../shared/shared/shared/shared/shared.bend as Shared
import ../shared/shared/shared/text.bend as Texts
import ./codes.bend as Coded
import ./run/answers.bend as RAnswers
import ./run/facts.bend as RFacts
import ./run/known.bend as RKnown
import ./shared/lists.bend as Lists
import ./spec.bend as Spec
import ./types.bend as Types

# Newest writes
# -------------
# The newest write of each writer at each path of each branch (run/known.bend,
# Tops) is what a view reads from all the facts (Tops.of_get), and an ask
# that is newer than every ask of the node, or a vote, changes it by one
# write of the map (Tops.of_insert).

# the words xs without the first
def Words.tail(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      []
    case Con{h, t}:
      t

# the place that the ask a writes; the place d for an ask that writes none
def Place.back(d: RKnown.Place, a: Types.Ask) -> RKnown.Place:
  match a:
    case Types.Ask{Ledgers.Id{w, n}, k, Spec.Request.Write{b, p, ws}}:
      RKnown.Place{w, b, p}
    case Types.Ask{Ledgers.Id{w, n}, k, r}:
      d

# two places with one key are one place
def Place.key_inj(
  g1: RKnown.Place,
  g2: RKnown.Place
) -> {
  Crits.Key.is_eq(RKnown.Place.key(g1), RKnown.Place.key(g2)) == True{}: Bool
} -> {g1 == g2: RKnown.Place}:
  match g1 g2:
    case RKnown.Place{+w1, +b1, +p1} RKnown.Place{+w2, +b2, +p2}:
      h => Equal.cong(
        Types.Ask,
        RKnown.Place,
        x => Place.back(RKnown.Place{w1, b1, p1}, x),
        RKnown.Place.ask(RKnown.Place{w1, b1, p1}),
        RKnown.Place.ask(RKnown.Place{w2, b2, p2}),
        Coded.Ask.is_eq_sound(
          RKnown.Place.ask(RKnown.Place{w1, b1, p1}),
          RKnown.Place.ask(RKnown.Place{w2, b2, p2})
        )((
            %Equal.cong(List<&2, U32>, List<&2, U32>, Words.tail, RKnown.Place.key(RKnown.Place{w1, b1, p1}), RKnown.Place.key(RKnown.Place{w2, b2, p2}), Crits.Key.is_eq_sound(RKnown.Place.key(RKnown.Place{w1, b1, p1}), RKnown.Place.key(RKnown.Place{w2, b2, p2}))(h)): {Crits.Key.is_eq(Coded.Ask.words(RKnown.Place.ask(RKnown.Place{w1, b1, p1})), _) == True{}: Bool}
            Crits.Key.is_eq_refl(Coded.Ask.words(RKnown.Place.ask(RKnown.Place{w1, b1, p1})))))
      )

# the place m, if any, has the key q
def Place.keyed(q: List<&2, U32>, m: Maybe<&2, RKnown.Place>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{g}:
      Crits.Key.is_eq(q, RKnown.Place.key(g))

# the fact f is a write at the place of the key q
def Fact.keyed(q: List<&2, U32>, f: Types.Fact) -> Bool:
  match f:
    case Types.Fact.Vote{v, st, x}:
      False{}
    case Types.Fact.Ask{a}:
      Place.keyed(q, RKnown.Ask.place(a))

# the place x is the place g, read part by part as Ask.writes reads it
def Place.wrote(g: RKnown.Place, x: RKnown.Place) -> Bool:
  match g x:
    case RKnown.Place{w, b, p} RKnown.Place{author, c, q}:
      Bool.and(String.eq(author, w), Bool.and(Ledgers.Line.is_eq(c, b), String.eq(q, p)))

# a place is the place that it is
def Place.wrote_refl(g: RKnown.Place) -> {Place.wrote(g, g) == True{}: Bool}:
  match g:
    case RKnown.Place{+w, +b, +p}:
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

# two places have one key exactly when one is the other, read part by part
def Place.keyed_wrote(
  +w: String,
  +b: Ledgers.Line,
  +p: String,
  +author: String,
  +c: Ledgers.Line,
  +q: String
) -> {
  Crits.Key.is_eq(
    RKnown.Place.key(RKnown.Place{w, b, p}),
    RKnown.Place.key(RKnown.Place{author, c, q})
  )
    == Bool.and(String.eq(author, w), Bool.and(Ledgers.Line.is_eq(c, b), String.eq(q, p))): Bool
}:
  Lists.Bool.by(
    x => {
      Crits.Key.is_eq(
        RKnown.Place.key(RKnown.Place{w, b, p}),
        RKnown.Place.key(RKnown.Place{author, c, q})
      )
        == x: Bool
    },
    Bool.and(String.eq(author, w), Bool.and(Ledgers.Line.is_eq(c, b), String.eq(q, p))),
    +ew => (
      %Equal.sym(String, author, w, Texts.String.eq_sound(author, w)(Shared.Bool.and_true_left(String.eq(author, w), Bool.and(Ledgers.Line.is_eq(c, b), String.eq(q, p)))(ew))): {Crits.Key.is_eq(RKnown.Place.key(RKnown.Place{w, b, p}), RKnown.Place.key(RKnown.Place{_, c, q})) == True{}: Bool}
      %Equal.sym(Ledgers.Line, c, b, Ledgers.Line.is_eq_sound(c, b)(Shared.Bool.and_true_left(Ledgers.Line.is_eq(c, b), String.eq(q, p))(Shared.Bool.and_true_right(String.eq(author, w), Bool.and(Ledgers.Line.is_eq(c, b), String.eq(q, p)))(ew)))): {Crits.Key.is_eq(RKnown.Place.key(RKnown.Place{w, b, p}), RKnown.Place.key(RKnown.Place{w, _, q})) == True{}: Bool}
      %Equal.sym(String, q, p, Texts.String.eq_sound(q, p)(Shared.Bool.and_true_right(Ledgers.Line.is_eq(c, b), String.eq(q, p))(Shared.Bool.and_true_right(String.eq(author, w), Bool.and(Ledgers.Line.is_eq(c, b), String.eq(q, p)))(ew)))): {Crits.Key.is_eq(RKnown.Place.key(RKnown.Place{w, b, p}), RKnown.Place.key(RKnown.Place{w, b, _})) == True{}: Bool}
      Crits.Key.is_eq_refl(RKnown.Place.key(RKnown.Place{w, b, p}))),
    ef => Lists.Bool.by(
      y => {y == False{}: Bool},
      Crits.Key.is_eq(
        RKnown.Place.key(RKnown.Place{w, b, p}),
        RKnown.Place.key(RKnown.Place{author, c, q})
      ),
      ek => Equal.trans(
        Bool,
        True{},
        Bool.and(String.eq(author, w), Bool.and(Ledgers.Line.is_eq(c, b), String.eq(q, p))),
        False{},
        Equal.sym(
          Bool,
          Bool.and(String.eq(author, w), Bool.and(Ledgers.Line.is_eq(c, b), String.eq(q, p))),
          True{},
          (
            %Place.key_inj(RKnown.Place{w, b, p}, RKnown.Place{author, c, q})(ek): {Place.wrote(RKnown.Place{w, b, p}, _) == True{}: Bool}
            Place.wrote_refl(RKnown.Place{w, b, p}))
        ),
        ef
      ),
      en => {==}
    )
  )

# an ask writes the place of a key exactly when it is a write there, as
# Ask.writes says
def Ask.keyed_writes(
  g: RKnown.Place,
  a: Types.Ask
) -> {Place.keyed(RKnown.Place.key(g), RKnown.Ask.place(a)) == RAnswers.Ask.writes(g, a): Bool}:
  match g a:
    case RKnown.Place{
      +w,
      +b,
      +p
    } Types.Ask{Ledgers.Id{+author, name}, k, Spec.Request.Write{+c, +q, ws}}:
      Place.keyed_wrote(w, b, p, author, c, q)
    case RKnown.Place{+w, +b, +p} Types.Ask{Ledgers.Id{+author, name}, k, Spec.Request.Start{os}}:
      Equal.sym(
        Bool,
        Bool.and(String.eq(author, w), False{}),
        False{},
        Shared.Bool.and_false_right(String.eq(author, w))
      )
    case RKnown.Place{+w, +b, +p} Types.Ask{Ledgers.Id{+author, name}, k, Spec.Request.Merge{f, x}}:
      Equal.sym(
        Bool,
        Bool.and(String.eq(author, w), False{}),
        False{},
        Shared.Bool.and_false_right(String.eq(author, w))
      )
    case RKnown.Place{
      +w,
      +b,
      +p
    } Types.Ask{Ledgers.Id{+author, name}, k, Spec.Request.Resolve{m, q, ws}}:
      Equal.sym(
        Bool,
        Bool.and(String.eq(author, w), False{}),
        False{},
        Shared.Bool.and_false_right(String.eq(author, w))
      )
    case RKnown.Place{
      +w,
      +b,
      +p
    } Types.Ask{Ledgers.Id{+author, name}, k, Spec.Request.Mark{c, m, v}}:
      Equal.sym(
        Bool,
        Bool.and(String.eq(author, w), False{}),
        False{},
        Shared.Bool.and_false_right(String.eq(author, w))
      )
    case RKnown.Place{
      +w,
      +b,
      +p
    } Types.Ask{Ledgers.Id{+author, name}, k, Spec.Request.Move{c, t, v}}:
      Equal.sym(
        Bool,
        Bool.and(String.eq(author, w), False{}),
        False{},
        Shared.Bool.and_false_right(String.eq(author, w))
      )
    case RKnown.Place{
      +w,
      +b,
      +p
    } Types.Ask{Ledgers.Id{+author, name}, k, Spec.Request.Group{h, x, ms}}:
      Equal.sym(
        Bool,
        Bool.and(String.eq(author, w), False{}),
        False{},
        Shared.Bool.and_false_right(String.eq(author, w))
      )
    case RKnown.Place{+w, +b, +p} Types.Ask{Ledgers.Id{+author, name}, k, Spec.Request.Own{c, x}}:
      Equal.sym(
        Bool,
        Bool.and(String.eq(author, w), False{}),
        False{},
        Shared.Bool.and_false_right(String.eq(author, w))
      )

# the newest of the asks among the facts fs and the ask mb, if any: of two
# asks with one number, the first
def Top.over(fs: List<&2, Types.Fact>, mb: Maybe<&2, Types.Ask>) -> Maybe<&2, Types.Ask>:
  match fs:
    case Nil{}:
      mb
    case Con{Types.Fact.Vote{v, st, x}, rest}:
      Top.over(rest, mb)
    case Con{Types.Fact.Ask{a}, rest}:
      Top.over(rest, Some{Crits.Crit.merge(~Types.Ask, ~RKnown.Ask.later, mb, a)})

# the newest of the asks xs and the ask mb, if any
def Top.asks(xs: List<&2, Types.Ask>, mb: Maybe<&2, Types.Ask>) -> Maybe<&2, Types.Ask>:
  match xs:
    case Nil{}:
      mb
    case Con{y, r}:
      Top.asks(r, Some{Crits.Crit.merge(~Types.Ask, ~RKnown.Ask.later, mb, y)})

# the newest of asks and an ask is what List.top.go gives
def Top.asks_some(
  xs: List<&2, Types.Ask>,
  +b: Types.Ask
) -> {
  Top.asks(
    xs,
    Some{b}
  )
    == Some{Lists.List.top.go(~Types.Ask, ~RFacts.Ask.seq, xs, b)}: Maybe<&2, Types.Ask>
}:
  match xs:
    case Nil{}:
      {==}
    case Con{+y, r}:
      Top.asks_some(r, Bool.pick(Types.Ask, Nat.is_lt(RFacts.Ask.seq(b), RFacts.Ask.seq(y)), y, b))

# the newest of asks is what List.top gives
def Top.asks_none(
  xs: List<&2, Types.Ask>
) -> {
  Top.asks(xs, None{}) == Lists.List.top(~Types.Ask, ~RFacts.Ask.seq, xs): Maybe<&2, Types.Ask>
}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, r}:
      Top.asks_some(r, x)

# the newest of the facts at the key of a place is the newest of the writes
# at the place
def Top.over_writes(
  fs: List<&2, Types.Fact>,
  +g: RKnown.Place,
  +mb: Maybe<&2, Types.Ask>
) -> {
  Top.over(
    Orders.Values.keep(~Types.Fact, ~List<&2, U32>, ~Fact.keyed, fs, RKnown.Place.key(g)),
    mb
  )
    == Top.asks(RAnswers.Writes.of(fs, g), mb): Maybe<&2, Types.Ask>
}:
  match fs:
    case Nil{}:
      {==}
    case Con{Types.Fact.Vote{v, st, x}, rest}:
      Top.over_writes(rest, g, mb)
    case Con{Types.Fact.Ask{+a}, +rest}:
      %Equal.sym(
        Bool,
        Place.keyed(RKnown.Place.key(g), RKnown.Ask.place(a)),
        RAnswers.Ask.writes(g, a),
        Ask.keyed_writes(g, a)
      ): {
        Top.over(
          List.filter.put(
            Types.Fact,
            Types.Fact.Ask{a},
            Orders.Values.keep(~Types.Fact, ~List<&2, U32>, ~Fact.keyed, rest, RKnown.Place.key(g)),
            _
          ),
          mb
        )
          == Top.asks(
            List.filter.put(Types.Ask, a, RAnswers.Writes.of(rest, g), RAnswers.Ask.writes(g, a)),
            mb
          ): Maybe<&2, Types.Ask>
      }
      Lists.Bool.by(
        c => {
          Top.over(
            List.filter.put(
              Types.Fact,
              Types.Fact.Ask{a},
              Orders.Values.keep(
                ~Types.Fact,
                ~List<&2, U32>,
                ~Fact.keyed,
                rest,
                RKnown.Place.key(g)
              ),
              c
            ),
            mb
          )
            == Top.asks(
              List.filter.put(Types.Ask, a, RAnswers.Writes.of(rest, g), c),
              mb
            ): Maybe<&2, Types.Ask>
        },
        RAnswers.Ask.writes(g, a),
        et => Top.over_writes(
          rest,
          g,
          Some{Crits.Crit.merge(~Types.Ask, ~RKnown.Ask.later, mb, a)}
        ),
        ef => Top.over_writes(rest, g, mb)
      )

# newest writes with one more ask are well formed when they were
def Tops.put_wf(
  +tx: Crits.Crit<Types.Ask>,
  +a: Types.Ask,
  m: Maybe<&2, RKnown.Place>
) -> {
  Crits.Crit.wf(~Types.Ask, tx, 0n) == True{}: Bool
} -> {Crits.Crit.wf(~Types.Ask, RKnown.Tops.put(tx, a, m), 0n) == True{}: Bool}:
  match m:
    case None{}:
      w => w
    case Some{+g}:
      w => Crits.Crit.upsert_wf(~Types.Ask, ~RKnown.Ask.later, tx, RKnown.Place.key(g), a)(w)

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof does not run
# what newest writes with one more ask hold under a key: at the key of the
# place of the ask, the newer of the ask and what they held
def Tops.put_lookup(
  +tx: Crits.Crit<Types.Ask>,
  +a: Types.Ask,
  m: Maybe<&2, RKnown.Place>,
  +q: List<&2, U32>
) -> {
  Crits.Crit.wf(~Types.Ask, tx, 0n) == True{}: Bool
} -> {
  Crits.Crit.lookup(
    Types.Ask,
    RKnown.Tops.put(tx, a, m),
    q
  )
    == Bool.pick(
      Maybe<&2, Types.Ask>,
      Place.keyed(q, m),
      Some{Crits.Crit.merge(~Types.Ask, ~RKnown.Ask.later, Crits.Crit.lookup(Types.Ask, tx, q), a)},
      Crits.Crit.lookup(Types.Ask, tx, q)
    ): Maybe<&2, Types.Ask>
}:
  match m:
    case None{}:
      w => {==}
    case Some{+g}:
      w => Equal.trans(
        Maybe<&2, Types.Ask>,
        Crits.Crit.lookup(
          Types.Ask,
          Crits.Crit.upsert(~Types.Ask, ~RKnown.Ask.later, tx, RKnown.Place.key(g), a),
          q
        ),
        Bool.pick(
          Maybe<&2, Types.Ask>,
          Crits.Key.is_eq(q, RKnown.Place.key(g)),
          Some{
            Crits.Crit.merge(
              ~Types.Ask,
              ~RKnown.Ask.later,
              Crits.Crit.lookup(Types.Ask, tx, RKnown.Place.key(g)),
              a
            )
          },
          Crits.Crit.lookup(Types.Ask, tx, q)
        ),
        Bool.pick(
          Maybe<&2, Types.Ask>,
          Crits.Key.is_eq(q, RKnown.Place.key(g)),
          Some{
            Crits.Crit.merge(~Types.Ask, ~RKnown.Ask.later, Crits.Crit.lookup(Types.Ask, tx, q), a)
          },
          Crits.Crit.lookup(Types.Ask, tx, q)
        ),
        Crits.Crit.upsert_lookup(~Types.Ask, ~RKnown.Ask.later, tx, RKnown.Place.key(g), a, q)(w),
        Lists.Bool.by(
          c => {
            Bool.pick(
              Maybe<&2, Types.Ask>,
              c,
              Some{
                Crits.Crit.merge(
                  ~Types.Ask,
                  ~RKnown.Ask.later,
                  Crits.Crit.lookup(Types.Ask, tx, RKnown.Place.key(g)),
                  a
                )
              },
              Crits.Crit.lookup(Types.Ask, tx, q)
            )
              == Bool.pick(
                Maybe<&2, Types.Ask>,
                c,
                Some{
                  Crits.Crit.merge(
                    ~Types.Ask,
                    ~RKnown.Ask.later,
                    Crits.Crit.lookup(Types.Ask, tx, q),
                    a
                  )
                },
                Crits.Crit.lookup(Types.Ask, tx, q)
              ): Maybe<&2, Types.Ask>
          },
          Crits.Key.is_eq(q, RKnown.Place.key(g)),
          et => (
            %Crits.Key.is_eq_sound(q, RKnown.Place.key(g))(et): {Some{Crits.Crit.merge(~Types.Ask, ~RKnown.Ask.later, Crits.Crit.lookup(Types.Ask, tx, _), a)} == Some{Crits.Crit.merge(~Types.Ask, ~RKnown.Ask.later, Crits.Crit.lookup(Types.Ask, tx, q), a)}: Maybe<&2, Types.Ask>}
            {==}),
          ef => {==}
        )
      )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# newest writes with more facts are well formed when they were
def Tops.go_wf(
  fs: List<&2, Types.Fact>,
  +tx: Crits.Crit<Types.Ask>
) -> {
  Crits.Crit.wf(~Types.Ask, tx, 0n) == True{}: Bool
} -> {Crits.Crit.wf(~Types.Ask, RKnown.Tops.go(fs, tx), 0n) == True{}: Bool}:
  match fs:
    case Nil{}:
      w => w
    case Con{Types.Fact.Vote{v, st, x}, rest}:
      w => Tops.go_wf(rest, tx)(w)
    case Con{Types.Fact.Ask{+a}, rest}:
      w => Tops.go_wf(
        rest,
        RKnown.Tops.put(tx, a, RKnown.Ask.place(a))
      )(Tops.put_wf(tx, a, RKnown.Ask.place(a))(w))

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof does not run
# what the newest writes with the facts fs hold under a key: the newest of
# the facts of fs at the key and what they held
def Tops.go_lookup(
  fs: List<&2, Types.Fact>,
  +tx: Crits.Crit<Types.Ask>,
  +q: List<&2, U32>
) -> {
  Crits.Crit.wf(~Types.Ask, tx, 0n) == True{}: Bool
} -> {
  Crits.Crit.lookup(
    Types.Ask,
    RKnown.Tops.go(fs, tx),
    q
  )
    == Top.over(
      Orders.Values.keep(~Types.Fact, ~List<&2, U32>, ~Fact.keyed, fs, q),
      Crits.Crit.lookup(Types.Ask, tx, q)
    ): Maybe<&2, Types.Ask>
}:
  match fs:
    case Nil{}:
      w => {==}
    case Con{Types.Fact.Vote{v, st, x}, rest}:
      w => Tops.go_lookup(rest, tx, q)(w)
    case Con{Types.Fact.Ask{+a}, +rest}:
      +w => Equal.trans(
        Maybe<&2, Types.Ask>,
        Crits.Crit.lookup(
          Types.Ask,
          RKnown.Tops.go(rest, RKnown.Tops.put(tx, a, RKnown.Ask.place(a))),
          q
        ),
        Top.over(
          Orders.Values.keep(~Types.Fact, ~List<&2, U32>, ~Fact.keyed, rest, q),
          Crits.Crit.lookup(Types.Ask, RKnown.Tops.put(tx, a, RKnown.Ask.place(a)), q)
        ),
        Top.over(
          List.filter.put(
            Types.Fact,
            Types.Fact.Ask{a},
            Orders.Values.keep(~Types.Fact, ~List<&2, U32>, ~Fact.keyed, rest, q),
            Place.keyed(q, RKnown.Ask.place(a))
          ),
          Crits.Crit.lookup(Types.Ask, tx, q)
        ),
        Tops.go_lookup(
          rest,
          RKnown.Tops.put(tx, a, RKnown.Ask.place(a)),
          q
        )(Tops.put_wf(tx, a, RKnown.Ask.place(a))(w)),
        (
          %Equal.sym(Maybe<&2, Types.Ask>, Crits.Crit.lookup(Types.Ask, RKnown.Tops.put(tx, a, RKnown.Ask.place(a)), q), Bool.pick(Maybe<&2, Types.Ask>, Place.keyed(q, RKnown.Ask.place(a)), Some{Crits.Crit.merge(~Types.Ask, ~RKnown.Ask.later, Crits.Crit.lookup(Types.Ask, tx, q), a)}, Crits.Crit.lookup(Types.Ask, tx, q)), Tops.put_lookup(tx, a, RKnown.Ask.place(a), q)(w)): {Top.over(Orders.Values.keep(~Types.Fact, ~List<&2, U32>, ~Fact.keyed, rest, q), _) == Top.over(List.filter.put(Types.Fact, Types.Fact.Ask{a}, Orders.Values.keep(~Types.Fact, ~List<&2, U32>, ~Fact.keyed, rest, q), Place.keyed(q, RKnown.Ask.place(a))), Crits.Crit.lookup(Types.Ask, tx, q)): Maybe<&2, Types.Ask>}
          Lists.Bool.by(c => {Top.over(Orders.Values.keep(~Types.Fact, ~List<&2, U32>, ~Fact.keyed, rest, q), Bool.pick(Maybe<&2, Types.Ask>, c, Some{Crits.Crit.merge(~Types.Ask, ~RKnown.Ask.later, Crits.Crit.lookup(Types.Ask, tx, q), a)}, Crits.Crit.lookup(Types.Ask, tx, q))) == Top.over(List.filter.put(Types.Fact, Types.Fact.Ask{a}, Orders.Values.keep(~Types.Fact, ~List<&2, U32>, ~Fact.keyed, rest, q), c), Crits.Crit.lookup(Types.Ask, tx, q)): Maybe<&2, Types.Ask>}, Place.keyed(q, RKnown.Ask.place(a)), et => {==}, ef => {==}))
      )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the newest writes of facts are well formed
def Tops.of_wf(
  fs: List<&2, Types.Fact>
) -> {Crits.Crit.wf(~Types.Ask, RKnown.Tops.of(fs), 0n) == True{}: Bool}:
  Tops.go_wf(fs, Crits.Crit.new(Types.Ask))({==})

# the newest write at a place, read from the newest writes of the facts fs,
# is the newest of the writes at the place among fs
def Tops.of_get(
  +fs: List<&2, Types.Fact>,
  +g: RKnown.Place
) -> {
  RKnown.Tops.get(
    RKnown.Tops.of(fs),
    g
  )
    == Lists.List.top(~Types.Ask, ~RFacts.Ask.seq, RAnswers.Writes.of(fs, g)): Maybe<&2, Types.Ask>
}:
  Equal.trans(
    Maybe<&2, Types.Ask>,
    RKnown.Tops.get(RKnown.Tops.of(fs), g),
    Crits.Crit.lookup(Types.Ask, RKnown.Tops.of(fs), RKnown.Place.key(g)),
    Lists.List.top(~Types.Ask, ~RFacts.Ask.seq, RAnswers.Writes.of(fs, g)),
    Crits.Crit.get_lookup(~Types.Ask, RKnown.Tops.of(fs), RKnown.Place.key(g))(Tops.of_wf(fs)),
    Equal.trans(
      Maybe<&2, Types.Ask>,
      Crits.Crit.lookup(Types.Ask, RKnown.Tops.of(fs), RKnown.Place.key(g)),
      Top.over(
        Orders.Values.keep(~Types.Fact, ~List<&2, U32>, ~Fact.keyed, fs, RKnown.Place.key(g)),
        None{}
      ),
      Lists.List.top(~Types.Ask, ~RFacts.Ask.seq, RAnswers.Writes.of(fs, g)),
      Tops.go_lookup(fs, Crits.Crit.new(Types.Ask), RKnown.Place.key(g))({==}),
      Equal.trans(
        Maybe<&2, Types.Ask>,
        Top.over(
          Orders.Values.keep(~Types.Fact, ~List<&2, U32>, ~Fact.keyed, fs, RKnown.Place.key(g)),
          None{}
        ),
        Top.asks(RAnswers.Writes.of(fs, g), None{}),
        Lists.List.top(~Types.Ask, ~RFacts.Ask.seq, RAnswers.Writes.of(fs, g)),
        Top.over_writes(fs, g, None{}),
        Top.asks_none(RAnswers.Writes.of(fs, g))
      )
    )
  )

# a fact that is no write at the place of a key changes no fact kept for the
# key, when it joins sorted facts
def Keep.miss(
  fs: List<&2, Types.Fact>,
  +f: Types.Fact,
  +q: List<&2, U32>
) -> {
  Fact.keyed(q, f) == False{}: Bool
} -> {
  Orders.Values.keep(
    ~Types.Fact,
    ~List<&2, U32>,
    ~Fact.keyed,
    Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f),
    q
  )
    == Orders.Values.keep(~Types.Fact, ~List<&2, U32>, ~Fact.keyed, fs, q): List<&2, Types.Fact>
}:
  match fs:
    case Nil{}:
      h => (
        %Equal.sym(Bool, Fact.keyed(q, f), False{}, h): {List.filter.put(Types.Fact, f, [], _) == []: List<&2, Types.Fact>}
        {==})
    case Con{+y, +r}:
      +h => Lists.Bool.by(
        b => {
          Orders.Values.keep(
            ~Types.Fact,
            ~List<&2, U32>,
            ~Fact.keyed,
            Shared.Bool.when(
              List<&2, Types.Fact>,
              b,
              u => f <> y <> r,
              u => Shared.Bool.when(
                List<&2, Types.Fact>,
                Crits.Key.is_eq(Coded.Fact.words(y), Coded.Fact.words(f)),
                w => f <> r,
                w => y <> Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, r, f)
              )
            ),
            q
          )
            == Orders.Values.keep(
              ~Types.Fact,
              ~List<&2, U32>,
              ~Fact.keyed,
              y <> r,
              q
            ): List<&2, Types.Fact>
        },
        Orders.Key.lt(Coded.Fact.words(f), Coded.Fact.words(y)),
        et => (
          %Equal.sym(Bool, Fact.keyed(q, f), False{}, h): {List.filter.put(Types.Fact, f, Orders.Values.keep(~Types.Fact, ~List<&2, U32>, ~Fact.keyed, y <> r, q), _) == Orders.Values.keep(~Types.Fact, ~List<&2, U32>, ~Fact.keyed, y <> r, q): List<&2, Types.Fact>}
          {==}),
        ef => Lists.Bool.by(
          c => {
            Orders.Values.keep(
              ~Types.Fact,
              ~List<&2, U32>,
              ~Fact.keyed,
              Shared.Bool.when(
                List<&2, Types.Fact>,
                c,
                w => f <> r,
                w => y <> Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, r, f)
              ),
              q
            )
              == Orders.Values.keep(
                ~Types.Fact,
                ~List<&2, U32>,
                ~Fact.keyed,
                y <> r,
                q
              ): List<&2, Types.Fact>
          },
          Crits.Key.is_eq(Coded.Fact.words(y), Coded.Fact.words(f)),
          ee => (
            %Equal.sym(Bool, Fact.keyed(q, f), False{}, h): {List.filter.put(Types.Fact, f, Orders.Values.keep(~Types.Fact, ~List<&2, U32>, ~Fact.keyed, r, q), _) == Orders.Values.keep(~Types.Fact, ~List<&2, U32>, ~Fact.keyed, y <> r, q): List<&2, Types.Fact>}
            %Equal.sym(Types.Fact, y, f, Coded.Fact.words_inj(y, f)(Crits.Key.is_eq_sound(Coded.Fact.words(y), Coded.Fact.words(f))(ee))): {Orders.Values.keep(~Types.Fact, ~List<&2, U32>, ~Fact.keyed, r, q) == List.filter.put(Types.Fact, y, Orders.Values.keep(~Types.Fact, ~List<&2, U32>, ~Fact.keyed, r, q), Fact.keyed(q, _)): List<&2, Types.Fact>}
            %Equal.sym(Bool, Fact.keyed(q, f), False{}, h): {Orders.Values.keep(~Types.Fact, ~List<&2, U32>, ~Fact.keyed, r, q) == List.filter.put(Types.Fact, y, Orders.Values.keep(~Types.Fact, ~List<&2, U32>, ~Fact.keyed, r, q), _): List<&2, Types.Fact>}
            {==}),
          en => (
            %Keep.miss(r, f, q)(h): {List.filter.put(Types.Fact, y, Orders.Values.keep(~Types.Fact, ~List<&2, U32>, ~Fact.keyed, Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, r, f), q), Fact.keyed(q, y)) == List.filter.put(Types.Fact, y, _, Fact.keyed(q, y)): List<&2, Types.Fact>}
            {==})
        )
      )

# the ask mb, if any, is older than the number n
def Top.under(mb: Maybe<&2, Types.Ask>, n: Nat) -> Bool:
  match mb:
    case None{}:
      True{}
    case Some{b}:
      Nat.is_lt(RFacts.Ask.seq(b), n)

# the newest of the fact y, if it is at the place of the key q, and the ask
# mb, if any
def Top.at(y: Types.Fact, q: List<&2, U32>, mb: Maybe<&2, Types.Ask>) -> Maybe<&2, Types.Ask>:
  match y:
    case Types.Fact.Vote{v, st, x}:
      mb
    case Types.Fact.Ask{+b}:
      +mb = mb
      Bool.pick(
        Maybe<&2, Types.Ask>,
        Place.keyed(q, RKnown.Ask.place(b)),
        Some{Crits.Crit.merge(~Types.Ask, ~RKnown.Ask.later, mb, b)},
        mb
      )

# an ask that is newer than another, if any, is the newer of the two
def Top.merge_new(
  mb: Maybe<&2, Types.Ask>,
  +a: Types.Ask
) -> {
  Top.under(mb, RFacts.Ask.seq(a)) == True{}: Bool
} -> {Crits.Crit.merge(~Types.Ask, ~RKnown.Ask.later, mb, a) == a: Types.Ask}:
  match mb:
    case None{}:
      h => {==}
    case Some{+b}:
      h => (
        %Equal.sym(Bool, Nat.is_lt(RFacts.Ask.seq(b), RFacts.Ask.seq(a)), True{}, h): {Bool.pick(Types.Ask, _, a, b) == a: Types.Ask}
        {==})

# the newer of two asks that are older than a number is older than it
def Top.merge_old(
  mb: Maybe<&2, Types.Ask>,
  +y: Types.Ask,
  +n: Nat
) -> {
  Top.under(mb, n) == True{}: Bool
} -> {
  Nat.is_lt(RFacts.Ask.seq(y), n) == True{}: Bool
} -> {Top.under(Some{Crits.Crit.merge(~Types.Ask, ~RKnown.Ask.later, mb, y)}, n) == True{}: Bool}:
  match mb:
    case None{}:
      h => hy => hy
    case Some{+b}:
      h => hy => Lists.Bool.by(
        c => {Nat.is_lt(RFacts.Ask.seq(Bool.pick(Types.Ask, c, y, b)), n) == True{}: Bool},
        Nat.is_lt(RFacts.Ask.seq(b), RFacts.Ask.seq(y)),
        et => hy,
        ef => h
      )

# a number above the greatest number of facts is above that of the facts
# after the first
def Peak.tail(
  y: Types.Fact,
  +rest: List<&2, Types.Fact>,
  +n: Nat
) -> {
  Nat.is_lt(RFacts.Seq.peak(y <> rest), n) == True{}: Bool
} -> {Nat.is_lt(RFacts.Seq.peak(rest), n) == True{}: Bool}:
  match y:
    case Types.Fact.Ask{+a}:
      h => Shared.Nat.le_lt(
        RFacts.Seq.peak(rest),
        Nat.max(RFacts.Ask.seq(a), RFacts.Seq.peak(rest)),
        n
      )(Lists.Nat.le_max_right(RFacts.Ask.seq(a), RFacts.Seq.peak(rest)))(h)
    case Types.Fact.Vote{v, st, Types.Cast.Vote{r, Types.Pick{+a, pins}, b}}:
      h => Shared.Nat.le_lt(
        RFacts.Seq.peak(rest),
        Nat.max(RFacts.Ask.seq(a), RFacts.Seq.peak(rest)),
        n
      )(Lists.Nat.le_max_right(RFacts.Ask.seq(a), RFacts.Seq.peak(rest)))(h)
    case Types.Fact.Vote{v, st, Types.Cast.Pass{r}}:
      h => h

# a number above the greatest number of facts is above that of a first ask
def Peak.head(
  +a: Types.Ask,
  +rest: List<&2, Types.Fact>,
  +n: Nat
) -> {
  Nat.is_lt(RFacts.Seq.peak(Types.Fact.Ask{a} <> rest), n) == True{}: Bool
} -> {Nat.is_lt(RFacts.Ask.seq(a), n) == True{}: Bool}:
  h => Shared.Nat.le_lt(
    RFacts.Ask.seq(a),
    Nat.max(RFacts.Ask.seq(a), RFacts.Seq.peak(rest)),
    n
  )(Lists.Nat.le_max_left(RFacts.Ask.seq(a), RFacts.Seq.peak(rest)))(h)

# the newest of facts with a first fact, kept if it is at the place of a key
def Top.over_put(
  y: Types.Fact,
  +ks: List<&2, Types.Fact>,
  +q: List<&2, U32>,
  +mb: Maybe<&2, Types.Ask>
) -> {
  Top.over(
    List.filter.put(Types.Fact, y, ks, Fact.keyed(q, y)),
    mb
  )
    == Top.over(ks, Top.at(y, q, mb)): Maybe<&2, Types.Ask>
}:
  match y:
    case Types.Fact.Vote{v, st, x}:
      {==}
    case Types.Fact.Ask{+b}:
      Lists.Bool.by(
        c => {
          Top.over(
            List.filter.put(Types.Fact, Types.Fact.Ask{b}, ks, c),
            mb
          )
            == Top.over(
              ks,
              Bool.pick(
                Maybe<&2, Types.Ask>,
                c,
                Some{Crits.Crit.merge(~Types.Ask, ~RKnown.Ask.later, mb, b)},
                mb
              )
            ): Maybe<&2, Types.Ask>
        },
        Place.keyed(q, RKnown.Ask.place(b)),
        et => {==},
        ef => {==}
      )

# an ask that is newer than each of the facts stays the newest with their
# first
def Top.at_keep(
  y: Types.Fact,
  +rest: List<&2, Types.Fact>,
  +a: Types.Ask,
  +q: List<&2, U32>
) -> {
  Nat.is_lt(RFacts.Seq.peak(y <> rest), RFacts.Ask.seq(a)) == True{}: Bool
} -> {Top.at(y, q, Some{a}) == Some{a}: Maybe<&2, Types.Ask>}:
  match y:
    case Types.Fact.Vote{v, st, x}:
      h => {==}
    case Types.Fact.Ask{+b}:
      h => Lists.Bool.by(
        c => {
          Bool.pick(
            Maybe<&2, Types.Ask>,
            c,
            Some{Bool.pick(Types.Ask, Nat.is_lt(RFacts.Ask.seq(a), RFacts.Ask.seq(b)), b, a)},
            Some{a}
          )
            == Some{a}: Maybe<&2, Types.Ask>
        },
        Place.keyed(q, RKnown.Ask.place(b)),
        et => (
          %Equal.sym(Bool, Nat.is_lt(RFacts.Ask.seq(a), RFacts.Ask.seq(b)), False{}, Shared.Nat.le_nlt(RFacts.Ask.seq(b), RFacts.Ask.seq(a))(Shared.Nat.lt_weak(RFacts.Ask.seq(b), RFacts.Ask.seq(a))(Peak.head(b, rest, RFacts.Ask.seq(a))(h)))): {Some{Bool.pick(Types.Ask, _, b, a)} == Some{a}: Maybe<&2, Types.Ask>}
          {==}),
        ef => {==}
      )

# the first of facts, if it is at the place of a key, leaves an ask older
# than a number above each of the facts
def Top.at_under(
  y: Types.Fact,
  +rest: List<&2, Types.Fact>,
  +q: List<&2, U32>,
  +mb: Maybe<&2, Types.Ask>,
  +n: Nat
) -> {
  Nat.is_lt(RFacts.Seq.peak(y <> rest), n) == True{}: Bool
} -> {Top.under(mb, n) == True{}: Bool} -> {Top.under(Top.at(y, q, mb), n) == True{}: Bool}:
  match y:
    case Types.Fact.Vote{v, st, x}:
      hp => h => h
    case Types.Fact.Ask{+b}:
      hp => +h => Lists.Bool.by(
        c => {
          Top.under(
            Bool.pick(
              Maybe<&2, Types.Ask>,
              c,
              Some{Crits.Crit.merge(~Types.Ask, ~RKnown.Ask.later, mb, b)},
              mb
            ),
            n
          )
            == True{}: Bool
        },
        Place.keyed(q, RKnown.Ask.place(b)),
        et => Top.merge_old(mb, b, n)(h)(Peak.head(b, rest, n)(hp)),
        ef => h
      )

# an ask that is newer than each of the facts is the newest with those at
# the place of a key
def Top.keep(
  fs: List<&2, Types.Fact>,
  +a: Types.Ask,
  +q: List<&2, U32>
) -> {
  Nat.is_lt(RFacts.Seq.peak(fs), RFacts.Ask.seq(a)) == True{}: Bool
} -> {
  Top.over(
    Orders.Values.keep(~Types.Fact, ~List<&2, U32>, ~Fact.keyed, fs, q),
    Some{a}
  )
    == Some{a}: Maybe<&2, Types.Ask>
}:
  match fs:
    case Nil{}:
      h => {==}
    case Con{+y, +r}:
      +h => Equal.trans(
        Maybe<&2, Types.Ask>,
        Top.over(
          List.filter.put(
            Types.Fact,
            y,
            Orders.Values.keep(~Types.Fact, ~List<&2, U32>, ~Fact.keyed, r, q),
            Fact.keyed(q, y)
          ),
          Some{a}
        ),
        Top.over(
          Orders.Values.keep(~Types.Fact, ~List<&2, U32>, ~Fact.keyed, r, q),
          Top.at(y, q, Some{a})
        ),
        Some{a},
        Top.over_put(
          y,
          Orders.Values.keep(~Types.Fact, ~List<&2, U32>, ~Fact.keyed, r, q),
          q,
          Some{a}
        ),
        (
          %Equal.sym(Maybe<&2, Types.Ask>, Top.at(y, q, Some{a}), Some{a}, Top.at_keep(y, r, a, q)(h)): {Top.over(Orders.Values.keep(~Types.Fact, ~List<&2, U32>, ~Fact.keyed, r, q), _) == Some{a}: Maybe<&2, Types.Ask>}
          Top.keep(r, a, q)(Peak.tail(y, r, RFacts.Ask.seq(a))(h)))
      )

# an ask that is newer than each of the facts, and than the ask mb, is the
# newest at the key of its place, once it joins the facts
def Top.fresh(
  fs: List<&2, Types.Fact>,
  +a: Types.Ask,
  +q: List<&2, U32>,
  +mb: Maybe<&2, Types.Ask>
) -> {
  Place.keyed(q, RKnown.Ask.place(a)) == True{}: Bool
} -> {
  Nat.is_lt(RFacts.Seq.peak(fs), RFacts.Ask.seq(a)) == True{}: Bool
} -> {
  Top.under(mb, RFacts.Ask.seq(a)) == True{}: Bool
} -> {
  Top.over(
    Orders.Values.keep(
      ~Types.Fact,
      ~List<&2, U32>,
      ~Fact.keyed,
      Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, Types.Fact.Ask{a}),
      q
    ),
    mb
  )
    == Some{a}: Maybe<&2, Types.Ask>
}:
  match fs:
    case Nil{}:
      hk => hp => hu => (
        %Equal.sym(Bool, Place.keyed(q, RKnown.Ask.place(a)), True{}, hk): {Top.over(List.filter.put(Types.Fact, Types.Fact.Ask{a}, [], _), mb) == Some{a}: Maybe<&2, Types.Ask>}
        %Equal.sym(Types.Ask, Crits.Crit.merge(~Types.Ask, ~RKnown.Ask.later, mb, a), a, Top.merge_new(mb, a)(hu)): {Some{_} == Some{a}: Maybe<&2, Types.Ask>}
        {==})
    case Con{+y, +r}:
      +hk => +hp => +hu => Lists.Bool.by(
        b => {
          Top.over(
            Orders.Values.keep(
              ~Types.Fact,
              ~List<&2, U32>,
              ~Fact.keyed,
              Shared.Bool.when(
                List<&2, Types.Fact>,
                b,
                u => Types.Fact.Ask{a} <> y <> r,
                u => Shared.Bool.when(
                  List<&2, Types.Fact>,
                  Crits.Key.is_eq(Coded.Fact.words(y), Coded.Fact.words(Types.Fact.Ask{a})),
                  w => Types.Fact.Ask{a} <> r,
                  w => y
                    <> Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, r, Types.Fact.Ask{a})
                )
              ),
              q
            ),
            mb
          )
            == Some{a}: Maybe<&2, Types.Ask>
        },
        Orders.Key.lt(Coded.Fact.words(Types.Fact.Ask{a}), Coded.Fact.words(y)),
        et => (
          %Equal.sym(Bool, Place.keyed(q, RKnown.Ask.place(a)), True{}, hk): {Top.over(List.filter.put(Types.Fact, Types.Fact.Ask{a}, Orders.Values.keep(~Types.Fact, ~List<&2, U32>, ~Fact.keyed, y <> r, q), _), mb) == Some{a}: Maybe<&2, Types.Ask>}
          %Equal.sym(Types.Ask, Crits.Crit.merge(~Types.Ask, ~RKnown.Ask.later, mb, a), a, Top.merge_new(mb, a)(hu)): {Top.over(Orders.Values.keep(~Types.Fact, ~List<&2, U32>, ~Fact.keyed, y <> r, q), Some{_}) == Some{a}: Maybe<&2, Types.Ask>}
          Top.keep(y <> r, a, q)(hp)),
        ef => Lists.Bool.by(
          c => {
            Top.over(
              Orders.Values.keep(
                ~Types.Fact,
                ~List<&2, U32>,
                ~Fact.keyed,
                Shared.Bool.when(
                  List<&2, Types.Fact>,
                  c,
                  w => Types.Fact.Ask{a} <> r,
                  w => y
                    <> Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, r, Types.Fact.Ask{a})
                ),
                q
              ),
              mb
            )
              == Some{a}: Maybe<&2, Types.Ask>
          },
          Crits.Key.is_eq(Coded.Fact.words(y), Coded.Fact.words(Types.Fact.Ask{a})),
          ee => (
            %Equal.sym(Bool, Place.keyed(q, RKnown.Ask.place(a)), True{}, hk): {Top.over(List.filter.put(Types.Fact, Types.Fact.Ask{a}, Orders.Values.keep(~Types.Fact, ~List<&2, U32>, ~Fact.keyed, r, q), _), mb) == Some{a}: Maybe<&2, Types.Ask>}
            %Equal.sym(Types.Ask, Crits.Crit.merge(~Types.Ask, ~RKnown.Ask.later, mb, a), a, Top.merge_new(mb, a)(hu)): {Top.over(Orders.Values.keep(~Types.Fact, ~List<&2, U32>, ~Fact.keyed, r, q), Some{_}) == Some{a}: Maybe<&2, Types.Ask>}
            Top.keep(r, a, q)(Peak.tail(y, r, RFacts.Ask.seq(a))(hp))),
          en => Equal.trans(
            Maybe<&2, Types.Ask>,
            Top.over(
              List.filter.put(
                Types.Fact,
                y,
                Orders.Values.keep(
                  ~Types.Fact,
                  ~List<&2, U32>,
                  ~Fact.keyed,
                  Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, r, Types.Fact.Ask{a}),
                  q
                ),
                Fact.keyed(q, y)
              ),
              mb
            ),
            Top.over(
              Orders.Values.keep(
                ~Types.Fact,
                ~List<&2, U32>,
                ~Fact.keyed,
                Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, r, Types.Fact.Ask{a}),
                q
              ),
              Top.at(y, q, mb)
            ),
            Some{a},
            Top.over_put(
              y,
              Orders.Values.keep(
                ~Types.Fact,
                ~List<&2, U32>,
                ~Fact.keyed,
                Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, r, Types.Fact.Ask{a}),
                q
              ),
              q,
              mb
            ),
            Top.fresh(
              r,
              a,
              q,
              Top.at(y, q, mb)
            )(
              hk
            )(
              Peak.tail(y, r, RFacts.Ask.seq(a))(hp)
            )(Top.at_under(y, r, q, mb, RFacts.Ask.seq(a))(hp)(hu))
          )
        )
      )

# the fact f is a vote, or an ask that is newer than the number n
def Fact.fresh(f: Types.Fact, n: Nat) -> Bool:
  match f:
    case Types.Fact.Vote{v, st, x}:
      True{}
    case Types.Fact.Ask{a}:
      Nat.is_lt(n, RFacts.Ask.seq(a))

# newest writes with the write of a newer ask are well formed when they were
def Tops.set_wf(
  +tx: Crits.Crit<Types.Ask>,
  +a: Types.Ask,
  m: Maybe<&2, RKnown.Place>
) -> {
  Crits.Crit.wf(~Types.Ask, tx, 0n) == True{}: Bool
} -> {Crits.Crit.wf(~Types.Ask, RKnown.Tops.set(tx, a, m), 0n) == True{}: Bool}:
  match m:
    case None{}:
      w => w
    case Some{+g}:
      w => Crits.Crit.upsert_wf(~Types.Ask, ~(w2 => x => x), tx, RKnown.Place.key(g), a)(w)

# a value that takes the place of another, if any
def Tops.merge_set(
  e: Maybe<&2, Types.Ask>,
  a: Types.Ask
) -> {Crits.Crit.merge(~Types.Ask, ~(w => x => x), e, a) == a: Types.Ask}:
  match e:
    case None{}:
      {==}
    case Some{b}:
      {==}

# what newest writes with the write of a newer ask hold under a key: at the
# key of the place of the ask, the ask
def Tops.set_lookup(
  +tx: Crits.Crit<Types.Ask>,
  +a: Types.Ask,
  m: Maybe<&2, RKnown.Place>,
  +q: List<&2, U32>
) -> {
  Crits.Crit.wf(~Types.Ask, tx, 0n) == True{}: Bool
} -> {
  Crits.Crit.lookup(
    Types.Ask,
    RKnown.Tops.set(tx, a, m),
    q
  )
    == Bool.pick(
      Maybe<&2, Types.Ask>,
      Place.keyed(q, m),
      Some{a},
      Crits.Crit.lookup(Types.Ask, tx, q)
    ): Maybe<&2, Types.Ask>
}:
  match m:
    case None{}:
      w => {==}
    case Some{+g}:
      w => (
        %Tops.merge_set(Crits.Crit.lookup(Types.Ask, tx, RKnown.Place.key(g)), a): {Crits.Crit.lookup(Types.Ask, Crits.Crit.upsert(~Types.Ask, ~(w2 => x => x), tx, RKnown.Place.key(g), a), q) == Bool.pick(Maybe<&2, Types.Ask>, Crits.Key.is_eq(q, RKnown.Place.key(g)), Some{_}, Crits.Crit.lookup(Types.Ask, tx, q)): Maybe<&2, Types.Ask>}
        Crits.Crit.upsert_lookup(~Types.Ask, ~(w2 => x => x), tx, RKnown.Place.key(g), a, q)(w))

# newest writes with a newer fact are well formed when they were
def Tops.join_wf(
  +tx: Crits.Crit<Types.Ask>,
  f: Types.Fact
) -> {
  Crits.Crit.wf(~Types.Ask, tx, 0n) == True{}: Bool
} -> {Crits.Crit.wf(~Types.Ask, RKnown.Tops.join(tx, f), 0n) == True{}: Bool}:
  match f:
    case Types.Fact.Vote{v, st, x}:
      w => w
    case Types.Fact.Ask{+a}:
      w => Tops.set_wf(tx, a, RKnown.Ask.place(a))(w)

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof does not run
# under each key, the newest writes of facts with a newer fact hold what the
# newest writes of the facts hold, with the fact
def Tops.join_lookup(
  +fs: List<&2, Types.Fact>,
  f: Types.Fact,
  +q: List<&2, U32>
) -> {
  Fact.fresh(f, RFacts.Seq.peak(fs)) == True{}: Bool
} -> {
  Crits.Crit.lookup(
    Types.Ask,
    RKnown.Tops.of(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f)),
    q
  )
    == Crits.Crit.lookup(
      Types.Ask,
      RKnown.Tops.join(RKnown.Tops.of(fs), f),
      q
    ): Maybe<&2, Types.Ask>
}:
  match f:
    case Types.Fact.Vote{+v, +st, +x}:
      h => Equal.trans(
        Maybe<&2, Types.Ask>,
        Crits.Crit.lookup(
          Types.Ask,
          RKnown.Tops.of(
            Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, Types.Fact.Vote{v, st, x})
          ),
          q
        ),
        Top.over(Orders.Values.keep(~Types.Fact, ~List<&2, U32>, ~Fact.keyed, fs, q), None{}),
        Crits.Crit.lookup(Types.Ask, RKnown.Tops.of(fs), q),
        (
          %Keep.miss(fs, Types.Fact.Vote{v, st, x}, q)({==}): {Crits.Crit.lookup(Types.Ask, RKnown.Tops.of(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, Types.Fact.Vote{v, st, x})), q) == Top.over(_, None{}): Maybe<&2, Types.Ask>}
          Tops.go_lookup(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, Types.Fact.Vote{v, st, x}), Crits.Crit.new(Types.Ask), q)({==})),
        Equal.sym(
          Maybe<&2, Types.Ask>,
          Crits.Crit.lookup(Types.Ask, RKnown.Tops.of(fs), q),
          Top.over(Orders.Values.keep(~Types.Fact, ~List<&2, U32>, ~Fact.keyed, fs, q), None{}),
          Tops.go_lookup(fs, Crits.Crit.new(Types.Ask), q)({==})
        )
      )
    case Types.Fact.Ask{+a}:
      h => Equal.trans(
        Maybe<&2, Types.Ask>,
        Crits.Crit.lookup(
          Types.Ask,
          RKnown.Tops.of(
            Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, Types.Fact.Ask{a})
          ),
          q
        ),
        Bool.pick(
          Maybe<&2, Types.Ask>,
          Place.keyed(q, RKnown.Ask.place(a)),
          Some{a},
          Crits.Crit.lookup(Types.Ask, RKnown.Tops.of(fs), q)
        ),
        Crits.Crit.lookup(
          Types.Ask,
          RKnown.Tops.set(RKnown.Tops.of(fs), a, RKnown.Ask.place(a)),
          q
        ),
        Equal.trans(
          Maybe<&2, Types.Ask>,
          Crits.Crit.lookup(
            Types.Ask,
            RKnown.Tops.of(
              Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, Types.Fact.Ask{a})
            ),
            q
          ),
          Top.over(
            Orders.Values.keep(
              ~Types.Fact,
              ~List<&2, U32>,
              ~Fact.keyed,
              Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, Types.Fact.Ask{a}),
              q
            ),
            None{}
          ),
          Bool.pick(
            Maybe<&2, Types.Ask>,
            Place.keyed(q, RKnown.Ask.place(a)),
            Some{a},
            Crits.Crit.lookup(Types.Ask, RKnown.Tops.of(fs), q)
          ),
          Tops.go_lookup(
            Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, Types.Fact.Ask{a}),
            Crits.Crit.new(Types.Ask),
            q
          )({==}),
          Lists.Bool.by(
            c => {
              Place.keyed(q, RKnown.Ask.place(a)) == c: Bool
            } -> {
              Top.over(
                Orders.Values.keep(
                  ~Types.Fact,
                  ~List<&2, U32>,
                  ~Fact.keyed,
                  Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, Types.Fact.Ask{a}),
                  q
                ),
                None{}
              )
                == Bool.pick(
                  Maybe<&2, Types.Ask>,
                  c,
                  Some{a},
                  Crits.Crit.lookup(Types.Ask, RKnown.Tops.of(fs), q)
                ): Maybe<&2, Types.Ask>
            },
            Place.keyed(q, RKnown.Ask.place(a)),
            et => hk => Top.fresh(fs, a, q, None{})(hk)(h)({==}),
            ef => hk => (
              %Equal.sym(List<&2, Types.Fact>, Orders.Values.keep(~Types.Fact, ~List<&2, U32>, ~Fact.keyed, Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, Types.Fact.Ask{a}), q), Orders.Values.keep(~Types.Fact, ~List<&2, U32>, ~Fact.keyed, fs, q), Keep.miss(fs, Types.Fact.Ask{a}, q)(hk)): {Top.over(_, None{}) == Crits.Crit.lookup(Types.Ask, RKnown.Tops.of(fs), q): Maybe<&2, Types.Ask>}
              Equal.sym(Maybe<&2, Types.Ask>, Crits.Crit.lookup(Types.Ask, RKnown.Tops.of(fs), q), Top.over(Orders.Values.keep(~Types.Fact, ~List<&2, U32>, ~Fact.keyed, fs, q), None{}), Tops.go_lookup(fs, Crits.Crit.new(Types.Ask), q)({==})))
          )({==})
        ),
        Equal.sym(
          Maybe<&2, Types.Ask>,
          Crits.Crit.lookup(
            Types.Ask,
            RKnown.Tops.set(RKnown.Tops.of(fs), a, RKnown.Ask.place(a)),
            q
          ),
          Bool.pick(
            Maybe<&2, Types.Ask>,
            Place.keyed(q, RKnown.Ask.place(a)),
            Some{a},
            Crits.Crit.lookup(Types.Ask, RKnown.Tops.of(fs), q)
          ),
          Tops.set_lookup(RKnown.Tops.of(fs), a, RKnown.Ask.place(a), q)(Tops.of_wf(fs))
        )
      )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the newest writes of facts with a newer fact, and the newest writes of the
# facts with the fact, hold the same under the key of each of the entries es
def Tops.join_same(
  es: List<&2, Crits.Bind<Types.Ask>>,
  +fs: List<&2, Types.Fact>,
  +f: Types.Fact
) -> {
  Fact.fresh(f, RFacts.Seq.peak(fs)) == True{}: Bool
} -> Orders.Binds.Same(
  Types.Ask,
  es,
  Crits.Crit.entries(
    Types.Ask,
    RKnown.Tops.of(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f))
  ),
  Crits.Crit.entries(Types.Ask, RKnown.Tops.join(RKnown.Tops.of(fs), f))
):
  match es:
    case Nil{}:
      h => Unit{}
    case Con{Crits.Bind{+q, v}, rest}:
      +h => (
        Equal.trans(
          Maybe<&2, Types.Ask>,
          Orders.Binds.get(
            Types.Ask,
            Crits.Crit.entries(
              Types.Ask,
              RKnown.Tops.of(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f))
            ),
            q
          ),
          Crits.Crit.lookup(
            Types.Ask,
            RKnown.Tops.of(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f)),
            q
          ),
          Orders.Binds.get(
            Types.Ask,
            Crits.Crit.entries(Types.Ask, RKnown.Tops.join(RKnown.Tops.of(fs), f)),
            q
          ),
          Orders.Crit.get_entries(
            Types.Ask,
            RKnown.Tops.of(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f)),
            q
          ),
          Equal.trans(
            Maybe<&2, Types.Ask>,
            Crits.Crit.lookup(
              Types.Ask,
              RKnown.Tops.of(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f)),
              q
            ),
            Crits.Crit.lookup(Types.Ask, RKnown.Tops.join(RKnown.Tops.of(fs), f), q),
            Orders.Binds.get(
              Types.Ask,
              Crits.Crit.entries(Types.Ask, RKnown.Tops.join(RKnown.Tops.of(fs), f)),
              q
            ),
            Tops.join_lookup(fs, f, q)(h),
            Equal.sym(
              Maybe<&2, Types.Ask>,
              Orders.Binds.get(
                Types.Ask,
                Crits.Crit.entries(Types.Ask, RKnown.Tops.join(RKnown.Tops.of(fs), f)),
                q
              ),
              Crits.Crit.lookup(Types.Ask, RKnown.Tops.join(RKnown.Tops.of(fs), f), q),
              Orders.Crit.get_entries(Types.Ask, RKnown.Tops.join(RKnown.Tops.of(fs), f), q)
            )
          )
        ),
        Tops.join_same(rest, fs, f)(h)
      )

# the newest writes of sorted facts with a fact that is newer than each of
# them (or a vote) are the newest writes of the facts, with the fact
def Tops.of_insert(
  +fs: List<&2, Types.Fact>,
  +f: Types.Fact
) -> {
  Fact.fresh(f, RFacts.Seq.peak(fs)) == True{}: Bool
} -> {
  RKnown.Tops.of(
    Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f)
  )
    == RKnown.Tops.join(RKnown.Tops.of(fs), f): Crits.Crit<Types.Ask>
}:
  +h => Crits.Crit.ext(
    ~Types.Ask,
    RKnown.Tops.of(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f)),
    RKnown.Tops.join(RKnown.Tops.of(fs), f)
  )(
    Tops.of_wf(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f))
  )(
    Tops.join_wf(RKnown.Tops.of(fs), f)(Tops.of_wf(fs))
  )(
    Orders.Binds.ext(
      ~Types.Ask,
      Crits.Crit.entries(
        Types.Ask,
        RKnown.Tops.of(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f))
      ),
      Crits.Crit.entries(Types.Ask, RKnown.Tops.join(RKnown.Tops.of(fs), f))
    )(
      Orders.Crit.entries_sorted(
        ~Types.Ask,
        RKnown.Tops.of(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f))
      )(Tops.of_wf(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f)))
    )(
      Orders.Crit.entries_sorted(
        ~Types.Ask,
        RKnown.Tops.join(RKnown.Tops.of(fs), f)
      )(Tops.join_wf(RKnown.Tops.of(fs), f)(Tops.of_wf(fs)))
    )(
      Tops.join_same(
        Crits.Crit.entries(
          Types.Ask,
          RKnown.Tops.of(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f))
        ),
        fs,
        f
      )(h)
    )(
      Tops.join_same(
        Crits.Crit.entries(Types.Ask, RKnown.Tops.join(RKnown.Tops.of(fs), f)),
        fs,
        f
      )(h)
    )
  )

# an ask, if any, is the same as itself
def End.same_refl(
  e: Maybe<&2, Types.Ask>
) -> {Shared.Maybe.is_eq(~Types.Ask, ~Coded.Ask.is_eq, e, e) == True{}: Bool}:
  match e:
    case None{}:
      {==}
    case Some{v}:
      Coded.Ask.is_eq_refl(v)

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof does not run
# bend-lint: expect-begin bend-lint-rules/performance/missed_fork@hint -- a proof does not run
# Tops.same is True for newest writes and themselves
def Tops.same_refl(a: Crits.Crit<Types.Ask>) -> {RKnown.Tops.same(a, a) == True{}: Bool}:
  match a:
    case Crits.Crit.Tip{}:
      {==}
    case Crits.Crit.Leaf{+k, +v}:
      Shared.Bool.and_both(
        Crits.Key.is_eq(k, k),
        Coded.Ask.is_eq(v, v)
      )(Crits.Key.is_eq_refl(k))(Coded.Ask.is_eq_refl(v))
    case Crits.Crit.Fork{+r, +p, +e, +z, +o}:
      Shared.Bool.and_both(
        Crits.Key.is_eq(r, r),
        Bool.and(
          Nat.is_eq(p, p),
          Bool.and(
            Shared.Maybe.is_eq(~Types.Ask, ~Coded.Ask.is_eq, e, e),
            Bool.and(RKnown.Tops.same(z, z), RKnown.Tops.same(o, o))
          )
        )
      )(
        Crits.Key.is_eq_refl(r)
      )(
        Shared.Bool.and_both(
          Nat.is_eq(p, p),
          Bool.and(
            Shared.Maybe.is_eq(~Types.Ask, ~Coded.Ask.is_eq, e, e),
            Bool.and(RKnown.Tops.same(z, z), RKnown.Tops.same(o, o))
          )
        )(
          Shared.Nat.is_eq_refl(p)
        )(
          Shared.Bool.and_both(
            Shared.Maybe.is_eq(~Types.Ask, ~Coded.Ask.is_eq, e, e),
            Bool.and(RKnown.Tops.same(z, z), RKnown.Tops.same(o, o))
          )(
            End.same_refl(e)
          )(
            Shared.Bool.and_both(
              RKnown.Tops.same(z, z),
              RKnown.Tops.same(o, o)
            )(Tops.same_refl(z))(Tops.same_refl(o))
          )
        )
      )
# bend-lint: expect-end bend-lint-rules/performance/missed_fork@hint

# Tops.same is True only for equal newest writes
def Tops.same_sound(
  a: Crits.Crit<Types.Ask>,
  b: Crits.Crit<Types.Ask>
) -> {RKnown.Tops.same(a, b) == True{}: Bool} -> {a == b: Crits.Crit<Types.Ask>}:
  match a b:
    case Crits.Crit.Tip{} Crits.Crit.Tip{}:
      h => {==}
    case Crits.Crit.Tip{} Crits.Crit.Leaf{k2, v2}:
      h => Empty.absurd(
        {Crits.Crit.Tip{} == Crits.Crit.Leaf{k2, v2}: Crits.Crit<Types.Ask>},
        Shared.Bool.false_ne_true(h)
      )
    case Crits.Crit.Tip{} Crits.Crit.Fork{r2, p2, e2, z2, o2}:
      h => Empty.absurd(
        {Crits.Crit.Tip{} == Crits.Crit.Fork{r2, p2, e2, z2, o2}: Crits.Crit<Types.Ask>},
        Shared.Bool.false_ne_true(h)
      )
    case Crits.Crit.Leaf{k1, v1} Crits.Crit.Tip{}:
      h => Empty.absurd(
        {Crits.Crit.Leaf{k1, v1} == Crits.Crit.Tip{}: Crits.Crit<Types.Ask>},
        Shared.Bool.false_ne_true(h)
      )
    case Crits.Crit.Leaf{k1, v1} Crits.Crit.Fork{r2, p2, e2, z2, o2}:
      h => Empty.absurd(
        {Crits.Crit.Leaf{k1, v1} == Crits.Crit.Fork{r2, p2, e2, z2, o2}: Crits.Crit<Types.Ask>},
        Shared.Bool.false_ne_true(h)
      )
    case Crits.Crit.Fork{r1, p1, e1, z1, o1} Crits.Crit.Tip{}:
      h => Empty.absurd(
        {Crits.Crit.Fork{r1, p1, e1, z1, o1} == Crits.Crit.Tip{}: Crits.Crit<Types.Ask>},
        Shared.Bool.false_ne_true(h)
      )
    case Crits.Crit.Fork{r1, p1, e1, z1, o1} Crits.Crit.Leaf{k2, v2}:
      h => Empty.absurd(
        {Crits.Crit.Fork{r1, p1, e1, z1, o1} == Crits.Crit.Leaf{k2, v2}: Crits.Crit<Types.Ask>},
        Shared.Bool.false_ne_true(h)
      )
    case Crits.Crit.Leaf{+k1, +v1} Crits.Crit.Leaf{+k2, +v2}:
      +h => (
        %Crits.Key.is_eq_sound(k1, k2)(Shared.Bool.and_true_left(Crits.Key.is_eq(k1, k2), Coded.Ask.is_eq(v1, v2))(h)): {Crits.Crit.Leaf{k1, v1} == Crits.Crit.Leaf{_, v2}: Crits.Crit<Types.Ask>}
        %Coded.Ask.is_eq_sound(v1, v2)(Shared.Bool.and_true_right(Crits.Key.is_eq(k1, k2), Coded.Ask.is_eq(v1, v2))(h)): {Crits.Crit.Leaf{k1, v1} == Crits.Crit.Leaf{k1, _}: Crits.Crit<Types.Ask>}
        {==})
    case Crits.Crit.Fork{+r1, +p1, +e1, +z1, +o1} Crits.Crit.Fork{+r2, +p2, +e2, +z2, +o2}:
      +h => (
        %Crits.Key.is_eq_sound(r1, r2)(Shared.Bool.and_true_left(Crits.Key.is_eq(r1, r2), Bool.and(Nat.is_eq(p1, p2), Bool.and(Shared.Maybe.is_eq(~Types.Ask, ~Coded.Ask.is_eq, e1, e2), Bool.and(RKnown.Tops.same(z1, z2), RKnown.Tops.same(o1, o2)))))(h)): {Crits.Crit.Fork{r1, p1, e1, z1, o1} == Crits.Crit.Fork{_, p2, e2, z2, o2}: Crits.Crit<Types.Ask>}
        %Shared.Nat.is_eq_sound(p1, p2)(Shared.Bool.and_true_left(Nat.is_eq(p1, p2), Bool.and(Shared.Maybe.is_eq(~Types.Ask, ~Coded.Ask.is_eq, e1, e2), Bool.and(RKnown.Tops.same(z1, z2), RKnown.Tops.same(o1, o2))))(Shared.Bool.and_true_right(Crits.Key.is_eq(r1, r2), Bool.and(Nat.is_eq(p1, p2), Bool.and(Shared.Maybe.is_eq(~Types.Ask, ~Coded.Ask.is_eq, e1, e2), Bool.and(RKnown.Tops.same(z1, z2), RKnown.Tops.same(o1, o2)))))(h))): {Crits.Crit.Fork{r1, p1, e1, z1, o1} == Crits.Crit.Fork{r1, _, e2, z2, o2}: Crits.Crit<Types.Ask>}
        %Shared.Maybe.is_eq_sound(~Types.Ask, ~Coded.Ask.is_eq, x => y => Coded.Ask.is_eq_sound(x, y), e1, e2)(Shared.Bool.and_true_left(Shared.Maybe.is_eq(~Types.Ask, ~Coded.Ask.is_eq, e1, e2), Bool.and(RKnown.Tops.same(z1, z2), RKnown.Tops.same(o1, o2)))(Shared.Bool.and_true_right(Nat.is_eq(p1, p2), Bool.and(Shared.Maybe.is_eq(~Types.Ask, ~Coded.Ask.is_eq, e1, e2), Bool.and(RKnown.Tops.same(z1, z2), RKnown.Tops.same(o1, o2))))(Shared.Bool.and_true_right(Crits.Key.is_eq(r1, r2), Bool.and(Nat.is_eq(p1, p2), Bool.and(Shared.Maybe.is_eq(~Types.Ask, ~Coded.Ask.is_eq, e1, e2), Bool.and(RKnown.Tops.same(z1, z2), RKnown.Tops.same(o1, o2)))))(h)))): {Crits.Crit.Fork{r1, p1, e1, z1, o1} == Crits.Crit.Fork{r1, p1, _, z2, o2}: Crits.Crit<Types.Ask>}
        %Tops.same_sound(z1, z2)(Shared.Bool.and_true_left(RKnown.Tops.same(z1, z2), RKnown.Tops.same(o1, o2))(Shared.Bool.and_true_right(Shared.Maybe.is_eq(~Types.Ask, ~Coded.Ask.is_eq, e1, e2), Bool.and(RKnown.Tops.same(z1, z2), RKnown.Tops.same(o1, o2)))(Shared.Bool.and_true_right(Nat.is_eq(p1, p2), Bool.and(Shared.Maybe.is_eq(~Types.Ask, ~Coded.Ask.is_eq, e1, e2), Bool.and(RKnown.Tops.same(z1, z2), RKnown.Tops.same(o1, o2))))(Shared.Bool.and_true_right(Crits.Key.is_eq(r1, r2), Bool.and(Nat.is_eq(p1, p2), Bool.and(Shared.Maybe.is_eq(~Types.Ask, ~Coded.Ask.is_eq, e1, e2), Bool.and(RKnown.Tops.same(z1, z2), RKnown.Tops.same(o1, o2)))))(h))))): {Crits.Crit.Fork{r1, p1, e1, z1, o1} == Crits.Crit.Fork{r1, p1, e1, _, o2}: Crits.Crit<Types.Ask>}
        %Tops.same_sound(o1, o2)(Shared.Bool.and_true_right(RKnown.Tops.same(z1, z2), RKnown.Tops.same(o1, o2))(Shared.Bool.and_true_right(Shared.Maybe.is_eq(~Types.Ask, ~Coded.Ask.is_eq, e1, e2), Bool.and(RKnown.Tops.same(z1, z2), RKnown.Tops.same(o1, o2)))(Shared.Bool.and_true_right(Nat.is_eq(p1, p2), Bool.and(Shared.Maybe.is_eq(~Types.Ask, ~Coded.Ask.is_eq, e1, e2), Bool.and(RKnown.Tops.same(z1, z2), RKnown.Tops.same(o1, o2))))(Shared.Bool.and_true_right(Crits.Key.is_eq(r1, r2), Bool.and(Nat.is_eq(p1, p2), Bool.and(Shared.Maybe.is_eq(~Types.Ask, ~Coded.Ask.is_eq, e1, e2), Bool.and(RKnown.Tops.same(z1, z2), RKnown.Tops.same(o1, o2)))))(h))))): {Crits.Crit.Fork{r1, p1, e1, z1, o1} == Crits.Crit.Fork{r1, p1, e1, z1, _}: Crits.Crit<Types.Ask>}
        {==})
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information
