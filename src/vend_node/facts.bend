import Base
import ../shared/shared/ledger.bend as Ledgers
import ../shared/shared/shared/shared/crit.bend as Crits
import ../shared/shared/shared/shared/hash.bend as Hashes
import ../shared/shared/shared/shared/shared.bend as Shared
import ../shared/shared/shared/text.bend as Texts
import ./codes.bend as Coded
import ./run/facts.bend as RFacts
import ./shared/lists.bend as Lists
import ./shared/set.bend as Sets
import ./spec.bend as Spec
import ./types.bend as Types

# The facts of a node
# -------------------
# The facts are a set with one shape for its content (Sets), so two nodes that
# hold the same facts hold equal sets, and all that is read from the set is the
# same at both.
#
# The code that runs is in run/facts.bend: it holds the plain map of the set
# (Facts.crit) and builds no proof. Here each def that reads the facts is
# that code on the map of the set, and each def that gives facts builds the
# proofs that its map is a set; it never runs. Its map is what the code that
# runs gives (Laws of the maps).

# the facts of a node
def Facts() -> Data:
  Sets.ValSet(~Types.Fact, ~Coded.Fact.words)

# the map of the facts s: what the code that runs holds
def Facts.crit(s: Facts()) -> RFacts.Plain():
  Sets.ValSet.crit(~Types.Fact, ~Coded.Fact.words, s)

# no fact
def Facts.new() -> Facts():
  Sets.ValSet.new(~Types.Fact, ~Coded.Fact.words)

# s holds the fact f
def Facts.has(s: Facts(), +f: Types.Fact) -> Bool:
  RFacts.Facts.has(Facts.crit(s), f)

# s with the fact f
def Facts.add(+s: Facts(), +f: Types.Fact) -> Facts():
  Sets.ValSet.add(~Types.Fact, ~Coded.Fact.words, s, f)

# the facts of s, each once
def Facts.list(s: Facts()) -> List<&2, Types.Fact>:
  RFacts.Facts.list(Facts.crit(s))

# how far a read of s may go from line to line: the count of its facts
def Facts.fuel(s: Facts()) -> Nat:
  RFacts.Facts.fuel(Facts.crit(s))

# Changes
# -------

# s holds the change c: the fact, or both votes of the lie, which differ
def Facts.holds(+s: Facts(), c: Types.Change) -> Bool:
  RFacts.Facts.holds(Facts.crit(s), c)

# Liars
# -----

# the voters that s proves to be liars: those with two votes that contradict
# each other
def Facts.liars(s: Facts()) -> List<&2, String>:
  RFacts.Facts.liars(Facts.crit(s))

# Trust
# -----
# A node trusts two things that no proof gives: that nobody else casts a vote
# under its name, and that no two requests start one store (SHA-256). When a
# node sees either broken, it says so with two votes that contradict each
# other, under a name of its own that is not its name. So it names a liar,
# and no law about a node that names no liar binds it any more. The names
# that start with '~' are reserved: no node has one, so the name under which
# a node says that its trust broke is never the name of a node.

# the name under which a node says that its trust broke is reserved
def Trust.voter_reserved(
  name: String
) -> {RFacts.Trust.reserved(RFacts.Trust.voter(name)) == True{}: Bool}:
  {==}

# s, where the trust of the node name broke
def Trust.break(s: Facts(), +name: String) -> Facts():
  Facts.add(Facts.add(s, RFacts.Trust.one(name)), RFacts.Trust.two(name))

# s says that the trust of the node name broke
def Trust.broken(+s: Facts(), +name: String) -> Bool:
  RFacts.Trust.broken(Facts.crit(s), name)

# Starts
# ------

# two asks of s start one store with different ids or requests
def Facts.collide(s: Facts()) -> Bool:
  RFacts.Facts.collide(Facts.crit(s))

# Taking a fact in
# ----------------

# the fact f is a vote under the name of the node that contradicts a vote that
# s holds: the node did not cast it
def Facts.refuses(+name: String, s: Facts(), f: Types.Fact) -> Bool:
  RFacts.Facts.refuses(name, Facts.crit(s), f)

# s with the fact f, as the node name takes it in: it does not take a vote
# under its own name that contradicts one that it holds, and it says that its
# trust broke when it sees such a vote, or a second start of one store
def Facts.take(+name: String, +s: Facts(), +f: Types.Fact) -> Facts():
  Shared.Bool.when(
    Facts(),
    Facts.refuses(name, s, f),
    u => Trust.break(s, name),
    u => Shared.Bool.when(
      Facts(),
      RFacts.Fact.collided(Facts.list(s), f),
      u => Trust.break(Facts.add(s, f), name),
      u => Facts.add(s, f)
    )
  )

# s with each of the facts fs, as the node name takes them in
def Facts.take_all(+name: String, fs: List<&2, Types.Fact>, +s: Facts()) -> Facts():
  match fs:
    case Nil{}:
      s
    case Con{f, rest}:
      Facts.take_all(name, rest, Facts.take(name, s, f))

# the facts s are sound for the node name: s does not name the node a liar,
# and, if two asks of s start one store, s says that the trust of the node
# broke
def Facts.ok(+name: String, +s: Facts()) -> Bool:
  RFacts.Facts.ok(name, Facts.crit(s))

# Votes of the node
# -----------------

# s holds a vote of the node name for the step st
def Facts.cast(s: Facts(), name: String, st: Types.Step) -> Bool:
  RFacts.Facts.cast(Facts.crit(s), name, st)

# Asks
# ----

# the ask of the request r of the id i, as a node that holds s takes it in:
# with a number above every number in s
def Facts.asked(s: Facts(), i: Ledgers.Id, r: Spec.Request) -> Types.Ask:
  RFacts.Facts.asked(Facts.crit(s), i, r)

# s after the node name takes in the request r of the id i
def Facts.ask(+name: String, +s: Facts(), i: Ledgers.Id, r: Spec.Request) -> Facts():
  Facts.take(name, s, Types.Fact.Ask{Facts.asked(s, i, r)})

# Wider sets
# ----------

# b holds the fact f
def Fact.held(b: Facts(), f: Types.Fact) -> Bool:
  RFacts.Fact.held(Facts.crit(b), f)

# b holds each fact of a, and a read of b may go as far as one of a
def Facts.wider(+a: Facts(), +b: Facts()) -> Bool:
  RFacts.Facts.wider(Facts.crit(a), Facts.crit(b))

# Cases
# -----

# a test that is not True is False
def Case.false_of(b: Bool) -> ({b == True{}: Bool} -> Empty) -> {b == False{}: Bool}:
  match b:
    case True{}:
      no => Empty.absurd({True{} == False{}: Bool}, no({==}))
    case False{}:
      no => {==}

# a test that is not False is True
def Case.true_of(b: Bool) -> ({b == False{}: Bool} -> Empty) -> {b == True{}: Bool}:
  match b:
    case True{}:
      no => {==}
    case False{}:
      no => Empty.absurd({False{} == True{}: Bool}, no({==}))

# the "not" of False is True
def Case.not_of(b: Bool) -> {b == False{}: Bool} -> {Bool.not(b) == True{}: Bool}:
  match b:
    case True{}:
      h => Empty.absurd({False{} == True{}: Bool}, Shared.Bool.true_ne_false(h))
    case False{}:
      h => {==}

# what follows from each side of a true "or" follows
def Case.or_by(
  -P: Type,
  a: Bool,
  -b: Bool,
  h: {Bool.or(a, b) == True{}: Bool},
  fa: {a == True{}: Bool} -> P,
  fb: {b == True{}: Bool} -> P
) -> P:
  match a:
    case True{}:
      fa({==})
    case False{}:
      fb(h)

# an "or" with a true first side is true
def Case.or_left(a: Bool, -b: Bool) -> {a == True{}: Bool} -> {Bool.or(a, b) == True{}: Bool}:
  match a:
    case True{}:
      h => {==}
    case False{}:
      h => Empty.absurd({b == True{}: Bool}, Shared.Bool.false_ne_true(h))

# an "or" with a true second side is true
def Case.or_right(a: Bool, -b: Bool) -> {b == True{}: Bool} -> {Bool.or(a, b) == True{}: Bool}:
  match a:
    case True{}:
      h => {==}
    case False{}:
      h => h

# a hit and a rest are true when each follows from h: one use of h gives both
def Case.all_one(
  -H: Type,
  hit: Bool,
  -rest: Unit -> Bool,
  h: H,
  fa: H -> {hit == True{}: Bool},
  fb: H -> {rest(Unit{}) == True{}: Bool}
) -> {List.all.if(rest, hit) == True{}: Bool}:
  match hit:
    case False{}:
      fa(h)
    case True{}:
      fb(h)

# Laws of the facts
# -----------------

# Coded.Fact.is_eq is the test of the keys of two facts
def Fact.agree(
  x: Types.Fact,
  y: Types.Fact
) -> {Coded.Fact.is_eq(x, y) == Crits.Key.is_eq(Coded.Fact.words(x), Coded.Fact.words(y)): Bool}:
  Equal.sym(
    Bool,
    Crits.Key.is_eq(Coded.Fact.words(x), Coded.Fact.words(y)),
    Coded.Fact.is_eq(x, y),
    Crits.Key.is_eq_list(Coded.Fact.words(x), Coded.Fact.words(y))
  )

# what a set with a fact holds: the fact, and what it held
def Facts.has_add(
  +s: Facts(),
  +y: Types.Fact,
  +x: Types.Fact
) -> {Facts.has(Facts.add(s, y), x) == Bool.or(Coded.Fact.is_eq(x, y), Facts.has(s, x)): Bool}:
  Sets.ValSet.has_add(~Types.Fact, ~Coded.Fact.is_eq, ~Coded.Fact.words, ~Fact.agree, s, y, x)

# a set holds the facts of its list
def Facts.has_list(
  +s: Facts(),
  +x: Types.Fact
) -> {Facts.has(s, x) == List.contains(~Types.Fact, ~Coded.Fact.is_eq, Facts.list(s), x): Bool}:
  Sets.ValSet.has_list(~Types.Fact, ~Coded.Fact.is_eq, ~Coded.Fact.words, ~Fact.agree, s, x)

# two sets that hold the same facts are one set
def Facts.ext(
  a: Facts(),
  b: Facts()
) -> (@f: Types.Fact -> {Facts.has(a, f) == Facts.has(b, f): Bool}) -> {a == b: Facts()}:
  Sets.ValSet.ext(
    ~Types.Fact,
    ~Coded.Fact.is_eq,
    ~Coded.Fact.words,
    ~Coded.Fact.laws(),
    ~Fact.agree,
    a,
    b
  )

# two sets that hold the same changes are one set
def Facts.same(
  a: Facts(),
  b: Facts()
) -> (@c: Types.Change -> {Facts.holds(a, c) == Facts.holds(b, c): Bool}) -> {a == b: Facts()}:
  h => Facts.ext(a, b)(f => h(Types.Change.Fact{f}))

# a set with a fact holds it
def Facts.add_has(+s: Facts(), +x: Types.Fact) -> {Facts.has(Facts.add(s, x), x) == True{}: Bool}:
  Sets.ValSet.add_has(~Types.Fact, ~Coded.Fact.is_eq, ~Coded.Fact.words, ~Fact.agree, s, x)

# a set with a fact holds each fact that it held
def Facts.add_keeps(
  +s: Facts(),
  +y: Types.Fact,
  +x: Types.Fact
) -> {Facts.has(s, x) == True{}: Bool} -> {Facts.has(Facts.add(s, y), x) == True{}: Bool}:
  Sets.ValSet.add_keeps(~Types.Fact, ~Coded.Fact.is_eq, ~Coded.Fact.words, ~Fact.agree, s, y, x)

# a set holds each member of its list
def Facts.in_has(
  +s: Facts(),
  +x: Types.Fact
) -> {
  List.contains(~Types.Fact, ~Coded.Fact.is_eq, Facts.list(s), x) == True{}: Bool
} -> {Facts.has(s, x) == True{}: Bool}:
  h => Equal.trans(
    Bool,
    Facts.has(s, x),
    List.contains(~Types.Fact, ~Coded.Fact.is_eq, Facts.list(s), x),
    True{},
    Facts.has_list(s, x),
    h
  )

# each fact that a set holds is a member of its list
def Facts.has_in(
  +s: Facts(),
  +x: Types.Fact
) -> {
  Facts.has(s, x) == True{}: Bool
} -> {List.contains(~Types.Fact, ~Coded.Fact.is_eq, Facts.list(s), x) == True{}: Bool}:
  h => Equal.trans(
    Bool,
    List.contains(~Types.Fact, ~Coded.Fact.is_eq, Facts.list(s), x),
    Facts.has(s, x),
    True{},
    Equal.sym(
      Bool,
      Facts.has(s, x),
      List.contains(~Types.Fact, ~Coded.Fact.is_eq, Facts.list(s), x),
      Facts.has_list(s, x)
    ),
    h
  )

# b holds each fact of xs when it holds each member of xs
def Facts.all_in(
  xs: List<&2, Types.Fact>,
  +b: Facts(),
  h: (
    @x: Types.Fact -> {
      List.contains(~Types.Fact, ~Coded.Fact.is_eq, xs, x) == True{}: Bool
    } -> {Facts.has(b, x) == True{}: Bool}
  )
) -> {
  Shared.List.holds(
    ~Types.Fact,
    ~RFacts.Plain(),
    ~RFacts.Fact.held,
    xs,
    Facts.crit(b)
  )
    == True{}: Bool
}:
  match xs:
    case Nil{}:
      {==}
    case Con{+y, +r}:
      Case.all_one(
        (
          @x: Types.Fact -> {
            List.contains(~Types.Fact, ~Coded.Fact.is_eq, y <> r, x) == True{}: Bool
          } -> {Facts.has(b, x) == True{}: Bool}
        ),
        Fact.held(b, y),
        u => Shared.List.holds(~Types.Fact, ~RFacts.Plain(), ~RFacts.Fact.held, r, Facts.crit(b)),
        h,
        g => g(
          y
        )(Lists.List.contains_head(~Types.Fact, ~Coded.Fact.is_eq, ~Coded.Fact.laws(), y, r)),
        g => Facts.all_in(
          r,
          b,
          +x => c => g(x)(Shared.List.contains_cons(~Types.Fact, ~Coded.Fact.is_eq, y, r, x)(c))
        )
      )

# a wider set holds each fact that the set holds
def Facts.wider_has(
  +a: Facts(),
  +b: Facts(),
  +f: Types.Fact
) -> {
  Facts.wider(a, b) == True{}: Bool
} -> {Facts.has(a, f) == True{}: Bool} -> {Facts.has(b, f) == True{}: Bool}:
  hw => hf => Lists.List.holds_in(
    ~Types.Fact,
    ~RFacts.Plain(),
    ~RFacts.Fact.held,
    ~Coded.Fact.is_eq,
    ~Coded.Fact.laws(),
    Facts.list(a),
    Facts.crit(b),
    f
  )(
    Shared.Bool.and_true_left(
      Shared.List.holds(
        ~Types.Fact,
        ~RFacts.Plain(),
        ~RFacts.Fact.held,
        Facts.list(a),
        Facts.crit(b)
      ),
      Nat.is_le(Facts.fuel(a), Facts.fuel(b))
    )(hw)
  )(Facts.has_in(a, f)(hf))

# a read of a wider set may go as far as one of the set
def Facts.wider_fuel(
  +a: Facts(),
  +b: Facts()
) -> {
  Facts.wider(a, b) == True{}: Bool
} -> {Nat.is_le(Facts.fuel(a), Facts.fuel(b)) == True{}: Bool}:
  hw => Shared.Bool.and_true_right(
    Shared.List.holds(
      ~Types.Fact,
      ~RFacts.Plain(),
      ~RFacts.Fact.held,
      Facts.list(a),
      Facts.crit(b)
    ),
    Nat.is_le(Facts.fuel(a), Facts.fuel(b))
  )(hw)

# a set is wider than itself
def Facts.wider_refl(+s: Facts()) -> {Facts.wider(s, s) == True{}: Bool}:
  Shared.Bool.and_both(
    Shared.List.holds(
      ~Types.Fact,
      ~RFacts.Plain(),
      ~RFacts.Fact.held,
      Facts.list(s),
      Facts.crit(s)
    ),
    Nat.is_le(Facts.fuel(s), Facts.fuel(s))
  )(
    Facts.all_in(Facts.list(s), s, x => c => Facts.in_has(s, x)(c))
  )(Shared.Nat.le_refl(Facts.fuel(s)))

# wider goes through
def Facts.wider_trans(
  +a: Facts(),
  +b: Facts(),
  +c: Facts()
) -> {
  Facts.wider(a, b) == True{}: Bool
} -> {Facts.wider(b, c) == True{}: Bool} -> {Facts.wider(a, c) == True{}: Bool}:
  +hab => +hbc => Shared.Bool.and_both(
    Shared.List.holds(
      ~Types.Fact,
      ~RFacts.Plain(),
      ~RFacts.Fact.held,
      Facts.list(a),
      Facts.crit(c)
    ),
    Nat.is_le(Facts.fuel(a), Facts.fuel(c))
  )(
    Facts.all_in(
      Facts.list(a),
      c,
      +x => i => Facts.wider_has(b, c, x)(hbc)(Facts.wider_has(a, b, x)(hab)(Facts.in_has(a, x)(i)))
    )
  )(
    Shared.Nat.le_trans(
      Facts.fuel(a),
      Facts.fuel(b),
      Facts.fuel(c)
    )(Facts.wider_fuel(a, b)(hab))(Facts.wider_fuel(b, c)(hbc))
  )

# a set with a fact is wider
def Facts.add_wider(
  +s: Facts(),
  +f: Types.Fact
) -> {Facts.wider(s, Facts.add(s, f)) == True{}: Bool}:
  Shared.Bool.and_both(
    Shared.List.holds(
      ~Types.Fact,
      ~RFacts.Plain(),
      ~RFacts.Fact.held,
      Facts.list(s),
      Facts.crit(Facts.add(s, f))
    ),
    Nat.is_le(Facts.fuel(s), Facts.fuel(Facts.add(s, f)))
  )(
    Facts.all_in(
      Facts.list(s),
      Facts.add(s, f),
      +x => c => Facts.add_keeps(s, f, x)(Facts.in_has(s, x)(c))
    )
  )(Sets.ValSet.size_add(~Types.Fact, ~Coded.Fact.words, s, f))

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof does not run
# a wider set holds each change that the set holds
def Facts.wider_holds(
  +a: Facts(),
  +b: Facts(),
  +c: Types.Change
) -> {
  Facts.wider(a, b) == True{}: Bool
} -> {Facts.holds(a, c) == True{}: Bool} -> {Facts.holds(b, c) == True{}: Bool}:
  match c:
    case Types.Change.Fact{f}:
      hw => hc => Facts.wider_has(a, b, f)(hw)(hc)
    case Types.Change.Lie{v, st, one, two}:
      +hw => +hc => Shared.Bool.and_both(
        Bool.and(
          Facts.has(b, Types.Fact.Vote{v, st, one}),
          Facts.has(b, Types.Fact.Vote{v, st, two})
        ),
        Bool.not(Coded.Cast.is_eq(one, two))
      )(
        Shared.Bool.and_both(
          Facts.has(b, Types.Fact.Vote{v, st, one}),
          Facts.has(b, Types.Fact.Vote{v, st, two})
        )(
          Facts.wider_has(
            a,
            b,
            Types.Fact.Vote{v, st, one}
          )(
            hw
          )(
            Shared.Bool.and_true_left(
              Facts.has(a, Types.Fact.Vote{v, st, one}),
              Facts.has(a, Types.Fact.Vote{v, st, two})
            )(
              Shared.Bool.and_true_left(
                Bool.and(
                  Facts.has(a, Types.Fact.Vote{v, st, one}),
                  Facts.has(a, Types.Fact.Vote{v, st, two})
                ),
                Bool.not(Coded.Cast.is_eq(one, two))
              )(hc)
            )
          )
        )(
          Facts.wider_has(
            a,
            b,
            Types.Fact.Vote{v, st, two}
          )(
            hw
          )(
            Shared.Bool.and_true_right(
              Facts.has(a, Types.Fact.Vote{v, st, one}),
              Facts.has(a, Types.Fact.Vote{v, st, two})
            )(
              Shared.Bool.and_true_left(
                Bool.and(
                  Facts.has(a, Types.Fact.Vote{v, st, one}),
                  Facts.has(a, Types.Fact.Vote{v, st, two})
                ),
                Bool.not(Coded.Cast.is_eq(one, two))
              )(hc)
            )
          )
        )
      )(
        Shared.Bool.and_true_right(
          Bool.and(
            Facts.has(a, Types.Fact.Vote{v, st, one}),
            Facts.has(a, Types.Fact.Vote{v, st, two})
          ),
          Bool.not(Coded.Cast.is_eq(one, two))
        )(hc)
      )

# a wider set lists each fact that the set lists
def Facts.wider_list(
  +a: Facts(),
  +b: Facts(),
  +f: Types.Fact
) -> {
  Facts.wider(a, b) == True{}: Bool
} -> {
  List.contains(~Types.Fact, ~Coded.Fact.is_eq, Facts.list(a), f) == True{}: Bool
} -> {List.contains(~Types.Fact, ~Coded.Fact.is_eq, Facts.list(b), f) == True{}: Bool}:
  hw => hc => Facts.has_in(b, f)(Facts.wider_has(a, b, f)(hw)(Facts.in_has(a, f)(hc)))

# Laws of the liars
# -----------------

# words are the same as themselves
def Words.is_eq_refl(x: List<&2, U32>) -> {RFacts.Words.is_eq(x, x) == True{}: Bool}:
  Shared.List.is_eq_refl(~U32, ~U32.is_eq, ~Shared.U32.laws(), x)

# only equal words are the same
def Words.is_eq_sound(
  x: List<&2, U32>,
  y: List<&2, U32>
) -> {RFacts.Words.is_eq(x, y) == True{}: Bool} -> {x == y: List<&2, U32>}:
  Shared.List.is_eq_sound(~U32, ~U32.is_eq, ~Shared.U32.laws(), x, y)

# words that are not the same are not equal
def Words.ne(
  +x: List<&2, U32>,
  +y: List<&2, U32>
) -> {Bool.not(RFacts.Words.is_eq(x, y)) == True{}: Bool} -> {x == y: List<&2, U32>} -> Empty:
  h => e => Lists.Bool.clash(
    Empty,
    RFacts.Words.is_eq(x, y),
    Shared.Bool.not_true(RFacts.Words.is_eq(x, y))(h),
    (
      %e: {RFacts.Words.is_eq(x, _) == True{}: Bool}
      Words.is_eq_refl(x))
  )

# words that are not equal are not the same
def Words.ne_not(
  +x: List<&2, U32>,
  +y: List<&2, U32>
) -> ({x == y: List<&2, U32>} -> Empty) -> {Bool.not(RFacts.Words.is_eq(x, y)) == True{}: Bool}:
  no => Case.not_of(
    RFacts.Words.is_eq(x, y)
  )(Case.false_of(RFacts.Words.is_eq(x, y))(t => no(Words.is_eq_sound(x, y)(t))))

# words that are not the same, the other way round
def Words.ne_sym(
  +x: List<&2, U32>,
  +y: List<&2, U32>
) -> {
  Bool.not(RFacts.Words.is_eq(x, y)) == True{}: Bool
} -> {Bool.not(RFacts.Words.is_eq(y, x)) == True{}: Bool}:
  h => Words.ne_not(y, x)(e => Words.ne(x, y)(h)(Equal.sym(List<&2, U32>, y, x, e)))

# a vote of the voter and the step of a ballot, for another choice,
# contradicts the ballot
def Fact.clashes_of(
  +v: String,
  +st: List<&2, U32>,
  +x: List<&2, U32>,
  +y: List<&2, U32>,
  +g: Types.Fact
) -> {
  RFacts.Fact.ballot(g) == Some{Spec.Ballot{v, st, y}}: Maybe<&2, Spec.Ballot>
} -> {
  Bool.not(RFacts.Words.is_eq(x, y)) == True{}: Bool
} -> {RFacts.Fact.clashes(Spec.Ballot{v, st, x}, g) == True{}: Bool}:
  e => hn =>
    %Equal.sym(
      Maybe<&2, Spec.Ballot>,
      RFacts.Fact.ballot(g),
      Some{Spec.Ballot{v, st, y}},
      e
    ): {RFacts.Fact.clashes.at(Spec.Ballot{v, st, x}, _) == True{}: Bool}
    Shared.Bool.and_both(
      String.eq(v, v),
      Bool.and(RFacts.Words.is_eq(st, st), Bool.not(RFacts.Words.is_eq(x, y)))
    )(
      Texts.String.eq_refl(v)
    )(
      Shared.Bool.and_both(
        RFacts.Words.is_eq(st, st),
        Bool.not(RFacts.Words.is_eq(x, y))
      )(Words.is_eq_refl(st))(hn)
    )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the fact g is a vote of the voter v for the step st, for a choice that is
# not x
def Fact.Clashed(v: String, st: List<&2, U32>, x: List<&2, U32>, g: Types.Fact) -> Type:
  Exists(
    List<&2, U32>,
    y => {
      RFacts.Fact.ballot(g) == Some{Spec.Ballot{v, st, y}}: Maybe<&2, Spec.Ballot>
    }
      & {Bool.not(RFacts.Words.is_eq(x, y)) == True{}: Bool}
  )

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof does not run
# a fact that contradicts a ballot is a vote of its voter and its step, for
# another choice
def Fact.clashes_are(
  +v: String,
  +st: List<&2, U32>,
  +x: List<&2, U32>,
  g: Types.Fact
) -> {RFacts.Fact.clashes(Spec.Ballot{v, st, x}, g) == True{}: Bool} -> Fact.Clashed(v, st, x, g):
  match g:
    case Types.Fact.Ask{a}:
      h => Empty.absurd(Fact.Clashed(v, st, x, Types.Fact.Ask{a}), Shared.Bool.false_ne_true(h))
    case Types.Fact.Vote{+u, +st2, +pk2}:
      +h => (Coded.Cast.words(pk2), ((
            %Texts.String.eq_sound(v, u)(Shared.Bool.and_true_left(String.eq(v, u), Bool.and(RFacts.Words.is_eq(st, Coded.Step.words(st2)), Bool.not(RFacts.Words.is_eq(x, Coded.Cast.words(pk2)))))(h)): {Some{Spec.Ballot{_, Coded.Step.words(st2), Coded.Cast.words(pk2)}} == Some{Spec.Ballot{v, st, Coded.Cast.words(pk2)}}: Maybe<&2, Spec.Ballot>}
            %Words.is_eq_sound(st, Coded.Step.words(st2))(Shared.Bool.and_second(String.eq(v, u), RFacts.Words.is_eq(st, Coded.Step.words(st2)), Bool.not(RFacts.Words.is_eq(x, Coded.Cast.words(pk2))))(h)): {Some{Spec.Ballot{v, _, Coded.Cast.words(pk2)}} == Some{Spec.Ballot{v, st, Coded.Cast.words(pk2)}}: Maybe<&2, Spec.Ballot>}
            {==}), Shared.Bool.and_third(String.eq(v, u), RFacts.Words.is_eq(st, Coded.Step.words(st2)), Bool.not(RFacts.Words.is_eq(x, Coded.Cast.words(pk2))))(h)))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the fact f is a vote of the voter v, and a member of all is a vote of v for
# the same step and another choice
def Fact.Lied(all: List<&2, Types.Fact>, v: String, f: Types.Fact) -> Type:
  Exists(
    Types.Fact,
    g => {
      List.contains(~Types.Fact, ~Coded.Fact.is_eq, all, g) == True{}: Bool
    }
      & Exists(
        List<&2, U32>,
        st => Exists(
          List<&2, U32>,
          x => Exists(
            List<&2, U32>,
            y => {
              RFacts.Fact.ballot(f) == Some{Spec.Ballot{v, st, x}}: Maybe<&2, Spec.Ballot>
            }
              & (
                {
                  RFacts.Fact.ballot(g) == Some{Spec.Ballot{v, st, y}}: Maybe<&2, Spec.Ballot>
                }
                  & {Bool.not(RFacts.Words.is_eq(x, y)) == True{}: Bool}
              )
          )
        )
      )
  )

# Fact.liar_of.at, with what the member g of all is
def Fact.liar_of.fin(
  +all: List<&2, Types.Fact>,
  +w: String,
  +st: Types.Step,
  +pk: Types.Cast,
  +v: String,
  +g: Types.Fact,
  e: {w == v: String},
  hin: {List.contains(~Types.Fact, ~Coded.Fact.is_eq, all, g) == True{}: Bool},
  cl: Fact.Clashed(w, Coded.Step.words(st), Coded.Cast.words(pk), g)
) -> Fact.Lied(all, v, Types.Fact.Vote{w, st, pk}):
  (+y, q) = cl
  (+eb, +hn) = q
  %e: Fact.Lied(all, _, Types.Fact.Vote{w, st, pk})
  (g, (hin, (Coded.Step.words(st), (Coded.Cast.words(pk), (y, ({==}, (eb, hn)))))))

# Fact.liar_of for a vote of w, with the member of all that contradicts it
def Fact.liar_of.at(
  +all: List<&2, Types.Fact>,
  +w: String,
  +st: Types.Step,
  +pk: Types.Cast,
  +v: String,
  e: {w == v: String},
  r: Exists(
    Types.Fact,
    g => {
      List.contains(~Types.Fact, ~Coded.Fact.is_eq, all, g) == True{}: Bool
    }
      & {
        RFacts.Fact.clashes(
          Spec.Ballot{w, Coded.Step.words(st), Coded.Cast.words(pk)},
          g
        )
          == True{}: Bool
      }
  )
) -> Fact.Lied(all, v, Types.Fact.Vote{w, st, pk}):
  (+g, p) = r
  (+hin, +hc) = p
  Fact.liar_of.fin(
    all,
    w,
    st,
    pk,
    v,
    g,
    e,
    hin,
    Fact.clashes_are(w, Coded.Step.words(st), Coded.Cast.words(pk), g)(hc)
  )

# a fact whose voter is named a liar by all is a vote that a member of all
# contradicts
def Fact.liar_of(
  +all: List<&2, Types.Fact>,
  f: Types.Fact,
  +v: String
) -> {RFacts.Fact.liar(all, f) == Some{v}: Maybe<&2, String>} -> Fact.Lied(all, v, f):
  match f:
    case Types.Fact.Ask{a}:
      h => Empty.absurd(
        Fact.Lied(all, v, Types.Fact.Ask{a}),
        Shared.Maybe.none_ne_some(String, v, h)
      )
    case Types.Fact.Vote{+w, +st, +pk}:
      Lists.Bool.by(
        c => {
          Shared.Maybe.when(String, c, u => Some{w}) == Some{v}: Maybe<&2, String>
        } -> Fact.Lied(all, v, Types.Fact.Vote{w, st, pk}),
        Shared.List.some(
          ~Types.Fact,
          ~Spec.Ballot,
          ~RFacts.Fact.clashes,
          all,
          Spec.Ballot{w, Coded.Step.words(st), Coded.Cast.words(pk)}
        ),
        et => h => Fact.liar_of.at(
          all,
          w,
          st,
          pk,
          v,
          Shared.Maybe.some_inj(String, w, v, h),
          Lists.List.some_in(
            ~Types.Fact,
            ~Spec.Ballot,
            ~RFacts.Fact.clashes,
            ~Coded.Fact.is_eq,
            ~Coded.Fact.laws(),
            all,
            Spec.Ballot{w, Coded.Step.words(st), Coded.Cast.words(pk)}
          )(et)
        ),
        ef => h => Empty.absurd(
          Fact.Lied(all, v, Types.Fact.Vote{w, st, pk}),
          Shared.Maybe.none_ne_some(String, v, h)
        )
      )

# all names the voter of a vote a liar when a member of all is a vote of the
# voter for the same step and another choice
def Fact.liar_in(
  +all: List<&2, Types.Fact>,
  +f: Types.Fact,
  +g: Types.Fact,
  +v: String,
  +st: List<&2, U32>,
  +x: List<&2, U32>,
  +y: List<&2, U32>
) -> {
  List.contains(~Types.Fact, ~Coded.Fact.is_eq, all, g) == True{}: Bool
} -> {
  RFacts.Fact.ballot(f) == Some{Spec.Ballot{v, st, x}}: Maybe<&2, Spec.Ballot>
} -> {
  RFacts.Fact.ballot(g) == Some{Spec.Ballot{v, st, y}}: Maybe<&2, Spec.Ballot>
} -> {
  Bool.not(RFacts.Words.is_eq(x, y)) == True{}: Bool
} -> {RFacts.Fact.liar(all, f) == Some{v}: Maybe<&2, String>}:
  hin => ef => eg => hn =>
    %Equal.sym(
      Maybe<&2, Spec.Ballot>,
      RFacts.Fact.ballot(f),
      Some{Spec.Ballot{v, st, x}},
      ef
    ): {RFacts.Fact.liar.at(all, _) == Some{v}: Maybe<&2, String>}
    %Equal.sym(
      Bool,
      Shared.List.some(~Types.Fact, ~Spec.Ballot, ~RFacts.Fact.clashes, all, Spec.Ballot{v, st, x}),
      True{},
      Lists.List.in_some(
        ~Types.Fact,
        ~Spec.Ballot,
        ~RFacts.Fact.clashes,
        ~Coded.Fact.is_eq,
        ~Coded.Fact.laws(),
        all,
        Spec.Ballot{v, st, x},
        g
      )(hin)(Fact.clashes_of(v, st, x, y, g)(eg)(hn))
    ): {Shared.Maybe.when(String, _, u => Some{v}) == Some{v}: Maybe<&2, String>}
    {==}

# the liars of fs hold the voter that all names a liar for a member of fs
def Facts.liars.go_in(
  +all: List<&2, Types.Fact>,
  fs: List<&2, Types.Fact>,
  +f: Types.Fact,
  +v: String
) -> {
  List.contains(~Types.Fact, ~Coded.Fact.is_eq, fs, f) == True{}: Bool
} -> {
  RFacts.Fact.liar(all, f) == Some{v}: Maybe<&2, String>
} -> {List.contains(~String, ~String.eq, RFacts.Facts.liars.go(all, fs), v) == True{}: Bool}:
  match fs:
    case Nil{}:
      hin => e => Empty.absurd({False{} == True{}: Bool}, Shared.Bool.false_ne_true(hin))
    case Con{+h, +t}:
      hin => +e => Lists.List.contains_cons_by(
        ~Types.Fact,
        ~Coded.Fact.is_eq,
        ~Coded.Fact.laws(),
        {
          List.contains(
            ~String,
            ~String.eq,
            Shared.Maybe.cons(String, RFacts.Fact.liar(all, h), RFacts.Facts.liars.go(all, t)),
            v
          )
            == True{}: Bool
        },
        h,
        t,
        f,
        hin,
        exh => (
          %Equal.sym(Maybe<&2, String>, RFacts.Fact.liar(all, h), Some{v}, Equal.trans(Maybe<&2, String>, RFacts.Fact.liar(all, h), RFacts.Fact.liar(all, f), Some{v}, Equal.cong(Types.Fact, Maybe<&2, String>, z => RFacts.Fact.liar(all, z), h, f, exh), e)): {List.contains(~String, ~String.eq, Shared.Maybe.cons(String, _, RFacts.Facts.liars.go(all, t)), v) == True{}: Bool}
          Lists.List.contains_head(~String, ~String.eq, ~Texts.String.laws(), v, RFacts.Facts.liars.go(all, t))),
        c => Lists.List.contains_maybe_cons(
          ~String,
          ~String.eq,
          RFacts.Fact.liar(all, h),
          RFacts.Facts.liars.go(all, t),
          v
        )(Facts.liars.go_in(all, t, f, v)(c)(e))
      )

# each liar of fs is the voter that all names a liar for a member of fs
def Facts.liars.go_of(
  +all: List<&2, Types.Fact>,
  fs: List<&2, Types.Fact>,
  +v: String
) -> {
  List.contains(~String, ~String.eq, RFacts.Facts.liars.go(all, fs), v) == True{}: Bool
} -> Exists(
  Types.Fact,
  f => {
    List.contains(~Types.Fact, ~Coded.Fact.is_eq, fs, f) == True{}: Bool
  }
    & {RFacts.Fact.liar(all, f) == Some{v}: Maybe<&2, String>}
):
  match fs:
    case Nil{}:
      hin => Empty.absurd(
        Exists(
          Types.Fact,
          f => {
            List.contains(~Types.Fact, ~Coded.Fact.is_eq, [], f) == True{}: Bool
          }
            & {RFacts.Fact.liar(all, f) == Some{v}: Maybe<&2, String>}
        ),
        Shared.Bool.false_ne_true(hin)
      )
    case Con{+h, +t}:
      Lists.Maybe.by(
        String,
        m => {
          List.contains(
            ~String,
            ~String.eq,
            Shared.Maybe.cons(String, m, RFacts.Facts.liars.go(all, t)),
            v
          )
            == True{}: Bool
        } -> Exists(
          Types.Fact,
          f => {
            List.contains(~Types.Fact, ~Coded.Fact.is_eq, h <> t, f) == True{}: Bool
          }
            & {RFacts.Fact.liar(all, f) == Some{v}: Maybe<&2, String>}
        ),
        RFacts.Fact.liar(all, h),
        en => c => Lists.List.exists_cons(
          ~Types.Fact,
          ~Coded.Fact.is_eq,
          f => {RFacts.Fact.liar(all, f) == Some{v}: Maybe<&2, String>},
          h,
          t,
          Facts.liars.go_of(all, t, v)(c)
        ),
        +z => +ez => Lists.Bool.by(
          s => {
            List.any.if(
              u => List.contains(~String, ~String.eq, RFacts.Facts.liars.go(all, t), v),
              s
            )
              == True{}: Bool
          } -> Exists(
            Types.Fact,
            f => {
              List.contains(~Types.Fact, ~Coded.Fact.is_eq, h <> t, f) == True{}: Bool
            }
              & {RFacts.Fact.liar(all, f) == Some{v}: Maybe<&2, String>}
          ),
          String.eq(z, v),
          es => c => (
            h,
            (Lists.List.contains_head(~Types.Fact, ~Coded.Fact.is_eq, ~Coded.Fact.laws(), h, t), (
                %Texts.String.eq_sound(z, v)(es): {RFacts.Fact.liar(all, h) == Some{_}: Maybe<&2, String>}
                ez))
          ),
          es => c => Lists.List.exists_cons(
            ~Types.Fact,
            ~Coded.Fact.is_eq,
            f => {RFacts.Fact.liar(all, f) == Some{v}: Maybe<&2, String>},
            h,
            t,
            Facts.liars.go_of(all, t, v)(c)
          )
        )
      )

# a set that holds two votes of one voter for one step with two choices names
# the voter a liar
def Facts.liars_in(
  +s: Facts(),
  +f: Types.Fact,
  +g: Types.Fact,
  +v: String,
  +st: List<&2, U32>,
  +x: List<&2, U32>,
  +y: List<&2, U32>
) -> {
  Facts.has(s, f) == True{}: Bool
} -> {
  Facts.has(s, g) == True{}: Bool
} -> {
  RFacts.Fact.ballot(f) == Some{Spec.Ballot{v, st, x}}: Maybe<&2, Spec.Ballot>
} -> {
  RFacts.Fact.ballot(g) == Some{Spec.Ballot{v, st, y}}: Maybe<&2, Spec.Ballot>
} -> {
  Bool.not(RFacts.Words.is_eq(x, y)) == True{}: Bool
} -> {List.contains(~String, ~String.eq, Facts.liars(s), v) == True{}: Bool}:
  hf => hg => ef => eg => hn => Facts.liars.go_in(
    Facts.list(s),
    Facts.list(s),
    f,
    v
  )(
    Facts.has_in(s, f)(hf)
  )(Fact.liar_in(Facts.list(s), f, g, v, st, x, y)(Facts.has_in(s, g)(hg))(ef)(eg)(hn))

# the set s holds two votes of the voter v for one step with two choices
def Facts.Liar(s: Facts(), v: String) -> Type:
  Exists(
    Types.Fact,
    f => Exists(
      Types.Fact,
      g => {
        Facts.has(s, f) == True{}: Bool
      }
        & (
          {
            Facts.has(s, g) == True{}: Bool
          }
            & Exists(
              List<&2, U32>,
              st => Exists(
                List<&2, U32>,
                x => Exists(
                  List<&2, U32>,
                  y => {
                    RFacts.Fact.ballot(f) == Some{Spec.Ballot{v, st, x}}: Maybe<&2, Spec.Ballot>
                  }
                    & (
                      {
                        RFacts.Fact.ballot(g) == Some{Spec.Ballot{v, st, y}}: Maybe<&2, Spec.Ballot>
                      }
                        & {Bool.not(RFacts.Words.is_eq(x, y)) == True{}: Bool}
                    )
                )
              )
            )
        )
    )
  )

# Facts.liars_of, with the vote f and what contradicts it
def Facts.liars_of.fin(
  +s: Facts(),
  +v: String,
  +f: Types.Fact,
  cf: {List.contains(~Types.Fact, ~Coded.Fact.is_eq, Facts.list(s), f) == True{}: Bool},
  r: Fact.Lied(Facts.list(s), v, f)
) -> Facts.Liar(s, v):
  (+g, q) = r
  (+cg, r0) = q
  (+st, r1) = r0
  (+x, r2) = r1
  (+y, r3) = r2
  (+ef, r4) = r3
  (+eg, hn) = r4
  (f, (g, (Facts.in_has(s, f)(cf), (Facts.in_has(s, g)(cg), (st, (x, (y, (ef, (eg, hn)))))))))

# Facts.liars_of, with the member of the list that names the liar
def Facts.liars_of.at(
  +s: Facts(),
  +v: String,
  r: Exists(
    Types.Fact,
    f => {
      List.contains(~Types.Fact, ~Coded.Fact.is_eq, Facts.list(s), f) == True{}: Bool
    }
      & {RFacts.Fact.liar(Facts.list(s), f) == Some{v}: Maybe<&2, String>}
  )
) -> Facts.Liar(s, v):
  (+f, p) = r
  (+cf, +el) = p
  Facts.liars_of.fin(s, v, f, cf, Fact.liar_of(Facts.list(s), f, v)(el))

# a set names a voter a liar only when it holds two votes of the voter for
# one step with two choices
def Facts.liars_of(
  +s: Facts(),
  +v: String
) -> {List.contains(~String, ~String.eq, Facts.liars(s), v) == True{}: Bool} -> Facts.Liar(s, v):
  hin => Facts.liars_of.at(s, v, Facts.liars.go_of(Facts.list(s), Facts.list(s), v)(hin))

# a set that holds two ballots of one voter for one step with two choices names
# the voter a liar
def Facts.liars_found(
  +s: Facts(),
  +a: Types.Change,
  +b: Types.Change,
  +v: String,
  +st: List<&2, U32>,
  +x: List<&2, U32>,
  +y: List<&2, U32>
) -> {
  Facts.holds(s, a) == True{}: Bool
} -> {
  Facts.holds(s, b) == True{}: Bool
} -> {
  RFacts.Change.ballot(a) == Some{Spec.Ballot{v, st, x}}: Maybe<&2, Spec.Ballot>
} -> {
  RFacts.Change.ballot(b) == Some{Spec.Ballot{v, st, y}}: Maybe<&2, Spec.Ballot>
} -> (
  {x == y: List<&2, U32>} -> Empty
) -> {List.contains(~String, ~String.eq, Facts.liars(s), v) == True{}: Bool}:
  match a b:
    case Types.Change.Fact{f} Types.Change.Fact{g}:
      ha => hb => ea => eb => ne => Facts.liars_in(
        s,
        f,
        g,
        v,
        st,
        x,
        y
      )(ha)(hb)(ea)(eb)(Words.ne_not(x, y)(ne))
    case Types.Change.Fact{f} Types.Change.Lie{w, t, one, two}:
      ha => hb => ea => eb => ne => Empty.absurd(
        {List.contains(~String, ~String.eq, Facts.liars(s), v) == True{}: Bool},
        Shared.Maybe.none_ne_some(Spec.Ballot, Spec.Ballot{v, st, y}, eb)
      )
    case Types.Change.Lie{w, t, one, two} c:
      ha => hb => ea => eb => ne => Empty.absurd(
        {List.contains(~String, ~String.eq, Facts.liars(s), v) == True{}: Bool},
        Shared.Maybe.none_ne_some(Spec.Ballot, Spec.Ballot{v, st, x}, ea)
      )

# the set s holds two ballots of the voter v for one step with two choices
def Facts.Lies(s: Facts(), v: String) -> Type:
  Exists(
    Types.Change,
    a => Exists(
      Types.Change,
      b => {
        Facts.holds(s, a) == True{}: Bool
      }
        & (
          {
            Facts.holds(s, b) == True{}: Bool
          }
            & Exists(
              List<&2, U32>,
              st => Exists(
                List<&2, U32>,
                x => Exists(
                  List<&2, U32>,
                  y => {
                    RFacts.Change.ballot(a) == Some{Spec.Ballot{v, st, x}}: Maybe<&2, Spec.Ballot>
                  }
                    & (
                      {
                        RFacts.Change.ballot(
                          b
                        )
                          == Some{Spec.Ballot{v, st, y}}: Maybe<&2, Spec.Ballot>
                      }
                        & ({x == y: List<&2, U32>} -> Empty)
                    )
                )
              )
            )
        )
    )
  )

# Facts.liars_are, with the two votes
def Facts.liars_are.at(+s: Facts(), +v: String, r: Facts.Liar(s, v)) -> Facts.Lies(s, v):
  (+f, p) = r
  (+g, p1) = p
  (+hf, p2) = p1
  (+hg, p3) = p2
  (+st, p4) = p3
  (+x, p5) = p4
  (+y, p6) = p5
  (+ef, p7) = p6
  (+eg, hn) = p7
  (
    Types.Change.Fact{f},
    (Types.Change.Fact{g}, (hf, (hg, (st, (x, (y, (ef, (eg, Words.ne(x, y)(hn)))))))))
  )

# a set names a voter a liar only when it holds two ballots of the voter for
# one step with two choices
def Facts.liars_are(
  +s: Facts(),
  +v: String
) -> {
  List.contains(~String, ~String.eq, Facts.liars(s), v) == True{}: Bool
} -> Exists(
  Types.Change,
  a => Exists(
    Types.Change,
    b => {
      Facts.holds(s, a) == True{}: Bool
    }
      & (
        {
          Facts.holds(s, b) == True{}: Bool
        }
          & Exists(
            List<&2, U32>,
            st => Exists(
              List<&2, U32>,
              x => Exists(
                List<&2, U32>,
                y => {
                  RFacts.Change.ballot(a) == Some{Spec.Ballot{v, st, x}}: Maybe<&2, Spec.Ballot>
                }
                  & (
                    {
                      RFacts.Change.ballot(b) == Some{Spec.Ballot{v, st, y}}: Maybe<&2, Spec.Ballot>
                    }
                      & ({x == y: List<&2, U32>} -> Empty)
                  )
              )
            )
          )
      )
  )
):
  hin => Facts.liars_are.at(s, v, Facts.liars_of(s, v)(hin))

# in a set that names no liar, a voter has one pick for a step
def Facts.honest_one(
  +s: Facts(),
  +v: String,
  +st: Types.Step,
  +p: Types.Cast,
  +q: Types.Cast
) -> {
  Facts.liars(s) == []: List<&2, String>
} -> {
  Facts.has(s, Types.Fact.Vote{v, st, p}) == True{}: Bool
} -> {Facts.has(s, Types.Fact.Vote{v, st, q}) == True{}: Bool} -> {p == q: Types.Cast}:
  hn => hp => hq => Coded.Cast.words_inj(
    p,
    q
  )(
    Words.is_eq_sound(
      Coded.Cast.words(p),
      Coded.Cast.words(q)
    )(
      Case.true_of(
        RFacts.Words.is_eq(Coded.Cast.words(p), Coded.Cast.words(q))
      )(
        ef => Lists.List.in_not_nil(
          ~String,
          ~String.eq,
          Facts.liars(s),
          v
        )(
          Facts.liars_in(
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
          )({==})(Case.not_of(RFacts.Words.is_eq(Coded.Cast.words(p), Coded.Cast.words(q)))(ef))
        )(hn)
      )
    )
  )

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof does not run
# a set that is sound for a node does not name the node a liar
def Facts.ok_never(
  +name: String,
  +s: Facts()
) -> {
  Facts.ok(name, s) == True{}: Bool
} -> {List.contains(~String, ~String.eq, Facts.liars(s), name) == False{}: Bool}:
  h => Shared.Bool.not_true(
    List.contains(~String, ~String.eq, Facts.liars(s), name)
  )(
    Shared.Bool.and_true_left(
      Bool.not(List.contains(~String, ~String.eq, Facts.liars(s), name)),
      Bool.or(Bool.not(Facts.collide(s)), Trust.broken(s, name))
    )(h)
  )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the empty set is sound for every node
def Facts.new_ok(+name: String) -> {Facts.ok(name, Facts.new()) == True{}: Bool}:
  {==}

# Laws of the numbers
# -------------------

# the number of the ask of the fact f: of the ask, or of the pick of the vote
def Fact.seq(f: Types.Fact) -> Nat:
  match f:
    case Types.Fact.Ask{a}:
      RFacts.Ask.seq(a)
    case Types.Fact.Vote{v, st, Types.Cast.Vote{r, Types.Pick{a, pins}, b}}:
      RFacts.Ask.seq(a)
    case Types.Fact.Vote{v, st, Types.Cast.Pass{r}}:
      0n

# Seq.peak_ge for a list h <> t, where m is the greatest number of t
def Seq.peak_ge.at(
  +h: Types.Fact,
  +t: List<&2, Types.Fact>,
  +f: Types.Fact,
  +m: Nat,
  hin: {List.contains(~Types.Fact, ~Coded.Fact.is_eq, h <> t, f) == True{}: Bool},
  rec: {
    List.contains(~Types.Fact, ~Coded.Fact.is_eq, t, f) == True{}: Bool
  } -> {Nat.is_le(Fact.seq(f), m) == True{}: Bool}
) -> {Nat.is_le(Fact.seq(f), Nat.max(Fact.seq(h), m)) == True{}: Bool}:
  Lists.List.contains_cons_by(
    ~Types.Fact,
    ~Coded.Fact.is_eq,
    ~Coded.Fact.laws(),
    {Nat.is_le(Fact.seq(f), Nat.max(Fact.seq(h), m)) == True{}: Bool},
    h,
    t,
    f,
    hin,
    e => (
      %e: {Nat.is_le(Fact.seq(_), Nat.max(Fact.seq(h), m)) == True{}: Bool}
      Lists.Nat.le_max_left(Fact.seq(h), m)),
    c => Shared.Nat.le_trans(
      Fact.seq(f),
      m,
      Nat.max(Fact.seq(h), m)
    )(rec(c))(Lists.Nat.le_max_right(Fact.seq(h), m))
  )

# the number of a member of fs is at most the greatest number of fs
def Seq.peak_ge(
  fs: List<&2, Types.Fact>,
  +f: Types.Fact
) -> {
  List.contains(~Types.Fact, ~Coded.Fact.is_eq, fs, f) == True{}: Bool
} -> {Nat.is_le(Fact.seq(f), RFacts.Seq.peak(fs)) == True{}: Bool}:
  match fs:
    case Nil{}:
      hin => Empty.absurd(
        {Nat.is_le(Fact.seq(f), 0n) == True{}: Bool},
        Shared.Bool.false_ne_true(hin)
      )
    case Con{Types.Fact.Ask{+a}, +rest}:
      hin => Seq.peak_ge.at(
        Types.Fact.Ask{a},
        rest,
        f,
        RFacts.Seq.peak(rest),
        hin,
        Seq.peak_ge(rest, f)
      )
    case Con{Types.Fact.Vote{+v, +st, Types.Cast.Vote{+r, Types.Pick{+a, +pins}, +b}}, +rest}:
      hin => Seq.peak_ge.at(
        Types.Fact.Vote{v, st, Types.Cast.Vote{r, Types.Pick{a, pins}, b}},
        rest,
        f,
        RFacts.Seq.peak(rest),
        hin,
        Seq.peak_ge(rest, f)
      )
    case Con{Types.Fact.Vote{+v, +st, Types.Cast.Pass{+r}}, +rest}:
      hin => Seq.peak_ge.at(
        Types.Fact.Vote{v, st, Types.Cast.Pass{r}},
        rest,
        f,
        RFacts.Seq.peak(rest),
        hin,
        Seq.peak_ge(rest, f)
      )

# the number of each ask that a set holds, as an ask or in a vote, is at most
# the greatest number of the set
def Facts.seq_ask(
  +s: Facts(),
  +a: Types.Ask
) -> {
  Facts.has(s, Types.Fact.Ask{a}) == True{}: Bool
} -> {Nat.is_le(RFacts.Ask.seq(a), RFacts.Seq.peak(Facts.list(s))) == True{}: Bool}:
  h => Seq.peak_ge(Facts.list(s), Types.Fact.Ask{a})(Facts.has_in(s, Types.Fact.Ask{a})(h))

# the number of the ask of each vote that a set holds is at most the greatest
# number of the set
def Facts.seq_vote(
  +s: Facts(),
  +v: String,
  +st: Types.Step,
  +r: Nat,
  +a: Types.Ask,
  +pins: Types.Pins,
  +b: List<&2, Types.Ref>
) -> {
  Facts.has(s, Types.Fact.Vote{v, st, Types.Cast.Vote{r, Types.Pick{a, pins}, b}}) == True{}: Bool
} -> {Nat.is_le(RFacts.Ask.seq(a), RFacts.Seq.peak(Facts.list(s))) == True{}: Bool}:
  h => Seq.peak_ge(
    Facts.list(s),
    Types.Fact.Vote{v, st, Types.Cast.Vote{r, Types.Pick{a, pins}, b}}
  )(Facts.has_in(s, Types.Fact.Vote{v, st, Types.Cast.Vote{r, Types.Pick{a, pins}, b}})(h))

# Laws of taking in
# -----------------

# what holds of each set that Facts.take may give, given the tests that lead
# to it, holds of the set that it gives
def Facts.take_by(
  -P: Facts() -> Type,
  +name: String,
  +s: Facts(),
  +f: Types.Fact,
  pr: {Facts.refuses(name, s, f) == True{}: Bool} -> P(Trust.break(s, name)),
  pc: {
    Facts.refuses(name, s, f) == False{}: Bool
  } -> {
    RFacts.Fact.collided(Facts.list(s), f) == True{}: Bool
  } -> P(Trust.break(Facts.add(s, f), name)),
  pa: {
    Facts.refuses(name, s, f) == False{}: Bool
  } -> {RFacts.Fact.collided(Facts.list(s), f) == False{}: Bool} -> P(Facts.add(s, f))
) -> P(Facts.take(name, s, f)):
  Shared.Bool.when_cases(
    Facts(),
    P,
    Facts.refuses(name, s, f),
    u => Trust.break(s, name),
    u => Shared.Bool.when(
      Facts(),
      RFacts.Fact.collided(Facts.list(s), f),
      u => Trust.break(Facts.add(s, f), name),
      u => Facts.add(s, f)
    ),
    pr,
    +er => Shared.Bool.when_cases(
      Facts(),
      P,
      RFacts.Fact.collided(Facts.list(s), f),
      u => Trust.break(Facts.add(s, f), name),
      u => Facts.add(s, f),
      ec => pc(er)(ec),
      ec => pa(er)(ec)
    )
  )

# facts that are not equal are not the same
def Fact.differ(
  +x: Types.Fact,
  +y: Types.Fact
) -> ({x == y: Types.Fact} -> Empty) -> {Coded.Fact.is_eq(x, y) == False{}: Bool}:
  no => Case.false_of(Coded.Fact.is_eq(x, y))(t => no(Coded.Fact.is_eq_sound(x, y)(t)))

# the fact f is a vote for a slot
def Fact.is_slot(f: Types.Fact) -> Bool:
  match f:
    case Types.Fact.Ask{a}:
      False{}
    case Types.Fact.Vote{v, Types.Step.At{c, k, t}, pk}:
      True{}
    case Types.Fact.Vote{v, Types.Step.Broken{}, pk}:
      False{}

# the fact f is an ask
def Fact.is_ask(f: Types.Fact) -> Bool:
  match f:
    case Types.Fact.Ask{a}:
      True{}
    case Types.Fact.Vote{v, st, pk}:
      False{}

# a vote for a slot is not a fact that is not one
def Fact.slot_differs(
  +x: Types.Fact,
  +y: Types.Fact
) -> {
  Fact.is_slot(x) == True{}: Bool
} -> {Fact.is_slot(y) == False{}: Bool} -> {Coded.Fact.is_eq(x, y) == False{}: Bool}:
  hx => hy => Fact.differ(
    x,
    y
  )(
    e => Shared.Bool.true_ne_false(
      Equal.trans(
        Bool,
        True{},
        Fact.is_slot(y),
        False{},
        Equal.trans(
          Bool,
          True{},
          Fact.is_slot(x),
          Fact.is_slot(y),
          Equal.sym(Bool, Fact.is_slot(x), True{}, hx),
          Equal.cong(Types.Fact, Bool, z => Fact.is_slot(z), x, y, e)
        ),
        hy
      )
    )
  )

# an ask is not a fact that is not one
def Fact.ask_differs(
  +x: Types.Fact,
  +y: Types.Fact
) -> {
  Fact.is_ask(x) == True{}: Bool
} -> {Fact.is_ask(y) == False{}: Bool} -> {Coded.Fact.is_eq(x, y) == False{}: Bool}:
  hx => hy => Fact.differ(
    x,
    y
  )(
    e => Shared.Bool.true_ne_false(
      Equal.trans(
        Bool,
        True{},
        Fact.is_ask(y),
        False{},
        Equal.trans(
          Bool,
          True{},
          Fact.is_ask(x),
          Fact.is_ask(y),
          Equal.sym(Bool, Fact.is_ask(x), True{}, hx),
          Equal.cong(Types.Fact, Bool, z => Fact.is_ask(z), x, y, e)
        ),
        hy
      )
    )
  )

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof does not run
# a set with another fact holds x exactly when the set did
def Facts.add_same(
  +s: Facts(),
  +y: Types.Fact,
  +x: Types.Fact
) -> {
  Coded.Fact.is_eq(x, y) == False{}: Bool
} -> {Facts.has(Facts.add(s, y), x) == Facts.has(s, x): Bool}:
  h => Equal.trans(
    Bool,
    Facts.has(Facts.add(s, y), x),
    Bool.or(Coded.Fact.is_eq(x, y), Facts.has(s, x)),
    Facts.has(s, x),
    Facts.has_add(s, y, x),
    (
      %Equal.sym(Bool, Coded.Fact.is_eq(x, y), False{}, h): {Bool.or(_, Facts.has(s, x)) == Facts.has(s, x): Bool}
      {==})
  )

# a set whose trust broke holds a fact that is neither of the two votes
# exactly when the set did
def Trust.break_same(
  +s: Facts(),
  +name: String,
  +x: Types.Fact
) -> {
  Coded.Fact.is_eq(x, RFacts.Trust.one(name)) == False{}: Bool
} -> {
  Coded.Fact.is_eq(x, RFacts.Trust.two(name)) == False{}: Bool
} -> {Facts.has(Trust.break(s, name), x) == Facts.has(s, x): Bool}:
  h1 => h2 => Equal.trans(
    Bool,
    Facts.has(Trust.break(s, name), x),
    Facts.has(Facts.add(s, RFacts.Trust.one(name)), x),
    Facts.has(s, x),
    Facts.add_same(Facts.add(s, RFacts.Trust.one(name)), RFacts.Trust.two(name), x)(h2),
    Facts.add_same(s, RFacts.Trust.one(name), x)(h1)
  )

# a set whose trust broke holds each fact that the set held
def Trust.break_keeps(
  +s: Facts(),
  +name: String,
  +x: Types.Fact
) -> {Facts.has(s, x) == True{}: Bool} -> {Facts.has(Trust.break(s, name), x) == True{}: Bool}:
  h => Facts.add_keeps(
    Facts.add(s, RFacts.Trust.one(name)),
    RFacts.Trust.two(name),
    x
  )(Facts.add_keeps(s, RFacts.Trust.one(name), x)(h))

# a set whose trust broke is wider
def Trust.break_wider(
  +s: Facts(),
  +name: String
) -> {Facts.wider(s, Trust.break(s, name)) == True{}: Bool}:
  Facts.wider_trans(
    s,
    Facts.add(s, RFacts.Trust.one(name)),
    Facts.add(Facts.add(s, RFacts.Trust.one(name)), RFacts.Trust.two(name))
  )(
    Facts.add_wider(s, RFacts.Trust.one(name))
  )(Facts.add_wider(Facts.add(s, RFacts.Trust.one(name)), RFacts.Trust.two(name)))

# a set that takes an ask in holds it
def Facts.take_ask_has(
  +name: String,
  +s: Facts(),
  +a: Types.Ask
) -> {Facts.has(Facts.take(name, s, Types.Fact.Ask{a}), Types.Fact.Ask{a}) == True{}: Bool}:
  Facts.take_by(
    t => {Facts.has(t, Types.Fact.Ask{a}) == True{}: Bool},
    name,
    s,
    Types.Fact.Ask{a},
    er => Empty.absurd(
      {Facts.has(Trust.break(s, name), Types.Fact.Ask{a}) == True{}: Bool},
      Shared.Bool.false_ne_true(er)
    ),
    er => ec => Trust.break_keeps(
      Facts.add(s, Types.Fact.Ask{a}),
      name,
      Types.Fact.Ask{a}
    )(Facts.add_has(s, Types.Fact.Ask{a})),
    er => ec => Facts.add_has(s, Types.Fact.Ask{a})
  )

# a set that takes an ask in holds the votes for slots that it held
def Facts.take_ask_votes(
  +name: String,
  +s: Facts(),
  +a: Types.Ask,
  +v: String,
  +c: Ledgers.Line,
  +k: Nat,
  +n: Nat,
  +pk: Types.Cast
) -> {
  Facts.has(
    Facts.take(name, s, Types.Fact.Ask{a}),
    Types.Fact.Vote{v, Types.Step.At{c, k, n}, pk}
  )
    == Facts.has(s, Types.Fact.Vote{v, Types.Step.At{c, k, n}, pk}): Bool
}:
  Facts.take_by(
    t => {
      Facts.has(
        t,
        Types.Fact.Vote{v, Types.Step.At{c, k, n}, pk}
      )
        == Facts.has(s, Types.Fact.Vote{v, Types.Step.At{c, k, n}, pk}): Bool
    },
    name,
    s,
    Types.Fact.Ask{a},
    er => Empty.absurd(
      {
        Facts.has(
          Trust.break(s, name),
          Types.Fact.Vote{v, Types.Step.At{c, k, n}, pk}
        )
          == Facts.has(s, Types.Fact.Vote{v, Types.Step.At{c, k, n}, pk}): Bool
      },
      Shared.Bool.false_ne_true(er)
    ),
    er => ec => Equal.trans(
      Bool,
      Facts.has(
        Trust.break(Facts.add(s, Types.Fact.Ask{a}), name),
        Types.Fact.Vote{v, Types.Step.At{c, k, n}, pk}
      ),
      Facts.has(Facts.add(s, Types.Fact.Ask{a}), Types.Fact.Vote{v, Types.Step.At{c, k, n}, pk}),
      Facts.has(s, Types.Fact.Vote{v, Types.Step.At{c, k, n}, pk}),
      Trust.break_same(
        Facts.add(s, Types.Fact.Ask{a}),
        name,
        Types.Fact.Vote{v, Types.Step.At{c, k, n}, pk}
      )(
        Fact.slot_differs(
          Types.Fact.Vote{v, Types.Step.At{c, k, n}, pk},
          RFacts.Trust.one(name)
        )({==})({==})
      )(
        Fact.slot_differs(
          Types.Fact.Vote{v, Types.Step.At{c, k, n}, pk},
          RFacts.Trust.two(name)
        )({==})({==})
      ),
      Facts.add_same(
        s,
        Types.Fact.Ask{a},
        Types.Fact.Vote{v, Types.Step.At{c, k, n}, pk}
      )(
        Fact.slot_differs(
          Types.Fact.Vote{v, Types.Step.At{c, k, n}, pk},
          Types.Fact.Ask{a}
        )({==})({==})
      )
    ),
    er => ec => Facts.add_same(
      s,
      Types.Fact.Ask{a},
      Types.Fact.Vote{v, Types.Step.At{c, k, n}, pk}
    )(
      Fact.slot_differs(
        Types.Fact.Vote{v, Types.Step.At{c, k, n}, pk},
        Types.Fact.Ask{a}
      )({==})({==})
    )
  )

# a set that takes an ask in holds that ask, and the asks that it held
def Facts.take_ask_asks(
  +name: String,
  +s: Facts(),
  +a: Types.Ask,
  +b: Types.Ask
) -> {
  Facts.has(
    Facts.take(name, s, Types.Fact.Ask{a}),
    Types.Fact.Ask{b}
  )
    == Bool.or(Coded.Ask.is_eq(b, a), Facts.has(s, Types.Fact.Ask{b})): Bool
}:
  Facts.take_by(
    t => {
      Facts.has(
        t,
        Types.Fact.Ask{b}
      )
        == Bool.or(Coded.Ask.is_eq(b, a), Facts.has(s, Types.Fact.Ask{b})): Bool
    },
    name,
    s,
    Types.Fact.Ask{a},
    er => Empty.absurd(
      {
        Facts.has(
          Trust.break(s, name),
          Types.Fact.Ask{b}
        )
          == Bool.or(Coded.Ask.is_eq(b, a), Facts.has(s, Types.Fact.Ask{b})): Bool
      },
      Shared.Bool.false_ne_true(er)
    ),
    er => ec => Equal.trans(
      Bool,
      Facts.has(Trust.break(Facts.add(s, Types.Fact.Ask{a}), name), Types.Fact.Ask{b}),
      Facts.has(Facts.add(s, Types.Fact.Ask{a}), Types.Fact.Ask{b}),
      Bool.or(Coded.Ask.is_eq(b, a), Facts.has(s, Types.Fact.Ask{b})),
      Trust.break_same(
        Facts.add(s, Types.Fact.Ask{a}),
        name,
        Types.Fact.Ask{b}
      )(
        Fact.ask_differs(Types.Fact.Ask{b}, RFacts.Trust.one(name))({==})({==})
      )(Fact.ask_differs(Types.Fact.Ask{b}, RFacts.Trust.two(name))({==})({==})),
      Facts.has_add(s, Types.Fact.Ask{a}, Types.Fact.Ask{b})
    ),
    er => ec => Facts.has_add(s, Types.Fact.Ask{a}, Types.Fact.Ask{b})
  )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# a set is wider after it takes a fact in
def Facts.take_wider(
  +name: String,
  +s: Facts(),
  +f: Types.Fact
) -> {Facts.wider(s, Facts.take(name, s, f)) == True{}: Bool}:
  Facts.take_by(
    t => {Facts.wider(s, t) == True{}: Bool},
    name,
    s,
    f,
    er => Trust.break_wider(s, name),
    er => ec => Facts.wider_trans(
      s,
      Facts.add(s, f),
      Trust.break(Facts.add(s, f), name)
    )(Facts.add_wider(s, f))(Trust.break_wider(Facts.add(s, f), name)),
    er => ec => Facts.add_wider(s, f)
  )

# a set is wider after it takes facts in
def Facts.take_all_wider(
  +name: String,
  +fs: List<&2, Types.Fact>,
  +s: Facts()
) -> {Facts.wider(s, Facts.take_all(name, fs, s)) == True{}: Bool}:
  match fs:
    case Nil{}:
      Facts.wider_refl(s)
    case Con{f, rest}:
      Facts.wider_trans(
        s,
        Facts.take(name, s, f),
        Facts.take_all(name, rest, Facts.take(name, s, f))
      )(Facts.take_wider(name, s, f))(Facts.take_all_wider(name, rest, Facts.take(name, s, f)))

# Laws of trust
# -------------

# no string is itself after a character
def String.cons_ne(name: String, +c: Char) -> {String.eq(SCon{c, name}, name) == False{}: Bool}:
  match name:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      Equal.trans(
        Bool,
        String.eq.go(SCon{h, t}, t, Char.is_eq(c, h)),
        Bool.and(Char.is_eq(c, h), String.eq(SCon{h, t}, t)),
        False{},
        Texts.String.eq.go_and(Char.is_eq(c, h), SCon{h, t}, t),
        (
          %Equal.sym(Bool, String.eq(SCon{h, t}, t), False{}, String.cons_ne(t, h)): {Bool.and(Char.is_eq(c, h), _) == False{}: Bool}
          Shared.Bool.and_false_right(Char.is_eq(c, h)))
      )

# the name under which a node says that its trust broke is not its name
def Trust.voter_ne(+name: String) -> {String.eq(RFacts.Trust.voter(name), name) == False{}: Bool}:
  String.cons_ne(name, '~')

# a node refuses no vote of another voter
def Facts.refuses_other(
  +name: String,
  +s: Facts(),
  +v: String,
  +st: Types.Step,
  +pk: Types.Cast
) -> {
  String.eq(v, name) == False{}: Bool
} -> {Facts.refuses(name, s, Types.Fact.Vote{v, st, pk}) == False{}: Bool}:
  h =>
    %Lists.Bool.and_when(
      String.eq(v, name),
      u => Shared.List.some(
        ~Types.Fact,
        ~Spec.Ballot,
        ~RFacts.Fact.clashes,
        Facts.list(s),
        Spec.Ballot{v, Coded.Step.words(st), Coded.Cast.words(pk)}
      )
    ): {_ == False{}: Bool}
    %Equal.sym(
      Bool,
      String.eq(v, name),
      False{},
      h
    ): {
      Bool.and(
        _,
        Shared.List.some(
          ~Types.Fact,
          ~Spec.Ballot,
          ~RFacts.Fact.clashes,
          Facts.list(s),
          Spec.Ballot{v, Coded.Step.words(st), Coded.Cast.words(pk)}
        )
      )
        == False{}: Bool
    }
    {==}

# the choice of the ballot m, if any
def Ballot.choice_of(m: Maybe<&2, Spec.Ballot>) -> List<&2, U32>:
  match m:
    case None{}:
      []
    case Some{Spec.Ballot{v, s, x}}:
      x

# a node refuses a vote under its name that a vote that it holds contradicts
def Facts.refuses_of(
  +name: String,
  +s: Facts(),
  f: Types.Fact,
  +g: Types.Fact,
  +st: List<&2, U32>,
  +x: List<&2, U32>,
  +y: List<&2, U32>
) -> {
  RFacts.Fact.ballot(f) == Some{Spec.Ballot{name, st, x}}: Maybe<&2, Spec.Ballot>
} -> {
  Facts.has(s, g) == True{}: Bool
} -> {
  RFacts.Fact.ballot(g) == Some{Spec.Ballot{name, st, y}}: Maybe<&2, Spec.Ballot>
} -> {
  Bool.not(RFacts.Words.is_eq(x, y)) == True{}: Bool
} -> {Facts.refuses(name, s, f) == True{}: Bool}:
  match f:
    case Types.Fact.Ask{a}:
      ef => hg => eg => hn => Empty.absurd(
        {False{} == True{}: Bool},
        Shared.Maybe.none_ne_some(Spec.Ballot, Spec.Ballot{name, st, x}, ef)
      )
    case Types.Fact.Vote{+v, +st1, +pk}:
      ef => hg => eg => hn =>
        %Lists.Bool.and_when(
          String.eq(v, name),
          u => Shared.List.some(
            ~Types.Fact,
            ~Spec.Ballot,
            ~RFacts.Fact.clashes,
            Facts.list(s),
            Spec.Ballot{v, Coded.Step.words(st1), Coded.Cast.words(pk)}
          )
        ): {_ == True{}: Bool}
        %Equal.sym(
          Spec.Ballot,
          Spec.Ballot{v, Coded.Step.words(st1), Coded.Cast.words(pk)},
          Spec.Ballot{name, st, x},
          Shared.Maybe.some_inj(
            Spec.Ballot,
            Spec.Ballot{v, Coded.Step.words(st1), Coded.Cast.words(pk)},
            Spec.Ballot{name, st, x},
            ef
          )
        ): {
          Bool.and(
            String.eq(RFacts.Ballot.voter(_), name),
            Shared.List.some(~Types.Fact, ~Spec.Ballot, ~RFacts.Fact.clashes, Facts.list(s), _)
          )
            == True{}: Bool
        }
        Shared.Bool.and_both(
          String.eq(name, name),
          Shared.List.some(
            ~Types.Fact,
            ~Spec.Ballot,
            ~RFacts.Fact.clashes,
            Facts.list(s),
            Spec.Ballot{name, st, x}
          )
        )(
          Texts.String.eq_refl(name)
        )(
          Lists.List.in_some(
            ~Types.Fact,
            ~Spec.Ballot,
            ~RFacts.Fact.clashes,
            ~Coded.Fact.is_eq,
            ~Coded.Fact.laws(),
            Facts.list(s),
            Spec.Ballot{name, st, x},
            g
          )(Facts.has_in(s, g)(hg))(Fact.clashes_of(name, st, x, y, g)(eg)(hn))
        )

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof does not run
# what follows when x is y, and when s holds x, follows when s with y holds x
def Facts.add_cases(
  -P: Type,
  +s: Facts(),
  +y: Types.Fact,
  +x: Types.Fact,
  h: {Facts.has(Facts.add(s, y), x) == True{}: Bool},
  fa: {x == y: Types.Fact} -> P,
  fb: {Facts.has(s, x) == True{}: Bool} -> P
) -> P:
  Case.or_by(
    P,
    Coded.Fact.is_eq(x, y),
    Facts.has(s, x),
    Equal.trans(
      Bool,
      Bool.or(Coded.Fact.is_eq(x, y), Facts.has(s, x)),
      Facts.has(Facts.add(s, y), x),
      True{},
      Equal.sym(
        Bool,
        Facts.has(Facts.add(s, y), x),
        Bool.or(Coded.Fact.is_eq(x, y), Facts.has(s, x)),
        Facts.has_add(s, y, x)
      ),
      h
    ),
    t => fa(Coded.Fact.is_eq_sound(x, y)(t)),
    fb
  )

# Facts.add_no_liar, with the two votes of the node
def Facts.add_no_liar.fin(
  +name: String,
  +s: Facts(),
  +f: Types.Fact,
  +f1: Types.Fact,
  +f2: Types.Fact,
  +st: List<&2, U32>,
  +x: List<&2, U32>,
  +y: List<&2, U32>,
  +hl: {List.contains(~String, ~String.eq, Facts.liars(s), name) == False{}: Bool},
  +hr: {Facts.refuses(name, s, f) == False{}: Bool},
  +h1: {Facts.has(Facts.add(s, f), f1) == True{}: Bool},
  +h2: {Facts.has(Facts.add(s, f), f2) == True{}: Bool},
  +e1: {RFacts.Fact.ballot(f1) == Some{Spec.Ballot{name, st, x}}: Maybe<&2, Spec.Ballot>},
  +e2: {RFacts.Fact.ballot(f2) == Some{Spec.Ballot{name, st, y}}: Maybe<&2, Spec.Ballot>},
  +hn: {Bool.not(RFacts.Words.is_eq(x, y)) == True{}: Bool}
) -> Empty:
  Facts.add_cases(
    Empty,
    s,
    f,
    f1,
    h1,
    +a1 => Facts.add_cases(
      Empty,
      s,
      f,
      f2,
      h2,
      a2 => Words.ne(
        x,
        y
      )(
        hn
      )(
        Equal.cong(
          Maybe<&2, Spec.Ballot>,
          List<&2, U32>,
          m => Ballot.choice_of(m),
          Some{Spec.Ballot{name, st, x}},
          Some{Spec.Ballot{name, st, y}},
          Equal.trans(
            Maybe<&2, Spec.Ballot>,
            Some{Spec.Ballot{name, st, x}},
            RFacts.Fact.ballot(f1),
            Some{Spec.Ballot{name, st, y}},
            Equal.sym(
              Maybe<&2, Spec.Ballot>,
              RFacts.Fact.ballot(f1),
              Some{Spec.Ballot{name, st, x}},
              e1
            ),
            Equal.trans(
              Maybe<&2, Spec.Ballot>,
              RFacts.Fact.ballot(f1),
              RFacts.Fact.ballot(f2),
              Some{Spec.Ballot{name, st, y}},
              Equal.cong(
                Types.Fact,
                Maybe<&2, Spec.Ballot>,
                z => RFacts.Fact.ballot(z),
                f1,
                f2,
                Equal.trans(Types.Fact, f1, f, f2, a1, Equal.sym(Types.Fact, f2, f, a2))
              ),
              e2
            )
          )
        )
      ),
      b2 => Lists.Bool.clash(
        Empty,
        Facts.refuses(name, s, f),
        hr,
        Facts.refuses_of(name, s, f, f2, st, x, y)((
            %a1: {RFacts.Fact.ballot(_) == Some{Spec.Ballot{name, st, x}}: Maybe<&2, Spec.Ballot>}
            e1))(b2)(e2)(hn)
      )
    ),
    +b1 => Facts.add_cases(
      Empty,
      s,
      f,
      f2,
      h2,
      a2 => Lists.Bool.clash(
        Empty,
        Facts.refuses(name, s, f),
        hr,
        Facts.refuses_of(name, s, f, f1, st, y, x)((
            %a2: {RFacts.Fact.ballot(_) == Some{Spec.Ballot{name, st, y}}: Maybe<&2, Spec.Ballot>}
            e2))(b1)(e1)(Words.ne_sym(x, y)(hn))
      ),
      b2 => Lists.Bool.clash(
        Empty,
        List.contains(~String, ~String.eq, Facts.liars(s), name),
        hl,
        Facts.liars_in(s, f1, f2, name, st, x, y)(b1)(b2)(e1)(e2)(hn)
      )
    )
  )

# Facts.add_no_liar, with what names the node a liar
def Facts.add_no_liar.at(
  +name: String,
  +s: Facts(),
  +f: Types.Fact,
  hl: {List.contains(~String, ~String.eq, Facts.liars(s), name) == False{}: Bool},
  hr: {Facts.refuses(name, s, f) == False{}: Bool},
  r: Facts.Liar(Facts.add(s, f), name)
) -> Empty:
  (+f1, p) = r
  (+f2, p1) = p
  (+h1, p2) = p1
  (+h2, p3) = p2
  (+st, p4) = p3
  (+x, p5) = p4
  (+y, p6) = p5
  (+e1, p7) = p6
  (+e2, hn) = p7
  Facts.add_no_liar.fin(name, s, f, f1, f2, st, x, y, hl, hr, h1, h2, e1, e2, hn)

# a set that does not name a node a liar does not with a fact that the node
# does not refuse
def Facts.add_no_liar(
  +name: String,
  +s: Facts(),
  +f: Types.Fact
) -> {
  List.contains(~String, ~String.eq, Facts.liars(s), name) == False{}: Bool
} -> {
  Facts.refuses(name, s, f) == False{}: Bool
} -> {List.contains(~String, ~String.eq, Facts.liars(Facts.add(s, f)), name) == False{}: Bool}:
  hl => hr => Case.false_of(
    List.contains(~String, ~String.eq, Facts.liars(Facts.add(s, f)), name)
  )(hin => Facts.add_no_liar.at(name, s, f, hl, hr, Facts.liars_of(Facts.add(s, f), name)(hin)))

# a set that does not name a node a liar does not when the trust of the node
# breaks
def Trust.break_no_liar(
  +name: String,
  +s: Facts()
) -> {
  List.contains(~String, ~String.eq, Facts.liars(s), name) == False{}: Bool
} -> {List.contains(~String, ~String.eq, Facts.liars(Trust.break(s, name)), name) == False{}: Bool}:
  hl => Facts.add_no_liar(
    name,
    Facts.add(s, RFacts.Trust.one(name)),
    RFacts.Trust.two(name)
  )(
    Facts.add_no_liar(
      name,
      s,
      RFacts.Trust.one(name)
    )(
      hl
    )(
      Facts.refuses_other(
        name,
        s,
        RFacts.Trust.voter(name),
        Types.Step.Broken{},
        RFacts.Trust.cast(0n)
      )(Trust.voter_ne(name))
    )
  )(
    Facts.refuses_other(
      name,
      Facts.add(s, RFacts.Trust.one(name)),
      RFacts.Trust.voter(name),
      Types.Step.Broken{},
      RFacts.Trust.cast(1n)
    )(Trust.voter_ne(name))
  )

# a set whose trust broke says so
def Trust.break_broken(
  +s: Facts(),
  +name: String
) -> {Trust.broken(Trust.break(s, name), name) == True{}: Bool}:
  Shared.Bool.and_both(
    Facts.has(Trust.break(s, name), RFacts.Trust.one(name)),
    Facts.has(Trust.break(s, name), RFacts.Trust.two(name))
  )(
    Facts.add_keeps(
      Facts.add(s, RFacts.Trust.one(name)),
      RFacts.Trust.two(name),
      RFacts.Trust.one(name)
    )(Facts.add_has(s, RFacts.Trust.one(name)))
  )(Facts.add_has(Facts.add(s, RFacts.Trust.one(name)), RFacts.Trust.two(name)))

# a wider set says that the trust broke when the set does
def Trust.wider_broken(
  +a: Facts(),
  +b: Facts(),
  +name: String
) -> {
  Facts.wider(a, b) == True{}: Bool
} -> {Trust.broken(a, name) == True{}: Bool} -> {Trust.broken(b, name) == True{}: Bool}:
  +hw => +hb => Shared.Bool.and_both(
    Facts.has(b, RFacts.Trust.one(name)),
    Facts.has(b, RFacts.Trust.two(name))
  )(
    Facts.wider_has(
      a,
      b,
      RFacts.Trust.one(name)
    )(
      hw
    )(
      Shared.Bool.and_true_left(
        Facts.has(a, RFacts.Trust.one(name)),
        Facts.has(a, RFacts.Trust.two(name))
      )(hb)
    )
  )(
    Facts.wider_has(
      a,
      b,
      RFacts.Trust.two(name)
    )(
      hw
    )(
      Shared.Bool.and_true_right(
        Facts.has(a, RFacts.Trust.one(name)),
        Facts.has(a, RFacts.Trust.two(name))
      )(hb)
    )
  )

# the two votes of a broken trust are for two choices
def Trust.casts_differ() -> {
  Bool.not(
    RFacts.Words.is_eq(
      Coded.Cast.words(RFacts.Trust.cast(0n)),
      Coded.Cast.words(RFacts.Trust.cast(1n))
    )
  )
    == True{}: Bool
}:
  {==}

# a set that says that the trust of a node broke names a liar
def Trust.broken_liar(
  +s: Facts(),
  +name: String
) -> {
  Trust.broken(s, name) == True{}: Bool
} -> {List.contains(~String, ~String.eq, Facts.liars(s), RFacts.Trust.voter(name)) == True{}: Bool}:
  +hb => Facts.liars_in(
    s,
    RFacts.Trust.one(name),
    RFacts.Trust.two(name),
    RFacts.Trust.voter(name),
    Coded.Step.words(Types.Step.Broken{}),
    Coded.Cast.words(RFacts.Trust.cast(0n)),
    Coded.Cast.words(RFacts.Trust.cast(1n))
  )(
    Shared.Bool.and_true_left(
      Facts.has(s, RFacts.Trust.one(name)),
      Facts.has(s, RFacts.Trust.two(name))
    )(hb)
  )(
    Shared.Bool.and_true_right(
      Facts.has(s, RFacts.Trust.one(name)),
      Facts.has(s, RFacts.Trust.two(name))
    )(hb)
  )({==})({==})(Trust.casts_differ())

# no set that names no liar says that the trust of a node broke
def Trust.broken_never(
  +s: Facts(),
  +name: String
) -> {Trust.broken(s, name) == True{}: Bool} -> {Facts.liars(s) == []: List<&2, String>} -> Empty:
  hb => hn => Lists.List.in_not_nil(
    ~String,
    ~String.eq,
    Facts.liars(s),
    RFacts.Trust.voter(name)
  )(Trust.broken_liar(s, name)(hb))(hn)

# Laws of the starts
# ------------------

# an ask that starts the store of the root h: its request starts a store,
# and its root is h
def Ask.starts_true(
  +h: Hashes.Hash,
  +i: Ledgers.Id,
  +k: Nat,
  +r: Spec.Request
) -> {
  RFacts.Ask.starts(h, Types.Ask{i, k, r}) == True{}: Bool
} -> {
  Bool.and(
    RFacts.Request.is_start(r),
    Hashes.Hash.is_eq(RFacts.Start.root(i, r), h)
  )
    == True{}: Bool
}:
  hs =>
    %Lists.Bool.when_and(
      RFacts.Request.is_start(r),
      u => Hashes.Hash.is_eq(RFacts.Start.root(i, r), h)
    ): {_ == True{}: Bool}
    hs

# the root of an ask that starts the store of a root is that root
def Ask.starts_root(
  +h: Hashes.Hash,
  a: Types.Ask
) -> {RFacts.Ask.starts(h, a) == True{}: Bool} -> {RFacts.Ask.root(a) == h: Hashes.Hash}:
  match a:
    case Types.Ask{+i, k, +r}:
      hs => Hashes.Hash.is_eq_sound(
        RFacts.Start.root(i, r),
        h
      )(
        Shared.Bool.and_true_right(
          RFacts.Request.is_start(r),
          Hashes.Hash.is_eq(RFacts.Start.root(i, r), h)
        )(Ask.starts_true(h, i, k, r)(hs))
      )

# an ask that starts a store starts the store of its root
def Ask.starts_self(
  +h: Hashes.Hash,
  +a: Types.Ask
) -> {
  RFacts.Ask.starts(h, a) == True{}: Bool
} -> {RFacts.Ask.starts(RFacts.Ask.root(a), a) == True{}: Bool}:
  +hs =>
    %Equal.sym(
      Hashes.Hash,
      RFacts.Ask.root(a),
      h,
      Ask.starts_root(h, a)(hs)
    ): {RFacts.Ask.starts(_, a) == True{}: Bool}
    hs

# an ask that starts the store that a starts, starts the store of the root
# of a
def Ask.starts_to(
  +h: Hashes.Hash,
  +a: Types.Ask,
  +b: Types.Ask
) -> {
  RFacts.Ask.starts(h, a) == True{}: Bool
} -> {
  RFacts.Ask.starts(h, b) == True{}: Bool
} -> {RFacts.Ask.starts(RFacts.Ask.root(a), b) == True{}: Bool}:
  ha => hb =>
    %Equal.sym(
      Hashes.Hash,
      RFacts.Ask.root(a),
      h,
      Ask.starts_root(h, a)(ha)
    ): {RFacts.Ask.starts(_, b) == True{}: Bool}
    hb

# an ask is of the id and the request of itself
def Ask.alike_refl(a: Types.Ask) -> {RFacts.Ask.alike(a, a) == True{}: Bool}:
  match a:
    case Types.Ask{+i, k, +r}:
      Shared.Bool.and_both(
        Ledgers.Id.is_eq(i, i),
        Coded.Request.is_eq(r, r)
      )(Ledgers.Id.is_eq_refl(i))(Coded.Request.is_eq_refl(r))

# alike, the other way round
def Ask.alike_sym(
  a: Types.Ask,
  b: Types.Ask
) -> {RFacts.Ask.alike(b, a) == True{}: Bool} -> {RFacts.Ask.alike(a, b) == True{}: Bool}:
  match a b:
    case Types.Ask{+i, k, +r} Types.Ask{+j, l, +q}:
      +h =>
        %Ledgers.Id.is_eq_sound(
          j,
          i
        )(
          Shared.Bool.and_true_left(Ledgers.Id.is_eq(j, i), Coded.Request.is_eq(q, r))(h)
        ): {Bool.and(Ledgers.Id.is_eq(_, j), Coded.Request.is_eq(r, q)) == True{}: Bool}
        %Coded.Request.is_eq_sound(
          q,
          r
        )(
          Shared.Bool.and_true_right(Ledgers.Id.is_eq(j, i), Coded.Request.is_eq(q, r))(h)
        ): {Bool.and(Ledgers.Id.is_eq(j, j), Coded.Request.is_eq(_, q)) == True{}: Bool}
        Shared.Bool.and_both(
          Ledgers.Id.is_eq(j, j),
          Coded.Request.is_eq(q, q)
        )(Ledgers.Id.is_eq_refl(j))(Coded.Request.is_eq_refl(q))

# the asks a and b start the store of the root of a, and differ
def Ask.clash(+a: Types.Ask, +b: Types.Ask) -> Bool:
  Bool.and(
    RFacts.Ask.starts(RFacts.Ask.root(a), a),
    Bool.and(RFacts.Ask.starts(RFacts.Ask.root(a), b), Bool.not(RFacts.Ask.alike(a, b)))
  )

# the test of a collision that the code that runs makes is Ask.clash
def Ask.collides_and(
  +a: Types.Ask,
  +b: Types.Ask
) -> {RFacts.Ask.collides(a, b) == Ask.clash(a, b): Bool}:
  %Lists.Bool.when_and(
    RFacts.Ask.starts(RFacts.Ask.root(a), b),
    u => Bool.not(RFacts.Ask.alike(a, b))
  ): {RFacts.Ask.collides(a, b) == Bool.and(RFacts.Ask.starts(RFacts.Ask.root(a), a), _): Bool}
  Lists.Bool.when_and(
    RFacts.Ask.starts(RFacts.Ask.root(a), a),
    un => Shared.Bool.when(
      Bool,
      RFacts.Ask.starts(RFacts.Ask.root(a), b),
      u => Bool.not(RFacts.Ask.alike(a, b)),
      u => False{}
    )
  )

# Ask.collides_sym, of Ask.clash
def Ask.collides_sym.and(
  +a: Types.Ask,
  +b: Types.Ask
) -> {Ask.clash(a, b) == True{}: Bool} -> {Ask.clash(b, a) == True{}: Bool}:
  +h =>
    %Equal.sym(
      Hashes.Hash,
      RFacts.Ask.root(b),
      RFacts.Ask.root(a),
      Ask.starts_root(
        RFacts.Ask.root(a),
        b
      )(
        Shared.Bool.and_second(
          RFacts.Ask.starts(RFacts.Ask.root(a), a),
          RFacts.Ask.starts(RFacts.Ask.root(a), b),
          Bool.not(RFacts.Ask.alike(a, b))
        )(h)
      )
    ): {
      Bool.and(
        RFacts.Ask.starts(_, b),
        Bool.and(RFacts.Ask.starts(_, a), Bool.not(RFacts.Ask.alike(b, a)))
      )
        == True{}: Bool
    }
    Shared.Bool.and_both(
      RFacts.Ask.starts(RFacts.Ask.root(a), b),
      Bool.and(RFacts.Ask.starts(RFacts.Ask.root(a), a), Bool.not(RFacts.Ask.alike(b, a)))
    )(
      Shared.Bool.and_second(
        RFacts.Ask.starts(RFacts.Ask.root(a), a),
        RFacts.Ask.starts(RFacts.Ask.root(a), b),
        Bool.not(RFacts.Ask.alike(a, b))
      )(h)
    )(
      Shared.Bool.and_both(
        RFacts.Ask.starts(RFacts.Ask.root(a), a),
        Bool.not(RFacts.Ask.alike(b, a))
      )(
        Shared.Bool.and_true_left(
          RFacts.Ask.starts(RFacts.Ask.root(a), a),
          Bool.and(RFacts.Ask.starts(RFacts.Ask.root(a), b), Bool.not(RFacts.Ask.alike(a, b)))
        )(h)
      )(
        Case.not_of(
          RFacts.Ask.alike(b, a)
        )(
          Case.false_of(
            RFacts.Ask.alike(b, a)
          )(
            t => Lists.Bool.clash(
              Empty,
              RFacts.Ask.alike(a, b),
              Shared.Bool.not_true(
                RFacts.Ask.alike(a, b)
              )(
                Shared.Bool.and_third(
                  RFacts.Ask.starts(RFacts.Ask.root(a), a),
                  RFacts.Ask.starts(RFacts.Ask.root(a), b),
                  Bool.not(RFacts.Ask.alike(a, b))
                )(h)
              ),
              Ask.alike_sym(a, b)(t)
            )
          )
        )
      )
    )

# an ask that collides with another: the other collides with it
def Ask.collides_sym(
  +a: Types.Ask,
  +b: Types.Ask
) -> {RFacts.Ask.collides(a, b) == True{}: Bool} -> {RFacts.Ask.collides(b, a) == True{}: Bool}:
  h =>
    %Equal.sym(
      Bool,
      RFacts.Ask.collides(b, a),
      Ask.clash(b, a),
      Ask.collides_and(b, a)
    ): {_ == True{}: Bool}
    Ask.collides_sym.and(a, b)(
      %Ask.collides_and(a, b): {_ == True{}: Bool}
      h)
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# no ask collides with itself
def Ask.collides_self(+a: Types.Ask) -> {RFacts.Ask.collides(a, a) == True{}: Bool} -> Empty:
  h => Lists.Bool.clash(
    Empty,
    RFacts.Ask.alike(a, a),
    Shared.Bool.not_true(
      RFacts.Ask.alike(a, a)
    )(
      Shared.Bool.and_third(
        RFacts.Ask.starts(RFacts.Ask.root(a), a),
        RFacts.Ask.starts(RFacts.Ask.root(a), a),
        Bool.not(RFacts.Ask.alike(a, a))
      )(
        %Ask.collides_and(a, a): {_ == True{}: Bool}
        h)
    ),
    Ask.alike_refl(a)
  )

# the ask of the fact f, or d when f is a vote
def Fact.ask_of(d: Types.Ask, f: Types.Fact) -> Types.Ask:
  match f:
    case Types.Fact.Ask{a}:
      a
    case Types.Fact.Vote{v, st, pk}:
      d

# two asks that are one fact are one ask
def Ask.inj(
  +a: Types.Ask,
  +b: Types.Ask
) -> {Types.Fact.Ask{a} == Types.Fact.Ask{b}: Types.Fact} -> {a == b: Types.Ask}:
  e => Equal.cong(
    Types.Fact,
    Types.Ask,
    z => Fact.ask_of(a, z),
    Types.Fact.Ask{a},
    Types.Fact.Ask{b},
    e
  )

# the set s holds two asks that collide
def Facts.Collide(s: Facts()) -> Type:
  Exists(
    Types.Ask,
    a1 => Exists(
      Types.Ask,
      a2 => {
        Facts.has(s, Types.Fact.Ask{a1}) == True{}: Bool
      }
        & (
          {
            Facts.has(s, Types.Fact.Ask{a2}) == True{}: Bool
          }
            & {RFacts.Ask.collides(a1, a2) == True{}: Bool}
        )
    )
  )

# Facts.collide_of, with the two facts
def Facts.collide_of.fin(
  +s: Facts(),
  +a1: Types.Ask,
  f2: Types.Fact,
  c1: {
    List.contains(~Types.Fact, ~Coded.Fact.is_eq, Facts.list(s), Types.Fact.Ask{a1}) == True{}: Bool
  },
  c2: {List.contains(~Types.Fact, ~Coded.Fact.is_eq, Facts.list(s), f2) == True{}: Bool},
  h: {RFacts.Fact.collides(a1, f2) == True{}: Bool}
) -> Facts.Collide(s):
  match f2:
    case Types.Fact.Ask{+a2}:
      (
        a1,
        (
          a2,
          (Facts.in_has(s, Types.Fact.Ask{a1})(c1), (Facts.in_has(s, Types.Fact.Ask{a2})(c2), h))
        )
      )
    case Types.Fact.Vote{v, st, pk}:
      Empty.absurd(Facts.Collide(s), Shared.Bool.false_ne_true(h))

# Facts.collide_of, with the first ask and what collides with it
def Facts.collide_of.two(
  +s: Facts(),
  +a1: Types.Ask,
  c1: {
    List.contains(~Types.Fact, ~Coded.Fact.is_eq, Facts.list(s), Types.Fact.Ask{a1}) == True{}: Bool
  },
  r: Exists(
    Types.Fact,
    f2 => {
      List.contains(~Types.Fact, ~Coded.Fact.is_eq, Facts.list(s), f2) == True{}: Bool
    }
      & {RFacts.Fact.collides(a1, f2) == True{}: Bool}
  )
) -> Facts.Collide(s):
  (+f2, p) = r
  (c2, h) = p
  Facts.collide_of.fin(s, a1, f2, c1, c2, h)

# Facts.collide_of, with the first fact
def Facts.collide_of.one(
  +s: Facts(),
  f1: Types.Fact,
  c1: {List.contains(~Types.Fact, ~Coded.Fact.is_eq, Facts.list(s), f1) == True{}: Bool},
  hc: {RFacts.Fact.collided(Facts.list(s), f1) == True{}: Bool}
) -> Facts.Collide(s):
  match f1:
    case Types.Fact.Ask{+a1}:
      Facts.collide_of.two(
        s,
        a1,
        c1,
        Lists.List.some_in(
          ~Types.Fact,
          ~Types.Ask,
          ~RFacts.Fact.collides,
          ~Coded.Fact.is_eq,
          ~Coded.Fact.laws(),
          Facts.list(s),
          a1
        )(hc)
      )
    case Types.Fact.Vote{v, st, pk}:
      Empty.absurd(Facts.Collide(s), Shared.Bool.false_ne_true(hc))

# Facts.collide_of, with the member of the list that collides
def Facts.collide_of.at(
  +s: Facts(),
  r: Exists(
    Types.Fact,
    f1 => {
      List.contains(~Types.Fact, ~Coded.Fact.is_eq, Facts.list(s), f1) == True{}: Bool
    }
      & {RFacts.Fact.collided(Facts.list(s), f1) == True{}: Bool}
  )
) -> Facts.Collide(s):
  (+f1, p) = r
  (c1, hc) = p
  Facts.collide_of.one(s, f1, c1, hc)

# a set whose asks collide holds two asks that collide
def Facts.collide_of(+s: Facts()) -> {Facts.collide(s) == True{}: Bool} -> Facts.Collide(s):
  hc => Facts.collide_of.at(
    s,
    Lists.List.some_in(
      ~Types.Fact,
      ~List<&2, Types.Fact>,
      ~RFacts.Fact.collided,
      ~Coded.Fact.is_eq,
      ~Coded.Fact.laws(),
      Facts.list(s),
      Facts.list(s)
    )(hc)
  )

# an ask collides with the list of a set that holds an ask that it collides
# with
def Facts.collided_in(
  +s: Facts(),
  +a: Types.Ask,
  +b: Types.Ask
) -> {
  Facts.has(s, Types.Fact.Ask{b}) == True{}: Bool
} -> {
  RFacts.Ask.collides(a, b) == True{}: Bool
} -> {RFacts.Fact.collided(Facts.list(s), Types.Fact.Ask{a}) == True{}: Bool}:
  hb => hc => Lists.List.in_some(
    ~Types.Fact,
    ~Types.Ask,
    ~RFacts.Fact.collides,
    ~Coded.Fact.is_eq,
    ~Coded.Fact.laws(),
    Facts.list(s),
    a,
    Types.Fact.Ask{b}
  )(Facts.has_in(s, Types.Fact.Ask{b})(hb))(hc)

# the asks of a set that holds two asks that collide collide
def Facts.collide_in(
  +s: Facts(),
  +a: Types.Ask,
  +b: Types.Ask
) -> {
  Facts.has(s, Types.Fact.Ask{a}) == True{}: Bool
} -> {
  Facts.has(s, Types.Fact.Ask{b}) == True{}: Bool
} -> {RFacts.Ask.collides(a, b) == True{}: Bool} -> {Facts.collide(s) == True{}: Bool}:
  ha => hb => hc => Lists.List.in_some(
    ~Types.Fact,
    ~List<&2, Types.Fact>,
    ~RFacts.Fact.collided,
    ~Coded.Fact.is_eq,
    ~Coded.Fact.laws(),
    Facts.list(s),
    Facts.list(s),
    Types.Fact.Ask{a}
  )(Facts.has_in(s, Types.Fact.Ask{a})(ha))(Facts.collided_in(s, a, b)(hb)(hc))

# Facts.add_collide, with the two asks
def Facts.add_collide.fin(
  +s: Facts(),
  +f: Types.Fact,
  +a1: Types.Ask,
  +a2: Types.Ask,
  +hf: {RFacts.Fact.collided(Facts.list(s), f) == False{}: Bool},
  +h1: {Facts.has(Facts.add(s, f), Types.Fact.Ask{a1}) == True{}: Bool},
  +h2: {Facts.has(Facts.add(s, f), Types.Fact.Ask{a2}) == True{}: Bool},
  +hc: {RFacts.Ask.collides(a1, a2) == True{}: Bool}
) -> {Facts.collide(s) == True{}: Bool}:
  Facts.add_cases(
    {Facts.collide(s) == True{}: Bool},
    s,
    f,
    Types.Fact.Ask{a1},
    h1,
    +e1 => Facts.add_cases(
      {Facts.collide(s) == True{}: Bool},
      s,
      f,
      Types.Fact.Ask{a2},
      h2,
      e2 => Empty.absurd({Facts.collide(s) == True{}: Bool}, Ask.collides_self(a1)((
            %Ask.inj(a2, a1)(Equal.trans(Types.Fact, Types.Fact.Ask{a2}, f, Types.Fact.Ask{a1}, e2, Equal.sym(Types.Fact, Types.Fact.Ask{a1}, f, e1))): {RFacts.Ask.collides(a1, _) == True{}: Bool}
            hc))),
      b2 => Lists.Bool.clash(
        {Facts.collide(s) == True{}: Bool},
        RFacts.Fact.collided(Facts.list(s), f),
        hf,
        (
          %e1: {RFacts.Fact.collided(Facts.list(s), _) == True{}: Bool}
          Facts.collided_in(s, a1, a2)(b2)(hc))
      )
    ),
    +b1 => Facts.add_cases(
      {Facts.collide(s) == True{}: Bool},
      s,
      f,
      Types.Fact.Ask{a2},
      h2,
      e2 => Lists.Bool.clash(
        {Facts.collide(s) == True{}: Bool},
        RFacts.Fact.collided(Facts.list(s), f),
        hf,
        (
          %e2: {RFacts.Fact.collided(Facts.list(s), _) == True{}: Bool}
          Facts.collided_in(s, a2, a1)(b1)(Ask.collides_sym(a1, a2)(hc)))
      ),
      b2 => Facts.collide_in(s, a1, a2)(b1)(b2)(hc)
    )
  )

# Facts.add_collide, with the two asks that collide
def Facts.add_collide.at(
  +s: Facts(),
  +f: Types.Fact,
  hf: {RFacts.Fact.collided(Facts.list(s), f) == False{}: Bool},
  r: Facts.Collide(Facts.add(s, f))
) -> {Facts.collide(s) == True{}: Bool}:
  (+a1, p) = r
  (+a2, p1) = p
  (+h1, p2) = p1
  (+h2, hc) = p2
  Facts.add_collide.fin(s, f, a1, a2, hf, h1, h2, hc)

# the asks of a set collide when they do with a fact that collides with none
# of them
def Facts.add_collide(
  +s: Facts(),
  +f: Types.Fact
) -> {
  RFacts.Fact.collided(Facts.list(s), f) == False{}: Bool
} -> {Facts.collide(Facts.add(s, f)) == True{}: Bool} -> {Facts.collide(s) == True{}: Bool}:
  hf => hc => Facts.add_collide.at(s, f, hf, Facts.collide_of(Facts.add(s, f))(hc))

# Laws of sound sets
# ------------------

# a set says that the trust broke when it did before a fact
def Trust.add_broken(
  +s: Facts(),
  +name: String,
  +f: Types.Fact
) -> {
  Trust.broken(s, name) == True{}: Bool
} -> {Trust.broken(Facts.add(s, f), name) == True{}: Bool}:
  +h => Shared.Bool.and_both(
    Facts.has(Facts.add(s, f), RFacts.Trust.one(name)),
    Facts.has(Facts.add(s, f), RFacts.Trust.two(name))
  )(
    Facts.add_keeps(
      s,
      f,
      RFacts.Trust.one(name)
    )(
      Shared.Bool.and_true_left(
        Facts.has(s, RFacts.Trust.one(name)),
        Facts.has(s, RFacts.Trust.two(name))
      )(h)
    )
  )(
    Facts.add_keeps(
      s,
      f,
      RFacts.Trust.two(name)
    )(
      Shared.Bool.and_true_right(
        Facts.has(s, RFacts.Trust.one(name)),
        Facts.has(s, RFacts.Trust.two(name))
      )(h)
    )
  )

# a set whose starts are sound stays so with a fact that collides with none
# of its asks
def Facts.add_trust(
  +name: String,
  +s: Facts(),
  +f: Types.Fact
) -> {
  Bool.or(Bool.not(Facts.collide(s)), Trust.broken(s, name)) == True{}: Bool
} -> {
  RFacts.Fact.collided(Facts.list(s), f) == False{}: Bool
} -> {
  Bool.or(
    Bool.not(Facts.collide(Facts.add(s, f))),
    Trust.broken(Facts.add(s, f), name)
  )
    == True{}: Bool
}:
  ht => hf => Case.or_by(
    {
      Bool.or(
        Bool.not(Facts.collide(Facts.add(s, f))),
        Trust.broken(Facts.add(s, f), name)
      )
        == True{}: Bool
    },
    Bool.not(Facts.collide(s)),
    Trust.broken(s, name),
    ht,
    hnc => Case.or_left(
      Bool.not(Facts.collide(Facts.add(s, f))),
      Trust.broken(Facts.add(s, f), name)
    )(
      Case.not_of(
        Facts.collide(Facts.add(s, f))
      )(
        Case.false_of(
          Facts.collide(Facts.add(s, f))
        )(
          t => Lists.Bool.clash(
            Empty,
            Facts.collide(s),
            Shared.Bool.not_true(Facts.collide(s))(hnc),
            Facts.add_collide(s, f)(hf)(t)
          )
        )
      )
    ),
    hb => Case.or_right(
      Bool.not(Facts.collide(Facts.add(s, f))),
      Trust.broken(Facts.add(s, f), name)
    )(Trust.add_broken(s, name, f)(hb))
  )

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof does not run
# a set that does not name a node a liar, and whose starts are sound, is sound
# for the node
def Facts.ok_of(
  +name: String,
  +s: Facts()
) -> {
  List.contains(~String, ~String.eq, Facts.liars(s), name) == False{}: Bool
} -> {
  Bool.or(Bool.not(Facts.collide(s)), Trust.broken(s, name)) == True{}: Bool
} -> {Facts.ok(name, s) == True{}: Bool}:
  hl => ht => Shared.Bool.and_both(
    Bool.not(List.contains(~String, ~String.eq, Facts.liars(s), name)),
    Bool.or(Bool.not(Facts.collide(s)), Trust.broken(s, name))
  )(Case.not_of(List.contains(~String, ~String.eq, Facts.liars(s), name))(hl))(ht)

# the starts of a set that is sound for a node are sound
def Facts.ok_trust(
  +name: String,
  +s: Facts()
) -> {
  Facts.ok(name, s) == True{}: Bool
} -> {Bool.or(Bool.not(Facts.collide(s)), Trust.broken(s, name)) == True{}: Bool}:
  h => Shared.Bool.and_true_right(
    Bool.not(List.contains(~String, ~String.eq, Facts.liars(s), name)),
    Bool.or(Bool.not(Facts.collide(s)), Trust.broken(s, name))
  )(h)

# a set that does not name a node a liar is sound for it once its trust broke
def Trust.break_ok(
  +name: String,
  +s: Facts()
) -> {
  List.contains(~String, ~String.eq, Facts.liars(s), name) == False{}: Bool
} -> {Facts.ok(name, Trust.break(s, name)) == True{}: Bool}:
  hl => Facts.ok_of(
    name,
    Trust.break(s, name)
  )(
    Trust.break_no_liar(name, s)(hl)
  )(
    Case.or_right(
      Bool.not(Facts.collide(Trust.break(s, name))),
      Trust.broken(Trust.break(s, name), name)
    )(Trust.break_broken(s, name))
  )

# in a set that is sound for a node and names no liar, two asks that start
# one store are of one id and one request
def Facts.honest_starts(
  +name: String,
  +s: Facts(),
  +h: Hashes.Hash,
  +a: Types.Ask,
  +b: Types.Ask
) -> {
  Facts.ok(name, s) == True{}: Bool
} -> {
  Facts.liars(s) == []: List<&2, String>
} -> {
  Facts.has(s, Types.Fact.Ask{a}) == True{}: Bool
} -> {
  Facts.has(s, Types.Fact.Ask{b}) == True{}: Bool
} -> {
  RFacts.Ask.starts(h, a) == True{}: Bool
} -> {RFacts.Ask.starts(h, b) == True{}: Bool} -> {RFacts.Ask.alike(a, b) == True{}: Bool}:
  hok => hn => ha => hb => +sa => sb => Case.true_of(
    RFacts.Ask.alike(a, b)
  )(
    ef => Lists.Bool.clash(
      Empty,
      Facts.collide(s),
      Shared.Bool.not_true(
        Facts.collide(s)
      )(
        Case.or_by(
          {Bool.not(Facts.collide(s)) == True{}: Bool},
          Bool.not(Facts.collide(s)),
          Trust.broken(s, name),
          Facts.ok_trust(name, s)(hok),
          hnc => hnc,
          hbk => Empty.absurd(
            {Bool.not(Facts.collide(s)) == True{}: Bool},
            Trust.broken_never(s, name)(hbk)(hn)
          )
        )
      ),
      Facts.collide_in(s, a, b)(ha)(hb)(
        %Equal.sym(Bool, RFacts.Ask.collides(a, b), Ask.clash(a, b), Ask.collides_and(a, b)): {_ == True{}: Bool}
        Shared.Bool.and_both(RFacts.Ask.starts(RFacts.Ask.root(a), a), Bool.and(RFacts.Ask.starts(RFacts.Ask.root(a), b), Bool.not(RFacts.Ask.alike(a, b))))(Ask.starts_self(h, a)(sa))(Shared.Bool.and_both(RFacts.Ask.starts(RFacts.Ask.root(a), b), Bool.not(RFacts.Ask.alike(a, b)))(Ask.starts_to(h, a, b)(sa)(sb))(Case.not_of(RFacts.Ask.alike(a, b))(ef))))
    )
  )

# a set stays sound when it takes a fact in
def Facts.take_ok(
  +name: String,
  +s: Facts(),
  +f: Types.Fact
) -> {
  Facts.ok(name, s) == True{}: Bool
} -> {Facts.ok(name, Facts.take(name, s, f)) == True{}: Bool}:
  +h => Facts.take_by(
    t => {Facts.ok(name, t) == True{}: Bool},
    name,
    s,
    f,
    er => Trust.break_ok(name, s)(Facts.ok_never(name, s)(h)),
    er => ec => Trust.break_ok(
      name,
      Facts.add(s, f)
    )(Facts.add_no_liar(name, s, f)(Facts.ok_never(name, s)(h))(er)),
    er => ec => Facts.ok_of(
      name,
      Facts.add(s, f)
    )(
      Facts.add_no_liar(name, s, f)(Facts.ok_never(name, s)(h))(er)
    )(Facts.add_trust(name, s, f)(Facts.ok_trust(name, s)(h))(ec))
  )

# a set stays sound when it takes facts in
def Facts.take_all_ok(
  +name: String,
  +fs: List<&2, Types.Fact>,
  +s: Facts()
) -> {
  Facts.ok(name, s) == True{}: Bool
} -> {Facts.ok(name, Facts.take_all(name, fs, s)) == True{}: Bool}:
  match fs:
    case Nil{}:
      h => h
    case Con{f, rest}:
      h => Facts.take_all_ok(name, rest, Facts.take(name, s, f))(Facts.take_ok(name, s, f)(h))

# a set that took a fact in holds it, or says that the trust of the node broke
def Facts.take_has(
  +name: String,
  +s: Facts(),
  +f: Types.Fact
) -> {
  Bool.or(
    Facts.has(Facts.take(name, s, f), f),
    Trust.broken(Facts.take(name, s, f), name)
  )
    == True{}: Bool
}:
  Facts.take_by(
    t => {Bool.or(Facts.has(t, f), Trust.broken(t, name)) == True{}: Bool},
    name,
    s,
    f,
    er => Case.or_right(
      Facts.has(Trust.break(s, name), f),
      Trust.broken(Trust.break(s, name), name)
    )(Trust.break_broken(s, name)),
    er => ec => Case.or_right(
      Facts.has(Trust.break(Facts.add(s, f), name), f),
      Trust.broken(Trust.break(Facts.add(s, f), name), name)
    )(Trust.break_broken(Facts.add(s, f), name)),
    er => ec => Case.or_left(
      Facts.has(Facts.add(s, f), f),
      Trust.broken(Facts.add(s, f), name)
    )(Facts.add_has(s, f))
  )

# a set that took facts in holds each of them, while it names no liar
def Facts.take_all_has(
  +name: String,
  +fs: List<&2, Types.Fact>,
  +s: Facts(),
  +f: Types.Fact
) -> {
  Facts.liars(Facts.take_all(name, fs, s)) == []: List<&2, String>
} -> {
  List.contains(~Types.Fact, ~Coded.Fact.is_eq, fs, f) == True{}: Bool
} -> {Facts.has(Facts.take_all(name, fs, s), f) == True{}: Bool}:
  match fs:
    case Nil{}:
      hn => hin => Empty.absurd({Facts.has(s, f) == True{}: Bool}, Shared.Bool.false_ne_true(hin))
    case Con{h, rest}:
      +hn => hin => Lists.List.contains_cons_by(
        ~Types.Fact,
        ~Coded.Fact.is_eq,
        ~Coded.Fact.laws(),
        {Facts.has(Facts.take_all(name, rest, Facts.take(name, s, h)), f) == True{}: Bool},
        h,
        rest,
        f,
        hin,
        e => (
          %e: {Facts.has(Facts.take_all(name, rest, Facts.take(name, s, h)), _) == True{}: Bool}
          Case.or_by({Facts.has(Facts.take_all(name, rest, Facts.take(name, s, h)), h) == True{}: Bool}, Facts.has(Facts.take(name, s, h), h), Trust.broken(Facts.take(name, s, h), name), Facts.take_has(name, s, h), ht => Facts.wider_has(Facts.take(name, s, h), Facts.take_all(name, rest, Facts.take(name, s, h)), h)(Facts.take_all_wider(name, rest, Facts.take(name, s, h)))(ht), hb => Empty.absurd({Facts.has(Facts.take_all(name, rest, Facts.take(name, s, h)), h) == True{}: Bool}, Trust.broken_never(Facts.take_all(name, rest, Facts.take(name, s, h)), name)(Trust.wider_broken(Facts.take(name, s, h), Facts.take_all(name, rest, Facts.take(name, s, h)), name)(Facts.take_all_wider(name, rest, Facts.take(name, s, h)))(hb))(hn)))),
        c => Facts.take_all_has(name, rest, Facts.take(name, s, h), f)(hn)(c)
      )

# a set that took in the facts of another holds each change that the other
# held, while it names no liar
def Facts.take_all_holds(
  +name: String,
  +m: Facts(),
  +s: Facts(),
  +c: Types.Change
) -> {
  Facts.liars(Facts.take_all(name, Facts.list(m), s)) == []: List<&2, String>
} -> {
  Facts.holds(m, c) == True{}: Bool
} -> {Facts.holds(Facts.take_all(name, Facts.list(m), s), c) == True{}: Bool}:
  match c:
    case Types.Change.Fact{f}:
      hn => hc => Facts.take_all_has(name, Facts.list(m), s, f)(hn)(Facts.has_in(m, f)(hc))
    case Types.Change.Lie{v, st, one, two}:
      +hn => +hc => Shared.Bool.and_both(
        Bool.and(
          Facts.has(Facts.take_all(name, Facts.list(m), s), Types.Fact.Vote{v, st, one}),
          Facts.has(Facts.take_all(name, Facts.list(m), s), Types.Fact.Vote{v, st, two})
        ),
        Bool.not(Coded.Cast.is_eq(one, two))
      )(
        Shared.Bool.and_both(
          Facts.has(Facts.take_all(name, Facts.list(m), s), Types.Fact.Vote{v, st, one}),
          Facts.has(Facts.take_all(name, Facts.list(m), s), Types.Fact.Vote{v, st, two})
        )(
          Facts.take_all_has(
            name,
            Facts.list(m),
            s,
            Types.Fact.Vote{v, st, one}
          )(
            hn
          )(
            Facts.has_in(
              m,
              Types.Fact.Vote{v, st, one}
            )(
              Shared.Bool.and_true_left(
                Facts.has(m, Types.Fact.Vote{v, st, one}),
                Facts.has(m, Types.Fact.Vote{v, st, two})
              )(
                Shared.Bool.and_true_left(
                  Bool.and(
                    Facts.has(m, Types.Fact.Vote{v, st, one}),
                    Facts.has(m, Types.Fact.Vote{v, st, two})
                  ),
                  Bool.not(Coded.Cast.is_eq(one, two))
                )(hc)
              )
            )
          )
        )(
          Facts.take_all_has(
            name,
            Facts.list(m),
            s,
            Types.Fact.Vote{v, st, two}
          )(
            hn
          )(
            Facts.has_in(
              m,
              Types.Fact.Vote{v, st, two}
            )(
              Shared.Bool.and_true_right(
                Facts.has(m, Types.Fact.Vote{v, st, one}),
                Facts.has(m, Types.Fact.Vote{v, st, two})
              )(
                Shared.Bool.and_true_left(
                  Bool.and(
                    Facts.has(m, Types.Fact.Vote{v, st, one}),
                    Facts.has(m, Types.Fact.Vote{v, st, two})
                  ),
                  Bool.not(Coded.Cast.is_eq(one, two))
                )(hc)
              )
            )
          )
        )
      )(
        Shared.Bool.and_true_right(
          Bool.and(
            Facts.has(m, Types.Fact.Vote{v, st, one}),
            Facts.has(m, Types.Fact.Vote{v, st, two})
          ),
          Bool.not(Coded.Cast.is_eq(one, two))
        )(hc)
      )

# Laws of the votes of the node
# -----------------------------

# a vote that contradicts a ballot of a node for a step is a vote of the node
# for the step
def Fact.clash_cast(
  +name: String,
  +st: Types.Step,
  +pk: Types.Cast,
  g: Types.Fact
) -> {
  RFacts.Fact.clashes(
    Spec.Ballot{name, Coded.Step.words(st), Coded.Cast.words(pk)},
    g
  )
    == True{}: Bool
} -> {RFacts.Fact.is_cast(RFacts.Seat{name, st}, g) == True{}: Bool}:
  match g:
    case Types.Fact.Ask{a}:
      h => Empty.absurd({False{} == True{}: Bool}, Shared.Bool.false_ne_true(h))
    case Types.Fact.Vote{+u, +st2, +pk2}:
      +h =>
        %Texts.String.eq_sound(
          name,
          u
        )(
          Shared.Bool.and_true_left(
            String.eq(name, u),
            Bool.and(
              RFacts.Words.is_eq(Coded.Step.words(st), Coded.Step.words(st2)),
              Bool.not(RFacts.Words.is_eq(Coded.Cast.words(pk), Coded.Cast.words(pk2)))
            )
          )(h)
        ): {Bool.and(String.eq(_, name), Coded.Step.is_eq(st2, st)) == True{}: Bool}
        %Coded.Step.words_inj(
          st,
          st2
        )(
          Words.is_eq_sound(
            Coded.Step.words(st),
            Coded.Step.words(st2)
          )(
            Shared.Bool.and_second(
              String.eq(name, u),
              RFacts.Words.is_eq(Coded.Step.words(st), Coded.Step.words(st2)),
              Bool.not(RFacts.Words.is_eq(Coded.Cast.words(pk), Coded.Cast.words(pk2)))
            )(h)
          )
        ): {Bool.and(String.eq(name, name), Coded.Step.is_eq(_, st)) == True{}: Bool}
        Shared.Bool.and_both(
          String.eq(name, name),
          Coded.Step.is_eq(st, st)
        )(Texts.String.eq_refl(name))(Coded.Step.is_eq_refl(st))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# Facts.cast_refuses, with the vote that contradicts the ballot
def Facts.cast_of.at(
  +name: String,
  +s: Facts(),
  +st: Types.Step,
  +pk: Types.Cast,
  r: Exists(
    Types.Fact,
    g => {
      List.contains(~Types.Fact, ~Coded.Fact.is_eq, Facts.list(s), g) == True{}: Bool
    }
      & {
        RFacts.Fact.clashes(
          Spec.Ballot{name, Coded.Step.words(st), Coded.Cast.words(pk)},
          g
        )
          == True{}: Bool
      }
  )
) -> {Facts.cast(s, name, st) == True{}: Bool}:
  (+g, p) = r
  (c, h) = p
  Lists.List.in_some(
    ~Types.Fact,
    ~RFacts.Seat,
    ~RFacts.Fact.is_cast,
    ~Coded.Fact.is_eq,
    ~Coded.Fact.laws(),
    Facts.list(s),
    RFacts.Seat{name, st},
    g
  )(c)(Fact.clash_cast(name, st, pk, g)(h))

# a node refuses no vote of its own for a step that it holds no vote of its
# own for
def Facts.cast_refuses(
  +name: String,
  +s: Facts(),
  +st: Types.Step,
  +pk: Types.Cast
) -> {
  Facts.cast(s, name, st) == False{}: Bool
} -> {Facts.refuses(name, s, Types.Fact.Vote{name, st, pk}) == False{}: Bool}:
  hc =>
    %Lists.Bool.and_when(
      String.eq(name, name),
      u => Shared.List.some(
        ~Types.Fact,
        ~Spec.Ballot,
        ~RFacts.Fact.clashes,
        Facts.list(s),
        Spec.Ballot{name, Coded.Step.words(st), Coded.Cast.words(pk)}
      )
    ): {_ == False{}: Bool}
    %Equal.sym(
      Bool,
      Shared.List.some(
        ~Types.Fact,
        ~Spec.Ballot,
        ~RFacts.Fact.clashes,
        Facts.list(s),
        Spec.Ballot{name, Coded.Step.words(st), Coded.Cast.words(pk)}
      ),
      False{},
      Case.false_of(
        Shared.List.some(
          ~Types.Fact,
          ~Spec.Ballot,
          ~RFacts.Fact.clashes,
          Facts.list(s),
          Spec.Ballot{name, Coded.Step.words(st), Coded.Cast.words(pk)}
        )
      )(
        t => Lists.Bool.clash(
          Empty,
          Facts.cast(s, name, st),
          hc,
          Facts.cast_of.at(
            name,
            s,
            st,
            pk,
            Lists.List.some_in(
              ~Types.Fact,
              ~Spec.Ballot,
              ~RFacts.Fact.clashes,
              ~Coded.Fact.is_eq,
              ~Coded.Fact.laws(),
              Facts.list(s),
              Spec.Ballot{name, Coded.Step.words(st), Coded.Cast.words(pk)}
            )(t)
          )
        )
      )
    ): {Bool.and(String.eq(name, name), _) == False{}: Bool}
    Shared.Bool.and_false_right(String.eq(name, name))

# a set stays sound with a vote of the node for a step that it held no vote
# of the node for
def Facts.add_cast_ok(
  +name: String,
  +s: Facts(),
  +st: Types.Step,
  +pk: Types.Cast
) -> {
  Facts.ok(name, s) == True{}: Bool
} -> {
  Facts.cast(s, name, st) == False{}: Bool
} -> {Facts.ok(name, Facts.add(s, Types.Fact.Vote{name, st, pk})) == True{}: Bool}:
  +h => hc => Facts.ok_of(
    name,
    Facts.add(s, Types.Fact.Vote{name, st, pk})
  )(
    Facts.add_no_liar(
      name,
      s,
      Types.Fact.Vote{name, st, pk}
    )(Facts.ok_never(name, s)(h))(Facts.cast_refuses(name, s, st, pk)(hc))
  )(Facts.add_trust(name, s, Types.Fact.Vote{name, st, pk})(Facts.ok_trust(name, s)(h))({==}))

# Laws of the maps
# ----------------
# The code that runs holds the map of the facts (RFacts.Plain) and builds no
# proof. Each def that gives facts gives, as its map, what the code that runs
# gives of the map.

# the map of no fact is the empty map
def Facts.new_crit() -> {Facts.crit(Facts.new()) == RFacts.Facts.new(): RFacts.Plain()}:
  {==}

# the map of s with f is the map of s with f
def Facts.add_crit(
  -s: Facts(),
  -f: Types.Fact
) -> {Facts.crit(Facts.add(s, f)) == RFacts.Facts.add(Facts.crit(s), f): RFacts.Plain()}:
  {==}

# the map of s where the trust broke is the map of s where the trust broke
def Trust.break_crit(
  -s: Facts(),
  -name: String
) -> {Facts.crit(Trust.break(s, name)) == RFacts.Trust.break(Facts.crit(s), name): RFacts.Plain()}:
  {==}

# the map of what a take gives, whatever its two tests b1 and b2 say
def Facts.take_crit.of(
  b1: Bool,
  b2: Bool,
  -name: String,
  -s: Facts(),
  -f: Types.Fact
) -> {
  Facts.crit(
    Shared.Bool.when(
      Facts(),
      b1,
      u => Trust.break(s, name),
      u => Shared.Bool.when(
        Facts(),
        b2,
        u => Trust.break(Facts.add(s, f), name),
        u => Facts.add(s, f)
      )
    )
  )
    == Shared.Bool.when(
      RFacts.Plain(),
      b1,
      u => RFacts.Trust.break(Facts.crit(s), name),
      u => Shared.Bool.when(
        RFacts.Plain(),
        b2,
        u => RFacts.Trust.break(RFacts.Facts.add(Facts.crit(s), f), name),
        u => RFacts.Facts.add(Facts.crit(s), f)
      )
    ): RFacts.Plain()
}:
  match b1 b2:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# the map of s after the node takes f in is what the code that runs gives
def Facts.take_crit(
  +name: String,
  +s: Facts(),
  +f: Types.Fact
) -> {
  Facts.crit(Facts.take(name, s, f)) == RFacts.Facts.take(name, Facts.crit(s), f): RFacts.Plain()
}:
  Facts.take_crit.of(Facts.refuses(name, s, f), RFacts.Fact.collided(Facts.list(s), f), name, s, f)

# the map of s after the node takes fs in is what the code that runs gives
def Facts.take_all_crit(
  +name: String,
  fs: List<&2, Types.Fact>,
  +s: Facts()
) -> {
  Facts.crit(
    Facts.take_all(name, fs, s)
  )
    == RFacts.Facts.take_all(name, fs, Facts.crit(s)): RFacts.Plain()
}:
  match fs:
    case Nil{}:
      {==}
    case Con{+f, rest}:
      %Facts.take_crit(
        name,
        s,
        f
      ): {
        Facts.crit(
          Facts.take_all(name, rest, Facts.take(name, s, f))
        )
          == RFacts.Facts.take_all(name, rest, _): RFacts.Plain()
      }
      Facts.take_all_crit(name, rest, Facts.take(name, s, f))

# the map of s after the node takes a request in is what the code that runs
# gives
def Facts.ask_crit(
  +name: String,
  +s: Facts(),
  i: Ledgers.Id,
  r: Spec.Request
) -> {
  Facts.crit(
    Facts.ask(name, s, i, r)
  )
    == RFacts.Facts.ask(name, Facts.crit(s), i, r): RFacts.Plain()
}:
  Facts.take_crit(name, s, Types.Fact.Ask{Facts.asked(s, i, r)})

# Facts that a set holds
# ----------------------
# A node that takes in a fact that it holds stays as it is: what a Sync
# costs is what it brings.

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof does not run
# a set with a fact that it holds is the set
def Facts.add_held(
  +s: Facts(),
  +f: Types.Fact
) -> {Facts.has(s, f) == True{}: Bool} -> {Facts.add(s, f) == s: Facts()}:
  +hf => Facts.ext(
    Facts.add(s, f),
    s
  )(
    +x => Equal.trans(
      Bool,
      Facts.has(Facts.add(s, f), x),
      Bool.or(Coded.Fact.is_eq(x, f), Facts.has(s, x)),
      Facts.has(s, x),
      Facts.has_add(s, f, x),
      Lists.Bool.by(
        z => {Bool.or(z, Facts.has(s, x)) == Facts.has(s, x): Bool},
        Coded.Fact.is_eq(x, f),
        et => Lists.Equal.to(
          Types.Fact,
          z => {True{} == Facts.has(s, z): Bool},
          f,
          x,
          Equal.sym(Types.Fact, x, f, Coded.Fact.is_eq_sound(x, f)(et)),
          Equal.sym(Bool, Facts.has(s, f), True{}, hf)
        ),
        ef => {==}
      )
    )
  )

# a set that says that the trust of a node broke is the set where it broke
def Trust.break_held(
  +s: Facts(),
  +name: String
) -> {Trust.broken(s, name) == True{}: Bool} -> {Trust.break(s, name) == s: Facts()}:
  +h => (
    %Equal.sym(Facts(), Facts.add(s, RFacts.Trust.one(name)), s, Facts.add_held(s, RFacts.Trust.one(name))(Shared.Bool.and_true_left(Facts.has(s, RFacts.Trust.one(name)), Facts.has(s, RFacts.Trust.two(name)))(h))): {Facts.add(_, RFacts.Trust.two(name)) == s: Facts()}
    Facts.add_held(s, RFacts.Trust.two(name))(Shared.Bool.and_true_right(Facts.has(s, RFacts.Trust.one(name)), Facts.has(s, RFacts.Trust.two(name)))(h)))

# Facts.refuses_held, with a vote g of the set that contradicts the vote
def Facts.refuses_held.fin(
  +name: String,
  +s: Facts(),
  +v: String,
  +st: Types.Step,
  +pk: Types.Cast,
  +g: Types.Fact,
  ok: {Facts.ok(name, s) == True{}: Bool},
  hf: {Facts.has(s, Types.Fact.Vote{v, st, pk}) == True{}: Bool},
  ev: {String.eq(v, name) == True{}: Bool},
  hg: {Facts.has(s, g) == True{}: Bool}
) -> {
  RFacts.Fact.clashes(Spec.Ballot{v, Coded.Step.words(st), Coded.Cast.words(pk)}, g) == True{}: Bool
} -> Empty:
  match g:
    case Types.Fact.Ask{a}:
      h => Shared.Bool.false_ne_true(h)
    case Types.Fact.Vote{+w, +st2, +pk2}:
      +h => Lists.Bool.clash(
        Empty,
        List.contains(~String, ~String.eq, Facts.liars(s), name),
        Facts.ok_never(name, s)(ok),
        Lists.Equal.to(
          String,
          z => {List.contains(~String, ~String.eq, Facts.liars(s), z) == True{}: Bool},
          v,
          name,
          Texts.String.eq_sound(v, name)(ev),
          Facts.liars_in(
            s,
            Types.Fact.Vote{v, st, pk},
            Types.Fact.Vote{w, st2, pk2},
            v,
            Coded.Step.words(st),
            Coded.Cast.words(pk),
            Coded.Cast.words(pk2)
          )(hf)(hg)({==})(
            %Texts.String.eq_sound(v, w)(Shared.Bool.and_true_left(String.eq(v, w), Bool.and(RFacts.Words.is_eq(Coded.Step.words(st), Coded.Step.words(st2)), Bool.not(RFacts.Words.is_eq(Coded.Cast.words(pk), Coded.Cast.words(pk2)))))(h)): {Some{Spec.Ballot{_, Coded.Step.words(st2), Coded.Cast.words(pk2)}} == Some{Spec.Ballot{v, Coded.Step.words(st), Coded.Cast.words(pk2)}}: Maybe<&2, Spec.Ballot>}
            %Words.is_eq_sound(Coded.Step.words(st), Coded.Step.words(st2))(Shared.Bool.and_true_left(RFacts.Words.is_eq(Coded.Step.words(st), Coded.Step.words(st2)), Bool.not(RFacts.Words.is_eq(Coded.Cast.words(pk), Coded.Cast.words(pk2))))(Shared.Bool.and_true_right(String.eq(v, w), Bool.and(RFacts.Words.is_eq(Coded.Step.words(st), Coded.Step.words(st2)), Bool.not(RFacts.Words.is_eq(Coded.Cast.words(pk), Coded.Cast.words(pk2)))))(h))): {Some{Spec.Ballot{v, _, Coded.Cast.words(pk2)}} == Some{Spec.Ballot{v, Coded.Step.words(st), Coded.Cast.words(pk2)}}: Maybe<&2, Spec.Ballot>}
            {==})(
            Shared.Bool.and_true_right(
              RFacts.Words.is_eq(Coded.Step.words(st), Coded.Step.words(st2)),
              Bool.not(RFacts.Words.is_eq(Coded.Cast.words(pk), Coded.Cast.words(pk2)))
            )(
              Shared.Bool.and_true_right(
                String.eq(v, w),
                Bool.and(
                  RFacts.Words.is_eq(Coded.Step.words(st), Coded.Step.words(st2)),
                  Bool.not(RFacts.Words.is_eq(Coded.Cast.words(pk), Coded.Cast.words(pk2)))
                )
              )(h)
            )
          )
        )
      )

# Facts.refuses_held, with the member of the set that contradicts the vote
def Facts.refuses_held.at(
  +name: String,
  +s: Facts(),
  +v: String,
  +st: Types.Step,
  +pk: Types.Cast,
  ok: {Facts.ok(name, s) == True{}: Bool},
  hf: {Facts.has(s, Types.Fact.Vote{v, st, pk}) == True{}: Bool},
  ev: {String.eq(v, name) == True{}: Bool},
  r: Exists(
    Types.Fact,
    g => {
      List.contains(~Types.Fact, ~Coded.Fact.is_eq, Facts.list(s), g) == True{}: Bool
    }
      & {
        RFacts.Fact.clashes(
          Spec.Ballot{v, Coded.Step.words(st), Coded.Cast.words(pk)},
          g
        )
          == True{}: Bool
      }
  )
) -> Empty:
  (+g, p) = r
  (c, h) = p
  Facts.refuses_held.fin(name, s, v, st, pk, g, ok, hf, ev, Facts.in_has(s, g)(c))(h)

# a node refuses no fact that it holds, in a set that is sound for it
def Facts.refuses_held(
  +name: String,
  +s: Facts(),
  +f: Types.Fact
) -> {
  Facts.ok(name, s) == True{}: Bool
} -> {Facts.has(s, f) == True{}: Bool} -> {Facts.refuses(name, s, f) == False{}: Bool}:
  match f:
    case Types.Fact.Ask{a}:
      ok => hf => {==}
    case Types.Fact.Vote{+v, +st, +pk}:
      ok => hf => Case.false_of(
        Facts.refuses(name, s, Types.Fact.Vote{v, st, pk})
      )(
        Lists.Bool.by(
          z => {
            Shared.Bool.when(
              Bool,
              z,
              u => Shared.List.some(
                ~Types.Fact,
                ~Spec.Ballot,
                ~RFacts.Fact.clashes,
                Facts.list(s),
                Spec.Ballot{v, Coded.Step.words(st), Coded.Cast.words(pk)}
              ),
              u => False{}
            )
              == True{}: Bool
          } -> Empty,
          String.eq(v, name),
          et => e => Facts.refuses_held.at(
            name,
            s,
            v,
            st,
            pk,
            ok,
            hf,
            et,
            Lists.List.some_in(
              ~Types.Fact,
              ~Spec.Ballot,
              ~RFacts.Fact.clashes,
              ~Coded.Fact.is_eq,
              ~Coded.Fact.laws(),
              Facts.list(s),
              Spec.Ballot{v, Coded.Step.words(st), Coded.Cast.words(pk)}
            )(e)
          ),
          ef => e => Shared.Bool.false_ne_true(e)
        )
      )

# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the asks of a set collide, when a fact that it holds collides with them
def Facts.collided_held(
  +s: Facts(),
  +f: Types.Fact
) -> {
  Facts.has(s, f) == True{}: Bool
} -> {RFacts.Fact.collided(Facts.list(s), f) == True{}: Bool} -> {Facts.collide(s) == True{}: Bool}:
  hf => hc => Lists.List.in_some(
    ~Types.Fact,
    ~List<&2, Types.Fact>,
    ~RFacts.Fact.collided,
    ~Coded.Fact.is_eq,
    ~Coded.Fact.laws(),
    Facts.list(s),
    Facts.list(s),
    f
  )(Facts.has_in(s, f)(hf))(hc)

# b is true, when c is, and b or not c
def Case.or_not(
  c: Bool,
  b: Bool
) -> {c == True{}: Bool} -> {Bool.or(Bool.not(c), b) == True{}: Bool} -> {b == True{}: Bool}:
  match c:
    case True{}:
      hc => h => h
    case False{}:
      hc => h => Empty.absurd({b == True{}: Bool}, Shared.Bool.false_ne_true(hc))

# a node that takes in a fact that it holds stays as it is, when its set is
# sound for it
def Facts.take_held(
  +name: String,
  +s: Facts(),
  +f: Types.Fact
) -> {
  Facts.ok(name, s) == True{}: Bool
} -> {Facts.has(s, f) == True{}: Bool} -> {Facts.take(name, s, f) == s: Facts()}:
  +ok => +hf => Facts.take_by(
    t => {t == s: Facts()},
    name,
    s,
    f,
    er => Lists.Bool.clash(
      {Trust.break(s, name) == s: Facts()},
      Facts.refuses(name, s, f),
      Facts.refuses_held(name, s, f)(ok)(hf),
      er
    ),
    er => ec => (
      %Equal.sym(Facts(), Facts.add(s, f), s, Facts.add_held(s, f)(hf)): {Trust.break(_, name) == s: Facts()}
      Trust.break_held(s, name)(Case.or_not(Facts.collide(s), Trust.broken(s, name))(Facts.collided_held(s, f)(hf)(ec))(Facts.ok_trust(name, s)(ok)))),
    er => ec => Facts.add_held(s, f)(hf)
  )

# a node that takes in a vote of another voter holds its set with the vote
def Facts.take_vote(
  +name: String,
  +s: Facts(),
  +v: String,
  +st: Types.Step,
  +x: Types.Cast
) -> {
  String.eq(v, name) == False{}: Bool
} -> {
  Facts.take(name, s, Types.Fact.Vote{v, st, x}) == Facts.add(s, Types.Fact.Vote{v, st, x}): Facts()
}:
  h => Facts.take_by(
    t => {t == Facts.add(s, Types.Fact.Vote{v, st, x}): Facts()},
    name,
    s,
    Types.Fact.Vote{v, st, x},
    er => Lists.Bool.clash(
      {Trust.break(s, name) == Facts.add(s, Types.Fact.Vote{v, st, x}): Facts()},
      Facts.refuses(name, s, Types.Fact.Vote{v, st, x}),
      Facts.refuses_other(name, s, v, st, x)(h),
      er
    ),
    er => ec => Empty.absurd(
      {
        Trust.break(
          Facts.add(s, Types.Fact.Vote{v, st, x}),
          name
        )
          == Facts.add(s, Types.Fact.Vote{v, st, x}): Facts()
      },
      Shared.Bool.false_ne_true(ec)
    ),
    er => ec => {==}
  )
