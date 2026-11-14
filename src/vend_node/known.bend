import Base
import ../shared/shared/ledger.bend as Ledgers
import ../shared/shared/shared/shared/crit.bend as Crits
import ../shared/shared/shared/shared/crit_order.bend as Orders
import ../shared/shared/shared/shared/hash.bend as Hashes
import ../shared/shared/shared/shared/shared.bend as Shared
import ../shared/shared/shared/text.bend as Texts
import ./codes.bend as Coded
import ./content.bend as Contents
import ./facts.bend as Facts
import ./groups.bend as Groups
import ./lines.bend as Lines
import ./mergers.bend as Mergers
import ./merges.bend as Merges
import ./moves.bend as Moves
import ./reads.bend as Reads
import ./run/answers.bend as RAnswers
import ./run/content.bend as RContents
import ./run/facts.bend as RFacts
import ./run/files.bend as RFiles
import ./run/known.bend as RKnown
import ./run/lines.bend as RLines
import ./run/rounds.bend as RRounds
import ./run/work.bend as RWorks
import ./shared/lists.bend as Lists
import ./shared/set.bend as Sets
import ./spec.bend as Spec
import ./stays.bend as Stays
import ./tops.bend as Newest
import ./types.bend as Types
import ./versions.bend as Versions

# Known states: laws
# ------------------
# A node keeps the states of the lines that it has read in a table
# (run/known.bend). Here: a table that is right for the facts
# (RContents.Known.ok) changes no read of a line, and it stays right when the
# node learns a state, takes in an ask that starts no store, or casts a vote.

# Same states
# -----------

# Entry.same is True for an entry and itself
def Entry.same_refl(a: Types.Entry) -> {RKnown.Entry.same(a, a) == True{}: Bool}:
  match a:
    case Types.Entry{+p, +k}:
      Shared.Bool.and_both(
        Coded.Pick.is_eq(p, p),
        Nat.is_eq(k, k)
      )(Coded.Pick.is_eq_refl(p))(Shared.Nat.is_eq_refl(k))

# Entry.same is True only for equal entries
def Entry.same_sound(
  a: Types.Entry,
  b: Types.Entry
) -> {RKnown.Entry.same(a, b) == True{}: Bool} -> {a == b: Types.Entry}:
  match a b:
    case Types.Entry{+p1, +k1} Types.Entry{+p2, +k2}:
      +h => (
        %Coded.Pick.is_eq_sound(p1, p2)(Shared.Bool.and_true_left(Coded.Pick.is_eq(p1, p2), Nat.is_eq(k1, k2))(h)): {Types.Entry{p1, k1} == Types.Entry{_, k2}: Types.Entry}
        %Shared.Nat.is_eq_sound(k1, k2)(Shared.Bool.and_true_right(Coded.Pick.is_eq(p1, p2), Nat.is_eq(k1, k2))(h)): {Types.Entry{p1, k1} == Types.Entry{p1, _}: Types.Entry}
        {==})

# Entries.same is True for versions and themselves
def Entries.same_refl(xs: List<&2, Types.Entry>) -> {RKnown.Entries.same(xs, xs) == True{}: Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      Shared.Bool.and_both(
        RKnown.Entry.same(x, x),
        RKnown.Entries.same(r, r)
      )(Entry.same_refl(x))(Entries.same_refl(r))

# Entries.same is True only for equal versions
def Entries.same_sound(
  xs: List<&2, Types.Entry>,
  ys: List<&2, Types.Entry>
) -> {RKnown.Entries.same(xs, ys) == True{}: Bool} -> {xs == ys: List<&2, Types.Entry>}:
  match xs ys:
    case Nil{} Nil{}:
      h => {==}
    case Nil{} Con{y, yr}:
      h => Empty.absurd({Nil{} == Con{y, yr}: List<&2, Types.Entry>}, Shared.Bool.false_ne_true(h))
    case Con{x, xr} Nil{}:
      h => Empty.absurd({Con{x, xr} == Nil{}: List<&2, Types.Entry>}, Shared.Bool.false_ne_true(h))
    case Con{+x, +xr} Con{+y, +yr}:
      +h => (
        %Entry.same_sound(x, y)(Shared.Bool.and_true_left(RKnown.Entry.same(x, y), RKnown.Entries.same(xr, yr))(h)): {Con{x, xr} == Con{_, yr}: List<&2, Types.Entry>}
        %Entries.same_sound(xr, yr)(Shared.Bool.and_true_right(RKnown.Entry.same(x, y), RKnown.Entries.same(xr, yr))(h)): {Con{x, xr} == Con{x, _}: List<&2, Types.Entry>}
        {==})

# State.same is True for a state and itself
def State.same_refl(a: RLines.State) -> {RKnown.State.same(a, a) == True{}: Bool}:
  match a:
    case RLines.State{+vs, +k}:
      Shared.Bool.and_both(
        RKnown.Entries.same(vs, vs),
        Nat.is_eq(k, k)
      )(Entries.same_refl(vs))(Shared.Nat.is_eq_refl(k))

# State.same is True only for equal states
def State.same_sound(
  a: RLines.State,
  b: RLines.State
) -> {RKnown.State.same(a, b) == True{}: Bool} -> {a == b: RLines.State}:
  match a b:
    case RLines.State{+v1, +k1} RLines.State{+v2, +k2}:
      +h => (
        %Entries.same_sound(v1, v2)(Shared.Bool.and_true_left(RKnown.Entries.same(v1, v2), Nat.is_eq(k1, k2))(h)): {RLines.State{v1, k1} == RLines.State{_, k2}: RLines.State}
        %Shared.Nat.is_eq_sound(k1, k2)(Shared.Bool.and_true_right(RKnown.Entries.same(v1, v2), Nat.is_eq(k1, k2))(h)): {RLines.State{v1, k1} == RLines.State{v1, _}: RLines.State}
        {==})

# a state that fits st is st
def State.fits_sound(
  m: Maybe<&2, RLines.State>,
  +st: RLines.State
) -> {RKnown.State.fits(m, st) == True{}: Bool} -> {m == Some{st}: Maybe<&2, RLines.State>}:
  match m:
    case None{}:
      h => Empty.absurd({None{} == Some{st}: Maybe<&2, RLines.State>}, Shared.Bool.false_ne_true(h))
    case Some{+x}:
      h => Equal.cong(
        RLines.State,
        Maybe<&2, RLines.State>,
        y => Some{y},
        x,
        st,
        State.same_sound(x, st)(h)
      )

# the state st fits what is st
def State.fits_of(
  m: Maybe<&2, RLines.State>,
  +st: RLines.State
) -> {m == Some{st}: Maybe<&2, RLines.State>} -> {RKnown.State.fits(m, st) == True{}: Bool}:
  e => (
    %Equal.sym(Maybe<&2, RLines.State>, m, Some{st}, e): {RKnown.State.fits(_, st) == True{}: Bool}
    State.same_refl(st))

# Same contents
# -------------

# Files.Item.same is True for a file and itself
def Item.same_refl(a: RFiles.Files.Item) -> {RFiles.Files.Item.same(a, a) == True{}: Bool}:
  match a:
    case RFiles.Files.Item{+p, +ws}:
      Shared.Bool.and_both(
        String.eq(p, p),
        Crits.Key.is_eq(ws, ws)
      )(Texts.String.eq_refl(p))(Crits.Key.is_eq_refl(ws))

# Files.Item.same is True only for equal files
def Item.same_sound(
  a: RFiles.Files.Item,
  b: RFiles.Files.Item
) -> {RFiles.Files.Item.same(a, b) == True{}: Bool} -> {a == b: RFiles.Files.Item}:
  match a b:
    case RFiles.Files.Item{+p, +ws} RFiles.Files.Item{+q, +vs}:
      +h => (
        %Texts.String.eq_sound(p, q)(Shared.Bool.and_true_left(String.eq(p, q), Crits.Key.is_eq(ws, vs))(h)): {RFiles.Files.Item{p, ws} == RFiles.Files.Item{_, vs}: RFiles.Files.Item}
        %Crits.Key.is_eq_sound(ws, vs)(Shared.Bool.and_true_right(String.eq(p, q), Crits.Key.is_eq(ws, vs))(h)): {RFiles.Files.Item{p, ws} == RFiles.Files.Item{p, _}: RFiles.Files.Item}
        {==})

# a file, if any, is the same as itself
def End.same_refl(
  e: Maybe<&2, RFiles.Files.Item>
) -> {Shared.Maybe.is_eq(~RFiles.Files.Item, ~RFiles.Files.Item.same, e, e) == True{}: Bool}:
  match e:
    case None{}:
      {==}
    case Some{v}:
      Item.same_refl(v)

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof does not run
# bend-lint: expect-begin bend-lint-rules/performance/missed_fork@hint -- a proof does not run
# Files.Crit.same is True for a map and itself
def Crit.same_refl(
  a: Crits.Crit<RFiles.Files.Item>
) -> {RFiles.Files.Crit.same(a, a) == True{}: Bool}:
  match a:
    case Crits.Crit.Tip{}:
      {==}
    case Crits.Crit.Leaf{+k, +v}:
      Shared.Bool.and_both(
        Crits.Key.is_eq(k, k),
        RFiles.Files.Item.same(v, v)
      )(Crits.Key.is_eq_refl(k))(Item.same_refl(v))
    case Crits.Crit.Fork{+r, +p, +e, +z, +o}:
      Shared.Bool.and_both(
        Crits.Key.is_eq(r, r),
        Bool.and(
          Nat.is_eq(p, p),
          Bool.and(
            Shared.Maybe.is_eq(~RFiles.Files.Item, ~RFiles.Files.Item.same, e, e),
            Bool.and(RFiles.Files.Crit.same(z, z), RFiles.Files.Crit.same(o, o))
          )
        )
      )(
        Crits.Key.is_eq_refl(r)
      )(
        Shared.Bool.and_both(
          Nat.is_eq(p, p),
          Bool.and(
            Shared.Maybe.is_eq(~RFiles.Files.Item, ~RFiles.Files.Item.same, e, e),
            Bool.and(RFiles.Files.Crit.same(z, z), RFiles.Files.Crit.same(o, o))
          )
        )(
          Shared.Nat.is_eq_refl(p)
        )(
          Shared.Bool.and_both(
            Shared.Maybe.is_eq(~RFiles.Files.Item, ~RFiles.Files.Item.same, e, e),
            Bool.and(RFiles.Files.Crit.same(z, z), RFiles.Files.Crit.same(o, o))
          )(
            End.same_refl(e)
          )(
            Shared.Bool.and_both(
              RFiles.Files.Crit.same(z, z),
              RFiles.Files.Crit.same(o, o)
            )(Crit.same_refl(z))(Crit.same_refl(o))
          )
        )
      )
# bend-lint: expect-end bend-lint-rules/performance/missed_fork@hint

# Files.Crit.same is True only for equal maps
def Crit.same_sound(
  a: Crits.Crit<RFiles.Files.Item>,
  b: Crits.Crit<RFiles.Files.Item>
) -> {RFiles.Files.Crit.same(a, b) == True{}: Bool} -> {a == b: Crits.Crit<RFiles.Files.Item>}:
  match a b:
    case Crits.Crit.Tip{} Crits.Crit.Tip{}:
      h => {==}
    case Crits.Crit.Tip{} Crits.Crit.Leaf{k2, v2}:
      h => Empty.absurd(
        {Crits.Crit.Tip{} == Crits.Crit.Leaf{k2, v2}: Crits.Crit<RFiles.Files.Item>},
        Shared.Bool.false_ne_true(h)
      )
    case Crits.Crit.Tip{} Crits.Crit.Fork{r2, p2, e2, z2, o2}:
      h => Empty.absurd(
        {Crits.Crit.Tip{} == Crits.Crit.Fork{r2, p2, e2, z2, o2}: Crits.Crit<RFiles.Files.Item>},
        Shared.Bool.false_ne_true(h)
      )
    case Crits.Crit.Leaf{k1, v1} Crits.Crit.Tip{}:
      h => Empty.absurd(
        {Crits.Crit.Leaf{k1, v1} == Crits.Crit.Tip{}: Crits.Crit<RFiles.Files.Item>},
        Shared.Bool.false_ne_true(h)
      )
    case Crits.Crit.Leaf{k1, v1} Crits.Crit.Fork{r2, p2, e2, z2, o2}:
      h => Empty.absurd(
        {
          Crits.Crit.Leaf{
            k1,
            v1
          }
            == Crits.Crit.Fork{r2, p2, e2, z2, o2}: Crits.Crit<RFiles.Files.Item>
        },
        Shared.Bool.false_ne_true(h)
      )
    case Crits.Crit.Fork{r1, p1, e1, z1, o1} Crits.Crit.Tip{}:
      h => Empty.absurd(
        {Crits.Crit.Fork{r1, p1, e1, z1, o1} == Crits.Crit.Tip{}: Crits.Crit<RFiles.Files.Item>},
        Shared.Bool.false_ne_true(h)
      )
    case Crits.Crit.Fork{r1, p1, e1, z1, o1} Crits.Crit.Leaf{k2, v2}:
      h => Empty.absurd(
        {
          Crits.Crit.Fork{
            r1,
            p1,
            e1,
            z1,
            o1
          }
            == Crits.Crit.Leaf{k2, v2}: Crits.Crit<RFiles.Files.Item>
        },
        Shared.Bool.false_ne_true(h)
      )
    case Crits.Crit.Leaf{+k1, +v1} Crits.Crit.Leaf{+k2, +v2}:
      +h => (
        %Crits.Key.is_eq_sound(k1, k2)(Shared.Bool.and_true_left(Crits.Key.is_eq(k1, k2), RFiles.Files.Item.same(v1, v2))(h)): {Crits.Crit.Leaf{k1, v1} == Crits.Crit.Leaf{_, v2}: Crits.Crit<RFiles.Files.Item>}
        %Item.same_sound(v1, v2)(Shared.Bool.and_true_right(Crits.Key.is_eq(k1, k2), RFiles.Files.Item.same(v1, v2))(h)): {Crits.Crit.Leaf{k1, v1} == Crits.Crit.Leaf{k1, _}: Crits.Crit<RFiles.Files.Item>}
        {==})
    case Crits.Crit.Fork{+r1, +p1, +e1, +z1, +o1} Crits.Crit.Fork{+r2, +p2, +e2, +z2, +o2}:
      +h => (
        %Crits.Key.is_eq_sound(r1, r2)(Shared.Bool.and_true_left(Crits.Key.is_eq(r1, r2), Bool.and(Nat.is_eq(p1, p2), Bool.and(Shared.Maybe.is_eq(~RFiles.Files.Item, ~RFiles.Files.Item.same, e1, e2), Bool.and(RFiles.Files.Crit.same(z1, z2), RFiles.Files.Crit.same(o1, o2)))))(h)): {Crits.Crit.Fork{r1, p1, e1, z1, o1} == Crits.Crit.Fork{_, p2, e2, z2, o2}: Crits.Crit<RFiles.Files.Item>}
        %Shared.Nat.is_eq_sound(p1, p2)(Shared.Bool.and_true_left(Nat.is_eq(p1, p2), Bool.and(Shared.Maybe.is_eq(~RFiles.Files.Item, ~RFiles.Files.Item.same, e1, e2), Bool.and(RFiles.Files.Crit.same(z1, z2), RFiles.Files.Crit.same(o1, o2))))(Shared.Bool.and_true_right(Crits.Key.is_eq(r1, r2), Bool.and(Nat.is_eq(p1, p2), Bool.and(Shared.Maybe.is_eq(~RFiles.Files.Item, ~RFiles.Files.Item.same, e1, e2), Bool.and(RFiles.Files.Crit.same(z1, z2), RFiles.Files.Crit.same(o1, o2)))))(h))): {Crits.Crit.Fork{r1, p1, e1, z1, o1} == Crits.Crit.Fork{r1, _, e2, z2, o2}: Crits.Crit<RFiles.Files.Item>}
        %Shared.Maybe.is_eq_sound(~RFiles.Files.Item, ~RFiles.Files.Item.same, x => y => Item.same_sound(x, y), e1, e2)(Shared.Bool.and_true_left(Shared.Maybe.is_eq(~RFiles.Files.Item, ~RFiles.Files.Item.same, e1, e2), Bool.and(RFiles.Files.Crit.same(z1, z2), RFiles.Files.Crit.same(o1, o2)))(Shared.Bool.and_true_right(Nat.is_eq(p1, p2), Bool.and(Shared.Maybe.is_eq(~RFiles.Files.Item, ~RFiles.Files.Item.same, e1, e2), Bool.and(RFiles.Files.Crit.same(z1, z2), RFiles.Files.Crit.same(o1, o2))))(Shared.Bool.and_true_right(Crits.Key.is_eq(r1, r2), Bool.and(Nat.is_eq(p1, p2), Bool.and(Shared.Maybe.is_eq(~RFiles.Files.Item, ~RFiles.Files.Item.same, e1, e2), Bool.and(RFiles.Files.Crit.same(z1, z2), RFiles.Files.Crit.same(o1, o2)))))(h)))): {Crits.Crit.Fork{r1, p1, e1, z1, o1} == Crits.Crit.Fork{r1, p1, _, z2, o2}: Crits.Crit<RFiles.Files.Item>}
        %Crit.same_sound(z1, z2)(Shared.Bool.and_true_left(RFiles.Files.Crit.same(z1, z2), RFiles.Files.Crit.same(o1, o2))(Shared.Bool.and_true_right(Shared.Maybe.is_eq(~RFiles.Files.Item, ~RFiles.Files.Item.same, e1, e2), Bool.and(RFiles.Files.Crit.same(z1, z2), RFiles.Files.Crit.same(o1, o2)))(Shared.Bool.and_true_right(Nat.is_eq(p1, p2), Bool.and(Shared.Maybe.is_eq(~RFiles.Files.Item, ~RFiles.Files.Item.same, e1, e2), Bool.and(RFiles.Files.Crit.same(z1, z2), RFiles.Files.Crit.same(o1, o2))))(Shared.Bool.and_true_right(Crits.Key.is_eq(r1, r2), Bool.and(Nat.is_eq(p1, p2), Bool.and(Shared.Maybe.is_eq(~RFiles.Files.Item, ~RFiles.Files.Item.same, e1, e2), Bool.and(RFiles.Files.Crit.same(z1, z2), RFiles.Files.Crit.same(o1, o2)))))(h))))): {Crits.Crit.Fork{r1, p1, e1, z1, o1} == Crits.Crit.Fork{r1, p1, e1, _, o2}: Crits.Crit<RFiles.Files.Item>}
        %Crit.same_sound(o1, o2)(Shared.Bool.and_true_right(RFiles.Files.Crit.same(z1, z2), RFiles.Files.Crit.same(o1, o2))(Shared.Bool.and_true_right(Shared.Maybe.is_eq(~RFiles.Files.Item, ~RFiles.Files.Item.same, e1, e2), Bool.and(RFiles.Files.Crit.same(z1, z2), RFiles.Files.Crit.same(o1, o2)))(Shared.Bool.and_true_right(Nat.is_eq(p1, p2), Bool.and(Shared.Maybe.is_eq(~RFiles.Files.Item, ~RFiles.Files.Item.same, e1, e2), Bool.and(RFiles.Files.Crit.same(z1, z2), RFiles.Files.Crit.same(o1, o2))))(Shared.Bool.and_true_right(Crits.Key.is_eq(r1, r2), Bool.and(Nat.is_eq(p1, p2), Bool.and(Shared.Maybe.is_eq(~RFiles.Files.Item, ~RFiles.Files.Item.same, e1, e2), Bool.and(RFiles.Files.Crit.same(z1, z2), RFiles.Files.Crit.same(o1, o2)))))(h))))): {Crits.Crit.Fork{r1, p1, e1, z1, o1} == Crits.Crit.Fork{r1, p1, e1, z1, _}: Crits.Crit<RFiles.Files.Item>}
        {==})
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# Files.same is True for a content and itself
def Files.same_refl(a: RFiles.Files()) -> {RFiles.Files.same(a, a) == True{}: Bool}:
  match a:
    case RFiles.Files{x}:
      Crit.same_refl(x)

# Files.same is True only for equal contents
def Files.same_sound(
  a: RFiles.Files(),
  b: RFiles.Files()
) -> {RFiles.Files.same(a, b) == True{}: Bool} -> {a == b: RFiles.Files()}:
  match a b:
    case RFiles.Files{x} RFiles.Files{y}:
      h => Equal.cong(
        Crits.Crit<RFiles.Files.Item>,
        RFiles.Files(),
        t => RFiles.Files{t},
        x,
        y,
        Crit.same_sound(x, y)(h)
      )

# a content that fits x is x
def Files.fits_sound(
  m: Maybe<&2, RFiles.Files()>,
  +x: RFiles.Files()
) -> {RFiles.Files.fits(m, x) == True{}: Bool} -> {m == Some{x}: Maybe<&2, RFiles.Files()>}:
  match m:
    case None{}:
      h => Empty.absurd(
        {None{} == Some{x}: Maybe<&2, RFiles.Files()>},
        Shared.Bool.false_ne_true(h)
      )
    case Some{+y}:
      h => Equal.cong(
        RFiles.Files(),
        Maybe<&2, RFiles.Files()>,
        t => Some{t},
        y,
        x,
        Files.same_sound(y, x)(h)
      )

# the content x fits what is x
def Files.fits_of(
  m: Maybe<&2, RFiles.Files()>,
  +x: RFiles.Files()
) -> {m == Some{x}: Maybe<&2, RFiles.Files()>} -> {RFiles.Files.fits(m, x) == True{}: Bool}:
  e => (
    %Equal.sym(Maybe<&2, RFiles.Files()>, m, Some{x}, e): {RFiles.Files.fits(_, x) == True{}: Bool}
    Files.same_refl(x))

# What a right table holds
# ------------------------

# no side of a false or is true
def Bool.or_false_left(
  a: Bool,
  b: Bool
) -> {Bool.or(a, b) == False{}: Bool} -> {a == False{}: Bool}:
  match a:
    case True{}:
      h => h
    case False{}:
      h => {==}

# no side of a false or is true
def Bool.or_false_right(
  a: Bool,
  b: Bool
) -> {Bool.or(a, b) == False{}: Bool} -> {b == False{}: Bool}:
  match a:
    case True{}:
      h => Empty.absurd({b == False{}: Bool}, Shared.Bool.true_ne_false(h))
    case False{}:
      h => h

# Known ids
# ---------

# the laws of Id.is_eq
def Id.laws() -> Shared.Eq.Laws(Ledgers.Id, Ledgers.Id.is_eq):
  (Ledgers.Id.is_eq_refl, Ledgers.Id.is_eq_sound)

# Found.same is True for a version and itself
def Found.same_refl(a: RKnown.Found) -> {RKnown.Found.same(a, a) == True{}: Bool}:
  match a:
    case RKnown.Found{+n, +e}:
      Shared.Bool.and_both(
        Nat.is_eq(n, n),
        RKnown.Entry.same(e, e)
      )(Shared.Nat.is_eq_refl(n))(Entry.same_refl(e))

# Found.same is True only for equal versions
def Found.same_sound(
  a: RKnown.Found,
  b: RKnown.Found
) -> {RKnown.Found.same(a, b) == True{}: Bool} -> {a == b: RKnown.Found}:
  match a b:
    case RKnown.Found{+n1, +e1} RKnown.Found{+n2, +e2}:
      +h => (
        %Shared.Nat.is_eq_sound(n1, n2)(Shared.Bool.and_true_left(Nat.is_eq(n1, n2), RKnown.Entry.same(e1, e2))(h)): {RKnown.Found{n1, e1} == RKnown.Found{_, e2}: RKnown.Found}
        %Entry.same_sound(e1, e2)(Shared.Bool.and_true_right(Nat.is_eq(n1, n2), RKnown.Entry.same(e1, e2))(h)): {RKnown.Found{n1, e1} == RKnown.Found{n1, _}: RKnown.Found}
        {==})

# the laws of Found.same
def Found.laws() -> Shared.Eq.Laws(RKnown.Found, RKnown.Found.same):
  (Found.same_refl, Found.same_sound)

# Bucket.same is True for versions and themselves
def Bucket.same_refl(a: List<&2, RKnown.Found>) -> {RKnown.Bucket.same(a, a) == True{}: Bool}:
  Shared.List.is_eq_refl(~RKnown.Found, ~RKnown.Found.same, ~Found.laws(), a)

# Bucket.same is True only for equal versions
def Bucket.same_sound(
  a: List<&2, RKnown.Found>,
  b: List<&2, RKnown.Found>
) -> {RKnown.Bucket.same(a, b) == True{}: Bool} -> {a == b: List<&2, RKnown.Found>}:
  Shared.List.is_eq_sound(~RKnown.Found, ~RKnown.Found.same, ~Found.laws(), a, b)

# ids, if any, are the same as themselves
def Tip.same_refl(
  e: Maybe<&2, List<&2, RKnown.Found>>
) -> {Shared.Maybe.is_eq(~List<&2, RKnown.Found>, ~RKnown.Bucket.same, e, e) == True{}: Bool}:
  match e:
    case None{}:
      {==}
    case Some{v}:
      Bucket.same_refl(v)

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof does not run
# bend-lint: expect-begin bend-lint-rules/performance/missed_fork@hint -- a proof does not run
# Map.same is True for a set and itself
def Map.same_refl(a: Crits.Crit<List<&2, RKnown.Found>>) -> {RKnown.Map.same(a, a) == True{}: Bool}:
  match a:
    case Crits.Crit.Tip{}:
      {==}
    case Crits.Crit.Leaf{+k, +v}:
      Shared.Bool.and_both(
        Crits.Key.is_eq(k, k),
        RKnown.Bucket.same(v, v)
      )(Crits.Key.is_eq_refl(k))(Bucket.same_refl(v))
    case Crits.Crit.Fork{+r, +p, +e, +z, +o}:
      Shared.Bool.and_both(
        Crits.Key.is_eq(r, r),
        Bool.and(
          Nat.is_eq(p, p),
          Bool.and(
            Shared.Maybe.is_eq(~List<&2, RKnown.Found>, ~RKnown.Bucket.same, e, e),
            Bool.and(RKnown.Map.same(z, z), RKnown.Map.same(o, o))
          )
        )
      )(
        Crits.Key.is_eq_refl(r)
      )(
        Shared.Bool.and_both(
          Nat.is_eq(p, p),
          Bool.and(
            Shared.Maybe.is_eq(~List<&2, RKnown.Found>, ~RKnown.Bucket.same, e, e),
            Bool.and(RKnown.Map.same(z, z), RKnown.Map.same(o, o))
          )
        )(
          Shared.Nat.is_eq_refl(p)
        )(
          Shared.Bool.and_both(
            Shared.Maybe.is_eq(~List<&2, RKnown.Found>, ~RKnown.Bucket.same, e, e),
            Bool.and(RKnown.Map.same(z, z), RKnown.Map.same(o, o))
          )(
            Tip.same_refl(e)
          )(
            Shared.Bool.and_both(
              RKnown.Map.same(z, z),
              RKnown.Map.same(o, o)
            )(Map.same_refl(z))(Map.same_refl(o))
          )
        )
      )
# bend-lint: expect-end bend-lint-rules/performance/missed_fork@hint

# Map.same is True only for equal sets
def Map.same_sound(
  a: Crits.Crit<List<&2, RKnown.Found>>,
  b: Crits.Crit<List<&2, RKnown.Found>>
) -> {RKnown.Map.same(a, b) == True{}: Bool} -> {a == b: Crits.Crit<List<&2, RKnown.Found>>}:
  match a b:
    case Crits.Crit.Tip{} Crits.Crit.Tip{}:
      h => {==}
    case Crits.Crit.Tip{} Crits.Crit.Leaf{k2, v2}:
      h => Empty.absurd(
        {Crits.Crit.Tip{} == Crits.Crit.Leaf{k2, v2}: Crits.Crit<List<&2, RKnown.Found>>},
        Shared.Bool.false_ne_true(h)
      )
    case Crits.Crit.Tip{} Crits.Crit.Fork{r2, p2, e2, z2, o2}:
      h => Empty.absurd(
        {
          Crits.Crit.Tip{}
            == Crits.Crit.Fork{r2, p2, e2, z2, o2}: Crits.Crit<List<&2, RKnown.Found>>
        },
        Shared.Bool.false_ne_true(h)
      )
    case Crits.Crit.Leaf{k1, v1} Crits.Crit.Tip{}:
      h => Empty.absurd(
        {Crits.Crit.Leaf{k1, v1} == Crits.Crit.Tip{}: Crits.Crit<List<&2, RKnown.Found>>},
        Shared.Bool.false_ne_true(h)
      )
    case Crits.Crit.Leaf{k1, v1} Crits.Crit.Fork{r2, p2, e2, z2, o2}:
      h => Empty.absurd(
        {
          Crits.Crit.Leaf{
            k1,
            v1
          }
            == Crits.Crit.Fork{r2, p2, e2, z2, o2}: Crits.Crit<List<&2, RKnown.Found>>
        },
        Shared.Bool.false_ne_true(h)
      )
    case Crits.Crit.Fork{r1, p1, e1, z1, o1} Crits.Crit.Tip{}:
      h => Empty.absurd(
        {
          Crits.Crit.Fork{
            r1,
            p1,
            e1,
            z1,
            o1
          }
            == Crits.Crit.Tip{}: Crits.Crit<List<&2, RKnown.Found>>
        },
        Shared.Bool.false_ne_true(h)
      )
    case Crits.Crit.Fork{r1, p1, e1, z1, o1} Crits.Crit.Leaf{k2, v2}:
      h => Empty.absurd(
        {
          Crits.Crit.Fork{
            r1,
            p1,
            e1,
            z1,
            o1
          }
            == Crits.Crit.Leaf{k2, v2}: Crits.Crit<List<&2, RKnown.Found>>
        },
        Shared.Bool.false_ne_true(h)
      )
    case Crits.Crit.Leaf{+k1, +v1} Crits.Crit.Leaf{+k2, +v2}:
      +h => (
        %Crits.Key.is_eq_sound(k1, k2)(Shared.Bool.and_true_left(Crits.Key.is_eq(k1, k2), RKnown.Bucket.same(v1, v2))(h)): {Crits.Crit.Leaf{k1, v1} == Crits.Crit.Leaf{_, v2}: Crits.Crit<List<&2, RKnown.Found>>}
        %Bucket.same_sound(v1, v2)(Shared.Bool.and_true_right(Crits.Key.is_eq(k1, k2), RKnown.Bucket.same(v1, v2))(h)): {Crits.Crit.Leaf{k1, v1} == Crits.Crit.Leaf{k1, _}: Crits.Crit<List<&2, RKnown.Found>>}
        {==})
    case Crits.Crit.Fork{+r1, +p1, +e1, +z1, +o1} Crits.Crit.Fork{+r2, +p2, +e2, +z2, +o2}:
      +h => (
        %Crits.Key.is_eq_sound(r1, r2)(Shared.Bool.and_true_left(Crits.Key.is_eq(r1, r2), Bool.and(Nat.is_eq(p1, p2), Bool.and(Shared.Maybe.is_eq(~List<&2, RKnown.Found>, ~RKnown.Bucket.same, e1, e2), Bool.and(RKnown.Map.same(z1, z2), RKnown.Map.same(o1, o2)))))(h)): {Crits.Crit.Fork{r1, p1, e1, z1, o1} == Crits.Crit.Fork{_, p2, e2, z2, o2}: Crits.Crit<List<&2, RKnown.Found>>}
        %Shared.Nat.is_eq_sound(p1, p2)(Shared.Bool.and_true_left(Nat.is_eq(p1, p2), Bool.and(Shared.Maybe.is_eq(~List<&2, RKnown.Found>, ~RKnown.Bucket.same, e1, e2), Bool.and(RKnown.Map.same(z1, z2), RKnown.Map.same(o1, o2))))(Shared.Bool.and_true_right(Crits.Key.is_eq(r1, r2), Bool.and(Nat.is_eq(p1, p2), Bool.and(Shared.Maybe.is_eq(~List<&2, RKnown.Found>, ~RKnown.Bucket.same, e1, e2), Bool.and(RKnown.Map.same(z1, z2), RKnown.Map.same(o1, o2)))))(h))): {Crits.Crit.Fork{r1, p1, e1, z1, o1} == Crits.Crit.Fork{r1, _, e2, z2, o2}: Crits.Crit<List<&2, RKnown.Found>>}
        %Shared.Maybe.is_eq_sound(~List<&2, RKnown.Found>, ~RKnown.Bucket.same, x => y => Bucket.same_sound(x, y), e1, e2)(Shared.Bool.and_true_left(Shared.Maybe.is_eq(~List<&2, RKnown.Found>, ~RKnown.Bucket.same, e1, e2), Bool.and(RKnown.Map.same(z1, z2), RKnown.Map.same(o1, o2)))(Shared.Bool.and_true_right(Nat.is_eq(p1, p2), Bool.and(Shared.Maybe.is_eq(~List<&2, RKnown.Found>, ~RKnown.Bucket.same, e1, e2), Bool.and(RKnown.Map.same(z1, z2), RKnown.Map.same(o1, o2))))(Shared.Bool.and_true_right(Crits.Key.is_eq(r1, r2), Bool.and(Nat.is_eq(p1, p2), Bool.and(Shared.Maybe.is_eq(~List<&2, RKnown.Found>, ~RKnown.Bucket.same, e1, e2), Bool.and(RKnown.Map.same(z1, z2), RKnown.Map.same(o1, o2)))))(h)))): {Crits.Crit.Fork{r1, p1, e1, z1, o1} == Crits.Crit.Fork{r1, p1, _, z2, o2}: Crits.Crit<List<&2, RKnown.Found>>}
        %Map.same_sound(z1, z2)(Shared.Bool.and_true_left(RKnown.Map.same(z1, z2), RKnown.Map.same(o1, o2))(Shared.Bool.and_true_right(Shared.Maybe.is_eq(~List<&2, RKnown.Found>, ~RKnown.Bucket.same, e1, e2), Bool.and(RKnown.Map.same(z1, z2), RKnown.Map.same(o1, o2)))(Shared.Bool.and_true_right(Nat.is_eq(p1, p2), Bool.and(Shared.Maybe.is_eq(~List<&2, RKnown.Found>, ~RKnown.Bucket.same, e1, e2), Bool.and(RKnown.Map.same(z1, z2), RKnown.Map.same(o1, o2))))(Shared.Bool.and_true_right(Crits.Key.is_eq(r1, r2), Bool.and(Nat.is_eq(p1, p2), Bool.and(Shared.Maybe.is_eq(~List<&2, RKnown.Found>, ~RKnown.Bucket.same, e1, e2), Bool.and(RKnown.Map.same(z1, z2), RKnown.Map.same(o1, o2)))))(h))))): {Crits.Crit.Fork{r1, p1, e1, z1, o1} == Crits.Crit.Fork{r1, p1, e1, _, o2}: Crits.Crit<List<&2, RKnown.Found>>}
        %Map.same_sound(o1, o2)(Shared.Bool.and_true_right(RKnown.Map.same(z1, z2), RKnown.Map.same(o1, o2))(Shared.Bool.and_true_right(Shared.Maybe.is_eq(~List<&2, RKnown.Found>, ~RKnown.Bucket.same, e1, e2), Bool.and(RKnown.Map.same(z1, z2), RKnown.Map.same(o1, o2)))(Shared.Bool.and_true_right(Nat.is_eq(p1, p2), Bool.and(Shared.Maybe.is_eq(~List<&2, RKnown.Found>, ~RKnown.Bucket.same, e1, e2), Bool.and(RKnown.Map.same(z1, z2), RKnown.Map.same(o1, o2))))(Shared.Bool.and_true_right(Crits.Key.is_eq(r1, r2), Bool.and(Nat.is_eq(p1, p2), Bool.and(Shared.Maybe.is_eq(~List<&2, RKnown.Found>, ~RKnown.Bucket.same, e1, e2), Bool.and(RKnown.Map.same(z1, z2), RKnown.Map.same(o1, o2)))))(h))))): {Crits.Crit.Fork{r1, p1, e1, z1, o1} == Crits.Crit.Fork{r1, p1, e1, z1, _}: Crits.Crit<List<&2, RKnown.Found>>}
        {==})
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# Ids.same is True for versions by id and themselves
def Ids.same_refl(a: RKnown.Ids) -> {RKnown.Ids.same(a, a) == True{}: Bool}:
  match a:
    case RKnown.Ids{+m, +n}:
      Shared.Bool.and_both(
        RKnown.Map.same(m, m),
        Nat.is_eq(n, n)
      )(Map.same_refl(m))(Shared.Nat.is_eq_refl(n))

# Ids.same is True only for equal versions by id
def Ids.same_sound(
  a: RKnown.Ids,
  b: RKnown.Ids
) -> {RKnown.Ids.same(a, b) == True{}: Bool} -> {a == b: RKnown.Ids}:
  match a b:
    case RKnown.Ids{+m1, +n1} RKnown.Ids{+m2, +n2}:
      +h => (
        %Map.same_sound(m1, m2)(Shared.Bool.and_true_left(RKnown.Map.same(m1, m2), Nat.is_eq(n1, n2))(h)): {RKnown.Ids{m1, n1} == RKnown.Ids{_, n2}: RKnown.Ids}
        %Shared.Nat.is_eq_sound(n1, n2)(Shared.Bool.and_true_right(RKnown.Map.same(m1, m2), Nat.is_eq(n1, n2))(h)): {RKnown.Ids{m1, n1} == RKnown.Ids{m1, _}: RKnown.Ids}
        {==})

# the ids that fit a state are the ids of its versions
def Made.fits_sound(
  -m: Maybe<&2, RLines.State>,
  +x: RKnown.Ids,
  +vs: List<&2, Types.Entry>,
  -k: Nat
) -> {
  m == Some{RLines.State{vs, k}}: Maybe<&2, RLines.State>
} -> {RKnown.Made.fits(m, x) == True{}: Bool} -> {x == RKnown.Ids.of(vs): RKnown.Ids}:
  e => h => Ids.same_sound(x, RKnown.Ids.of(vs))((
      %e: {RKnown.Made.fits(_, x) == True{}: Bool}
      h))

# the ids of the versions of a state fit it
def Made.fits_of(
  -m: Maybe<&2, RLines.State>,
  +vs: List<&2, Types.Entry>,
  -k: Nat
) -> {
  m == Some{RLines.State{vs, k}}: Maybe<&2, RLines.State>
} -> {RKnown.Made.fits(m, RKnown.Ids.of(vs)) == True{}: Bool}:
  e => (
    %Equal.sym(Maybe<&2, RLines.State>, m, Some{RLines.State{vs, k}}, e): {RKnown.Made.fits(_, RKnown.Ids.of(vs)) == True{}: Bool}
    Ids.same_refl(RKnown.Ids.of(vs)))

# an id whose key is not the key of another is not the other
def Key.ne_id(
  +e: Ledgers.Id,
  +i: Ledgers.Id
) -> {
  Crits.Key.is_eq(RKnown.Id.key(i), RKnown.Id.key(e)) == False{}: Bool
} -> {Ledgers.Id.is_eq(e, i) == False{}: Bool}:
  +ef => Lists.Bool.by(
    y => {y == False{}: Bool},
    Ledgers.Id.is_eq(e, i),
    et2 => Equal.trans(
      Bool,
      True{},
      Crits.Key.is_eq(RKnown.Id.key(i), RKnown.Id.key(e)),
      False{},
      Equal.sym(Bool, Crits.Key.is_eq(RKnown.Id.key(i), RKnown.Id.key(e)), True{}, (
          %Equal.sym(Ledgers.Id, e, i, Ledgers.Id.is_eq_sound(e, i)(et2)): {Crits.Key.is_eq(RKnown.Id.key(i), RKnown.Id.key(_)) == True{}: Bool}
          Crits.Key.is_eq_refl(RKnown.Id.key(i)))),
      ef
    ),
    ef2 => {==}
  )

# the map of the versions x by id
def Ids.map(x: RKnown.Ids) -> Crits.Crit<List<&2, RKnown.Found>>:
  match x:
    case RKnown.Ids{m, n}:
      m

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof does not run
# what a map with one more version under the key kk holds under a key: under
# kk, the version before the versions that the map held there
def Map.get_put(
  +acc: Crits.Crit<List<&2, RKnown.Found>>,
  +kk: List<&2, U32>,
  +f: RKnown.Found,
  +k: List<&2, U32>
) -> {
  Crits.Crit.wf(~List<&2, RKnown.Found>, acc, 0n) == True{}: Bool
} -> {
  Crits.Crit.get(
    List<&2, RKnown.Found>,
    Crits.Crit.upsert(~List<&2, RKnown.Found>, ~RKnown.Ids.join, acc, kk, [f]),
    k
  )
    == Bool.pick(
      Maybe<&2, List<&2, RKnown.Found>>,
      Crits.Key.is_eq(k, kk),
      Some{
        Crits.Crit.merge(
          ~List<&2, RKnown.Found>,
          ~RKnown.Ids.join,
          Crits.Crit.get(List<&2, RKnown.Found>, acc, kk),
          [f]
        )
      },
      Crits.Crit.get(List<&2, RKnown.Found>, acc, k)
    ): Maybe<&2, List<&2, RKnown.Found>>
}:
  +w =>
    %Equal.sym(
      Maybe<&2, List<&2, RKnown.Found>>,
      Crits.Crit.get(
        List<&2, RKnown.Found>,
        Crits.Crit.upsert(~List<&2, RKnown.Found>, ~RKnown.Ids.join, acc, kk, [f]),
        k
      ),
      Crits.Crit.lookup(
        List<&2, RKnown.Found>,
        Crits.Crit.upsert(~List<&2, RKnown.Found>, ~RKnown.Ids.join, acc, kk, [f]),
        k
      ),
      Crits.Crit.get_lookup(
        ~List<&2, RKnown.Found>,
        Crits.Crit.upsert(~List<&2, RKnown.Found>, ~RKnown.Ids.join, acc, kk, [f]),
        k
      )(Crits.Crit.upsert_wf(~List<&2, RKnown.Found>, ~RKnown.Ids.join, acc, kk, [f])(w))
    ): {
      _
        == Bool.pick(
          Maybe<&2, List<&2, RKnown.Found>>,
          Crits.Key.is_eq(k, kk),
          Some{
            Crits.Crit.merge(
              ~List<&2, RKnown.Found>,
              ~RKnown.Ids.join,
              Crits.Crit.get(List<&2, RKnown.Found>, acc, kk),
              [f]
            )
          },
          Crits.Crit.get(List<&2, RKnown.Found>, acc, k)
        ): Maybe<&2, List<&2, RKnown.Found>>
    }
    %Equal.sym(
      Maybe<&2, List<&2, RKnown.Found>>,
      Crits.Crit.lookup(
        List<&2, RKnown.Found>,
        Crits.Crit.upsert(~List<&2, RKnown.Found>, ~RKnown.Ids.join, acc, kk, [f]),
        k
      ),
      Bool.pick(
        Maybe<&2, List<&2, RKnown.Found>>,
        Crits.Key.is_eq(k, kk),
        Some{
          Crits.Crit.merge(
            ~List<&2, RKnown.Found>,
            ~RKnown.Ids.join,
            Crits.Crit.lookup(List<&2, RKnown.Found>, acc, kk),
            [f]
          )
        },
        Crits.Crit.lookup(List<&2, RKnown.Found>, acc, k)
      ),
      Crits.Crit.upsert_lookup(~List<&2, RKnown.Found>, ~RKnown.Ids.join, acc, kk, [f], k)(w)
    ): {
      _
        == Bool.pick(
          Maybe<&2, List<&2, RKnown.Found>>,
          Crits.Key.is_eq(k, kk),
          Some{
            Crits.Crit.merge(
              ~List<&2, RKnown.Found>,
              ~RKnown.Ids.join,
              Crits.Crit.get(List<&2, RKnown.Found>, acc, kk),
              [f]
            )
          },
          Crits.Crit.get(List<&2, RKnown.Found>, acc, k)
        ): Maybe<&2, List<&2, RKnown.Found>>
    }
    %Equal.sym(
      Maybe<&2, List<&2, RKnown.Found>>,
      Crits.Crit.get(List<&2, RKnown.Found>, acc, k),
      Crits.Crit.lookup(List<&2, RKnown.Found>, acc, k),
      Crits.Crit.get_lookup(~List<&2, RKnown.Found>, acc, k)(w)
    ): {
      Bool.pick(
        Maybe<&2, List<&2, RKnown.Found>>,
        Crits.Key.is_eq(k, kk),
        Some{
          Crits.Crit.merge(
            ~List<&2, RKnown.Found>,
            ~RKnown.Ids.join,
            Crits.Crit.lookup(List<&2, RKnown.Found>, acc, kk),
            [f]
          )
        },
        Crits.Crit.lookup(List<&2, RKnown.Found>, acc, k)
      )
        == Bool.pick(
          Maybe<&2, List<&2, RKnown.Found>>,
          Crits.Key.is_eq(k, kk),
          Some{
            Crits.Crit.merge(
              ~List<&2, RKnown.Found>,
              ~RKnown.Ids.join,
              Crits.Crit.get(List<&2, RKnown.Found>, acc, kk),
              [f]
            )
          },
          _
        ): Maybe<&2, List<&2, RKnown.Found>>
    }
    %Equal.sym(
      Maybe<&2, List<&2, RKnown.Found>>,
      Crits.Crit.get(List<&2, RKnown.Found>, acc, kk),
      Crits.Crit.lookup(List<&2, RKnown.Found>, acc, kk),
      Crits.Crit.get_lookup(~List<&2, RKnown.Found>, acc, kk)(w)
    ): {
      Bool.pick(
        Maybe<&2, List<&2, RKnown.Found>>,
        Crits.Key.is_eq(k, kk),
        Some{
          Crits.Crit.merge(
            ~List<&2, RKnown.Found>,
            ~RKnown.Ids.join,
            Crits.Crit.lookup(List<&2, RKnown.Found>, acc, kk),
            [f]
          )
        },
        Crits.Crit.lookup(List<&2, RKnown.Found>, acc, k)
      )
        == Bool.pick(
          Maybe<&2, List<&2, RKnown.Found>>,
          Crits.Key.is_eq(k, kk),
          Some{Crits.Crit.merge(~List<&2, RKnown.Found>, ~RKnown.Ids.join, _, [f])},
          Crits.Crit.lookup(List<&2, RKnown.Found>, acc, k)
        ): Maybe<&2, List<&2, RKnown.Found>>
    }
    {==}
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the request of an id made one of the versions m, if any, with a version
# before them, exactly when it made that version or one of m
def Bucket.has_put(
  m: Maybe<&2, List<&2, RKnown.Found>>,
  +n: Nat,
  +e: Types.Entry,
  +i: Ledgers.Id
) -> {
  RKnown.Ids.has.of(
    Some{Crits.Crit.merge(~List<&2, RKnown.Found>, ~RKnown.Ids.join, m, [RKnown.Found{n, e}])},
    i
  )
    == Bool.or(RLines.Entry.is_of(i, e), RKnown.Ids.has.of(m, i)): Bool
}:
  match m:
    case None{}:
      Lists.Bool.by(
        b => {List.any.if(u => False{}, b) == Bool.or(b, False{}): Bool},
        RLines.Entry.is_of(i, e),
        et => {==},
        ef => {==}
      )
    case Some{+old}:
      Lists.Bool.by(
        b => {
          List.any.if(
            u => RKnown.Ids.holds(old, i),
            b
          )
            == Bool.or(b, RKnown.Ids.holds(old, i)): Bool
        },
        RLines.Entry.is_of(i, e),
        et => {==},
        ef => {==}
      )

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof does not run
# the request of an id made one of the versions by id with one more version
# exactly when it made that version, or one of the versions before
def Ids.put_has(
  +m: Crits.Crit<List<&2, RKnown.Found>>,
  +n: Nat,
  +e: Types.Entry,
  +i: Ledgers.Id
) -> {
  Crits.Crit.wf(~List<&2, RKnown.Found>, m, 0n) == True{}: Bool
} -> {
  RKnown.Ids.has(
    RKnown.Ids.put(RKnown.Ids{m, n}, e),
    i
  )
    == Bool.or(RLines.Entry.is_of(i, e), RKnown.Ids.has(RKnown.Ids{m, n}, i)): Bool
}:
  w =>
    %Equal.sym(
      Maybe<&2, List<&2, RKnown.Found>>,
      Crits.Crit.get(
        List<&2, RKnown.Found>,
        Crits.Crit.upsert(
          ~List<&2, RKnown.Found>,
          ~RKnown.Ids.join,
          m,
          RKnown.Id.key(RLines.Entry.id(e)),
          [RKnown.Found{n, e}]
        ),
        RKnown.Id.key(i)
      ),
      Bool.pick(
        Maybe<&2, List<&2, RKnown.Found>>,
        Crits.Key.is_eq(RKnown.Id.key(i), RKnown.Id.key(RLines.Entry.id(e))),
        Some{
          Crits.Crit.merge(
            ~List<&2, RKnown.Found>,
            ~RKnown.Ids.join,
            Crits.Crit.get(List<&2, RKnown.Found>, m, RKnown.Id.key(RLines.Entry.id(e))),
            [RKnown.Found{n, e}]
          )
        },
        Crits.Crit.get(List<&2, RKnown.Found>, m, RKnown.Id.key(i))
      ),
      Map.get_put(m, RKnown.Id.key(RLines.Entry.id(e)), RKnown.Found{n, e}, RKnown.Id.key(i))(w)
    ): {
      RKnown.Ids.has.of(
        _,
        i
      )
        == Bool.or(RLines.Entry.is_of(i, e), RKnown.Ids.has(RKnown.Ids{m, n}, i)): Bool
    }
    Lists.Bool.by(
      h => {
        RKnown.Ids.has.of(
          Bool.pick(
            Maybe<&2, List<&2, RKnown.Found>>,
            h,
            Some{
              Crits.Crit.merge(
                ~List<&2, RKnown.Found>,
                ~RKnown.Ids.join,
                Crits.Crit.get(List<&2, RKnown.Found>, m, RKnown.Id.key(RLines.Entry.id(e))),
                [RKnown.Found{n, e}]
              )
            },
            Crits.Crit.get(List<&2, RKnown.Found>, m, RKnown.Id.key(i))
          ),
          i
        )
          == Bool.or(RLines.Entry.is_of(i, e), RKnown.Ids.has(RKnown.Ids{m, n}, i)): Bool
      },
      Crits.Key.is_eq(RKnown.Id.key(i), RKnown.Id.key(RLines.Entry.id(e))),
      et => (
        %Crits.Key.is_eq_sound(RKnown.Id.key(i), RKnown.Id.key(RLines.Entry.id(e)))(et): {RKnown.Ids.has.of(Some{Crits.Crit.merge(~List<&2, RKnown.Found>, ~RKnown.Ids.join, Crits.Crit.get(List<&2, RKnown.Found>, m, _), [RKnown.Found{n, e}])}, i) == Bool.or(RLines.Entry.is_of(i, e), RKnown.Ids.has(RKnown.Ids{m, n}, i)): Bool}
        Bucket.has_put(Crits.Crit.get(List<&2, RKnown.Found>, m, RKnown.Id.key(i)), n, e, i)),
      ef => (
        %Equal.sym(Bool, RLines.Entry.is_of(i, e), False{}, Key.ne_id(RLines.Entry.id(e), i)(ef)): {RKnown.Ids.has(RKnown.Ids{m, n}, i) == Bool.or(_, RKnown.Ids.has(RKnown.Ids{m, n}, i)): Bool}
        {==})
    )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# versions by id with more versions are well formed when they were
def Ids.go_wf(
  vs: List<&2, Types.Entry>,
  +m: Crits.Crit<List<&2, RKnown.Found>>,
  +n: Nat
) -> {
  Crits.Crit.wf(~List<&2, RKnown.Found>, m, 0n) == True{}: Bool
} -> {
  Crits.Crit.wf(
    ~List<&2, RKnown.Found>,
    Ids.map(RKnown.Ids.go(vs, RKnown.Ids{m, n})),
    0n
  )
    == True{}: Bool
}:
  match vs:
    case Nil{}:
      w => w
    case Con{+e, rest}:
      w => Ids.go_wf(
        rest,
        Crits.Crit.upsert(
          ~List<&2, RKnown.Found>,
          ~RKnown.Ids.join,
          m,
          RKnown.Id.key(RLines.Entry.id(e)),
          [RKnown.Found{n, e}]
        ),
        1n+n
      )(
        Crits.Crit.upsert_wf(
          ~List<&2, RKnown.Found>,
          ~RKnown.Ids.join,
          m,
          RKnown.Id.key(RLines.Entry.id(e)),
          [RKnown.Found{n, e}]
        )(w)
      )

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof does not run
# the request of an id made one of the versions by id with the versions vs
# exactly when it made one of vs, or one of the versions before
def Ids.go_has(
  vs: List<&2, Types.Entry>,
  +m: Crits.Crit<List<&2, RKnown.Found>>,
  +n: Nat,
  +i: Ledgers.Id
) -> {
  Crits.Crit.wf(~List<&2, RKnown.Found>, m, 0n) == True{}: Bool
} -> {
  RKnown.Ids.has(
    RKnown.Ids.go(vs, RKnown.Ids{m, n}),
    i
  )
    == Bool.or(
      Shared.List.some(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, vs, i),
      RKnown.Ids.has(RKnown.Ids{m, n}, i)
    ): Bool
}:
  match vs:
    case Nil{}:
      w => {==}
    case Con{+e, +rest}:
      +w => Equal.trans(
        Bool,
        RKnown.Ids.has(RKnown.Ids.go(rest, RKnown.Ids.put(RKnown.Ids{m, n}, e)), i),
        Bool.or(
          Shared.List.some(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, rest, i),
          RKnown.Ids.has(RKnown.Ids.put(RKnown.Ids{m, n}, e), i)
        ),
        Bool.or(
          Shared.List.some(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, e <> rest, i),
          RKnown.Ids.has(RKnown.Ids{m, n}, i)
        ),
        Ids.go_has(
          rest,
          Crits.Crit.upsert(
            ~List<&2, RKnown.Found>,
            ~RKnown.Ids.join,
            m,
            RKnown.Id.key(RLines.Entry.id(e)),
            [RKnown.Found{n, e}]
          ),
          1n+n,
          i
        )(
          Crits.Crit.upsert_wf(
            ~List<&2, RKnown.Found>,
            ~RKnown.Ids.join,
            m,
            RKnown.Id.key(RLines.Entry.id(e)),
            [RKnown.Found{n, e}]
          )(w)
        ),
        (
          %Equal.sym(Bool, RKnown.Ids.has(RKnown.Ids.put(RKnown.Ids{m, n}, e), i), Bool.or(RLines.Entry.is_of(i, e), RKnown.Ids.has(RKnown.Ids{m, n}, i)), Ids.put_has(m, n, e, i)(w)): {Bool.or(Shared.List.some(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, rest, i), _) == Bool.or(List.any.if(u => Shared.List.some(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, rest, i), RLines.Entry.is_of(i, e)), RKnown.Ids.has(RKnown.Ids{m, n}, i)): Bool}
          Lists.Bool.by(b => {Bool.or(Shared.List.some(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, rest, i), Bool.or(b, RKnown.Ids.has(RKnown.Ids{m, n}, i))) == Bool.or(List.any.if(u => Shared.List.some(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, rest, i), b), RKnown.Ids.has(RKnown.Ids{m, n}, i)): Bool}, RLines.Entry.is_of(i, e), et => Shared.Bool.or_true_right(Shared.List.some(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, rest, i)), ef => {==}))
      )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the request of an id made one of the versions vs by id exactly when it made
# one of vs
def Ids.of_has(
  +vs: List<&2, Types.Entry>,
  +i: Ledgers.Id
) -> {
  RKnown.Ids.has(
    RKnown.Ids.of(vs),
    i
  )
    == Shared.List.some(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, vs, i): Bool
}:
  Equal.trans(
    Bool,
    RKnown.Ids.has(RKnown.Ids.of(vs), i),
    Bool.or(Shared.List.some(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, vs, i), False{}),
    Shared.List.some(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, vs, i),
    Ids.go_has(vs, Crits.Crit.new(List<&2, RKnown.Found>), 0n, i)({==}),
    Equal.sym(
      Bool,
      Shared.List.some(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, vs, i),
      Bool.or(Shared.List.some(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, vs, i), False{}),
      Shared.Bool.or_false(Shared.List.some(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, vs, i))
    )
  )

# ys after xs, without as many items as xs has, is ys
def Past.append(
  xs: List<&2, Types.Entry>,
  +zs: List<&2, Types.Entry>
) -> {RKnown.Entries.past(xs, List.append(&2, Types.Entry, xs, zs)) == zs: List<&2, Types.Entry>}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, rest}:
      Past.append(rest, zs)

# the versions by id with vs and then zs are those with vs, with zs
def Ids.go_append(
  vs: List<&2, Types.Entry>,
  +zs: List<&2, Types.Entry>,
  +acc: RKnown.Ids
) -> {
  RKnown.Ids.go(
    List.append(&2, Types.Entry, vs, zs),
    acc
  )
    == RKnown.Ids.go(zs, RKnown.Ids.go(vs, acc)): RKnown.Ids
}:
  match vs:
    case Nil{}:
      {==}
    case Con{+e, rest}:
      Ids.go_append(rest, zs, RKnown.Ids.put(acc, e))

# a version that the request of an id did not make changes no version found
def Found.or_miss(
  x: Maybe<&2, RKnown.Found>,
  +n: Nat,
  +e: Types.Entry,
  +i: Ledgers.Id
) -> {
  RLines.Entry.is_of(i, e) == False{}: Bool
} -> {RKnown.Found.or(x, RKnown.Found{n, e}, i) == x: Maybe<&2, RKnown.Found>}:
  match x:
    case Some{g}:
      h => {==}
    case None{}:
      h => (
        %Equal.sym(Bool, RLines.Entry.is_of(i, e), False{}, h): {Shared.Maybe.when(RKnown.Found, _, u => Some{RKnown.Found{n, e}}) == None{}: Maybe<&2, RKnown.Found>}
        {==})

# the oldest version that the request of an id made among the versions m,
# if any, with a version before them: the oldest among m, else that version
def Bucket.find_put(
  m: Maybe<&2, List<&2, RKnown.Found>>,
  +n: Nat,
  +e: Types.Entry,
  +i: Ledgers.Id
) -> {
  RKnown.Ids.find.of(
    Some{Crits.Crit.merge(~List<&2, RKnown.Found>, ~RKnown.Ids.join, m, [RKnown.Found{n, e}])},
    i
  )
    == RKnown.Found.or(RKnown.Ids.find.of(m, i), RKnown.Found{n, e}, i): Maybe<&2, RKnown.Found>
}:
  match m:
    case None{}:
      {==}
    case Some{old}:
      {==}

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof does not run
# the oldest version that the request of an id made in the versions by id
# with one more version: the oldest before, else that version
def Ids.put_find(
  +m: Crits.Crit<List<&2, RKnown.Found>>,
  +n: Nat,
  +e: Types.Entry,
  +i: Ledgers.Id
) -> {
  Crits.Crit.wf(~List<&2, RKnown.Found>, m, 0n) == True{}: Bool
} -> {
  RKnown.Ids.find(
    RKnown.Ids.put(RKnown.Ids{m, n}, e),
    i
  )
    == RKnown.Found.or(
      RKnown.Ids.find(RKnown.Ids{m, n}, i),
      RKnown.Found{n, e},
      i
    ): Maybe<&2, RKnown.Found>
}:
  w =>
    %Equal.sym(
      Maybe<&2, List<&2, RKnown.Found>>,
      Crits.Crit.get(
        List<&2, RKnown.Found>,
        Crits.Crit.upsert(
          ~List<&2, RKnown.Found>,
          ~RKnown.Ids.join,
          m,
          RKnown.Id.key(RLines.Entry.id(e)),
          [RKnown.Found{n, e}]
        ),
        RKnown.Id.key(i)
      ),
      Bool.pick(
        Maybe<&2, List<&2, RKnown.Found>>,
        Crits.Key.is_eq(RKnown.Id.key(i), RKnown.Id.key(RLines.Entry.id(e))),
        Some{
          Crits.Crit.merge(
            ~List<&2, RKnown.Found>,
            ~RKnown.Ids.join,
            Crits.Crit.get(List<&2, RKnown.Found>, m, RKnown.Id.key(RLines.Entry.id(e))),
            [RKnown.Found{n, e}]
          )
        },
        Crits.Crit.get(List<&2, RKnown.Found>, m, RKnown.Id.key(i))
      ),
      Map.get_put(m, RKnown.Id.key(RLines.Entry.id(e)), RKnown.Found{n, e}, RKnown.Id.key(i))(w)
    ): {
      RKnown.Ids.find.of(
        _,
        i
      )
        == RKnown.Found.or(
          RKnown.Ids.find(RKnown.Ids{m, n}, i),
          RKnown.Found{n, e},
          i
        ): Maybe<&2, RKnown.Found>
    }
    Lists.Bool.by(
      h => {
        RKnown.Ids.find.of(
          Bool.pick(
            Maybe<&2, List<&2, RKnown.Found>>,
            h,
            Some{
              Crits.Crit.merge(
                ~List<&2, RKnown.Found>,
                ~RKnown.Ids.join,
                Crits.Crit.get(List<&2, RKnown.Found>, m, RKnown.Id.key(RLines.Entry.id(e))),
                [RKnown.Found{n, e}]
              )
            },
            Crits.Crit.get(List<&2, RKnown.Found>, m, RKnown.Id.key(i))
          ),
          i
        )
          == RKnown.Found.or(
            RKnown.Ids.find(RKnown.Ids{m, n}, i),
            RKnown.Found{n, e},
            i
          ): Maybe<&2, RKnown.Found>
      },
      Crits.Key.is_eq(RKnown.Id.key(i), RKnown.Id.key(RLines.Entry.id(e))),
      et => (
        %Crits.Key.is_eq_sound(RKnown.Id.key(i), RKnown.Id.key(RLines.Entry.id(e)))(et): {RKnown.Ids.find.of(Some{Crits.Crit.merge(~List<&2, RKnown.Found>, ~RKnown.Ids.join, Crits.Crit.get(List<&2, RKnown.Found>, m, _), [RKnown.Found{n, e}])}, i) == RKnown.Found.or(RKnown.Ids.find(RKnown.Ids{m, n}, i), RKnown.Found{n, e}, i): Maybe<&2, RKnown.Found>}
        Bucket.find_put(Crits.Crit.get(List<&2, RKnown.Found>, m, RKnown.Id.key(i)), n, e, i)),
      ef => Equal.sym(
        Maybe<&2, RKnown.Found>,
        RKnown.Found.or(RKnown.Ids.find(RKnown.Ids{m, n}, i), RKnown.Found{n, e}, i),
        RKnown.Ids.find(RKnown.Ids{m, n}, i),
        Found.or_miss(
          RKnown.Ids.find(RKnown.Ids{m, n}, i),
          n,
          e,
          i
        )(Key.ne_id(RLines.Entry.id(e), i)(ef))
      )
    )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the oldest version that the request of the id i made: m, if any, else the
# first of vs that it made, where the versions vs are numbered from n on
def Found.over(
  vs: List<&2, Types.Entry>,
  m: Maybe<&2, RKnown.Found>,
  n: Nat,
  +i: Ledgers.Id
) -> Maybe<&2, RKnown.Found>:
  match vs:
    case Nil{}:
      m
    case Con{+e, rest}:
      +n = n
      Found.over(rest, RKnown.Found.or(m, RKnown.Found{n, e}, i), 1n+n, i)

# the oldest version that the request of an id made in the versions by id
# with the versions vs: the oldest before, else the first of vs
def Ids.go_find(
  vs: List<&2, Types.Entry>,
  +m: Crits.Crit<List<&2, RKnown.Found>>,
  +n: Nat,
  +i: Ledgers.Id
) -> {
  Crits.Crit.wf(~List<&2, RKnown.Found>, m, 0n) == True{}: Bool
} -> {
  RKnown.Ids.find(
    RKnown.Ids.go(vs, RKnown.Ids{m, n}),
    i
  )
    == Found.over(vs, RKnown.Ids.find(RKnown.Ids{m, n}, i), n, i): Maybe<&2, RKnown.Found>
}:
  match vs:
    case Nil{}:
      w => {==}
    case Con{+e, +rest}:
      +w => (
        %Ids.put_find(m, n, e, i)(w): {RKnown.Ids.find(RKnown.Ids.go(rest, RKnown.Ids.put(RKnown.Ids{m, n}, e)), i) == Found.over(rest, _, 1n+n, i): Maybe<&2, RKnown.Found>}
        Ids.go_find(rest, Crits.Crit.upsert(~List<&2, RKnown.Found>, ~RKnown.Ids.join, m, RKnown.Id.key(RLines.Entry.id(e)), [RKnown.Found{n, e}]), 1n+n, i)(Crits.Crit.upsert_wf(~List<&2, RKnown.Found>, ~RKnown.Ids.join, m, RKnown.Id.key(RLines.Entry.id(e)), [RKnown.Found{n, e}])(w)))

# bend-lint: expect-begin bend-lint-rules/performance/dead_accumulator@information -- a proof does not run
# a version that was found stays the oldest
def Found.over_some(
  vs: List<&2, Types.Entry>,
  +g: RKnown.Found,
  n: Nat,
  +i: Ledgers.Id
) -> {Found.over(vs, Some{g}, n, i) == Some{g}: Maybe<&2, RKnown.Found>}:
  match vs:
    case Nil{}:
      {==}
    case Con{+e, rest}:
      Found.over_some(rest, g, 1n+n, i)
# bend-lint: expect-end bend-lint-rules/performance/dead_accumulator@information

# the version m, if any, with n more as its number
def Found.shift(n: Nat, m: Maybe<&2, RKnown.Found>) -> Maybe<&2, RKnown.Found>:
  match m:
    case None{}:
      None{}
    case Some{RKnown.Found{j, e}}:
      Some{RKnown.Found{Nat.add(j, n), e}}

# an entry g, if any, as version 1+j, numbered from n, is g as version j,
# numbered from 1+n
def Find.up_get(
  g: Maybe<&2, Types.Entry>,
  +j: Nat,
  +n: Nat
) -> {
  Found.shift(
    n,
    Maybe.map(&2, Types.Entry, RKnown.Found, e => RKnown.Found{1n+j, e}, g)
  )
    == Found.shift(
      1n+n,
      Maybe.map(&2, Types.Entry, RKnown.Found, e => RKnown.Found{j, e}, g)
    ): Maybe<&2, RKnown.Found>
}:
  match g:
    case None{}:
      {==}
    case Some{x}:
      %Equal.sym(
        Nat,
        Nat.add(j, 1n+n),
        1n+Nat.add(j, n),
        Shared.Nat.add_succ(j, n)
      ): {
        Some{RKnown.Found{1n+Nat.add(j, n), x}} == Some{RKnown.Found{_, x}}: Maybe<&2, RKnown.Found>
      }
      {==}

# the version at an index after the one of mi, among versions with one more
# before them, numbered from n, is the version at mi, numbered from 1+n
def Find.up(
  e: Types.Entry,
  +rest: List<&2, Types.Entry>,
  mi: Maybe<&2, Nat>,
  +n: Nat
) -> {
  Found.shift(
    n,
    RAnswers.Versions.find.at(e <> rest, Lists.List.index.up(mi))
  )
    == Found.shift(1n+n, RAnswers.Versions.find.at(rest, mi)): Maybe<&2, RKnown.Found>
}:
  match mi:
    case None{}:
      {==}
    case Some{+j}:
      Find.up_get(List.get(&2, Types.Entry, rest, j), j, n)

# the first of the versions vs, numbered from n on, that the request of an
# id made is the version that Versions.find gives, with n more as its number
def Found.over_none(
  vs: List<&2, Types.Entry>,
  +n: Nat,
  +i: Ledgers.Id
) -> {
  Found.over(
    vs,
    None{},
    n,
    i
  )
    == Found.shift(n, RAnswers.Versions.find(vs, i)): Maybe<&2, RKnown.Found>
}:
  match vs:
    case Nil{}:
      {==}
    case Con{+e, +rest}:
      Lists.Bool.by(
        b => {
          Found.over(
            rest,
            Shared.Maybe.when(RKnown.Found, b, u => Some{RKnown.Found{n, e}}),
            1n+n,
            i
          )
            == Found.shift(
              n,
              RAnswers.Versions.find.at(
                e <> rest,
                Lists.List.index.if(
                  u => Lists.List.index(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, rest, i),
                  b
                )
              )
            ): Maybe<&2, RKnown.Found>
        },
        RLines.Entry.is_of(i, e),
        et => Found.over_some(rest, RKnown.Found{n, e}, 1n+n, i),
        ef => Equal.trans(
          Maybe<&2, RKnown.Found>,
          Found.over(rest, None{}, 1n+n, i),
          Found.shift(1n+n, RAnswers.Versions.find(rest, i)),
          Found.shift(
            n,
            RAnswers.Versions.find.at(
              e <> rest,
              Lists.List.index.up(
                Lists.List.index(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, rest, i)
              )
            )
          ),
          Found.over_none(rest, 1n+n, i),
          Equal.sym(
            Maybe<&2, RKnown.Found>,
            Found.shift(
              n,
              RAnswers.Versions.find.at(
                e <> rest,
                Lists.List.index.up(
                  Lists.List.index(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, rest, i)
                )
              )
            ),
            Found.shift(1n+n, RAnswers.Versions.find(rest, i)),
            Find.up(
              e,
              rest,
              Lists.List.index(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, rest, i),
              n
            )
          )
        )
      )

# a version with 0 more as its number is itself
def Found.shift_zero(
  m: Maybe<&2, RKnown.Found>
) -> {Found.shift(0n, m) == m: Maybe<&2, RKnown.Found>}:
  match m:
    case None{}:
      {==}
    case Some{RKnown.Found{j, e}}:
      %Equal.sym(
        Nat,
        Nat.add(j, 0n),
        j,
        Shared.Nat.add_zero(j)
      ): {Some{RKnown.Found{_, e}} == Some{RKnown.Found{j, e}}: Maybe<&2, RKnown.Found>}
      {==}

# the oldest version that the request of an id made, read from the versions
# vs by id, is the version that Versions.find gives
def Ids.of_find(
  +vs: List<&2, Types.Entry>,
  +i: Ledgers.Id
) -> {
  RKnown.Ids.find(RKnown.Ids.of(vs), i) == RAnswers.Versions.find(vs, i): Maybe<&2, RKnown.Found>
}:
  Equal.trans(
    Maybe<&2, RKnown.Found>,
    RKnown.Ids.find(RKnown.Ids.of(vs), i),
    Found.over(vs, None{}, 0n, i),
    RAnswers.Versions.find(vs, i),
    Ids.go_find(vs, Crits.Crit.new(List<&2, RKnown.Found>), 0n, i)({==}),
    Equal.trans(
      Maybe<&2, RKnown.Found>,
      Found.over(vs, None{}, 0n, i),
      Found.shift(0n, RAnswers.Versions.find(vs, i)),
      RAnswers.Versions.find(vs, i),
      Found.over_none(vs, 0n, i),
      Found.shift_zero(RAnswers.Versions.find(vs, i))
    )
  )

# an ask made one of the versions m, if any, with a version before them,
# exactly when it made that version or one of m
def Bucket.made_put(
  m: Maybe<&2, List<&2, RKnown.Found>>,
  +n: Nat,
  +e: Types.Entry,
  +a: Types.Ask
) -> {
  RKnown.Ids.made.of(
    Some{Crits.Crit.merge(~List<&2, RKnown.Found>, ~RKnown.Ids.join, m, [RKnown.Found{n, e}])},
    a
  )
    == Bool.or(RKnown.Entry.made_by(a, e), RKnown.Ids.made.of(m, a)): Bool
}:
  match m:
    case None{}:
      Lists.Bool.by(
        b => {List.any.if(u => False{}, b) == Bool.or(b, False{}): Bool},
        RKnown.Entry.made_by(a, e),
        et => {==},
        ef => {==}
      )
    case Some{+old}:
      Lists.Bool.by(
        b => {
          List.any.if(
            u => RKnown.Ids.made.in(old, a),
            b
          )
            == Bool.or(b, RKnown.Ids.made.in(old, a)): Bool
        },
        RKnown.Entry.made_by(a, e),
        et => {==},
        ef => {==}
      )

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof does not run
# an ask made one of the versions by id with one more version exactly when
# it made that version, or one of the versions before
def Ids.put_made(
  +m: Crits.Crit<List<&2, RKnown.Found>>,
  +n: Nat,
  +e: Types.Entry,
  +a: Types.Ask
) -> {
  Crits.Crit.wf(~List<&2, RKnown.Found>, m, 0n) == True{}: Bool
} -> {
  RKnown.Ids.made(
    RKnown.Ids.put(RKnown.Ids{m, n}, e),
    a
  )
    == Bool.or(RKnown.Entry.made_by(a, e), RKnown.Ids.made(RKnown.Ids{m, n}, a)): Bool
}:
  w =>
    %Equal.sym(
      Maybe<&2, List<&2, RKnown.Found>>,
      Crits.Crit.get(
        List<&2, RKnown.Found>,
        Crits.Crit.upsert(
          ~List<&2, RKnown.Found>,
          ~RKnown.Ids.join,
          m,
          RKnown.Id.key(RLines.Entry.id(e)),
          [RKnown.Found{n, e}]
        ),
        RKnown.Id.key(RLines.Ask.id(a))
      ),
      Bool.pick(
        Maybe<&2, List<&2, RKnown.Found>>,
        Crits.Key.is_eq(RKnown.Id.key(RLines.Ask.id(a)), RKnown.Id.key(RLines.Entry.id(e))),
        Some{
          Crits.Crit.merge(
            ~List<&2, RKnown.Found>,
            ~RKnown.Ids.join,
            Crits.Crit.get(List<&2, RKnown.Found>, m, RKnown.Id.key(RLines.Entry.id(e))),
            [RKnown.Found{n, e}]
          )
        },
        Crits.Crit.get(List<&2, RKnown.Found>, m, RKnown.Id.key(RLines.Ask.id(a)))
      ),
      Map.get_put(
        m,
        RKnown.Id.key(RLines.Entry.id(e)),
        RKnown.Found{n, e},
        RKnown.Id.key(RLines.Ask.id(a))
      )(w)
    ): {
      RKnown.Ids.made.of(
        _,
        a
      )
        == Bool.or(RKnown.Entry.made_by(a, e), RKnown.Ids.made(RKnown.Ids{m, n}, a)): Bool
    }
    Lists.Bool.by(
      h => {
        RKnown.Ids.made.of(
          Bool.pick(
            Maybe<&2, List<&2, RKnown.Found>>,
            h,
            Some{
              Crits.Crit.merge(
                ~List<&2, RKnown.Found>,
                ~RKnown.Ids.join,
                Crits.Crit.get(List<&2, RKnown.Found>, m, RKnown.Id.key(RLines.Entry.id(e))),
                [RKnown.Found{n, e}]
              )
            },
            Crits.Crit.get(List<&2, RKnown.Found>, m, RKnown.Id.key(RLines.Ask.id(a)))
          ),
          a
        )
          == Bool.or(RKnown.Entry.made_by(a, e), RKnown.Ids.made(RKnown.Ids{m, n}, a)): Bool
      },
      Crits.Key.is_eq(RKnown.Id.key(RLines.Ask.id(a)), RKnown.Id.key(RLines.Entry.id(e))),
      et => (
        %Crits.Key.is_eq_sound(RKnown.Id.key(RLines.Ask.id(a)), RKnown.Id.key(RLines.Entry.id(e)))(et): {RKnown.Ids.made.of(Some{Crits.Crit.merge(~List<&2, RKnown.Found>, ~RKnown.Ids.join, Crits.Crit.get(List<&2, RKnown.Found>, m, _), [RKnown.Found{n, e}])}, a) == Bool.or(RKnown.Entry.made_by(a, e), RKnown.Ids.made(RKnown.Ids{m, n}, a)): Bool}
        Bucket.made_put(Crits.Crit.get(List<&2, RKnown.Found>, m, RKnown.Id.key(RLines.Ask.id(a))), n, e, a)),
      ef => (
        %Equal.sym(Bool, Ledgers.Id.is_eq(RLines.Entry.id(e), RLines.Ask.id(a)), False{}, Key.ne_id(RLines.Entry.id(e), RLines.Ask.id(a))(ef)): {RKnown.Ids.made(RKnown.Ids{m, n}, a) == Bool.or(List.all.if(u => Coded.Ask.is_eq(RLines.Entry.ask(e), a), _), RKnown.Ids.made(RKnown.Ids{m, n}, a)): Bool}
        {==})
    )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof does not run
# an ask made one of the versions by id with the versions vs exactly when it
# made one of vs, or one of the versions before
def Ids.go_made(
  vs: List<&2, Types.Entry>,
  +m: Crits.Crit<List<&2, RKnown.Found>>,
  +n: Nat,
  +a: Types.Ask
) -> {
  Crits.Crit.wf(~List<&2, RKnown.Found>, m, 0n) == True{}: Bool
} -> {
  RKnown.Ids.made(
    RKnown.Ids.go(vs, RKnown.Ids{m, n}),
    a
  )
    == Bool.or(
      Shared.List.some(~Types.Entry, ~Types.Ask, ~RKnown.Entry.made_by, vs, a),
      RKnown.Ids.made(RKnown.Ids{m, n}, a)
    ): Bool
}:
  match vs:
    case Nil{}:
      w => {==}
    case Con{+e, +rest}:
      +w => Equal.trans(
        Bool,
        RKnown.Ids.made(RKnown.Ids.go(rest, RKnown.Ids.put(RKnown.Ids{m, n}, e)), a),
        Bool.or(
          Shared.List.some(~Types.Entry, ~Types.Ask, ~RKnown.Entry.made_by, rest, a),
          RKnown.Ids.made(RKnown.Ids.put(RKnown.Ids{m, n}, e), a)
        ),
        Bool.or(
          Shared.List.some(~Types.Entry, ~Types.Ask, ~RKnown.Entry.made_by, e <> rest, a),
          RKnown.Ids.made(RKnown.Ids{m, n}, a)
        ),
        Ids.go_made(
          rest,
          Crits.Crit.upsert(
            ~List<&2, RKnown.Found>,
            ~RKnown.Ids.join,
            m,
            RKnown.Id.key(RLines.Entry.id(e)),
            [RKnown.Found{n, e}]
          ),
          1n+n,
          a
        )(
          Crits.Crit.upsert_wf(
            ~List<&2, RKnown.Found>,
            ~RKnown.Ids.join,
            m,
            RKnown.Id.key(RLines.Entry.id(e)),
            [RKnown.Found{n, e}]
          )(w)
        ),
        (
          %Equal.sym(Bool, RKnown.Ids.made(RKnown.Ids.put(RKnown.Ids{m, n}, e), a), Bool.or(RKnown.Entry.made_by(a, e), RKnown.Ids.made(RKnown.Ids{m, n}, a)), Ids.put_made(m, n, e, a)(w)): {Bool.or(Shared.List.some(~Types.Entry, ~Types.Ask, ~RKnown.Entry.made_by, rest, a), _) == Bool.or(List.any.if(u => Shared.List.some(~Types.Entry, ~Types.Ask, ~RKnown.Entry.made_by, rest, a), RKnown.Entry.made_by(a, e)), RKnown.Ids.made(RKnown.Ids{m, n}, a)): Bool}
          Lists.Bool.by(b => {Bool.or(Shared.List.some(~Types.Entry, ~Types.Ask, ~RKnown.Entry.made_by, rest, a), Bool.or(b, RKnown.Ids.made(RKnown.Ids{m, n}, a))) == Bool.or(List.any.if(u => Shared.List.some(~Types.Entry, ~Types.Ask, ~RKnown.Entry.made_by, rest, a), b), RKnown.Ids.made(RKnown.Ids{m, n}, a)): Bool}, RKnown.Entry.made_by(a, e), et => Shared.Bool.or_true_right(Shared.List.some(~Types.Entry, ~Types.Ask, ~RKnown.Entry.made_by, rest, a)), ef => {==}))
      )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# an ask made one of the versions vs by id exactly when it made one of vs
def Ids.of_made(
  +vs: List<&2, Types.Entry>,
  +a: Types.Ask
) -> {
  RKnown.Ids.made(
    RKnown.Ids.of(vs),
    a
  )
    == Shared.List.some(~Types.Entry, ~Types.Ask, ~RKnown.Entry.made_by, vs, a): Bool
}:
  Equal.trans(
    Bool,
    RKnown.Ids.made(RKnown.Ids.of(vs), a),
    Bool.or(Shared.List.some(~Types.Entry, ~Types.Ask, ~RKnown.Entry.made_by, vs, a), False{}),
    Shared.List.some(~Types.Entry, ~Types.Ask, ~RKnown.Entry.made_by, vs, a),
    Ids.go_made(vs, Crits.Crit.new(List<&2, RKnown.Found>), 0n, a)({==}),
    Equal.sym(
      Bool,
      Shared.List.some(~Types.Entry, ~Types.Ask, ~RKnown.Entry.made_by, vs, a),
      Bool.or(Shared.List.some(~Types.Entry, ~Types.Ask, ~RKnown.Entry.made_by, vs, a), False{}),
      Shared.Bool.or_false(Shared.List.some(~Types.Entry, ~Types.Ask, ~RKnown.Entry.made_by, vs, a))
    )
  )

# the count of the versions by id with the versions vs: as many more
def Ids.go_count(
  vs: List<&2, Types.Entry>,
  +m: Crits.Crit<List<&2, RKnown.Found>>,
  +n: Nat
) -> {
  RKnown.Ids.count(
    RKnown.Ids.go(vs, RKnown.Ids{m, n})
  )
    == Nat.add(List.length(&2, Types.Entry, vs), n): Nat
}:
  match vs:
    case Nil{}:
      {==}
    case Con{+e, +rest}:
      %Shared.Nat.add_succ(
        List.length(&2, Types.Entry, rest),
        n
      ): {RKnown.Ids.count(RKnown.Ids.go(rest, RKnown.Ids.put(RKnown.Ids{m, n}, e))) == _: Nat}
      Ids.go_count(
        rest,
        Crits.Crit.upsert(
          ~List<&2, RKnown.Found>,
          ~RKnown.Ids.join,
          m,
          RKnown.Id.key(RLines.Entry.id(e)),
          [RKnown.Found{n, e}]
        ),
        1n+n
      )

# the count of the versions vs by id is the number of vs
def Ids.of_count(
  +vs: List<&2, Types.Entry>
) -> {RKnown.Ids.count(RKnown.Ids.of(vs)) == List.length(&2, Types.Entry, vs): Nat}:
  Equal.trans(
    Nat,
    RKnown.Ids.count(RKnown.Ids.of(vs)),
    Nat.add(List.length(&2, Types.Entry, vs), 0n),
    List.length(&2, Types.Entry, vs),
    Ids.go_count(vs, Crits.Crit.new(List<&2, RKnown.Found>), 0n),
    Shared.Nat.add_zero(List.length(&2, Types.Entry, vs))
  )

# the first entry of a right table is right
def Ok.head(
  e: RKnown.Kept,
  rest: RKnown.Known(),
  +s: RFacts.Plain()
) -> {
  RContents.Known.ok(e <> rest, s) == True{}: Bool
} -> {RContents.Kept.ok(s, e) == True{}: Bool}:
  Shared.Bool.and_true_left(RContents.Kept.ok(s, e), RContents.Known.ok(rest, s))

# a right table without its first entry is right
def Ok.tail(
  e: RKnown.Kept,
  rest: RKnown.Known(),
  +s: RFacts.Plain()
) -> {
  RContents.Known.ok(e <> rest, s) == True{}: Bool
} -> {RContents.Known.ok(rest, s) == True{}: Bool}:
  Shared.Bool.and_true_right(RContents.Kept.ok(s, e), RContents.Known.ok(rest, s))

# a right table with a right entry before it is right
def Ok.cons(
  e: RKnown.Kept,
  rest: RKnown.Known(),
  +s: RFacts.Plain()
) -> {
  RContents.Kept.ok(s, e) == True{}: Bool
} -> {
  RContents.Known.ok(rest, s) == True{}: Bool
} -> {RContents.Known.ok(e <> rest, s) == True{}: Bool}:
  Shared.Bool.and_both(RContents.Kept.ok(s, e), RContents.Known.ok(rest, s))

# the contents that are the first entry of a right table are right
def Stock.head(
  +m: Crits.Crit<RKnown.Held>,
  +q: Nat,
  rest: RKnown.Known(),
  +s: RFacts.Plain()
) -> {
  RContents.Known.ok(RKnown.Stock{m, q} <> rest, s) == True{}: Bool
} -> {Orders.Crit.every(~RKnown.Held, ~RFacts.Plain(), ~RContents.Held.ok, m, s) == True{}: Bool}:
  ok => Shared.Bool.and_true_left(
    Orders.Crit.every(~RKnown.Held, ~RFacts.Plain(), ~RContents.Held.ok, m, s),
    Nat.is_le(q, RFacts.Facts.fuel(s))
  )(Ok.head(RKnown.Stock{m, q}, rest, s)(ok))

# the number of the contents that are the first entry of a right table is at
# most the count of the facts
def Stock.head_low(
  +m: Crits.Crit<RKnown.Held>,
  +q: Nat,
  rest: RKnown.Known(),
  +s: RFacts.Plain()
) -> {
  RContents.Known.ok(RKnown.Stock{m, q} <> rest, s) == True{}: Bool
} -> {Nat.is_le(q, RFacts.Facts.fuel(s)) == True{}: Bool}:
  ok => Shared.Bool.and_true_right(
    Orders.Crit.every(~RKnown.Held, ~RFacts.Plain(), ~RContents.Held.ok, m, s),
    Nat.is_le(q, RFacts.Facts.fuel(s))
  )(Ok.head(RKnown.Stock{m, q}, rest, s)(ok))

# a right table with right contents before it, whose number is at most the
# count of the facts, is right
def Stock.cons(
  +m: Crits.Crit<RKnown.Held>,
  +q: Nat,
  rest: RKnown.Known(),
  +s: RFacts.Plain()
) -> {
  Orders.Crit.every(~RKnown.Held, ~RFacts.Plain(), ~RContents.Held.ok, m, s) == True{}: Bool
} -> {
  Nat.is_le(q, RFacts.Facts.fuel(s)) == True{}: Bool
} -> {
  RContents.Known.ok(rest, s) == True{}: Bool
} -> {RContents.Known.ok(RKnown.Stock{m, q} <> rest, s) == True{}: Bool}:
  he => hq => ok => Ok.cons(
    RKnown.Stock{m, q},
    rest,
    s
  )(
    Shared.Bool.and_both(
      Orders.Crit.every(~RKnown.Held, ~RFacts.Plain(), ~RContents.Held.ok, m, s),
      Nat.is_le(q, RFacts.Facts.fuel(s))
    )(he)(hq)
  )(ok)

# the state that a right table holds for a line is the state that the facts
# give the line
def Known.find_ok(
  kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +st: RLines.State
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RKnown.Known.find(kn, c) == Some{st}: Maybe<&2, RLines.State>
} -> {RLines.Line.state(s, c) == Some{st}: Maybe<&2, RLines.State>}:
  match kn:
    case Nil{}:
      ok => e => Empty.absurd(
        {RLines.Line.state(s, c) == Some{st}: Maybe<&2, RLines.State>},
        Shared.Maybe.none_ne_some(RLines.State, st, e)
      )
    case Con{RKnown.Kept{+c2, +st2}, +rest}:
      +ok => Lists.Bool.by(
        b => {
          Shared.Bool.when(
            Maybe<&2, RLines.State>,
            b,
            u => Some{st2},
            u => RKnown.Known.find(rest, c)
          )
            == Some{st}: Maybe<&2, RLines.State>
        } -> {RLines.Line.state(s, c) == Some{st}: Maybe<&2, RLines.State>},
        Ledgers.Line.is_eq(c2, c),
        +et => +e => (
          %Ledgers.Line.is_eq_sound(c2, c)(et): {RLines.Line.state(s, _) == Some{st}: Maybe<&2, RLines.State>}
          %e: {RLines.Line.state(s, c2) == _: Maybe<&2, RLines.State>}
          State.fits_sound(RLines.Line.state(s, c2), st2)(Shared.Bool.and_true_left(RKnown.State.fits(RLines.Line.state(s, c2), st2), RContents.Known.ok(rest, s))(ok))),
        ef => e => Known.find_ok(
          rest,
          s,
          c,
          st
        )(
          Shared.Bool.and_true_right(
            RKnown.State.fits(RLines.Line.state(s, c2), st2),
            RContents.Known.ok(rest, s)
          )(ok)
        )(e)
      )
    case Con{RKnown.Stock{+m2, +lwm2}, +rest}:
      ok => e => Known.find_ok(rest, s, c, st)(Ok.tail(RKnown.Stock{m2, lwm2}, rest, s)(ok))(e)
    case Con{RKnown.Ruled{+c2, +zu2, +u2}, +rest}:
      ok => e => Known.find_ok(rest, s, c, st)(Ok.tail(RKnown.Ruled{c2, zu2, u2}, rest, s)(ok))(e)
    case Con{RKnown.Made{+c2, +y2}, +rest}:
      ok => e => Known.find_ok(rest, s, c, st)(Ok.tail(RKnown.Made{c2, y2}, rest, s)(ok))(e)
    case Con{RKnown.Open{+fs2, +pk2, +tx9, +mtx9}, +rest}:
      ok => e => Known.find_ok(
        rest,
        s,
        c,
        st
      )(Ok.tail(RKnown.Open{fs2, pk2, tx9, mtx9}, rest, s)(ok))(e)

# the ids that a right table holds for a line fit the state that the facts
# give the line
def Known.ids_ok(
  kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +x: RKnown.Ids
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RKnown.Known.ids(kn, c) == Some{x}: Maybe<&2, RKnown.Ids>
} -> {RKnown.Made.fits(RLines.Line.state(s, c), x) == True{}: Bool}:
  match kn:
    case Nil{}:
      ok => e => Empty.absurd(
        {RKnown.Made.fits(RLines.Line.state(s, c), x) == True{}: Bool},
        Shared.Maybe.none_ne_some(RKnown.Ids, x, e)
      )
    case Con{RKnown.Kept{+c2, +st2}, +rest}:
      ok => e => Known.ids_ok(rest, s, c, x)(Ok.tail(RKnown.Kept{c2, st2}, rest, s)(ok))(e)
    case Con{RKnown.Stock{+m2, +lwm2}, +rest}:
      ok => e => Known.ids_ok(rest, s, c, x)(Ok.tail(RKnown.Stock{m2, lwm2}, rest, s)(ok))(e)
    case Con{RKnown.Ruled{+c2, +zu2, +u2}, +rest}:
      ok => e => Known.ids_ok(rest, s, c, x)(Ok.tail(RKnown.Ruled{c2, zu2, u2}, rest, s)(ok))(e)
    case Con{RKnown.Open{+fs2, +pk2, +tx9, +mtx9}, +rest}:
      ok => e => Known.ids_ok(
        rest,
        s,
        c,
        x
      )(Ok.tail(RKnown.Open{fs2, pk2, tx9, mtx9}, rest, s)(ok))(e)
    case Con{RKnown.Made{+c2, +y2}, +rest}:
      +ok => Lists.Bool.by(
        b => {
          Shared.Bool.when(
            Maybe<&2, RKnown.Ids>,
            b,
            w => Some{y2},
            w => RKnown.Known.ids(rest, c)
          )
            == Some{x}: Maybe<&2, RKnown.Ids>
        } -> {RKnown.Made.fits(RLines.Line.state(s, c), x) == True{}: Bool},
        Ledgers.Line.is_eq(c2, c),
        +et => +e => (
          %Ledgers.Line.is_eq_sound(c2, c)(et): {RKnown.Made.fits(RLines.Line.state(s, _), x) == True{}: Bool}
          %Shared.Maybe.some_inj(RKnown.Ids, y2, x, e): {RKnown.Made.fits(RLines.Line.state(s, c2), _) == True{}: Bool}
          Ok.head(RKnown.Made{c2, y2}, rest, s)(ok)),
        ef => e => Known.ids_ok(rest, s, c, x)(Ok.tail(RKnown.Made{c2, y2}, rest, s)(ok))(e)
      )

# a right table changes no test of whether a request made a version of a
# line, said of the versions that the facts give the line
def Known.made_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +vs: List<&2, Types.Entry>,
  +k: Nat,
  +i: Ledgers.Id
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RLines.Line.state(s, c) == Some{RLines.State{vs, k}}: Maybe<&2, RLines.State>
} -> {
  RKnown.Known.made(
    kn,
    c,
    vs,
    i
  )
    == Shared.List.some(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, vs, i): Bool
}:
  ok => e => Lists.Maybe.by(
    RKnown.Ids,
    m => {
      RKnown.Made.in(
        m,
        vs,
        i
      )
        == Shared.List.some(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, vs, i): Bool
    },
    RKnown.Known.ids(kn, c),
    en => {==},
    +y => ey => (
      %Equal.sym(RKnown.Ids, y, RKnown.Ids.of(vs), Made.fits_sound(RLines.Line.state(s, c), y, vs, k)(e)(Known.ids_ok(kn, s, c, y)(ok)(ey))): {RKnown.Ids.has(_, i) == Shared.List.some(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, vs, i): Bool}
      Ids.of_has(vs, i))
  )

# the versions by id that fit a state are those of its versions
def Made.at(
  +y: RKnown.Ids,
  -m: Maybe<&2, RLines.State>,
  st: RLines.State
) -> {
  m == Some{st}: Maybe<&2, RLines.State>
} -> {
  RKnown.Made.fits(m, y) == True{}: Bool
} -> {y == RKnown.Ids.of(RLines.State.versions(st)): RKnown.Ids}:
  match st:
    case RLines.State{+vs, k}:
      e => h => Made.fits_sound(m, y, vs, k)(e)(h)

# what holds of the versions y by id that a right table holds for the line
# c: the line has a state, and y is its versions by id
def Made.case(
  -P: Type,
  kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +y: RKnown.Ids,
  ok: {RContents.Known.ok(kn, s) == True{}: Bool},
  ey: {RKnown.Known.ids(kn, c) == Some{y}: Maybe<&2, RKnown.Ids>},
  k: @st: RLines.State -> {
    RLines.Line.state(s, c) == Some{st}: Maybe<&2, RLines.State>
  } -> {y == RKnown.Ids.of(RLines.State.versions(st)): RKnown.Ids} -> P
) -> P:
  Lists.Maybe.by(
    RLines.State,
    m => {RKnown.Made.fits(m, y) == True{}: Bool} -> P,
    RLines.Line.state(s, c),
    en => h => Empty.absurd(P, Shared.Bool.false_ne_true(h)),
    +st => est => h => k(st)(est)(Made.at(y, Some{st}, st)({==})(h))
  )(Known.ids_ok(kn, s, c, y)(ok)(ey))

# Rule.same is True for a rule and itself
def Rule.same_refl(a: RLines.Rule) -> {RKnown.Rule.same(a, a) == True{}: Bool}:
  match a:
    case RLines.Rule{+g, +ns}:
      Shared.Bool.and_both(
        Shared.Maybe.is_eq(~String, ~String.eq, g, g),
        Shared.List.is_eq(~String, ~String.eq, ns, ns)
      )(
        Ledgers.Sub.is_eq_refl(g)
      )(Shared.List.is_eq_refl(~String, ~String.eq, ~Texts.String.laws(), ns))

# Rule.same is True only for equal rules
def Rule.same_sound(
  a: RLines.Rule,
  b: RLines.Rule
) -> {RKnown.Rule.same(a, b) == True{}: Bool} -> {a == b: RLines.Rule}:
  match a b:
    case RLines.Rule{+g1, +n1} RLines.Rule{+g2, +n2}:
      +h => (
        %Ledgers.Sub.is_eq_sound(g1, g2)(Shared.Bool.and_true_left(Shared.Maybe.is_eq(~String, ~String.eq, g1, g2), Shared.List.is_eq(~String, ~String.eq, n1, n2))(h)): {RLines.Rule{g1, n1} == RLines.Rule{_, n2}: RLines.Rule}
        %Shared.List.is_eq_sound(~String, ~String.eq, ~Texts.String.laws(), n1, n2)(Shared.Bool.and_true_right(Shared.Maybe.is_eq(~String, ~String.eq, g1, g2), Shared.List.is_eq(~String, ~String.eq, n1, n2))(h)): {RLines.Rule{g1, n1} == RLines.Rule{g1, _}: RLines.Rule}
        {==})

# a rule that fits u is u
def Rule.fits_sound(
  m: Maybe<&2, RLines.Rule>,
  +u: RLines.Rule
) -> {RKnown.Rule.fits(m, u) == True{}: Bool} -> {m == Some{u}: Maybe<&2, RLines.Rule>}:
  match m:
    case None{}:
      h => Empty.absurd({None{} == Some{u}: Maybe<&2, RLines.Rule>}, Shared.Bool.false_ne_true(h))
    case Some{+x}:
      h => Equal.cong(
        RLines.Rule,
        Maybe<&2, RLines.Rule>,
        y => Some{y},
        x,
        u,
        Rule.same_sound(x, u)(h)
      )

# the rule u fits what is u
def Rule.fits_of(
  m: Maybe<&2, RLines.Rule>,
  +u: RLines.Rule
) -> {m == Some{u}: Maybe<&2, RLines.Rule>} -> {RKnown.Rule.fits(m, u) == True{}: Bool}:
  e => (
    %Equal.sym(Maybe<&2, RLines.Rule>, m, Some{u}, e): {RKnown.Rule.fits(_, u) == True{}: Bool}
    Rule.same_refl(u))

# the rule that a right table holds for a line is the rule of the next
# version of the line in the facts
def Known.ruled_ok(
  kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +u: RLines.Rule
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RKnown.Known.ruled(kn, c) == Some{u}: Maybe<&2, RLines.Rule>
} -> {
  RKnown.Known.rule.next(
    RKnown.Known.none(),
    s,
    c,
    RLines.Line.state(s, c)
  )
    == Some{u}: Maybe<&2, RLines.Rule>
}:
  match kn:
    case Nil{}:
      ok => e => Empty.absurd(
        {
          RKnown.Known.rule.next(
            RKnown.Known.none(),
            s,
            c,
            RLines.Line.state(s, c)
          )
            == Some{u}: Maybe<&2, RLines.Rule>
        },
        Shared.Maybe.none_ne_some(RLines.Rule, u, e)
      )
    case Con{RKnown.Kept{+c2, +st2}, +rest}:
      ok => e => Known.ruled_ok(rest, s, c, u)(Ok.tail(RKnown.Kept{c2, st2}, rest, s)(ok))(e)
    case Con{RKnown.Stock{+m2, +lwm2}, +rest}:
      ok => e => Known.ruled_ok(rest, s, c, u)(Ok.tail(RKnown.Stock{m2, lwm2}, rest, s)(ok))(e)
    case Con{RKnown.Ruled{+c2, +zu2, +u2}, +rest}:
      +ok => Lists.Bool.by(
        b => {
          Shared.Bool.when(
            Maybe<&2, RLines.Rule>,
            b,
            w => Some{u2},
            w => RKnown.Known.ruled(rest, c)
          )
            == Some{u}: Maybe<&2, RLines.Rule>
        } -> {
          RKnown.Known.rule.next(
            RKnown.Known.none(),
            s,
            c,
            RLines.Line.state(s, c)
          )
            == Some{u}: Maybe<&2, RLines.Rule>
        },
        Ledgers.Line.is_eq(c2, c),
        +et => +e => (
          %Ledgers.Line.is_eq_sound(c2, c)(et): {RKnown.Known.rule.next(RKnown.Known.none(), s, _, RLines.Line.state(s, _)) == Some{u}: Maybe<&2, RLines.Rule>}
          %Shared.Maybe.some_inj(RLines.Rule, u2, u, e): {RKnown.Known.rule.next(RKnown.Known.none(), s, c2, RLines.Line.state(s, c2)) == Some{_}: Maybe<&2, RLines.Rule>}
          Rule.fits_sound(RKnown.Known.rule.next(RKnown.Known.none(), s, c2, RLines.Line.state(s, c2)), u2)(Shared.Bool.and_true_left(RKnown.Rule.fits(RKnown.Known.rule.next(RKnown.Known.none(), s, c2, RLines.Line.state(s, c2)), u2), RKnown.Era.fits(RLines.Line.state(s, c2), c2, zu2))(Ok.head(RKnown.Ruled{c2, zu2, u2}, rest, s)(ok)))),
        ef => e => Known.ruled_ok(rest, s, c, u)(Ok.tail(RKnown.Ruled{c2, zu2, u2}, rest, s)(ok))(e)
      )
    case Con{RKnown.Made{+c2, +y2}, +rest}:
      ok => e => Known.ruled_ok(rest, s, c, u)(Ok.tail(RKnown.Made{c2, y2}, rest, s)(ok))(e)
    case Con{RKnown.Open{+fs2, +pk2, +tx9, +mtx9}, +rest}:
      ok => e => Known.ruled_ok(
        rest,
        s,
        c,
        u
      )(Ok.tail(RKnown.Open{fs2, pk2, tx9, mtx9}, rest, s)(ok))(e)

# the era that a right table holds for a line is the era of the next version
# of the line in the facts
def Known.era_ok(
  kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +m: Nat
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RKnown.Known.era(kn, c) == Some{m}: Maybe<&2, Nat>
} -> {RKnown.Era.fits(RLines.Line.state(s, c), c, m) == True{}: Bool}:
  match kn:
    case Nil{}:
      ok => e => Empty.absurd(
        {RKnown.Era.fits(RLines.Line.state(s, c), c, m) == True{}: Bool},
        Shared.Maybe.none_ne_some(Nat, m, e)
      )
    case Con{RKnown.Kept{+c2, +st2}, +rest}:
      ok => e => Known.era_ok(rest, s, c, m)(Ok.tail(RKnown.Kept{c2, st2}, rest, s)(ok))(e)
    case Con{RKnown.Stock{+m2, +lwm2}, +rest}:
      ok => e => Known.era_ok(rest, s, c, m)(Ok.tail(RKnown.Stock{m2, lwm2}, rest, s)(ok))(e)
    case Con{RKnown.Ruled{+c2, +zu2, +u2}, +rest}:
      +ok => Lists.Bool.by(
        b => {
          Shared.Bool.when(
            Maybe<&2, Nat>,
            b,
            w => Some{zu2},
            w => RKnown.Known.era(rest, c)
          )
            == Some{m}: Maybe<&2, Nat>
        } -> {RKnown.Era.fits(RLines.Line.state(s, c), c, m) == True{}: Bool},
        Ledgers.Line.is_eq(c2, c),
        +et => +e => (
          %Ledgers.Line.is_eq_sound(c2, c)(et): {RKnown.Era.fits(RLines.Line.state(s, _), _, m) == True{}: Bool}
          %Shared.Maybe.some_inj(Nat, zu2, m, e): {RKnown.Era.fits(RLines.Line.state(s, c2), c2, _) == True{}: Bool}
          Shared.Bool.and_true_right(RKnown.Rule.fits(RKnown.Known.rule.next(RKnown.Known.none(), s, c2, RLines.Line.state(s, c2)), u2), RKnown.Era.fits(RLines.Line.state(s, c2), c2, zu2))(Ok.head(RKnown.Ruled{c2, zu2, u2}, rest, s)(ok))),
        ef => e => Known.era_ok(rest, s, c, m)(Ok.tail(RKnown.Ruled{c2, zu2, u2}, rest, s)(ok))(e)
      )
    case Con{RKnown.Made{+c2, +y2}, +rest}:
      ok => e => Known.era_ok(rest, s, c, m)(Ok.tail(RKnown.Made{c2, y2}, rest, s)(ok))(e)
    case Con{RKnown.Open{+fs2, +pk2, +tx9, +mtx9}, +rest}:
      ok => e => Known.era_ok(
        rest,
        s,
        c,
        m
      )(Ok.tail(RKnown.Open{fs2, pk2, tx9, mtx9}, rest, s)(ok))(e)

# the state of a line, computed with the state rs and k of its store, is the
# state that the facts give it
def Known.fresh_at_ok(
  +s: RFacts.Plain(),
  c: Ledgers.Line,
  +rs: List<&2, Types.Entry>,
  +k: Nat
) -> {
  RLines.Line.state(s, RKnown.Known.root(c)) == Some{RLines.State{rs, k}}: Maybe<&2, RLines.State>
} -> {RKnown.Known.fresh.at(s, c, rs, k) == RLines.Line.state(s, c): Maybe<&2, RLines.State>}:
  match c:
    case Ledgers.Line{+h, None{}}:
      e => Equal.sym(
        Maybe<&2, RLines.State>,
        RLines.Line.state(s, Ledgers.Line{h, None{}}),
        Some{RLines.State{rs, k}},
        e
      )
    case Ledgers.Line{+h, Some{+b}}:
      e => (
        %Equal.sym(Maybe<&2, RLines.State>, RLines.Store.state(s, h), Some{RLines.State{rs, k}}, e): {RLines.Branch.state(s, Ledgers.Line{h, Some{b}}, Some{rs}) == RLines.Branch.state(s, Ledgers.Line{h, Some{b}}, Maybe.map(&2, RLines.State, List<&2, Types.Entry>, RLines.State.versions, _)): Maybe<&2, RLines.State>}
        {==})

# the state of a line, computed with the state x that a right table holds
# for its store, is the state that the facts give it
def Known.fresh_ok.at(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  x: RLines.State
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RKnown.Known.find(kn, RKnown.Known.root(c)) == Some{x}: Maybe<&2, RLines.State>
} -> {RKnown.Known.fresh.of(Some{x}, s, c) == RLines.Line.state(s, c): Maybe<&2, RLines.State>}:
  match x:
    case RLines.State{+R, +k}:
      ok => e => Known.fresh_at_ok(
        s,
        c,
        R,
        k
      )(Known.find_ok(kn, s, RKnown.Known.root(c), RLines.State{R, k})(ok)(e))

# the state of a line, computed with the state that a right table holds for
# its store, is the state that the facts give it
def Known.fresh_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {RKnown.Known.fresh(kn, s, c) == RLines.Line.state(s, c): Maybe<&2, RLines.State>}:
  ok => Lists.Maybe.by(
    RLines.State,
    m => {RKnown.Known.fresh.of(m, s, c) == RLines.Line.state(s, c): Maybe<&2, RLines.State>},
    RKnown.Known.find(kn, RKnown.Known.root(c)),
    en => {==},
    x => ex => Known.fresh_ok.at(kn, s, c, x)(ok)(ex)
  )

# a right table changes no read of the state of a line
def Known.state_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {RKnown.Known.state(kn, s, c) == RLines.Line.state(s, c): Maybe<&2, RLines.State>}:
  +ok => Lists.Maybe.by(
    RLines.State,
    m => {RKnown.Known.state.of(m, kn, s, c) == RLines.Line.state(s, c): Maybe<&2, RLines.State>},
    RKnown.Known.find(kn, c),
    en => Known.fresh_ok(kn, s, c)(ok),
    +x => ex => Equal.sym(
      Maybe<&2, RLines.State>,
      RLines.Line.state(s, c),
      Some{x},
      Known.find_ok(kn, s, c, x)(ok)(ex)
    )
  )

# a right table changes no read of the versions of a line
def Known.versions_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RKnown.Known.versions(kn, s, c) == RLines.Line.versions(s, c): Maybe<&2, List<&2, Types.Entry>>
}:
  ok => Equal.cong(
    Maybe<&2, RLines.State>,
    Maybe<&2, List<&2, Types.Entry>>,
    m => Maybe.map(&2, RLines.State, List<&2, Types.Entry>, RLines.State.versions, m),
    RKnown.Known.state(kn, s, c),
    RLines.Line.state(s, c),
    Known.state_ok(kn, s, c)(ok)
  )

# a right table changes no read of a version of a line
def Known.at_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +k: Nat
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {RKnown.Known.at(kn, s, c, k) == RLines.Line.at(s, c, k): Maybe<&2, Types.Entry>}:
  ok => Equal.cong(
    Maybe<&2, List<&2, Types.Entry>>,
    Maybe<&2, Types.Entry>,
    m => RLines.Line.at.of(m, k),
    RKnown.Known.versions(kn, s, c),
    RLines.Line.versions(s, c),
    Known.versions_ok(kn, s, c)(ok)
  )

# a right table changes no read of the versions of a store
def Known.store_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +h: Hashes.Hash
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RKnown.Known.store(kn, s, h) == RLines.Store.versions(s, h): Maybe<&2, List<&2, Types.Entry>>
}:
  ok => Known.versions_ok(kn, s, Ledgers.Line{h, None{}})(ok)

# the rule after the versions vs of a line, with the versions rs of its
# store, is the rule that the facts give
def Known.rule_at_ok(
  +s: RFacts.Plain(),
  c: Ledgers.Line,
  +vs: List<&2, Types.Entry>,
  +rs: List<&2, Types.Entry>,
  +k: Nat
) -> {
  RLines.Line.state(s, RKnown.Known.root(c)) == Some{RLines.State{rs, k}}: Maybe<&2, RLines.State>
} -> {RKnown.Known.rule.at(c, vs, rs) == RLines.Rule.after(s, c, vs): Maybe<&2, RLines.Rule>}:
  match c:
    case Ledgers.Line{+h, None{}}:
      e => {==}
    case Ledgers.Line{+h, Some{+b}}:
      e => (
        %Equal.sym(Maybe<&2, RLines.State>, RLines.Store.state(s, h), Some{RLines.State{rs, k}}, e): {RLines.Line.rule(Some{rs}, Ledgers.Line{h, Some{b}}, vs) == RLines.Rule.after.of(Ledgers.Line{h, Some{b}}, vs, Maybe.map(&2, RLines.State, List<&2, Types.Entry>, RLines.State.versions, _)): Maybe<&2, RLines.Rule>}
        {==})

# the rule after the versions vs of a line, with the state x that a right
# table holds for its store, is the rule that the facts give
def Known.rule_ok.at(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +vs: List<&2, Types.Entry>,
  x: RLines.State
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RKnown.Known.find(kn, RKnown.Known.root(c)) == Some{x}: Maybe<&2, RLines.State>
} -> {
  RKnown.Known.rule.of(Some{x}, s, c, vs) == RLines.Rule.after(s, c, vs): Maybe<&2, RLines.Rule>
}:
  match x:
    case RLines.State{+R, +k}:
      ok => e => Known.rule_at_ok(
        s,
        c,
        vs,
        R,
        k
      )(Known.find_ok(kn, s, RKnown.Known.root(c), RLines.State{R, k})(ok)(e))

# a right table changes no read of the rule of the next version of a line
def Known.rule_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +vs: List<&2, Types.Entry>
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {RKnown.Known.rule(kn, s, c, vs) == RLines.Rule.after(s, c, vs): Maybe<&2, RLines.Rule>}:
  ok => Lists.Maybe.by(
    RLines.State,
    m => {RKnown.Known.rule.of(m, s, c, vs) == RLines.Rule.after(s, c, vs): Maybe<&2, RLines.Rule>},
    RKnown.Known.find(kn, RKnown.Known.root(c)),
    en => {==},
    x => ex => Known.rule_ok.at(kn, s, c, vs, x)(ok)(ex)
  )

# A table stays right
# -------------------

# a right table with the state that the facts give a line is right
def Known.put_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  m: Maybe<&2, RLines.State>
) -> {
  RLines.Line.state(s, c) == m: Maybe<&2, RLines.State>
} -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {RContents.Known.ok(RKnown.Known.put(kn, c, m), s) == True{}: Bool}:
  match m:
    case None{}:
      e => ok => ok
    case Some{+st}:
      e => ok => Shared.Bool.and_both(
        RKnown.State.fits(RLines.Line.state(s, c), st),
        RContents.Known.ok(kn, s)
      )(State.fits_of(RLines.Line.state(s, c), st)(e))(ok)

# a right table that learns the state of a line is right
def Known.learn_one_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {RContents.Known.ok(RKnown.Known.learn.one(kn, s, c), s) == True{}: Bool}:
  +ok => Lists.Maybe.by(
    RLines.State,
    m => {RContents.Known.ok(RKnown.Known.learn.of(kn, s, c, m), s) == True{}: Bool},
    RKnown.Known.find(kn, c),
    en => Known.put_ok(
      kn,
      s,
      c,
      RKnown.Known.fresh(kn, s, c)
    )(
      Equal.sym(
        Maybe<&2, RLines.State>,
        RKnown.Known.fresh(kn, s, c),
        RLines.Line.state(s, c),
        Known.fresh_ok(kn, s, c)(ok)
      )
    )(ok),
    x => ex => ok
  )

# Known.rule_learn_ok, with the state m that the table holds for the line
def Known.rule_learn_of_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  m: Maybe<&2, RLines.State>
) -> {
  RKnown.Known.find(kn, c) == m: Maybe<&2, RLines.State>
} -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RContents.Known.ok(
    RKnown.Known.rule.put(kn, c, RKnown.Era.next(c, m), RKnown.Known.rule.next(kn, s, c, m)),
    s
  )
    == True{}: Bool
}:
  match m:
    case None{}:
      e => ok => ok
    case Some{RLines.State{+vs, +k}}:
      +e => +ok => Lists.Maybe.by(
        RLines.Rule,
        y => {
          RContents.Known.ok(
            RKnown.Known.rule.put(kn, c, RLines.Line.era(c, vs), y),
            s
          )
            == True{}: Bool
        },
        RKnown.Known.rule(kn, s, c, vs),
        en => ok,
        +u => eu => Ok.cons(
          RKnown.Ruled{c, RLines.Line.era(c, vs), u},
          kn,
          s
        )(
          Shared.Bool.and_both(
            RKnown.Rule.fits(
              RKnown.Known.rule.next(RKnown.Known.none(), s, c, RLines.Line.state(s, c)),
              u
            ),
            RKnown.Era.fits(RLines.Line.state(s, c), c, RLines.Line.era(c, vs))
          )(
            Rule.fits_of(
              RKnown.Known.rule.next(RKnown.Known.none(), s, c, RLines.Line.state(s, c)),
              u
            )(
              %Equal.sym(Maybe<&2, RLines.State>, RLines.Line.state(s, c), Some{RLines.State{vs, k}}, Known.find_ok(kn, s, c, RLines.State{vs, k})(ok)(e)): {RKnown.Known.rule.next(RKnown.Known.none(), s, c, _) == Some{u}: Maybe<&2, RLines.Rule>}
              Equal.trans(Maybe<&2, RLines.Rule>, RLines.Rule.after(s, c, vs), RKnown.Known.rule(kn, s, c, vs), Some{u}, Equal.sym(Maybe<&2, RLines.Rule>, RKnown.Known.rule(kn, s, c, vs), RLines.Rule.after(s, c, vs), Known.rule_ok(kn, s, c, vs)(ok)), eu))
          )((
              %Equal.sym(Maybe<&2, RLines.State>, RLines.Line.state(s, c), Some{RLines.State{vs, k}}, Known.find_ok(kn, s, c, RLines.State{vs, k})(ok)(e)): {RKnown.Era.fits(_, c, RLines.Line.era(c, vs)) == True{}: Bool}
              Shared.Nat.is_eq_refl(RLines.Line.era(c, vs))))
        )(ok)
      )

# a right table that learns the rule of the next version of a line is right
def Known.rule_learn_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {RContents.Known.ok(RKnown.Known.rule.learn(kn, s, c), s) == True{}: Bool}:
  +ok => Lists.Bool.by(
    b => {RContents.Known.ok(RKnown.Known.rule.learn.if(b, kn, s, c), s) == True{}: Bool},
    Maybe.is_some(&2, RLines.Rule, RKnown.Known.ruled(kn, c)),
    et => ok,
    ef => Known.rule_learn_of_ok(kn, s, c, RKnown.Known.find(kn, c))({==})(ok)
  )

# a right table with the ids of the versions of the state that the facts
# give a line is right
def Ids.put_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  st: RLines.State
) -> {
  RLines.Line.state(s, c) == Some{st}: Maybe<&2, RLines.State>
} -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {RContents.Known.ok(RKnown.Known.ids.put(kn, c, Some{st}), s) == True{}: Bool}:
  match st:
    case RLines.State{+vs, +k}:
      e => ok => Ok.cons(
        RKnown.Made{c, RKnown.Ids.of(vs)},
        kn,
        s
      )(Made.fits_of(RLines.Line.state(s, c), vs, k)(e))(ok)

# a right table that learns the ids of the versions of a line is right
def Known.ids_learn_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {RContents.Known.ok(RKnown.Known.ids.learn(kn, c), s) == True{}: Bool}:
  +ok => Lists.Bool.by(
    b => {RContents.Known.ok(RKnown.Known.ids.learn.if(b, kn, c), s) == True{}: Bool},
    Maybe.is_some(&2, RKnown.Ids, RKnown.Known.ids(kn, c)),
    et => ok,
    ef => Lists.Maybe.by(
      RLines.State,
      m => {RContents.Known.ok(RKnown.Known.ids.put(kn, c, m), s) == True{}: Bool},
      RKnown.Known.find(kn, c),
      en => ok,
      +st => est => Ids.put_ok(kn, s, c, st)(Known.find_ok(kn, s, c, st)(ok)(est))(ok)
    )
  )

# a right table that learns the states of a line and of its store is right
def Known.learn_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {RContents.Known.ok(RKnown.Known.learn(kn, s, c), s) == True{}: Bool}:
  ok => Known.ids_learn_ok(
    RKnown.Known.rule.learn(
      RKnown.Known.learn.one(RKnown.Known.learn.one(kn, s, RKnown.Known.root(c)), s, c),
      s,
      c
    ),
    s,
    c
  )(
    Known.rule_learn_ok(
      RKnown.Known.learn.one(RKnown.Known.learn.one(kn, s, RKnown.Known.root(c)), s, c),
      s,
      c
    )(
      Known.learn_one_ok(
        RKnown.Known.learn.one(kn, s, RKnown.Known.root(c)),
        s,
        c
      )(Known.learn_one_ok(kn, s, RKnown.Known.root(c))(ok))
    )
  )

# a vote for a slot of the line c changes no state of a line that it does
# not hit
def Line.state_voted(
  +name: String,
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +t: Nat,
  +x: Types.Cast,
  c2: Ledgers.Line
) -> {
  RKnown.Known.hit(c, c2) == False{}: Bool
} -> {
  Lines.Line.state(
    Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}),
    c2
  )
    == Lines.Line.state(s, c2): Maybe<&2, RLines.State>
}:
  match c2:
    case Ledgers.Line{+h, None{}}:
      h0 => Moves.Store.same(Moves.Delta.Vote{name, c, k, t, x}, s, h)({==})(
        %Equal.sym(Bool, Ledgers.Line.is_eq(Ledgers.Line{h, None{}}, c), False{}, Bool.or_false_left(Ledgers.Line.is_eq(Ledgers.Line{h, None{}}, c), Ledgers.Line.is_eq(Ledgers.Line{h, None{}}, c))(h0)): {Bool.not(_) == True{}: Bool}
        {==})
    case Ledgers.Line{+h, Some{+b}}:
      +h0 => Moves.Branch.same(Moves.Delta.Vote{name, c, k, t, x}, s, h, b)({==})(
        %Equal.sym(Bool, Ledgers.Line.is_eq(Ledgers.Line{h, None{}}, c), False{}, Bool.or_false_right(Ledgers.Line.is_eq(Ledgers.Line{h, Some{b}}, c), Ledgers.Line.is_eq(Ledgers.Line{h, None{}}, c))(h0)): {Bool.not(_) == True{}: Bool}
        {==})(
        %Equal.sym(Bool, Ledgers.Line.is_eq(Ledgers.Line{h, Some{b}}, c), False{}, Bool.or_false_left(Ledgers.Line.is_eq(Ledgers.Line{h, Some{b}}, c), Ledgers.Line.is_eq(Ledgers.Line{h, None{}}, c))(h0)): {Bool.not(_) == True{}: Bool}
        {==})

# the rule after some versions of a line is read as before, when the state
# of its store is
def After.same(
  +s: Facts.Facts(),
  +s2: Facts.Facts(),
  c: Ledgers.Line,
  +vs: List<&2, Types.Entry>
) -> {
  Lines.Line.state(
    s2,
    RKnown.Known.root(c)
  )
    == Lines.Line.state(s, RKnown.Known.root(c)): Maybe<&2, RLines.State>
} -> {
  RLines.Rule.after(
    Facts.Facts.crit(s2),
    c,
    vs
  )
    == RLines.Rule.after(Facts.Facts.crit(s), c, vs): Maybe<&2, RLines.Rule>
}:
  match c:
    case Ledgers.Line{+h, None{}}:
      e => {==}
    case Ledgers.Line{+h, Some{+b}}:
      e => (
        %e: {RLines.Rule.after(Facts.Facts.crit(s2), Ledgers.Line{h, Some{b}}, vs) == RLines.Rule.after.of(Ledgers.Line{h, Some{b}}, vs, Maybe.map(&2, RLines.State, List<&2, Types.Entry>, RLines.State.versions, _)): Maybe<&2, RLines.Rule>}
        {==})

# the rule of the next version of a line in a state is read as before, when
# the state of its store is
def Next.same(
  +s: Facts.Facts(),
  +s2: Facts.Facts(),
  +c: Ledgers.Line,
  m: Maybe<&2, RLines.State>
) -> {
  Lines.Line.state(
    s2,
    RKnown.Known.root(c)
  )
    == Lines.Line.state(s, RKnown.Known.root(c)): Maybe<&2, RLines.State>
} -> {
  RKnown.Known.rule.next(
    RKnown.Known.none(),
    Facts.Facts.crit(s2),
    c,
    m
  )
    == RKnown.Known.rule.next(
      RKnown.Known.none(),
      Facts.Facts.crit(s),
      c,
      m
    ): Maybe<&2, RLines.Rule>
}:
  match m:
    case None{}:
      e => {==}
    case Some{RLines.State{+vs, k}}:
      e => After.same(s, s2, c, vs)(e)

# a rule that a table holds for a line stays right, when the states of the
# line and of its store are read as before
def Ruled.same(
  +s: Facts.Facts(),
  +s2: Facts.Facts(),
  +c: Ledgers.Line,
  +zu: Nat,
  +u: RLines.Rule
) -> {
  Lines.Line.state(s2, c) == Lines.Line.state(s, c): Maybe<&2, RLines.State>
} -> {
  Lines.Line.state(
    s2,
    RKnown.Known.root(c)
  )
    == Lines.Line.state(s, RKnown.Known.root(c)): Maybe<&2, RLines.State>
} -> {
  RContents.Kept.ok(Facts.Facts.crit(s), RKnown.Ruled{c, zu, u}) == True{}: Bool
} -> {RContents.Kept.ok(Facts.Facts.crit(s2), RKnown.Ruled{c, zu, u}) == True{}: Bool}:
  ec => er => h => (
    %Equal.sym(Maybe<&2, RLines.State>, Lines.Line.state(s2, c), Lines.Line.state(s, c), ec): {Bool.and(RKnown.Rule.fits(RKnown.Known.rule.next(RKnown.Known.none(), Facts.Facts.crit(s2), c, _), u), RKnown.Era.fits(_, c, zu)) == True{}: Bool}
    %Equal.sym(Maybe<&2, RLines.Rule>, RKnown.Known.rule.next(RKnown.Known.none(), Facts.Facts.crit(s2), c, Lines.Line.state(s, c)), RKnown.Known.rule.next(RKnown.Known.none(), Facts.Facts.crit(s), c, Lines.Line.state(s, c)), Next.same(s, s2, c, Lines.Line.state(s, c))(er)): {Bool.and(RKnown.Rule.fits(_, u), RKnown.Era.fits(Lines.Line.state(s, c), c, zu)) == True{}: Bool}
    h)

# the ids that a table holds for a line stay right, when the state of the
# line is read as before
def Made.same(
  +s: Facts.Facts(),
  +s2: Facts.Facts(),
  +c: Ledgers.Line,
  +y: RKnown.Ids
) -> {
  Lines.Line.state(s2, c) == Lines.Line.state(s, c): Maybe<&2, RLines.State>
} -> {
  RContents.Kept.ok(Facts.Facts.crit(s), RKnown.Made{c, y}) == True{}: Bool
} -> {RContents.Kept.ok(Facts.Facts.crit(s2), RKnown.Made{c, y}) == True{}: Bool}:
  ec => h => (
    %Equal.sym(Maybe<&2, RLines.State>, Lines.Line.state(s2, c), Lines.Line.state(s, c), ec): {RKnown.Made.fits(_, y) == True{}: Bool}
    h)

# a vote that does not hit a line does not hit its store
def Hit.root(
  +c: Ledgers.Line,
  +c2: Ledgers.Line
) -> {
  RKnown.Known.hit(c, c2) == False{}: Bool
} -> {RKnown.Known.hit(c, RKnown.Known.root(c2)) == False{}: Bool}:
  h => (
    %Equal.sym(Bool, Ledgers.Line.is_eq(RKnown.Known.root(c2), c), False{}, Bool.or_false_right(Ledgers.Line.is_eq(c2, c), Ledgers.Line.is_eq(RKnown.Known.root(c2), c))(h)): {Bool.or(_, _) == False{}: Bool}
    {==})

# a table that is right for the facts s, without the states that a vote for
# the line c may change, is right after the vote
def Known.voted_ok(
  kn: RKnown.Known(),
  +name: String,
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +t: Nat,
  +x: Types.Cast
) -> {
  RContents.Known.ok(kn, Facts.Facts.crit(s)) == True{}: Bool
} -> {
  RContents.Known.ok(
    RKnown.Known.voted(kn, c),
    Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))
  )
    == True{}: Bool
}:
  match kn:
    case Nil{}:
      ok => {==}
    case Con{RKnown.Kept{+c2, +st}, +rest}:
      +ok => Lists.Bool.by(
        b => {
          RContents.Known.ok(
            List.filter.put(
              RKnown.Kept,
              RKnown.Kept{c2, st},
              RKnown.Known.voted(rest, c),
              Bool.not(b)
            ),
            Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))
          )
            == True{}: Bool
        },
        RKnown.Known.hit(c, c2),
        et => Known.voted_ok(
          rest,
          name,
          s,
          c,
          k,
          t,
          x
        )(
          Shared.Bool.and_true_right(
            RKnown.State.fits(Lines.Line.state(s, c2), st),
            RContents.Known.ok(rest, Facts.Facts.crit(s))
          )(ok)
        ),
        ef => Shared.Bool.and_both(
          RKnown.State.fits(
            Lines.Line.state(
              Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}),
              c2
            ),
            st
          ),
          RContents.Known.ok(
            RKnown.Known.voted(rest, c),
            Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))
          )
        )(
          %Equal.sym(Maybe<&2, RLines.State>, Lines.Line.state(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}), c2), Lines.Line.state(s, c2), Line.state_voted(name, s, c, k, t, x, c2)(ef)): {RKnown.State.fits(_, st) == True{}: Bool}
          Shared.Bool.and_true_left(RKnown.State.fits(Lines.Line.state(s, c2), st), RContents.Known.ok(rest, Facts.Facts.crit(s)))(ok))(
          Known.voted_ok(
            rest,
            name,
            s,
            c,
            k,
            t,
            x
          )(
            Shared.Bool.and_true_right(
              RKnown.State.fits(Lines.Line.state(s, c2), st),
              RContents.Known.ok(rest, Facts.Facts.crit(s))
            )(ok)
          )
        )
      )
    case Con{RKnown.Stock{+m2, +lwm2}, +rest}:
      ok => Known.voted_ok(
        rest,
        name,
        s,
        c,
        k,
        t,
        x
      )(Ok.tail(RKnown.Stock{m2, lwm2}, rest, Facts.Facts.crit(s))(ok))
    case Con{RKnown.Ruled{+c2, +zu, +u}, +rest}:
      +ok => Lists.Bool.by(
        b => {
          RContents.Known.ok(
            List.filter.put(
              RKnown.Kept,
              RKnown.Ruled{c2, zu, u},
              RKnown.Known.voted(rest, c),
              Bool.not(b)
            ),
            Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))
          )
            == True{}: Bool
        },
        RKnown.Known.hit(c, c2),
        et => Known.voted_ok(
          rest,
          name,
          s,
          c,
          k,
          t,
          x
        )(Ok.tail(RKnown.Ruled{c2, zu, u}, rest, Facts.Facts.crit(s))(ok)),
        +ef => Ok.cons(
          RKnown.Ruled{c2, zu, u},
          RKnown.Known.voted(rest, c),
          Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))
        )(
          Ruled.same(
            s,
            Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}),
            c2,
            zu,
            u
          )(
            Line.state_voted(name, s, c, k, t, x, c2)(ef)
          )(
            Line.state_voted(name, s, c, k, t, x, RKnown.Known.root(c2))(Hit.root(c, c2)(ef))
          )(Ok.head(RKnown.Ruled{c2, zu, u}, rest, Facts.Facts.crit(s))(ok))
        )(
          Known.voted_ok(
            rest,
            name,
            s,
            c,
            k,
            t,
            x
          )(Ok.tail(RKnown.Ruled{c2, zu, u}, rest, Facts.Facts.crit(s))(ok))
        )
      )
    case Con{RKnown.Made{+c2, +y}, +rest}:
      +ok => Lists.Bool.by(
        b => {
          RContents.Known.ok(
            List.filter.put(
              RKnown.Kept,
              RKnown.Made{c2, y},
              RKnown.Known.voted(rest, c),
              Bool.not(b)
            ),
            Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))
          )
            == True{}: Bool
        },
        RKnown.Known.hit(c, c2),
        et => Known.voted_ok(
          rest,
          name,
          s,
          c,
          k,
          t,
          x
        )(Ok.tail(RKnown.Made{c2, y}, rest, Facts.Facts.crit(s))(ok)),
        +ef => Ok.cons(
          RKnown.Made{c2, y},
          RKnown.Known.voted(rest, c),
          Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))
        )(
          Made.same(
            s,
            Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}),
            c2,
            y
          )(
            Line.state_voted(name, s, c, k, t, x, c2)(ef)
          )(Ok.head(RKnown.Made{c2, y}, rest, Facts.Facts.crit(s))(ok))
        )(
          Known.voted_ok(
            rest,
            name,
            s,
            c,
            k,
            t,
            x
          )(Ok.tail(RKnown.Made{c2, y}, rest, Facts.Facts.crit(s))(ok))
        )
      )
    case Con{RKnown.Open{+fs2, +pk2, +tx9, +mtx9}, +rest}:
      ok => Known.voted_ok(
        rest,
        name,
        s,
        c,
        k,
        t,
        x
      )(Ok.tail(RKnown.Open{fs2, pk2, tx9, mtx9}, rest, Facts.Facts.crit(s))(ok))

# Open facts: laws
# ----------------
# A table that fits holds, for a work, the facts that a work may still act
# on (RKnown.Open.of): a fact that waits no more gives no ballot, and no
# ballot for a slot that waits is left out. So a work that walks them plans
# what a work that walks all the facts plans.

# the insert of a fact that reads its key once is the insert
def Open.put_insert(
  fs: List<&2, Types.Fact>,
  +f: Types.Fact
) -> {
  RKnown.Open.put(
    fs,
    f
  )
    == Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f): List<&2, Types.Fact>
}:
  Orders.Values.put_insert(~Types.Fact, ~Coded.Fact.words, fs, f)

# a table that fits is right
def Fit.ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain()
) -> {RContents.Known.fit(kn, s) == True{}: Bool} -> {RContents.Known.ok(kn, s) == True{}: Bool}:
  Shared.Bool.and_true_left(
    RContents.Known.ok(kn, s),
    RContents.Shelf.fits(RKnown.Known.shelf(kn), s)
  )

# the facts that a table that fits holds for a work are right
def Fit.open(
  +kn: RKnown.Known(),
  +s: RFacts.Plain()
) -> {
  RContents.Known.fit(kn, s) == True{}: Bool
} -> {RContents.Shelf.fits(RKnown.Known.shelf(kn), s) == True{}: Bool}:
  Shared.Bool.and_true_right(
    RContents.Known.ok(kn, s),
    RContents.Shelf.fits(RKnown.Known.shelf(kn), s)
  )

# a right table that holds the right facts for a work fits
def Fit.both(
  +kn: RKnown.Known(),
  +s: RFacts.Plain()
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RContents.Shelf.fits(RKnown.Known.shelf(kn), s) == True{}: Bool
} -> {RContents.Known.fit(kn, s) == True{}: Bool}:
  Shared.Bool.and_both(RContents.Known.ok(kn, s), RContents.Shelf.fits(RKnown.Known.shelf(kn), s))

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof does not run
# the facts and the number of an entry for a work that is right are right
def Open.fits_old(
  +fs: List<&2, Types.Fact>,
  +n: Nat,
  +tx: Crits.Crit<Types.Ask>,
  +mtx: Crits.Crit<Ledgers.Line>,
  +s: RFacts.Plain()
) -> {
  RContents.Shelf.fits(Some{RKnown.Open{fs, n, tx, mtx}}, s) == True{}: Bool
} -> {
  Bool.and(
    Shared.List.is_eq(
      ~Types.Fact,
      ~Coded.Fact.is_eq,
      fs,
      RKnown.Open.of(RFacts.Facts.list(s), RKnown.Scene{RKnown.Known.none(), s})
    ),
    Nat.is_eq(n, RFacts.Seq.peak(RFacts.Facts.list(s)))
  )
    == True{}: Bool
}:
  h => Shared.Bool.and_true_left(
    Bool.and(
      Shared.List.is_eq(
        ~Types.Fact,
        ~Coded.Fact.is_eq,
        fs,
        RKnown.Open.of(RFacts.Facts.list(s), RKnown.Scene{RKnown.Known.none(), s})
      ),
      Nat.is_eq(n, RFacts.Seq.peak(RFacts.Facts.list(s)))
    ),
    RKnown.Tops.same(tx, RKnown.Tops.of(RFacts.Facts.list(s)))
  )(
    Shared.Bool.and_true_left(
      Bool.and(
        Bool.and(
          Shared.List.is_eq(
            ~Types.Fact,
            ~Coded.Fact.is_eq,
            fs,
            RKnown.Open.of(RFacts.Facts.list(s), RKnown.Scene{RKnown.Known.none(), s})
          ),
          Nat.is_eq(n, RFacts.Seq.peak(RFacts.Facts.list(s)))
        ),
        RKnown.Tops.same(tx, RKnown.Tops.of(RFacts.Facts.list(s)))
      ),
      RKnown.Mergers.same(mtx, RKnown.Mergers.of(RFacts.Facts.list(s)))
    )(h)
  )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof does not run
# the newest writes of an entry for a work that is right are those of the
# facts
def Open.fits_tops(
  +fs: List<&2, Types.Fact>,
  +n: Nat,
  +tx: Crits.Crit<Types.Ask>,
  +mtx: Crits.Crit<Ledgers.Line>,
  +s: RFacts.Plain()
) -> {
  RContents.Shelf.fits(Some{RKnown.Open{fs, n, tx, mtx}}, s) == True{}: Bool
} -> {tx == RKnown.Tops.of(RFacts.Facts.list(s)): Crits.Crit<Types.Ask>}:
  h => Newest.Tops.same_sound(
    tx,
    RKnown.Tops.of(RFacts.Facts.list(s))
  )(
    Shared.Bool.and_true_right(
      Bool.and(
        Shared.List.is_eq(
          ~Types.Fact,
          ~Coded.Fact.is_eq,
          fs,
          RKnown.Open.of(RFacts.Facts.list(s), RKnown.Scene{RKnown.Known.none(), s})
        ),
        Nat.is_eq(n, RFacts.Seq.peak(RFacts.Facts.list(s)))
      ),
      RKnown.Tops.same(tx, RKnown.Tops.of(RFacts.Facts.list(s)))
    )(
      Shared.Bool.and_true_left(
        Bool.and(
          Bool.and(
            Shared.List.is_eq(
              ~Types.Fact,
              ~Coded.Fact.is_eq,
              fs,
              RKnown.Open.of(RFacts.Facts.list(s), RKnown.Scene{RKnown.Known.none(), s})
            ),
            Nat.is_eq(n, RFacts.Seq.peak(RFacts.Facts.list(s)))
          ),
          RKnown.Tops.same(tx, RKnown.Tops.of(RFacts.Facts.list(s)))
        ),
        RKnown.Mergers.same(mtx, RKnown.Mergers.of(RFacts.Facts.list(s)))
      )(h)
    )
  )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof does not run
# the lines of merges of an entry for a work that is right are those of the
# facts
def Open.fits_merges(
  +fs: List<&2, Types.Fact>,
  +n: Nat,
  +tx: Crits.Crit<Types.Ask>,
  +mtx: Crits.Crit<Ledgers.Line>,
  +s: RFacts.Plain()
) -> {
  RContents.Shelf.fits(Some{RKnown.Open{fs, n, tx, mtx}}, s) == True{}: Bool
} -> {mtx == RKnown.Mergers.of(RFacts.Facts.list(s)): Crits.Crit<Ledgers.Line>}:
  h => Mergers.Mergers.same_sound(
    mtx,
    RKnown.Mergers.of(RFacts.Facts.list(s))
  )(
    Shared.Bool.and_true_right(
      Bool.and(
        Bool.and(
          Shared.List.is_eq(
            ~Types.Fact,
            ~Coded.Fact.is_eq,
            fs,
            RKnown.Open.of(RFacts.Facts.list(s), RKnown.Scene{RKnown.Known.none(), s})
          ),
          Nat.is_eq(n, RFacts.Seq.peak(RFacts.Facts.list(s)))
        ),
        RKnown.Tops.same(tx, RKnown.Tops.of(RFacts.Facts.list(s)))
      ),
      RKnown.Mergers.same(mtx, RKnown.Mergers.of(RFacts.Facts.list(s)))
    )(h)
  )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof does not run
# an entry for a work is right when its facts and its number are, and its
# newest writes and its lines of merges are those of the facts
def Open.fits_of(
  +fs: List<&2, Types.Fact>,
  +n: Nat,
  +tx: Crits.Crit<Types.Ask>,
  +mtx: Crits.Crit<Ledgers.Line>,
  +s: RFacts.Plain()
) -> {
  Bool.and(
    Shared.List.is_eq(
      ~Types.Fact,
      ~Coded.Fact.is_eq,
      fs,
      RKnown.Open.of(RFacts.Facts.list(s), RKnown.Scene{RKnown.Known.none(), s})
    ),
    Nat.is_eq(n, RFacts.Seq.peak(RFacts.Facts.list(s)))
  )
    == True{}: Bool
} -> {
  tx == RKnown.Tops.of(RFacts.Facts.list(s)): Crits.Crit<Types.Ask>
} -> {
  mtx == RKnown.Mergers.of(RFacts.Facts.list(s)): Crits.Crit<Ledgers.Line>
} -> {RContents.Shelf.fits(Some{RKnown.Open{fs, n, tx, mtx}}, s) == True{}: Bool}:
  ha => et => em => Shared.Bool.and_both(
    Bool.and(
      Bool.and(
        Shared.List.is_eq(
          ~Types.Fact,
          ~Coded.Fact.is_eq,
          fs,
          RKnown.Open.of(RFacts.Facts.list(s), RKnown.Scene{RKnown.Known.none(), s})
        ),
        Nat.is_eq(n, RFacts.Seq.peak(RFacts.Facts.list(s)))
      ),
      RKnown.Tops.same(tx, RKnown.Tops.of(RFacts.Facts.list(s)))
    ),
    RKnown.Mergers.same(mtx, RKnown.Mergers.of(RFacts.Facts.list(s)))
  )(
    Shared.Bool.and_both(
      Bool.and(
        Shared.List.is_eq(
          ~Types.Fact,
          ~Coded.Fact.is_eq,
          fs,
          RKnown.Open.of(RFacts.Facts.list(s), RKnown.Scene{RKnown.Known.none(), s})
        ),
        Nat.is_eq(n, RFacts.Seq.peak(RFacts.Facts.list(s)))
      ),
      RKnown.Tops.same(tx, RKnown.Tops.of(RFacts.Facts.list(s)))
    )(ha)((
        %Equal.sym(Crits.Crit<Types.Ask>, tx, RKnown.Tops.of(RFacts.Facts.list(s)), et): {RKnown.Tops.same(_, RKnown.Tops.of(RFacts.Facts.list(s))) == True{}: Bool}
        Newest.Tops.same_refl(RKnown.Tops.of(RFacts.Facts.list(s)))))
  )((
      %Equal.sym(Crits.Crit<Ledgers.Line>, mtx, RKnown.Mergers.of(RFacts.Facts.list(s)), em): {RKnown.Mergers.same(_, RKnown.Mergers.of(RFacts.Facts.list(s))) == True{}: Bool}
      Mergers.Mergers.same_refl(RKnown.Mergers.of(RFacts.Facts.list(s)))))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the newest writes that an entry that is right holds are those of the facts
def Shelf.tops_fit(
  m: Maybe<&2, RKnown.Kept>,
  +s: RFacts.Plain(),
  +tx: Crits.Crit<Types.Ask>
) -> {
  RContents.Shelf.fits(m, s) == True{}: Bool
} -> {
  RKnown.Shelf.tops(m) == Some{tx}: Maybe<&2, Crits.Crit<Types.Ask>>
} -> {tx == RKnown.Tops.of(RFacts.Facts.list(s)): Crits.Crit<Types.Ask>}:
  match m:
    case None{}:
      h => e => Empty.absurd(
        {tx == RKnown.Tops.of(RFacts.Facts.list(s)): Crits.Crit<Types.Ask>},
        Shared.Maybe.none_ne_some(Crits.Crit<Types.Ask>, tx, e)
      )
    case Some{RKnown.Kept{c2, st2}}:
      h => e => Empty.absurd(
        {tx == RKnown.Tops.of(RFacts.Facts.list(s)): Crits.Crit<Types.Ask>},
        Shared.Maybe.none_ne_some(Crits.Crit<Types.Ask>, tx, e)
      )
    case Some{RKnown.Stock{m2, lwm2}}:
      h => e => Empty.absurd(
        {tx == RKnown.Tops.of(RFacts.Facts.list(s)): Crits.Crit<Types.Ask>},
        Shared.Maybe.none_ne_some(Crits.Crit<Types.Ask>, tx, e)
      )
    case Some{RKnown.Ruled{c2, zu2, u2}}:
      h => e => Empty.absurd(
        {tx == RKnown.Tops.of(RFacts.Facts.list(s)): Crits.Crit<Types.Ask>},
        Shared.Maybe.none_ne_some(Crits.Crit<Types.Ask>, tx, e)
      )
    case Some{RKnown.Made{c2, y2}}:
      h => e => Empty.absurd(
        {tx == RKnown.Tops.of(RFacts.Facts.list(s)): Crits.Crit<Types.Ask>},
        Shared.Maybe.none_ne_some(Crits.Crit<Types.Ask>, tx, e)
      )
    case Some{RKnown.Open{fs2, pk2, +tx2, +mtx2}}:
      h => e => (
        %Shared.Maybe.some_inj(Crits.Crit<Types.Ask>, tx2, tx, e): {_ == RKnown.Tops.of(RFacts.Facts.list(s)): Crits.Crit<Types.Ask>}
        Open.fits_tops(fs2, pk2, tx2, mtx2, s)(h))

# the facts that an entry that is right holds for a work are those that a
# work may act on
def Shelf.open_fit(
  m: Maybe<&2, RKnown.Kept>,
  +s: RFacts.Plain(),
  +fs: List<&2, Types.Fact>
) -> {
  RContents.Shelf.fits(m, s) == True{}: Bool
} -> {
  RKnown.Shelf.facts(m) == Some{fs}: Maybe<&2, List<&2, Types.Fact>>
} -> {
  fs
    == RKnown.Open.of(
      RFacts.Facts.list(s),
      RKnown.Scene{RKnown.Known.none(), s}
    ): List<&2, Types.Fact>
}:
  match m:
    case None{}:
      h => e => Empty.absurd(
        {
          fs
            == RKnown.Open.of(
              RFacts.Facts.list(s),
              RKnown.Scene{RKnown.Known.none(), s}
            ): List<&2, Types.Fact>
        },
        Shared.Maybe.none_ne_some(List<&2, Types.Fact>, fs, e)
      )
    case Some{RKnown.Kept{c2, st2}}:
      h => e => Empty.absurd(
        {
          fs
            == RKnown.Open.of(
              RFacts.Facts.list(s),
              RKnown.Scene{RKnown.Known.none(), s}
            ): List<&2, Types.Fact>
        },
        Shared.Maybe.none_ne_some(List<&2, Types.Fact>, fs, e)
      )
    case Some{RKnown.Stock{m2, lwm2}}:
      h => e => Empty.absurd(
        {
          fs
            == RKnown.Open.of(
              RFacts.Facts.list(s),
              RKnown.Scene{RKnown.Known.none(), s}
            ): List<&2, Types.Fact>
        },
        Shared.Maybe.none_ne_some(List<&2, Types.Fact>, fs, e)
      )
    case Some{RKnown.Ruled{c2, zu2, u2}}:
      h => e => Empty.absurd(
        {
          fs
            == RKnown.Open.of(
              RFacts.Facts.list(s),
              RKnown.Scene{RKnown.Known.none(), s}
            ): List<&2, Types.Fact>
        },
        Shared.Maybe.none_ne_some(List<&2, Types.Fact>, fs, e)
      )
    case Some{RKnown.Made{c2, y2}}:
      h => e => Empty.absurd(
        {
          fs
            == RKnown.Open.of(
              RFacts.Facts.list(s),
              RKnown.Scene{RKnown.Known.none(), s}
            ): List<&2, Types.Fact>
        },
        Shared.Maybe.none_ne_some(List<&2, Types.Fact>, fs, e)
      )
    case Some{RKnown.Open{+fs2, +pk2, +tx9, +mtx9}}:
      h => e => (
        %Shared.Maybe.some_inj(List<&2, Types.Fact>, fs2, fs, e): {_ == RKnown.Open.of(RFacts.Facts.list(s), RKnown.Scene{RKnown.Known.none(), s}): List<&2, Types.Fact>}
        Shared.List.is_eq_sound(~Types.Fact, ~Coded.Fact.is_eq, ~Coded.Fact.laws(), fs2, RKnown.Open.of(RFacts.Facts.list(s), RKnown.Scene{RKnown.Known.none(), s}))(Shared.Bool.and_true_left(Shared.List.is_eq(~Types.Fact, ~Coded.Fact.is_eq, fs2, RKnown.Open.of(RFacts.Facts.list(s), RKnown.Scene{RKnown.Known.none(), s})), Nat.is_eq(pk2, RFacts.Seq.peak(RFacts.Facts.list(s))))(Open.fits_old(fs2, pk2, tx9, mtx9, s)(h))))

# the greatest number of an ask, read from an entry that is right, is the
# one read from the facts
def Shelf.peak_fit(
  m: Maybe<&2, RKnown.Kept>,
  +s: RFacts.Plain()
) -> {
  RContents.Shelf.fits(m, s) == True{}: Bool
} -> {RKnown.Shelf.peak(m, s) == RFacts.Seq.peak(RFacts.Facts.list(s)): Nat}:
  match m:
    case None{}:
      h => {==}
    case Some{RKnown.Kept{c2, st2}}:
      h => {==}
    case Some{RKnown.Stock{m2, lwm2}}:
      h => {==}
    case Some{RKnown.Ruled{c2, zu2, u2}}:
      h => {==}
    case Some{RKnown.Made{c2, y2}}:
      h => {==}
    case Some{RKnown.Open{+fs2, +pk2, +tx9, +mtx9}}:
      h => Shared.Nat.is_eq_sound(
        pk2,
        RFacts.Seq.peak(RFacts.Facts.list(s))
      )(
        Shared.Bool.and_true_right(
          Shared.List.is_eq(
            ~Types.Fact,
            ~Coded.Fact.is_eq,
            fs2,
            RKnown.Open.of(RFacts.Facts.list(s), RKnown.Scene{RKnown.Known.none(), s})
          ),
          Nat.is_eq(pk2, RFacts.Seq.peak(RFacts.Facts.list(s)))
        )(Open.fits_old(fs2, pk2, tx9, mtx9, s)(h))
      )

# the greatest number of an ask, read through a table that fits, is the one
# read from the facts
def Known.peak_fit(
  +kn: RKnown.Known(),
  +s: RFacts.Plain()
) -> {
  RContents.Known.fit(kn, s) == True{}: Bool
} -> {RKnown.Known.peak(kn, s) == RFacts.Seq.peak(RFacts.Facts.list(s)): Nat}:
  h => Shelf.peak_fit(RKnown.Known.shelf(kn), s)(Fit.open(kn, s)(h))

# the facts that a table that fits holds for a work are those that a work
# may act on
def Known.open_fit(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +fs: List<&2, Types.Fact>
) -> {
  RContents.Known.fit(kn, s) == True{}: Bool
} -> {
  RKnown.Known.open(kn) == Some{fs}: Maybe<&2, List<&2, Types.Fact>>
} -> {
  fs
    == RKnown.Open.of(
      RFacts.Facts.list(s),
      RKnown.Scene{RKnown.Known.none(), s}
    ): List<&2, Types.Fact>
}:
  h => e => Shelf.open_fit(RKnown.Known.shelf(kn), s, fs)(Fit.open(kn, s)(h))(e)

# a right table changes no test of whether a request waits on a line in the
# state m, the state that the facts give the line
def Id.waits_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +i: Ledgers.Id,
  m: Maybe<&2, RLines.State>
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RLines.Line.state(s, c) == m: Maybe<&2, RLines.State>
} -> {RKnown.Id.waits(m, kn, c, i) == RKnown.Id.waits(m, RKnown.Known.none(), c, i): Bool}:
  match m:
    case None{}:
      ok => e => {==}
    case Some{RLines.State{+vs, +k}}:
      ok => e => Equal.cong(
        Bool,
        Bool,
        b => Bool.not(b),
        RKnown.Known.made(kn, c, vs, i),
        Shared.List.some(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, vs, i),
        Known.made_ok(kn, s, c, vs, k, i)(ok)(e)
      )

# a right table changes no test of whether a request waits on a line
def Line.waits_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +i: Ledgers.Id
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {RKnown.Line.waits(kn, s, c, i) == RKnown.Line.waits(RKnown.Known.none(), s, c, i): Bool}:
  +ok => (
    %Equal.sym(Maybe<&2, RLines.State>, RKnown.Known.state(kn, s, c), RLines.Line.state(s, c), Known.state_ok(kn, s, c)(ok)): {RKnown.Id.waits(_, kn, c, i) == RKnown.Id.waits(RLines.Line.state(s, c), RKnown.Known.none(), c, i): Bool}
    Id.waits_ok(kn, s, c, i, RLines.Line.state(s, c))(ok)({==}))

# the lines of merges that an entry that fits holds are those of the facts
def Shelf.fits_led(
  m: Maybe<&2, RKnown.Kept>,
  +s: RFacts.Plain()
) -> {RContents.Shelf.fits(m, s) == True{}: Bool} -> {RContents.Shelf.led(m, s) == True{}: Bool}:
  match m:
    case None{}:
      h => {==}
    case Some{RKnown.Kept{c2, st2}}:
      h => {==}
    case Some{RKnown.Stock{m2, lwm2}}:
      h => {==}
    case Some{RKnown.Ruled{c2, zu2, u2}}:
      h => {==}
    case Some{RKnown.Made{c2, y2}}:
      h => {==}
    case Some{RKnown.Open{+fs2, +pk2, +tx2, +mtx2}}:
      h => Mergers.Mergers.same_refl_of(
        mtx2,
        RKnown.Mergers.of(RFacts.Facts.list(s))
      )(Open.fits_merges(fs2, pk2, tx2, mtx2, s)(h))

# the lines of merges that a table that fits holds are those of the facts
def Fit.led(
  +kn: RKnown.Known(),
  +s: RFacts.Plain()
) -> {
  RContents.Known.fit(kn, s) == True{}: Bool
} -> {RContents.Shelf.led(RKnown.Known.shelf(kn), s) == True{}: Bool}:
  h => Shelf.fits_led(RKnown.Known.shelf(kn), s)(Fit.open(kn, s)(h))

# the line of a merge, read from an entry whose lines of merges are those of
# the facts, is the line that an ask among the facts says
def Shelf.line_led(
  m: Maybe<&2, RKnown.Kept>,
  +s: RFacts.Plain(),
  +i: Ledgers.Id
) -> {
  RContents.Shelf.led(m, s) == True{}: Bool
} -> {
  RKnown.Shelf.line(
    m,
    u => RFacts.Facts.list(s),
    i
  )
    == RKnown.Merge.line(RFacts.Facts.list(s), i): Maybe<&2, Ledgers.Line>
}:
  match m:
    case None{}:
      h => {==}
    case Some{RKnown.Kept{c2, st2}}:
      h => {==}
    case Some{RKnown.Stock{m2, lwm2}}:
      h => {==}
    case Some{RKnown.Ruled{c2, zu2, u2}}:
      h => {==}
    case Some{RKnown.Made{c2, y2}}:
      h => {==}
    case Some{RKnown.Open{fs2, pk2, tx2, +mtx2}}:
      h => Reads.Eq.back(
        Crits.Crit<Ledgers.Line>,
        y => {
          RKnown.Mergers.get(
            y,
            i
          )
            == RKnown.Merge.line(RFacts.Facts.list(s), i): Maybe<&2, Ledgers.Line>
        },
        mtx2,
        RKnown.Mergers.of(RFacts.Facts.list(s)),
        Mergers.Mergers.same_sound(mtx2, RKnown.Mergers.of(RFacts.Facts.list(s)))(h),
        Mergers.Mergers.get_line(RFacts.Facts.list(s), i)
      )

# a right table changes no test of whether a request that resolves a merge
# of the line l waits
def Resolve.waits_ok(
  l: Maybe<&2, Ledgers.Line>,
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +i: Ledgers.Id
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RKnown.Resolve.waits(l, kn, s, i) == RKnown.Resolve.waits(l, RKnown.Known.none(), s, i): Bool
}:
  match l:
    case None{}:
      ok => {==}
    case Some{+c}:
      ok => Line.waits_ok(kn, s, c, i)(ok)

# a right table, whose lines of merges are those of the facts, changes no
# test of whether a request waits
def Request.waits_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +i: Ledgers.Id,
  r: Spec.Request
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RContents.Shelf.led(RKnown.Known.shelf(kn), s) == True{}: Bool
} -> {
  RKnown.Request.waits(kn, s, i, r) == RKnown.Request.waits(RKnown.Known.none(), s, i, r): Bool
}:
  match r:
    case Spec.Request.Start{os}:
      ok => hl => {==}
    case Spec.Request.Write{+b, p, w}:
      ok => hl => Line.waits_ok(kn, s, b, i)(ok)
    case Spec.Request.Merge{f, +x}:
      ok => hl => Line.waits_ok(kn, s, x, i)(ok)
    case Spec.Request.Resolve{+m, p, w}:
      +ok => hl => Equal.trans(
        Bool,
        RKnown.Resolve.waits(
          RKnown.Shelf.line(RKnown.Known.shelf(kn), u => RFacts.Facts.list(s), m),
          kn,
          s,
          i
        ),
        RKnown.Resolve.waits(RKnown.Merge.line(RFacts.Facts.list(s), m), kn, s, i),
        RKnown.Resolve.waits(RKnown.Merge.line(RFacts.Facts.list(s), m), RKnown.Known.none(), s, i),
        Equal.cong(
          Maybe<&2, Ledgers.Line>,
          Bool,
          l => RKnown.Resolve.waits(l, kn, s, i),
          RKnown.Shelf.line(RKnown.Known.shelf(kn), u => RFacts.Facts.list(s), m),
          RKnown.Merge.line(RFacts.Facts.list(s), m),
          Shelf.line_led(RKnown.Known.shelf(kn), s, m)(hl)
        ),
        Resolve.waits_ok(RKnown.Merge.line(RFacts.Facts.list(s), m), kn, s, i)(ok)
      )
    case Spec.Request.Mark{+b, m, v}:
      ok => hl => Line.waits_ok(kn, s, b, i)(ok)
    case Spec.Request.Move{+b, t, v}:
      ok => hl => Line.waits_ok(kn, s, b, i)(ok)
    case Spec.Request.Group{+h, g, ms}:
      ok => hl => Line.waits_ok(kn, s, Ledgers.Line{h, None{}}, i)(ok)
    case Spec.Request.Own{Ledgers.Line{+h, b}, g}:
      ok => hl => Line.waits_ok(kn, s, Ledgers.Line{h, None{}}, i)(ok)

# a right table, whose lines of merges are those of the facts, changes no
# test of whether a work may act on a fact
def Fact.waits_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  f: Types.Fact
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RContents.Shelf.led(RKnown.Known.shelf(kn), s) == True{}: Bool
} -> {
  RKnown.Fact.waits(
    RKnown.Scene{kn, s},
    f
  )
    == RKnown.Fact.waits(RKnown.Scene{RKnown.Known.none(), s}, f): Bool
}:
  match f:
    case Types.Fact.Vote{v, Types.Step.Broken{}, x}:
      ok => hl => {==}
    case Types.Fact.Vote{v, Types.Step.At{+c, +k, t}, x}:
      ok => hl => Equal.cong(
        Maybe<&2, RLines.State>,
        Bool,
        m => RKnown.Slot.waits(m, k),
        RKnown.Known.state(kn, s, c),
        RLines.Line.state(s, c),
        Known.state_ok(kn, s, c)(ok)
      )
    case Types.Fact.Ask{Types.Ask{+i, n, +r}}:
      ok => hl => Request.waits_ok(kn, s, i, r)(ok)(hl)

# a right table, whose lines of merges are those of the facts, changes no
# fact that a work may act on
def Open.of_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  fs: List<&2, Types.Fact>
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RContents.Shelf.led(RKnown.Known.shelf(kn), s) == True{}: Bool
} -> {
  RKnown.Open.of(
    fs,
    RKnown.Scene{kn, s}
  )
    == RKnown.Open.of(fs, RKnown.Scene{RKnown.Known.none(), s}): List<&2, Types.Fact>
}:
  match fs:
    case Nil{}:
      ok => hl => {==}
    case Con{+f, +rest}:
      +ok => +hl => (
        %Fact.waits_ok(kn, s, f)(ok)(hl): {RKnown.Open.of(f <> rest, RKnown.Scene{kn, s}) == List.filter.put(Types.Fact, f, RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), s}), _): List<&2, Types.Fact>}
        %Open.of_ok(kn, s, rest)(ok)(hl): {RKnown.Open.of(f <> rest, RKnown.Scene{kn, s}) == List.filter.put(Types.Fact, f, _, RKnown.Fact.waits(RKnown.Scene{kn, s}, f)): List<&2, Types.Fact>}
        {==})

# the ballots for a slot among facts with an ask first, when it is there (w),
# are those among the facts
def Ballots.put_ask(
  +a: Types.Ask,
  +fs: List<&2, Types.Fact>,
  w: Bool,
  +c: Ledgers.Line,
  +k: Nat
) -> {
  RRounds.Slot.ballots(
    List.filter.put(Types.Fact, Types.Fact.Ask{a}, fs, w),
    c,
    k
  )
    == RRounds.Slot.ballots(fs, c, k): List<&2, RRounds.Ballot>
}:
  match w:
    case True{}:
      {==}
    case False{}:
      {==}

# the ballots for a slot among facts with a ballot for another slot first,
# when it is there (w), are those among the facts
def Ballots.put_miss(
  +v: String,
  +c2: Ledgers.Line,
  +k2: Nat,
  +t: Nat,
  +x: Types.Cast,
  +fs: List<&2, Types.Fact>,
  w: Bool,
  +c: Ledgers.Line,
  +k: Nat
) -> {
  Bool.and(Ledgers.Line.is_eq(c2, c), Nat.is_eq(k2, k)) == False{}: Bool
} -> {
  RRounds.Slot.ballots(
    List.filter.put(Types.Fact, Types.Fact.Vote{v, Types.Step.At{c2, k2, t}, x}, fs, w),
    c,
    k
  )
    == RRounds.Slot.ballots(fs, c, k): List<&2, RRounds.Ballot>
}:
  match w:
    case True{}:
      e => (
        %Equal.sym(Bool, Bool.and(Ledgers.Line.is_eq(c2, c), Nat.is_eq(k2, k)), False{}, e): {List.filter.put(RRounds.Ballot, RRounds.Ballot{v, t, x}, RRounds.Slot.ballots(fs, c, k), _) == RRounds.Slot.ballots(fs, c, k): List<&2, RRounds.Ballot>}
        {==})
    case False{}:
      e => {==}

# the facts that a work may act on hold each ballot for a slot that waits
def Ballots.open(
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +k: Nat,
  fs: List<&2, Types.Fact>
) -> {
  RKnown.Slot.waits(RLines.Line.state(s, c), k) == True{}: Bool
} -> {
  RRounds.Slot.ballots(
    RKnown.Open.of(fs, RKnown.Scene{RKnown.Known.none(), s}),
    c,
    k
  )
    == RRounds.Slot.ballots(fs, c, k): List<&2, RRounds.Ballot>
}:
  match fs:
    case Nil{}:
      h => {==}
    case Con{Types.Fact.Ask{Types.Ask{+j, +n, +r}}, +rest}:
      h => Equal.trans(
        List<&2, RRounds.Ballot>,
        RRounds.Slot.ballots(
          List.filter.put(
            Types.Fact,
            Types.Fact.Ask{Types.Ask{j, n, r}},
            RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), s}),
            RKnown.Request.waits(RKnown.Known.none(), s, j, r)
          ),
          c,
          k
        ),
        RRounds.Slot.ballots(RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), s}), c, k),
        RRounds.Slot.ballots(rest, c, k),
        Ballots.put_ask(
          Types.Ask{j, n, r},
          RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), s}),
          RKnown.Request.waits(RKnown.Known.none(), s, j, r),
          c,
          k
        ),
        Ballots.open(s, c, k, rest)(h)
      )
    case Con{Types.Fact.Vote{v, Types.Step.Broken{}, x}, rest}:
      h => Ballots.open(s, c, k, rest)(h)
    case Con{Types.Fact.Vote{+v, Types.Step.At{+c2, +k2, +t}, +x}, +rest}:
      +h => Lists.Bool.by(
        b => {
          RRounds.Slot.ballots(
            List.filter.put(
              Types.Fact,
              Types.Fact.Vote{v, Types.Step.At{c2, k2, t}, x},
              RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), s}),
              RKnown.Slot.waits(RLines.Line.state(s, c2), k2)
            ),
            c,
            k
          )
            == List.filter.put(
              RRounds.Ballot,
              RRounds.Ballot{v, t, x},
              RRounds.Slot.ballots(rest, c, k),
              b
            ): List<&2, RRounds.Ballot>
        },
        Bool.and(Ledgers.Line.is_eq(c2, c), Nat.is_eq(k2, k)),
        +et => (
          %Equal.sym(Bool, RKnown.Slot.waits(RLines.Line.state(s, c2), k2), True{}, (
            %Equal.sym(Ledgers.Line, c2, c, Ledgers.Line.is_eq_sound(c2, c)(Shared.Bool.and_true_left(Ledgers.Line.is_eq(c2, c), Nat.is_eq(k2, k))(et))): {RKnown.Slot.waits(RLines.Line.state(s, _), k2) == True{}: Bool}
            %Equal.sym(Nat, k2, k, Shared.Nat.is_eq_sound(k2, k)(Shared.Bool.and_true_right(Ledgers.Line.is_eq(c2, c), Nat.is_eq(k2, k))(et))): {RKnown.Slot.waits(RLines.Line.state(s, c), _) == True{}: Bool}
            h)): {RRounds.Slot.ballots(List.filter.put(Types.Fact, Types.Fact.Vote{v, Types.Step.At{c2, k2, t}, x}, RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), s}), _), c, k) == List.filter.put(RRounds.Ballot, RRounds.Ballot{v, t, x}, RRounds.Slot.ballots(rest, c, k), True{}): List<&2, RRounds.Ballot>}
          %Equal.sym(Bool, Bool.and(Ledgers.Line.is_eq(c2, c), Nat.is_eq(k2, k)), True{}, et): {List.filter.put(RRounds.Ballot, RRounds.Ballot{v, t, x}, RRounds.Slot.ballots(RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), s}), c, k), _) == RRounds.Ballot{v, t, x} <> RRounds.Slot.ballots(rest, c, k): List<&2, RRounds.Ballot>}
          %Ballots.open(s, c, k, rest)(h): {RRounds.Ballot{v, t, x} <> RRounds.Slot.ballots(RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), s}), c, k) == RRounds.Ballot{v, t, x} <> _: List<&2, RRounds.Ballot>}
          {==}),
        ef => Equal.trans(
          List<&2, RRounds.Ballot>,
          RRounds.Slot.ballots(
            List.filter.put(
              Types.Fact,
              Types.Fact.Vote{v, Types.Step.At{c2, k2, t}, x},
              RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), s}),
              RKnown.Slot.waits(RLines.Line.state(s, c2), k2)
            ),
            c,
            k
          ),
          RRounds.Slot.ballots(RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), s}), c, k),
          RRounds.Slot.ballots(rest, c, k),
          Ballots.put_miss(
            v,
            c2,
            k2,
            t,
            x,
            RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), s}),
            RKnown.Slot.waits(RLines.Line.state(s, c2), k2),
            c,
            k
          )(ef),
          Ballots.open(s, c, k, rest)(h)
        )
      )

# a ballot for the next slot of a line waits
def Slot.waits_at(
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  -vs: List<&2, Types.Entry>,
  +k: Nat
) -> {
  RLines.Line.state(s, c) == Some{RLines.State{vs, k}}: Maybe<&2, RLines.State>
} -> {RKnown.Slot.waits(RLines.Line.state(s, c), k) == True{}: Bool}:
  o => (
    %Equal.sym(Maybe<&2, RLines.State>, RLines.Line.state(s, c), Some{RLines.State{vs, k}}, o): {RKnown.Slot.waits(_, k) == True{}: Bool}
    Shared.Nat.le_refl(k))

# a right table changes no ballot that a work reads for a slot that waits
def Work.ballots_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +k: Nat
) -> {
  RContents.Known.fit(kn, s) == True{}: Bool
} -> {
  RKnown.Slot.waits(RLines.Line.state(s, c), k) == True{}: Bool
} -> {
  RWorks.Work.ballots(
    kn,
    s,
    c,
    k
  )
    == RWorks.Work.ballots(RKnown.Known.none(), s, c, k): List<&2, RRounds.Ballot>
}:
  +ok => h => Lists.Maybe.by(
    List<&2, Types.Fact>,
    m => {
      RKnown.Known.open(kn) == m: Maybe<&2, List<&2, Types.Fact>>
    } -> {
      RRounds.Slot.ballots(
        RKnown.Open.or(m, s),
        c,
        k
      )
        == RRounds.Slot.ballots(RFacts.Facts.list(s), c, k): List<&2, RRounds.Ballot>
    },
    RKnown.Known.open(kn),
    en => e => {==},
    +fs => es => e => (
      %Equal.sym(List<&2, Types.Fact>, fs, RKnown.Open.of(RFacts.Facts.list(s), RKnown.Scene{RKnown.Known.none(), s}), Known.open_fit(kn, s, fs)(ok)(e)): {RRounds.Slot.ballots(_, c, k) == RRounds.Slot.ballots(RFacts.Facts.list(s), c, k): List<&2, RRounds.Ballot>}
      Ballots.open(s, c, k, RFacts.Facts.list(s))(h))
  )({==})

# A work reads through a right table
# ----------------------------------

# a right table changes no pins
def Pins.for_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +vs: List<&2, Types.Entry>,
  +m: Nat,
  r: Spec.Request
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RWorks.Pins.for(
    kn,
    s,
    c,
    vs,
    m,
    r
  )
    == RWorks.Pins.for(RKnown.Known.none(), s, c, vs, m, r): Types.Pins
}:
  match r:
    case Spec.Request.Merge{+f, x}:
      ok => Equal.cong(
        Maybe<&2, List<&2, Types.Entry>>,
        Types.Pins,
        fv => RWorks.Pins.merge(m, c, f, vs, fv),
        RKnown.Known.versions(kn, s, f),
        RLines.Line.versions(s, f),
        Known.versions_ok(kn, s, f)(ok)
      )
    case Spec.Request.Start{os}:
      ok => {==}
    case Spec.Request.Write{b, p, w}:
      ok => {==}
    case Spec.Request.Resolve{j, p, w}:
      ok => {==}
    case Spec.Request.Mark{b, j, v}:
      ok => {==}
    case Spec.Request.Move{b, j, v}:
      ok => {==}
    case Spec.Request.Group{h, g, ms}:
      ok => {==}
    case Spec.Request.Own{b, g}:
      ok => {==}

# a right table changes no era that the node pins
def Era.now_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  c: Ledgers.Line
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {RWorks.Era.now(kn, s, c) == RWorks.Era.now(RKnown.Known.none(), s, c): Nat}:
  match c:
    case Ledgers.Line{+h, b}:
      ok => Equal.cong(
        Maybe<&2, List<&2, Types.Entry>>,
        Nat,
        m => RWorks.Era.now.of(m),
        RKnown.Known.store(kn, s, h),
        RLines.Store.versions(s, h),
        Known.store_ok(kn, s, h)(ok)
      )

# a right table changes no rule of the next version of a line
def Work.rule_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  m: Maybe<&2, RLines.State>
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RWorks.Work.rule(
    kn,
    s,
    c,
    m
  )
    == RWorks.Work.rule(RKnown.Known.none(), s, c, m): Maybe<&2, RLines.Rule>
}:
  match m:
    case None{}:
      ok => {==}
    case Some{RLines.State{+vs, k}}:
      ok => Known.rule_ok(kn, s, c, vs)(ok)

# the rule of the next version of a line in a state, read with no table, is
# Known.rule.next
def Next.is(
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  m: Maybe<&2, RLines.State>
) -> {
  RWorks.Work.rule(
    RKnown.Known.none(),
    s,
    c,
    m
  )
    == RKnown.Known.rule.next(RKnown.Known.none(), s, c, m): Maybe<&2, RLines.Rule>
}:
  match m:
    case None{}:
      {==}
    case Some{RLines.State{vs, k}}:
      {==}

# a right table changes no rule of the next version of a line that a work
# reads
def Rule.or_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RWorks.Work.rule.or(
    RKnown.Known.ruled(kn, c),
    kn,
    s,
    c,
    RKnown.Known.state(kn, s, c)
  )
    == RWorks.Work.rule(
      RKnown.Known.none(),
      s,
      c,
      RKnown.Known.state(kn, s, c)
    ): Maybe<&2, RLines.Rule>
}:
  +ok => Lists.Maybe.by(
    RLines.Rule,
    y => {
      RWorks.Work.rule.or(
        y,
        kn,
        s,
        c,
        RKnown.Known.state(kn, s, c)
      )
        == RWorks.Work.rule(
          RKnown.Known.none(),
          s,
          c,
          RKnown.Known.state(kn, s, c)
        ): Maybe<&2, RLines.Rule>
    },
    RKnown.Known.ruled(kn, c),
    en => Work.rule_ok(kn, s, c, RKnown.Known.state(kn, s, c))(ok),
    +u => eu => (
      %Equal.sym(Maybe<&2, RLines.State>, RKnown.Known.state(kn, s, c), RLines.Line.state(s, c), Known.state_ok(kn, s, c)(ok)): {Some{u} == RWorks.Work.rule(RKnown.Known.none(), s, c, _): Maybe<&2, RLines.Rule>}
      Equal.sym(Maybe<&2, RLines.Rule>, RWorks.Work.rule(RKnown.Known.none(), s, c, RLines.Line.state(s, c)), Some{u}, Equal.trans(Maybe<&2, RLines.Rule>, RWorks.Work.rule(RKnown.Known.none(), s, c, RLines.Line.state(s, c)), RKnown.Known.rule.next(RKnown.Known.none(), s, c, RLines.Line.state(s, c)), Some{u}, Next.is(s, c, RLines.Line.state(s, c)), Known.ruled_ok(kn, s, c, u)(ok)(eu))))
  )

# a right table changes no next slot of a line
def Work.open_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +name: String,
  +c: Ledgers.Line
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RWorks.Work.open(
    kn,
    s,
    name,
    c
  )
    == RWorks.Work.open(RKnown.Known.none(), s, name, c): Maybe<&2, RWorks.Open>
}:
  +ok => (
    %Known.state_ok(kn, s, c)(ok): {RWorks.Work.open(kn, s, name, c) == RWorks.Work.open.at(name, _, RWorks.Work.rule(RKnown.Known.none(), s, c, _)): Maybe<&2, RWorks.Open>}
    %Rule.or_ok(kn, s, c)(ok): {RWorks.Work.open(kn, s, name, c) == RWorks.Work.open.at(name, RKnown.Known.state(kn, s, c), _): Maybe<&2, RWorks.Open>}
    {==})

# the next slot m of a line is read from the state st: its versions and its
# slot are those of st
def Open.From(st: Maybe<&2, RLines.State>, m: Maybe<&2, RWorks.Open>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{RWorks.Open{vs, k, ns}}:
      {st == Some{RLines.State{vs, k}}: Maybe<&2, RLines.State>}

# the next slot of a line in a state is read from the state
def Open.at_from(
  +name: String,
  st: Maybe<&2, RLines.State>,
  u: Maybe<&2, RLines.Rule>
) -> Open.From(st, RWorks.Work.open.at(name, st, u)):
  match st u:
    case Some{RLines.State{+vs, +k}} Some{RLines.Rule{g, +ns}}:
      Lists.Bool.by(
        b => Open.From(
          Some{RLines.State{vs, k}},
          Shared.Maybe.when(RWorks.Open, b, u2 => Some{RWorks.Open{vs, k, ns}})
        ),
        List.contains(~String, ~String.eq, ns, name),
        et => {==},
        ef => Unit{}
      )
    case Some{RLines.State{vs, k}} None{}:
      Unit{}
    case None{} Some{RLines.Rule{g, ns}}:
      Unit{}
    case None{} None{}:
      Unit{}

# the next slot of a line, as the facts give it, is read from the state that
# the facts give the line
def Work.open_from(
  +s: RFacts.Plain(),
  +name: String,
  +c: Ledgers.Line
) -> Open.From(RLines.Line.state(s, c), RWorks.Work.open(RKnown.Known.none(), s, name, c)):
  Open.at_from(
    name,
    RLines.Line.state(s, c),
    RWorks.Work.rule(RKnown.Known.none(), s, c, RLines.Line.state(s, c))
  )

# Work.offer.at_ok, at the next slot of the line
def Work.offer.at_ok.some(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +name: String,
  +c: Ledgers.Line,
  +a: Types.Ask,
  +vs: List<&2, Types.Entry>,
  +k: Nat,
  +ns: List<&2, String>
) -> {
  RContents.Known.fit(kn, s) == True{}: Bool
} -> {
  RLines.Line.state(s, c) == Some{RLines.State{vs, k}}: Maybe<&2, RLines.State>
} -> {
  RWorks.Work.offer.at(
    kn,
    s,
    name,
    c,
    a,
    Some{RWorks.Open{vs, k, ns}}
  )
    == RWorks.Work.offer.at(
      RKnown.Known.none(),
      s,
      name,
      c,
      a,
      Some{RWorks.Open{vs, k, ns}}
    ): Maybe<&2, RWorks.Plan>
}:
  +ok => +o => (
    %Work.ballots_ok(kn, s, c, k)(ok)(Slot.waits_at(s, c, vs, k)(o)): {RWorks.Work.offer.at(kn, s, name, c, a, Some{RWorks.Open{vs, k, ns}}) == Shared.Maybe.when(RWorks.Plan, Bool.not(Shared.List.some(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, vs, RLines.Ask.id(a))), u => RWorks.Plan.of(c, k, RWorks.Work.offer.of(u2 => Types.Pick{a, RWorks.Pins.for(RKnown.Known.none(), s, c, vs, RWorks.Era.now(RKnown.Known.none(), s, c), RLines.Ask.request(a))}, RRounds.Slot.chance(_, ns, k, name)))): Maybe<&2, RWorks.Plan>}
    %Era.now_ok(kn, s, c)(Fit.ok(kn, s)(ok)): {RWorks.Work.offer.at(kn, s, name, c, a, Some{RWorks.Open{vs, k, ns}}) == Shared.Maybe.when(RWorks.Plan, Bool.not(Shared.List.some(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, vs, RLines.Ask.id(a))), u => RWorks.Plan.of(c, k, RWorks.Work.offer.of(u2 => Types.Pick{a, RWorks.Pins.for(RKnown.Known.none(), s, c, vs, _, RLines.Ask.request(a))}, RRounds.Slot.chance(RWorks.Work.ballots(kn, s, c, k), ns, k, name)))): Maybe<&2, RWorks.Plan>}
    %Pins.for_ok(kn, s, c, vs, RWorks.Era.now(kn, s, c), RLines.Ask.request(a))(Fit.ok(kn, s)(ok)): {RWorks.Work.offer.at(kn, s, name, c, a, Some{RWorks.Open{vs, k, ns}}) == Shared.Maybe.when(RWorks.Plan, Bool.not(Shared.List.some(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, vs, RLines.Ask.id(a))), u => RWorks.Plan.of(c, k, RWorks.Work.offer.of(u2 => Types.Pick{a, _}, RRounds.Slot.chance(RWorks.Work.ballots(kn, s, c, k), ns, k, name)))): Maybe<&2, RWorks.Plan>}
    %Known.made_ok(kn, s, c, vs, k, RLines.Ask.id(a))(Fit.ok(kn, s)(ok))(o): {RWorks.Work.offer.at(kn, s, name, c, a, Some{RWorks.Open{vs, k, ns}}) == Shared.Maybe.when(RWorks.Plan, Bool.not(_), u => RWorks.Plan.of(c, k, RWorks.Work.offer.of(u2 => Types.Pick{a, RWorks.Pins.for(kn, s, c, vs, RWorks.Era.now(kn, s, c), RLines.Ask.request(a))}, RRounds.Slot.chance(RWorks.Work.ballots(kn, s, c, k), ns, k, name)))): Maybe<&2, RWorks.Plan>}
    {==})

# a right table changes no vote for an ask at the next slot of a line
def Work.offer.at_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +name: String,
  +c: Ledgers.Line,
  +a: Types.Ask,
  m: Maybe<&2, RWorks.Open>
) -> {
  RContents.Known.fit(kn, s) == True{}: Bool
} -> Open.From(
  RLines.Line.state(s, c),
  m
) -> {
  RWorks.Work.offer.at(
    kn,
    s,
    name,
    c,
    a,
    m
  )
    == RWorks.Work.offer.at(RKnown.Known.none(), s, name, c, a, m): Maybe<&2, RWorks.Plan>
}:
  match m:
    case None{}:
      ok => o => {==}
    case Some{RWorks.Open{+vs, +k, +ns}}:
      ok => o => Work.offer.at_ok.some(kn, s, name, c, a, vs, k, ns)(ok)(o)

# a right table changes no vote for an ask on its line
def Work.offer.on_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +name: String,
  +a: Types.Ask,
  m: Maybe<&2, Ledgers.Line>
) -> {
  RContents.Known.fit(kn, s) == True{}: Bool
} -> {
  RWorks.Work.offer.on(
    kn,
    s,
    name,
    a,
    m
  )
    == RWorks.Work.offer.on(RKnown.Known.none(), s, name, a, m): Maybe<&2, RWorks.Plan>
}:
  match m:
    case None{}:
      ok => {==}
    case Some{+c}:
      +ok => (
        %Equal.sym(Maybe<&2, RWorks.Open>, RWorks.Work.open(kn, s, name, c), RWorks.Work.open(RKnown.Known.none(), s, name, c), Work.open_ok(kn, s, name, c)(Fit.ok(kn, s)(ok))): {RWorks.Work.offer.at(kn, s, name, c, a, _) == RWorks.Work.offer.at(RKnown.Known.none(), s, name, c, a, RWorks.Work.open(RKnown.Known.none(), s, name, c)): Maybe<&2, RWorks.Plan>}
        Work.offer.at_ok(kn, s, name, c, a, RWorks.Work.open(RKnown.Known.none(), s, name, c))(ok)(Work.open_from(s, name, c)))

# the line of a merge, read through an entry whose lines of merges are those
# of the facts, else from the facts that the entry holds for a work, else
# from all the facts, is the line that an ask among the facts says
def Shelf.line_facts(
  m: Maybe<&2, RKnown.Kept>,
  +s: RFacts.Plain(),
  +i: Ledgers.Id
) -> {
  RContents.Shelf.led(m, s) == True{}: Bool
} -> {
  RKnown.Shelf.line(
    m,
    u => RKnown.Open.or(RKnown.Shelf.facts(m), s),
    i
  )
    == RKnown.Merge.line(RFacts.Facts.list(s), i): Maybe<&2, Ledgers.Line>
}:
  match m:
    case None{}:
      h => {==}
    case Some{RKnown.Kept{c2, st2}}:
      h => {==}
    case Some{RKnown.Stock{m2, lwm2}}:
      h => {==}
    case Some{RKnown.Ruled{c2, zu2, u2}}:
      h => {==}
    case Some{RKnown.Made{c2, y2}}:
      h => {==}
    case Some{RKnown.Open{fs2, pk2, tx2, +mtx2}}:
      h => Reads.Eq.back(
        Crits.Crit<Ledgers.Line>,
        y => {
          RKnown.Mergers.get(
            y,
            i
          )
            == RKnown.Merge.line(RFacts.Facts.list(s), i): Maybe<&2, Ledgers.Line>
        },
        mtx2,
        RKnown.Mergers.of(RFacts.Facts.list(s)),
        Mergers.Mergers.same_sound(mtx2, RKnown.Mergers.of(RFacts.Facts.list(s)))(h),
        Mergers.Mergers.get_line(RFacts.Facts.list(s), i)
      )

# the line of a request, read through a table that fits and the facts that
# a work walks, is its line read from all the facts
def Request.line_fit(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  r: Spec.Request
) -> {
  RContents.Known.fit(kn, s) == True{}: Bool
} -> {
  RWorks.Request.line(
    kn,
    RKnown.Known.facts(kn, s),
    r
  )
    == RWorks.Request.line(RKnown.Known.none(), RFacts.Facts.list(s), r): Maybe<&2, Ledgers.Line>
}:
  match r:
    case Spec.Request.Start{os}:
      h => {==}
    case Spec.Request.Write{b, p, w}:
      h => {==}
    case Spec.Request.Merge{f, x}:
      h => {==}
    case Spec.Request.Resolve{+m, p, w}:
      h => Shelf.line_facts(RKnown.Known.shelf(kn), s, m)(Fit.led(kn, s)(h))
    case Spec.Request.Mark{b, m, v}:
      h => {==}
    case Spec.Request.Move{b, t, v}:
      h => {==}
    case Spec.Request.Group{hh, g, ms}:
      h => {==}
    case Spec.Request.Own{Ledgers.Line{hh, b}, g}:
      h => {==}

# a right table changes no vote for an ask
def Work.offer_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +name: String,
  +a: Types.Ask
) -> {
  RContents.Known.fit(kn, s) == True{}: Bool
} -> {
  RWorks.Work.offer(
    kn,
    s,
    RKnown.Known.facts(kn, s),
    name,
    a
  )
    == RWorks.Work.offer(
      RKnown.Known.none(),
      s,
      RFacts.Facts.list(s),
      name,
      a
    ): Maybe<&2, RWorks.Plan>
}:
  +ok =>
    %Request.line_fit(
      kn,
      s,
      RLines.Ask.request(a)
    )(
      ok
    ): {
      RWorks.Work.offer(
        kn,
        s,
        RKnown.Known.facts(kn, s),
        name,
        a
      )
        == RWorks.Work.offer.on(RKnown.Known.none(), s, name, a, _): Maybe<&2, RWorks.Plan>
    }
    Work.offer.on_ok(
      kn,
      s,
      name,
      a,
      RWorks.Request.line(kn, RKnown.Known.facts(kn, s), RLines.Ask.request(a))
    )(ok)

# a right table changes no ask that the node may vote for
def Work.ready_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +name: String,
  fs: List<&2, Types.Fact>
) -> {
  RContents.Known.fit(kn, s) == True{}: Bool
} -> {
  RWorks.Work.ready(
    fs,
    kn,
    s,
    RKnown.Known.facts(kn, s),
    name
  )
    == RWorks.Work.ready(
      fs,
      RKnown.Known.none(),
      s,
      RFacts.Facts.list(s),
      name
    ): List<&2, Types.Ask>
}:
  match fs:
    case Nil{}:
      ok => {==}
    case Con{Types.Fact.Vote{v, st, x}, rest}:
      ok => Work.ready_ok(kn, s, name, rest)(ok)
    case Con{Types.Fact.Ask{+a}, +rest}:
      +ok => (
        %Work.ready_ok(kn, s, name, rest)(ok): {RWorks.Work.ready(Types.Fact.Ask{a} <> rest, kn, s, RKnown.Known.facts(kn, s), name) == List.filter.put(Types.Ask, a, _, Maybe.is_some(&2, RWorks.Plan, RWorks.Work.offer(RKnown.Known.none(), s, RFacts.Facts.list(s), name, a))): List<&2, Types.Ask>}
        %Work.offer_ok(kn, s, name, a)(ok): {RWorks.Work.ready(Types.Fact.Ask{a} <> rest, kn, s, RKnown.Known.facts(kn, s), name) == List.filter.put(Types.Ask, a, RWorks.Work.ready(rest, kn, s, RKnown.Known.facts(kn, s), name), Maybe.is_some(&2, RWorks.Plan, _)): List<&2, Types.Ask>}
        {==})

# a right table changes no vote for the ask m
def Work.propose.of_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +name: String,
  m: Maybe<&2, Types.Ask>
) -> {
  RContents.Known.fit(kn, s) == True{}: Bool
} -> {
  RWorks.Work.propose.of(
    m,
    kn,
    s,
    RKnown.Known.facts(kn, s),
    name
  )
    == RWorks.Work.propose.of(
      m,
      RKnown.Known.none(),
      s,
      RFacts.Facts.list(s),
      name
    ): Maybe<&2, RWorks.Plan>
}:
  match m:
    case None{}:
      ok => {==}
    case Some{+a}:
      ok => Work.offer_ok(kn, s, name, a)(ok)

# slot of the line, read from the state that the facts give the line
def Work.follow.at_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +name: String,
  +c: Ledgers.Line,
  +k: Nat,
  m: Maybe<&2, RWorks.Open>
) -> {
  RContents.Known.fit(kn, s) == True{}: Bool
} -> Open.From(
  RLines.Line.state(s, c),
  m
) -> {
  RWorks.Work.follow.at(
    kn,
    s,
    name,
    c,
    k,
    m
  )
    == RWorks.Work.follow.at(RKnown.Known.none(), s, name, c, k, m): Maybe<&2, RWorks.Plan>
}:
  match m:
    case None{}:
      ok => o => {==}
    case Some{RWorks.Open{+vs, +k2, +ns}}:
      ok => o => Lists.Bool.by(
        b => {
          Shared.Maybe.when(
            RWorks.Plan,
            b,
            u => RWorks.Plan.of(
              c,
              k,
              RRounds.Slot.follow(RWorks.Work.ballots(kn, s, c, k), ns, k, name)
            )
          )
            == Shared.Maybe.when(
              RWorks.Plan,
              b,
              u => RWorks.Plan.of(
                c,
                k,
                RRounds.Slot.follow(RWorks.Work.ballots(RKnown.Known.none(), s, c, k), ns, k, name)
              )
            ): Maybe<&2, RWorks.Plan>
        },
        Nat.is_eq(k2, k),
        et => (
          %Work.ballots_ok(kn, s, c, k)(ok)((
            %Shared.Nat.is_eq_sound(k2, k)(et): {RKnown.Slot.waits(RLines.Line.state(s, c), _) == True{}: Bool}
            Slot.waits_at(s, c, vs, k2)(o))): {RWorks.Plan.of(c, k, RRounds.Slot.follow(RWorks.Work.ballots(kn, s, c, k), ns, k, name)) == RWorks.Plan.of(c, k, RRounds.Slot.follow(_, ns, k, name)): Maybe<&2, RWorks.Plan>}
          {==}),
        ef => {==}
      )

# a right table changes no vote at the slot of a ballot
def Work.follow.of_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +name: String,
  f: Types.Fact
) -> {
  RContents.Known.fit(kn, s) == True{}: Bool
} -> {
  RWorks.Work.follow.of(
    kn,
    s,
    name,
    f
  )
    == RWorks.Work.follow.of(RKnown.Known.none(), s, name, f): Maybe<&2, RWorks.Plan>
}:
  match f:
    case Types.Fact.Vote{v, Types.Step.At{+c, +k, t}, x}:
      +ok => (
        %Equal.sym(Maybe<&2, RWorks.Open>, RWorks.Work.open(kn, s, name, c), RWorks.Work.open(RKnown.Known.none(), s, name, c), Work.open_ok(kn, s, name, c)(Fit.ok(kn, s)(ok))): {RWorks.Work.follow.at(kn, s, name, c, k, _) == RWorks.Work.follow.at(RKnown.Known.none(), s, name, c, k, RWorks.Work.open(RKnown.Known.none(), s, name, c)): Maybe<&2, RWorks.Plan>}
        Work.follow.at_ok(kn, s, name, c, k, RWorks.Work.open(RKnown.Known.none(), s, name, c))(ok)(Work.open_from(s, name, c)))
    case Types.Fact.Vote{v, Types.Step.Broken{}, x}:
      ok => {==}
    case Types.Fact.Ask{a}:
      ok => {==}

# a right table changes no vote at the slot of a ballot among fs
def Work.follow_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +name: String,
  fs: List<&2, Types.Fact>
) -> {
  RContents.Known.fit(kn, s) == True{}: Bool
} -> {
  RWorks.Work.follow(
    kn,
    s,
    name,
    fs
  )
    == RWorks.Work.follow(RKnown.Known.none(), s, name, fs): Maybe<&2, RWorks.Plan>
}:
  match fs:
    case Nil{}:
      ok => {==}
    case Con{+f, +rest}:
      +ok => (
        %Work.follow.of_ok(kn, s, name, f)(ok): {RWorks.Work.follow(kn, s, name, f <> rest) == RWorks.Work.follow.or(_, u => RWorks.Work.follow(RKnown.Known.none(), s, name, rest)): Maybe<&2, RWorks.Plan>}
        %Work.follow_ok(kn, s, name, rest)(ok): {RWorks.Work.follow(kn, s, name, f <> rest) == RWorks.Work.follow.or(RWorks.Work.follow.of(kn, s, name, f), u => _): Maybe<&2, RWorks.Plan>}
        {==})

# Work.pass.at_ok, for a request at the next slot of the line
def Work.pass.at_ok.id(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +name: String,
  +c: Ledgers.Line,
  +id: Ledgers.Id,
  +vs: List<&2, Types.Entry>,
  +k2: Nat,
  +ns: List<&2, String>
) -> {
  RContents.Known.fit(kn, s) == True{}: Bool
} -> {
  RLines.Line.state(s, c) == Some{RLines.State{vs, k2}}: Maybe<&2, RLines.State>
} -> {
  RWorks.Work.pass.at(
    kn,
    s,
    name,
    c,
    None{},
    Some{id},
    Some{RWorks.Open{vs, k2, ns}}
  )
    == RWorks.Work.pass.at(
      RKnown.Known.none(),
      s,
      name,
      c,
      None{},
      Some{id},
      Some{RWorks.Open{vs, k2, ns}}
    ): Maybe<&2, RWorks.Plan>
}:
  +ok => +o => (
    %Work.ballots_ok(kn, s, c, k2)(ok)(Slot.waits_at(s, c, vs, k2)(o)): {RWorks.Work.pass.at(kn, s, name, c, None{}, Some{id}, Some{RWorks.Open{vs, k2, ns}}) == Shared.Maybe.when(RWorks.Plan, Bool.not(Shared.List.some(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, vs, id)), u => RWorks.Plan.of(c, k2, RRounds.Slot.pass(_, name))): Maybe<&2, RWorks.Plan>}
    Equal.cong(Bool, Maybe<&2, RWorks.Plan>, b => Shared.Maybe.when(RWorks.Plan, Bool.not(b), u => RWorks.Plan.of(c, k2, RRounds.Slot.pass(RWorks.Work.ballots(kn, s, c, k2), name))), RKnown.Known.made(kn, c, vs, id), Shared.List.some(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, vs, id), Known.made_ok(kn, s, c, vs, k2, id)(Fit.ok(kn, s)(ok))(o)))

# a right table changes no pass at the next slot of a line that is read from
# the state that the facts give the line
def Work.pass.at_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +name: String,
  +c: Ledgers.Line,
  j: Maybe<&2, Nat>,
  i: Maybe<&2, Ledgers.Id>,
  m: Maybe<&2, RWorks.Open>
) -> {
  RContents.Known.fit(kn, s) == True{}: Bool
} -> Open.From(
  RLines.Line.state(s, c),
  m
) -> {
  RWorks.Work.pass.at(
    kn,
    s,
    name,
    c,
    j,
    i,
    m
  )
    == RWorks.Work.pass.at(RKnown.Known.none(), s, name, c, j, i, m): Maybe<&2, RWorks.Plan>
}:
  match j i m:
    case Some{k1} Some{id} None{}:
      ok => o => {==}
    case Some{k1} None{} None{}:
      ok => o => {==}
    case Some{+k1} Some{id} Some{RWorks.Open{+vs, +k2, ns}}:
      ok => o => Equal.cong(
        List<&2, RRounds.Ballot>,
        Maybe<&2, RWorks.Plan>,
        bs => Shared.Maybe.when(
          RWorks.Plan,
          Nat.is_eq(k2, k1),
          u => RWorks.Plan.of(c, k2, RRounds.Slot.pass(bs, name))
        ),
        RWorks.Work.ballots(kn, s, c, k2),
        RWorks.Work.ballots(RKnown.Known.none(), s, c, k2),
        Work.ballots_ok(kn, s, c, k2)(ok)(Slot.waits_at(s, c, vs, k2)(o))
      )
    case Some{+k1} None{} Some{RWorks.Open{+vs, +k2, ns}}:
      ok => o => Equal.cong(
        List<&2, RRounds.Ballot>,
        Maybe<&2, RWorks.Plan>,
        bs => Shared.Maybe.when(
          RWorks.Plan,
          Nat.is_eq(k2, k1),
          u => RWorks.Plan.of(c, k2, RRounds.Slot.pass(bs, name))
        ),
        RWorks.Work.ballots(kn, s, c, k2),
        RWorks.Work.ballots(RKnown.Known.none(), s, c, k2),
        Work.ballots_ok(kn, s, c, k2)(ok)(Slot.waits_at(s, c, vs, k2)(o))
      )
    case None{} Some{id} None{}:
      ok => o => {==}
    case None{} None{} None{}:
      ok => o => {==}
    case None{} None{} Some{RWorks.Open{vs, k2, ns}}:
      ok => o => {==}
    case None{} Some{+id} Some{RWorks.Open{+vs, +k2, +ns}}:
      ok => o => Work.pass.at_ok.id(kn, s, name, c, id, vs, k2, ns)(ok)(o)

# a right table changes no pass for a request on its line
def Work.pass.on_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +name: String,
  +i: Ledgers.Id,
  m: Maybe<&2, Ledgers.Line>
) -> {
  RContents.Known.fit(kn, s) == True{}: Bool
} -> {
  RWorks.Work.pass.on(
    kn,
    s,
    name,
    i,
    m
  )
    == RWorks.Work.pass.on(RKnown.Known.none(), s, name, i, m): Maybe<&2, RWorks.Plan>
}:
  match m:
    case None{}:
      ok => {==}
    case Some{+c}:
      +ok => (
        %Equal.sym(Maybe<&2, RWorks.Open>, RWorks.Work.open(kn, s, name, c), RWorks.Work.open(RKnown.Known.none(), s, name, c), Work.open_ok(kn, s, name, c)(Fit.ok(kn, s)(ok))): {RWorks.Work.pass.at(kn, s, name, c, None{}, Some{i}, _) == RWorks.Work.pass.at(RKnown.Known.none(), s, name, c, None{}, Some{i}, RWorks.Work.open(RKnown.Known.none(), s, name, c)): Maybe<&2, RWorks.Plan>}
        Work.pass.at_ok(kn, s, name, c, None{}, Some{i}, RWorks.Work.open(RKnown.Known.none(), s, name, c))(ok)(Work.open_from(s, name, c)))

# a right table changes no pass at the slot of a fact
def Work.pass.of_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +name: String,
  f: Types.Fact
) -> {
  RContents.Known.fit(kn, s) == True{}: Bool
} -> {
  RWorks.Work.pass.of(
    f,
    kn,
    s,
    RKnown.Known.facts(kn, s),
    name
  )
    == RWorks.Work.pass.of(
      f,
      RKnown.Known.none(),
      s,
      RFacts.Facts.list(s),
      name
    ): Maybe<&2, RWorks.Plan>
}:
  match f:
    case Types.Fact.Vote{v, Types.Step.At{+c, +k, t}, x}:
      +ok => (
        %Equal.sym(Maybe<&2, RWorks.Open>, RWorks.Work.open(kn, s, name, c), RWorks.Work.open(RKnown.Known.none(), s, name, c), Work.open_ok(kn, s, name, c)(Fit.ok(kn, s)(ok))): {RWorks.Work.pass.at(kn, s, name, c, Some{k}, None{}, _) == RWorks.Work.pass.at(RKnown.Known.none(), s, name, c, Some{k}, None{}, RWorks.Work.open(RKnown.Known.none(), s, name, c)): Maybe<&2, RWorks.Plan>}
        Work.pass.at_ok(kn, s, name, c, Some{k}, None{}, RWorks.Work.open(RKnown.Known.none(), s, name, c))(ok)(Work.open_from(s, name, c)))
    case Types.Fact.Vote{v, Types.Step.Broken{}, x}:
      ok => {==}
    case Types.Fact.Ask{Types.Ask{+i, n, +r}}:
      +ok => (
        %Request.line_fit(kn, s, r)(ok): {RWorks.Work.pass.of(Types.Fact.Ask{Types.Ask{i, n, r}}, kn, s, RKnown.Known.facts(kn, s), name) == RWorks.Work.pass.on(RKnown.Known.none(), s, name, i, _): Maybe<&2, RWorks.Plan>}
        Work.pass.on_ok(kn, s, name, i, RWorks.Request.line(kn, RKnown.Known.facts(kn, s), r))(ok))

# a right table changes no pass at the slot of a fact among fs
def Work.pass_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +name: String,
  fs: List<&2, Types.Fact>
) -> {
  RContents.Known.fit(kn, s) == True{}: Bool
} -> {
  RWorks.Work.pass(
    fs,
    kn,
    s,
    RKnown.Known.facts(kn, s),
    name
  )
    == RWorks.Work.pass(
      fs,
      RKnown.Known.none(),
      s,
      RFacts.Facts.list(s),
      name
    ): Maybe<&2, RWorks.Plan>
}:
  match fs:
    case Nil{}:
      ok => {==}
    case Con{+f, +rest}:
      +ok => (
        %Work.pass.of_ok(kn, s, name, f)(ok): {RWorks.Work.pass(f <> rest, kn, s, RKnown.Known.facts(kn, s), name) == RWorks.Work.follow.or(_, u => RWorks.Work.pass(rest, RKnown.Known.none(), s, RFacts.Facts.list(s), name)): Maybe<&2, RWorks.Plan>}
        %Work.pass_ok(kn, s, name, rest)(ok): {RWorks.Work.pass(f <> rest, kn, s, RKnown.Known.facts(kn, s), name) == RWorks.Work.follow.or(RWorks.Work.pass.of(f, kn, s, RKnown.Known.facts(kn, s), name), u => _): Maybe<&2, RWorks.Plan>}
        {==})

# What waits no more gives no ballot
# ---------------------------------

# a number that is not at most another is not it
def Nat.nle_ne(
  a: Nat,
  b: Nat
) -> {Nat.is_le(a, b) == False{}: Bool} -> {Nat.is_eq(a, b) == False{}: Bool}:
  match a b:
    case 0n 0n:
      h => Empty.absurd({True{} == False{}: Bool}, Shared.Bool.true_ne_false(h))
    case 0n 1n+q:
      h => {==}
    case 1n+p 0n:
      h => {==}
    case 1n+p 1n+q:
      h => Nat.nle_ne(p, q)(h)

# no vote for an ask at the next slot m of a line, when its request waits no
# more on the line
def Offer.at_dead(
  +s: RFacts.Plain(),
  +name: String,
  +c: Ledgers.Line,
  +a: Types.Ask,
  m: Maybe<&2, RWorks.Open>
) -> Open.From(
  RLines.Line.state(s, c),
  m
) -> {
  RKnown.Id.waits(
    RLines.Line.state(s, c),
    RKnown.Known.none(),
    c,
    RLines.Ask.id(a)
  )
    == False{}: Bool
} -> {
  RWorks.Work.offer.at(RKnown.Known.none(), s, name, c, a, m) == None{}: Maybe<&2, RWorks.Plan>
}:
  match m:
    case None{}:
      o => h => {==}
    case Some{RWorks.Open{+vs, +k, +ns}}:
      o => h => Crits.Crit.when_false(
        RWorks.Plan,
        Bool.not(
          Shared.List.some(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, vs, RLines.Ask.id(a))
        ),
        u => RWorks.Plan.of(
          c,
          k,
          RWorks.Work.offer.of(
            u2 => Types.Pick{
              a,
              RWorks.Pins.for(
                RKnown.Known.none(),
                s,
                c,
                vs,
                RWorks.Era.now(RKnown.Known.none(), s, c),
                RLines.Ask.request(a)
              )
            },
            RRounds.Slot.chance(RWorks.Work.ballots(RKnown.Known.none(), s, c, k), ns, k, name)
          )
        )
      )(
        %o: {RKnown.Id.waits(_, RKnown.Known.none(), c, RLines.Ask.id(a)) == False{}: Bool}
        h)

# no vote for an ask on its line, when its request waits no more on the line
def Offer.dead(
  +s: RFacts.Plain(),
  +name: String,
  +c: Ledgers.Line,
  +a: Types.Ask
) -> {
  RKnown.Line.waits(RKnown.Known.none(), s, c, RLines.Ask.id(a)) == False{}: Bool
} -> {
  RWorks.Work.offer.on(RKnown.Known.none(), s, name, a, Some{c}) == None{}: Maybe<&2, RWorks.Plan>
}:
  h => Offer.at_dead(
    s,
    name,
    c,
    a,
    RWorks.Work.open(RKnown.Known.none(), s, name, c)
  )(Work.open_from(s, name, c))(h)

# the asks that the node may vote for among facts with a ballot first, when
# it is there (w), are those among the facts
def Ready.put_vote(
  +v: String,
  +st: Types.Step,
  +x: Types.Cast,
  +fs: List<&2, Types.Fact>,
  w: Bool,
  +s: RFacts.Plain(),
  +all: List<&2, Types.Fact>,
  +name: String
) -> {
  RWorks.Work.ready(
    List.filter.put(Types.Fact, Types.Fact.Vote{v, st, x}, fs, w),
    RKnown.Known.none(),
    s,
    all,
    name
  )
    == RWorks.Work.ready(fs, RKnown.Known.none(), s, all, name): List<&2, Types.Ask>
}:
  match w:
    case True{}:
      {==}
    case False{}:
      {==}

# Ready.open at an ask for the line c, once it is known whether its request
# waits on the line (w)
def Ready.at(
  +s: RFacts.Plain(),
  +all: List<&2, Types.Fact>,
  +name: String,
  +a: Types.Ask,
  +c: Ledgers.Line,
  +rest: List<&2, Types.Fact>,
  w: Bool
) -> {
  RWorks.Request.line(
    RKnown.Known.none(),
    all,
    RLines.Ask.request(a)
  )
    == Some{c}: Maybe<&2, Ledgers.Line>
} -> {
  w == RKnown.Line.waits(RKnown.Known.none(), s, c, RLines.Ask.id(a)): Bool
} -> {
  RWorks.Work.ready(
    RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), s}),
    RKnown.Known.none(),
    s,
    all,
    name
  )
    == RWorks.Work.ready(rest, RKnown.Known.none(), s, all, name): List<&2, Types.Ask>
} -> {
  RWorks.Work.ready(
    List.filter.put(
      Types.Fact,
      Types.Fact.Ask{a},
      RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), s}),
      w
    ),
    RKnown.Known.none(),
    s,
    all,
    name
  )
    == RWorks.Work.ready(
      Types.Fact.Ask{a} <> rest,
      RKnown.Known.none(),
      s,
      all,
      name
    ): List<&2, Types.Ask>
}:
  match w:
    case True{}:
      el => ew => ih => (
        %ih: {RWorks.Work.ready(Types.Fact.Ask{a} <> RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), s}), RKnown.Known.none(), s, all, name) == List.filter.put(Types.Ask, a, _, Maybe.is_some(&2, RWorks.Plan, RWorks.Work.offer(RKnown.Known.none(), s, all, name, a))): List<&2, Types.Ask>}
        {==})
    case False{}:
      el => ew => ih => (
        %Equal.sym(Maybe<&2, Ledgers.Line>, RWorks.Request.line(RKnown.Known.none(), all, RLines.Ask.request(a)), Some{c}, el): {RWorks.Work.ready(RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), s}), RKnown.Known.none(), s, all, name) == List.filter.put(Types.Ask, a, RWorks.Work.ready(rest, RKnown.Known.none(), s, all, name), Maybe.is_some(&2, RWorks.Plan, RWorks.Work.offer.on(RKnown.Known.none(), s, name, a, _))): List<&2, Types.Ask>}
        %Equal.sym(Maybe<&2, RWorks.Plan>, RWorks.Work.offer.on(RKnown.Known.none(), s, name, a, Some{c}), None{}, Offer.dead(s, name, c, a)(Equal.sym(Bool, False{}, RKnown.Line.waits(RKnown.Known.none(), s, c, RLines.Ask.id(a)), ew))): {RWorks.Work.ready(RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), s}), RKnown.Known.none(), s, all, name) == List.filter.put(Types.Ask, a, RWorks.Work.ready(rest, RKnown.Known.none(), s, all, name), Maybe.is_some(&2, RWorks.Plan, _)): List<&2, Types.Ask>}
        ih)

# the asks that the node may vote for among the facts that a work may act
# on are those among all the facts
def Ready.open(
  +s: RFacts.Plain(),
  +name: String,
  fs: List<&2, Types.Fact>
) -> {
  RWorks.Work.ready(
    RKnown.Open.of(fs, RKnown.Scene{RKnown.Known.none(), s}),
    RKnown.Known.none(),
    s,
    RFacts.Facts.list(s),
    name
  )
    == RWorks.Work.ready(
      fs,
      RKnown.Known.none(),
      s,
      RFacts.Facts.list(s),
      name
    ): List<&2, Types.Ask>
}:
  match fs:
    case Nil{}:
      {==}
    case Con{Types.Fact.Vote{+v, +st, +x}, +rest}:
      Equal.trans(
        List<&2, Types.Ask>,
        RWorks.Work.ready(
          List.filter.put(
            Types.Fact,
            Types.Fact.Vote{v, st, x},
            RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), s}),
            RKnown.Fact.waits(RKnown.Scene{RKnown.Known.none(), s}, Types.Fact.Vote{v, st, x})
          ),
          RKnown.Known.none(),
          s,
          RFacts.Facts.list(s),
          name
        ),
        RWorks.Work.ready(
          RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), s}),
          RKnown.Known.none(),
          s,
          RFacts.Facts.list(s),
          name
        ),
        RWorks.Work.ready(rest, RKnown.Known.none(), s, RFacts.Facts.list(s), name),
        Ready.put_vote(
          v,
          st,
          x,
          RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), s}),
          RKnown.Fact.waits(RKnown.Scene{RKnown.Known.none(), s}, Types.Fact.Vote{v, st, x}),
          s,
          RFacts.Facts.list(s),
          name
        ),
        Ready.open(s, name, rest)
      )
    case Con{Types.Fact.Ask{Types.Ask{+i, +n, Spec.Request.Start{+os}}}, +rest}:
      Ready.open(s, name, rest)
    case Con{Types.Fact.Ask{Types.Ask{+i, +n, Spec.Request.Write{+b, +p, +w}}}, +rest}:
      Ready.at(
        s,
        RFacts.Facts.list(s),
        name,
        Types.Ask{i, n, Spec.Request.Write{b, p, w}},
        b,
        rest,
        RKnown.Line.waits(RKnown.Known.none(), s, b, i)
      )({==})({==})(Ready.open(s, name, rest))
    case Con{Types.Fact.Ask{Types.Ask{+i, +n, Spec.Request.Merge{+f, +x}}}, +rest}:
      Ready.at(
        s,
        RFacts.Facts.list(s),
        name,
        Types.Ask{i, n, Spec.Request.Merge{f, x}},
        x,
        rest,
        RKnown.Line.waits(RKnown.Known.none(), s, x, i)
      )({==})({==})(Ready.open(s, name, rest))
    case Con{Types.Fact.Ask{Types.Ask{+i, +n, Spec.Request.Resolve{+m, +p, +w}}}, +rest}:
      Lists.Maybe.by(
        Ledgers.Line,
        l => {
          RWorks.Work.ready(
            List.filter.put(
              Types.Fact,
              Types.Fact.Ask{Types.Ask{i, n, Spec.Request.Resolve{m, p, w}}},
              RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), s}),
              RKnown.Resolve.waits(l, RKnown.Known.none(), s, i)
            ),
            RKnown.Known.none(),
            s,
            RFacts.Facts.list(s),
            name
          )
            == RWorks.Work.ready(
              Types.Fact.Ask{Types.Ask{i, n, Spec.Request.Resolve{m, p, w}}} <> rest,
              RKnown.Known.none(),
              s,
              RFacts.Facts.list(s),
              name
            ): List<&2, Types.Ask>
        },
        RKnown.Merge.line(RFacts.Facts.list(s), m),
        en => (
          %Ready.open(s, name, rest): {RWorks.Work.ready(Types.Fact.Ask{Types.Ask{i, n, Spec.Request.Resolve{m, p, w}}} <> RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), s}), RKnown.Known.none(), s, RFacts.Facts.list(s), name) == List.filter.put(Types.Ask, Types.Ask{i, n, Spec.Request.Resolve{m, p, w}}, _, Maybe.is_some(&2, RWorks.Plan, RWorks.Work.offer(RKnown.Known.none(), s, RFacts.Facts.list(s), name, Types.Ask{i, n, Spec.Request.Resolve{m, p, w}}))): List<&2, Types.Ask>}
          {==}),
        +c => es => Ready.at(
          s,
          RFacts.Facts.list(s),
          name,
          Types.Ask{i, n, Spec.Request.Resolve{m, p, w}},
          c,
          rest,
          RKnown.Line.waits(RKnown.Known.none(), s, c, i)
        )(es)({==})(Ready.open(s, name, rest))
      )
    case Con{Types.Fact.Ask{Types.Ask{+i, +n, Spec.Request.Mark{+b, +m, +v}}}, +rest}:
      Ready.at(
        s,
        RFacts.Facts.list(s),
        name,
        Types.Ask{i, n, Spec.Request.Mark{b, m, v}},
        b,
        rest,
        RKnown.Line.waits(RKnown.Known.none(), s, b, i)
      )({==})({==})(Ready.open(s, name, rest))
    case Con{Types.Fact.Ask{Types.Ask{+i, +n, Spec.Request.Move{+b, +t, +v}}}, +rest}:
      Ready.at(
        s,
        RFacts.Facts.list(s),
        name,
        Types.Ask{i, n, Spec.Request.Move{b, t, v}},
        b,
        rest,
        RKnown.Line.waits(RKnown.Known.none(), s, b, i)
      )({==})({==})(Ready.open(s, name, rest))
    case Con{Types.Fact.Ask{Types.Ask{+i, +n, Spec.Request.Group{+h, +g, +ms}}}, +rest}:
      Ready.at(
        s,
        RFacts.Facts.list(s),
        name,
        Types.Ask{i, n, Spec.Request.Group{h, g, ms}},
        Ledgers.Line{h, None{}},
        rest,
        RKnown.Line.waits(RKnown.Known.none(), s, Ledgers.Line{h, None{}}, i)
      )({==})({==})(Ready.open(s, name, rest))
    case Con{Types.Fact.Ask{Types.Ask{+i, +n, Spec.Request.Own{Ledgers.Line{+h, +b}, +g}}}, +rest}:
      Ready.at(
        s,
        RFacts.Facts.list(s),
        name,
        Types.Ask{i, n, Spec.Request.Own{Ledgers.Line{h, b}, g}},
        Ledgers.Line{h, None{}},
        rest,
        RKnown.Line.waits(RKnown.Known.none(), s, Ledgers.Line{h, None{}}, i)
      )({==})({==})(Ready.open(s, name, rest))

# no vote at a slot of a line that waits no more, whatever the next slot m of
# the line
def Follow.at_dead(
  +s: RFacts.Plain(),
  +name: String,
  +c: Ledgers.Line,
  +k: Nat,
  m: Maybe<&2, RWorks.Open>
) -> Open.From(
  RLines.Line.state(s, c),
  m
) -> {
  RKnown.Slot.waits(RLines.Line.state(s, c), k) == False{}: Bool
} -> {
  RWorks.Work.follow.at(RKnown.Known.none(), s, name, c, k, m) == None{}: Maybe<&2, RWorks.Plan>
}:
  match m:
    case None{}:
      o => h => {==}
    case Some{RWorks.Open{+vs, +k2, +ns}}:
      o => h => Crits.Crit.when_false(
        RWorks.Plan,
        Nat.is_eq(k2, k),
        u => RWorks.Plan.of(
          c,
          k,
          RRounds.Slot.follow(RWorks.Work.ballots(RKnown.Known.none(), s, c, k), ns, k, name)
        )
      )(Nat.nle_ne(k2, k)((
            %o: {RKnown.Slot.waits(_, k) == False{}: Bool}
            h)))

# no vote at the slot of a fact that waits no more
def Follow.dead(
  +s: RFacts.Plain(),
  +name: String,
  f: Types.Fact
) -> {
  RKnown.Fact.waits(RKnown.Scene{RKnown.Known.none(), s}, f) == False{}: Bool
} -> {RWorks.Work.follow.of(RKnown.Known.none(), s, name, f) == None{}: Maybe<&2, RWorks.Plan>}:
  match f:
    case Types.Fact.Ask{a}:
      h => {==}
    case Types.Fact.Vote{v, Types.Step.Broken{}, x}:
      h => {==}
    case Types.Fact.Vote{v, Types.Step.At{+c, +k, t}, x}:
      h => Follow.at_dead(
        s,
        name,
        c,
        k,
        RWorks.Work.open(RKnown.Known.none(), s, name, c)
      )(Work.open_from(s, name, c))(h)

# Follow.open at one fact, once it is known whether it waits (w)
def Follow.at(
  +s: RFacts.Plain(),
  +name: String,
  +f: Types.Fact,
  +rest: List<&2, Types.Fact>,
  w: Bool
) -> {
  w == RKnown.Fact.waits(RKnown.Scene{RKnown.Known.none(), s}, f): Bool
} -> {
  RWorks.Work.follow(
    RKnown.Known.none(),
    s,
    name,
    RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), s})
  )
    == RWorks.Work.follow(RKnown.Known.none(), s, name, rest): Maybe<&2, RWorks.Plan>
} -> {
  RWorks.Work.follow(
    RKnown.Known.none(),
    s,
    name,
    List.filter.put(Types.Fact, f, RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), s}), w)
  )
    == RWorks.Work.follow(RKnown.Known.none(), s, name, f <> rest): Maybe<&2, RWorks.Plan>
}:
  match w:
    case True{}:
      ew => ih => (
        %ih: {RWorks.Work.follow(RKnown.Known.none(), s, name, f <> RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), s})) == RWorks.Work.follow.or(RWorks.Work.follow.of(RKnown.Known.none(), s, name, f), u => _): Maybe<&2, RWorks.Plan>}
        {==})
    case False{}:
      ew => ih => (
        %Equal.sym(Maybe<&2, RWorks.Plan>, RWorks.Work.follow.of(RKnown.Known.none(), s, name, f), None{}, Follow.dead(s, name, f)(Equal.sym(Bool, False{}, RKnown.Fact.waits(RKnown.Scene{RKnown.Known.none(), s}, f), ew))): {RWorks.Work.follow(RKnown.Known.none(), s, name, RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), s})) == RWorks.Work.follow.or(_, u => RWorks.Work.follow(RKnown.Known.none(), s, name, rest)): Maybe<&2, RWorks.Plan>}
        ih)

# the first vote at the slot of a ballot among the facts that a work may act
# on is the first among all the facts
def Follow.open(
  +s: RFacts.Plain(),
  +name: String,
  fs: List<&2, Types.Fact>
) -> {
  RWorks.Work.follow(
    RKnown.Known.none(),
    s,
    name,
    RKnown.Open.of(fs, RKnown.Scene{RKnown.Known.none(), s})
  )
    == RWorks.Work.follow(RKnown.Known.none(), s, name, fs): Maybe<&2, RWorks.Plan>
}:
  match fs:
    case Nil{}:
      {==}
    case Con{+f, +rest}:
      Follow.at(
        s,
        name,
        f,
        rest,
        RKnown.Fact.waits(RKnown.Scene{RKnown.Known.none(), s}, f)
      )({==})(Follow.open(s, name, rest))

# no pass at a slot of a line that waits no more, whatever the next slot m of
# the line
def Pass.slot_dead(
  +s: RFacts.Plain(),
  +name: String,
  +c: Ledgers.Line,
  +k: Nat,
  m: Maybe<&2, RWorks.Open>
) -> Open.From(
  RLines.Line.state(s, c),
  m
) -> {
  RKnown.Slot.waits(RLines.Line.state(s, c), k) == False{}: Bool
} -> {
  RWorks.Work.pass.at(
    RKnown.Known.none(),
    s,
    name,
    c,
    Some{k},
    None{},
    m
  )
    == None{}: Maybe<&2, RWorks.Plan>
}:
  match m:
    case None{}:
      o => h => {==}
    case Some{RWorks.Open{+vs, +k2, +ns}}:
      o => h => Crits.Crit.when_false(
        RWorks.Plan,
        Nat.is_eq(k2, k),
        u => RWorks.Plan.of(
          c,
          k2,
          RRounds.Slot.pass(RWorks.Work.ballots(RKnown.Known.none(), s, c, k2), name)
        )
      )(Nat.nle_ne(k2, k)((
            %o: {RKnown.Slot.waits(_, k) == False{}: Bool}
            h)))

# no pass for a request at the next slot m of a line, when the request waits
# no more on the line
def Pass.id_dead(
  +s: RFacts.Plain(),
  +name: String,
  +c: Ledgers.Line,
  +i: Ledgers.Id,
  m: Maybe<&2, RWorks.Open>
) -> Open.From(
  RLines.Line.state(s, c),
  m
) -> {
  RKnown.Id.waits(RLines.Line.state(s, c), RKnown.Known.none(), c, i) == False{}: Bool
} -> {
  RWorks.Work.pass.at(
    RKnown.Known.none(),
    s,
    name,
    c,
    None{},
    Some{i},
    m
  )
    == None{}: Maybe<&2, RWorks.Plan>
}:
  match m:
    case None{}:
      o => h => {==}
    case Some{RWorks.Open{+vs, +k2, +ns}}:
      o => h => Crits.Crit.when_false(
        RWorks.Plan,
        Bool.not(Shared.List.some(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, vs, i)),
        u => RWorks.Plan.of(
          c,
          k2,
          RRounds.Slot.pass(RWorks.Work.ballots(RKnown.Known.none(), s, c, k2), name)
        )
      )(
        %o: {RKnown.Id.waits(_, RKnown.Known.none(), c, i) == False{}: Bool}
        h)

# no pass for a request on its line, when it waits no more on the line
def Pass.line_dead(
  +s: RFacts.Plain(),
  +name: String,
  +c: Ledgers.Line,
  +i: Ledgers.Id
) -> {
  RKnown.Line.waits(RKnown.Known.none(), s, c, i) == False{}: Bool
} -> {
  RWorks.Work.pass.on(RKnown.Known.none(), s, name, i, Some{c}) == None{}: Maybe<&2, RWorks.Plan>
}:
  h => Pass.id_dead(
    s,
    name,
    c,
    i,
    RWorks.Work.open(RKnown.Known.none(), s, name, c)
  )(Work.open_from(s, name, c))(h)

# no pass at the slot of a fact that waits no more
def Pass.dead(
  +s: RFacts.Plain(),
  +name: String,
  f: Types.Fact
) -> {
  RKnown.Fact.waits(RKnown.Scene{RKnown.Known.none(), s}, f) == False{}: Bool
} -> {
  RWorks.Work.pass.of(
    f,
    RKnown.Known.none(),
    s,
    RFacts.Facts.list(s),
    name
  )
    == None{}: Maybe<&2, RWorks.Plan>
}:
  match f:
    case Types.Fact.Vote{v, Types.Step.Broken{}, x}:
      hw => {==}
    case Types.Fact.Vote{v, Types.Step.At{+c, +k, t}, x}:
      hw => Pass.slot_dead(
        s,
        name,
        c,
        k,
        RWorks.Work.open(RKnown.Known.none(), s, name, c)
      )(Work.open_from(s, name, c))(hw)
    case Types.Fact.Ask{Types.Ask{+i, +n, Spec.Request.Start{+os}}}:
      hw => {==}
    case Types.Fact.Ask{Types.Ask{+i, +n, Spec.Request.Write{+b, +p, +w}}}:
      hw => Pass.line_dead(s, name, b, i)(hw)
    case Types.Fact.Ask{Types.Ask{+i, +n, Spec.Request.Merge{+f, +x}}}:
      hw => Pass.line_dead(s, name, x, i)(hw)
    case Types.Fact.Ask{Types.Ask{+i, +n, Spec.Request.Resolve{+m, +p, +w}}}:
      hw => Lists.Maybe.by(
        Ledgers.Line,
        l => {
          RKnown.Resolve.waits(l, RKnown.Known.none(), s, i) == False{}: Bool
        } -> {
          RWorks.Work.pass.on(RKnown.Known.none(), s, name, i, l) == None{}: Maybe<&2, RWorks.Plan>
        },
        RKnown.Merge.line(RFacts.Facts.list(s), m),
        en => h2 => Empty.absurd(
          {
            RWorks.Work.pass.on(
              RKnown.Known.none(),
              s,
              name,
              i,
              None{}
            )
              == None{}: Maybe<&2, RWorks.Plan>
          },
          Shared.Bool.true_ne_false(h2)
        ),
        +c => es => h2 => Pass.line_dead(s, name, c, i)(h2)
      )(hw)
    case Types.Fact.Ask{Types.Ask{+i, +n, Spec.Request.Mark{+b, +m, +v}}}:
      hw => Pass.line_dead(s, name, b, i)(hw)
    case Types.Fact.Ask{Types.Ask{+i, +n, Spec.Request.Move{+b, +t, +v}}}:
      hw => Pass.line_dead(s, name, b, i)(hw)
    case Types.Fact.Ask{Types.Ask{+i, +n, Spec.Request.Group{+h, +g, +ms}}}:
      hw => Pass.line_dead(s, name, Ledgers.Line{h, None{}}, i)(hw)
    case Types.Fact.Ask{Types.Ask{+i, +n, Spec.Request.Own{Ledgers.Line{+h, +b}, +g}}}:
      hw => Pass.line_dead(s, name, Ledgers.Line{h, None{}}, i)(hw)

# Pass.open at one fact, once it is known whether it waits (w)
def Pass.at(
  +s: RFacts.Plain(),
  +name: String,
  +f: Types.Fact,
  +rest: List<&2, Types.Fact>,
  w: Bool
) -> {
  w == RKnown.Fact.waits(RKnown.Scene{RKnown.Known.none(), s}, f): Bool
} -> {
  RWorks.Work.pass(
    RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), s}),
    RKnown.Known.none(),
    s,
    RFacts.Facts.list(s),
    name
  )
    == RWorks.Work.pass(
      rest,
      RKnown.Known.none(),
      s,
      RFacts.Facts.list(s),
      name
    ): Maybe<&2, RWorks.Plan>
} -> {
  RWorks.Work.pass(
    List.filter.put(Types.Fact, f, RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), s}), w),
    RKnown.Known.none(),
    s,
    RFacts.Facts.list(s),
    name
  )
    == RWorks.Work.pass(
      f <> rest,
      RKnown.Known.none(),
      s,
      RFacts.Facts.list(s),
      name
    ): Maybe<&2, RWorks.Plan>
}:
  match w:
    case True{}:
      ew => ih => (
        %ih: {RWorks.Work.pass(f <> RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), s}), RKnown.Known.none(), s, RFacts.Facts.list(s), name) == RWorks.Work.follow.or(RWorks.Work.pass.of(f, RKnown.Known.none(), s, RFacts.Facts.list(s), name), u => _): Maybe<&2, RWorks.Plan>}
        {==})
    case False{}:
      ew => ih => (
        %Equal.sym(Maybe<&2, RWorks.Plan>, RWorks.Work.pass.of(f, RKnown.Known.none(), s, RFacts.Facts.list(s), name), None{}, Pass.dead(s, name, f)(Equal.sym(Bool, False{}, RKnown.Fact.waits(RKnown.Scene{RKnown.Known.none(), s}, f), ew))): {RWorks.Work.pass(RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), s}), RKnown.Known.none(), s, RFacts.Facts.list(s), name) == RWorks.Work.follow.or(_, u => RWorks.Work.pass(rest, RKnown.Known.none(), s, RFacts.Facts.list(s), name)): Maybe<&2, RWorks.Plan>}
        ih)

# the first pass at the slot of a fact among the facts that a work may act
# on is the first among all the facts
def Pass.open(
  +s: RFacts.Plain(),
  +name: String,
  fs: List<&2, Types.Fact>
) -> {
  RWorks.Work.pass(
    RKnown.Open.of(fs, RKnown.Scene{RKnown.Known.none(), s}),
    RKnown.Known.none(),
    s,
    RFacts.Facts.list(s),
    name
  )
    == RWorks.Work.pass(
      fs,
      RKnown.Known.none(),
      s,
      RFacts.Facts.list(s),
      name
    ): Maybe<&2, RWorks.Plan>
}:
  match fs:
    case Nil{}:
      {==}
    case Con{+f, +rest}:
      Pass.at(
        s,
        name,
        f,
        rest,
        RKnown.Fact.waits(RKnown.Scene{RKnown.Known.none(), s}, f)
      )({==})(Pass.open(s, name, rest))

# The plan of a work
# ------------------

# the ballot that the node name casts next, when it walks the facts fs, and
# reads the line of a merge from all the facts of s
def Plan.mix(
  +fs: List<&2, Types.Fact>,
  +s: RFacts.Plain(),
  +name: String
) -> Maybe<&2, RWorks.Plan>:
  RWorks.Work.follow.or(
    RWorks.Work.propose.of(
      Lists.List.top(
        ~Types.Ask,
        ~RFacts.Ask.seq,
        RWorks.Work.ready(fs, RKnown.Known.none(), s, RFacts.Facts.list(s), name)
      ),
      RKnown.Known.none(),
      s,
      RFacts.Facts.list(s),
      name
    ),
    u => RWorks.Work.follow.or(
      RWorks.Work.follow(RKnown.Known.none(), s, name, fs),
      u2 => RWorks.Work.pass(fs, RKnown.Known.none(), s, RFacts.Facts.list(s), name)
    )
  )

# a table that fits changes no ballot that the node casts next, where it
# walks the facts that the table holds for a work
def Work.plan.on_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +name: String
) -> {
  RContents.Known.fit(kn, s) == True{}: Bool
} -> {
  RWorks.Work.plan.on(
    RKnown.Known.facts(kn, s),
    kn,
    s,
    name
  )
    == Plan.mix(RKnown.Known.facts(kn, s), s, name): Maybe<&2, RWorks.Plan>
}:
  +ok => (
    %Work.propose.of_ok(kn, s, name, Lists.List.top(~Types.Ask, ~RFacts.Ask.seq, RWorks.Work.ready(RKnown.Known.facts(kn, s), RKnown.Known.none(), s, RFacts.Facts.list(s), name)))(ok): {RWorks.Work.plan.on(RKnown.Known.facts(kn, s), kn, s, name) == RWorks.Work.follow.or(_, u => RWorks.Work.follow.or(RWorks.Work.follow(RKnown.Known.none(), s, name, RKnown.Known.facts(kn, s)), u2 => RWorks.Work.pass(RKnown.Known.facts(kn, s), RKnown.Known.none(), s, RFacts.Facts.list(s), name))): Maybe<&2, RWorks.Plan>}
    %Work.ready_ok(kn, s, name, RKnown.Known.facts(kn, s))(ok): {RWorks.Work.plan.on(RKnown.Known.facts(kn, s), kn, s, name) == RWorks.Work.follow.or(RWorks.Work.propose.of(Lists.List.top(~Types.Ask, ~RFacts.Ask.seq, _), kn, s, RKnown.Known.facts(kn, s), name), u => RWorks.Work.follow.or(RWorks.Work.follow(RKnown.Known.none(), s, name, RKnown.Known.facts(kn, s)), u2 => RWorks.Work.pass(RKnown.Known.facts(kn, s), RKnown.Known.none(), s, RFacts.Facts.list(s), name))): Maybe<&2, RWorks.Plan>}
    %Work.follow_ok(kn, s, name, RKnown.Known.facts(kn, s))(ok): {RWorks.Work.plan.on(RKnown.Known.facts(kn, s), kn, s, name) == RWorks.Work.follow.or(RWorks.Work.propose.of(Lists.List.top(~Types.Ask, ~RFacts.Ask.seq, RWorks.Work.ready(RKnown.Known.facts(kn, s), kn, s, RKnown.Known.facts(kn, s), name)), kn, s, RKnown.Known.facts(kn, s), name), u => RWorks.Work.follow.or(_, u2 => RWorks.Work.pass(RKnown.Known.facts(kn, s), RKnown.Known.none(), s, RFacts.Facts.list(s), name))): Maybe<&2, RWorks.Plan>}
    %Work.pass_ok(kn, s, name, RKnown.Known.facts(kn, s))(ok): {RWorks.Work.plan.on(RKnown.Known.facts(kn, s), kn, s, name) == RWorks.Work.follow.or(RWorks.Work.propose.of(Lists.List.top(~Types.Ask, ~RFacts.Ask.seq, RWorks.Work.ready(RKnown.Known.facts(kn, s), kn, s, RKnown.Known.facts(kn, s), name)), kn, s, RKnown.Known.facts(kn, s), name), u => RWorks.Work.follow.or(RWorks.Work.follow(kn, s, name, RKnown.Known.facts(kn, s)), u2 => _)): Maybe<&2, RWorks.Plan>}
    {==})

# the ballot that the node casts next, where it walks the facts that a work
# may act on, is the one where it walks all the facts
def Plan.mix_open(
  +s: RFacts.Plain(),
  +name: String
) -> {
  Plan.mix(
    RKnown.Open.of(RFacts.Facts.list(s), RKnown.Scene{RKnown.Known.none(), s}),
    s,
    name
  )
    == Plan.mix(RFacts.Facts.list(s), s, name): Maybe<&2, RWorks.Plan>
}:
  %Ready.open(
    s,
    name,
    RFacts.Facts.list(s)
  ): {
    Plan.mix(
      RKnown.Open.of(RFacts.Facts.list(s), RKnown.Scene{RKnown.Known.none(), s}),
      s,
      name
    )
      == RWorks.Work.follow.or(
        RWorks.Work.propose.of(
          Lists.List.top(~Types.Ask, ~RFacts.Ask.seq, _),
          RKnown.Known.none(),
          s,
          RFacts.Facts.list(s),
          name
        ),
        u => RWorks.Work.follow.or(
          RWorks.Work.follow(RKnown.Known.none(), s, name, RFacts.Facts.list(s)),
          u2 => RWorks.Work.pass(
            RFacts.Facts.list(s),
            RKnown.Known.none(),
            s,
            RFacts.Facts.list(s),
            name
          )
        )
      ): Maybe<&2, RWorks.Plan>
  }
  %Follow.open(
    s,
    name,
    RFacts.Facts.list(s)
  ): {
    Plan.mix(
      RKnown.Open.of(RFacts.Facts.list(s), RKnown.Scene{RKnown.Known.none(), s}),
      s,
      name
    )
      == RWorks.Work.follow.or(
        RWorks.Work.propose.of(
          Lists.List.top(
            ~Types.Ask,
            ~RFacts.Ask.seq,
            RWorks.Work.ready(
              RKnown.Open.of(RFacts.Facts.list(s), RKnown.Scene{RKnown.Known.none(), s}),
              RKnown.Known.none(),
              s,
              RFacts.Facts.list(s),
              name
            )
          ),
          RKnown.Known.none(),
          s,
          RFacts.Facts.list(s),
          name
        ),
        u => RWorks.Work.follow.or(
          _,
          u2 => RWorks.Work.pass(
            RFacts.Facts.list(s),
            RKnown.Known.none(),
            s,
            RFacts.Facts.list(s),
            name
          )
        )
      ): Maybe<&2, RWorks.Plan>
  }
  %Pass.open(
    s,
    name,
    RFacts.Facts.list(s)
  ): {
    Plan.mix(
      RKnown.Open.of(RFacts.Facts.list(s), RKnown.Scene{RKnown.Known.none(), s}),
      s,
      name
    )
      == RWorks.Work.follow.or(
        RWorks.Work.propose.of(
          Lists.List.top(
            ~Types.Ask,
            ~RFacts.Ask.seq,
            RWorks.Work.ready(
              RKnown.Open.of(RFacts.Facts.list(s), RKnown.Scene{RKnown.Known.none(), s}),
              RKnown.Known.none(),
              s,
              RFacts.Facts.list(s),
              name
            )
          ),
          RKnown.Known.none(),
          s,
          RFacts.Facts.list(s),
          name
        ),
        u => RWorks.Work.follow.or(
          RWorks.Work.follow(
            RKnown.Known.none(),
            s,
            name,
            RKnown.Open.of(RFacts.Facts.list(s), RKnown.Scene{RKnown.Known.none(), s})
          ),
          u2 => _
        )
      ): Maybe<&2, RWorks.Plan>
  }
  {==}

# a table that fits changes no ballot that the node casts next
def Work.plan_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +name: String
) -> {
  RContents.Known.fit(kn, s) == True{}: Bool
} -> {
  RWorks.Work.plan(
    kn,
    s,
    name
  )
    == RWorks.Work.plan(RKnown.Known.none(), s, name): Maybe<&2, RWorks.Plan>
}:
  +ok => Equal.trans(
    Maybe<&2, RWorks.Plan>,
    RWorks.Work.plan(kn, s, name),
    Plan.mix(RKnown.Known.facts(kn, s), s, name),
    RWorks.Work.plan(RKnown.Known.none(), s, name),
    Work.plan.on_ok(kn, s, name)(ok),
    Lists.Maybe.by(
      List<&2, Types.Fact>,
      m => {
        Plan.mix(
          RKnown.Open.or(m, s),
          s,
          name
        )
          == Plan.mix(RFacts.Facts.list(s), s, name): Maybe<&2, RWorks.Plan>
      },
      RKnown.Known.open(kn),
      en => {==},
      +fs => es => (
        %Equal.sym(List<&2, Types.Fact>, fs, RKnown.Open.of(RFacts.Facts.list(s), RKnown.Scene{RKnown.Known.none(), s}), Known.open_fit(kn, s, fs)(ok)(es)): {Plan.mix(_, s, name) == Plan.mix(RFacts.Facts.list(s), s, name): Maybe<&2, RWorks.Plan>}
        Plan.mix_open(s, name))
    )
  )

# a right table changes no work
def Work.does_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +name: String
) -> {
  RContents.Known.fit(kn, s) == True{}: Bool
} -> {
  RWorks.Work.does(kn, s, name) == RWorks.Work.does(RKnown.Known.none(), s, name): RFacts.Plain()
}:
  ok => Equal.cong(
    Maybe<&2, RWorks.Plan>,
    RFacts.Plain(),
    m => RWorks.Work.cast(s, name, m),
    RWorks.Work.plan(kn, s, name),
    RWorks.Work.plan(RKnown.Known.none(), s, name),
    Work.plan_ok(kn, s, name)(ok)
  )

# The content and the answers read through a right table
# -----------------------------------------------------

# a right table changes no step of a way
def Way.hop_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +k: Nat,
  +w: Spec.Point
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RContents.Way.hop(kn, s, c, k, w) == RContents.Way.hop(RKnown.Known.none(), s, c, k, w): Bool
}:
  ok => Equal.cong(
    Maybe<&2, Types.Entry>,
    Bool,
    m => RContents.Way.hop.of(c, k, w, m),
    RKnown.Known.at(kn, s, c, k),
    RLines.Line.at(s, c, k),
    Known.at_ok(kn, s, c, k)(ok)
  )

# a right table changes no way
def Way.ok_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +a: Spec.Point,
  ws: List<&2, Spec.Point>,
  +c: Ledgers.Line,
  +k: Nat
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RContents.Way.ok(
    kn,
    s,
    a,
    ws,
    c,
    k
  )
    == RContents.Way.ok(RKnown.Known.none(), s, a, ws, c, k): Bool
}:
  match ws:
    case Nil{}:
      ok => {==}
    case Con{+w, +rest}:
      +ok => (
        %Way.hop_ok(kn, s, c, k, w)(ok): {RContents.Way.ok(kn, s, a, w <> rest, c, k) == Bool.and(_, RContents.Way.ok(RKnown.Known.none(), s, a, rest, Spec.Point.line(w), Spec.Point.n(w))): Bool}
        %Way.ok_ok(kn, s, a, rest, Spec.Point.line(w), Spec.Point.n(w))(ok): {RContents.Way.ok(kn, s, a, w <> rest, c, k) == Bool.and(RContents.Way.hop(kn, s, c, k, w), _): Bool}
        {==})

# a right table changes no check of the ways of a merge
def Merge.fits.of_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +j: Nat,
  m: Maybe<&2, Spec.Point>,
  +ours: List<&2, Spec.Point>,
  +theirs: List<&2, Spec.Point>,
  +t: Spec.Point
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RContents.Merge.fits.of(
    kn,
    s,
    c,
    j,
    m,
    ours,
    theirs,
    t
  )
    == RContents.Merge.fits.of(RKnown.Known.none(), s, c, j, m, ours, theirs, t): Bool
}:
  match m:
    case None{}:
      ok => {==}
    case Some{+a}:
      +ok => (
        %Way.ok_ok(kn, s, a, ours, c, j)(ok): {RContents.Merge.fits.of(kn, s, c, j, Some{a}, ours, theirs, t) == Bool.and(_, RContents.Way.ok(RKnown.Known.none(), s, a, theirs, Spec.Point.line(t), Spec.Point.n(t))): Bool}
        %Way.ok_ok(kn, s, a, theirs, Spec.Point.line(t), Spec.Point.n(t))(ok): {RContents.Merge.fits.of(kn, s, c, j, Some{a}, ours, theirs, t) == Bool.and(RContents.Way.ok(kn, s, a, ours, c, j), _): Bool}
        {==})

# a right table changes no check of a merge
def Merge.fits_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +j: Nat,
  +e: Types.Entry
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RContents.Merge.fits(
    kn,
    s,
    c,
    j,
    e
  )
    == RContents.Merge.fits(RKnown.Known.none(), s, c, j, e): Bool
}:
  ok => Merge.fits.of_ok(
    kn,
    s,
    c,
    j,
    RContents.Entry.base(e),
    RContents.Entry.ours(e),
    RContents.Entry.theirs(e),
    RContents.Point.or(c, RContents.Entry.takes(e))
  )(ok)

# a right table changes no check of a version
def Entry.fits_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +j: Nat,
  m: Maybe<&2, Types.Entry>
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RContents.Entry.fits(
    kn,
    s,
    c,
    j,
    m
  )
    == RContents.Entry.fits(RKnown.Known.none(), s, c, j, m): Bool
}:
  match m:
    case None{}:
      ok => {==}
    case Some{+e}:
      ok => Merge.fits_ok(kn, s, c, j, e)(ok)

# More fuel, same content
# -----------------------

# bend-lint: expect-begin bend-lint-rules/performance/missed_fork@hint -- a proof does not run
# a content read from a plain map with some fuel is read with one more
def Plain.at_more(
  f: Nat,
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  k: Nat,
  -t: RFiles.Files()
) -> {
  RContents.Content.at(f, RKnown.Known.none(), s, c, k) == Some{t}: Maybe<&2, RFiles.Files()>
} -> {
  RContents.Content.at(1n+f, RKnown.Known.none(), s, c, k) == Some{t}: Maybe<&2, RFiles.Files()>
}:
  match f k:
    case 0n k:
      h => Empty.absurd(
        {
          RContents.Content.at(
            1n,
            RKnown.Known.none(),
            s,
            c,
            k
          )
            == Some{t}: Maybe<&2, RFiles.Files()>
        },
        Shared.Maybe.none_ne_some(RFiles.Files(), t, h)
      )
    case 1n+g 0n:
      h => h
    case 1n+(+g) 1n+(+j):
      h => Reads.Content.next_le(
        RLines.Line.at(s, c, 1n+j),
        RContents.Entry.fits(RKnown.Known.none(), s, c, j, RLines.Line.at(s, c, 1n+j)),
        RContents.Content.at(g, RKnown.Known.none(), s, c, j),
        RContents.Content.at(
          g,
          RKnown.Known.none(),
          s,
          Spec.Point.line(RContents.Entry.taken(c, RLines.Line.at(s, c, 1n+j))),
          Spec.Point.n(RContents.Entry.taken(c, RLines.Line.at(s, c, 1n+j)))
        ),
        RContents.Content.at(
          g,
          RKnown.Known.none(),
          s,
          Spec.Point.line(RContents.Entry.based(c, RLines.Line.at(s, c, 1n+j))),
          Spec.Point.n(RContents.Entry.based(c, RLines.Line.at(s, c, 1n+j)))
        ),
        RContents.Entry.fits(RKnown.Known.none(), s, c, j, RLines.Line.at(s, c, 1n+j)),
        RContents.Content.at(1n+g, RKnown.Known.none(), s, c, j),
        RContents.Content.at(
          1n+g,
          RKnown.Known.none(),
          s,
          Spec.Point.line(RContents.Entry.taken(c, RLines.Line.at(s, c, 1n+j))),
          Spec.Point.n(RContents.Entry.taken(c, RLines.Line.at(s, c, 1n+j)))
        ),
        RContents.Content.at(
          1n+g,
          RKnown.Known.none(),
          s,
          Spec.Point.line(RContents.Entry.based(c, RLines.Line.at(s, c, 1n+j))),
          Spec.Point.n(RContents.Entry.based(c, RLines.Line.at(s, c, 1n+j)))
        ),
        t
      )(
        e => e
      )(
        Plain.at_more(g, s, c, j)
      )(
        Plain.at_more(
          g,
          s,
          Spec.Point.line(RContents.Entry.taken(c, RLines.Line.at(s, c, 1n+j))),
          Spec.Point.n(RContents.Entry.taken(c, RLines.Line.at(s, c, 1n+j)))
        )
      )(
        Plain.at_more(
          g,
          s,
          Spec.Point.line(RContents.Entry.based(c, RLines.Line.at(s, c, 1n+j))),
          Spec.Point.n(RContents.Entry.based(c, RLines.Line.at(s, c, 1n+j)))
        )
      )(h)
# bend-lint: expect-end bend-lint-rules/performance/missed_fork@hint

# a content read from a plain map with some fuel is read with any larger fuel
def Plain.at_le(
  g: Nat,
  +f: Nat,
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +k: Nat,
  -t: RFiles.Files()
) -> {
  Nat.is_le(f, g) == True{}: Bool
} -> {
  RContents.Content.at(f, RKnown.Known.none(), s, c, k) == Some{t}: Maybe<&2, RFiles.Files()>
} -> {RContents.Content.at(g, RKnown.Known.none(), s, c, k) == Some{t}: Maybe<&2, RFiles.Files()>}:
  match g:
    case 0n:
      hle => h => Reads.Eq.to(
        Nat,
        y => {
          RContents.Content.at(
            y,
            RKnown.Known.none(),
            s,
            c,
            k
          )
            == Some{t}: Maybe<&2, RFiles.Files()>
        },
        f,
        0n,
        Shared.Nat.le_nlt_eq(f, 0n)(hle)({==}),
        h
      )
    case 1n+(+p):
      +hle => +h => Lists.Bool.by(
        b => {
          RContents.Content.at(
            1n+p,
            RKnown.Known.none(),
            s,
            c,
            k
          )
            == Some{t}: Maybe<&2, RFiles.Files()>
        },
        Nat.is_le(f, p),
        et => Plain.at_more(p, s, c, k, t)(Plain.at_le(p, f, s, c, k, t)(et)(h)),
        ef => Reads.Eq.to(
          Nat,
          y => {
            RContents.Content.at(
              y,
              RKnown.Known.none(),
              s,
              c,
              k
            )
              == Some{t}: Maybe<&2, RFiles.Files()>
          },
          f,
          1n+p,
          Shared.Nat.le_nlt_eq(f, 1n+p)(hle)(ef),
          h
        )
      )

# What a right table holds of the contents
# ----------------------------------------

# the fuel of the content e
def Held.depth(e: RKnown.Held) -> Nat:
  match e:
    case RKnown.Held{c, k, d, x}:
      d

# the files of the content e
def Held.files(e: RKnown.Held) -> RFiles.Files():
  match e:
    case RKnown.Held{c, k, d, x}:
      x

# Stock.get_ok, with the content v that the read gives
def Stock.get_ok.at(
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +k: Nat,
  +c2: Ledgers.Line,
  +k2: Nat,
  +d: Nat,
  +x: RFiles.Files(),
  v: RKnown.Held
) -> {
  RContents.Held.ok(s, v) == True{}: Bool
} -> {
  RKnown.Held.of(Some{v}, c, k) == Some{RKnown.Held{c2, k2, d, x}}: Maybe<&2, RKnown.Held>
} -> {RFiles.Files.fits(RContents.Content.at(d, RKnown.Known.none(), s, c, k), x) == True{}: Bool}:
  match v:
    case RKnown.Held{+c3, +k3, +d3, +x3}:
      +hv => Lists.Bool.by(
        b => {
          Shared.Maybe.when(
            RKnown.Held,
            b,
            u => Some{RKnown.Held{c3, k3, d3, x3}}
          )
            == Some{RKnown.Held{c2, k2, d, x}}: Maybe<&2, RKnown.Held>
        } -> {
          RFiles.Files.fits(
            RContents.Content.at(d, RKnown.Known.none(), s, c, k),
            x
          )
            == True{}: Bool
        },
        List.all.if(u2 => Ledgers.Line.is_eq(c3, c), Nat.is_eq(k3, k)),
        +et => +e => (
          %Ledgers.Line.is_eq_sound(c3, c)(Shared.List.all.if_rest(Nat.is_eq(k3, k), u2 => Ledgers.Line.is_eq(c3, c))(et)): {RFiles.Files.fits(RContents.Content.at(d, RKnown.Known.none(), s, _, k), x) == True{}: Bool}
          %Shared.Nat.is_eq_sound(k3, k)(Shared.List.all.if_hit(Nat.is_eq(k3, k), u2 => Ledgers.Line.is_eq(c3, c))(et)): {RFiles.Files.fits(RContents.Content.at(d, RKnown.Known.none(), s, c3, _), x) == True{}: Bool}
          %Equal.cong(RKnown.Held, Nat, Held.depth, RKnown.Held{c3, k3, d3, x3}, RKnown.Held{c2, k2, d, x}, Shared.Maybe.some_inj(RKnown.Held, RKnown.Held{c3, k3, d3, x3}, RKnown.Held{c2, k2, d, x}, e)): {RFiles.Files.fits(RContents.Content.at(_, RKnown.Known.none(), s, c3, k3), x) == True{}: Bool}
          %Equal.cong(RKnown.Held, RFiles.Files(), Held.files, RKnown.Held{c3, k3, d3, x3}, RKnown.Held{c2, k2, d, x}, Shared.Maybe.some_inj(RKnown.Held, RKnown.Held{c3, k3, d3, x3}, RKnown.Held{c2, k2, d, x}, e)): {RFiles.Files.fits(RContents.Content.at(d3, RKnown.Known.none(), s, c3, k3), _) == True{}: Bool}
          hv),
        ef => e => Empty.absurd(
          {
            RFiles.Files.fits(
              RContents.Content.at(d, RKnown.Known.none(), s, c, k),
              x
            )
              == True{}: Bool
          },
          Shared.Maybe.none_ne_some(RKnown.Held, RKnown.Held{c2, k2, d, x}, e)
        )
      )

# a content that right contents give for a version of a line is the content
# of that version
def Stock.get_ok(
  +m: Crits.Crit<RKnown.Held>,
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +k: Nat,
  +c2: Ledgers.Line,
  +k2: Nat,
  +d: Nat,
  +x: RFiles.Files()
) -> {
  Orders.Crit.every(~RKnown.Held, ~RFacts.Plain(), ~RContents.Held.ok, m, s) == True{}: Bool
} -> {
  RKnown.Stock.get(m, c, k) == Some{RKnown.Held{c2, k2, d, x}}: Maybe<&2, RKnown.Held>
} -> {RFiles.Files.fits(RContents.Content.at(d, RKnown.Known.none(), s, c, k), x) == True{}: Bool}:
  +h => Lists.Maybe.by(
    RKnown.Held,
    mm => {
      RKnown.Held.of(mm, c, k) == Some{RKnown.Held{c2, k2, d, x}}: Maybe<&2, RKnown.Held>
    } -> {
      RFiles.Files.fits(RContents.Content.at(d, RKnown.Known.none(), s, c, k), x) == True{}: Bool
    },
    Crits.Crit.get(RKnown.Held, m, RKnown.Held.key(c, k)),
    en => e => Empty.absurd(
      {RFiles.Files.fits(RContents.Content.at(d, RKnown.Known.none(), s, c, k), x) == True{}: Bool},
      Shared.Maybe.none_ne_some(RKnown.Held, RKnown.Held{c2, k2, d, x}, e)
    ),
    +v => ev => e => Stock.get_ok.at(
      s,
      c,
      k,
      c2,
      k2,
      d,
      x,
      v
    )(
      Orders.Crit.every_get(
        ~RKnown.Held,
        ~RFacts.Plain(),
        ~RContents.Held.ok,
        m,
        s,
        RKnown.Held.key(c, k),
        v
      )(h)(ev)
    )(e)
  )

# a content that a right table holds for a version of a line is the content
# of that version
def Known.held_ok(
  kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +k: Nat,
  +c2: Ledgers.Line,
  +k2: Nat,
  +d: Nat,
  +x: RFiles.Files()
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RKnown.Known.held(kn, c, k) == Some{RKnown.Held{c2, k2, d, x}}: Maybe<&2, RKnown.Held>
} -> {RFiles.Files.fits(RContents.Content.at(d, RKnown.Known.none(), s, c, k), x) == True{}: Bool}:
  match kn:
    case Nil{}:
      ok => e => Empty.absurd(
        {
          RFiles.Files.fits(
            RContents.Content.at(d, RKnown.Known.none(), s, c, k),
            x
          )
            == True{}: Bool
        },
        Shared.Maybe.none_ne_some(RKnown.Held, RKnown.Held{c2, k2, d, x}, e)
      )
    case Con{RKnown.Kept{+c3, +st3}, +rest}:
      ok => e => Known.held_ok(
        rest,
        s,
        c,
        k,
        c2,
        k2,
        d,
        x
      )(Ok.tail(RKnown.Kept{c3, st3}, rest, s)(ok))(e)
    case Con{RKnown.Ruled{+c3, +zu3, +u3}, +rest}:
      ok => e => Known.held_ok(
        rest,
        s,
        c,
        k,
        c2,
        k2,
        d,
        x
      )(Ok.tail(RKnown.Ruled{c3, zu3, u3}, rest, s)(ok))(e)
    case Con{RKnown.Made{+c3, +y3}, +rest}:
      ok => e => Known.held_ok(
        rest,
        s,
        c,
        k,
        c2,
        k2,
        d,
        x
      )(Ok.tail(RKnown.Made{c3, y3}, rest, s)(ok))(e)
    case Con{RKnown.Open{+fs3, +pk3, +tx9, +mtx9}, +rest}:
      ok => e => Known.held_ok(
        rest,
        s,
        c,
        k,
        c2,
        k2,
        d,
        x
      )(Ok.tail(RKnown.Open{fs3, pk3, tx9, mtx9}, rest, s)(ok))(e)
    case Con{RKnown.Stock{+m3, +lwm3}, +rest}:
      +ok => Lists.Maybe.by(
        RKnown.Held,
        mm => {
          RKnown.Held.or(
            mm,
            u => RKnown.Known.held(rest, c, k)
          )
            == Some{RKnown.Held{c2, k2, d, x}}: Maybe<&2, RKnown.Held>
        } -> {
          RFiles.Files.fits(
            RContents.Content.at(d, RKnown.Known.none(), s, c, k),
            x
          )
            == True{}: Bool
        },
        RKnown.Stock.get(m3, c, k),
        en => e => Known.held_ok(
          rest,
          s,
          c,
          k,
          c2,
          k2,
          d,
          x
        )(Ok.tail(RKnown.Stock{m3, lwm3}, rest, s)(ok))(e),
        +v => ev => e => Stock.get_ok(
          m3,
          s,
          c,
          k,
          c2,
          k2,
          d,
          x
        )(
          Stock.head(m3, lwm3, rest, s)(ok)
        )(
          Equal.trans(
            Maybe<&2, RKnown.Held>,
            RKnown.Stock.get(m3, c, k),
            Some{v},
            Some{RKnown.Held{c2, k2, d, x}},
            ev,
            e
          )
        )
      )

# Known.files_ok, with the content m that the table holds
def Known.files_ok.at(
  m: Maybe<&2, RKnown.Held>,
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +k: Nat,
  +f: Nat,
  +x: RFiles.Files()
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RKnown.Known.held(kn, c, k) == m: Maybe<&2, RKnown.Held>
} -> {
  RKnown.Known.files.of(m, f) == Some{x}: Maybe<&2, RFiles.Files()>
} -> {RContents.Content.at(f, RKnown.Known.none(), s, c, k) == Some{x}: Maybe<&2, RFiles.Files()>}:
  match m:
    case None{}:
      ok => em => e => Empty.absurd(
        {
          RContents.Content.at(
            f,
            RKnown.Known.none(),
            s,
            c,
            k
          )
            == Some{x}: Maybe<&2, RFiles.Files()>
        },
        Shared.Maybe.none_ne_some(RFiles.Files(), x, e)
      )
    case Some{RKnown.Held{+c2, +k2, +d, +x2}}:
      ok => em => Lists.Bool.by(
        b => {
          Shared.Maybe.when(RFiles.Files(), b, u => Some{x2}) == Some{x}: Maybe<&2, RFiles.Files()>
        } -> {
          RContents.Content.at(
            f,
            RKnown.Known.none(),
            s,
            c,
            k
          )
            == Some{x}: Maybe<&2, RFiles.Files()>
        },
        Nat.is_le(d, f),
        el => e => (
          %Shared.Maybe.some_inj(RFiles.Files(), x2, x, e): {RContents.Content.at(f, RKnown.Known.none(), s, c, k) == Some{_}: Maybe<&2, RFiles.Files()>}
          Plain.at_le(f, d, s, c, k, x2)(el)(Files.fits_sound(RContents.Content.at(d, RKnown.Known.none(), s, c, k), x2)(Known.held_ok(kn, s, c, k, c2, k2, d, x2)(ok)(em)))),
        el => e => Empty.absurd(
          {
            RContents.Content.at(
              f,
              RKnown.Known.none(),
              s,
              c,
              k
            )
              == Some{x}: Maybe<&2, RFiles.Files()>
          },
          Shared.Maybe.none_ne_some(RFiles.Files(), x, e)
        )
      )

# a content that a right table gives a read with the fuel f is what the read
# gives
def Known.files_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +k: Nat,
  +f: Nat,
  +x: RFiles.Files()
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RKnown.Known.files(kn, c, k, f) == Some{x}: Maybe<&2, RFiles.Files()>
} -> {RContents.Content.at(f, RKnown.Known.none(), s, c, k) == Some{x}: Maybe<&2, RFiles.Files()>}:
  ok => e => Known.files_ok.at(RKnown.Known.held(kn, c, k), kn, s, c, k, f, x)(ok)({==})(e)

# a read through a right table of a content that the table may hold, when
# the read y that it does otherwise is the read with no table, is that read
def Or.ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +k: Nat,
  +f: Nat,
  -y: Maybe<&2, RFiles.Files()>
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  y == RContents.Content.at(f, RKnown.Known.none(), s, c, k): Maybe<&2, RFiles.Files()>
} -> {
  RContents.Content.or(
    RKnown.Known.files(kn, c, k, f),
    u => y
  )
    == RContents.Content.at(f, RKnown.Known.none(), s, c, k): Maybe<&2, RFiles.Files()>
}:
  ok => ey => Lists.Maybe.by(
    RFiles.Files(),
    m => {
      RKnown.Known.files(kn, c, k, f) == m: Maybe<&2, RFiles.Files()>
    } -> {
      RContents.Content.or(
        m,
        u => y
      )
        == RContents.Content.at(f, RKnown.Known.none(), s, c, k): Maybe<&2, RFiles.Files()>
    },
    RKnown.Known.files(kn, c, k, f),
    en => em => ey,
    +x => ex => em => Equal.sym(
      Maybe<&2, RFiles.Files()>,
      RContents.Content.at(f, RKnown.Known.none(), s, c, k),
      Some{x},
      Known.files_ok(kn, s, c, k, f, x)(ok)(em)
    )
  )({==})

# A merge reads a few paths through a right table
# -----------------------------------------------

# what a merge takes is its base with the writes that the hint gives, when
# the state st is that of the line that the merge takes from
def Hint.at(
  st: RLines.State,
  +s: RFacts.Plain(),
  +f: Nat,
  +tl: Ledgers.Line,
  +tn: Nat,
  +al: Ledgers.Line,
  +an: Nat,
  +ws: List<&2, RContents.Write>,
  -x: RFiles.Files(),
  +b: RFiles.Files()
) -> {
  RLines.Line.state(s, tl) == Some{st}: Maybe<&2, RLines.State>
} -> {
  RContents.Merge.hint(
    Some{st},
    Spec.Point{tl, tn},
    Spec.Point{al, an}
  )
    == Some{ws}: Maybe<&2, List<&2, RContents.Write>>
} -> {
  RContents.Content.at(f, RKnown.Known.none(), s, tl, tn) == Some{x}: Maybe<&2, RFiles.Files()>
} -> {
  RContents.Content.at(f, RKnown.Known.none(), s, al, an) == Some{b}: Maybe<&2, RFiles.Files()>
} -> {x == Merges.Writes.apply(ws, b): RFiles.Files()}:
  match st:
    case RLines.State{+vs, +k}:
      hst => +h => hx => hb => Shared.Maybe.some_inj(
        RFiles.Files(),
        x,
        Merges.Writes.apply(ws, b),
        Equal.trans(
          Maybe<&2, RFiles.Files()>,
          Some{x},
          RContents.Content.at(Nat.add(Nat.sub(tn, an), f), RKnown.Known.none(), s, tl, tn),
          Some{Merges.Writes.apply(ws, b)},
          Equal.sym(
            Maybe<&2, RFiles.Files()>,
            RContents.Content.at(Nat.add(Nat.sub(tn, an), f), RKnown.Known.none(), s, tl, tn),
            Some{x},
            Plain.at_le(
              Nat.add(Nat.sub(tn, an), f),
              f,
              s,
              tl,
              tn,
              x
            )(Shared.Nat.le_add(Nat.sub(tn, an), f))(hx)
          ),
          Reads.Eq.to(
            Nat,
            y => {
              RContents.Content.at(
                Nat.add(Nat.sub(tn, an), f),
                RKnown.Known.none(),
                s,
                tl,
                y
              )
                == Some{Merges.Writes.apply(ws, b)}: Maybe<&2, RFiles.Files()>
            },
            Nat.add(Nat.sub(tn, an), an),
            tn,
            Merges.Nat.sub_add(
              tn,
              an
            )(
              Shared.List.all.if_rest(
                Ledgers.Line.is_eq(al, tl),
                u => Nat.is_le(an, tn)
              )(
                Merges.When.cond(
                  List<&2, RContents.Write>,
                  List.all.if(u => Nat.is_le(an, tn), Ledgers.Line.is_eq(al, tl)),
                  u => RContents.Writes.of(Nat.sub(tn, an), List.drop(&2, Types.Entry, vs, 1n+an)),
                  ws
                )(h)
              )
            ),
            Reads.Eq.to(
              Maybe<&2, RFiles.Files()>,
              m => {
                RContents.Content.at(
                  Nat.add(Nat.sub(tn, an), f),
                  RKnown.Known.none(),
                  s,
                  tl,
                  Nat.add(Nat.sub(tn, an), an)
                )
                  == Merges.Writes.over(ws, m): Maybe<&2, RFiles.Files()>
              },
              RContents.Content.at(f, RKnown.Known.none(), s, tl, an),
              Some{b},
              Reads.Eq.to(
                Ledgers.Line,
                y => {
                  RContents.Content.at(
                    f,
                    RKnown.Known.none(),
                    s,
                    y,
                    an
                  )
                    == Some{b}: Maybe<&2, RFiles.Files()>
                },
                al,
                tl,
                Ledgers.Line.is_eq_sound(
                  al,
                  tl
                )(
                  Shared.List.all.if_hit(
                    Ledgers.Line.is_eq(al, tl),
                    u => Nat.is_le(an, tn)
                  )(
                    Merges.When.cond(
                      List<&2, RContents.Write>,
                      List.all.if(u => Nat.is_le(an, tn), Ledgers.Line.is_eq(al, tl)),
                      u => RContents.Writes.of(
                        Nat.sub(tn, an),
                        List.drop(&2, Types.Entry, vs, 1n+an)
                      ),
                      ws
                    )(h)
                  )
                ),
                hb
              ),
              Merges.Writes.at(
                Nat.sub(tn, an),
                List.drop(&2, Types.Entry, vs, 1n+an),
                f,
                s,
                tl,
                an,
                vs,
                ws
              )(
                Reads.Eq.back(
                  Maybe<&2, RLines.State>,
                  m => {
                    Maybe.map(
                      &2,
                      RLines.State,
                      List<&2, Types.Entry>,
                      RLines.State.versions,
                      m
                    )
                      == Some{vs}: Maybe<&2, List<&2, Types.Entry>>
                  },
                  RLines.Line.state(s, tl),
                  Some{RLines.State{vs, k}},
                  hst,
                  {==}
                )
              )(
                {==}
              )(
                Merges.When.then(
                  List<&2, RContents.Write>,
                  List.all.if(u => Nat.is_le(an, tn), Ledgers.Line.is_eq(al, tl)),
                  u => RContents.Writes.of(Nat.sub(tn, an), List.drop(&2, Types.Entry, vs, 1n+an)),
                  ws
                )(h)
              )
            )
          )
        )
      )

# what a merge takes is its base with the writes that the hint gives, read
# through a right table
def Hint.ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +f: Nat,
  t: Spec.Point,
  a: Spec.Point,
  +ws: List<&2, RContents.Write>,
  -x: RFiles.Files(),
  +b: RFiles.Files()
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RContents.Merge.hint(
    RKnown.Known.find(kn, Spec.Point.line(t)),
    t,
    a
  )
    == Some{ws}: Maybe<&2, List<&2, RContents.Write>>
} -> {
  RContents.Content.at(
    f,
    RKnown.Known.none(),
    s,
    Spec.Point.line(t),
    Spec.Point.n(t)
  )
    == Some{x}: Maybe<&2, RFiles.Files()>
} -> {
  RContents.Content.at(
    f,
    RKnown.Known.none(),
    s,
    Spec.Point.line(a),
    Spec.Point.n(a)
  )
    == Some{b}: Maybe<&2, RFiles.Files()>
} -> {x == Merges.Writes.apply(ws, b): RFiles.Files()}:
  match t a:
    case Spec.Point{+tl, +tn} Spec.Point{+al, +an}:
      ok => h => hx => hb => Lists.Maybe.by(
        RLines.State,
        m => {
          RContents.Merge.hint(
            m,
            Spec.Point{tl, tn},
            Spec.Point{al, an}
          )
            == Some{ws}: Maybe<&2, List<&2, RContents.Write>>
        } -> {x == Merges.Writes.apply(ws, b): RFiles.Files()},
        RKnown.Known.find(kn, tl),
        en => h2 => Empty.absurd(
          {x == Merges.Writes.apply(ws, b): RFiles.Files()},
          Shared.Maybe.none_ne_some(List<&2, RContents.Write>, ws, h2)
        ),
        +st => es => h2 => Hint.at(
          st,
          s,
          f,
          tl,
          tn,
          al,
          an,
          ws,
          x,
          b
        )(Known.find_ok(kn, s, tl, st)(ok)(es))(h2)(hx)(hb)
      )(h)

# a version read through a right table, where a merge reads only the paths
# that the hint gives, has the content that it has when a merge reads every
# path
def Hint.next(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +j: Nat,
  +f: Nat
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RContents.Content.quick(
    RContents.Merge.hint(
      RKnown.Known.find(kn, Spec.Point.line(RContents.Entry.taken(c, RLines.Line.at(s, c, 1n+j)))),
      RContents.Entry.taken(c, RLines.Line.at(s, c, 1n+j)),
      RContents.Entry.based(c, RLines.Line.at(s, c, 1n+j))
    ),
    RLines.Line.at(s, c, 1n+j),
    RContents.Entry.fits(RKnown.Known.none(), s, c, j, RLines.Line.at(s, c, 1n+j)),
    RContents.Content.at(f, RKnown.Known.none(), s, c, j),
    RContents.Content.at(
      f,
      RKnown.Known.none(),
      s,
      Spec.Point.line(RContents.Entry.taken(c, RLines.Line.at(s, c, 1n+j))),
      Spec.Point.n(RContents.Entry.taken(c, RLines.Line.at(s, c, 1n+j)))
    ),
    RContents.Content.at(
      f,
      RKnown.Known.none(),
      s,
      Spec.Point.line(RContents.Entry.based(c, RLines.Line.at(s, c, 1n+j))),
      Spec.Point.n(RContents.Entry.based(c, RLines.Line.at(s, c, 1n+j)))
    )
  )
    == RContents.Content.next(
      RLines.Line.at(s, c, 1n+j),
      RContents.Entry.fits(RKnown.Known.none(), s, c, j, RLines.Line.at(s, c, 1n+j)),
      RContents.Content.at(f, RKnown.Known.none(), s, c, j),
      RContents.Content.at(
        f,
        RKnown.Known.none(),
        s,
        Spec.Point.line(RContents.Entry.taken(c, RLines.Line.at(s, c, 1n+j))),
        Spec.Point.n(RContents.Entry.taken(c, RLines.Line.at(s, c, 1n+j)))
      ),
      RContents.Content.at(
        f,
        RKnown.Known.none(),
        s,
        Spec.Point.line(RContents.Entry.based(c, RLines.Line.at(s, c, 1n+j))),
        Spec.Point.n(RContents.Entry.based(c, RLines.Line.at(s, c, 1n+j)))
      )
    ): Maybe<&2, RFiles.Files()>
}:
  ok => Merges.Few.next(
    RContents.Merge.hint(
      RKnown.Known.find(kn, Spec.Point.line(RContents.Entry.taken(c, RLines.Line.at(s, c, 1n+j)))),
      RContents.Entry.taken(c, RLines.Line.at(s, c, 1n+j)),
      RContents.Entry.based(c, RLines.Line.at(s, c, 1n+j))
    ),
    RLines.Line.at(s, c, 1n+j),
    RContents.Entry.fits(RKnown.Known.none(), s, c, j, RLines.Line.at(s, c, 1n+j)),
    RContents.Content.at(f, RKnown.Known.none(), s, c, j),
    RContents.Content.at(
      f,
      RKnown.Known.none(),
      s,
      Spec.Point.line(RContents.Entry.taken(c, RLines.Line.at(s, c, 1n+j))),
      Spec.Point.n(RContents.Entry.taken(c, RLines.Line.at(s, c, 1n+j)))
    ),
    RContents.Content.at(
      f,
      RKnown.Known.none(),
      s,
      Spec.Point.line(RContents.Entry.based(c, RLines.Line.at(s, c, 1n+j))),
      Spec.Point.n(RContents.Entry.based(c, RLines.Line.at(s, c, 1n+j)))
    )
  )(
    Contents.Content.at_sound(f, s, c, j)
  )(
    Contents.Content.at_sound(
      f,
      s,
      Spec.Point.line(RContents.Entry.based(c, RLines.Line.at(s, c, 1n+j))),
      Spec.Point.n(RContents.Entry.based(c, RLines.Line.at(s, c, 1n+j)))
    )
  )(
    ws => t => b => eh => et => eb => Hint.ok(
      kn,
      s,
      f,
      RContents.Entry.taken(c, RLines.Line.at(s, c, 1n+j)),
      RContents.Entry.based(c, RLines.Line.at(s, c, 1n+j)),
      ws,
      t,
      b
    )(ok)(eh)(et)(eb)
  )(
    +ws => +o => +b => eh => ep => eb => Merges.Content.at_clean_all(
      f,
      s,
      c,
      j,
      List.append(
        &2,
        String,
        RContents.Writes.paths(ws),
        RContents.Merge.paths(b, o, Merges.Writes.apply(ws, b))
      ),
      o
    )(ep)
  )

# a right table changes no content of a version
def Content.at_ok(
  fuel: Nat,
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +k: Nat
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RContents.Content.at(
    fuel,
    kn,
    s,
    c,
    k
  )
    == RContents.Content.at(fuel, RKnown.Known.none(), s, c, k): Maybe<&2, RFiles.Files()>
}:
  match fuel k:
    case 0n k:
      ok => {==}
    case 1n+f 0n:
      ok => Equal.cong(
        Maybe<&2, Types.Entry>,
        Maybe<&2, RFiles.Files()>,
        m => RContents.Content.first(m),
        RKnown.Known.at(kn, s, c, 0n),
        RLines.Line.at(s, c, 0n),
        Known.at_ok(kn, s, c, 0n)(ok)
      )
    case 1n+(+f) 1n+(+j):
      +ok => (
        %Hint.next(kn, s, c, j, f)(ok): {RContents.Content.at(1n+f, kn, s, c, 1n+j) == _: Maybe<&2, RFiles.Files()>}
        %Known.at_ok(kn, s, c, 1n+j)(ok): {RContents.Content.at(1n+f, kn, s, c, 1n+j) == RContents.Content.quick(RContents.Merge.hint(RKnown.Known.find(kn, Spec.Point.line(RContents.Entry.taken(c, _))), RContents.Entry.taken(c, _), RContents.Entry.based(c, _)), _, RContents.Entry.fits(RKnown.Known.none(), s, c, j, _), RContents.Content.at(f, RKnown.Known.none(), s, c, j), RContents.Content.at(f, RKnown.Known.none(), s, Spec.Point.line(RContents.Entry.taken(c, _)), Spec.Point.n(RContents.Entry.taken(c, _))), RContents.Content.at(f, RKnown.Known.none(), s, Spec.Point.line(RContents.Entry.based(c, _)), Spec.Point.n(RContents.Entry.based(c, _)))): Maybe<&2, RFiles.Files()>}
        %Entry.fits_ok(kn, s, c, j, RKnown.Known.at(kn, s, c, 1n+j))(ok): {RContents.Content.at(1n+f, kn, s, c, 1n+j) == RContents.Content.quick(RContents.Merge.hint(RKnown.Known.find(kn, Spec.Point.line(RContents.Entry.taken(c, RKnown.Known.at(kn, s, c, 1n+j)))), RContents.Entry.taken(c, RKnown.Known.at(kn, s, c, 1n+j)), RContents.Entry.based(c, RKnown.Known.at(kn, s, c, 1n+j))), RKnown.Known.at(kn, s, c, 1n+j), _, RContents.Content.at(f, RKnown.Known.none(), s, c, j), RContents.Content.at(f, RKnown.Known.none(), s, Spec.Point.line(RContents.Entry.taken(c, RKnown.Known.at(kn, s, c, 1n+j))), Spec.Point.n(RContents.Entry.taken(c, RKnown.Known.at(kn, s, c, 1n+j)))), RContents.Content.at(f, RKnown.Known.none(), s, Spec.Point.line(RContents.Entry.based(c, RKnown.Known.at(kn, s, c, 1n+j))), Spec.Point.n(RContents.Entry.based(c, RKnown.Known.at(kn, s, c, 1n+j))))): Maybe<&2, RFiles.Files()>}
        %Or.ok(kn, s, c, j, f, RContents.Content.at(f, kn, s, c, j))(ok)(Content.at_ok(f, kn, s, c, j)(ok)): {RContents.Content.at(1n+f, kn, s, c, 1n+j) == RContents.Content.quick(RContents.Merge.hint(RKnown.Known.find(kn, Spec.Point.line(RContents.Entry.taken(c, RKnown.Known.at(kn, s, c, 1n+j)))), RContents.Entry.taken(c, RKnown.Known.at(kn, s, c, 1n+j)), RContents.Entry.based(c, RKnown.Known.at(kn, s, c, 1n+j))), RKnown.Known.at(kn, s, c, 1n+j), RContents.Entry.fits(kn, s, c, j, RKnown.Known.at(kn, s, c, 1n+j)), _, RContents.Content.at(f, RKnown.Known.none(), s, Spec.Point.line(RContents.Entry.taken(c, RKnown.Known.at(kn, s, c, 1n+j))), Spec.Point.n(RContents.Entry.taken(c, RKnown.Known.at(kn, s, c, 1n+j)))), RContents.Content.at(f, RKnown.Known.none(), s, Spec.Point.line(RContents.Entry.based(c, RKnown.Known.at(kn, s, c, 1n+j))), Spec.Point.n(RContents.Entry.based(c, RKnown.Known.at(kn, s, c, 1n+j))))): Maybe<&2, RFiles.Files()>}
        %Or.ok(kn, s, Spec.Point.line(RContents.Entry.taken(c, RKnown.Known.at(kn, s, c, 1n+j))), Spec.Point.n(RContents.Entry.taken(c, RKnown.Known.at(kn, s, c, 1n+j))), f, RContents.Content.at(f, kn, s, Spec.Point.line(RContents.Entry.taken(c, RKnown.Known.at(kn, s, c, 1n+j))), Spec.Point.n(RContents.Entry.taken(c, RKnown.Known.at(kn, s, c, 1n+j)))))(ok)(Content.at_ok(f, kn, s, Spec.Point.line(RContents.Entry.taken(c, RKnown.Known.at(kn, s, c, 1n+j))), Spec.Point.n(RContents.Entry.taken(c, RKnown.Known.at(kn, s, c, 1n+j))))(ok)): {RContents.Content.at(1n+f, kn, s, c, 1n+j) == RContents.Content.quick(RContents.Merge.hint(RKnown.Known.find(kn, Spec.Point.line(RContents.Entry.taken(c, RKnown.Known.at(kn, s, c, 1n+j)))), RContents.Entry.taken(c, RKnown.Known.at(kn, s, c, 1n+j)), RContents.Entry.based(c, RKnown.Known.at(kn, s, c, 1n+j))), RKnown.Known.at(kn, s, c, 1n+j), RContents.Entry.fits(kn, s, c, j, RKnown.Known.at(kn, s, c, 1n+j)), RContents.Content.or(RKnown.Known.files(kn, c, j, f), u => RContents.Content.at(f, kn, s, c, j)), _, RContents.Content.at(f, RKnown.Known.none(), s, Spec.Point.line(RContents.Entry.based(c, RKnown.Known.at(kn, s, c, 1n+j))), Spec.Point.n(RContents.Entry.based(c, RKnown.Known.at(kn, s, c, 1n+j))))): Maybe<&2, RFiles.Files()>}
        %Or.ok(kn, s, Spec.Point.line(RContents.Entry.based(c, RKnown.Known.at(kn, s, c, 1n+j))), Spec.Point.n(RContents.Entry.based(c, RKnown.Known.at(kn, s, c, 1n+j))), f, RContents.Content.at(f, kn, s, Spec.Point.line(RContents.Entry.based(c, RKnown.Known.at(kn, s, c, 1n+j))), Spec.Point.n(RContents.Entry.based(c, RKnown.Known.at(kn, s, c, 1n+j)))))(ok)(Content.at_ok(f, kn, s, Spec.Point.line(RContents.Entry.based(c, RKnown.Known.at(kn, s, c, 1n+j))), Spec.Point.n(RContents.Entry.based(c, RKnown.Known.at(kn, s, c, 1n+j))))(ok)): {RContents.Content.at(1n+f, kn, s, c, 1n+j) == RContents.Content.quick(RContents.Merge.hint(RKnown.Known.find(kn, Spec.Point.line(RContents.Entry.taken(c, RKnown.Known.at(kn, s, c, 1n+j)))), RContents.Entry.taken(c, RKnown.Known.at(kn, s, c, 1n+j)), RContents.Entry.based(c, RKnown.Known.at(kn, s, c, 1n+j))), RKnown.Known.at(kn, s, c, 1n+j), RContents.Entry.fits(kn, s, c, j, RKnown.Known.at(kn, s, c, 1n+j)), RContents.Content.or(RKnown.Known.files(kn, c, j, f), u => RContents.Content.at(f, kn, s, c, j)), RContents.Content.or(RKnown.Known.files(kn, Spec.Point.line(RContents.Entry.taken(c, RKnown.Known.at(kn, s, c, 1n+j))), Spec.Point.n(RContents.Entry.taken(c, RKnown.Known.at(kn, s, c, 1n+j))), f), u => RContents.Content.at(f, kn, s, Spec.Point.line(RContents.Entry.taken(c, RKnown.Known.at(kn, s, c, 1n+j))), Spec.Point.n(RContents.Entry.taken(c, RKnown.Known.at(kn, s, c, 1n+j))))), _): Maybe<&2, RFiles.Files()>}
        {==})

# the number that a right table holds with its first contents is at most
# the count of the facts
def Known.low_ok(
  kn: RKnown.Known(),
  +s: RFacts.Plain()
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {Nat.is_le(RKnown.Known.low(kn), RFacts.Facts.fuel(s)) == True{}: Bool}:
  match kn:
    case Nil{}:
      ok => Shared.Nat.le_zero(RFacts.Facts.fuel(s))
    case Con{RKnown.Kept{+c2, +st2}, +rest}:
      ok => Known.low_ok(rest, s)(Ok.tail(RKnown.Kept{c2, st2}, rest, s)(ok))
    case Con{RKnown.Ruled{+c2, +zu2, +u2}, +rest}:
      ok => Known.low_ok(rest, s)(Ok.tail(RKnown.Ruled{c2, zu2, u2}, rest, s)(ok))
    case Con{RKnown.Made{+c2, +y2}, +rest}:
      ok => Known.low_ok(rest, s)(Ok.tail(RKnown.Made{c2, y2}, rest, s)(ok))
    case Con{RKnown.Open{+fs2, +pk2, +tx9, +mtx9}, +rest}:
      ok => Known.low_ok(rest, s)(Ok.tail(RKnown.Open{fs2, pk2, tx9, mtx9}, rest, s)(ok))
    case Con{RKnown.Stock{+m2, +lwm2}, +rest}:
      ok => Stock.head_low(m2, lwm2, rest, s)(ok)

# a right table changes no content
def Content.of_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +k: Nat
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RContents.Content.of(
    kn,
    s,
    c,
    k
  )
    == RContents.Content.of(RKnown.Known.none(), s, c, k): Maybe<&2, RFiles.Files()>
}:
  +ok =>
    %Equal.sym(
      Maybe<&2, RFiles.Files()>,
      RContents.Content.from(RFacts.Facts.fuel(s), kn, s, c, k),
      RContents.Content.at(RFacts.Facts.fuel(s), RKnown.Known.none(), s, c, k),
      Or.ok(
        kn,
        s,
        c,
        k,
        RFacts.Facts.fuel(s),
        RContents.Content.at(RFacts.Facts.fuel(s), kn, s, c, k)
      )(ok)(Content.at_ok(RFacts.Facts.fuel(s), kn, s, c, k)(ok))
    ): {
      RContents.Content.or(
        RKnown.Known.files(kn, c, k, RKnown.Known.low(kn)),
        u => _
      )
        == RContents.Content.at(
          RFacts.Facts.fuel(s),
          RKnown.Known.none(),
          s,
          c,
          k
        ): Maybe<&2, RFiles.Files()>
    }
    Lists.Maybe.by(
      RFiles.Files(),
      m => {
        RKnown.Known.files(kn, c, k, RKnown.Known.low(kn)) == m: Maybe<&2, RFiles.Files()>
      } -> {
        RContents.Content.or(
          m,
          u => RContents.Content.at(RFacts.Facts.fuel(s), RKnown.Known.none(), s, c, k)
        )
          == RContents.Content.at(
            RFacts.Facts.fuel(s),
            RKnown.Known.none(),
            s,
            c,
            k
          ): Maybe<&2, RFiles.Files()>
      },
      RKnown.Known.files(kn, c, k, RKnown.Known.low(kn)),
      en => em => {==},
      +x => ex => em => Equal.sym(
        Maybe<&2, RFiles.Files()>,
        RContents.Content.at(RFacts.Facts.fuel(s), RKnown.Known.none(), s, c, k),
        Some{x},
        Plain.at_le(
          RFacts.Facts.fuel(s),
          RKnown.Known.low(kn),
          s,
          c,
          k,
          x
        )(Known.low_ok(kn, s)(ok))(Known.files_ok(kn, s, c, k, RKnown.Known.low(kn), x)(ok)(em))
      )
    )({==})

# What a node learns of the contents
# ----------------------------------

# right contents with a right content are right
def Stock.put_ok(
  +m: Crits.Crit<RKnown.Held>,
  +s: RFacts.Plain(),
  e: RKnown.Held
) -> {
  Orders.Crit.every(~RKnown.Held, ~RFacts.Plain(), ~RContents.Held.ok, m, s) == True{}: Bool
} -> {
  RContents.Held.ok(s, e) == True{}: Bool
} -> {
  Orders.Crit.every(
    ~RKnown.Held,
    ~RFacts.Plain(),
    ~RContents.Held.ok,
    RKnown.Stock.put(m, e),
    s
  )
    == True{}: Bool
}:
  match e:
    case RKnown.Held{+c, +k, +d, +x}:
      h => he => Orders.Crit.every_set(
        ~RKnown.Held,
        ~RFacts.Plain(),
        ~RContents.Held.ok,
        m,
        s,
        RKnown.Held.key(c, k),
        RKnown.Held{c, k, d, x}
      )(h)(he)

# a right table with a right content is right
def Known.hold_ok(
  kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +e: RKnown.Held
) -> {
  RContents.Held.ok(s, e) == True{}: Bool
} -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {RContents.Known.ok(RKnown.Known.hold(kn, e), s) == True{}: Bool}:
  match kn:
    case Nil{}:
      he => ok => Stock.cons(
        RKnown.Stock.put(Crits.Crit.new(RKnown.Held), e),
        0n,
        [],
        s
      )(
        Stock.put_ok(Crits.Crit.new(RKnown.Held), s, e)({==})(he)
      )(Shared.Nat.le_zero(RFacts.Facts.fuel(s)))({==})
    case Con{RKnown.Kept{+c, +st}, +rest}:
      he => +ok => Ok.cons(
        RKnown.Kept{c, st},
        RKnown.Known.hold(rest, e),
        s
      )(
        Ok.head(RKnown.Kept{c, st}, rest, s)(ok)
      )(Known.hold_ok(rest, s, e)(he)(Ok.tail(RKnown.Kept{c, st}, rest, s)(ok)))
    case Con{RKnown.Stock{+m, +lwm}, +rest}:
      he => +ok => Stock.cons(
        RKnown.Stock.put(m, e),
        lwm,
        rest,
        s
      )(
        Stock.put_ok(m, s, e)(Stock.head(m, lwm, rest, s)(ok))(he)
      )(Stock.head_low(m, lwm, rest, s)(ok))(Ok.tail(RKnown.Stock{m, lwm}, rest, s)(ok))
    case Con{RKnown.Ruled{+c, +zu, +u}, +rest}:
      he => +ok => Ok.cons(
        RKnown.Ruled{c, zu, u},
        RKnown.Known.hold(rest, e),
        s
      )(
        Ok.head(RKnown.Ruled{c, zu, u}, rest, s)(ok)
      )(Known.hold_ok(rest, s, e)(he)(Ok.tail(RKnown.Ruled{c, zu, u}, rest, s)(ok)))
    case Con{RKnown.Made{+c, +y}, +rest}:
      he => +ok => Ok.cons(
        RKnown.Made{c, y},
        RKnown.Known.hold(rest, e),
        s
      )(
        Ok.head(RKnown.Made{c, y}, rest, s)(ok)
      )(Known.hold_ok(rest, s, e)(he)(Ok.tail(RKnown.Made{c, y}, rest, s)(ok)))
    case Con{RKnown.Open{+fs2, +pk2, +tx9, +mtx9}, +rest}:
      he => +ok => Ok.cons(
        RKnown.Open{fs2, pk2, tx9, mtx9},
        RKnown.Known.hold(rest, e),
        s
      )(
        Ok.head(RKnown.Open{fs2, pk2, tx9, mtx9}, rest, s)(ok)
      )(Known.hold_ok(rest, s, e)(he)(Ok.tail(RKnown.Open{fs2, pk2, tx9, mtx9}, rest, s)(ok)))

# a right table with the content m, if any, that a read with the fuel d
# gives, is right
def Known.fill_of_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +k: Nat,
  +d: Nat,
  m: Maybe<&2, RFiles.Files()>
) -> {
  RContents.Content.at(d, RKnown.Known.none(), s, c, k) == m: Maybe<&2, RFiles.Files()>
} -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {RContents.Known.ok(RContents.Known.fill.of(kn, c, k, d, m), s) == True{}: Bool}:
  match m:
    case None{}:
      e => ok => ok
    case Some{+x}:
      e => ok => Known.hold_ok(
        kn,
        s,
        RKnown.Held{c, k, d, x}
      )(Files.fits_of(RContents.Content.at(d, RKnown.Known.none(), s, c, k), x)(e))(ok)

# a right table with a content read through it is right
def Known.fill_at_ok(
  +d: Nat,
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +k: Nat
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {RContents.Known.ok(RContents.Known.fill.at(d, kn, s, c, k), s) == True{}: Bool}:
  +ok => Known.fill_of_ok(
    kn,
    s,
    c,
    k,
    d,
    RContents.Content.at(d, kn, s, c, k)
  )(
    Equal.sym(
      Maybe<&2, RFiles.Files()>,
      RContents.Content.at(d, kn, s, c, k),
      RContents.Content.at(d, RKnown.Known.none(), s, c, k),
      Content.at_ok(d, kn, s, c, k)(ok)
    )
  )(ok)

# the content of the version after j, read with one more fuel than d, is
# what the entry m of that version makes of the contents that it reads with
# the fuel d
def Content.at_step(
  +d: Nat,
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +j: Nat,
  +m: Maybe<&2, Types.Entry>
) -> {
  RLines.Line.at(s, c, 1n+j) == m: Maybe<&2, Types.Entry>
} -> {
  RContents.Content.at(
    1n+d,
    RKnown.Known.none(),
    s,
    c,
    1n+j
  )
    == RContents.Content.next(
      m,
      RContents.Entry.fits(RKnown.Known.none(), s, c, j, m),
      RContents.Content.at(d, RKnown.Known.none(), s, c, j),
      RContents.Content.or(
        RKnown.Known.files(
          RKnown.Known.none(),
          Spec.Point.line(RContents.Entry.taken(c, m)),
          Spec.Point.n(RContents.Entry.taken(c, m)),
          d
        ),
        u => RContents.Content.at(
          d,
          RKnown.Known.none(),
          s,
          Spec.Point.line(RContents.Entry.taken(c, m)),
          Spec.Point.n(RContents.Entry.taken(c, m))
        )
      ),
      RContents.Content.or(
        RKnown.Known.files(
          RKnown.Known.none(),
          Spec.Point.line(RContents.Entry.based(c, m)),
          Spec.Point.n(RContents.Entry.based(c, m)),
          d
        ),
        u => RContents.Content.at(
          d,
          RKnown.Known.none(),
          s,
          Spec.Point.line(RContents.Entry.based(c, m)),
          Spec.Point.n(RContents.Entry.based(c, m))
        )
      )
    ): Maybe<&2, RFiles.Files()>
}:
  e => (
    %e: {RContents.Content.at(1n+d, RKnown.Known.none(), s, c, 1n+j) == RContents.Content.next(_, RContents.Entry.fits(RKnown.Known.none(), s, c, j, _), RContents.Content.at(d, RKnown.Known.none(), s, c, j), RContents.Content.or(RKnown.Known.files(RKnown.Known.none(), Spec.Point.line(RContents.Entry.taken(c, _)), Spec.Point.n(RContents.Entry.taken(c, _)), d), u => RContents.Content.at(d, RKnown.Known.none(), s, Spec.Point.line(RContents.Entry.taken(c, _)), Spec.Point.n(RContents.Entry.taken(c, _)))), RContents.Content.or(RKnown.Known.files(RKnown.Known.none(), Spec.Point.line(RContents.Entry.based(c, _)), Spec.Point.n(RContents.Entry.based(c, _)), d), u => RContents.Content.at(d, RKnown.Known.none(), s, Spec.Point.line(RContents.Entry.based(c, _)), Spec.Point.n(RContents.Entry.based(c, _))))): Maybe<&2, RFiles.Files()>}
    {==})

# a right table with the content of the version after j, made by the request
# r from the content x of version j, is right
def Known.fill_write_ok(
  r: Spec.Request,
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +j: Nat,
  +d: Nat,
  +x: RFiles.Files(),
  +i: Ledgers.Id,
  +n: Nat,
  +pins: Types.Pins,
  +slot: Nat
) -> {
  RLines.Line.at(
    s,
    c,
    1n+j
  )
    == Some{Types.Entry{Types.Pick{Types.Ask{i, n, r}, pins}, slot}}: Maybe<&2, Types.Entry>
} -> {
  RContents.Content.at(d, RKnown.Known.none(), s, c, j) == Some{x}: Maybe<&2, RFiles.Files()>
} -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {RContents.Known.ok(RContents.Known.fill.write(r, kn, s, c, j, d, x), s) == True{}: Bool}:
  match r:
    case Spec.Request.Start{os}:
      he => hx => ok => Known.fill_at_ok(
        RContents.Fill.fuel(
          1n+j,
          kn,
          c,
          RKnown.Known.at(kn, s, c, 1n+j),
          u => RFacts.Facts.fuel(s)
        ),
        kn,
        s,
        c,
        1n+j
      )(ok)
    case Spec.Request.Write{+b, +p, +w}:
      he => hx => ok => Known.fill_of_ok(
        kn,
        s,
        c,
        1n+j,
        1n+d,
        Some{RFiles.Files.set(x, p, w)}
      )(
        Equal.trans(
          Maybe<&2, RFiles.Files()>,
          RContents.Content.at(1n+d, RKnown.Known.none(), s, c, 1n+j),
          RContents.Content.write(p, w, RContents.Content.at(d, RKnown.Known.none(), s, c, j)),
          Some{RFiles.Files.set(x, p, w)},
          Content.at_step(
            d,
            s,
            c,
            j,
            Some{Types.Entry{Types.Pick{Types.Ask{i, n, Spec.Request.Write{b, p, w}}, pins}, slot}}
          )(he),
          Equal.cong(
            Maybe<&2, RFiles.Files()>,
            Maybe<&2, RFiles.Files()>,
            y => RContents.Content.write(p, w, y),
            RContents.Content.at(d, RKnown.Known.none(), s, c, j),
            Some{x},
            hx
          )
        )
      )(ok)
    case Spec.Request.Merge{f, y}:
      he => hx => ok => Known.fill_at_ok(
        RContents.Fill.fuel(
          1n+j,
          kn,
          c,
          RKnown.Known.at(kn, s, c, 1n+j),
          u => RFacts.Facts.fuel(s)
        ),
        kn,
        s,
        c,
        1n+j
      )(ok)
    case Spec.Request.Resolve{+m, +p, +w}:
      he => hx => ok => Known.fill_of_ok(
        kn,
        s,
        c,
        1n+j,
        1n+d,
        Some{RFiles.Files.set(x, p, w)}
      )(
        Equal.trans(
          Maybe<&2, RFiles.Files()>,
          RContents.Content.at(1n+d, RKnown.Known.none(), s, c, 1n+j),
          RContents.Content.write(p, w, RContents.Content.at(d, RKnown.Known.none(), s, c, j)),
          Some{RFiles.Files.set(x, p, w)},
          Content.at_step(
            d,
            s,
            c,
            j,
            Some{
              Types.Entry{Types.Pick{Types.Ask{i, n, Spec.Request.Resolve{m, p, w}}, pins}, slot}
            }
          )(he),
          Equal.cong(
            Maybe<&2, RFiles.Files()>,
            Maybe<&2, RFiles.Files()>,
            y => RContents.Content.write(p, w, y),
            RContents.Content.at(d, RKnown.Known.none(), s, c, j),
            Some{x},
            hx
          )
        )
      )(ok)
    case Spec.Request.Mark{b, m, v}:
      he => hx => ok => Known.fill_at_ok(
        RContents.Fill.fuel(
          1n+j,
          kn,
          c,
          RKnown.Known.at(kn, s, c, 1n+j),
          u => RFacts.Facts.fuel(s)
        ),
        kn,
        s,
        c,
        1n+j
      )(ok)
    case Spec.Request.Move{b, t, v}:
      he => hx => ok => Known.fill_at_ok(
        RContents.Fill.fuel(
          1n+j,
          kn,
          c,
          RKnown.Known.at(kn, s, c, 1n+j),
          u => RFacts.Facts.fuel(s)
        ),
        kn,
        s,
        c,
        1n+j
      )(ok)
    case Spec.Request.Group{h, g, ms}:
      he => hx => ok => Known.fill_at_ok(
        RContents.Fill.fuel(
          1n+j,
          kn,
          c,
          RKnown.Known.at(kn, s, c, 1n+j),
          u => RFacts.Facts.fuel(s)
        ),
        kn,
        s,
        c,
        1n+j
      )(ok)
    case Spec.Request.Own{b, g}:
      he => hx => ok => Known.fill_at_ok(
        RContents.Fill.fuel(
          1n+j,
          kn,
          c,
          RKnown.Known.at(kn, s, c, 1n+j),
          u => RFacts.Facts.fuel(s)
        ),
        kn,
        s,
        c,
        1n+j
      )(ok)

# a right table with the content of the version after j, when prev is what
# the table holds of the content of version j and e the entry of the version
# after j, is right
def Known.fill_next_ok(
  prev: Maybe<&2, RKnown.Held>,
  e: Maybe<&2, Types.Entry>,
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +j: Nat
) -> {
  RKnown.Known.held(kn, c, j) == prev: Maybe<&2, RKnown.Held>
} -> {
  RKnown.Known.at(kn, s, c, 1n+j) == e: Maybe<&2, Types.Entry>
} -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {RContents.Known.ok(RContents.Known.fill.next(prev, e, kn, s, c, j), s) == True{}: Bool}:
  match prev e:
    case Some{
      RKnown.Held{+c2, +k2, +d, +x}
    } Some{Types.Entry{Types.Pick{Types.Ask{+i, +n, +r}, +pins}, +slot}}:
      hp => he => +ok => Known.fill_write_ok(
        r,
        kn,
        s,
        c,
        j,
        d,
        x,
        i,
        n,
        pins,
        slot
      )(
        Equal.trans(
          Maybe<&2, Types.Entry>,
          RLines.Line.at(s, c, 1n+j),
          RKnown.Known.at(kn, s, c, 1n+j),
          Some{Types.Entry{Types.Pick{Types.Ask{i, n, r}, pins}, slot}},
          Equal.sym(
            Maybe<&2, Types.Entry>,
            RKnown.Known.at(kn, s, c, 1n+j),
            RLines.Line.at(s, c, 1n+j),
            Known.at_ok(kn, s, c, 1n+j)(ok)
          ),
          he
        )
      )(Known.files_ok(kn, s, c, j, d, x)(ok)((
            %Equal.sym(Maybe<&2, RKnown.Held>, RKnown.Known.held(kn, c, j), Some{RKnown.Held{c2, k2, d, x}}, hp): {RKnown.Known.files.of(_, d) == Some{x}: Maybe<&2, RFiles.Files()>}
            %Equal.sym(Bool, Nat.is_le(d, d), True{}, Shared.Nat.le_refl(d)): {Shared.Maybe.when(RFiles.Files(), _, u => Some{x}) == Some{x}: Maybe<&2, RFiles.Files()>}
            {==})))(ok)
    case None{} None{}:
      hp => he => ok => Known.fill_at_ok(
        RContents.Fill.fuel(
          1n+j,
          kn,
          c,
          RKnown.Known.at(kn, s, c, 1n+j),
          u => RFacts.Facts.fuel(s)
        ),
        kn,
        s,
        c,
        1n+j
      )(ok)
    case None{} Some{Types.Entry{Types.Pick{Types.Ask{i, n, r}, pins}, slot}}:
      hp => he => ok => Known.fill_at_ok(
        RContents.Fill.fuel(
          1n+j,
          kn,
          c,
          RKnown.Known.at(kn, s, c, 1n+j),
          u => RFacts.Facts.fuel(s)
        ),
        kn,
        s,
        c,
        1n+j
      )(ok)
    case Some{RKnown.Held{c2, k2, d, x}} None{}:
      hp => he => ok => Known.fill_at_ok(
        RContents.Fill.fuel(
          1n+j,
          kn,
          c,
          RKnown.Known.at(kn, s, c, 1n+j),
          u => RFacts.Facts.fuel(s)
        ),
        kn,
        s,
        c,
        1n+j
      )(ok)

# a right table with the content of a version is right
def Known.fill_new_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  k: Nat
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {RContents.Known.ok(RContents.Known.fill.new(kn, s, c, k), s) == True{}: Bool}:
  match k:
    case 0n:
      ok => Known.fill_at_ok(
        RContents.Fill.fuel(0n, kn, c, RKnown.Known.at(kn, s, c, 0n), u => RFacts.Facts.fuel(s)),
        kn,
        s,
        c,
        0n
      )(ok)
    case 1n+(+j):
      ok => Known.fill_next_ok(
        RKnown.Known.held(kn, c, j),
        RKnown.Known.at(kn, s, c, 1n+j),
        kn,
        s,
        c,
        j
      )({==})({==})(ok)

# a right table with the content of a version is right
def Known.fill_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +k: Nat
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {RContents.Known.ok(RContents.Known.fill(kn, s, c, k), s) == True{}: Bool}:
  +ok => Lists.Bool.by(
    b => {RContents.Known.ok(RContents.Known.fill.if(b, kn, s, c, k), s) == True{}: Bool},
    Maybe.is_some(&2, Nat, RKnown.Known.depth(kn, c, k)),
    et => ok,
    ef => Known.fill_new_ok(kn, s, c, k)(ok)
  )

# a right table with the contents of some versions of a line is right
def Known.warm_go_ok(
  n: Nat,
  +k: Nat,
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {RContents.Known.ok(RContents.Known.warm.go(n, k, kn, s, c), s) == True{}: Bool}:
  match n:
    case 0n:
      ok => ok
    case 1n+p:
      ok => Known.warm_go_ok(
        p,
        1n+k,
        RContents.Known.fill(kn, s, c, k),
        s,
        c
      )(Known.fill_ok(kn, s, c, k)(ok))

# a right table with the count of the facts as the number of its first
# contents is right
def Known.sync_ok(
  kn: RKnown.Known(),
  +s: RFacts.Plain()
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {RContents.Known.ok(RKnown.Known.sync(kn, RFacts.Facts.fuel(s)), s) == True{}: Bool}:
  match kn:
    case Nil{}:
      ok => Stock.cons(
        Crits.Crit.new(RKnown.Held),
        RFacts.Facts.fuel(s),
        [],
        s
      )({==})(Shared.Nat.le_refl(RFacts.Facts.fuel(s)))({==})
    case Con{RKnown.Kept{+c2, +st2}, +rest}:
      +ok => Ok.cons(
        RKnown.Kept{c2, st2},
        RKnown.Known.sync(rest, RFacts.Facts.fuel(s)),
        s
      )(
        Ok.head(RKnown.Kept{c2, st2}, rest, s)(ok)
      )(Known.sync_ok(rest, s)(Ok.tail(RKnown.Kept{c2, st2}, rest, s)(ok)))
    case Con{RKnown.Ruled{+c2, +zu2, +u2}, +rest}:
      +ok => Ok.cons(
        RKnown.Ruled{c2, zu2, u2},
        RKnown.Known.sync(rest, RFacts.Facts.fuel(s)),
        s
      )(
        Ok.head(RKnown.Ruled{c2, zu2, u2}, rest, s)(ok)
      )(Known.sync_ok(rest, s)(Ok.tail(RKnown.Ruled{c2, zu2, u2}, rest, s)(ok)))
    case Con{RKnown.Made{+c2, +y2}, +rest}:
      +ok => Ok.cons(
        RKnown.Made{c2, y2},
        RKnown.Known.sync(rest, RFacts.Facts.fuel(s)),
        s
      )(
        Ok.head(RKnown.Made{c2, y2}, rest, s)(ok)
      )(Known.sync_ok(rest, s)(Ok.tail(RKnown.Made{c2, y2}, rest, s)(ok)))
    case Con{RKnown.Open{+fs2, +pk2, +tx9, +mtx9}, +rest}:
      +ok => Ok.cons(
        RKnown.Open{fs2, pk2, tx9, mtx9},
        RKnown.Known.sync(rest, RFacts.Facts.fuel(s)),
        s
      )(
        Ok.head(RKnown.Open{fs2, pk2, tx9, mtx9}, rest, s)(ok)
      )(Known.sync_ok(rest, s)(Ok.tail(RKnown.Open{fs2, pk2, tx9, mtx9}, rest, s)(ok)))
    case Con{RKnown.Stock{+m2, +lwm2}, +rest}:
      +ok => Stock.cons(
        m2,
        RFacts.Facts.fuel(s),
        rest,
        s
      )(
        Stock.head(m2, lwm2, rest, s)(ok)
      )(Shared.Nat.le_refl(RFacts.Facts.fuel(s)))(Ok.tail(RKnown.Stock{m2, lwm2}, rest, s)(ok))

# a right table with the contents of the versions of a line is right
def Known.warm_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {RContents.Known.ok(RContents.Known.warm(kn, s, c), s) == True{}: Bool}:
  ok => Known.warm_go_ok(
    RContents.Versions.count(RKnown.Known.versions(kn, s, c)),
    0n,
    RKnown.Known.sync(kn, RFacts.Facts.fuel(s)),
    s,
    c
  )(Known.sync_ok(kn, s)(ok))

# Known.grow_ok, once it is known whether the table holds the content before
def Known.grow_if_ok(
  near: Bool,
  +a: Nat,
  +b: Nat,
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {RContents.Known.ok(RContents.Known.grow.if(near, a, b, kn, s, c), s) == True{}: Bool}:
  match near:
    case True{}:
      Known.warm_go_ok(Nat.sub(b, a), a, kn, s, c)
    case False{}:
      ok => Known.warm_go_ok(
        b,
        0n,
        RKnown.Known.sync(kn, RFacts.Facts.fuel(s)),
        s,
        c
      )(Known.sync_ok(kn, s)(ok))

# a right table with the contents of the new versions of a line is right
def Known.grow_ok(
  +old: RKnown.Known(),
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {RContents.Known.ok(RContents.Known.grow(old, kn, s, c), s) == True{}: Bool}:
  Known.grow_if_ok(
    Maybe.is_some(&2, Nat, RKnown.Known.depth(kn, c, Nat.sub(RContents.Known.tally(old, c), 1n))),
    RContents.Known.tally(old, c),
    RContents.Known.tally(kn, c),
    kn,
    s,
    c
  )

# a right table changes no read of a resource
def Content.read_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +k: Nat,
  +p: String
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RContents.Content.read(
    kn,
    s,
    c,
    k,
    p
  )
    == RContents.Content.read(RKnown.Known.none(), s, c, k, p): Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  ok => Equal.cong(
    Maybe<&2, RFiles.Files()>,
    Maybe<&2, Maybe<&2, List<&2, U32>>>,
    m => RContents.Content.get(m, p),
    RContents.Content.of(kn, s, c, k),
    RContents.Content.of(RKnown.Known.none(), s, c, k),
    Content.of_ok(kn, s, c, k)(ok)
  )

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof does not run
# the clashes of a merge read through a right table, from the paths that
# the hint gives, are the clashes read from every path
def Hint.clashes(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +j: Nat,
  +e: Types.Entry
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RAnswers.Clashes.quick(
    RContents.Merge.hint(
      RKnown.Known.find(kn, Spec.Point.line(RContents.Entry.taken(c, Some{e}))),
      RContents.Entry.taken(c, Some{e}),
      RContents.Entry.based(c, Some{e})
    ),
    Bool.and(
      RContents.Request.is_merge(RAnswers.Entry.request(e)),
      RContents.Merge.fits(RKnown.Known.none(), s, c, j, e)
    ),
    RContents.Content.of(
      RKnown.Known.none(),
      s,
      Spec.Point.line(RContents.Entry.based(c, Some{e})),
      Spec.Point.n(RContents.Entry.based(c, Some{e}))
    ),
    RContents.Content.of(RKnown.Known.none(), s, c, j),
    RContents.Content.of(
      RKnown.Known.none(),
      s,
      Spec.Point.line(RContents.Entry.taken(c, Some{e})),
      Spec.Point.n(RContents.Entry.taken(c, Some{e}))
    )
  )
    == RAnswers.Clashes.at(
      Bool.and(
        RContents.Request.is_merge(RAnswers.Entry.request(e)),
        RContents.Merge.fits(RKnown.Known.none(), s, c, j, e)
      ),
      RContents.Content.of(
        RKnown.Known.none(),
        s,
        Spec.Point.line(RContents.Entry.based(c, Some{e})),
        Spec.Point.n(RContents.Entry.based(c, Some{e}))
      ),
      RContents.Content.of(RKnown.Known.none(), s, c, j),
      RContents.Content.of(
        RKnown.Known.none(),
        s,
        Spec.Point.line(RContents.Entry.taken(c, Some{e})),
        Spec.Point.n(RContents.Entry.taken(c, Some{e}))
      )
    ): Maybe<&2, List<&2, String>>
}:
  ok => Merges.Few.clashes_at(
    RContents.Merge.hint(
      RKnown.Known.find(kn, Spec.Point.line(RContents.Entry.taken(c, Some{e}))),
      RContents.Entry.taken(c, Some{e}),
      RContents.Entry.based(c, Some{e})
    ),
    Bool.and(
      RContents.Request.is_merge(RAnswers.Entry.request(e)),
      RContents.Merge.fits(RKnown.Known.none(), s, c, j, e)
    ),
    RContents.Content.of(
      RKnown.Known.none(),
      s,
      Spec.Point.line(RContents.Entry.based(c, Some{e})),
      Spec.Point.n(RContents.Entry.based(c, Some{e}))
    ),
    RContents.Content.of(RKnown.Known.none(), s, c, j),
    RContents.Content.of(
      RKnown.Known.none(),
      s,
      Spec.Point.line(RContents.Entry.taken(c, Some{e})),
      Spec.Point.n(RContents.Entry.taken(c, Some{e}))
    )
  )(
    Contents.Content.at_sound(
      RFacts.Facts.fuel(s),
      s,
      Spec.Point.line(RContents.Entry.based(c, Some{e})),
      Spec.Point.n(RContents.Entry.based(c, Some{e}))
    )
  )(
    ws => t => b => eh => et => eb => Hint.ok(
      kn,
      s,
      RFacts.Facts.fuel(s),
      RContents.Entry.taken(c, Some{e}),
      RContents.Entry.based(c, Some{e}),
      ws,
      t,
      b
    )(ok)(eh)(et)(eb)
  )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# a right table changes no clash
def Clashes.of_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  k: Nat,
  +e: Types.Entry
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RAnswers.Clashes.of(
    kn,
    s,
    c,
    k,
    e
  )
    == RAnswers.Clashes.of(RKnown.Known.none(), s, c, k, e): Maybe<&2, List<&2, String>>
}:
  match k:
    case 0n:
      ok => {==}
    case 1n+(+j):
      +ok => (
        %Hint.clashes(kn, s, c, j, e)(ok): {RAnswers.Clashes.of(kn, s, c, 1n+j, e) == _: Maybe<&2, List<&2, String>>}
        %Merge.fits_ok(kn, s, c, j, e)(ok): {RAnswers.Clashes.of(kn, s, c, 1n+j, e) == RAnswers.Clashes.quick(RContents.Merge.hint(RKnown.Known.find(kn, Spec.Point.line(RContents.Entry.taken(c, Some{e}))), RContents.Entry.taken(c, Some{e}), RContents.Entry.based(c, Some{e})), Bool.and(RContents.Request.is_merge(RAnswers.Entry.request(e)), _), RContents.Content.of(RKnown.Known.none(), s, Spec.Point.line(RContents.Entry.based(c, Some{e})), Spec.Point.n(RContents.Entry.based(c, Some{e}))), RContents.Content.of(RKnown.Known.none(), s, c, j), RContents.Content.of(RKnown.Known.none(), s, Spec.Point.line(RContents.Entry.taken(c, Some{e})), Spec.Point.n(RContents.Entry.taken(c, Some{e})))): Maybe<&2, List<&2, String>>}
        %Content.of_ok(kn, s, Spec.Point.line(RContents.Entry.based(c, Some{e})), Spec.Point.n(RContents.Entry.based(c, Some{e})))(ok): {RAnswers.Clashes.of(kn, s, c, 1n+j, e) == RAnswers.Clashes.quick(RContents.Merge.hint(RKnown.Known.find(kn, Spec.Point.line(RContents.Entry.taken(c, Some{e}))), RContents.Entry.taken(c, Some{e}), RContents.Entry.based(c, Some{e})), Bool.and(RContents.Request.is_merge(RAnswers.Entry.request(e)), RContents.Merge.fits(kn, s, c, j, e)), _, RContents.Content.of(RKnown.Known.none(), s, c, j), RContents.Content.of(RKnown.Known.none(), s, Spec.Point.line(RContents.Entry.taken(c, Some{e})), Spec.Point.n(RContents.Entry.taken(c, Some{e})))): Maybe<&2, List<&2, String>>}
        %Content.of_ok(kn, s, c, j)(ok): {RAnswers.Clashes.of(kn, s, c, 1n+j, e) == RAnswers.Clashes.quick(RContents.Merge.hint(RKnown.Known.find(kn, Spec.Point.line(RContents.Entry.taken(c, Some{e}))), RContents.Entry.taken(c, Some{e}), RContents.Entry.based(c, Some{e})), Bool.and(RContents.Request.is_merge(RAnswers.Entry.request(e)), RContents.Merge.fits(kn, s, c, j, e)), RContents.Content.of(kn, s, Spec.Point.line(RContents.Entry.based(c, Some{e})), Spec.Point.n(RContents.Entry.based(c, Some{e}))), _, RContents.Content.of(RKnown.Known.none(), s, Spec.Point.line(RContents.Entry.taken(c, Some{e})), Spec.Point.n(RContents.Entry.taken(c, Some{e})))): Maybe<&2, List<&2, String>>}
        %Content.of_ok(kn, s, Spec.Point.line(RContents.Entry.taken(c, Some{e})), Spec.Point.n(RContents.Entry.taken(c, Some{e})))(ok): {RAnswers.Clashes.of(kn, s, c, 1n+j, e) == RAnswers.Clashes.quick(RContents.Merge.hint(RKnown.Known.find(kn, Spec.Point.line(RContents.Entry.taken(c, Some{e}))), RContents.Entry.taken(c, Some{e}), RContents.Entry.based(c, Some{e})), Bool.and(RContents.Request.is_merge(RAnswers.Entry.request(e)), RContents.Merge.fits(kn, s, c, j, e)), RContents.Content.of(kn, s, Spec.Point.line(RContents.Entry.based(c, Some{e})), Spec.Point.n(RContents.Entry.based(c, Some{e}))), RContents.Content.of(kn, s, c, j), _): Maybe<&2, List<&2, String>>}
        {==})

# a right table changes no base of a merge
def Base.of_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  k: Nat,
  +e: Types.Entry
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RAnswers.Base.of(
    kn,
    s,
    c,
    k,
    e
  )
    == RAnswers.Base.of(RKnown.Known.none(), s, c, k, e): Maybe<&2, Spec.Point>
}:
  match k:
    case 0n:
      ok => {==}
    case 1n+(+j):
      ok => Equal.cong(
        Bool,
        Maybe<&2, Spec.Point>,
        b => Shared.Maybe.when(Spec.Point, b, u => RContents.Entry.base(e)),
        RContents.Merge.fits(kn, s, c, j, e),
        RContents.Merge.fits(RKnown.Known.none(), s, c, j, e),
        Merge.fits_ok(kn, s, c, j, e)(ok)
      )

# a right table changes no status
def Status.of_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +vs: List<&2, Types.Entry>,
  +k: Nat,
  +e: Types.Entry
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RAnswers.Status.of(
    kn,
    s,
    c,
    vs,
    k,
    e
  )
    == RAnswers.Status.of(RKnown.Known.none(), s, c, vs, k, e): Spec.Status
}:
  ok => Equal.cong(
    Maybe<&2, List<&2, String>>,
    Spec.Status,
    cs => RAnswers.Status.by(vs, k, RLines.Entry.id(e), RAnswers.Entry.request(e), cs),
    RAnswers.Clashes.of(kn, s, c, k, e),
    RAnswers.Clashes.of(RKnown.Known.none(), s, c, k, e),
    Clashes.of_ok(kn, s, c, k, e)(ok)
  )

# a right table changes no versions before a version
def Line.before_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +j: Nat
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RAnswers.Line.before(
    kn,
    s,
    c,
    j
  )
    == RAnswers.Line.before(RKnown.Known.none(), s, c, j): Maybe<&2, List<&2, Types.Entry>>
}:
  ok => Equal.cong(
    Maybe<&2, List<&2, Types.Entry>>,
    Maybe<&2, List<&2, Types.Entry>>,
    m => RAnswers.Line.before.of(j, m),
    RKnown.Known.versions(kn, s, c),
    RLines.Line.versions(s, c),
    Known.versions_ok(kn, s, c)(ok)
  )

# a right table changes no rule after the versions m
def Rule.for.of_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  m: Maybe<&2, List<&2, Types.Entry>>
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RAnswers.Rule.for.of(
    kn,
    s,
    c,
    m
  )
    == RAnswers.Rule.for.of(RKnown.Known.none(), s, c, m): Maybe<&2, RLines.Rule>
}:
  match m:
    case None{}:
      ok => {==}
    case Some{+vs}:
      ok => Known.rule_ok(kn, s, c, vs)(ok)

# a right table changes no rule of a version
def Rule.for_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  k: Nat
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RAnswers.Rule.for(
    kn,
    s,
    c,
    k
  )
    == RAnswers.Rule.for(RKnown.Known.none(), s, c, k): Maybe<&2, RLines.Rule>
}:
  match k:
    case 0n:
      ok => {==}
    case 1n+(+j):
      +ok => (
        %Line.before_ok(kn, s, c, j)(ok): {RAnswers.Rule.for(kn, s, c, 1n+j) == RAnswers.Rule.for.of(RKnown.Known.none(), s, c, _): Maybe<&2, RLines.Rule>}
        Rule.for.of_ok(kn, s, c, RAnswers.Line.before(kn, s, c, j))(ok))

# a right table changes no era of a version
def Era.for_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  k: Nat
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RAnswers.Era.for(kn, s, c, k) == RAnswers.Era.for(RKnown.Known.none(), s, c, k): Maybe<&2, Nat>
}:
  match k:
    case 0n:
      ok => {==}
    case 1n+(+j):
      ok => Equal.cong(
        Maybe<&2, List<&2, Types.Entry>>,
        Maybe<&2, Nat>,
        m => Maybe.map(&2, List<&2, Types.Entry>, Nat, vs => RLines.Line.era(c, vs), m),
        RAnswers.Line.before(kn, s, c, j),
        RAnswers.Line.before(RKnown.Known.none(), s, c, j),
        Line.before_ok(kn, s, c, j)(ok)
      )

# a right table changes no read of the versions of a store
def Store.read_ok(
  -A: Data,
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +h: Hashes.Hash,
  +m: Nat,
  -f: List<&2, Types.Entry> -> Maybe<&2, A>
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RAnswers.Store.read(
    A,
    kn,
    s,
    h,
    m,
    f
  )
    == RAnswers.Store.read(A, RKnown.Known.none(), s, h, m, f): Maybe<&2, A>
}:
  ok => (
    %Known.store_ok(kn, s, h)(ok): {RAnswers.Store.read(A, kn, s, h, m, f) == RAnswers.Store.read.of(A, m, f, _): Maybe<&2, A>}
    {==})

# a right table changes no entry that is found by its id
def Line.find_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +i: Ledgers.Id
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RAnswers.Line.find(
    kn,
    s,
    c,
    i
  )
    == RAnswers.Line.find(RKnown.Known.none(), s, c, i): Maybe<&2, RKnown.Found>
}:
  +ok => Lists.Maybe.by(
    RKnown.Ids,
    x => {
      RAnswers.Line.find.by(
        x,
        kn,
        s,
        c,
        i
      )
        == RAnswers.Line.find(RKnown.Known.none(), s, c, i): Maybe<&2, RKnown.Found>
    },
    RKnown.Known.ids(kn, c),
    en => Equal.cong(
      Maybe<&2, List<&2, Types.Entry>>,
      Maybe<&2, RKnown.Found>,
      m => RAnswers.Line.find.of(i, m),
      RKnown.Known.versions(kn, s, c),
      RLines.Line.versions(s, c),
      Known.versions_ok(kn, s, c)(ok)
    ),
    +y => ey => Made.case(
      {
        RKnown.Ids.find(
          y,
          i
        )
          == RAnswers.Line.find(RKnown.Known.none(), s, c, i): Maybe<&2, RKnown.Found>
      },
      kn,
      s,
      c,
      y,
      ok,
      ey,
      +st => est => eq => (
        %Equal.sym(Maybe<&2, RLines.State>, RLines.Line.state(s, c), Some{st}, est): {RKnown.Ids.find(y, i) == RAnswers.Line.find.of(i, Maybe.map(&2, RLines.State, List<&2, Types.Entry>, RLines.State.versions, _)): Maybe<&2, RKnown.Found>}
        %Equal.sym(RKnown.Ids, y, RKnown.Ids.of(RLines.State.versions(st)), eq): {RKnown.Ids.find(_, i) == RAnswers.Versions.find(RLines.State.versions(st), i): Maybe<&2, RKnown.Found>}
        Ids.of_find(RLines.State.versions(st), i))
    )
  )

# a right table changes no count of the versions of a line
def Reply.count_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RAnswers.Reply.count.by(
    RKnown.Known.ids(kn, c),
    kn,
    s,
    c
  )
    == RAnswers.Reply.count(RLines.Line.versions(s, c)): Maybe<&2, Spec.Reply>
}:
  +ok => Lists.Maybe.by(
    RKnown.Ids,
    x => {
      RAnswers.Reply.count.by(
        x,
        kn,
        s,
        c
      )
        == RAnswers.Reply.count(RLines.Line.versions(s, c)): Maybe<&2, Spec.Reply>
    },
    RKnown.Known.ids(kn, c),
    en => (
      %Known.versions_ok(kn, s, c)(ok): {RAnswers.Reply.count(RKnown.Known.versions(kn, s, c)) == RAnswers.Reply.count(_): Maybe<&2, Spec.Reply>}
      {==}),
    +y => ey => Made.case(
      {
        Some{
          Spec.Reply.Number{RKnown.Ids.count(y)}
        }
          == RAnswers.Reply.count(RLines.Line.versions(s, c)): Maybe<&2, Spec.Reply>
      },
      kn,
      s,
      c,
      y,
      ok,
      ey,
      +st => est => eq => (
        %Equal.sym(Maybe<&2, RLines.State>, RLines.Line.state(s, c), Some{st}, est): {Some{Spec.Reply.Number{RKnown.Ids.count(y)}} == RAnswers.Reply.count(Maybe.map(&2, RLines.State, List<&2, Types.Entry>, RLines.State.versions, _)): Maybe<&2, Spec.Reply>}
        %Equal.sym(RKnown.Ids, y, RKnown.Ids.of(RLines.State.versions(st)), eq): {Some{Spec.Reply.Number{RKnown.Ids.count(_)}} == Some{Spec.Reply.Number{List.length(&2, Types.Entry, RLines.State.versions(st))}}: Maybe<&2, Spec.Reply>}
        %Equal.sym(Nat, RKnown.Ids.count(RKnown.Ids.of(RLines.State.versions(st))), List.length(&2, Types.Entry, RLines.State.versions(st)), Ids.of_count(RLines.State.versions(st))): {Some{Spec.Reply.Number{_}} == Some{Spec.Reply.Number{List.length(&2, Types.Entry, RLines.State.versions(st))}}: Maybe<&2, Spec.Reply>}
        {==})
    )
  )

# a right table changes no reply with a status
def Reply.status_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  v: Maybe<&2, List<&2, Types.Entry>>,
  m: Maybe<&2, RKnown.Found>
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RAnswers.Reply.status(
    kn,
    s,
    c,
    v,
    m
  )
    == RAnswers.Reply.status(RKnown.Known.none(), s, c, v, m): Maybe<&2, Spec.Reply>
}:
  match v m:
    case None{} None{}:
      ok => {==}
    case None{} Some{x}:
      ok => {==}
    case Some{vs} None{}:
      ok => {==}
    case Some{+vs} Some{RKnown.Found{+k, +e}}:
      ok => Equal.cong(
        Spec.Status,
        Maybe<&2, Spec.Reply>,
        x => Some{Spec.Reply.Status{x}},
        RAnswers.Status.of(kn, s, c, vs, k, e),
        RAnswers.Status.of(RKnown.Known.none(), s, c, vs, k, e),
        Status.of_ok(kn, s, c, vs, k, e)(ok)
      )

# a right table changes no clash of a found request
def Clashes.then_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  m: Maybe<&2, RKnown.Found>
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RAnswers.Found.then(
    List<&2, String>,
    m,
    k => e => RAnswers.Clashes.of(kn, s, c, k, e)
  )
    == RAnswers.Found.then(
      List<&2, String>,
      m,
      k => e => RAnswers.Clashes.of(RKnown.Known.none(), s, c, k, e)
    ): Maybe<&2, List<&2, String>>
}:
  match m:
    case None{}:
      ok => {==}
    case Some{RKnown.Found{+k, +e}}:
      ok => Clashes.of_ok(kn, s, c, k, e)(ok)

# a right table changes no base of a found merge
def Base.then_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  m: Maybe<&2, RKnown.Found>
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RAnswers.Found.then(
    Spec.Point,
    m,
    k => e => RAnswers.Base.of(kn, s, c, k, e)
  )
    == RAnswers.Found.then(
      Spec.Point,
      m,
      k => e => RAnswers.Base.of(RKnown.Known.none(), s, c, k, e)
    ): Maybe<&2, Spec.Point>
}:
  match m:
    case None{}:
      ok => {==}
    case Some{RKnown.Found{+k, +e}}:
      ok => Base.of_ok(kn, s, c, k, e)(ok)

# a right table changes no reply
def Answer.of_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  q: Spec.Question
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RAnswers.Answer.of(
    kn,
    s,
    q
  )
    == RAnswers.Answer.of(RKnown.Known.none(), s, q): Maybe<&2, Spec.Reply>
}:
  match q:
    case Spec.Question.Status{+c, +i}:
      +ok => (
        %Known.versions_ok(kn, s, c)(ok): {RAnswers.Answer.of(kn, s, Spec.Question.Status{c, i}) == RAnswers.Reply.status(RKnown.Known.none(), s, c, _, RAnswers.Line.find(RKnown.Known.none(), s, c, i)): Maybe<&2, Spec.Reply>}
        %Line.find_ok(kn, s, c, i)(ok): {RAnswers.Answer.of(kn, s, Spec.Question.Status{c, i}) == RAnswers.Reply.status(RKnown.Known.none(), s, c, RKnown.Known.versions(kn, s, c), _): Maybe<&2, Spec.Reply>}
        Reply.status_ok(kn, s, c, RKnown.Known.versions(kn, s, c), RAnswers.Line.find(kn, s, c, i))(ok))
    case Spec.Question.Request{+c, +i}:
      ok => (
        %Line.find_ok(kn, s, c, i)(ok): {RAnswers.Answer.of(kn, s, Spec.Question.Request{c, i}) == RAnswers.Reply.ask(_): Maybe<&2, Spec.Reply>}
        {==})
    case Spec.Question.Version{+c, +k}:
      ok => (
        %Known.at_ok(kn, s, c, k)(ok): {RAnswers.Answer.of(kn, s, Spec.Question.Version{c, k}) == RAnswers.Reply.id(_): Maybe<&2, Spec.Reply>}
        {==})
    case Spec.Question.Content{+c, +k}:
      ok => (
        %Content.of_ok(kn, s, c, k)(ok): {RAnswers.Answer.of(kn, s, Spec.Question.Content{c, k}) == RAnswers.Reply.hash(_): Maybe<&2, Spec.Reply>}
        {==})
    case Spec.Question.Group{+c, +k}:
      ok => (
        %Rule.for_ok(kn, s, c, k)(ok): {RAnswers.Answer.of(kn, s, Spec.Question.Group{c, k}) == Maybe.bind(&2, RLines.Rule, Spec.Reply, _, RAnswers.Rule.group): Maybe<&2, Spec.Reply>}
        {==})
    case Spec.Question.Owners{+c, +k}:
      +ok => (
        %Known.at_ok(kn, s, c, k)(ok): {RAnswers.Answer.of(kn, s, Spec.Question.Owners{c, k}) == RAnswers.Owners.of(s, c, _, RAnswers.Rule.for(RKnown.Known.none(), s, c, k)): Maybe<&2, Spec.Reply>}
        %Rule.for_ok(kn, s, c, k)(ok): {RAnswers.Answer.of(kn, s, Spec.Question.Owners{c, k}) == RAnswers.Owners.of(s, c, RKnown.Known.at(kn, s, c, k), _): Maybe<&2, Spec.Reply>}
        {==})
    case Spec.Question.Members{+h, +g, +m}:
      ok => (
        %Store.read_ok(List<&2, String>, kn, s, h, m, R => Groups.Groups.members(R, h, g, m))(ok): {RAnswers.Answer.of(kn, s, Spec.Question.Members{h, g, m}) == RAnswers.Reply.names(_): Maybe<&2, Spec.Reply>}
        {==})
    case Spec.Question.Nodes{+h, +g, +m}:
      ok => (
        %Store.read_ok(List<&2, String>, kn, s, h, m, R => Groups.Groups.nodes(R, h, g, m))(ok): {RAnswers.Answer.of(kn, s, Spec.Question.Nodes{h, g, m}) == RAnswers.Reply.names(_): Maybe<&2, Spec.Reply>}
        {==})
    case Spec.Question.IsGroup{+h, +g, +m}:
      ok => (
        %Store.read_ok(Bool, kn, s, h, m, R => Groups.Groups.is_group(R, h, g, m))(ok): {RAnswers.Answer.of(kn, s, Spec.Question.IsGroup{h, g, m}) == RAnswers.Reply.yes(_): Maybe<&2, Spec.Reply>}
        {==})
    case Spec.Question.Mark{+c, +m}:
      ok => (
        %Known.versions_ok(kn, s, c)(ok): {RAnswers.Answer.of(kn, s, Spec.Question.Mark{c, m}) == RAnswers.Reply.number(RAnswers.Mark.of(m, _)): Maybe<&2, Spec.Reply>}
        {==})
    case Spec.Question.Count{+c}:
      ok => Reply.count_ok(kn, s, c)(ok)
    case Spec.Question.Clashes{+c, +i}:
      +ok => (
        %Line.find_ok(kn, s, c, i)(ok): {RAnswers.Answer.of(kn, s, Spec.Question.Clashes{c, i}) == RAnswers.Reply.names(RAnswers.Found.then(List<&2, String>, _, k => e => RAnswers.Clashes.of(RKnown.Known.none(), s, c, k, e))): Maybe<&2, Spec.Reply>}
        %Clashes.then_ok(kn, s, c, RAnswers.Line.find(kn, s, c, i))(ok): {RAnswers.Answer.of(kn, s, Spec.Question.Clashes{c, i}) == RAnswers.Reply.names(_): Maybe<&2, Spec.Reply>}
        {==})
    case Spec.Question.Affects{+c, +a, +b, +us, +bs}:
      +ok => (
        %Content.of_ok(kn, s, c, a)(ok): {RAnswers.Answer.of(kn, s, Spec.Question.Affects{c, a, b, us, bs}) == RAnswers.Affects.of(_, RContents.Content.of(RKnown.Known.none(), s, c, b), us, bs): Maybe<&2, Spec.Reply>}
        %Content.of_ok(kn, s, c, b)(ok): {RAnswers.Answer.of(kn, s, Spec.Question.Affects{c, a, b, us, bs}) == RAnswers.Affects.of(RContents.Content.of(kn, s, c, a), _, us, bs): Maybe<&2, Spec.Reply>}
        {==})
    case Spec.Question.Parents{+c, +k}:
      ok => (
        %Known.at_ok(kn, s, c, k)(ok): {RAnswers.Answer.of(kn, s, Spec.Question.Parents{c, k}) == RAnswers.Reply.parents(c, k, _): Maybe<&2, Spec.Reply>}
        {==})
    case Spec.Question.Base{+c, +i}:
      +ok => (
        %Line.find_ok(kn, s, c, i)(ok): {RAnswers.Answer.of(kn, s, Spec.Question.Base{c, i}) == RAnswers.Reply.point(RAnswers.Found.then(Spec.Point, _, k => e => RAnswers.Base.of(RKnown.Known.none(), s, c, k, e))): Maybe<&2, Spec.Reply>}
        %Base.then_ok(kn, s, c, RAnswers.Line.find(kn, s, c, i))(ok): {RAnswers.Answer.of(kn, s, Spec.Question.Base{c, i}) == RAnswers.Reply.point(_): Maybe<&2, Spec.Reply>}
        {==})
    case Spec.Question.Owner{+c, +k}:
      ok => (
        %Rule.for_ok(kn, s, c, k)(ok): {RAnswers.Answer.of(kn, s, Spec.Question.Owner{c, k}) == Maybe.bind(&2, RLines.Rule, Spec.Reply, _, RAnswers.Rule.owner): Maybe<&2, Spec.Reply>}
        {==})
    case Spec.Question.Era{+c, +k}:
      ok => (
        %Era.for_ok(kn, s, c, k)(ok): {RAnswers.Answer.of(kn, s, Spec.Question.Era{c, k}) == RAnswers.Reply.number(_): Maybe<&2, Spec.Reply>}
        {==})

# a right table changes no view of the newest version
def View.newest_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +b: Ledgers.Line,
  +p: String,
  m: Maybe<&2, List<&2, Types.Entry>>
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RAnswers.View.newest(
    kn,
    s,
    b,
    p,
    m
  )
    == RAnswers.View.newest(RKnown.Known.none(), s, b, p, m): Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  match m:
    case None{}:
      ok => {==}
    case Some{+vs}:
      ok => Content.read_ok(kn, s, b, Nat.sub(List.length(&2, Types.Entry, vs), 1n), p)(ok)

# a right table changes no view after the write m
def View.slow_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +b: Ledgers.Line,
  +p: String,
  m: Maybe<&2, Types.Ask>
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RAnswers.View.slow(
    kn,
    s,
    b,
    p,
    m
  )
    == RAnswers.View.slow(RKnown.Known.none(), s, b, p, m): Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  match m:
    case None{}:
      +ok => (
        %Known.versions_ok(kn, s, b)(ok): {RAnswers.View.slow(kn, s, b, p, None{}) == RAnswers.View.newest(RKnown.Known.none(), s, b, p, _): Maybe<&2, Maybe<&2, List<&2, U32>>>}
        View.newest_ok(kn, s, b, p, RKnown.Known.versions(kn, s, b))(ok))
    case Some{+a}:
      +ok => (
        %Known.versions_ok(kn, s, b)(ok): {RAnswers.View.slow(kn, s, b, p, Some{a}) == Shared.Bool.when(Maybe<&2, Maybe<&2, List<&2, U32>>>, RAnswers.View.decided(a, _), u => RAnswers.View.newest(RKnown.Known.none(), s, b, p, _), u => Some{RAnswers.Request.words(RLines.Ask.request(a))}): Maybe<&2, Maybe<&2, List<&2, U32>>>}
        %View.newest_ok(kn, s, b, p, RKnown.Known.versions(kn, s, b))(ok): {RAnswers.View.slow(kn, s, b, p, Some{a}) == Shared.Bool.when(Maybe<&2, Maybe<&2, List<&2, U32>>>, RAnswers.View.decided(a, RKnown.Known.versions(kn, s, b)), u => _, u => Some{RAnswers.Request.words(RLines.Ask.request(a))}): Maybe<&2, Maybe<&2, List<&2, U32>>>}
        {==})

# the view after the write m, read from the versions by id of a state of the
# branch through a right table, is the view that the facts give
def View.quick_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +b: Ledgers.Line,
  +p: String,
  m: Maybe<&2, Types.Ask>,
  +st: RLines.State
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RLines.Line.state(s, b) == Some{st}: Maybe<&2, RLines.State>
} -> {
  RAnswers.View.quick(
    RKnown.Ids.of(RLines.State.versions(st)),
    kn,
    s,
    b,
    p,
    m
  )
    == RAnswers.View.slow(RKnown.Known.none(), s, b, p, m): Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  match m:
    case None{}:
      ok => est => (
        %Equal.sym(Maybe<&2, RLines.State>, RLines.Line.state(s, b), Some{st}, est): {RAnswers.View.last(kn, s, b, p, RKnown.Ids.of(RLines.State.versions(st))) == RAnswers.View.newest(RKnown.Known.none(), s, b, p, Maybe.map(&2, RLines.State, List<&2, Types.Entry>, RLines.State.versions, _)): Maybe<&2, Maybe<&2, List<&2, U32>>>}
        %Equal.sym(Nat, RKnown.Ids.count(RKnown.Ids.of(RLines.State.versions(st))), List.length(&2, Types.Entry, RLines.State.versions(st)), Ids.of_count(RLines.State.versions(st))): {RContents.Content.read(kn, s, b, Nat.sub(_, 1n), p) == RContents.Content.read(RKnown.Known.none(), s, b, Nat.sub(List.length(&2, Types.Entry, RLines.State.versions(st)), 1n), p): Maybe<&2, Maybe<&2, List<&2, U32>>>}
        Content.read_ok(kn, s, b, Nat.sub(List.length(&2, Types.Entry, RLines.State.versions(st)), 1n), p)(ok))
    case Some{+a}:
      ok => est => (
        %Equal.sym(Maybe<&2, RLines.State>, RLines.Line.state(s, b), Some{st}, est): {RAnswers.View.quick(RKnown.Ids.of(RLines.State.versions(st)), kn, s, b, p, Some{a}) == Shared.Bool.when(Maybe<&2, Maybe<&2, List<&2, U32>>>, RAnswers.View.decided(a, Maybe.map(&2, RLines.State, List<&2, Types.Entry>, RLines.State.versions, _)), u => RAnswers.View.newest(RKnown.Known.none(), s, b, p, Maybe.map(&2, RLines.State, List<&2, Types.Entry>, RLines.State.versions, _)), u => Some{RAnswers.Request.words(RLines.Ask.request(a))}): Maybe<&2, Maybe<&2, List<&2, U32>>>}
        %Equal.sym(Bool, RKnown.Ids.made(RKnown.Ids.of(RLines.State.versions(st)), a), Shared.List.some(~Types.Entry, ~Types.Ask, ~RKnown.Entry.made_by, RLines.State.versions(st), a), Ids.of_made(RLines.State.versions(st), a)): {Shared.Bool.when(Maybe<&2, Maybe<&2, List<&2, U32>>>, _, u => RAnswers.View.last(kn, s, b, p, RKnown.Ids.of(RLines.State.versions(st))), u => Some{RAnswers.Request.words(RLines.Ask.request(a))}) == Shared.Bool.when(Maybe<&2, Maybe<&2, List<&2, U32>>>, Shared.List.some(~Types.Entry, ~Types.Ask, ~RKnown.Entry.made_by, RLines.State.versions(st), a), u => RContents.Content.read(RKnown.Known.none(), s, b, Nat.sub(List.length(&2, Types.Entry, RLines.State.versions(st)), 1n), p), u => Some{RAnswers.Request.words(RLines.Ask.request(a))}): Maybe<&2, Maybe<&2, List<&2, U32>>>}
        %Equal.sym(Nat, RKnown.Ids.count(RKnown.Ids.of(RLines.State.versions(st))), List.length(&2, Types.Entry, RLines.State.versions(st)), Ids.of_count(RLines.State.versions(st))): {Shared.Bool.when(Maybe<&2, Maybe<&2, List<&2, U32>>>, Shared.List.some(~Types.Entry, ~Types.Ask, ~RKnown.Entry.made_by, RLines.State.versions(st), a), u => RContents.Content.read(kn, s, b, Nat.sub(_, 1n), p), u => Some{RAnswers.Request.words(RLines.Ask.request(a))}) == Shared.Bool.when(Maybe<&2, Maybe<&2, List<&2, U32>>>, Shared.List.some(~Types.Entry, ~Types.Ask, ~RKnown.Entry.made_by, RLines.State.versions(st), a), u => RContents.Content.read(RKnown.Known.none(), s, b, Nat.sub(List.length(&2, Types.Entry, RLines.State.versions(st)), 1n), p), u => Some{RAnswers.Request.words(RLines.Ask.request(a))}): Maybe<&2, Maybe<&2, List<&2, U32>>>}
        %Content.read_ok(kn, s, b, Nat.sub(List.length(&2, Types.Entry, RLines.State.versions(st)), 1n), p)(ok): {Shared.Bool.when(Maybe<&2, Maybe<&2, List<&2, U32>>>, Shared.List.some(~Types.Entry, ~Types.Ask, ~RKnown.Entry.made_by, RLines.State.versions(st), a), u => RContents.Content.read(kn, s, b, Nat.sub(List.length(&2, Types.Entry, RLines.State.versions(st)), 1n), p), u => Some{RAnswers.Request.words(RLines.Ask.request(a))}) == Shared.Bool.when(Maybe<&2, Maybe<&2, List<&2, U32>>>, Shared.List.some(~Types.Entry, ~Types.Ask, ~RKnown.Entry.made_by, RLines.State.versions(st), a), u => _, u => Some{RAnswers.Request.words(RLines.Ask.request(a))}): Maybe<&2, Maybe<&2, List<&2, U32>>>}
        {==})

# a right table changes no view after the write m
def View.of_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +b: Ledgers.Line,
  +p: String,
  +m: Maybe<&2, Types.Ask>
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RAnswers.View.of(
    kn,
    s,
    b,
    p,
    m
  )
    == RAnswers.View.of(RKnown.Known.none(), s, b, p, m): Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  +ok => Lists.Maybe.by(
    RKnown.Ids,
    x => {
      RAnswers.View.of.by(
        x,
        kn,
        s,
        b,
        p,
        m
      )
        == RAnswers.View.slow(RKnown.Known.none(), s, b, p, m): Maybe<&2, Maybe<&2, List<&2, U32>>>
    },
    RKnown.Known.ids(kn, b),
    en => View.slow_ok(kn, s, b, p, m)(ok),
    +y => ey => Made.case(
      {
        RAnswers.View.quick(
          y,
          kn,
          s,
          b,
          p,
          m
        )
          == RAnswers.View.slow(
            RKnown.Known.none(),
            s,
            b,
            p,
            m
          ): Maybe<&2, Maybe<&2, List<&2, U32>>>
      },
      kn,
      s,
      b,
      y,
      ok,
      ey,
      +st => est => eq => (
        %Equal.sym(RKnown.Ids, y, RKnown.Ids.of(RLines.State.versions(st)), eq): {RAnswers.View.quick(_, kn, s, b, p, m) == RAnswers.View.slow(RKnown.Known.none(), s, b, p, m): Maybe<&2, Maybe<&2, List<&2, U32>>>}
        View.quick_ok(kn, s, b, p, m, st)(ok)(est))
    )
  )

# the newest write at a place, read from an entry that is right, is the one
# read from the facts
def View.top_fit(
  m: Maybe<&2, RKnown.Kept>,
  +s: RFacts.Plain(),
  +g: RKnown.Place
) -> {
  RContents.Shelf.fits(m, s) == True{}: Bool
} -> {
  RAnswers.View.top(
    m,
    s,
    g
  )
    == Lists.List.top(
      ~Types.Ask,
      ~RFacts.Ask.seq,
      RAnswers.Writes.of(RFacts.Facts.list(s), g)
    ): Maybe<&2, Types.Ask>
}:
  match m:
    case None{}:
      h => {==}
    case Some{RKnown.Kept{c2, st2}}:
      h => {==}
    case Some{RKnown.Stock{m2, lwm2}}:
      h => {==}
    case Some{RKnown.Ruled{c2, zu2, u2}}:
      h => {==}
    case Some{RKnown.Made{c2, y2}}:
      h => {==}
    case Some{RKnown.Open{+fs2, +pk2, +tx2, +mtx2}}:
      h => (
        %Equal.sym(Crits.Crit<Types.Ask>, tx2, RKnown.Tops.of(RFacts.Facts.list(s)), Open.fits_tops(fs2, pk2, tx2, mtx2, s)(h)): {RKnown.Tops.get(_, g) == Lists.List.top(~Types.Ask, ~RFacts.Ask.seq, RAnswers.Writes.of(RFacts.Facts.list(s), g)): Maybe<&2, Types.Ask>}
        Newest.Tops.of_get(RFacts.Facts.list(s), g))

# a table that fits changes no view
def View.at_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +w: String,
  +b: Ledgers.Line,
  +p: String
) -> {
  RContents.Known.fit(kn, s) == True{}: Bool
} -> {
  RAnswers.View.at(
    kn,
    s,
    w,
    b,
    p
  )
    == RAnswers.View.at(RKnown.Known.none(), s, w, b, p): Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  +h => (
    %View.top_fit(RKnown.Known.shelf(kn), s, RKnown.Place{w, b, p})(Fit.open(kn, s)(h)): {RAnswers.View.at(kn, s, w, b, p) == RAnswers.View.of(RKnown.Known.none(), s, b, p, _): Maybe<&2, Maybe<&2, List<&2, U32>>>}
    View.of_ok(kn, s, b, p, RAnswers.View.top(RKnown.Known.shelf(kn), s, RKnown.Place{w, b, p}))(Fit.ok(kn, s)(h)))

# A vote continues a run
# ----------------------

# 0 added to a number is the number
def Nat.add_zero(a: Nat) -> {Nat.add(a, 0n) == a: Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, n => 1n+n, Nat.add(p, 0n), p, Nat.add_zero(p))

# a sum is the sum of its terms in the other order
def Nat.add_comm(a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a): Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, Nat.add_zero(b))
    case 1n+(+p):
      %Equal.sym(
        Nat,
        Nat.add(b, 1n+p),
        1n+Nat.add(b, p),
        Shared.Nat.add_succ(b, p)
      ): {1n+Nat.add(p, b) == _: Nat}
      Equal.cong(Nat, Nat, n => 1n+n, Nat.add(p, b), Nat.add(b, p), Nat.add_comm(p, b))

# a number is below one more than its sum with another
def Nat.lt_succ_add(+a: Nat, +b: Nat) -> {Nat.is_lt(a, 1n+Nat.add(a, b)) == True{}: Bool}:
  Shared.Nat.le_lt(
    a,
    Nat.add(a, b),
    1n+Nat.add(a, b)
  )(Shared.Nat.le_add_first(a, b))(Shared.Nat.lt_succ(Nat.add(a, b)))

# a run whose next slot is not decided stays where it is
def Run.none(
  g: Nat,
  +s: Facts.Facts(),
  +r: Maybe<&2, List<&2, Types.Entry>>,
  +c: Ledgers.Line,
  +st: RLines.State
) -> {Lines.Line.run(g, s, r, c, st, None{}) == st: RLines.State}:
  match g:
    case 0n:
      {==}
    case 1n+p:
      {==}

# a run of f and g slots is a run of g slots from where a run of f slots ends
def Run.plus(
  f: Nat,
  +g: Nat,
  +s: Facts.Facts(),
  +r: Maybe<&2, List<&2, Types.Entry>>,
  +c: Ledgers.Line,
  +st: RLines.State
) -> {
  Lines.Line.run(
    Nat.add(f, g),
    s,
    r,
    c,
    st,
    Lines.Line.step(s, r, c, st)
  )
    == Lines.Line.run(
      g,
      s,
      r,
      c,
      Lines.Line.run(f, s, r, c, st, Lines.Line.step(s, r, c, st)),
      Lines.Line.step(s, r, c, Lines.Line.run(f, s, r, c, st, Lines.Line.step(s, r, c, st)))
    ): RLines.State
}:
  match f:
    case 0n:
      {==}
    case 1n+(+p):
      Lists.Maybe.by(
        RLines.State,
        m => {
          Lines.Line.run(
            1n+Nat.add(p, g),
            s,
            r,
            c,
            st,
            m
          )
            == Lines.Line.run(
              g,
              s,
              r,
              c,
              Lines.Line.run(1n+p, s, r, c, st, m),
              Lines.Line.step(s, r, c, Lines.Line.run(1n+p, s, r, c, st, m))
            ): RLines.State
        },
        Lines.Line.step(s, r, c, st),
        en => (
          %Equal.sym(Maybe<&2, RLines.State>, Lines.Line.step(s, r, c, st), None{}, en): {st == Lines.Line.run(g, s, r, c, st, _): RLines.State}
          Equal.sym(RLines.State, Lines.Line.run(g, s, r, c, st, None{}), st, Run.none(g, s, r, c, st))),
        +st2 => e2 => Run.plus(p, g, s, r, c, st2)
      )

# a run that may go past the bound of the line ends where it ends with more
# slots to go
def Run.more(
  +f: Nat,
  +g: Nat,
  +s: Facts.Facts(),
  +r: Maybe<&2, List<&2, Types.Entry>>,
  +c: Ledgers.Line,
  +st: RLines.State
) -> {
  Nat.is_lt(
    RLines.Line.bound(Facts.Facts.list(s), c),
    Nat.add(f, RLines.State.slot(st))
  )
    == True{}: Bool
} -> {
  Lines.Line.run(
    Nat.add(f, g),
    s,
    r,
    c,
    st,
    Lines.Line.step(s, r, c, st)
  )
    == Lines.Line.run(f, s, r, c, st, Lines.Line.step(s, r, c, st)): RLines.State
}:
  h => (
    %Equal.sym(RLines.State, Lines.Line.run(Nat.add(f, g), s, r, c, st, Lines.Line.step(s, r, c, st)), Lines.Line.run(g, s, r, c, Lines.Line.run(f, s, r, c, st, Lines.Line.step(s, r, c, st)), Lines.Line.step(s, r, c, Lines.Line.run(f, s, r, c, st, Lines.Line.step(s, r, c, st)))), Run.plus(f, g, s, r, c, st)): {_ == Lines.Line.run(f, s, r, c, st, Lines.Line.step(s, r, c, st)): RLines.State}
    %Equal.sym(Maybe<&2, RLines.State>, Lines.Line.step(s, r, c, Lines.Line.run(f, s, r, c, st, Lines.Line.step(s, r, c, st))), None{}, Versions.Run.stops(f, s, r, c, st)(h)): {Lines.Line.run(g, s, r, c, Lines.Line.run(f, s, r, c, st, Lines.Line.step(s, r, c, st)), _) == Lines.Line.run(f, s, r, c, st, Lines.Line.step(s, r, c, st)): RLines.State}
    Run.none(g, s, r, c, Lines.Line.run(f, s, r, c, st, Lines.Line.step(s, r, c, st))))

# two runs that may go past the bound of the line end at the same state
def Run.fuel(
  +f: Nat,
  +g: Nat,
  +s: Facts.Facts(),
  +r: Maybe<&2, List<&2, Types.Entry>>,
  +c: Ledgers.Line,
  +st: RLines.State
) -> {
  Nat.is_lt(
    RLines.Line.bound(Facts.Facts.list(s), c),
    Nat.add(f, RLines.State.slot(st))
  )
    == True{}: Bool
} -> {
  Nat.is_lt(
    RLines.Line.bound(Facts.Facts.list(s), c),
    Nat.add(g, RLines.State.slot(st))
  )
    == True{}: Bool
} -> {
  Lines.Line.run(
    f,
    s,
    r,
    c,
    st,
    Lines.Line.step(s, r, c, st)
  )
    == Lines.Line.run(g, s, r, c, st, Lines.Line.step(s, r, c, st)): RLines.State
}:
  hf => hg => Equal.trans(
    RLines.State,
    Lines.Line.run(f, s, r, c, st, Lines.Line.step(s, r, c, st)),
    Lines.Line.run(Nat.add(f, g), s, r, c, st, Lines.Line.step(s, r, c, st)),
    Lines.Line.run(g, s, r, c, st, Lines.Line.step(s, r, c, st)),
    Equal.sym(
      RLines.State,
      Lines.Line.run(Nat.add(f, g), s, r, c, st, Lines.Line.step(s, r, c, st)),
      Lines.Line.run(f, s, r, c, st, Lines.Line.step(s, r, c, st)),
      Run.more(f, g, s, r, c, st)(hf)
    ),
    (
      %Equal.sym(Nat, Nat.add(f, g), Nat.add(g, f), Nat.add_comm(f, g)): {Lines.Line.run(_, s, r, c, st, Lines.Line.step(s, r, c, st)) == Lines.Line.run(g, s, r, c, st, Lines.Line.step(s, r, c, st)): RLines.State}
      Run.more(g, f, s, r, c, st)(hg))
  )

# a vote for the slot k of the line c is no vote for a slot of c below k
def Cast.keeps(
  +name: String,
  +c: Ledgers.Line,
  +k: Nat,
  +t: Nat,
  +x: Types.Cast,
  +j: Nat
) -> {
  Nat.is_le(1n+j, k) == True{}: Bool
} -> {Moves.Delta.keeps(Moves.Delta.Vote{name, c, k, t, x}, c, j) == True{}: Bool}:
  lt => (
    %Equal.sym(Bool, Nat.is_eq(j, k), False{}, Moves.Nat.lt_ne(j, k)(lt)): {Bool.not(Bool.and(Ledgers.Line.is_eq(c, c), _)) == True{}: Bool}
    %Equal.sym(Bool, Bool.and(Ledgers.Line.is_eq(c, c), False{}), False{}, Shared.Bool.and_false_right(Ledgers.Line.is_eq(c, c))): {Bool.not(_) == True{}: Bool}
    {==})

# after a vote for the next slot of the state st, a run from st that may go
# past the bound of the line ends where the continued run ends
def Cast.stop(
  +f2: Nat,
  +name: String,
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +t: Nat,
  +x: Types.Cast,
  +r: Maybe<&2, List<&2, Types.Entry>>,
  +st: RLines.State
) -> {
  Nat.is_lt(
    RLines.Line.bound(
      Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(st), t, x}, s)),
      c
    ),
    Nat.add(f2, RLines.State.slot(st))
  )
    == True{}: Bool
} -> {
  Lines.Line.run(
    f2,
    Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(st), t, x}, s),
    r,
    c,
    st,
    Lines.Line.step(
      Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(st), t, x}, s),
      r,
      c,
      st
    )
  )
    == Lines.Line.run(
      1n+RLines.Line.bound(
        Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(st), t, x}, s)),
        c
      ),
      Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(st), t, x}, s),
      r,
      c,
      st,
      Lines.Line.step(
        Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(st), t, x}, s),
        r,
        c,
        st
      )
    ): RLines.State
}:
  hw => Run.fuel(
    f2,
    1n+RLines.Line.bound(
      Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(st), t, x}, s)),
      c
    ),
    Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(st), t, x}, s),
    r,
    c,
    st
  )(
    hw
  )(
    Nat.lt_succ_add(
      RLines.Line.bound(
        Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(st), t, x}, s)),
        c
      ),
      RLines.State.slot(st)
    )
  )

# from a state whose slot is below the slot of the vote and decided, a run
# after the vote does what a run from the state after that slot does (ih)
def Cast.go(
  f2: Nat,
  +name: String,
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +t: Nat,
  +x: Types.Cast,
  +r: Maybe<&2, List<&2, Types.Entry>>,
  +st: RLines.State,
  +st2: RLines.State,
  +xs: RLines.State,
  +e2: {Lines.Line.step(s, r, c, st) == Some{st2}: Maybe<&2, RLines.State>},
  lt: {Nat.is_le(1n+RLines.State.slot(st), RLines.State.slot(xs)) == True{}: Bool},
  ih: @f3: Nat -> {
    Nat.is_lt(RLines.State.slot(xs), Nat.add(f3, RLines.State.slot(st2))) == True{}: Bool
  } -> {
    Nat.is_lt(
      RLines.Line.bound(
        Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(xs), t, x}, s)),
        c
      ),
      Nat.add(f3, RLines.State.slot(st2))
    )
      == True{}: Bool
  } -> {
    Lines.Line.run(
      f3,
      Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(xs), t, x}, s),
      r,
      c,
      st2,
      Lines.Line.step(
        Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(xs), t, x}, s),
        r,
        c,
        st2
      )
    )
      == Lines.Line.run(
        1n+RLines.Line.bound(
          Facts.Facts.list(
            Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(xs), t, x}, s)
          ),
          c
        ),
        Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(xs), t, x}, s),
        r,
        c,
        xs,
        Lines.Line.step(
          Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(xs), t, x}, s),
          r,
          c,
          xs
        )
      ): RLines.State
  }
) -> {
  Nat.is_lt(RLines.State.slot(xs), Nat.add(f2, RLines.State.slot(st))) == True{}: Bool
} -> {
  Nat.is_lt(
    RLines.Line.bound(
      Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(xs), t, x}, s)),
      c
    ),
    Nat.add(f2, RLines.State.slot(st))
  )
    == True{}: Bool
} -> {
  Lines.Line.run(
    f2,
    Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(xs), t, x}, s),
    r,
    c,
    st,
    Lines.Line.step(
      Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(xs), t, x}, s),
      r,
      c,
      st
    )
  )
    == Lines.Line.run(
      1n+RLines.Line.bound(
        Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(xs), t, x}, s)),
        c
      ),
      Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(xs), t, x}, s),
      r,
      c,
      xs,
      Lines.Line.step(
        Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(xs), t, x}, s),
        r,
        c,
        xs
      )
    ): RLines.State
}:
  match f2:
    case 0n:
      hv => hw => Lists.Bool.clash(
        {
          Lines.Line.run(
            0n,
            Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(xs), t, x}, s),
            r,
            c,
            st,
            Lines.Line.step(
              Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(xs), t, x}, s),
              r,
              c,
              st
            )
          )
            == Lines.Line.run(
              1n+RLines.Line.bound(
                Facts.Facts.list(
                  Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(xs), t, x}, s)
                ),
                c
              ),
              Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(xs), t, x}, s),
              r,
              c,
              xs,
              Lines.Line.step(
                Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(xs), t, x}, s),
                r,
                c,
                xs
              )
            ): RLines.State
        },
        Nat.is_lt(RLines.State.slot(xs), RLines.State.slot(st)),
        Shared.Nat.le_nlt(
          RLines.State.slot(st),
          RLines.State.slot(xs)
        )(
          Shared.Nat.le_trans(
            RLines.State.slot(st),
            1n+RLines.State.slot(st),
            RLines.State.slot(xs)
          )(
            Shared.Nat.le_succ(
              RLines.State.slot(st),
              RLines.State.slot(st)
            )(Shared.Nat.le_refl(RLines.State.slot(st)))
          )(lt)
        ),
        hv
      )
    case 1n+(+p):
      hv => hw => (
        %Equal.sym(Maybe<&2, RLines.State>, Lines.Line.step(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(xs), t, x}, s), r, c, st), Some{st2}, Equal.trans(Maybe<&2, RLines.State>, Lines.Line.step(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(xs), t, x}, s), r, c, st), Lines.Line.step(s, r, c, st), Some{st2}, Moves.Step.kept.at(Moves.Delta.Vote{name, c, RLines.State.slot(xs), t, x}, s, c, st, RLines.Line.rule(r, c, RLines.State.versions(st)))(Cast.keeps(name, c, RLines.State.slot(xs), t, x, RLines.State.slot(st))(lt)), e2)): {Lines.Line.run(1n+p, Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(xs), t, x}, s), r, c, st, _) == Lines.Line.run(1n+RLines.Line.bound(Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(xs), t, x}, s)), c), Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(xs), t, x}, s), r, c, xs, Lines.Line.step(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(xs), t, x}, s), r, c, xs)): RLines.State}
        ih(p)(
        %Equal.sym(Nat, RLines.State.slot(st2), 1n+RLines.State.slot(st), Moves.Next.slot(st, st2, Moves.Step.next(s, r, c, st, st2)(e2))): {Nat.is_lt(RLines.State.slot(xs), Nat.add(p, _)) == True{}: Bool}
        %Equal.sym(Nat, Nat.add(p, 1n+RLines.State.slot(st)), 1n+Nat.add(p, RLines.State.slot(st)), Shared.Nat.add_succ(p, RLines.State.slot(st))): {Nat.is_lt(RLines.State.slot(xs), _) == True{}: Bool}
        hv)(
        %Equal.sym(Nat, RLines.State.slot(st2), 1n+RLines.State.slot(st), Moves.Next.slot(st, st2, Moves.Step.next(s, r, c, st, st2)(e2))): {Nat.is_lt(RLines.Line.bound(Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(xs), t, x}, s)), c), Nat.add(p, _)) == True{}: Bool}
        %Equal.sym(Nat, Nat.add(p, 1n+RLines.State.slot(st)), 1n+Nat.add(p, RLines.State.slot(st)), Shared.Nat.add_succ(p, RLines.State.slot(st))): {Nat.is_lt(RLines.Line.bound(Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(xs), t, x}, s)), c), _) == True{}: Bool}
        hw))

# when a run of f slots before the vote ends at a state, and the vote is for
# the next slot of that state, a run of f2 slots after the vote, that may go
# past that slot and past the bound of the line, ends where the continued
# run from that state ends
def Cast.run(
  f: Nat,
  +f2: Nat,
  +name: String,
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +t: Nat,
  +x: Types.Cast,
  +r: Maybe<&2, List<&2, Types.Entry>>,
  +st: RLines.State
) -> {
  Nat.is_lt(
    RLines.State.slot(Lines.Line.run(f, s, r, c, st, Lines.Line.step(s, r, c, st))),
    Nat.add(f2, RLines.State.slot(st))
  )
    == True{}: Bool
} -> {
  Nat.is_lt(
    RLines.Line.bound(
      Facts.Facts.list(
        Moves.Delta.to(
          Moves.Delta.Vote{
            name,
            c,
            RLines.State.slot(Lines.Line.run(f, s, r, c, st, Lines.Line.step(s, r, c, st))),
            t,
            x
          },
          s
        )
      ),
      c
    ),
    Nat.add(f2, RLines.State.slot(st))
  )
    == True{}: Bool
} -> {
  Lines.Line.run(
    f2,
    Moves.Delta.to(
      Moves.Delta.Vote{
        name,
        c,
        RLines.State.slot(Lines.Line.run(f, s, r, c, st, Lines.Line.step(s, r, c, st))),
        t,
        x
      },
      s
    ),
    r,
    c,
    st,
    Lines.Line.step(
      Moves.Delta.to(
        Moves.Delta.Vote{
          name,
          c,
          RLines.State.slot(Lines.Line.run(f, s, r, c, st, Lines.Line.step(s, r, c, st))),
          t,
          x
        },
        s
      ),
      r,
      c,
      st
    )
  )
    == Lines.Line.run(
      1n+RLines.Line.bound(
        Facts.Facts.list(
          Moves.Delta.to(
            Moves.Delta.Vote{
              name,
              c,
              RLines.State.slot(Lines.Line.run(f, s, r, c, st, Lines.Line.step(s, r, c, st))),
              t,
              x
            },
            s
          )
        ),
        c
      ),
      Moves.Delta.to(
        Moves.Delta.Vote{
          name,
          c,
          RLines.State.slot(Lines.Line.run(f, s, r, c, st, Lines.Line.step(s, r, c, st))),
          t,
          x
        },
        s
      ),
      r,
      c,
      Lines.Line.run(f, s, r, c, st, Lines.Line.step(s, r, c, st)),
      Lines.Line.step(
        Moves.Delta.to(
          Moves.Delta.Vote{
            name,
            c,
            RLines.State.slot(Lines.Line.run(f, s, r, c, st, Lines.Line.step(s, r, c, st))),
            t,
            x
          },
          s
        ),
        r,
        c,
        Lines.Line.run(f, s, r, c, st, Lines.Line.step(s, r, c, st))
      )
    ): RLines.State
}:
  match f:
    case 0n:
      hv => hw => Cast.stop(f2, name, s, c, t, x, r, st)(hw)
    case 1n+(+p):
      Lists.Maybe.by(
        RLines.State,
        m => {
          Nat.is_lt(
            RLines.State.slot(Lines.Line.run(1n+p, s, r, c, st, m)),
            Nat.add(f2, RLines.State.slot(st))
          )
            == True{}: Bool
        } -> {
          Nat.is_lt(
            RLines.Line.bound(
              Facts.Facts.list(
                Moves.Delta.to(
                  Moves.Delta.Vote{
                    name,
                    c,
                    RLines.State.slot(Lines.Line.run(1n+p, s, r, c, st, m)),
                    t,
                    x
                  },
                  s
                )
              ),
              c
            ),
            Nat.add(f2, RLines.State.slot(st))
          )
            == True{}: Bool
        } -> {
          Lines.Line.run(
            f2,
            Moves.Delta.to(
              Moves.Delta.Vote{
                name,
                c,
                RLines.State.slot(Lines.Line.run(1n+p, s, r, c, st, m)),
                t,
                x
              },
              s
            ),
            r,
            c,
            st,
            Lines.Line.step(
              Moves.Delta.to(
                Moves.Delta.Vote{
                  name,
                  c,
                  RLines.State.slot(Lines.Line.run(1n+p, s, r, c, st, m)),
                  t,
                  x
                },
                s
              ),
              r,
              c,
              st
            )
          )
            == Lines.Line.run(
              1n+RLines.Line.bound(
                Facts.Facts.list(
                  Moves.Delta.to(
                    Moves.Delta.Vote{
                      name,
                      c,
                      RLines.State.slot(Lines.Line.run(1n+p, s, r, c, st, m)),
                      t,
                      x
                    },
                    s
                  )
                ),
                c
              ),
              Moves.Delta.to(
                Moves.Delta.Vote{
                  name,
                  c,
                  RLines.State.slot(Lines.Line.run(1n+p, s, r, c, st, m)),
                  t,
                  x
                },
                s
              ),
              r,
              c,
              Lines.Line.run(1n+p, s, r, c, st, m),
              Lines.Line.step(
                Moves.Delta.to(
                  Moves.Delta.Vote{
                    name,
                    c,
                    RLines.State.slot(Lines.Line.run(1n+p, s, r, c, st, m)),
                    t,
                    x
                  },
                  s
                ),
                r,
                c,
                Lines.Line.run(1n+p, s, r, c, st, m)
              )
            ): RLines.State
        },
        Lines.Line.step(s, r, c, st),
        en => hv => hw => Cast.stop(f2, name, s, c, t, x, r, st)(hw),
        +st2 => +e2 => hv => hw => Cast.go(
          f2,
          name,
          s,
          c,
          t,
          x,
          r,
          st,
          st2,
          Lines.Line.run(p, s, r, c, st2, Lines.Line.step(s, r, c, st2)),
          e2,
          (
            %Moves.Next.slot(st, st2, Moves.Step.next(s, r, c, st, st2)(e2)): {Nat.is_le(_, RLines.State.slot(Lines.Line.run(p, s, r, c, st2, Lines.Line.step(s, r, c, st2)))) == True{}: Bool}
            Moves.Run.slot_le(p, s, r, c, st2)),
          +f3 => h3 => h4 => Cast.run(p, f3, name, s, c, t, x, r, st2)(h3)(h4)
        )(hv)(hw)
      )

# after a vote for the next slot of the state st that a line was read up to
# from its version 0 m, the line reads up to where the run continued from st
# ends
def From.cast(
  +name: String,
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +t: Nat,
  +x: Types.Cast,
  +r: Maybe<&2, List<&2, Types.Entry>>,
  m: Maybe<&2, Types.Entry>,
  +st: RLines.State
) -> {
  Lines.Line.from(s, r, c, m) == Some{st}: Maybe<&2, RLines.State>
} -> {
  Lines.Line.from(
    Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(st), t, x}, s),
    r,
    c,
    m
  )
    == Some{
      Lines.Line.run(
        1n+RLines.Line.bound(
          Facts.Facts.list(
            Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(st), t, x}, s)
          ),
          c
        ),
        Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(st), t, x}, s),
        r,
        c,
        st,
        Lines.Line.step(
          Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(st), t, x}, s),
          r,
          c,
          st
        )
      )
    }: Maybe<&2, RLines.State>
}:
  match m:
    case None{}:
      e => Empty.absurd(
        {
          None{}
            == Some{
              Lines.Line.run(
                1n+RLines.Line.bound(
                  Facts.Facts.list(
                    Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(st), t, x}, s)
                  ),
                  c
                ),
                Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(st), t, x}, s),
                r,
                c,
                st,
                Lines.Line.step(
                  Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(st), t, x}, s),
                  r,
                  c,
                  st
                )
              )
            }: Maybe<&2, RLines.State>
        },
        Shared.Maybe.none_ne_some(RLines.State, st, e)
      )
    case Some{+e0}:
      e => (
        %Shared.Maybe.some_inj(RLines.State, Lines.Line.start(s, r, c, RLines.State{[e0], 1n}), st, e): {Lines.Line.from(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(_), t, x}, s), r, c, Some{e0}) == Some{Lines.Line.run(1n+RLines.Line.bound(Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(_), t, x}, s)), c), Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(_), t, x}, s), r, c, _, Lines.Line.step(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(_), t, x}, s), r, c, _))}: Maybe<&2, RLines.State>}
        Equal.cong(RLines.State, Maybe<&2, RLines.State>, y => Some{y}, Lines.Line.run(RLines.Line.bound(Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(Lines.Line.start(s, r, c, RLines.State{[e0], 1n})), t, x}, s)), c), Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(Lines.Line.start(s, r, c, RLines.State{[e0], 1n})), t, x}, s), r, c, RLines.State{[e0], 1n}, Lines.Line.step(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(Lines.Line.start(s, r, c, RLines.State{[e0], 1n})), t, x}, s), r, c, RLines.State{[e0], 1n})), Lines.Line.run(1n+RLines.Line.bound(Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(Lines.Line.start(s, r, c, RLines.State{[e0], 1n})), t, x}, s)), c), Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(Lines.Line.start(s, r, c, RLines.State{[e0], 1n})), t, x}, s), r, c, Lines.Line.start(s, r, c, RLines.State{[e0], 1n}), Lines.Line.step(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(Lines.Line.start(s, r, c, RLines.State{[e0], 1n})), t, x}, s), r, c, Lines.Line.start(s, r, c, RLines.State{[e0], 1n}))), Cast.run(RLines.Line.bound(Facts.Facts.list(s), c), RLines.Line.bound(Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(Lines.Line.start(s, r, c, RLines.State{[e0], 1n})), t, x}, s)), c), name, s, c, t, x, r, RLines.State{[e0], 1n})(Shared.Nat.lt_le(RLines.State.slot(Lines.Line.start(s, r, c, RLines.State{[e0], 1n})), RLines.Line.bound(Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(Lines.Line.start(s, r, c, RLines.State{[e0], 1n})), t, x}, s)), c), Nat.add(RLines.Line.bound(Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(Lines.Line.start(s, r, c, RLines.State{[e0], 1n})), t, x}, s)), c), 1n))(Shared.Nat.lt_le(RLines.State.slot(Lines.Line.start(s, r, c, RLines.State{[e0], 1n})), 1n+RLines.State.slot(Lines.Line.start(s, r, c, RLines.State{[e0], 1n})), RLines.Line.bound(Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(Lines.Line.start(s, r, c, RLines.State{[e0], 1n})), t, x}, s)), c))(Shared.Nat.lt_succ(RLines.State.slot(Lines.Line.start(s, r, c, RLines.State{[e0], 1n}))))(Moves.Bound.ge(Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(Lines.Line.start(s, r, c, RLines.State{[e0], 1n})), t, x}, s)), c, name, RLines.State.slot(Lines.Line.start(s, r, c, RLines.State{[e0], 1n})), RRounds.Draft{t, x})(Facts.Facts.has_in(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(Lines.Line.start(s, r, c, RLines.State{[e0], 1n})), t, x}, s), Types.Fact.Vote{name, Types.Step.At{c, RLines.State.slot(Lines.Line.start(s, r, c, RLines.State{[e0], 1n})), t}, x})(Facts.Facts.add_has(s, Types.Fact.Vote{name, Types.Step.At{c, RLines.State.slot(Lines.Line.start(s, r, c, RLines.State{[e0], 1n})), t}, x})))))(Shared.Nat.le_add_first(RLines.Line.bound(Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(Lines.Line.start(s, r, c, RLines.State{[e0], 1n})), t, x}, s)), c), 1n)))(
          %Equal.sym(Nat, Nat.add(RLines.Line.bound(Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(Lines.Line.start(s, r, c, RLines.State{[e0], 1n})), t, x}, s)), c), 1n), 1n+RLines.Line.bound(Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(Lines.Line.start(s, r, c, RLines.State{[e0], 1n})), t, x}, s)), c), Crits.Crit.add_one(RLines.Line.bound(Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(Lines.Line.start(s, r, c, RLines.State{[e0], 1n})), t, x}, s)), c))): {Nat.is_lt(RLines.Line.bound(Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(Lines.Line.start(s, r, c, RLines.State{[e0], 1n})), t, x}, s)), c), _) == True{}: Bool}
          Shared.Nat.lt_succ(RLines.Line.bound(Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(Lines.Line.start(s, r, c, RLines.State{[e0], 1n})), t, x}, s)), c)))))

# after a vote for the next slot of the state st of a store, the state of
# the store is the run continued from st
def Store.state_cast(
  +name: String,
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +t: Nat,
  +x: Types.Cast,
  +st: RLines.State
) -> {
  Lines.Store.state(s, h) == Some{st}: Maybe<&2, RLines.State>
} -> {
  Lines.Store.state(
    Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, None{}}, RLines.State.slot(st), t, x}, s),
    h
  )
    == Some{
      RKnown.Known.go.at(
        Facts.Facts.crit(
          Moves.Delta.to(
            Moves.Delta.Vote{name, Ledgers.Line{h, None{}}, RLines.State.slot(st), t, x},
            s
          )
        ),
        Ledgers.Line{h, None{}},
        st,
        None{}
      )
    }: Maybe<&2, RLines.State>
}:
  e => (
    %Equal.sym(Maybe<&2, Types.Entry>, RLines.Store.first(Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, None{}}, RLines.State.slot(st), t, x}, s)), h), RLines.Store.first(Facts.Facts.list(s), h), Moves.First.same(Moves.Delta.Vote{name, Ledgers.Line{h, None{}}, RLines.State.slot(st), t, x}, s, h)({==})): {Lines.Line.from(Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, None{}}, RLines.State.slot(st), t, x}, s), None{}, Ledgers.Line{h, None{}}, _) == Some{RKnown.Known.go.at(Facts.Facts.crit(Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, None{}}, RLines.State.slot(st), t, x}, s)), Ledgers.Line{h, None{}}, st, None{})}: Maybe<&2, RLines.State>}
    From.cast(name, s, Ledgers.Line{h, None{}}, t, x, None{}, RLines.Store.first(Facts.Facts.list(s), h), st)(e))

# after a vote for the next slot of the state st of a branch, whose store
# has the versions rs, the state of the branch is the run continued from st
def Branch.state_cast(
  +name: String,
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +b: String,
  +t: Nat,
  +x: Types.Cast,
  +rs: List<&2, Types.Entry>,
  +j: Nat,
  +st: RLines.State
) -> {
  Lines.Line.state(s, Ledgers.Line{h, Some{b}}) == Some{st}: Maybe<&2, RLines.State>
} -> {
  Lines.Store.state(s, h) == Some{RLines.State{rs, j}}: Maybe<&2, RLines.State>
} -> {
  Lines.Line.state(
    Moves.Delta.to(
      Moves.Delta.Vote{name, Ledgers.Line{h, Some{b}}, RLines.State.slot(st), t, x},
      s
    ),
    Ledgers.Line{h, Some{b}}
  )
    == Some{
      RKnown.Known.go.at(
        Facts.Facts.crit(
          Moves.Delta.to(
            Moves.Delta.Vote{name, Ledgers.Line{h, Some{b}}, RLines.State.slot(st), t, x},
            s
          )
        ),
        Ledgers.Line{h, Some{b}},
        st,
        Some{rs}
      )
    }: Maybe<&2, RLines.State>
}:
  e => +es => (
    %Equal.sym(Maybe<&2, RLines.State>, Lines.Store.state(Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, Some{b}}, RLines.State.slot(st), t, x}, s), h), Lines.Store.state(s, h), Moves.Store.same(Moves.Delta.Vote{name, Ledgers.Line{h, Some{b}}, RLines.State.slot(st), t, x}, s, h)({==})(
      %Equal.sym(Bool, Ledgers.Line.is_eq(Ledgers.Line{h, None{}}, Ledgers.Line{h, Some{b}}), False{}, Moves.Line.root_ne(h, b)): {Bool.not(_) == True{}: Bool}
      {==})): {Lines.Branch.state(Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, Some{b}}, RLines.State.slot(st), t, x}, s), Ledgers.Line{h, Some{b}}, Maybe.map(&2, RLines.State, List<&2, Types.Entry>, RLines.State.versions, _)) == Some{RKnown.Known.go.at(Facts.Facts.crit(Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, Some{b}}, RLines.State.slot(st), t, x}, s)), Ledgers.Line{h, Some{b}}, st, Some{rs})}: Maybe<&2, RLines.State>}
    %Equal.sym(Maybe<&2, RLines.State>, Lines.Store.state(s, h), Some{RLines.State{rs, j}}, es): {Lines.Branch.state(Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, Some{b}}, RLines.State.slot(st), t, x}, s), Ledgers.Line{h, Some{b}}, Maybe.map(&2, RLines.State, List<&2, Types.Entry>, RLines.State.versions, _)) == Some{RKnown.Known.go.at(Facts.Facts.crit(Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, Some{b}}, RLines.State.slot(st), t, x}, s)), Ledgers.Line{h, Some{b}}, st, Some{rs})}: Maybe<&2, RLines.State>}
    From.cast(name, s, Ledgers.Line{h, Some{b}}, t, x, Some{rs}, RLines.Branch.first(rs, Ledgers.Line{h, Some{b}}), st)(Equal.trans(Maybe<&2, RLines.State>, Lines.Branch.state(s, Ledgers.Line{h, Some{b}}, Some{rs}), Lines.Line.state(s, Ledgers.Line{h, Some{b}}), Some{st}, Equal.cong(Maybe<&2, RLines.State>, Maybe<&2, RLines.State>, m => Lines.Branch.state(s, Ledgers.Line{h, Some{b}}, Maybe.map(&2, RLines.State, List<&2, Types.Entry>, RLines.State.versions, m)), Some{RLines.State{rs, j}}, Lines.Store.state(s, h), Equal.sym(Maybe<&2, RLines.State>, Lines.Store.state(s, h), Some{RLines.State{rs, j}}, es)), e)))

# What one more fact keeps of the contents
# ----------------------------------------
# A content is read from the versions of lines. A node that takes in an ask
# that starts no store reads each line as before. A ballot for the next slot
# of the known state of a branch, whose store is known, continues the
# versions of the branch and changes no other line. So each version that was
# read is read again, and a content that was read stays.

# what a node adds leaves each version that it read as it was: an ask that
# starts no store, or a ballot that continues a branch (Known.safe)
def Delta.safe(d: Moves.Delta, +s: Facts.Facts()) -> Bool:
  match d:
    case Moves.Delta.Ask{name, a}:
      Bool.not(RFacts.Request.is_start(RLines.Ask.request(a)))
    case Moves.Delta.Vote{name, +c, k, t, x}:
      RKnown.Known.safe(c, Lines.Line.state(s, c), Lines.Line.state(s, RKnown.Known.root(c)), k)

# no store is a branch
def Root.ne(
  +h2: Hashes.Hash,
  +h: Hashes.Hash,
  +b: String
) -> {Ledgers.Line.is_eq(Ledgers.Line{h2, None{}}, Ledgers.Line{h, Some{b}}) == False{}: Bool}:
  Lists.Bool.by(
    x => {x == False{}: Bool},
    Ledgers.Line.is_eq(Ledgers.Line{h2, None{}}, Ledgers.Line{h, Some{b}}),
    et => Equal.cong(
      Ledgers.Line,
      Bool,
      l => RLines.Line.is_root(l),
      Ledgers.Line{h2, None{}},
      Ledgers.Line{h, Some{b}},
      Ledgers.Line.is_eq_sound(Ledgers.Line{h2, None{}}, Ledgers.Line{h, Some{b}})(et)
    ),
    ef => {==}
  )

# a ballot for a slot of a branch hits no other line
def Branch.hit_other(
  +h: Hashes.Hash,
  +b: String,
  c2: Ledgers.Line
) -> {
  Ledgers.Line.is_eq(c2, Ledgers.Line{h, Some{b}}) == False{}: Bool
} -> {RKnown.Known.hit(Ledgers.Line{h, Some{b}}, c2) == False{}: Bool}:
  match c2:
    case Ledgers.Line{+h2, +b2}:
      ef => (
        %Equal.sym(Bool, Ledgers.Line.is_eq(Ledgers.Line{h2, b2}, Ledgers.Line{h, Some{b}}), False{}, ef): {Bool.or(_, Ledgers.Line.is_eq(Ledgers.Line{h2, None{}}, Ledgers.Line{h, Some{b}})) == False{}: Bool}
        Root.ne(h2, h, b))

# a version of a line whose state stays is read as before
def At.same(
  +s: Facts.Facts(),
  +s2: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  -e: Types.Entry
) -> {
  Lines.Line.state(s2, c) == Lines.Line.state(s, c): Maybe<&2, RLines.State>
} -> {
  Lines.Line.at(s, c, k) == Some{e}: Maybe<&2, Types.Entry>
} -> {Lines.Line.at(s2, c, k) == Some{e}: Maybe<&2, Types.Entry>}:
  es => ee => (
    %Equal.sym(Maybe<&2, RLines.State>, Lines.Line.state(s2, c), Lines.Line.state(s, c), es): {RLines.Line.at.of(Maybe.map(&2, RLines.State, List<&2, Types.Entry>, RLines.State.versions, _), k) == Some{e}: Maybe<&2, Types.Entry>}
    ee)

# a version of a branch is read again after a ballot for the next slot of
# its state st, when the state of its store is known
def Branch.at_cast(
  +name: String,
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +b: String,
  +t: Nat,
  +x: Types.Cast,
  +rs: List<&2, Types.Entry>,
  +j: Nat,
  +st: RLines.State,
  +i: Nat,
  -e: Types.Entry
) -> {
  Lines.Line.state(s, Ledgers.Line{h, Some{b}}) == Some{st}: Maybe<&2, RLines.State>
} -> {
  Lines.Store.state(s, h) == Some{RLines.State{rs, j}}: Maybe<&2, RLines.State>
} -> {
  Lines.Line.at(s, Ledgers.Line{h, Some{b}}, i) == Some{e}: Maybe<&2, Types.Entry>
} -> {
  Lines.Line.at(
    Moves.Delta.to(
      Moves.Delta.Vote{name, Ledgers.Line{h, Some{b}}, RLines.State.slot(st), t, x},
      s
    ),
    Ledgers.Line{h, Some{b}},
    i
  )
    == Some{e}: Maybe<&2, Types.Entry>
}:
  +em => es => ee => (
    %Equal.sym(Maybe<&2, RLines.State>, Lines.Line.state(Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, Some{b}}, RLines.State.slot(st), t, x}, s), Ledgers.Line{h, Some{b}}), Some{RKnown.Known.go.at(Facts.Facts.crit(Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, Some{b}}, RLines.State.slot(st), t, x}, s)), Ledgers.Line{h, Some{b}}, st, Some{rs})}, Branch.state_cast(name, s, h, b, t, x, rs, j, st)(em)(es)): {RLines.Line.at.of(Maybe.map(&2, RLines.State, List<&2, Types.Entry>, RLines.State.versions, _), i) == Some{e}: Maybe<&2, Types.Entry>}
    Lists.List.ext_get.of(Types.Entry, RLines.State.versions(st), RLines.State.versions(RKnown.Known.go.at(Facts.Facts.crit(Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, Some{b}}, RLines.State.slot(st), t, x}, s)), Ledgers.Line{h, Some{b}}, st, Some{rs})), i, e, Versions.Run.keeps(~List<&2, Types.Entry>, ~Versions.Run.Ext, ~Versions.Run.ext_step, 1n+RLines.Line.bound(Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, Some{b}}, RLines.State.slot(st), t, x}, s)), Ledgers.Line{h, Some{b}}), RLines.State.versions(st), Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, Some{b}}, RLines.State.slot(st), t, x}, s), Some{rs}, Ledgers.Line{h, Some{b}}, st, Lists.List.ext_refl(Types.Entry, RLines.State.versions(st))), (
      %em: {RLines.Line.at.of(Maybe.map(&2, RLines.State, List<&2, Types.Entry>, RLines.State.versions, _), i) == Some{e}: Maybe<&2, Types.Entry>}
      ee)))

# Vote.at_kept, with the states m of the line and ms of its store
def Vote.at_kept.of(
  +name: String,
  +s: Facts.Facts(),
  c: Ledgers.Line,
  m: Maybe<&2, RLines.State>,
  ms: Maybe<&2, RLines.State>,
  +k: Nat,
  +t: Nat,
  +x: Types.Cast,
  +c2: Ledgers.Line,
  +i: Nat,
  -e: Types.Entry
) -> {
  Lines.Line.state(s, c) == m: Maybe<&2, RLines.State>
} -> {
  Lines.Line.state(s, RKnown.Known.root(c)) == ms: Maybe<&2, RLines.State>
} -> {
  RKnown.Known.safe(c, m, ms, k) == True{}: Bool
} -> {
  Lines.Line.at(s, c2, i) == Some{e}: Maybe<&2, Types.Entry>
} -> {
  Lines.Line.at(
    Moves.Delta.to(Moves.Delta.Vote{name, c, k, t, x}, s),
    c2,
    i
  )
    == Some{e}: Maybe<&2, Types.Entry>
}:
  match c m ms:
    case Ledgers.Line{h, None{}} m ms:
      em => es => hs => ee => Empty.absurd(
        {
          Lines.Line.at(
            Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, None{}}, k, t, x}, s),
            c2,
            i
          )
            == Some{e}: Maybe<&2, Types.Entry>
        },
        Shared.Bool.false_ne_true(hs)
      )
    case Ledgers.Line{h, Some{b}} None{} ms:
      em => es => hs => ee => Empty.absurd(
        {
          Lines.Line.at(
            Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, Some{b}}, k, t, x}, s),
            c2,
            i
          )
            == Some{e}: Maybe<&2, Types.Entry>
        },
        Shared.Bool.false_ne_true(hs)
      )
    case Ledgers.Line{h, Some{b}} Some{st} None{}:
      em => es => hs => ee => Empty.absurd(
        {
          Lines.Line.at(
            Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, Some{b}}, k, t, x}, s),
            c2,
            i
          )
            == Some{e}: Maybe<&2, Types.Entry>
        },
        Shared.Bool.false_ne_true(hs)
      )
    case Ledgers.Line{+h, Some{+b}} Some{+st} Some{RLines.State{+R, +j}}:
      +em => +es => hs => +ee => (
        %Shared.Nat.is_eq_sound(RLines.State.slot(st), k)(hs): {Lines.Line.at(Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, Some{b}}, _, t, x}, s), c2, i) == Some{e}: Maybe<&2, Types.Entry>}
        Lists.Bool.by(y => {Lines.Line.at(Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, Some{b}}, RLines.State.slot(st), t, x}, s), c2, i) == Some{e}: Maybe<&2, Types.Entry>}, Ledgers.Line.is_eq(c2, Ledgers.Line{h, Some{b}}), +et => Reads.Eq.back(Ledgers.Line, l => {Lines.Line.at(Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, Some{b}}, RLines.State.slot(st), t, x}, s), l, i) == Some{e}: Maybe<&2, Types.Entry>}, c2, Ledgers.Line{h, Some{b}}, Ledgers.Line.is_eq_sound(c2, Ledgers.Line{h, Some{b}})(et), Branch.at_cast(name, s, h, b, t, x, R, j, st, i, e)(em)(es)(Reads.Eq.to(Ledgers.Line, l => {Lines.Line.at(s, l, i) == Some{e}: Maybe<&2, Types.Entry>}, c2, Ledgers.Line{h, Some{b}}, Ledgers.Line.is_eq_sound(c2, Ledgers.Line{h, Some{b}})(et), ee))), ef => At.same(s, Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, Some{b}}, RLines.State.slot(st), t, x}, s), c2, i, e)(Line.state_voted(name, s, Ledgers.Line{h, Some{b}}, RLines.State.slot(st), t, x, c2)(Branch.hit_other(h, b, c2)(ef)))(ee)))

# a version that was read is read again after a node adds what is safe
def Delta.at_kept(
  d: Moves.Delta,
  +s: Facts.Facts(),
  +c2: Ledgers.Line,
  +i: Nat,
  -e: Types.Entry
) -> {
  Delta.safe(d, s) == True{}: Bool
} -> {
  Lines.Line.at(s, c2, i) == Some{e}: Maybe<&2, Types.Entry>
} -> {Lines.Line.at(Moves.Delta.to(d, s), c2, i) == Some{e}: Maybe<&2, Types.Entry>}:
  match d:
    case Moves.Delta.Ask{+name, +a}:
      hs => At.same(
        s,
        Moves.Delta.to(Moves.Delta.Ask{name, a}, s),
        c2,
        i,
        e
      )(
        Moves.Line.state_asked(
          name,
          s,
          a,
          c2
        )(Shared.Bool.not_true(RFacts.Request.is_start(RLines.Ask.request(a)))(hs))
      )
    case Moves.Delta.Vote{+name, +c, +k, +t, +x}:
      Vote.at_kept.of(
        name,
        s,
        c,
        Lines.Line.state(s, c),
        Lines.Line.state(s, RKnown.Known.root(c)),
        k,
        t,
        x,
        c2,
        i,
        e
      )({==})({==})

# a hop stays when a node adds what is safe
def Hop.kept(
  +d: Moves.Delta,
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +w: Spec.Point
) -> {
  Delta.safe(d, s) == True{}: Bool
} -> {
  Contents.Way.hop(s, c, k, w) == True{}: Bool
} -> {Contents.Way.hop(Moves.Delta.to(d, s), c, k, w) == True{}: Bool}:
  hs => Lists.Maybe.by(
    Types.Entry,
    m => {
      RContents.Way.hop.of(c, k, w, m) == True{}: Bool
    } -> {Contents.Way.hop(Moves.Delta.to(d, s), c, k, w) == True{}: Bool},
    Lines.Line.at(s, c, k),
    en => h => Empty.absurd(
      {Contents.Way.hop(Moves.Delta.to(d, s), c, k, w) == True{}: Bool},
      Shared.Bool.false_ne_true(h)
    ),
    +e => ee => h => Reads.Eq.back(
      Maybe<&2, Types.Entry>,
      m => {RContents.Way.hop.of(c, k, w, m) == True{}: Bool},
      Lines.Line.at(Moves.Delta.to(d, s), c, k),
      Some{e},
      Delta.at_kept(d, s, c, k, e)(hs)(ee),
      h
    )
  )

# a way stays when a node adds what is safe
def Way.ok_kept(
  +d: Moves.Delta,
  +s: Facts.Facts(),
  +a: Spec.Point,
  ws: List<&2, Spec.Point>,
  +c: Ledgers.Line,
  +k: Nat
) -> {
  Delta.safe(d, s) == True{}: Bool
} -> {
  Contents.Way.ok(s, a, ws, c, k) == True{}: Bool
} -> {Contents.Way.ok(Moves.Delta.to(d, s), a, ws, c, k) == True{}: Bool}:
  match ws:
    case Nil{}:
      hs => h => h
    case Con{+w, +rest}:
      +hs => +h => Shared.Bool.and_both(
        Contents.Way.hop(Moves.Delta.to(d, s), c, k, w),
        Contents.Way.ok(Moves.Delta.to(d, s), a, rest, Spec.Point.line(w), Spec.Point.n(w))
      )(
        Hop.kept(
          d,
          s,
          c,
          k,
          w
        )(
          hs
        )(
          Shared.Bool.and_true_left(
            Contents.Way.hop(s, c, k, w),
            Contents.Way.ok(s, a, rest, Spec.Point.line(w), Spec.Point.n(w))
          )(h)
        )
      )(
        Way.ok_kept(
          d,
          s,
          a,
          rest,
          Spec.Point.line(w),
          Spec.Point.n(w)
        )(
          hs
        )(
          Shared.Bool.and_true_right(
            Contents.Way.hop(s, c, k, w),
            Contents.Way.ok(s, a, rest, Spec.Point.line(w), Spec.Point.n(w))
          )(h)
        )
      )

# Merge.fits_kept, for the base m
def Merge.fits.of_kept(
  +d: Moves.Delta,
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +j: Nat,
  m: Maybe<&2, Spec.Point>,
  +ours: List<&2, Spec.Point>,
  +theirs: List<&2, Spec.Point>,
  +t: Spec.Point
) -> {
  Delta.safe(d, s) == True{}: Bool
} -> {
  Contents.Merge.fits.of(s, c, j, m, ours, theirs, t) == True{}: Bool
} -> {Contents.Merge.fits.of(Moves.Delta.to(d, s), c, j, m, ours, theirs, t) == True{}: Bool}:
  match m:
    case None{}:
      hs => h => {==}
    case Some{+a}:
      +hs => +h => Shared.Bool.and_both(
        Contents.Way.ok(Moves.Delta.to(d, s), a, ours, c, j),
        Contents.Way.ok(Moves.Delta.to(d, s), a, theirs, Spec.Point.line(t), Spec.Point.n(t))
      )(
        Way.ok_kept(
          d,
          s,
          a,
          ours,
          c,
          j
        )(
          hs
        )(
          Shared.Bool.and_true_left(
            Contents.Way.ok(s, a, ours, c, j),
            Contents.Way.ok(s, a, theirs, Spec.Point.line(t), Spec.Point.n(t))
          )(h)
        )
      )(
        Way.ok_kept(
          d,
          s,
          a,
          theirs,
          Spec.Point.line(t),
          Spec.Point.n(t)
        )(
          hs
        )(
          Shared.Bool.and_true_right(
            Contents.Way.ok(s, a, ours, c, j),
            Contents.Way.ok(s, a, theirs, Spec.Point.line(t), Spec.Point.n(t))
          )(h)
        )
      )

# a merge that fits still fits when a node adds what is safe
def Merge.fits_kept(
  +d: Moves.Delta,
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +j: Nat,
  +e: Types.Entry
) -> {
  Delta.safe(d, s) == True{}: Bool
} -> {
  Contents.Merge.fits(s, c, j, e) == True{}: Bool
} -> {Contents.Merge.fits(Moves.Delta.to(d, s), c, j, e) == True{}: Bool}:
  Merge.fits.of_kept(
    d,
    s,
    c,
    j,
    RContents.Entry.base(e),
    RContents.Entry.ours(e),
    RContents.Entry.theirs(e),
    RContents.Point.or(c, RContents.Entry.takes(e))
  )

# the content of version 0 stays when a node adds what is safe
def First.kept(
  +d: Moves.Delta,
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  -t: RFiles.Files()
) -> {
  Delta.safe(d, s) == True{}: Bool
} -> {
  RContents.Content.first(Lines.Line.at(s, c, 0n)) == Some{t}: Maybe<&2, RFiles.Files()>
} -> {
  RContents.Content.first(
    Lines.Line.at(Moves.Delta.to(d, s), c, 0n)
  )
    == Some{t}: Maybe<&2, RFiles.Files()>
}:
  hs => Lists.Maybe.by(
    Types.Entry,
    m => {
      RContents.Content.first(m) == Some{t}: Maybe<&2, RFiles.Files()>
    } -> {
      RContents.Content.first(
        Lines.Line.at(Moves.Delta.to(d, s), c, 0n)
      )
        == Some{t}: Maybe<&2, RFiles.Files()>
    },
    Lines.Line.at(s, c, 0n),
    en => h => Empty.absurd(
      {
        RContents.Content.first(
          Lines.Line.at(Moves.Delta.to(d, s), c, 0n)
        )
          == Some{t}: Maybe<&2, RFiles.Files()>
      },
      Shared.Maybe.none_ne_some(RFiles.Files(), t, h)
    ),
    +e => ee => h => Reads.Eq.back(
      Maybe<&2, Types.Entry>,
      m => {RContents.Content.first(m) == Some{t}: Maybe<&2, RFiles.Files()>},
      Lines.Line.at(Moves.Delta.to(d, s), c, 0n),
      Some{e},
      Delta.at_kept(d, s, c, 0n, e)(hs)(ee),
      h
    )
  )

# bend-lint: expect-begin bend-lint-rules/performance/missed_fork@hint -- a proof does not run
# a content read with some fuel stays, read with the same fuel, when a node
# adds what is safe
def Content.at_kept(
  f: Nat,
  +d: Moves.Delta,
  +s: Facts.Facts(),
  +hs: {Delta.safe(d, s) == True{}: Bool},
  +c: Ledgers.Line,
  k: Nat,
  -t: RFiles.Files()
) -> {
  Contents.Content.at(f, s, c, k) == Some{t}: Maybe<&2, RFiles.Files()>
} -> {Contents.Content.at(f, Moves.Delta.to(d, s), c, k) == Some{t}: Maybe<&2, RFiles.Files()>}:
  match f k:
    case 0n k:
      h => Empty.absurd(
        {Contents.Content.at(0n, Moves.Delta.to(d, s), c, k) == Some{t}: Maybe<&2, RFiles.Files()>},
        Shared.Maybe.none_ne_some(RFiles.Files(), t, h)
      )
    case 1n+g 0n:
      First.kept(d, s, c, t)(hs)
    case 1n+(+g) 1n+(+j):
      Lists.Maybe.by(
        Types.Entry,
        m => {
          RContents.Content.next(
            m,
            Contents.Entry.fits(s, c, j, m),
            Contents.Content.at(g, s, c, j),
            Reads.Sub.taken(g, s, c, m),
            Reads.Sub.based(g, s, c, m)
          )
            == Some{t}: Maybe<&2, RFiles.Files()>
        } -> {
          Contents.Content.at(
            1n+g,
            Moves.Delta.to(d, s),
            c,
            1n+j
          )
            == Some{t}: Maybe<&2, RFiles.Files()>
        },
        Lines.Line.at(s, c, 1n+j),
        en => h => Empty.absurd(
          {
            Contents.Content.at(
              1n+g,
              Moves.Delta.to(d, s),
              c,
              1n+j
            )
              == Some{t}: Maybe<&2, RFiles.Files()>
          },
          Shared.Maybe.none_ne_some(RFiles.Files(), t, h)
        ),
        +e => ee => h => Reads.Eq.back(
          Maybe<&2, Types.Entry>,
          m => {
            RContents.Content.next(
              m,
              Contents.Entry.fits(Moves.Delta.to(d, s), c, j, m),
              Contents.Content.at(g, Moves.Delta.to(d, s), c, j),
              Reads.Sub.taken(g, Moves.Delta.to(d, s), c, m),
              Reads.Sub.based(g, Moves.Delta.to(d, s), c, m)
            )
              == Some{t}: Maybe<&2, RFiles.Files()>
          },
          Lines.Line.at(Moves.Delta.to(d, s), c, 1n+j),
          Some{e},
          Delta.at_kept(d, s, c, 1n+j, e)(hs)(ee),
          Reads.Content.apply_le(
            RAnswers.Entry.request(e),
            Contents.Merge.fits(s, c, j, e),
            Contents.Content.at(g, s, c, j),
            Reads.Sub.taken(g, s, c, Some{e}),
            Reads.Sub.based(g, s, c, Some{e}),
            Contents.Merge.fits(Moves.Delta.to(d, s), c, j, e),
            Contents.Content.at(g, Moves.Delta.to(d, s), c, j),
            Reads.Sub.taken(g, Moves.Delta.to(d, s), c, Some{e}),
            Reads.Sub.based(g, Moves.Delta.to(d, s), c, Some{e}),
            t
          )(
            Merge.fits_kept(d, s, c, j, e)(hs)
          )(
            Content.at_kept(g, d, s, hs, c, j)
          )(
            Content.at_kept(
              g,
              d,
              s,
              hs,
              Spec.Point.line(RContents.Entry.taken(c, Some{e})),
              Spec.Point.n(RContents.Entry.taken(c, Some{e}))
            )
          )(
            Content.at_kept(
              g,
              d,
              s,
              hs,
              Spec.Point.line(RContents.Entry.based(c, Some{e})),
              Spec.Point.n(RContents.Entry.based(c, Some{e}))
            )
          )(h)
        )
      )
# bend-lint: expect-end bend-lint-rules/performance/missed_fork@hint

# a content that a table holds stays right when a node adds what is safe
def Held.kept(
  +d: Moves.Delta,
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +f: Nat,
  +x: RFiles.Files()
) -> {
  Delta.safe(d, s) == True{}: Bool
} -> {
  RFiles.Files.fits(Contents.Content.at(f, s, c, k), x) == True{}: Bool
} -> {RFiles.Files.fits(Contents.Content.at(f, Moves.Delta.to(d, s), c, k), x) == True{}: Bool}:
  hs => h => Files.fits_of(
    Contents.Content.at(f, Moves.Delta.to(d, s), c, k),
    x
  )(Content.at_kept(f, d, s, hs, c, k, x)(Files.fits_sound(Contents.Content.at(f, s, c, k), x)(h)))

# contents that are right stay right when a node adds what is safe: each of
# the entries es
def Binds.kept(
  es: List<&2, Crits.Bind<RKnown.Held>>,
  +d: Moves.Delta,
  +s: Facts.Facts()
) -> {
  Delta.safe(d, s) == True{}: Bool
} -> {
  Orders.Binds.every(
    ~RKnown.Held,
    ~RFacts.Plain(),
    ~RContents.Held.ok,
    es,
    Facts.Facts.crit(s)
  )
    == True{}: Bool
} -> {
  Orders.Binds.every(
    ~RKnown.Held,
    ~RFacts.Plain(),
    ~RContents.Held.ok,
    es,
    Facts.Facts.crit(Moves.Delta.to(d, s))
  )
    == True{}: Bool
}:
  match es:
    case Nil{}:
      hs => h => {==}
    case Con{Crits.Bind{q, RKnown.Held{+c, +k, +f, +x}}, +r}:
      +hs => +h => Shared.Bool.and_both(
        RContents.Held.ok(Facts.Facts.crit(Moves.Delta.to(d, s)), RKnown.Held{c, k, f, x}),
        Orders.Binds.every(
          ~RKnown.Held,
          ~RFacts.Plain(),
          ~RContents.Held.ok,
          r,
          Facts.Facts.crit(Moves.Delta.to(d, s))
        )
      )(
        Held.kept(
          d,
          s,
          c,
          k,
          f,
          x
        )(
          hs
        )(
          Shared.Bool.and_true_left(
            RContents.Held.ok(Facts.Facts.crit(s), RKnown.Held{c, k, f, x}),
            Orders.Binds.every(
              ~RKnown.Held,
              ~RFacts.Plain(),
              ~RContents.Held.ok,
              r,
              Facts.Facts.crit(s)
            )
          )(h)
        )
      )(
        Binds.kept(
          r,
          d,
          s
        )(
          hs
        )(
          Shared.Bool.and_true_right(
            RContents.Held.ok(Facts.Facts.crit(s), RKnown.Held{c, k, f, x}),
            Orders.Binds.every(
              ~RKnown.Held,
              ~RFacts.Plain(),
              ~RContents.Held.ok,
              r,
              Facts.Facts.crit(s)
            )
          )(h)
        )
      )

# contents that are right stay right when a node adds what is safe
def Stock.kept(
  +m: Crits.Crit<RKnown.Held>,
  +d: Moves.Delta,
  +s: Facts.Facts()
) -> {
  Delta.safe(d, s) == True{}: Bool
} -> {
  Orders.Crit.every(
    ~RKnown.Held,
    ~RFacts.Plain(),
    ~RContents.Held.ok,
    m,
    Facts.Facts.crit(s)
  )
    == True{}: Bool
} -> {
  Orders.Crit.every(
    ~RKnown.Held,
    ~RFacts.Plain(),
    ~RContents.Held.ok,
    m,
    Facts.Facts.crit(Moves.Delta.to(d, s))
  )
    == True{}: Bool
}:
  hs => +h => Shared.Bool.and_both(
    Crits.Crit.wf(~RKnown.Held, m, 0n),
    Orders.Binds.every(
      ~RKnown.Held,
      ~RFacts.Plain(),
      ~RContents.Held.ok,
      Crits.Crit.entries(RKnown.Held, m),
      Facts.Facts.crit(Moves.Delta.to(d, s))
    )
  )(
    Shared.Bool.and_true_left(
      Crits.Crit.wf(~RKnown.Held, m, 0n),
      Orders.Binds.every(
        ~RKnown.Held,
        ~RFacts.Plain(),
        ~RContents.Held.ok,
        Crits.Crit.entries(RKnown.Held, m),
        Facts.Facts.crit(s)
      )
    )(h)
  )(
    Binds.kept(
      Crits.Crit.entries(RKnown.Held, m),
      d,
      s
    )(
      hs
    )(
      Shared.Bool.and_true_right(
        Crits.Crit.wf(~RKnown.Held, m, 0n),
        Orders.Binds.every(
          ~RKnown.Held,
          ~RFacts.Plain(),
          ~RContents.Held.ok,
          Crits.Crit.entries(RKnown.Held, m),
          Facts.Facts.crit(s)
        )
      )(h)
    )
  )

# the contents of a table that is right are right
def Known.contents_ok(
  kn: RKnown.Known(),
  +s: RFacts.Plain()
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {RContents.Known.ok(RKnown.Known.contents(kn), s) == True{}: Bool}:
  match kn:
    case Nil{}:
      ok => {==}
    case Con{RKnown.Kept{+c, +st}, +rest}:
      ok => Known.contents_ok(rest, s)(Ok.tail(RKnown.Kept{c, st}, rest, s)(ok))
    case Con{RKnown.Ruled{+c, +zu, +u}, +rest}:
      ok => Known.contents_ok(rest, s)(Ok.tail(RKnown.Ruled{c, zu, u}, rest, s)(ok))
    case Con{RKnown.Stock{+m, +lwm}, +rest}:
      +ok => Ok.cons(
        RKnown.Stock{m, lwm},
        RKnown.Known.contents(rest),
        s
      )(
        Ok.head(RKnown.Stock{m, lwm}, rest, s)(ok)
      )(Known.contents_ok(rest, s)(Ok.tail(RKnown.Stock{m, lwm}, rest, s)(ok)))
    case Con{RKnown.Made{+c, +y}, +rest}:
      ok => Known.contents_ok(rest, s)(Ok.tail(RKnown.Made{c, y}, rest, s)(ok))
    case Con{RKnown.Open{+fs2, +pk2, +tx9, +mtx9}, +rest}:
      ok => Known.contents_ok(rest, s)(Ok.tail(RKnown.Open{fs2, pk2, tx9, mtx9}, rest, s)(ok))

# a set with a fact that it did not hold has one more fact
def Fuel.add_new(
  +s: Facts.Facts(),
  +f: Types.Fact
) -> {
  Facts.Facts.has(s, f) == False{}: Bool
} -> {
  RFacts.Facts.fuel(
    Facts.Facts.crit(Facts.Facts.add(s, f))
  )
    == 1n+RFacts.Facts.fuel(Facts.Facts.crit(s)): Nat
}:
  h =>
    %Equal.sym(
      Nat,
      List.length(
        &2,
        Types.Fact,
        Sets.ValSet.list(~Types.Fact, ~Coded.Fact.words, Facts.Facts.add(s, f))
      ),
      Crits.Crit.size(Types.Fact, Facts.Facts.crit(Facts.Facts.add(s, f))),
      Sets.ValSet.size_list(~Types.Fact, ~Coded.Fact.words, Facts.Facts.add(s, f))
    ): {_ == 1n+RFacts.Facts.fuel(Facts.Facts.crit(s)): Nat}
    %Equal.sym(
      Nat,
      List.length(&2, Types.Fact, Sets.ValSet.list(~Types.Fact, ~Coded.Fact.words, s)),
      Crits.Crit.size(Types.Fact, Facts.Facts.crit(s)),
      Sets.ValSet.size_list(~Types.Fact, ~Coded.Fact.words, s)
    ): {Crits.Crit.size(Types.Fact, Facts.Facts.crit(Facts.Facts.add(s, f))) == 1n+_: Nat}
    %Equal.sym(
      Nat,
      Crits.Crit.size(
        Types.Fact,
        Crits.Crit.set(~Types.Fact, Facts.Facts.crit(s), Coded.Fact.words(f), f)
      ),
      Shared.Nat.add_if(
        Bool.not(
          Maybe.is_some(
            &2,
            Types.Fact,
            Crits.Crit.get(Types.Fact, Facts.Facts.crit(s), Coded.Fact.words(f))
          )
        ),
        Crits.Crit.size(Types.Fact, Facts.Facts.crit(s))
      ),
      Crits.Dict.size_set.at(
        ~Types.Fact,
        Facts.Facts.crit(s),
        Coded.Fact.words(f),
        f
      )(Sets.ValSet.wf(~Types.Fact, ~Coded.Fact.words, s))
    ): {_ == 1n+Crits.Crit.size(Types.Fact, Facts.Facts.crit(s)): Nat}
    %Equal.sym(
      Bool,
      Maybe.is_some(
        &2,
        Types.Fact,
        Crits.Crit.get(Types.Fact, Facts.Facts.crit(s), Coded.Fact.words(f))
      ),
      False{},
      h
    ): {
      Shared.Nat.add_if(
        Bool.not(_),
        Crits.Crit.size(Types.Fact, Facts.Facts.crit(s))
      )
        == 1n+Crits.Crit.size(Types.Fact, Facts.Facts.crit(s)): Nat
    }
    {==}

# a set that holds no vote of a node for a step does not hold a vote of the
# node for the step
def Vote.fresh(
  +name: String,
  +s: Facts.Facts(),
  +st: Types.Step,
  +x: Types.Cast
) -> {
  RFacts.Facts.cast(Facts.Facts.crit(s), name, st) == False{}: Bool
} -> {Facts.Facts.has(s, Types.Fact.Vote{name, st, x}) == False{}: Bool}:
  hc => Lists.Bool.by(
    b => {
      Facts.Facts.has(s, Types.Fact.Vote{name, st, x}) == b: Bool
    } -> {Facts.Facts.has(s, Types.Fact.Vote{name, st, x}) == False{}: Bool},
    Facts.Facts.has(s, Types.Fact.Vote{name, st, x}),
    et => e => Empty.absurd(
      {Facts.Facts.has(s, Types.Fact.Vote{name, st, x}) == False{}: Bool},
      Shared.Bool.true_ne_false(
        Equal.trans(
          Bool,
          True{},
          RFacts.Facts.cast(Facts.Facts.crit(s), name, st),
          False{},
          Equal.sym(
            Bool,
            RFacts.Facts.cast(Facts.Facts.crit(s), name, st),
            True{},
            Shared.List.some_member(
              ~Types.Fact,
              ~RFacts.Seat,
              ~Coded.Fact.is_eq,
              ~RFacts.Fact.is_cast,
              ~Coded.Fact.laws(),
              Facts.Facts.list(s),
              Types.Fact.Vote{name, st, x},
              RFacts.Seat{name, st}
            )(
              Facts.Facts.has_in(s, Types.Fact.Vote{name, st, x})(e)
            )(
              Shared.Bool.and_both(
                String.eq(name, name),
                Coded.Step.is_eq(st, st)
              )(Texts.String.eq_refl(name))(Coded.Step.is_eq_refl(st))
            )
          ),
          hc
        )
      )
    ),
    ef => e => e
  )({==})

# the contents of a table that is right for the facts s, each with one more
# as its number, are right when a node adds a ballot that is safe and that
# it did not hold
def Known.spared_kept(
  kn: RKnown.Known(),
  +name: String,
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +t: Nat,
  +x: Types.Cast
) -> {
  Delta.safe(Moves.Delta.Vote{name, c, k, t, x}, s) == True{}: Bool
} -> {
  Facts.Facts.has(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}) == False{}: Bool
} -> {
  RContents.Known.ok(kn, Facts.Facts.crit(s)) == True{}: Bool
} -> {
  RContents.Known.ok(
    RKnown.Known.deeper(RKnown.Known.contents(kn)),
    Facts.Facts.crit(Moves.Delta.to(Moves.Delta.Vote{name, c, k, t, x}, s))
  )
    == True{}: Bool
}:
  match kn:
    case Nil{}:
      hs => hf => ok => {==}
    case Con{RKnown.Kept{+c2, +st2}, +rest}:
      hs => hf => ok => Known.spared_kept(
        rest,
        name,
        s,
        c,
        k,
        t,
        x
      )(hs)(hf)(Ok.tail(RKnown.Kept{c2, st2}, rest, Facts.Facts.crit(s))(ok))
    case Con{RKnown.Ruled{+c2, +zu2, +u2}, +rest}:
      hs => hf => ok => Known.spared_kept(
        rest,
        name,
        s,
        c,
        k,
        t,
        x
      )(hs)(hf)(Ok.tail(RKnown.Ruled{c2, zu2, u2}, rest, Facts.Facts.crit(s))(ok))
    case Con{RKnown.Made{+c2, +y2}, +rest}:
      hs => hf => ok => Known.spared_kept(
        rest,
        name,
        s,
        c,
        k,
        t,
        x
      )(hs)(hf)(Ok.tail(RKnown.Made{c2, y2}, rest, Facts.Facts.crit(s))(ok))
    case Con{RKnown.Open{+fs2, +pk2, +tx9, +mtx9}, +rest}:
      hs => hf => ok => Known.spared_kept(
        rest,
        name,
        s,
        c,
        k,
        t,
        x
      )(hs)(hf)(Ok.tail(RKnown.Open{fs2, pk2, tx9, mtx9}, rest, Facts.Facts.crit(s))(ok))
    case Con{RKnown.Stock{+m, +lwm}, +rest}:
      +hs => +hf => +ok => Stock.cons(
        m,
        1n+lwm,
        RKnown.Known.deeper(RKnown.Known.contents(rest)),
        Facts.Facts.crit(Moves.Delta.to(Moves.Delta.Vote{name, c, k, t, x}, s))
      )(
        Stock.kept(
          m,
          Moves.Delta.Vote{name, c, k, t, x},
          s
        )(hs)(Stock.head(m, lwm, rest, Facts.Facts.crit(s))(ok))
      )((
          %Equal.sym(Nat, RFacts.Facts.fuel(Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))), 1n+RFacts.Facts.fuel(Facts.Facts.crit(s)), Fuel.add_new(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})(hf)): {Nat.is_le(1n+lwm, _) == True{}: Bool}
          Stock.head_low(m, lwm, rest, Facts.Facts.crit(s))(ok)))(
        Known.spared_kept(
          rest,
          name,
          s,
          c,
          k,
          t,
          x
        )(hs)(hf)(Ok.tail(RKnown.Stock{m, lwm}, rest, Facts.Facts.crit(s))(ok))
      )

# a table that is right for the facts s is right after a node takes in an
# ask that starts no store
def Known.asked_ok(
  kn: RKnown.Known(),
  +name: String,
  +s: Facts.Facts(),
  +a: Types.Ask
) -> {
  RFacts.Request.is_start(RLines.Ask.request(a)) == False{}: Bool
} -> {
  RContents.Known.ok(kn, Facts.Facts.crit(s)) == True{}: Bool
} -> {
  RContents.Known.ok(
    kn,
    Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{a}))
  )
    == True{}: Bool
}:
  match kn:
    case Nil{}:
      e => ok => {==}
    case Con{RKnown.Kept{+c, +st}, +rest}:
      +e => +ok => Shared.Bool.and_both(
        RKnown.State.fits(Lines.Line.state(Facts.Facts.take(name, s, Types.Fact.Ask{a}), c), st),
        RContents.Known.ok(rest, Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{a})))
      )(
        %Equal.sym(Maybe<&2, RLines.State>, Lines.Line.state(Facts.Facts.take(name, s, Types.Fact.Ask{a}), c), Lines.Line.state(s, c), Moves.Line.state_asked(name, s, a, c)(e)): {RKnown.State.fits(_, st) == True{}: Bool}
        Shared.Bool.and_true_left(RKnown.State.fits(Lines.Line.state(s, c), st), RContents.Known.ok(rest, Facts.Facts.crit(s)))(ok))(
        Known.asked_ok(
          rest,
          name,
          s,
          a
        )(
          e
        )(
          Shared.Bool.and_true_right(
            RKnown.State.fits(Lines.Line.state(s, c), st),
            RContents.Known.ok(rest, Facts.Facts.crit(s))
          )(ok)
        )
      )
    case Con{RKnown.Stock{+m, +lwm}, +rest}:
      +e => +ok => Stock.cons(
        m,
        lwm,
        rest,
        Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{a}))
      )(Stock.kept(m, Moves.Delta.Ask{name, a}, s)(
          %Equal.sym(Bool, RFacts.Request.is_start(RLines.Ask.request(a)), False{}, e): {Bool.not(_) == True{}: Bool}
          {==})(Stock.head(m, lwm, rest, Facts.Facts.crit(s))(ok)))(
        Shared.Nat.le_trans(
          lwm,
          RFacts.Facts.fuel(Facts.Facts.crit(s)),
          RFacts.Facts.fuel(Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{a})))
        )(
          Stock.head_low(m, lwm, rest, Facts.Facts.crit(s))(ok)
        )(
          Facts.Facts.wider_fuel(
            s,
            Facts.Facts.take(name, s, Types.Fact.Ask{a})
          )(Facts.Facts.take_wider(name, s, Types.Fact.Ask{a}))
        )
      )(
        Known.asked_ok(
          rest,
          name,
          s,
          a
        )(e)(Ok.tail(RKnown.Stock{m, lwm}, rest, Facts.Facts.crit(s))(ok))
      )
    case Con{RKnown.Ruled{+c, +zu, +u}, +rest}:
      +e => +ok => Ok.cons(
        RKnown.Ruled{c, zu, u},
        rest,
        Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{a}))
      )(
        Ruled.same(
          s,
          Facts.Facts.take(name, s, Types.Fact.Ask{a}),
          c,
          zu,
          u
        )(
          Moves.Line.state_asked(name, s, a, c)(e)
        )(
          Moves.Line.state_asked(name, s, a, RKnown.Known.root(c))(e)
        )(Ok.head(RKnown.Ruled{c, zu, u}, rest, Facts.Facts.crit(s))(ok))
      )(
        Known.asked_ok(
          rest,
          name,
          s,
          a
        )(e)(Ok.tail(RKnown.Ruled{c, zu, u}, rest, Facts.Facts.crit(s))(ok))
      )
    case Con{RKnown.Made{+c, +y}, +rest}:
      +e => +ok => Ok.cons(
        RKnown.Made{c, y},
        rest,
        Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{a}))
      )(
        Made.same(
          s,
          Facts.Facts.take(name, s, Types.Fact.Ask{a}),
          c,
          y
        )(
          Moves.Line.state_asked(name, s, a, c)(e)
        )(Ok.head(RKnown.Made{c, y}, rest, Facts.Facts.crit(s))(ok))
      )(
        Known.asked_ok(
          rest,
          name,
          s,
          a
        )(e)(Ok.tail(RKnown.Made{c, y}, rest, Facts.Facts.crit(s))(ok))
      )
    case Con{RKnown.Open{+fs2, +pk2, +tx9, +mtx9}, +rest}:
      e => ok => Known.asked_ok(
        rest,
        name,
        s,
        a
      )(e)(Ok.tail(RKnown.Open{fs2, pk2, tx9, mtx9}, rest, Facts.Facts.crit(s))(ok))

# the state m, if any, is the state x
def Put.Ok(x: Maybe<&2, RLines.State>, m: Maybe<&2, RLines.State>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{st}:
      {x == Some{st}: Maybe<&2, RLines.State>}

# a right table with a state of a line, if any, that is the state that the
# facts give the line, is right
def Known.put_fits(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  m: Maybe<&2, RLines.State>
) -> Put.Ok(
  RLines.Line.state(s, c),
  m
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {RContents.Known.ok(RKnown.Known.put(kn, c, m), s) == True{}: Bool}:
  match m:
    case None{}:
      e => ok => ok
    case Some{+st}:
      e => ok => Shared.Bool.and_both(
        RKnown.State.fits(RLines.Line.state(s, c), st),
        RContents.Known.ok(kn, s)
      )(State.fits_of(RLines.Line.state(s, c), st)(e))(ok)

# what is known of a state that the table holds: a state that is some state
# is not none, so it is what the facts give
def Known.have(
  -A: Data,
  -m: Maybe<&2, RLines.State>,
  -x: Maybe<&2, RLines.State>,
  -st: RLines.State,
  e: {Some{st} == None{}: Maybe<&2, RLines.State>} | {x == Some{st}: Maybe<&2, RLines.State>}
) -> {x == Some{st}: Maybe<&2, RLines.State>}:
  match e:
    case Inl{n}:
      Empty.absurd(
        {x == Some{st}: Maybe<&2, RLines.State>},
        Shared.Maybe.none_ne_some(
          RLines.State,
          st,
          Equal.sym(Maybe<&2, RLines.State>, Some{st}, None{}, n)
        )
      )
    case Inr{y}:
      y

# the state that a vote for the slot k of the line c continues, from the
# state m of c and the state ms of its store in the facts before the vote,
# is the state of c after the vote
def Known.next_ok(
  +name: String,
  +s: Facts.Facts(),
  c: Ledgers.Line,
  +k: Nat,
  +t: Nat,
  +x: Types.Cast,
  m: Maybe<&2, RLines.State>,
  ms: Maybe<&2, RLines.State>
) -> (
  {m == None{}: Maybe<&2, RLines.State>} | {Lines.Line.state(s, c) == m: Maybe<&2, RLines.State>}
) -> (
  {
    ms == None{}: Maybe<&2, RLines.State>
  }
    | {Lines.Line.state(s, RKnown.Known.root(c)) == ms: Maybe<&2, RLines.State>}
) -> Put.Ok(
  Lines.Line.state(Moves.Delta.to(Moves.Delta.Vote{name, c, k, t, x}, s), c),
  RKnown.Known.next.of(
    None{},
    Facts.Facts.crit(Moves.Delta.to(Moves.Delta.Vote{name, c, k, t, x}, s)),
    c,
    k,
    m,
    RKnown.Known.over(c, ms)
  )
):
  match c m ms:
    case Ledgers.Line{h, None{}} None{} None{}:
      e => es => Unit{}
    case Ledgers.Line{h, None{}} None{} Some{y}:
      e => es => Unit{}
    case Ledgers.Line{h, Some{b}} None{} None{}:
      e => es => Unit{}
    case Ledgers.Line{h, Some{b}} None{} Some{RLines.State{R, j}}:
      e => es => Unit{}
    case Ledgers.Line{h, Some{b}} Some{st} None{}:
      e => es => Unit{}
    case Ledgers.Line{+h, None{}} Some{+st} None{}:
      e => es => Lists.Bool.by(
        y => Put.Ok(
          Lines.Line.state(
            Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, None{}}, k, t, x}, s),
            Ledgers.Line{h, None{}}
          ),
          Shared.Maybe.when(
            RLines.State,
            y,
            u => Some{
              RKnown.Known.go.at(
                Facts.Facts.crit(
                  Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, None{}}, k, t, x}, s)
                ),
                Ledgers.Line{h, None{}},
                st,
                None{}
              )
            }
          )
        ),
        Nat.is_eq(RLines.State.slot(st), k),
        et => (
          %Shared.Nat.is_eq_sound(RLines.State.slot(st), k)(et): {Lines.Line.state(Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, None{}}, _, t, x}, s), Ledgers.Line{h, None{}}) == Some{RKnown.Known.go.at(Facts.Facts.crit(Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, None{}}, _, t, x}, s)), Ledgers.Line{h, None{}}, st, None{})}: Maybe<&2, RLines.State>}
          Store.state_cast(name, s, h, t, x, st)(Known.have(Maybe<&2, RLines.State>, Some{st}, Lines.Store.state(s, h), st, e))),
        ef => Unit{}
      )
    case Ledgers.Line{+h, None{}} Some{+st} Some{y}:
      e => es => Lists.Bool.by(
        y => Put.Ok(
          Lines.Line.state(
            Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, None{}}, k, t, x}, s),
            Ledgers.Line{h, None{}}
          ),
          Shared.Maybe.when(
            RLines.State,
            y,
            u => Some{
              RKnown.Known.go.at(
                Facts.Facts.crit(
                  Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, None{}}, k, t, x}, s)
                ),
                Ledgers.Line{h, None{}},
                st,
                None{}
              )
            }
          )
        ),
        Nat.is_eq(RLines.State.slot(st), k),
        et => (
          %Shared.Nat.is_eq_sound(RLines.State.slot(st), k)(et): {Lines.Line.state(Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, None{}}, _, t, x}, s), Ledgers.Line{h, None{}}) == Some{RKnown.Known.go.at(Facts.Facts.crit(Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, None{}}, _, t, x}, s)), Ledgers.Line{h, None{}}, st, None{})}: Maybe<&2, RLines.State>}
          Store.state_cast(name, s, h, t, x, st)(Known.have(Maybe<&2, RLines.State>, Some{st}, Lines.Store.state(s, h), st, e))),
        ef => Unit{}
      )
    case Ledgers.Line{+h, Some{+b}} Some{+st} Some{RLines.State{+R, +j}}:
      e => es => Lists.Bool.by(
        y => Put.Ok(
          Lines.Line.state(
            Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, Some{b}}, k, t, x}, s),
            Ledgers.Line{h, Some{b}}
          ),
          Shared.Maybe.when(
            RLines.State,
            y,
            u => Some{
              RKnown.Known.go.at(
                Facts.Facts.crit(
                  Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, Some{b}}, k, t, x}, s)
                ),
                Ledgers.Line{h, Some{b}},
                st,
                Some{R}
              )
            }
          )
        ),
        Nat.is_eq(RLines.State.slot(st), k),
        et => (
          %Shared.Nat.is_eq_sound(RLines.State.slot(st), k)(et): {Lines.Line.state(Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, Some{b}}, _, t, x}, s), Ledgers.Line{h, Some{b}}) == Some{RKnown.Known.go.at(Facts.Facts.crit(Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, Some{b}}, _, t, x}, s)), Ledgers.Line{h, Some{b}}, st, Some{R})}: Maybe<&2, RLines.State>}
          Branch.state_cast(name, s, h, b, t, x, R, j, st)(Known.have(Maybe<&2, RLines.State>, Some{st}, Lines.Line.state(s, Ledgers.Line{h, Some{b}}), st, e))(Known.have(Maybe<&2, RLines.State>, Some{RLines.State{R, j}}, Lines.Store.state(s, h), RLines.State{R, j}, es))),
        ef => Unit{}
      )

# the state that a right table holds for a line, if any, is the state that
# the facts give the line
def Known.found(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> (
  {
    RKnown.Known.find(kn, c) == None{}: Maybe<&2, RLines.State>
  }
    | {RLines.Line.state(s, c) == RKnown.Known.find(kn, c): Maybe<&2, RLines.State>}
):
  ok => Lists.Maybe.by(
    RLines.State,
    m => (
      {
        m == None{}: Maybe<&2, RLines.State>
      }
        | {RLines.Line.state(s, c) == m: Maybe<&2, RLines.State>}
    ),
    RKnown.Known.find(kn, c),
    en => Inl{{==}},
    +y => ey => Inr{Known.find_ok(kn, s, c, y)(ok)(ey)}
  )

# two right tables, one after the other, are a right table
def Ok.append(
  a: RKnown.Known(),
  +b: RKnown.Known(),
  +s: RFacts.Plain()
) -> {
  RContents.Known.ok(a, s) == True{}: Bool
} -> {
  RContents.Known.ok(b, s) == True{}: Bool
} -> {RContents.Known.ok(List.append(&2, RKnown.Kept, a, b), s) == True{}: Bool}:
  match a:
    case Nil{}:
      ha => hb => hb
    case Con{+e, +rest}:
      +ha => hb => Ok.cons(
        e,
        List.append(&2, RKnown.Kept, rest, b),
        s
      )(Ok.head(e, rest, s)(ha))(Ok.append(rest, b, s)(Ok.tail(e, rest, s)(ha))(hb))

# a ballot that is safe by the states m and ms that a right table holds is
# safe by the states x and xs that the facts give
def Safe.found(
  c: Ledgers.Line,
  m: Maybe<&2, RLines.State>,
  ms: Maybe<&2, RLines.State>,
  -x: Maybe<&2, RLines.State>,
  -xs: Maybe<&2, RLines.State>,
  -k: Nat
) -> (
  {m == None{}: Maybe<&2, RLines.State>} | {x == m: Maybe<&2, RLines.State>}
) -> (
  {ms == None{}: Maybe<&2, RLines.State>} | {xs == ms: Maybe<&2, RLines.State>}
) -> {
  RKnown.Known.safe(c, m, ms, k) == True{}: Bool
} -> {RKnown.Known.safe(c, x, xs, k) == True{}: Bool}:
  match c m ms:
    case Ledgers.Line{h, None{}} m ms:
      a => b => hs => Empty.absurd(
        {RKnown.Known.safe(Ledgers.Line{h, None{}}, x, xs, k) == True{}: Bool},
        Shared.Bool.false_ne_true(hs)
      )
    case Ledgers.Line{h, Some{b0}} None{} ms:
      a => b => hs => Empty.absurd(
        {RKnown.Known.safe(Ledgers.Line{h, Some{b0}}, x, xs, k) == True{}: Bool},
        Shared.Bool.false_ne_true(hs)
      )
    case Ledgers.Line{h, Some{b0}} Some{st} None{}:
      a => b => hs => Empty.absurd(
        {RKnown.Known.safe(Ledgers.Line{h, Some{b0}}, x, xs, k) == True{}: Bool},
        Shared.Bool.false_ne_true(hs)
      )
    case Ledgers.Line{h, Some{b0}} Some{st} Some{y}:
      a => b => hs => (
        %Equal.sym(Maybe<&2, RLines.State>, x, Some{st}, Known.have(Maybe<&2, RLines.State>, Some{st}, x, st, a)): {RKnown.Known.safe(Ledgers.Line{h, Some{b0}}, _, xs, k) == True{}: Bool}
        %Equal.sym(Maybe<&2, RLines.State>, xs, Some{y}, Known.have(Maybe<&2, RLines.State>, Some{y}, xs, y, b)): {RKnown.Known.safe(Ledgers.Line{h, Some{b0}}, Some{st}, _, k) == True{}: Bool}
        hs)

# the contents that a ballot spares of a table that is right for the facts s
# are right for the facts with the ballot
def Known.spared_ok(
  +kn: RKnown.Known(),
  +name: String,
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +t: Nat,
  +x: Types.Cast
) -> {
  RContents.Known.ok(kn, Facts.Facts.crit(s)) == True{}: Bool
} -> {
  Facts.Facts.has(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}) == False{}: Bool
} -> {
  RContents.Known.ok(
    RKnown.Known.spared(
      RKnown.Known.safe(
        c,
        RKnown.Known.find(kn, c),
        RKnown.Known.find(kn, RKnown.Known.root(c)),
        k
      ),
      kn
    ),
    Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))
  )
    == True{}: Bool
}:
  +ok => hf => Lists.Bool.by(
    y => {
      RContents.Known.ok(
        RKnown.Known.spared(y, kn),
        Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))
      )
        == True{}: Bool
    },
    RKnown.Known.safe(c, RKnown.Known.find(kn, c), RKnown.Known.find(kn, RKnown.Known.root(c)), k),
    et => Known.spared_kept(
      kn,
      name,
      s,
      c,
      k,
      t,
      x
    )(
      Safe.found(
        c,
        RKnown.Known.find(kn, c),
        RKnown.Known.find(kn, RKnown.Known.root(c)),
        Lines.Line.state(s, c),
        Lines.Line.state(s, RKnown.Known.root(c)),
        k
      )(
        Known.found(kn, Facts.Facts.crit(s), c)(ok)
      )(Known.found(kn, Facts.Facts.crit(s), RKnown.Known.root(c))(ok))(et)
    )(hf)(ok),
    ef => {==}
  )

# the ids m, if any, fit the state x
def Made.Ok(x: Maybe<&2, RLines.State>, m: Maybe<&2, RKnown.Ids>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{y}:
      {RKnown.Made.fits(x, y) == True{}: Bool}

# a right table with ids, if any, that fit the state that the facts give a
# line, is right
def Known.made_put_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  m: Maybe<&2, RKnown.Ids>
) -> Made.Ok(
  RLines.Line.state(s, c),
  m
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {RContents.Known.ok(RKnown.Known.made.put(kn, c, m), s) == True{}: Bool}:
  match m:
    case None{}:
      e => ok => ok
    case Some{+y}:
      e => ok => Ok.cons(RKnown.Made{c, y}, kn, s)(e)(ok)

# the ids that a right table holds for a line, if any, fit the state that
# the facts give the line
def Known.ids_found(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> Made.Ok(RLines.Line.state(s, c), RKnown.Known.ids(kn, c)):
  ok => Lists.Maybe.by(
    RKnown.Ids,
    m => Made.Ok(RLines.Line.state(s, c), m),
    RKnown.Known.ids(kn, c),
    en => Unit{},
    +y => ey => Known.ids_ok(kn, s, c, y)(ok)(ey)
  )

# the versions of the state m extend those of the state old, if both are
# known
def Grow.Ok(old: Maybe<&2, RLines.State>, m: Maybe<&2, RLines.State>) -> Type:
  match old m:
    case Some{st} Some{st2}:
      Lists.List.Ext(Types.Entry, RLines.State.versions(st), RLines.State.versions(st2))
    case Some{st} None{}:
      Unit
    case None{} m:
      Unit

# the versions of the state that a vote continues extend those of the state
# that it continues
def Next.grows(
  +name: String,
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +t: Nat,
  +x: Types.Cast,
  old: Maybe<&2, RLines.State>,
  r: Maybe<&2, Maybe<&2, List<&2, Types.Entry>>>
) -> Grow.Ok(
  old,
  RKnown.Known.next.of(
    None{},
    Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})),
    c,
    k,
    old,
    r
  )
):
  match old r:
    case Some{+st} Some{+rr}:
      Lists.Bool.by(
        y => Grow.Ok(
          Some{st},
          Shared.Maybe.when(
            RLines.State,
            y,
            u => Some{
              RKnown.Known.go.at(
                Facts.Facts.crit(
                  Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})
                ),
                c,
                st,
                rr
              )
            }
          )
        ),
        Nat.is_eq(RLines.State.slot(st), k),
        et => Moves.Run.grows(
          1n+RLines.Line.bound(
            Facts.Facts.list(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})),
            c
          ),
          Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}),
          rr,
          c,
          st
        ),
        ef => Unit{}
      )
    case Some{st} None{}:
      Unit{}
    case None{} Some{rr}:
      Unit{}
    case None{} None{}:
      Unit{}

# Made.next_ok, when the three are known
def Made.next_ok.at(
  +vs2: List<&2, Types.Entry>,
  +k2: Nat,
  +vs: List<&2, Types.Entry>,
  +k: Nat,
  +y: RKnown.Ids,
  -x2: Maybe<&2, RLines.State>,
  -x1: Maybe<&2, RLines.State>,
  a: {x2 == Some{RLines.State{vs2, k2}}: Maybe<&2, RLines.State>},
  b: {x1 == Some{RLines.State{vs, k}}: Maybe<&2, RLines.State>},
  i: {RKnown.Made.fits(x1, y) == True{}: Bool},
  d: Lists.List.Ext(Types.Entry, vs, vs2)
) -> {RKnown.Made.fits(x2, RKnown.Ids.go(RKnown.Entries.past(vs, vs2), y)) == True{}: Bool}:
  match d:
    case Tuple{+zs, e}:
      %Equal.sym(
        Maybe<&2, RLines.State>,
        x2,
        Some{RLines.State{vs2, k2}},
        a
      ): {RKnown.Made.fits(_, RKnown.Ids.go(RKnown.Entries.past(vs, vs2), y)) == True{}: Bool}
      %Equal.sym(
        List<&2, Types.Entry>,
        vs2,
        List.append(&2, Types.Entry, vs, zs),
        e
      ): {
        RKnown.Ids.same(
          RKnown.Ids.go(RKnown.Entries.past(vs, _), y),
          RKnown.Ids.of(_)
        )
          == True{}: Bool
      }
      %Equal.sym(
        RKnown.Ids,
        y,
        RKnown.Ids.of(vs),
        Made.fits_sound(x1, y, vs, k)(b)(i)
      ): {
        RKnown.Ids.same(
          RKnown.Ids.go(RKnown.Entries.past(vs, List.append(&2, Types.Entry, vs, zs)), _),
          RKnown.Ids.of(List.append(&2, Types.Entry, vs, zs))
        )
          == True{}: Bool
      }
      %Equal.sym(
        List<&2, Types.Entry>,
        RKnown.Entries.past(vs, List.append(&2, Types.Entry, vs, zs)),
        zs,
        Past.append(vs, zs)
      ): {
        RKnown.Ids.same(
          RKnown.Ids.go(_, RKnown.Ids.of(vs)),
          RKnown.Ids.of(List.append(&2, Types.Entry, vs, zs))
        )
          == True{}: Bool
      }
      %Ids.go_append(
        vs,
        zs,
        RKnown.Ids.new()
      ): {RKnown.Ids.same(_, RKnown.Ids.of(List.append(&2, Types.Entry, vs, zs))) == True{}: Bool}
      Ids.same_refl(RKnown.Ids.of(List.append(&2, Types.Entry, vs, zs)))

# the ids that a vote continues fit the state after the vote: m is the state
# x2 after the vote, old the state x1 before it, that m extends, and ids fit
# x1
def Made.next_ok(
  m: Maybe<&2, RLines.State>,
  old: Maybe<&2, RLines.State>,
  ids: Maybe<&2, RKnown.Ids>,
  -x2: Maybe<&2, RLines.State>,
  -x1: Maybe<&2, RLines.State>
) -> Put.Ok(
  x2,
  m
) -> (
  {old == None{}: Maybe<&2, RLines.State>} | {x1 == old: Maybe<&2, RLines.State>}
) -> Made.Ok(x1, ids) -> Grow.Ok(old, m) -> Made.Ok(x2, RKnown.Made.next(m, old, ids)):
  match m old ids:
    case None{} None{} None{}:
      a => b => i => d => Unit{}
    case None{} None{} Some{y}:
      a => b => i => d => Unit{}
    case None{} Some{RLines.State{vs, k}} None{}:
      a => b => i => d => Unit{}
    case None{} Some{RLines.State{vs, k}} Some{y}:
      a => b => i => d => Unit{}
    case Some{RLines.State{vs2, k2}} None{} None{}:
      a => b => i => d => Unit{}
    case Some{RLines.State{vs2, k2}} None{} Some{y}:
      a => b => i => d => Unit{}
    case Some{RLines.State{vs2, k2}} Some{RLines.State{vs, k}} None{}:
      a => b => i => d => Unit{}
    case Some{RLines.State{+vs2, +k2}} Some{RLines.State{+vs, +k}} Some{+y}:
      a => b => i => d => Made.next_ok.at(
        vs2,
        k2,
        vs,
        k,
        y,
        x2,
        x1,
        a,
        Known.have(Maybe<&2, RLines.State>, Some{RLines.State{vs, k}}, x1, RLines.State{vs, k}, b),
        i,
        d
      )

# a table that is right for the facts s, after a ballot for the slot k of
# the line c (without the states that the ballot may change, and with the
# state of c continued from its known state), is right for the facts with
# the ballot
def Known.cast_ok(
  +kn: RKnown.Known(),
  +name: String,
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +t: Nat,
  +x: Types.Cast
) -> {
  RContents.Known.ok(kn, Facts.Facts.crit(s)) == True{}: Bool
} -> {
  Facts.Facts.has(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}) == False{}: Bool
} -> {
  RContents.Known.ok(
    RKnown.Known.cast.plain(
      kn,
      Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})),
      c,
      k,
      None{}
    ),
    Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))
  )
    == True{}: Bool
}:
  +ok => hf => Known.made_put_ok(
    RKnown.Known.put(
      List.append(
        &2,
        RKnown.Kept,
        RKnown.Known.voted(kn, c),
        RKnown.Known.spared(
          RKnown.Known.safe(
            c,
            RKnown.Known.find(kn, c),
            RKnown.Known.find(kn, RKnown.Known.root(c)),
            k
          ),
          kn
        )
      ),
      c,
      RKnown.Known.next.of(
        None{},
        Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})),
        c,
        k,
        RKnown.Known.find(kn, c),
        RKnown.Known.over(c, RKnown.Known.find(kn, RKnown.Known.root(c)))
      )
    ),
    Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})),
    c,
    RKnown.Made.next(
      RKnown.Known.next.of(
        None{},
        Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})),
        c,
        k,
        RKnown.Known.find(kn, c),
        RKnown.Known.over(c, RKnown.Known.find(kn, RKnown.Known.root(c)))
      ),
      RKnown.Known.find(kn, c),
      RKnown.Known.ids(kn, c)
    )
  )(
    Made.next_ok(
      RKnown.Known.next.of(
        None{},
        Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})),
        c,
        k,
        RKnown.Known.find(kn, c),
        RKnown.Known.over(c, RKnown.Known.find(kn, RKnown.Known.root(c)))
      ),
      RKnown.Known.find(kn, c),
      RKnown.Known.ids(kn, c),
      RLines.Line.state(
        Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})),
        c
      ),
      RLines.Line.state(Facts.Facts.crit(s), c)
    )(
      Known.next_ok(
        name,
        s,
        c,
        k,
        t,
        x,
        RKnown.Known.find(kn, c),
        RKnown.Known.find(kn, RKnown.Known.root(c))
      )(
        Known.found(kn, Facts.Facts.crit(s), c)(ok)
      )(Known.found(kn, Facts.Facts.crit(s), RKnown.Known.root(c))(ok))
    )(
      Known.found(kn, Facts.Facts.crit(s), c)(ok)
    )(
      Known.ids_found(kn, Facts.Facts.crit(s), c)(ok)
    )(
      Next.grows(
        name,
        s,
        c,
        k,
        t,
        x,
        RKnown.Known.find(kn, c),
        RKnown.Known.over(c, RKnown.Known.find(kn, RKnown.Known.root(c)))
      )
    )
  )(
    Known.put_fits(
      List.append(
        &2,
        RKnown.Kept,
        RKnown.Known.voted(kn, c),
        RKnown.Known.spared(
          RKnown.Known.safe(
            c,
            RKnown.Known.find(kn, c),
            RKnown.Known.find(kn, RKnown.Known.root(c)),
            k
          ),
          kn
        )
      ),
      Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})),
      c,
      RKnown.Known.next.of(
        None{},
        Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})),
        c,
        k,
        RKnown.Known.find(kn, c),
        RKnown.Known.over(c, RKnown.Known.find(kn, RKnown.Known.root(c)))
      )
    )(
      Known.next_ok(
        name,
        s,
        c,
        k,
        t,
        x,
        RKnown.Known.find(kn, c),
        RKnown.Known.find(kn, RKnown.Known.root(c))
      )(
        Known.found(kn, Facts.Facts.crit(s), c)(ok)
      )(Known.found(kn, Facts.Facts.crit(s), RKnown.Known.root(c))(ok))
    )(
      Ok.append(
        RKnown.Known.voted(kn, c),
        RKnown.Known.spared(
          RKnown.Known.safe(
            c,
            RKnown.Known.find(kn, c),
            RKnown.Known.find(kn, RKnown.Known.root(c)),
            k
          ),
          kn
        ),
        Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))
      )(
        Known.voted_ok(kn, name, s, c, k, t, x)(ok)
      )(Known.spared_ok(kn, name, s, c, k, t, x)(ok)(hf))
    )
  )

# The facts that a work may act on stay right
# -------------------------------------------
# What a node learns goes before the facts that its table holds for a work,
# or after its states: the table holds the same facts for a work. A ballot
# drops them. An ask joins them. A ballot for the next slot of a branch
# joins them, and those that wait no more leave.

# a table with a state holds the same facts for a work
def Known.put_open(
  -kn: RKnown.Known(),
  -c: Ledgers.Line,
  m: Maybe<&2, RLines.State>
) -> {
  RKnown.Known.shelf(kn) == RKnown.Known.shelf(RKnown.Known.put(kn, c, m)): Maybe<&2, RKnown.Kept>
}:
  match m:
    case None{}:
      {==}
    case Some{st}:
      {==}

# a table that learns a state, unless it holds it (old), holds the same facts
# for a work
def Known.learn_of_open(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  old: Maybe<&2, RLines.State>
) -> {
  RKnown.Known.shelf(
    kn
  )
    == RKnown.Known.shelf(RKnown.Known.learn.of(kn, s, c, old)): Maybe<&2, RKnown.Kept>
}:
  match old:
    case Some{st}:
      {==}
    case None{}:
      Known.put_open(kn, c, RKnown.Known.fresh(kn, s, c))

# a table with a rule holds the same facts for a work
def Known.rule_put_open(
  -kn: RKnown.Known(),
  -c: Ledgers.Line,
  -n: Nat,
  m: Maybe<&2, RLines.Rule>
) -> {
  RKnown.Known.shelf(
    kn
  )
    == RKnown.Known.shelf(RKnown.Known.rule.put(kn, c, n, m)): Maybe<&2, RKnown.Kept>
}:
  match m:
    case None{}:
      {==}
    case Some{u}:
      {==}

# a table that learns a rule, unless it holds it (old), holds the same facts
# for a work
def Known.rule_learn_open(
  old: Bool,
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line
) -> {
  RKnown.Known.shelf(
    kn
  )
    == RKnown.Known.shelf(RKnown.Known.rule.learn.if(old, kn, s, c)): Maybe<&2, RKnown.Kept>
}:
  match old:
    case True{}:
      {==}
    case False{}:
      Known.rule_put_open(
        kn,
        c,
        RKnown.Era.next(c, RKnown.Known.find(kn, c)),
        RKnown.Known.rule.next(kn, s, c, RKnown.Known.find(kn, c))
      )

# a table with the ids of the versions of a state holds the same facts for a
# work
def Known.ids_put_open(
  -kn: RKnown.Known(),
  -c: Ledgers.Line,
  m: Maybe<&2, RLines.State>
) -> {
  RKnown.Known.shelf(
    kn
  )
    == RKnown.Known.shelf(RKnown.Known.ids.put(kn, c, m)): Maybe<&2, RKnown.Kept>
}:
  match m:
    case None{}:
      {==}
    case Some{RLines.State{vs, k}}:
      {==}

# a table that learns the ids of the versions of a line, unless it holds
# them (old), holds the same facts for a work
def Known.ids_learn_open(
  old: Bool,
  +kn: RKnown.Known(),
  +c: Ledgers.Line
) -> {
  RKnown.Known.shelf(
    kn
  )
    == RKnown.Known.shelf(RKnown.Known.ids.learn.if(old, kn, c)): Maybe<&2, RKnown.Kept>
}:
  match old:
    case True{}:
      {==}
    case False{}:
      Known.ids_put_open(kn, c, RKnown.Known.find(kn, c))

# a table that learns a line holds the same facts for a work
def Known.learn_open(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line
) -> {
  RKnown.Known.shelf(kn) == RKnown.Known.shelf(RKnown.Known.learn(kn, s, c)): Maybe<&2, RKnown.Kept>
}:
  Equal.trans(
    Maybe<&2, RKnown.Kept>,
    RKnown.Known.shelf(kn),
    RKnown.Known.shelf(RKnown.Known.learn.one(kn, s, RKnown.Known.root(c))),
    RKnown.Known.shelf(RKnown.Known.learn(kn, s, c)),
    Known.learn_of_open(kn, s, RKnown.Known.root(c), RKnown.Known.find(kn, RKnown.Known.root(c))),
    Equal.trans(
      Maybe<&2, RKnown.Kept>,
      RKnown.Known.shelf(RKnown.Known.learn.one(kn, s, RKnown.Known.root(c))),
      RKnown.Known.shelf(
        RKnown.Known.learn.one(RKnown.Known.learn.one(kn, s, RKnown.Known.root(c)), s, c)
      ),
      RKnown.Known.shelf(RKnown.Known.learn(kn, s, c)),
      Known.learn_of_open(
        RKnown.Known.learn.one(kn, s, RKnown.Known.root(c)),
        s,
        c,
        RKnown.Known.find(RKnown.Known.learn.one(kn, s, RKnown.Known.root(c)), c)
      ),
      Equal.trans(
        Maybe<&2, RKnown.Kept>,
        RKnown.Known.shelf(
          RKnown.Known.learn.one(RKnown.Known.learn.one(kn, s, RKnown.Known.root(c)), s, c)
        ),
        RKnown.Known.shelf(
          RKnown.Known.rule.learn(
            RKnown.Known.learn.one(RKnown.Known.learn.one(kn, s, RKnown.Known.root(c)), s, c),
            s,
            c
          )
        ),
        RKnown.Known.shelf(RKnown.Known.learn(kn, s, c)),
        Known.rule_learn_open(
          Maybe.is_some(
            &2,
            RLines.Rule,
            RKnown.Known.ruled(
              RKnown.Known.learn.one(RKnown.Known.learn.one(kn, s, RKnown.Known.root(c)), s, c),
              c
            )
          ),
          RKnown.Known.learn.one(RKnown.Known.learn.one(kn, s, RKnown.Known.root(c)), s, c),
          s,
          c
        ),
        Known.ids_learn_open(
          Maybe.is_some(
            &2,
            RKnown.Ids,
            RKnown.Known.ids(
              RKnown.Known.rule.learn(
                RKnown.Known.learn.one(RKnown.Known.learn.one(kn, s, RKnown.Known.root(c)), s, c),
                s,
                c
              ),
              c
            )
          ),
          RKnown.Known.rule.learn(
            RKnown.Known.learn.one(RKnown.Known.learn.one(kn, s, RKnown.Known.root(c)), s, c),
            s,
            c
          ),
          c
        )
      )
    )
  )

# a table that fits, after it learns a line, fits
def Known.learn_fit(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line
) -> {
  RContents.Known.fit(kn, s) == True{}: Bool
} -> {RContents.Known.fit(RKnown.Known.learn(kn, s, c), s) == True{}: Bool}:
  +h => Fit.both(RKnown.Known.learn(kn, s, c), s)(Known.learn_ok(kn, s, c)(Fit.ok(kn, s)(h)))((
      %Known.learn_open(kn, s, c): {RContents.Shelf.fits(_, s) == True{}: Bool}
      Fit.open(kn, s)(h)))

# a table with a content holds the same facts for a work
def Known.hold_open(
  kn: RKnown.Known(),
  +c: Ledgers.Line,
  +k: Nat,
  +d: Nat,
  +x: RFiles.Files()
) -> {
  RKnown.Known.shelf(
    kn
  )
    == RKnown.Known.shelf(RKnown.Known.hold(kn, RKnown.Held{c, k, d, x})): Maybe<&2, RKnown.Kept>
}:
  match kn:
    case Nil{}:
      {==}
    case Con{RKnown.Kept{c2, st2}, rest}:
      Known.hold_open(rest, c, k, d, x)
    case Con{RKnown.Stock{m2, lwm2}, rest}:
      {==}
    case Con{RKnown.Ruled{c2, zu2, u2}, rest}:
      Known.hold_open(rest, c, k, d, x)
    case Con{RKnown.Made{c2, y2}, rest}:
      Known.hold_open(rest, c, k, d, x)
    case Con{RKnown.Open{fs2, pk2, tx9, mtx9}, rest}:
      {==}

# a table with the content m, if any, holds the same facts for a work
def Known.fill_of_open(
  +kn: RKnown.Known(),
  +c: Ledgers.Line,
  +k: Nat,
  +d: Nat,
  m: Maybe<&2, RFiles.Files()>
) -> {
  RKnown.Known.shelf(
    kn
  )
    == RKnown.Known.shelf(RContents.Known.fill.of(kn, c, k, d, m)): Maybe<&2, RKnown.Kept>
}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      Known.hold_open(kn, c, k, d, x)

# a table with the content of the version after j, made by the request r,
# holds the same facts for a work
def Known.fill_write_open(
  r: Spec.Request,
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +j: Nat,
  +d: Nat,
  +x: RFiles.Files()
) -> {
  RKnown.Known.shelf(
    kn
  )
    == RKnown.Known.shelf(RContents.Known.fill.write(r, kn, s, c, j, d, x)): Maybe<&2, RKnown.Kept>
}:
  match r:
    case Spec.Request.Start{os}:
      Known.fill_of_open(
        kn,
        c,
        1n+j,
        RContents.Fill.fuel(
          1n+j,
          kn,
          c,
          RKnown.Known.at(kn, s, c, 1n+j),
          u => RFacts.Facts.fuel(s)
        ),
        RContents.Content.at(
          RContents.Fill.fuel(
            1n+j,
            kn,
            c,
            RKnown.Known.at(kn, s, c, 1n+j),
            u => RFacts.Facts.fuel(s)
          ),
          kn,
          s,
          c,
          1n+j
        )
      )
    case Spec.Request.Write{b, +p, +w}:
      Known.fill_of_open(kn, c, 1n+j, 1n+d, Some{RFiles.Files.set(x, p, w)})
    case Spec.Request.Merge{f, y}:
      Known.fill_of_open(
        kn,
        c,
        1n+j,
        RContents.Fill.fuel(
          1n+j,
          kn,
          c,
          RKnown.Known.at(kn, s, c, 1n+j),
          u => RFacts.Facts.fuel(s)
        ),
        RContents.Content.at(
          RContents.Fill.fuel(
            1n+j,
            kn,
            c,
            RKnown.Known.at(kn, s, c, 1n+j),
            u => RFacts.Facts.fuel(s)
          ),
          kn,
          s,
          c,
          1n+j
        )
      )
    case Spec.Request.Resolve{m, +p, +w}:
      Known.fill_of_open(kn, c, 1n+j, 1n+d, Some{RFiles.Files.set(x, p, w)})
    case Spec.Request.Mark{b, m, v}:
      Known.fill_of_open(
        kn,
        c,
        1n+j,
        RContents.Fill.fuel(
          1n+j,
          kn,
          c,
          RKnown.Known.at(kn, s, c, 1n+j),
          u => RFacts.Facts.fuel(s)
        ),
        RContents.Content.at(
          RContents.Fill.fuel(
            1n+j,
            kn,
            c,
            RKnown.Known.at(kn, s, c, 1n+j),
            u => RFacts.Facts.fuel(s)
          ),
          kn,
          s,
          c,
          1n+j
        )
      )
    case Spec.Request.Move{b, t, v}:
      Known.fill_of_open(
        kn,
        c,
        1n+j,
        RContents.Fill.fuel(
          1n+j,
          kn,
          c,
          RKnown.Known.at(kn, s, c, 1n+j),
          u => RFacts.Facts.fuel(s)
        ),
        RContents.Content.at(
          RContents.Fill.fuel(
            1n+j,
            kn,
            c,
            RKnown.Known.at(kn, s, c, 1n+j),
            u => RFacts.Facts.fuel(s)
          ),
          kn,
          s,
          c,
          1n+j
        )
      )
    case Spec.Request.Group{h, g, ms}:
      Known.fill_of_open(
        kn,
        c,
        1n+j,
        RContents.Fill.fuel(
          1n+j,
          kn,
          c,
          RKnown.Known.at(kn, s, c, 1n+j),
          u => RFacts.Facts.fuel(s)
        ),
        RContents.Content.at(
          RContents.Fill.fuel(
            1n+j,
            kn,
            c,
            RKnown.Known.at(kn, s, c, 1n+j),
            u => RFacts.Facts.fuel(s)
          ),
          kn,
          s,
          c,
          1n+j
        )
      )
    case Spec.Request.Own{b, g}:
      Known.fill_of_open(
        kn,
        c,
        1n+j,
        RContents.Fill.fuel(
          1n+j,
          kn,
          c,
          RKnown.Known.at(kn, s, c, 1n+j),
          u => RFacts.Facts.fuel(s)
        ),
        RContents.Content.at(
          RContents.Fill.fuel(
            1n+j,
            kn,
            c,
            RKnown.Known.at(kn, s, c, 1n+j),
            u => RFacts.Facts.fuel(s)
          ),
          kn,
          s,
          c,
          1n+j
        )
      )

# a table with the content of the version after j holds the same facts for a
# work
def Known.fill_next_open(
  prev: Maybe<&2, RKnown.Held>,
  e: Maybe<&2, Types.Entry>,
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +j: Nat
) -> {
  RKnown.Known.shelf(
    kn
  )
    == RKnown.Known.shelf(RContents.Known.fill.next(prev, e, kn, s, c, j)): Maybe<&2, RKnown.Kept>
}:
  match prev e:
    case Some{
      RKnown.Held{c2, k2, +d, +x}
    } Some{Types.Entry{Types.Pick{Types.Ask{i, n, r}, pins}, slot}}:
      Known.fill_write_open(r, kn, s, c, j, d, x)
    case None{} None{}:
      Known.fill_of_open(
        kn,
        c,
        1n+j,
        RContents.Fill.fuel(
          1n+j,
          kn,
          c,
          RKnown.Known.at(kn, s, c, 1n+j),
          u => RFacts.Facts.fuel(s)
        ),
        RContents.Content.at(
          RContents.Fill.fuel(
            1n+j,
            kn,
            c,
            RKnown.Known.at(kn, s, c, 1n+j),
            u => RFacts.Facts.fuel(s)
          ),
          kn,
          s,
          c,
          1n+j
        )
      )
    case None{} Some{Types.Entry{Types.Pick{Types.Ask{i, n, r}, pins}, slot}}:
      Known.fill_of_open(
        kn,
        c,
        1n+j,
        RContents.Fill.fuel(
          1n+j,
          kn,
          c,
          RKnown.Known.at(kn, s, c, 1n+j),
          u => RFacts.Facts.fuel(s)
        ),
        RContents.Content.at(
          RContents.Fill.fuel(
            1n+j,
            kn,
            c,
            RKnown.Known.at(kn, s, c, 1n+j),
            u => RFacts.Facts.fuel(s)
          ),
          kn,
          s,
          c,
          1n+j
        )
      )
    case Some{RKnown.Held{c2, k2, d, x}} None{}:
      Known.fill_of_open(
        kn,
        c,
        1n+j,
        RContents.Fill.fuel(
          1n+j,
          kn,
          c,
          RKnown.Known.at(kn, s, c, 1n+j),
          u => RFacts.Facts.fuel(s)
        ),
        RContents.Content.at(
          RContents.Fill.fuel(
            1n+j,
            kn,
            c,
            RKnown.Known.at(kn, s, c, 1n+j),
            u => RFacts.Facts.fuel(s)
          ),
          kn,
          s,
          c,
          1n+j
        )
      )

# a table that learns a content, unless it holds it (old), holds the same
# facts for a work
def Known.fill_if_open(
  old: Bool,
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  k: Nat
) -> {
  RKnown.Known.shelf(
    kn
  )
    == RKnown.Known.shelf(RContents.Known.fill.if(old, kn, s, c, k)): Maybe<&2, RKnown.Kept>
}:
  match old k:
    case True{} 0n:
      {==}
    case True{} 1n+j:
      {==}
    case False{} 0n:
      Known.fill_of_open(
        kn,
        c,
        0n,
        RContents.Fill.fuel(0n, kn, c, RKnown.Known.at(kn, s, c, 0n), u => RFacts.Facts.fuel(s)),
        RContents.Content.at(
          RContents.Fill.fuel(0n, kn, c, RKnown.Known.at(kn, s, c, 0n), u => RFacts.Facts.fuel(s)),
          kn,
          s,
          c,
          0n
        )
      )
    case False{} 1n+(+j):
      Known.fill_next_open(
        RKnown.Known.held(kn, c, j),
        RKnown.Known.at(kn, s, c, 1n+j),
        kn,
        s,
        c,
        j
      )

# a table that learns the contents of versions of a line holds the same
# facts for a work
def Known.warm_go_open(
  n: Nat,
  +k: Nat,
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line
) -> {
  RKnown.Known.shelf(
    kn
  )
    == RKnown.Known.shelf(RContents.Known.warm.go(n, k, kn, s, c)): Maybe<&2, RKnown.Kept>
}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.trans(
        Maybe<&2, RKnown.Kept>,
        RKnown.Known.shelf(kn),
        RKnown.Known.shelf(RContents.Known.fill(kn, s, c, k)),
        RKnown.Known.shelf(
          RContents.Known.warm.go(p, 1n+k, RContents.Known.fill(kn, s, c, k), s, c)
        ),
        Known.fill_if_open(Maybe.is_some(&2, Nat, RKnown.Known.depth(kn, c, k)), kn, s, c, k),
        Known.warm_go_open(p, 1n+k, RContents.Known.fill(kn, s, c, k), s, c)
      )

# a table with a number with its first contents holds the same facts for a
# work
def Known.sync_open(
  kn: RKnown.Known(),
  -g: Nat
) -> {
  RKnown.Known.shelf(kn) == RKnown.Known.shelf(RKnown.Known.sync(kn, g)): Maybe<&2, RKnown.Kept>
}:
  match kn:
    case Nil{}:
      {==}
    case Con{RKnown.Kept{c2, st2}, rest}:
      Known.sync_open(rest, g)
    case Con{RKnown.Ruled{c2, zu2, u2}, rest}:
      Known.sync_open(rest, g)
    case Con{RKnown.Made{c2, y2}, rest}:
      Known.sync_open(rest, g)
    case Con{RKnown.Open{fs2, pk2, tx9, mtx9}, rest}:
      {==}
    case Con{RKnown.Stock{m2, lwm2}, rest}:
      {==}

# a table that fits, after it learns the content of each version of a line,
# fits
def Known.warm_fit(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line
) -> {
  RContents.Known.fit(kn, s) == True{}: Bool
} -> {RContents.Known.fit(RContents.Known.warm(kn, s, c), s) == True{}: Bool}:
  +h => Fit.both(RContents.Known.warm(kn, s, c), s)(Known.warm_ok(kn, s, c)(Fit.ok(kn, s)(h)))((
      %Known.warm_go_open(RContents.Versions.count(RKnown.Known.versions(kn, s, c)), 0n, RKnown.Known.sync(kn, RFacts.Facts.fuel(s)), s, c): {RContents.Shelf.fits(_, s) == True{}: Bool}
      %Known.sync_open(kn, RFacts.Facts.fuel(s)): {RContents.Shelf.fits(_, s) == True{}: Bool}
      Fit.open(kn, s)(h)))

# a table that learns the contents of the new versions of a line holds the
# same facts for a work
def Known.grow_open(
  near: Bool,
  +a: Nat,
  +b: Nat,
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line
) -> {
  RKnown.Known.shelf(
    kn
  )
    == RKnown.Known.shelf(RContents.Known.grow.if(near, a, b, kn, s, c)): Maybe<&2, RKnown.Kept>
}:
  match near:
    case True{}:
      Known.warm_go_open(Nat.sub(b, a), a, kn, s, c)
    case False{}:
      Equal.trans(
        Maybe<&2, RKnown.Kept>,
        RKnown.Known.shelf(kn),
        RKnown.Known.shelf(RKnown.Known.sync(kn, RFacts.Facts.fuel(s))),
        RKnown.Known.shelf(
          RContents.Known.warm.go(b, 0n, RKnown.Known.sync(kn, RFacts.Facts.fuel(s)), s, c)
        ),
        Known.sync_open(kn, RFacts.Facts.fuel(s)),
        Known.warm_go_open(b, 0n, RKnown.Known.sync(kn, RFacts.Facts.fuel(s)), s, c)
      )

# a right table with all the facts that a work may act on fits
def Known.opened_fit(
  +kn: RKnown.Known(),
  +s: RFacts.Plain()
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {RContents.Known.fit(RKnown.Known.opened(kn, s), s) == True{}: Bool}:
  +ok => Fit.both(
    RKnown.Known.opened(kn, s),
    s
  )(
    ok
  )(
    Open.fits_of(
      RKnown.Open.of(
        RFacts.Facts.list(s),
        RKnown.Scene{
          RKnown.Open{
            [],
            0n,
            Crits.Crit.new(Types.Ask),
            RKnown.Mergers.of(RFacts.Facts.list(s))
          }
            <> kn,
          s
        }
      ),
      RFacts.Seq.peak(RFacts.Facts.list(s)),
      RKnown.Tops.of(RFacts.Facts.list(s)),
      RKnown.Mergers.of(RFacts.Facts.list(s)),
      s
    )(
      Shared.Bool.and_both(
        Shared.List.is_eq(
          ~Types.Fact,
          ~Coded.Fact.is_eq,
          RKnown.Open.of(
            RFacts.Facts.list(s),
            RKnown.Scene{
              RKnown.Open{
                [],
                0n,
                Crits.Crit.new(Types.Ask),
                RKnown.Mergers.of(RFacts.Facts.list(s))
              }
                <> kn,
              s
            }
          ),
          RKnown.Open.of(RFacts.Facts.list(s), RKnown.Scene{RKnown.Known.none(), s})
        ),
        Nat.is_eq(RFacts.Seq.peak(RFacts.Facts.list(s)), RFacts.Seq.peak(RFacts.Facts.list(s)))
      )((
          %Open.of_ok(RKnown.Open{[], 0n, Crits.Crit.new(Types.Ask), RKnown.Mergers.of(RFacts.Facts.list(s))} <> kn, s, RFacts.Facts.list(s))(ok)(Mergers.Mergers.same_refl(RKnown.Mergers.of(RFacts.Facts.list(s)))): {Shared.List.is_eq(~Types.Fact, ~Coded.Fact.is_eq, RKnown.Open.of(RFacts.Facts.list(s), RKnown.Scene{RKnown.Open{[], 0n, Crits.Crit.new(Types.Ask), RKnown.Mergers.of(RFacts.Facts.list(s))} <> kn, s}), _) == True{}: Bool}
          Shared.List.is_eq_refl(~Types.Fact, ~Coded.Fact.is_eq, ~Coded.Fact.laws(), RKnown.Open.of(RFacts.Facts.list(s), RKnown.Scene{RKnown.Open{[], 0n, Crits.Crit.new(Types.Ask), RKnown.Mergers.of(RFacts.Facts.list(s))} <> kn, s}))))(
        Shared.Nat.is_eq_refl(RFacts.Seq.peak(RFacts.Facts.list(s)))
      )
    )({==})({==})
  )

# a right table with other facts for a work is right
def Known.reopen_ok(
  kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +fs: List<&2, Types.Fact>,
  +n: Nat,
  +tx: Crits.Crit<Types.Ask>,
  +mx: Crits.Crit<Ledgers.Line>
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {RContents.Known.ok(RKnown.Known.reopen(kn, fs, n, tx, mx), s) == True{}: Bool}:
  match kn:
    case Nil{}:
      ok => {==}
    case Con{RKnown.Kept{+c2, +st2}, +rest}:
      +ok => Ok.cons(
        RKnown.Kept{c2, st2},
        RKnown.Known.reopen(rest, fs, n, tx, mx),
        s
      )(
        Ok.head(RKnown.Kept{c2, st2}, rest, s)(ok)
      )(Known.reopen_ok(rest, s, fs, n, tx, mx)(Ok.tail(RKnown.Kept{c2, st2}, rest, s)(ok)))
    case Con{RKnown.Stock{m2, lwm2}, rest}:
      ok => ok
    case Con{RKnown.Ruled{+c2, +zu2, +u2}, +rest}:
      +ok => Ok.cons(
        RKnown.Ruled{c2, zu2, u2},
        RKnown.Known.reopen(rest, fs, n, tx, mx),
        s
      )(
        Ok.head(RKnown.Ruled{c2, zu2, u2}, rest, s)(ok)
      )(Known.reopen_ok(rest, s, fs, n, tx, mx)(Ok.tail(RKnown.Ruled{c2, zu2, u2}, rest, s)(ok)))
    case Con{RKnown.Made{+c2, +y2}, +rest}:
      +ok => Ok.cons(
        RKnown.Made{c2, y2},
        RKnown.Known.reopen(rest, fs, n, tx, mx),
        s
      )(
        Ok.head(RKnown.Made{c2, y2}, rest, s)(ok)
      )(Known.reopen_ok(rest, s, fs, n, tx, mx)(Ok.tail(RKnown.Made{c2, y2}, rest, s)(ok)))
    case Con{RKnown.Open{+fs2, +pk2, +tx9, +mtx9}, +rest}:
      ok => Ok.tail(RKnown.Open{fs2, pk2, tx9, mtx9}, rest, s)(ok)

# a table that holds an entry for a work holds what it is given in its
# place
def Known.reopen_shelf(
  kn: RKnown.Known(),
  +fs: List<&2, Types.Fact>,
  +n: Nat,
  +tx: Crits.Crit<Types.Ask>,
  +mx: Crits.Crit<Ledgers.Line>,
  -old: List<&2, Types.Fact>,
  -n0: Nat,
  -tx0: Crits.Crit<Types.Ask>,
  -mtx0: Crits.Crit<Ledgers.Line>
) -> {
  RKnown.Known.shelf(kn) == Some{RKnown.Open{old, n0, tx0, mtx0}}: Maybe<&2, RKnown.Kept>
} -> {
  RKnown.Known.shelf(
    RKnown.Known.reopen(kn, fs, n, tx, mx)
  )
    == Some{RKnown.Open{fs, n, tx, mx}}: Maybe<&2, RKnown.Kept>
}:
  match kn:
    case Nil{}:
      e => Empty.absurd(
        {None{} == Some{RKnown.Open{fs, n, tx, mx}}: Maybe<&2, RKnown.Kept>},
        Shared.Maybe.none_ne_some(RKnown.Kept, RKnown.Open{old, n0, tx0, mtx0}, e)
      )
    case Con{RKnown.Kept{c2, st2}, rest}:
      e => Known.reopen_shelf(rest, fs, n, tx, mx, old, n0, tx0, mtx0)(e)
    case Con{RKnown.Stock{m2, lwm2}, rest}:
      e => Empty.absurd(
        {None{} == Some{RKnown.Open{fs, n, tx, mx}}: Maybe<&2, RKnown.Kept>},
        Shared.Maybe.none_ne_some(RKnown.Kept, RKnown.Open{old, n0, tx0, mtx0}, e)
      )
    case Con{RKnown.Ruled{c2, zu2, u2}, rest}:
      e => Known.reopen_shelf(rest, fs, n, tx, mx, old, n0, tx0, mtx0)(e)
    case Con{RKnown.Made{c2, y2}, rest}:
      e => Known.reopen_shelf(rest, fs, n, tx, mx, old, n0, tx0, mtx0)(e)
    case Con{RKnown.Open{fs2, pk2, tx9, mtx9}, rest}:
      e => {==}

# The facts of a node, in order
# -----------------------------

# the facts of a node are sorted by their words
def Listed.sorted(
  +s: Facts.Facts()
) -> {
  Orders.Values.sorted(
    ~Types.Fact,
    ~Coded.Fact.words,
    RFacts.Facts.list(Facts.Facts.crit(s))
  )
    == True{}: Bool
}:
  Sets.ValSet.list_sorted(~Types.Fact, ~Coded.Fact.words, s)

# the facts of a node with one more fact are an insert of the fact into its
# facts
def Listed.add(
  +s: Facts.Facts(),
  +f: Types.Fact
) -> {
  RFacts.Facts.list(
    RFacts.Facts.add(Facts.Facts.crit(s), f)
  )
    == Orders.Values.insert(
      ~Types.Fact,
      ~Coded.Fact.words,
      RFacts.Facts.list(Facts.Facts.crit(s)),
      f
    ): List<&2, Types.Fact>
}:
  Sets.ValSet.list_set(~Types.Fact, ~Coded.Fact.words, s, f)

# a choice that runs one side is a choice of two values
def Bool.when_pick(
  -A: Data,
  b: Bool,
  -x: A,
  -y: A
) -> {Shared.Bool.when(A, b, u => x, u => y) == Bool.pick(A, b, x, y): A}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# The greatest number of an ask
# -----------------------------

# the greater of a number and itself is the number
def Nat.max_self(a: Nat) -> {Nat.max(a, a) == a: Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, y => 1n+y, Nat.max(p, p), p, Nat.max_self(p))

# the greater of two numbers, in either order
def Nat.max_comm(a: Nat, b: Nat) -> {Nat.max(a, b) == Nat.max(b, a): Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, y => 1n+y, Nat.max(p, q), Nat.max(q, p), Nat.max_comm(p, q))

# the greater of a number and the greater of it and another
def Nat.max_idem(a: Nat, b: Nat) -> {Nat.max(a, Nat.max(a, b)) == Nat.max(a, b): Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Equal.cong(Nat, Nat, y => 1n+y, Nat.max(p, p), p, Nat.max_self(p))
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, y => 1n+y, Nat.max(p, Nat.max(p, q)), Nat.max(p, q), Nat.max_idem(p, q))

# the greatest of three numbers, with the first two in either order
def Nat.max_swap(
  a: Nat,
  b: Nat,
  c: Nat
) -> {Nat.max(a, Nat.max(b, c)) == Nat.max(b, Nat.max(a, c)): Nat}:
  match a b c:
    case 0n 0n 0n:
      {==}
    case 0n 0n 1n+r:
      {==}
    case 0n 1n+q 0n:
      {==}
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 0n 0n:
      {==}
    case 1n+p 0n 1n+r:
      {==}
    case 1n+p 1n+q 0n:
      Equal.cong(Nat, Nat, y => 1n+y, Nat.max(p, q), Nat.max(q, p), Nat.max_comm(p, q))
    case 1n+p 1n+q 1n+r:
      Equal.cong(
        Nat,
        Nat,
        y => 1n+y,
        Nat.max(p, Nat.max(q, r)),
        Nat.max(q, Nat.max(p, r)),
        Nat.max_swap(p, q, r)
      )

# the greatest number among facts with one more fact first
def Seq.peak_cons(
  f: Types.Fact,
  -rest: List<&2, Types.Fact>
) -> {RFacts.Seq.peak(f <> rest) == Nat.max(RFacts.Seq.of(f), RFacts.Seq.peak(rest)): Nat}:
  match f:
    case Types.Fact.Ask{a}:
      {==}
    case Types.Fact.Vote{v, st, Types.Cast.Vote{r, Types.Pick{a, pins}, b}}:
      {==}
    case Types.Fact.Vote{v, st, Types.Cast.Pass{r}}:
      {==}

# the greatest number among facts after an insert of a fact
def Seq.peak_insert(
  xs: List<&2, Types.Fact>,
  +x: Types.Fact
) -> {
  RFacts.Seq.peak(
    Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, xs, x)
  )
    == Nat.max(RFacts.Seq.of(x), RFacts.Seq.peak(xs)): Nat
}:
  match xs:
    case Nil{}:
      Seq.peak_cons(x, [])
    case Con{+y, +r}:
      Lists.Bool.by(
        b => {
          Orders.Key.lt(Coded.Fact.words(x), Coded.Fact.words(y)) == b: Bool
        } -> {
          RFacts.Seq.peak(
            Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, y <> r, x)
          )
            == Nat.max(RFacts.Seq.of(x), RFacts.Seq.peak(y <> r)): Nat
        },
        Orders.Key.lt(Coded.Fact.words(x), Coded.Fact.words(y)),
        et => hl => (
          %Equal.sym(List<&2, Types.Fact>, Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, y <> r, x), x <> y <> r, Orders.Values.insert_lt(~Types.Fact, ~Coded.Fact.words, y, r, x)(hl)): {RFacts.Seq.peak(_) == Nat.max(RFacts.Seq.of(x), RFacts.Seq.peak(y <> r)): Nat}
          Seq.peak_cons(x, y <> r)),
        ef => +hn => Lists.Bool.by(
          b => {
            Crits.Key.is_eq(Coded.Fact.words(y), Coded.Fact.words(x)) == b: Bool
          } -> {
            RFacts.Seq.peak(
              Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, y <> r, x)
            )
              == Nat.max(RFacts.Seq.of(x), RFacts.Seq.peak(y <> r)): Nat
          },
          Crits.Key.is_eq(Coded.Fact.words(y), Coded.Fact.words(x)),
          et2 => +he => (
            %Equal.sym(List<&2, Types.Fact>, Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, y <> r, x), x <> r, Orders.Values.insert_eq(~Types.Fact, ~Coded.Fact.words, y, r, x)(hn)(he)): {RFacts.Seq.peak(_) == Nat.max(RFacts.Seq.of(x), RFacts.Seq.peak(y <> r)): Nat}
            %Equal.sym(Types.Fact, y, x, Coded.Fact.words_inj(y, x)(Crits.Key.is_eq_sound(Coded.Fact.words(y), Coded.Fact.words(x))(he))): {RFacts.Seq.peak(x <> r) == Nat.max(RFacts.Seq.of(x), RFacts.Seq.peak(_ <> r)): Nat}
            %Equal.sym(Nat, RFacts.Seq.peak(x <> r), Nat.max(RFacts.Seq.of(x), RFacts.Seq.peak(r)), Seq.peak_cons(x, r)): {_ == Nat.max(RFacts.Seq.of(x), _): Nat}
            Equal.sym(Nat, Nat.max(RFacts.Seq.of(x), Nat.max(RFacts.Seq.of(x), RFacts.Seq.peak(r))), Nat.max(RFacts.Seq.of(x), RFacts.Seq.peak(r)), Nat.max_idem(RFacts.Seq.of(x), RFacts.Seq.peak(r)))),
          ef2 => he => (
            %Equal.sym(List<&2, Types.Fact>, Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, y <> r, x), y <> Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, r, x), Orders.Values.insert_gt(~Types.Fact, ~Coded.Fact.words, y, r, x)(hn)(he)): {RFacts.Seq.peak(_) == Nat.max(RFacts.Seq.of(x), RFacts.Seq.peak(y <> r)): Nat}
            %Equal.sym(Nat, RFacts.Seq.peak(y <> Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, r, x)), Nat.max(RFacts.Seq.of(y), RFacts.Seq.peak(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, r, x))), Seq.peak_cons(y, Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, r, x))): {_ == Nat.max(RFacts.Seq.of(x), RFacts.Seq.peak(y <> r)): Nat}
            %Equal.sym(Nat, RFacts.Seq.peak(y <> r), Nat.max(RFacts.Seq.of(y), RFacts.Seq.peak(r)), Seq.peak_cons(y, r)): {Nat.max(RFacts.Seq.of(y), RFacts.Seq.peak(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, r, x))) == Nat.max(RFacts.Seq.of(x), _): Nat}
            %Equal.sym(Nat, RFacts.Seq.peak(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, r, x)), Nat.max(RFacts.Seq.of(x), RFacts.Seq.peak(r)), Seq.peak_insert(r, x)): {Nat.max(RFacts.Seq.of(y), _) == Nat.max(RFacts.Seq.of(x), Nat.max(RFacts.Seq.of(y), RFacts.Seq.peak(r))): Nat}
            Nat.max_swap(RFacts.Seq.of(y), RFacts.Seq.of(x), RFacts.Seq.peak(r)))
        )({==})
      )({==})

# An ask joins the facts that a work may act on
# ---------------------------------------------

# the ask of a request that starts no store collides with no ask among all
def Collided.none(
  all: List<&2, Types.Fact>,
  +i: Ledgers.Id,
  +k: Nat,
  +r: Spec.Request
) -> {
  RFacts.Request.is_start(r) == False{}: Bool
} -> {
  Shared.List.some(
    ~Types.Fact,
    ~Types.Ask,
    ~RFacts.Fact.collides,
    all,
    Types.Ask{i, k, r}
  )
    == False{}: Bool
}:
  match all:
    case Nil{}:
      e => {==}
    case Con{Types.Fact.Vote{v, st, pk}, rest}:
      e => Collided.none(rest, i, k, r)(e)
    case Con{Types.Fact.Ask{+b}, +rest}:
      +e =>
        %Equal.sym(
          Bool,
          RFacts.Request.is_start(r),
          False{},
          e
        ): {
          List.any.if(
            u => Shared.List.some(
              ~Types.Fact,
              ~Types.Ask,
              ~RFacts.Fact.collides,
              rest,
              Types.Ask{i, k, r}
            ),
            Shared.Bool.when(
              Bool,
              Shared.Bool.when(
                Bool,
                _,
                u => Hashes.Hash.is_eq(
                  RFacts.Start.root(i, r),
                  RFacts.Ask.root(Types.Ask{i, k, r})
                ),
                u => False{}
              ),
              un => Shared.Bool.when(
                Bool,
                RFacts.Ask.starts(RFacts.Ask.root(Types.Ask{i, k, r}), b),
                u => Bool.not(RFacts.Ask.alike(Types.Ask{i, k, r}, b)),
                u => False{}
              ),
              un => False{}
            )
          )
            == False{}: Bool
        }
        Collided.none(rest, i, k, r)(e)

# the facts of a node that takes in an ask that starts no store are its
# facts with the ask
def Take.ask(
  +name: String,
  +s: Facts.Facts(),
  +i: Ledgers.Id,
  +n: Nat,
  +r: Spec.Request
) -> {
  RFacts.Request.is_start(r) == False{}: Bool
} -> {
  Facts.Facts.crit(
    Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})
  )
    == RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Ask{Types.Ask{i, n, r}}): RFacts.Plain()
}:
  e => Equal.trans(
    RFacts.Plain(),
    Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})),
    RFacts.Facts.take(name, Facts.Facts.crit(s), Types.Fact.Ask{Types.Ask{i, n, r}}),
    RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Ask{Types.Ask{i, n, r}}),
    Facts.Facts.take_crit(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}),
    Equal.cong(
      Bool,
      RFacts.Plain(),
      y => Shared.Bool.when(
        RFacts.Plain(),
        y,
        u => RFacts.Trust.break(
          RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Ask{Types.Ask{i, n, r}}),
          name
        ),
        u => RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Ask{Types.Ask{i, n, r}})
      ),
      Shared.List.some(
        ~Types.Fact,
        ~Types.Ask,
        ~RFacts.Fact.collides,
        RFacts.Facts.list(Facts.Facts.crit(s)),
        Types.Ask{i, n, r}
      ),
      False{},
      Collided.none(RFacts.Facts.list(Facts.Facts.crit(s)), i, n, r)(e)
    )
  )

# the facts of a node that takes in an ask that starts no store are an
# insert of the ask into its facts
def Asked.list(
  +name: String,
  +s: Facts.Facts(),
  +i: Ledgers.Id,
  +n: Nat,
  +r: Spec.Request
) -> {
  RFacts.Request.is_start(r) == False{}: Bool
} -> {
  RFacts.Facts.list(
    Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
  )
    == Orders.Values.insert(
      ~Types.Fact,
      ~Coded.Fact.words,
      RFacts.Facts.list(Facts.Facts.crit(s)),
      Types.Fact.Ask{Types.Ask{i, n, r}}
    ): List<&2, Types.Fact>
}:
  e => Equal.trans(
    List<&2, Types.Fact>,
    RFacts.Facts.list(
      Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
    ),
    RFacts.Facts.list(RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Ask{Types.Ask{i, n, r}})),
    Orders.Values.insert(
      ~Types.Fact,
      ~Coded.Fact.words,
      RFacts.Facts.list(Facts.Facts.crit(s)),
      Types.Fact.Ask{Types.Ask{i, n, r}}
    ),
    Equal.cong(
      RFacts.Plain(),
      List<&2, Types.Fact>,
      y => RFacts.Facts.list(y),
      Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})),
      RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Ask{Types.Ask{i, n, r}}),
      Take.ask(name, s, i, n, r)(e)
    ),
    Listed.add(s, Types.Fact.Ask{Types.Ask{i, n, r}})
  )

# a request that resolves a merge of the line l waits after a node takes in
# an ask that starts no store as before
def Resolve.waits_asked(
  l: Maybe<&2, Ledgers.Line>,
  +name: String,
  +s: Facts.Facts(),
  +i: Ledgers.Id,
  +n: Nat,
  +r: Spec.Request,
  +i2: Ledgers.Id
) -> {
  RFacts.Request.is_start(r) == False{}: Bool
} -> {
  RKnown.Resolve.waits(
    l,
    RKnown.Known.none(),
    Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})),
    i2
  )
    == RKnown.Resolve.waits(l, RKnown.Known.none(), Facts.Facts.crit(s), i2): Bool
}:
  match l:
    case None{}:
      e => {==}
    case Some{+c}:
      e => Equal.cong(
        Maybe<&2, RLines.State>,
        Bool,
        m => RKnown.Id.waits(m, RKnown.Known.none(), c, i2),
        Lines.Line.state(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}), c),
        Lines.Line.state(s, c),
        Moves.Line.state_asked(name, s, Types.Ask{i, n, r}, c)(e)
      )

# a work may act on a fact after a node takes in an ask that starts no
# store as before
def Waits.asked(
  +name: String,
  +s: Facts.Facts(),
  +i: Ledgers.Id,
  +n: Nat,
  +r: Spec.Request,
  f: Types.Fact
) -> {
  RFacts.Request.is_start(r) == False{}: Bool
} -> {
  RKnown.Fact.merges(Types.Fact.Ask{Types.Ask{i, n, r}}) == False{}: Bool
} -> {
  RKnown.Fact.waits(
    RKnown.Scene{
      RKnown.Known.none(),
      Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
    },
    f
  )
    == RKnown.Fact.waits(RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}, f): Bool
}:
  match f:
    case Types.Fact.Vote{v, Types.Step.Broken{}, x}:
      e => hm => {==}
    case Types.Fact.Vote{v, Types.Step.At{+c2, +k2, t2}, x}:
      e => hm => Equal.cong(
        Maybe<&2, RLines.State>,
        Bool,
        m => RKnown.Slot.waits(m, k2),
        Lines.Line.state(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}), c2),
        Lines.Line.state(s, c2),
        Moves.Line.state_asked(name, s, Types.Ask{i, n, r}, c2)(e)
      )
    case Types.Fact.Ask{Types.Ask{+i2, n2, Spec.Request.Start{os}}}:
      e => hm => {==}
    case Types.Fact.Ask{Types.Ask{+i2, n2, Spec.Request.Write{+b2, p2, w2}}}:
      e => hm => Equal.cong(
        Maybe<&2, RLines.State>,
        Bool,
        m => RKnown.Id.waits(m, RKnown.Known.none(), b2, i2),
        Lines.Line.state(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}), b2),
        Lines.Line.state(s, b2),
        Moves.Line.state_asked(name, s, Types.Ask{i, n, r}, b2)(e)
      )
    case Types.Fact.Ask{Types.Ask{+i2, n2, Spec.Request.Merge{f2, +x2}}}:
      e => hm => Equal.cong(
        Maybe<&2, RLines.State>,
        Bool,
        m => RKnown.Id.waits(m, RKnown.Known.none(), x2, i2),
        Lines.Line.state(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}), x2),
        Lines.Line.state(s, x2),
        Moves.Line.state_asked(name, s, Types.Ask{i, n, r}, x2)(e)
      )
    case Types.Fact.Ask{Types.Ask{+i2, n2, Spec.Request.Resolve{+m2, p2, w2}}}:
      +e => hm => Equal.trans(
        Bool,
        RKnown.Resolve.waits(
          RKnown.Merge.line(
            RFacts.Facts.list(
              Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
            ),
            m2
          ),
          RKnown.Known.none(),
          Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})),
          i2
        ),
        RKnown.Resolve.waits(
          RKnown.Merge.line(RFacts.Facts.list(Facts.Facts.crit(s)), m2),
          RKnown.Known.none(),
          Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})),
          i2
        ),
        RKnown.Resolve.waits(
          RKnown.Merge.line(RFacts.Facts.list(Facts.Facts.crit(s)), m2),
          RKnown.Known.none(),
          Facts.Facts.crit(s),
          i2
        ),
        Equal.cong(
          Maybe<&2, Ledgers.Line>,
          Bool,
          l => RKnown.Resolve.waits(
            l,
            RKnown.Known.none(),
            Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})),
            i2
          ),
          RKnown.Merge.line(
            RFacts.Facts.list(
              Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
            ),
            m2
          ),
          RKnown.Merge.line(RFacts.Facts.list(Facts.Facts.crit(s)), m2),
          Equal.trans(
            Maybe<&2, Ledgers.Line>,
            RKnown.Merge.line(
              RFacts.Facts.list(
                Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
              ),
              m2
            ),
            RKnown.Merge.line(
              Orders.Values.insert(
                ~Types.Fact,
                ~Coded.Fact.words,
                RFacts.Facts.list(Facts.Facts.crit(s)),
                Types.Fact.Ask{Types.Ask{i, n, r}}
              ),
              m2
            ),
            RKnown.Merge.line(RFacts.Facts.list(Facts.Facts.crit(s)), m2),
            Equal.cong(
              List<&2, Types.Fact>,
              Maybe<&2, Ledgers.Line>,
              l => RKnown.Merge.line(l, m2),
              RFacts.Facts.list(
                Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
              ),
              Orders.Values.insert(
                ~Types.Fact,
                ~Coded.Fact.words,
                RFacts.Facts.list(Facts.Facts.crit(s)),
                Types.Fact.Ask{Types.Ask{i, n, r}}
              ),
              Asked.list(name, s, i, n, r)(e)
            ),
            Mergers.Merge.line_insert_pass(
              RFacts.Facts.list(Facts.Facts.crit(s)),
              Types.Fact.Ask{Types.Ask{i, n, r}},
              m2
            )(hm)
          )
        ),
        Resolve.waits_asked(
          RKnown.Merge.line(RFacts.Facts.list(Facts.Facts.crit(s)), m2),
          name,
          s,
          i,
          n,
          r,
          i2
        )(e)
      )
    case Types.Fact.Ask{Types.Ask{+i2, n2, Spec.Request.Mark{+b2, m2, v2}}}:
      e => hm => Equal.cong(
        Maybe<&2, RLines.State>,
        Bool,
        m => RKnown.Id.waits(m, RKnown.Known.none(), b2, i2),
        Lines.Line.state(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}), b2),
        Lines.Line.state(s, b2),
        Moves.Line.state_asked(name, s, Types.Ask{i, n, r}, b2)(e)
      )
    case Types.Fact.Ask{Types.Ask{+i2, n2, Spec.Request.Move{+b2, t2, v2}}}:
      e => hm => Equal.cong(
        Maybe<&2, RLines.State>,
        Bool,
        m => RKnown.Id.waits(m, RKnown.Known.none(), b2, i2),
        Lines.Line.state(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}), b2),
        Lines.Line.state(s, b2),
        Moves.Line.state_asked(name, s, Types.Ask{i, n, r}, b2)(e)
      )
    case Types.Fact.Ask{Types.Ask{+i2, n2, Spec.Request.Group{+h2, g2, ms2}}}:
      e => hm => Equal.cong(
        Maybe<&2, RLines.State>,
        Bool,
        m => RKnown.Id.waits(m, RKnown.Known.none(), Ledgers.Line{h2, None{}}, i2),
        Lines.Line.state(
          Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}),
          Ledgers.Line{h2, None{}}
        ),
        Lines.Line.state(s, Ledgers.Line{h2, None{}}),
        Moves.Line.state_asked(name, s, Types.Ask{i, n, r}, Ledgers.Line{h2, None{}})(e)
      )
    case Types.Fact.Ask{Types.Ask{+i2, n2, Spec.Request.Own{Ledgers.Line{+h2, b2}, g2}}}:
      e => hm => Equal.cong(
        Maybe<&2, RLines.State>,
        Bool,
        m => RKnown.Id.waits(m, RKnown.Known.none(), Ledgers.Line{h2, None{}}, i2),
        Lines.Line.state(
          Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}),
          Ledgers.Line{h2, None{}}
        ),
        Lines.Line.state(s, Ledgers.Line{h2, None{}}),
        Moves.Line.state_asked(name, s, Types.Ask{i, n, r}, Ledgers.Line{h2, None{}})(e)
      )

# the facts among xs that a work may act on, after a node takes in an ask
# that starts no store, are those before
def Open.of_asked(
  +name: String,
  +s: Facts.Facts(),
  +i: Ledgers.Id,
  +n: Nat,
  +r: Spec.Request,
  xs: List<&2, Types.Fact>
) -> {
  RFacts.Request.is_start(r) == False{}: Bool
} -> {
  RKnown.Fact.merges(Types.Fact.Ask{Types.Ask{i, n, r}}) == False{}: Bool
} -> {
  RKnown.Open.of(
    xs,
    RKnown.Scene{
      RKnown.Known.none(),
      Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
    }
  )
    == RKnown.Open.of(
      xs,
      RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}
    ): List<&2, Types.Fact>
}:
  match xs:
    case Nil{}:
      e => hm => {==}
    case Con{+f, +rest}:
      +e => +hm => (
        %Waits.asked(name, s, i, n, r, f)(e)(hm): {RKnown.Open.of(f <> rest, RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))}) == List.filter.put(Types.Fact, f, RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}), _): List<&2, Types.Fact>}
        %Open.of_asked(name, s, i, n, r, rest)(e)(hm): {RKnown.Open.of(f <> rest, RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))}) == List.filter.put(Types.Fact, f, _, RKnown.Fact.waits(RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))}, f)): List<&2, Types.Fact>}
        {==})

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof does not run
# the facts that a work may act on, with an ask that starts no store if a
# work may act on it, are those that a work may act on once the node took
# the ask in
def Asked.open(
  +name: String,
  +s: Facts.Facts(),
  +i: Ledgers.Id,
  +n: Nat,
  +r: Spec.Request,
  +fs: List<&2, Types.Fact>,
  +kn: RKnown.Known()
) -> {
  RFacts.Request.is_start(r) == False{}: Bool
} -> {
  RContents.Known.ok(
    kn,
    Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
  )
    == True{}: Bool
} -> {
  RContents.Shelf.led(
    RKnown.Known.shelf(kn),
    Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
  )
    == True{}: Bool
} -> {
  RKnown.Fact.merges(Types.Fact.Ask{Types.Ask{i, n, r}}) == False{}: Bool
} -> {
  fs
    == RKnown.Open.of(
      RFacts.Facts.list(Facts.Facts.crit(s)),
      RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}
    ): List<&2, Types.Fact>
} -> {
  RKnown.Open.with(
    fs,
    Types.Fact.Ask{Types.Ask{i, n, r}},
    RKnown.Scene{
      kn,
      Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
    }
  )
    == RKnown.Open.of(
      RFacts.Facts.list(
        Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
      ),
      RKnown.Scene{
        RKnown.Known.none(),
        Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
      }
    ): List<&2, Types.Fact>
}:
  +e => ok => hl => +hm => efs => (
    %Equal.sym(List<&2, Types.Fact>, RFacts.Facts.list(Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))), Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, RFacts.Facts.list(Facts.Facts.crit(s)), Types.Fact.Ask{Types.Ask{i, n, r}}), Asked.list(name, s, i, n, r)(e)): {RKnown.Open.with(fs, Types.Fact.Ask{Types.Ask{i, n, r}}, RKnown.Scene{kn, Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))}) == RKnown.Open.of(_, RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))}): List<&2, Types.Fact>}
    %Equal.sym(List<&2, Types.Fact>, RKnown.Open.of(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, RFacts.Facts.list(Facts.Facts.crit(s)), Types.Fact.Ask{Types.Ask{i, n, r}}), RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))}), RKnown.Open.of(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, RFacts.Facts.list(Facts.Facts.crit(s)), Types.Fact.Ask{Types.Ask{i, n, r}}), RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}), Open.of_asked(name, s, i, n, r, Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, RFacts.Facts.list(Facts.Facts.crit(s)), Types.Fact.Ask{Types.Ask{i, n, r}}))(e)(hm)): {RKnown.Open.with(fs, Types.Fact.Ask{Types.Ask{i, n, r}}, RKnown.Scene{kn, Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))}) == _: List<&2, Types.Fact>}
    %Equal.sym(List<&2, Types.Fact>, RKnown.Open.of(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, RFacts.Facts.list(Facts.Facts.crit(s)), Types.Fact.Ask{Types.Ask{i, n, r}}), RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}), Bool.pick(List<&2, Types.Fact>, RKnown.Fact.waits(RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}, Types.Fact.Ask{Types.Ask{i, n, r}}), Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, RKnown.Open.of(RFacts.Facts.list(Facts.Facts.crit(s)), RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}), Types.Fact.Ask{Types.Ask{i, n, r}}), RKnown.Open.of(RFacts.Facts.list(Facts.Facts.crit(s)), RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)})), Orders.Values.keep_insert(~Types.Fact, ~Coded.Fact.words, ~Coded.Fact.words_inj, ~RKnown.Scene, ~RKnown.Fact.waits, RFacts.Facts.list(Facts.Facts.crit(s)), Types.Fact.Ask{Types.Ask{i, n, r}}, RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)})(Listed.sorted(s))): {RKnown.Open.with(fs, Types.Fact.Ask{Types.Ask{i, n, r}}, RKnown.Scene{kn, Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))}) == _: List<&2, Types.Fact>}
    %efs: {RKnown.Open.with(fs, Types.Fact.Ask{Types.Ask{i, n, r}}, RKnown.Scene{kn, Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))}) == Bool.pick(List<&2, Types.Fact>, RKnown.Fact.waits(RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}, Types.Fact.Ask{Types.Ask{i, n, r}}), Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, _, Types.Fact.Ask{Types.Ask{i, n, r}}), _): List<&2, Types.Fact>}
    %Waits.asked(name, s, i, n, r, Types.Fact.Ask{Types.Ask{i, n, r}})(e)(hm): {RKnown.Open.with(fs, Types.Fact.Ask{Types.Ask{i, n, r}}, RKnown.Scene{kn, Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))}) == Bool.pick(List<&2, Types.Fact>, _, Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, Types.Fact.Ask{Types.Ask{i, n, r}}), fs): List<&2, Types.Fact>}
    %Fact.waits_ok(kn, Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})), Types.Fact.Ask{Types.Ask{i, n, r}})(ok)(hl): {RKnown.Open.with(fs, Types.Fact.Ask{Types.Ask{i, n, r}}, RKnown.Scene{kn, Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))}) == Bool.pick(List<&2, Types.Fact>, _, Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, Types.Fact.Ask{Types.Ask{i, n, r}}), fs): List<&2, Types.Fact>}
    %Equal.sym(List<&2, Types.Fact>, RKnown.Open.put(fs, Types.Fact.Ask{Types.Ask{i, n, r}}), Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, Types.Fact.Ask{Types.Ask{i, n, r}}), Open.put_insert(fs, Types.Fact.Ask{Types.Ask{i, n, r}})): {Shared.Bool.when(List<&2, Types.Fact>, RKnown.Fact.waits(RKnown.Scene{kn, Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))}, Types.Fact.Ask{Types.Ask{i, n, r}}), u => _, u => fs) == Bool.pick(List<&2, Types.Fact>, RKnown.Fact.waits(RKnown.Scene{kn, Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))}, Types.Fact.Ask{Types.Ask{i, n, r}}), Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, Types.Fact.Ask{Types.Ask{i, n, r}}), fs): List<&2, Types.Fact>}
    Bool.when_pick(List<&2, Types.Fact>, RKnown.Fact.waits(RKnown.Scene{kn, Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))}, Types.Fact.Ask{Types.Ask{i, n, r}}), Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, Types.Fact.Ask{Types.Ask{i, n, r}}), fs))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the greatest number of an ask, after a node takes in an ask that starts
# no store, is the greater of its number and the greatest before
def Asked.peak(
  +name: String,
  +s: Facts.Facts(),
  +i: Ledgers.Id,
  +n: Nat,
  +r: Spec.Request
) -> {
  RFacts.Request.is_start(r) == False{}: Bool
} -> {
  RFacts.Seq.peak(
    RFacts.Facts.list(
      Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
    )
  )
    == Nat.max(n, RFacts.Seq.peak(RFacts.Facts.list(Facts.Facts.crit(s)))): Nat
}:
  e => (
    %Equal.sym(List<&2, Types.Fact>, RFacts.Facts.list(Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))), Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, RFacts.Facts.list(Facts.Facts.crit(s)), Types.Fact.Ask{Types.Ask{i, n, r}}), Asked.list(name, s, i, n, r)(e)): {RFacts.Seq.peak(_) == Nat.max(n, RFacts.Seq.peak(RFacts.Facts.list(Facts.Facts.crit(s)))): Nat}
    Seq.peak_insert(RFacts.Facts.list(Facts.Facts.crit(s)), Types.Fact.Ask{Types.Ask{i, n, r}}))

# the ask of a merge waits after a node takes it in as before
def Waits.asked_self(
  +name: String,
  +s: Facts.Facts(),
  +i: Ledgers.Id,
  +n: Nat,
  r: Spec.Request
) -> {
  RFacts.Request.is_start(r) == False{}: Bool
} -> {
  RKnown.Request.merges(r) == True{}: Bool
} -> {
  RKnown.Fact.waits(
    RKnown.Scene{
      RKnown.Known.none(),
      Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
    },
    Types.Fact.Ask{Types.Ask{i, n, r}}
  )
    == RKnown.Fact.waits(
      RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)},
      Types.Fact.Ask{Types.Ask{i, n, r}}
    ): Bool
}:
  match r:
    case Spec.Request.Start{+os2}:
      e => ht => Empty.absurd(
        {
          RKnown.Fact.waits(
            RKnown.Scene{
              RKnown.Known.none(),
              Facts.Facts.crit(
                Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, Spec.Request.Start{os2}}})
              )
            },
            Types.Fact.Ask{Types.Ask{i, n, Spec.Request.Start{os2}}}
          )
            == RKnown.Fact.waits(
              RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)},
              Types.Fact.Ask{Types.Ask{i, n, Spec.Request.Start{os2}}}
            ): Bool
        },
        Shared.Bool.false_ne_true(ht)
      )
    case Spec.Request.Write{+b2, +p2, +w2}:
      e => ht => Empty.absurd(
        {
          RKnown.Fact.waits(
            RKnown.Scene{
              RKnown.Known.none(),
              Facts.Facts.crit(
                Facts.Facts.take(
                  name,
                  s,
                  Types.Fact.Ask{Types.Ask{i, n, Spec.Request.Write{b2, p2, w2}}}
                )
              )
            },
            Types.Fact.Ask{Types.Ask{i, n, Spec.Request.Write{b2, p2, w2}}}
          )
            == RKnown.Fact.waits(
              RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)},
              Types.Fact.Ask{Types.Ask{i, n, Spec.Request.Write{b2, p2, w2}}}
            ): Bool
        },
        Shared.Bool.false_ne_true(ht)
      )
    case Spec.Request.Merge{+f2, +x2}:
      e => ht => Equal.cong(
        Maybe<&2, RLines.State>,
        Bool,
        m => RKnown.Id.waits(m, RKnown.Known.none(), x2, i),
        Lines.Line.state(
          Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, Spec.Request.Merge{f2, x2}}}),
          x2
        ),
        Lines.Line.state(s, x2),
        Moves.Line.state_asked(name, s, Types.Ask{i, n, Spec.Request.Merge{f2, x2}}, x2)(e)
      )
    case Spec.Request.Resolve{+m2, +p2, +w2}:
      e => ht => Empty.absurd(
        {
          RKnown.Fact.waits(
            RKnown.Scene{
              RKnown.Known.none(),
              Facts.Facts.crit(
                Facts.Facts.take(
                  name,
                  s,
                  Types.Fact.Ask{Types.Ask{i, n, Spec.Request.Resolve{m2, p2, w2}}}
                )
              )
            },
            Types.Fact.Ask{Types.Ask{i, n, Spec.Request.Resolve{m2, p2, w2}}}
          )
            == RKnown.Fact.waits(
              RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)},
              Types.Fact.Ask{Types.Ask{i, n, Spec.Request.Resolve{m2, p2, w2}}}
            ): Bool
        },
        Shared.Bool.false_ne_true(ht)
      )
    case Spec.Request.Mark{+b2, +m2, +v2}:
      e => ht => Empty.absurd(
        {
          RKnown.Fact.waits(
            RKnown.Scene{
              RKnown.Known.none(),
              Facts.Facts.crit(
                Facts.Facts.take(
                  name,
                  s,
                  Types.Fact.Ask{Types.Ask{i, n, Spec.Request.Mark{b2, m2, v2}}}
                )
              )
            },
            Types.Fact.Ask{Types.Ask{i, n, Spec.Request.Mark{b2, m2, v2}}}
          )
            == RKnown.Fact.waits(
              RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)},
              Types.Fact.Ask{Types.Ask{i, n, Spec.Request.Mark{b2, m2, v2}}}
            ): Bool
        },
        Shared.Bool.false_ne_true(ht)
      )
    case Spec.Request.Move{+b2, +t2, +v2}:
      e => ht => Empty.absurd(
        {
          RKnown.Fact.waits(
            RKnown.Scene{
              RKnown.Known.none(),
              Facts.Facts.crit(
                Facts.Facts.take(
                  name,
                  s,
                  Types.Fact.Ask{Types.Ask{i, n, Spec.Request.Move{b2, t2, v2}}}
                )
              )
            },
            Types.Fact.Ask{Types.Ask{i, n, Spec.Request.Move{b2, t2, v2}}}
          )
            == RKnown.Fact.waits(
              RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)},
              Types.Fact.Ask{Types.Ask{i, n, Spec.Request.Move{b2, t2, v2}}}
            ): Bool
        },
        Shared.Bool.false_ne_true(ht)
      )
    case Spec.Request.Group{+h2, +g2, +ms2}:
      e => ht => Empty.absurd(
        {
          RKnown.Fact.waits(
            RKnown.Scene{
              RKnown.Known.none(),
              Facts.Facts.crit(
                Facts.Facts.take(
                  name,
                  s,
                  Types.Fact.Ask{Types.Ask{i, n, Spec.Request.Group{h2, g2, ms2}}}
                )
              )
            },
            Types.Fact.Ask{Types.Ask{i, n, Spec.Request.Group{h2, g2, ms2}}}
          )
            == RKnown.Fact.waits(
              RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)},
              Types.Fact.Ask{Types.Ask{i, n, Spec.Request.Group{h2, g2, ms2}}}
            ): Bool
        },
        Shared.Bool.false_ne_true(ht)
      )
    case Spec.Request.Own{+c2, +g2}:
      e => ht => Empty.absurd(
        {
          RKnown.Fact.waits(
            RKnown.Scene{
              RKnown.Known.none(),
              Facts.Facts.crit(
                Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, Spec.Request.Own{c2, g2}}})
              )
            },
            Types.Fact.Ask{Types.Ask{i, n, Spec.Request.Own{c2, g2}}}
          )
            == RKnown.Fact.waits(
              RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)},
              Types.Fact.Ask{Types.Ask{i, n, Spec.Request.Own{c2, g2}}}
            ): Bool
        },
        Shared.Bool.false_ne_true(ht)
      )

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof does not run
# the facts that a work may act on, with the ask of a merge that the node
# takes in, if a work may act on it: those among the facts with the ask that
# a work could act on before
def Asked.open_old(
  +name: String,
  +s: Facts.Facts(),
  +i: Ledgers.Id,
  +n: Nat,
  +r: Spec.Request,
  +fs: List<&2, Types.Fact>,
  +kn: RKnown.Known()
) -> {
  RFacts.Request.is_start(r) == False{}: Bool
} -> {
  RContents.Known.ok(
    kn,
    Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
  )
    == True{}: Bool
} -> {
  RContents.Shelf.led(
    RKnown.Known.shelf(kn),
    Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
  )
    == True{}: Bool
} -> {
  RKnown.Request.merges(r) == True{}: Bool
} -> {
  fs
    == RKnown.Open.of(
      RFacts.Facts.list(Facts.Facts.crit(s)),
      RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}
    ): List<&2, Types.Fact>
} -> {
  RKnown.Open.with(
    fs,
    Types.Fact.Ask{Types.Ask{i, n, r}},
    RKnown.Scene{
      kn,
      Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
    }
  )
    == RKnown.Open.of(
      RFacts.Facts.list(
        Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
      ),
      RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}
    ): List<&2, Types.Fact>
}:
  +e => ok => hl => ht => efs => (
    %Equal.sym(List<&2, Types.Fact>, RFacts.Facts.list(Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))), Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, RFacts.Facts.list(Facts.Facts.crit(s)), Types.Fact.Ask{Types.Ask{i, n, r}}), Asked.list(name, s, i, n, r)(e)): {RKnown.Open.with(fs, Types.Fact.Ask{Types.Ask{i, n, r}}, RKnown.Scene{kn, Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))}) == RKnown.Open.of(_, RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}): List<&2, Types.Fact>}
    %Equal.sym(List<&2, Types.Fact>, RKnown.Open.of(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, RFacts.Facts.list(Facts.Facts.crit(s)), Types.Fact.Ask{Types.Ask{i, n, r}}), RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}), Bool.pick(List<&2, Types.Fact>, RKnown.Fact.waits(RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}, Types.Fact.Ask{Types.Ask{i, n, r}}), Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, RKnown.Open.of(RFacts.Facts.list(Facts.Facts.crit(s)), RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}), Types.Fact.Ask{Types.Ask{i, n, r}}), RKnown.Open.of(RFacts.Facts.list(Facts.Facts.crit(s)), RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)})), Orders.Values.keep_insert(~Types.Fact, ~Coded.Fact.words, ~Coded.Fact.words_inj, ~RKnown.Scene, ~RKnown.Fact.waits, RFacts.Facts.list(Facts.Facts.crit(s)), Types.Fact.Ask{Types.Ask{i, n, r}}, RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)})(Listed.sorted(s))): {RKnown.Open.with(fs, Types.Fact.Ask{Types.Ask{i, n, r}}, RKnown.Scene{kn, Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))}) == _: List<&2, Types.Fact>}
    %efs: {RKnown.Open.with(fs, Types.Fact.Ask{Types.Ask{i, n, r}}, RKnown.Scene{kn, Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))}) == Bool.pick(List<&2, Types.Fact>, RKnown.Fact.waits(RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}, Types.Fact.Ask{Types.Ask{i, n, r}}), Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, _, Types.Fact.Ask{Types.Ask{i, n, r}}), _): List<&2, Types.Fact>}
    %Waits.asked_self(name, s, i, n, r)(e)(ht): {RKnown.Open.with(fs, Types.Fact.Ask{Types.Ask{i, n, r}}, RKnown.Scene{kn, Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))}) == Bool.pick(List<&2, Types.Fact>, _, Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, Types.Fact.Ask{Types.Ask{i, n, r}}), fs): List<&2, Types.Fact>}
    %Fact.waits_ok(kn, Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})), Types.Fact.Ask{Types.Ask{i, n, r}})(ok)(hl): {RKnown.Open.with(fs, Types.Fact.Ask{Types.Ask{i, n, r}}, RKnown.Scene{kn, Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))}) == Bool.pick(List<&2, Types.Fact>, _, Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, Types.Fact.Ask{Types.Ask{i, n, r}}), fs): List<&2, Types.Fact>}
    %Equal.sym(List<&2, Types.Fact>, RKnown.Open.put(fs, Types.Fact.Ask{Types.Ask{i, n, r}}), Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, Types.Fact.Ask{Types.Ask{i, n, r}}), Open.put_insert(fs, Types.Fact.Ask{Types.Ask{i, n, r}})): {Shared.Bool.when(List<&2, Types.Fact>, RKnown.Fact.waits(RKnown.Scene{kn, Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))}, Types.Fact.Ask{Types.Ask{i, n, r}}), u => _, u => fs) == Bool.pick(List<&2, Types.Fact>, RKnown.Fact.waits(RKnown.Scene{kn, Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))}, Types.Fact.Ask{Types.Ask{i, n, r}}), Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, Types.Fact.Ask{Types.Ask{i, n, r}}), fs): List<&2, Types.Fact>}
    Bool.when_pick(List<&2, Types.Fact>, RKnown.Fact.waits(RKnown.Scene{kn, Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))}, Types.Fact.Ask{Types.Ask{i, n, r}}), Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, Types.Fact.Ask{Types.Ask{i, n, r}}), fs))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# a fact that a work may act on after a node takes in an ask that starts no
# store is one that it could act on before: when the ask gives the lines of
# merges none for an id that they hold one for
def Waits.asked_less(
  +name: String,
  +s: Facts.Facts(),
  +i: Ledgers.Id,
  +n: Nat,
  +r: Spec.Request,
  f: Types.Fact
) -> {
  RFacts.Request.is_start(r) == False{}: Bool
} -> {
  RKnown.Mergers.fresh(
    RKnown.Mergers.of(RFacts.Facts.list(Facts.Facts.crit(s))),
    Types.Fact.Ask{Types.Ask{i, n, r}}
  )
    == True{}: Bool
} -> {
  RKnown.Fact.waits(
    RKnown.Scene{
      RKnown.Known.none(),
      Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
    },
    f
  )
    == True{}: Bool
} -> {RKnown.Fact.waits(RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}, f) == True{}: Bool}:
  match f:
    case Types.Fact.Vote{+v, Types.Step.Broken{}, +x}:
      e => hfr => h => Reads.Eq.to(
        Bool,
        b => {b == True{}: Bool},
        RKnown.Fact.waits(
          RKnown.Scene{
            RKnown.Known.none(),
            Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
          },
          Types.Fact.Vote{v, Types.Step.Broken{}, x}
        ),
        RKnown.Fact.waits(
          RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)},
          Types.Fact.Vote{v, Types.Step.Broken{}, x}
        ),
        ({==}),
        h
      )
    case Types.Fact.Vote{+v, Types.Step.At{+c2, +k2, +t2}, +x}:
      e => hfr => h => Reads.Eq.to(
        Bool,
        b => {b == True{}: Bool},
        RKnown.Fact.waits(
          RKnown.Scene{
            RKnown.Known.none(),
            Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
          },
          Types.Fact.Vote{v, Types.Step.At{c2, k2, t2}, x}
        ),
        RKnown.Fact.waits(
          RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)},
          Types.Fact.Vote{v, Types.Step.At{c2, k2, t2}, x}
        ),
        (
          Equal.cong(
            Maybe<&2, RLines.State>,
            Bool,
            m => RKnown.Slot.waits(m, k2),
            Lines.Line.state(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}), c2),
            Lines.Line.state(s, c2),
            Moves.Line.state_asked(name, s, Types.Ask{i, n, r}, c2)(e)
          )
        ),
        h
      )
    case Types.Fact.Ask{Types.Ask{+i2, +n2, Spec.Request.Start{+os}}}:
      e => hfr => h => Reads.Eq.to(
        Bool,
        b => {b == True{}: Bool},
        RKnown.Fact.waits(
          RKnown.Scene{
            RKnown.Known.none(),
            Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
          },
          Types.Fact.Ask{Types.Ask{i2, n2, Spec.Request.Start{os}}}
        ),
        RKnown.Fact.waits(
          RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)},
          Types.Fact.Ask{Types.Ask{i2, n2, Spec.Request.Start{os}}}
        ),
        ({==}),
        h
      )
    case Types.Fact.Ask{Types.Ask{+i2, +n2, Spec.Request.Write{+b2, +p2, +w2}}}:
      e => hfr => h => Reads.Eq.to(
        Bool,
        b => {b == True{}: Bool},
        RKnown.Fact.waits(
          RKnown.Scene{
            RKnown.Known.none(),
            Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
          },
          Types.Fact.Ask{Types.Ask{i2, n2, Spec.Request.Write{b2, p2, w2}}}
        ),
        RKnown.Fact.waits(
          RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)},
          Types.Fact.Ask{Types.Ask{i2, n2, Spec.Request.Write{b2, p2, w2}}}
        ),
        (
          Equal.cong(
            Maybe<&2, RLines.State>,
            Bool,
            m => RKnown.Id.waits(m, RKnown.Known.none(), b2, i2),
            Lines.Line.state(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}), b2),
            Lines.Line.state(s, b2),
            Moves.Line.state_asked(name, s, Types.Ask{i, n, r}, b2)(e)
          )
        ),
        h
      )
    case Types.Fact.Ask{Types.Ask{+i2, +n2, Spec.Request.Merge{+f2, +x2}}}:
      e => hfr => h => Reads.Eq.to(
        Bool,
        b => {b == True{}: Bool},
        RKnown.Fact.waits(
          RKnown.Scene{
            RKnown.Known.none(),
            Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
          },
          Types.Fact.Ask{Types.Ask{i2, n2, Spec.Request.Merge{f2, x2}}}
        ),
        RKnown.Fact.waits(
          RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)},
          Types.Fact.Ask{Types.Ask{i2, n2, Spec.Request.Merge{f2, x2}}}
        ),
        (
          Equal.cong(
            Maybe<&2, RLines.State>,
            Bool,
            m => RKnown.Id.waits(m, RKnown.Known.none(), x2, i2),
            Lines.Line.state(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}), x2),
            Lines.Line.state(s, x2),
            Moves.Line.state_asked(name, s, Types.Ask{i, n, r}, x2)(e)
          )
        ),
        h
      )
    case Types.Fact.Ask{Types.Ask{+i2, +n2, Spec.Request.Resolve{+m2, +p2, +w2}}}:
      +e => hfr => h => Lists.Maybe.by(
        Ledgers.Line,
        l => {
          RKnown.Resolve.waits(l, RKnown.Known.none(), Facts.Facts.crit(s), i2) == True{}: Bool
        },
        RKnown.Merge.line(RFacts.Facts.list(Facts.Facts.crit(s)), m2),
        en => {==},
        +c => es => Reads.Eq.to(
          Bool,
          b => {b == True{}: Bool},
          RKnown.Resolve.waits(
            Some{c},
            RKnown.Known.none(),
            Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})),
            i2
          ),
          RKnown.Resolve.waits(Some{c}, RKnown.Known.none(), Facts.Facts.crit(s), i2),
          Resolve.waits_asked(Some{c}, name, s, i, n, r, i2)(e),
          Reads.Eq.to(
            Maybe<&2, Ledgers.Line>,
            l => {
              RKnown.Resolve.waits(
                l,
                RKnown.Known.none(),
                Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})),
                i2
              )
                == True{}: Bool
            },
            RKnown.Merge.line(
              RFacts.Facts.list(
                Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
              ),
              m2
            ),
            Some{c},
            Equal.trans(
              Maybe<&2, Ledgers.Line>,
              RKnown.Merge.line(
                RFacts.Facts.list(
                  Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
                ),
                m2
              ),
              RKnown.Merge.line(
                Orders.Values.insert(
                  ~Types.Fact,
                  ~Coded.Fact.words,
                  RFacts.Facts.list(Facts.Facts.crit(s)),
                  Types.Fact.Ask{Types.Ask{i, n, r}}
                ),
                m2
              ),
              Some{c},
              Equal.cong(
                List<&2, Types.Fact>,
                Maybe<&2, Ledgers.Line>,
                l => RKnown.Merge.line(l, m2),
                RFacts.Facts.list(
                  Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
                ),
                Orders.Values.insert(
                  ~Types.Fact,
                  ~Coded.Fact.words,
                  RFacts.Facts.list(Facts.Facts.crit(s)),
                  Types.Fact.Ask{Types.Ask{i, n, r}}
                ),
                Asked.list(name, s, i, n, r)(e)
              ),
              Mergers.Merge.line_insert_keep(
                RFacts.Facts.list(Facts.Facts.crit(s)),
                Types.Fact.Ask{Types.Ask{i, n, r}},
                m2,
                c
              )(hfr)(es)
            ),
            h
          )
        )
      )
    case Types.Fact.Ask{Types.Ask{+i2, +n2, Spec.Request.Mark{+b2, +m2, +v2}}}:
      e => hfr => h => Reads.Eq.to(
        Bool,
        b => {b == True{}: Bool},
        RKnown.Fact.waits(
          RKnown.Scene{
            RKnown.Known.none(),
            Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
          },
          Types.Fact.Ask{Types.Ask{i2, n2, Spec.Request.Mark{b2, m2, v2}}}
        ),
        RKnown.Fact.waits(
          RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)},
          Types.Fact.Ask{Types.Ask{i2, n2, Spec.Request.Mark{b2, m2, v2}}}
        ),
        (
          Equal.cong(
            Maybe<&2, RLines.State>,
            Bool,
            m => RKnown.Id.waits(m, RKnown.Known.none(), b2, i2),
            Lines.Line.state(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}), b2),
            Lines.Line.state(s, b2),
            Moves.Line.state_asked(name, s, Types.Ask{i, n, r}, b2)(e)
          )
        ),
        h
      )
    case Types.Fact.Ask{Types.Ask{+i2, +n2, Spec.Request.Move{+b2, +t2, +v2}}}:
      e => hfr => h => Reads.Eq.to(
        Bool,
        b => {b == True{}: Bool},
        RKnown.Fact.waits(
          RKnown.Scene{
            RKnown.Known.none(),
            Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
          },
          Types.Fact.Ask{Types.Ask{i2, n2, Spec.Request.Move{b2, t2, v2}}}
        ),
        RKnown.Fact.waits(
          RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)},
          Types.Fact.Ask{Types.Ask{i2, n2, Spec.Request.Move{b2, t2, v2}}}
        ),
        (
          Equal.cong(
            Maybe<&2, RLines.State>,
            Bool,
            m => RKnown.Id.waits(m, RKnown.Known.none(), b2, i2),
            Lines.Line.state(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}), b2),
            Lines.Line.state(s, b2),
            Moves.Line.state_asked(name, s, Types.Ask{i, n, r}, b2)(e)
          )
        ),
        h
      )
    case Types.Fact.Ask{Types.Ask{+i2, +n2, Spec.Request.Group{+h2, +g2, +ms2}}}:
      e => hfr => h => Reads.Eq.to(
        Bool,
        b => {b == True{}: Bool},
        RKnown.Fact.waits(
          RKnown.Scene{
            RKnown.Known.none(),
            Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
          },
          Types.Fact.Ask{Types.Ask{i2, n2, Spec.Request.Group{h2, g2, ms2}}}
        ),
        RKnown.Fact.waits(
          RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)},
          Types.Fact.Ask{Types.Ask{i2, n2, Spec.Request.Group{h2, g2, ms2}}}
        ),
        (
          Equal.cong(
            Maybe<&2, RLines.State>,
            Bool,
            m => RKnown.Id.waits(m, RKnown.Known.none(), Ledgers.Line{h2, None{}}, i2),
            Lines.Line.state(
              Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}),
              Ledgers.Line{h2, None{}}
            ),
            Lines.Line.state(s, Ledgers.Line{h2, None{}}),
            Moves.Line.state_asked(name, s, Types.Ask{i, n, r}, Ledgers.Line{h2, None{}})(e)
          )
        ),
        h
      )
    case Types.Fact.Ask{Types.Ask{+i2, +n2, Spec.Request.Own{Ledgers.Line{+h2, +b2}, +g2}}}:
      e => hfr => h => Reads.Eq.to(
        Bool,
        b => {b == True{}: Bool},
        RKnown.Fact.waits(
          RKnown.Scene{
            RKnown.Known.none(),
            Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
          },
          Types.Fact.Ask{Types.Ask{i2, n2, Spec.Request.Own{Ledgers.Line{h2, b2}, g2}}}
        ),
        RKnown.Fact.waits(
          RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)},
          Types.Fact.Ask{Types.Ask{i2, n2, Spec.Request.Own{Ledgers.Line{h2, b2}, g2}}}
        ),
        (
          Equal.cong(
            Maybe<&2, RLines.State>,
            Bool,
            m => RKnown.Id.waits(m, RKnown.Known.none(), Ledgers.Line{h2, None{}}, i2),
            Lines.Line.state(
              Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}),
              Ledgers.Line{h2, None{}}
            ),
            Lines.Line.state(s, Ledgers.Line{h2, None{}}),
            Moves.Line.state_asked(name, s, Types.Ask{i, n, r}, Ledgers.Line{h2, None{}})(e)
          )
        ),
        h
      )

# the facts that a work may act on after a node takes in an ask, among those
# that it could act on before, are all that it may act on
def Open.twice(
  +name: String,
  +s: Facts.Facts(),
  +i: Ledgers.Id,
  +n: Nat,
  +r: Spec.Request,
  xs: List<&2, Types.Fact>
) -> {
  RFacts.Request.is_start(r) == False{}: Bool
} -> {
  RKnown.Mergers.fresh(
    RKnown.Mergers.of(RFacts.Facts.list(Facts.Facts.crit(s))),
    Types.Fact.Ask{Types.Ask{i, n, r}}
  )
    == True{}: Bool
} -> {
  RKnown.Open.of(
    RKnown.Open.of(xs, RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}),
    RKnown.Scene{
      RKnown.Known.none(),
      Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
    }
  )
    == RKnown.Open.of(
      xs,
      RKnown.Scene{
        RKnown.Known.none(),
        Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
      }
    ): List<&2, Types.Fact>
}:
  match xs:
    case Nil{}:
      e => hfr => {==}
    case Con{+g, +rest}:
      +e => +hfr => Lists.Bool.by(
        d => {
          RKnown.Open.of(
            List.filter.put(
              Types.Fact,
              g,
              RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}),
              d
            ),
            RKnown.Scene{
              RKnown.Known.none(),
              Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
            }
          )
            == List.filter.put(
              Types.Fact,
              g,
              RKnown.Open.of(
                rest,
                RKnown.Scene{
                  RKnown.Known.none(),
                  Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
                }
              ),
              RKnown.Fact.waits(
                RKnown.Scene{
                  RKnown.Known.none(),
                  Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
                },
                g
              )
            ): List<&2, Types.Fact>
        },
        RKnown.Fact.waits(RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}, g),
        et => Equal.cong(
          List<&2, Types.Fact>,
          List<&2, Types.Fact>,
          l => List.filter.put(
            Types.Fact,
            g,
            l,
            RKnown.Fact.waits(
              RKnown.Scene{
                RKnown.Known.none(),
                Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
              },
              g
            )
          ),
          RKnown.Open.of(
            RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}),
            RKnown.Scene{
              RKnown.Known.none(),
              Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
            }
          ),
          RKnown.Open.of(
            rest,
            RKnown.Scene{
              RKnown.Known.none(),
              Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
            }
          ),
          Open.twice(name, s, i, n, r, rest)(e)(hfr)
        ),
        ef => Lists.Bool.by(
          d2 => {
            RKnown.Open.of(
              RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}),
              RKnown.Scene{
                RKnown.Known.none(),
                Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
              }
            )
              == List.filter.put(
                Types.Fact,
                g,
                RKnown.Open.of(
                  rest,
                  RKnown.Scene{
                    RKnown.Known.none(),
                    Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
                  }
                ),
                d2
              ): List<&2, Types.Fact>
          },
          RKnown.Fact.waits(
            RKnown.Scene{
              RKnown.Known.none(),
              Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
            },
            g
          ),
          e2 => Empty.absurd(
            {
              RKnown.Open.of(
                RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}),
                RKnown.Scene{
                  RKnown.Known.none(),
                  Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
                }
              )
                == List.filter.put(
                  Types.Fact,
                  g,
                  RKnown.Open.of(
                    rest,
                    RKnown.Scene{
                      RKnown.Known.none(),
                      Facts.Facts.crit(
                        Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})
                      )
                    }
                  ),
                  True{}
                ): List<&2, Types.Fact>
            },
            Shared.Bool.true_ne_false(
              Equal.trans(
                Bool,
                True{},
                RKnown.Fact.waits(RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}, g),
                False{},
                Equal.sym(
                  Bool,
                  RKnown.Fact.waits(RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}, g),
                  True{},
                  Waits.asked_less(name, s, i, n, r, g)(e)(hfr)(e2)
                ),
                ef
              )
            )
          ),
          e2 => Open.twice(name, s, i, n, r, rest)(e)(hfr)
        )
      )

# the facts that a work may act on, with the ask of a merge that the node
# takes in, each tested again: all that a work may act on after
def Asked.open_merge(
  +name: String,
  +s: Facts.Facts(),
  +i: Ledgers.Id,
  +n: Nat,
  +r: Spec.Request,
  +fs: List<&2, Types.Fact>,
  +kn: RKnown.Known()
) -> {
  RFacts.Request.is_start(r) == False{}: Bool
} -> {
  RContents.Known.ok(
    kn,
    Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
  )
    == True{}: Bool
} -> {
  RContents.Shelf.led(
    RKnown.Known.shelf(kn),
    Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
  )
    == True{}: Bool
} -> {
  RKnown.Request.merges(r) == True{}: Bool
} -> {
  RKnown.Mergers.fresh(
    RKnown.Mergers.of(RFacts.Facts.list(Facts.Facts.crit(s))),
    Types.Fact.Ask{Types.Ask{i, n, r}}
  )
    == True{}: Bool
} -> {
  fs
    == RKnown.Open.of(
      RFacts.Facts.list(Facts.Facts.crit(s)),
      RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}
    ): List<&2, Types.Fact>
} -> {
  RKnown.Open.of(
    RKnown.Open.with(
      fs,
      Types.Fact.Ask{Types.Ask{i, n, r}},
      RKnown.Scene{
        kn,
        Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
      }
    ),
    RKnown.Scene{
      kn,
      Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
    }
  )
    == RKnown.Open.of(
      RFacts.Facts.list(
        Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
      ),
      RKnown.Scene{
        RKnown.Known.none(),
        Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
      }
    ): List<&2, Types.Fact>
}:
  +e => +ok => +hl => ht => hfr => efs => Equal.trans(
    List<&2, Types.Fact>,
    RKnown.Open.of(
      RKnown.Open.with(
        fs,
        Types.Fact.Ask{Types.Ask{i, n, r}},
        RKnown.Scene{
          kn,
          Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
        }
      ),
      RKnown.Scene{
        kn,
        Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
      }
    ),
    RKnown.Open.of(
      RKnown.Open.of(
        RFacts.Facts.list(
          Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
        ),
        RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}
      ),
      RKnown.Scene{
        RKnown.Known.none(),
        Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
      }
    ),
    RKnown.Open.of(
      RFacts.Facts.list(
        Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
      ),
      RKnown.Scene{
        RKnown.Known.none(),
        Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
      }
    ),
    Equal.trans(
      List<&2, Types.Fact>,
      RKnown.Open.of(
        RKnown.Open.with(
          fs,
          Types.Fact.Ask{Types.Ask{i, n, r}},
          RKnown.Scene{
            kn,
            Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
          }
        ),
        RKnown.Scene{
          kn,
          Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
        }
      ),
      RKnown.Open.of(
        RKnown.Open.with(
          fs,
          Types.Fact.Ask{Types.Ask{i, n, r}},
          RKnown.Scene{
            kn,
            Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
          }
        ),
        RKnown.Scene{
          RKnown.Known.none(),
          Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
        }
      ),
      RKnown.Open.of(
        RKnown.Open.of(
          RFacts.Facts.list(
            Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
          ),
          RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}
        ),
        RKnown.Scene{
          RKnown.Known.none(),
          Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
        }
      ),
      Open.of_ok(
        kn,
        Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})),
        RKnown.Open.with(
          fs,
          Types.Fact.Ask{Types.Ask{i, n, r}},
          RKnown.Scene{
            kn,
            Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
          }
        )
      )(ok)(hl),
      Equal.cong(
        List<&2, Types.Fact>,
        List<&2, Types.Fact>,
        l => RKnown.Open.of(
          l,
          RKnown.Scene{
            RKnown.Known.none(),
            Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
          }
        ),
        RKnown.Open.with(
          fs,
          Types.Fact.Ask{Types.Ask{i, n, r}},
          RKnown.Scene{
            kn,
            Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
          }
        ),
        RKnown.Open.of(
          RFacts.Facts.list(
            Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
          ),
          RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}
        ),
        Asked.open_old(name, s, i, n, r, fs, kn)(e)(ok)(hl)(ht)(efs)
      )
    ),
    Open.twice(
      name,
      s,
      i,
      n,
      r,
      RFacts.Facts.list(
        Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
      )
    )(e)(hfr)
  )

# a table that holds an entry for a work is the table with the facts that a
# work may act on after a fact joined the facts, in the place of its entry
def Known.sift_at(
  +kn2: RKnown.Known(),
  +s2: RFacts.Plain(),
  +f: Types.Fact,
  +fs: List<&2, Types.Fact>,
  +n: Nat,
  +tx: Crits.Crit<Types.Ask>,
  +mx: Crits.Crit<Ledgers.Line>
) -> {
  RKnown.Known.shelf(kn2) == Some{RKnown.Open{fs, n, tx, mx}}: Maybe<&2, RKnown.Kept>
} -> {
  RKnown.Known.sift(
    kn2,
    s2,
    f
  )
    == RKnown.Known.reopen(
      kn2,
      RKnown.Open.join(RKnown.Fact.merges(f), fs, f, RKnown.Scene{kn2, s2}),
      n,
      tx,
      mx
    ): RKnown.Known()
}:
  e => Reads.Eq.back(
    Maybe<&2, RKnown.Kept>,
    m => {
      RKnown.Known.sift.of(
        m,
        kn2,
        s2,
        f
      )
        == RKnown.Known.reopen(
          kn2,
          RKnown.Open.join(RKnown.Fact.merges(f), fs, f, RKnown.Scene{kn2, s2}),
          n,
          tx,
          mx
        ): RKnown.Known()
    },
    RKnown.Known.shelf(kn2),
    Some{RKnown.Open{fs, n, tx, mx}},
    e,
    {==}
  )

# a right table that holds an entry for a work, with the right facts, number,
# newest writes and lines of merges in its place, fits
def Joined.fits(
  +kn2: RKnown.Known(),
  +s2: RFacts.Plain(),
  +xs: List<&2, Types.Fact>,
  +n2: Nat,
  +tx2: Crits.Crit<Types.Ask>,
  +mx2: Crits.Crit<Ledgers.Line>,
  -fs0: List<&2, Types.Fact>,
  -n0: Nat,
  -tx0: Crits.Crit<Types.Ask>,
  -mx0: Crits.Crit<Ledgers.Line>
) -> {
  RContents.Known.ok(kn2, s2) == True{}: Bool
} -> {
  RKnown.Known.shelf(kn2) == Some{RKnown.Open{fs0, n0, tx0, mx0}}: Maybe<&2, RKnown.Kept>
} -> {
  xs
    == RKnown.Open.of(
      RFacts.Facts.list(s2),
      RKnown.Scene{RKnown.Known.none(), s2}
    ): List<&2, Types.Fact>
} -> {
  n2 == RFacts.Seq.peak(RFacts.Facts.list(s2)): Nat
} -> {
  tx2 == RKnown.Tops.of(RFacts.Facts.list(s2)): Crits.Crit<Types.Ask>
} -> {
  mx2 == RKnown.Mergers.of(RFacts.Facts.list(s2)): Crits.Crit<Ledgers.Line>
} -> {RContents.Known.fit(RKnown.Known.reopen(kn2, xs, n2, tx2, mx2), s2) == True{}: Bool}:
  ok => esh => ex => en => etx => emx => Fit.both(
    RKnown.Known.reopen(kn2, xs, n2, tx2, mx2),
    s2
  )(Known.reopen_ok(kn2, s2, xs, n2, tx2, mx2)(ok))((
      %Equal.sym(Maybe<&2, RKnown.Kept>, RKnown.Known.shelf(RKnown.Known.reopen(kn2, xs, n2, tx2, mx2)), Some{RKnown.Open{xs, n2, tx2, mx2}}, Known.reopen_shelf(kn2, xs, n2, tx2, mx2, fs0, n0, tx0, mx0)(esh)): {RContents.Shelf.fits(_, s2) == True{}: Bool}
      Open.fits_of(xs, n2, tx2, mx2, s2)(Shared.Bool.and_both(Shared.List.is_eq(~Types.Fact, ~Coded.Fact.is_eq, xs, RKnown.Open.of(RFacts.Facts.list(s2), RKnown.Scene{RKnown.Known.none(), s2})), Nat.is_eq(n2, RFacts.Seq.peak(RFacts.Facts.list(s2))))(Reads.Eq.back(List<&2, Types.Fact>, y => {Shared.List.is_eq(~Types.Fact, ~Coded.Fact.is_eq, y, RKnown.Open.of(RFacts.Facts.list(s2), RKnown.Scene{RKnown.Known.none(), s2})) == True{}: Bool}, xs, RKnown.Open.of(RFacts.Facts.list(s2), RKnown.Scene{RKnown.Known.none(), s2}), ex, Shared.List.is_eq_refl(~Types.Fact, ~Coded.Fact.is_eq, ~Coded.Fact.laws(), RKnown.Open.of(RFacts.Facts.list(s2), RKnown.Scene{RKnown.Known.none(), s2}))))(Reads.Eq.back(Nat, y => {Nat.is_eq(y, RFacts.Seq.peak(RFacts.Facts.list(s2))) == True{}: Bool}, n2, RFacts.Seq.peak(RFacts.Facts.list(s2)), en, Shared.Nat.is_eq_refl(RFacts.Seq.peak(RFacts.Facts.list(s2))))))(etx)(emx)))

# a right table without what it holds for a work is right
def Known.shut_ok(
  kn: RKnown.Known(),
  +s: RFacts.Plain()
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {RContents.Known.ok(RKnown.Known.shut(kn), s) == True{}: Bool}:
  match kn:
    case Nil{}:
      ok => {==}
    case Con{RKnown.Kept{+c2, +st2}, +rest}:
      +ok => Ok.cons(
        RKnown.Kept{c2, st2},
        RKnown.Known.shut(rest),
        s
      )(
        Ok.head(RKnown.Kept{c2, st2}, rest, s)(ok)
      )(Known.shut_ok(rest, s)(Ok.tail(RKnown.Kept{c2, st2}, rest, s)(ok)))
    case Con{RKnown.Stock{+m2, +lwm2}, +rest}:
      +ok => Ok.cons(
        RKnown.Stock{m2, lwm2},
        RKnown.Known.shut(rest),
        s
      )(
        Ok.head(RKnown.Stock{m2, lwm2}, rest, s)(ok)
      )(Known.shut_ok(rest, s)(Ok.tail(RKnown.Stock{m2, lwm2}, rest, s)(ok)))
    case Con{RKnown.Ruled{+c2, +zu2, +u2}, +rest}:
      +ok => Ok.cons(
        RKnown.Ruled{c2, zu2, u2},
        RKnown.Known.shut(rest),
        s
      )(
        Ok.head(RKnown.Ruled{c2, zu2, u2}, rest, s)(ok)
      )(Known.shut_ok(rest, s)(Ok.tail(RKnown.Ruled{c2, zu2, u2}, rest, s)(ok)))
    case Con{RKnown.Made{+c2, +y2}, +rest}:
      +ok => Ok.cons(
        RKnown.Made{c2, y2},
        RKnown.Known.shut(rest),
        s
      )(
        Ok.head(RKnown.Made{c2, y2}, rest, s)(ok)
      )(Known.shut_ok(rest, s)(Ok.tail(RKnown.Made{c2, y2}, rest, s)(ok)))
    case Con{RKnown.Open{+fs2, +pk2, +tx9, +mtx9}, +rest}:
      ok => Known.shut_ok(rest, s)(Ok.tail(RKnown.Open{fs2, pk2, tx9, mtx9}, rest, s)(ok))

# a table without what it holds for a work holds nothing for a work
def Known.shut_shelf(
  kn: RKnown.Known()
) -> {RKnown.Known.shelf(RKnown.Known.shut(kn)) == None{}: Maybe<&2, RKnown.Kept>}:
  match kn:
    case Nil{}:
      {==}
    case Con{RKnown.Kept{c2, st2}, rest}:
      Known.shut_shelf(rest)
    case Con{RKnown.Stock{m2, lwm2}, rest}:
      {==}
    case Con{RKnown.Ruled{c2, zu2, u2}, rest}:
      Known.shut_shelf(rest)
    case Con{RKnown.Made{c2, y2}, rest}:
      Known.shut_shelf(rest)
    case Con{RKnown.Open{fs2, pk2, tx9, mtx9}, rest}:
      Known.shut_shelf(rest)

# Known.joined_fit, with the entry m that the table holds for a work
def Known.joined_fit.at(
  m: Maybe<&2, RKnown.Kept>,
  +kn: RKnown.Known(),
  +name: String,
  +s: Facts.Facts(),
  +i: Ledgers.Id,
  +n: Nat,
  +r: Spec.Request
) -> {
  RKnown.Known.shelf(kn) == m: Maybe<&2, RKnown.Kept>
} -> {
  RFacts.Request.is_start(r) == False{}: Bool
} -> {
  RContents.Known.ok(
    kn,
    Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
  )
    == True{}: Bool
} -> {
  RContents.Shelf.fits(m, Facts.Facts.crit(s)) == True{}: Bool
} -> {
  RContents.Known.fit(
    RKnown.Known.joined.of(
      m,
      kn,
      Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})),
      Types.Fact.Ask{Types.Ask{i, n, r}}
    ),
    Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
  )
    == True{}: Bool
}:
  match m:
    case None{}:
      em => e => ok => hf => Fit.both(
        kn,
        Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
      )(ok)((
          %Equal.sym(Maybe<&2, RKnown.Kept>, RKnown.Known.shelf(kn), None{}, em): {RContents.Shelf.fits(_, Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))) == True{}: Bool}
          {==}))
    case Some{RKnown.Kept{c2, st2}}:
      em => e => ok => hf => Fit.both(
        kn,
        Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
      )(ok)((
          %Equal.sym(Maybe<&2, RKnown.Kept>, RKnown.Known.shelf(kn), Some{RKnown.Kept{c2, st2}}, em): {RContents.Shelf.fits(_, Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))) == True{}: Bool}
          {==}))
    case Some{RKnown.Stock{m2, lwm2}}:
      em => e => ok => hf => Fit.both(
        kn,
        Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
      )(ok)((
          %Equal.sym(Maybe<&2, RKnown.Kept>, RKnown.Known.shelf(kn), Some{RKnown.Stock{m2, lwm2}}, em): {RContents.Shelf.fits(_, Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))) == True{}: Bool}
          {==}))
    case Some{RKnown.Ruled{c2, zu2, u2}}:
      em => e => ok => hf => Fit.both(
        kn,
        Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
      )(ok)((
          %Equal.sym(Maybe<&2, RKnown.Kept>, RKnown.Known.shelf(kn), Some{RKnown.Ruled{c2, zu2, u2}}, em): {RContents.Shelf.fits(_, Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))) == True{}: Bool}
          {==}))
    case Some{RKnown.Made{c2, y2}}:
      em => e => ok => hf => Fit.both(
        kn,
        Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
      )(ok)((
          %Equal.sym(Maybe<&2, RKnown.Kept>, RKnown.Known.shelf(kn), Some{RKnown.Made{c2, y2}}, em): {RContents.Shelf.fits(_, Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))) == True{}: Bool}
          {==}))
    case Some{RKnown.Open{+fs, +n0, +tx9, +mtx9}}:
      +em => +e => +ok => +hf => Lists.Bool.by(
        d => {
          RContents.Known.fit(
            Shared.Bool.when(
              RKnown.Known(),
              d,
              u => RKnown.Known.sift(
                RKnown.Known.reopen(
                  kn,
                  fs,
                  Nat.max(n, n0),
                  Shared.Bool.when(
                    Crits.Crit<Types.Ask>,
                    Nat.is_lt(n0, n),
                    u => RKnown.Tops.join(tx9, Types.Fact.Ask{Types.Ask{i, n, r}}),
                    u => RKnown.Tops.of(
                      RFacts.Facts.list(
                        Facts.Facts.crit(
                          Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})
                        )
                      )
                    )
                  ),
                  RKnown.Mergers.step(mtx9, Types.Fact.Ask{Types.Ask{i, n, r}})
                ),
                Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})),
                Types.Fact.Ask{Types.Ask{i, n, r}}
              ),
              u => RKnown.Known.shut(kn)
            ),
            Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
          )
            == True{}: Bool
        },
        RKnown.Mergers.fresh(mtx9, Types.Fact.Ask{Types.Ask{i, n, r}}),
        +hfr => Reads.Eq.back(
          RKnown.Known(),
          y => {
            RContents.Known.fit(
              y,
              Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
            )
              == True{}: Bool
          },
          RKnown.Known.sift(
            RKnown.Known.reopen(
              kn,
              fs,
              Nat.max(n, n0),
              Shared.Bool.when(
                Crits.Crit<Types.Ask>,
                Nat.is_lt(n0, n),
                u => RKnown.Tops.join(tx9, Types.Fact.Ask{Types.Ask{i, n, r}}),
                u => RKnown.Tops.of(
                  RFacts.Facts.list(
                    Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
                  )
                )
              ),
              RKnown.Mergers.step(mtx9, Types.Fact.Ask{Types.Ask{i, n, r}})
            ),
            Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})),
            Types.Fact.Ask{Types.Ask{i, n, r}}
          ),
          RKnown.Known.reopen(
            RKnown.Known.reopen(
              kn,
              fs,
              Nat.max(n, n0),
              Shared.Bool.when(
                Crits.Crit<Types.Ask>,
                Nat.is_lt(n0, n),
                u => RKnown.Tops.join(tx9, Types.Fact.Ask{Types.Ask{i, n, r}}),
                u => RKnown.Tops.of(
                  RFacts.Facts.list(
                    Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
                  )
                )
              ),
              RKnown.Mergers.step(mtx9, Types.Fact.Ask{Types.Ask{i, n, r}})
            ),
            RKnown.Open.join(
              RKnown.Fact.merges(Types.Fact.Ask{Types.Ask{i, n, r}}),
              fs,
              Types.Fact.Ask{Types.Ask{i, n, r}},
              RKnown.Scene{
                RKnown.Known.reopen(
                  kn,
                  fs,
                  Nat.max(n, n0),
                  Shared.Bool.when(
                    Crits.Crit<Types.Ask>,
                    Nat.is_lt(n0, n),
                    u => RKnown.Tops.join(tx9, Types.Fact.Ask{Types.Ask{i, n, r}}),
                    u => RKnown.Tops.of(
                      RFacts.Facts.list(
                        Facts.Facts.crit(
                          Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})
                        )
                      )
                    )
                  ),
                  RKnown.Mergers.step(mtx9, Types.Fact.Ask{Types.Ask{i, n, r}})
                ),
                Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
              }
            ),
            Nat.max(n, n0),
            Shared.Bool.when(
              Crits.Crit<Types.Ask>,
              Nat.is_lt(n0, n),
              u => RKnown.Tops.join(tx9, Types.Fact.Ask{Types.Ask{i, n, r}}),
              u => RKnown.Tops.of(
                RFacts.Facts.list(
                  Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
                )
              )
            ),
            RKnown.Mergers.step(mtx9, Types.Fact.Ask{Types.Ask{i, n, r}})
          ),
          Known.sift_at(
            RKnown.Known.reopen(
              kn,
              fs,
              Nat.max(n, n0),
              Shared.Bool.when(
                Crits.Crit<Types.Ask>,
                Nat.is_lt(n0, n),
                u => RKnown.Tops.join(tx9, Types.Fact.Ask{Types.Ask{i, n, r}}),
                u => RKnown.Tops.of(
                  RFacts.Facts.list(
                    Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
                  )
                )
              ),
              RKnown.Mergers.step(mtx9, Types.Fact.Ask{Types.Ask{i, n, r}})
            ),
            Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})),
            Types.Fact.Ask{Types.Ask{i, n, r}},
            fs,
            Nat.max(n, n0),
            Shared.Bool.when(
              Crits.Crit<Types.Ask>,
              Nat.is_lt(n0, n),
              u => RKnown.Tops.join(tx9, Types.Fact.Ask{Types.Ask{i, n, r}}),
              u => RKnown.Tops.of(
                RFacts.Facts.list(
                  Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
                )
              )
            ),
            RKnown.Mergers.step(mtx9, Types.Fact.Ask{Types.Ask{i, n, r}})
          )(
            Known.reopen_shelf(
              kn,
              fs,
              Nat.max(n, n0),
              Shared.Bool.when(
                Crits.Crit<Types.Ask>,
                Nat.is_lt(n0, n),
                u => RKnown.Tops.join(tx9, Types.Fact.Ask{Types.Ask{i, n, r}}),
                u => RKnown.Tops.of(
                  RFacts.Facts.list(
                    Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
                  )
                )
              ),
              RKnown.Mergers.step(mtx9, Types.Fact.Ask{Types.Ask{i, n, r}}),
              fs,
              n0,
              tx9,
              mtx9
            )(em)
          ),
          Joined.fits(
            RKnown.Known.reopen(
              kn,
              fs,
              Nat.max(n, n0),
              Shared.Bool.when(
                Crits.Crit<Types.Ask>,
                Nat.is_lt(n0, n),
                u => RKnown.Tops.join(tx9, Types.Fact.Ask{Types.Ask{i, n, r}}),
                u => RKnown.Tops.of(
                  RFacts.Facts.list(
                    Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
                  )
                )
              ),
              RKnown.Mergers.step(mtx9, Types.Fact.Ask{Types.Ask{i, n, r}})
            ),
            Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})),
            RKnown.Open.join(
              RKnown.Fact.merges(Types.Fact.Ask{Types.Ask{i, n, r}}),
              fs,
              Types.Fact.Ask{Types.Ask{i, n, r}},
              RKnown.Scene{
                RKnown.Known.reopen(
                  kn,
                  fs,
                  Nat.max(n, n0),
                  Shared.Bool.when(
                    Crits.Crit<Types.Ask>,
                    Nat.is_lt(n0, n),
                    u => RKnown.Tops.join(tx9, Types.Fact.Ask{Types.Ask{i, n, r}}),
                    u => RKnown.Tops.of(
                      RFacts.Facts.list(
                        Facts.Facts.crit(
                          Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})
                        )
                      )
                    )
                  ),
                  RKnown.Mergers.step(mtx9, Types.Fact.Ask{Types.Ask{i, n, r}})
                ),
                Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
              }
            ),
            Nat.max(n, n0),
            Shared.Bool.when(
              Crits.Crit<Types.Ask>,
              Nat.is_lt(n0, n),
              u => RKnown.Tops.join(tx9, Types.Fact.Ask{Types.Ask{i, n, r}}),
              u => RKnown.Tops.of(
                RFacts.Facts.list(
                  Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
                )
              )
            ),
            RKnown.Mergers.step(mtx9, Types.Fact.Ask{Types.Ask{i, n, r}}),
            fs,
            Nat.max(n, n0),
            Shared.Bool.when(
              Crits.Crit<Types.Ask>,
              Nat.is_lt(n0, n),
              u => RKnown.Tops.join(tx9, Types.Fact.Ask{Types.Ask{i, n, r}}),
              u => RKnown.Tops.of(
                RFacts.Facts.list(
                  Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
                )
              )
            ),
            RKnown.Mergers.step(mtx9, Types.Fact.Ask{Types.Ask{i, n, r}})
          )(
            Known.reopen_ok(
              kn,
              Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})),
              fs,
              Nat.max(n, n0),
              Shared.Bool.when(
                Crits.Crit<Types.Ask>,
                Nat.is_lt(n0, n),
                u => RKnown.Tops.join(tx9, Types.Fact.Ask{Types.Ask{i, n, r}}),
                u => RKnown.Tops.of(
                  RFacts.Facts.list(
                    Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
                  )
                )
              ),
              RKnown.Mergers.step(mtx9, Types.Fact.Ask{Types.Ask{i, n, r}})
            )(ok)
          )(
            Known.reopen_shelf(
              kn,
              fs,
              Nat.max(n, n0),
              Shared.Bool.when(
                Crits.Crit<Types.Ask>,
                Nat.is_lt(n0, n),
                u => RKnown.Tops.join(tx9, Types.Fact.Ask{Types.Ask{i, n, r}}),
                u => RKnown.Tops.of(
                  RFacts.Facts.list(
                    Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
                  )
                )
              ),
              RKnown.Mergers.step(mtx9, Types.Fact.Ask{Types.Ask{i, n, r}}),
              fs,
              n0,
              tx9,
              mtx9
            )(em)
          )(
            Lists.Bool.by(
              d => {
                RKnown.Open.join(
                  d,
                  fs,
                  Types.Fact.Ask{Types.Ask{i, n, r}},
                  RKnown.Scene{
                    RKnown.Known.reopen(
                      kn,
                      fs,
                      Nat.max(n, n0),
                      Shared.Bool.when(
                        Crits.Crit<Types.Ask>,
                        Nat.is_lt(n0, n),
                        u => RKnown.Tops.join(tx9, Types.Fact.Ask{Types.Ask{i, n, r}}),
                        u => RKnown.Tops.of(
                          RFacts.Facts.list(
                            Facts.Facts.crit(
                              Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})
                            )
                          )
                        )
                      ),
                      RKnown.Mergers.step(mtx9, Types.Fact.Ask{Types.Ask{i, n, r}})
                    ),
                    Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
                  }
                )
                  == RKnown.Open.of(
                    RFacts.Facts.list(
                      Facts.Facts.crit(
                        Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})
                      )
                    ),
                    RKnown.Scene{
                      RKnown.Known.none(),
                      Facts.Facts.crit(
                        Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})
                      )
                    }
                  ): List<&2, Types.Fact>
              },
              RKnown.Fact.merges(Types.Fact.Ask{Types.Ask{i, n, r}}),
              et => Asked.open_merge(
                name,
                s,
                i,
                n,
                r,
                fs,
                RKnown.Known.reopen(
                  kn,
                  fs,
                  Nat.max(n, n0),
                  Shared.Bool.when(
                    Crits.Crit<Types.Ask>,
                    Nat.is_lt(n0, n),
                    u => RKnown.Tops.join(tx9, Types.Fact.Ask{Types.Ask{i, n, r}}),
                    u => RKnown.Tops.of(
                      RFacts.Facts.list(
                        Facts.Facts.crit(
                          Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})
                        )
                      )
                    )
                  ),
                  RKnown.Mergers.step(mtx9, Types.Fact.Ask{Types.Ask{i, n, r}})
                )
              )(
                e
              )(
                Known.reopen_ok(
                  kn,
                  Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})),
                  fs,
                  Nat.max(n, n0),
                  Shared.Bool.when(
                    Crits.Crit<Types.Ask>,
                    Nat.is_lt(n0, n),
                    u => RKnown.Tops.join(tx9, Types.Fact.Ask{Types.Ask{i, n, r}}),
                    u => RKnown.Tops.of(
                      RFacts.Facts.list(
                        Facts.Facts.crit(
                          Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})
                        )
                      )
                    )
                  ),
                  RKnown.Mergers.step(mtx9, Types.Fact.Ask{Types.Ask{i, n, r}})
                )(ok)
              )(
                Reads.Eq.back(
                  Maybe<&2, RKnown.Kept>,
                  m => {
                    RContents.Shelf.led(
                      m,
                      Facts.Facts.crit(
                        Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})
                      )
                    )
                      == True{}: Bool
                  },
                  RKnown.Known.shelf(
                    RKnown.Known.reopen(
                      kn,
                      fs,
                      Nat.max(n, n0),
                      Shared.Bool.when(
                        Crits.Crit<Types.Ask>,
                        Nat.is_lt(n0, n),
                        u => RKnown.Tops.join(tx9, Types.Fact.Ask{Types.Ask{i, n, r}}),
                        u => RKnown.Tops.of(
                          RFacts.Facts.list(
                            Facts.Facts.crit(
                              Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})
                            )
                          )
                        )
                      ),
                      RKnown.Mergers.step(mtx9, Types.Fact.Ask{Types.Ask{i, n, r}})
                    )
                  ),
                  Some{
                    RKnown.Open{
                      fs,
                      Nat.max(n, n0),
                      Shared.Bool.when(
                        Crits.Crit<Types.Ask>,
                        Nat.is_lt(n0, n),
                        u => RKnown.Tops.join(tx9, Types.Fact.Ask{Types.Ask{i, n, r}}),
                        u => RKnown.Tops.of(
                          RFacts.Facts.list(
                            Facts.Facts.crit(
                              Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})
                            )
                          )
                        )
                      ),
                      RKnown.Mergers.step(mtx9, Types.Fact.Ask{Types.Ask{i, n, r}})
                    }
                  },
                  Known.reopen_shelf(
                    kn,
                    fs,
                    Nat.max(n, n0),
                    Shared.Bool.when(
                      Crits.Crit<Types.Ask>,
                      Nat.is_lt(n0, n),
                      u => RKnown.Tops.join(tx9, Types.Fact.Ask{Types.Ask{i, n, r}}),
                      u => RKnown.Tops.of(
                        RFacts.Facts.list(
                          Facts.Facts.crit(
                            Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})
                          )
                        )
                      )
                    ),
                    RKnown.Mergers.step(mtx9, Types.Fact.Ask{Types.Ask{i, n, r}}),
                    fs,
                    n0,
                    tx9,
                    mtx9
                  )(em),
                  Mergers.Mergers.same_refl_of(
                    RKnown.Mergers.step(mtx9, Types.Fact.Ask{Types.Ask{i, n, r}}),
                    RKnown.Mergers.of(
                      RFacts.Facts.list(
                        Facts.Facts.crit(
                          Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})
                        )
                      )
                    )
                  )(
                    Reads.Eq.back(
                      Crits.Crit<Ledgers.Line>,
                      y => {
                        RKnown.Mergers.step(
                          y,
                          Types.Fact.Ask{Types.Ask{i, n, r}}
                        )
                          == RKnown.Mergers.of(
                            RFacts.Facts.list(
                              Facts.Facts.crit(
                                Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})
                              )
                            )
                          ): Crits.Crit<Ledgers.Line>
                      },
                      mtx9,
                      RKnown.Mergers.of(RFacts.Facts.list(Facts.Facts.crit(s))),
                      Open.fits_merges(fs, n0, tx9, mtx9, Facts.Facts.crit(s))(hf),
                      Equal.sym(
                        Crits.Crit<Ledgers.Line>,
                        RKnown.Mergers.of(
                          RFacts.Facts.list(
                            Facts.Facts.crit(
                              Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})
                            )
                          )
                        ),
                        RKnown.Mergers.step(
                          RKnown.Mergers.of(RFacts.Facts.list(Facts.Facts.crit(s))),
                          Types.Fact.Ask{Types.Ask{i, n, r}}
                        ),
                        Equal.trans(
                          Crits.Crit<Ledgers.Line>,
                          RKnown.Mergers.of(
                            RFacts.Facts.list(
                              Facts.Facts.crit(
                                Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})
                              )
                            )
                          ),
                          RKnown.Mergers.of(
                            Orders.Values.insert(
                              ~Types.Fact,
                              ~Coded.Fact.words,
                              RFacts.Facts.list(Facts.Facts.crit(s)),
                              Types.Fact.Ask{Types.Ask{i, n, r}}
                            )
                          ),
                          RKnown.Mergers.step(
                            RKnown.Mergers.of(RFacts.Facts.list(Facts.Facts.crit(s))),
                            Types.Fact.Ask{Types.Ask{i, n, r}}
                          ),
                          Equal.cong(
                            List<&2, Types.Fact>,
                            Crits.Crit<Ledgers.Line>,
                            l => RKnown.Mergers.of(l),
                            RFacts.Facts.list(
                              Facts.Facts.crit(
                                Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})
                              )
                            ),
                            Orders.Values.insert(
                              ~Types.Fact,
                              ~Coded.Fact.words,
                              RFacts.Facts.list(Facts.Facts.crit(s)),
                              Types.Fact.Ask{Types.Ask{i, n, r}}
                            ),
                            Asked.list(name, s, i, n, r)(e)
                          ),
                          Mergers.Mergers.of_insert(
                            RFacts.Facts.list(Facts.Facts.crit(s)),
                            Types.Fact.Ask{Types.Ask{i, n, r}}
                          )(
                            Reads.Eq.to(
                              Crits.Crit<Ledgers.Line>,
                              y => {
                                RKnown.Mergers.fresh(
                                  y,
                                  Types.Fact.Ask{Types.Ask{i, n, r}}
                                )
                                  == True{}: Bool
                              },
                              mtx9,
                              RKnown.Mergers.of(RFacts.Facts.list(Facts.Facts.crit(s))),
                              Open.fits_merges(fs, n0, tx9, mtx9, Facts.Facts.crit(s))(hf),
                              hfr
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )(
                et
              )(
                Reads.Eq.to(
                  Crits.Crit<Ledgers.Line>,
                  y => {
                    RKnown.Mergers.fresh(y, Types.Fact.Ask{Types.Ask{i, n, r}}) == True{}: Bool
                  },
                  mtx9,
                  RKnown.Mergers.of(RFacts.Facts.list(Facts.Facts.crit(s))),
                  Open.fits_merges(fs, n0, tx9, mtx9, Facts.Facts.crit(s))(hf),
                  hfr
                )
              )(
                Shared.List.is_eq_sound(
                  ~Types.Fact,
                  ~Coded.Fact.is_eq,
                  ~Coded.Fact.laws(),
                  fs,
                  RKnown.Open.of(
                    RFacts.Facts.list(Facts.Facts.crit(s)),
                    RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}
                  )
                )(
                  Shared.Bool.and_true_left(
                    Shared.List.is_eq(
                      ~Types.Fact,
                      ~Coded.Fact.is_eq,
                      fs,
                      RKnown.Open.of(
                        RFacts.Facts.list(Facts.Facts.crit(s)),
                        RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}
                      )
                    ),
                    Nat.is_eq(n0, RFacts.Seq.peak(RFacts.Facts.list(Facts.Facts.crit(s))))
                  )(Open.fits_old(fs, n0, tx9, mtx9, Facts.Facts.crit(s))(hf))
                )
              ),
              ef => Asked.open(
                name,
                s,
                i,
                n,
                r,
                fs,
                RKnown.Known.reopen(
                  kn,
                  fs,
                  Nat.max(n, n0),
                  Shared.Bool.when(
                    Crits.Crit<Types.Ask>,
                    Nat.is_lt(n0, n),
                    u => RKnown.Tops.join(tx9, Types.Fact.Ask{Types.Ask{i, n, r}}),
                    u => RKnown.Tops.of(
                      RFacts.Facts.list(
                        Facts.Facts.crit(
                          Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})
                        )
                      )
                    )
                  ),
                  RKnown.Mergers.step(mtx9, Types.Fact.Ask{Types.Ask{i, n, r}})
                )
              )(
                e
              )(
                Known.reopen_ok(
                  kn,
                  Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})),
                  fs,
                  Nat.max(n, n0),
                  Shared.Bool.when(
                    Crits.Crit<Types.Ask>,
                    Nat.is_lt(n0, n),
                    u => RKnown.Tops.join(tx9, Types.Fact.Ask{Types.Ask{i, n, r}}),
                    u => RKnown.Tops.of(
                      RFacts.Facts.list(
                        Facts.Facts.crit(
                          Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})
                        )
                      )
                    )
                  ),
                  RKnown.Mergers.step(mtx9, Types.Fact.Ask{Types.Ask{i, n, r}})
                )(ok)
              )(
                Reads.Eq.back(
                  Maybe<&2, RKnown.Kept>,
                  m => {
                    RContents.Shelf.led(
                      m,
                      Facts.Facts.crit(
                        Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})
                      )
                    )
                      == True{}: Bool
                  },
                  RKnown.Known.shelf(
                    RKnown.Known.reopen(
                      kn,
                      fs,
                      Nat.max(n, n0),
                      Shared.Bool.when(
                        Crits.Crit<Types.Ask>,
                        Nat.is_lt(n0, n),
                        u => RKnown.Tops.join(tx9, Types.Fact.Ask{Types.Ask{i, n, r}}),
                        u => RKnown.Tops.of(
                          RFacts.Facts.list(
                            Facts.Facts.crit(
                              Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})
                            )
                          )
                        )
                      ),
                      RKnown.Mergers.step(mtx9, Types.Fact.Ask{Types.Ask{i, n, r}})
                    )
                  ),
                  Some{
                    RKnown.Open{
                      fs,
                      Nat.max(n, n0),
                      Shared.Bool.when(
                        Crits.Crit<Types.Ask>,
                        Nat.is_lt(n0, n),
                        u => RKnown.Tops.join(tx9, Types.Fact.Ask{Types.Ask{i, n, r}}),
                        u => RKnown.Tops.of(
                          RFacts.Facts.list(
                            Facts.Facts.crit(
                              Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})
                            )
                          )
                        )
                      ),
                      RKnown.Mergers.step(mtx9, Types.Fact.Ask{Types.Ask{i, n, r}})
                    }
                  },
                  Known.reopen_shelf(
                    kn,
                    fs,
                    Nat.max(n, n0),
                    Shared.Bool.when(
                      Crits.Crit<Types.Ask>,
                      Nat.is_lt(n0, n),
                      u => RKnown.Tops.join(tx9, Types.Fact.Ask{Types.Ask{i, n, r}}),
                      u => RKnown.Tops.of(
                        RFacts.Facts.list(
                          Facts.Facts.crit(
                            Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})
                          )
                        )
                      )
                    ),
                    RKnown.Mergers.step(mtx9, Types.Fact.Ask{Types.Ask{i, n, r}}),
                    fs,
                    n0,
                    tx9,
                    mtx9
                  )(em),
                  Mergers.Mergers.same_refl_of(
                    RKnown.Mergers.step(mtx9, Types.Fact.Ask{Types.Ask{i, n, r}}),
                    RKnown.Mergers.of(
                      RFacts.Facts.list(
                        Facts.Facts.crit(
                          Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})
                        )
                      )
                    )
                  )(
                    Reads.Eq.back(
                      Crits.Crit<Ledgers.Line>,
                      y => {
                        RKnown.Mergers.step(
                          y,
                          Types.Fact.Ask{Types.Ask{i, n, r}}
                        )
                          == RKnown.Mergers.of(
                            RFacts.Facts.list(
                              Facts.Facts.crit(
                                Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})
                              )
                            )
                          ): Crits.Crit<Ledgers.Line>
                      },
                      mtx9,
                      RKnown.Mergers.of(RFacts.Facts.list(Facts.Facts.crit(s))),
                      Open.fits_merges(fs, n0, tx9, mtx9, Facts.Facts.crit(s))(hf),
                      Equal.sym(
                        Crits.Crit<Ledgers.Line>,
                        RKnown.Mergers.of(
                          RFacts.Facts.list(
                            Facts.Facts.crit(
                              Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})
                            )
                          )
                        ),
                        RKnown.Mergers.step(
                          RKnown.Mergers.of(RFacts.Facts.list(Facts.Facts.crit(s))),
                          Types.Fact.Ask{Types.Ask{i, n, r}}
                        ),
                        Equal.trans(
                          Crits.Crit<Ledgers.Line>,
                          RKnown.Mergers.of(
                            RFacts.Facts.list(
                              Facts.Facts.crit(
                                Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})
                              )
                            )
                          ),
                          RKnown.Mergers.of(
                            Orders.Values.insert(
                              ~Types.Fact,
                              ~Coded.Fact.words,
                              RFacts.Facts.list(Facts.Facts.crit(s)),
                              Types.Fact.Ask{Types.Ask{i, n, r}}
                            )
                          ),
                          RKnown.Mergers.step(
                            RKnown.Mergers.of(RFacts.Facts.list(Facts.Facts.crit(s))),
                            Types.Fact.Ask{Types.Ask{i, n, r}}
                          ),
                          Equal.cong(
                            List<&2, Types.Fact>,
                            Crits.Crit<Ledgers.Line>,
                            l => RKnown.Mergers.of(l),
                            RFacts.Facts.list(
                              Facts.Facts.crit(
                                Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})
                              )
                            ),
                            Orders.Values.insert(
                              ~Types.Fact,
                              ~Coded.Fact.words,
                              RFacts.Facts.list(Facts.Facts.crit(s)),
                              Types.Fact.Ask{Types.Ask{i, n, r}}
                            ),
                            Asked.list(name, s, i, n, r)(e)
                          ),
                          Mergers.Mergers.of_insert(
                            RFacts.Facts.list(Facts.Facts.crit(s)),
                            Types.Fact.Ask{Types.Ask{i, n, r}}
                          )(
                            Reads.Eq.to(
                              Crits.Crit<Ledgers.Line>,
                              y => {
                                RKnown.Mergers.fresh(
                                  y,
                                  Types.Fact.Ask{Types.Ask{i, n, r}}
                                )
                                  == True{}: Bool
                              },
                              mtx9,
                              RKnown.Mergers.of(RFacts.Facts.list(Facts.Facts.crit(s))),
                              Open.fits_merges(fs, n0, tx9, mtx9, Facts.Facts.crit(s))(hf),
                              hfr
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )(
                ef
              )(
                Shared.List.is_eq_sound(
                  ~Types.Fact,
                  ~Coded.Fact.is_eq,
                  ~Coded.Fact.laws(),
                  fs,
                  RKnown.Open.of(
                    RFacts.Facts.list(Facts.Facts.crit(s)),
                    RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}
                  )
                )(
                  Shared.Bool.and_true_left(
                    Shared.List.is_eq(
                      ~Types.Fact,
                      ~Coded.Fact.is_eq,
                      fs,
                      RKnown.Open.of(
                        RFacts.Facts.list(Facts.Facts.crit(s)),
                        RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}
                      )
                    ),
                    Nat.is_eq(n0, RFacts.Seq.peak(RFacts.Facts.list(Facts.Facts.crit(s))))
                  )(Open.fits_old(fs, n0, tx9, mtx9, Facts.Facts.crit(s))(hf))
                )
              )
            )
          )(
            Equal.trans(
              Nat,
              Nat.max(n, n0),
              Nat.max(n, RFacts.Seq.peak(RFacts.Facts.list(Facts.Facts.crit(s)))),
              RFacts.Seq.peak(
                RFacts.Facts.list(
                  Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
                )
              ),
              Equal.cong(
                Nat,
                Nat,
                y => Nat.max(n, y),
                n0,
                RFacts.Seq.peak(RFacts.Facts.list(Facts.Facts.crit(s))),
                Shared.Nat.is_eq_sound(
                  n0,
                  RFacts.Seq.peak(RFacts.Facts.list(Facts.Facts.crit(s)))
                )(
                  Shared.Bool.and_true_right(
                    Shared.List.is_eq(
                      ~Types.Fact,
                      ~Coded.Fact.is_eq,
                      fs,
                      RKnown.Open.of(
                        RFacts.Facts.list(Facts.Facts.crit(s)),
                        RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}
                      )
                    ),
                    Nat.is_eq(n0, RFacts.Seq.peak(RFacts.Facts.list(Facts.Facts.crit(s))))
                  )(Open.fits_old(fs, n0, tx9, mtx9, Facts.Facts.crit(s))(hf))
                )
              ),
              Equal.sym(
                Nat,
                RFacts.Seq.peak(
                  RFacts.Facts.list(
                    Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
                  )
                ),
                Nat.max(n, RFacts.Seq.peak(RFacts.Facts.list(Facts.Facts.crit(s)))),
                Asked.peak(name, s, i, n, r)(e)
              )
            )
          )(
            Lists.Bool.by(
              c => {
                Nat.is_lt(n0, n) == c: Bool
              } -> {
                Shared.Bool.when(
                  Crits.Crit<Types.Ask>,
                  c,
                  u => RKnown.Tops.join(tx9, Types.Fact.Ask{Types.Ask{i, n, r}}),
                  u => RKnown.Tops.of(
                    RFacts.Facts.list(
                      Facts.Facts.crit(
                        Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})
                      )
                    )
                  )
                )
                  == RKnown.Tops.of(
                    RFacts.Facts.list(
                      Facts.Facts.crit(
                        Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})
                      )
                    )
                  ): Crits.Crit<Types.Ask>
              },
              Nat.is_lt(n0, n),
              et => hl => (
                %Equal.sym(Crits.Crit<Types.Ask>, tx9, RKnown.Tops.of(RFacts.Facts.list(Facts.Facts.crit(s))), Open.fits_tops(fs, n0, tx9, mtx9, Facts.Facts.crit(s))(hf)): {RKnown.Tops.join(_, Types.Fact.Ask{Types.Ask{i, n, r}}) == RKnown.Tops.of(RFacts.Facts.list(Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})))): Crits.Crit<Types.Ask>}
                %Equal.sym(List<&2, Types.Fact>, RFacts.Facts.list(Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))), Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, RFacts.Facts.list(Facts.Facts.crit(s)), Types.Fact.Ask{Types.Ask{i, n, r}}), Asked.list(name, s, i, n, r)(e)): {RKnown.Tops.join(RKnown.Tops.of(RFacts.Facts.list(Facts.Facts.crit(s))), Types.Fact.Ask{Types.Ask{i, n, r}}) == RKnown.Tops.of(_): Crits.Crit<Types.Ask>}
                Equal.sym(Crits.Crit<Types.Ask>, RKnown.Tops.of(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, RFacts.Facts.list(Facts.Facts.crit(s)), Types.Fact.Ask{Types.Ask{i, n, r}})), RKnown.Tops.join(RKnown.Tops.of(RFacts.Facts.list(Facts.Facts.crit(s))), Types.Fact.Ask{Types.Ask{i, n, r}}), Newest.Tops.of_insert(RFacts.Facts.list(Facts.Facts.crit(s)), Types.Fact.Ask{Types.Ask{i, n, r}})((
                    %Shared.Nat.is_eq_sound(n0, RFacts.Seq.peak(RFacts.Facts.list(Facts.Facts.crit(s))))(Shared.Bool.and_true_right(Shared.List.is_eq(~Types.Fact, ~Coded.Fact.is_eq, fs, RKnown.Open.of(RFacts.Facts.list(Facts.Facts.crit(s)), RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)})), Nat.is_eq(n0, RFacts.Seq.peak(RFacts.Facts.list(Facts.Facts.crit(s)))))(Open.fits_old(fs, n0, tx9, mtx9, Facts.Facts.crit(s))(hf))): {Nat.is_lt(_, n) == True{}: Bool}
                    hl)))),
              ef => hl => {==}
            )({==})
          )(
            Reads.Eq.back(
              Crits.Crit<Ledgers.Line>,
              y => {
                RKnown.Mergers.step(
                  y,
                  Types.Fact.Ask{Types.Ask{i, n, r}}
                )
                  == RKnown.Mergers.of(
                    RFacts.Facts.list(
                      Facts.Facts.crit(
                        Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})
                      )
                    )
                  ): Crits.Crit<Ledgers.Line>
              },
              mtx9,
              RKnown.Mergers.of(RFacts.Facts.list(Facts.Facts.crit(s))),
              Open.fits_merges(fs, n0, tx9, mtx9, Facts.Facts.crit(s))(hf),
              Equal.sym(
                Crits.Crit<Ledgers.Line>,
                RKnown.Mergers.of(
                  RFacts.Facts.list(
                    Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
                  )
                ),
                RKnown.Mergers.step(
                  RKnown.Mergers.of(RFacts.Facts.list(Facts.Facts.crit(s))),
                  Types.Fact.Ask{Types.Ask{i, n, r}}
                ),
                Equal.trans(
                  Crits.Crit<Ledgers.Line>,
                  RKnown.Mergers.of(
                    RFacts.Facts.list(
                      Facts.Facts.crit(
                        Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})
                      )
                    )
                  ),
                  RKnown.Mergers.of(
                    Orders.Values.insert(
                      ~Types.Fact,
                      ~Coded.Fact.words,
                      RFacts.Facts.list(Facts.Facts.crit(s)),
                      Types.Fact.Ask{Types.Ask{i, n, r}}
                    )
                  ),
                  RKnown.Mergers.step(
                    RKnown.Mergers.of(RFacts.Facts.list(Facts.Facts.crit(s))),
                    Types.Fact.Ask{Types.Ask{i, n, r}}
                  ),
                  Equal.cong(
                    List<&2, Types.Fact>,
                    Crits.Crit<Ledgers.Line>,
                    l => RKnown.Mergers.of(l),
                    RFacts.Facts.list(
                      Facts.Facts.crit(
                        Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})
                      )
                    ),
                    Orders.Values.insert(
                      ~Types.Fact,
                      ~Coded.Fact.words,
                      RFacts.Facts.list(Facts.Facts.crit(s)),
                      Types.Fact.Ask{Types.Ask{i, n, r}}
                    ),
                    Asked.list(name, s, i, n, r)(e)
                  ),
                  Mergers.Mergers.of_insert(
                    RFacts.Facts.list(Facts.Facts.crit(s)),
                    Types.Fact.Ask{Types.Ask{i, n, r}}
                  )(
                    Reads.Eq.to(
                      Crits.Crit<Ledgers.Line>,
                      y => {
                        RKnown.Mergers.fresh(y, Types.Fact.Ask{Types.Ask{i, n, r}}) == True{}: Bool
                      },
                      mtx9,
                      RKnown.Mergers.of(RFacts.Facts.list(Facts.Facts.crit(s))),
                      Open.fits_merges(fs, n0, tx9, mtx9, Facts.Facts.crit(s))(hf),
                      hfr
                    )
                  )
                )
              )
            )
          )
        ),
        hfn => Fit.both(
          RKnown.Known.shut(kn),
          Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
        )(
          Known.shut_ok(
            kn,
            Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
          )(ok)
        )((
            %Equal.sym(Maybe<&2, RKnown.Kept>, RKnown.Known.shelf(RKnown.Known.shut(kn)), None{}, Known.shut_shelf(kn)): {RContents.Shelf.fits(_, Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))) == True{}: Bool}
            {==}))
      )

# a table that is right after a node takes in an ask that starts no store,
# and that held the right entry for a work before, fits once the ask joined
# what it holds
def Known.joined_fit(
  +kn: RKnown.Known(),
  +name: String,
  +s: Facts.Facts(),
  +i: Ledgers.Id,
  +n: Nat,
  +r: Spec.Request
) -> {
  RFacts.Request.is_start(r) == False{}: Bool
} -> {
  RContents.Known.ok(
    kn,
    Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
  )
    == True{}: Bool
} -> {
  RContents.Shelf.fits(RKnown.Known.shelf(kn), Facts.Facts.crit(s)) == True{}: Bool
} -> {
  RContents.Known.fit(
    RKnown.Known.joined(
      kn,
      Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})),
      Types.Fact.Ask{Types.Ask{i, n, r}}
    ),
    Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
  )
    == True{}: Bool
}:
  e => ok => hf => Known.joined_fit.at(
    RKnown.Known.shelf(kn),
    kn,
    name,
    s,
    i,
    n,
    r
  )({==})(e)(ok)(hf)

# A ballot joins the facts that a work may act on
# -----------------------------------------------

# a number that is not at most c, and at most b: b is not at most c
def Nat.nle_up(
  +a: Nat,
  +b: Nat,
  +c: Nat
) -> {
  Nat.is_le(a, c) == False{}: Bool
} -> {Nat.is_le(a, b) == True{}: Bool} -> {Nat.is_le(b, c) == False{}: Bool}:
  h => l => Lists.Bool.by(
    y => {y == False{}: Bool},
    Nat.is_le(b, c),
    et => Equal.trans(
      Bool,
      True{},
      Nat.is_le(a, c),
      False{},
      Equal.sym(Bool, Nat.is_le(a, c), True{}, Shared.Nat.le_trans(a, b, c)(l)(et)),
      h
    ),
    ef => {==}
  )

# what is not false when negated is true
def Bool.not_false(b: Bool) -> {Bool.not(b) == False{}: Bool} -> {b == True{}: Bool}:
  match b:
    case True{}:
      h => {==}
    case False{}:
      h => Equal.sym(Bool, True{}, False{}, h)

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof does not run
# a request that made one of the versions vs made one of the versions that
# extend them
def Some.ext(
  +vs: List<&2, Types.Entry>,
  +vs2: List<&2, Types.Entry>,
  +i: Ledgers.Id,
  ext: Lists.List.Ext(Types.Entry, vs, vs2)
) -> {
  Shared.List.some(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, vs, i) == True{}: Bool
} -> {Shared.List.some(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, vs2, i) == True{}: Bool}:
  (zs, e) = ext
  hv => (
    %Equal.sym(List<&2, Types.Entry>, vs2, List.append(&2, Types.Entry, vs, zs), e): {Shared.List.some(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, _, i) == True{}: Bool}
    %Equal.sym(Bool, Shared.List.some(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, List.append(&2, Types.Entry, vs, zs), i), Bool.or(Shared.List.some(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, vs, i), Shared.List.some(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, zs, i)), Shared.List.some_append(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, vs, zs, i)): {_ == True{}: Bool}
    %Equal.sym(Bool, Shared.List.some(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, vs, i), True{}, hv): {Bool.or(_, Shared.List.some(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, zs, i)) == True{}: Bool}
    {==})
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# a ballot for a slot of a line whose next slot only grew waits no more, if
# it did not wait before
def Slot.back.at(
  st: RLines.State,
  st2: RLines.State,
  +k2: Nat
) -> {
  Nat.is_le(RLines.State.slot(st), RLines.State.slot(st2)) == True{}: Bool
} -> {
  RKnown.Slot.waits(Some{st}, k2) == False{}: Bool
} -> {RKnown.Slot.waits(Some{st2}, k2) == False{}: Bool}:
  match st st2:
    case RLines.State{vs, +j} RLines.State{vs2, +j2}:
      hl => hw => Nat.nle_up(j, j2, k2)(hw)(hl)

# a request waits no more on a line whose versions only grew, if it did not
# wait before
def Id.back.at(
  st: RLines.State,
  st2: RLines.State,
  +c: Ledgers.Line,
  +i: Ledgers.Id
) -> Lists.List.Ext(
  Types.Entry,
  RLines.State.versions(st),
  RLines.State.versions(st2)
) -> {
  RKnown.Id.waits(Some{st}, RKnown.Known.none(), c, i) == False{}: Bool
} -> {RKnown.Id.waits(Some{st2}, RKnown.Known.none(), c, i) == False{}: Bool}:
  match st st2:
    case RLines.State{+vs, j} RLines.State{+vs2, j2}:
      ext => hw => Equal.cong(
        Bool,
        Bool,
        y => Bool.not(y),
        Shared.List.some(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, vs2, i),
        True{},
        Some.ext(
          vs,
          vs2,
          i,
          ext
        )(
          Bool.not_false(
            Shared.List.some(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, vs, i)
          )(hw)
        )
      )

# the state of a branch after a ballot for its next slot is the run from its
# state before, when the state of its store is known
def Voted.state(
  +name: String,
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +b: String,
  +k: Nat,
  +t: Nat,
  +x: Types.Cast,
  +st: RLines.State,
  +rs: List<&2, Types.Entry>,
  +j: Nat
) -> {
  Lines.Line.state(s, Ledgers.Line{h, Some{b}}) == Some{st}: Maybe<&2, RLines.State>
} -> {
  Nat.is_eq(RLines.State.slot(st), k) == True{}: Bool
} -> {
  Lines.Line.state(s, Ledgers.Line{h, None{}}) == Some{RLines.State{rs, j}}: Maybe<&2, RLines.State>
} -> {
  Lines.Line.state(
    Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}),
    Ledgers.Line{h, Some{b}}
  )
    == Some{
      RKnown.Known.go.at(
        Facts.Facts.crit(
          Facts.Facts.add(
            s,
            Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}
          )
        ),
        Ledgers.Line{h, Some{b}},
        st,
        Some{rs}
      )
    }: Maybe<&2, RLines.State>
}:
  e1 => et => e2 => (
    %et: Put.Ok(Lines.Line.state(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}), Ledgers.Line{h, Some{b}}), Shared.Maybe.when(RLines.State, _, u => Some{RKnown.Known.go.at(Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x})), Ledgers.Line{h, Some{b}}, st, Some{rs})}))
    Known.next_ok(name, s, Ledgers.Line{h, Some{b}}, k, t, x, Some{st}, Some{RLines.State{rs, j}})(Inr{e1})(Inr{e2}))

# a ballot for a slot of a line waits no more after a ballot for the next
# slot of a branch, if it did not wait before
def Slot.back(
  +name: String,
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +b: String,
  +k: Nat,
  +t: Nat,
  +x: Types.Cast,
  +st: RLines.State,
  +rs: List<&2, Types.Entry>,
  +j: Nat,
  +c2: Ledgers.Line,
  +k2: Nat
) -> {
  Lines.Line.state(s, Ledgers.Line{h, Some{b}}) == Some{st}: Maybe<&2, RLines.State>
} -> {
  Nat.is_eq(RLines.State.slot(st), k) == True{}: Bool
} -> {
  Lines.Line.state(s, Ledgers.Line{h, None{}}) == Some{RLines.State{rs, j}}: Maybe<&2, RLines.State>
} -> {
  RKnown.Slot.waits(Lines.Line.state(s, c2), k2) == False{}: Bool
} -> {
  RKnown.Slot.waits(
    Lines.Line.state(
      Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}),
      c2
    ),
    k2
  )
    == False{}: Bool
}:
  +e1 => et => e2 => +hw => Lists.Bool.by(
    y => {
      Ledgers.Line.is_eq(c2, Ledgers.Line{h, Some{b}}) == y: Bool
    } -> {
      RKnown.Slot.waits(
        Lines.Line.state(
          Facts.Facts.add(
            s,
            Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}
          ),
          c2
        ),
        k2
      )
        == False{}: Bool
    },
    Ledgers.Line.is_eq(c2, Ledgers.Line{h, Some{b}}),
    et2 => +eq => (
      %Equal.sym(Ledgers.Line, c2, Ledgers.Line{h, Some{b}}, Ledgers.Line.is_eq_sound(c2, Ledgers.Line{h, Some{b}})(eq)): {RKnown.Slot.waits(Lines.Line.state(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}), _), k2) == False{}: Bool}
      %Equal.sym(Maybe<&2, RLines.State>, Lines.Line.state(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}), Ledgers.Line{h, Some{b}}), Some{RKnown.Known.go.at(Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x})), Ledgers.Line{h, Some{b}}, st, Some{rs})}, Voted.state(name, s, h, b, k, t, x, st, rs, j)(e1)(et)(e2)): {RKnown.Slot.waits(_, k2) == False{}: Bool}
      Slot.back.at(st, RKnown.Known.go.at(Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x})), Ledgers.Line{h, Some{b}}, st, Some{rs}), k2)(Moves.Run.slot_le(1n+RLines.Line.bound(Facts.Facts.list(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x})), Ledgers.Line{h, Some{b}}), Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}), Some{rs}, Ledgers.Line{h, Some{b}}, st))((
        %e1: {RKnown.Slot.waits(_, k2) == False{}: Bool}
        %Ledgers.Line.is_eq_sound(c2, Ledgers.Line{h, Some{b}})(eq): {RKnown.Slot.waits(Lines.Line.state(s, _), k2) == False{}: Bool}
        hw))),
    ef2 => eq => (
      %Equal.sym(Maybe<&2, RLines.State>, Lines.Line.state(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}), c2), Lines.Line.state(s, c2), Line.state_voted(name, s, Ledgers.Line{h, Some{b}}, k, t, x, c2)(Branch.hit_other(h, b, c2)(eq))): {RKnown.Slot.waits(_, k2) == False{}: Bool}
      hw)
  )({==})

# a request waits no more on a line after a ballot for the next slot of a
# branch, if it did not wait before
def Id.back(
  +name: String,
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +b: String,
  +k: Nat,
  +t: Nat,
  +x: Types.Cast,
  +st: RLines.State,
  +rs: List<&2, Types.Entry>,
  +j: Nat,
  +c2: Ledgers.Line,
  +i: Ledgers.Id
) -> {
  Lines.Line.state(s, Ledgers.Line{h, Some{b}}) == Some{st}: Maybe<&2, RLines.State>
} -> {
  Nat.is_eq(RLines.State.slot(st), k) == True{}: Bool
} -> {
  Lines.Line.state(s, Ledgers.Line{h, None{}}) == Some{RLines.State{rs, j}}: Maybe<&2, RLines.State>
} -> {
  RKnown.Id.waits(Lines.Line.state(s, c2), RKnown.Known.none(), c2, i) == False{}: Bool
} -> {
  RKnown.Id.waits(
    Lines.Line.state(
      Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}),
      c2
    ),
    RKnown.Known.none(),
    c2,
    i
  )
    == False{}: Bool
}:
  +e1 => et => e2 => +hw => Lists.Bool.by(
    y => {
      Ledgers.Line.is_eq(c2, Ledgers.Line{h, Some{b}}) == y: Bool
    } -> {
      RKnown.Id.waits(
        Lines.Line.state(
          Facts.Facts.add(
            s,
            Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}
          ),
          c2
        ),
        RKnown.Known.none(),
        c2,
        i
      )
        == False{}: Bool
    },
    Ledgers.Line.is_eq(c2, Ledgers.Line{h, Some{b}}),
    et2 => +eq => (
      %Equal.sym(Ledgers.Line, c2, Ledgers.Line{h, Some{b}}, Ledgers.Line.is_eq_sound(c2, Ledgers.Line{h, Some{b}})(eq)): {RKnown.Id.waits(Lines.Line.state(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}), _), RKnown.Known.none(), _, i) == False{}: Bool}
      %Equal.sym(Maybe<&2, RLines.State>, Lines.Line.state(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}), Ledgers.Line{h, Some{b}}), Some{RKnown.Known.go.at(Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x})), Ledgers.Line{h, Some{b}}, st, Some{rs})}, Voted.state(name, s, h, b, k, t, x, st, rs, j)(e1)(et)(e2)): {RKnown.Id.waits(_, RKnown.Known.none(), Ledgers.Line{h, Some{b}}, i) == False{}: Bool}
      Id.back.at(st, RKnown.Known.go.at(Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x})), Ledgers.Line{h, Some{b}}, st, Some{rs}), Ledgers.Line{h, Some{b}}, i)(Moves.Run.grows(1n+RLines.Line.bound(Facts.Facts.list(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x})), Ledgers.Line{h, Some{b}}), Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}), Some{rs}, Ledgers.Line{h, Some{b}}, st))((
        %e1: {RKnown.Id.waits(_, RKnown.Known.none(), Ledgers.Line{h, Some{b}}, i) == False{}: Bool}
        %Ledgers.Line.is_eq_sound(c2, Ledgers.Line{h, Some{b}})(eq): {RKnown.Id.waits(Lines.Line.state(s, _), RKnown.Known.none(), _, i) == False{}: Bool}
        hw))),
    ef2 => eq => (
      %Equal.sym(Maybe<&2, RLines.State>, Lines.Line.state(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}), c2), Lines.Line.state(s, c2), Line.state_voted(name, s, Ledgers.Line{h, Some{b}}, k, t, x, c2)(Branch.hit_other(h, b, c2)(eq))): {RKnown.Id.waits(_, RKnown.Known.none(), c2, i) == False{}: Bool}
      hw)
  )({==})

# a fact that a work could not act on before a ballot for the next slot of a
# branch is one that it cannot act on after it
def Waits.back(
  +name: String,
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +b: String,
  +k: Nat,
  +t: Nat,
  +x: Types.Cast,
  +st: RLines.State,
  +rs: List<&2, Types.Entry>,
  +j: Nat,
  f: Types.Fact
) -> {
  Lines.Line.state(s, Ledgers.Line{h, Some{b}}) == Some{st}: Maybe<&2, RLines.State>
} -> {
  Nat.is_eq(RLines.State.slot(st), k) == True{}: Bool
} -> {
  Lines.Line.state(s, Ledgers.Line{h, None{}}) == Some{RLines.State{rs, j}}: Maybe<&2, RLines.State>
} -> {
  RKnown.Fact.waits(RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}, f) == False{}: Bool
} -> {
  RKnown.Fact.waits(
    RKnown.Scene{
      RKnown.Known.none(),
      Facts.Facts.crit(
        Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x})
      )
    },
    f
  )
    == False{}: Bool
}:
  match f:
    case Types.Fact.Vote{v2, Types.Step.Broken{}, x2}:
      e1 => et => e2 => hw => {==}
    case Types.Fact.Vote{v2, Types.Step.At{+c2, +k2, t2}, x2}:
      e1 => et => e2 => hw => Slot.back(name, s, h, b, k, t, x, st, rs, j, c2, k2)(e1)(et)(e2)(hw)
    case Types.Fact.Ask{Types.Ask{+i2, n2, Spec.Request.Start{os}}}:
      e1 => et => e2 => hw => hw
    case Types.Fact.Ask{Types.Ask{+i2, n2, Spec.Request.Write{+b2, p2, w2}}}:
      e1 => et => e2 => hw => Id.back(name, s, h, b, k, t, x, st, rs, j, b2, i2)(e1)(et)(e2)(hw)
    case Types.Fact.Ask{Types.Ask{+i2, n2, Spec.Request.Merge{f2, +x2}}}:
      e1 => et => e2 => hw => Id.back(name, s, h, b, k, t, x, st, rs, j, x2, i2)(e1)(et)(e2)(hw)
    case Types.Fact.Ask{Types.Ask{+i2, n2, Spec.Request.Resolve{+m2, p2, w2}}}:
      e1 => et => e2 => hw => Reads.Eq.back(
        Maybe<&2, Ledgers.Line>,
        l => {
          RKnown.Resolve.waits(
            l,
            RKnown.Known.none(),
            Facts.Facts.crit(
              Facts.Facts.add(
                s,
                Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}
              )
            ),
            i2
          )
            == False{}: Bool
        },
        RKnown.Merge.line(
          RFacts.Facts.list(
            Facts.Facts.crit(
              Facts.Facts.add(
                s,
                Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}
              )
            )
          ),
          m2
        ),
        RKnown.Merge.line(RFacts.Facts.list(Facts.Facts.crit(s)), m2),
        Equal.trans(
          Maybe<&2, Ledgers.Line>,
          RKnown.Merge.line(
            RFacts.Facts.list(
              Facts.Facts.crit(
                Facts.Facts.add(
                  s,
                  Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}
                )
              )
            ),
            m2
          ),
          RKnown.Merge.line(
            Orders.Values.insert(
              ~Types.Fact,
              ~Coded.Fact.words,
              RFacts.Facts.list(Facts.Facts.crit(s)),
              Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}
            ),
            m2
          ),
          RKnown.Merge.line(RFacts.Facts.list(Facts.Facts.crit(s)), m2),
          Equal.cong(
            List<&2, Types.Fact>,
            Maybe<&2, Ledgers.Line>,
            l => RKnown.Merge.line(l, m2),
            RFacts.Facts.list(
              Facts.Facts.crit(
                Facts.Facts.add(
                  s,
                  Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}
                )
              )
            ),
            Orders.Values.insert(
              ~Types.Fact,
              ~Coded.Fact.words,
              RFacts.Facts.list(Facts.Facts.crit(s)),
              Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}
            ),
            Listed.add(s, Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x})
          ),
          Mergers.Merge.line_insert_pass(
            RFacts.Facts.list(Facts.Facts.crit(s)),
            Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x},
            m2
          )({==})
        ),
        Lists.Maybe.by(
          Ledgers.Line,
          l => {
            RKnown.Resolve.waits(l, RKnown.Known.none(), Facts.Facts.crit(s), i2) == False{}: Bool
          } -> {
            RKnown.Resolve.waits(
              l,
              RKnown.Known.none(),
              Facts.Facts.crit(
                Facts.Facts.add(
                  s,
                  Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}
                )
              ),
              i2
            )
              == False{}: Bool
          },
          RKnown.Merge.line(RFacts.Facts.list(Facts.Facts.crit(s)), m2),
          en => h2 => Empty.absurd({True{} == False{}: Bool}, Shared.Bool.true_ne_false(h2)),
          +c => es => h2 => Id.back(name, s, h, b, k, t, x, st, rs, j, c, i2)(e1)(et)(e2)(h2)
        )(hw)
      )
    case Types.Fact.Ask{Types.Ask{+i2, n2, Spec.Request.Mark{+b2, m2, v2}}}:
      e1 => et => e2 => hw => Id.back(name, s, h, b, k, t, x, st, rs, j, b2, i2)(e1)(et)(e2)(hw)
    case Types.Fact.Ask{Types.Ask{+i2, n2, Spec.Request.Move{+b2, t2, v2}}}:
      e1 => et => e2 => hw => Id.back(name, s, h, b, k, t, x, st, rs, j, b2, i2)(e1)(et)(e2)(hw)
    case Types.Fact.Ask{Types.Ask{+i2, n2, Spec.Request.Group{+h2, g2, ms2}}}:
      e1 => et => e2 => hw => Id.back(
        name,
        s,
        h,
        b,
        k,
        t,
        x,
        st,
        rs,
        j,
        Ledgers.Line{h2, None{}},
        i2
      )(e1)(et)(e2)(hw)
    case Types.Fact.Ask{Types.Ask{+i2, n2, Spec.Request.Own{Ledgers.Line{+h2, b2}, g2}}}:
      e1 => et => e2 => hw => Id.back(
        name,
        s,
        h,
        b,
        k,
        t,
        x,
        st,
        rs,
        j,
        Ledgers.Line{h2, None{}},
        i2
      )(e1)(et)(e2)(hw)

# Open.again at one fact, once it is known whether a work could act on it
# before the ballot (w)
def Open.again.at(
  +name: String,
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +b: String,
  +k: Nat,
  +t: Nat,
  +x: Types.Cast,
  +st: RLines.State,
  +rs: List<&2, Types.Entry>,
  +j: Nat,
  +f: Types.Fact,
  +rest: List<&2, Types.Fact>,
  w: Bool
) -> {
  Lines.Line.state(s, Ledgers.Line{h, Some{b}}) == Some{st}: Maybe<&2, RLines.State>
} -> {
  Nat.is_eq(RLines.State.slot(st), k) == True{}: Bool
} -> {
  Lines.Line.state(s, Ledgers.Line{h, None{}}) == Some{RLines.State{rs, j}}: Maybe<&2, RLines.State>
} -> {
  w == RKnown.Fact.waits(RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}, f): Bool
} -> {
  RKnown.Open.of(
    RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}),
    RKnown.Scene{
      RKnown.Known.none(),
      Facts.Facts.crit(
        Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x})
      )
    }
  )
    == RKnown.Open.of(
      rest,
      RKnown.Scene{
        RKnown.Known.none(),
        Facts.Facts.crit(
          Facts.Facts.add(
            s,
            Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}
          )
        )
      }
    ): List<&2, Types.Fact>
} -> {
  RKnown.Open.of(
    List.filter.put(
      Types.Fact,
      f,
      RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}),
      w
    ),
    RKnown.Scene{
      RKnown.Known.none(),
      Facts.Facts.crit(
        Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x})
      )
    }
  )
    == RKnown.Open.of(
      f <> rest,
      RKnown.Scene{
        RKnown.Known.none(),
        Facts.Facts.crit(
          Facts.Facts.add(
            s,
            Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}
          )
        )
      }
    ): List<&2, Types.Fact>
}:
  match w:
    case True{}:
      e1 => et => e2 => ew => ih => (
        %ih: {RKnown.Open.of(f <> RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}), RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}))}) == List.filter.put(Types.Fact, f, _, RKnown.Fact.waits(RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}))}, f)): List<&2, Types.Fact>}
        {==})
    case False{}:
      e1 => et => e2 => ew => ih => (
        %Equal.sym(Bool, RKnown.Fact.waits(RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}))}, f), False{}, Waits.back(name, s, h, b, k, t, x, st, rs, j, f)(e1)(et)(e2)(Equal.sym(Bool, False{}, RKnown.Fact.waits(RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}, f), ew))): {RKnown.Open.of(RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}), RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}))}) == List.filter.put(Types.Fact, f, RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}))}), _): List<&2, Types.Fact>}
        ih)

# the facts that a work may act on after a ballot for the next slot of a
# branch are among those that it could act on before
def Open.again(
  +name: String,
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +b: String,
  +k: Nat,
  +t: Nat,
  +x: Types.Cast,
  +st: RLines.State,
  +rs: List<&2, Types.Entry>,
  +j: Nat,
  xs: List<&2, Types.Fact>
) -> {
  Lines.Line.state(s, Ledgers.Line{h, Some{b}}) == Some{st}: Maybe<&2, RLines.State>
} -> {
  Nat.is_eq(RLines.State.slot(st), k) == True{}: Bool
} -> {
  Lines.Line.state(s, Ledgers.Line{h, None{}}) == Some{RLines.State{rs, j}}: Maybe<&2, RLines.State>
} -> {
  RKnown.Open.of(
    RKnown.Open.of(xs, RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}),
    RKnown.Scene{
      RKnown.Known.none(),
      Facts.Facts.crit(
        Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x})
      )
    }
  )
    == RKnown.Open.of(
      xs,
      RKnown.Scene{
        RKnown.Known.none(),
        Facts.Facts.crit(
          Facts.Facts.add(
            s,
            Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}
          )
        )
      }
    ): List<&2, Types.Fact>
}:
  match xs:
    case Nil{}:
      e1 => et => e2 => {==}
    case Con{+f, +rest}:
      +e1 => +et => +e2 => Open.again.at(
        name,
        s,
        h,
        b,
        k,
        t,
        x,
        st,
        rs,
        j,
        f,
        rest,
        RKnown.Fact.waits(RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}, f)
      )(e1)(et)(e2)({==})(Open.again(name, s, h, b, k, t, x, st, rs, j, rest)(e1)(et)(e2))

# a ballot for the next slot of a line waits
def Slot.waits_eq(
  st: RLines.State,
  +k: Nat
) -> {
  Nat.is_eq(RLines.State.slot(st), k) == True{}: Bool
} -> {RKnown.Slot.waits(Some{st}, k) == True{}: Bool}:
  match st:
    case RLines.State{vs, +j}:
      et => (
        %Shared.Nat.is_eq_sound(j, k)(et): {Nat.is_le(j, _) == True{}: Bool}
        Shared.Nat.le_refl(j))

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof does not run
# the facts that a work could act on, with a ballot for the next slot of a
# branch: those among them that a work may act on after the ballot are all
# that it may act on
def Voted.open(
  +name: String,
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +b: String,
  +k: Nat,
  +t: Nat,
  +x: Types.Cast,
  +st: RLines.State,
  +rs: List<&2, Types.Entry>,
  +j: Nat,
  +fs: List<&2, Types.Fact>
) -> {
  Lines.Line.state(s, Ledgers.Line{h, Some{b}}) == Some{st}: Maybe<&2, RLines.State>
} -> {
  Nat.is_eq(RLines.State.slot(st), k) == True{}: Bool
} -> {
  Lines.Line.state(s, Ledgers.Line{h, None{}}) == Some{RLines.State{rs, j}}: Maybe<&2, RLines.State>
} -> {
  fs
    == RKnown.Open.of(
      RFacts.Facts.list(Facts.Facts.crit(s)),
      RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}
    ): List<&2, Types.Fact>
} -> {
  RKnown.Open.of(
    RKnown.Open.put(fs, Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}),
    RKnown.Scene{
      RKnown.Known.none(),
      Facts.Facts.crit(
        Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x})
      )
    }
  )
    == RKnown.Open.of(
      RFacts.Facts.list(
        Facts.Facts.crit(
          Facts.Facts.add(
            s,
            Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}
          )
        )
      ),
      RKnown.Scene{
        RKnown.Known.none(),
        Facts.Facts.crit(
          Facts.Facts.add(
            s,
            Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}
          )
        )
      }
    ): List<&2, Types.Fact>
}:
  +e1 => +et => e2 => efs => (
    %Equal.sym(List<&2, Types.Fact>, RFacts.Facts.list(Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}))), Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, RFacts.Facts.list(Facts.Facts.crit(s)), Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}), Listed.add(s, Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x})): {RKnown.Open.of(RKnown.Open.put(fs, Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}), RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}))}) == RKnown.Open.of(_, RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}))}): List<&2, Types.Fact>}
    %Open.again(name, s, h, b, k, t, x, st, rs, j, Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, RFacts.Facts.list(Facts.Facts.crit(s)), Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}))(e1)(et)(e2): {RKnown.Open.of(RKnown.Open.put(fs, Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}), RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}))}) == _: List<&2, Types.Fact>}
    %Equal.sym(List<&2, Types.Fact>, RKnown.Open.of(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, RFacts.Facts.list(Facts.Facts.crit(s)), Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}), RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}), Bool.pick(List<&2, Types.Fact>, RKnown.Fact.waits(RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}, Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}), Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, RKnown.Open.of(RFacts.Facts.list(Facts.Facts.crit(s)), RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}), Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}), RKnown.Open.of(RFacts.Facts.list(Facts.Facts.crit(s)), RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)})), Orders.Values.keep_insert(~Types.Fact, ~Coded.Fact.words, ~Coded.Fact.words_inj, ~RKnown.Scene, ~RKnown.Fact.waits, RFacts.Facts.list(Facts.Facts.crit(s)), Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}, RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)})(Listed.sorted(s))): {RKnown.Open.of(RKnown.Open.put(fs, Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}), RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}))}) == RKnown.Open.of(_, RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}))}): List<&2, Types.Fact>}
    %Equal.sym(Bool, RKnown.Fact.waits(RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}, Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}), True{}, (
      %Equal.sym(Maybe<&2, RLines.State>, Lines.Line.state(s, Ledgers.Line{h, Some{b}}), Some{st}, e1): {RKnown.Slot.waits(_, k) == True{}: Bool}
      Slot.waits_eq(st, k)(et))): {RKnown.Open.of(RKnown.Open.put(fs, Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}), RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}))}) == RKnown.Open.of(Bool.pick(List<&2, Types.Fact>, _, Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, RKnown.Open.of(RFacts.Facts.list(Facts.Facts.crit(s)), RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}), Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}), RKnown.Open.of(RFacts.Facts.list(Facts.Facts.crit(s)), RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)})), RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}))}): List<&2, Types.Fact>}
    %efs: {RKnown.Open.of(RKnown.Open.put(fs, Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}), RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}))}) == RKnown.Open.of(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, _, Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}), RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}))}): List<&2, Types.Fact>}
    Equal.cong(List<&2, Types.Fact>, List<&2, Types.Fact>, z => RKnown.Open.of(z, RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}))}), RKnown.Open.put(fs, Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}), Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}), Open.put_insert(fs, Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x})))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# A run reads the facts that a work may act on
# --------------------------------------------
# The facts that a work may act on hold each ballot for a slot that waits.
# A run from the state of a line reads only such slots: it ends at the same
# state when it reads them from those facts, with a bound from those facts.

# the next slot of a state, read from the facts of a node as a list, is the
# one read from the facts, once the rule u of the slot is known
def Step.at_in_eq(
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +st: RLines.State,
  u: Maybe<&2, RLines.Rule>
) -> {
  RLines.Line.step.at(
    s,
    c,
    st,
    u
  )
    == RLines.Line.step.at.in(RFacts.Facts.list(s), c, st, u): Maybe<&2, RLines.State>
}:
  match u:
    case None{}:
      {==}
    case Some{rule}:
      {==}

# the next slot of a state, read from the facts of a node as a list, is the
# one read from the facts
def Step.in_eq(
  +s: RFacts.Plain(),
  +r: Maybe<&2, List<&2, Types.Entry>>,
  +c: Ledgers.Line,
  +st: RLines.State
) -> {
  RLines.Line.step(
    s,
    r,
    c,
    st
  )
    == RLines.Line.step.in(RFacts.Facts.list(s), r, c, st): Maybe<&2, RLines.State>
}:
  Step.at_in_eq(s, c, st, RLines.Line.rule(r, c, RLines.State.versions(st)))

# a run that reads the facts of a node as a list is the run that reads the
# facts
def Run.in_eq(
  f: Nat,
  +s: RFacts.Plain(),
  +r: Maybe<&2, List<&2, Types.Entry>>,
  +c: Ledgers.Line,
  +st: RLines.State,
  m: Maybe<&2, RLines.State>
) -> {
  RLines.Line.run(
    f,
    s,
    r,
    c,
    st,
    m
  )
    == RLines.Line.run.in(f, RFacts.Facts.list(s), r, c, st, m): RLines.State
}:
  match f m:
    case 0n None{}:
      {==}
    case 0n Some{st2}:
      {==}
    case 1n+p None{}:
      {==}
    case 1n+p Some{+st2}:
      (
        %Step.in_eq(s, r, c, st2): {RLines.Line.run(p, s, r, c, st2, RLines.Line.step(s, r, c, st2)) == RLines.Line.run.in(p, RFacts.Facts.list(s), r, c, st2, _): RLines.State}
        Run.in_eq(p, s, r, c, st2, RLines.Line.step(s, r, c, st2)))

# a ballot for the slot after a slot that waits waits
def Slot.waits_up(
  m: Maybe<&2, RLines.State>,
  k: Nat
) -> {RKnown.Slot.waits(m, k) == True{}: Bool} -> {RKnown.Slot.waits(m, 1n+k) == True{}: Bool}:
  match m:
    case None{}:
      h => {==}
    case Some{RLines.State{vs, j}}:
      h => Shared.Nat.le_succ(j, k)(h)

# the next slot of a state, when it waits, is read from the facts that a
# work may act on as from the facts xs, once the rule u of the slot is known
def Step.at_open(
  +s: RFacts.Plain(),
  +xs: List<&2, Types.Fact>,
  +c: Ledgers.Line,
  +st: RLines.State,
  u: Maybe<&2, RLines.Rule>
) -> {
  RKnown.Slot.waits(RLines.Line.state(s, c), RLines.State.slot(st)) == True{}: Bool
} -> {
  RLines.Line.step.at.in(
    RKnown.Open.of(xs, RKnown.Scene{RKnown.Known.none(), s}),
    c,
    st,
    u
  )
    == RLines.Line.step.at.in(xs, c, st, u): Maybe<&2, RLines.State>
}:
  match u:
    case None{}:
      hw => {==}
    case Some{+rule}:
      hw => Equal.cong(
        List<&2, RRounds.Ballot>,
        Maybe<&2, RLines.State>,
        bs => RLines.Line.step.of(
          st,
          RRounds.Slot.decided(bs, RLines.Rule.nodes(rule), RLines.State.slot(st))
        ),
        RRounds.Slot.ballots(
          RKnown.Open.of(xs, RKnown.Scene{RKnown.Known.none(), s}),
          c,
          RLines.State.slot(st)
        ),
        RRounds.Slot.ballots(xs, c, RLines.State.slot(st)),
        Ballots.open(s, c, RLines.State.slot(st), xs)(hw)
      )

# the state after a decided slot, read from a list of facts, comes after the
# state before it, once the rule u of the slot is known
def Step.at_in_next(
  +xs: List<&2, Types.Fact>,
  +c: Ledgers.Line,
  +st: RLines.State,
  -st2: RLines.State,
  u: Maybe<&2, RLines.Rule>
) -> {
  RLines.Line.step.at.in(xs, c, st, u) == Some{st2}: Maybe<&2, RLines.State>
} -> Moves.Step.Next(st, st2):
  match u:
    case None{}:
      e => Empty.absurd(Moves.Step.Next(st, st2), Shared.Maybe.none_ne_some(RLines.State, st2, e))
    case Some{rule}:
      e => Moves.Step.next.of(
        st,
        st2,
        RLines.Votes.decided.in(xs, c, RLines.State.slot(st), RLines.Rule.nodes(rule))
      )(e)

# a run from a state whose next slot waits reads the facts that a work may
# act on as it reads the facts xs
def Run.open(
  f: Nat,
  +s: RFacts.Plain(),
  +xs: List<&2, Types.Fact>,
  +r: Maybe<&2, List<&2, Types.Entry>>,
  +c: Ledgers.Line,
  +st: RLines.State
) -> {
  RKnown.Slot.waits(RLines.Line.state(s, c), RLines.State.slot(st)) == True{}: Bool
} -> {
  RLines.Line.run.in(
    f,
    RKnown.Open.of(xs, RKnown.Scene{RKnown.Known.none(), s}),
    r,
    c,
    st,
    RLines.Line.step.in(RKnown.Open.of(xs, RKnown.Scene{RKnown.Known.none(), s}), r, c, st)
  )
    == RLines.Line.run.in(f, xs, r, c, st, RLines.Line.step.in(xs, r, c, st)): RLines.State
}:
  match f:
    case 0n:
      hw => {==}
    case 1n+p:
      +hw => (
        %Equal.sym(Maybe<&2, RLines.State>, RLines.Line.step.in(RKnown.Open.of(xs, RKnown.Scene{RKnown.Known.none(), s}), r, c, st), RLines.Line.step.in(xs, r, c, st), Step.at_open(s, xs, c, st, RLines.Line.rule(r, c, RLines.State.versions(st)))(hw)): {RLines.Line.run.in(1n+p, RKnown.Open.of(xs, RKnown.Scene{RKnown.Known.none(), s}), r, c, st, _) == RLines.Line.run.in(1n+p, xs, r, c, st, RLines.Line.step.in(xs, r, c, st)): RLines.State}
        Lists.Maybe.by(RLines.State, m => {RLines.Line.run.in(1n+p, RKnown.Open.of(xs, RKnown.Scene{RKnown.Known.none(), s}), r, c, st, m) == RLines.Line.run.in(1n+p, xs, r, c, st, m): RLines.State}, RLines.Line.step.in(xs, r, c, st), en => {==}, +st2 => e2 => Run.open(p, s, xs, r, c, st2)((
            %Equal.sym(Nat, RLines.State.slot(st2), 1n+RLines.State.slot(st), Moves.Next.slot(st, st2, Step.at_in_next(xs, c, st, st2, RLines.Line.rule(r, c, RLines.State.versions(st)))(e2))): {RKnown.Slot.waits(RLines.Line.state(s, c), _) == True{}: Bool}
            Slot.waits_up(RLines.Line.state(s, c), RLines.State.slot(st))(hw)))))

# the bound of a line among facts with an ask first, when it is there (w),
# is the bound among the facts
def Bound.put_ask(
  +a: Types.Ask,
  +fs: List<&2, Types.Fact>,
  w: Bool,
  +c: Ledgers.Line
) -> {
  RLines.Line.bound(
    List.filter.put(Types.Fact, Types.Fact.Ask{a}, fs, w),
    c
  )
    == RLines.Line.bound(fs, c): Nat
}:
  match w:
    case True{}:
      {==}
    case False{}:
      {==}

# the bound of a line among the facts xs is at most its bound among the
# facts that a work may act on, plus the next slot of the line
def Bound.open_le(
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +vs: List<&2, Types.Entry>,
  +k0: Nat,
  xs: List<&2, Types.Fact>
) -> {
  RLines.Line.state(s, c) == Some{RLines.State{vs, k0}}: Maybe<&2, RLines.State>
} -> {
  Nat.is_le(
    RLines.Line.bound(xs, c),
    Nat.add(RLines.Line.bound(RKnown.Open.of(xs, RKnown.Scene{RKnown.Known.none(), s}), c), k0)
  )
    == True{}: Bool
}:
  match xs:
    case Nil{}:
      e => Shared.Nat.le_add_first(1n, k0)
    case Con{Types.Fact.Ask{Types.Ask{+i, +n, +r}}, +rest}:
      e => (
        %Equal.sym(Nat, RLines.Line.bound(List.filter.put(Types.Fact, Types.Fact.Ask{Types.Ask{i, n, r}}, RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), s}), RKnown.Request.waits(RKnown.Known.none(), s, i, r)), c), RLines.Line.bound(RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), s}), c), Bound.put_ask(Types.Ask{i, n, r}, RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), s}), RKnown.Request.waits(RKnown.Known.none(), s, i, r), c)): {Nat.is_le(RLines.Line.bound(rest, c), Nat.add(_, k0)) == True{}: Bool}
        Bound.open_le(s, c, vs, k0, rest)(e))
    case Con{Types.Fact.Vote{v, Types.Step.Broken{}, x}, rest}:
      e => Bound.open_le(s, c, vs, k0, rest)(e)
    case Con{Types.Fact.Vote{+v, Types.Step.At{+c2, +k2, +t}, +x}, +rest}:
      +e => Lists.Bool.by(
        y => {
          RKnown.Slot.waits(RLines.Line.state(s, c2), k2) == y: Bool
        } -> {
          Nat.is_le(
            Nat.max(
              RLines.Line.bound.at(Ledgers.Line.is_eq(c2, c), k2),
              RLines.Line.bound(rest, c)
            ),
            Nat.add(
              RLines.Line.bound(
                List.filter.put(
                  Types.Fact,
                  Types.Fact.Vote{v, Types.Step.At{c2, k2, t}, x},
                  RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), s}),
                  y
                ),
                c
              ),
              k0
            )
          )
            == True{}: Bool
        },
        RKnown.Slot.waits(RLines.Line.state(s, c2), k2),
        et => ew => Stays.Nat.max_le(
          RLines.Line.bound.at(Ledgers.Line.is_eq(c2, c), k2),
          RLines.Line.bound(rest, c),
          Nat.add(
            Nat.max(
              RLines.Line.bound.at(Ledgers.Line.is_eq(c2, c), k2),
              RLines.Line.bound(RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), s}), c)
            ),
            k0
          )
        )(
          Shared.Nat.le_trans(
            RLines.Line.bound.at(Ledgers.Line.is_eq(c2, c), k2),
            Nat.max(
              RLines.Line.bound.at(Ledgers.Line.is_eq(c2, c), k2),
              RLines.Line.bound(RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), s}), c)
            ),
            Nat.add(
              Nat.max(
                RLines.Line.bound.at(Ledgers.Line.is_eq(c2, c), k2),
                RLines.Line.bound(RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), s}), c)
              ),
              k0
            )
          )(
            Lists.Nat.le_max_left(
              RLines.Line.bound.at(Ledgers.Line.is_eq(c2, c), k2),
              RLines.Line.bound(RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), s}), c)
            )
          )(
            Shared.Nat.le_add_first(
              Nat.max(
                RLines.Line.bound.at(Ledgers.Line.is_eq(c2, c), k2),
                RLines.Line.bound(RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), s}), c)
              ),
              k0
            )
          )
        )(
          Shared.Nat.le_trans(
            RLines.Line.bound(rest, c),
            Nat.add(
              RLines.Line.bound(RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), s}), c),
              k0
            ),
            Nat.add(
              Nat.max(
                RLines.Line.bound.at(Ledgers.Line.is_eq(c2, c), k2),
                RLines.Line.bound(RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), s}), c)
              ),
              k0
            )
          )(
            Bound.open_le(s, c, vs, k0, rest)(e)
          )(
            Shared.Nat.add_le_right(
              Nat.max(
                RLines.Line.bound.at(Ledgers.Line.is_eq(c2, c), k2),
                RLines.Line.bound(RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), s}), c)
              ),
              RLines.Line.bound(RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), s}), c),
              k0
            )(
              Lists.Nat.le_max_right(
                RLines.Line.bound.at(Ledgers.Line.is_eq(c2, c), k2),
                RLines.Line.bound(RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), s}), c)
              )
            )
          )
        ),
        ef => ew => Stays.Nat.max_le(
          RLines.Line.bound.at(Ledgers.Line.is_eq(c2, c), k2),
          RLines.Line.bound(rest, c),
          Nat.add(
            RLines.Line.bound(RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), s}), c),
            k0
          )
        )(
          Lists.Bool.by(
            y => {
              Ledgers.Line.is_eq(c2, c) == y: Bool
            } -> {
              Nat.is_le(
                RLines.Line.bound.at(y, k2),
                Nat.add(
                  RLines.Line.bound(RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), s}), c),
                  k0
                )
              )
                == True{}: Bool
            },
            Ledgers.Line.is_eq(c2, c),
            et2 => eq => Shared.Nat.le_trans(
              1n+k2,
              k0,
              Nat.add(
                RLines.Line.bound(RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), s}), c),
                k0
              )
            )(Shared.Nat.nle_succ_le(k0, k2)((
                  %e: {RKnown.Slot.waits(_, k2) == False{}: Bool}
                  %Ledgers.Line.is_eq_sound(c2, c)(eq): {RKnown.Slot.waits(RLines.Line.state(s, _), k2) == False{}: Bool}
                  ew)))(
              Shared.Nat.le_add(
                RLines.Line.bound(RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), s}), c),
                k0
              )
            ),
            ef2 => eq => Shared.Nat.le_zero(
              Nat.add(
                RLines.Line.bound(RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), s}), c),
                k0
              )
            )
          )({==})
        )(Bound.open_le(s, c, vs, k0, rest)(e))
      )({==})

# the bound of a line among the facts xs is below one more than its bound
# among the facts that a work may act on, plus the next slot of the line
def Bound.open_lt(
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +vs: List<&2, Types.Entry>,
  +k0: Nat,
  +xs: List<&2, Types.Fact>
) -> {
  RLines.Line.state(s, c) == Some{RLines.State{vs, k0}}: Maybe<&2, RLines.State>
} -> {
  Nat.is_lt(
    RLines.Line.bound(xs, c),
    Nat.add(1n+RLines.Line.bound(RKnown.Open.of(xs, RKnown.Scene{RKnown.Known.none(), s}), c), k0)
  )
    == True{}: Bool
}:
  e => Shared.Nat.le_lt(
    RLines.Line.bound(xs, c),
    Nat.add(RLines.Line.bound(RKnown.Open.of(xs, RKnown.Scene{RKnown.Known.none(), s}), c), k0),
    1n+Nat.add(RLines.Line.bound(RKnown.Open.of(xs, RKnown.Scene{RKnown.Known.none(), s}), c), k0)
  )(
    Bound.open_le(s, c, vs, k0, xs)(e)
  )(
    Shared.Nat.lt_succ(
      Nat.add(RLines.Line.bound(RKnown.Open.of(xs, RKnown.Scene{RKnown.Known.none(), s}), c), k0)
    )
  )

# the run that continues a line after a ballot ends at the same state when
# it reads the facts that a work could act on before the ballot, among the
# facts with the ballot
def Go.open(
  +name: String,
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +t: Nat,
  +x: Types.Cast,
  +vs: List<&2, Types.Entry>,
  +k0: Nat,
  +r: Maybe<&2, List<&2, Types.Entry>>
) -> {
  Lines.Line.state(s, c) == Some{RLines.State{vs, k0}}: Maybe<&2, RLines.State>
} -> {
  RKnown.Known.go.in(
    RKnown.Open.of(
      RFacts.Facts.list(
        Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))
      ),
      RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}
    ),
    c,
    RLines.State{vs, k0},
    r
  )
    == RKnown.Known.go.at(
      Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})),
      c,
      RLines.State{vs, k0},
      r
    ): RLines.State
}:
  +e => Equal.trans(
    RLines.State,
    RKnown.Known.go.in(
      RKnown.Open.of(
        RFacts.Facts.list(
          Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))
        ),
        RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}
      ),
      c,
      RLines.State{vs, k0},
      r
    ),
    RLines.Line.run.in(
      1n+RLines.Line.bound(
        RKnown.Open.of(
          RFacts.Facts.list(
            Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))
          ),
          RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}
        ),
        c
      ),
      RFacts.Facts.list(
        Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))
      ),
      r,
      c,
      RLines.State{vs, k0},
      RLines.Line.step.in(
        RFacts.Facts.list(
          Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))
        ),
        r,
        c,
        RLines.State{vs, k0}
      )
    ),
    RKnown.Known.go.at(
      Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})),
      c,
      RLines.State{vs, k0},
      r
    ),
    Run.open(
      1n+RLines.Line.bound(
        RKnown.Open.of(
          RFacts.Facts.list(
            Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))
          ),
          RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}
        ),
        c
      ),
      Facts.Facts.crit(s),
      RFacts.Facts.list(
        Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))
      ),
      r,
      c,
      RLines.State{vs, k0}
    )(Slot.waits_at(Facts.Facts.crit(s), c, vs, k0)(e)),
    Equal.trans(
      RLines.State,
      RLines.Line.run.in(
        1n+RLines.Line.bound(
          RKnown.Open.of(
            RFacts.Facts.list(
              Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))
            ),
            RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}
          ),
          c
        ),
        RFacts.Facts.list(
          Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))
        ),
        r,
        c,
        RLines.State{vs, k0},
        RLines.Line.step.in(
          RFacts.Facts.list(
            Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))
          ),
          r,
          c,
          RLines.State{vs, k0}
        )
      ),
      RLines.Line.run(
        1n+RLines.Line.bound(
          RKnown.Open.of(
            RFacts.Facts.list(
              Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))
            ),
            RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}
          ),
          c
        ),
        Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})),
        r,
        c,
        RLines.State{vs, k0},
        RLines.Line.step(
          Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})),
          r,
          c,
          RLines.State{vs, k0}
        )
      ),
      RKnown.Known.go.at(
        Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})),
        c,
        RLines.State{vs, k0},
        r
      ),
      Equal.sym(
        RLines.State,
        RLines.Line.run(
          1n+RLines.Line.bound(
            RKnown.Open.of(
              RFacts.Facts.list(
                Facts.Facts.crit(
                  Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})
                )
              ),
              RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}
            ),
            c
          ),
          Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})),
          r,
          c,
          RLines.State{vs, k0},
          RLines.Line.step(
            Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})),
            r,
            c,
            RLines.State{vs, k0}
          )
        ),
        RLines.Line.run.in(
          1n+RLines.Line.bound(
            RKnown.Open.of(
              RFacts.Facts.list(
                Facts.Facts.crit(
                  Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})
                )
              ),
              RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}
            ),
            c
          ),
          RFacts.Facts.list(
            Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))
          ),
          r,
          c,
          RLines.State{vs, k0},
          RLines.Line.step.in(
            RFacts.Facts.list(
              Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))
            ),
            r,
            c,
            RLines.State{vs, k0}
          )
        ),
        (
          %Step.in_eq(Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})), r, c, RLines.State{vs, k0}): {RLines.Line.run(1n+RLines.Line.bound(RKnown.Open.of(RFacts.Facts.list(Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))), RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}), c), Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})), r, c, RLines.State{vs, k0}, RLines.Line.step(Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})), r, c, RLines.State{vs, k0})) == RLines.Line.run.in(1n+RLines.Line.bound(RKnown.Open.of(RFacts.Facts.list(Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))), RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}), c), RFacts.Facts.list(Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))), r, c, RLines.State{vs, k0}, _): RLines.State}
          Run.in_eq(1n+RLines.Line.bound(RKnown.Open.of(RFacts.Facts.list(Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))), RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}), c), Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})), r, c, RLines.State{vs, k0}, RLines.Line.step(Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})), r, c, RLines.State{vs, k0})))
      ),
      Run.fuel(
        1n+RLines.Line.bound(
          RKnown.Open.of(
            RFacts.Facts.list(
              Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))
            ),
            RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}
          ),
          c
        ),
        1n+RLines.Line.bound(
          RFacts.Facts.list(
            Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))
          ),
          c
        ),
        Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}),
        r,
        c,
        RLines.State{vs, k0}
      )(
        Bound.open_lt(
          Facts.Facts.crit(s),
          c,
          vs,
          k0,
          RFacts.Facts.list(
            Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))
          )
        )(e)
      )(
        Nat.lt_succ_add(
          RLines.Line.bound(
            RFacts.Facts.list(
              Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))
            ),
            c
          ),
          k0
        )
      )
    )
  )

# a ballot for the next slot of a line waits, as a fact
def Vote.waits(
  +name: String,
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +t: Nat,
  +x: Types.Cast,
  +st: RLines.State
) -> {
  Lines.Line.state(s, c) == Some{st}: Maybe<&2, RLines.State>
} -> {
  Nat.is_eq(RLines.State.slot(st), k) == True{}: Bool
} -> {
  RKnown.Fact.waits(
    RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)},
    Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}
  )
    == True{}: Bool
}:
  e => et => (
    %Equal.sym(Maybe<&2, RLines.State>, Lines.Line.state(s, c), Some{st}, e): {RKnown.Slot.waits(_, k) == True{}: Bool}
    Slot.waits_eq(st, k)(et))

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof does not run
# the facts that a work could act on, with a ballot for the next slot of a
# line, are the facts that it could act on before the ballot among the facts
# with the ballot
def Walk.open(
  +name: String,
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +t: Nat,
  +x: Types.Cast,
  +st: RLines.State,
  +fs: List<&2, Types.Fact>
) -> {
  Lines.Line.state(s, c) == Some{st}: Maybe<&2, RLines.State>
} -> {
  Nat.is_eq(RLines.State.slot(st), k) == True{}: Bool
} -> {
  fs
    == RKnown.Open.of(
      RFacts.Facts.list(Facts.Facts.crit(s)),
      RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}
    ): List<&2, Types.Fact>
} -> {
  RKnown.Open.put(
    fs,
    Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}
  )
    == RKnown.Open.of(
      RFacts.Facts.list(
        Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))
      ),
      RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}
    ): List<&2, Types.Fact>
}:
  e => et => efs => (
    %Equal.sym(List<&2, Types.Fact>, RFacts.Facts.list(Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))), Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, RFacts.Facts.list(Facts.Facts.crit(s)), Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}), Listed.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})): {RKnown.Open.put(fs, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}) == RKnown.Open.of(_, RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}): List<&2, Types.Fact>}
    %Equal.sym(List<&2, Types.Fact>, RKnown.Open.of(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, RFacts.Facts.list(Facts.Facts.crit(s)), Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}), RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}), Bool.pick(List<&2, Types.Fact>, RKnown.Fact.waits(RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}), Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, RKnown.Open.of(RFacts.Facts.list(Facts.Facts.crit(s)), RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}), Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}), RKnown.Open.of(RFacts.Facts.list(Facts.Facts.crit(s)), RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)})), Orders.Values.keep_insert(~Types.Fact, ~Coded.Fact.words, ~Coded.Fact.words_inj, ~RKnown.Scene, ~RKnown.Fact.waits, RFacts.Facts.list(Facts.Facts.crit(s)), Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}, RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)})(Listed.sorted(s))): {RKnown.Open.put(fs, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}) == _: List<&2, Types.Fact>}
    %Equal.sym(Bool, RKnown.Fact.waits(RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}), True{}, Vote.waits(name, s, c, k, t, x, st)(e)(et)): {RKnown.Open.put(fs, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}) == Bool.pick(List<&2, Types.Fact>, _, Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, RKnown.Open.of(RFacts.Facts.list(Facts.Facts.crit(s)), RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}), Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}), RKnown.Open.of(RFacts.Facts.list(Facts.Facts.crit(s)), RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)})): List<&2, Types.Fact>}
    %efs: {RKnown.Open.put(fs, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}) == Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, _, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}): List<&2, Types.Fact>}
    Open.put_insert(fs, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the run that continues a line after a ballot for its next slot ends at the
# same state when it reads the facts that the table holds for a work, with
# the ballot
def Next.walk.go(
  +kn: RKnown.Known(),
  +name: String,
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +t: Nat,
  +x: Types.Cast,
  +vs: List<&2, Types.Entry>,
  +k0: Nat,
  +r: Maybe<&2, List<&2, Types.Entry>>
) -> {
  Lines.Line.state(s, c) == Some{RLines.State{vs, k0}}: Maybe<&2, RLines.State>
} -> {
  Nat.is_eq(k0, k) == True{}: Bool
} -> {
  RContents.Known.fit(kn, Facts.Facts.crit(s)) == True{}: Bool
} -> {
  RKnown.Known.go.of(
    RKnown.Known.walk(kn, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}),
    Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})),
    c,
    RLines.State{vs, k0},
    r
  )
    == RKnown.Known.go.at(
      Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})),
      c,
      RLines.State{vs, k0},
      r
    ): RLines.State
}:
  +e => et => hf => Lists.Maybe.by(
    List<&2, Types.Fact>,
    mm => {
      RKnown.Known.go.of(
        RKnown.Known.walk.of(mm, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}),
        Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})),
        c,
        RLines.State{vs, k0},
        r
      )
        == RKnown.Known.go.at(
          Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})),
          c,
          RLines.State{vs, k0},
          r
        ): RLines.State
    },
    RKnown.Known.open(kn),
    en => {==},
    +fs => es => (
      %Equal.sym(List<&2, Types.Fact>, RKnown.Open.put(fs, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}), RKnown.Open.of(RFacts.Facts.list(Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))), RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)}), Walk.open(name, s, c, k, t, x, RLines.State{vs, k0}, fs)(e)(et)(Known.open_fit(kn, Facts.Facts.crit(s), fs)(hf)(es))): {RKnown.Known.go.in(_, c, RLines.State{vs, k0}, r) == RKnown.Known.go.at(Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})), c, RLines.State{vs, k0}, r): RLines.State}
      Go.open(name, s, c, k, t, x, vs, k0, r)(e))
  )

# the state that a ballot continues is the same when its run reads the facts
# that the table holds for a work, with the ballot
def Next.walk(
  +kn: RKnown.Known(),
  +name: String,
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +t: Nat,
  +x: Types.Cast,
  m: Maybe<&2, RLines.State>,
  r: Maybe<&2, Maybe<&2, List<&2, Types.Entry>>>
) -> (
  {m == None{}: Maybe<&2, RLines.State>} | {Lines.Line.state(s, c) == m: Maybe<&2, RLines.State>}
) -> {
  RContents.Known.fit(kn, Facts.Facts.crit(s)) == True{}: Bool
} -> {
  RKnown.Known.next.of(
    RKnown.Known.walk(kn, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}),
    Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})),
    c,
    k,
    m,
    r
  )
    == RKnown.Known.next.of(
      None{},
      Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})),
      c,
      k,
      m,
      r
    ): Maybe<&2, RLines.State>
}:
  match m r:
    case None{} None{}:
      e => hf => {==}
    case None{} Some{rr}:
      e => hf => {==}
    case Some{st} None{}:
      e => hf => {==}
    case Some{RLines.State{+vs, +k0}} Some{+rr}:
      e => hf => Lists.Bool.by(
        y => {
          Nat.is_eq(k0, k) == y: Bool
        } -> {
          Shared.Maybe.when(
            RLines.State,
            y,
            u => Some{
              RKnown.Known.go.of(
                RKnown.Known.walk(kn, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}),
                Facts.Facts.crit(
                  Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})
                ),
                c,
                RLines.State{vs, k0},
                rr
              )
            }
          )
            == Shared.Maybe.when(
              RLines.State,
              y,
              u => Some{
                RKnown.Known.go.at(
                  Facts.Facts.crit(
                    Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})
                  ),
                  c,
                  RLines.State{vs, k0},
                  rr
                )
              }
            ): Maybe<&2, RLines.State>
        },
        Nat.is_eq(k0, k),
        et => eq => Equal.cong(
          RLines.State,
          Maybe<&2, RLines.State>,
          y => Some{y},
          RKnown.Known.go.of(
            RKnown.Known.walk(kn, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}),
            Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})),
            c,
            RLines.State{vs, k0},
            rr
          ),
          RKnown.Known.go.at(
            Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})),
            c,
            RLines.State{vs, k0},
            rr
          ),
          Next.walk.go(
            kn,
            name,
            s,
            c,
            k,
            t,
            x,
            vs,
            k0,
            rr
          )(
            Known.have(
              Maybe<&2, RLines.State>,
              Some{RLines.State{vs, k0}},
              Lines.Line.state(s, c),
              RLines.State{vs, k0},
              e
            )
          )(eq)(hf)
        ),
        ef => eq => {==}
      )({==})

# the table after a ballot is the same when the run that continues the line
# reads the facts that the table holds for a work, with the ballot
def Known.cast_walk(
  +kn: RKnown.Known(),
  +name: String,
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +t: Nat,
  +x: Types.Cast
) -> {
  RContents.Known.fit(kn, Facts.Facts.crit(s)) == True{}: Bool
} -> {
  RKnown.Known.cast.plain(
    kn,
    Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})),
    c,
    k,
    RKnown.Known.walk(kn, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})
  )
    == RKnown.Known.cast.plain(
      kn,
      Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})),
      c,
      k,
      None{}
    ): RKnown.Known()
}:
  +hf => Equal.cong(
    Maybe<&2, RLines.State>,
    RKnown.Known(),
    y => RKnown.Known.cast.to(
      kn,
      c,
      List.append(
        &2,
        RKnown.Kept,
        RKnown.Known.voted(kn, c),
        RKnown.Known.spared(
          RKnown.Known.safe(
            c,
            RKnown.Known.find(kn, c),
            RKnown.Known.find(kn, RKnown.Known.root(c)),
            k
          ),
          kn
        )
      ),
      y
    ),
    RKnown.Known.next.of(
      RKnown.Known.walk(kn, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}),
      Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})),
      c,
      k,
      RKnown.Known.find(kn, c),
      RKnown.Known.over(c, RKnown.Known.find(kn, RKnown.Known.root(c)))
    ),
    RKnown.Known.next.of(
      None{},
      Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})),
      c,
      k,
      RKnown.Known.find(kn, c),
      RKnown.Known.over(c, RKnown.Known.find(kn, RKnown.Known.root(c)))
    ),
    Next.walk(
      kn,
      name,
      s,
      c,
      k,
      t,
      x,
      RKnown.Known.find(kn, c),
      RKnown.Known.over(c, RKnown.Known.find(kn, RKnown.Known.root(c)))
    )(Known.found(kn, Facts.Facts.crit(s), c)(Fit.ok(kn, Facts.Facts.crit(s))(hf)))(hf)
  )

# The facts that a work may act on after a ballot
# -----------------------------------------------

# what is known of the facts m that a work could act on, with the fact that
# joined them: those among them that a work may act on in the facts s are
# all that it may act on
def Moved.Ok(m: Maybe<&2, List<&2, Types.Fact>>, +s: RFacts.Plain()) -> Type:
  match m:
    case None{}:
      Unit
    case Some{fs}:
      {
        RKnown.Open.of(
          fs,
          RKnown.Scene{RKnown.Known.none(), s}
        )
          == RKnown.Open.of(
            RFacts.Facts.list(s),
            RKnown.Scene{RKnown.Known.none(), s}
          ): List<&2, Types.Fact>
      }

# what is known of the number n, with the facts m that a work could act on:
# it is the greatest number of an ask in the facts s
def Moved.Top(m: Maybe<&2, List<&2, Types.Fact>>, n: Nat, +s: RFacts.Plain()) -> Type:
  match m:
    case None{}:
      Unit
    case Some{fs}:
      {n == RFacts.Seq.peak(RFacts.Facts.list(s)): Nat}

# what is known of the newest writes t, if any: they are those of the facts s
def Moved.Tops(t: Maybe<&2, Crits.Crit<Types.Ask>>, +s: RFacts.Plain()) -> Type:
  match t:
    case None{}:
      Unit
    case Some{tx}:
      {tx == RKnown.Tops.of(RFacts.Facts.list(s)): Crits.Crit<Types.Ask>}

# the lines of merges x, if any, are those of the facts s
def Moved.Merges(x: Maybe<&2, Crits.Crit<Ledgers.Line>>, +s: RFacts.Plain()) -> Type:
  match x:
    case None{}:
      Unit
    case Some{mx}:
      {mx == RKnown.Mergers.of(RFacts.Facts.list(s)): Crits.Crit<Ledgers.Line>}

# a right table that holds nothing for a work, with the facts that a work
# may act on after a fact joined them, the greatest number of an ask, the
# newest writes and the lines of merges, fits
def Known.moved_fit(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  m: Maybe<&2, List<&2, Types.Fact>>,
  +n: Nat,
  t: Maybe<&2, Crits.Crit<Types.Ask>>,
  x: Maybe<&2, Crits.Crit<Ledgers.Line>>
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RKnown.Known.shelf(kn) == None{}: Maybe<&2, RKnown.Kept>
} -> Moved.Ok(
  m,
  s
) -> Moved.Top(
  m,
  n,
  s
) -> Moved.Tops(
  t,
  s
) -> Moved.Merges(
  x,
  s
) -> {RContents.Known.fit(RKnown.Known.moved(kn, s, m, n, t, x), s) == True{}: Bool}:
  match m t x:
    case None{} None{} None{}:
      ok => sh => u => u2 => u3 => u4 => Fit.both(kn, s)(ok)((
          %Equal.sym(Maybe<&2, RKnown.Kept>, RKnown.Known.shelf(kn), None{}, sh): {RContents.Shelf.fits(_, s) == True{}: Bool}
          {==}))
    case None{} None{} Some{mx}:
      ok => sh => u => u2 => u3 => u4 => Fit.both(kn, s)(ok)((
          %Equal.sym(Maybe<&2, RKnown.Kept>, RKnown.Known.shelf(kn), None{}, sh): {RContents.Shelf.fits(_, s) == True{}: Bool}
          {==}))
    case None{} Some{tx} None{}:
      ok => sh => u => u2 => u3 => u4 => Fit.both(kn, s)(ok)((
          %Equal.sym(Maybe<&2, RKnown.Kept>, RKnown.Known.shelf(kn), None{}, sh): {RContents.Shelf.fits(_, s) == True{}: Bool}
          {==}))
    case None{} Some{tx} Some{mx}:
      ok => sh => u => u2 => u3 => u4 => Fit.both(kn, s)(ok)((
          %Equal.sym(Maybe<&2, RKnown.Kept>, RKnown.Known.shelf(kn), None{}, sh): {RContents.Shelf.fits(_, s) == True{}: Bool}
          {==}))
    case Some{fs} None{} None{}:
      ok => sh => u => u2 => u3 => u4 => Fit.both(kn, s)(ok)((
          %Equal.sym(Maybe<&2, RKnown.Kept>, RKnown.Known.shelf(kn), None{}, sh): {RContents.Shelf.fits(_, s) == True{}: Bool}
          {==}))
    case Some{fs} None{} Some{mx}:
      ok => sh => u => u2 => u3 => u4 => Fit.both(kn, s)(ok)((
          %Equal.sym(Maybe<&2, RKnown.Kept>, RKnown.Known.shelf(kn), None{}, sh): {RContents.Shelf.fits(_, s) == True{}: Bool}
          {==}))
    case Some{fs} Some{tx} None{}:
      ok => sh => u => u2 => u3 => u4 => Fit.both(kn, s)(ok)((
          %Equal.sym(Maybe<&2, RKnown.Kept>, RKnown.Known.shelf(kn), None{}, sh): {RContents.Shelf.fits(_, s) == True{}: Bool}
          {==}))
    case Some{+fs} Some{+tx} Some{+mx}:
      +ok => sh => e => et => e3 => e4 => Reads.Eq.back(
        Crits.Crit<Ledgers.Line>,
        y => {
          RContents.Known.fit(
            RKnown.Open{
              RKnown.Open.of(fs, RKnown.Scene{RKnown.Open{[], n, tx, y} <> kn, s}),
              n,
              tx,
              y
            }
              <> kn,
            s
          )
            == True{}: Bool
        },
        mx,
        RKnown.Mergers.of(RFacts.Facts.list(s)),
        e4,
        Fit.both(
          RKnown.Open{
            RKnown.Open.of(
              fs,
              RKnown.Scene{RKnown.Open{[], n, tx, RKnown.Mergers.of(RFacts.Facts.list(s))} <> kn, s}
            ),
            n,
            tx,
            RKnown.Mergers.of(RFacts.Facts.list(s))
          }
            <> kn,
          s
        )(
          ok
        )(
          Open.fits_of(
            RKnown.Open.of(
              fs,
              RKnown.Scene{RKnown.Open{[], n, tx, RKnown.Mergers.of(RFacts.Facts.list(s))} <> kn, s}
            ),
            n,
            tx,
            RKnown.Mergers.of(RFacts.Facts.list(s)),
            s
          )(
            Shared.Bool.and_both(
              Shared.List.is_eq(
                ~Types.Fact,
                ~Coded.Fact.is_eq,
                RKnown.Open.of(
                  fs,
                  RKnown.Scene{
                    RKnown.Open{[], n, tx, RKnown.Mergers.of(RFacts.Facts.list(s))} <> kn,
                    s
                  }
                ),
                RKnown.Open.of(RFacts.Facts.list(s), RKnown.Scene{RKnown.Known.none(), s})
              ),
              Nat.is_eq(n, RFacts.Seq.peak(RFacts.Facts.list(s)))
            )((
                %e: {Shared.List.is_eq(~Types.Fact, ~Coded.Fact.is_eq, RKnown.Open.of(fs, RKnown.Scene{RKnown.Open{[], n, tx, RKnown.Mergers.of(RFacts.Facts.list(s))} <> kn, s}), _) == True{}: Bool}
                %Open.of_ok(RKnown.Open{[], n, tx, RKnown.Mergers.of(RFacts.Facts.list(s))} <> kn, s, fs)(ok)(Mergers.Mergers.same_refl(RKnown.Mergers.of(RFacts.Facts.list(s)))): {Shared.List.is_eq(~Types.Fact, ~Coded.Fact.is_eq, RKnown.Open.of(fs, RKnown.Scene{RKnown.Open{[], n, tx, RKnown.Mergers.of(RFacts.Facts.list(s))} <> kn, s}), _) == True{}: Bool}
                Shared.List.is_eq_refl(~Types.Fact, ~Coded.Fact.is_eq, ~Coded.Fact.laws(), RKnown.Open.of(fs, RKnown.Scene{RKnown.Open{[], n, tx, RKnown.Mergers.of(RFacts.Facts.list(s))} <> kn, s}))))(
              (
                %et: {Nat.is_eq(n, _) == True{}: Bool}
                Shared.Nat.is_eq_refl(n))
            )
          )(e3)({==})
        )
      )

# the greatest number of an ask after a ballot is the greater of the number
# that the ballot votes for and the greatest before
def Voted.peak(
  +name: String,
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +t: Nat,
  +x: Types.Cast
) -> {
  RFacts.Seq.peak(
    RFacts.Facts.list(
      Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))
    )
  )
    == Nat.max(
      RFacts.Seq.of(Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}),
      RFacts.Seq.peak(RFacts.Facts.list(Facts.Facts.crit(s)))
    ): Nat
}:
  (
    %Equal.sym(List<&2, Types.Fact>, RFacts.Facts.list(Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))), Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, RFacts.Facts.list(Facts.Facts.crit(s)), Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}), Listed.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})): {RFacts.Seq.peak(_) == Nat.max(RFacts.Seq.of(Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}), RFacts.Seq.peak(RFacts.Facts.list(Facts.Facts.crit(s)))): Nat}
    Seq.peak_insert(RFacts.Facts.list(Facts.Facts.crit(s)), Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))

# Voted.top, with the entry m that the table holds for a work
def Voted.top.at(
  m: Maybe<&2, RKnown.Kept>,
  +name: String,
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +t: Nat,
  +x: Types.Cast
) -> {
  RContents.Shelf.fits(m, Facts.Facts.crit(s)) == True{}: Bool
} -> Moved.Top(
  RKnown.Known.walk.of(RKnown.Shelf.facts(m), Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}),
  Nat.max(RFacts.Seq.of(Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}), RKnown.Shelf.top(m)),
  Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))
):
  match m:
    case None{}:
      h => Unit{}
    case Some{RKnown.Kept{c2, st2}}:
      h => Unit{}
    case Some{RKnown.Stock{m2, lwm2}}:
      h => Unit{}
    case Some{RKnown.Ruled{c2, zu2, u2}}:
      h => Unit{}
    case Some{RKnown.Made{c2, y2}}:
      h => Unit{}
    case Some{RKnown.Open{+fs2, +pk2, +tx9, +mtx9}}:
      h => (
        %Equal.sym(Nat, RFacts.Seq.peak(RFacts.Facts.list(Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})))), Nat.max(RFacts.Seq.of(Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}), RFacts.Seq.peak(RFacts.Facts.list(Facts.Facts.crit(s)))), Voted.peak(name, s, c, k, t, x)): {Nat.max(RFacts.Seq.of(Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}), pk2) == _: Nat}
        %Shared.Nat.is_eq_sound(pk2, RFacts.Seq.peak(RFacts.Facts.list(Facts.Facts.crit(s))))(Shared.Bool.and_true_right(Shared.List.is_eq(~Types.Fact, ~Coded.Fact.is_eq, fs2, RKnown.Open.of(RFacts.Facts.list(Facts.Facts.crit(s)), RKnown.Scene{RKnown.Known.none(), Facts.Facts.crit(s)})), Nat.is_eq(pk2, RFacts.Seq.peak(RFacts.Facts.list(Facts.Facts.crit(s)))))(Open.fits_old(fs2, pk2, tx9, mtx9, Facts.Facts.crit(s))(h))): {Nat.max(RFacts.Seq.of(Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}), pk2) == Nat.max(RFacts.Seq.of(Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}), _): Nat}
        {==})

# the number that a table that fits gives for the facts after a ballot is
# the greatest number of an ask in them
def Voted.top(
  +kn: RKnown.Known(),
  +name: String,
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +t: Nat,
  +x: Types.Cast
) -> {
  RContents.Known.fit(kn, Facts.Facts.crit(s)) == True{}: Bool
} -> Moved.Top(
  RKnown.Known.walk.if(
    RKnown.Known.safe(c, RKnown.Known.find(kn, c), RKnown.Known.find(kn, RKnown.Known.root(c)), k),
    RKnown.Known.walk(kn, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})
  ),
  Nat.max(
    RFacts.Seq.of(Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}),
    RKnown.Shelf.top(RKnown.Known.shelf(kn))
  ),
  Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))
):
  h => Lists.Bool.by(
    y => Moved.Top(
      RKnown.Known.walk.if(
        y,
        RKnown.Known.walk(kn, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})
      ),
      Nat.max(
        RFacts.Seq.of(Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}),
        RKnown.Shelf.top(RKnown.Known.shelf(kn))
      ),
      Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))
    ),
    RKnown.Known.safe(c, RKnown.Known.find(kn, c), RKnown.Known.find(kn, RKnown.Known.root(c)), k),
    et => Voted.top.at(
      RKnown.Known.shelf(kn),
      name,
      s,
      c,
      k,
      t,
      x
    )(Fit.open(kn, Facts.Facts.crit(s))(h)),
    ef => Unit{}
  )

# Voted.tops, with the entry m that the table holds for a work
def Voted.tops.at(
  m: Maybe<&2, RKnown.Kept>,
  +name: String,
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +t: Nat,
  +x: Types.Cast
) -> {
  RContents.Shelf.fits(m, Facts.Facts.crit(s)) == True{}: Bool
} -> Moved.Tops(
  RKnown.Shelf.tops(m),
  Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))
):
  match m:
    case None{}:
      h => Unit{}
    case Some{RKnown.Kept{c2, st2}}:
      h => Unit{}
    case Some{RKnown.Stock{m2, lwm2}}:
      h => Unit{}
    case Some{RKnown.Ruled{c2, zu2, u2}}:
      h => Unit{}
    case Some{RKnown.Made{c2, y2}}:
      h => Unit{}
    case Some{RKnown.Open{+fs2, +pk2, +tx2, +mtx2}}:
      h => (
        %Equal.sym(List<&2, Types.Fact>, RFacts.Facts.list(Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))), Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, RFacts.Facts.list(Facts.Facts.crit(s)), Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}), Listed.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})): {tx2 == RKnown.Tops.of(_): Crits.Crit<Types.Ask>}
        Equal.trans(Crits.Crit<Types.Ask>, tx2, RKnown.Tops.of(RFacts.Facts.list(Facts.Facts.crit(s))), RKnown.Tops.of(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, RFacts.Facts.list(Facts.Facts.crit(s)), Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})), Open.fits_tops(fs2, pk2, tx2, mtx2, Facts.Facts.crit(s))(h), Equal.sym(Crits.Crit<Types.Ask>, RKnown.Tops.of(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, RFacts.Facts.list(Facts.Facts.crit(s)), Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})), RKnown.Tops.of(RFacts.Facts.list(Facts.Facts.crit(s))), Newest.Tops.of_insert(RFacts.Facts.list(Facts.Facts.crit(s)), Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})({==}))))

# the newest writes that a table that fits holds are those of the facts
# after a ballot
def Voted.tops(
  +kn: RKnown.Known(),
  +name: String,
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +t: Nat,
  +x: Types.Cast
) -> {
  RContents.Known.fit(kn, Facts.Facts.crit(s)) == True{}: Bool
} -> Moved.Tops(
  RKnown.Shelf.tops(RKnown.Known.shelf(kn)),
  Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))
):
  h => Voted.tops.at(
    RKnown.Known.shelf(kn),
    name,
    s,
    c,
    k,
    t,
    x
  )(Fit.open(kn, Facts.Facts.crit(s))(h))

# the lines of merges that an entry that is right holds are those of the
# facts after a ballot
def Voted.merges.at(
  m: Maybe<&2, RKnown.Kept>,
  +name: String,
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +t: Nat,
  +x: Types.Cast
) -> {
  RContents.Shelf.fits(m, Facts.Facts.crit(s)) == True{}: Bool
} -> Moved.Merges(
  RKnown.Shelf.merges(m),
  Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))
):
  match m:
    case None{}:
      h => Unit{}
    case Some{RKnown.Kept{c2, st2}}:
      h => Unit{}
    case Some{RKnown.Stock{m2, lwm2}}:
      h => Unit{}
    case Some{RKnown.Ruled{c2, zu2, u2}}:
      h => Unit{}
    case Some{RKnown.Made{c2, y2}}:
      h => Unit{}
    case Some{RKnown.Open{+fs2, +pk2, +tx2, +mtx2}}:
      h => Equal.trans(
        Crits.Crit<Ledgers.Line>,
        mtx2,
        RKnown.Mergers.of(RFacts.Facts.list(Facts.Facts.crit(s))),
        RKnown.Mergers.of(
          RFacts.Facts.list(
            Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))
          )
        ),
        Open.fits_merges(fs2, pk2, tx2, mtx2, Facts.Facts.crit(s))(h),
        Equal.sym(
          Crits.Crit<Ledgers.Line>,
          RKnown.Mergers.of(
            RFacts.Facts.list(
              Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))
            )
          ),
          RKnown.Mergers.of(RFacts.Facts.list(Facts.Facts.crit(s))),
          Equal.trans(
            Crits.Crit<Ledgers.Line>,
            RKnown.Mergers.of(
              RFacts.Facts.list(
                Facts.Facts.crit(
                  Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})
                )
              )
            ),
            RKnown.Mergers.of(
              Orders.Values.insert(
                ~Types.Fact,
                ~Coded.Fact.words,
                RFacts.Facts.list(Facts.Facts.crit(s)),
                Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}
              )
            ),
            RKnown.Mergers.of(RFacts.Facts.list(Facts.Facts.crit(s))),
            Equal.cong(
              List<&2, Types.Fact>,
              Crits.Crit<Ledgers.Line>,
              l => RKnown.Mergers.of(l),
              RFacts.Facts.list(
                Facts.Facts.crit(
                  Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})
                )
              ),
              Orders.Values.insert(
                ~Types.Fact,
                ~Coded.Fact.words,
                RFacts.Facts.list(Facts.Facts.crit(s)),
                Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}
              ),
              Listed.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})
            ),
            Mergers.Mergers.of_insert(
              RFacts.Facts.list(Facts.Facts.crit(s)),
              Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}
            )({==})
          )
        )
      )

# the lines of merges that a table that fits holds are those of the facts
# after a ballot
def Voted.merges(
  +kn: RKnown.Known(),
  +name: String,
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +t: Nat,
  +x: Types.Cast
) -> {
  RContents.Known.fit(kn, Facts.Facts.crit(s)) == True{}: Bool
} -> Moved.Merges(
  RKnown.Shelf.merges(RKnown.Known.shelf(kn)),
  Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))
):
  h => Voted.merges.at(
    RKnown.Known.shelf(kn),
    name,
    s,
    c,
    k,
    t,
    x
  )(Fit.open(kn, Facts.Facts.crit(s))(h))

# Voted.moved_ok, with the states m of the line and ms of its store that the
# table holds
def Voted.moved_ok.at(
  +kn: RKnown.Known(),
  +name: String,
  +s: Facts.Facts(),
  c: Ledgers.Line,
  +k: Nat,
  +t: Nat,
  +x: Types.Cast,
  m: Maybe<&2, RLines.State>,
  ms: Maybe<&2, RLines.State>
) -> (
  {m == None{}: Maybe<&2, RLines.State>} | {Lines.Line.state(s, c) == m: Maybe<&2, RLines.State>}
) -> (
  {
    ms == None{}: Maybe<&2, RLines.State>
  }
    | {Lines.Line.state(s, RKnown.Known.root(c)) == ms: Maybe<&2, RLines.State>}
) -> {
  RContents.Known.fit(kn, Facts.Facts.crit(s)) == True{}: Bool
} -> Moved.Ok(
  RKnown.Known.walk.if(
    RKnown.Known.safe(c, m, ms, k),
    RKnown.Known.walk(kn, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})
  ),
  Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))
):
  match c m ms:
    case Ledgers.Line{h, None{}} None{} None{}:
      e => es => hf => Unit{}
    case Ledgers.Line{h, None{}} None{} Some{y}:
      e => es => hf => Unit{}
    case Ledgers.Line{h, None{}} Some{st} None{}:
      e => es => hf => Unit{}
    case Ledgers.Line{h, None{}} Some{st} Some{y}:
      e => es => hf => Unit{}
    case Ledgers.Line{h, Some{b}} None{} None{}:
      e => es => hf => Unit{}
    case Ledgers.Line{h, Some{b}} None{} Some{y}:
      e => es => hf => Unit{}
    case Ledgers.Line{h, Some{b}} Some{st} None{}:
      e => es => hf => Unit{}
    case Ledgers.Line{+h, Some{+b}} Some{+st} Some{RLines.State{+rs, +j}}:
      e => es => hf => Lists.Bool.by(
        y => Moved.Ok(
          RKnown.Known.walk.if(
            y,
            RKnown.Known.walk(
              kn,
              Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}
            )
          ),
          Facts.Facts.crit(
            Facts.Facts.add(
              s,
              Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}
            )
          )
        ),
        Nat.is_eq(RLines.State.slot(st), k),
        et => Lists.Maybe.by(
          List<&2, Types.Fact>,
          mm => Moved.Ok(
            RKnown.Known.walk.of(
              mm,
              Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}
            ),
            Facts.Facts.crit(
              Facts.Facts.add(
                s,
                Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}
              )
            )
          ),
          RKnown.Known.open(kn),
          en => Unit{},
          +fs => efs => Voted.open(
            name,
            s,
            h,
            b,
            k,
            t,
            x,
            st,
            rs,
            j,
            fs
          )(
            Known.have(
              Maybe<&2, RLines.State>,
              Some{st},
              Lines.Line.state(s, Ledgers.Line{h, Some{b}}),
              st,
              e
            )
          )(
            et
          )(
            Known.have(
              Maybe<&2, RLines.State>,
              Some{RLines.State{rs, j}},
              Lines.Line.state(s, Ledgers.Line{h, None{}}),
              RLines.State{rs, j},
              es
            )
          )(Known.open_fit(kn, Facts.Facts.crit(s), fs)(hf)(efs))
        ),
        ef => Unit{}
      )

# the facts that a table that fits holds for a work, when a ballot leaves
# the other lines as they are, with the ballot: those among them that a work
# may act on after the ballot are all that it may act on
def Voted.moved_ok(
  +kn: RKnown.Known(),
  +name: String,
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +t: Nat,
  +x: Types.Cast
) -> {
  RContents.Known.fit(kn, Facts.Facts.crit(s)) == True{}: Bool
} -> Moved.Ok(
  RKnown.Known.walk.if(
    RKnown.Known.safe(c, RKnown.Known.find(kn, c), RKnown.Known.find(kn, RKnown.Known.root(c)), k),
    RKnown.Known.walk(kn, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})
  ),
  Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))
):
  +hf => Voted.moved_ok.at(
    kn,
    name,
    s,
    c,
    k,
    t,
    x,
    RKnown.Known.find(kn, c),
    RKnown.Known.find(kn, RKnown.Known.root(c))
  )(
    Known.found(kn, Facts.Facts.crit(s), c)(Fit.ok(kn, Facts.Facts.crit(s))(hf))
  )(
    Known.found(kn, Facts.Facts.crit(s), RKnown.Known.root(c))(Fit.ok(kn, Facts.Facts.crit(s))(hf))
  )(hf)

# A ballot drops the facts that the table held for a work
# -------------------------------------------------------

# the entries that a vote leaves of a table, then ys, hold for a work the
# facts that ys hold for it
def Known.voted_append(
  kn: RKnown.Known(),
  +c: Ledgers.Line,
  +ys: RKnown.Known()
) -> {
  RKnown.Known.shelf(
    ys
  )
    == RKnown.Known.shelf(
      List.append(&2, RKnown.Kept, RKnown.Known.voted(kn, c), ys)
    ): Maybe<&2, RKnown.Kept>
}:
  match kn:
    case Nil{}:
      {==}
    case Con{RKnown.Kept{+c2, +st2}, +rest}:
      Lists.Bool.by(
        y => {
          RKnown.Known.shelf(
            ys
          )
            == RKnown.Known.shelf(
              List.append(
                &2,
                RKnown.Kept,
                List.filter.put(RKnown.Kept, RKnown.Kept{c2, st2}, RKnown.Known.voted(rest, c), y),
                ys
              )
            ): Maybe<&2, RKnown.Kept>
        },
        Bool.not(RKnown.Known.hit(c, c2)),
        et => Known.voted_append(rest, c, ys),
        ef => Known.voted_append(rest, c, ys)
      )
    case Con{RKnown.Stock{m2, lwm2}, rest}:
      Known.voted_append(rest, c, ys)
    case Con{RKnown.Ruled{+c2, +zu2, +u2}, +rest}:
      Lists.Bool.by(
        y => {
          RKnown.Known.shelf(
            ys
          )
            == RKnown.Known.shelf(
              List.append(
                &2,
                RKnown.Kept,
                List.filter.put(
                  RKnown.Kept,
                  RKnown.Ruled{c2, zu2, u2},
                  RKnown.Known.voted(rest, c),
                  y
                ),
                ys
              )
            ): Maybe<&2, RKnown.Kept>
        },
        Bool.not(RKnown.Known.hit(c, c2)),
        et => Known.voted_append(rest, c, ys),
        ef => Known.voted_append(rest, c, ys)
      )
    case Con{RKnown.Made{+c2, +y2}, +rest}:
      Lists.Bool.by(
        y => {
          RKnown.Known.shelf(
            ys
          )
            == RKnown.Known.shelf(
              List.append(
                &2,
                RKnown.Kept,
                List.filter.put(RKnown.Kept, RKnown.Made{c2, y2}, RKnown.Known.voted(rest, c), y),
                ys
              )
            ): Maybe<&2, RKnown.Kept>
        },
        Bool.not(RKnown.Known.hit(c, c2)),
        et => Known.voted_append(rest, c, ys),
        ef => Known.voted_append(rest, c, ys)
      )
    case Con{RKnown.Open{fs2, pk2, tx9, mtx9}, rest}:
      Known.voted_append(rest, c, ys)

# the contents of a table hold no facts for a work
def Known.contents_shut(
  kn: RKnown.Known()
) -> {RKnown.Known.shelf(RKnown.Known.contents(kn)) == None{}: Maybe<&2, RKnown.Kept>}:
  match kn:
    case Nil{}:
      {==}
    case Con{RKnown.Kept{c2, st2}, rest}:
      Known.contents_shut(rest)
    case Con{RKnown.Stock{m2, lwm2}, rest}:
      {==}
    case Con{RKnown.Ruled{c2, zu2, u2}, rest}:
      Known.contents_shut(rest)
    case Con{RKnown.Made{c2, y2}, rest}:
      Known.contents_shut(rest)
    case Con{RKnown.Open{fs2, pk2, tx9, mtx9}, rest}:
      Known.contents_shut(rest)

# the contents of a table, each with one more as its number, hold no facts
# for a work
def Known.deeper_shut(
  kn: RKnown.Known()
) -> {
  RKnown.Known.shelf(
    RKnown.Known.deeper(RKnown.Known.contents(kn))
  )
    == None{}: Maybe<&2, RKnown.Kept>
}:
  match kn:
    case Nil{}:
      {==}
    case Con{RKnown.Kept{c2, st2}, rest}:
      Known.deeper_shut(rest)
    case Con{RKnown.Stock{m2, lwm2}, rest}:
      {==}
    case Con{RKnown.Ruled{c2, zu2, u2}, rest}:
      Known.deeper_shut(rest)
    case Con{RKnown.Made{c2, y2}, rest}:
      Known.deeper_shut(rest)
    case Con{RKnown.Open{fs2, pk2, tx9, mtx9}, rest}:
      Known.deeper_shut(rest)

# the contents that a ballot spares hold no facts for a work
def Known.spared_shut(
  safe: Bool,
  kn: RKnown.Known()
) -> {RKnown.Known.shelf(RKnown.Known.spared(safe, kn)) == None{}: Maybe<&2, RKnown.Kept>}:
  match safe:
    case True{}:
      Known.deeper_shut(kn)
    case False{}:
      {==}

# a table with the ids of the versions of a line holds the same facts for a
# work
def Known.made_put_open(
  -kn: RKnown.Known(),
  -c: Ledgers.Line,
  m: Maybe<&2, RKnown.Ids>
) -> {
  RKnown.Known.shelf(
    kn
  )
    == RKnown.Known.shelf(RKnown.Known.made.put(kn, c, m)): Maybe<&2, RKnown.Kept>
}:
  match m:
    case None{}:
      {==}
    case Some{y}:
      {==}

# the table after a ballot, built on entries that hold no facts for a work,
# holds none
def Known.cast_to_shut(
  +kn: RKnown.Known(),
  +c: Ledgers.Line,
  +rest: RKnown.Known(),
  +m: Maybe<&2, RLines.State>
) -> {
  RKnown.Known.shelf(rest) == None{}: Maybe<&2, RKnown.Kept>
} -> {RKnown.Known.shelf(RKnown.Known.cast.to(kn, c, rest, m)) == None{}: Maybe<&2, RKnown.Kept>}:
  h => (
    %Known.made_put_open(RKnown.Known.put(rest, c, m), c, RKnown.Made.next(m, RKnown.Known.find(kn, c), RKnown.Known.ids(kn, c))): {_ == None{}: Maybe<&2, RKnown.Kept>}
    %Known.put_open(rest, c, m): {_ == None{}: Maybe<&2, RKnown.Kept>}
    h)

# the table after a ballot holds no facts for a work
def Known.cast_shut(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +k: Nat,
  +w: Maybe<&2, List<&2, Types.Fact>>
) -> {
  RKnown.Known.shelf(RKnown.Known.cast.plain(kn, s, c, k, w)) == None{}: Maybe<&2, RKnown.Kept>
}:
  Known.cast_to_shut(
    kn,
    c,
    List.append(
      &2,
      RKnown.Kept,
      RKnown.Known.voted(kn, c),
      RKnown.Known.spared(
        RKnown.Known.safe(
          c,
          RKnown.Known.find(kn, c),
          RKnown.Known.find(kn, RKnown.Known.root(c)),
          k
        ),
        kn
      )
    ),
    RKnown.Known.next.of(
      w,
      s,
      c,
      k,
      RKnown.Known.find(kn, c),
      RKnown.Known.over(c, RKnown.Known.find(kn, RKnown.Known.root(c)))
    )
  )((
      %Known.voted_append(kn, c, RKnown.Known.spared(RKnown.Known.safe(c, RKnown.Known.find(kn, c), RKnown.Known.find(kn, RKnown.Known.root(c)), k), kn)): {_ == None{}: Maybe<&2, RKnown.Kept>}
      Known.spared_shut(RKnown.Known.safe(c, RKnown.Known.find(kn, c), RKnown.Known.find(kn, RKnown.Known.root(c)), k), kn)))

# A run that keeps the rule and the ids
# -------------------------------------
# A run of a branch that holds the era and the rule of the next version and
# the ids of the versions (RKnown.Run) leaves the state that the run from
# the versions leaves (RKnown.Known.go.in), with the era, the rule and the
# ids of that state.

# what a run holds of the branch c in the state st, with the versions r of
# its store
def Run.of(c: Ledgers.Line, r: List<&2, Types.Entry>, st: RLines.State) -> RKnown.Run:
  match st:
    case RLines.State{+vs, k}:
      +c = c
      RKnown.Run{
        RLines.State{vs, k},
        RLines.Line.era(c, vs),
        RLines.Line.rule(Some{r}, c, vs),
        RKnown.Ids.of(vs)
      }

# Run.of of the state m, if any
def Run.of.maybe(
  c: Ledgers.Line,
  r: List<&2, Types.Entry>,
  m: Maybe<&2, RLines.State>
) -> Maybe<&2, RKnown.Run>:
  match m:
    case None{}:
      None{}
    case Some{st}:
      Some{Run.of(c, r, st)}

# the greatest era of versions with one more is the greater of its era and
# the greatest before
def Peak.snoc(
  vs: List<&2, Types.Entry>,
  +e: Types.Entry
) -> {
  Lists.List.peak(
    ~Types.Entry,
    ~RLines.Entry.era,
    List.append(&2, Types.Entry, vs, [e])
  )
    == Nat.max(RLines.Entry.era(e), Lists.List.peak(~Types.Entry, ~RLines.Entry.era, vs)): Nat
}:
  match vs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      %Equal.sym(
        Nat,
        Lists.List.peak(~Types.Entry, ~RLines.Entry.era, List.append(&2, Types.Entry, rest, [e])),
        Nat.max(RLines.Entry.era(e), Lists.List.peak(~Types.Entry, ~RLines.Entry.era, rest)),
        Peak.snoc(rest, e)
      ): {
        Nat.max(
          RLines.Entry.era(x),
          _
        )
          == Nat.max(
            RLines.Entry.era(e),
            Nat.max(RLines.Entry.era(x), Lists.List.peak(~Types.Entry, ~RLines.Entry.era, rest))
          ): Nat
      }
      Nat.max_swap(
        RLines.Entry.era(x),
        RLines.Entry.era(e),
        Lists.List.peak(~Types.Entry, ~RLines.Entry.era, rest)
      )

# the rule at an era that is the era before is the rule before
def Run.rule_at(
  same: Bool,
  +r: List<&2, Types.Entry>,
  +c: Ledgers.Line,
  +m2: Nat,
  +m: Nat
) -> {
  Nat.is_eq(m2, m) == same: Bool
} -> {
  RKnown.Run.rule(
    same,
    r,
    c,
    m2,
    RLines.Rule.at(r, c, m)
  )
    == RLines.Rule.at(r, c, m2): Maybe<&2, RLines.Rule>
}:
  match same:
    case False{}:
      e => {==}
    case True{}:
      e =>
        %Shared.Nat.is_eq_sound(
          m2,
          m
        )(e): {RLines.Rule.at(r, c, _) == RLines.Rule.at(r, c, m2): Maybe<&2, RLines.Rule>}
        {==}

# Run.put_of, once it is known whether the id of the pick made a version
# (dup)
def Run.put_of.if(
  dup: Bool,
  +h: Hashes.Hash,
  +b: String,
  +r: List<&2, Types.Entry>,
  +vs: List<&2, Types.Entry>,
  +k: Nat,
  +a: Types.Ask,
  +pins: Types.Pins
) -> {
  RKnown.Run.put(
    dup,
    r,
    Ledgers.Line{h, Some{b}},
    vs,
    k,
    RLines.Line.era(Ledgers.Line{h, Some{b}}, vs),
    RLines.Line.rule(Some{r}, Ledgers.Line{h, Some{b}}, vs),
    RKnown.Ids.of(vs),
    Types.Pick{a, pins}
  )
    == Run.of(
      Ledgers.Line{h, Some{b}},
      r,
      RLines.State.put.if(vs, k, Types.Pick{a, pins}, dup)
    ): RKnown.Run
}:
  match dup:
    case True{}:
      {==}
    case False{}:
      +c = {Ledgers.Line{h, Some{b}}: Ledgers.Line}
      +e = {Types.Entry{Types.Pick{a, pins}, k}: Types.Entry}
      +m = Lists.List.peak(~Types.Entry, ~RLines.Entry.era, vs)
      +m2 = Nat.max(RLines.Entry.era(e), m)
      +vs2 = List.append(&2, Types.Entry, vs, [e])
      +x2 = RKnown.Ids.put(RKnown.Ids.of(vs), e)
      +u2 = RKnown.Run.rule(Nat.is_eq(m2, m), r, c, m2, RLines.Rule.at(r, c, m))
      %Equal.sym(
        Nat,
        Lists.List.peak(~Types.Entry, ~RLines.Entry.era, vs2),
        m2,
        Peak.snoc(vs, e)
      ): {
        RKnown.Run{
          RLines.State{vs2, 1n+k},
          m2,
          u2,
          x2
        }
          == RKnown.Run{
            RLines.State{vs2, 1n+k},
            _,
            RLines.Rule.at(r, c, _),
            RKnown.Ids.of(vs2)
          }: RKnown.Run
      }
      %Equal.sym(
        RKnown.Ids,
        RKnown.Ids.of(vs2),
        x2,
        Ids.go_append(vs, [e], RKnown.Ids.new())
      ): {
        RKnown.Run{
          RLines.State{vs2, 1n+k},
          m2,
          u2,
          x2
        }
          == RKnown.Run{RLines.State{vs2, 1n+k}, m2, RLines.Rule.at(r, c, m2), _}: RKnown.Run
      }
      %Run.rule_at(
        Nat.is_eq(m2, m),
        r,
        c,
        m2,
        m
      )(
        {==}
      ): {
        RKnown.Run{
          RLines.State{vs2, 1n+k},
          m2,
          u2,
          x2
        }
          == RKnown.Run{RLines.State{vs2, 1n+k}, m2, _, x2}: RKnown.Run
      }
      {==}

# what a run holds after a decided slot is what it holds of the state after
# the slot
def Run.put_of(
  +h: Hashes.Hash,
  +b: String,
  +r: List<&2, Types.Entry>,
  +vs: List<&2, Types.Entry>,
  +k: Nat,
  pk: Types.Pick
) -> {
  RKnown.Run.put(
    RKnown.Ids.has(RKnown.Ids.of(vs), RLines.Pick.id(pk)),
    r,
    Ledgers.Line{h, Some{b}},
    vs,
    k,
    RLines.Line.era(Ledgers.Line{h, Some{b}}, vs),
    RLines.Line.rule(Some{r}, Ledgers.Line{h, Some{b}}, vs),
    RKnown.Ids.of(vs),
    pk
  )
    == Run.of(Ledgers.Line{h, Some{b}}, r, RLines.State.put(vs, k, pk)): RKnown.Run
}:
  match pk:
    case Types.Pick{+a, +pins}:
      %Equal.sym(
        Bool,
        RKnown.Ids.has(RKnown.Ids.of(vs), RLines.Ask.id(a)),
        Shared.List.some(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, vs, RLines.Ask.id(a)),
        Ids.of_has(vs, RLines.Ask.id(a))
      ): {
        RKnown.Run.put(
          _,
          r,
          Ledgers.Line{h, Some{b}},
          vs,
          k,
          RLines.Line.era(Ledgers.Line{h, Some{b}}, vs),
          RLines.Line.rule(Some{r}, Ledgers.Line{h, Some{b}}, vs),
          RKnown.Ids.of(vs),
          Types.Pick{a, pins}
        )
          == Run.of(
            Ledgers.Line{h, Some{b}},
            r,
            RLines.State.put.if(
              vs,
              k,
              Types.Pick{a, pins},
              Shared.List.some(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, vs, RLines.Ask.id(a))
            )
          ): RKnown.Run
      }
      Run.put_of.if(
        Shared.List.some(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, vs, RLines.Ask.id(a)),
        h,
        b,
        r,
        vs,
        k,
        a,
        pins
      )

# Run.step_of, once the decided pick p of the slot is known
def Run.step_of.pick(
  +h: Hashes.Hash,
  +b: String,
  +r: List<&2, Types.Entry>,
  +vs: List<&2, Types.Entry>,
  +k: Nat,
  +rule: RLines.Rule,
  p: Maybe<&2, Types.Pick>
) -> {
  RLines.Line.rule(Some{r}, Ledgers.Line{h, Some{b}}, vs) == Some{rule}: Maybe<&2, RLines.Rule>
} -> {
  RKnown.Run.step.of(
    r,
    Ledgers.Line{h, Some{b}},
    RKnown.Run{
      RLines.State{vs, k},
      RLines.Line.era(Ledgers.Line{h, Some{b}}, vs),
      Some{rule},
      RKnown.Ids.of(vs)
    },
    p
  )
    == Run.of.maybe(
      Ledgers.Line{h, Some{b}},
      r,
      RLines.Line.step.of(RLines.State{vs, k}, p)
    ): Maybe<&2, RKnown.Run>
}:
  match p:
    case None{}:
      e => {==}
    case Some{+pk}:
      e =>
        %e: {
          Some{
            RKnown.Run.put(
              RKnown.Ids.has(RKnown.Ids.of(vs), RLines.Pick.id(pk)),
              r,
              Ledgers.Line{h, Some{b}},
              vs,
              k,
              RLines.Line.era(Ledgers.Line{h, Some{b}}, vs),
              _,
              RKnown.Ids.of(vs),
              pk
            )
          }
            == Some{
              Run.of(Ledgers.Line{h, Some{b}}, r, RLines.State.put(vs, k, pk))
            }: Maybe<&2, RKnown.Run>
        }
        Equal.cong(
          RKnown.Run,
          Maybe<&2, RKnown.Run>,
          q => Some{q},
          RKnown.Run.put(
            RKnown.Ids.has(RKnown.Ids.of(vs), RLines.Pick.id(pk)),
            r,
            Ledgers.Line{h, Some{b}},
            vs,
            k,
            RLines.Line.era(Ledgers.Line{h, Some{b}}, vs),
            RLines.Line.rule(Some{r}, Ledgers.Line{h, Some{b}}, vs),
            RKnown.Ids.of(vs),
            pk
          ),
          Run.of(Ledgers.Line{h, Some{b}}, r, RLines.State.put(vs, k, pk)),
          Run.put_of(h, b, r, vs, k, pk)
        )

# Run.step_of, once the rule u of the slot is known
def Run.step_of.at(
  +h: Hashes.Hash,
  +b: String,
  +fs: List<&2, Types.Fact>,
  +r: List<&2, Types.Entry>,
  +vs: List<&2, Types.Entry>,
  +k: Nat,
  u: Maybe<&2, RLines.Rule>
) -> {
  RLines.Line.rule(Some{r}, Ledgers.Line{h, Some{b}}, vs) == u: Maybe<&2, RLines.Rule>
} -> {
  RKnown.Run.step(
    fs,
    r,
    Ledgers.Line{h, Some{b}},
    RKnown.Run{
      RLines.State{vs, k},
      RLines.Line.era(Ledgers.Line{h, Some{b}}, vs),
      u,
      RKnown.Ids.of(vs)
    }
  )
    == Run.of.maybe(
      Ledgers.Line{h, Some{b}},
      r,
      RLines.Line.step.at.in(fs, Ledgers.Line{h, Some{b}}, RLines.State{vs, k}, u)
    ): Maybe<&2, RKnown.Run>
}:
  match u:
    case None{}:
      e => {==}
    case Some{+rule}:
      e => Run.step_of.pick(
        h,
        b,
        r,
        vs,
        k,
        rule,
        RLines.Votes.decided.in(fs, Ledgers.Line{h, Some{b}}, k, RLines.Rule.nodes(rule))
      )(e)

# the next slot of a run that holds what Run.of gives is the next slot of
# the state, with what Run.of gives of it
def Run.step_of(
  +h: Hashes.Hash,
  +b: String,
  +fs: List<&2, Types.Fact>,
  +r: List<&2, Types.Entry>,
  st: RLines.State
) -> {
  RKnown.Run.step(
    fs,
    r,
    Ledgers.Line{h, Some{b}},
    Run.of(Ledgers.Line{h, Some{b}}, r, st)
  )
    == Run.of.maybe(
      Ledgers.Line{h, Some{b}},
      r,
      RLines.Line.step.in(fs, Some{r}, Ledgers.Line{h, Some{b}}, st)
    ): Maybe<&2, RKnown.Run>
}:
  match st:
    case RLines.State{+vs, +k}:
      Run.step_of.at(
        h,
        b,
        fs,
        r,
        vs,
        k,
        RLines.Line.rule(Some{r}, Ledgers.Line{h, Some{b}}, vs)
      )({==})

# a run that holds what Run.of gives ends with what Run.of gives of the
# state where the run of the state ends
def Run.go_of(
  f: Nat,
  +h: Hashes.Hash,
  +b: String,
  +fs: List<&2, Types.Fact>,
  +r: List<&2, Types.Entry>,
  +st: RLines.State,
  m: Maybe<&2, RLines.State>
) -> {
  RKnown.Run.go(
    f,
    fs,
    r,
    Ledgers.Line{h, Some{b}},
    Run.of(Ledgers.Line{h, Some{b}}, r, st),
    Run.of.maybe(Ledgers.Line{h, Some{b}}, r, m)
  )
    == Run.of(
      Ledgers.Line{h, Some{b}},
      r,
      RLines.Line.run.in(f, fs, Some{r}, Ledgers.Line{h, Some{b}}, st, m)
    ): RKnown.Run
}:
  match f m:
    case 0n None{}:
      {==}
    case 0n Some{st2}:
      {==}
    case 1n+g None{}:
      {==}
    case 1n+g Some{+st2}:
      %Equal.sym(
        Maybe<&2, RKnown.Run>,
        RKnown.Run.step(fs, r, Ledgers.Line{h, Some{b}}, Run.of(Ledgers.Line{h, Some{b}}, r, st2)),
        Run.of.maybe(
          Ledgers.Line{h, Some{b}},
          r,
          RLines.Line.step.in(fs, Some{r}, Ledgers.Line{h, Some{b}}, st2)
        ),
        Run.step_of(h, b, fs, r, st2)
      ): {
        RKnown.Run.go(
          g,
          fs,
          r,
          Ledgers.Line{h, Some{b}},
          Run.of(Ledgers.Line{h, Some{b}}, r, st2),
          _
        )
          == Run.of(
            Ledgers.Line{h, Some{b}},
            r,
            RLines.Line.run.in(
              g,
              fs,
              Some{r},
              Ledgers.Line{h, Some{b}},
              st2,
              RLines.Line.step.in(fs, Some{r}, Ledgers.Line{h, Some{b}}, st2)
            )
          ): RKnown.Run
      }
      Run.go_of(
        g,
        h,
        b,
        fs,
        r,
        st2,
        RLines.Line.step.in(fs, Some{r}, Ledgers.Line{h, Some{b}}, st2)
      )

# the run of a branch that holds what Run.of gives of a state leaves what
# Run.of gives of the state that the run from the versions leaves
def Run.from_of(
  +h: Hashes.Hash,
  +b: String,
  +fs: List<&2, Types.Fact>,
  +r: List<&2, Types.Entry>,
  +st: RLines.State
) -> {
  RKnown.Run.from(
    fs,
    r,
    Ledgers.Line{h, Some{b}},
    Run.of(Ledgers.Line{h, Some{b}}, r, st)
  )
    == Run.of(
      Ledgers.Line{h, Some{b}},
      r,
      RKnown.Known.go.in(fs, Ledgers.Line{h, Some{b}}, st, Some{r})
    ): RKnown.Run
}:
  %Equal.sym(
    Maybe<&2, RKnown.Run>,
    RKnown.Run.step(fs, r, Ledgers.Line{h, Some{b}}, Run.of(Ledgers.Line{h, Some{b}}, r, st)),
    Run.of.maybe(
      Ledgers.Line{h, Some{b}},
      r,
      RLines.Line.step.in(fs, Some{r}, Ledgers.Line{h, Some{b}}, st)
    ),
    Run.step_of(h, b, fs, r, st)
  ): {
    RKnown.Run.go(
      1n+RLines.Line.bound(fs, Ledgers.Line{h, Some{b}}),
      fs,
      r,
      Ledgers.Line{h, Some{b}},
      Run.of(Ledgers.Line{h, Some{b}}, r, st),
      _
    )
      == Run.of(
        Ledgers.Line{h, Some{b}},
        r,
        RKnown.Known.go.in(fs, Ledgers.Line{h, Some{b}}, st, Some{r})
      ): RKnown.Run
  }
  Run.go_of(
    1n+RLines.Line.bound(fs, Ledgers.Line{h, Some{b}}),
    h,
    b,
    fs,
    r,
    st,
    RLines.Line.step.in(fs, Some{r}, Ledgers.Line{h, Some{b}}, st)
  )

# The table after a ballot, with what the run keeps
# -------------------------------------------------

# what Run.of gives, with the rule read from the facts s
def Ran.make(+s: RFacts.Plain(), +c: Ledgers.Line, st: RLines.State) -> RKnown.Run:
  match st:
    case RLines.State{+vs, k}:
      RKnown.Run{
        RLines.State{vs, k},
        RLines.Line.era(c, vs),
        RLines.Rule.after(s, c, vs),
        RKnown.Ids.of(vs)
      }

# what a run leaves of the line c in the state m, if any, in the facts s
def Ran.of.at(
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  m: Maybe<&2, RLines.State>
) -> Maybe<&2, RKnown.Run>:
  match m:
    case None{}:
      None{}
    case Some{st}:
      Some{Ran.make(s, c, st)}

# the run q, if any, is what a run leaves of the line c in the facts s: the
# state of c, with the era and the rule of its next version and the ids of
# its versions
def Ran.Ok(+s: RFacts.Plain(), +c: Ledgers.Line, q: Maybe<&2, RKnown.Run>) -> Type:
  match q:
    case None{}:
      Unit
    case Some{run}:
      {Some{run} == Ran.of.at(s, c, RLines.Line.state(s, c)): Maybe<&2, RKnown.Run>}

# what Run.of gives of a branch, with the versions of its store in the facts
# s, is what Ran.make gives
def Ran.make_of(
  +s: RFacts.Plain(),
  +h: Hashes.Hash,
  +b: String,
  +r: List<&2, Types.Entry>,
  +j: Nat,
  st: RLines.State
) -> {
  RLines.Line.state(s, Ledgers.Line{h, None{}}) == Some{RLines.State{r, j}}: Maybe<&2, RLines.State>
} -> {
  Run.of(Ledgers.Line{h, Some{b}}, r, st) == Ran.make(s, Ledgers.Line{h, Some{b}}, st): RKnown.Run
}:
  match st:
    case RLines.State{+vs, +k}:
      e => Equal.cong(
        Maybe<&2, RLines.Rule>,
        RKnown.Run,
        u => RKnown.Run{
          RLines.State{vs, k},
          RLines.Line.era(Ledgers.Line{h, Some{b}}, vs),
          u,
          RKnown.Ids.of(vs)
        },
        RLines.Line.rule(Some{r}, Ledgers.Line{h, Some{b}}, vs),
        RLines.Rule.after(s, Ledgers.Line{h, Some{b}}, vs),
        Known.rule_at_ok(s, Ledgers.Line{h, Some{b}}, vs, r, j)(e)
      )

# a right table with what a run leaves of a line in the state of the line is
# right
def Known.ran_ok(
  +rest: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +vs: List<&2, Types.Entry>,
  +k: Nat
) -> {
  RLines.Line.state(s, c) == Some{RLines.State{vs, k}}: Maybe<&2, RLines.State>
} -> {
  RContents.Known.ok(rest, s) == True{}: Bool
} -> {
  RContents.Known.ok(
    RKnown.Known.rule.put(
      RKnown.Made{c, RKnown.Ids.of(vs)} <> RKnown.Kept{c, RLines.State{vs, k}} <> rest,
      c,
      RLines.Line.era(c, vs),
      RLines.Rule.after(s, c, vs)
    ),
    s
  )
    == True{}: Bool
}:
  +e1 => +ok => Lists.Maybe.by(
    RLines.Rule,
    y => {
      RContents.Known.ok(
        RKnown.Known.rule.put(
          RKnown.Made{c, RKnown.Ids.of(vs)} <> RKnown.Kept{c, RLines.State{vs, k}} <> rest,
          c,
          RLines.Line.era(c, vs),
          y
        ),
        s
      )
        == True{}: Bool
    },
    RLines.Rule.after(s, c, vs),
    en => Ok.cons(
      RKnown.Made{c, RKnown.Ids.of(vs)},
      RKnown.Kept{c, RLines.State{vs, k}} <> rest,
      s
    )(
      Made.fits_of(RLines.Line.state(s, c), vs, k)(e1)
    )(
      Ok.cons(
        RKnown.Kept{c, RLines.State{vs, k}},
        rest,
        s
      )(State.fits_of(RLines.Line.state(s, c), RLines.State{vs, k})(e1))(ok)
    ),
    +u => eu => Ok.cons(
      RKnown.Ruled{c, RLines.Line.era(c, vs), u},
      RKnown.Made{c, RKnown.Ids.of(vs)} <> RKnown.Kept{c, RLines.State{vs, k}} <> rest,
      s
    )(
      Shared.Bool.and_both(
        RKnown.Rule.fits(
          RKnown.Known.rule.next(RKnown.Known.none(), s, c, RLines.Line.state(s, c)),
          u
        ),
        RKnown.Era.fits(RLines.Line.state(s, c), c, RLines.Line.era(c, vs))
      )(
        Rule.fits_of(
          RKnown.Known.rule.next(RKnown.Known.none(), s, c, RLines.Line.state(s, c)),
          u
        )((
            %Equal.sym(Maybe<&2, RLines.State>, RLines.Line.state(s, c), Some{RLines.State{vs, k}}, e1): {RKnown.Known.rule.next(RKnown.Known.none(), s, c, _) == Some{u}: Maybe<&2, RLines.Rule>}
            eu))
      )((
          %Equal.sym(Maybe<&2, RLines.State>, RLines.Line.state(s, c), Some{RLines.State{vs, k}}, e1): {RKnown.Era.fits(_, c, RLines.Line.era(c, vs)) == True{}: Bool}
          Shared.Nat.is_eq_refl(RLines.Line.era(c, vs))))
    )(
      Ok.cons(
        RKnown.Made{c, RKnown.Ids.of(vs)},
        RKnown.Kept{c, RLines.State{vs, k}} <> rest,
        s
      )(
        Made.fits_of(RLines.Line.state(s, c), vs, k)(e1)
      )(
        Ok.cons(
          RKnown.Kept{c, RLines.State{vs, k}},
          rest,
          s
        )(State.fits_of(RLines.Line.state(s, c), RLines.State{vs, k})(e1))(ok)
      )
    )
  )

# Known.ran_ok, with the state m of the line
def Known.ran_ok.at(
  +rest: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +run: RKnown.Run,
  m: Maybe<&2, RLines.State>
) -> {
  RLines.Line.state(s, c) == m: Maybe<&2, RLines.State>
} -> {
  Some{run} == Ran.of.at(s, c, m): Maybe<&2, RKnown.Run>
} -> {
  RContents.Known.ok(rest, s) == True{}: Bool
} -> {RContents.Known.ok(RKnown.Known.ran(rest, c, run), s) == True{}: Bool}:
  match m:
    case None{}:
      e1 => e2 => ok => Empty.absurd(
        {RContents.Known.ok(RKnown.Known.ran(rest, c, run), s) == True{}: Bool},
        Shared.Maybe.none_ne_some(
          RKnown.Run,
          run,
          Equal.sym(Maybe<&2, RKnown.Run>, Some{run}, None{}, e2)
        )
      )
    case Some{RLines.State{+vs, +k}}:
      e1 => e2 => ok =>
        %Equal.sym(
          RKnown.Run,
          run,
          RKnown.Run{
            RLines.State{vs, k},
            RLines.Line.era(c, vs),
            RLines.Rule.after(s, c, vs),
            RKnown.Ids.of(vs)
          },
          Shared.Maybe.some_inj(
            RKnown.Run,
            run,
            RKnown.Run{
              RLines.State{vs, k},
              RLines.Line.era(c, vs),
              RLines.Rule.after(s, c, vs),
              RKnown.Ids.of(vs)
            },
            e2
          )
        ): {RContents.Known.ok(RKnown.Known.ran(rest, c, _), s) == True{}: Bool}
        Known.ran_ok(rest, s, c, vs, k)(e1)(ok)

# the state of a branch after a ballot for its next slot is the state that
# the run from its known state leaves, read from the facts that the table
# holds for a work, with the ballot
def Quick.state(
  +kn: RKnown.Known(),
  +name: String,
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +b: String,
  +k: Nat,
  +t: Nat,
  +x: Types.Cast,
  +fs: List<&2, Types.Fact>,
  +vs: List<&2, Types.Entry>,
  +k0: Nat,
  +r: List<&2, Types.Entry>,
  +j: Nat
) -> {
  RKnown.Known.walk(
    kn,
    Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}
  )
    == Some{fs}: Maybe<&2, List<&2, Types.Fact>>
} -> {
  RLines.Line.state(
    Facts.Facts.crit(s),
    Ledgers.Line{h, Some{b}}
  )
    == Some{RLines.State{vs, k0}}: Maybe<&2, RLines.State>
} -> {
  RLines.Line.state(
    Facts.Facts.crit(s),
    Ledgers.Line{h, None{}}
  )
    == Some{RLines.State{r, j}}: Maybe<&2, RLines.State>
} -> {
  RContents.Known.fit(kn, Facts.Facts.crit(s)) == True{}: Bool
} -> {
  Nat.is_eq(k0, k) == True{}: Bool
} -> {
  RLines.Line.state(
    Facts.Facts.crit(
      Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x})
    ),
    Ledgers.Line{h, Some{b}}
  )
    == Some{
      RKnown.Known.go.in(fs, Ledgers.Line{h, Some{b}}, RLines.State{vs, k0}, Some{r})
    }: Maybe<&2, RLines.State>
}:
  hw => +e1 => e2 => fit => et =>
    %et: Put.Ok(
      RLines.Line.state(
        Facts.Facts.crit(
          Facts.Facts.add(
            s,
            Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}
          )
        ),
        Ledgers.Line{h, Some{b}}
      ),
      Shared.Maybe.when(
        RLines.State,
        _,
        u => Some{RKnown.Known.go.in(fs, Ledgers.Line{h, Some{b}}, RLines.State{vs, k0}, Some{r})}
      )
    )
    %hw: Put.Ok(
      RLines.Line.state(
        Facts.Facts.crit(
          Facts.Facts.add(
            s,
            Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}
          )
        ),
        Ledgers.Line{h, Some{b}}
      ),
      RKnown.Known.next.of(
        _,
        Facts.Facts.crit(
          Facts.Facts.add(
            s,
            Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}
          )
        ),
        Ledgers.Line{h, Some{b}},
        k,
        Some{RLines.State{vs, k0}},
        Some{Some{r}}
      )
    )
    %Equal.sym(
      Maybe<&2, RLines.State>,
      RKnown.Known.next.of(
        RKnown.Known.walk(
          kn,
          Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}
        ),
        Facts.Facts.crit(
          Facts.Facts.add(
            s,
            Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}
          )
        ),
        Ledgers.Line{h, Some{b}},
        k,
        Some{RLines.State{vs, k0}},
        Some{Some{r}}
      ),
      RKnown.Known.next.of(
        None{},
        Facts.Facts.crit(
          Facts.Facts.add(
            s,
            Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}
          )
        ),
        Ledgers.Line{h, Some{b}},
        k,
        Some{RLines.State{vs, k0}},
        Some{Some{r}}
      ),
      Next.walk(
        kn,
        name,
        s,
        Ledgers.Line{h, Some{b}},
        k,
        t,
        x,
        Some{RLines.State{vs, k0}},
        Some{Some{r}}
      )(Inr{e1})(fit)
    ): Put.Ok(
      RLines.Line.state(
        Facts.Facts.crit(
          Facts.Facts.add(
            s,
            Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}
          )
        ),
        Ledgers.Line{h, Some{b}}
      ),
      _
    )
    Known.next_ok(
      name,
      s,
      Ledgers.Line{h, Some{b}},
      k,
      t,
      x,
      Some{RLines.State{vs, k0}},
      Some{RLines.State{r, j}}
    )(Inr{e1})(Inr{e2})

# Known.quick_ok, when the table holds all that the run reads
def Known.quick_ok.all(
  +kn: RKnown.Known(),
  +name: String,
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +b: String,
  +k: Nat,
  +t: Nat,
  +x: Types.Cast,
  +fs: List<&2, Types.Fact>,
  +vs: List<&2, Types.Entry>,
  +k0: Nat,
  +r: List<&2, Types.Entry>,
  +j: Nat,
  +era: Nat,
  +rule: RLines.Rule,
  +ids: RKnown.Ids
) -> {
  RKnown.Known.walk(
    kn,
    Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}
  )
    == Some{fs}: Maybe<&2, List<&2, Types.Fact>>
} -> {
  RKnown.Known.find(
    kn,
    Ledgers.Line{h, Some{b}}
  )
    == Some{RLines.State{vs, k0}}: Maybe<&2, RLines.State>
} -> {
  RKnown.Known.find(
    kn,
    Ledgers.Line{h, None{}}
  )
    == Some{RLines.State{r, j}}: Maybe<&2, RLines.State>
} -> {
  RKnown.Known.era(kn, Ledgers.Line{h, Some{b}}) == Some{era}: Maybe<&2, Nat>
} -> {
  RKnown.Known.ruled(kn, Ledgers.Line{h, Some{b}}) == Some{rule}: Maybe<&2, RLines.Rule>
} -> {
  RKnown.Known.ids(kn, Ledgers.Line{h, Some{b}}) == Some{ids}: Maybe<&2, RKnown.Ids>
} -> {
  RContents.Known.fit(kn, Facts.Facts.crit(s)) == True{}: Bool
} -> {
  Nat.is_eq(k0, k) == True{}: Bool
} -> {
  Some{
    RKnown.Run.from(
      fs,
      r,
      Ledgers.Line{h, Some{b}},
      RKnown.Run{RLines.State{vs, k0}, era, Some{rule}, ids}
    )
  }
    == Ran.of.at(
      Facts.Facts.crit(
        Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x})
      ),
      Ledgers.Line{h, Some{b}},
      RLines.Line.state(
        Facts.Facts.crit(
          Facts.Facts.add(
            s,
            Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}
          )
        ),
        Ledgers.Line{h, Some{b}}
      )
    ): Maybe<&2, RKnown.Run>
}:
  hw => +hm => +hms => hn => hu => hx => +fit => et =>
    +ok = Fit.ok(kn, Facts.Facts.crit(s))(fit)
    +e1 = Known.find_ok(
      kn,
      Facts.Facts.crit(s),
      Ledgers.Line{h, Some{b}},
      RLines.State{vs, k0}
    )(ok)(hm)
    +e2 = Known.find_ok(
      kn,
      Facts.Facts.crit(s),
      Ledgers.Line{h, None{}},
      RLines.State{r, j}
    )(ok)(hms)
    +g = RKnown.Known.go.in(fs, Ledgers.Line{h, Some{b}}, RLines.State{vs, k0}, Some{r})
    %Equal.sym(
      Maybe<&2, RLines.State>,
      RLines.Line.state(
        Facts.Facts.crit(
          Facts.Facts.add(
            s,
            Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}
          )
        ),
        Ledgers.Line{h, Some{b}}
      ),
      Some{g},
      Quick.state(kn, name, s, h, b, k, t, x, fs, vs, k0, r, j)(hw)(e1)(e2)(fit)(et)
    ): {
      Some{
        RKnown.Run.from(
          fs,
          r,
          Ledgers.Line{h, Some{b}},
          RKnown.Run{RLines.State{vs, k0}, era, Some{rule}, ids}
        )
      }
        == Ran.of.at(
          Facts.Facts.crit(
            Facts.Facts.add(
              s,
              Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}
            )
          ),
          Ledgers.Line{h, Some{b}},
          _
        ): Maybe<&2, RKnown.Run>
    }
    %Ran.make_of(
      Facts.Facts.crit(
        Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x})
      ),
      h,
      b,
      r,
      j,
      g
    )(
      Equal.trans(
        Maybe<&2, RLines.State>,
        RLines.Line.state(
          Facts.Facts.crit(
            Facts.Facts.add(
              s,
              Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}
            )
          ),
          Ledgers.Line{h, None{}}
        ),
        RLines.Line.state(Facts.Facts.crit(s), Ledgers.Line{h, None{}}),
        Some{RLines.State{r, j}},
        Line.state_voted(
          name,
          s,
          Ledgers.Line{h, Some{b}},
          k,
          t,
          x,
          Ledgers.Line{h, None{}}
        )(Branch.hit_other(h, b, Ledgers.Line{h, None{}})(Root.ne(h, h, b))),
        e2
      )
    ): {
      Some{
        RKnown.Run.from(
          fs,
          r,
          Ledgers.Line{h, Some{b}},
          RKnown.Run{RLines.State{vs, k0}, era, Some{rule}, ids}
        )
      }
        == Some{_}: Maybe<&2, RKnown.Run>
    }
    %Run.from_of(
      h,
      b,
      fs,
      r,
      RLines.State{vs, k0}
    ): {
      Some{
        RKnown.Run.from(
          fs,
          r,
          Ledgers.Line{h, Some{b}},
          RKnown.Run{RLines.State{vs, k0}, era, Some{rule}, ids}
        )
      }
        == Some{_}: Maybe<&2, RKnown.Run>
    }
    %Equal.sym(
      Nat,
      era,
      RLines.Line.era(Ledgers.Line{h, Some{b}}, vs),
      Shared.Nat.is_eq_sound(era, RLines.Line.era(Ledgers.Line{h, Some{b}}, vs))((
          %e1: {RKnown.Era.fits(_, Ledgers.Line{h, Some{b}}, era) == True{}: Bool}
          Known.era_ok(kn, Facts.Facts.crit(s), Ledgers.Line{h, Some{b}}, era)(ok)(hn)))
    ): {
      Some{
        RKnown.Run.from(
          fs,
          r,
          Ledgers.Line{h, Some{b}},
          RKnown.Run{RLines.State{vs, k0}, _, Some{rule}, ids}
        )
      }
        == Some{
          RKnown.Run.from(
            fs,
            r,
            Ledgers.Line{h, Some{b}},
            Run.of(Ledgers.Line{h, Some{b}}, r, RLines.State{vs, k0})
          )
        }: Maybe<&2, RKnown.Run>
    }
    %Equal.trans(
      Maybe<&2, RLines.Rule>,
      RLines.Line.rule(Some{r}, Ledgers.Line{h, Some{b}}, vs),
      RLines.Rule.after(Facts.Facts.crit(s), Ledgers.Line{h, Some{b}}, vs),
      Some{rule},
      Known.rule_at_ok(Facts.Facts.crit(s), Ledgers.Line{h, Some{b}}, vs, r, j)(e2),
      (
        %e1: {RKnown.Known.rule.next(RKnown.Known.none(), Facts.Facts.crit(s), Ledgers.Line{h, Some{b}}, _) == Some{rule}: Maybe<&2, RLines.Rule>}
        Known.ruled_ok(kn, Facts.Facts.crit(s), Ledgers.Line{h, Some{b}}, rule)(ok)(hu))
    ): {
      Some{
        RKnown.Run.from(
          fs,
          r,
          Ledgers.Line{h, Some{b}},
          RKnown.Run{RLines.State{vs, k0}, RLines.Line.era(Ledgers.Line{h, Some{b}}, vs), _, ids}
        )
      }
        == Some{
          RKnown.Run.from(
            fs,
            r,
            Ledgers.Line{h, Some{b}},
            Run.of(Ledgers.Line{h, Some{b}}, r, RLines.State{vs, k0})
          )
        }: Maybe<&2, RKnown.Run>
    }
    %Equal.sym(
      RKnown.Ids,
      ids,
      RKnown.Ids.of(vs),
      Made.fits_sound(
        RLines.Line.state(Facts.Facts.crit(s), Ledgers.Line{h, Some{b}}),
        ids,
        vs,
        k0
      )(e1)(Known.ids_ok(kn, Facts.Facts.crit(s), Ledgers.Line{h, Some{b}}, ids)(ok)(hx))
    ): {
      Some{
        RKnown.Run.from(
          fs,
          r,
          Ledgers.Line{h, Some{b}},
          RKnown.Run{
            RLines.State{vs, k0},
            RLines.Line.era(Ledgers.Line{h, Some{b}}, vs),
            RLines.Line.rule(Some{r}, Ledgers.Line{h, Some{b}}, vs),
            _
          }
        )
      }
        == Some{
          RKnown.Run.from(
            fs,
            r,
            Ledgers.Line{h, Some{b}},
            Run.of(Ledgers.Line{h, Some{b}}, r, RLines.State{vs, k0})
          )
        }: Maybe<&2, RKnown.Run>
    }
    {==}

# Known.quick_ok, with what the table holds
def Known.quick_ok.at(
  +kn: RKnown.Known(),
  +name: String,
  +s: Facts.Facts(),
  w: Maybe<&2, List<&2, Types.Fact>>,
  c: Ledgers.Line,
  +k: Nat,
  +t: Nat,
  +x: Types.Cast,
  m: Maybe<&2, RLines.State>,
  ms: Maybe<&2, RLines.State>,
  n: Maybe<&2, Nat>,
  u: Maybe<&2, RLines.Rule>,
  y: Maybe<&2, RKnown.Ids>
) -> {
  RKnown.Known.walk(
    kn,
    Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}
  )
    == w: Maybe<&2, List<&2, Types.Fact>>
} -> {
  RKnown.Known.find(kn, c) == m: Maybe<&2, RLines.State>
} -> {
  RKnown.Known.find(kn, RKnown.Known.root(c)) == ms: Maybe<&2, RLines.State>
} -> {
  RKnown.Known.era(kn, c) == n: Maybe<&2, Nat>
} -> {
  RKnown.Known.ruled(kn, c) == u: Maybe<&2, RLines.Rule>
} -> {
  RKnown.Known.ids(kn, c) == y: Maybe<&2, RKnown.Ids>
} -> {
  RContents.Known.fit(kn, Facts.Facts.crit(s)) == True{}: Bool
} -> Ran.Ok(
  Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})),
  c,
  RKnown.Known.quick.of(w, c, k, m, ms, n, u, y)
):
  match w c m ms n u y:
    case None{} c1 m1 ms1 n1 u1 y1:
      hw => hm => hms => hn => hu => hx => fit => Unit{}
    case Some{fs} Ledgers.Line{h, None{}} m1 ms1 n1 u1 y1:
      hw => hm => hms => hn => hu => hx => fit => Unit{}
    case Some{fs} Ledgers.Line{h, Some{b}} None{} ms1 n1 u1 y1:
      hw => hm => hms => hn => hu => hx => fit => Unit{}
    case Some{fs} Ledgers.Line{h, Some{b}} Some{st} None{} n1 u1 y1:
      hw => hm => hms => hn => hu => hx => fit => Unit{}
    case Some{fs} Ledgers.Line{h, Some{b}} Some{st} Some{RLines.State{r, j}} None{} u1 y1:
      hw => hm => hms => hn => hu => hx => fit => Unit{}
    case Some{fs} Ledgers.Line{h, Some{b}} Some{st} Some{RLines.State{r, j}} Some{era} None{} y1:
      hw => hm => hms => hn => hu => hx => fit => Unit{}
    case Some{
      fs
    } Ledgers.Line{h, Some{b}} Some{st} Some{RLines.State{r, j}} Some{era} Some{rule} None{}:
      hw => hm => hms => hn => hu => hx => fit => Unit{}
    case Some{
      +fs
    } Ledgers.Line{
      +h,
      Some{+b}
    } Some{RLines.State{+vs, +k0}} Some{RLines.State{+r, +j}} Some{+era} Some{+rule} Some{+ids}:
      hw => hm => hms => hn => hu => hx => fit => Lists.Bool.by(
        d => {
          Nat.is_eq(k0, k) == d: Bool
        } -> Ran.Ok(
          Facts.Facts.crit(
            Facts.Facts.add(
              s,
              Types.Fact.Vote{name, Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}, x}
            )
          ),
          Ledgers.Line{h, Some{b}},
          Shared.Maybe.when(
            RKnown.Run,
            d,
            z => Some{
              RKnown.Run.from(
                fs,
                r,
                Ledgers.Line{h, Some{b}},
                RKnown.Run{RLines.State{vs, k0}, era, Some{rule}, ids}
              )
            }
          )
        ),
        Nat.is_eq(k0, k),
        et => e => Known.quick_ok.all(
          kn,
          name,
          s,
          h,
          b,
          k,
          t,
          x,
          fs,
          vs,
          k0,
          r,
          j,
          era,
          rule,
          ids
        )(hw)(hm)(hms)(hn)(hu)(hx)(fit)(et),
        ef => e => Unit{}
      )({==})

# the run that a ballot continues, when the table holds all that it reads,
# leaves the state of the line after the ballot, with the era and the rule
# of its next version and the ids of its versions
def Known.quick_ok(
  +kn: RKnown.Known(),
  +name: String,
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +t: Nat,
  +x: Types.Cast
) -> {
  RContents.Known.fit(kn, Facts.Facts.crit(s)) == True{}: Bool
} -> Ran.Ok(
  Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})),
  c,
  RKnown.Known.quick(
    kn,
    c,
    k,
    RKnown.Known.walk(kn, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})
  )
):
  fit => Known.quick_ok.at(
    kn,
    name,
    s,
    RKnown.Known.walk(kn, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}),
    c,
    k,
    t,
    x,
    RKnown.Known.find(kn, c),
    RKnown.Known.find(kn, RKnown.Known.root(c)),
    RKnown.Known.era(kn, c),
    RKnown.Known.ruled(kn, c),
    RKnown.Known.ids(kn, c)
  )({==})({==})({==})({==})({==})({==})(fit)

# Known.cast_fits, with the run q that the ballot continues
def Known.cast_fits.at(
  q: Maybe<&2, RKnown.Run>,
  +kn: RKnown.Known(),
  +name: String,
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +t: Nat,
  +x: Types.Cast
) -> {
  RContents.Known.fit(kn, Facts.Facts.crit(s)) == True{}: Bool
} -> {
  Facts.Facts.has(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}) == False{}: Bool
} -> Ran.Ok(
  Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})),
  c,
  q
) -> {
  RContents.Known.ok(
    RKnown.Known.cast.as(
      q,
      kn,
      Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})),
      c,
      k,
      RKnown.Known.walk(kn, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})
    ),
    Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))
  )
    == True{}: Bool
}:
  match q:
    case None{}:
      +fit => hf => p =>
        %Equal.sym(
          RKnown.Known(),
          RKnown.Known.cast.plain(
            kn,
            Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})),
            c,
            k,
            RKnown.Known.walk(kn, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})
          ),
          RKnown.Known.cast.plain(
            kn,
            Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})),
            c,
            k,
            None{}
          ),
          Known.cast_walk(kn, name, s, c, k, t, x)(fit)
        ): {
          RContents.Known.ok(
            _,
            Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))
          )
            == True{}: Bool
        }
        Known.cast_ok(kn, name, s, c, k, t, x)(Fit.ok(kn, Facts.Facts.crit(s))(fit))(hf)
    case Some{+run}:
      +fit => hf => p => Known.ran_ok.at(
        List.append(
          &2,
          RKnown.Kept,
          RKnown.Known.voted(kn, c),
          RKnown.Known.spared(
            RKnown.Known.safe(
              c,
              RKnown.Known.find(kn, c),
              RKnown.Known.find(kn, RKnown.Known.root(c)),
              k
            ),
            kn
          )
        ),
        Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})),
        c,
        run,
        RLines.Line.state(
          Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})),
          c
        )
      )(
        {==}
      )(
        p
      )(
        Ok.append(
          RKnown.Known.voted(kn, c),
          RKnown.Known.spared(
            RKnown.Known.safe(
              c,
              RKnown.Known.find(kn, c),
              RKnown.Known.find(kn, RKnown.Known.root(c)),
              k
            ),
            kn
          ),
          Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))
        )(
          Known.voted_ok(kn, name, s, c, k, t, x)(Fit.ok(kn, Facts.Facts.crit(s))(fit))
        )(Known.spared_ok(kn, name, s, c, k, t, x)(Fit.ok(kn, Facts.Facts.crit(s))(fit))(hf))
      )

# the table that a ballot for the slot k of the line c leaves of a table
# that fits, with what its run keeps, is right for the facts with the ballot
def Known.cast_fits(
  +kn: RKnown.Known(),
  +name: String,
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +t: Nat,
  +x: Types.Cast
) -> {
  RContents.Known.fit(kn, Facts.Facts.crit(s)) == True{}: Bool
} -> {
  Facts.Facts.has(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}) == False{}: Bool
} -> {
  RContents.Known.ok(
    RKnown.Known.cast(
      kn,
      Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})),
      c,
      k,
      RKnown.Known.walk(kn, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})
    ),
    Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))
  )
    == True{}: Bool
}:
  +fit => hf => Known.cast_fits.at(
    RKnown.Known.quick(
      kn,
      c,
      k,
      RKnown.Known.walk(kn, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})
    ),
    kn,
    name,
    s,
    c,
    k,
    t,
    x
  )(fit)(hf)(Known.quick_ok(kn, name, s, c, k, t, x)(fit))

# Known.cast_shuts, with the run q that the ballot continues
def Known.cast_shuts.at(
  q: Maybe<&2, RKnown.Run>,
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +k: Nat,
  +w: Maybe<&2, List<&2, Types.Fact>>
) -> {
  RKnown.Known.shelf(RKnown.Known.cast.as(q, kn, s, c, k, w)) == None{}: Maybe<&2, RKnown.Kept>
}:
  match q:
    case None{}:
      Known.cast_shut(kn, s, c, k, w)
    case Some{RKnown.Run{st, m, None{}, y}}:
      %Known.voted_append(
        kn,
        c,
        RKnown.Known.spared(
          RKnown.Known.safe(
            c,
            RKnown.Known.find(kn, c),
            RKnown.Known.find(kn, RKnown.Known.root(c)),
            k
          ),
          kn
        )
      ): {_ == None{}: Maybe<&2, RKnown.Kept>}
      Known.spared_shut(
        RKnown.Known.safe(
          c,
          RKnown.Known.find(kn, c),
          RKnown.Known.find(kn, RKnown.Known.root(c)),
          k
        ),
        kn
      )
    case Some{RKnown.Run{st, m, Some{u}, y}}:
      %Known.voted_append(
        kn,
        c,
        RKnown.Known.spared(
          RKnown.Known.safe(
            c,
            RKnown.Known.find(kn, c),
            RKnown.Known.find(kn, RKnown.Known.root(c)),
            k
          ),
          kn
        )
      ): {_ == None{}: Maybe<&2, RKnown.Kept>}
      Known.spared_shut(
        RKnown.Known.safe(
          c,
          RKnown.Known.find(kn, c),
          RKnown.Known.find(kn, RKnown.Known.root(c)),
          k
        ),
        kn
      )

# the table after a ballot, with what its run keeps, holds no facts for a
# work
def Known.cast_shuts(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +k: Nat,
  +w: Maybe<&2, List<&2, Types.Fact>>
) -> {RKnown.Known.shelf(RKnown.Known.cast(kn, s, c, k, w)) == None{}: Maybe<&2, RKnown.Kept>}:
  Known.cast_shuts.at(RKnown.Known.quick(kn, c, k, w), kn, s, c, k, w)
