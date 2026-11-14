import Base
import ../shared/shared/ledger.bend as Ledgers
import ../shared/shared/shared/shared/crit.bend as Crits
import ../shared/shared/shared/shared/hash.bend as Hashes
import ../shared/shared/shared/shared/shared.bend as Shared
import ../shared/shared/shared/text.bend as Texts
import ./codes.bend as Coded
import ./content.bend as Contents
import ./facts.bend as Facts
import ./groups.bend as Groups
import ./lines.bend as Lines
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
import ./spec.bend as Spec
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

# Bucket.same is True for ids and themselves
def Bucket.same_refl(a: List<&2, Ledgers.Id>) -> {RKnown.Bucket.same(a, a) == True{}: Bool}:
  Shared.List.is_eq_refl(~Ledgers.Id, ~Ledgers.Id.is_eq, ~Id.laws(), a)

# Bucket.same is True only for equal ids
def Bucket.same_sound(
  a: List<&2, Ledgers.Id>,
  b: List<&2, Ledgers.Id>
) -> {RKnown.Bucket.same(a, b) == True{}: Bool} -> {a == b: List<&2, Ledgers.Id>}:
  Shared.List.is_eq_sound(~Ledgers.Id, ~Ledgers.Id.is_eq, ~Id.laws(), a, b)

# ids, if any, are the same as themselves
def Tip.same_refl(
  e: Maybe<&2, List<&2, Ledgers.Id>>
) -> {Shared.Maybe.is_eq(~List<&2, Ledgers.Id>, ~RKnown.Bucket.same, e, e) == True{}: Bool}:
  match e:
    case None{}:
      {==}
    case Some{v}:
      Bucket.same_refl(v)

# Ids.same is True for a set and itself
def Ids.same_refl(a: Crits.Crit<List<&2, Ledgers.Id>>) -> {RKnown.Ids.same(a, a) == True{}: Bool}:
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
            Shared.Maybe.is_eq(~List<&2, Ledgers.Id>, ~RKnown.Bucket.same, e, e),
            Bool.and(RKnown.Ids.same(z, z), RKnown.Ids.same(o, o))
          )
        )
      )(
        Crits.Key.is_eq_refl(r)
      )(
        Shared.Bool.and_both(
          Nat.is_eq(p, p),
          Bool.and(
            Shared.Maybe.is_eq(~List<&2, Ledgers.Id>, ~RKnown.Bucket.same, e, e),
            Bool.and(RKnown.Ids.same(z, z), RKnown.Ids.same(o, o))
          )
        )(
          Shared.Nat.is_eq_refl(p)
        )(
          Shared.Bool.and_both(
            Shared.Maybe.is_eq(~List<&2, Ledgers.Id>, ~RKnown.Bucket.same, e, e),
            Bool.and(RKnown.Ids.same(z, z), RKnown.Ids.same(o, o))
          )(
            Tip.same_refl(e)
          )(
            Shared.Bool.and_both(
              RKnown.Ids.same(z, z),
              RKnown.Ids.same(o, o)
            )(Ids.same_refl(z))(Ids.same_refl(o))
          )
        )
      )

# Ids.same is True only for equal sets
def Ids.same_sound(
  a: Crits.Crit<List<&2, Ledgers.Id>>,
  b: Crits.Crit<List<&2, Ledgers.Id>>
) -> {RKnown.Ids.same(a, b) == True{}: Bool} -> {a == b: Crits.Crit<List<&2, Ledgers.Id>>}:
  match a b:
    case Crits.Crit.Tip{} Crits.Crit.Tip{}:
      h => {==}
    case Crits.Crit.Tip{} Crits.Crit.Leaf{k2, v2}:
      h => Empty.absurd(
        {Crits.Crit.Tip{} == Crits.Crit.Leaf{k2, v2}: Crits.Crit<List<&2, Ledgers.Id>>},
        Shared.Bool.false_ne_true(h)
      )
    case Crits.Crit.Tip{} Crits.Crit.Fork{r2, p2, e2, z2, o2}:
      h => Empty.absurd(
        {Crits.Crit.Tip{} == Crits.Crit.Fork{r2, p2, e2, z2, o2}: Crits.Crit<List<&2, Ledgers.Id>>},
        Shared.Bool.false_ne_true(h)
      )
    case Crits.Crit.Leaf{k1, v1} Crits.Crit.Tip{}:
      h => Empty.absurd(
        {Crits.Crit.Leaf{k1, v1} == Crits.Crit.Tip{}: Crits.Crit<List<&2, Ledgers.Id>>},
        Shared.Bool.false_ne_true(h)
      )
    case Crits.Crit.Leaf{k1, v1} Crits.Crit.Fork{r2, p2, e2, z2, o2}:
      h => Empty.absurd(
        {
          Crits.Crit.Leaf{
            k1,
            v1
          }
            == Crits.Crit.Fork{r2, p2, e2, z2, o2}: Crits.Crit<List<&2, Ledgers.Id>>
        },
        Shared.Bool.false_ne_true(h)
      )
    case Crits.Crit.Fork{r1, p1, e1, z1, o1} Crits.Crit.Tip{}:
      h => Empty.absurd(
        {Crits.Crit.Fork{r1, p1, e1, z1, o1} == Crits.Crit.Tip{}: Crits.Crit<List<&2, Ledgers.Id>>},
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
            == Crits.Crit.Leaf{k2, v2}: Crits.Crit<List<&2, Ledgers.Id>>
        },
        Shared.Bool.false_ne_true(h)
      )
    case Crits.Crit.Leaf{+k1, +v1} Crits.Crit.Leaf{+k2, +v2}:
      +h => (
        %Crits.Key.is_eq_sound(k1, k2)(Shared.Bool.and_true_left(Crits.Key.is_eq(k1, k2), RKnown.Bucket.same(v1, v2))(h)): {Crits.Crit.Leaf{k1, v1} == Crits.Crit.Leaf{_, v2}: Crits.Crit<List<&2, Ledgers.Id>>}
        %Bucket.same_sound(v1, v2)(Shared.Bool.and_true_right(Crits.Key.is_eq(k1, k2), RKnown.Bucket.same(v1, v2))(h)): {Crits.Crit.Leaf{k1, v1} == Crits.Crit.Leaf{k1, _}: Crits.Crit<List<&2, Ledgers.Id>>}
        {==})
    case Crits.Crit.Fork{+r1, +p1, +e1, +z1, +o1} Crits.Crit.Fork{+r2, +p2, +e2, +z2, +o2}:
      +h => (
        %Crits.Key.is_eq_sound(r1, r2)(Shared.Bool.and_true_left(Crits.Key.is_eq(r1, r2), Bool.and(Nat.is_eq(p1, p2), Bool.and(Shared.Maybe.is_eq(~List<&2, Ledgers.Id>, ~RKnown.Bucket.same, e1, e2), Bool.and(RKnown.Ids.same(z1, z2), RKnown.Ids.same(o1, o2)))))(h)): {Crits.Crit.Fork{r1, p1, e1, z1, o1} == Crits.Crit.Fork{_, p2, e2, z2, o2}: Crits.Crit<List<&2, Ledgers.Id>>}
        %Shared.Nat.is_eq_sound(p1, p2)(Shared.Bool.and_true_left(Nat.is_eq(p1, p2), Bool.and(Shared.Maybe.is_eq(~List<&2, Ledgers.Id>, ~RKnown.Bucket.same, e1, e2), Bool.and(RKnown.Ids.same(z1, z2), RKnown.Ids.same(o1, o2))))(Shared.Bool.and_true_right(Crits.Key.is_eq(r1, r2), Bool.and(Nat.is_eq(p1, p2), Bool.and(Shared.Maybe.is_eq(~List<&2, Ledgers.Id>, ~RKnown.Bucket.same, e1, e2), Bool.and(RKnown.Ids.same(z1, z2), RKnown.Ids.same(o1, o2)))))(h))): {Crits.Crit.Fork{r1, p1, e1, z1, o1} == Crits.Crit.Fork{r1, _, e2, z2, o2}: Crits.Crit<List<&2, Ledgers.Id>>}
        %Shared.Maybe.is_eq_sound(~List<&2, Ledgers.Id>, ~RKnown.Bucket.same, x => y => Bucket.same_sound(x, y), e1, e2)(Shared.Bool.and_true_left(Shared.Maybe.is_eq(~List<&2, Ledgers.Id>, ~RKnown.Bucket.same, e1, e2), Bool.and(RKnown.Ids.same(z1, z2), RKnown.Ids.same(o1, o2)))(Shared.Bool.and_true_right(Nat.is_eq(p1, p2), Bool.and(Shared.Maybe.is_eq(~List<&2, Ledgers.Id>, ~RKnown.Bucket.same, e1, e2), Bool.and(RKnown.Ids.same(z1, z2), RKnown.Ids.same(o1, o2))))(Shared.Bool.and_true_right(Crits.Key.is_eq(r1, r2), Bool.and(Nat.is_eq(p1, p2), Bool.and(Shared.Maybe.is_eq(~List<&2, Ledgers.Id>, ~RKnown.Bucket.same, e1, e2), Bool.and(RKnown.Ids.same(z1, z2), RKnown.Ids.same(o1, o2)))))(h)))): {Crits.Crit.Fork{r1, p1, e1, z1, o1} == Crits.Crit.Fork{r1, p1, _, z2, o2}: Crits.Crit<List<&2, Ledgers.Id>>}
        %Ids.same_sound(z1, z2)(Shared.Bool.and_true_left(RKnown.Ids.same(z1, z2), RKnown.Ids.same(o1, o2))(Shared.Bool.and_true_right(Shared.Maybe.is_eq(~List<&2, Ledgers.Id>, ~RKnown.Bucket.same, e1, e2), Bool.and(RKnown.Ids.same(z1, z2), RKnown.Ids.same(o1, o2)))(Shared.Bool.and_true_right(Nat.is_eq(p1, p2), Bool.and(Shared.Maybe.is_eq(~List<&2, Ledgers.Id>, ~RKnown.Bucket.same, e1, e2), Bool.and(RKnown.Ids.same(z1, z2), RKnown.Ids.same(o1, o2))))(Shared.Bool.and_true_right(Crits.Key.is_eq(r1, r2), Bool.and(Nat.is_eq(p1, p2), Bool.and(Shared.Maybe.is_eq(~List<&2, Ledgers.Id>, ~RKnown.Bucket.same, e1, e2), Bool.and(RKnown.Ids.same(z1, z2), RKnown.Ids.same(o1, o2)))))(h))))): {Crits.Crit.Fork{r1, p1, e1, z1, o1} == Crits.Crit.Fork{r1, p1, e1, _, o2}: Crits.Crit<List<&2, Ledgers.Id>>}
        %Ids.same_sound(o1, o2)(Shared.Bool.and_true_right(RKnown.Ids.same(z1, z2), RKnown.Ids.same(o1, o2))(Shared.Bool.and_true_right(Shared.Maybe.is_eq(~List<&2, Ledgers.Id>, ~RKnown.Bucket.same, e1, e2), Bool.and(RKnown.Ids.same(z1, z2), RKnown.Ids.same(o1, o2)))(Shared.Bool.and_true_right(Nat.is_eq(p1, p2), Bool.and(Shared.Maybe.is_eq(~List<&2, Ledgers.Id>, ~RKnown.Bucket.same, e1, e2), Bool.and(RKnown.Ids.same(z1, z2), RKnown.Ids.same(o1, o2))))(Shared.Bool.and_true_right(Crits.Key.is_eq(r1, r2), Bool.and(Nat.is_eq(p1, p2), Bool.and(Shared.Maybe.is_eq(~List<&2, Ledgers.Id>, ~RKnown.Bucket.same, e1, e2), Bool.and(RKnown.Ids.same(z1, z2), RKnown.Ids.same(o1, o2)))))(h))))): {Crits.Crit.Fork{r1, p1, e1, z1, o1} == Crits.Crit.Fork{r1, p1, e1, z1, _}: Crits.Crit<List<&2, Ledgers.Id>>}
        {==})

# the ids that fit a state are the ids of its versions
def Made.fits_sound(
  -m: Maybe<&2, RLines.State>,
  +x: RKnown.Ids(),
  +vs: List<&2, Types.Entry>,
  -k: Nat
) -> {
  m == Some{RLines.State{vs, k}}: Maybe<&2, RLines.State>
} -> {RKnown.Made.fits(m, x) == True{}: Bool} -> {x == RKnown.Ids.of(vs): RKnown.Ids()}:
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

# the ids m, if any, with the id e before them, hold an id exactly when it
# is e or m holds it
def Bucket.has_put(
  m: Maybe<&2, List<&2, Ledgers.Id>>,
  +e: Ledgers.Id,
  +i: Ledgers.Id
) -> {
  RKnown.Ids.has.of(
    Some{Crits.Crit.merge(~List<&2, Ledgers.Id>, ~RKnown.Ids.join, m, [e])},
    i
  )
    == Bool.or(Ledgers.Id.is_eq(e, i), RKnown.Ids.has.of(m, i)): Bool
}:
  match m:
    case None{}:
      Lists.Bool.by(
        b => {List.any.if(u => False{}, b) == Bool.or(b, False{}): Bool},
        Ledgers.Id.is_eq(e, i),
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
        Ledgers.Id.is_eq(e, i),
        et => {==},
        ef => {==}
      )

# what a set with one more id holds under a key: under the key of the id,
# the id before the ids that the set held there
def Ids.get_put(
  +acc: RKnown.Ids(),
  +e: Ledgers.Id,
  +k: List<&2, U32>
) -> {
  Crits.Crit.wf(~List<&2, Ledgers.Id>, acc, 0n) == True{}: Bool
} -> {
  Crits.Crit.get(
    List<&2, Ledgers.Id>,
    RKnown.Ids.put(acc, e),
    k
  )
    == Bool.pick(
      Maybe<&2, List<&2, Ledgers.Id>>,
      Crits.Key.is_eq(k, RKnown.Id.key(e)),
      Some{
        Crits.Crit.merge(
          ~List<&2, Ledgers.Id>,
          ~RKnown.Ids.join,
          Crits.Crit.get(List<&2, Ledgers.Id>, acc, RKnown.Id.key(e)),
          [e]
        )
      },
      Crits.Crit.get(List<&2, Ledgers.Id>, acc, k)
    ): Maybe<&2, List<&2, Ledgers.Id>>
}:
  +w =>
    %Equal.sym(
      Maybe<&2, List<&2, Ledgers.Id>>,
      Crits.Crit.get(List<&2, Ledgers.Id>, RKnown.Ids.put(acc, e), k),
      Crits.Crit.lookup(List<&2, Ledgers.Id>, RKnown.Ids.put(acc, e), k),
      Crits.Crit.get_lookup(
        ~List<&2, Ledgers.Id>,
        RKnown.Ids.put(acc, e),
        k
      )(
        Crits.Crit.upsert_wf(~List<&2, Ledgers.Id>, ~RKnown.Ids.join, acc, RKnown.Id.key(e), [e])(w)
      )
    ): {
      _
        == Bool.pick(
          Maybe<&2, List<&2, Ledgers.Id>>,
          Crits.Key.is_eq(k, RKnown.Id.key(e)),
          Some{
            Crits.Crit.merge(
              ~List<&2, Ledgers.Id>,
              ~RKnown.Ids.join,
              Crits.Crit.get(List<&2, Ledgers.Id>, acc, RKnown.Id.key(e)),
              [e]
            )
          },
          Crits.Crit.get(List<&2, Ledgers.Id>, acc, k)
        ): Maybe<&2, List<&2, Ledgers.Id>>
    }
    %Equal.sym(
      Maybe<&2, List<&2, Ledgers.Id>>,
      Crits.Crit.lookup(List<&2, Ledgers.Id>, RKnown.Ids.put(acc, e), k),
      Bool.pick(
        Maybe<&2, List<&2, Ledgers.Id>>,
        Crits.Key.is_eq(k, RKnown.Id.key(e)),
        Some{
          Crits.Crit.merge(
            ~List<&2, Ledgers.Id>,
            ~RKnown.Ids.join,
            Crits.Crit.lookup(List<&2, Ledgers.Id>, acc, RKnown.Id.key(e)),
            [e]
          )
        },
        Crits.Crit.lookup(List<&2, Ledgers.Id>, acc, k)
      ),
      Crits.Crit.upsert_lookup(
        ~List<&2, Ledgers.Id>,
        ~RKnown.Ids.join,
        acc,
        RKnown.Id.key(e),
        [e],
        k
      )(w)
    ): {
      _
        == Bool.pick(
          Maybe<&2, List<&2, Ledgers.Id>>,
          Crits.Key.is_eq(k, RKnown.Id.key(e)),
          Some{
            Crits.Crit.merge(
              ~List<&2, Ledgers.Id>,
              ~RKnown.Ids.join,
              Crits.Crit.get(List<&2, Ledgers.Id>, acc, RKnown.Id.key(e)),
              [e]
            )
          },
          Crits.Crit.get(List<&2, Ledgers.Id>, acc, k)
        ): Maybe<&2, List<&2, Ledgers.Id>>
    }
    %Equal.sym(
      Maybe<&2, List<&2, Ledgers.Id>>,
      Crits.Crit.get(List<&2, Ledgers.Id>, acc, k),
      Crits.Crit.lookup(List<&2, Ledgers.Id>, acc, k),
      Crits.Crit.get_lookup(~List<&2, Ledgers.Id>, acc, k)(w)
    ): {
      Bool.pick(
        Maybe<&2, List<&2, Ledgers.Id>>,
        Crits.Key.is_eq(k, RKnown.Id.key(e)),
        Some{
          Crits.Crit.merge(
            ~List<&2, Ledgers.Id>,
            ~RKnown.Ids.join,
            Crits.Crit.lookup(List<&2, Ledgers.Id>, acc, RKnown.Id.key(e)),
            [e]
          )
        },
        Crits.Crit.lookup(List<&2, Ledgers.Id>, acc, k)
      )
        == Bool.pick(
          Maybe<&2, List<&2, Ledgers.Id>>,
          Crits.Key.is_eq(k, RKnown.Id.key(e)),
          Some{
            Crits.Crit.merge(
              ~List<&2, Ledgers.Id>,
              ~RKnown.Ids.join,
              Crits.Crit.get(List<&2, Ledgers.Id>, acc, RKnown.Id.key(e)),
              [e]
            )
          },
          _
        ): Maybe<&2, List<&2, Ledgers.Id>>
    }
    %Equal.sym(
      Maybe<&2, List<&2, Ledgers.Id>>,
      Crits.Crit.get(List<&2, Ledgers.Id>, acc, RKnown.Id.key(e)),
      Crits.Crit.lookup(List<&2, Ledgers.Id>, acc, RKnown.Id.key(e)),
      Crits.Crit.get_lookup(~List<&2, Ledgers.Id>, acc, RKnown.Id.key(e))(w)
    ): {
      Bool.pick(
        Maybe<&2, List<&2, Ledgers.Id>>,
        Crits.Key.is_eq(k, RKnown.Id.key(e)),
        Some{
          Crits.Crit.merge(
            ~List<&2, Ledgers.Id>,
            ~RKnown.Ids.join,
            Crits.Crit.lookup(List<&2, Ledgers.Id>, acc, RKnown.Id.key(e)),
            [e]
          )
        },
        Crits.Crit.lookup(List<&2, Ledgers.Id>, acc, k)
      )
        == Bool.pick(
          Maybe<&2, List<&2, Ledgers.Id>>,
          Crits.Key.is_eq(k, RKnown.Id.key(e)),
          Some{Crits.Crit.merge(~List<&2, Ledgers.Id>, ~RKnown.Ids.join, _, [e])},
          Crits.Crit.lookup(List<&2, Ledgers.Id>, acc, k)
        ): Maybe<&2, List<&2, Ledgers.Id>>
    }
    {==}

# a set with one more id holds an id exactly when it is that id, or the set
# held it
def Ids.put_has(
  +acc: RKnown.Ids(),
  +e: Ledgers.Id,
  +i: Ledgers.Id
) -> {
  Crits.Crit.wf(~List<&2, Ledgers.Id>, acc, 0n) == True{}: Bool
} -> {
  RKnown.Ids.has(
    RKnown.Ids.put(acc, e),
    i
  )
    == Bool.or(Ledgers.Id.is_eq(e, i), RKnown.Ids.has(acc, i)): Bool
}:
  w =>
    %Equal.sym(
      Maybe<&2, List<&2, Ledgers.Id>>,
      Crits.Crit.get(List<&2, Ledgers.Id>, RKnown.Ids.put(acc, e), RKnown.Id.key(i)),
      Bool.pick(
        Maybe<&2, List<&2, Ledgers.Id>>,
        Crits.Key.is_eq(RKnown.Id.key(i), RKnown.Id.key(e)),
        Some{
          Crits.Crit.merge(
            ~List<&2, Ledgers.Id>,
            ~RKnown.Ids.join,
            Crits.Crit.get(List<&2, Ledgers.Id>, acc, RKnown.Id.key(e)),
            [e]
          )
        },
        Crits.Crit.get(List<&2, Ledgers.Id>, acc, RKnown.Id.key(i))
      ),
      Ids.get_put(acc, e, RKnown.Id.key(i))(w)
    ): {RKnown.Ids.has.of(_, i) == Bool.or(Ledgers.Id.is_eq(e, i), RKnown.Ids.has(acc, i)): Bool}
    Lists.Bool.by(
      h => {
        RKnown.Ids.has.of(
          Bool.pick(
            Maybe<&2, List<&2, Ledgers.Id>>,
            h,
            Some{
              Crits.Crit.merge(
                ~List<&2, Ledgers.Id>,
                ~RKnown.Ids.join,
                Crits.Crit.get(List<&2, Ledgers.Id>, acc, RKnown.Id.key(e)),
                [e]
              )
            },
            Crits.Crit.get(List<&2, Ledgers.Id>, acc, RKnown.Id.key(i))
          ),
          i
        )
          == Bool.or(Ledgers.Id.is_eq(e, i), RKnown.Ids.has(acc, i)): Bool
      },
      Crits.Key.is_eq(RKnown.Id.key(i), RKnown.Id.key(e)),
      et => (
        %Crits.Key.is_eq_sound(RKnown.Id.key(i), RKnown.Id.key(e))(et): {RKnown.Ids.has.of(Some{Crits.Crit.merge(~List<&2, Ledgers.Id>, ~RKnown.Ids.join, Crits.Crit.get(List<&2, Ledgers.Id>, acc, _), [e])}, i) == Bool.or(Ledgers.Id.is_eq(e, i), RKnown.Ids.has(acc, i)): Bool}
        Bucket.has_put(Crits.Crit.get(List<&2, Ledgers.Id>, acc, RKnown.Id.key(i)), e, i)),
      ef => (
        %Equal.sym(Bool, Ledgers.Id.is_eq(e, i), False{}, Key.ne_id(e, i)(ef)): {RKnown.Ids.has(acc, i) == Bool.or(_, RKnown.Ids.has(acc, i)): Bool}
        {==})
    )

# a set with the ids of some versions is well formed when it was
def Ids.go_wf(
  vs: List<&2, Types.Entry>,
  +acc: RKnown.Ids()
) -> {
  Crits.Crit.wf(~List<&2, Ledgers.Id>, acc, 0n) == True{}: Bool
} -> {Crits.Crit.wf(~List<&2, Ledgers.Id>, RKnown.Ids.go(vs, acc), 0n) == True{}: Bool}:
  match vs:
    case Nil{}:
      w => w
    case Con{+e, rest}:
      w => Ids.go_wf(
        rest,
        RKnown.Ids.put(acc, RLines.Entry.id(e))
      )(
        Crits.Crit.upsert_wf(
          ~List<&2, Ledgers.Id>,
          ~RKnown.Ids.join,
          acc,
          RKnown.Id.key(RLines.Entry.id(e)),
          [RLines.Entry.id(e)]
        )(w)
      )

# a set with the ids of the versions vs holds an id exactly when the id made
# one of vs, or the set held it
def Ids.go_has(
  vs: List<&2, Types.Entry>,
  +acc: RKnown.Ids(),
  +i: Ledgers.Id
) -> {
  Crits.Crit.wf(~List<&2, Ledgers.Id>, acc, 0n) == True{}: Bool
} -> {
  RKnown.Ids.has(
    RKnown.Ids.go(vs, acc),
    i
  )
    == Bool.or(
      Shared.List.some(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, vs, i),
      RKnown.Ids.has(acc, i)
    ): Bool
}:
  match vs:
    case Nil{}:
      w => {==}
    case Con{+e, +rest}:
      +w => Equal.trans(
        Bool,
        RKnown.Ids.has(RKnown.Ids.go(rest, RKnown.Ids.put(acc, RLines.Entry.id(e))), i),
        Bool.or(
          Shared.List.some(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, rest, i),
          RKnown.Ids.has(RKnown.Ids.put(acc, RLines.Entry.id(e)), i)
        ),
        Bool.or(
          Shared.List.some(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, e <> rest, i),
          RKnown.Ids.has(acc, i)
        ),
        Ids.go_has(
          rest,
          RKnown.Ids.put(acc, RLines.Entry.id(e)),
          i
        )(
          Crits.Crit.upsert_wf(
            ~List<&2, Ledgers.Id>,
            ~RKnown.Ids.join,
            acc,
            RKnown.Id.key(RLines.Entry.id(e)),
            [RLines.Entry.id(e)]
          )(w)
        ),
        (
          %Equal.sym(Bool, RKnown.Ids.has(RKnown.Ids.put(acc, RLines.Entry.id(e)), i), Bool.or(Ledgers.Id.is_eq(RLines.Entry.id(e), i), RKnown.Ids.has(acc, i)), Ids.put_has(acc, RLines.Entry.id(e), i)(w)): {Bool.or(Shared.List.some(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, rest, i), _) == Bool.or(List.any.if(u => Shared.List.some(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, rest, i), Ledgers.Id.is_eq(RLines.Entry.id(e), i)), RKnown.Ids.has(acc, i)): Bool}
          Lists.Bool.by(b => {Bool.or(Shared.List.some(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, rest, i), Bool.or(b, RKnown.Ids.has(acc, i))) == Bool.or(List.any.if(u => Shared.List.some(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, rest, i), b), RKnown.Ids.has(acc, i)): Bool}, Ledgers.Id.is_eq(RLines.Entry.id(e), i), et => Shared.Bool.or_true_right(Shared.List.some(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, rest, i)), ef => {==}))
      )

# the ids of the versions vs hold an id exactly when the id made one of vs
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
    Ids.go_has(vs, Crits.Crit.new(List<&2, Ledgers.Id>), i)({==}),
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

# a set with the ids of vs and then zs is the set with the ids of vs, with
# the ids of zs
def Ids.go_append(
  vs: List<&2, Types.Entry>,
  +zs: List<&2, Types.Entry>,
  +acc: RKnown.Ids()
) -> {
  RKnown.Ids.go(
    List.append(&2, Types.Entry, vs, zs),
    acc
  )
    == RKnown.Ids.go(zs, RKnown.Ids.go(vs, acc)): RKnown.Ids()
}:
  match vs:
    case Nil{}:
      {==}
    case Con{+e, rest}:
      Ids.go_append(rest, zs, RKnown.Ids.put(acc, RLines.Entry.id(e)))

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
    case Con{RKnown.Held{+c2, +k2, +d2, +x2}, +rest}:
      ok => e => Known.find_ok(rest, s, c, st)(Ok.tail(RKnown.Held{c2, k2, d2, x2}, rest, s)(ok))(e)
    case Con{RKnown.Ruled{+c2, +u2}, +rest}:
      ok => e => Known.find_ok(rest, s, c, st)(Ok.tail(RKnown.Ruled{c2, u2}, rest, s)(ok))(e)
    case Con{RKnown.Made{+c2, +y2}, +rest}:
      ok => e => Known.find_ok(rest, s, c, st)(Ok.tail(RKnown.Made{c2, y2}, rest, s)(ok))(e)

# the ids that a right table holds for a line fit the state that the facts
# give the line
def Known.ids_ok(
  kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +x: RKnown.Ids()
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RKnown.Known.ids(kn, c) == Some{x}: Maybe<&2, RKnown.Ids()>
} -> {RKnown.Made.fits(RLines.Line.state(s, c), x) == True{}: Bool}:
  match kn:
    case Nil{}:
      ok => e => Empty.absurd(
        {RKnown.Made.fits(RLines.Line.state(s, c), x) == True{}: Bool},
        Shared.Maybe.none_ne_some(RKnown.Ids(), x, e)
      )
    case Con{RKnown.Kept{+c2, +st2}, +rest}:
      ok => e => Known.ids_ok(rest, s, c, x)(Ok.tail(RKnown.Kept{c2, st2}, rest, s)(ok))(e)
    case Con{RKnown.Held{+c2, +k2, +d2, +x2}, +rest}:
      ok => e => Known.ids_ok(rest, s, c, x)(Ok.tail(RKnown.Held{c2, k2, d2, x2}, rest, s)(ok))(e)
    case Con{RKnown.Ruled{+c2, +u2}, +rest}:
      ok => e => Known.ids_ok(rest, s, c, x)(Ok.tail(RKnown.Ruled{c2, u2}, rest, s)(ok))(e)
    case Con{RKnown.Made{+c2, +y2}, +rest}:
      +ok => Lists.Bool.by(
        b => {
          Shared.Bool.when(
            Maybe<&2, RKnown.Ids()>,
            b,
            w => Some{y2},
            w => RKnown.Known.ids(rest, c)
          )
            == Some{x}: Maybe<&2, RKnown.Ids()>
        } -> {RKnown.Made.fits(RLines.Line.state(s, c), x) == True{}: Bool},
        Ledgers.Line.is_eq(c2, c),
        +et => +e => (
          %Ledgers.Line.is_eq_sound(c2, c)(et): {RKnown.Made.fits(RLines.Line.state(s, _), x) == True{}: Bool}
          %Shared.Maybe.some_inj(RKnown.Ids(), y2, x, e): {RKnown.Made.fits(RLines.Line.state(s, c2), _) == True{}: Bool}
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
    RKnown.Ids(),
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
      %Equal.sym(RKnown.Ids(), y, RKnown.Ids.of(vs), Made.fits_sound(RLines.Line.state(s, c), y, vs, k)(e)(Known.ids_ok(kn, s, c, y)(ok)(ey))): {RKnown.Ids.has(_, i) == Shared.List.some(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, vs, i): Bool}
      Ids.of_has(vs, i))
  )

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
    case Con{RKnown.Held{+c2, +k2, +d2, +x2}, +rest}:
      ok => e => Known.ruled_ok(rest, s, c, u)(Ok.tail(RKnown.Held{c2, k2, d2, x2}, rest, s)(ok))(e)
    case Con{RKnown.Ruled{+c2, +u2}, +rest}:
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
          Rule.fits_sound(RKnown.Known.rule.next(RKnown.Known.none(), s, c2, RLines.Line.state(s, c2)), u2)(Ok.head(RKnown.Ruled{c2, u2}, rest, s)(ok))),
        ef => e => Known.ruled_ok(rest, s, c, u)(Ok.tail(RKnown.Ruled{c2, u2}, rest, s)(ok))(e)
      )
    case Con{RKnown.Made{+c2, +y2}, +rest}:
      ok => e => Known.ruled_ok(rest, s, c, u)(Ok.tail(RKnown.Made{c2, y2}, rest, s)(ok))(e)

# the state of a line, computed with the state R and k of its store, is the
# state that the facts give it
def Known.fresh_at_ok(
  +s: RFacts.Plain(),
  c: Ledgers.Line,
  +R: List<&2, Types.Entry>,
  +k: Nat
) -> {
  RLines.Line.state(s, RKnown.Known.root(c)) == Some{RLines.State{R, k}}: Maybe<&2, RLines.State>
} -> {RKnown.Known.fresh.at(s, c, R, k) == RLines.Line.state(s, c): Maybe<&2, RLines.State>}:
  match c:
    case Ledgers.Line{+h, None{}}:
      e => Equal.sym(
        Maybe<&2, RLines.State>,
        RLines.Line.state(s, Ledgers.Line{h, None{}}),
        Some{RLines.State{R, k}},
        e
      )
    case Ledgers.Line{+h, Some{+b}}:
      e => (
        %Equal.sym(Maybe<&2, RLines.State>, RLines.Store.state(s, h), Some{RLines.State{R, k}}, e): {RLines.Branch.state(s, Ledgers.Line{h, Some{b}}, Some{R}) == RLines.Branch.state(s, Ledgers.Line{h, Some{b}}, Maybe.map(&2, RLines.State, List<&2, Types.Entry>, RLines.State.versions, _)): Maybe<&2, RLines.State>}
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

# the rule after the versions vs of a line, with the versions R of its
# store, is the rule that the facts give
def Known.rule_at_ok(
  +s: RFacts.Plain(),
  c: Ledgers.Line,
  +vs: List<&2, Types.Entry>,
  +R: List<&2, Types.Entry>,
  +k: Nat
) -> {
  RLines.Line.state(s, RKnown.Known.root(c)) == Some{RLines.State{R, k}}: Maybe<&2, RLines.State>
} -> {RKnown.Known.rule.at(c, vs, R) == RLines.Rule.after(s, c, vs): Maybe<&2, RLines.Rule>}:
  match c:
    case Ledgers.Line{+h, None{}}:
      e => {==}
    case Ledgers.Line{+h, Some{+b}}:
      e => (
        %Equal.sym(Maybe<&2, RLines.State>, RLines.Store.state(s, h), Some{RLines.State{R, k}}, e): {RLines.Line.rule(Some{R}, Ledgers.Line{h, Some{b}}, vs) == RLines.Rule.after.of(Ledgers.Line{h, Some{b}}, vs, Maybe.map(&2, RLines.State, List<&2, Types.Entry>, RLines.State.versions, _)): Maybe<&2, RLines.Rule>}
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
    RKnown.Known.rule.put(kn, c, RKnown.Known.rule.next(kn, s, c, m)),
    s
  )
    == True{}: Bool
}:
  match m:
    case None{}:
      e => ok => ok
    case Some{RLines.State{+vs, +k}}:
      e => +ok => Lists.Maybe.by(
        RLines.Rule,
        y => {RContents.Known.ok(RKnown.Known.rule.put(kn, c, y), s) == True{}: Bool},
        RKnown.Known.rule(kn, s, c, vs),
        en => ok,
        +u => eu => Ok.cons(
          RKnown.Ruled{c, u},
          kn,
          s
        )(
          Rule.fits_of(
            RKnown.Known.rule.next(RKnown.Known.none(), s, c, RLines.Line.state(s, c)),
            u
          )(
            %Equal.sym(Maybe<&2, RLines.State>, RLines.Line.state(s, c), Some{RLines.State{vs, k}}, Known.find_ok(kn, s, c, RLines.State{vs, k})(ok)(e)): {RKnown.Known.rule.next(RKnown.Known.none(), s, c, _) == Some{u}: Maybe<&2, RLines.Rule>}
            Equal.trans(Maybe<&2, RLines.Rule>, RLines.Rule.after(s, c, vs), RKnown.Known.rule(kn, s, c, vs), Some{u}, Equal.sym(Maybe<&2, RLines.Rule>, RKnown.Known.rule(kn, s, c, vs), RLines.Rule.after(s, c, vs), Known.rule_ok(kn, s, c, vs)(ok)), eu))
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
    Maybe.is_some(&2, RKnown.Ids(), RKnown.Known.ids(kn, c)),
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
  RContents.Kept.ok(Facts.Facts.crit(s), RKnown.Ruled{c, u}) == True{}: Bool
} -> {RContents.Kept.ok(Facts.Facts.crit(s2), RKnown.Ruled{c, u}) == True{}: Bool}:
  ec => er => h => (
    %Equal.sym(Maybe<&2, RLines.State>, Lines.Line.state(s2, c), Lines.Line.state(s, c), ec): {RKnown.Rule.fits(RKnown.Known.rule.next(RKnown.Known.none(), Facts.Facts.crit(s2), c, _), u) == True{}: Bool}
    %Equal.sym(Maybe<&2, RLines.Rule>, RKnown.Known.rule.next(RKnown.Known.none(), Facts.Facts.crit(s2), c, Lines.Line.state(s, c)), RKnown.Known.rule.next(RKnown.Known.none(), Facts.Facts.crit(s), c, Lines.Line.state(s, c)), Next.same(s, s2, c, Lines.Line.state(s, c))(er)): {RKnown.Rule.fits(_, u) == True{}: Bool}
    h)

# the ids that a table holds for a line stay right, when the state of the
# line is read as before
def Made.same(
  +s: Facts.Facts(),
  +s2: Facts.Facts(),
  +c: Ledgers.Line,
  +y: RKnown.Ids()
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
    case Con{RKnown.Held{+c2, +k2, +d2, +x2}, +rest}:
      ok => Known.voted_ok(
        rest,
        name,
        s,
        c,
        k,
        t,
        x
      )(Ok.tail(RKnown.Held{c2, k2, d2, x2}, rest, Facts.Facts.crit(s))(ok))
    case Con{RKnown.Ruled{+c2, +u}, +rest}:
      +ok => Lists.Bool.by(
        b => {
          RContents.Known.ok(
            List.filter.put(
              RKnown.Kept,
              RKnown.Ruled{c2, u},
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
        )(Ok.tail(RKnown.Ruled{c2, u}, rest, Facts.Facts.crit(s))(ok)),
        +ef => Ok.cons(
          RKnown.Ruled{c2, u},
          RKnown.Known.voted(rest, c),
          Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))
        )(
          Ruled.same(
            s,
            Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}),
            c2,
            u
          )(
            Line.state_voted(name, s, c, k, t, x, c2)(ef)
          )(
            Line.state_voted(name, s, c, k, t, x, RKnown.Known.root(c2))(Hit.root(c, c2)(ef))
          )(Ok.head(RKnown.Ruled{c2, u}, rest, Facts.Facts.crit(s))(ok))
        )(
          Known.voted_ok(
            rest,
            name,
            s,
            c,
            k,
            t,
            x
          )(Ok.tail(RKnown.Ruled{c2, u}, rest, Facts.Facts.crit(s))(ok))
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

# a right table changes no vote for an ask at the next slot of a line
def Work.offer.at_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +name: String,
  +c: Ledgers.Line,
  +a: Types.Ask,
  m: Maybe<&2, RWorks.Open>
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
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
      +ok => o => (
        %Era.now_ok(kn, s, c)(ok): {RWorks.Work.offer.at(kn, s, name, c, a, Some{RWorks.Open{vs, k, ns}}) == Shared.Maybe.when(RWorks.Plan, Bool.not(Shared.List.some(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, vs, RLines.Ask.id(a))), u => RWorks.Plan.of(c, k, RWorks.Work.offer.of(u2 => Types.Pick{a, RWorks.Pins.for(RKnown.Known.none(), s, c, vs, _, RLines.Ask.request(a))}, RRounds.Slot.chance(RWorks.Work.ballots(s, c, k), ns, k, name)))): Maybe<&2, RWorks.Plan>}
        %Pins.for_ok(kn, s, c, vs, RWorks.Era.now(kn, s, c), RLines.Ask.request(a))(ok): {RWorks.Work.offer.at(kn, s, name, c, a, Some{RWorks.Open{vs, k, ns}}) == Shared.Maybe.when(RWorks.Plan, Bool.not(Shared.List.some(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, vs, RLines.Ask.id(a))), u => RWorks.Plan.of(c, k, RWorks.Work.offer.of(u2 => Types.Pick{a, _}, RRounds.Slot.chance(RWorks.Work.ballots(s, c, k), ns, k, name)))): Maybe<&2, RWorks.Plan>}
        %Known.made_ok(kn, s, c, vs, k, RLines.Ask.id(a))(ok)(o): {RWorks.Work.offer.at(kn, s, name, c, a, Some{RWorks.Open{vs, k, ns}}) == Shared.Maybe.when(RWorks.Plan, Bool.not(_), u => RWorks.Plan.of(c, k, RWorks.Work.offer.of(u2 => Types.Pick{a, RWorks.Pins.for(kn, s, c, vs, RWorks.Era.now(kn, s, c), RLines.Ask.request(a))}, RRounds.Slot.chance(RWorks.Work.ballots(s, c, k), ns, k, name)))): Maybe<&2, RWorks.Plan>}
        {==})

# a right table changes no vote for an ask on its line
def Work.offer.on_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +name: String,
  +a: Types.Ask,
  m: Maybe<&2, Ledgers.Line>
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
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
        %Equal.sym(Maybe<&2, RWorks.Open>, RWorks.Work.open(kn, s, name, c), RWorks.Work.open(RKnown.Known.none(), s, name, c), Work.open_ok(kn, s, name, c)(ok)): {RWorks.Work.offer.at(kn, s, name, c, a, _) == RWorks.Work.offer.at(RKnown.Known.none(), s, name, c, a, RWorks.Work.open(RKnown.Known.none(), s, name, c)): Maybe<&2, RWorks.Plan>}
        Work.offer.at_ok(kn, s, name, c, a, RWorks.Work.open(RKnown.Known.none(), s, name, c))(ok)(Work.open_from(s, name, c)))

# a right table changes no vote for an ask
def Work.offer_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +all: List<&2, Types.Fact>,
  +name: String,
  +a: Types.Ask
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RWorks.Work.offer(
    kn,
    s,
    all,
    name,
    a
  )
    == RWorks.Work.offer(RKnown.Known.none(), s, all, name, a): Maybe<&2, RWorks.Plan>
}:
  ok => Work.offer.on_ok(kn, s, name, a, RWorks.Request.line(all, RLines.Ask.request(a)))(ok)

# a right table changes no ask that the node may vote for
def Work.ready_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +all: List<&2, Types.Fact>,
  +name: String,
  fs: List<&2, Types.Fact>
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RWorks.Work.ready(
    fs,
    kn,
    s,
    all,
    name
  )
    == RWorks.Work.ready(fs, RKnown.Known.none(), s, all, name): List<&2, Types.Ask>
}:
  match fs:
    case Nil{}:
      ok => {==}
    case Con{Types.Fact.Vote{v, st, x}, rest}:
      ok => Work.ready_ok(kn, s, all, name, rest)(ok)
    case Con{Types.Fact.Ask{+a}, +rest}:
      +ok => (
        %Work.ready_ok(kn, s, all, name, rest)(ok): {RWorks.Work.ready(Types.Fact.Ask{a} <> rest, kn, s, all, name) == List.filter.put(Types.Ask, a, _, Maybe.is_some(&2, RWorks.Plan, RWorks.Work.offer(RKnown.Known.none(), s, all, name, a))): List<&2, Types.Ask>}
        %Work.offer_ok(kn, s, all, name, a)(ok): {RWorks.Work.ready(Types.Fact.Ask{a} <> rest, kn, s, all, name) == List.filter.put(Types.Ask, a, RWorks.Work.ready(rest, kn, s, all, name), Maybe.is_some(&2, RWorks.Plan, _)): List<&2, Types.Ask>}
        {==})

# a right table changes no vote for the ask m
def Work.propose.of_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +all: List<&2, Types.Fact>,
  +name: String,
  m: Maybe<&2, Types.Ask>
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RWorks.Work.propose.of(
    m,
    kn,
    s,
    all,
    name
  )
    == RWorks.Work.propose.of(m, RKnown.Known.none(), s, all, name): Maybe<&2, RWorks.Plan>
}:
  match m:
    case None{}:
      ok => {==}
    case Some{+a}:
      ok => Work.offer_ok(kn, s, all, name, a)(ok)

# a right table changes no vote that the node proposes
def Work.propose_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +name: String
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RWorks.Work.propose(
    kn,
    s,
    name
  )
    == RWorks.Work.propose(RKnown.Known.none(), s, name): Maybe<&2, RWorks.Plan>
}:
  +ok => (
    %Work.ready_ok(kn, s, RFacts.Facts.list(s), name, RFacts.Facts.list(s))(ok): {RWorks.Work.propose(kn, s, name) == RWorks.Work.propose.of(Lists.List.top(~Types.Ask, ~RFacts.Ask.seq, _), RKnown.Known.none(), s, RFacts.Facts.list(s), name): Maybe<&2, RWorks.Plan>}
    Work.propose.of_ok(kn, s, RFacts.Facts.list(s), name, Lists.List.top(~Types.Ask, ~RFacts.Ask.seq, RWorks.Work.ready(RFacts.Facts.list(s), kn, s, RFacts.Facts.list(s), name)))(ok))

# a right table changes no vote at the slot of a ballot
def Work.follow.of_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +name: String,
  f: Types.Fact
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
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
      ok => Equal.cong(
        Maybe<&2, RWorks.Open>,
        Maybe<&2, RWorks.Plan>,
        m => RWorks.Work.follow.at(s, name, c, k, m),
        RWorks.Work.open(kn, s, name, c),
        RWorks.Work.open(RKnown.Known.none(), s, name, c),
        Work.open_ok(kn, s, name, c)(ok)
      )
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
  RContents.Known.ok(kn, s) == True{}: Bool
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
  RContents.Known.ok(kn, s) == True{}: Bool
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
    case Some{k1} Some{id} Some{RWorks.Open{vs, k2, ns}}:
      ok => o => {==}
    case Some{k1} None{} Some{RWorks.Open{vs, k2, ns}}:
      ok => o => {==}
    case None{} Some{id} None{}:
      ok => o => {==}
    case None{} None{} None{}:
      ok => o => {==}
    case None{} None{} Some{RWorks.Open{vs, k2, ns}}:
      ok => o => {==}
    case None{} Some{+id} Some{RWorks.Open{+vs, +k2, ns}}:
      ok => o => Equal.cong(
        Bool,
        Maybe<&2, RWorks.Plan>,
        b => Shared.Maybe.when(
          RWorks.Plan,
          Bool.not(b),
          u => RWorks.Plan.of(c, k2, RRounds.Slot.pass(RWorks.Work.ballots(s, c, k2), name))
        ),
        RKnown.Known.made(kn, c, vs, id),
        Shared.List.some(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, vs, id),
        Known.made_ok(kn, s, c, vs, k2, id)(ok)(o)
      )

# a right table changes no pass for a request on its line
def Work.pass.on_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +name: String,
  +i: Ledgers.Id,
  m: Maybe<&2, Ledgers.Line>
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
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
        %Equal.sym(Maybe<&2, RWorks.Open>, RWorks.Work.open(kn, s, name, c), RWorks.Work.open(RKnown.Known.none(), s, name, c), Work.open_ok(kn, s, name, c)(ok)): {RWorks.Work.pass.at(kn, s, name, c, None{}, Some{i}, _) == RWorks.Work.pass.at(RKnown.Known.none(), s, name, c, None{}, Some{i}, RWorks.Work.open(RKnown.Known.none(), s, name, c)): Maybe<&2, RWorks.Plan>}
        Work.pass.at_ok(kn, s, name, c, None{}, Some{i}, RWorks.Work.open(RKnown.Known.none(), s, name, c))(ok)(Work.open_from(s, name, c)))

# a right table changes no pass at the slot of a fact
def Work.pass.of_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +all: List<&2, Types.Fact>,
  +name: String,
  f: Types.Fact
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RWorks.Work.pass.of(
    f,
    kn,
    s,
    all,
    name
  )
    == RWorks.Work.pass.of(f, RKnown.Known.none(), s, all, name): Maybe<&2, RWorks.Plan>
}:
  match f:
    case Types.Fact.Vote{v, Types.Step.At{+c, +k, t}, x}:
      +ok => (
        %Equal.sym(Maybe<&2, RWorks.Open>, RWorks.Work.open(kn, s, name, c), RWorks.Work.open(RKnown.Known.none(), s, name, c), Work.open_ok(kn, s, name, c)(ok)): {RWorks.Work.pass.at(kn, s, name, c, Some{k}, None{}, _) == RWorks.Work.pass.at(RKnown.Known.none(), s, name, c, Some{k}, None{}, RWorks.Work.open(RKnown.Known.none(), s, name, c)): Maybe<&2, RWorks.Plan>}
        Work.pass.at_ok(kn, s, name, c, Some{k}, None{}, RWorks.Work.open(RKnown.Known.none(), s, name, c))(ok)(Work.open_from(s, name, c)))
    case Types.Fact.Vote{v, Types.Step.Broken{}, x}:
      ok => {==}
    case Types.Fact.Ask{Types.Ask{+i, n, +r}}:
      ok => Work.pass.on_ok(kn, s, name, i, RWorks.Request.line(all, r))(ok)

# a right table changes no pass at the slot of a fact among fs
def Work.pass_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +all: List<&2, Types.Fact>,
  +name: String,
  fs: List<&2, Types.Fact>
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RWorks.Work.pass(
    fs,
    kn,
    s,
    all,
    name
  )
    == RWorks.Work.pass(fs, RKnown.Known.none(), s, all, name): Maybe<&2, RWorks.Plan>
}:
  match fs:
    case Nil{}:
      ok => {==}
    case Con{+f, +rest}:
      +ok => (
        %Work.pass.of_ok(kn, s, all, name, f)(ok): {RWorks.Work.pass(f <> rest, kn, s, all, name) == RWorks.Work.follow.or(_, u => RWorks.Work.pass(rest, RKnown.Known.none(), s, all, name)): Maybe<&2, RWorks.Plan>}
        %Work.pass_ok(kn, s, all, name, rest)(ok): {RWorks.Work.pass(f <> rest, kn, s, all, name) == RWorks.Work.follow.or(RWorks.Work.pass.of(f, kn, s, all, name), u => _): Maybe<&2, RWorks.Plan>}
        {==})

# a right table changes no ballot that the node casts next
def Work.plan_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +name: String
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  RWorks.Work.plan(
    kn,
    s,
    name
  )
    == RWorks.Work.plan(RKnown.Known.none(), s, name): Maybe<&2, RWorks.Plan>
}:
  +ok => (
    %Work.propose_ok(kn, s, name)(ok): {RWorks.Work.plan(kn, s, name) == RWorks.Work.follow.or(_, u => RWorks.Work.follow.or(RWorks.Work.follow(RKnown.Known.none(), s, name, RFacts.Facts.list(s)), u2 => RWorks.Work.pass(RFacts.Facts.list(s), RKnown.Known.none(), s, RFacts.Facts.list(s), name))): Maybe<&2, RWorks.Plan>}
    %Work.follow_ok(kn, s, name, RFacts.Facts.list(s))(ok): {RWorks.Work.plan(kn, s, name) == RWorks.Work.follow.or(RWorks.Work.propose(kn, s, name), u => RWorks.Work.follow.or(_, u2 => RWorks.Work.pass(RFacts.Facts.list(s), RKnown.Known.none(), s, RFacts.Facts.list(s), name))): Maybe<&2, RWorks.Plan>}
    %Work.pass_ok(kn, s, RFacts.Facts.list(s), name, RFacts.Facts.list(s))(ok): {RWorks.Work.plan(kn, s, name) == RWorks.Work.follow.or(RWorks.Work.propose(kn, s, name), u => RWorks.Work.follow.or(RWorks.Work.follow(kn, s, name, RFacts.Facts.list(s)), u2 => _)): Maybe<&2, RWorks.Plan>}
    {==})

# a right table changes no work
def Work.does_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +name: String
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
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

# a content that a right table gives a read with the fuel f is what the read
# gives
def Known.files_ok(
  kn: RKnown.Known(),
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
  match kn:
    case Nil{}:
      ok => e => Empty.absurd(
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
    case Con{RKnown.Kept{+c2, +st2}, +rest}:
      ok => e => Known.files_ok(rest, s, c, k, f, x)(Ok.tail(RKnown.Kept{c2, st2}, rest, s)(ok))(e)
    case Con{RKnown.Ruled{+c2, +u2}, +rest}:
      ok => e => Known.files_ok(rest, s, c, k, f, x)(Ok.tail(RKnown.Ruled{c2, u2}, rest, s)(ok))(e)
    case Con{RKnown.Held{+c2, +k2, +d, +x2}, +rest}:
      +ok => Lists.Bool.by(
        b => {
          RKnown.Known.files.of(
            Shared.Bool.when(
              Maybe<&2, RKnown.Kept>,
              b,
              u => Some{RKnown.Held{c2, k2, d, x2}},
              u => RKnown.Known.held(rest, c, k)
            ),
            f
          )
            == Some{x}: Maybe<&2, RFiles.Files()>
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
        List.all.if(u2 => Ledgers.Line.is_eq(c2, c), Nat.is_eq(k2, k)),
        +et => Lists.Bool.by(
          b => {
            Shared.Maybe.when(
              RFiles.Files(),
              b,
              u => Some{x2}
            )
              == Some{x}: Maybe<&2, RFiles.Files()>
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
            %Ledgers.Line.is_eq_sound(c2, c)(Shared.List.all.if_rest(Nat.is_eq(k2, k), u2 => Ledgers.Line.is_eq(c2, c))(et)): {RContents.Content.at(f, RKnown.Known.none(), s, _, k) == Some{x}: Maybe<&2, RFiles.Files()>}
            %Shared.Nat.is_eq_sound(k2, k)(Shared.List.all.if_hit(Nat.is_eq(k2, k), u2 => Ledgers.Line.is_eq(c2, c))(et)): {RContents.Content.at(f, RKnown.Known.none(), s, c2, _) == Some{x}: Maybe<&2, RFiles.Files()>}
            %Shared.Maybe.some_inj(RFiles.Files(), x2, x, e): {RContents.Content.at(f, RKnown.Known.none(), s, c2, k2) == Some{_}: Maybe<&2, RFiles.Files()>}
            Plain.at_le(f, d, s, c2, k2, x2)(el)(Files.fits_sound(RContents.Content.at(d, RKnown.Known.none(), s, c2, k2), x2)(Ok.head(RKnown.Held{c2, k2, d, x2}, rest, s)(ok)))),
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
        ),
        ef => e => Known.files_ok(
          rest,
          s,
          c,
          k,
          f,
          x
        )(Ok.tail(RKnown.Held{c2, k2, d, x2}, rest, s)(ok))(e)
      )
    case Con{RKnown.Made{+c2, +y2}, +rest}:
      ok => e => Known.files_ok(rest, s, c, k, f, x)(Ok.tail(RKnown.Made{c2, y2}, rest, s)(ok))(e)

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
        %Known.at_ok(kn, s, c, 1n+j)(ok): {RContents.Content.at(1n+f, kn, s, c, 1n+j) == RContents.Content.next(_, RContents.Entry.fits(RKnown.Known.none(), s, c, j, _), RContents.Content.at(f, RKnown.Known.none(), s, c, j), RContents.Content.at(f, RKnown.Known.none(), s, Spec.Point.line(RContents.Entry.taken(c, _)), Spec.Point.n(RContents.Entry.taken(c, _))), RContents.Content.at(f, RKnown.Known.none(), s, Spec.Point.line(RContents.Entry.based(c, _)), Spec.Point.n(RContents.Entry.based(c, _)))): Maybe<&2, RFiles.Files()>}
        %Entry.fits_ok(kn, s, c, j, RKnown.Known.at(kn, s, c, 1n+j))(ok): {RContents.Content.at(1n+f, kn, s, c, 1n+j) == RContents.Content.next(RKnown.Known.at(kn, s, c, 1n+j), _, RContents.Content.at(f, RKnown.Known.none(), s, c, j), RContents.Content.at(f, RKnown.Known.none(), s, Spec.Point.line(RContents.Entry.taken(c, RKnown.Known.at(kn, s, c, 1n+j))), Spec.Point.n(RContents.Entry.taken(c, RKnown.Known.at(kn, s, c, 1n+j)))), RContents.Content.at(f, RKnown.Known.none(), s, Spec.Point.line(RContents.Entry.based(c, RKnown.Known.at(kn, s, c, 1n+j))), Spec.Point.n(RContents.Entry.based(c, RKnown.Known.at(kn, s, c, 1n+j))))): Maybe<&2, RFiles.Files()>}
        %Or.ok(kn, s, c, j, f, RContents.Content.at(f, kn, s, c, j))(ok)(Content.at_ok(f, kn, s, c, j)(ok)): {RContents.Content.at(1n+f, kn, s, c, 1n+j) == RContents.Content.next(RKnown.Known.at(kn, s, c, 1n+j), RContents.Entry.fits(kn, s, c, j, RKnown.Known.at(kn, s, c, 1n+j)), _, RContents.Content.at(f, RKnown.Known.none(), s, Spec.Point.line(RContents.Entry.taken(c, RKnown.Known.at(kn, s, c, 1n+j))), Spec.Point.n(RContents.Entry.taken(c, RKnown.Known.at(kn, s, c, 1n+j)))), RContents.Content.at(f, RKnown.Known.none(), s, Spec.Point.line(RContents.Entry.based(c, RKnown.Known.at(kn, s, c, 1n+j))), Spec.Point.n(RContents.Entry.based(c, RKnown.Known.at(kn, s, c, 1n+j))))): Maybe<&2, RFiles.Files()>}
        %Or.ok(kn, s, Spec.Point.line(RContents.Entry.taken(c, RKnown.Known.at(kn, s, c, 1n+j))), Spec.Point.n(RContents.Entry.taken(c, RKnown.Known.at(kn, s, c, 1n+j))), f, RContents.Content.at(f, kn, s, Spec.Point.line(RContents.Entry.taken(c, RKnown.Known.at(kn, s, c, 1n+j))), Spec.Point.n(RContents.Entry.taken(c, RKnown.Known.at(kn, s, c, 1n+j)))))(ok)(Content.at_ok(f, kn, s, Spec.Point.line(RContents.Entry.taken(c, RKnown.Known.at(kn, s, c, 1n+j))), Spec.Point.n(RContents.Entry.taken(c, RKnown.Known.at(kn, s, c, 1n+j))))(ok)): {RContents.Content.at(1n+f, kn, s, c, 1n+j) == RContents.Content.next(RKnown.Known.at(kn, s, c, 1n+j), RContents.Entry.fits(kn, s, c, j, RKnown.Known.at(kn, s, c, 1n+j)), RContents.Content.or(RKnown.Known.files(kn, c, j, f), u => RContents.Content.at(f, kn, s, c, j)), _, RContents.Content.at(f, RKnown.Known.none(), s, Spec.Point.line(RContents.Entry.based(c, RKnown.Known.at(kn, s, c, 1n+j))), Spec.Point.n(RContents.Entry.based(c, RKnown.Known.at(kn, s, c, 1n+j))))): Maybe<&2, RFiles.Files()>}
        %Or.ok(kn, s, Spec.Point.line(RContents.Entry.based(c, RKnown.Known.at(kn, s, c, 1n+j))), Spec.Point.n(RContents.Entry.based(c, RKnown.Known.at(kn, s, c, 1n+j))), f, RContents.Content.at(f, kn, s, Spec.Point.line(RContents.Entry.based(c, RKnown.Known.at(kn, s, c, 1n+j))), Spec.Point.n(RContents.Entry.based(c, RKnown.Known.at(kn, s, c, 1n+j)))))(ok)(Content.at_ok(f, kn, s, Spec.Point.line(RContents.Entry.based(c, RKnown.Known.at(kn, s, c, 1n+j))), Spec.Point.n(RContents.Entry.based(c, RKnown.Known.at(kn, s, c, 1n+j))))(ok)): {RContents.Content.at(1n+f, kn, s, c, 1n+j) == RContents.Content.next(RKnown.Known.at(kn, s, c, 1n+j), RContents.Entry.fits(kn, s, c, j, RKnown.Known.at(kn, s, c, 1n+j)), RContents.Content.or(RKnown.Known.files(kn, c, j, f), u => RContents.Content.at(f, kn, s, c, j)), RContents.Content.or(RKnown.Known.files(kn, Spec.Point.line(RContents.Entry.taken(c, RKnown.Known.at(kn, s, c, 1n+j))), Spec.Point.n(RContents.Entry.taken(c, RKnown.Known.at(kn, s, c, 1n+j))), f), u => RContents.Content.at(f, kn, s, Spec.Point.line(RContents.Entry.taken(c, RKnown.Known.at(kn, s, c, 1n+j))), Spec.Point.n(RContents.Entry.taken(c, RKnown.Known.at(kn, s, c, 1n+j))))), _): Maybe<&2, RFiles.Files()>}
        {==})

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
  +ok => Or.ok(
    kn,
    s,
    c,
    k,
    RFacts.Facts.fuel(s),
    RContents.Content.at(RFacts.Facts.fuel(s), kn, s, c, k)
  )(ok)(Content.at_ok(RFacts.Facts.fuel(s), kn, s, c, k)(ok))

# What a node learns of the contents
# ----------------------------------

# a right table with a right content is right
def Known.hold_ok(
  kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +e: RKnown.Kept
) -> {
  RContents.Kept.ok(s, e) == True{}: Bool
} -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {RContents.Known.ok(RKnown.Known.hold(kn, e), s) == True{}: Bool}:
  match kn:
    case Nil{}:
      he => ok => Ok.cons(e, [], s)(he)({==})
    case Con{RKnown.Kept{+c, +st}, +rest}:
      he => +ok => Ok.cons(
        RKnown.Kept{c, st},
        RKnown.Known.hold(rest, e),
        s
      )(
        Ok.head(RKnown.Kept{c, st}, rest, s)(ok)
      )(Known.hold_ok(rest, s, e)(he)(Ok.tail(RKnown.Kept{c, st}, rest, s)(ok)))
    case Con{RKnown.Held{+c, +k, +d, +x}, +rest}:
      he => ok => Ok.cons(e, RKnown.Held{c, k, d, x} <> rest, s)(he)(ok)
    case Con{RKnown.Ruled{+c, +u}, +rest}:
      he => +ok => Ok.cons(
        RKnown.Ruled{c, u},
        RKnown.Known.hold(rest, e),
        s
      )(
        Ok.head(RKnown.Ruled{c, u}, rest, s)(ok)
      )(Known.hold_ok(rest, s, e)(he)(Ok.tail(RKnown.Ruled{c, u}, rest, s)(ok)))
    case Con{RKnown.Made{+c, +y}, +rest}:
      he => +ok => Ok.cons(
        RKnown.Made{c, y},
        RKnown.Known.hold(rest, e),
        s
      )(
        Ok.head(RKnown.Made{c, y}, rest, s)(ok)
      )(Known.hold_ok(rest, s, e)(he)(Ok.tail(RKnown.Made{c, y}, rest, s)(ok)))

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
    ef => Known.fill_at_ok(
      RContents.Fill.fuel(k, kn, c, RKnown.Known.at(kn, s, c, k), RFacts.Facts.fuel(s)),
      kn,
      s,
      c,
      k
    )(ok)
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

# a right table with the contents of the versions of a line is right
def Known.warm_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {RContents.Known.ok(RContents.Known.warm(kn, s, c), s) == True{}: Bool}:
  Known.warm_go_ok(RContents.Versions.count(RKnown.Known.versions(kn, s, c)), 0n, kn, s, c)

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
      Known.warm_go_ok(b, 0n, kn, s, c)

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
    Maybe.is_some(
      &2,
      Nat,
      RKnown.Known.depth(kn, c, Nat.sub(RContents.State.count(RKnown.Known.find(old, c)), 1n))
    ),
    RContents.State.count(RKnown.Known.find(old, c)),
    RContents.State.count(RKnown.Known.find(kn, c)),
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
        %Merge.fits_ok(kn, s, c, j, e)(ok): {RAnswers.Clashes.of(kn, s, c, 1n+j, e) == RAnswers.Clashes.at(Bool.and(RContents.Request.is_merge(RAnswers.Entry.request(e)), _), RContents.Content.of(RKnown.Known.none(), s, Spec.Point.line(RContents.Entry.based(c, Some{e})), Spec.Point.n(RContents.Entry.based(c, Some{e}))), RContents.Content.of(RKnown.Known.none(), s, c, j), RContents.Content.of(RKnown.Known.none(), s, Spec.Point.line(RContents.Entry.taken(c, Some{e})), Spec.Point.n(RContents.Entry.taken(c, Some{e})))): Maybe<&2, List<&2, String>>}
        %Content.of_ok(kn, s, Spec.Point.line(RContents.Entry.based(c, Some{e})), Spec.Point.n(RContents.Entry.based(c, Some{e})))(ok): {RAnswers.Clashes.of(kn, s, c, 1n+j, e) == RAnswers.Clashes.at(Bool.and(RContents.Request.is_merge(RAnswers.Entry.request(e)), RContents.Merge.fits(kn, s, c, j, e)), _, RContents.Content.of(RKnown.Known.none(), s, c, j), RContents.Content.of(RKnown.Known.none(), s, Spec.Point.line(RContents.Entry.taken(c, Some{e})), Spec.Point.n(RContents.Entry.taken(c, Some{e})))): Maybe<&2, List<&2, String>>}
        %Content.of_ok(kn, s, c, j)(ok): {RAnswers.Clashes.of(kn, s, c, 1n+j, e) == RAnswers.Clashes.at(Bool.and(RContents.Request.is_merge(RAnswers.Entry.request(e)), RContents.Merge.fits(kn, s, c, j, e)), RContents.Content.of(kn, s, Spec.Point.line(RContents.Entry.based(c, Some{e})), Spec.Point.n(RContents.Entry.based(c, Some{e}))), _, RContents.Content.of(RKnown.Known.none(), s, Spec.Point.line(RContents.Entry.taken(c, Some{e})), Spec.Point.n(RContents.Entry.taken(c, Some{e})))): Maybe<&2, List<&2, String>>}
        %Content.of_ok(kn, s, Spec.Point.line(RContents.Entry.taken(c, Some{e})), Spec.Point.n(RContents.Entry.taken(c, Some{e})))(ok): {RAnswers.Clashes.of(kn, s, c, 1n+j, e) == RAnswers.Clashes.at(Bool.and(RContents.Request.is_merge(RAnswers.Entry.request(e)), RContents.Merge.fits(kn, s, c, j, e)), RContents.Content.of(kn, s, Spec.Point.line(RContents.Entry.based(c, Some{e})), Spec.Point.n(RContents.Entry.based(c, Some{e}))), RContents.Content.of(kn, s, c, j), _): Maybe<&2, List<&2, String>>}
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

# a right table changes no search of a request
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
    == RAnswers.Line.find(RKnown.Known.none(), s, c, i): Maybe<&2, RAnswers.Found>
}:
  ok => Equal.cong(
    Maybe<&2, List<&2, Types.Entry>>,
    Maybe<&2, RAnswers.Found>,
    m => RAnswers.Line.find.of(i, m),
    RKnown.Known.versions(kn, s, c),
    RLines.Line.versions(s, c),
    Known.versions_ok(kn, s, c)(ok)
  )

# a right table changes no reply with a status
def Reply.status_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  v: Maybe<&2, List<&2, Types.Entry>>,
  m: Maybe<&2, RAnswers.Found>
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
    case Some{+vs} Some{RAnswers.Found{+k, +e}}:
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
  m: Maybe<&2, RAnswers.Found>
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
    case Some{RAnswers.Found{+k, +e}}:
      ok => Clashes.of_ok(kn, s, c, k, e)(ok)

# a right table changes no base of a found merge
def Base.then_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  m: Maybe<&2, RAnswers.Found>
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
    case Some{RAnswers.Found{+k, +e}}:
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
      ok => (
        %Known.versions_ok(kn, s, c)(ok): {RAnswers.Answer.of(kn, s, Spec.Question.Count{c}) == RAnswers.Reply.count(_): Maybe<&2, Spec.Reply>}
        {==})
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
def View.of_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +b: Ledgers.Line,
  +p: String,
  m: Maybe<&2, Types.Ask>
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
  match m:
    case None{}:
      +ok => (
        %Known.versions_ok(kn, s, b)(ok): {RAnswers.View.of(kn, s, b, p, None{}) == RAnswers.View.newest(RKnown.Known.none(), s, b, p, _): Maybe<&2, Maybe<&2, List<&2, U32>>>}
        View.newest_ok(kn, s, b, p, RKnown.Known.versions(kn, s, b))(ok))
    case Some{+a}:
      +ok => (
        %Known.versions_ok(kn, s, b)(ok): {RAnswers.View.of(kn, s, b, p, Some{a}) == Shared.Bool.when(Maybe<&2, Maybe<&2, List<&2, U32>>>, RAnswers.View.decided(a, _), u => RAnswers.View.newest(RKnown.Known.none(), s, b, p, _), u => Some{RAnswers.Request.words(RLines.Ask.request(a))}): Maybe<&2, Maybe<&2, List<&2, U32>>>}
        %View.newest_ok(kn, s, b, p, RKnown.Known.versions(kn, s, b))(ok): {RAnswers.View.of(kn, s, b, p, Some{a}) == Shared.Bool.when(Maybe<&2, Maybe<&2, List<&2, U32>>>, RAnswers.View.decided(a, RKnown.Known.versions(kn, s, b)), u => _, u => Some{RAnswers.Request.words(RLines.Ask.request(a))}): Maybe<&2, Maybe<&2, List<&2, U32>>>}
        {==})

# a right table changes no view
def View.at_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +w: String,
  +b: Ledgers.Line,
  +p: String
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
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
  ok => View.of_ok(
    kn,
    s,
    b,
    p,
    Lists.List.top(
      ~Types.Ask,
      ~RFacts.Ask.seq,
      RAnswers.Writes.of(RFacts.Facts.list(s), RAnswers.Place{w, b, p})
    )
  )(ok)

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
  +X: RLines.State,
  +e2: {Lines.Line.step(s, r, c, st) == Some{st2}: Maybe<&2, RLines.State>},
  lt: {Nat.is_le(1n+RLines.State.slot(st), RLines.State.slot(X)) == True{}: Bool},
  ih: @f3: Nat -> {
    Nat.is_lt(RLines.State.slot(X), Nat.add(f3, RLines.State.slot(st2))) == True{}: Bool
  } -> {
    Nat.is_lt(
      RLines.Line.bound(
        Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(X), t, x}, s)),
        c
      ),
      Nat.add(f3, RLines.State.slot(st2))
    )
      == True{}: Bool
  } -> {
    Lines.Line.run(
      f3,
      Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(X), t, x}, s),
      r,
      c,
      st2,
      Lines.Line.step(
        Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(X), t, x}, s),
        r,
        c,
        st2
      )
    )
      == Lines.Line.run(
        1n+RLines.Line.bound(
          Facts.Facts.list(
            Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(X), t, x}, s)
          ),
          c
        ),
        Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(X), t, x}, s),
        r,
        c,
        X,
        Lines.Line.step(
          Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(X), t, x}, s),
          r,
          c,
          X
        )
      ): RLines.State
  }
) -> {
  Nat.is_lt(RLines.State.slot(X), Nat.add(f2, RLines.State.slot(st))) == True{}: Bool
} -> {
  Nat.is_lt(
    RLines.Line.bound(
      Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(X), t, x}, s)),
      c
    ),
    Nat.add(f2, RLines.State.slot(st))
  )
    == True{}: Bool
} -> {
  Lines.Line.run(
    f2,
    Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(X), t, x}, s),
    r,
    c,
    st,
    Lines.Line.step(
      Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(X), t, x}, s),
      r,
      c,
      st
    )
  )
    == Lines.Line.run(
      1n+RLines.Line.bound(
        Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(X), t, x}, s)),
        c
      ),
      Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(X), t, x}, s),
      r,
      c,
      X,
      Lines.Line.step(
        Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(X), t, x}, s),
        r,
        c,
        X
      )
    ): RLines.State
}:
  match f2:
    case 0n:
      hv => hw => Lists.Bool.clash(
        {
          Lines.Line.run(
            0n,
            Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(X), t, x}, s),
            r,
            c,
            st,
            Lines.Line.step(
              Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(X), t, x}, s),
              r,
              c,
              st
            )
          )
            == Lines.Line.run(
              1n+RLines.Line.bound(
                Facts.Facts.list(
                  Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(X), t, x}, s)
                ),
                c
              ),
              Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(X), t, x}, s),
              r,
              c,
              X,
              Lines.Line.step(
                Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(X), t, x}, s),
                r,
                c,
                X
              )
            ): RLines.State
        },
        Nat.is_lt(RLines.State.slot(X), RLines.State.slot(st)),
        Shared.Nat.le_nlt(
          RLines.State.slot(st),
          RLines.State.slot(X)
        )(
          Shared.Nat.le_trans(
            RLines.State.slot(st),
            1n+RLines.State.slot(st),
            RLines.State.slot(X)
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
        %Equal.sym(Maybe<&2, RLines.State>, Lines.Line.step(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(X), t, x}, s), r, c, st), Some{st2}, Equal.trans(Maybe<&2, RLines.State>, Lines.Line.step(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(X), t, x}, s), r, c, st), Lines.Line.step(s, r, c, st), Some{st2}, Moves.Step.kept.at(Moves.Delta.Vote{name, c, RLines.State.slot(X), t, x}, s, c, st, RLines.Line.rule(r, c, RLines.State.versions(st)))(Cast.keeps(name, c, RLines.State.slot(X), t, x, RLines.State.slot(st))(lt)), e2)): {Lines.Line.run(1n+p, Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(X), t, x}, s), r, c, st, _) == Lines.Line.run(1n+RLines.Line.bound(Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(X), t, x}, s)), c), Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(X), t, x}, s), r, c, X, Lines.Line.step(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(X), t, x}, s), r, c, X)): RLines.State}
        ih(p)(
        %Equal.sym(Nat, RLines.State.slot(st2), 1n+RLines.State.slot(st), Moves.Next.slot(st, st2, Moves.Step.next(s, r, c, st, st2)(e2))): {Nat.is_lt(RLines.State.slot(X), Nat.add(p, _)) == True{}: Bool}
        %Equal.sym(Nat, Nat.add(p, 1n+RLines.State.slot(st)), 1n+Nat.add(p, RLines.State.slot(st)), Shared.Nat.add_succ(p, RLines.State.slot(st))): {Nat.is_lt(RLines.State.slot(X), _) == True{}: Bool}
        hv)(
        %Equal.sym(Nat, RLines.State.slot(st2), 1n+RLines.State.slot(st), Moves.Next.slot(st, st2, Moves.Step.next(s, r, c, st, st2)(e2))): {Nat.is_lt(RLines.Line.bound(Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(X), t, x}, s)), c), Nat.add(p, _)) == True{}: Bool}
        %Equal.sym(Nat, Nat.add(p, 1n+RLines.State.slot(st)), 1n+Nat.add(p, RLines.State.slot(st)), Shared.Nat.add_succ(p, RLines.State.slot(st))): {Nat.is_lt(RLines.Line.bound(Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(X), t, x}, s)), c), _) == True{}: Bool}
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
# has the versions R, the state of the branch is the run continued from st
def Branch.state_cast(
  +name: String,
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +b: String,
  +t: Nat,
  +x: Types.Cast,
  +R: List<&2, Types.Entry>,
  +j: Nat,
  +st: RLines.State
) -> {
  Lines.Line.state(s, Ledgers.Line{h, Some{b}}) == Some{st}: Maybe<&2, RLines.State>
} -> {
  Lines.Store.state(s, h) == Some{RLines.State{R, j}}: Maybe<&2, RLines.State>
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
        Some{R}
      )
    }: Maybe<&2, RLines.State>
}:
  e => +es => (
    %Equal.sym(Maybe<&2, RLines.State>, Lines.Store.state(Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, Some{b}}, RLines.State.slot(st), t, x}, s), h), Lines.Store.state(s, h), Moves.Store.same(Moves.Delta.Vote{name, Ledgers.Line{h, Some{b}}, RLines.State.slot(st), t, x}, s, h)({==})(
      %Equal.sym(Bool, Ledgers.Line.is_eq(Ledgers.Line{h, None{}}, Ledgers.Line{h, Some{b}}), False{}, Moves.Line.root_ne(h, b)): {Bool.not(_) == True{}: Bool}
      {==})): {Lines.Branch.state(Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, Some{b}}, RLines.State.slot(st), t, x}, s), Ledgers.Line{h, Some{b}}, Maybe.map(&2, RLines.State, List<&2, Types.Entry>, RLines.State.versions, _)) == Some{RKnown.Known.go.at(Facts.Facts.crit(Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, Some{b}}, RLines.State.slot(st), t, x}, s)), Ledgers.Line{h, Some{b}}, st, Some{R})}: Maybe<&2, RLines.State>}
    %Equal.sym(Maybe<&2, RLines.State>, Lines.Store.state(s, h), Some{RLines.State{R, j}}, es): {Lines.Branch.state(Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, Some{b}}, RLines.State.slot(st), t, x}, s), Ledgers.Line{h, Some{b}}, Maybe.map(&2, RLines.State, List<&2, Types.Entry>, RLines.State.versions, _)) == Some{RKnown.Known.go.at(Facts.Facts.crit(Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, Some{b}}, RLines.State.slot(st), t, x}, s)), Ledgers.Line{h, Some{b}}, st, Some{R})}: Maybe<&2, RLines.State>}
    From.cast(name, s, Ledgers.Line{h, Some{b}}, t, x, Some{R}, RLines.Branch.first(R, Ledgers.Line{h, Some{b}}), st)(Equal.trans(Maybe<&2, RLines.State>, Lines.Branch.state(s, Ledgers.Line{h, Some{b}}, Some{R}), Lines.Line.state(s, Ledgers.Line{h, Some{b}}), Some{st}, Equal.cong(Maybe<&2, RLines.State>, Maybe<&2, RLines.State>, m => Lines.Branch.state(s, Ledgers.Line{h, Some{b}}, Maybe.map(&2, RLines.State, List<&2, Types.Entry>, RLines.State.versions, m)), Some{RLines.State{R, j}}, Lines.Store.state(s, h), Equal.sym(Maybe<&2, RLines.State>, Lines.Store.state(s, h), Some{RLines.State{R, j}}, es)), e)))

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
  +R: List<&2, Types.Entry>,
  +j: Nat,
  +st: RLines.State,
  +i: Nat,
  -e: Types.Entry
) -> {
  Lines.Line.state(s, Ledgers.Line{h, Some{b}}) == Some{st}: Maybe<&2, RLines.State>
} -> {
  Lines.Store.state(s, h) == Some{RLines.State{R, j}}: Maybe<&2, RLines.State>
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
    %Equal.sym(Maybe<&2, RLines.State>, Lines.Line.state(Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, Some{b}}, RLines.State.slot(st), t, x}, s), Ledgers.Line{h, Some{b}}), Some{RKnown.Known.go.at(Facts.Facts.crit(Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, Some{b}}, RLines.State.slot(st), t, x}, s)), Ledgers.Line{h, Some{b}}, st, Some{R})}, Branch.state_cast(name, s, h, b, t, x, R, j, st)(em)(es)): {RLines.Line.at.of(Maybe.map(&2, RLines.State, List<&2, Types.Entry>, RLines.State.versions, _), i) == Some{e}: Maybe<&2, Types.Entry>}
    Lists.List.ext_get.of(Types.Entry, RLines.State.versions(st), RLines.State.versions(RKnown.Known.go.at(Facts.Facts.crit(Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, Some{b}}, RLines.State.slot(st), t, x}, s)), Ledgers.Line{h, Some{b}}, st, Some{R})), i, e, Versions.Run.keeps(~List<&2, Types.Entry>, ~Versions.Run.Ext, ~Versions.Run.ext_step, 1n+RLines.Line.bound(Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, Some{b}}, RLines.State.slot(st), t, x}, s)), Ledgers.Line{h, Some{b}}), RLines.State.versions(st), Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, Some{b}}, RLines.State.slot(st), t, x}, s), Some{R}, Ledgers.Line{h, Some{b}}, st, Lists.List.ext_refl(Types.Entry, RLines.State.versions(st))), (
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
    case Con{RKnown.Ruled{+c, +u}, +rest}:
      ok => Known.contents_ok(rest, s)(Ok.tail(RKnown.Ruled{c, u}, rest, s)(ok))
    case Con{RKnown.Held{+c, +k, +f, +x}, +rest}:
      +ok => Ok.cons(
        RKnown.Held{c, k, f, x},
        RKnown.Known.contents(rest),
        s
      )(
        Ok.head(RKnown.Held{c, k, f, x}, rest, s)(ok)
      )(Known.contents_ok(rest, s)(Ok.tail(RKnown.Held{c, k, f, x}, rest, s)(ok)))
    case Con{RKnown.Made{+c, +y}, +rest}:
      ok => Known.contents_ok(rest, s)(Ok.tail(RKnown.Made{c, y}, rest, s)(ok))

# the contents of a table that is right for the facts s are right when a
# node adds what is safe
def Known.contents_kept(
  kn: RKnown.Known(),
  +d: Moves.Delta,
  +s: Facts.Facts()
) -> {
  Delta.safe(d, s) == True{}: Bool
} -> {
  RContents.Known.ok(kn, Facts.Facts.crit(s)) == True{}: Bool
} -> {
  RContents.Known.ok(
    RKnown.Known.contents(kn),
    Facts.Facts.crit(Moves.Delta.to(d, s))
  )
    == True{}: Bool
}:
  match kn:
    case Nil{}:
      hs => ok => {==}
    case Con{RKnown.Kept{+c, +st}, +rest}:
      hs => ok => Known.contents_kept(
        rest,
        d,
        s
      )(hs)(Ok.tail(RKnown.Kept{c, st}, rest, Facts.Facts.crit(s))(ok))
    case Con{RKnown.Ruled{+c, +u}, +rest}:
      hs => ok => Known.contents_kept(
        rest,
        d,
        s
      )(hs)(Ok.tail(RKnown.Ruled{c, u}, rest, Facts.Facts.crit(s))(ok))
    case Con{RKnown.Held{+c, +k, +f, +x}, +rest}:
      +hs => +ok => Ok.cons(
        RKnown.Held{c, k, f, x},
        RKnown.Known.contents(rest),
        Facts.Facts.crit(Moves.Delta.to(d, s))
      )(
        Held.kept(
          d,
          s,
          c,
          k,
          f,
          x
        )(hs)(Ok.head(RKnown.Held{c, k, f, x}, rest, Facts.Facts.crit(s))(ok))
      )(
        Known.contents_kept(
          rest,
          d,
          s
        )(hs)(Ok.tail(RKnown.Held{c, k, f, x}, rest, Facts.Facts.crit(s))(ok))
      )
    case Con{RKnown.Made{+c, +y}, +rest}:
      hs => ok => Known.contents_kept(
        rest,
        d,
        s
      )(hs)(Ok.tail(RKnown.Made{c, y}, rest, Facts.Facts.crit(s))(ok))

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
    case Con{RKnown.Held{+c, +k, +f, +x}, +rest}:
      +e => +ok => Ok.cons(
        RKnown.Held{c, k, f, x},
        rest,
        Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{a}))
      )(Held.kept(Moves.Delta.Ask{name, a}, s, c, k, f, x)(
          %Equal.sym(Bool, RFacts.Request.is_start(RLines.Ask.request(a)), False{}, e): {Bool.not(_) == True{}: Bool}
          {==})(Ok.head(RKnown.Held{c, k, f, x}, rest, Facts.Facts.crit(s))(ok)))(
        Known.asked_ok(
          rest,
          name,
          s,
          a
        )(e)(Ok.tail(RKnown.Held{c, k, f, x}, rest, Facts.Facts.crit(s))(ok))
      )
    case Con{RKnown.Ruled{+c, +u}, +rest}:
      +e => +ok => Ok.cons(
        RKnown.Ruled{c, u},
        rest,
        Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{a}))
      )(
        Ruled.same(
          s,
          Facts.Facts.take(name, s, Types.Fact.Ask{a}),
          c,
          u
        )(
          Moves.Line.state_asked(name, s, a, c)(e)
        )(
          Moves.Line.state_asked(name, s, a, RKnown.Known.root(c))(e)
        )(Ok.head(RKnown.Ruled{c, u}, rest, Facts.Facts.crit(s))(ok))
      )(
        Known.asked_ok(
          rest,
          name,
          s,
          a
        )(e)(Ok.tail(RKnown.Ruled{c, u}, rest, Facts.Facts.crit(s))(ok))
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
  +ok => Lists.Bool.by(
    y => {
      RContents.Known.ok(
        RKnown.Known.spared(y, kn),
        Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))
      )
        == True{}: Bool
    },
    RKnown.Known.safe(c, RKnown.Known.find(kn, c), RKnown.Known.find(kn, RKnown.Known.root(c)), k),
    et => Known.contents_kept(
      kn,
      Moves.Delta.Vote{name, c, k, t, x},
      s
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
    )(ok),
    ef => {==}
  )

# the ids m, if any, fit the state x
def Made.Ok(x: Maybe<&2, RLines.State>, m: Maybe<&2, RKnown.Ids()>) -> Type:
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
  m: Maybe<&2, RKnown.Ids()>
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
    RKnown.Ids(),
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
  +y: RKnown.Ids(),
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
        RKnown.Ids(),
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
        Crits.Crit.new(List<&2, Ledgers.Id>)
      ): {RKnown.Ids.same(_, RKnown.Ids.of(List.append(&2, Types.Entry, vs, zs))) == True{}: Bool}
      Ids.same_refl(RKnown.Ids.of(List.append(&2, Types.Entry, vs, zs)))

# the ids that a vote continues fit the state after the vote: m is the state
# x2 after the vote, old the state x1 before it, that m extends, and ids fit
# x1
def Made.next_ok(
  m: Maybe<&2, RLines.State>,
  old: Maybe<&2, RLines.State>,
  ids: Maybe<&2, RKnown.Ids()>,
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
  RContents.Known.ok(
    RKnown.Known.cast(
      kn,
      Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})),
      c,
      k
    ),
    Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))
  )
    == True{}: Bool
}:
  +ok => Known.made_put_ok(
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
      )(Known.voted_ok(kn, name, s, c, k, t, x)(ok))(Known.spared_ok(kn, name, s, c, k, t, x)(ok))
    )
  )
