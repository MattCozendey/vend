import Base
import ../shared/shared/ledger.bend as Ledgers
import ../shared/shared/shared/shared/hash.bend as Hashes
import ../shared/shared/shared/shared/shared.bend as Shared
import ../shared/shared/shared/text.bend as Texts
import ./answers.bend as Answers
import ./content.bend as Contents
import ./facts.bend as Facts
import ./groups.bend as Groups
import ./lines.bend as Lines
import ./reads.bend as Reads
import ./rounds.bend as Rounds
import ./run/answers.bend as RAnswers
import ./run/content.bend as RContents
import ./run/files.bend as Files
import ./run/known.bend as RKnown
import ./run/lines.bend as RLines
import ./run/rounds.bend as RRounds
import ./shared/lists.bend as Lists
import ./spec.bend as Spec
import ./stays.bend as Stays
import ./types.bend as Types

# Answers move forward
# --------------------
# As the facts of a node grow, a reply that it gave stays, but for the count
# of a line, which may grow, and a status, which may go from Conflicted to
# Written. Premises, each an equation: hw says that s2 is wider than s, hl
# that s2 names no liar, ho that s2 is sound for the node name.

# P holds of a, when it holds of what a is equal to
def Eq.up(-A: Type, -P: A -> Type, -a: A, -b: A, e: {a == b: A}, x: P(b)) -> P(a):
  %Equal.sym(A, a, b, e): P(_)
  x

# a status follows itself
def Status.follows_refl(x: Spec.Status) -> {Spec.Status.follows(x, x) == True{}: Bool}:
  match x:
    case Spec.Status.Written{}:
      {==}
    case Spec.Status.Conflicted{i}:
      Ledgers.Id.is_eq_refl(i)
    case Spec.Status.Stale{}:
      {==}
    case Spec.Status.Refused{}:
      {==}

# a reply moves to itself
def Reply.moves_refl(q: Spec.Question, a: Spec.Reply) -> Spec.Reply.Moves(q, a, a):
  match q a:
    case Spec.Question.Status{q0, q1} Spec.Reply.Status{x}:
      Status.follows_refl(x)
    case Spec.Question.Status{q0, q1} Spec.Reply.Ask{x}:
      {==}
    case Spec.Question.Status{q0, q1} Spec.Reply.Id{x}:
      {==}
    case Spec.Question.Status{q0, q1} Spec.Reply.Hash{x}:
      {==}
    case Spec.Question.Status{q0, q1} Spec.Reply.Names{x}:
      {==}
    case Spec.Question.Status{q0, q1} Spec.Reply.Number{x}:
      {==}
    case Spec.Question.Status{q0, q1} Spec.Reply.Yes{x}:
      {==}
    case Spec.Question.Status{q0, q1} Spec.Reply.Name{x}:
      {==}
    case Spec.Question.Status{q0, q1} Spec.Reply.Point{x}:
      {==}
    case Spec.Question.Status{q0, q1} Spec.Reply.Points{x}:
      {==}
    case Spec.Question.Request{q0, q1} Spec.Reply.Status{x}:
      Status.follows_refl(x)
    case Spec.Question.Request{q0, q1} Spec.Reply.Ask{x}:
      {==}
    case Spec.Question.Request{q0, q1} Spec.Reply.Id{x}:
      {==}
    case Spec.Question.Request{q0, q1} Spec.Reply.Hash{x}:
      {==}
    case Spec.Question.Request{q0, q1} Spec.Reply.Names{x}:
      {==}
    case Spec.Question.Request{q0, q1} Spec.Reply.Number{x}:
      {==}
    case Spec.Question.Request{q0, q1} Spec.Reply.Yes{x}:
      {==}
    case Spec.Question.Request{q0, q1} Spec.Reply.Name{x}:
      {==}
    case Spec.Question.Request{q0, q1} Spec.Reply.Point{x}:
      {==}
    case Spec.Question.Request{q0, q1} Spec.Reply.Points{x}:
      {==}
    case Spec.Question.Version{q0, q1} Spec.Reply.Status{x}:
      Status.follows_refl(x)
    case Spec.Question.Version{q0, q1} Spec.Reply.Ask{x}:
      {==}
    case Spec.Question.Version{q0, q1} Spec.Reply.Id{x}:
      {==}
    case Spec.Question.Version{q0, q1} Spec.Reply.Hash{x}:
      {==}
    case Spec.Question.Version{q0, q1} Spec.Reply.Names{x}:
      {==}
    case Spec.Question.Version{q0, q1} Spec.Reply.Number{x}:
      {==}
    case Spec.Question.Version{q0, q1} Spec.Reply.Yes{x}:
      {==}
    case Spec.Question.Version{q0, q1} Spec.Reply.Name{x}:
      {==}
    case Spec.Question.Version{q0, q1} Spec.Reply.Point{x}:
      {==}
    case Spec.Question.Version{q0, q1} Spec.Reply.Points{x}:
      {==}
    case Spec.Question.Content{q0, q1} Spec.Reply.Status{x}:
      Status.follows_refl(x)
    case Spec.Question.Content{q0, q1} Spec.Reply.Ask{x}:
      {==}
    case Spec.Question.Content{q0, q1} Spec.Reply.Id{x}:
      {==}
    case Spec.Question.Content{q0, q1} Spec.Reply.Hash{x}:
      {==}
    case Spec.Question.Content{q0, q1} Spec.Reply.Names{x}:
      {==}
    case Spec.Question.Content{q0, q1} Spec.Reply.Number{x}:
      {==}
    case Spec.Question.Content{q0, q1} Spec.Reply.Yes{x}:
      {==}
    case Spec.Question.Content{q0, q1} Spec.Reply.Name{x}:
      {==}
    case Spec.Question.Content{q0, q1} Spec.Reply.Point{x}:
      {==}
    case Spec.Question.Content{q0, q1} Spec.Reply.Points{x}:
      {==}
    case Spec.Question.Group{q0, q1} Spec.Reply.Status{x}:
      Status.follows_refl(x)
    case Spec.Question.Group{q0, q1} Spec.Reply.Ask{x}:
      {==}
    case Spec.Question.Group{q0, q1} Spec.Reply.Id{x}:
      {==}
    case Spec.Question.Group{q0, q1} Spec.Reply.Hash{x}:
      {==}
    case Spec.Question.Group{q0, q1} Spec.Reply.Names{x}:
      {==}
    case Spec.Question.Group{q0, q1} Spec.Reply.Number{x}:
      {==}
    case Spec.Question.Group{q0, q1} Spec.Reply.Yes{x}:
      {==}
    case Spec.Question.Group{q0, q1} Spec.Reply.Name{x}:
      {==}
    case Spec.Question.Group{q0, q1} Spec.Reply.Point{x}:
      {==}
    case Spec.Question.Group{q0, q1} Spec.Reply.Points{x}:
      {==}
    case Spec.Question.Owners{q0, q1} Spec.Reply.Status{x}:
      Status.follows_refl(x)
    case Spec.Question.Owners{q0, q1} Spec.Reply.Ask{x}:
      {==}
    case Spec.Question.Owners{q0, q1} Spec.Reply.Id{x}:
      {==}
    case Spec.Question.Owners{q0, q1} Spec.Reply.Hash{x}:
      {==}
    case Spec.Question.Owners{q0, q1} Spec.Reply.Names{x}:
      {==}
    case Spec.Question.Owners{q0, q1} Spec.Reply.Number{x}:
      {==}
    case Spec.Question.Owners{q0, q1} Spec.Reply.Yes{x}:
      {==}
    case Spec.Question.Owners{q0, q1} Spec.Reply.Name{x}:
      {==}
    case Spec.Question.Owners{q0, q1} Spec.Reply.Point{x}:
      {==}
    case Spec.Question.Owners{q0, q1} Spec.Reply.Points{x}:
      {==}
    case Spec.Question.Members{q0, q1, q2} Spec.Reply.Status{x}:
      Status.follows_refl(x)
    case Spec.Question.Members{q0, q1, q2} Spec.Reply.Ask{x}:
      {==}
    case Spec.Question.Members{q0, q1, q2} Spec.Reply.Id{x}:
      {==}
    case Spec.Question.Members{q0, q1, q2} Spec.Reply.Hash{x}:
      {==}
    case Spec.Question.Members{q0, q1, q2} Spec.Reply.Names{x}:
      {==}
    case Spec.Question.Members{q0, q1, q2} Spec.Reply.Number{x}:
      {==}
    case Spec.Question.Members{q0, q1, q2} Spec.Reply.Yes{x}:
      {==}
    case Spec.Question.Members{q0, q1, q2} Spec.Reply.Name{x}:
      {==}
    case Spec.Question.Members{q0, q1, q2} Spec.Reply.Point{x}:
      {==}
    case Spec.Question.Members{q0, q1, q2} Spec.Reply.Points{x}:
      {==}
    case Spec.Question.Nodes{q0, q1, q2} Spec.Reply.Status{x}:
      Status.follows_refl(x)
    case Spec.Question.Nodes{q0, q1, q2} Spec.Reply.Ask{x}:
      {==}
    case Spec.Question.Nodes{q0, q1, q2} Spec.Reply.Id{x}:
      {==}
    case Spec.Question.Nodes{q0, q1, q2} Spec.Reply.Hash{x}:
      {==}
    case Spec.Question.Nodes{q0, q1, q2} Spec.Reply.Names{x}:
      {==}
    case Spec.Question.Nodes{q0, q1, q2} Spec.Reply.Number{x}:
      {==}
    case Spec.Question.Nodes{q0, q1, q2} Spec.Reply.Yes{x}:
      {==}
    case Spec.Question.Nodes{q0, q1, q2} Spec.Reply.Name{x}:
      {==}
    case Spec.Question.Nodes{q0, q1, q2} Spec.Reply.Point{x}:
      {==}
    case Spec.Question.Nodes{q0, q1, q2} Spec.Reply.Points{x}:
      {==}
    case Spec.Question.IsGroup{q0, q1, q2} Spec.Reply.Status{x}:
      Status.follows_refl(x)
    case Spec.Question.IsGroup{q0, q1, q2} Spec.Reply.Ask{x}:
      {==}
    case Spec.Question.IsGroup{q0, q1, q2} Spec.Reply.Id{x}:
      {==}
    case Spec.Question.IsGroup{q0, q1, q2} Spec.Reply.Hash{x}:
      {==}
    case Spec.Question.IsGroup{q0, q1, q2} Spec.Reply.Names{x}:
      {==}
    case Spec.Question.IsGroup{q0, q1, q2} Spec.Reply.Number{x}:
      {==}
    case Spec.Question.IsGroup{q0, q1, q2} Spec.Reply.Yes{x}:
      {==}
    case Spec.Question.IsGroup{q0, q1, q2} Spec.Reply.Name{x}:
      {==}
    case Spec.Question.IsGroup{q0, q1, q2} Spec.Reply.Point{x}:
      {==}
    case Spec.Question.IsGroup{q0, q1, q2} Spec.Reply.Points{x}:
      {==}
    case Spec.Question.Mark{q0, q1} Spec.Reply.Status{x}:
      Status.follows_refl(x)
    case Spec.Question.Mark{q0, q1} Spec.Reply.Ask{x}:
      {==}
    case Spec.Question.Mark{q0, q1} Spec.Reply.Id{x}:
      {==}
    case Spec.Question.Mark{q0, q1} Spec.Reply.Hash{x}:
      {==}
    case Spec.Question.Mark{q0, q1} Spec.Reply.Names{x}:
      {==}
    case Spec.Question.Mark{q0, q1} Spec.Reply.Number{x}:
      {==}
    case Spec.Question.Mark{q0, q1} Spec.Reply.Yes{x}:
      {==}
    case Spec.Question.Mark{q0, q1} Spec.Reply.Name{x}:
      {==}
    case Spec.Question.Mark{q0, q1} Spec.Reply.Point{x}:
      {==}
    case Spec.Question.Mark{q0, q1} Spec.Reply.Points{x}:
      {==}
    case Spec.Question.Count{q0} Spec.Reply.Status{x}:
      Status.follows_refl(x)
    case Spec.Question.Count{q0} Spec.Reply.Ask{x}:
      {==}
    case Spec.Question.Count{q0} Spec.Reply.Id{x}:
      {==}
    case Spec.Question.Count{q0} Spec.Reply.Hash{x}:
      {==}
    case Spec.Question.Count{q0} Spec.Reply.Names{x}:
      {==}
    case Spec.Question.Count{q0} Spec.Reply.Number{x}:
      Shared.Nat.le_refl(x)
    case Spec.Question.Count{q0} Spec.Reply.Yes{x}:
      {==}
    case Spec.Question.Count{q0} Spec.Reply.Name{x}:
      {==}
    case Spec.Question.Count{q0} Spec.Reply.Point{x}:
      {==}
    case Spec.Question.Count{q0} Spec.Reply.Points{x}:
      {==}
    case Spec.Question.Clashes{q0, q1} Spec.Reply.Status{x}:
      Status.follows_refl(x)
    case Spec.Question.Clashes{q0, q1} Spec.Reply.Ask{x}:
      {==}
    case Spec.Question.Clashes{q0, q1} Spec.Reply.Id{x}:
      {==}
    case Spec.Question.Clashes{q0, q1} Spec.Reply.Hash{x}:
      {==}
    case Spec.Question.Clashes{q0, q1} Spec.Reply.Names{x}:
      {==}
    case Spec.Question.Clashes{q0, q1} Spec.Reply.Number{x}:
      {==}
    case Spec.Question.Clashes{q0, q1} Spec.Reply.Yes{x}:
      {==}
    case Spec.Question.Clashes{q0, q1} Spec.Reply.Name{x}:
      {==}
    case Spec.Question.Clashes{q0, q1} Spec.Reply.Point{x}:
      {==}
    case Spec.Question.Clashes{q0, q1} Spec.Reply.Points{x}:
      {==}
    case Spec.Question.Affects{q0, q1, q2, q3, q4} Spec.Reply.Status{x}:
      Status.follows_refl(x)
    case Spec.Question.Affects{q0, q1, q2, q3, q4} Spec.Reply.Ask{x}:
      {==}
    case Spec.Question.Affects{q0, q1, q2, q3, q4} Spec.Reply.Id{x}:
      {==}
    case Spec.Question.Affects{q0, q1, q2, q3, q4} Spec.Reply.Hash{x}:
      {==}
    case Spec.Question.Affects{q0, q1, q2, q3, q4} Spec.Reply.Names{x}:
      {==}
    case Spec.Question.Affects{q0, q1, q2, q3, q4} Spec.Reply.Number{x}:
      {==}
    case Spec.Question.Affects{q0, q1, q2, q3, q4} Spec.Reply.Yes{x}:
      {==}
    case Spec.Question.Affects{q0, q1, q2, q3, q4} Spec.Reply.Name{x}:
      {==}
    case Spec.Question.Affects{q0, q1, q2, q3, q4} Spec.Reply.Point{x}:
      {==}
    case Spec.Question.Affects{q0, q1, q2, q3, q4} Spec.Reply.Points{x}:
      {==}
    case Spec.Question.Parents{q0, q1} Spec.Reply.Status{x}:
      Status.follows_refl(x)
    case Spec.Question.Parents{q0, q1} Spec.Reply.Ask{x}:
      {==}
    case Spec.Question.Parents{q0, q1} Spec.Reply.Id{x}:
      {==}
    case Spec.Question.Parents{q0, q1} Spec.Reply.Hash{x}:
      {==}
    case Spec.Question.Parents{q0, q1} Spec.Reply.Names{x}:
      {==}
    case Spec.Question.Parents{q0, q1} Spec.Reply.Number{x}:
      {==}
    case Spec.Question.Parents{q0, q1} Spec.Reply.Yes{x}:
      {==}
    case Spec.Question.Parents{q0, q1} Spec.Reply.Name{x}:
      {==}
    case Spec.Question.Parents{q0, q1} Spec.Reply.Point{x}:
      {==}
    case Spec.Question.Parents{q0, q1} Spec.Reply.Points{x}:
      {==}
    case Spec.Question.Base{q0, q1} Spec.Reply.Status{x}:
      Status.follows_refl(x)
    case Spec.Question.Base{q0, q1} Spec.Reply.Ask{x}:
      {==}
    case Spec.Question.Base{q0, q1} Spec.Reply.Id{x}:
      {==}
    case Spec.Question.Base{q0, q1} Spec.Reply.Hash{x}:
      {==}
    case Spec.Question.Base{q0, q1} Spec.Reply.Names{x}:
      {==}
    case Spec.Question.Base{q0, q1} Spec.Reply.Number{x}:
      {==}
    case Spec.Question.Base{q0, q1} Spec.Reply.Yes{x}:
      {==}
    case Spec.Question.Base{q0, q1} Spec.Reply.Name{x}:
      {==}
    case Spec.Question.Base{q0, q1} Spec.Reply.Point{x}:
      {==}
    case Spec.Question.Base{q0, q1} Spec.Reply.Points{x}:
      {==}
    case Spec.Question.Owner{q0, q1} Spec.Reply.Status{x}:
      Status.follows_refl(x)
    case Spec.Question.Owner{q0, q1} Spec.Reply.Ask{x}:
      {==}
    case Spec.Question.Owner{q0, q1} Spec.Reply.Id{x}:
      {==}
    case Spec.Question.Owner{q0, q1} Spec.Reply.Hash{x}:
      {==}
    case Spec.Question.Owner{q0, q1} Spec.Reply.Names{x}:
      {==}
    case Spec.Question.Owner{q0, q1} Spec.Reply.Number{x}:
      {==}
    case Spec.Question.Owner{q0, q1} Spec.Reply.Yes{x}:
      {==}
    case Spec.Question.Owner{q0, q1} Spec.Reply.Name{x}:
      {==}
    case Spec.Question.Owner{q0, q1} Spec.Reply.Point{x}:
      {==}
    case Spec.Question.Owner{q0, q1} Spec.Reply.Points{x}:
      {==}
    case Spec.Question.Era{q0, q1} Spec.Reply.Status{x}:
      Status.follows_refl(x)
    case Spec.Question.Era{q0, q1} Spec.Reply.Ask{x}:
      {==}
    case Spec.Question.Era{q0, q1} Spec.Reply.Id{x}:
      {==}
    case Spec.Question.Era{q0, q1} Spec.Reply.Hash{x}:
      {==}
    case Spec.Question.Era{q0, q1} Spec.Reply.Names{x}:
      {==}
    case Spec.Question.Era{q0, q1} Spec.Reply.Number{x}:
      {==}
    case Spec.Question.Era{q0, q1} Spec.Reply.Yes{x}:
      {==}
    case Spec.Question.Era{q0, q1} Spec.Reply.Name{x}:
      {==}
    case Spec.Question.Era{q0, q1} Spec.Reply.Point{x}:
      {==}
    case Spec.Question.Era{q0, q1} Spec.Reply.Points{x}:
      {==}

# what the theorem asks of the reply a to the question q
def Moved(s2: Facts.Facts(), q: Spec.Question, a: Spec.Reply) -> Type:
  Exists(
    Spec.Reply,
    b => {Answers.Answer.of(s2, q) == Some{b}: Maybe<&2, Spec.Reply>} & Spec.Reply.Moves(q, a, b)
  )

# a reply that stays moved
def Moved.same(
  -s2: Facts.Facts(),
  +q: Spec.Question,
  +a: Spec.Reply,
  e: {Answers.Answer.of(s2, q) == Some{a}: Maybe<&2, Spec.Reply>}
) -> Moved(s2, q, a):
  (a, (e, Reply.moves_refl(q, a)))

# nothing is something: absurd
def None.elim(-A: Data, -Q: Type, -x: A, h: {None{} == Some{x}: Maybe<&2, A>}) -> Q:
  Empty.absurd(Q, Shared.Maybe.none_ne_some(A, x, h))

# the reply a moved, when a reply equal to it did
def Moved.to(
  -s2: Facts.Facts(),
  -q: Spec.Question,
  -a0: Spec.Reply,
  -a: Spec.Reply,
  e: {Some{a0} == Some{a}: Maybe<&2, Spec.Reply>},
  g: Moved(s2, q, a0)
) -> Moved(s2, q, a):
  %Shared.Maybe.some_inj(Spec.Reply, a0, a, e): Moved(s2, q, _)
  g

# a < b says that 1 + a <= b
def Nat.lt_to_le(
  a: Nat,
  b: Nat
) -> {Nat.is_lt(a, b) == True{}: Bool} -> {Nat.is_le(1n+a, b) == True{}: Bool}:
  match a b:
    case 0n 0n:
      h => Empty.absurd({Nat.is_le(1n, 0n) == True{}: Bool}, Shared.Bool.false_ne_true(h))
    case 0n 1n+q:
      h => Shared.Nat.le_zero(q)
    case 1n+p 0n:
      h => Empty.absurd({Nat.is_le(2n+p, 0n) == True{}: Bool}, Shared.Bool.false_ne_true(h))
    case 1n+p 1n+q:
      Nat.lt_to_le(p, q)

# Line.versions_by, once the versions in s2 are given
def Line.versions_by.of(
  -Q: Type,
  -s2: Facts.Facts(),
  -c: Ledgers.Line,
  -vs: List<&2, Types.Entry>,
  r: Exists(
    List<&2, Types.Entry>,
    vs2 => {
      Lines.Line.versions(s2, c) == Some{vs2}: Maybe<&2, List<&2, Types.Entry>>
    }
      & Lists.List.Ext(Types.Entry, vs, vs2)
  ),
  k: @vs2: List<
    &2,
    Types.Entry> -> @zs: List<
    &2,
    Types.Entry> -> {
    Lines.Line.versions(s2, c) == Some{vs2}: Maybe<&2, List<&2, Types.Entry>>
  } -> {vs2 == List.append(&2, Types.Entry, vs, zs): List<&2, Types.Entry>} -> Q
) -> Q:
  (vs2, w) = r
  (e2, x) = w
  (zs, ez) = x
  k(vs2)(zs)(e2)(ez)

# what follows from the versions of a line in s follows from those in s2,
# which extend them
def Line.versions_by(
  -Q: Type,
  +name: String,
  +s: Facts.Facts(),
  +s2: Facts.Facts(),
  +c: Ledgers.Line,
  +vs: List<&2, Types.Entry>,
  +hw: {Facts.Facts.wider(s, s2) == True{}: Bool},
  +hl: {Facts.Facts.liars(s2) == []: List<&2, String>},
  +ho: {Facts.Facts.ok(name, s2) == True{}: Bool},
  e: {Lines.Line.versions(s, c) == Some{vs}: Maybe<&2, List<&2, Types.Entry>>},
  k: @vs2: List<
    &2,
    Types.Entry> -> @zs: List<
    &2,
    Types.Entry> -> {
    Lines.Line.versions(s2, c) == Some{vs2}: Maybe<&2, List<&2, Types.Entry>>
  } -> {vs2 == List.append(&2, Types.Entry, vs, zs): List<&2, Types.Entry>} -> Q
) -> Q:
  Line.versions_by.of(Q, s2, c, vs, Stays.Line.versions_stay(name, s, s2, c, vs)(hw)(hl)(ho)(e), k)

# a version below the count of vs is below the count of an extension
def Ext.lt(
  +vs: List<&2, Types.Entry>,
  +vs2: List<&2, Types.Entry>,
  +zs: List<&2, Types.Entry>,
  +ez: {vs2 == List.append(&2, Types.Entry, vs, zs): List<&2, Types.Entry>},
  +j: Nat
) -> {
  Nat.is_lt(j, List.length(&2, Types.Entry, vs)) == True{}: Bool
} -> {Nat.is_lt(j, List.length(&2, Types.Entry, vs2)) == True{}: Bool}:
  h => Shared.Nat.lt_le(
    j,
    List.length(&2, Types.Entry, vs),
    List.length(&2, Types.Entry, vs2)
  )(h)(Lists.List.ext_length(Types.Entry, vs, vs2)((zs, ez)))

# the first 1+j versions of an extension of vs are those of vs, which has them
def Ext.take(
  +vs: List<&2, Types.Entry>,
  +vs2: List<&2, Types.Entry>,
  +zs: List<&2, Types.Entry>,
  +ez: {vs2 == List.append(&2, Types.Entry, vs, zs): List<&2, Types.Entry>},
  +j: Nat
) -> {
  Nat.is_lt(j, List.length(&2, Types.Entry, vs)) == True{}: Bool
} -> {
  List.take(
    &2,
    Types.Entry,
    vs2,
    1n+j
  )
    == List.take(&2, Types.Entry, vs, 1n+j): List<&2, Types.Entry>
}:
  h => Lists.List.ext_take(
    Types.Entry,
    vs,
    vs2,
    1n+j
  )((zs, ez))(Nat.lt_to_le(j, List.length(&2, Types.Entry, vs))(h))

# what holds of nothing, and of each version of the id i among vs, holds of
# what Versions.find gives
def Find.by(
  -P: Maybe<&2, RKnown.Found> -> Type,
  +vs: List<&2, Types.Entry>,
  +i: Ledgers.Id,
  n: P(None{}),
  f: @j: Nat -> @x: Types.Entry -> {
    Lists.List.index(
      ~Types.Entry,
      ~Ledgers.Id,
      ~RLines.Entry.is_of,
      vs,
      i
    )
      == Some{j}: Maybe<&2, Nat>
  } -> {
    List.get(&2, Types.Entry, vs, j) == Some{x}: Maybe<&2, Types.Entry>
  } -> P(Some{RKnown.Found{j, x}})
) -> P(RAnswers.Versions.find(vs, i)):
  Lists.Maybe.by(
    Nat,
    m => P(None{}) -> P(RAnswers.Versions.find.at(vs, m)),
    Lists.List.index(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, vs, i),
    en => n => n,
    +j => +ej => n => Lists.Maybe.by(
      Types.Entry,
      g => P(None{}) -> P(Maybe.map(&2, Types.Entry, RKnown.Found, e => RKnown.Found{j, e}, g)),
      List.get(&2, Types.Entry, vs, j),
      en => n => n,
      +x => +eg => n => f(j)(x)(ej)(eg)
    )(n)
  )(n)

# a version found among vs is found among an extension of vs
def Find.ext(
  +vs: List<&2, Types.Entry>,
  +vs2: List<&2, Types.Entry>,
  +zs: List<&2, Types.Entry>,
  +ez: {vs2 == List.append(&2, Types.Entry, vs, zs): List<&2, Types.Entry>},
  +i: Ledgers.Id,
  +j: Nat,
  +x: Types.Entry,
  ei: {
    Lists.List.index(
      ~Types.Entry,
      ~Ledgers.Id,
      ~RLines.Entry.is_of,
      vs,
      i
    )
      == Some{j}: Maybe<&2, Nat>
  },
  eg: {List.get(&2, Types.Entry, vs, j) == Some{x}: Maybe<&2, Types.Entry>}
) -> {RAnswers.Versions.find(vs2, i) == Some{RKnown.Found{j, x}}: Maybe<&2, RKnown.Found>}:
  Eq.up(
    Maybe<&2, Nat>,
    m => {RAnswers.Versions.find.at(vs2, m) == Some{RKnown.Found{j, x}}: Maybe<&2, RKnown.Found>},
    Lists.List.index(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, vs2, i),
    Some{j},
    Lists.List.index_ext(
      ~Types.Entry,
      ~Ledgers.Id,
      ~RLines.Entry.is_of,
      vs,
      vs2,
      i,
      j
    )((zs, ez))(ei),
    Eq.up(
      Maybe<&2, Types.Entry>,
      g => {
        Maybe.map(
          &2,
          Types.Entry,
          RKnown.Found,
          e => RKnown.Found{j, e},
          g
        )
          == Some{RKnown.Found{j, x}}: Maybe<&2, RKnown.Found>
      },
      List.get(&2, Types.Entry, vs2, j),
      Some{x},
      Lists.List.ext_get(Types.Entry, vs, vs2, j, x)((zs, ez))(eg),
      {==}
    )
  )

# the versions before a version of vs are the same before it in an extension
def Before.ext(
  +vs: List<&2, Types.Entry>,
  +vs2: List<&2, Types.Entry>,
  +zs: List<&2, Types.Entry>,
  +ez: {vs2 == List.append(&2, Types.Entry, vs, zs): List<&2, Types.Entry>},
  +j: Nat,
  -ws: List<&2, Types.Entry>
) -> {
  RAnswers.Line.before.of(j, Some{vs}) == Some{ws}: Maybe<&2, List<&2, Types.Entry>>
} -> {RAnswers.Line.before.of(j, Some{vs2}) == Some{ws}: Maybe<&2, List<&2, Types.Entry>>}:
  ha => Lists.Bool.by(
    b => {
      Shared.Maybe.when(
        List<&2, Types.Entry>,
        b,
        u => Some{List.take(&2, Types.Entry, vs, 1n+j)}
      )
        == Some{ws}: Maybe<&2, List<&2, Types.Entry>>
    } -> {RAnswers.Line.before.of(j, Some{vs2}) == Some{ws}: Maybe<&2, List<&2, Types.Entry>>},
    Nat.is_lt(j, List.length(&2, Types.Entry, vs)),
    +et => +ha => Eq.up(
      Bool,
      b => {
        Shared.Maybe.when(
          List<&2, Types.Entry>,
          b,
          u => Some{List.take(&2, Types.Entry, vs2, 1n+j)}
        )
          == Some{ws}: Maybe<&2, List<&2, Types.Entry>>
      },
      Nat.is_lt(j, List.length(&2, Types.Entry, vs2)),
      True{},
      Ext.lt(vs, vs2, zs, ez, j)(et),
      Eq.up(
        List<&2, Types.Entry>,
        t => {Some{t} == Some{ws}: Maybe<&2, List<&2, Types.Entry>>},
        List.take(&2, Types.Entry, vs2, 1n+j),
        List.take(&2, Types.Entry, vs, 1n+j),
        Ext.take(vs, vs2, zs, ez, j)(et),
        ha
      )
    ),
    ef => ha => None.elim(
      List<&2, Types.Entry>,
      {RAnswers.Line.before.of(j, Some{vs2}) == Some{ws}: Maybe<&2, List<&2, Types.Entry>>},
      ws,
      ha
    )
  )(ha)

# the versions before a version of a line stay
def Before.stays(
  +name: String,
  +s: Facts.Facts(),
  +s2: Facts.Facts(),
  +c: Ledgers.Line,
  +j: Nat,
  +ws: List<&2, Types.Entry>,
  +hw: {Facts.Facts.wider(s, s2) == True{}: Bool},
  +hl: {Facts.Facts.liars(s2) == []: List<&2, String>},
  +ho: {Facts.Facts.ok(name, s2) == True{}: Bool}
) -> {
  Answers.Line.before(s, c, j) == Some{ws}: Maybe<&2, List<&2, Types.Entry>>
} -> {Answers.Line.before(s2, c, j) == Some{ws}: Maybe<&2, List<&2, Types.Entry>>}:
  ha => Lists.Maybe.by(
    List<&2, Types.Entry>,
    m => {
      RAnswers.Line.before.of(j, m) == Some{ws}: Maybe<&2, List<&2, Types.Entry>>
    } -> {Answers.Line.before(s2, c, j) == Some{ws}: Maybe<&2, List<&2, Types.Entry>>},
    Lines.Line.versions(s, c),
    en => ha => None.elim(
      List<&2, Types.Entry>,
      {Answers.Line.before(s2, c, j) == Some{ws}: Maybe<&2, List<&2, Types.Entry>>},
      ws,
      ha
    ),
    +vs => +ev => +ha => Line.versions_by(
      {Answers.Line.before(s2, c, j) == Some{ws}: Maybe<&2, List<&2, Types.Entry>>},
      name,
      s,
      s2,
      c,
      vs,
      hw,
      hl,
      ho,
      ev,
      +vs2 => +zs => +e2 => +ez => Eq.up(
        Maybe<&2, List<&2, Types.Entry>>,
        m => {RAnswers.Line.before.of(j, m) == Some{ws}: Maybe<&2, List<&2, Types.Entry>>},
        Lines.Line.versions(s2, c),
        Some{vs2},
        e2,
        Before.ext(vs, vs2, zs, ez, j, ws)(ha)
      )
    )
  )(ha)

# the rule of a version of a line stays
def Rule.for_stays(
  +name: String,
  +s: Facts.Facts(),
  +s2: Facts.Facts(),
  +c: Ledgers.Line,
  k: Nat,
  +u: RLines.Rule,
  +hw: {Facts.Facts.wider(s, s2) == True{}: Bool},
  +hl: {Facts.Facts.liars(s2) == []: List<&2, String>},
  +ho: {Facts.Facts.ok(name, s2) == True{}: Bool}
) -> {
  Answers.Rule.for(s, c, k) == Some{u}: Maybe<&2, RLines.Rule>
} -> {Answers.Rule.for(s2, c, k) == Some{u}: Maybe<&2, RLines.Rule>}:
  match k:
    case 0n:
      ha => None.elim(
        RLines.Rule,
        {Answers.Rule.for(s2, c, 0n) == Some{u}: Maybe<&2, RLines.Rule>},
        u,
        ha
      )
    case 1n+(+j):
      ha => Lists.Maybe.by(
        List<&2, Types.Entry>,
        m => {
          Answers.Rule.for.of(s, c, m) == Some{u}: Maybe<&2, RLines.Rule>
        } -> {Answers.Rule.for(s2, c, 1n+j) == Some{u}: Maybe<&2, RLines.Rule>},
        Answers.Line.before(s, c, j),
        en => ha => None.elim(
          RLines.Rule,
          {Answers.Rule.for(s2, c, 1n+j) == Some{u}: Maybe<&2, RLines.Rule>},
          u,
          ha
        ),
        +ws => +eb => +ha => Eq.up(
          Maybe<&2, List<&2, Types.Entry>>,
          m => {Answers.Rule.for.of(s2, c, m) == Some{u}: Maybe<&2, RLines.Rule>},
          Answers.Line.before(s2, c, j),
          Some{ws},
          Before.stays(name, s, s2, c, j, ws, hw, hl, ho)(eb),
          Stays.Rule.after_stays(name, s, s2, c, ws, u)(hw)(hl)(ho)(ha)
        )
      )(ha)

# the era of a version of a line stays
def Era.for_stays(
  +name: String,
  +s: Facts.Facts(),
  +s2: Facts.Facts(),
  +c: Ledgers.Line,
  k: Nat,
  +n: Nat,
  +hw: {Facts.Facts.wider(s, s2) == True{}: Bool},
  +hl: {Facts.Facts.liars(s2) == []: List<&2, String>},
  +ho: {Facts.Facts.ok(name, s2) == True{}: Bool}
) -> {
  Answers.Era.for(s, c, k) == Some{n}: Maybe<&2, Nat>
} -> {Answers.Era.for(s2, c, k) == Some{n}: Maybe<&2, Nat>}:
  match k:
    case 0n:
      ha => None.elim(Nat, {Answers.Era.for(s2, c, 0n) == Some{n}: Maybe<&2, Nat>}, n, ha)
    case 1n+(+j):
      ha => Lists.Maybe.by(
        List<&2, Types.Entry>,
        m => {
          Maybe.map(
            &2,
            List<&2, Types.Entry>,
            Nat,
            vs => RLines.Line.era(c, vs),
            m
          )
            == Some{n}: Maybe<&2, Nat>
        } -> {Answers.Era.for(s2, c, 1n+j) == Some{n}: Maybe<&2, Nat>},
        Answers.Line.before(s, c, j),
        en => ha => None.elim(
          Nat,
          {Answers.Era.for(s2, c, 1n+j) == Some{n}: Maybe<&2, Nat>},
          n,
          ha
        ),
        +ws => +eb => +ha => Eq.up(
          Maybe<&2, List<&2, Types.Entry>>,
          m => {
            Maybe.map(
              &2,
              List<&2, Types.Entry>,
              Nat,
              vs => RLines.Line.era(c, vs),
              m
            )
              == Some{n}: Maybe<&2, Nat>
          },
          Answers.Line.before(s2, c, j),
          Some{ws},
          Before.stays(name, s, s2, c, j, ws, hw, hl, ho)(eb),
          ha
        )
      )(ha)

# the voters that decided a version stay
def Rule.voters_stay(
  +name: String,
  +s: Facts.Facts(),
  +s2: Facts.Facts(),
  +c: Ledgers.Line,
  e: Types.Entry,
  u: RLines.Rule,
  +a: Spec.Reply,
  +hw: {Facts.Facts.wider(s, s2) == True{}: Bool},
  +hl: {Facts.Facts.liars(s2) == []: List<&2, String>}
) -> {
  Answers.Rule.voters(s, c, e, u) == Some{a}: Maybe<&2, Spec.Reply>
} -> {Answers.Rule.voters(s2, c, e, u) == Some{a}: Maybe<&2, Spec.Reply>}:
  match e u:
    case Types.Entry{+pk, +k} RLines.Rule{+g, +ns}:
      ha => Lists.Bool.by(
        b => {
          Shared.Maybe.when(
            Spec.Reply,
            Shared.Bool.when(
              Bool,
              b,
              un => RRounds.Slot.backed(
                Rounds.Slot.ballots(s, c, k),
                ns,
                k,
                Lists.List.lead(String, ns),
                pk
              ),
              un => False{}
            ),
            u2 => Some{Spec.Reply.Names{Lists.List.lead(String, ns)}}
          )
            == Some{a}: Maybe<&2, Spec.Reply>
        } -> {
          Answers.Rule.voters(
            s2,
            c,
            Types.Entry{pk, k},
            RLines.Rule{g, ns}
          )
            == Some{a}: Maybe<&2, Spec.Reply>
        },
        Bool.not(List.is_empty(&2, String, ns)),
        +et => +ha => Lists.Bool.by(
          b => {
            Shared.Maybe.when(
              Spec.Reply,
              b,
              u2 => Some{Spec.Reply.Names{Lists.List.lead(String, ns)}}
            )
              == Some{a}: Maybe<&2, Spec.Reply>
          } -> {
            Answers.Rule.voters(
              s2,
              c,
              Types.Entry{pk, k},
              RLines.Rule{g, ns}
            )
              == Some{a}: Maybe<&2, Spec.Reply>
          },
          RRounds.Slot.backed(Rounds.Slot.ballots(s, c, k), ns, k, Lists.List.lead(String, ns), pk),
          +eh => +ha => Eq.up(
            Bool,
            b => {
              Shared.Maybe.when(
                Spec.Reply,
                Shared.Bool.when(
                  Bool,
                  b,
                  un => RRounds.Slot.backed(
                    Rounds.Slot.ballots(s2, c, k),
                    ns,
                    k,
                    Lists.List.lead(String, ns),
                    pk
                  ),
                  un => False{}
                ),
                u2 => Some{Spec.Reply.Names{Lists.List.lead(String, ns)}}
              )
                == Some{a}: Maybe<&2, Spec.Reply>
            },
            Bool.not(List.is_empty(&2, String, ns)),
            True{},
            et,
            Eq.up(
              Bool,
              b => {
                Shared.Maybe.when(
                  Spec.Reply,
                  b,
                  u2 => Some{Spec.Reply.Names{Lists.List.lead(String, ns)}}
                )
                  == Some{a}: Maybe<&2, Spec.Reply>
              },
              RRounds.Slot.backed(
                Rounds.Slot.ballots(s2, c, k),
                ns,
                k,
                Lists.List.lead(String, ns),
                pk
              ),
              True{},
              Rounds.Votes.backed_stays(
                s,
                s2,
                c,
                k,
                ns,
                Lists.List.lead(String, ns),
                pk
              )(hw)(hl)(eh),
              ha
            )
          ),
          ef => ha => None.elim(
            Spec.Reply,
            {
              Answers.Rule.voters(
                s2,
                c,
                Types.Entry{pk, k},
                RLines.Rule{g, ns}
              )
                == Some{a}: Maybe<&2, Spec.Reply>
            },
            a,
            ha
          )
        )(ha),
        ef => ha => None.elim(
          Spec.Reply,
          {
            Answers.Rule.voters(
              s2,
              c,
              Types.Entry{pk, k},
              RLines.Rule{g, ns}
            )
              == Some{a}: Maybe<&2, Spec.Reply>
          },
          a,
          ha
        )
      )(ha)

# the paths that clash in a merge stay
def Clashes.of_stays(
  +name: String,
  +s: Facts.Facts(),
  +s2: Facts.Facts(),
  +c: Ledgers.Line,
  k: Nat,
  +e: Types.Entry,
  +ps: List<&2, String>,
  +hw: {Facts.Facts.wider(s, s2) == True{}: Bool},
  +hl: {Facts.Facts.liars(s2) == []: List<&2, String>},
  +ho: {Facts.Facts.ok(name, s2) == True{}: Bool}
) -> {
  Answers.Clashes.of(s, c, k, e) == Some{ps}: Maybe<&2, List<&2, String>>
} -> {Answers.Clashes.of(s2, c, k, e) == Some{ps}: Maybe<&2, List<&2, String>>}:
  match k:
    case 0n:
      ha => None.elim(
        List<&2, String>,
        {Answers.Clashes.of(s2, c, 0n, e) == Some{ps}: Maybe<&2, List<&2, String>>},
        ps,
        ha
      )
    case 1n+(+j):
      ha => Lists.Bool.by(
        b => {
          RAnswers.Clashes.at(
            Bool.and(b, Contents.Merge.fits(s, c, j, e)),
            Contents.Content.of(
              s,
              Spec.Point.line(RContents.Entry.based(c, Some{e})),
              Spec.Point.n(RContents.Entry.based(c, Some{e}))
            ),
            Contents.Content.of(s, c, j),
            Contents.Content.of(
              s,
              Spec.Point.line(RContents.Entry.taken(c, Some{e})),
              Spec.Point.n(RContents.Entry.taken(c, Some{e}))
            )
          )
            == Some{ps}: Maybe<&2, List<&2, String>>
        } -> {Answers.Clashes.of(s2, c, 1n+j, e) == Some{ps}: Maybe<&2, List<&2, String>>},
        RContents.Request.is_merge(RAnswers.Entry.request(e)),
        +em => +ha => Lists.Bool.by(
          b => {
            RAnswers.Clashes.at(
              b,
              Contents.Content.of(
                s,
                Spec.Point.line(RContents.Entry.based(c, Some{e})),
                Spec.Point.n(RContents.Entry.based(c, Some{e}))
              ),
              Contents.Content.of(s, c, j),
              Contents.Content.of(
                s,
                Spec.Point.line(RContents.Entry.taken(c, Some{e})),
                Spec.Point.n(RContents.Entry.taken(c, Some{e}))
              )
            )
              == Some{ps}: Maybe<&2, List<&2, String>>
          } -> {Answers.Clashes.of(s2, c, 1n+j, e) == Some{ps}: Maybe<&2, List<&2, String>>},
          Contents.Merge.fits(s, c, j, e),
          +ef => +ha => Lists.Maybe.by(
            Files.Files(),
            m => {
              RAnswers.Clashes.at(
                True{},
                m,
                Contents.Content.of(s, c, j),
                Contents.Content.of(
                  s,
                  Spec.Point.line(RContents.Entry.taken(c, Some{e})),
                  Spec.Point.n(RContents.Entry.taken(c, Some{e}))
                )
              )
                == Some{ps}: Maybe<&2, List<&2, String>>
            } -> {Answers.Clashes.of(s2, c, 1n+j, e) == Some{ps}: Maybe<&2, List<&2, String>>},
            Contents.Content.of(
              s,
              Spec.Point.line(RContents.Entry.based(c, Some{e})),
              Spec.Point.n(RContents.Entry.based(c, Some{e}))
            ),
            en => ha => None.elim(
              List<&2, String>,
              {Answers.Clashes.of(s2, c, 1n+j, e) == Some{ps}: Maybe<&2, List<&2, String>>},
              ps,
              ha
            ),
            +fb => +eb => +ha => Lists.Maybe.by(
              Files.Files(),
              m => {
                RAnswers.Clashes.at(
                  True{},
                  Some{fb},
                  m,
                  Contents.Content.of(
                    s,
                    Spec.Point.line(RContents.Entry.taken(c, Some{e})),
                    Spec.Point.n(RContents.Entry.taken(c, Some{e}))
                  )
                )
                  == Some{ps}: Maybe<&2, List<&2, String>>
              } -> {Answers.Clashes.of(s2, c, 1n+j, e) == Some{ps}: Maybe<&2, List<&2, String>>},
              Contents.Content.of(s, c, j),
              en => ha => None.elim(
                List<&2, String>,
                {Answers.Clashes.of(s2, c, 1n+j, e) == Some{ps}: Maybe<&2, List<&2, String>>},
                ps,
                ha
              ),
              +fo => +eo => +ha => Lists.Maybe.by(
                Files.Files(),
                m => {
                  RAnswers.Clashes.at(
                    True{},
                    Some{fb},
                    Some{fo},
                    m
                  )
                    == Some{ps}: Maybe<&2, List<&2, String>>
                } -> {Answers.Clashes.of(s2, c, 1n+j, e) == Some{ps}: Maybe<&2, List<&2, String>>},
                Contents.Content.of(
                  s,
                  Spec.Point.line(RContents.Entry.taken(c, Some{e})),
                  Spec.Point.n(RContents.Entry.taken(c, Some{e}))
                ),
                en => ha => None.elim(
                  List<&2, String>,
                  {Answers.Clashes.of(s2, c, 1n+j, e) == Some{ps}: Maybe<&2, List<&2, String>>},
                  ps,
                  ha
                ),
                +ft => +et => +ha => Eq.up(
                  Bool,
                  b => {
                    RAnswers.Clashes.at(
                      Bool.and(b, Contents.Merge.fits(s2, c, j, e)),
                      Contents.Content.of(
                        s2,
                        Spec.Point.line(RContents.Entry.based(c, Some{e})),
                        Spec.Point.n(RContents.Entry.based(c, Some{e}))
                      ),
                      Contents.Content.of(s2, c, j),
                      Contents.Content.of(
                        s2,
                        Spec.Point.line(RContents.Entry.taken(c, Some{e})),
                        Spec.Point.n(RContents.Entry.taken(c, Some{e}))
                      )
                    )
                      == Some{ps}: Maybe<&2, List<&2, String>>
                  },
                  RContents.Request.is_merge(RAnswers.Entry.request(e)),
                  True{},
                  em,
                  Eq.up(
                    Bool,
                    b => {
                      RAnswers.Clashes.at(
                        b,
                        Contents.Content.of(
                          s2,
                          Spec.Point.line(RContents.Entry.based(c, Some{e})),
                          Spec.Point.n(RContents.Entry.based(c, Some{e}))
                        ),
                        Contents.Content.of(s2, c, j),
                        Contents.Content.of(
                          s2,
                          Spec.Point.line(RContents.Entry.taken(c, Some{e})),
                          Spec.Point.n(RContents.Entry.taken(c, Some{e}))
                        )
                      )
                        == Some{ps}: Maybe<&2, List<&2, String>>
                    },
                    Contents.Merge.fits(s2, c, j, e),
                    True{},
                    Reads.Merge.fits_stays(name, s, s2, c, j, e)(hw)(hl)(ho)(ef),
                    Eq.up(
                      Maybe<&2, Files.Files()>,
                      m => {
                        RAnswers.Clashes.at(
                          True{},
                          m,
                          Contents.Content.of(s2, c, j),
                          Contents.Content.of(
                            s2,
                            Spec.Point.line(RContents.Entry.taken(c, Some{e})),
                            Spec.Point.n(RContents.Entry.taken(c, Some{e}))
                          )
                        )
                          == Some{ps}: Maybe<&2, List<&2, String>>
                      },
                      Contents.Content.of(
                        s2,
                        Spec.Point.line(RContents.Entry.based(c, Some{e})),
                        Spec.Point.n(RContents.Entry.based(c, Some{e}))
                      ),
                      Some{fb},
                      Reads.Content.of_stays(
                        name,
                        s,
                        s2,
                        Spec.Point.line(RContents.Entry.based(c, Some{e})),
                        Spec.Point.n(RContents.Entry.based(c, Some{e})),
                        fb
                      )(hw)(hl)(ho)(eb),
                      Eq.up(
                        Maybe<&2, Files.Files()>,
                        m => {
                          RAnswers.Clashes.at(
                            True{},
                            Some{fb},
                            m,
                            Contents.Content.of(
                              s2,
                              Spec.Point.line(RContents.Entry.taken(c, Some{e})),
                              Spec.Point.n(RContents.Entry.taken(c, Some{e}))
                            )
                          )
                            == Some{ps}: Maybe<&2, List<&2, String>>
                        },
                        Contents.Content.of(s2, c, j),
                        Some{fo},
                        Reads.Content.of_stays(name, s, s2, c, j, fo)(hw)(hl)(ho)(eo),
                        Eq.up(
                          Maybe<&2, Files.Files()>,
                          m => {
                            RAnswers.Clashes.at(
                              True{},
                              Some{fb},
                              Some{fo},
                              m
                            )
                              == Some{ps}: Maybe<&2, List<&2, String>>
                          },
                          Contents.Content.of(
                            s2,
                            Spec.Point.line(RContents.Entry.taken(c, Some{e})),
                            Spec.Point.n(RContents.Entry.taken(c, Some{e}))
                          ),
                          Some{ft},
                          Reads.Content.of_stays(
                            name,
                            s,
                            s2,
                            Spec.Point.line(RContents.Entry.taken(c, Some{e})),
                            Spec.Point.n(RContents.Entry.taken(c, Some{e})),
                            ft
                          )(hw)(hl)(ho)(et),
                          ha
                        )
                      )
                    )
                  )
                )
              )(ha)
            )(ha)
          )(ha),
          ef => ha => None.elim(
            List<&2, String>,
            {Answers.Clashes.of(s2, c, 1n+j, e) == Some{ps}: Maybe<&2, List<&2, String>>},
            ps,
            ha
          )
        )(ha),
        ef => ha => None.elim(
          List<&2, String>,
          {Answers.Clashes.of(s2, c, 1n+j, e) == Some{ps}: Maybe<&2, List<&2, String>>},
          ps,
          ha
        )
      )(ha)

# the base of a merge stays
def Merge.base_stays(
  +name: String,
  +s: Facts.Facts(),
  +s2: Facts.Facts(),
  +c: Ledgers.Line,
  k: Nat,
  +e: Types.Entry,
  +pt: Spec.Point,
  +hw: {Facts.Facts.wider(s, s2) == True{}: Bool},
  +hl: {Facts.Facts.liars(s2) == []: List<&2, String>},
  +ho: {Facts.Facts.ok(name, s2) == True{}: Bool}
) -> {
  Answers.Base.of(s, c, k, e) == Some{pt}: Maybe<&2, Spec.Point>
} -> {Answers.Base.of(s2, c, k, e) == Some{pt}: Maybe<&2, Spec.Point>}:
  match k:
    case 0n:
      ha => None.elim(
        Spec.Point,
        {Answers.Base.of(s2, c, 0n, e) == Some{pt}: Maybe<&2, Spec.Point>},
        pt,
        ha
      )
    case 1n+(+j):
      ha => Lists.Bool.by(
        b => {
          Shared.Maybe.when(
            Spec.Point,
            b,
            u => RContents.Entry.base(e)
          )
            == Some{pt}: Maybe<&2, Spec.Point>
        } -> {Answers.Base.of(s2, c, 1n+j, e) == Some{pt}: Maybe<&2, Spec.Point>},
        Contents.Merge.fits(s, c, j, e),
        +ef => +ha => Eq.up(
          Bool,
          b => {
            Shared.Maybe.when(
              Spec.Point,
              b,
              u => RContents.Entry.base(e)
            )
              == Some{pt}: Maybe<&2, Spec.Point>
          },
          Contents.Merge.fits(s2, c, j, e),
          True{},
          Reads.Merge.fits_stays(name, s, s2, c, j, e)(hw)(hl)(ho)(ef),
          ha
        ),
        ef => ha => None.elim(
          Spec.Point,
          {Answers.Base.of(s2, c, 1n+j, e) == Some{pt}: Maybe<&2, Spec.Point>},
          pt,
          ha
        )
      )(ha)

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof does not run
# a path that a version of vs resolves, a version of an extension resolves
def Resolved.has_ext(
  +vs: List<&2, Types.Entry>,
  +vs2: List<&2, Types.Entry>,
  +zs: List<&2, Types.Entry>,
  +ez: {vs2 == List.append(&2, Types.Entry, vs, zs): List<&2, Types.Entry>},
  +i: Ledgers.Id,
  +p: String
) -> {
  RAnswers.Resolved.has(RAnswers.Resolved{vs, i}, p) == True{}: Bool
} -> {RAnswers.Resolved.has(RAnswers.Resolved{vs2, i}, p) == True{}: Bool}:
  h => Eq.up(
    List<&2, Types.Entry>,
    l => {RAnswers.Resolved.has(RAnswers.Resolved{l, i}, p) == True{}: Bool},
    vs2,
    List.append(&2, Types.Entry, vs, zs),
    ez,
    Eq.up(
      Bool,
      b => {b == True{}: Bool},
      Shared.List.some(
        ~Types.Entry,
        ~RAnswers.Clash,
        ~RAnswers.Entry.resolves,
        List.append(&2, Types.Entry, vs, zs),
        RAnswers.Clash{i, p}
      ),
      Bool.or(
        Shared.List.some(
          ~Types.Entry,
          ~RAnswers.Clash,
          ~RAnswers.Entry.resolves,
          vs,
          RAnswers.Clash{i, p}
        ),
        Shared.List.some(
          ~Types.Entry,
          ~RAnswers.Clash,
          ~RAnswers.Entry.resolves,
          zs,
          RAnswers.Clash{i, p}
        )
      ),
      Shared.List.some_append(
        ~Types.Entry,
        ~RAnswers.Clash,
        ~RAnswers.Entry.resolves,
        vs,
        zs,
        RAnswers.Clash{i, p}
      ),
      Eq.up(
        Bool,
        b => {
          Bool.or(
            b,
            Shared.List.some(
              ~Types.Entry,
              ~RAnswers.Clash,
              ~RAnswers.Entry.resolves,
              zs,
              RAnswers.Clash{i, p}
            )
          )
            == True{}: Bool
        },
        Shared.List.some(
          ~Types.Entry,
          ~RAnswers.Clash,
          ~RAnswers.Entry.resolves,
          vs,
          RAnswers.Clash{i, p}
        ),
        True{},
        h,
        {==}
      )
    )
  )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the paths that the versions vs resolve, an extension resolves
def Resolved.holds_ext(
  ps: List<&2, String>,
  +vs: List<&2, Types.Entry>,
  +vs2: List<&2, Types.Entry>,
  +zs: List<&2, Types.Entry>,
  +ez: {vs2 == List.append(&2, Types.Entry, vs, zs): List<&2, Types.Entry>},
  +i: Ledgers.Id
) -> {
  Shared.List.holds(
    ~String,
    ~RAnswers.Resolved,
    ~RAnswers.Resolved.has,
    ps,
    RAnswers.Resolved{vs, i}
  )
    == True{}: Bool
} -> {
  Shared.List.holds(
    ~String,
    ~RAnswers.Resolved,
    ~RAnswers.Resolved.has,
    ps,
    RAnswers.Resolved{vs2, i}
  )
    == True{}: Bool
}:
  match ps:
    case Nil{}:
      h => {==}
    case Con{+p, +r}:
      +h => Shared.List.all.if_both(
        RAnswers.Resolved.has(RAnswers.Resolved{vs2, i}, p),
        u => Shared.List.holds(
          ~String,
          ~RAnswers.Resolved,
          ~RAnswers.Resolved.has,
          r,
          RAnswers.Resolved{vs2, i}
        )
      )(
        Resolved.has_ext(
          vs,
          vs2,
          zs,
          ez,
          i,
          p
        )(
          Shared.List.all.if_hit(
            RAnswers.Resolved.has(RAnswers.Resolved{vs, i}, p),
            u => Shared.List.holds(
              ~String,
              ~RAnswers.Resolved,
              ~RAnswers.Resolved.has,
              r,
              RAnswers.Resolved{vs, i}
            )
          )(h)
        )
      )(
        Resolved.holds_ext(
          r,
          vs,
          vs2,
          zs,
          ez,
          i
        )(
          Shared.List.all.if_rest(
            RAnswers.Resolved.has(RAnswers.Resolved{vs, i}, p),
            u => Shared.List.holds(
              ~String,
              ~RAnswers.Resolved,
              ~RAnswers.Resolved.has,
              r,
              RAnswers.Resolved{vs, i}
            )
          )(h)
        )
      )

# the status of a merge follows Conflicted
def Status.merge_after(
  +vs2: List<&2, Types.Entry>,
  +i: Ledgers.Id,
  m: Maybe<&2, List<&2, String>>
) -> {
  Spec.Status.follows(Spec.Status.Conflicted{i}, RAnswers.Status.merge(vs2, i, m)) == True{}: Bool
}:
  match m:
    case None{}:
      Ledgers.Id.is_eq_refl(i)
    case Some{+ps}:
      Lists.Bool.by(
        b => {
          Spec.Status.follows(
            Spec.Status.Conflicted{i},
            Bool.pick(Spec.Status, b, Spec.Status.Written{}, Spec.Status.Conflicted{i})
          )
            == True{}: Bool
        },
        Shared.List.holds(
          ~String,
          ~RAnswers.Resolved,
          ~RAnswers.Resolved.has,
          ps,
          RAnswers.Resolved{vs2, i}
        ),
        et => {==},
        ef => Ledgers.Id.is_eq_refl(i)
      )

# the status of a merge among an extension follows its status among vs
def Status.merge_follows(
  +name: String,
  +s: Facts.Facts(),
  +s2: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +e: Types.Entry,
  +vs: List<&2, Types.Entry>,
  +vs2: List<&2, Types.Entry>,
  +zs: List<&2, Types.Entry>,
  +ez: {vs2 == List.append(&2, Types.Entry, vs, zs): List<&2, Types.Entry>},
  +i: Ledgers.Id,
  +hw: {Facts.Facts.wider(s, s2) == True{}: Bool},
  +hl: {Facts.Facts.liars(s2) == []: List<&2, String>},
  +ho: {Facts.Facts.ok(name, s2) == True{}: Bool}
) -> {
  Spec.Status.follows(
    RAnswers.Status.merge(vs, i, Answers.Clashes.of(s, c, k, e)),
    RAnswers.Status.merge(vs2, i, Answers.Clashes.of(s2, c, k, e))
  )
    == True{}: Bool
}:
  Lists.Maybe.by(
    List<&2, String>,
    m => {
      Spec.Status.follows(
        RAnswers.Status.merge(vs, i, m),
        RAnswers.Status.merge(vs2, i, Answers.Clashes.of(s2, c, k, e))
      )
        == True{}: Bool
    },
    Answers.Clashes.of(s, c, k, e),
    en => Status.merge_after(vs2, i, Answers.Clashes.of(s2, c, k, e)),
    +ps => +ep => Eq.up(
      Maybe<&2, List<&2, String>>,
      m => {
        Spec.Status.follows(
          RAnswers.Status.merge(vs, i, Some{ps}),
          RAnswers.Status.merge(vs2, i, m)
        )
          == True{}: Bool
      },
      Answers.Clashes.of(s2, c, k, e),
      Some{ps},
      Clashes.of_stays(name, s, s2, c, k, e, ps, hw, hl, ho)(ep),
      Lists.Bool.by(
        b => {
          Spec.Status.follows(
            Bool.pick(Spec.Status, b, Spec.Status.Written{}, Spec.Status.Conflicted{i}),
            Bool.pick(
              Spec.Status,
              Shared.List.holds(
                ~String,
                ~RAnswers.Resolved,
                ~RAnswers.Resolved.has,
                ps,
                RAnswers.Resolved{vs2, i}
              ),
              Spec.Status.Written{},
              Spec.Status.Conflicted{i}
            )
          )
            == True{}: Bool
        },
        Shared.List.holds(
          ~String,
          ~RAnswers.Resolved,
          ~RAnswers.Resolved.has,
          ps,
          RAnswers.Resolved{vs, i}
        ),
        et => Eq.up(
          Bool,
          b => {
            Spec.Status.follows(
              Spec.Status.Written{},
              Bool.pick(Spec.Status, b, Spec.Status.Written{}, Spec.Status.Conflicted{i})
            )
              == True{}: Bool
          },
          Shared.List.holds(
            ~String,
            ~RAnswers.Resolved,
            ~RAnswers.Resolved.has,
            ps,
            RAnswers.Resolved{vs2, i}
          ),
          True{},
          Resolved.holds_ext(ps, vs, vs2, zs, ez, i)(et),
          {==}
        ),
        ef => Lists.Bool.by(
          b => {
            Spec.Status.follows(
              Spec.Status.Conflicted{i},
              Bool.pick(Spec.Status, b, Spec.Status.Written{}, Spec.Status.Conflicted{i})
            )
              == True{}: Bool
          },
          Shared.List.holds(
            ~String,
            ~RAnswers.Resolved,
            ~RAnswers.Resolved.has,
            ps,
            RAnswers.Resolved{vs2, i}
          ),
          et => {==},
          ef2 => Ledgers.Id.is_eq_refl(i)
        )
      )
    )
  )

# Status.mark_follows, with the version j that sets the mark
def Status.mark_follows.of(
  +vs: List<&2, Types.Entry>,
  +vs2: List<&2, Types.Entry>,
  +zs: List<&2, Types.Entry>,
  +ez: {vs2 == List.append(&2, Types.Entry, vs, zs): List<&2, Types.Entry>},
  +m: String,
  +k: Nat,
  +j: Nat,
  +ej: {
    Lists.List.index(~Types.Entry, ~String, ~RAnswers.Entry.marks, vs, m) == Some{j}: Maybe<&2, Nat>
  }
) -> {
  Spec.Status.follows(
    RAnswers.Status.mark(vs, m, k),
    RAnswers.Status.mark(vs2, m, k)
  )
    == True{}: Bool
}:
  Eq.up(
    Maybe<&2, Nat>,
    y => {
      Spec.Status.follows(
        Bool.pick(
          Spec.Status,
          Shared.Maybe.is_eq(~Nat, ~Nat.is_eq, y, Some{k}),
          Spec.Status.Written{},
          Spec.Status.Stale{}
        ),
        RAnswers.Status.mark(vs2, m, k)
      )
        == True{}: Bool
    },
    Lists.List.index(~Types.Entry, ~String, ~RAnswers.Entry.marks, vs, m),
    Some{j},
    ej,
    Eq.up(
      Maybe<&2, Nat>,
      y => {
        Spec.Status.follows(
          Bool.pick(
            Spec.Status,
            Shared.Maybe.is_eq(~Nat, ~Nat.is_eq, Some{j}, Some{k}),
            Spec.Status.Written{},
            Spec.Status.Stale{}
          ),
          Bool.pick(
            Spec.Status,
            Shared.Maybe.is_eq(~Nat, ~Nat.is_eq, y, Some{k}),
            Spec.Status.Written{},
            Spec.Status.Stale{}
          )
        )
          == True{}: Bool
      },
      Lists.List.index(~Types.Entry, ~String, ~RAnswers.Entry.marks, vs2, m),
      Some{j},
      Lists.List.index_ext(
        ~Types.Entry,
        ~String,
        ~RAnswers.Entry.marks,
        vs,
        vs2,
        m,
        j
      )((zs, ez))(ej),
      Status.follows_refl(
        Bool.pick(
          Spec.Status,
          Shared.Maybe.is_eq(~Nat, ~Nat.is_eq, Some{j}, Some{k}),
          Spec.Status.Written{},
          Spec.Status.Stale{}
        )
      )
    )
  )

# the status of a mark among an extension follows its status among vs, when a
# version of vs sets the mark
def Status.mark_follows(
  +vs: List<&2, Types.Entry>,
  +vs2: List<&2, Types.Entry>,
  +zs: List<&2, Types.Entry>,
  +ez: {vs2 == List.append(&2, Types.Entry, vs, zs): List<&2, Types.Entry>},
  +m: String,
  +k: Nat,
  r: Exists(
    Nat,
    j => {
      Lists.List.index(
        ~Types.Entry,
        ~String,
        ~RAnswers.Entry.marks,
        vs,
        m
      )
        == Some{j}: Maybe<&2, Nat>
    }
  )
) -> {
  Spec.Status.follows(
    RAnswers.Status.mark(vs, m, k),
    RAnswers.Status.mark(vs2, m, k)
  )
    == True{}: Bool
}:
  (j, ej) = r
  Status.mark_follows.of(vs, vs2, zs, ez, m, k, j, ej)

# the status of a version among an extension follows its status among vs
def Status.of_follows(
  +name: String,
  +s: Facts.Facts(),
  +s2: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  e: Types.Entry,
  +vs: List<&2, Types.Entry>,
  +vs2: List<&2, Types.Entry>,
  +zs: List<&2, Types.Entry>,
  +ez: {vs2 == List.append(&2, Types.Entry, vs, zs): List<&2, Types.Entry>},
  +hw: {Facts.Facts.wider(s, s2) == True{}: Bool},
  +hl: {Facts.Facts.liars(s2) == []: List<&2, String>},
  +ho: {Facts.Facts.ok(name, s2) == True{}: Bool}
) -> {
  List.get(&2, Types.Entry, vs, k) == Some{e}: Maybe<&2, Types.Entry>
} -> {
  Spec.Status.follows(
    Answers.Status.of(s, c, vs, k, e),
    Answers.Status.of(s2, c, vs2, k, e)
  )
    == True{}: Bool
}:
  match e:
    case Types.Entry{Types.Pick{Types.Ask{+i, +n, Spec.Request.Start{os}}, +pins}, +slot}:
      eg => {==}
    case Types.Entry{Types.Pick{Types.Ask{+i, +n, Spec.Request.Write{b, p, w}}, +pins}, +slot}:
      eg => {==}
    case Types.Entry{Types.Pick{Types.Ask{+i, +n, Spec.Request.Resolve{m, p, w}}, +pins}, +slot}:
      eg => {==}
    case Types.Entry{Types.Pick{Types.Ask{+i, +n, Spec.Request.Move{b, t, v}}, +pins}, +slot}:
      eg => {==}
    case Types.Entry{Types.Pick{Types.Ask{+i, +n, Spec.Request.Group{h, g, ms}}, +pins}, +slot}:
      eg => {==}
    case Types.Entry{Types.Pick{Types.Ask{+i, +n, Spec.Request.Own{l, g}}, +pins}, +slot}:
      eg => {==}
    case Types.Entry{Types.Pick{Types.Ask{+i, +n, Spec.Request.Merge{+f, +x}}, +pins}, +slot}:
      eg => Status.merge_follows(
        name,
        s,
        s2,
        c,
        k,
        Types.Entry{Types.Pick{Types.Ask{i, n, Spec.Request.Merge{f, x}}, pins}, slot},
        vs,
        vs2,
        zs,
        ez,
        i,
        hw,
        hl,
        ho
      )
    case Types.Entry{Types.Pick{Types.Ask{+i, +n, Spec.Request.Mark{+b, +m, +v}}, +pins}, +slot}:
      eg => Status.mark_follows(
        vs,
        vs2,
        zs,
        ez,
        m,
        k,
        Lists.List.index_some(
          ~Types.Entry,
          ~String,
          ~RAnswers.Entry.marks,
          vs,
          m,
          k,
          Types.Entry{Types.Pick{Types.Ask{i, n, Spec.Request.Mark{b, m, v}}, pins}, slot}
        )(eg)(Texts.String.eq_refl(m))
      )

# the id of a version stays
def Case.version(
  +name: String,
  +s: Facts.Facts(),
  +s2: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +a: Spec.Reply,
  +hw: {Facts.Facts.wider(s, s2) == True{}: Bool},
  +hl: {Facts.Facts.liars(s2) == []: List<&2, String>},
  +ho: {Facts.Facts.ok(name, s2) == True{}: Bool}
) -> {
  Answers.Answer.of(s, Spec.Question.Version{c, k}) == Some{a}: Maybe<&2, Spec.Reply>
} -> Moved(s2, Spec.Question.Version{c, k}, a):
  ha => Lists.Maybe.by(
    Types.Entry,
    m => {
      RAnswers.Reply.id(m) == Some{a}: Maybe<&2, Spec.Reply>
    } -> Moved(s2, Spec.Question.Version{c, k}, a),
    Lines.Line.at(s, c, k),
    en => ha => None.elim(Spec.Reply, Moved(s2, Spec.Question.Version{c, k}, a), a, ha),
    +e => +ee => +ha => Moved.same(
      s2,
      Spec.Question.Version{c, k},
      a,
      Eq.up(
        Maybe<&2, Types.Entry>,
        m => {RAnswers.Reply.id(m) == Some{a}: Maybe<&2, Spec.Reply>},
        Lines.Line.at(s2, c, k),
        Some{e},
        Stays.Line.at_stays(name, s, s2, c, k, e)(hw)(hl)(ho)(ee),
        ha
      )
    )
  )(ha)

# the parents of a version stay
def Case.parents(
  +name: String,
  +s: Facts.Facts(),
  +s2: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +a: Spec.Reply,
  +hw: {Facts.Facts.wider(s, s2) == True{}: Bool},
  +hl: {Facts.Facts.liars(s2) == []: List<&2, String>},
  +ho: {Facts.Facts.ok(name, s2) == True{}: Bool}
) -> {
  Answers.Answer.of(s, Spec.Question.Parents{c, k}) == Some{a}: Maybe<&2, Spec.Reply>
} -> Moved(s2, Spec.Question.Parents{c, k}, a):
  ha => Lists.Maybe.by(
    Types.Entry,
    m => {
      RAnswers.Reply.parents(c, k, m) == Some{a}: Maybe<&2, Spec.Reply>
    } -> Moved(s2, Spec.Question.Parents{c, k}, a),
    Lines.Line.at(s, c, k),
    en => ha => None.elim(Spec.Reply, Moved(s2, Spec.Question.Parents{c, k}, a), a, ha),
    +e => +ee => +ha => Moved.same(
      s2,
      Spec.Question.Parents{c, k},
      a,
      Eq.up(
        Maybe<&2, Types.Entry>,
        m => {RAnswers.Reply.parents(c, k, m) == Some{a}: Maybe<&2, Spec.Reply>},
        Lines.Line.at(s2, c, k),
        Some{e},
        Stays.Line.at_stays(name, s, s2, c, k, e)(hw)(hl)(ho)(ee),
        ha
      )
    )
  )(ha)

# the content of a version stays
def Case.content(
  +name: String,
  +s: Facts.Facts(),
  +s2: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +a: Spec.Reply,
  +hw: {Facts.Facts.wider(s, s2) == True{}: Bool},
  +hl: {Facts.Facts.liars(s2) == []: List<&2, String>},
  +ho: {Facts.Facts.ok(name, s2) == True{}: Bool}
) -> {
  Answers.Answer.of(s, Spec.Question.Content{c, k}) == Some{a}: Maybe<&2, Spec.Reply>
} -> Moved(s2, Spec.Question.Content{c, k}, a):
  ha => Lists.Maybe.by(
    Files.Files(),
    m => {
      RAnswers.Reply.hash(m) == Some{a}: Maybe<&2, Spec.Reply>
    } -> Moved(s2, Spec.Question.Content{c, k}, a),
    Contents.Content.of(s, c, k),
    en => ha => None.elim(Spec.Reply, Moved(s2, Spec.Question.Content{c, k}, a), a, ha),
    +t => +et => +ha => Moved.same(
      s2,
      Spec.Question.Content{c, k},
      a,
      Eq.up(
        Maybe<&2, Files.Files()>,
        m => {RAnswers.Reply.hash(m) == Some{a}: Maybe<&2, Spec.Reply>},
        Contents.Content.of(s2, c, k),
        Some{t},
        Reads.Content.of_stays(name, s, s2, c, k, t)(hw)(hl)(ho)(et),
        ha
      )
    )
  )(ha)

# what a change affects stays
def Case.affects(
  +name: String,
  +s: Facts.Facts(),
  +s2: Facts.Facts(),
  +c: Ledgers.Line,
  +x: Nat,
  +y: Nat,
  +us: List<&2, String>,
  +bs: List<&2, String>,
  +a: Spec.Reply,
  +hw: {Facts.Facts.wider(s, s2) == True{}: Bool},
  +hl: {Facts.Facts.liars(s2) == []: List<&2, String>},
  +ho: {Facts.Facts.ok(name, s2) == True{}: Bool}
) -> {
  Answers.Answer.of(s, Spec.Question.Affects{c, x, y, us, bs}) == Some{a}: Maybe<&2, Spec.Reply>
} -> Moved(s2, Spec.Question.Affects{c, x, y, us, bs}, a):
  ha => Lists.Maybe.by(
    Files.Files(),
    m => {
      RAnswers.Affects.of(m, Contents.Content.of(s, c, y), us, bs) == Some{a}: Maybe<&2, Spec.Reply>
    } -> Moved(s2, Spec.Question.Affects{c, x, y, us, bs}, a),
    Contents.Content.of(s, c, x),
    en => ha => None.elim(Spec.Reply, Moved(s2, Spec.Question.Affects{c, x, y, us, bs}, a), a, ha),
    +t1 => +e1 => +ha => Lists.Maybe.by(
      Files.Files(),
      m => {
        RAnswers.Affects.of(Some{t1}, m, us, bs) == Some{a}: Maybe<&2, Spec.Reply>
      } -> Moved(s2, Spec.Question.Affects{c, x, y, us, bs}, a),
      Contents.Content.of(s, c, y),
      en => ha => None.elim(
        Spec.Reply,
        Moved(s2, Spec.Question.Affects{c, x, y, us, bs}, a),
        a,
        ha
      ),
      +t2 => +e3 => +ha => Moved.same(
        s2,
        Spec.Question.Affects{c, x, y, us, bs},
        a,
        Eq.up(
          Maybe<&2, Files.Files()>,
          m => {
            RAnswers.Affects.of(
              m,
              Contents.Content.of(s2, c, y),
              us,
              bs
            )
              == Some{a}: Maybe<&2, Spec.Reply>
          },
          Contents.Content.of(s2, c, x),
          Some{t1},
          Reads.Content.of_stays(name, s, s2, c, x, t1)(hw)(hl)(ho)(e1),
          Eq.up(
            Maybe<&2, Files.Files()>,
            m => {RAnswers.Affects.of(Some{t1}, m, us, bs) == Some{a}: Maybe<&2, Spec.Reply>},
            Contents.Content.of(s2, c, y),
            Some{t2},
            Reads.Content.of_stays(name, s, s2, c, y, t2)(hw)(hl)(ho)(e3),
            ha
          )
        )
      )
    )(ha)
  )(ha)

# the nodes of the owner group of a version stay
def Case.group(
  +name: String,
  +s: Facts.Facts(),
  +s2: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +a: Spec.Reply,
  +hw: {Facts.Facts.wider(s, s2) == True{}: Bool},
  +hl: {Facts.Facts.liars(s2) == []: List<&2, String>},
  +ho: {Facts.Facts.ok(name, s2) == True{}: Bool}
) -> {
  Answers.Answer.of(s, Spec.Question.Group{c, k}) == Some{a}: Maybe<&2, Spec.Reply>
} -> Moved(s2, Spec.Question.Group{c, k}, a):
  ha => Lists.Maybe.by(
    RLines.Rule,
    m => {
      Maybe.bind(
        &2,
        RLines.Rule,
        Spec.Reply,
        m,
        RAnswers.Rule.group
      )
        == Some{a}: Maybe<&2, Spec.Reply>
    } -> Moved(s2, Spec.Question.Group{c, k}, a),
    Answers.Rule.for(s, c, k),
    en => ha => None.elim(Spec.Reply, Moved(s2, Spec.Question.Group{c, k}, a), a, ha),
    +u => +eu => +ha => Moved.same(
      s2,
      Spec.Question.Group{c, k},
      a,
      Eq.up(
        Maybe<&2, RLines.Rule>,
        m => {
          Maybe.bind(
            &2,
            RLines.Rule,
            Spec.Reply,
            m,
            RAnswers.Rule.group
          )
            == Some{a}: Maybe<&2, Spec.Reply>
        },
        Answers.Rule.for(s2, c, k),
        Some{u},
        Rule.for_stays(name, s, s2, c, k, u, hw, hl, ho)(eu),
        ha
      )
    )
  )(ha)

# the owner group of a version stays
def Case.owner(
  +name: String,
  +s: Facts.Facts(),
  +s2: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +a: Spec.Reply,
  +hw: {Facts.Facts.wider(s, s2) == True{}: Bool},
  +hl: {Facts.Facts.liars(s2) == []: List<&2, String>},
  +ho: {Facts.Facts.ok(name, s2) == True{}: Bool}
) -> {
  Answers.Answer.of(s, Spec.Question.Owner{c, k}) == Some{a}: Maybe<&2, Spec.Reply>
} -> Moved(s2, Spec.Question.Owner{c, k}, a):
  ha => Lists.Maybe.by(
    RLines.Rule,
    m => {
      Maybe.bind(
        &2,
        RLines.Rule,
        Spec.Reply,
        m,
        RAnswers.Rule.owner
      )
        == Some{a}: Maybe<&2, Spec.Reply>
    } -> Moved(s2, Spec.Question.Owner{c, k}, a),
    Answers.Rule.for(s, c, k),
    en => ha => None.elim(Spec.Reply, Moved(s2, Spec.Question.Owner{c, k}, a), a, ha),
    +u => +eu => +ha => Moved.same(
      s2,
      Spec.Question.Owner{c, k},
      a,
      Eq.up(
        Maybe<&2, RLines.Rule>,
        m => {
          Maybe.bind(
            &2,
            RLines.Rule,
            Spec.Reply,
            m,
            RAnswers.Rule.owner
          )
            == Some{a}: Maybe<&2, Spec.Reply>
        },
        Answers.Rule.for(s2, c, k),
        Some{u},
        Rule.for_stays(name, s, s2, c, k, u, hw, hl, ho)(eu),
        ha
      )
    )
  )(ha)

# the era of a version stays
def Case.era(
  +name: String,
  +s: Facts.Facts(),
  +s2: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +a: Spec.Reply,
  +hw: {Facts.Facts.wider(s, s2) == True{}: Bool},
  +hl: {Facts.Facts.liars(s2) == []: List<&2, String>},
  +ho: {Facts.Facts.ok(name, s2) == True{}: Bool}
) -> {
  Answers.Answer.of(s, Spec.Question.Era{c, k}) == Some{a}: Maybe<&2, Spec.Reply>
} -> Moved(s2, Spec.Question.Era{c, k}, a):
  ha => Lists.Maybe.by(
    Nat,
    m => {
      RAnswers.Reply.number(m) == Some{a}: Maybe<&2, Spec.Reply>
    } -> Moved(s2, Spec.Question.Era{c, k}, a),
    Answers.Era.for(s, c, k),
    en => ha => None.elim(Spec.Reply, Moved(s2, Spec.Question.Era{c, k}, a), a, ha),
    +n => +en2 => +ha => Moved.same(
      s2,
      Spec.Question.Era{c, k},
      a,
      Eq.up(
        Maybe<&2, Nat>,
        m => {RAnswers.Reply.number(m) == Some{a}: Maybe<&2, Spec.Reply>},
        Answers.Era.for(s2, c, k),
        Some{n},
        Era.for_stays(name, s, s2, c, k, n, hw, hl, ho)(en2),
        ha
      )
    )
  )(ha)

# the voters of a version stay
def Case.owners(
  +name: String,
  +s: Facts.Facts(),
  +s2: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +a: Spec.Reply,
  +hw: {Facts.Facts.wider(s, s2) == True{}: Bool},
  +hl: {Facts.Facts.liars(s2) == []: List<&2, String>},
  +ho: {Facts.Facts.ok(name, s2) == True{}: Bool}
) -> {
  Answers.Answer.of(s, Spec.Question.Owners{c, k}) == Some{a}: Maybe<&2, Spec.Reply>
} -> Moved(s2, Spec.Question.Owners{c, k}, a):
  ha => Lists.Maybe.by(
    Types.Entry,
    m => {
      Answers.Owners.of(s, c, m, Answers.Rule.for(s, c, k)) == Some{a}: Maybe<&2, Spec.Reply>
    } -> Moved(s2, Spec.Question.Owners{c, k}, a),
    Lines.Line.at(s, c, k),
    en => ha => None.elim(Spec.Reply, Moved(s2, Spec.Question.Owners{c, k}, a), a, ha),
    +e => +ee => +ha => Lists.Maybe.by(
      RLines.Rule,
      m => {
        Answers.Owners.of(s, c, Some{e}, m) == Some{a}: Maybe<&2, Spec.Reply>
      } -> Moved(s2, Spec.Question.Owners{c, k}, a),
      Answers.Rule.for(s, c, k),
      en => ha => None.elim(Spec.Reply, Moved(s2, Spec.Question.Owners{c, k}, a), a, ha),
      +u => +eu => +ha => Moved.same(
        s2,
        Spec.Question.Owners{c, k},
        a,
        Eq.up(
          Maybe<&2, Types.Entry>,
          m => {
            Answers.Owners.of(
              s2,
              c,
              m,
              Answers.Rule.for(s2, c, k)
            )
              == Some{a}: Maybe<&2, Spec.Reply>
          },
          Lines.Line.at(s2, c, k),
          Some{e},
          Stays.Line.at_stays(name, s, s2, c, k, e)(hw)(hl)(ho)(ee),
          Eq.up(
            Maybe<&2, RLines.Rule>,
            m => {Answers.Owners.of(s2, c, Some{e}, m) == Some{a}: Maybe<&2, Spec.Reply>},
            Answers.Rule.for(s2, c, k),
            Some{u},
            Rule.for_stays(name, s, s2, c, k, u, hw, hl, ho)(eu),
            Rule.voters_stay(name, s, s2, c, e, u, a, hw, hl)(ha)
          )
        )
      )
    )(ha)
  )(ha)

# the members of a group stay
def Case.members(
  +name: String,
  +s: Facts.Facts(),
  +s2: Facts.Facts(),
  +r: Hashes.Hash,
  +g: String,
  +m: Nat,
  +a: Spec.Reply,
  +hw: {Facts.Facts.wider(s, s2) == True{}: Bool},
  +hl: {Facts.Facts.liars(s2) == []: List<&2, String>},
  +ho: {Facts.Facts.ok(name, s2) == True{}: Bool}
) -> {
  Answers.Answer.of(s, Spec.Question.Members{r, g, m}) == Some{a}: Maybe<&2, Spec.Reply>
} -> Moved(s2, Spec.Question.Members{r, g, m}, a):
  ha => Lists.Maybe.by(
    List<&2, Types.Entry>,
    v => {
      RAnswers.Reply.names(
        RAnswers.Store.read.of(List<&2, String>, m, R => Groups.Groups.members(R, r, g, m), v)
      )
        == Some{a}: Maybe<&2, Spec.Reply>
    } -> Moved(s2, Spec.Question.Members{r, g, m}, a),
    Lines.Line.versions(s, Ledgers.Line{r, None{}}),
    en => ha => None.elim(Spec.Reply, Moved(s2, Spec.Question.Members{r, g, m}, a), a, ha),
    +vs => +ev => +ha => Lists.Bool.by(
      b => {
        RAnswers.Reply.names(
          Shared.Maybe.when(List<&2, String>, b, u => Groups.Groups.members(vs, r, g, m))
        )
          == Some{a}: Maybe<&2, Spec.Reply>
      } -> Moved(s2, Spec.Question.Members{r, g, m}, a),
      Nat.is_lt(m, List.length(&2, Types.Entry, vs)),
      +elt => +ha => Line.versions_by(
        Moved(s2, Spec.Question.Members{r, g, m}, a),
        name,
        s,
        s2,
        Ledgers.Line{r, None{}},
        vs,
        hw,
        hl,
        ho,
        ev,
        +vs2 => +zs => +e2 => +ez => Moved.same(
          s2,
          Spec.Question.Members{r, g, m},
          a,
          Eq.up(
            Maybe<&2, List<&2, Types.Entry>>,
            v => {
              RAnswers.Reply.names(
                RAnswers.Store.read.of(
                  List<&2, String>,
                  m,
                  R => Groups.Groups.members(R, r, g, m),
                  v
                )
              )
                == Some{a}: Maybe<&2, Spec.Reply>
            },
            Lines.Line.versions(s2, Ledgers.Line{r, None{}}),
            Some{vs2},
            e2,
            Eq.up(
              Bool,
              b => {
                RAnswers.Reply.names(
                  Shared.Maybe.when(List<&2, String>, b, u => Groups.Groups.members(vs2, r, g, m))
                )
                  == Some{a}: Maybe<&2, Spec.Reply>
              },
              Nat.is_lt(m, List.length(&2, Types.Entry, vs2)),
              True{},
              Ext.lt(vs, vs2, zs, ez, m)(elt),
              Eq.up(
                Maybe<&2, List<&2, String>>,
                y => {RAnswers.Reply.names(y) == Some{a}: Maybe<&2, Spec.Reply>},
                Groups.Groups.members(vs2, r, g, m),
                Groups.Groups.members(vs, r, g, m),
                Groups.Groups.members_take(vs2, vs, r, g, m, Ext.take(vs, vs2, zs, ez, m)(elt)),
                ha
              )
            )
          )
        )
      ),
      ef => ha => None.elim(Spec.Reply, Moved(s2, Spec.Question.Members{r, g, m}, a), a, ha)
    )(ha)
  )(ha)

# the nodes of a group stay
def Case.nodes(
  +name: String,
  +s: Facts.Facts(),
  +s2: Facts.Facts(),
  +r: Hashes.Hash,
  +g: String,
  +m: Nat,
  +a: Spec.Reply,
  +hw: {Facts.Facts.wider(s, s2) == True{}: Bool},
  +hl: {Facts.Facts.liars(s2) == []: List<&2, String>},
  +ho: {Facts.Facts.ok(name, s2) == True{}: Bool}
) -> {
  Answers.Answer.of(s, Spec.Question.Nodes{r, g, m}) == Some{a}: Maybe<&2, Spec.Reply>
} -> Moved(s2, Spec.Question.Nodes{r, g, m}, a):
  ha => Lists.Maybe.by(
    List<&2, Types.Entry>,
    v => {
      RAnswers.Reply.names(
        RAnswers.Store.read.of(List<&2, String>, m, R => Groups.Groups.nodes(R, r, g, m), v)
      )
        == Some{a}: Maybe<&2, Spec.Reply>
    } -> Moved(s2, Spec.Question.Nodes{r, g, m}, a),
    Lines.Line.versions(s, Ledgers.Line{r, None{}}),
    en => ha => None.elim(Spec.Reply, Moved(s2, Spec.Question.Nodes{r, g, m}, a), a, ha),
    +vs => +ev => +ha => Lists.Bool.by(
      b => {
        RAnswers.Reply.names(
          Shared.Maybe.when(List<&2, String>, b, u => Groups.Groups.nodes(vs, r, g, m))
        )
          == Some{a}: Maybe<&2, Spec.Reply>
      } -> Moved(s2, Spec.Question.Nodes{r, g, m}, a),
      Nat.is_lt(m, List.length(&2, Types.Entry, vs)),
      +elt => +ha => Line.versions_by(
        Moved(s2, Spec.Question.Nodes{r, g, m}, a),
        name,
        s,
        s2,
        Ledgers.Line{r, None{}},
        vs,
        hw,
        hl,
        ho,
        ev,
        +vs2 => +zs => +e2 => +ez => Moved.same(
          s2,
          Spec.Question.Nodes{r, g, m},
          a,
          Eq.up(
            Maybe<&2, List<&2, Types.Entry>>,
            v => {
              RAnswers.Reply.names(
                RAnswers.Store.read.of(List<&2, String>, m, R => Groups.Groups.nodes(R, r, g, m), v)
              )
                == Some{a}: Maybe<&2, Spec.Reply>
            },
            Lines.Line.versions(s2, Ledgers.Line{r, None{}}),
            Some{vs2},
            e2,
            Eq.up(
              Bool,
              b => {
                RAnswers.Reply.names(
                  Shared.Maybe.when(List<&2, String>, b, u => Groups.Groups.nodes(vs2, r, g, m))
                )
                  == Some{a}: Maybe<&2, Spec.Reply>
              },
              Nat.is_lt(m, List.length(&2, Types.Entry, vs2)),
              True{},
              Ext.lt(vs, vs2, zs, ez, m)(elt),
              Eq.up(
                Maybe<&2, List<&2, String>>,
                y => {RAnswers.Reply.names(y) == Some{a}: Maybe<&2, Spec.Reply>},
                Groups.Groups.nodes(vs2, r, g, m),
                Groups.Groups.nodes(vs, r, g, m),
                Groups.Groups.nodes_take(vs2, vs, r, g, m, Ext.take(vs, vs2, zs, ez, m)(elt)),
                ha
              )
            )
          )
        )
      ),
      ef => ha => None.elim(Spec.Reply, Moved(s2, Spec.Question.Nodes{r, g, m}, a), a, ha)
    )(ha)
  )(ha)

# whether a name is a group stays
def Case.is_group(
  +name: String,
  +s: Facts.Facts(),
  +s2: Facts.Facts(),
  +r: Hashes.Hash,
  +g: String,
  +m: Nat,
  +a: Spec.Reply,
  +hw: {Facts.Facts.wider(s, s2) == True{}: Bool},
  +hl: {Facts.Facts.liars(s2) == []: List<&2, String>},
  +ho: {Facts.Facts.ok(name, s2) == True{}: Bool}
) -> {
  Answers.Answer.of(s, Spec.Question.IsGroup{r, g, m}) == Some{a}: Maybe<&2, Spec.Reply>
} -> Moved(s2, Spec.Question.IsGroup{r, g, m}, a):
  ha => Lists.Maybe.by(
    List<&2, Types.Entry>,
    v => {
      RAnswers.Reply.yes(
        RAnswers.Store.read.of(Bool, m, R => Groups.Groups.is_group(R, r, g, m), v)
      )
        == Some{a}: Maybe<&2, Spec.Reply>
    } -> Moved(s2, Spec.Question.IsGroup{r, g, m}, a),
    Lines.Line.versions(s, Ledgers.Line{r, None{}}),
    en => ha => None.elim(Spec.Reply, Moved(s2, Spec.Question.IsGroup{r, g, m}, a), a, ha),
    +vs => +ev => +ha => Lists.Bool.by(
      b => {
        RAnswers.Reply.yes(
          Shared.Maybe.when(Bool, b, u => Groups.Groups.is_group(vs, r, g, m))
        )
          == Some{a}: Maybe<&2, Spec.Reply>
      } -> Moved(s2, Spec.Question.IsGroup{r, g, m}, a),
      Nat.is_lt(m, List.length(&2, Types.Entry, vs)),
      +elt => +ha => Line.versions_by(
        Moved(s2, Spec.Question.IsGroup{r, g, m}, a),
        name,
        s,
        s2,
        Ledgers.Line{r, None{}},
        vs,
        hw,
        hl,
        ho,
        ev,
        +vs2 => +zs => +e2 => +ez => Moved.same(
          s2,
          Spec.Question.IsGroup{r, g, m},
          a,
          Eq.up(
            Maybe<&2, List<&2, Types.Entry>>,
            v => {
              RAnswers.Reply.yes(
                RAnswers.Store.read.of(Bool, m, R => Groups.Groups.is_group(R, r, g, m), v)
              )
                == Some{a}: Maybe<&2, Spec.Reply>
            },
            Lines.Line.versions(s2, Ledgers.Line{r, None{}}),
            Some{vs2},
            e2,
            Eq.up(
              Bool,
              b => {
                RAnswers.Reply.yes(
                  Shared.Maybe.when(Bool, b, u => Groups.Groups.is_group(vs2, r, g, m))
                )
                  == Some{a}: Maybe<&2, Spec.Reply>
              },
              Nat.is_lt(m, List.length(&2, Types.Entry, vs2)),
              True{},
              Ext.lt(vs, vs2, zs, ez, m)(elt),
              Eq.up(
                Maybe<&2, Bool>,
                y => {RAnswers.Reply.yes(y) == Some{a}: Maybe<&2, Spec.Reply>},
                Groups.Groups.is_group(vs2, r, g, m),
                Groups.Groups.is_group(vs, r, g, m),
                Groups.Groups.is_group_take(vs2, vs, r, g, m, Ext.take(vs, vs2, zs, ez, m)(elt)),
                ha
              )
            )
          )
        )
      ),
      ef => ha => None.elim(Spec.Reply, Moved(s2, Spec.Question.IsGroup{r, g, m}, a), a, ha)
    )(ha)
  )(ha)

# the version that a mark names stays
def Case.mark(
  +name: String,
  +s: Facts.Facts(),
  +s2: Facts.Facts(),
  +c: Ledgers.Line,
  +m: String,
  +a: Spec.Reply,
  +hw: {Facts.Facts.wider(s, s2) == True{}: Bool},
  +hl: {Facts.Facts.liars(s2) == []: List<&2, String>},
  +ho: {Facts.Facts.ok(name, s2) == True{}: Bool}
) -> {
  Answers.Answer.of(s, Spec.Question.Mark{c, m}) == Some{a}: Maybe<&2, Spec.Reply>
} -> Moved(s2, Spec.Question.Mark{c, m}, a):
  ha => Lists.Maybe.by(
    List<&2, Types.Entry>,
    v => {
      RAnswers.Reply.number(RAnswers.Mark.of(m, v)) == Some{a}: Maybe<&2, Spec.Reply>
    } -> Moved(s2, Spec.Question.Mark{c, m}, a),
    Lines.Line.versions(s, c),
    en => ha => None.elim(Spec.Reply, Moved(s2, Spec.Question.Mark{c, m}, a), a, ha),
    +vs => +ev => +ha => Lists.Maybe.by(
      Nat,
      y => {
        RAnswers.Reply.number(RAnswers.Mark.at(vs, y)) == Some{a}: Maybe<&2, Spec.Reply>
      } -> Moved(s2, Spec.Question.Mark{c, m}, a),
      Lists.List.index(~Types.Entry, ~String, ~RAnswers.Entry.marks, vs, m),
      en => ha => None.elim(Spec.Reply, Moved(s2, Spec.Question.Mark{c, m}, a), a, ha),
      +j => +ej => +ha => Lists.Maybe.by(
        Types.Entry,
        y => {
          RAnswers.Reply.number(RAnswers.Mark.in(y)) == Some{a}: Maybe<&2, Spec.Reply>
        } -> Moved(s2, Spec.Question.Mark{c, m}, a),
        List.get(&2, Types.Entry, vs, j),
        en => ha => None.elim(Spec.Reply, Moved(s2, Spec.Question.Mark{c, m}, a), a, ha),
        +e => +eg => +ha => Line.versions_by(
          Moved(s2, Spec.Question.Mark{c, m}, a),
          name,
          s,
          s2,
          c,
          vs,
          hw,
          hl,
          ho,
          ev,
          +vs2 => +zs => +e2 => +ez => Moved.same(
            s2,
            Spec.Question.Mark{c, m},
            a,
            Eq.up(
              Maybe<&2, List<&2, Types.Entry>>,
              v => {
                RAnswers.Reply.number(RAnswers.Mark.of(m, v)) == Some{a}: Maybe<&2, Spec.Reply>
              },
              Lines.Line.versions(s2, c),
              Some{vs2},
              e2,
              Eq.up(
                Maybe<&2, Nat>,
                y => {
                  RAnswers.Reply.number(RAnswers.Mark.at(vs2, y)) == Some{a}: Maybe<&2, Spec.Reply>
                },
                Lists.List.index(~Types.Entry, ~String, ~RAnswers.Entry.marks, vs2, m),
                Some{j},
                Lists.List.index_ext(
                  ~Types.Entry,
                  ~String,
                  ~RAnswers.Entry.marks,
                  vs,
                  vs2,
                  m,
                  j
                )((zs, ez))(ej),
                Eq.up(
                  Maybe<&2, Types.Entry>,
                  y => {
                    RAnswers.Reply.number(RAnswers.Mark.in(y)) == Some{a}: Maybe<&2, Spec.Reply>
                  },
                  List.get(&2, Types.Entry, vs2, j),
                  Some{e},
                  Lists.List.ext_get(Types.Entry, vs, vs2, j, e)((zs, ez))(eg),
                  ha
                )
              )
            )
          )
        )
      )(ha)
    )(ha)
  )(ha)

# the count of a line does not go back
def Case.count(
  +name: String,
  +s: Facts.Facts(),
  +s2: Facts.Facts(),
  +c: Ledgers.Line,
  +a: Spec.Reply,
  +hw: {Facts.Facts.wider(s, s2) == True{}: Bool},
  +hl: {Facts.Facts.liars(s2) == []: List<&2, String>},
  +ho: {Facts.Facts.ok(name, s2) == True{}: Bool}
) -> {
  Answers.Answer.of(s, Spec.Question.Count{c}) == Some{a}: Maybe<&2, Spec.Reply>
} -> Moved(s2, Spec.Question.Count{c}, a):
  ha => Lists.Maybe.by(
    List<&2, Types.Entry>,
    v => {
      RAnswers.Reply.count(v) == Some{a}: Maybe<&2, Spec.Reply>
    } -> Moved(s2, Spec.Question.Count{c}, a),
    Lines.Line.versions(s, c),
    en => ha => None.elim(Spec.Reply, Moved(s2, Spec.Question.Count{c}, a), a, ha),
    +vs => +ev => +ha => Line.versions_by(
      Moved(s2, Spec.Question.Count{c}, a),
      name,
      s,
      s2,
      c,
      vs,
      hw,
      hl,
      ho,
      ev,
      +vs2 => +zs => +e2 => +ez => Moved.to(
        s2,
        Spec.Question.Count{c},
        Spec.Reply.Number{List.length(&2, Types.Entry, vs)},
        a,
        ha,
        (
          Spec.Reply.Number{List.length(&2, Types.Entry, vs2)},
          (
            Eq.up(
              Maybe<&2, List<&2, Types.Entry>>,
              v => {
                RAnswers.Reply.count(
                  v
                )
                  == Some{
                    Spec.Reply.Number{List.length(&2, Types.Entry, vs2)}
                  }: Maybe<&2, Spec.Reply>
              },
              Lines.Line.versions(s2, c),
              Some{vs2},
              e2,
              {==}
            ),
            Lists.List.ext_length(Types.Entry, vs, vs2)((zs, ez))
          )
        )
      )
    )
  )(ha)

# the request of an id stays
def Case.request(
  +name: String,
  +s: Facts.Facts(),
  +s2: Facts.Facts(),
  +c: Ledgers.Line,
  +i: Ledgers.Id,
  +a: Spec.Reply,
  +hw: {Facts.Facts.wider(s, s2) == True{}: Bool},
  +hl: {Facts.Facts.liars(s2) == []: List<&2, String>},
  +ho: {Facts.Facts.ok(name, s2) == True{}: Bool}
) -> {
  Answers.Answer.of(s, Spec.Question.Request{c, i}) == Some{a}: Maybe<&2, Spec.Reply>
} -> Moved(s2, Spec.Question.Request{c, i}, a):
  ha => Lists.Maybe.by(
    List<&2, Types.Entry>,
    v => {
      RAnswers.Reply.ask(RAnswers.Line.find.of(i, v)) == Some{a}: Maybe<&2, Spec.Reply>
    } -> Moved(s2, Spec.Question.Request{c, i}, a),
    Lines.Line.versions(s, c),
    en => ha => None.elim(Spec.Reply, Moved(s2, Spec.Question.Request{c, i}, a), a, ha),
    +vs => +ev => +ha => Find.by(
      f => {
        RAnswers.Reply.ask(f) == Some{a}: Maybe<&2, Spec.Reply>
      } -> Moved(s2, Spec.Question.Request{c, i}, a),
      vs,
      i,
      ha => None.elim(Spec.Reply, Moved(s2, Spec.Question.Request{c, i}, a), a, ha),
      +j => +x => +ei => +eg => +ha => Line.versions_by(
        Moved(s2, Spec.Question.Request{c, i}, a),
        name,
        s,
        s2,
        c,
        vs,
        hw,
        hl,
        ho,
        ev,
        +vs2 => +zs => +e2 => +ez => Moved.same(
          s2,
          Spec.Question.Request{c, i},
          a,
          Eq.up(
            Maybe<&2, List<&2, Types.Entry>>,
            v => {
              RAnswers.Reply.ask(RAnswers.Line.find.of(i, v)) == Some{a}: Maybe<&2, Spec.Reply>
            },
            Lines.Line.versions(s2, c),
            Some{vs2},
            e2,
            Eq.up(
              Maybe<&2, RKnown.Found>,
              f => {RAnswers.Reply.ask(f) == Some{a}: Maybe<&2, Spec.Reply>},
              RAnswers.Versions.find(vs2, i),
              Some{RKnown.Found{j, x}},
              Find.ext(vs, vs2, zs, ez, i, j, x, ei, eg),
              ha
            )
          )
        )
      )
    )(ha)
  )(ha)

# the paths that clash in a merge stay
def Case.clashes(
  +name: String,
  +s: Facts.Facts(),
  +s2: Facts.Facts(),
  +c: Ledgers.Line,
  +i: Ledgers.Id,
  +a: Spec.Reply,
  +hw: {Facts.Facts.wider(s, s2) == True{}: Bool},
  +hl: {Facts.Facts.liars(s2) == []: List<&2, String>},
  +ho: {Facts.Facts.ok(name, s2) == True{}: Bool}
) -> {
  Answers.Answer.of(s, Spec.Question.Clashes{c, i}) == Some{a}: Maybe<&2, Spec.Reply>
} -> Moved(s2, Spec.Question.Clashes{c, i}, a):
  ha => Lists.Maybe.by(
    List<&2, Types.Entry>,
    v => {
      RAnswers.Reply.names(
        RAnswers.Found.then(
          List<&2, String>,
          RAnswers.Line.find.of(i, v),
          k => e => Answers.Clashes.of(s, c, k, e)
        )
      )
        == Some{a}: Maybe<&2, Spec.Reply>
    } -> Moved(s2, Spec.Question.Clashes{c, i}, a),
    Lines.Line.versions(s, c),
    en => ha => None.elim(Spec.Reply, Moved(s2, Spec.Question.Clashes{c, i}, a), a, ha),
    +vs => +ev => +ha => Find.by(
      f => {
        RAnswers.Reply.names(
          RAnswers.Found.then(List<&2, String>, f, k => e => Answers.Clashes.of(s, c, k, e))
        )
          == Some{a}: Maybe<&2, Spec.Reply>
      } -> Moved(s2, Spec.Question.Clashes{c, i}, a),
      vs,
      i,
      ha => None.elim(Spec.Reply, Moved(s2, Spec.Question.Clashes{c, i}, a), a, ha),
      +j => +x => +ei => +eg => +ha => Lists.Maybe.by(
        List<&2, String>,
        y => {
          RAnswers.Reply.names(y) == Some{a}: Maybe<&2, Spec.Reply>
        } -> Moved(s2, Spec.Question.Clashes{c, i}, a),
        Answers.Clashes.of(s, c, j, x),
        en => ha => None.elim(Spec.Reply, Moved(s2, Spec.Question.Clashes{c, i}, a), a, ha),
        +z => +ep => +ha => Line.versions_by(
          Moved(s2, Spec.Question.Clashes{c, i}, a),
          name,
          s,
          s2,
          c,
          vs,
          hw,
          hl,
          ho,
          ev,
          +vs2 => +zs => +e2 => +ez => Moved.same(
            s2,
            Spec.Question.Clashes{c, i},
            a,
            Eq.up(
              Maybe<&2, List<&2, Types.Entry>>,
              v => {
                RAnswers.Reply.names(
                  RAnswers.Found.then(
                    List<&2, String>,
                    RAnswers.Line.find.of(i, v),
                    k => e => Answers.Clashes.of(s2, c, k, e)
                  )
                )
                  == Some{a}: Maybe<&2, Spec.Reply>
              },
              Lines.Line.versions(s2, c),
              Some{vs2},
              e2,
              Eq.up(
                Maybe<&2, RKnown.Found>,
                f => {
                  RAnswers.Reply.names(
                    RAnswers.Found.then(
                      List<&2, String>,
                      f,
                      k => e => Answers.Clashes.of(s2, c, k, e)
                    )
                  )
                    == Some{a}: Maybe<&2, Spec.Reply>
                },
                RAnswers.Versions.find(vs2, i),
                Some{RKnown.Found{j, x}},
                Find.ext(vs, vs2, zs, ez, i, j, x, ei, eg),
                Eq.up(
                  Maybe<&2, List<&2, String>>,
                  y => {RAnswers.Reply.names(y) == Some{a}: Maybe<&2, Spec.Reply>},
                  Answers.Clashes.of(s2, c, j, x),
                  Some{z},
                  Clashes.of_stays(name, s, s2, c, j, x, z, hw, hl, ho)(ep),
                  ha
                )
              )
            )
          )
        )
      )(ha)
    )(ha)
  )(ha)

# the base of a merge stays
def Case.base(
  +name: String,
  +s: Facts.Facts(),
  +s2: Facts.Facts(),
  +c: Ledgers.Line,
  +i: Ledgers.Id,
  +a: Spec.Reply,
  +hw: {Facts.Facts.wider(s, s2) == True{}: Bool},
  +hl: {Facts.Facts.liars(s2) == []: List<&2, String>},
  +ho: {Facts.Facts.ok(name, s2) == True{}: Bool}
) -> {
  Answers.Answer.of(s, Spec.Question.Base{c, i}) == Some{a}: Maybe<&2, Spec.Reply>
} -> Moved(s2, Spec.Question.Base{c, i}, a):
  ha => Lists.Maybe.by(
    List<&2, Types.Entry>,
    v => {
      RAnswers.Reply.point(
        RAnswers.Found.then(
          Spec.Point,
          RAnswers.Line.find.of(i, v),
          k => e => Answers.Base.of(s, c, k, e)
        )
      )
        == Some{a}: Maybe<&2, Spec.Reply>
    } -> Moved(s2, Spec.Question.Base{c, i}, a),
    Lines.Line.versions(s, c),
    en => ha => None.elim(Spec.Reply, Moved(s2, Spec.Question.Base{c, i}, a), a, ha),
    +vs => +ev => +ha => Find.by(
      f => {
        RAnswers.Reply.point(
          RAnswers.Found.then(Spec.Point, f, k => e => Answers.Base.of(s, c, k, e))
        )
          == Some{a}: Maybe<&2, Spec.Reply>
      } -> Moved(s2, Spec.Question.Base{c, i}, a),
      vs,
      i,
      ha => None.elim(Spec.Reply, Moved(s2, Spec.Question.Base{c, i}, a), a, ha),
      +j => +x => +ei => +eg => +ha => Lists.Maybe.by(
        Spec.Point,
        y => {
          RAnswers.Reply.point(y) == Some{a}: Maybe<&2, Spec.Reply>
        } -> Moved(s2, Spec.Question.Base{c, i}, a),
        Answers.Base.of(s, c, j, x),
        en => ha => None.elim(Spec.Reply, Moved(s2, Spec.Question.Base{c, i}, a), a, ha),
        +z => +ep => +ha => Line.versions_by(
          Moved(s2, Spec.Question.Base{c, i}, a),
          name,
          s,
          s2,
          c,
          vs,
          hw,
          hl,
          ho,
          ev,
          +vs2 => +zs => +e2 => +ez => Moved.same(
            s2,
            Spec.Question.Base{c, i},
            a,
            Eq.up(
              Maybe<&2, List<&2, Types.Entry>>,
              v => {
                RAnswers.Reply.point(
                  RAnswers.Found.then(
                    Spec.Point,
                    RAnswers.Line.find.of(i, v),
                    k => e => Answers.Base.of(s2, c, k, e)
                  )
                )
                  == Some{a}: Maybe<&2, Spec.Reply>
              },
              Lines.Line.versions(s2, c),
              Some{vs2},
              e2,
              Eq.up(
                Maybe<&2, RKnown.Found>,
                f => {
                  RAnswers.Reply.point(
                    RAnswers.Found.then(Spec.Point, f, k => e => Answers.Base.of(s2, c, k, e))
                  )
                    == Some{a}: Maybe<&2, Spec.Reply>
                },
                RAnswers.Versions.find(vs2, i),
                Some{RKnown.Found{j, x}},
                Find.ext(vs, vs2, zs, ez, i, j, x, ei, eg),
                Eq.up(
                  Maybe<&2, Spec.Point>,
                  y => {RAnswers.Reply.point(y) == Some{a}: Maybe<&2, Spec.Reply>},
                  Answers.Base.of(s2, c, j, x),
                  Some{z},
                  Merge.base_stays(name, s, s2, c, j, x, z, hw, hl, ho)(ep),
                  ha
                )
              )
            )
          )
        )
      )(ha)
    )(ha)
  )(ha)

# the status of a request stays, or goes from Conflicted to Written
def Case.status(
  +name: String,
  +s: Facts.Facts(),
  +s2: Facts.Facts(),
  +c: Ledgers.Line,
  +i: Ledgers.Id,
  +a: Spec.Reply,
  +hw: {Facts.Facts.wider(s, s2) == True{}: Bool},
  +hl: {Facts.Facts.liars(s2) == []: List<&2, String>},
  +ho: {Facts.Facts.ok(name, s2) == True{}: Bool}
) -> {
  Answers.Answer.of(s, Spec.Question.Status{c, i}) == Some{a}: Maybe<&2, Spec.Reply>
} -> Moved(s2, Spec.Question.Status{c, i}, a):
  ha => Lists.Maybe.by(
    List<&2, Types.Entry>,
    v => {
      Answers.Reply.status(s, c, v, RAnswers.Line.find.of(i, v)) == Some{a}: Maybe<&2, Spec.Reply>
    } -> Moved(s2, Spec.Question.Status{c, i}, a),
    Lines.Line.versions(s, c),
    en => ha => None.elim(Spec.Reply, Moved(s2, Spec.Question.Status{c, i}, a), a, ha),
    +vs => +ev => +ha => Find.by(
      f => {
        Answers.Reply.status(s, c, Some{vs}, f) == Some{a}: Maybe<&2, Spec.Reply>
      } -> Moved(s2, Spec.Question.Status{c, i}, a),
      vs,
      i,
      ha => None.elim(Spec.Reply, Moved(s2, Spec.Question.Status{c, i}, a), a, ha),
      +j => +x => +ei => +eg => +ha => Line.versions_by(
        Moved(s2, Spec.Question.Status{c, i}, a),
        name,
        s,
        s2,
        c,
        vs,
        hw,
        hl,
        ho,
        ev,
        +vs2 => +zs => +e2 => +ez => Moved.to(
          s2,
          Spec.Question.Status{c, i},
          Spec.Reply.Status{Answers.Status.of(s, c, vs, j, x)},
          a,
          ha,
          (
            Spec.Reply.Status{Answers.Status.of(s2, c, vs2, j, x)},
            (
              Eq.up(
                Maybe<&2, List<&2, Types.Entry>>,
                v => {
                  Answers.Reply.status(
                    s2,
                    c,
                    v,
                    RAnswers.Line.find.of(i, v)
                  )
                    == Some{
                      Spec.Reply.Status{Answers.Status.of(s2, c, vs2, j, x)}
                    }: Maybe<&2, Spec.Reply>
                },
                Lines.Line.versions(s2, c),
                Some{vs2},
                e2,
                Eq.up(
                  Maybe<&2, RKnown.Found>,
                  f => {
                    Answers.Reply.status(
                      s2,
                      c,
                      Some{vs2},
                      f
                    )
                      == Some{
                        Spec.Reply.Status{Answers.Status.of(s2, c, vs2, j, x)}
                      }: Maybe<&2, Spec.Reply>
                  },
                  RAnswers.Versions.find(vs2, i),
                  Some{RKnown.Found{j, x}},
                  Find.ext(vs, vs2, zs, ez, i, j, x, ei, eg),
                  {==}
                )
              ),
              Status.of_follows(name, s, s2, c, j, x, vs, vs2, zs, ez, hw, hl, ho)(eg)
            )
          )
        )
      )
    )(ha)
  )(ha)

# the reply of a node to a question moves forward as its facts grow: the core
# form of VendNode.answer_moves_forward
def Core.answer_moves(
  +name: String,
  +s: Facts.Facts(),
  +s2: Facts.Facts(),
  +q: Spec.Question,
  +a: Spec.Reply
) -> {
  Facts.Facts.wider(s, s2) == True{}: Bool
} -> {
  Facts.Facts.liars(s2) == []: List<&2, String>
} -> {
  Facts.Facts.ok(name, s2) == True{}: Bool
} -> {
  Answers.Answer.of(s, q) == Some{a}: Maybe<&2, Spec.Reply>
} -> Exists(
  Spec.Reply,
  b => {Answers.Answer.of(s2, q) == Some{b}: Maybe<&2, Spec.Reply>} & Spec.Reply.Moves(q, a, b)
):
  match q:
    case Spec.Question.Status{+c, +i}:
      +hw => +hl => +ho => ha => Case.status(name, s, s2, c, i, a, hw, hl, ho)(ha)
    case Spec.Question.Request{+c, +i}:
      +hw => +hl => +ho => ha => Case.request(name, s, s2, c, i, a, hw, hl, ho)(ha)
    case Spec.Question.Version{+c, +k}:
      +hw => +hl => +ho => ha => Case.version(name, s, s2, c, k, a, hw, hl, ho)(ha)
    case Spec.Question.Content{+c, +k}:
      +hw => +hl => +ho => ha => Case.content(name, s, s2, c, k, a, hw, hl, ho)(ha)
    case Spec.Question.Group{+c, +k}:
      +hw => +hl => +ho => ha => Case.group(name, s, s2, c, k, a, hw, hl, ho)(ha)
    case Spec.Question.Owners{+c, +k}:
      +hw => +hl => +ho => ha => Case.owners(name, s, s2, c, k, a, hw, hl, ho)(ha)
    case Spec.Question.Members{+r, +g, +m}:
      +hw => +hl => +ho => ha => Case.members(name, s, s2, r, g, m, a, hw, hl, ho)(ha)
    case Spec.Question.Nodes{+r, +g, +m}:
      +hw => +hl => +ho => ha => Case.nodes(name, s, s2, r, g, m, a, hw, hl, ho)(ha)
    case Spec.Question.IsGroup{+r, +g, +m}:
      +hw => +hl => +ho => ha => Case.is_group(name, s, s2, r, g, m, a, hw, hl, ho)(ha)
    case Spec.Question.Mark{+c, +m}:
      +hw => +hl => +ho => ha => Case.mark(name, s, s2, c, m, a, hw, hl, ho)(ha)
    case Spec.Question.Count{+c}:
      +hw => +hl => +ho => ha => Case.count(name, s, s2, c, a, hw, hl, ho)(ha)
    case Spec.Question.Clashes{+c, +i}:
      +hw => +hl => +ho => ha => Case.clashes(name, s, s2, c, i, a, hw, hl, ho)(ha)
    case Spec.Question.Affects{+c, +x, +y, +us, +bs}:
      +hw => +hl => +ho => ha => Case.affects(name, s, s2, c, x, y, us, bs, a, hw, hl, ho)(ha)
    case Spec.Question.Parents{+c, +k}:
      +hw => +hl => +ho => ha => Case.parents(name, s, s2, c, k, a, hw, hl, ho)(ha)
    case Spec.Question.Base{+c, +i}:
      +hw => +hl => +ho => ha => Case.base(name, s, s2, c, i, a, hw, hl, ho)(ha)
    case Spec.Question.Owner{+c, +k}:
      +hw => +hl => +ho => ha => Case.owner(name, s, s2, c, k, a, hw, hl, ho)(ha)
    case Spec.Question.Era{+c, +k}:
      +hw => +hl => +ho => ha => Case.era(name, s, s2, c, k, a, hw, hl, ho)(ha)
