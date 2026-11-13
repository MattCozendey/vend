import Base
import ../shared/shared/ledger.bend as Ledgers
import ../shared/shared/shared/shared/hash.bend as Hashes
import ../shared/shared/shared/shared/shared.bend as Shared
import ../shared/shared/shared/text.bend as Texts
import ./answers.bend as Answers
import ./codes.bend as Coded
import ./content.bend as Contents
import ./facts.bend as Facts
import ./groups.bend as Groups
import ./lines.bend as Lines
import ./reads.bend as Reads
import ./shared/files.bend as Files
import ./shared/lists.bend as Lists
import ./spec.bend as Spec
import ./stays.bend as Stays
import ./types.bend as Types
import ./versions.bend as Versions

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
  Exists(Spec.Reply, b => {Answers.Answer.of(s2, q) == Some{b}: Maybe<&2, Spec.Reply>} & Spec.Reply.Moves(q, a, b))

# a reply that stays moved
def Moved.same(-s2: Facts.Facts(), +q: Spec.Question, +a: Spec.Reply, e: {Answers.Answer.of(s2, q) == Some{a}: Maybe<&2, Spec.Reply>}) -> Moved(s2, q, a):
  (a, (e, Reply.moves_refl(q, a)))
