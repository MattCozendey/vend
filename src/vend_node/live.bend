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

# the facts of a node stay sound when it works
def Work.does_ok(+name: String, +s: Facts.Facts()) -> {Facts.Facts.ok(name, s) == True{}: Bool} -> {
  Facts.Facts.ok(name, Works.Work.does(s, name)) == True{}: Bool
}:
  ?TODO

# the facts of a node are wider after it works
def Work.does_wider(+name: String, +s: Facts.Facts()) -> {
  Facts.Facts.wider(s, Works.Work.does(s, name)) == True{}: Bool
}:
  ?TODO

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
  ?TODO
