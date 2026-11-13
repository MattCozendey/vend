import Base
import ../shared/shared/ledger.bend as Ledgers
import ../shared/shared/shared/shared/hash.bend as Hashes
import ../shared/shared/shared/shared/shared.bend as Shared
import ./codes.bend as Coded
import ./content.bend as Contents
import ./facts.bend as Facts
import ./groups.bend as Groups
import ./lines.bend as Lines
import ./run/answers.bend as RAnswers
import ./run/content.bend as RContents
import ./run/facts.bend as RFacts
import ./run/files.bend as Files
import ./run/lines.bend as RLines
import ./shared/format.bend as Formats
import ./shared/lists.bend as Lists
import ./spec.bend as Spec
import ./types.bend as Types

# Answers
# -------
# What a node replies to a question: a read of the versions that its facts
# decide. A reply is nothing (Unknown) while the facts do not decide it.
#
# The code that runs is in run/answers.bend: it reads the plain map of the facts
# and builds no proof. Here each def that reads the facts is that code on the
# map of a set of facts (Facts.crit), so the laws said of the set are laws of
# the code that runs.

# Merges
# ------

# the paths that clash in the merge e, version k of the line c
def Clashes.of(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  k: Nat,
  +e: Types.Entry
) -> Maybe<&2, List<&2, String>>:
  RAnswers.Clashes.of(Facts.Facts.crit(s), c, k, e)

# the base of the merge e, version k of the line c, when its ways lead to it
def Base.of(+s: Facts.Facts(), +c: Ledgers.Line, k: Nat, +e: Types.Entry) -> Maybe<&2, Spec.Point>:
  RAnswers.Base.of(Facts.Facts.crit(s), c, k, e)

# the status of the request r, version k of the line c
def Status.of(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +vs: List<&2, Types.Entry>,
  +k: Nat,
  +e: Types.Entry
) -> Spec.Status:
  RAnswers.Status.of(Facts.Facts.crit(s), c, vs, k, e)

# The rule of a version
# ---------------------

# the versions of the line c before its version 1+j, when the line has that
# many, or one less (the version that comes next)
def Line.before(+s: Facts.Facts(), +c: Ledgers.Line, +j: Nat) -> Maybe<&2, List<&2, Types.Entry>>:
  RAnswers.Line.before(Facts.Facts.crit(s), c, j)

# Rule.for, once the versions m before the version are known
def Rule.for.of(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  m: Maybe<&2, List<&2, Types.Entry>>
) -> Maybe<&2, RLines.Rule>:
  RAnswers.Rule.for.of(Facts.Facts.crit(s), c, m)

# the rule of version k of the line c: of the versions before it
def Rule.for(+s: Facts.Facts(), +c: Ledgers.Line, k: Nat) -> Maybe<&2, RLines.Rule>:
  RAnswers.Rule.for(Facts.Facts.crit(s), c, k)

# the era of version k of the line c
def Era.for(+s: Facts.Facts(), +c: Ledgers.Line, k: Nat) -> Maybe<&2, Nat>:
  RAnswers.Era.for(Facts.Facts.crit(s), c, k)

# the first nodes of the rule u that are more than half of it, when the facts
# hold the vote of each of them for the entry e of the line c
def Rule.voters(
  +s: Facts.Facts(),
  c: Ledgers.Line,
  e: Types.Entry,
  u: RLines.Rule
) -> Maybe<&2, Spec.Reply>:
  RAnswers.Rule.voters(Facts.Facts.crit(s), c, e, u)

# the nodes whose votes decided version k of the line c, once its entry m and
# its rule u are known
def Owners.of(
  +s: Facts.Facts(),
  c: Ledgers.Line,
  m: Maybe<&2, Types.Entry>,
  u: Maybe<&2, RLines.Rule>
) -> Maybe<&2, Spec.Reply>:
  RAnswers.Owners.of(Facts.Facts.crit(s), c, m, u)

# Groups
# ------

# a read of the groups of the store h at its version m, when the node holds
# that version
def Store.read(
  -A: Data,
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +m: Nat,
  f: List<&2, Types.Entry> -> Maybe<&2, A>
) -> Maybe<&2, A>:
  RAnswers.Store.read(A, Facts.Facts.crit(s), h, m, f)

# The answer
# ----------

# the entry of the id i in the line c, and its version
def Line.find(+s: Facts.Facts(), +c: Ledgers.Line, i: Ledgers.Id) -> Maybe<&2, RAnswers.Found>:
  RAnswers.Line.find(Facts.Facts.crit(s), c, i)

# the reply of the status of the found entry m of the line c, with the
# versions v of the line
def Reply.status(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  v: Maybe<&2, List<&2, Types.Entry>>,
  m: Maybe<&2, RAnswers.Found>
) -> Maybe<&2, Spec.Reply>:
  RAnswers.Reply.status(Facts.Facts.crit(s), c, v, m)

# the reply of the facts s to the question q
def Answer.of(+s: Facts.Facts(), q: Spec.Question) -> Maybe<&2, Spec.Reply>:
  RAnswers.Answer.of(Facts.Facts.crit(s), q)

# Views
# -----

# the words at the path p of the newest of the versions m of the branch b
def View.newest(
  +s: Facts.Facts(),
  +b: Ledgers.Line,
  +p: String,
  m: Maybe<&2, List<&2, Types.Entry>>
) -> Maybe<&2, Maybe<&2, List<&2, U32>>>:
  RAnswers.View.newest(Facts.Facts.crit(s), b, p, m)

# the view of a writer whose last write there is the ask m, if any: its words
# while no version was made by it; else what the newest version holds
def View.of(
  +s: Facts.Facts(),
  +b: Ledgers.Line,
  +p: String,
  m: Maybe<&2, Types.Ask>
) -> Maybe<&2, Maybe<&2, List<&2, U32>>>:
  RAnswers.View.of(Facts.Facts.crit(s), b, p, m)

# the words that the writer w reads at the path p of the newest version of
# the branch b, its own writes included
def View.at(
  +s: Facts.Facts(),
  +w: String,
  +b: Ledgers.Line,
  +p: String
) -> Maybe<&2, Maybe<&2, List<&2, U32>>>:
  RAnswers.View.at(Facts.Facts.crit(s), w, b, p)
