import Base
import ../../shared/shared/ledger.bend as Ledgers
import ../../shared/shared/shared/shared/hash.bend as Hashes
import ../../shared/shared/shared/shared/shared.bend as Shared
import ../node.bend as Nodes
import ./answers.bend as Answers
import ./content.bend as Contents
import ./facts.bend as Facts
import ./known.bend as Known
import ./lines.bend as Lines
import ./parts.bend as Parts
import ./work.bend as Works
import ../spec.bend as Spec
import ../types.bend as Types

# The fast node
# -------------
# The state of a node (Nodes.Raw) with the table of the states of the lines
# that it has read. It does what Nodes.Raw.does does, and answers what a
# Nodes.Raw answers, but reads each line through the table, so it does not
# read a line again from all the facts. This is code that runs: it builds no
# proof. fast.bend proves that the state of a fast node is the state that
# Nodes.Raw.does gives (Fast.does_raw), that its table stays right
# (Fast.does_ok), and that it answers as its state does (Fast.answer_raw, ...).

# a node and the states that it knows
type Fast is Data:
  Fast{raw: Nodes.Raw, lines: Known.Known()}

# a fast node of the name name, that holds nothing yet
def Fast.new(name: String) -> Fast:
  Fast{Nodes.Raw.new(name), Known.Known.none()}

# the state of the fast node f
def Fast.raw(f: Fast) -> Nodes.Raw:
  match f:
    case Fast{r, kn}:
      r

# the states that the fast node f knows
def Fast.lines(f: Fast) -> Known.Known():
  match f:
    case Fast{r, kn}:
      kn

# What a work reads
# -----------------

# the table kn with the states of the line m, if any, and of its store
def Learn.line(kn: Known.Known(), +s: Facts.Plain(), m: Maybe<&2, Ledgers.Line>) -> Known.Known():
  match m:
    case None{}:
      kn
    case Some{+c}:
      Known.Known.learn(kn, s, c)

# the table kn with the states of the line that the request r takes from, if
# it is a merge
def Learn.merge(kn: Known.Known(), +s: Facts.Plain(), r: Spec.Request) -> Known.Known():
  match r:
    case Spec.Request.Merge{+f, x}:
      Known.Known.learn(kn, s, f)
    case _:
      kn

# the table kn with the states of the lines that a work reads for the
# request r, where all is the facts of s
def Learn.request(
  kn: Known.Known(),
  +s: Facts.Plain(),
  all: List<&2, Types.Fact>,
  +r: Spec.Request
) -> Known.Known():
  Learn.merge(Learn.line(kn, s, Works.Request.line(all, r)), s, r)

# the table kn with the states of the lines that a work reads for the facts
# fs: the line of each ballot, and the lines of each request; all is the
# facts of s
def Learn.facts(
  fs: List<&2, Types.Fact>,
  kn: Known.Known(),
  +s: Facts.Plain(),
  +all: List<&2, Types.Fact>
) -> Known.Known():
  match fs:
    case Nil{}:
      kn
    case Con{Types.Fact.Vote{v, Types.Step.Broken{}, x}, rest}:
      Learn.facts(rest, kn, s, all)
    case Con{Types.Fact.Vote{v, Types.Step.At{+c, k, t}, x}, rest}:
      Learn.facts(rest, Known.Known.learn(kn, s, c), s, all)
    case Con{Types.Fact.Ask{Types.Ask{i, n, +r}}, rest}:
      Learn.facts(rest, Learn.request(kn, s, all, r), s, all)

# the table kn with the states of the lines that a work reads in the facts s
def Learn.work(kn: Known.Known(), +s: Facts.Plain()) -> Known.Known():
  +all = Facts.Facts.list(s)
  Learn.facts(all, kn, s, all)

# What a deed leaves of the table
# -------------------------------

# the table kn after a ballot is cast at the step st, where s is the facts
# with the ballot: without the states that a vote for the line of st may
# change, and with the state of that line continued from its known state
def Table.voted(kn: Known.Known(), +s: Facts.Plain(), st: Types.Step) -> Known.Known():
  match st:
    case Types.Step.Broken{}:
      Known.Known.none()
    case Types.Step.At{+c, k, t}:
      Known.Known.cast(kn, s, c, k)

# the table kn after a work of the node name on the facts s casts the ballot
# m, if any (as Works.Work.cast does: not when s holds a ballot of the node
# with the same number)
def Table.cast(
  +kn: Known.Known(),
  +s: Facts.Plain(),
  +name: String,
  m: Maybe<&2, Works.Plan>
) -> Known.Known():
  match m:
    case None{}:
      kn
    case Some{Works.Plan{+st, x}}:
      Shared.Bool.when(
        Known.Known(),
        Facts.Facts.cast(s, name, st),
        u => kn,
        u => Table.voted(kn, Facts.Facts.add(s, Types.Fact.Vote{name, st, x}), st)
      )

# the table kn after the node takes in the request r: no state if r starts a
# store, else as before (a request that starts no store changes no state)
def Table.asked(kn: Known.Known(), r: Spec.Request) -> Known.Known():
  Shared.Bool.when(
    Known.Known(),
    Facts.Request.is_start(r),
    u => Known.Known.none(),
    u => kn
  )

# What a fast node does
# ---------------------

# the fast node after a work, with the plan m of its ballot, read through the
# table kn of the states that the work reads
def Fast.works.at(
  +name: String,
  ws: List<&2, String>,
  ms: List<&2, Nodes.Mounted>,
  +fs: Facts.Plain(),
  ps: Parts.Parts,
  +kn: Known.Known(),
  +m: Maybe<&2, Works.Plan>
) -> Fast:
  Fast{
    Nodes.Raw{name, ws, ms, False{}, Works.Work.cast(fs, name, m), ps},
    Table.cast(kn, fs, name, m)
  }

# the fast node after a work, read through the table kn of the states that
# the work reads
def Fast.works.on(
  +name: String,
  ws: List<&2, String>,
  ms: List<&2, Nodes.Mounted>,
  +fs: Facts.Plain(),
  ps: Parts.Parts,
  +kn: Known.Known()
) -> Fast:
  Fast.works.at(name, ws, ms, fs, ps, kn, Works.Work.plan(kn, fs, name))

# the fast node after a work, unless it has stopped
def Fast.works(
  +name: String,
  ws: List<&2, String>,
  ms: List<&2, Nodes.Mounted>,
  st: Bool,
  +fs: Facts.Plain(),
  ps: Parts.Parts,
  kn: Known.Known()
) -> Fast:
  match st:
    case True{}:
      Fast{Nodes.Raw{name, ws, ms, True{}, fs, ps}, kn}
    case False{}:
      Fast.works.on(name, ws, ms, fs, ps, Learn.work(kn, fs))

# the fast node f after the deed a: its state is the state that
# Nodes.Raw.does gives, read through the table; the table keeps the states
# that the deed cannot change
def Fast.does(f: Fast, a: Nodes.Act) -> Fast:
  match f a:
    case Fast{r, kn} Nodes.Act.Connect{w}:
      Fast{Nodes.Raw.does(r, Nodes.Act.Connect{w}), kn}
    case Fast{r, kn} Nodes.Act.Leave{w}:
      Fast{Nodes.Raw.does(r, Nodes.Act.Leave{w}), kn}
    case Fast{r, kn} Nodes.Act.Ask{i, +q}:
      Fast{Nodes.Raw.does(r, Nodes.Act.Ask{i, q}), Table.asked(kn, q)}
    case Fast{r, kn} Nodes.Act.Sync{from}:
      Fast{Nodes.Raw.does(r, Nodes.Act.Sync{from}), Known.Known.none()}
    case Fast{r, kn} Nodes.Act.Mount{a, b, p, held}:
      Fast{Nodes.Raw.does(r, Nodes.Act.Mount{a, b, p, held}), kn}
    case Fast{r, kn} Nodes.Act.Unmount{a}:
      Fast{Nodes.Raw.does(r, Nodes.Act.Unmount{a}), kn}
    case Fast{Nodes.Raw{name, ws, ms, st, fs, ps}, kn} Nodes.Act.Work{}:
      Fast.works(name, ws, ms, st, fs, ps, kn)
    case Fast{Nodes.Raw{+name, ws, +ms, st, +fs, ps}, +kn} Nodes.Act.Drop{}:
      Fast{
        Nodes.Raw{name, ws, ms, st, fs, Parts.Parts.only(ps, Nodes.Needs.of(kn, fs, name, ms))},
        kn
      }
    case Fast{r, kn} Nodes.Act.Stop{force}:
      Fast{Nodes.Raw.does(r, Nodes.Act.Stop{force}), kn}

# the fast node f with the states of the line c and of its store in its
# table: a read of c does not read it again from all the facts
def Fast.learn(f: Fast, +c: Ledgers.Line) -> Fast:
  match f:
    case Fast{+r, kn}:
      Fast{r, Known.Known.learn(kn, Nodes.Raw.facts(r), c)}

# What a fast node shows
# ----------------------

# the fast node f holds the change c
def Fast.holds(f: Fast, c: Types.Change) -> Bool:
  Nodes.Raw.holds(Fast.raw(f), c)

# the words of the resource at the path p in version k of the line c, as the
# fast node f reads them
def Fast.read(f: Fast, c: Ledgers.Line, k: Nat, p: String) -> Maybe<&2, Maybe<&2, List<&2, U32>>>:
  match f:
    case Fast{r, kn}:
      Contents.Content.read(kn, Nodes.Raw.facts(r), c, k, p)

# the words of the resource at the path p of the branch b, as the fast node
# f shows them to the writer w
def Fast.view(f: Fast, w: String, b: Ledgers.Line, p: String) -> Maybe<&2, Maybe<&2, List<&2, U32>>>:
  match f:
    case Fast{r, kn}:
      Answers.View.at(kn, Nodes.Raw.facts(r), w, b, p)

# the reply of the fast node f to the question q
def Fast.answer(f: Fast, q: Spec.Question) -> Maybe<&2, Spec.Reply>:
  match f:
    case Fast{r, kn}:
      Answers.Answer.of(kn, Nodes.Raw.facts(r), q)

# the voters that the fast node f proves to be liars
def Fast.liars(f: Fast) -> List<&2, String>:
  Nodes.Raw.liars(Fast.raw(f))

# the hashes of the parts that the fast node f holds, each once
def Fast.parts(f: Fast) -> List<&2, Hashes.Hash>:
  Nodes.Raw.parts(Fast.raw(f))

# the words of the hash h, if the fast node f holds them
def Fast.part(f: Fast, h: Hashes.Hash) -> Maybe<&2, List<&2, U32>>:
  Nodes.Raw.part(Fast.raw(f), h)

# the table of the fast node f is right: each state that it holds is the
# state that the facts of f give the line
def Fast.ok(f: Fast) -> Bool:
  match f:
    case Fast{r, kn}:
      Known.Known.ok(kn, Nodes.Raw.facts(r))
