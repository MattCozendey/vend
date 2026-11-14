import Base
import ../../shared/shared/ledger.bend as Ledgers
import ../../shared/shared/shared/shared/hash.bend as Hashes
import ../../shared/shared/shared/shared/shared.bend as Shared
import ../node.bend as Nodes
import ./answers.bend as Answers
import ./content.bend as Contents
import ./facts.bend as Facts
import ./known.bend as Known
import ./parts.bend as Parts
import ./work.bend as Works
import ../spec.bend as Spec
import ../types.bend as Types

# The fast node
# -------------
# The state of a node (Nodes.Raw) with the table of the states of the lines
# that it has read, and of the contents of their versions. It does what Nodes.Raw.does does, and answers what a
# Nodes.Raw answers, but reads each line through the table, so it does not
# read a line again from all the facts. This is code that runs: it builds no
# proof. fast.bend proves that the state of a fast node is the state that
# Nodes.Raw.does gives (Fast.does_raw), that its table stays right
# (Fast.does_ok), and that it answers as its state does (Fast.answer_raw, ...).

# a node and the states that it knows; read says that the table holds what
# a work reads of the line of each fact, so a work need not learn them again
type Fast is Data:
  Fast{raw: Nodes.Raw, lines: Known.Known(), read: Bool}

# a fast node of the name name, that holds nothing yet
def Fast.new(name: String) -> Fast:
  Fast{Nodes.Raw.new(name), Known.Known.none(), True{}}

# the state of the fast node f
def Fast.raw(f: Fast) -> Nodes.Raw:
  match f:
    case Fast{r, kn, ld}:
      r

# the states that the fast node f knows
def Fast.lines(f: Fast) -> Known.Known():
  match f:
    case Fast{r, kn, ld}:
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

# the table kn with the states of the lines that a work reads in the facts
# s, unless it holds them (read)
def Learn.if(read: Bool, kn: Known.Known(), +s: Facts.Plain()) -> Known.Known():
  match read:
    case True{}:
      kn
    case False{}:
      Learn.work(kn, s)

# the table kn with the states of the lines that a work reads for the
# request r, in the facts s
def Learn.asked(kn: Known.Known(), +s: Facts.Plain(), +r: Spec.Request) -> Known.Known():
  Learn.request(kn, s, Facts.Facts.list(s), r)

# What a deed leaves of the table
# -------------------------------

# a ballot at the step st changes the state of its line only: the line is a
# branch
def Step.spares(st: Types.Step) -> Bool:
  match st:
    case Types.Step.At{Ledgers.Line{h, Some{b}}, k, t}:
      True{}
    case _:
      False{}

# the table kn after a ballot is cast at the step st, where s is the facts
# with the ballot: without the states that a vote for the line of st may
# change, with the state of that line continued from its known state, with
# the contents that the ballot leaves as they are, with the contents of
# the new versions of the line, and with what a work reads of the line
def Table.voted(+kn: Known.Known(), +s: Facts.Plain(), st: Types.Step) -> Known.Known():
  match st:
    case Types.Step.Broken{}:
      Known.Known.none()
    case Types.Step.At{+c, k, t}:
      Known.Known.learn(Contents.Known.grow(kn, Known.Known.cast(kn, s, c, k), s, c), s, c)

# the table kn after the node takes in the request r: no state if r starts a
# store, else as before (a request that starts no store changes no state)
def Table.asked(kn: Known.Known(), r: Spec.Request) -> Known.Known():
  Shared.Bool.when(Known.Known(), Facts.Request.is_start(r), u => Known.Known.none(), u => kn)

# What a fast node takes in
# -------------------------

# the facts s after the node name takes in the request r of the id i, as
# Facts.Facts.ask gives them: the ask of a request that starts no store
# collides with no ask, so no fact is read for a second start
def Asked.take(+name: String, +s: Facts.Plain(), +i: Ledgers.Id, +r: Spec.Request) -> Facts.Plain():
  Shared.Bool.when(
    Facts.Plain(),
    Facts.Request.is_start(r),
    u => Facts.Facts.ask(name, s, i, r),
    u => Facts.Facts.add(s, Types.Fact.Ask{Facts.Facts.asked(s, i, r)})
  )

# the fast node of the state r, after it took in the request q, with the
# table kn: if the table held what a work reads (read), it learns what a work
# reads for q; a request that starts a store leaves no table
def Fast.asked(+r: Nodes.Raw, kn: Known.Known(), read: Bool, +q: Spec.Request) -> Fast:
  match read:
    case False{}:
      Fast{r, kn, False{}}
    case True{}:
      Fast{r, Learn.asked(kn, Nodes.Raw.facts(r), q), Bool.not(Facts.Request.is_start(q))}

# the state after the node takes in the request r of the id i, when it may
# (go), as Nodes.Raw.asks gives it
def Fast.asks(
  +name: String,
  ws: List<&2, String>,
  ms: List<&2, Nodes.Mounted>,
  st: Bool,
  fs: Facts.Plain(),
  ps: Parts.Parts,
  i: Ledgers.Id,
  +r: Spec.Request,
  go: Bool
) -> Nodes.Raw:
  match go:
    case False{}:
      Nodes.Raw{name, ws, ms, st, fs, ps}
    case True{}:
      Nodes.Raw{
        name,
        ws,
        ms,
        st,
        Asked.take(name, fs, i, r),
        Nodes.Kept.with(ps, Nodes.Request.content(r))
      }

# What a fast node casts
# ----------------------

# the steps a and b are the same, read part by part
def Step.same(a: Types.Step, b: Types.Step) -> Bool:
  match a b:
    case Types.Step.Broken{} Types.Step.Broken{}:
      True{}
    case Types.Step.At{c1, k1, t1} Types.Step.At{c2, k2, t2}:
      List.all.if(
        u => List.all.if(u2 => Ledgers.Line.is_eq(c1, c2), Nat.is_eq(t1, t2)),
        Nat.is_eq(k1, k2)
      )
    case _ _:
      False{}

# the fact f is a vote of the node of g for the step of g, as
# Facts.Fact.is_cast says: the steps are read only for a vote of the node
def Fact.sits(g: Facts.Seat, f: Types.Fact) -> Bool:
  match g f:
    case Facts.Seat{name, st} Types.Fact.Vote{v, st2, pk}:
      List.all.if(u => Step.same(st2, st), String.eq(v, name))
    case Facts.Seat{name, st} Types.Fact.Ask{a}:
      False{}

# s holds a vote of the node name for the step st, as Facts.Facts.cast says
def Seat.cast(s: Facts.Plain(), name: String, st: Types.Step) -> Bool:
  Shared.List.some(~Types.Fact, ~Facts.Seat, ~Fact.sits, Facts.Facts.list(s), Facts.Seat{name, st})

# the fast node with the facts s after its ballot at the step st, and the
# table that the ballot leaves of kn
def Fast.casts.to(
  name: String,
  ws: List<&2, String>,
  ms: List<&2, Nodes.Mounted>,
  +s: Facts.Plain(),
  ps: Parts.Parts,
  +kn: Known.Known(),
  st: Types.Step
) -> Fast:
  +st = st
  Fast{Nodes.Raw{name, ws, ms, False{}, s, ps}, Table.voted(kn, s, st), Step.spares(st)}

# the fast node after a work that plans the ballot x at the step st: with the
# ballot, unless its facts hold a ballot of the node at the step (done)
def Fast.casts.if(
  done: Bool,
  +name: String,
  ws: List<&2, String>,
  ms: List<&2, Nodes.Mounted>,
  +fs: Facts.Plain(),
  ps: Parts.Parts,
  +kn: Known.Known(),
  +st: Types.Step,
  x: Types.Cast
) -> Fast:
  match done:
    case True{}:
      Fast{Nodes.Raw{name, ws, ms, False{}, fs, ps}, kn, True{}}
    case False{}:
      Fast.casts.to(name, ws, ms, Facts.Facts.add(fs, Types.Fact.Vote{name, st, x}), ps, kn, st)

# What a fast node does
# ---------------------

# the fast node after a work, with the plan m of its ballot, read through the
# table kn of the states that the work reads: its facts are those that
# Works.Work.cast gives
def Fast.works.at(
  +name: String,
  ws: List<&2, String>,
  ms: List<&2, Nodes.Mounted>,
  +fs: Facts.Plain(),
  ps: Parts.Parts,
  +kn: Known.Known(),
  m: Maybe<&2, Works.Plan>
) -> Fast:
  match m:
    case None{}:
      Fast{Nodes.Raw{name, ws, ms, False{}, fs, ps}, kn, True{}}
    case Some{Works.Plan{+st, x}}:
      Fast.casts.if(Seat.cast(fs, name, st), name, ws, ms, fs, ps, kn, st, x)

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

# the fast node after a work, unless it has stopped: the work learns the
# lines that it reads, unless the table holds them (read)
def Fast.works(
  +name: String,
  ws: List<&2, String>,
  ms: List<&2, Nodes.Mounted>,
  st: Bool,
  +fs: Facts.Plain(),
  ps: Parts.Parts,
  kn: Known.Known(),
  read: Bool
) -> Fast:
  match st:
    case True{}:
      Fast{Nodes.Raw{name, ws, ms, True{}, fs, ps}, kn, read}
    case False{}:
      Fast.works.on(name, ws, ms, fs, ps, Learn.if(read, kn, fs))

# the fast node f after the deed a: its state is the state that
# Nodes.Raw.does gives, read through the table; the table keeps the states
# that the deed cannot change
def Fast.does(f: Fast, a: Nodes.Act) -> Fast:
  match f a:
    case Fast{r, kn, ld} Nodes.Act.Connect{w}:
      Fast{Nodes.Raw.does(r, Nodes.Act.Connect{w}), kn, ld}
    case Fast{r, kn, ld} Nodes.Act.Leave{w}:
      Fast{Nodes.Raw.does(r, Nodes.Act.Leave{w}), kn, ld}
    case Fast{Nodes.Raw{name, +ws, ms, +st, fs, ps}, kn, ld} Nodes.Act.Ask{+i, +q}:
      Fast.asked(
        Fast.asks(
          name,
          ws,
          ms,
          st,
          fs,
          ps,
          i,
          q,
          Bool.and(Bool.not(st), List.contains(~String, ~String.eq, ws, Spec.Id.writer(i)))
        ),
        Table.asked(kn, q),
        ld,
        q
      )
    case Fast{r, kn, ld} Nodes.Act.Sync{from}:
      Fast{Nodes.Raw.does(r, Nodes.Act.Sync{from}), Known.Known.none(), False{}}
    case Fast{Nodes.Raw{+name, ws, ms, +st, fs, ps}, kn, ld} Nodes.Act.Mount{+a, +b, +p, held}:
      Fast.asked(
        Fast.asks(
          name,
          ws,
          Nodes.Mounted{a, b, p} <> Nodes.Mounts.remove(ms, a),
          st,
          fs,
          ps,
          Nodes.Mount.id(name, a),
          Spec.Request.Write{b, p, Some{held}},
          Bool.not(st)
        ),
        kn,
        ld,
        Spec.Request.Write{b, p, None{}}
      )
    case Fast{r, kn, ld} Nodes.Act.Unmount{a}:
      Fast{Nodes.Raw.does(r, Nodes.Act.Unmount{a}), kn, ld}
    case Fast{Nodes.Raw{name, ws, ms, st, fs, ps}, kn, ld} Nodes.Act.Work{}:
      Fast.works(name, ws, ms, st, fs, ps, kn, ld)
    case Fast{Nodes.Raw{+name, ws, +ms, st, +fs, ps}, +kn, ld} Nodes.Act.Drop{}:
      Fast{
        Nodes.Raw{name, ws, ms, st, fs, Parts.Parts.only(ps, Nodes.Needs.of(kn, fs, name, ms))},
        kn,
        ld
      }
    case Fast{r, kn, ld} Nodes.Act.Stop{force}:
      Fast{Nodes.Raw.does(r, Nodes.Act.Stop{force}), kn, ld}

# the fast node f with the states of the line c and of its store, and the
# content of each version of c, in its table: a read of c does not read it
# again from all the facts
def Fast.learn(f: Fast, +c: Ledgers.Line) -> Fast:
  match f:
    case Fast{+r, kn, ld}:
      Fast{
        r,
        Contents.Known.warm(Known.Known.learn(kn, Nodes.Raw.facts(r), c), Nodes.Raw.facts(r), c),
        ld
      }

# What a fast node shows
# ----------------------

# the fast node f holds the change c
def Fast.holds(f: Fast, c: Types.Change) -> Bool:
  Nodes.Raw.holds(Fast.raw(f), c)

# the words of the resource at the path p in version k of the line c, as the
# fast node f reads them
def Fast.read(f: Fast, c: Ledgers.Line, k: Nat, p: String) -> Maybe<&2, Maybe<&2, List<&2, U32>>>:
  match f:
    case Fast{r, kn, ld}:
      Contents.Content.read(kn, Nodes.Raw.facts(r), c, k, p)

# the words of the resource at the path p of the branch b, as the fast node
# f shows them to the writer w
def Fast.view(
  f: Fast,
  w: String,
  b: Ledgers.Line,
  p: String
) -> Maybe<&2, Maybe<&2, List<&2, U32>>>:
  match f:
    case Fast{r, kn, ld}:
      Answers.View.at(kn, Nodes.Raw.facts(r), w, b, p)

# the reply of the fast node f to the question q
def Fast.answer(f: Fast, q: Spec.Question) -> Maybe<&2, Spec.Reply>:
  match f:
    case Fast{r, kn, ld}:
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

# the table of the fast node f is right: each state and each content that it
# holds is what the facts of f give
def Fast.ok(f: Fast) -> Bool:
  match f:
    case Fast{r, kn, ld}:
      Contents.Known.ok(kn, Nodes.Raw.facts(r))
