import Base
import ../../shared.bend as Shared
import ../shared/ledger.bend as Ledgers
import ../shared/shared/shared/hash.bend as Hashes
import ../shared/tree.bend as Trees
import ./basics.bend as Basics
import ./judging.bend as Judging

# Steps
# -----
# A step runs a batch of requests, in order, from a tip: each request gets its
# outcome in the log, once, and a request that the log holds already is
# skipped. A run is a function of the tip, the requests and the versions that
# they name, so every node that runs a step gets the same tip.

# a run: the state with its new nodes, the tip so far, and the new nodes
type Run is Data:
  Run{state: Basics.Node, tip: Basics.Tip, nodes: List<&2, List<&2, U32>>}

# the state of the run r
def Run.state(r: Run) -> Basics.Node:
  match r:
    case Run{s, t, ns}:
      s

# the tip of the run r
def Run.tip(r: Run) -> Basics.Tip:
  match r:
    case Run{s, t, ns}:
      t

# the run of the content c and the new log m
def Run.of(c: Maybe<&2, Hashes.Hash>, m: Maybe<&2, Judging.Work>) -> Maybe<&2, Run>:
  match m:
    case None{}:
      None{}
    case Some{Judging.Work{s, l, ns}}:
      Some{Run{s, Basics.Tip{c, l}, ns}}

# the run r with the key k of its log set to x (none: the node lacks a node)
def Run.log(r: Run, k: List<&2, U32>, x: List<&2, U32>) -> Maybe<&2, Run>:
  match r:
    case Run{s, Basics.Tip{c, l}, ns}:
      Run.of(c, Judging.Work.set(Judging.Work{s, l, ns}, k, x))

# the run on the state m, at the tip t, with the new nodes ds before ns
def Run.put(
  m: Maybe<&2, Basics.Node>,
  t: Basics.Tip,
  ds: List<&2, List<&2, U32>>,
  ns: List<&2, List<&2, U32>>
) -> Maybe<&2, Run>:
  match m:
    case None{}:
      None{}
    case Some{s2}:
      Some{Run{s2, t, List.append(&2, List<&2, U32>, ds, ns)}}

# Run.add once the value m of the key in the log is known
def Run.add.at(
  r: Run,
  k: List<&2, U32>,
  x: List<&2, U32>,
  m: Maybe<&2, List<&2, U32>>
) -> Maybe<&2, Run>:
  match m:
    case None{}:
      Run.log(r, k, x)
    case Some{old}:
      None{}

# the run r with the new key k of its log set to x (none: the log holds k, or
# the node lacks a node). A log only gains keys: an outcome, a version and a
# mark are written once
def Run.add(+r: Run, +k: List<&2, U32>, x: List<&2, U32>) -> Maybe<&2, Run>:
  Run.add.at(r, k, x, Basics.Node.get(Run.state(r), Basics.Tip.log(Run.tip(r)), k))

# the run r with the content h, and its new nodes ds
def Run.content(r: Run, h: Maybe<&2, Hashes.Hash>, +ds: List<&2, List<&2, U32>>) -> Maybe<&2, Run>:
  match r:
    case Run{s, Basics.Tip{c, l}, ns}:
      Run.put(Judging.State.put(s, ds), Basics.Tip{h, l}, ds, ns)

# the run r with the owners os of the next step, if the change gives any
def Run.owners(r: Run, m: Maybe<&2, List<&2, String>>) -> Maybe<&2, Run>:
  match m:
    case None{}:
      Some{r}
    case Some{os}:
      Run.log(r, Basics.Log.owners(), Ledgers.Owners.code(os, []))

# the run r, after it refused the request i as stale
def Step.stale(r: Run, i: Ledgers.Id) -> Maybe<&2, Run>:
  Run.add(r, Basics.Log.out(i), Basics.Out.words(Basics.Out.Stale{}))

# the run r, after it took the request i as the version of the number n: its
# outcome, its version (the content of r), the count, and the owners that it
# gives
def Step.taken.at(
  r: Run,
  +i: Ledgers.Id,
  +n: U32,
  own: Maybe<&2, List<&2, String>>
) -> Maybe<&2, Run>:
  Maybe.bind(
    &2,
    Run,
    Run,
    Run.add(r, Basics.Log.out(i), Basics.Out.words(Basics.Out.Taken{n})),
    +r1 => Maybe.bind(
      &2,
      Run,
      Run,
      Run.add(
        r1,
        Basics.Log.version(n),
        Basics.Version.words(Basics.Version{i, Basics.Tip.content(Run.tip(r1))})
      ),
      r2 => Maybe.bind(
        &2,
        Run,
        Run,
        Run.log(r2, Basics.Log.count(), [U32.inc(n)]),
        r3 => Run.owners(r3, own)
      )
    )
  )

# the run r, after it took the request i as its next version
def Step.taken(+r: Run, i: Ledgers.Id, own: Maybe<&2, List<&2, String>>) -> Maybe<&2, Run>:
  Step.taken.at(r, i, Basics.Line.count(Run.state(r), Run.tip(r)), own)

# the run r, after the verdict m on the request i (none: wait)
def Step.judged(
  r: Run,
  i: Ledgers.Id,
  own: Maybe<&2, List<&2, String>>,
  m: Maybe<&2, Basics.Verdict>
) -> Maybe<&2, Run>:
  match m:
    case None{}:
      None{}
    case Some{Basics.Verdict{False{}, h, ds}}:
      Step.stale(r, i)
    case Some{Basics.Verdict{True{}, h, ds}}:
      Maybe.bind(&2, Run, Run, Run.content(r, h, ds), r2 => Step.taken(r2, i, own))

# the run r with the mark m on the version v, then the request i taken
def Step.marked(r: Run, i: Ledgers.Id, m: String, v: Maybe<&2, Basics.Version>) -> Maybe<&2, Run>:
  match v:
    case None{}:
      None{}
    case Some{x}:
      Maybe.bind(
        &2,
        Run,
        Run,
        Run.add(r, Basics.Log.mark(m), Ledgers.Id.code(Basics.Version.id(x), [])),
        r2 => Step.taken(r2, i, None{})
      )

# the run r, after a request i for the mark m: it names the newest version,
# for good; a mark that the line has, or a line with no version, refuses it
def Step.mark(+r: Run, +i: Ledgers.Id, +m: String) -> Maybe<&2, Run>:
  +s = Run.state(r)
  +t = Run.tip(r)
  +n = Basics.Line.count(s, t)
  Shared.Bool.when(
    Maybe<&2, Run>,
    List.all.if(
      u => Maybe.is_none(&2, Ledgers.Id, Basics.Line.mark(s, t, m)),
      Bool.not(U32.is_eq(n, 0))
    ),
    u => Step.marked(r, i, m, Basics.Line.version(s, t, U32.sub(n, 1))),
    u => Step.stale(r, i)
  )

# the run r with the first tip m of the new branch b of its store in its log,
# then the request i taken (none: the node lacks a node)
def Branch.made(+r: Run, i: Ledgers.Id, b: String, m: Maybe<&2, Judging.Made>) -> Maybe<&2, Run>:
  match m:
    case None{}:
      None{}
    case Some{Judging.Made{t, ds}}:
      Maybe.bind(
        &2,
        Run,
        Run,
        Run.content(r, Basics.Tip.content(Run.tip(r)), ds),
        +r1 => Maybe.bind(
          &2,
          Run,
          Run,
          Run.add(r1, Basics.Log.start(b), Hashes.Hash.code(Basics.Tip.hash(t), [])),
          r2 => Step.taken(r2, i, None{})
        )
      )

# Step.branch once it is known whether the version that the branch starts at
# is one (m; none: wait for it)
def Branch.ready(
  +r: Run,
  i: Ledgers.Id,
  st: Ledgers.Id,
  +b: String,
  +at: Maybe<&2, Ledgers.Id>,
  m: Maybe<&2, Bool>
) -> Maybe<&2, Run>:
  match m:
    case None{}:
      None{}
    case Some{False{}}:
      Step.stale(r, i)
    case Some{True{}}:
      Shared.Bool.when(
        Maybe<&2, Run>,
        Trees.Tree.whole(
          ~Basics.Node,
          ~Basics.Store.fetch,
          Run.state(r),
          Basics.Node.root_of(Run.state(r), at)
        ),
        u => Branch.made(
          r,
          i,
          b,
          Judging.Make.first(
            Judging.Make.branch(Run.state(r), Basics.Line.chain(st, Some{b}), at),
            Basics.Line.owners(Run.state(r), Run.tip(r))
          )
        ),
        u => None{}
      )

# Step.branch once what the log of the store holds for the branch is known
# (m; none: the node lacks a part of the log)
def Branch.new(
  +r: Run,
  i: Ledgers.Id,
  st: Ledgers.Id,
  b: String,
  +at: Maybe<&2, Ledgers.Id>,
  m: Maybe<&2, Maybe<&2, List<&2, U32>>>
) -> Maybe<&2, Run>:
  match m:
    case None{}:
      None{}
    case Some{Some{x}}:
      Step.stale(r, i)
    case Some{None{}}:
      Branch.ready(r, i, st, b, at, Judging.Judge.ready_maybe(Run.state(r), at))

# the run r of a store, after the request i for a new branch b from the
# version at: the log gets the first tip of b, for good; a store makes a
# branch once, so a branch that it has refuses the request
def Step.branch(
  +r: Run,
  i: Ledgers.Id,
  st: Ledgers.Id,
  +b: String,
  at: Maybe<&2, Ledgers.Id>
) -> Maybe<&2, Run>:
  Branch.new(
    r,
    i,
    st,
    b,
    at,
    Basics.Node.find(Run.state(r), Basics.Tip.log(Run.tip(r)), Basics.Log.start(b))
  )

# the run r, after the request i of the change ch of the line l of the store
# st
def Step.on(
  +r: Run,
  i: Ledgers.Id,
  st: Ledgers.Id,
  l: Maybe<&2, String>,
  ch: Basics.Change
) -> Maybe<&2, Run>:
  match l ch:
    case Some{b} Basics.Change.Mark{m, d}:
      Step.mark(r, i, m)
    case None{} Basics.Change.Branch{b, at}:
      Step.branch(r, i, st, b, at)
    case x +y:
      +s = Run.state(r)
      +t = Run.tip(r)
      Step.judged(
        r,
        i,
        Basics.Change.owners(y),
        Judging.Judge.change(s, st, x, y, Basics.Tip.content(t), Basics.Line.owners(s, t))
      )

# the run r of the line c, after the request i of q: a request of another
# line, or one that starts a store, is stale here
def Step.change(+r: Run, c: Ledgers.Chain, +i: Ledgers.Id, q: Basics.Ask) -> Maybe<&2, Run>:
  match q:
    case Basics.Ask.Start{os}:
      Step.stale(r, i)
    case Basics.Ask.On{+st, +l, ch}:
      Shared.Bool.when(
        Maybe<&2, Run>,
        Ledgers.Chain.is_eq(Basics.Line.chain(st, l), c),
        u => Step.on(r, i, st, l, ch),
        u => Step.stale(r, i)
      )

# the run r of the line c, after the request i, which the node holds as a
# (none: wait for the request)
def Step.asked(
  r: Run,
  c: Ledgers.Chain,
  i: Ledgers.Id,
  a: Maybe<&2, Ledgers.Asked<Basics.Ask>>
) -> Maybe<&2, Run>:
  match a:
    case None{}:
      None{}
    case Some{Ledgers.Asked{t, q}}:
      Step.change(r, c, i, q)

# the run r of the line c, after the request i, whose outcome in the log is o:
# a request that has one is skipped
def Step.fresh(
  +r: Run,
  c: Ledgers.Chain,
  +i: Ledgers.Id,
  o: Maybe<&2, Basics.Out>
) -> Maybe<&2, Run>:
  match o:
    case Some{x}:
      Some{r}
    case None{}:
      Step.asked(r, c, i, Basics.Node.asked(Run.state(r), i))

# the run r of the line c, after the request i
def Step.one(+r: Run, c: Ledgers.Chain, +i: Ledgers.Id) -> Maybe<&2, Run>:
  Step.fresh(r, c, i, Basics.Line.out(Run.state(r), Run.tip(r), i))

# the run m of the line c, after each request of is, in order
def Step.all(+c: Ledgers.Chain, qs: List<&2, Ledgers.Id>, m: Maybe<&2, Run>) -> Maybe<&2, Run>:
  match qs:
    case Nil{}:
      m
    case Con{i, rest}:
      Step.all(c, rest, Maybe.bind(&2, Run, Run, m, r => Step.one(r, c, i)))

# the requests of a step that a node can run now, in order, and the run after
# them
type Picked is Data:
  Picked{run: Run, asks: List<&2, Ledgers.Id>}

# the run of p
def Picked.run(p: Picked) -> Run:
  match p:
    case Picked{r, qs}:
      r

# the requests of p
def Picked.asks(p: Picked) -> List<&2, Ledgers.Id>:
  match p:
    case Picked{r, qs}:
      qs

# p, with the request i before its requests when b holds
def Picked.add(b: Bool, i: Ledgers.Id, p: Picked) -> Picked:
  match p:
    case Picked{r, qs}:
      Picked{r, List.filter.put(Ledgers.Id, i, qs, b)}

# the requests of qs that can run now on the line c, from the run r, and the
# run after them. A request that must wait (for a version, a request or a
# node) is left out: it waits, and does not stop the others
def Step.some(+c: Ledgers.Chain, qs: List<&2, Ledgers.Id>, +r: Run) -> Picked:
  match qs:
    case Nil{}:
      Picked{r, []}
    case Con{+i, rest}:
      +m = Step.one(r, c, i)
      Picked.add(Maybe.is_some(&2, Run, m), i, Step.some(c, rest, Maybe.default(&2, Run, m, r)))

# the step of the line c that runs the requests qs from the tip t (none: wait
# for a request, a version or a node)
def Step.run(
  s: Basics.Node,
  c: Ledgers.Chain,
  t: Basics.Tip,
  qs: List<&2, Ledgers.Id>
) -> Maybe<&2, Run>:
  Step.all(c, qs, Some{Run{s, t, []}})
