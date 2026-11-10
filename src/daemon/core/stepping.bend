import Base
import ../../shared.bend as Shared
import ../shared/ledger.bend as Ledgers
import ../shared/shared/shared/hash.bend as Hashes
import ../shared/tree.bend as Trees
import ./basics.bend as Basics
import ./judging.bend as Judging
import ../replica/impl.bend as Replicas

# Steps
# -----
# A step runs a batch of requests, in order, from a tip: each request gets its
# outcome in the log, once, and a request that the log holds already is
# skipped. A run is a function of the tip, the requests and the versions that
# they name, so every node that runs a step gets the same tip.

# Step.branch once it is known whether the version that the branch starts at
# is one (m; none: wait for it)
def Branch.ready(
  +r: Replicas.Run<Basics.Ask>,
  i: Ledgers.Id,
  st: Ledgers.Id,
  +b: String,
  +at: Maybe<&2, Ledgers.Id>,
  m: Maybe<&2, Bool>
) -> Maybe<&2, Replicas.Run<Basics.Ask>>:
  match m:
    case None{}:
      None{}
    case Some{False{}}:
      Replicas.Step.stale(~Basics.Ask.machine(), r, i)
    case Some{True{}}:
      Shared.Bool.when(
        Maybe<&2, Replicas.Run<Basics.Ask>>,
        Trees.Tree.whole(
          ~Replicas.Node<Basics.Ask>,
          ~Replicas.Store.fetch(~Basics.Ask.machine()),
          Replicas.Run.state(~Basics.Ask.machine(), r),
          Basics.Node.root_of(Replicas.Run.state(~Basics.Ask.machine(), r), at)
        ),
        u => Replicas.Branch.made(~Basics.Ask.machine(), 
          r,
          i,
          b,
          Judging.Make.first(
            Judging.Make.branch(Replicas.Run.state(~Basics.Ask.machine(), r), Replicas.Line.chain(st, Some{b}), at),
            Replicas.Tip.owners(Replicas.Run.tip(~Basics.Ask.machine(), r))
          )
        ),
        u => None{}
      )

# Step.branch once what the log of the store holds for the branch is known
# (m; none: the node lacks a part of the log)
def Branch.new(
  +r: Replicas.Run<Basics.Ask>,
  i: Ledgers.Id,
  st: Ledgers.Id,
  b: String,
  +at: Maybe<&2, Ledgers.Id>,
  m: Maybe<&2, Maybe<&2, List<&2, U32>>>
) -> Maybe<&2, Replicas.Run<Basics.Ask>>:
  match m:
    case None{}:
      None{}
    case Some{Some{x}}:
      Replicas.Step.stale(~Basics.Ask.machine(), r, i)
    case Some{None{}}:
      Branch.ready(r, i, st, b, at, Judging.Judge.ready_maybe(Replicas.Run.state(~Basics.Ask.machine(), r), at))

# the run r of a store, after the request i for a new branch b from the
# version at: the log gets the first tip of b, for good; a store makes a
# branch once, so a branch that it has refuses the request
def Step.branch(
  +r: Replicas.Run<Basics.Ask>,
  i: Ledgers.Id,
  st: Ledgers.Id,
  +b: String,
  at: Maybe<&2, Ledgers.Id>
) -> Maybe<&2, Replicas.Run<Basics.Ask>>:
  Branch.new(
    r,
    i,
    st,
    b,
    at,
    Replicas.Node.find(~Basics.Ask.machine(), Replicas.Run.state(~Basics.Ask.machine(), r), Replicas.Tip.log(Replicas.Run.tip(~Basics.Ask.machine(), r)), Replicas.Log.start(b))
  )

# bend-lint: expect-begin bend-lint-rules/layout/case@warning -- a constructor is PascalCase, as in Base (Some, Con): the rule reads a constructor as a law
# how a line takes a change: a branch writes a mark to its log, a store
# writes a new branch to its log, and a judge decides any other change
type Route is Data:
  Route.Mark{mark: String}
  Route.Branch{name: String, at: Maybe<&2, Ledgers.Id>}
  Route.Judge{}
# bend-lint: expect-end bend-lint-rules/layout/case@warning

# how the line l takes the change ch
def Route.of(l: Maybe<&2, String>, ch: Basics.Change) -> Route:
  match l ch:
    case Some{b} Basics.Change.Mark{m, d}:
      Route.Mark{m}
    case None{} Basics.Change.Branch{b, at}:
      Route.Branch{b, at}
    case x y:
      Route.Judge{}

# Step.on once it is known how the line takes the change (w)
def Step.on.of(
  +r: Replicas.Run<Basics.Ask>,
  i: Ledgers.Id,
  st: Ledgers.Id,
  l: Maybe<&2, String>,
  +ch: Basics.Change,
  w: Route
) -> Maybe<&2, Replicas.Run<Basics.Ask>>:
  match w:
    case Route.Mark{m}:
      Replicas.Step.mark(~Basics.Ask.machine(), r, i, m)
    case Route.Branch{b, at}:
      Step.branch(r, i, st, b, at)
    case Route.Judge{}:
      +s = Replicas.Run.state(~Basics.Ask.machine(), r)
      +t = Replicas.Run.tip(~Basics.Ask.machine(), r)
      Replicas.Step.judged(~Basics.Ask.machine(), 
        r,
        i,
        Basics.Change.owners(ch),
        Judging.Judge.change(s, st, l, ch, Replicas.Tip.content(t), Replicas.Tip.owners(t))
      )

# the run r, after the request i of the change ch of the line l of the store
# st
def Step.on(
  r: Replicas.Run<Basics.Ask>,
  i: Ledgers.Id,
  st: Ledgers.Id,
  +l: Maybe<&2, String>,
  +ch: Basics.Change
) -> Maybe<&2, Replicas.Run<Basics.Ask>>:
  Step.on.of(r, i, st, l, ch, Route.of(l, ch))

# the run r of the line c, after the request i of q: a request of another
# line, or one that starts a store, is stale here
def Step.change(+r: Replicas.Run<Basics.Ask>, c: Ledgers.Chain, +i: Ledgers.Id, q: Basics.Ask) -> Maybe<&2, Replicas.Run<Basics.Ask>>:
  match q:
    case Basics.Ask.Start{os}:
      Replicas.Step.stale(~Basics.Ask.machine(), r, i)
    case Basics.Ask.On{+st, +l, ch}:
      Shared.Bool.when(
        Maybe<&2, Replicas.Run<Basics.Ask>>,
        Ledgers.Chain.is_eq(Replicas.Line.chain(st, l), c),
        u => Step.on(r, i, st, l, ch),
        u => Replicas.Step.stale(~Basics.Ask.machine(), r, i)
      )

# the kernel of Vend
def Ask.kernel() -> Replicas.Kernel():
  (
    Basics.Ask.machine(),
    (
      Basics.Ask.arrival,
      (Basics.Ask.governs, (Basics.Key.seal, +r => c => +i => q => Step.change(r, c, i, q)))
    )
  )
