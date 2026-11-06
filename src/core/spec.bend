import Base
import ../endpoints/spec.bend as Ep
import ../glob/spec.bend as Glob
import ../history/spec.bend as History
import ../shared.bend as Shared
import ../store/spec.bend as Store

# The core: one pure step for each input. The loop owns all IO: it waits
# for inputs, calls the step, and carries out the outputs. A front (the
# CLI, later the agent API) only builds inputs and reads outputs, so every
# front shares one behavior.

# Inputs
# ------

# A write through the core: the bytes, and the heads of the resource that
# the writer saw. The core orders these, so its check is exact.
type Request is Data:
  Write{name: Shared.Name, bytes: Shared.Bytes(), expect: List<&2, Shared.Bytes()>}
  Stop{}

# Something for the core to handle. Noticed: a signal from an endpoint
# about one resource. Moved: the endpoint saw the resource from move to to.
# Asked: a front asks for something.
type Input is Data:
  Noticed{name: Shared.Name, signal: Ep.Signal}
  Moved{from: Shared.Name, to: Shared.Name}
  Asked{request: Request}

# Outputs
# -------

# Something for the loop to carry out or to report. Command: send it to the
# endpoint of name. Recorded: a new version of name, with its id. Refused: a
# write whose expected heads are not the heads now, which it names. Failed:
# a version that the store could not keep (a hash collision), so the history
# did not change. Stopped: the loop ends.
type Output is Data:
  Command{name: Shared.Name, command: Ep.Command}
  Recorded{name: Shared.Name, id: Shared.Bytes()}
  Refused{name: Shared.Name, heads: List<&2, Shared.Bytes()>}
  Failed{name: Shared.Name, problem: Store.Problem}
  Stopped{}

# The state
# ---------

# track: the rules that choose the resources the core versions, matched
# against the rest of a file name. store, history: the content and its
# versions. streams: what the core knows of each resource, by the text of
# its name. moves: for a resource that a move just made, the name it came
# from, to put on its next version.
type Core is Data:
  Core{
    track: List<&2, Glob.Rule>,
    store: Store.Store,
    history: History.History,
    streams: Map<&2, Ep.Stream>,
    moves: Map<&2, Maybe<&2, Shared.Name>>
  }

# a core that tracks what rules select, and knows nothing yet
def Core.new(rules: List<&2, Glob.Rule>) -> Core:
  Core{
    rules,
    Store.Store.new(),
    History.History.new(),
    Map.new(&2, Ep.Stream),
    Map.new(&2, Maybe<&2, Shared.Name>)
  }

# the core versions the resource n: its rules select n's path
def Core.tracks(c: Core, n: Shared.Name) -> Bool:
  match c n:
    case Core{tr, s, h, ss, ms} Shared.Name{Shared.FileScheme{}, rest}:
      Glob.Rule.selects(tr, rest)

# the history of c
def Core.history(c: Core) -> History.History:
  match c:
    case Core{tr, s, h, ss, ms}:
      h

# the store of c
def Core.store(c: Core) -> Store.Store:
  match c:
    case Core{tr, s, h, ss, ms}:
      s

# the stream of n in c: a new stream for a resource seen for the first time
def Core.stream.got(r: Map<&2, Ep.Stream> & Ep.Stream) -> Ep.Stream:
  (m, k) = r
  k

# the stream of n in c
def Core.stream(c: Core, n: Shared.Name) -> Ep.Stream:
  match c:
    case Core{tr, s, h, ss, ms}:
      Core.stream.got(Map.get(Ep.Stream, Ep.Stream.new(), ss, Shared.Name.show(n)))

# the pending moved-from name of n in c
def Core.moved.got(
  r: Map<&2, Maybe<&2, Shared.Name>> & Maybe<&2, Shared.Name>
) -> Maybe<&2, Shared.Name>:
  (m, k) = r
  k

# the name n moved from, while its next version is not recorded yet
def Core.moved(c: Core, n: Shared.Name) -> Maybe<&2, Shared.Name>:
  match c:
    case Core{tr, s, h, ss, ms}:
      Core.moved.got(Map.get(Maybe<&2, Shared.Name>, None{}, ms, Shared.Name.show(n)))

# The result of a step: the core after it, and its outputs in order.
type Stepped is Data:
  Stepped{core: Core, outputs: List<&2, Output>}

# the core after input i, and its outputs
law Core.step:
  for c: Core
  for i: Input
  Stepped

# the core after a step
def Stepped.core(s: Stepped) -> Core:
  match s:
    case Stepped{c, os}:
      c

# the outputs of a step
def Stepped.outputs(s: Stepped) -> List<&2, Output>:
  match s:
    case Stepped{c, os}:
      os

# the commands among outputs, with their names dropped
def Output.commands(os: List<&2, Output>) -> List<&2, Ep.Command>:
  match os:
    case Nil{}:
      Nil{}
    case Con{Command{n, k}, t}:
      k <> Output.commands(t)
    case Con{o, t}:
      Output.commands(t)

# o is a Failed output
def Output.is_failed(o: Output) -> Bool:
  match o:
    case Failed{n, p}:
      True{}
    case _:
      False{}

# the ids among outputs
def Output.recorded(os: List<&2, Output>) -> List<&2, Shared.Bytes()>:
  match os:
    case Nil{}:
      Nil{}
    case Con{Recorded{n, x}, t}:
      x <> Output.recorded(t)
    case Con{o, t}:
      Output.recorded(t)

# the bytes as items for the store: one item per byte
def Core.items(b: Shared.Bytes()) -> List<&2, Shared.Bytes()>:
  match b:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      [x] <> Core.items(t)

# Laws
# ----

# a signal about a resource the core does not track changes nothing
law untracked_ignored:
  for c: Core
  for n: Shared.Name
  for s: Ep.Signal
  for h: {Core.tracks(c, n) == False{}: Bool}
  {Core.step(c, Noticed{n, s}) == Stepped{c, []}: Stepped}

# a signal about a tracked resource sends exactly the commands that its
# stream sends
law noticed_follows_stream:
  for c: Core
  for n: Shared.Name
  for s: Ep.Signal
  for h: {Core.tracks(c, n) == True{}: Bool}
  {
    Output.commands(
      Stepped.outputs(Core.step(c, Noticed{n, s}))
    )
      == Ep.Stepped.commands(Ep.Stream.step(Core.stream(c, n), s)): List<&2, Ep.Command>
  }

# each version that the stream records becomes exactly one history node,
# unless the store fails; so the number of Recorded outputs is the number
# of versions, when no output is Failed
law records_each_version:
  for c: Core
  for n: Shared.Name
  for s: Ep.Signal
  for h: {Core.tracks(c, n) == True{}: Bool}
  for f: {
    List.any(
      ~&2,
      ~Output,
      ~Output.is_failed,
      Stepped.outputs(Core.step(c, Noticed{n, s}))
    )
      == False{}: Bool
  }
  {
    List.length(
      &2,
      Shared.Bytes(),
      Output.recorded(Stepped.outputs(Core.step(c, Noticed{n, s})))
    )
      == List.length(&2, Ep.Version, Ep.Stepped.versions(Ep.Stream.step(Core.stream(c, n), s))): Nat
  }

# fetched content that the core records reads back from its node: the
# node's root in the store gives exactly the fetched bytes
law fetched_reads_back:
  for c: Core
  for n: Shared.Name
  for bytes: Shared.Bytes()
  for t: Shared.Bytes()
  for x: Shared.Bytes()
  for parents: List<&2, Shared.Bytes()>
  for r: Store.Ref
  for from: Maybe<&2, Shared.Name>
  for h: {Core.tracks(c, n) == True{}: Bool}
  for o: {
    Output.recorded(
      Stepped.outputs(Core.step(c, Noticed{n, Ep.Fetched{bytes, t}}))
    )
      == [x]: List<&2, Shared.Bytes()>
  }
  for g: {
    History.History.get(
      Core.history(Stepped.core(Core.step(c, Noticed{n, Ep.Fetched{bytes, t}}))),
      x
    )
      == Some{History.Node{n, parents, History.Has{r}, from}}: Maybe<&2, History.Node>
  }
  {
    Store.Tree.read(
      Core.store(Stepped.core(Core.step(c, Noticed{n, Ep.Fetched{bytes, t}}))),
      r
    )
      == Some{Core.items(bytes)}: Maybe<&2, List<&2, Shared.Bytes()>>
  }

# a write whose expected heads are not the heads now changes nothing and is
# refused, naming the heads
law write_refused:
  for c: Core
  for n: Shared.Name
  for b: Shared.Bytes()
  for e: List<&2, Shared.Bytes()>
  for h: {History.Ids.is_eq(e, History.History.heads(Core.history(c), n)) == False{}: Bool}
  {
    Core.step(
      c,
      Asked{Write{n, b, e}}
    )
      == Stepped{c, [Refused{n, History.History.heads(Core.history(c), n)}]}: Stepped
  }

# a write of a tracked resource with the right heads sends one Put of its
# bytes and records one version
law write_accepted:
  for c: Core
  for n: Shared.Name
  for b: Shared.Bytes()
  for e: List<&2, Shared.Bytes()>
  for t: {Core.tracks(c, n) == True{}: Bool}
  for h: {History.Ids.is_eq(e, History.History.heads(Core.history(c), n)) == True{}: Bool}
  for f: {
    List.any(
      ~&2,
      ~Output,
      ~Output.is_failed,
      Stepped.outputs(Core.step(c, Asked{Write{n, b, e}}))
    )
      == False{}: Bool
  }
  {
    List.length(
      &2,
      Ep.Command,
      Output.commands(Stepped.outputs(Core.step(c, Asked{Write{n, b, e}})))
    )
      == 1n: Nat
  }
    &
    {
      List.length(
        &2,
        Shared.Bytes(),
        Output.recorded(Stepped.outputs(Core.step(c, Asked{Write{n, b, e}})))
      )
        == 1n: Nat
    }

# a move records and sends nothing, and remembers where the resource came
# from for its next version
law move_remembered:
  for c: Core
  for f: Shared.Name
  for t: Shared.Name
  {Stepped.outputs(Core.step(c, Moved{f, t})) == []: List<&2, Output>} &
    {Core.moved(Stepped.core(Core.step(c, Moved{f, t})), t) == Some{f}: Maybe<&2, Shared.Name>}

# a step leaves every node of the history in place
law step_keeps_history:
  for c: Core
  for i: Input
  for x: Shared.Bytes()
  for v: History.Node
  for o: {History.History.get(Core.history(c), x) == Some{v}: Maybe<&2, History.Node>}
  {
    History.History.get(
      Core.history(Stepped.core(Core.step(c, i))),
      x
    )
      == Some{v}: Maybe<&2, History.Node>
  }
