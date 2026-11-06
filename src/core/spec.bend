import Base
import ../endpoints/spec.bend as Ep
import ../glob/spec.bend as Glob
import ../hash/spec.bend as Hash
import ../history/spec.bend as History
import ../journal/spec.bend as Journal
import ../lines/spec.bend as Lines
import ../shared.bend as Shared
import ../store/spec.bend as Store

# The core: one pure step for each input. The loop owns all IO: it waits
# for inputs, calls the step, and carries out the outputs. A front (the
# CLI, later the agent API) only builds inputs and reads outputs, so every
# front shares one behavior.

# Mounts
# ------

# A mount binds a line of a space to a URI prefix on one machine. Its
# globs choose the files it versions, matched against the path relative to
# the root. The space id lives in the file ".bend-ver" at the root, which
# is never versioned. A directory below the root that holds its own
# ".bend-ver" starts another space (like a git submodule): nothing under
# it belongs to this mount.
type Mount is Data:
  Mount{space: String, line: String, root: Shared.Uri, globs: List<&2, Glob.Rule>}

# the file at the root of a space that holds its id
def Mount.space_file() -> String:
  ".bend-ver"

# Inputs
# ------

# A request from a front. Write: write bytes to the file at path, by the
# agent named agent, which saw the heads expect on the line of the mount;
# the version records the agent as its author. The core orders these, so
# its check is exact. Stop: end the loop.
type Request is Data:
  Write{path: String, bytes: Shared.Bytes(), expect: List<&2, Shared.Bytes()>, agent: String}
  Stop{}

# Something for the core to handle; an endpoint speaks in paths relative
# to the root. Noticed: a signal about the file at path. Moved: the file
# moved from one path to another. Nested: the directory dir holds its own
# ".bend-ver", so it starts another space. Asked: a front asks for
# something.
type Input is Data:
  Noticed{path: String, signal: Ep.Signal}
  Moved{from: String, to: String}
  Nested{dir: String}
  Asked{request: Request}

# Outputs
# -------

# Why a version was not kept. Store: the store met a hash collision.
# History: the history refused the node (a missing parent, or a collision).
# Line: the line did not move.
type Problem is Data:
  StoreProblem{problem: Store.Problem}
  HistoryProblem{refusal: History.Refusal}
  LineProblem{refused: Lines.Refused}

# Something for the loop to carry out or to report. Logged: a record for
# the journal; the loop appends the records of a step and syncs the journal
# before it carries out or reports any other output of that step, so no
# version is reported, and no endpoint is written, before it is on disk.
# Command: send it to the endpoint for the file at path. Recorded: a new
# version of name, with its id and author, now the head of name on the
# line. Refused: a write whose expected heads are not the heads on the
# line, which it names. Failed: a version that could not be kept, so the
# store, the history and the line did not change. Stopped: the loop ends.
type Output is Data:
  Logged{record: Journal.Record}
  Command{path: String, command: Ep.Command}
  Recorded{name: Shared.Name, id: Shared.Bytes(), author: History.Author}
  Refused{name: Shared.Name, heads: List<&2, Shared.Bytes()>}
  Failed{name: Shared.Name, problem: Problem}
  Stopped{}

# The state
# ---------

# mount: what the core serves. store, history: the content and its
# versions. line: the line of the mount. streams: what the core knows of
# each file, by its path. moves: for a file that a move just made, the name
# it came from, to put on its next version. nested: the directories that
# start other spaces.
type Core is Data:
  Core{
    mount: Mount,
    store: Store.Store,
    history: History.History,
    line: Lines.Line,
    streams: Shared.Table<Ep.Stream>,
    moves: Shared.Table<Maybe<&2, Shared.Name>>,
    nested: List<&2, String>
  }

# a core that serves the mount m and knows nothing yet
def Core.new(m: Mount) -> Core:
  match m:
    case Mount{+sp, +ln, r, g}:
      Core{
        Mount{sp, ln, r, g},
        Store.Store.new(),
        History.History.new(),
        Lines.Line.new(sp, ln),
        Shared.Table.new(Ep.Stream),
        Shared.Table.new(Maybe<&2, Shared.Name>),
        []
      }

# the space of c
def Core.space(c: Core) -> String:
  match c:
    case Core{Mount{sp, ln, r, g}, s, h, l, ss, ms, ns}:
      sp

# the name of the file at path in the space of c
def Core.name(c: Core, path: String) -> Shared.Name:
  Shared.Name{Core.space(c), path}

# path lies under the directory dir
def Core.under(path: String, dir: String) -> Bool:
  String.starts_with(path, String.append(dir, "/"))

# path lies under one of the directories ds
def Core.under_any(ds: List<&2, String>, +path: String) -> Bool:
  match ds:
    case Nil{}:
      False{}
    case Con{d, t}:
      List.any.if(u => Core.under_any(t, path), Core.under(path, d))

# the core versions the file at path: it is a valid path, not the space
# file, under no nested space, and the globs of the mount select it
def Core.tracks(c: Core, +path: String) -> Bool:
  match c:
    case Core{Mount{sp, ln, r, g}, s, h, l, ss, ms, ns}:
      mine = List.all.if(
        u => Bool.not(Core.under_any(ns, path)),
        Bool.not(String.eq(path, Mount.space_file()))
      )
      List.all.if(u => Glob.Rule.selects(g, path), Bool.and(Glob.is_path(path), mine))

# the history of c
def Core.history(c: Core) -> History.History:
  match c:
    case Core{m, s, h, l, ss, ms, ns}:
      h

# the store of c
def Core.store(c: Core) -> Store.Store:
  match c:
    case Core{m, s, h, l, ss, ms, ns}:
      s

# the line of c
def Core.line(c: Core) -> Lines.Line:
  match c:
    case Core{m, s, h, l, ss, ms, ns}:
      l

# the stream of the file at path in c: a new stream for a file seen for the
# first time
def Core.stream(c: Core, path: String) -> Ep.Stream:
  match c:
    case Core{m, s, h, l, ss, ms, ns}:
      Maybe.default(&2, Ep.Stream, Shared.Table.get(Ep.Stream, ss, path), Ep.Stream.new())

# the name the file at path moved from, while its next version is not
# recorded yet
def Core.moved(c: Core, path: String) -> Maybe<&2, Shared.Name>:
  match c:
    case Core{m, s, h, l, ss, ms, ns}:
      Maybe.default(
        &2,
        Maybe<&2, Shared.Name>,
        Shared.Table.get(Maybe<&2, Shared.Name>, ms, path),
        None{}
      )

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

# the commands among outputs, with their paths dropped
def Output.commands(os: List<&2, Output>) -> List<&2, Ep.Command>:
  match os:
    case Nil{}:
      Nil{}
    case Con{Command{p, k}, t}:
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
    case Con{Recorded{n, x, a}, t}:
      x <> Output.recorded(t)
    case Con{o, t}:
      Output.recorded(t)

# the outputs hold a Recorded of n with id x
def Output.has_recorded(os: List<&2, Output>, +n: Shared.Name, +x: Shared.Bytes()) -> Bool:
  match os:
    case Nil{}:
      False{}
    case Con{Recorded{m, y, a}, t}:
      same = List.all.if(
        u => Shared.Bytes.is_eq(y, x),
        String.eq(Shared.Name.show(m), Shared.Name.show(n))
      )
      List.any.if(u => Output.has_recorded(t, n, x), same)
    case Con{o, t}:
      Output.has_recorded(t, n, x)

# the records among outputs, in order
def Output.logged(os: List<&2, Output>) -> List<&2, Journal.Record>:
  match os:
    case Nil{}:
      Nil{}
    case Con{Logged{r}, t}:
      r <> Output.logged(t)
    case Con{o, t}:
      Output.logged(t)

# the bytes as items for the store: one item per byte
def Core.items(b: Shared.Bytes()) -> List<&2, Shared.Bytes()>:
  match b:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      [x] <> Core.items(t)

# Laws
# ----

# a signal about a file the core does not track changes nothing
law untracked_ignored:
  for c: Core
  for p: String
  for s: Ep.Signal
  for h: {Core.tracks(c, p) == False{}: Bool}
  {Core.step(c, Noticed{p, s}) == Stepped{c, []}: Stepped}

# a signal about a tracked file sends exactly the commands that its stream
# sends
law noticed_follows_stream:
  for c: Core
  for p: String
  for s: Ep.Signal
  for h: {Core.tracks(c, p) == True{}: Bool}
  {
    Output.commands(
      Stepped.outputs(Core.step(c, Noticed{p, s}))
    )
      == Ep.Stepped.commands(Ep.Stream.step(Core.stream(c, p), s)): List<&2, Ep.Command>
  }

# each version that the stream records becomes exactly one Recorded
# output, when no output is Failed
law records_each_version:
  for c: Core
  for p: String
  for s: Ep.Signal
  for h: {Core.tracks(c, p) == True{}: Bool}
  for f: {
    List.any(
      ~&2,
      ~Output,
      ~Output.is_failed,
      Stepped.outputs(Core.step(c, Noticed{p, s}))
    )
      == False{}: Bool
  }
  {
    List.length(
      &2,
      Shared.Bytes(),
      Output.recorded(Stepped.outputs(Core.step(c, Noticed{p, s})))
    )
      == List.length(&2, Ep.Version, Ep.Stepped.versions(Ep.Stream.step(Core.stream(c, p), s))): Nat
  }

# fetched content that the core records reads back from its node: a node
# of the file, whose root in the store gives exactly the fetched bytes
law fetched_reads_back:
  for c: Core
  for p: String
  for bytes: Shared.Bytes()
  for t: Shared.Bytes()
  for x: Shared.Bytes()
  for parents: List<&2, Shared.Bytes()>
  for r: Store.Ref
  for from: Maybe<&2, Shared.Name>
  for h: {Core.tracks(c, p) == True{}: Bool}
  for o: {
    Output.recorded(
      Stepped.outputs(Core.step(c, Noticed{p, Ep.Fetched{bytes, t}}))
    )
      == [x]: List<&2, Shared.Bytes()>
  }
  for g: {
    History.History.get(
      Core.history(Stepped.core(Core.step(c, Noticed{p, Ep.Fetched{bytes, t}}))),
      x
    )
      == Some{
        History.Node{Core.name(c, p), parents, History.Has{r}, from, History.Outside{}}
      }: Maybe<&2, History.Node>
  }
  {
    Store.Tree.read(
      Core.store(Stepped.core(Core.step(c, Noticed{p, Ep.Fetched{bytes, t}}))),
      r
    )
      == Some{Core.items(bytes)}: Maybe<&2, List<&2, Shared.Bytes()>>
  }

# a recorded version is the one head of its file on the line of the mount
law recorded_heads_line:
  for c: Core
  for i: Input
  for n: Shared.Name
  for x: Shared.Bytes()
  for o: {Output.has_recorded(Stepped.outputs(Core.step(c, i)), n, x) == True{}: Bool}
  {Lines.Line.heads(Core.line(Stepped.core(Core.step(c, i))), n) == [x]: List<&2, Shared.Bytes()>}

# a write whose expected heads are not the heads on the line changes
# nothing and is refused, naming those heads
law write_refused:
  for c: Core
  for p: String
  for b: Shared.Bytes()
  for e: List<&2, Shared.Bytes()>
  for a: String
  for h: {History.Ids.is_eq(e, Lines.Line.heads(Core.line(c), Core.name(c, p))) == False{}: Bool}
  {
    Core.step(
      c,
      Asked{Write{p, b, e, a}}
    )
      == Stepped{
        c,
        [Refused{Core.name(c, p), Lines.Line.heads(Core.line(c), Core.name(c, p))}]
      }: Stepped
  }

# a write of a tracked file with the heads on the line sends one Put of its
# bytes and records one version
law write_accepted:
  for c: Core
  for p: String
  for b: Shared.Bytes()
  for e: List<&2, Shared.Bytes()>
  for a: String
  for t: {Core.tracks(c, p) == True{}: Bool}
  for h: {History.Ids.is_eq(e, Lines.Line.heads(Core.line(c), Core.name(c, p))) == True{}: Bool}
  for f: {
    List.any(
      ~&2,
      ~Output,
      ~Output.is_failed,
      Stepped.outputs(Core.step(c, Asked{Write{p, b, e, a}}))
    )
      == False{}: Bool
  }
  {
    List.length(
      &2,
      Ep.Command,
      Output.commands(Stepped.outputs(Core.step(c, Asked{Write{p, b, e, a}})))
    )
      == 1n: Nat
  }
    &
    {
      List.length(
        &2,
        Shared.Bytes(),
        Output.recorded(Stepped.outputs(Core.step(c, Asked{Write{p, b, e, a}})))
      )
        == 1n: Nat
    }

# the version an accepted write records names its agent as the author
law write_authored:
  for c: Core
  for p: String
  for b: Shared.Bytes()
  for e: List<&2, Shared.Bytes()>
  for a: String
  for x: Shared.Bytes()
  for v: History.Node
  for o: {
    Output.recorded(
      Stepped.outputs(Core.step(c, Asked{Write{p, b, e, a}}))
    )
      == [x]: List<&2, Shared.Bytes()>
  }
  for g: {
    History.History.get(
      Core.history(Stepped.core(Core.step(c, Asked{Write{p, b, e, a}}))),
      x
    )
      == Some{v}: Maybe<&2, History.Node>
  }
  {History.Node.author(v) == History.Agent{a}: History.Author}

# a move records and sends nothing, and remembers where the file came from
# for its next version
law move_remembered:
  for c: Core
  for f: String
  for t: String
  {Stepped.outputs(Core.step(c, Moved{f, t})) == []: List<&2, Output>} &
    {
      Core.moved(
        Stepped.core(Core.step(c, Moved{f, t})),
        t
      )
        == Some{Core.name(c, f)}: Maybe<&2, Shared.Name>
    }

# once a directory starts another space, the core tracks nothing under it
law nested_untracked:
  for c: Core
  for d: String
  for p: String
  for u: {Core.under(p, d) == True{}: Bool}
  {Core.tracks(Stepped.core(Core.step(c, Nested{d})), p) == False{}: Bool}

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

# Persistence
# -----------
# The store, the history and the line are what a power cut must not lose;
# the streams, the pending moves and the nested spaces are rebuilt on
# start, by fetching every file again.

# The state that the journal keeps.
type Persisted is Data:
  Persisted{store: Store.Store, history: History.History, line: Lines.Line}

# the state of c that the journal keeps
def Core.persisted(c: Core) -> Persisted:
  match c:
    case Core{m, s, h, l, ss, ms, ns}:
      Persisted{s, h, l}

# c after the records, in order: each Kept puts its content in the store and
# its node in the history, and moves the line of c when it names that line;
# the other records (seen markers, marks, forks) are the daemon's and leave
# c as it is
law Core.replay:
  for c: Core
  for rs: List<&2, Journal.Record>
  Core

# a core that serves m, after the records of its journal: the records
# replayed into Core.new(m), and the stream of each file whose one head on
# the line holds content primed with the token of that content, so fetching
# the same content again records nothing
law Core.restore:
  for m: Mount
  for rs: List<&2, Journal.Record>
  Core

# the records of a step rebuild exactly what the step kept: replaying them
# on the core before the step gives its store, history and line after the
# step; so replaying a journal rebuilds the state of the run that wrote it
law replay_matches:
  for c: Core
  for i: Input
  {
    Core.persisted(
      Core.replay(c, Output.logged(Stepped.outputs(Core.step(c, i))))
    )
      == Core.persisted(Stepped.core(Core.step(c, i))): Persisted
  }

# no duplicate versions after a restart: on a restored core, content that
# equals the content of a file's one head on the line records nothing
law restored_quiet:
  for m: Mount
  for rs: List<&2, Journal.Record>
  for p: String
  for bytes: Shared.Bytes()
  for x: Shared.Bytes()
  for ps: List<&2, Shared.Bytes()>
  for root: Store.Ref
  for f: Maybe<&2, Shared.Name>
  for a: History.Author
  for h: {
    Lines.Line.heads(
      Core.line(Core.restore(m, rs)),
      Core.name(Core.restore(m, rs), p)
    )
      == [x]: List<&2, Shared.Bytes()>
  }
  for g: {
    History.History.get(
      Core.history(Core.restore(m, rs)),
      x
    )
      == Some{
        History.Node{Core.name(Core.restore(m, rs), p), ps, History.Has{root}, f, a}
      }: Maybe<&2, History.Node>
  }
  for r: {
    Store.Tree.read(
      Core.store(Core.restore(m, rs)),
      root
    )
      == Some{Core.items(bytes)}: Maybe<&2, List<&2, Shared.Bytes()>>
  }
  {
    Output.recorded(
      Stepped.outputs(
        Core.step(Core.restore(m, rs), Noticed{p, Ep.Fetched{bytes, Hash.Hash.blake3(bytes)}})
      )
    )
      == []: List<&2, Shared.Bytes()>
  }
