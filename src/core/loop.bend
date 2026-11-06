import Base
import ../endpoints/file/impl.bend as FileImpl
import ../endpoints/file/spec.bend as File
import ../endpoints/spec.bend as Ep
import ../glob/spec.bend as Glob
import ../shared.bend as Shared
import ./impl.bend as Impl
import ./spec.bend as Spec

# The loop: all of the core's IO, for the file endpoint. It watches the
# root, lists it once so files that already exist get versioned, then
# waits for reports. Each input goes through Spec.Core.step; each command
# goes to the endpoint, whose answer is the next input; every other output
# goes to the front's report, so the loop prints nothing itself. Bend
# needs every loop to end: the loop counts down waits (each at most half a
# second), and the inputs of one wait count down a budget of steps.

# the most steps that the inputs of one wait may take
def Loop.budget() -> Nat:
  1000000n

# how long one wait lasts at most, in milliseconds
def Loop.wait_ms() -> U32:
  500

# the path of n below the root
def Loop.rest(n: Shared.Name) -> String:
  match n:
    case Shared.Name{Shared.FileScheme{}, r}:
      r

# the inputs of the signals about n
def Loop.about(+n: Shared.Name, ss: List<&2, Ep.Signal>) -> List<&2, Spec.Input>:
  match ss:
    case Nil{}:
      Nil{}
    case Con{s, t}:
      Spec.Noticed{n, s} <> Loop.about(n, t)

# the inputs of signal s for every name of ns
def Loop.each(ns: List<&2, Shared.Name>, +s: Ep.Signal) -> List<&2, Spec.Input>:
  match ns:
    case Nil{}:
      Nil{}
    case Con{n, t}:
      Spec.Noticed{n, s} <> Loop.each(t, s)

# rest, with the name m in front when there is one
def Loop.put(m: Maybe<&2, Shared.Name>, rest: List<&2, Shared.Name>) -> List<&2, Shared.Name>:
  match m:
    case None{}:
      rest
    case Some{n}:
      n <> rest

# the names of the texts that read as names
def Loop.names(ks: List<&2, String>) -> List<&2, Shared.Name>:
  match ks:
    case Nil{}:
      Nil{}
    case Con{k, t}:
      Loop.put(Shared.Name.read(k), Loop.names(t))

# the names of the resources whose streams the core keeps
def Loop.known(c: Spec.Core) -> List<&2, Shared.Name>:
  match c:
    case Spec.Core{tr, s, h, ss, ms}:
      Loop.names(Map.keys(&2, Ep.Stream, ss))

# the inputs of the notices: AllOverflowed asks every known resource to
# fetch again (again: a hint for each), and AllLost makes every known
# resource unreachable
def Loop.inputs(
  ns: List<&2, File.Notice>,
  +known: List<&2, Shared.Name>,
  +again: List<&2, Spec.Input>
) -> List<&2, Spec.Input>:
  match ns:
    case Nil{}:
      Nil{}
    case Con{File.About{n, s}, t}:
      Spec.Noticed{n, s} <> Loop.inputs(t, known, again)
    case Con{File.Moved{a, b}, t}:
      Spec.Moved{a, b} <> Loop.inputs(t, known, again)
    case Con{File.AllOverflowed{}, t}:
      List.append(&2, Spec.Input, again, Loop.inputs(t, known, again))
    case Con{File.AllLost{why}, t}:
      List.append(
        &2,
        Spec.Input,
        Loop.each(known, Ep.Reached{Ep.Unreachable{why}}),
        Loop.inputs(t, known, again)
      )

# some notice says that reports were lost
def Loop.overflowed(ns: List<&2, File.Notice>) -> Bool:
  match ns:
    case Nil{}:
      False{}
    case Con{File.AllOverflowed{}, t}:
      True{}
    case Con{n, t}:
      Loop.overflowed(t)

# the names below the root when reports were lost, so files that came
# without a report of their own (an unpaired rename, say) get fetched too;
# none otherwise
def Loop.relist(root: File.Root, lost: Bool) -> IO(List<&2, Shared.Name>):
  match lost:
    case False{}:
      IO.pure(List<&2, Shared.Name>, [])
    case True{}:
      FileImpl.FileEp.list(root)

# a hint for each name, so the core fetches what it tracks
def Loop.hints(ns: List<&2, Shared.Name>) -> List<&2, Spec.Input>:
  Loop.each(ns, Ep.Hinted{})

# the inputs that carrying out the output o gives: a command goes to the
# endpoint and its answer comes back; anything else is reported
def Loop.carry(
  ~report: Spec.Output -> IO(Unit),
  root: File.Root,
  o: Spec.Output
) -> IO(List<&2, Spec.Input>):
  match o:
    case Spec.Command{+n, Ep.Fetch{}}:
      do IO<List<&2, Spec.Input>>:
        s: Ep.Signal <- FileImpl.FileEp.fetch(root, Loop.rest(n))
        return [Spec.Noticed{n, s}]
    case Spec.Command{+n, Ep.Put{b, e}}:
      do IO<List<&2, Spec.Input>>:
        ss: List<&2, Ep.Signal> <- FileImpl.FileEp.put(root, Loop.rest(n), b, e)
        return Loop.about(n, ss)
    case x:
      do IO<List<&2, Spec.Input>>:
        report(x)
        return []

# the inputs that carrying out the outputs gives, in order
def Loop.carry_all(
  ~report: Spec.Output -> IO(Unit),
  +root: File.Root,
  os: List<&2, Spec.Output>
) -> IO(List<&2, Spec.Input>):
  match os:
    case Nil{}:
      IO.pure(List<&2, Spec.Input>, [])
    case Con{o, t}:
      do IO<List<&2, Spec.Input>>:
        a: List<&2, Spec.Input> <- Loop.carry(~report, root, o)
        b: List<&2, Spec.Input> <- Loop.carry_all(~report, root, t)
        return List.append(&2, Spec.Input, a, b)

# k of the core and the outputs of a step
def Loop.split(
  s: Spec.Stepped,
  k: Spec.Core -> List<&2, Spec.Output> -> IO(Spec.Core)
) -> IO(Spec.Core):
  match s:
    case Spec.Stepped{c, os}:
      k(c, os)

# the core after the inputs of queue, and the inputs their outputs give,
# in order; fuel bounds the steps
def Loop.drain(
  ~report: Spec.Output -> IO(Unit),
  fuel: Nat,
  +root: File.Root,
  c: Spec.Core,
  queue: List<&2, Spec.Input>
) -> IO(Spec.Core):
  match fuel:
    case 0n:
      IO.pure(Spec.Core, c)
    case 1n+f:
      match queue:
        case Nil{}:
          IO.pure(Spec.Core, c)
        case Con{i, t}:
          Loop.split(Spec.Core.step(c, i), c2 => os => do IO<Spec.Core>:
            more: List<&2, Spec.Input> <- Loop.carry_all(~report, root, os)
            Loop.drain(~report, f, root, c2, List.append(&2, Spec.Input, t, more)))

# the text of an error
def Loop.why(e: U32 & String) -> String:
  (c, t) = e
  t

# k of the watcher and the notices of a wait, or the text of its failure
def Loop.waited(
  r: File & Result<&1, &1, U32 & String, List<&2, File.Notice>>,
  k: File -> List<&2, File.Notice> -> IO(Maybe<&2, String>)
) -> IO(Maybe<&2, String>):
  (w, res) = r
  match res:
    case Fail{e}:
      do IO<Maybe<&2, String>>:
        FileImpl.FileEp.unwatch(w)
        return Some{Loop.why(e)}
    case Done{ns}:
      k(w, ns)

# the waits of the watcher w, at most waits of them, with the core c; None
# when the waits ran out, or the text of a failed wait
def Loop.go(
  ~report: Spec.Output -> IO(Unit),
  waits: Nat,
  +root: File.Root,
  w: File,
  +c: Spec.Core
) -> IO(Maybe<&2, String>):
  match waits:
    case 0n:
      do IO<Maybe<&2, String>>:
        FileImpl.FileEp.unwatch(w)
        return None{}
    case 1n+f:
      do IO<Maybe<&2, String>>:
        r: File
          & Result<
            &1,
            &1,
            U32 & String,
            List<&2, File.Notice>> <- FileImpl.FileEp.next(w, Loop.wait_ms())
        Loop.waited(r, w2 => +ns => do IO<Maybe<&2, String>>:
          listed: List<&2, Shared.Name> <- Loop.relist(root, Loop.overflowed(ns))
          ins: List<&2, Spec.Input> = List.append(&2, Spec.Input, Loop.inputs(ns, Loop.known(c), Loop.each(Loop.known(c), Ep.Hinted{})), Loop.hints(listed))
          c2: Spec.Core <- Loop.drain(~report, Loop.budget(), root, c, ins)
          Loop.go(~report, f, root, w2, c2))

# the loop once the watcher of the root started: list the root, fetch what
# the core tracks, then wait
def Loop.started(
  ~report: Spec.Output -> IO(Unit),
  waits: Nat,
  +root: File.Root,
  c: Spec.Core,
  wr: Result<&1, &1, U32 & String, File>
) -> IO(Maybe<&2, String>):
  match wr:
    case Fail{e}:
      IO.pure(Maybe<&2, String>, Some{Loop.why(e)})
    case Done{w}:
      do IO<Maybe<&2, String>>:
        ns: List<&2, Shared.Name> <- FileImpl.FileEp.list(root)
        c2: Spec.Core <- Loop.drain(~report, Loop.budget(), root, c, Loop.hints(ns))
        Loop.go(~report, waits, root, w, c2)

# the loop once the root is open: start the watcher, then the rest
def Loop.opened(
  ~report: Spec.Output -> IO(Unit),
  waits: Nat,
  +root: File.Root,
  rules: List<&2, Glob.Rule>
) -> IO(Maybe<&2, String>):
  do IO<Maybe<&2, String>>:
    wr: Result<&1, &1, U32 & String, File> <- FileImpl.FileEp.watch(root)
    Loop.started(~report, waits, root, Spec.Core.new(rules), wr)

# the core's loop over the files below root that rules select, for at most
# waits waits; None when the waits ran out, or the text of what stopped it.
# The watcher starts before the listing, so no change between them is lost.
def Loop.run(
  ~report: Spec.Output -> IO(Unit),
  root: String,
  rules: List<&2, Glob.Rule>,
  waits: Nat
) -> IO(Maybe<&2, String>):
  do IO<Maybe<&2, String>>:
    r: File.Root <- FileImpl.FileEp.open(root)
    Loop.opened(~report, waits, r, rules)
