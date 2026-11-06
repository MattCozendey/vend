import Base
import ../endpoints/file/impl.bend as FileImpl
import ../endpoints/file/spec.bend as File
import ../endpoints/spec.bend as Ep
import ../glob/spec.bend as Glob
import ../hash/spec.bend as Hash
import ../shared.bend as Shared
import ../views/text/impl.bend as TextImpl
import ../views/text/spec.bend as Text
import ./impl.bend as Impl
import ./spec.bend as Spec

# The loop: all of the core's IO, for the file endpoint. It reads the
# space of the root (or makes one), watches the root, lists it once so files that already exist get versioned, then
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

# the inputs of the signals about the file at p
def Loop.about(+p: String, ss: List<&2, Ep.Signal>) -> List<&2, Spec.Input>:
  match ss:
    case Nil{}:
      Nil{}
    case Con{s, t}:
      Spec.Noticed{p, s} <> Loop.about(p, t)

# the inputs of signal s for every path of ps
def Loop.each(ps: List<&2, String>, +s: Ep.Signal) -> List<&2, Spec.Input>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{p, t}:
      Spec.Noticed{p, s} <> Loop.each(t, s)

# the paths of the files whose streams the core keeps
def Loop.known(c: Spec.Core) -> List<&2, String>:
  match c:
    case Spec.Core{m, s, h, l, ss, ms, ns}:
      Shared.Table.keys(Ep.Stream, ss)

# p is the space file of a directory below the root: it starts another
# space there
def Loop.is_nested(p: String) -> Bool:
  String.ends_with(p, String.append("/", Spec.Mount.space_file()))

# the input of signal s about the file at p, after a Nested input for the
# directory of p when p is the space file of another space
def Loop.noticed(+p: String, +s: Ep.Signal) -> List<&2, Spec.Input>:
  dir = String.take(p, Nat.sub(String.length(p), 1n+String.length(Spec.Mount.space_file())))
  Shared.Bool.when(
    List<&2, Spec.Input>,
    Loop.is_nested(p),
    u => [Spec.Nested{dir}, Spec.Noticed{p, s}],
    u => [Spec.Noticed{p, s}]
  )

# the inputs of the notices: AllOverflowed asks every known resource to
# fetch again (again: a hint for each), and AllLost makes every known
# resource unreachable
def Loop.inputs(
  ns: List<&2, File.Notice>,
  +known: List<&2, String>,
  +again: List<&2, Spec.Input>
) -> List<&2, Spec.Input>:
  match ns:
    case Nil{}:
      Nil{}
    case Con{File.About{p, s}, t}:
      List.append(&2, Spec.Input, Loop.noticed(p, s), Loop.inputs(t, known, again))
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

# the paths below the root when reports were lost, so files that came
# without a report of their own (an unpaired rename, say) get fetched too;
# none otherwise
def Loop.relist(root: File.Root, lost: Bool) -> IO(List<&2, String>):
  match lost:
    case False{}:
      IO.pure(List<&2, String>, [])
    case True{}:
      FileImpl.FileEp.list(root)

# a hint for each path, so the core fetches what it tracks, with the
# Nested inputs of the space files of other spaces
def Loop.hints(ps: List<&2, String>) -> List<&2, Spec.Input>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{p, t}:
      List.append(&2, Spec.Input, Loop.noticed(p, Ep.Hinted{}), Loop.hints(t))

# the inputs that carrying out the output o gives: a command goes to the
# endpoint and its answer comes back; anything else is reported
def Loop.carry(
  ~report: Spec.Output -> IO(Unit),
  root: File.Root,
  o: Spec.Output
) -> IO(List<&2, Spec.Input>):
  match o:
    case Spec.Command{+p, Ep.Fetch{}}:
      do IO<List<&2, Spec.Input>>:
        s: Ep.Signal <- FileImpl.FileEp.fetch(root, p)
        return [Spec.Noticed{p, s}]
    case Spec.Command{+p, Ep.Put{b, e}}:
      do IO<List<&2, Spec.Input>>:
        ss: List<&2, Ep.Signal> <- FileImpl.FileEp.put(root, p, b, e)
        return Loop.about(p, ss)
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
          listed: List<&2, String> <- Loop.relist(root, Loop.overflowed(ns))
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
        ns: List<&2, String> <- FileImpl.FileEp.list(root)
        c2: Spec.Core <- Loop.drain(~report, Loop.budget(), root, c, Loop.hints(ns))
        Loop.go(~report, waits, root, w, c2)

# the loop once the root is open and the space is known: start the
# watcher, then the rest
def Loop.opened(
  ~report: Spec.Output -> IO(Unit),
  waits: Nat,
  +root: File.Root,
  m: Spec.Mount
) -> IO(Maybe<&2, String>):
  do IO<Maybe<&2, String>>:
    wr: Result<&1, &1, U32 & String, File> <- FileImpl.FileEp.watch(root)
    Loop.started(~report, waits, root, Spec.Core.new(m), wr)

# The space file
# --------------
# The id of a space is the text of the file ".bend-ver" at its root. A root
# without one gets a new id: 16 random bytes as 32 lowercase hex
# characters, written there before anything else happens.

# the bytes of one random word, low byte first, or the text of its failure
def Loop.word(r: Result<&1, &1, U32 & String, U32>) -> Result<&2, &2, String, Shared.Bytes()>:
  match r:
    case Fail{e}:
      Fail{Loop.why(e)}
    case Done{+x}:
      Done{[(x .&. 255: U32), ((x >> 8n) .&. 255: U32), ((x >> 16n) .&. 255: U32), (x >> 24n: U32)]}

# a then b, or the first failure
def Loop.join(
  a: Result<&2, &2, String, Shared.Bytes()>,
  b: Result<&2, &2, String, Shared.Bytes()>
) -> Result<&2, &2, String, Shared.Bytes()>:
  match a b:
    case Done{x} Done{y}:
      Done{List.append(&2, U32, x, y)}
    case Fail{e} _:
      Fail{e}
    case _ Fail{e}:
      Fail{e}

# n random words as bytes, or the text of a failure
def Loop.random(n: Nat) -> IO(Result<&2, &2, String, Shared.Bytes()>):
  match n:
    case 0n:
      IO.pure(Result<&2, &2, String, Shared.Bytes()>, Done{[]})
    case 1n+k:
      do IO<Result<&2, &2, String, Shared.Bytes()>>:
        r: Result<&1, &1, U32 & String, U32> <- IO.random_u32()
        rest: Result<&2, &2, String, Shared.Bytes()> <- Loop.random(k)
        return Loop.join(Loop.word(r), rest)

# the id that the put of a new space file left, or the text of what went
# wrong
def Loop.created(id: String, ss: List<&2, Ep.Signal>) -> Result<&2, &2, String, String>:
  match ss:
    case Con{Ep.Fetched{b, t}, r}:
      Done{id}
    case Con{Ep.Reached{Ep.Unreachable{why}}, r}:
      Fail{why}
    case Con{s, r}:
      Loop.created(id, r)
    case Nil{}:
      Fail{"the space file was not written"}

# a new space file at the root, with a random id
def Loop.create(
  root: File.Root,
  r: Result<&2, &2, String, Shared.Bytes()>
) -> IO(Result<&2, &2, String, String>):
  match r:
    case Fail{e}:
      IO.pure(Result<&2, &2, String, String>, Fail{e})
    case Done{bytes}:
      +id = Hash.Hash.hex(bytes)
      do IO<Result<&2, &2, String, String>>:
        ss: List<
          &2,
          Ep.Signal> <- FileImpl.FileEp.put(
          root,
          Spec.Mount.space_file(),
          Text.Text.encode(id),
          Ep.WasAbsent{}
        )
        return Loop.created(id, ss)

# the id of the text of a space file: trimmed, and not empty
def Loop.space.text(t: Maybe<&2, String>) -> Result<&2, &2, String, String>:
  match t:
    case None{}:
      Fail{"the space file is not UTF-8"}
    case Some{x}:
      +id = String.trim(x)
      Shared.Bool.when(
        Result<&2, &2, String, String>,
        String.is_empty(id),
        u => Fail{"the space file is empty"},
        u => Done{id}
      )

# the id that the fetched space file holds, trimmed of spaces and line
# ends, or a new one when the root has none
def Loop.space.of(root: File.Root, s: Ep.Signal) -> IO(Result<&2, &2, String, String>):
  match s:
    case Ep.Fetched{b, t}:
      IO.pure(Result<&2, &2, String, String>, Loop.space.text(Text.Text.decode(b)))
    case Ep.Reached{Ep.Absent{}}:
      do IO<Result<&2, &2, String, String>>:
        r: Result<&2, &2, String, Shared.Bytes()> <- Loop.random(4n)
        Loop.create(root, r)
    case Ep.Reached{Ep.Unreachable{why}}:
      IO.pure(Result<&2, &2, String, String>, Fail{why})
    case _:
      IO.pure(Result<&2, &2, String, String>, Fail{"the space file could not be read"})

# the space of the root: read from its space file, or made new
def Loop.space(+root: File.Root) -> IO(Result<&2, &2, String, String>):
  do IO<Result<&2, &2, String, String>>:
    s: Ep.Signal <- FileImpl.FileEp.fetch(root, Spec.Mount.space_file())
    Loop.space.of(root, s)

# the loop once the space is known, or the text of why it is not
def Loop.spaced(
  ~report: Spec.Output -> IO(Unit),
  waits: Nat,
  root: File.Root,
  uri: Shared.Uri,
  line: String,
  globs: List<&2, Glob.Rule>,
  sp: Result<&2, &2, String, String>
) -> IO(Maybe<&2, String>):
  match sp:
    case Fail{e}:
      IO.pure(Maybe<&2, String>, Some{e})
    case Done{id}:
      Loop.opened(~report, waits, root, Spec.Mount{id, line, uri, globs})

# the loop over the root at the OS path os
def Loop.rooted(
  ~report: Spec.Output -> IO(Unit),
  waits: Nat,
  uri: Shared.Uri,
  line: String,
  globs: List<&2, Glob.Rule>,
  os: Maybe<&2, String>
) -> IO(Maybe<&2, String>):
  match os:
    case None{}:
      IO.pure(Maybe<&2, String>, Some{"not a local file URI"})
    case Some{path}:
      do IO<Maybe<&2, String>>:
        +r: File.Root <- FileImpl.FileEp.open(path)
        sp: Result<&2, &2, String, String> <- Loop.space(r)
        Loop.spaced(~report, waits, r, uri, line, globs, sp)

# the core loop over the files below the URI root that the globs select,
# on the line named line, for at most waits waits; None when the waits ran
# out, or the text of what stopped it. The space id comes from the space
# file at the root (made when missing). The watcher starts before the
# listing, so no change between them is lost.
def Loop.run(
  ~report: Spec.Output -> IO(Unit),
  +root: Shared.Uri,
  line: String,
  globs: List<&2, Glob.Rule>,
  waits: Nat
) -> IO(Maybe<&2, String>):
  Loop.rooted(~report, waits, root, line, globs, File.FileEp.root_of(root))
