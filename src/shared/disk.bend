import Base

# Disk
# ----
# The effects of a program that keeps its state in files: steps that may
# fail with a message, files read and written whole as bytes, words kept as
# bytes, and the directories and the removal of files that Base has no
# effect for, done by the programs of the operating system (mkdir, ls, rm).
# This is code that runs and talks to the operating system: no law covers it.

# Steps that may fail
# -------------------

# an effect that answers a value of A, or a message that says why it could not
def Run(-A: Type) -> Type:
  IO(Result<&1, &1, String, A>)

# the step that answers x
def Run.pure(-A: Type, x: A) -> Run(A):
  IO.pure(Result<&1, &1, String, A>, Done{x})

# what f does with the value of r; a message of r stays
def Run.next(-A: Type, -B: Type, r: Result<&1, &1, String, A>, f: A -> Run(B)) -> Run(B):
  match r:
    case Fail{e}:
      IO.pure(Result<&1, &1, String, B>, Fail{e})
    case Done{x}:
      f(x)

# the step m, then f on its value
def Run.bind(-A: Type, -B: Type, m: Run(A), f: A -> Run(B)) -> Run(B):
  IO.bind(Result<&1, &1, String, A>, Result<&1, &1, String, B>, m, r => Run.next(A, B, r, f))

# the step that fails with the message msg
def Run.fail(-A: Type, msg: String) -> Run(A):
  IO.pure(Result<&1, &1, String, A>, Fail{msg})

# the step that answers what r holds
def Run.of(-A: Type, r: Result<&1, &1, String, A>) -> Run(A):
  IO.pure(Result<&1, &1, String, A>, r)

# the effect m, as a step that does not fail
def Run.io(-A: Type, m: IO(A)) -> Run(A):
  IO.bind(A, Result<&1, &1, String, A>, m, x => IO.pure(Result<&1, &1, String, A>, Done{x}))

# what the effect answered, with what it was doing (what) before its message
def Run.sys.of(
  -A: Type,
  what: String,
  r: Result<&1, &1, U32 & String, A>
) -> Result<&1, &1, String, A>:
  match r:
    case Fail{(code, msg)}:
      Fail{what ++ ": " ++ msg}
    case Done{x}:
      Done{x}

# the effect m of Base, as a step whose message says what it was doing
def Run.sys(-A: Type, what: String, m: IO(Result<&1, &1, U32 & String, A>)) -> Run(A):
  IO.bind(
    Result<&1, &1, U32 & String, A>,
    Result<&1, &1, String, A>,
    m,
    r => IO.pure(Result<&1, &1, String, A>, Run.sys.of(A, what, r))
  )

# what r holds, with the message msg for its message
def Run.else.of(-A: Type, msg: String, r: Result<&1, &1, String, A>) -> Result<&1, &1, String, A>:
  match r:
    case Fail{e}:
      Fail{msg}
    case Done{x}:
      Done{x}

# the step m, which fails with the message msg when it fails
def Run.else(-A: Type, msg: String, m: Run(A)) -> Run(A):
  IO.bind(
    Result<&1, &1, String, A>,
    Result<&1, &1, String, A>,
    m,
    r => IO.pure(Result<&1, &1, String, A>, Run.else.of(A, msg, r))
  )

# Words as bytes
# --------------
# A word is kept as its four bytes, the highest first.

# the bytes of the words ws, then rest
def Words.bytes(ws: List<&2, U32>, rest: List<&2, U32>) -> List<&2, U32>:
  match ws:
    case Nil{}:
      rest
    case Con{+w, more}:
      +hi = (w / 65536: U32)
      b0 = (hi / 256: U32)
      b0
        <> (hi % 256: U32)
        <> ((w / 256: U32) % 256: U32)
        <> (w % 256: U32)
        <> Words.bytes(more, rest)

# the words of the bytes bs, after the words acc in reverse order; none when
# the bytes do not end at a whole word
def Words.of_bytes(bs: List<&2, U32>, acc: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match bs:
    case Nil{}:
      Some{List.reverse(&2, U32, acc)}
    case Con{a, Con{b, Con{c, Con{d, rest}}}}:
      Words.of_bytes(rest, (((a * 256 + b: U32) * 256 + c: U32) * 256 + d: U32) <> acc)
    case _:
      None{}

# Files
# -----

# what the effect on a file answered, and the file closed
def File.done(
  -A: Type,
  p: File & Result<&1, &1, U32 & String, A>
) -> IO(Result<&1, &1, U32 & String, A>):
  (f, r) = p
  IO.bind(
    Unit,
    Result<&1, &1, U32 & String, A>,
    File.close(f),
    u => IO.pure(Result<&1, &1, U32 & String, A>, r)
  )

# the bytes of the file whose size p answered, and the file closed
def File.sized(
  p: File & Result<&1, &1, U32 & String, U32>
) -> IO(Result<&1, &1, U32 & String, List<&2, U32>>):
  match p:
    case (f, Fail{e}):
      do IO<Result<&1, &1, U32 & String, List<&2, U32>>>:
        File.close(f)
        return Fail{e}
    case (f, Done{size}):
      IO.bind(
        File & Result<&1, &1, U32 & String, List<&2, U32>>,
        Result<&1, &1, U32 & String, List<&2, U32>>,
        File.read_bytes(f, size),
        File.done(List<&2, U32>)
      )

# the bytes of the file at the path path
def Disk.read(+path: String) -> Run(List<&2, U32>):
  do Run<List<&2, U32>>:
    f: File <- Run.sys(File, "open " ++ path, File.open(path, "r"))
    Run.sys(
      List<&2, U32>,
      "read " ++ path,
      IO.bind(
        File & Result<&1, &1, U32 & String, U32>,
        Result<&1, &1, U32 & String, List<&2, U32>>,
        File.size(f),
        File.sized
      )
    )

# the file at the path path, opened in the mode mode of File.open, after it
# took the bytes bs
def Disk.write(+path: String, mode: String, bs: List<&2, U32>) -> Run(Unit):
  do Run<Unit>:
    f: File <- Run.sys(File, "open " ++ path, File.open(path, mode))
    Run.sys(
      Unit,
      "write " ++ path,
      IO.bind(
        File & Result<&1, &1, U32 & String, Unit>,
        Result<&1, &1, U32 & String, Unit>,
        File.write_bytes(f, bs),
        File.done(Unit)
      )
    )

# the words m that the file at the path path holds, if it ends at a whole word
def Words.got(path: String, m: Maybe<&2, List<&2, U32>>) -> Run(List<&2, U32>):
  match m:
    case None{}:
      Run.fail(List<&2, U32>, path ++ ": the file does not end at a whole word")
    case Some{ws}:
      Run.pure(List<&2, U32>, ws)

# the words of the file at the path path
def Disk.words(+path: String) -> Run(List<&2, U32>):
  do Run<List<&2, U32>>:
    bs: List<&2, U32> <- Disk.read(path)
    Words.got(path, Words.of_bytes(bs, []))

# Programs
# --------

# what the program answered: its output when its status is 0, else what it
# said on its error output
def Program.done(r: U32 & (String & String)) -> Result<&1, &1, String, String>:
  match r:
    case (0, (out, err)):
      Done{out}
    case (status, (out, err)):
      Fail{err}

# the output of the program program run with the arguments args
def Program.run(+program: String, args: List<String>) -> Run(String):
  Run.bind(
    U32 & (String & String),
    String,
    Run.sys(U32 & (String & String), program, Process.run(program, args, "", 67108864, 60000)),
    r => Run.of(String, Program.done(r))
  )

# a new directory at the path path; it fails when the path is there
def Disk.make_dir(path: String) -> Run(Unit):
  do Run<Unit>:
    out: String <- Program.run("mkdir", [path])
    return Unit{}

# the names in the directory at the path path
def Disk.names(path: String) -> Run(List<&2, String>):
  do Run<List<&2, String>>:
    out: String <- Program.run("ls", ["-1", path])
    return List.filter(~String, ~(s => Bool.not(String.is_empty(s))), String.lines(out))

# the files at the paths paths removed; a path that is not there is no error
def Disk.remove(paths: List<String>) -> Run(Unit):
  do Run<Unit>:
    out: String <- Program.run("rm", "-f" <> paths)
    return Unit{}
