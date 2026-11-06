import Base
import ./cli/spec.bend as Cli
import ./core/loop.bend as Loop
import ./core/spec.bend as Core
import ./glob/impl.bend as GlobImpl
import ./glob/spec.bend as Glob
import ./hash/spec.bend as Hash
import ./shared.bend as Shared

# The program: the CLI picks the command, and the core's loop does the
# work. This file only turns outputs into lines.

# the line of an output; commands go to the endpoint and never reach here
def Main.report(o: Core.Output) -> IO(Unit):
  match o:
    case Core.Recorded{n, x}:
      IO.print(String.concat(["recorded ", Shared.Name.show(n), " ", Hash.Hash.hex(x)]))
    case Core.Refused{n, hs}:
      IO.print("refused " ++ Shared.Name.show(n))
    case Core.Failed{n, p}:
      IO.print("failed " ++ Shared.Name.show(n))
    case Core.Stopped{}:
      IO.print("stopped")
    case Core.Command{n, k}:
      IO.pure(Unit, Unit{})

# rest, with the glob m in front when there is one
def Main.put(m: Maybe<&2, Glob.Rule>, rest: List<&2, Glob.Rule>) -> List<&2, Glob.Rule>:
  match m:
    case None{}:
      rest
    case Some{g}:
      g <> rest

# the globs of the lines; Cli.parse already checked that each reads
def Main.globs(ls: List<&2, String>) -> List<&2, Glob.Rule>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{l, t}:
      Main.put(Glob.Rule.read(l), Main.globs(t))

# how many waits a watch lasts at most: the largest Nat literal, about 68
# years of half-second waits
def Main.waits() -> Nat:
  4294967295n

# the line for how the loop ended: nothing when its waits ran out
def Main.ended(r: Maybe<&2, String>) -> IO(Unit):
  match r:
    case None{}:
      IO.pure(Unit, Unit{})
    case Some{why}:
      IO.print("stopped: " ++ why)

# the run of a parsed command line
def Main.run(c: Result<&2, &2, String, Cli.Cmd>) -> IO(Unit):
  match c:
    case Fail{u}:
      IO.print(u)
    case Done{Cli.Help{}}:
      IO.print(Cli.Cli.usage())
    case Done{Cli.Watch{root, gs}}:
      do IO<Unit>:
        r: Maybe<&2, String> <- Loop.Loop.run(~Main.report, root, Main.globs(gs), Main.waits())
        Main.ended(r)

# the arguments as a reusable list
def Main.args(xs: List<String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      x <> Main.args(t)

def main() -> IO(Unit):
  do IO<Unit>:
    args: List<String> <- IO.args()
    Main.run(Cli.Cli.parse(List.tail(&2, String, Main.args(args))))
