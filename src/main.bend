import Base
import ./cli/spec.bend as Cli
import ./daemon/impl.bend as DaemonImpl
import ./daemon/loop.bend as Daemon
import ./daemon/spec.bend as Spec
import ./shared.bend as Shared

# The program: the CLI picks the command; start-or-resume runs the daemon,
# and every other command asks it.

# the URI text as the daemon names mounts: read, then shown
def Main.uri(+t: String) -> String:
  Maybe.default(
    &2,
    String,
    Maybe.map(&2, Shared.Uri, String, u => Shared.Uri.show(u), Shared.Uri.read(t)),
    t
  )

# the everyday command of the words ws sent with standard input as its
# bytes, or why standard input could not be read
def Main.stdin(r: Result<&1, &1, U32 & String, Shared.Bytes()>, ws: List<&2, String>) -> IO(Unit):
  match r:
    case Fail{e}:
      (c, t) = e
      IO.die(Unit, 1, String.append("cannot read standard input: ", t))
    case Done{b}:
      Daemon.Client.everyday(ws, b)

# the everyday command of the words ws sent with its bytes: standard input
# when it reads it (a write without --from), else none
def Main.ask(stdin: Bool, ws: List<&2, String>) -> IO(Unit):
  match stdin:
    case False{}:
      Daemon.Client.everyday(ws, [])
    case True{}:
      do IO<Unit>:
        r: Result<&1, &1, U32 & String, Shared.Bytes()> <- Cli.Stdin.read_all()
        Main.stdin(r, ws)

# the run of a parsed command line
def Main.run(c: Result<&2, &2, String, Cli.Cmd>) -> IO(Unit):
  match c:
    case Fail{u}:
      IO.die(Unit, 2, u)
    case Done{Cli.Help{}}:
      IO.print(Cli.Cli.usage())
    case Done{Cli.StartOrResume{}}:
      Daemon.Daemon.start_or_resume()
    case Done{Cli.StatusCmd{}}:
      Daemon.Client.ask(Spec.Status{})
    case Done{Cli.MountCmd{r, gs, ln}}:
      Daemon.Client.ask(Spec.Mount{Main.uri(r), gs, ln})
    case Done{Cli.UnmountCmd{r}}:
      Daemon.Client.ask(Spec.Unmount{Main.uri(r)})
    case Done{Cli.DaemonStop{f}}:
      Daemon.Client.ask(Spec.Stop{f})
    case Done{Cli.AskCmd{+ws}}:
      Main.ask(Cli.Cli.reads_stdin(ws), ws)

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
