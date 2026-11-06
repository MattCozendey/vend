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
