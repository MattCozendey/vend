import Base
import ../glob/spec.bend as Glob
import ../shared.bend as Shared

# The command line. It only turns arguments into a command; the core's loop
# does the work, so the CLI holds no behavior of its own.

# A command. Watch: version the files under root that the globs select
# (each read by Glob.Rule.read: a leading '!' excludes, and the last glob
# that matches a path decides); with no globs given, every file ("**").
# Help: print the usage.
type Cmd is Data:
  Watch{root: String, globs: List<&2, String>}
  Help{}

# how to call the program
def Cli.usage() -> String:
  "usage: bend-ver watch <root> [<glob>...]   version the files under <root> that the globs select (default: **; a leading ! excludes; the last glob that matches decides)"

# every glob of rs reads
def Cli.globs_read(rs: List<&2, String>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case Con{r, t}:
      List.all.if(u => Cli.globs_read(t), Maybe.is_some(&2, Glob.Rule, Glob.Rule.read(r)))

# the watch command of root and globs rs, or the usage when one does not
# read
def Cli.watch(root: String, +rs: List<&2, String>) -> Result<&2, &2, String, Cmd>:
  match rs:
    case Nil{}:
      Done{Watch{root, ["**"]}}
    case Con{r, t}:
      Bool.pick(
        Result<&2, &2, String, Cmd>,
        Cli.globs_read(rs),
        Done{Watch{root, rs}},
        Fail{Cli.usage()}
      )

# the command of the arguments after the program's own name, or the usage
def Cli.parse(args: List<&2, String>) -> Result<&2, &2, String, Cmd>:
  match args:
    case Con{w, Con{root, rs}}:
      Shared.Bool.when(
        Result<&2, &2, String, Cmd>,
        String.eq(w, "watch"),
        u => Cli.watch(root, rs),
        u => Fail{Cli.usage()}
      )
    case Con{+w, Nil{}}:
      Bool.pick(Result<&2, &2, String, Cmd>, String.eq(w, "help"), Done{Help{}}, Fail{Cli.usage()})
    case Nil{}:
      Done{Help{}}

# the arguments that spell c
def Cli.show(c: Cmd) -> List<&2, String>:
  match c:
    case Watch{root, rs}:
      "watch" <> root <> rs
    case Help{}:
      ["help"]

# a command reads back from its arguments, when its globs read and there
# is at least one (no globs reads back as "**")
law parse_after_show:
  for root: String
  for rs: List<&2, String>
  for h: {Cli.globs_read(rs) == True{}: Bool}
  for n: {List.is_empty(&2, String, rs) == False{}: Bool}
  {Cli.parse(Cli.show(Watch{root, rs})) == Done{Watch{root, rs}}: Result<&2, &2, String, Cmd>}
