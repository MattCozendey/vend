import Base
import ../daemon/spec.bend as Daemon
import ../glob/spec.bend as Glob
import ../shared.bend as Shared

# The command line. It only turns arguments into a command; the daemon
# does the work, so the CLI holds no behavior of its own.

# A command. StartOrResume: run the daemon in the foreground; the only way
# it starts. StatusCmd: the mounts and clients. MountCmd: version the files
# under the URI root (as Shared.Uri.read reads it) that the globs select,
# on the line named line; each glob is read by Glob.Rule.read and matches
# the path relative to the root (a leading '!' excludes, and the last glob
# that matches a path decides); with no globs given, every file ("**").
# UnmountCmd: stop versioning the mount at the root. DaemonStop: end the
# daemon; without force it refuses while mounts are active or other
# clients are connected. AskCmd: an everyday command (lines, log, show,
# diff, affects, impact, line new, write, restore, mark, merge), whose words
# the daemon reads as they are; a write without --from <uri> writes the
# bytes of standard input (Cli.reads_stdin). Versions from the endpoint are
# recorded as Outside; a command that writes signs its versions with the
# agent name in the environment variable VEND_AGENT. McpCmd: serve the
# everyday commands as MCP tools on standard input and output, for an agent
# harness that starts it (src/mcp). Help: print the usage.
type Cmd is Data:
  StartOrResume{}
  StatusCmd{}
  MountCmd{root: String, globs: List<&2, String>, line: String}
  UnmountCmd{root: String}
  DaemonStop{force: Bool}
  AskCmd{words: List<&2, String>}
  McpCmd{}
  Help{}

# how to call the program
def Cli.usage() -> String:
  String.concat(
    [
      "usage: vend start-or-resume                          run the daemon (in the foreground)\n",
      "       vend status                                   the mounts and clients\n",
      "       vend mount <uri> [<glob>...] [--line <name>]  version the files under the URI root (as\n",
      "         file:///C:/repo) that the globs select (default **; a leading ! excludes; the last glob\n",
      "         that matches decides), on the line <name> (default main)\n",
      "       vend unmount <uri>                            stop versioning that root\n",
      "       vend daemon stop [--force]                    end the daemon (--force: even with mounts)
",
      "       vend mcp                                      the everyday commands as MCP tools on stdio
",
      "       vend ",
      Daemon.Command.syntax(),
      "
         write writes standard input, or the resource at --from <uri>; names are <space>:<path>;",
      " versions are id prefixes or lines; writes are signed with VEND_AGENT"
    ]
  )

# every glob of rs reads
def Cli.globs_read(rs: List<&2, String>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case Con{r, t}:
      List.all.if(u => Cli.globs_read(t), Maybe.is_some(&2, Glob.Rule, Glob.Rule.read(r)))

# The globs and the line of the arguments after the root of a mount.
type Picked is Data:
  Picked{globs: List<&2, String>, line: String}

# the globs and line of the arguments all, given them reversed (rev): a
# last "--line <name>" names the line, else it is "main"
def Cli.pick.rev(rev: List<&2, String>, all: List<&2, String>) -> Picked:
  match rev:
    case Con{ln, Con{flag, t}}:
      Shared.Bool.when(
        Picked,
        String.eq(flag, "--line"),
        u => Picked{List.reverse(&2, String, t), ln},
        u => Picked{all, "main"}
      )
    case _:
      Picked{all, "main"}

# the globs and line of the arguments after the root of a mount
def Cli.pick(+rest: List<&2, String>) -> Picked:
  Cli.pick.rev(List.reverse(&2, String, rest), rest)

# the globs of picked arguments
def Picked.globs(p: Picked) -> List<&2, String>:
  match p:
    case Picked{gs, ln}:
      gs

# the mount command of root and the picked globs and line, with "**" for
# no globs
def Cli.mount.of(root: String, p: Picked) -> Result<&2, &2, String, Cmd>:
  match p:
    case Picked{Nil{}, ln}:
      Done{MountCmd{root, ["**"], ln}}
    case Picked{Con{r, t}, ln}:
      Done{MountCmd{root, Con{r, t}, ln}}

# the mount command of root and the arguments after it, when the root
# reads as a URI and every glob reads; else the usage
def Cli.mount(+root: String, rest: List<&2, String>) -> Result<&2, &2, String, Cmd>:
  +p = Cli.pick(rest)
  ok = List.all.if(
    u => Cli.globs_read(Picked.globs(p)),
    Maybe.is_some(&2, Shared.Uri, Shared.Uri.read(root))
  )
  Shared.Bool.when(
    Result<&2, &2, String, Cmd>,
    ok,
    u => Cli.mount.of(root, p),
    u => Fail{Cli.usage()}
  )

# the unmount command of root, when it reads as a URI
def Cli.unmount(+root: String) -> Result<&2, &2, String, Cmd>:
  Shared.Bool.when(
    Result<&2, &2, String, Cmd>,
    Maybe.is_some(&2, Shared.Uri, Shared.Uri.read(root)),
    u => Done{UnmountCmd{root}},
    u => Fail{Cli.usage()}
  )

# the command of one word
def Cli.word(+w: String) -> Result<&2, &2, String, Cmd>:
  Shared.Bool.when(
    Result<&2, &2, String, Cmd>,
    String.eq(w, "start-or-resume"),
    u => Done{StartOrResume{}},
    u => Shared.Bool.when(
      Result<&2, &2, String, Cmd>,
      String.eq(w, "status"),
      v => Done{StatusCmd{}},
      v => Shared.Bool.when(
        Result<&2, &2, String, Cmd>,
        String.eq(w, "mcp"),
        x => Done{McpCmd{}},
        x => Bool.pick(
          Result<&2, &2, String, Cmd>,
          String.eq(w, "help"),
          Done{Help{}},
          Fail{Cli.usage()}
        )
      )
    )
  )

# w is the first word of an everyday command
def Cli.everyday(w: String) -> Bool:
  List.contains(~String, ~String.eq, Daemon.Command.words(), w)

# the bytes of standard input, read to its end
def Stdin.read_all() -> IO(Result<&1, &1, U32 & String, Shared.Bytes()>):
  import "./effs/stdin.c"
  import "./effs/stdin.js"

# the next line of standard input with its line feed, or the last bytes
# before its end without one; no bytes at its end
def Stdin.read_line() -> IO(Result<&1, &1, U32 & String, Shared.Bytes()>):
  import "./effs/stdin.c"
  import "./effs/stdin.js"

# ws has the option key
def Cli.has(ws: List<&2, String>, key: String) -> Bool:
  List.contains(~String, ~String.eq, ws, key)

# the everyday command of the words ws reads its bytes from standard input:
# a write that names no --from
def Cli.reads_stdin(ws: List<&2, String>) -> Bool:
  match ws:
    case Con{w, r}:
      Bool.and(String.eq(w, "write"), Bool.not(Cli.has(r, "--from")))
    case Nil{}:
      False{}

# the daemon command of the words after "daemon"
def Cli.daemon(ws: List<&2, String>) -> Result<&2, &2, String, Cmd>:
  match ws:
    case Con{s, Nil{}}:
      Bool.pick(
        Result<&2, &2, String, Cmd>,
        String.eq(s, "stop"),
        Done{DaemonStop{False{}}},
        Fail{Cli.usage()}
      )
    case Con{s, Con{f, Nil{}}}:
      Bool.pick(
        Result<&2, &2, String, Cmd>,
        Bool.and(String.eq(s, "stop"), String.eq(f, "--force")),
        Done{DaemonStop{True{}}},
        Fail{Cli.usage()}
      )
    case _:
      Fail{Cli.usage()}

# the command of the words w, a, rest when w is no everyday command
def Cli.parse.other(+w: String, +a: String, +rest: List<&2, String>) -> Result<&2, &2, String, Cmd>:
  Shared.Bool.when(
    Result<&2, &2, String, Cmd>,
    String.eq(w, "mount"),
    u => Cli.mount(a, rest),
    u => Shared.Bool.when(
      Result<&2, &2, String, Cmd>,
      Bool.and(String.eq(w, "unmount"), List.is_empty(&2, String, rest)),
      v => Cli.unmount(a),
      v => Shared.Bool.when(
        Result<&2, &2, String, Cmd>,
        String.eq(w, "daemon"),
        x => Cli.daemon(a <> rest),
        x => Fail{Cli.usage()}
      )
    )
  )

# the command of the arguments after the program's own name, or the usage
def Cli.parse(args: List<&2, String>) -> Result<&2, &2, String, Cmd>:
  match args:
    case Nil{}:
      Done{Help{}}
    case Con{+w, Nil{}}:
      Shared.Bool.when(
        Result<&2, &2, String, Cmd>,
        Cli.everyday(w),
        u => Done{AskCmd{[w]}},
        u => Cli.word(w)
      )
    case Con{+w, Con{+a, +rest}}:
      Shared.Bool.when(
        Result<&2, &2, String, Cmd>,
        Cli.everyday(w),
        e => Done{AskCmd{w <> a <> rest}},
        e => Cli.parse.other(w, a, rest)
      )

# the arguments that spell c
def Cli.show(c: Cmd) -> List<&2, String>:
  match c:
    case StartOrResume{}:
      ["start-or-resume"]
    case StatusCmd{}:
      ["status"]
    case MountCmd{root, gs, ln}:
      "mount" <> root <> List.append(&2, String, gs, ["--line", ln])
    case UnmountCmd{root}:
      ["unmount", root]
    case DaemonStop{False{}}:
      ["daemon", "stop"]
    case DaemonStop{True{}}:
      ["daemon", "stop", "--force"]
    case AskCmd{ws}:
      ws
    case McpCmd{}:
      ["mcp"]
    case Help{}:
      ["help"]

# a mount command reads back from its arguments, when its root reads as a
# URI, its globs read, and there is at least one (no globs reads back as
# "**")
law parse_after_show:
  for root: String
  for rs: List<&2, String>
  for ln: String
  for u: {Maybe.is_some(&2, Shared.Uri, Shared.Uri.read(root)) == True{}: Bool}
  for h: {Cli.globs_read(rs) == True{}: Bool}
  for n: {List.is_empty(&2, String, rs) == False{}: Bool}
  {
    Cli.parse(
      Cli.show(MountCmd{root, rs, ln})
    )
      == Done{MountCmd{root, rs, ln}}: Result<&2, &2, String, Cmd>
  }

# the words of an everyday command reach the daemon as they are
law ask_passes_words:
  for w: String
  for ws: List<&2, String>
  for e: {Cli.everyday(w) == True{}: Bool}
  {Cli.parse(w <> ws) == Done{AskCmd{w <> ws}}: Result<&2, &2, String, Cmd>}
