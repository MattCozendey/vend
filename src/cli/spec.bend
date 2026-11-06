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
# the daemon reads; from: the file whose bytes a write writes (--from), as
# Base has no effect that reads standard input. Versions from the endpoint
# are recorded as Outside; a command that writes signs its versions with
# the agent name in the environment variable BEND_VER_AGENT. Help: print
# the usage.
type Cmd is Data:
  StartOrResume{}
  StatusCmd{}
  MountCmd{root: String, globs: List<&2, String>, line: String}
  UnmountCmd{root: String}
  DaemonStop{force: Bool}
  AskCmd{words: List<&2, String>, from: Maybe<&2, String>}
  Help{}

# how to call the program
def Cli.usage() -> String:
  String.concat(
    [
      "usage: bend-ver start-or-resume                          run the daemon (in the foreground)\n",
      "       bend-ver status                                   the mounts and clients\n",
      "       bend-ver mount <uri> [<glob>...] [--line <name>]  version the files under the URI root (as\n",
      "         file:///C:/repo) that the globs select (default **; a leading ! excludes; the last glob\n",
      "         that matches decides), on the line <name> (default main)\n",
      "       bend-ver unmount <uri>                            stop versioning that root\n",
      "       bend-ver daemon stop [--force]                    end the daemon (--force: even with mounts)
",
      "       bend-ver ",
      Daemon.Command.syntax(),
      "
         write also takes --from <file> (its bytes); names are <space>:<path>; versions are id prefixes or",
      " lines; writes are signed with BEND_VER_AGENT"
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
      v => Bool.pick(
        Result<&2, &2, String, Cmd>,
        String.eq(w, "help"),
        Done{Help{}},
        Fail{Cli.usage()}
      )
    )
  )

# w is the first word of an everyday command
def Cli.everyday(+w: String) -> Bool:
  List.contains(~String, ~String.eq, Daemon.Command.words(), w)

# the words without a "--from <file>" pair, and the file of the first one
type Split is Data:
  Split{words: List<&2, String>, from: Maybe<&2, String>}

# a split with the file f, when it has none yet
def Cli.split.from(s: Split, f: String) -> Split:
  match s:
    case Split{ws, None{}}:
      Split{ws, Some{f}}
    case Split{ws, m}:
      Split{ws, m}

# the split of ws, given the words before, reversed
def Cli.split.go(ws: List<&2, String>, +before: List<&2, String>) -> Split:
  match ws:
    case Nil{}:
      Split{List.reverse(&2, String, before), None{}}
    case Con{+w, Con{+f, +t}}:
      Shared.Bool.when(
        Split,
        String.eq(w, "--from"),
        u => Cli.split.from(Cli.split.go(t, before), f),
        u => Cli.split.go(Con{f, t}, w <> before)
      )
    case Con{w, Nil{}}:
      Split{List.reverse(&2, String, w <> before), None{}}

# the command of a split write
def Cli.ask.split(s: Split) -> Cmd:
  match s:
    case Split{ws, m}:
      AskCmd{ws, m}

# the everyday command of the words ws: a write takes its bytes from the
# file of --from; every other command keeps --from among its words (line
# new names its source with it)
def Cli.ask(+ws: List<&2, String>) -> Cmd:
  match ws:
    case Con{w, r}:
      Shared.Bool.when(
        Cmd,
        String.eq(w, "write"),
        u => Cli.ask.split(Cli.split.go(ws, [])),
        u => AskCmd{ws, None{}}
      )
    case Nil{}:
      AskCmd{ws, None{}}

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
        u => Done{Cli.ask([w])},
        u => Cli.word(w)
      )
    case Con{+w, Con{+a, +rest}}:
      Shared.Bool.when(
        Result<&2, &2, String, Cmd>,
        Cli.everyday(w),
        e => Done{Cli.ask(w <> a <> rest)},
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
    case AskCmd{ws, None{}}:
      ws
    case AskCmd{ws, Some{f}}:
      List.append(&2, String, ws, ["--from", f])
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

# the words of an everyday command reach the daemon as they are, when the
# command is not a write (a write moves its --from file out of its words)
law ask_passes_words:
  for w: String
  for ws: List<&2, String>
  for e: {Cli.everyday(w) == True{}: Bool}
  for n: {String.eq(w, "write") == False{}: Bool}
  {Cli.parse(w <> ws) == Done{AskCmd{w <> ws, None{}}}: Result<&2, &2, String, Cmd>}
