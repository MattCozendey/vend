import Base
import ../cli/spec.bend as Cli
import ../daemon/loop.bend as Daemon
import ../json/spec.bend as J
import ../shared.bend as Shared
import ../views/text/impl.bend as TextImpl
import ../views/text/spec.bend as Text
import ./spec.bend as Spec

# The MCP front's loop: read one line of standard input, step, answer on
# standard output; a tool call goes to the daemon, and its answer becomes
# the tool result. It never starts the daemon: when the daemon is down, a
# tool call is an error result that says so. It ends at the end of its
# input, or when standard input cannot be read. Stdout is flushed before
# each wait for input, so every answer is out before the next read.

# r without the line ends at its start
def Line.trim.rev(r: Shared.Bytes()) -> Shared.Bytes():
  match r:
    case Nil{}:
      Nil{}
    case Con{+x, +t}:
      Shared.Bool.when(
        Shared.Bytes(),
        Bool.or(U32.is_eq(x, 10), U32.is_eq(x, 13)),
        u => Line.trim.rev(t),
        u => Con{x, t}
      )

# b without the line feed and carriage return at its end
def Line.trim(b: Shared.Bytes()) -> Shared.Bytes():
  List.reverse(&2, U32, Line.trim.rev(List.reverse(&2, U32, b)))

# the JSON value of a line of UTF-8, or None when it is not one
def Line.json(m: Maybe<&2, String>) -> Maybe<&2, J.Json>:
  match m:
    case None{}:
      None{}
    case Some{s}:
      J.Json.read(s)

# what the daemon said, as the result of the tool call id
def Mcp.told(id: J.Json, e: Spec.Era, s: Daemon.Shown) -> J.Json:
  match s:
    case Daemon.Shown{ok, ls}:
      Spec.Mcp.result(id, e, ok, String.join(ls, "\n"))

# what the loop does for the step: answer, ask the daemon then answer, or
# nothing; and the state after it
def Mcp.out(st: Spec.McpStep) -> IO(Spec.McpState):
  match st:
    case Spec.McpStep{s, Spec.Quiet{}}:
      IO.pure(Spec.McpState, s)
    case Spec.McpStep{s, Spec.Answer{msg}}:
      do IO<Spec.McpState>:
        IO.print(J.Json.show(msg))
        return s
    case Spec.McpStep{s, Spec.Forward{id, e, b}}:
      do IO<Spec.McpState>:
        h: Daemon.Heard <- Daemon.Client.request(b)
        IO.print(J.Json.show(Mcp.told(id, e, Daemon.Client.shown(h))))
        return s

# the state after the line b (its bytes without line ends); a blank line is
# skipped
def Mcp.line(s: Spec.McpState, b: Shared.Bytes()) -> IO(Spec.McpState):
  match b:
    case Nil{}:
      IO.pure(Spec.McpState, s)
    case Con{x, t}:
      Mcp.out(Spec.Mcp.step(s, Line.json(Text.Text.decode(Con{x, t}))))

# the loop, given what the last read of a line got: no bytes is the end of
# input; fuel bounds the lines
def Mcp.go(
  fuel: Nat,
  s: Spec.McpState,
  r: Result<&1, &1, U32 & String, Shared.Bytes()>
) -> IO(Unit):
  match fuel:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+f:
      match r:
        case Fail{e}:
          IO.pure(Unit, Unit{})
        case Done{Nil{}}:
          IO.pure(Unit, Unit{})
        case Done{Con{x, t}}:
          do IO<Unit>:
            s2: Spec.McpState <- Mcp.line(s, Line.trim(Con{x, t}))
            next: Result<&1, &1, U32 & String, Shared.Bytes()> <- Cli.Stdin.read_line()
            Mcp.go(f, s2, next)

# serve MCP on standard input and output until the input ends; the agent
# when no client names one is the one VEND_AGENT names, else "unnamed"
def Mcp.run() -> IO(Unit):
  do IO<Unit>:
    a: String <- Daemon.Client.agent()
    r: Result<&1, &1, U32 & String, Shared.Bytes()> <- Cli.Stdin.read_line()
    Mcp.go(4294967295n, Spec.McpState{a, None{}}, r)
