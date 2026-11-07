import Base
import ../cli/spec.bend as Cli
import ../daemon/spec.bend as Daemon
import ../json/spec.bend as J
import ../shared/bools.bend as Bools
import ../shared/bytes.bend as Octets
import ../views/text/spec.bend as Text

# The MCP front: the everyday commands as tools for agents, over the Model
# Context Protocol on standard input and output (JSON-RPC 2.0, one message
# per line; https://modelcontextprotocol.io/specification/2026-07-28). Like
# the CLI it holds no behavior of its own: each tool call becomes the
# daemon request the CLI sends for the same words.
#
# It serves both eras of the protocol. A request whose params carry
# _meta["io.modelcontextprotocol/protocolVersion"] is modern (2026-07-28):
# served on its own, its agent named by
# _meta["io.modelcontextprotocol/clientInfo"].name. Any other request is
# legacy (2025-11-25 and earlier): an initialize request picks the version
# and names the agent (params.clientInfo.name) for the rest of the
# process. With no client name, the agent is the one VEND_AGENT names, or
# "unnamed". The name only labels the versions an agent writes: the
# protocol does not verify it, and vend makes no decision on it.

# Versions
# --------

# the modern protocol version that this front serves
def Mcp.modern() -> String:
  "2026-07-28"

# the legacy protocol versions that this front serves, newest first
def Mcp.legacy() -> List<&2, String>:
  ["2025-11-25", "2025-06-18", "2025-03-26", "2024-11-05"]

# every protocol version that this front serves
def Mcp.versions() -> List<&2, String>:
  Mcp.modern() <> Mcp.legacy()

# Tools
# -----

# A part of a tool call. AWord: a fixed word of the command. APos: the
# argument key as one word; AOpt: the flag, then the argument key. When an
# argument that need marks is missing, the call is refused. AText and
# ABase64: the bytes that a write writes, as text (UTF-8) or as base64 (RFC
# 4648) for bytes that are not text; at most one of them.
type Arg is Data:
  AWord{w: String}
  APos{key: String, about: String, need: Bool}
  AOpt{key: String, flag: String, about: String, need: Bool}
  AText{key: String, about: String}
  ABase64{key: String, about: String}

# What a tool does: ask the daemon one everyday command, spelled by args,
# or ask its status.
type Does is Data:
  Says{args: List<&2, Arg>}
  Tells{}

# A tool: its name, what it is for, and what it does.
type McpTool is Data:
  McpTool{name: String, about: String, does: Does}

# the argument about a name, <space>:<path>
def Arg.name() -> Arg:
  APos{"name", "the resource, as <space>:<path>", True{}}

# the argument about a line
def Arg.line(need: Bool) -> Arg:
  AOpt{"line", "--line", "the line (default main)", need}

# every tool. Mount, unmount and stopping the daemon are the user's: no
# tool does them.
def Mcp.tools() -> List<&2, McpTool>:
  [
    McpTool{"vend_status", "The mounts the daemon versions, and its clients.", Tells{}},
    McpTool{
      "vend_lines",
      "Every line, and how far each moved since it forked.",
      Says{[AWord{"lines"}]}
    },
    McpTool{
      "vend_log",
      "The versions of a resource, newest first.",
      Says{
        [
          AWord{"log"},
          Arg.name(),
          Arg.line(False{}),
          AOpt{"author", "--author", "only the versions this agent wrote", False{}}
        ]
      }
    },
    McpTool{
      "vend_show",
      "The content of a version of a resource.",
      Says{
        [
          AWord{"show"},
          Arg.name(),
          APos{"version", "a node id prefix or a line (default: the head of main)", False{}}
        ]
      }
    },
    McpTool{
      "vend_diff",
      "Two versions of a resource compared through its view: by item for Bend, by line for text.",
      Says{
        [
          AWord{"diff"},
          Arg.name(),
          APos{"a", "a node id prefix or a line", True{}},
          APos{"b", "a node id prefix or a line", True{}}
        ]
      }
    },
    McpTool{
      "vend_affects",
      "What changed on a line since you last asked, and which of your resources it affects; then marks it seen.",
      Says{[AWord{"affects"}, APos{"line", "the line", True{}}]}
    },
    McpTool{
      "vend_impact",
      "The changes of a line (or line@mark) since its fork, classified, and every item they reach.",
      Says{[AWord{"impact"}, APos{"target", "a line, or line@mark", True{}}]}
    },
    McpTool{
      "vend_line_new",
      "A new line, forked from a line or a mark.",
      Says{
        [
          AWord{"line"},
          AWord{"new"},
          APos{"name", "the new line", True{}},
          AOpt{"from", "--from", "a line, or line@mark (default main)", False{}}
        ]
      }
    },
    McpTool{
      "vend_write",
      "A new version of a resource, signed with your client name. Refused when expect is not the line's heads now.",
      Says{
        [
          AWord{"write"},
          Arg.name(),
          AOpt{
            "expect",
            "--expect",
            "the heads you saw: node id prefixes joined by ',', or none",
            True{}
          },
          Arg.line(False{}),
          AOpt{
            "from",
            "--from",
            "a resource URI whose bytes to write, instead of text or base64",
            False{}
          },
          AText{"text", "the new content, as text"},
          ABase64{"base64", "the new content, as base64, for bytes that are not text"}
        ]
      }
    },
    McpTool{
      "vend_restore",
      "A new version of a resource with the content of an old one.",
      Says{
        [
          AWord{"restore"},
          Arg.name(),
          APos{"version", "a node id prefix or a line", True{}},
          Arg.line(False{})
        ]
      }
    },
    McpTool{
      "vend_mark",
      "A named mark of a line as it is now.",
      Says{
        [
          AWord{"mark"},
          APos{"line", "the line", True{}},
          APos{"name", "the mark", True{}},
          AOpt{"message", "-m", "what the mark is for", False{}}
        ]
      }
    },
    McpTool{
      "vend_merge",
      "A merge of a line (or line@mark) into another, by item: every resource, or none when one clashes.",
      Says{
        [
          AWord{"merge"},
          APos{"from", "a line, or line@mark", True{}},
          AWord{"into"},
          APos{"into", "the line to merge into", True{}}
        ]
      }
    },
    McpTool{
      "vend_checkout",
      "Your own working copy of a line: a folder inside the user's mount (.vend-checkouts/<you>/<line>/) that holds the line's files. What you save there is recorded on that line, signed with your client name. Answers with the folder's path.",
      Says{[AWord{"checkout"}, APos{"line", "the line", True{}}]}
    },
    McpTool{
      "vend_release",
      "Your working copy of a line removed: the folder is deleted, the line and its versions stay.",
      Says{[AWord{"release"}, APos{"line", "the line", True{}}]}
    },
    McpTool{
      "vend_open",
      "What each resource of a line still owes, as its view says (for Bend: laws no def fills, and ?holes in proofs), by resource.",
      Says{[AWord{"open"}, APos{"line", "the line", True{}}]}
    },
    McpTool{
      "vend_verify",
      "Each resource of a line checked by its view's verifier (for Bend: bend --check-only), in your checkout of the line, else in the user's mount that shows it.",
      Says{[AWord{"verify"}, APos{"line", "the line", True{}}]}
    }
  ]

# the tool named n
def Mcp.tool(ts: List<&2, McpTool>, +n: String) -> Maybe<&2, McpTool>:
  match ts:
    case Nil{}:
      None{}
    case Con{McpTool{+x, ab, d}, t}:
      Bools.Bool.when(
        Maybe<&2, McpTool>,
        String.eq(x, n),
        u => Some{McpTool{x, ab, d}},
        u => Mcp.tool(t, n)
      )

# Calls
# -----

# ws before the words r
def Mcp.then(
  ws: List<&2, String>,
  r: Result<&2, &2, String, List<&2, String>>
) -> Result<&2, &2, String, List<&2, String>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{xs}:
      Done{List.append(&2, String, ws, xs)}

# the words of the argument k with value m, before the words r: f of its
# text; none when it is missing and not needed
def Mcp.got(
  k: String,
  m: Maybe<&2, J.Json>,
  need: Bool,
  f: String -> List<&2, String>,
  r: Result<&2, &2, String, List<&2, String>>
) -> Result<&2, &2, String, List<&2, String>>:
  match m need:
    case Some{J.JStr{s}} _:
      Mcp.then(f(s), r)
    case Some{x} _:
      Fail{String.concat(["argument ", k, " must be a string"])}
    case None{} True{}:
      Fail{String.append("missing argument ", k)}
    case None{} False{}:
      r

# the words of the args, given the arguments object, or why they are wrong
def Mcp.words(args: List<&2, Arg>, +v: J.Json) -> Result<&2, &2, String, List<&2, String>>:
  match args:
    case Nil{}:
      Done{[]}
    case Con{AWord{w}, t}:
      Mcp.then([w], Mcp.words(t, v))
    case Con{APos{+k, ab, need}, t}:
      Mcp.got(k, J.Json.get(v, k), need, x => [x], Mcp.words(t, v))
    case Con{AOpt{+k, fl, ab, need}, t}:
      Mcp.got(k, J.Json.get(v, k), need, x => [fl, x], Mcp.words(t, v))
    case Con{AText{k, ab}, t}:
      Mcp.words(t, v)
    case Con{ABase64{k, ab}, t}:
      Mcp.words(t, v)

# The value of each base64 character (RFC 4648, section 4).
def B64.value(+c: Char) -> Maybe<&2, U32>:
  +x = Char.to_u32(c)
  Bools.Bool.when(
    Maybe<&2, U32>,
    Bool.and((x >= 65: U32), (x <= 90: U32)),
    u => Some{(x - 65: U32)},
    u => Bools.Bool.when(
      Maybe<&2, U32>,
      Bool.and((x >= 97: U32), (x <= 122: U32)),
      v => Some{(x - 71: U32)},
      v => Bools.Bool.when(
        Maybe<&2, U32>,
        Char.is_digit(c),
        w => Some{(x + 4: U32)},
        w => Bools.Bool.when(
          Maybe<&2, U32>,
          U32.is_eq(x, 43),
          y => Some{62},
          y => Bool.pick(Maybe<&2, U32>, U32.is_eq(x, 47), Some{63}, None{})
        )
      )
    )
  )

# the three bytes of one group of four values a, b, c, d (each below 64)
def B64.group(a: U32, b: U32, c: U32, d: U32) -> Octets.Bytes():
  +w = ((((a << 18n) .|. (b << 12n)) .|. ((c << 6n) .|. d)): U32)
  [((w >> 16n) .&. 255: U32), ((w >> 8n) .&. 255: U32), (w .&. 255: U32)]

# the rest after a first '=' is at most one more '='
def B64.pad(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, SNil{}}:
      U32.is_eq(Char.to_u32(c), 61)
    case _:
      False{}

# v before the values r
def B64.cons(m: Maybe<&2, U32>, r: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match m r:
    case Some{v} Some{xs}:
      Some{v <> xs}
    case _ _:
      None{}

# the value of each character of s, or None when one is no base64
# character; '=' only ends the text
def B64.values(s: String) -> Maybe<&2, List<&2, U32>>:
  match s:
    case SNil{}:
      Some{[]}
    case SCon{+c, +t}:
      Bools.Bool.when(
        Maybe<&2, List<&2, U32>>,
        U32.is_eq(Char.to_u32(c), 61),
        u => Bool.pick(Maybe<&2, List<&2, U32>>, B64.pad(t), Some{[]}, None{}),
        u => B64.cons(B64.value(c), B64.values(t))
      )

# the bytes of the base64 values vs, four at a time; a last group of two or
# three values gives one or two bytes, and a last group of one is wrong
def B64.bytes(vs: List<&2, U32>) -> Maybe<&2, Octets.Bytes()>:
  match vs:
    case Nil{}:
      Some{[]}
    case Con{a, Con{b, Con{c, Con{d, t}}}}:
      Maybe.map(
        &2,
        Octets.Bytes(),
        Octets.Bytes(),
        r => List.append(&2, U32, B64.group(a, b, c, d), r),
        B64.bytes(t)
      )
    case Con{+a, Con{+b, Con{+c, Nil{}}}}:
      Some{List.take(&2, U32, B64.group(a, b, c, 0), 2n)}
    case Con{+a, Con{+b, Nil{}}}:
      Some{List.take(&2, U32, B64.group(a, b, 0, 0), 1n)}
    case _:
      None{}

# the bytes of the values, when every character was base64
def B64.decode.of(m: Maybe<&2, List<&2, U32>>) -> Maybe<&2, Octets.Bytes()>:
  match m:
    case None{}:
      None{}
    case Some{vs}:
      B64.bytes(vs)

# the bytes that the base64 text s spells (RFC 4648, section 4; the '='
# padding is optional), or None when s is no base64
def B64.decode(s: String) -> Maybe<&2, Octets.Bytes()>:
  B64.decode.of(B64.values(s))

# the bytes a call writes, given here (from one argument) and rest (from
# the others): at most one argument gives them
def Mcp.data.both(
  here: Result<&2, &2, String, Maybe<&2, Octets.Bytes()>>,
  rest: Result<&2, &2, String, Maybe<&2, Octets.Bytes()>>
) -> Result<&2, &2, String, Maybe<&2, Octets.Bytes()>>:
  match here rest:
    case Fail{e} _:
      Fail{e}
    case _ Fail{e}:
      Fail{e}
    case Done{Some{a}} Done{Some{b}}:
      Fail{"give text or base64, not both"}
    case Done{None{}} r:
      r
    case Done{Some{a}} Done{None{}}:
      Done{Some{a}}

# the bytes of the argument k with value m: f of its text, None when it is
# missing
def Mcp.data.of(
  k: String,
  m: Maybe<&2, J.Json>,
  f: String -> Result<&2, &2, String, Maybe<&2, Octets.Bytes()>>
) -> Result<&2, &2, String, Maybe<&2, Octets.Bytes()>>:
  match m:
    case None{}:
      Done{None{}}
    case Some{J.JStr{s}}:
      f(s)
    case Some{x}:
      Fail{String.concat(["argument ", k, " must be a string"])}

# the bytes of a base64 text, or why it is not base64
def Mcp.base64(m: Maybe<&2, Octets.Bytes()>) -> Result<&2, &2, String, Maybe<&2, Octets.Bytes()>>:
  match m:
    case None{}:
      Fail{"argument base64 is not base64"}
    case Some{b}:
      Done{Some{b}}

# the bytes that the args of a call write, given the arguments object: the
# text as UTF-8, or the base64 decoded; None when neither is given
def Mcp.data(args: List<&2, Arg>, +v: J.Json) -> Result<&2, &2, String, Maybe<&2, Octets.Bytes()>>:
  match args:
    case Nil{}:
      Done{None{}}
    case Con{AText{+k, ab}, t}:
      here = Mcp.data.of(k, J.Json.get(v, k), s => Done{Some{Text.Text.encode(s)}})
      Mcp.data.both(here, Mcp.data(t, v))
    case Con{ABase64{+k, ab}, t}:
      here = Mcp.data.of(k, J.Json.get(v, k), s => Mcp.base64(B64.decode(s)))
      Mcp.data.both(here, Mcp.data(t, v))
    case Con{a, t}:
      Mcp.data(t, v)

# the request of words ws and data m, signed by agent a
def Mcp.ask(
  a: String,
  ws: Result<&2, &2, String, List<&2, String>>,
  m: Result<&2, &2, String, Maybe<&2, Octets.Bytes()>>
) -> Result<&2, &2, String, Daemon.Body>:
  match ws m:
    case Fail{e} _:
      Fail{e}
    case _ Fail{e}:
      Fail{e}
    case Done{xs} Done{d}:
      Done{Daemon.Ask{a, xs, Maybe.default(&2, Octets.Bytes(), d, [])}}

# the daemon request of a call of the tool t with the arguments object v,
# signed by the agent a; or why the arguments are wrong
def Mcp.body(a: String, t: McpTool, v: J.Json) -> Result<&2, &2, String, Daemon.Body>:
  match t:
    case McpTool{n, ab, Tells{}}:
      Done{Daemon.Status{}}
    case McpTool{n, ab, Says{+args}}:
      +v = v
      Mcp.ask(a, Mcp.words(args, v), Mcp.data(args, v))

# b is a request that an agent may make: a status, or an everyday command;
# never a mount, an unmount, or a stop
def Mcp.agents(b: Daemon.Body) -> Bool:
  match b:
    case Daemon.Status{}:
      True{}
    case Daemon.Ask{a, ws, d}:
      True{}
    case _:
      False{}

# Messages
# --------

# The era of a request: legacy (the version an initialize picked) or
# modern (the version in its _meta).
type Era is Data:
  Legacy{}
  Modern{}

# What the front keeps between messages: the agent when no client names
# one, and the agent that a legacy initialize named.
type McpState is Data:
  McpState{fallback: String, agent: Maybe<&2, String>}

# What a message asks of the loop: nothing (a notification), an answer
# now, or the daemon request whose answer becomes the tool result for the
# request id.
type Out is Data:
  Quiet{}
  Answer{msg: J.Json}
  Forward{id: J.Json, era: Era, body: Daemon.Body}

# The state after a message, and what it asks of the loop.
type McpStep is Data:
  McpStep{state: McpState, out: Out}

# this front, as MCP names an implementation
def Mcp.server() -> J.Json:
  J.Json.obj([J.Field{"name", J.JStr{"vend"}}, J.Field{"version", J.JStr{"0.1.0"}}])

# what this front can do: tools
def Mcp.capabilities() -> J.Json:
  J.Json.obj([J.Field{"tools", J.Json.obj([])}])

# how an agent uses vend
def Mcp.instructions() -> String:
  String.concat(
    [
      "vend versions every save live, by item for Bend and C. Names are <space>:<path>; a version is a node ",
      "id prefix or a line. Write with the heads you last saw (expect); a stale write is refused with the ",
      "heads now. Your writes are signed with your client name. To edit files with your own tools, take a ",
      "checkout of your line (vend_checkout) and edit there; release it when done. Mounting, unmounting and stopping vend are ",
      "the user's: when a tool says vend is not running, ask the user to run `vend start-or-resume`."
    ]
  )

# the members a modern result adds
def Mcp.modern.extra(e: Era) -> List<&2, J.Field>:
  match e:
    case Legacy{}:
      []
    case Modern{}:
      [
        J.Field{"resultType", J.JStr{"complete"}},
        J.Field{"_meta", J.Json.obj([J.Field{"io.modelcontextprotocol/serverInfo", Mcp.server()}])}
      ]

# the answer to the request id with the members fs of its result; a modern
# result also says it is complete and names the server
def Mcp.reply(id: J.Json, e: Era, fs: List<&2, J.Field>) -> J.Json:
  more = Mcp.modern.extra(e)
  J.Json.obj(
    [
      J.Field{"jsonrpc", J.JStr{"2.0"}},
      J.Field{"id", id},
      J.Field{"result", J.Json.obj(List.append(&2, J.Field, fs, more))}
    ]
  )

# the error answer to the request id (JNull when it is not known), with
# its code, message and data
def Mcp.error(id: J.Json, code: String, message: String, data: List<&2, J.Field>) -> J.Json:
  J.Json.obj(
    [
      J.Field{"jsonrpc", J.JStr{"2.0"}},
      J.Field{"id", id},
      J.Field{
        "error",
        J.Json.obj(J.Field{"code", J.JNum{code}} <> J.Field{"message", J.JStr{message}} <> data)
      }
    ]
  )

# the result of a tool call: its text, and whether it is an error
def Mcp.result(id: J.Json, e: Era, ok: Bool, text: String) -> J.Json:
  content = J.Json.arr(
    [J.Json.obj([J.Field{"type", J.JStr{"text"}}, J.Field{"text", J.JStr{text}}])]
  )
  Mcp.reply(id, e, [J.Field{"content", content}, J.Field{"isError", J.JBool{Bool.not(ok)}}])

# the schema of a string argument about ab
def Arg.string(ab: String) -> J.Json:
  J.Json.obj([J.Field{"type", J.JStr{"string"}}, J.Field{"description", J.JStr{ab}}])

# the JSON Schema of one argument, when it is one
def Arg.schema(a: Arg) -> List<&2, J.Field>:
  match a:
    case AWord{w}:
      []
    case APos{k, ab, n}:
      [J.Field{k, Arg.string(ab)}]
    case AOpt{k, fl, ab, n}:
      [J.Field{k, Arg.string(ab)}]
    case AText{k, ab}:
      [J.Field{k, Arg.string(ab)}]
    case ABase64{k, ab}:
      [J.Field{k, Arg.string(ab)}]

# the keys of the arguments that need a value
def Arg.needed(args: List<&2, Arg>) -> List<&2, J.Json>:
  match args:
    case Nil{}:
      Nil{}
    case Con{APos{k, ab, True{}}, t}:
      J.JStr{k} <> Arg.needed(t)
    case Con{AOpt{k, fl, ab, True{}}, t}:
      J.JStr{k} <> Arg.needed(t)
    case Con{a, t}:
      Arg.needed(t)

# the properties of the arguments
def Arg.properties(args: List<&2, Arg>) -> List<&2, J.Field>:
  match args:
    case Nil{}:
      Nil{}
    case Con{a, t}:
      List.append(&2, J.Field, Arg.schema(a), Arg.properties(t))

# the input schema of what a tool does
def Does.schema(d: Does) -> J.Json:
  match d:
    case Tells{}:
      J.Json.obj([J.Field{"type", J.JStr{"object"}}])
    case Says{+args}:
      J.Json.obj(
        [
          J.Field{"type", J.JStr{"object"}},
          J.Field{"properties", J.Json.obj(Arg.properties(args))},
          J.Field{"required", J.Json.arr(Arg.needed(args))}
        ]
      )

# a tool as tools/list lists it
def McpTool.json(t: McpTool) -> J.Json:
  match t:
    case McpTool{n, ab, d}:
      J.Json.obj(
        [
          J.Field{"name", J.JStr{n}},
          J.Field{"description", J.JStr{ab}},
          J.Field{"inputSchema", Does.schema(d)}
        ]
      )

# every tool as tools/list lists them
def McpTool.all(ts: List<&2, McpTool>) -> List<&2, J.Json>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{t, r}:
      McpTool.json(t) <> McpTool.all(r)

# the versions as JSON strings
def Mcp.version.list(vs: List<&2, String>) -> List<&2, J.Json>:
  match vs:
    case Nil{}:
      Nil{}
    case Con{v, t}:
      J.JStr{v} <> Mcp.version.list(t)

# the answer to a call whose request is r: the request to forward, or the
# tool error that says why its arguments are wrong
def Mcp.call.body(id: J.Json, e: Era, r: Result<&2, &2, String, Daemon.Body>) -> Out:
  match r:
    case Fail{why}:
      Answer{Mcp.result(id, e, False{}, why)}
    case Done{b}:
      Forward{id, e, b}

# the answer to a call of the tool t (named x), if there is one
def Mcp.call.tool(
  id: J.Json,
  e: Era,
  a: String,
  x: String,
  t: Maybe<&2, McpTool>,
  v: J.Json
) -> Out:
  match t:
    case None{}:
      Answer{Mcp.error(id, "-32602", String.append("no such tool: ", x), [])}
    case Some{tool}:
      Mcp.call.body(id, e, Mcp.body(a, tool, v))

# the answer to tools/call: the request of the tool named n, or why it
# cannot be made
def Mcp.call(id: J.Json, e: Era, a: String, n: Maybe<&2, String>, v: J.Json) -> Out:
  match n:
    case None{}:
      Answer{Mcp.error(id, "-32602", "tools/call needs the name of a tool", [])}
    case Some{+x}:
      Mcp.call.tool(id, e, a, x, Mcp.tool(Mcp.tools(), x), v)

# the answer to the request id with method m and params p, in era e, from
# agent a
def Mcp.serve(+id: J.Json, +e: Era, a: String, +m: String, +p: J.Json) -> Out:
  Bools.Bool.when(
    Out,
    String.eq(m, "tools/call"),
    u => Mcp.call(
      id,
      e,
      a,
      J.Json.text(J.Json.get(p, "name")),
      Maybe.default(&2, J.Json, J.Json.get(p, "arguments"), J.Json.obj([]))
    ),
    u => Bools.Bool.when(
      Out,
      String.eq(m, "tools/list"),
      v => Answer{Mcp.reply(id, e, [J.Field{"tools", J.Json.arr(McpTool.all(Mcp.tools()))}])},
      v => Bools.Bool.when(
        Out,
        String.eq(m, "ping"),
        w => Answer{Mcp.reply(id, e, [])},
        w => Bools.Bool.when(
          Out,
          String.eq(m, "server/discover"),
          x => Answer{
            Mcp.reply(
              id,
              e,
              [
                J.Field{"supportedVersions", J.Json.arr(Mcp.version.list(Mcp.versions()))},
                J.Field{"capabilities", Mcp.capabilities()},
                J.Field{"instructions", J.JStr{Mcp.instructions()}}
              ]
            )
          },
          x => Answer{Mcp.error(id, "-32601", String.append("no such method: ", m), [])}
        )
      )
    )
  )

# the version a legacy initialize gets: the one it asks for when this front
# serves it, else the newest legacy one
def Mcp.legacy.pick(+asked: Maybe<&2, String>) -> String:
  match asked:
    case Some{+v}:
      Bool.pick(String, List.contains(~String, ~String.eq, Mcp.legacy(), v), v, "2025-11-25")
    case None{}:
      "2025-11-25"

# the answer to a legacy initialize, and the agent its client names
def Mcp.initialize(s: McpState, id: J.Json, +p: J.Json) -> McpStep:
  match s:
    case McpState{fb, ag}:
      name = J.Json.text(
        J.Json.get(Maybe.default(&2, J.Json, J.Json.get(p, "clientInfo"), J.JNull{}), "name")
      )
      result = {
        [
          J.Field{
            "protocolVersion",
            J.JStr{Mcp.legacy.pick(J.Json.text(J.Json.get(p, "protocolVersion")))}
          },
          J.Field{"capabilities", Mcp.capabilities()},
          J.Field{"serverInfo", Mcp.server()},
          J.Field{"instructions", J.JStr{Mcp.instructions()}}
        ]: List<&2, J.Field>
      }
      McpStep{McpState{fb, Maybe.or(&2, String, name, ag)}, Answer{Mcp.reply(id, Legacy{}, result)}}

# the agent of a legacy request: the one initialize named, else the fallback
def McpState.agent(s: McpState) -> String:
  match s:
    case McpState{fb, ag}:
      Maybe.default(&2, String, ag, fb)

# the fallback agent of the state
def McpState.fallback(s: McpState) -> String:
  match s:
    case McpState{fb, ag}:
      fb

# the answer to a legacy request
def Mcp.legacy.serve(+s: McpState, +id: J.Json, +m: String, +p: J.Json) -> McpStep:
  Bools.Bool.when(
    McpStep,
    String.eq(m, "initialize"),
    u => Mcp.initialize(s, id, p),
    u => McpStep{s, Mcp.serve(id, Legacy{}, McpState.agent(s), m, p)}
  )

# the answer to a modern request with _meta meta, asking for the version
# ver: refused when this front does not serve ver or the request lacks the
# client capabilities
def Mcp.modern.serve(
  +s: McpState,
  +id: J.Json,
  m: String,
  p: J.Json,
  +meta: J.Json,
  +ver: String
) -> McpStep:
  info = Maybe.default(
    &2,
    J.Json,
    J.Json.get(meta, "io.modelcontextprotocol/clientInfo"),
    J.JNull{}
  )
  agent = Maybe.default(&2, String, J.Json.text(J.Json.get(info, "name")), McpState.fallback(s))
  caps = Maybe.is_some(&2, J.Json, J.Json.get(meta, "io.modelcontextprotocol/clientCapabilities"))
  supported = J.Json.obj(
    [
      J.Field{"supported", J.Json.arr(Mcp.version.list(Mcp.versions()))},
      J.Field{"requested", J.JStr{ver}}
    ]
  )
  Bools.Bool.when(
    McpStep,
    String.eq(ver, Mcp.modern()),
    u => Bools.Bool.when(
      McpStep,
      caps,
      v => McpStep{s, Mcp.serve(id, Modern{}, agent, m, p)},
      v => McpStep{
        s,
        Answer{
          Mcp.error(id, "-32602", "_meta lacks io.modelcontextprotocol/clientCapabilities", [])
        }
      }
    ),
    u => McpStep{
      s,
      Answer{Mcp.error(id, "-32022", "Unsupported protocol version", [J.Field{"data", supported}])}
    }
  )

# the answer to a request whose _meta is meta and names the version v, if
# it names one
def Mcp.request.era(
  s: McpState,
  id: J.Json,
  m: String,
  p: J.Json,
  meta: J.Json,
  v: Maybe<&2, String>
) -> McpStep:
  match v:
    case None{}:
      Mcp.legacy.serve(s, id, m, p)
    case Some{ver}:
      Mcp.modern.serve(s, id, m, p, meta, ver)

# the answer to the request id with method m and params p: modern when its
# _meta names a protocol version, else legacy
def Mcp.request(s: McpState, id: J.Json, m: String, +p: J.Json) -> McpStep:
  +meta = Maybe.default(&2, J.Json, J.Json.get(p, "_meta"), J.JNull{})
  Mcp.request.era(
    s,
    id,
    m,
    p,
    meta,
    J.Json.text(J.Json.get(meta, "io.modelcontextprotocol/protocolVersion"))
  )

# the step of a message with method m, id i and params p
def Mcp.message.of(s: McpState, m: Maybe<&2, String>, i: Maybe<&2, J.Json>, p: J.Json) -> McpStep:
  match m i:
    case Some{meth} Some{id}:
      Mcp.request(s, id, meth, p)
    case Some{meth} None{}:
      McpStep{s, Quiet{}}
    case None{} Some{id}:
      McpStep{s, Answer{Mcp.error(id, "-32600", "Invalid Request", [])}}
    case None{} None{}:
      McpStep{s, Answer{Mcp.error(J.JNull{}, "-32600", "Invalid Request", [])}}

# the step of the message v: a request (with a method and an id) is
# answered; a notification (with no id) is not; anything else is an
# invalid request
def Mcp.message(s: McpState, +v: J.Json) -> McpStep:
  Mcp.message.of(
    s,
    J.Json.text(J.Json.get(v, "method")),
    J.Json.get(v, "id"),
    Maybe.default(&2, J.Json, J.Json.get(v, "params"), J.JNull{})
  )

# the step of one line of input: its JSON value, or None when it is not
# JSON (a parse error)
def Mcp.step(s: McpState, m: Maybe<&2, J.Json>) -> McpStep:
  match m:
    case None{}:
      McpStep{s, Answer{Mcp.error(J.JNull{}, "-32700", "Parse error", [])}}
    case Some{v}:
      Mcp.message(s, v)

# Laws
# ----

# a call of a listed tool sends what the CLI sends for the same words: a
# status, or the Ask of words that the CLI reads as that everyday command
# as they are, signed by the agent
law body_is_cli:
  for a: String
  for n: String
  for t: McpTool
  for v: J.Json
  for x: String
  for ws: List<&2, String>
  for d: Octets.Bytes()
  for k: {Mcp.tool(Mcp.tools(), n) == Some{t}: Maybe<&2, McpTool>}
  for h: {Mcp.body(a, t, v) == Done{Daemon.Ask{x, ws, d}}: Result<&2, &2, String, Daemon.Body>}
  {x == a: String} & {Cli.Cli.parse(ws) == Done{Cli.AskCmd{ws}}: Result<&2, &2, String, Cli.Cmd>}

# an agent can never mount, unmount or stop: every request the front
# forwards is a status or an everyday command
law forwards_agents_only:
  for s: McpState
  for m: Maybe<&2, J.Json>
  for s2: McpState
  for id: J.Json
  for e: Era
  for b: Daemon.Body
  for h: {Mcp.step(s, m) == McpStep{s2, Forward{id, e, b}}: McpStep}
  {Mcp.agents(b) == True{}: Bool}
