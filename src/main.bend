import Base
import ./shared/disk.bend as Disk
import ./shared/shared/ledger.bend as Ledgers
import ./shared/shared/shared/shared/code.bend as Codes
import ./shared/shared/shared/shared/crit.bend as Crits
import ./shared/shared/shared/shared/hash.bend as Hashes
import ./shared/shared/shared/shared/shared.bend as Shared
import ./shared/shared/shared/text.bend as Texts
import ./vend_node/codes.bend as Coded
import ./vend_node/impl.bend as Impl
import ./vend_node/node.bend as Nodes
import ./vend_node/run/facts.bend as Facts
import ./vend_node/run/fast.bend as Fasts
import ./vend_node/run/known.bend as Known
import ./vend_node/run/parts.bend as Parts
import ./vend_node/run/work.bend as Works
import ./vend_node/spec.bend as Spec
import ./vend_node/types.bend as Types

# vend
# ----
# The program: a thin shell around the core. A command resumes the node of a
# data address, connects its writer, does its deeds, works until a work adds
# no fact, keeps the new facts and parts, leaves, and prints the reply. Every
# decision is the core's (Fasts.Fast.does and its observers); the shell only
# reads and writes the state of the node, which is its facts and its parts.
#
# A data address is a directory:
#   name          the name of the node, as UTF-8
#   facts         the facts, each written once, as the codes of
#                 Coded.Fact.code back to back, each word as 4 bytes
#   parts/<hash>  the words of a part, each as 4 bytes, under the SHA-256 of
#                 its words in hex
#   lock          there while a node runs on the address

# Hex
# ---

# the hex digit of d, below 16
def Hex.digit(+d: U32) -> Char:
  Chr{(d + 48 + Bool.to_u32((d > 9: U32)) * 39: U32)}

# the n lowest hex digits of w, then acc
def Hex.word(n: Nat, +w: U32, acc: String) -> String:
  match n:
    case 0n:
      acc
    case 1n+p:
      Hex.word(p, (w / 16: U32), SCon{Hex.digit((w % 16: U32)), acc})

# the words ws in hex, eight digits each
def Hex.words(ws: List<&2, U32>) -> String:
  match ws:
    case Nil{}:
      ""
    case Con{w, rest}:
      Hex.word(8n, w, "") ++ Hex.words(rest)

# the value of the hex digit c; 16 when c is not one
def Hex.value(c: Char) -> U32:
  +x = Char.to_u32(c)
  Bool.pick(
    U32,
    Bool.and((x >= 48: U32), (x <= 57: U32)),
    (x - 48: U32),
    Bool.pick(U32, Bool.and((x >= 97: U32), (x <= 102: U32)), (x - 87: U32), 16)
  )

# the values of the hex digits of s
def Hex.values(s: String) -> List<&2, U32>:
  match s:
    case SNil{}:
      []
    case SCon{c, rest}:
      Hex.value(c) <> Hex.values(rest)

# the words of the hex digits ns, eight to a word, after the words acc in
# reverse order; none when the digits do not end at a whole word
def Hex.join(ns: List<&2, U32>, acc: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match ns:
    case Nil{}:
      Some{List.reverse(&2, U32, acc)}
    case Con{a, Con{b, Con{c, Con{d, Con{e, Con{f, Con{g, Con{h, rest}}}}}}}}:
      hi = (((a * 16 + b: U32) * 16 + c: U32) * 16 + d: U32)
      lo = (((e * 16 + f: U32) * 16 + g: U32) * 16 + h: U32)
      Hex.join(rest, (hi * 65536 + lo: U32) <> acc)
    case _:
      None{}

# the hash of the eight words m, if m holds eight
def Hash.of_words(m: Maybe<&2, List<&2, U32>>) -> Maybe<&2, Hashes.Hash>:
  match m:
    case Some{Con{a, Con{b, Con{c, Con{d, Con{e, Con{f, Con{g, Con{h, Nil{}}}}}}}}}}:
      Some{Hashes.Hash{a, b, c, d, e, f, g, h}}
    case _:
      None{}

# the hash whose hex digits are ns, if each is one (ok)
def Hash.read.if(ok: Bool, ns: List<&2, U32>) -> Maybe<&2, Hashes.Hash>:
  match ok:
    case True{}:
      Hash.of_words(Hex.join(ns, []))
    case False{}:
      None{}

# the hash of the 64 hex digits s
def Hash.read(s: String) -> Maybe<&2, Hashes.Hash>:
  +ns = Hex.values(s)
  Hash.read.if(List.all(~&2, ~U32, ~(n => (n < 16: U32)), ns), ns)

# the hash h in hex
def Hash.show(h: Hashes.Hash) -> String:
  Hex.words(Hashes.Hash.code(h, []))

# Names
# -----
# A line is the hash of its store, then ':' and the name of a branch. An id is
# a writer, '/' and the id that the writer gave the request; without '/', the
# writer is the one connected.

# the line of the store h whose branch is named by the parts bs
def Line.of(h: Hashes.Hash, bs: List<&2, String>) -> Ledgers.Line:
  match bs:
    case Nil{}:
      Ledgers.Line{h, None{}}
    case Con{b, rest}:
      Ledgers.Line{h, Some{String.join(b <> rest, ":")}}

# the line that the parts ps of a text name: a store, then a branch
def Line.of_parts(ps: List<&2, String>) -> Maybe<&2, Ledgers.Line>:
  match ps:
    case Con{h, bs}:
      Maybe.bind(&2, Hashes.Hash, Ledgers.Line, Hash.read(h), x => Some{Line.of(x, bs)})
    case Nil{}:
      None{}

# the line that s names
def Line.read(s: String) -> Maybe<&2, Ledgers.Line>:
  Line.of_parts(String.split(s, ':'))

# the line c as text
def Line.show(c: Ledgers.Line) -> String:
  match c:
    case Ledgers.Line{h, None{}}:
      Hash.show(h)
    case Ledgers.Line{h, Some{b}}:
      Hash.show(h) ++ ":" ++ b

# the id that the parts ps of a text name, where w is the writer connected
def Id.of(w: String, ps: List<&2, String>) -> Ledgers.Id:
  match ps:
    case Con{r, Nil{}}:
      Ledgers.Id{w, r}
    case Con{a, Con{r, rest}}:
      Ledgers.Id{a, String.join(r <> rest, "/")}
    case Nil{}:
      Ledgers.Id{w, ""}

# the id that s names, where w is the writer connected
def Id.read(w: String, s: String) -> Ledgers.Id:
  Id.of(w, String.split(s, '/'))

# the id i as text
def Id.show(i: Ledgers.Id) -> String:
  match i:
    case Ledgers.Id{w, r}:
      w ++ "/" ++ r

# the names that s lists, split at ','; '-' lists none
def Names.read(s: String) -> List<&2, String>:
  match s:
    case "-":
      []
    case _:
      String.split(s, ',')

# the names ns as text
def Names.show(ns: List<&2, String>) -> String:
  match ns:
    case Nil{}:
      "(none)"
    case Con{n, rest}:
      String.join(n <> rest, ", ")

# the version x as text
def Point.show(x: Spec.Point) -> String:
  match x:
    case Spec.Point{c, k}:
      Line.show(c) ++ "@" ++ Nat.show(k)

# the versions xs, each as text
def Points.texts(xs: List<&2, Spec.Point>) -> List<&2, String>:
  match xs:
    case Nil{}:
      []
    case Con{x, rest}:
      Point.show(x) <> Points.texts(rest)

# the versions xs as text
def Points.show(xs: List<&2, Spec.Point>) -> String:
  Names.show(Points.texts(xs))

# Replies
# -------

# the status s as text
def Status.show(s: Spec.Status) -> String:
  match s:
    case Spec.Status.Written{}:
      "written"
    case Spec.Status.Conflicted{i}:
      "conflicted (merge " ++ Id.show(i) ++ ")"
    case Spec.Status.Stale{}:
      "stale"
    case Spec.Status.Refused{}:
      "refused"

# the words m, if any, as text
def Words.show(m: Maybe<&2, List<&2, U32>>) -> String:
  match m:
    case None{}:
      "nothing (deleted)"
    case Some{+ws}:
      Nat.show(List.length(&2, U32, ws)) ++ " bytes"

# the request r as text
def Request.show(r: Spec.Request) -> String:
  match r:
    case Spec.Request.Start{os}:
      "start, owners " ++ Names.show(os)
    case Spec.Request.Write{b, p, w}:
      "write " ++ p ++ " on " ++ Line.show(b) ++ ": " ++ Words.show(w)
    case Spec.Request.Merge{f, x}:
      "merge " ++ Line.show(f) ++ " into " ++ Line.show(x)
    case Spec.Request.Resolve{m, p, w}:
      "resolve " ++ p ++ " of merge " ++ Id.show(m) ++ ": " ++ Words.show(w)
    case Spec.Request.Mark{b, m, k}:
      "mark " ++ m ++ " = " ++ Line.show(b) ++ "@" ++ Nat.show(k)
    case Spec.Request.Move{b, t, k}:
      "move " ++ Line.show(b) ++ " to " ++ Line.show(t) ++ "@" ++ Nat.show(k)
    case Spec.Request.Group{h, g, ms}:
      "group " ++ g ++ " of " ++ Hash.show(h) ++ ": " ++ Names.show(ms)
    case Spec.Request.Own{c, g}:
      "own " ++ Line.show(c) ++ " by " ++ g

# the reply r as text
def Reply.show(r: Spec.Reply) -> String:
  match r:
    case Spec.Reply.Status{s}:
      Status.show(s)
    case Spec.Reply.Ask{q}:
      Request.show(q)
    case Spec.Reply.Id{i}:
      Id.show(i)
    case Spec.Reply.Hash{h}:
      Hash.show(h)
    case Spec.Reply.Names{ns}:
      Names.show(ns)
    case Spec.Reply.Number{n}:
      Nat.show(n)
    case Spec.Reply.Yes{True{}}:
      "yes"
    case Spec.Reply.Yes{False{}}:
      "no"
    case Spec.Reply.Name{g}:
      g
    case Spec.Reply.Point{x}:
      Point.show(x)
    case Spec.Reply.Points{xs}:
      Points.show(xs)

# the reply m to the question q as text: no reply is pending for a status,
# and unknown for any other question
def Answer.show(q: Spec.Question, m: Maybe<&2, Spec.Reply>) -> String:
  match q m:
    case _ Some{r}:
      Reply.show(r)
    case Spec.Question.Status{c, i} None{}:
      "pending"
    case _ None{}:
      "unknown"

# the content m of a resource as text: unknown, none, or its words as UTF-8
def Content.show(m: Maybe<&2, Maybe<&2, List<&2, U32>>>) -> String:
  match m:
    case None{}:
      "unknown"
    case Some{None{}}:
      "(no resource at this path)"
    case Some{Some{ws}}:
      Texts.Bytes.to_text(ws)

# Commands
# --------

# what a command asks of the node, beside connecting its writer
type Cmd is Data:
  Cmd.Ask{id: Ledgers.Id, request: Spec.Request}
  Cmd.Put{id: Ledgers.Id, branch: Ledgers.Line, path: String, file: String}
  Cmd.Fix{id: Ledgers.Id, merge: Ledgers.Id, path: String, file: String}
  Cmd.Answer{question: Spec.Question}
  Cmd.Read{line: Ledgers.Line, n: Nat, path: String}
  Cmd.View{branch: Ledgers.Line, path: String}
  Cmd.Work{}
  Cmd.Sync{from: String}
  Cmd.Drop{}
  Cmd.Stop{force: Bool}
  Cmd.Liars{}
  Cmd.Mount{dir: String, line: Ledgers.Line, path: String}
  Cmd.Unmount{dir: String}

# the question of the kind k about the line c and the id i
def Question.id(k: String, c: Ledgers.Line, i: Ledgers.Id) -> Maybe<&2, Spec.Question>:
  match k:
    case "status":
      Some{Spec.Question.Status{c, i}}
    case "request":
      Some{Spec.Question.Request{c, i}}
    case "clashes":
      Some{Spec.Question.Clashes{c, i}}
    case "base":
      Some{Spec.Question.Base{c, i}}
    case _:
      None{}

# the question of the kind k about version n of the line c
def Question.at(k: String, c: Ledgers.Line, n: Nat) -> Maybe<&2, Spec.Question>:
  match k:
    case "version":
      Some{Spec.Question.Version{c, n}}
    case "content":
      Some{Spec.Question.Content{c, n}}
    case "group":
      Some{Spec.Question.Group{c, n}}
    case "owners":
      Some{Spec.Question.Owners{c, n}}
    case "parents":
      Some{Spec.Question.Parents{c, n}}
    case "owner":
      Some{Spec.Question.Owner{c, n}}
    case "era":
      Some{Spec.Question.Era{c, n}}
    case _:
      None{}

# the question of the kind k about the line c and the word x: an id, a
# mark, or the number of a version
def Question.two(+w: String, k: String, c: Ledgers.Line, +x: String) -> Maybe<&2, Spec.Question>:
  match k:
    case "mark":
      Some{Spec.Question.Mark{c, x}}
    case "status":
      Question.id("status", c, Id.read(w, x))
    case "request":
      Question.id("request", c, Id.read(w, x))
    case "clashes":
      Question.id("clashes", c, Id.read(w, x))
    case "base":
      Question.id("base", c, Id.read(w, x))
    case _:
      Maybe.bind(&2, Nat, Spec.Question, Nat.read(x), n => Question.at(k, c, n))

# the question of the kind k about the group g of the store h at its version n
def Question.group(k: String, h: Hashes.Hash, g: String, n: Nat) -> Maybe<&2, Spec.Question>:
  match k:
    case "members":
      Some{Spec.Question.Members{h, g, n}}
    case "nodes":
      Some{Spec.Question.Nodes{h, g, n}}
    case "is-group":
      Some{Spec.Question.IsGroup{h, g, n}}
    case _:
      None{}

# the question that the words ws of the kind k ask, where w is the writer
# connected
def Question.read(+w: String, +k: String, ws: List<&2, String>) -> Maybe<&2, Spec.Question>:
  match ws:
    case Con{c, Nil{}}:
      Maybe.bind(
        &2,
        Ledgers.Line,
        Spec.Question,
        Line.read(c),
        x => Bool.pick(
          Maybe<&2, Spec.Question>,
          String.eq(k, "count"),
          Some{Spec.Question.Count{x}},
          None{}
        )
      )
    case Con{c, Con{y, Nil{}}}:
      Maybe.bind(&2, Ledgers.Line, Spec.Question, Line.read(c), x => Question.two(w, k, x, y))
    case Con{h, Con{g, Con{n, Nil{}}}}:
      do Maybe<&2, Spec.Question>:
        x: Hashes.Hash <- Hash.read(h)
        m: Nat <- Nat.read(n)
        Question.group(k, x, g, m)
    case Con{c, Con{a, Con{b, Con{us, Con{bs, Nil{}}}}}}:
      do Maybe<&2, Spec.Question>:
        x: Ledgers.Line <- Line.read(c)
        y: Nat <- Nat.read(a)
        z: Nat <- Nat.read(b)
        Bool.pick(
          Maybe<&2, Spec.Question>,
          String.eq(k, "affects"),
          Some{Spec.Question.Affects{x, y, z, Names.read(us), Names.read(bs)}},
          None{}
        )
    case _:
      None{}

# the command that the words ws give, where w is the writer connected
def Cmd.read(+w: String, ws: List<&2, String>) -> Maybe<&2, Cmd>:
  match ws:
    case Con{"start", Con{i, os}}:
      Some{Cmd.Ask{Ledgers.Id{w, i}, Spec.Request.Start{os}}}
    case Con{"write", Con{i, Con{c, Con{p, Con{f, Nil{}}}}}}:
      Maybe.bind(&2, Ledgers.Line, Cmd, Line.read(c), x => Some{Cmd.Put{Ledgers.Id{w, i}, x, p, f}})
    case Con{"merge", Con{i, Con{a, Con{b, Nil{}}}}}:
      do Maybe<&2, Cmd>:
        x: Ledgers.Line <- Line.read(a)
        y: Ledgers.Line <- Line.read(b)
        return Cmd.Ask{Ledgers.Id{w, i}, Spec.Request.Merge{x, y}}
    case Con{"resolve", Con{i, Con{m, Con{p, Con{f, Nil{}}}}}}:
      Some{Cmd.Fix{Ledgers.Id{w, i}, Id.read(w, m), p, f}}
    case Con{"mark", Con{i, Con{c, Con{m, Con{k, Nil{}}}}}}:
      do Maybe<&2, Cmd>:
        x: Ledgers.Line <- Line.read(c)
        n: Nat <- Nat.read(k)
        return Cmd.Ask{Ledgers.Id{w, i}, Spec.Request.Mark{x, m, n}}
    case Con{"move", Con{i, Con{a, Con{b, Con{k, Nil{}}}}}}:
      do Maybe<&2, Cmd>:
        x: Ledgers.Line <- Line.read(a)
        y: Ledgers.Line <- Line.read(b)
        n: Nat <- Nat.read(k)
        return Cmd.Ask{Ledgers.Id{w, i}, Spec.Request.Move{x, y, n}}
    case Con{"group", Con{i, Con{h, Con{g, ms}}}}:
      Maybe.bind(
        &2,
        Hashes.Hash,
        Cmd,
        Hash.read(h),
        x => Some{Cmd.Ask{Ledgers.Id{w, i}, Spec.Request.Group{x, g, ms}}}
      )
    case Con{"own", Con{i, Con{c, Con{g, Nil{}}}}}:
      Maybe.bind(
        &2,
        Ledgers.Line,
        Cmd,
        Line.read(c),
        x => Some{Cmd.Ask{Ledgers.Id{w, i}, Spec.Request.Own{x, g}}}
      )
    case Con{"answer", Con{k, rest}}:
      Maybe.bind(&2, Spec.Question, Cmd, Question.read(w, k, rest), q => Some{Cmd.Answer{q}})
    case Con{"status", rest}:
      Maybe.bind(&2, Spec.Question, Cmd, Question.read(w, "status", rest), q => Some{Cmd.Answer{q}})
    case Con{"affects", rest}:
      Maybe.bind(
        &2,
        Spec.Question,
        Cmd,
        Question.read(w, "affects", rest),
        q => Some{Cmd.Answer{q}}
      )
    case Con{"read", Con{c, Con{k, Con{p, Nil{}}}}}:
      do Maybe<&2, Cmd>:
        x: Ledgers.Line <- Line.read(c)
        n: Nat <- Nat.read(k)
        return Cmd.Read{x, n, p}
    case Con{"view", Con{c, Con{p, Nil{}}}}:
      Maybe.bind(&2, Ledgers.Line, Cmd, Line.read(c), x => Some{Cmd.View{x, p}})
    case Con{"work", Nil{}}:
      Some{Cmd.Work{}}
    case Con{"sync", Con{a, Nil{}}}:
      Some{Cmd.Sync{a}}
    case Con{"drop", Nil{}}:
      Some{Cmd.Drop{}}
    case Con{"stop", Nil{}}:
      Some{Cmd.Stop{False{}}}
    case Con{"stop", Con{"--force", Nil{}}}:
      Some{Cmd.Stop{True{}}}
    case Con{"liars", Nil{}}:
      Some{Cmd.Liars{}}
    case Con{"mount", Con{d, Con{c, Con{p, Nil{}}}}}:
      Maybe.bind(&2, Ledgers.Line, Cmd, Line.read(c), x => Some{Cmd.Mount{d, x, p}})
    case Con{"unmount", Con{d, Nil{}}}:
      Some{Cmd.Unmount{d}}
    case _:
      None{}

# The state on disk
# -----------------

# the path of the file named f in the directory d
def Path.at(d: String, f: String) -> String:
  d ++ "/" ++ f

# The log
# -------
# The file facts is the header Log.head, then one record per fact, each
# written once, as short bytes (Disk.Short.bytes). A record is the code of
# its fact (Coded.Fact.code: tag 0, an ask; tag 1, a vote), or, for a vote
# whose request an earlier record holds, tag 2: the number of that record,
# then the vote without its ask (Ref.code). So the words of a request are
# kept once, however many votes name it. The records are numbered from 0.

# the first words of a log of this format
def Log.head() -> List<&2, U32>:
  Texts.Bytes.of_text("vend facts 2\n")

# what the records of a log give beside the facts: how many there are, the
# ask that each record that holds one holds, under the code of its number
# (Log.key), and the number of the first record that holds each ask, under
# the code of the ask
type Log is Data:
  Log{count: Nat, asks: Crits.Crit<Types.Ask>, index: Crits.Crit<Nat>}

# a log with no record
def Log.new() -> Log:
  Log{0n, Crits.Crit.new(Types.Ask), Crits.Crit.new(Nat)}

# the key of the record number n
def Log.key(n: Nat) -> List<&2, U32>:
  Codes.Code.count(n, [])

# the asks of the records of the log l
def Log.asks(l: Log) -> Crits.Crit<Types.Ask>:
  match l:
    case Log{n, xs, ix}:
      xs

# the index ix of the first record of each ask, with the record n for the
# ask of the code k, unless it has one
def Log.first(+ix: Crits.Crit<Nat>, +k: List<&2, U32>, n: Nat) -> Crits.Crit<Nat>:
  Shared.Bool.when(
    Crits.Crit<Nat>,
    Crits.Crit.has(Nat, ix, k),
    u => ix,
    u => Crits.Crit.set(~Nat, ix, k, n)
  )

# the log l with one more record, which holds the ask m, if any
def Log.add(l: Log, m: Maybe<&2, Types.Ask>) -> Log:
  match l m:
    case Log{n, xs, ix} None{}:
      Log{1n+n, xs, ix}
    case Log{+n, xs, ix} Some{+a}:
      Log{
        1n+n,
        Crits.Crit.set(~Types.Ask, xs, Log.key(n), a),
        Log.first(ix, Coded.Ask.code(a, []), n)
      }

# the ask that the fact f holds, if any: an ask, or the pick of a vote
def Fact.ask(f: Types.Fact) -> Maybe<&2, Types.Ask>:
  match f:
    case Types.Fact.Ask{a}:
      Some{a}
    case Types.Fact.Vote{v, st, Types.Cast.Vote{r, Types.Pick{a, pins}, b}}:
      Some{a}
    case Types.Fact.Vote{v, st, Types.Cast.Pass{r}}:
      None{}

# the vote of v at the step st in the round r, for the ask a, if known, with
# the pins pins and the basis b
def Ref.vote(
  m: Maybe<&2, Types.Ask>,
  v: String,
  st: Types.Step,
  r: Nat,
  pins: Types.Pins,
  b: List<&2, Types.Ref>
) -> Maybe<&2, Types.Fact>:
  match m:
    case None{}:
      None{}
    case Some{a}:
      Some{Types.Fact.Vote{v, st, Types.Cast.Vote{r, Types.Pick{a, pins}, b}}}

# Ref.read, once the basis is read
def Ref.read.basis(
  m: Maybe<&2, Types.Ask>,
  w: String,
  x: Types.Step,
  k: Nat,
  ps: Types.Pins,
  b: Codes.Read<List<&2, Types.Ref>>
) -> Maybe<&2, Codes.Read<Types.Fact>>:
  match b:
    case Codes.Read{bs, ts}:
      do Maybe<&2, Codes.Read<Types.Fact>>:
        f: Types.Fact <- Ref.vote(m, w, x, k, ps, bs)
        return Codes.Read{f, ts}

# Ref.read, once the pins are read
def Ref.read.pins(
  m: Maybe<&2, Types.Ask>,
  w: String,
  x: Types.Step,
  k: Nat,
  pins: Codes.Read<Types.Pins>
) -> Maybe<&2, Codes.Read<Types.Fact>>:
  match pins:
    case Codes.Read{ps, ts}:
      do Maybe<&2, Codes.Read<Types.Fact>>:
        b: Codes.Read<List<&2, Types.Ref>> <- Coded.Refs.code.read(ts)
        Ref.read.basis(m, w, x, k, ps, b)

# Ref.read, once the round is read (r)
def Ref.read.round(
  m: Maybe<&2, Types.Ask>,
  w: String,
  x: Types.Step,
  r: Codes.Read<Nat>
) -> Maybe<&2, Codes.Read<Types.Fact>>:
  match r:
    case Codes.Read{k, ts}:
      do Maybe<&2, Codes.Read<Types.Fact>>:
        pins: Codes.Read<Types.Pins> <- Coded.Pins.code.read(ts)
        Ref.read.pins(m, w, x, k, pins)

# Ref.read, once the step is read (st)
def Ref.read.step(
  m: Maybe<&2, Types.Ask>,
  w: String,
  st: Codes.Read<Types.Step>
) -> Maybe<&2, Codes.Read<Types.Fact>>:
  match st:
    case Codes.Read{x, ts}:
      do Maybe<&2, Codes.Read<Types.Fact>>:
        r: Codes.Read<Nat> <- Codes.Code.count.read(ts)
        Ref.read.round(m, w, x, r)

# Ref.read, once the voter is read (v)
def Ref.read.voter(
  m: Maybe<&2, Types.Ask>,
  v: Codes.Read<String>
) -> Maybe<&2, Codes.Read<Types.Fact>>:
  match v:
    case Codes.Read{w, ts}:
      do Maybe<&2, Codes.Read<Types.Fact>>:
        st: Codes.Read<Types.Step> <- Coded.Step.code.read(ts)
        Ref.read.step(m, w, st)

# Ref.read, once the number of the record of the ask is read (j)
def Ref.read.at(
  +xs: Crits.Crit<Types.Ask>,
  j: Codes.Read<Nat>
) -> Maybe<&2, Codes.Read<Types.Fact>>:
  match j:
    case Codes.Read{n, ts}:
      do Maybe<&2, Codes.Read<Types.Fact>>:
        v: Codes.Read<String> <- Codes.Code.text.read(ts)
        Ref.read.voter(Crits.Crit.get(Types.Ask, xs, Log.key(n)), v)

# the vote of a record of tag 2, from the words ts after its tag, with the
# asks xs of the records before it
def Ref.read(+xs: Crits.Crit<Types.Ask>, ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Types.Fact>>:
  do Maybe<&2, Codes.Read<Types.Fact>>:
    j: Codes.Read<Nat> <- Codes.Code.count.read(ts)
    Ref.read.at(xs, j)

# the words of a record of tag 2: the number j of the record of the ask, then
# the vote of v at the step st in the round r, with the pins pins and the
# basis b, then rest
def Ref.code(
  j: Nat,
  v: String,
  st: Types.Step,
  r: Nat,
  pins: Types.Pins,
  b: List<&2, Types.Ref>,
  rest: List<&2, U32>
) -> List<&2, U32>:
  2
    <> Codes.Code.count(
      j,
      Codes.Code.text(
        v,
        Coded.Step.code(st, Codes.Code.count(r, Coded.Pins.code(pins, Coded.Refs.code(b, rest))))
      )
    )

# what a read of the records of a log found next
type Next is Data:
  Next.End{}
  Next.Bad{}
  Next.Got{fact: Types.Fact, fresh: Bool, rest: List<&2, U32>}

# what the read m of a record found: a record that names the record of its
# ask is not fresh
def Next.of(fresh: Bool, m: Maybe<&2, Codes.Read<Types.Fact>>) -> Next:
  match m:
    case None{}:
      Next.Bad{}
    case Some{Codes.Read{f, r}}:
      Next.Got{f, fresh, r}

# the record whose tag is x, with the words r after it, where xs are the
# asks of the records before it
def Next.at(+xs: Crits.Crit<Types.Ask>, +x: U32, +r: List<&2, U32>) -> Next:
  Next.of(
    Bool.not(U32.is_eq(x, 2)),
    Shared.Bool.when(
      Maybe<&2, Codes.Read<Types.Fact>>,
      U32.is_eq(x, 2),
      u => Ref.read(xs, r),
      u => Coded.Fact.code.read.of(x, r)
    )
  )

# the first record of the words ws, if any, where xs are the asks of the
# records before it
def Next.read(+xs: Crits.Crit<Types.Ask>, ws: List<&2, U32>) -> Next:
  match ws:
    case Nil{}:
      Next.End{}
    case Con{+x, +r}:
      Next.at(xs, x, r)

# the ask that a fresh record (fresh) of the fact f holds, if any: the
# record of the first is the one that a later record names
def Fresh.ask(fresh: Bool, f: Types.Fact) -> Maybe<&2, Types.Ask>:
  match fresh:
    case True{}:
      Fact.ask(f)
    case False{}:
      None{}

# the log l and the facts s with the record that x found and those after it,
# read in at most n reads; the file at the path at holds them
def Log.go(
  at: String,
  n: Nat,
  x: Next,
  l: Log,
  s: Facts.Plain()
) -> Result<&1, &1, String, Log & Facts.Plain()>:
  match n x:
    case _ Next.End{}:
      Done{(l, s)}
    case 1n+p Next.Got{+f, fresh, r}:
      +l2 = Log.add(l, Fresh.ask(fresh, f))
      Log.go(at, p, Next.read(Log.asks(l2), r), l2, Facts.Facts.add(s, f))
    case _ _:
      Fail{at ++ ": a record does not read; the log is damaged"}

# the words of a log that m holds after the header h, if it holds one and
# the words before matched it (ok)
def Log.strip(h: List<&2, U32>, ok: Bool, m: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match h ok m:
    case _ False{} _:
      None{}
    case Nil{} True{} m2:
      m2
    case Con{+a, hr} True{} Some{Con{+b, wr}}:
      Log.strip(hr, U32.is_eq(a, b), Some{wr})
    case _ _ _:
      None{}

# the log and the facts that the words m after the header hold, the file at
# the path at
def Log.of(at: String, m: Maybe<&2, List<&2, U32>>) -> Result<&1, &1, String, Log & Facts.Plain()>:
  match m:
    case None{}:
      Fail{
        at
          ++ ": not a log of this version (it starts with "
          ++ Texts.Bytes.to_text(Log.head())
          ++ ")"
      }
    case Some{+ws}:
      Log.go(
        at,
        List.length(&2, U32, ws),
        Next.read(Crits.Crit.new(Types.Ask), ws),
        Log.new(),
        Facts.Facts.new()
      )

# the log and the facts that the bytes bs of the file at the path at hold
def Log.read(+at: String, bs: List<&2, U32>) -> Result<&1, &1, String, Log & Facts.Plain()>:
  Log.of(at, Log.strip(Log.head(), True{}, Disk.Short.words(bs)))

# the record of the vote of v at the step st in the round r for the ask a,
# with the pins pins and the basis b, then rest, where m is the record of a,
# if any: that record by its number, else the vote whole
def Log.vote(
  m: Maybe<&2, Nat>,
  +v: String,
  +st: Types.Step,
  +r: Nat,
  +a: Types.Ask,
  +pins: Types.Pins,
  +b: List<&2, Types.Ref>,
  rest: List<&2, U32>
) -> List<&2, U32>:
  match m:
    case None{}:
      Coded.Fact.code(Types.Fact.Vote{v, st, Types.Cast.Vote{r, Types.Pick{a, pins}, b}}, rest)
    case Some{j}:
      Ref.code(j, v, st, r, pins, b, rest)

# the ask that the record of the ask a holds, where m is the record of an
# earlier ask like it, if any: none then
def Log.fresh_ask(m: Maybe<&2, Nat>, a: Types.Ask) -> Maybe<&2, Types.Ask>:
  match m:
    case None{}:
      Some{a}
    case Some{j}:
      None{}

# the index of the first record of each ask of the log l
def Log.index(l: Log) -> Crits.Crit<Nat>:
  match l:
    case Log{n, xs, ix}:
      ix

# the record of the fact f after the log l, then rest
def Log.code(+l: Log, f: Types.Fact, rest: List<&2, U32>) -> List<&2, U32>:
  match f:
    case Types.Fact.Vote{v, st, Types.Cast.Vote{r, Types.Pick{+a, pins}, b}}:
      Log.vote(Crits.Crit.get(Nat, Log.index(l), Coded.Ask.code(a, [])), v, st, r, a, pins, b, rest)
    case _:
      Coded.Fact.code(f, rest)

# the log l after the record of the fact f
def Log.after(+l: Log, f: Types.Fact) -> Log:
  match f:
    case Types.Fact.Vote{v, st, Types.Cast.Vote{r, Types.Pick{+a, pins}, b}}:
      Log.add(l, Log.fresh_ask(Crits.Crit.get(Nat, Log.index(l), Coded.Ask.code(a, [])), a))
    case _:
      Log.add(l, Fact.ask(f))

# the records of the facts fs after the log l, then rest
def Log.puts(fs: List<&2, Types.Fact>, +l: Log) -> List<&2, U32>:
  match fs:
    case Nil{}:
      []
    case Con{+f, more}:
      Log.code(l, f, Log.puts(more, Log.after(l, f)))

# the fact f is an ask
def Fact.is_ask(f: Types.Fact) -> Bool:
  match f:
    case Types.Fact.Ask{a}:
      True{}
    case Types.Fact.Vote{v, st, x}:
      False{}

# the facts of the entries es that old does not hold, asks first (Ask) or
# votes (not Ask)
def Log.fresh(
  +ask: Bool,
  es: List<&2, Crits.Bind<Types.Fact>>,
  +old: Facts.Plain()
) -> List<&2, Types.Fact>:
  match es:
    case Nil{}:
      []
    case Con{Crits.Bind{k, +f}, more}:
      List.filter.put(
        Types.Fact,
        f,
        Log.fresh(ask, more, old),
        Bool.and(
          Bool.not(Crits.Crit.has(Types.Fact, old, k)),
          Bool.not(Bool.xor(ask, Fact.is_ask(f)))
        )
      )

# s holds each of the facts fs, and the test before held (ok)
def Log.all(fs: List<&2, Types.Fact>, ok: Bool, +s: Facts.Plain()) -> Bool:
  match fs ok:
    case _ False{}:
      False{}
    case Nil{} True{}:
      True{}
    case Con{f, rest} True{}:
      Log.all(rest, Facts.Facts.has(s, f), s)

# the facts fs hold no fact twice, and s holds each and no other
def Log.same(+fs: List<&2, Types.Fact>, +s: Facts.Plain()) -> Bool:
  Log.all(fs, Nat.is_eq(List.length(&2, Types.Fact, fs), Crits.Crit.size(Types.Fact, s)), s)

# the records ws that the facts fs gave, with the log after them, when they
# read back as fs (r), at the file at the path at
def Log.checked(
  at: String,
  +fs: List<&2, Types.Fact>,
  ws: List<&2, U32>,
  r: Result<&1, &1, String, Log & Facts.Plain()>
) -> Result<&1, &1, String, Log & List<&2, U32>>:
  match r:
    case Done{(l, +s)}:
      Bool.pick(
        Result<&1, &1, String, Log & List<&2, U32>>,
        Log.same(fs, s),
        Done{(l, ws)},
        Fail{at ++ ": the new records do not read back as the new facts; nothing is written"}
      )
    case Fail{e}:
      Fail{e}

# the records of the facts fs after the log l, with the log after them, when
# they read back as fs, for the file at the path at
def Log.records(
  +at: String,
  +fs: List<&2, Types.Fact>,
  +l: Log
) -> Result<&1, &1, String, Log & List<&2, U32>>:
  +ws = Log.puts(fs, l)
  Log.checked(
    at,
    fs,
    ws,
    Log.go(at, List.length(&2, U32, ws), Next.read(Log.asks(l), ws), l, Facts.Facts.new())
  )

# the parts ps, with the words ws under their hash h when the file that holds
# them is named by it (ok)
def Kept.if(ok: Bool, h: Hashes.Hash, ws: List<&2, U32>, ps: Parts.Parts) -> Parts.Parts:
  match ok:
    case True{}:
      Parts.Parts.put.at(ps, h, ws)
    case False{}:
      ps

# the parts ps, with the words ws of the file named n, when n is their hash
def Kept.add(n: String, +ws: List<&2, U32>, ps: Parts.Parts) -> Parts.Parts:
  +h = Hashes.Sha.hash(ws)
  Kept.if(String.eq(Hash.show(h), n), h, ws, ps)

# the parts ps with those of the files named ns in the directory d
def Kept.load(ns: List<&2, String>, +d: String, ps: Parts.Parts) -> Disk.Run(Parts.Parts):
  match ns:
    case Nil{}:
      Disk.Run.pure(Parts.Parts, ps)
    case Con{+n, rest}:
      do Disk.Run<Parts.Parts>:
        ws: List<&2, U32> <- Disk.Disk.shorts(Path.at(d, n))
        Kept.load(rest, d, Kept.add(n, ws, ps))

# the file at the path at written with the words ws, unless it is held
def Kept.write(held: Bool, at: String, ws: List<&2, U32>) -> Disk.Run(Unit):
  match held:
    case True{}:
      Disk.Run.pure(Unit, Unit{})
    case False{}:
      Disk.Disk.write(at, "w", Disk.Short.bytes(ws, []))

# the parts of the entries es that old does not hold, written to the
# directory d
def Kept.save(
  es: List<&2, Crits.Bind<List<&2, U32>>>,
  +old: Crits.Crit<List<&2, U32>>,
  +d: String
) -> Disk.Run(Unit):
  match es:
    case Nil{}:
      Disk.Run.pure(Unit, Unit{})
    case Con{Crits.Bind{+k, ws}, more}:
      do Disk.Run<Unit>:
        Kept.write(Crits.Crit.has(List<&2, U32>, old, k), Path.at(d, Hex.words(k)), ws)
        Kept.save(more, old, d)

# the path at before rest, unless the parts hold it (held)
def Kept.gone.put(held: Bool, at: String, rest: List<String>) -> List<String>:
  match held:
    case True{}:
      rest
    case False{}:
      at <> rest

# the paths in the directory d of the parts of the entries es that now does
# not hold
def Kept.gone(
  es: List<&2, Crits.Bind<List<&2, U32>>>,
  +now: Crits.Crit<List<&2, U32>>,
  +d: String
) -> List<String>:
  match es:
    case Nil{}:
      []
    case Con{Crits.Bind{+k, ws}, more}:
      Kept.gone.put(
        Crits.Crit.has(List<&2, U32>, now, k),
        Path.at(d, Hex.words(k)),
        Kept.gone(more, now, d)
      )

# The node
# --------

# the name of the node r
def Raw.name(r: Nodes.Raw) -> String:
  match r:
    case Nodes.Raw{n, ws, ms, st, fs, ps}:
      n

# the node r has stopped
def Raw.stopped(r: Nodes.Raw) -> Bool:
  match r:
    case Nodes.Raw{n, ws, ms, st, fs, ps}:
      st

# the map of the parts of the node r
def Raw.kept(r: Nodes.Raw) -> Crits.Crit<List<&2, U32>>:
  match r:
    case Nodes.Raw{n, ws, ms, st, fs, Parts.Parts{t}}:
      t

# the facts of the fast node f
def Node.facts(f: Fasts.Fast) -> Facts.Plain():
  Nodes.Raw.facts(Fasts.Fast.raw(f))

# the parts of the fast node f
def Node.kept(f: Fasts.Fast) -> Crits.Crit<List<&2, U32>>:
  Raw.kept(Fasts.Fast.raw(f))

# the count of the facts of the fast node f
def Node.size(f: Fasts.Fast) -> Nat:
  Crits.Crit.size(Types.Fact, Node.facts(f))

# what a data address keeps: the node, and the log of its facts
type Stored is Data:
  Stored{node: Nodes.Raw, log: Log}

# what a data address keeps, from the name n, the log and the facts p that
# its log holds, and its parts ps
def Stored.of(n: String, p: Log & Facts.Plain(), ps: Parts.Parts) -> Stored:
  (l, fs) = p
  Stored{Nodes.Raw{n, [], [], False{}, fs, ps}, l}

# the node of what a data address keeps
def Stored.node(k: Stored) -> Nodes.Raw:
  match k:
    case Stored{r, l}:
      r

# what the data address a keeps: the name, the facts and the parts of its
# node, and the log
def Node.load(+a: String) -> Disk.Run(Stored):
  do Disk.Run<Stored>:
    name: List<&2, U32> <- Disk.Disk.read(Path.at(a, "name"))
    bs: List<&2, U32> <- Disk.Disk.read(Path.at(a, "facts"))
    p: Log & Facts.Plain() <- Disk.Run.of(Log & Facts.Plain(), Log.read(Path.at(a, "facts"), bs))
    ns: List<&2, String> <- Disk.Disk.names(Path.at(a, "parts"))
    ps: Parts.Parts <- Kept.load(ns, Path.at(a, "parts"), Parts.Parts.new())
    return Stored.of(Texts.Bytes.to_text(name), p, ps)

# the node r of the data address a as a fast node whose table knows nothing
# yet, which is right for any state (Fast.none_ok in fast.bend); the first
# work learns what it reads. A fast node does what its state does only while
# that state can be a node (Nodes.Raw.ok, a premise of Fast.does_raw), so an
# address whose facts are not sound for its name is refused (Raw.ok.fast is
# Raw.ok: Raw.ok_fast in fast.bend)
def Node.resume(+a: String, +r: Nodes.Raw) -> Disk.Run(Fasts.Fast):
  Shared.Bool.when(
    Disk.Run(Fasts.Fast),
    Nodes.Raw.ok.fast(r),
    u => Disk.Run.pure(Fasts.Fast, Fasts.Fast{r, Known.Known.none()}),
    u => Disk.Run.fail(
      Fasts.Fast,
      a ++ ": the facts there cannot be those of a node named " ++ Raw.name(r)
    )
  )

# the fast node f after at most n more works, which stop once a work adds no
# fact (done): a work then adds none again, since it reads only the facts
def Node.settle(n: Nat, done: Bool, +f: Fasts.Fast) -> Fasts.Fast:
  match n done:
    case _ True{}:
      f
    case 0n False{}:
      f
    case 1n+p False{}:
      +g = Fasts.Fast.does(f, Nodes.Act.Work{})
      Node.settle(p, Nat.is_eq(Node.size(f), Node.size(g)), g)

# the records ws appended to the log at the path at, and the log l after
# them
def Log.write(+at: String, p: Log & List<&2, U32>) -> Disk.Run(Log):
  (l, ws) = p
  do Disk.Run<Log>:
    Disk.Disk.write(at, "a", Disk.Short.bytes(ws, []))
    return l

# the data address a, whose log was l when it kept the node f0, keeping the
# node f that f0 became: the new parts first, then the new facts (asks first,
# so that a vote names the record of its ask), then the parts that f let go
# of removed; and the log after it
def Node.save(+a: String, +l: Log, +f0: Fasts.Fast, +f: Fasts.Fast) -> Disk.Run(Log):
  +d = Path.at(a, "parts")
  +at = Path.at(a, "facts")
  +es = Crits.Crit.entries(Types.Fact, Node.facts(f))
  do Disk.Run<Log>:
    Kept.save(Crits.Crit.entries(List<&2, U32>, Node.kept(f)), Node.kept(f0), d)
    l2: Log <- Disk.Run.bind(
      Log & List<&2, U32>,
      Log,
      Disk.Run.of(
        Log & List<&2, U32>,
        Log.records(
          at,
          List.append(
            &2,
            Types.Fact,
            Log.fresh(True{}, es, Node.facts(f0)),
            Log.fresh(False{}, es, Node.facts(f0))
          ),
          l
        )
      ),
      p => Log.write(at, p)
    )
    Disk.Disk.remove(Kept.gone(Crits.Crit.entries(List<&2, U32>, Node.kept(f0)), Node.kept(f), d))
    return l2

# the step m, while the node holds the lock of the data address a: only one
# node runs on an address, since the lock is made only where it is not
def Node.locked(-A: Type, +a: String, m: Disk.Run(A)) -> Disk.Run(A):
  +lock = Path.at(a, "lock")
  do Disk.Run<A>:
    Disk.Run.else(
      Unit,
      "no node can run on "
        ++ a
        ++ ": none is there, or one runs there (if none runs, remove "
        ++ lock
        ++ ")",
      Disk.Disk.write(lock, "x", [])
    )
    r: Result<&1, &1, String, A> <- Disk.Run.io(Result<&1, &1, String, A>, m)
    Disk.Disk.remove([lock])
    Disk.Run.of(A, r)

# Sync over TCP
# -------------
# A session, in one connection: the node that fetches (the client) sends
# what it asks (Ask.sync, or a stop) and a summary of what it holds, the
# SHA-256 of the code of each fact and the hash of each part; the node that
# serves answers with the facts and parts that the client lacks, and the
# summary of its own; the client sends the facts and parts that the server
# lacks. Each side takes the facts in by the core's Sync, which checks each,
# and a part only under the hash of its words (Parts.put). A summary is one
# round trip each way and a hash per fact (as the store trusts SHA-256); a
# hash per crit subtree would send less when both hold almost the same, but
# costs a round trip per level of the tree and the same hashes to build.
# Each message is the words of Codes, as short bytes (Disk.Short.bytes).

# what the client of a session asks: a sync (0), or a stop (1, forced 2)
def Ask.sync() -> Nat:
  0n

# how long a node waits for a message of a session, in milliseconds
def Wire.wait_ms() -> U32:
  30000

# what a node holds, for the other node of a session: the hash of the code
# of each fact, and the hash of each part
type Summary is Data:
  Summary{facts: List<&2, Hashes.Hash>, parts: List<&2, Hashes.Hash>}

# what a node sends the other: facts, and the words of parts
type Offer is Data:
  Offer{facts: List<&2, Types.Fact>, parts: List<&2, List<&2, U32>>}

# the hash of the code of the fact f
def Wire.digest(f: Types.Fact) -> Hashes.Hash:
  Hashes.Sha.hash(Coded.Fact.code(f, []))

# the hashes of the facts of the entries es
def Wire.digests(es: List<&2, Crits.Bind<Types.Fact>>) -> List<&2, Hashes.Hash>:
  match es:
    case Nil{}:
      []
    case Con{Crits.Bind{k, f}, rest}:
      Wire.digest(f) <> Wire.digests(rest)

# the set of the hashes hs, each under its code
def Wire.set(hs: List<&2, Hashes.Hash>, acc: Crits.Crit<Unit>) -> Crits.Crit<Unit>:
  match hs:
    case Nil{}:
      acc
    case Con{h, rest}:
      Wire.set(rest, Crits.Crit.set(~Unit, acc, Hashes.Hash.code(h, []), Unit{}))

# the summary of the fast node f
def Wire.summary(+f: Fasts.Fast) -> Summary:
  Summary{Wire.digests(Crits.Crit.entries(Types.Fact, Node.facts(f))), Fasts.Fast.parts(f)}

# the facts of the entries es whose hash the set have does not hold
def Wire.lacks(
  es: List<&2, Crits.Bind<Types.Fact>>,
  +have: Crits.Crit<Unit>
) -> List<&2, Types.Fact>:
  match es:
    case Nil{}:
      []
    case Con{Crits.Bind{k, +f}, rest}:
      List.filter.put(
        Types.Fact,
        f,
        Wire.lacks(rest, have),
        Bool.not(Crits.Crit.has(Unit, have, Hashes.Hash.code(Wire.digest(f), [])))
      )

# the words of the parts of the entries es whose key the set have does not
# hold
def Wire.lacks_parts(
  es: List<&2, Crits.Bind<List<&2, U32>>>,
  +have: Crits.Crit<Unit>
) -> List<&2, List<&2, U32>>:
  match es:
    case Nil{}:
      []
    case Con{Crits.Bind{+k, ws}, rest}:
      List.filter.put(
        List<&2, U32>,
        ws,
        Wire.lacks_parts(rest, have),
        Bool.not(Crits.Crit.has(Unit, have, k))
      )

# what the fast node f sends a node whose summary is x: what x lacks
def Wire.offer(+f: Fasts.Fast, x: Summary) -> Offer:
  match x:
    case Summary{hs, ps}:
      Offer{
        Wire.lacks(
          Crits.Crit.entries(Types.Fact, Node.facts(f)),
          Wire.set(hs, Crits.Crit.new(Unit))
        ),
        Wire.lacks_parts(
          Crits.Crit.entries(List<&2, U32>, Node.kept(f)),
          Wire.set(ps, Crits.Crit.new(Unit))
        )
      }

# the facts s with the facts fs
def Wire.facts(fs: List<&2, Types.Fact>, s: Facts.Plain()) -> Facts.Plain():
  match fs:
    case Nil{}:
      s
    case Con{f, rest}:
      Wire.facts(rest, Facts.Facts.add(s, f))

# the parts ps with the words of each of wss under their hash
def Wire.parts(wss: List<&2, List<&2, U32>>, ps: Parts.Parts) -> Parts.Parts:
  match wss:
    case Nil{}:
      ps
    case Con{ws, rest}:
      Wire.parts(rest, Parts.Parts.put(ps, ws))

# the fast node f after it takes in the offer o, by the core's Sync
def Wire.take(f: Fasts.Fast, o: Offer) -> Fasts.Fast:
  match o:
    case Offer{fs, wss}:
      Fasts.Fast.does(
        f,
        Nodes.Act.Sync{
          Nodes.Raw{
            "",
            [],
            [],
            False{},
            Wire.facts(fs, Facts.Facts.new()),
            Wire.parts(wss, Parts.Parts.new())
          }
        }
      )

# the summary x, then r
def Summary.code(x: Summary, r: List<&2, U32>) -> List<&2, U32>:
  match x:
    case Summary{hs, ps}:
      Codes.Code.list(
        ~Hashes.Hash,
        ~Hashes.Hash.code,
        hs,
        Codes.Code.list(~Hashes.Hash, ~Hashes.Hash.code, ps, r)
      )

# a summary
def Summary.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Summary>>:
  Codes.Code.two.read(
    ~List<&2, Hashes.Hash>,
    ~List<&2, Hashes.Hash>,
    ~Summary,
    ~(t => Codes.Code.list.read(~Hashes.Hash, ~Hashes.Hash.code.read, t)),
    ~(t => Codes.Code.list.read(~Hashes.Hash, ~Hashes.Hash.code.read, t)),
    a => b => Summary{a, b},
    ts
  )

# the offer x, then r
def Offer.code(x: Offer, r: List<&2, U32>) -> List<&2, U32>:
  match x:
    case Offer{fs, wss}:
      Codes.Code.list(
        ~Types.Fact,
        ~Coded.Fact.code,
        fs,
        Codes.Code.list(~List<&2, U32>, ~Codes.Code.words, wss, r)
      )

# an offer
def Offer.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Offer>>:
  Codes.Code.two.read(
    ~List<&2, Types.Fact>,
    ~List<&2, List<&2, U32>>,
    ~Offer,
    ~(t => Codes.Code.list.read(~Types.Fact, ~Coded.Fact.code.read, t)),
    ~(t => Codes.Code.list.read(~List<&2, U32>, ~Codes.Code.words.read, t)),
    a => b => Offer{a, b},
    ts
  )

# the value that m read, when it read all the words
def Wire.whole(-A: Data, m: Maybe<&2, Codes.Read<A>>) -> Maybe<&2, A>:
  match m:
    case Some{Codes.Read{x, Nil{}}}:
      Some{x}
    case _:
      None{}

# the words that the short bytes bs of a message hold, read by r
def Wire.read(
  ~A: Data,
  ~r: List<&2, U32> -> Maybe<&2, Codes.Read<A>>,
  bs: List<&2, U32>
) -> Maybe<&2, A>:
  Maybe.bind(&2, List<&2, U32>, A, Disk.Short.words(bs), ws => Wire.whole(A, r(ws)))

# the message of the words ws sent on the socket s
def Wire.send(s: Socket, ws: List<&2, U32>) -> Disk.Sock(Unit):
  Disk.Net.send(s, Disk.Short.bytes(ws, []))

# the value of the message m, or a step that fails
def Wire.got(-A: Data, s: Socket, m: Maybe<&2, A>) -> Disk.Sock(A):
  match m:
    case None{}:
      IO.pure(
        Socket & Result<&1, &1, String, A>,
        (s, Fail{"the other node sent a message that does not read"})
      )
    case Some{x}:
      Disk.Sock.pure(A, s, x)

# the next message from the socket s, read by r
def Wire.recv(~A: Data, ~r: List<&2, U32> -> Maybe<&2, Codes.Read<A>>, s: Socket) -> Disk.Sock(A):
  Disk.Sock.bind(
    List<&2, U32>,
    A,
    Disk.Net.recv(s, Wire.wait_ms()),
    t => bs => Wire.got(A, t, Wire.read(~A, ~r, bs))
  )

# what the node that serves answers a sync: the offer of what the client
# lacks, and the summary of what it holds
type Served is Data:
  Served{offer: Offer, summary: Summary}

# an answer to a sync
def Served.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Served>>:
  Codes.Code.two.read(
    ~Offer,
    ~Summary,
    ~Served,
    ~Offer.read,
    ~Summary.read,
    a => b => Served{a, b},
    ts
  )

# the answer x, then r
def Served.code(x: Served, r: List<&2, U32>) -> List<&2, U32>:
  match x:
    case Served{o, y}:
      Offer.code(o, Summary.code(y, r))

# the client of a session, with the fast node g after it took in the offer
# of the node that serves, whose summary is x: it sends what x lacks
def Client.took(s: Socket, +g: Fasts.Fast, x: Summary) -> Disk.Sock(Fasts.Fast):
  Disk.Sock.bind(
    Unit,
    Fasts.Fast,
    Wire.send(s, Offer.code(Wire.offer(g, x), [])),
    t => u => Disk.Sock.pure(Fasts.Fast, t, g)
  )

# the client of a session, with the fast node f, after the answer p of the
# node that serves: it takes the offer in and sends what the other lacks
def Client.answered(s: Socket, +f: Fasts.Fast, p: Served) -> Disk.Sock(Fasts.Fast):
  match p:
    case Served{o, x}:
      Client.took(s, Wire.take(f, o), x)

# a session of the client with the fast node f on the socket s
def Client.session(s: Socket, +f: Fasts.Fast) -> Disk.Sock(Fasts.Fast):
  Disk.Sock.bind(
    Unit,
    Fasts.Fast,
    Wire.send(s, Codes.Code.count(Ask.sync(), Summary.code(Wire.summary(f), []))),
    t => u => Disk.Sock.bind(
      Served,
      Fasts.Fast,
      Wire.recv(~Served, ~Served.read, t),
      t2 => p => Client.answered(t2, f, p)
    )
  )

# a TCP address: a host (an IPv4 literal) and a port
type Tcp is Data:
  Tcp{host: String, port: U32}

# the TCP address that the parts ps of tcp:<host>:<port> name
def Tcp.of(ps: List<&2, String>) -> Maybe<&2, Tcp>:
  match ps:
    case Con{"tcp", Con{h, Con{p, Nil{}}}}:
      Maybe.bind(&2, U32, Tcp, U32.read(p), n => Some{Tcp{h, n}})
    case _:
      None{}

# the TCP address tcp:<host>:<port>, if a is one
def Tcp.read(a: String) -> Maybe<&2, Tcp>:
  Tcp.of(String.split(a, ':'))

# the step m on a socket that connects to the host h and the port n
def Tcp.connect.to(-A: Type, +h: String, +n: U32, m: Socket -> Disk.Sock(A)) -> Disk.Run(A):
  Disk.Run.bind(
    Socket,
    A,
    Disk.Run.sys(Socket, "connect to " ++ h ++ ":" ++ U32.show(n), TCP.connect(h, n)),
    s => Disk.Sock.close(A, m(s))
  )

# the step m on a socket that connects to the TCP address t
def Tcp.connect(-A: Type, t: Tcp, m: Socket -> Disk.Sock(A)) -> Disk.Run(A):
  match t:
    case Tcp{+h, +n}:
      Tcp.connect.to(A, h, n, m)

# Mounts
# -------
# A folder mounted at a path of a line: each file in it is a resource,
# mounted at that path and its own path under the folder. The file mounts
# of the address lists the folders and the files that the node saw in each
# when it last read them, one to a line: M, the folder, the line and the
# path; F, the folder and the path of a file in it. Each command, and each
# tick of a node that serves, reads the files: a file that the node did not
# hold is mounted (the core's Mount records what it held); a file whose
# words are not what the node shows at its path is written as a request of
# the node itself (each save a version); a file that is gone is written as
# none, and unmounted; the files of a folder no longer mounted are
# unmounted.

# a folder mounted at the path path of the line line
type Mount is Data:
  Mount{dir: String, line: Ledgers.Line, path: String}

# a file that the node saw in a folder, by its path in it
type Seen is Data:
  Seen{dir: String, file: String}

# the mounted folders of a node, and the files that it saw in them
type Mounts is Data:
  Mounts{dirs: List<&2, Mount>, files: List<&2, Seen>}

# the folder d mounted at the path p of the line m, if it reads, before ds
def Mounts.put(
  m: Maybe<&2, Ledgers.Line>,
  d: String,
  p: String,
  ds: List<&2, Mount>
) -> List<&2, Mount>:
  match m:
    case None{}:
      ds
    case Some{c}:
      Mount{d, c, p} <> ds

# the mounts m of a line of the file mounts, before ms
def Mounts.line(ps: List<&2, String>, ms: Mounts) -> Mounts:
  match ps ms:
    case Con{"M", Con{d, Con{c, Con{p, Nil{}}}}} Mounts{ds, fs}:
      Mounts{Mounts.put(Line.read(c), d, p, ds), fs}
    case Con{"F", Con{d, Con{f, Nil{}}}} Mounts{ds, fs}:
      Mounts{ds, Seen{d, f} <> fs}
    case _ m2:
      m2

# the mounts that the lines ls of the file mounts list
def Mounts.lines(ls: List<&2, String>) -> Mounts:
  match ls:
    case Nil{}:
      Mounts{[], []}
    case Con{x, rest}:
      Mounts.line(String.split(x, '\t'), Mounts.lines(rest))

# the mounts that the file mounts gave (r): none when it is not there
def Mounts.got(r: Result<&1, &1, String, List<&2, U32>>) -> Result<&1, &1, String, Mounts>:
  match r:
    case Fail{e}:
      Done{Mounts{[], []}}
    case Done{bs}:
      Done{Mounts.lines(String.lines(Texts.Bytes.to_text(bs)))}

# the mounts that the data address a keeps
def Mounts.load(+a: String) -> Disk.Run(Mounts):
  IO.bind(
    Result<&1, &1, String, List<&2, U32>>,
    Result<&1, &1, String, Mounts>,
    Disk.Disk.read(Path.at(a, "mounts")),
    r => IO.pure(Result<&1, &1, String, Mounts>, Mounts.got(r))
  )

# the folders ds as lines of the file mounts
def Mounts.show_dirs(ds: List<&2, Mount>) -> String:
  match ds:
    case Nil{}:
      ""
    case Con{Mount{d, c, p}, rest}:
      "M\t" ++ d ++ "\t" ++ Line.show(c) ++ "\t" ++ p ++ "\n" ++ Mounts.show_dirs(rest)

# the files fs as lines of the file mounts
def Mounts.show_files(fs: List<&2, Seen>) -> String:
  match fs:
    case Nil{}:
      ""
    case Con{Seen{d, f}, rest}:
      "F\t" ++ d ++ "\t" ++ f ++ "\n" ++ Mounts.show_files(rest)

# the data address a keeping the mounts ms
def Mounts.save(+a: String, ms: Mounts) -> Disk.Run(Unit):
  match ms:
    case Mounts{ds, fs}:
      Disk.Disk.write(
        Path.at(a, "mounts"),
        "w",
        Texts.Bytes.of_text(Mounts.show_dirs(ds) ++ Mounts.show_files(fs))
      )

# the mounted folders among ds that are the folder d (same), or that are
# not (not same)
def Mounts.keep(ds: List<&2, Mount>, +d: String, +same: Bool) -> List<&2, Mount>:
  match ds:
    case Nil{}:
      []
    case Con{Mount{+e, c, p}, rest}:
      List.filter.put(
        Mount,
        Mount{e, c, p},
        Mounts.keep(rest, d, same),
        Bool.not(Bool.xor(String.eq(e, d), same))
      )

# the mounts ms after the command c mounts or unmounts a folder
def Mounts.change(c: Cmd, ms: Mounts) -> Mounts:
  match c ms:
    case Cmd.Mount{+d, x, p} Mounts{ds, fs}:
      Mounts{Mount{d, x, p} <> Mounts.keep(ds, d, False{}), fs}
    case Cmd.Unmount{+d} Mounts{ds, fs}:
      Mounts{Mounts.keep(ds, d, False{}), fs}
    case _ m2:
      m2

# the path in its line of the file at the path f of a folder mounted at p
def Mount.path(+p: String, f: String) -> String:
  match p:
    case "":
      f
    case ".":
      f
    case _:
      p ++ "/" ++ f

# the fast node shows the words ws at a path (m)
def Mount.shows(m: Maybe<&2, Maybe<&2, List<&2, U32>>>, ws: List<&2, U32>) -> Bool:
  match m:
    case Some{Some{xs}}:
      Facts.Words.is_eq(xs, ws)
    case _:
      False{}

# the fast node shows words at a path (m)
def Mount.holds(m: Maybe<&2, Maybe<&2, List<&2, U32>>>) -> Bool:
  match m:
    case Some{Some{xs}}:
      True{}
    case _:
      False{}

# the fast node g after the node writes the words m at the path q of the
# line c, for what a mounted resource held at the time now
def Mount.save(
  +g: Fasts.Fast,
  +c: Ledgers.Line,
  +q: String,
  m: Maybe<&2, List<&2, U32>>,
  +now: Nat
) -> Fasts.Fast:
  +name = Raw.name(Fasts.Fast.raw(g))
  Fasts.Fast.does(
    Fasts.Fast.does(
      Fasts.Fast.does(g, Nodes.Act.Connect{name}),
      Nodes.Act.Ask{
        Ledgers.Id{name, "save " ++ q ++ " " ++ Nat.show(now)},
        Spec.Request.Write{c, q, m}
      }
    ),
    Nodes.Act.Leave{name}
  )

# the key of the file x of the folder d
def Seen.key(d: String, x: String) -> List<&2, U32>:
  Codes.Code.text(d, Codes.Code.text(x, []))

# the set of the files fs
def Seen.set(fs: List<&2, Seen>, acc: Crits.Crit<Unit>) -> Crits.Crit<Unit>:
  match fs:
    case Nil{}:
      acc
    case Con{Seen{d, x}, rest}:
      Seen.set(rest, Crits.Crit.set(~Unit, acc, Seen.key(d, x), Unit{}))

# the fast node f after it mounts the resource at the address r, which holds
# the words ws, at the path q of the line c, unless it saw it before (seen):
# a mount records the words as a request, and a request is taken in again
# each time, so a resource is mounted once; the node keeps its mounts in the
# file mounts (Mounts.raw)
def Mount.new(
  seen: Bool,
  +f: Fasts.Fast,
  +r: String,
  +c: Ledgers.Line,
  +q: String,
  +ws: List<&2, U32>
) -> Fasts.Fast:
  match seen:
    case True{}:
      f
    case False{}:
      Fasts.Fast.does(f, Nodes.Act.Mount{r, c, q, ws})

# the fast node f after it reads the file at the path x of the folder d,
# mounted at the path p of the line c, which holds the words ws at the time
# now: it mounts it unless it saw it before (old is the set of the files
# seen), and writes it when it does not show those words
def Mount.file(
  +old: Crits.Crit<Unit>,
  +f: Fasts.Fast,
  +d: String,
  +c: Ledgers.Line,
  +p: String,
  +x: String,
  +ws: List<&2, U32>,
  +now: Nat
) -> Fasts.Fast:
  +r = Path.at(d, x)
  +q = Mount.path(p, x)
  +g = Mount.new(Crits.Crit.has(Unit, old, Seen.key(d, x)), f, r, c, q, ws)
  Shared.Bool.when(
    Fasts.Fast,
    Mount.shows(Fasts.Fast.view(g, Raw.name(Fasts.Fast.raw(g)), c, q), ws),
    u => g,
    u => Mount.save(g, c, q, Some{ws}, now)
  )

# what a read of the mounted files gives: the node, and the files it saw
type Scanned is Data:
  Scanned{fast: Fasts.Fast, seen: List<&2, Seen>}

# the paths that the output r of find lists; none when it failed
def Dir.listed(r: Result<&1, &1, String, String>) -> Result<&1, &1, String, List<&2, String>>:
  match r:
    case Fail{e}:
      Done{[]}
    case Done{out}:
      Done{List.filter(~String, ~(x => Bool.not(String.is_empty(x))), String.lines(out))}

# the files in the folder d, each by its path in it; none when it is not
# there
def Dir.files(+d: String) -> Disk.Run(List<&2, String>):
  IO.bind(
    Result<&1, &1, String, String>,
    Result<&1, &1, String, List<&2, String>>,
    Disk.Program.run("find", [d, "-type", "f", "-printf", "%P\n"]),
    r => IO.pure(Result<&1, &1, String, List<&2, String>>, Dir.listed(r))
  )

# what the node has after it reads the files xs of the folder d, mounted at
# the path p of the line c, at the time now, after what it had (acc)
def Scan.files(
  xs: List<&2, String>,
  +old: Crits.Crit<Unit>,
  +d: String,
  +c: Ledgers.Line,
  +p: String,
  +now: Nat,
  acc: Scanned
) -> Disk.Run(Scanned):
  match xs acc:
    case Nil{} a2:
      Disk.Run.pure(Scanned, a2)
    case Con{+x, rest} Scanned{+f, seen}:
      do Disk.Run<Scanned>:
        ws: List<&2, U32> <- Disk.Disk.read(Path.at(d, x))
        Scan.files(
          rest,
          old,
          d,
          c,
          p,
          now,
          Scanned{Mount.file(old, f, d, c, p, x, ws, now), Seen{d, x} <> seen}
        )

# what the node has after it reads the files of the mounted folders ds at
# the time now, after what it had (acc)
def Scan.dirs(
  ds: List<&2, Mount>,
  +old: Crits.Crit<Unit>,
  +now: Nat,
  acc: Scanned
) -> Disk.Run(Scanned):
  match ds:
    case Nil{}:
      Disk.Run.pure(Scanned, acc)
    case Con{Mount{+d, +c, +p}, rest}:
      do Disk.Run<Scanned>:
        xs: List<&2, String> <- Dir.files(d)
        b: Scanned <- Scan.files(xs, old, d, c, p, now, acc)
        Scan.dirs(rest, old, now, b)

# the resource that the file x of the folder d is, before rest, if m is the
# mount of the folder
def Mounts.resource(
  m: Maybe<&2, Mount>,
  +d: String,
  +x: String,
  rest: List<&2, Nodes.Mounted>
) -> List<&2, Nodes.Mounted>:
  match m:
    case None{}:
      rest
    case Some{Mount{e, c, p}}:
      Nodes.Mounted{Path.at(d, x), c, Mount.path(p, x)} <> rest

# the first of the mounts ms, if any
def Mounts.first(ms: List<&2, Mount>) -> Maybe<&2, Mount>:
  match ms:
    case Nil{}:
      None{}
    case Con{m, rest}:
      Some{m}

# the fast node g after it unmounted the file x at the address r, where m is
# the mount of its folder, if it is still mounted: the node writes none at
# its path if it shows words there
def Gone.at(m: Maybe<&2, Mount>, +g: Fasts.Fast, +r: String, +x: String, +now: Nat) -> Fasts.Fast:
  match m:
    case None{}:
      g
    case Some{Mount{e, +c, +p}}:
      +q = Mount.path(p, x)
      Shared.Bool.when(
        Fasts.Fast,
        Mount.holds(Fasts.Fast.view(g, Raw.name(Fasts.Fast.raw(g)), c, q)),
        u => Mount.save(g, c, q, None{}, now),
        u => g
      )

# the fast node f after the file x of the folder d is gone, where m is the
# mount of the folder, if it is still mounted
def Gone.file(+f: Fasts.Fast, +d: String, +x: String, m: Maybe<&2, Mount>, +now: Nat) -> Fasts.Fast:
  +r = Path.at(d, x)
  Gone.at(m, Fasts.Fast.does(f, Nodes.Act.Unmount{r}), r, x, now)

# the fast node f after each of the files fs that the set now does not hold
# is gone, where ds are the mounted folders
def Gone.files(
  fs: List<&2, Seen>,
  +ds: List<&2, Mount>,
  +now: Crits.Crit<Unit>,
  +t: Nat,
  +f: Fasts.Fast
) -> Fasts.Fast:
  match fs:
    case Nil{}:
      f
    case Con{Seen{+d, +x}, rest}:
      Gone.files(
        rest,
        ds,
        now,
        t,
        Shared.Bool.when(
          Fasts.Fast,
          Crits.Crit.has(Unit, now, Seen.key(d, x)),
          u => f,
          u => Gone.file(f, d, x, Mounts.first(Mounts.keep(ds, d, True{})), t)
        )
      )

# the node after the files of the earlier read fs that the read b did not
# see are gone, where ds are the mounted folders
def Mounts.gone(
  +ds: List<&2, Mount>,
  fs: List<&2, Seen>,
  +now: Nat,
  b: Scanned
) -> Disk.Run(Scanned):
  match b:
    case Scanned{g, +seen}:
      Disk.Run.pure(
        Scanned,
        Scanned{Gone.files(fs, ds, Seen.set(seen, Crits.Crit.new(Unit)), now, g), seen}
      )

# the node f and the mounts ms after the node reads the mounted files at the
# time now
def Mounts.scan(+now: Nat, ms: Mounts, +f: Fasts.Fast) -> Disk.Run(Scanned):
  match ms:
    case Mounts{+ds, +fs}:
      do Disk.Run<Scanned>:
        b: Scanned <- Scan.dirs(ds, Seen.set(fs, Crits.Crit.new(Unit)), now, Scanned{f, []})
        Mounts.gone(ds, fs, now, b)

# the resources that the files fs of the mounted folders ds are, as the
# node keeps them
def Mounts.resources(fs: List<&2, Seen>, +ds: List<&2, Mount>) -> List<&2, Nodes.Mounted>:
  match fs:
    case Nil{}:
      []
    case Con{Seen{+d, +x}, rest}:
      Mounts.resource(Mounts.first(Mounts.keep(ds, d, True{})), d, x, Mounts.resources(rest, ds))

# the node r with the mounts ms: the resources that its mounted folders held
# when it last read them
def Mounts.raw(r: Nodes.Raw, ms: Mounts) -> Nodes.Raw:
  match r ms:
    case Nodes.Raw{n, ws, xs, st, fs, ps} Mounts{+ds, files}:
      Nodes.Raw{n, ws, Mounts.resources(files, ds), st, fs, ps}

# the mounts ms with the files seen
def Mounts.with(ms: Mounts, seen: List<&2, Seen>) -> Mounts:
  match ms:
    case Mounts{ds, fs}:
      Mounts{ds, seen}

# the output r of a program; none when it failed
def Dir.out(r: Result<&1, &1, String, String>) -> Result<&1, &1, String, String>:
  match r:
    case Fail{e}:
      Done{""}
    case Done{out}:
      Done{out}

# the sizes and times of the files of the mounted folders ds, as text: what
# a node that serves compares, so that it reads the files only after one
# changed
def Mounts.listing(ds: List<&2, Mount>) -> Disk.Run(String):
  match ds:
    case Nil{}:
      Disk.Run.pure(String, "")
    case Con{Mount{+d, c, p}, rest}:
      do Disk.Run<String>:
        out: String <- IO.bind(
          Result<&1, &1, String, String>,
          Result<&1, &1, String, String>,
          Disk.Program.run("find", [d, "-type", "f", "-printf", "%P %s %T@\n"]),
          r => IO.pure(Result<&1, &1, String, String>, Dir.out(r))
        )
        more: String <- Mounts.listing(rest)
        return d ++ "\n" ++ out ++ more

# A command
# ---------

# the words of the file at the path at; none for "--delete"
def Words.load(+at: String) -> Disk.Run(Maybe<&2, List<&2, U32>>):
  match at:
    case "--delete":
      Disk.Run.pure(Maybe<&2, List<&2, U32>>, None{})
    case _:
      do Disk.Run<Maybe<&2, List<&2, U32>>>:
        ws: List<&2, U32> <- Disk.Disk.read(at)
        return Some{ws}

# the fast node f after it takes in what the node at a holds: over TCP when
# a is a TCP address (m), else from the data address a
def Sync.from(+a: String, m: Maybe<&2, Tcp>, +f: Fasts.Fast) -> Disk.Run(Fasts.Fast):
  match m:
    case Some{t}:
      Tcp.connect(Fasts.Fast, t, s => Client.session(s, f))
    case None{}:
      do Disk.Run<Fasts.Fast>:
        k: Stored <- Node.load(a)
        return Fasts.Fast.does(f, Nodes.Act.Sync{Stored.node(k)})

# the fast node f, after the deeds of the command c of the writer w
def Cmd.does(+w: String, c: Cmd, +f: Fasts.Fast) -> Disk.Run(Fasts.Fast):
  match c:
    case Cmd.Ask{i, q}:
      Disk.Run.pure(Fasts.Fast, Fasts.Fast.does(f, Nodes.Act.Ask{i, q}))
    case Cmd.Put{i, b, p, at}:
      do Disk.Run<Fasts.Fast>:
        m: Maybe<&2, List<&2, U32>> <- Words.load(at)
        return Fasts.Fast.does(f, Nodes.Act.Ask{i, Spec.Request.Write{b, p, m}})
    case Cmd.Fix{i, x, p, at}:
      do Disk.Run<Fasts.Fast>:
        m: Maybe<&2, List<&2, U32>> <- Words.load(at)
        return Fasts.Fast.does(f, Nodes.Act.Ask{i, Spec.Request.Resolve{x, p, m}})
    case Cmd.Sync{+a}:
      Sync.from(a, Tcp.read(a), f)
    case Cmd.Drop{}:
      Disk.Run.pure(Fasts.Fast, Fasts.Fast.does(f, Nodes.Act.Drop{}))
    case Cmd.Stop{force}:
      Disk.Run.pure(
        Fasts.Fast,
        Fasts.Fast.does(Fasts.Fast.does(f, Nodes.Act.Leave{w}), Nodes.Act.Stop{force})
      )
    case _:
      Disk.Run.pure(Fasts.Fast, f)

# the line whose status says what became of the request r of the id i, where
# m is the line that the core reads for r: a start is for its store
def Ask.line(m: Maybe<&2, Ledgers.Line>, i: Ledgers.Id, r: Spec.Request) -> Maybe<&2, Ledgers.Line>:
  match m r:
    case Some{c} _:
      Some{c}
    case None{} Spec.Request.Start{os}:
      Some{Ledgers.Line{Facts.Start.root(i, Spec.Request.Start{os}), None{}}}
    case None{} _:
      None{}

# what became of the request of the id i, whose line is m, at the node f
def Ask.status(+f: Fasts.Fast, +i: Ledgers.Id, m: Maybe<&2, Ledgers.Line>) -> String:
  match m:
    case None{}:
      Id.show(i) ++ ": pending (its line is not known yet)"
    case Some{+c}:
      Id.show(
        i
      )
        ++ ": "
        ++ Answer.show(Spec.Question.Status{c, i}, Fasts.Fast.answer(f, Spec.Question.Status{c, i}))
        ++ " on "
        ++ Line.show(c)

# what became of the request r of the id i at the node f
def Ask.reply(+f: Fasts.Fast, +i: Ledgers.Id, +r: Spec.Request) -> String:
  Ask.status(
    f,
    i,
    Ask.line(Works.Request.line(Fasts.Fast.lines(f), Facts.Facts.list(Node.facts(f)), r), i, r)
  )

# how many facts and parts the node f holds, and how many facts are new since f0
def Node.summary(+f0: Fasts.Fast, +f: Fasts.Fast) -> String:
  Nat.show(
    Node.size(f)
  )
    ++ " facts ("
    ++ Nat.show(Nat.sub(Node.size(f), Node.size(f0)))
    ++ " new), "
    ++ Nat.show(Crits.Crit.size(List<&2, U32>, Node.kept(f)))
    ++ " parts"

# whether the node r has stopped, as text
def Stop.show(b: Bool) -> String:
  match b:
    case True{}:
      "stopped"
    case False{}:
      "running: a writer is connected or a resource is mounted"

# the reply to the command c of the writer w at the node f, which was f0
# when it resumed
def Cmd.reply(+w: String, c: Cmd, +f0: Fasts.Fast, +f: Fasts.Fast) -> String:
  match c:
    case Cmd.Ask{i, q}:
      Ask.reply(f, i, q)
    case Cmd.Put{i, b, p, at}:
      Ask.reply(f, i, Spec.Request.Write{b, p, None{}})
    case Cmd.Fix{i, x, p, at}:
      Ask.reply(f, i, Spec.Request.Resolve{x, p, None{}})
    case Cmd.Answer{+q}:
      Answer.show(q, Fasts.Fast.answer(f, q))
    case Cmd.Read{x, k, p}:
      Content.show(Fasts.Fast.read(f, x, k, p))
    case Cmd.View{b, p}:
      Content.show(Fasts.Fast.view(f, w, b, p))
    case Cmd.Stop{force}:
      Stop.show(Raw.stopped(Fasts.Fast.raw(f)))
    case Cmd.Liars{}:
      Names.show(Fasts.Fast.liars(f))
    case _:
      Node.summary(f0, f)

# the reply to the command c of the writer w at the node f, which was f0
# when it resumed with the log l, after the data address a keeps f and the
# mounts ms
def Node.done(
  +a: String,
  +w: String,
  +c: Cmd,
  +l: Log,
  ms: Mounts,
  +f0: Fasts.Fast,
  +f: Fasts.Fast
) -> Disk.Run(String):
  do Disk.Run<String>:
    l2: Log <- Node.save(a, l, f0, f)
    Mounts.save(a, ms)
    return Cmd.reply(w, c, f0, f)

# Node.resumed, once the node read its mounted files (b)
def Node.scanned(
  +a: String,
  +w: String,
  +c: Cmd,
  +l: Log,
  ms: Mounts,
  +f0: Fasts.Fast,
  b: Scanned
) -> Disk.Run(String):
  match b:
    case Scanned{f1, seen}:
      do Disk.Run<String>:
        f2: Fasts.Fast <- Cmd.does(w, c, Fasts.Fast.does(f1, Nodes.Act.Connect{w}))
        Node.done(
          a,
          w,
          c,
          l,
          Mounts.with(ms, seen),
          f0,
          Fasts.Fast.does(Node.settle(256n, False{}, f2), Nodes.Act.Leave{w})
        )

# the reply to the command c of the writer w, at the data address a where
# the node f0 resumed with the log l and the mounts ms: the node reads its
# mounted files, the writer connects, the command does its deeds, the node
# works until a work adds no fact (at most 256 works), the writer leaves,
# and the new facts and parts are kept
def Node.resumed(
  +a: String,
  +w: String,
  +c: Cmd,
  +l: Log,
  +ms: Mounts,
  +f0: Fasts.Fast
) -> Disk.Run(String):
  do Disk.Run<String>:
    now: Nat <- Disk.Run.io(Nat, IO.now())
    b: Scanned <- Mounts.scan(now, ms, f0)
    Node.scanned(a, w, c, l, ms, f0, b)

# the reply to the command c of the writer w, at the data address a that
# keeps k and the mounts ms
def Node.ran(+a: String, +w: String, +c: Cmd, +ms: Mounts, k: Stored) -> Disk.Run(String):
  match k:
    case Stored{r, +l}:
      Disk.Run.bind(
        Fasts.Fast,
        String,
        Node.resume(a, Mounts.raw(r, ms)),
        f0 => Node.resumed(a, w, c, l, ms, f0)
      )

# the reply to the command c of the writer w, at the data address a, while
# the node holds its lock; a mount or an unmount changes the mounts first
def Node.run(+a: String, +w: String, +c: Cmd) -> Disk.Run(String):
  Node.locked(
    String,
    a,
    do Disk.Run<String>:
      k: Stored <- Node.load(a)
      ms: Mounts <- Mounts.load(a)
      Node.ran(a, w, c, Mounts.change(c, ms), k))

# A node that serves
# ------------------
# vend <address> serve [<host>:]<port>: the node holds the lock of its
# address and runs. It waits for a session at most Serve.poll_ms at a time;
# it answers each session, and between them it reads the sizes and times of
# its mounted files, and reads the files when they changed. After each, it
# works until a work adds no fact, and keeps its facts, parts and mounts: it
# catches up by itself. A stop session stops it once it can stop (no writer,
# no mount, or forced). It listens on 127.0.0.1 unless a host is given.

# how long a node that serves waits for a session before it reads its
# mounts again, in milliseconds
def Serve.poll_ms() -> U32:
  500

# what a node that serves holds between sessions: its log, the node, its
# mounts, and the sizes and times of its mounted files when it last read
# them
type Held is Data:
  Held{log: Log, fast: Fasts.Fast, mounts: Mounts, listing: String}

# what a session did: the node after it, and whether it stopped
type Session is Data:
  Session{fast: Fasts.Fast, stopped: Bool}

# what the client of a session asks first: a sync (0) or a stop, and its
# summary
type Hello is Data:
  Hello{kind: Nat, summary: Summary}

# what a client asks first
def Hello.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Hello>>:
  Codes.Code.two.read(
    ~Nat,
    ~Summary,
    ~Hello,
    ~Codes.Code.count.read,
    ~Summary.read,
    a => b => Hello{a, b},
    ts
  )

# the session on the socket s of the node f that serves, after the client
# asked h
def Serve.hello(s: Socket, +f: Fasts.Fast, h: Hello) -> Disk.Sock(Session):
  match h:
    case Hello{0n, x}:
      Disk.Sock.bind(
        Unit,
        Session,
        Wire.send(s, Served.code(Served{Wire.offer(f, x), Wire.summary(f)}, [])),
        t => u => Disk.Sock.bind(
          Offer,
          Session,
          Wire.recv(~Offer, ~Offer.read, t),
          t2 => o => Disk.Sock.pure(Session, t2, Session{Wire.take(f, o), False{}})
        )
      )
    case Hello{1n+k, x}:
      +g = Fasts.Fast.does(f, Nodes.Act.Stop{Bool.not(Nat.is_eq(k, 0n))})
      +st = Raw.stopped(Fasts.Fast.raw(g))
      Disk.Sock.bind(
        Unit,
        Session,
        Wire.send(s, Codes.Code.count(Bool.pick(Nat, st, 1n, 0n), [])),
        t => u => Disk.Sock.pure(Session, t, Session{g, st})
      )

# a session of the node f that serves, on the socket s
def Serve.session(s: Socket, +f: Fasts.Fast) -> Disk.Sock(Session):
  Disk.Sock.bind(Hello, Session, Wire.recv(~Hello, ~Hello.read, s), t => h => Serve.hello(t, f, h))

# what the node that serves holds after it worked on the node g and kept it
# at the data address a, where h is what it held before; and whether it
# stops (st)
def Serve.keep(+a: String, h: Held, +g: Fasts.Fast, +st: Bool) -> Disk.Run(Maybe<&2, Held>):
  match h:
    case Held{+l, +f, +ms, +ls}:
      +g2 = Node.settle(256n, False{}, g)
      do Disk.Run<Maybe<&2, Held>>:
        l2: Log <- Node.save(a, l, f, g2)
        Mounts.save(a, ms)
        return Bool.pick(Maybe<&2, Held>, st, None{}, Some{Held{l2, g2, ms, ls}})

# what the node that serves holds after a session answered r, where h is
# what it held before: a session that failed changes nothing
def Serve.answered(
  +a: String,
  +h: Held,
  r: Result<&1, &1, String, Session>
) -> Disk.Run(Maybe<&2, Held>):
  match r:
    case Fail{e}:
      do Disk.Run<Maybe<&2, Held>>:
        Disk.Run.io(Unit, IO.print_err("a session failed: " ++ e))
        return Some{h}
    case Done{Session{g, st}}:
      Serve.keep(a, h, g, st)

# the fast node of what a node that serves holds
def Held.fast(h: Held) -> Fasts.Fast:
  match h:
    case Held{l, f, ms, ls}:
      f

# what the node that serves holds after a session on the socket s, where h
# is what it held before
def Serve.met(+a: String, +h: Held, s: Socket) -> Disk.Run(Maybe<&2, Held>):
  IO.bind(
    Result<&1, &1, String, Session>,
    Result<&1, &1, String, Maybe<&2, Held>>,
    Disk.Sock.close(Session, Serve.session(s, Held.fast(h))),
    r => Serve.answered(a, h, r)
  )

# Serve.read, once the node read its mounted files (b)
def Serve.scanned(+a: String, h: Held, b: Scanned) -> Disk.Run(Maybe<&2, Held>):
  match h b:
    case Held{l, f, ms, ls} Scanned{g, seen}:
      Serve.keep(a, Held{l, f, Mounts.with(ms, seen), ls}, g, False{})

# what the node that serves holds after it read its mounted files, where h
# is what it held before and ls the sizes and times of the files now
def Serve.read(+a: String, h: Held, +ls: String) -> Disk.Run(Maybe<&2, Held>):
  match h:
    case Held{+l, +f, +ms, +old}:
      Shared.Bool.when(
        Disk.Run(Maybe<&2, Held>),
        String.eq(old, ls),
        u => Disk.Run.pure(Maybe<&2, Held>, Some{Held{l, f, ms, old}}),
        u => do Disk.Run<Maybe<&2, Held>>:
          now: Nat <- Disk.Run.io(Nat, IO.now())
          b: Scanned <- Mounts.scan(now, ms, f)
          Serve.scanned(a, Held{l, f, ms, ls}, b))

# what the node that serves holds after a tick with no session, where h is
# what it held before
def Serve.tick(+a: String, h: Held) -> Disk.Run(Maybe<&2, Held>):
  match h:
    case Held{l, f, Mounts{+ds, fs}, ls}:
      Disk.Run.bind(
        String,
        Maybe<&2, Held>,
        Mounts.listing(ds),
        x => Serve.read(a, Held{l, f, Mounts{ds, fs}, ls}, x)
      )

# what the listener li does with an accept that answered r: a session, or a
# tick when none came in time
def Serve.polled(
  li: Listener,
  r: Poll<&1, &1, Result<&1, &1, U32 & String, Socket>, Unit>,
  session: Listener -> Socket -> IO(Result<&1, &1, String, String>),
  tick: Listener -> IO(Result<&1, &1, String, String>)
) -> IO(Result<&1, &1, String, String>):
  match r:
    case Wait{u}:
      tick(li)
    case Ready{Fail{(code, msg)}}:
      IO.bind(Unit, Result<&1, &1, String, String>, IO.print_err("accept: " ++ msg), u => tick(li))
    case Ready{Done{s}}:
      session(li)(s)

# the listener li closed, and what the node that serves ends with, from the
# step r: the end when it stopped (none), else what next does with what it
# holds
def Serve.next(
  li: Listener,
  r: Result<&1, &1, String, Maybe<&2, Held>>,
  next: Listener -> Held -> IO(Result<&1, &1, String, String>)
) -> IO(Result<&1, &1, String, String>):
  match r:
    case Fail{e}:
      IO.bind(
        Unit,
        Result<&1, &1, String, String>,
        Listener.close(li),
        u => IO.pure(Result<&1, &1, String, String>, Fail{e})
      )
    case Done{None{}}:
      IO.bind(
        Unit,
        Result<&1, &1, String, String>,
        Listener.close(li),
        u => IO.pure(Result<&1, &1, String, String>, Done{"stopped"})
      )
    case Done{Some{h}}:
      next(li)(h)

# the node that serves, holding h at the data address a, listening on li,
# for at most o times 65536 and i more polls
def Serve.loop(
  +o: Nat,
  i: Nat,
  +a: String,
  +h: Held,
  li: Listener
) -> IO(Result<&1, &1, String, String>):
  match o i:
    case 0n 0n:
      IO.bind(
        Unit,
        Result<&1, &1, String, String>,
        Listener.close(li),
        u => IO.pure(Result<&1, &1, String, String>, Done{"stopped: it served as long as it may"})
      )
    case 1n+p 0n:
      Serve.loop(p, 65535n, a, h, li)
    case _ 1n+q:
      +q = q
      IO.bind(
        Listener & Poll<&1, &1, Result<&1, &1, U32 & String, Socket>, Unit>,
        Result<&1, &1, String, String>,
        TCP.try_accept(li, Serve.poll_ms()),
        x => Disk.Pair.on(
          Listener,
          Poll<&1, &1, Result<&1, &1, U32 & String, Socket>, Unit>,
          IO(Result<&1, &1, String, String>),
          x,
          li2 => r => Serve.polled(
            li2,
            r,
            li3 => s => IO.bind(
              Result<&1, &1, String, Maybe<&2, Held>>,
              Result<&1, &1, String, String>,
              Serve.met(a, h, s),
              m => Serve.next(li3, m, li4 => h2 => Serve.loop(o, q, a, h2, li4))
            ),
            li3 => IO.bind(
              Result<&1, &1, String, Maybe<&2, Held>>,
              Result<&1, &1, String, String>,
              Serve.tick(a, h),
              m => Serve.next(li3, m, li4 => h2 => Serve.loop(o, q, a, h2, li4))
            )
          )
        )
      )

# the node that serves, holding h at the data address a, once it listens on
# li at the address t
def Serve.listening(
  +a: String,
  +t: String,
  +h: Held,
  li: Listener
) -> IO(Result<&1, &1, String, String>):
  IO.bind(
    Unit,
    Result<&1, &1, String, String>,
    IO.print("node " ++ Raw.name(Fasts.Fast.raw(Held.fast(h))) ++ " serves on " ++ t),
    u => Serve.loop(65535n, 65535n, a, h, li)
  )

# the node that serves at the data address a, at the TCP address t, from
# what it holds (h)
def Serve.listen(+a: String, t: Tcp, +h: Held) -> Disk.Run(String):
  match t:
    case Tcp{+host, +port}:
      Disk.Run.bind(
        Listener,
        String,
        Disk.Run.sys(
          Listener,
          "listen on " ++ host ++ ":" ++ U32.show(port),
          TCP.listen(host, port)
        ),
        li => Serve.listening(a, host ++ ":" ++ U32.show(port), h, li)
      )

# the node that serves at the data address a that keeps k and the mounts
# ms, at the TCP address t
def Serve.ran(+a: String, +t: Tcp, +ms: Mounts, k: Stored) -> Disk.Run(String):
  match k:
    case Stored{r, +l}:
      Disk.Run.bind(
        Fasts.Fast,
        String,
        Node.resume(a, Mounts.raw(r, ms)),
        f0 => Serve.listen(a, t, Held{l, f0, ms, ""})
      )

# the node that serves at the data address a, at the TCP address t, while it
# holds the lock
def Serve.run(+a: String, +t: Tcp) -> Disk.Run(String):
  Node.locked(
    String,
    a,
    do Disk.Run<String>:
      k: Stored <- Node.load(a)
      ms: Mounts <- Mounts.load(a)
      Serve.ran(a, t, ms, k))

# the TCP address that [<host>:]<port> names
def Serve.at(ps: List<&2, String>) -> Maybe<&2, Tcp>:
  match ps:
    case Con{p, Nil{}}:
      Maybe.bind(&2, U32, Tcp, U32.read(p), n => Some{Tcp{"127.0.0.1", n}})
    case Con{h, Con{p, Nil{}}}:
      Maybe.bind(&2, U32, Tcp, U32.read(p), n => Some{Tcp{h, n}})
    case _:
      None{}

# a stop sent to the node that serves at the TCP address t, as the reply it
# gives (whether it stopped)
def Remote.stop(t: Tcp, +force: Bool) -> Disk.Run(String):
  Tcp.connect(
    String,
    t,
    s => Disk.Sock.bind(
      Unit,
      String,
      Wire.send(
        s,
        Codes.Code.count(Bool.pick(Nat, force, 2n, 1n), Summary.code(Summary{[], []}, []))
      ),
      t2 => u => Disk.Sock.bind(
        Nat,
        String,
        Wire.recv(~Nat, ~Codes.Code.count.read, t2),
        t3 => n => Disk.Sock.pure(String, t3, Stop.show(Bool.not(Nat.is_eq(n, 0n))))
      )
    )
  )

# a new node of the name n on the new data address a: its directory, its
# name, no facts and no parts. A reserved name is no node's
def Node.init.if(reserved: Bool, +a: String, +n: String) -> Disk.Run(String):
  match reserved:
    case True{}:
      Disk.Run.fail(String, "the name " ++ n ++ " is reserved: it starts with '~'")
    case False{}:
      do Disk.Run<String>:
        Disk.Disk.make_dir(a)
        Disk.Disk.make_dir(Path.at(a, "parts"))
        Disk.Disk.write(Path.at(a, "name"), "x", Texts.Bytes.of_text(n))
        Disk.Disk.write(Path.at(a, "facts"), "x", Disk.Short.bytes(Log.head(), []))
        return "node " ++ n ++ " starts on " ++ a

# a new node of the name n on the new data address a
def Node.init(+a: String, +n: String) -> Disk.Run(String):
  Node.init.if(Facts.Trust.reserved(n), a, n)

# Main
# ----

# how to call vend
def Main.usage() -> String:
  String.join(
    [
      "usage: vend <address> init <node name>",
      "       vend <address> <writer> <command>",
      "commands (a line is <store hash>[:<branch>]; an id is [<writer>/]<request id>):",
      "  start <id> <owner node>...           a new store",
      "  write <id> <line> <path> <file>      the words of a file (--delete: none)",
      "  merge <id> <from line> <into line>",
      "  resolve <id> <merge id> <path> <file>",
      "  mark <id> <line> <name> <version>",
      "  move <id> <line> <to line> <version>",
      "  group <id> <store hash> <name> <member>...",
      "  own <id> <line> <group>",
      "  status <line> <id>",
      "  affects <line> <from> <to> <uses,..|-> <build,..|->",
      "  answer <question> <args>             status request clashes base <line> <id>;",
      "                                       version content group owners parents owner era <line> <n>;",
      "                                       mark <line> <name>; count <line>; affects ...;",
      "                                       members nodes is-group <store hash> <group> <n>",
      "  read <line> <version> <path>",
      "  view <line> <path>",
      "  work | drop | liars | stop [--force]",
      "  sync <other address>|tcp:<host>:<port>  take in what the node there holds, and give it what it lacks over TCP",
      "  mount <folder> <line> <path> | unmount <folder>   each save of a file in the folder becomes a version",
      "       vend <address> serve [<host>:]<port>   run: answer syncs, read the mounts, work, keep",
      "       vend tcp:<host>:<port> <writer> stop [--force]"
    ],
    "\n"
  )

# the command that the words m give, run by the writer w at the data address a
def Main.cmd(+a: String, +w: String, m: Maybe<&2, Cmd>) -> Disk.Run(String):
  match m:
    case None{}:
      Disk.Run.fail(String, Main.usage())
    case Some{c}:
      Node.run(a, w, c)

# the node at the data address a serving at the TCP address m, if it reads
def Main.serve(+a: String, m: Maybe<&2, Tcp>) -> Disk.Run(String):
  match m:
    case None{}:
      Disk.Run.fail(String, Main.usage())
    case Some{t}:
      Serve.run(a, t)

# the command ws of the writer w at a, which is a data address, or the TCP
# address of a node that serves (m): only a stop goes to such a node
def Main.to(+a: String, m: Maybe<&2, Tcp>, +w: String, ws: List<&2, String>) -> Disk.Run(String):
  match m ws:
    case Some{t} Con{"stop", Nil{}}:
      Remote.stop(t, False{})
    case Some{t} Con{"stop", Con{"--force", Nil{}}}:
      Remote.stop(t, True{})
    case Some{t} _:
      Disk.Run.fail(
        String,
        "a node that serves takes a stop only (vend tcp:<host>:<port> <writer> stop)"
      )
    case None{} rest:
      Main.cmd(a, w, Cmd.read(w, rest))

# what the command line ws asks for, after the name of the program
def Main.go(ws: List<&2, String>) -> Disk.Run(String):
  match ws:
    case Con{x, Con{a, Con{"init", Con{n, Nil{}}}}}:
      Node.init(a, n)
    case Con{x, Con{+a, Con{"serve", Con{t, Nil{}}}}}:
      Main.serve(a, Serve.at(String.split(t, ':')))
    case Con{x, Con{+a, Con{+w, rest}}}:
      Main.to(a, Tcp.read(a), w, rest)
    case _:
      Disk.Run.fail(String, Main.usage())

# the words xs, as words that can be read more than once
def Main.args(xs: List<&1, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      []
    case Con{x, rest}:
      x <> Main.args(rest)

# the end of a run: its reply printed, or its message and the status 1
def Main.ended(r: Result<&1, &1, String, String>) -> IO(Unit):
  match r:
    case Done{t}:
      IO.print(t)
    case Fail{e}:
      IO.die(Unit, 1, e)

def main() -> IO(Unit):
  do IO<Unit>:
    xs: List<&1, String> <- IO.args()
    r: Result<&1, &1, String, String> <- Main.go(Main.args(xs))
    Main.ended(r)
