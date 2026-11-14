import Base
import ./shared/disk.bend as Disk
import ./shared/shared/ledger.bend as Ledgers
import ./shared/shared/shared/shared/code.bend as Codes
import ./shared/shared/shared/shared/crit.bend as Crits
import ./shared/shared/shared/shared/hash.bend as Hashes
import ./shared/shared/shared/text.bend as Texts
import ./vend_node/codes.bend as Coded
import ./vend_node/impl.bend as Impl
import ./vend_node/node.bend as Nodes
import ./vend_node/run/facts.bend as Facts
import ./vend_node/run/fast.bend as Fasts
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
    case _:
      None{}

# The state on disk
# -----------------

# the path of the file named f in the directory d
def Path.at(d: String, f: String) -> String:
  d ++ "/" ++ f

# what a read of the facts of a log found next
type Next is Data:
  Next.End{}
  Next.Bad{}
  Next.Got{fact: Types.Fact, rest: List<&2, U32>}

# what the read m of a fact found
def Next.of(m: Maybe<&2, Codes.Read<Types.Fact>>) -> Next:
  match m:
    case None{}:
      Next.Bad{}
    case Some{Codes.Read{f, r}}:
      Next.Got{f, r}

# the first fact of the words ws, if any
def Next.read(ws: List<&2, U32>) -> Next:
  match ws:
    case Nil{}:
      Next.End{}
    case Con{x, r}:
      Next.of(Coded.Fact.code.read.of(x, r))

# the facts s with the fact that x found and those after it, read in at most
# n reads; the file at the path at holds them
def Log.go(at: String, n: Nat, x: Next, s: Facts.Plain()) -> Result<&1, &1, String, Facts.Plain()>:
  match n x:
    case _ Next.End{}:
      Done{s}
    case 1n+p Next.Got{f, r}:
      Log.go(at, p, Next.read(r), Facts.Facts.add(s, f))
    case _ _:
      Fail{at ++ ": a fact does not read; the end of the log is damaged"}

# the facts that the words ws of the file at the path at hold
def Log.read(at: String, +ws: List<&2, U32>) -> Result<&1, &1, String, Facts.Plain()>:
  Log.go(at, List.length(&2, U32, ws), Next.read(ws), Facts.Facts.new())

# the code of the fact f, then rest, unless the facts held it (held)
def Log.put(held: Bool, f: Types.Fact, rest: List<&2, U32>) -> List<&2, U32>:
  match held:
    case True{}:
      rest
    case False{}:
      Coded.Fact.code(f, rest)

# the codes of the facts of the entries es that old does not hold, then rest
def Log.new(
  es: List<&2, Crits.Bind<Types.Fact>>,
  +old: Facts.Plain(),
  rest: List<&2, U32>
) -> List<&2, U32>:
  match es:
    case Nil{}:
      rest
    case Con{Crits.Bind{k, f}, more}:
      Log.put(Crits.Crit.has(Types.Fact, old, k), f, Log.new(more, old, rest))

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
        ws: List<&2, U32> <- Disk.Disk.words(Path.at(d, n))
        Kept.load(rest, d, Kept.add(n, ws, ps))

# the file at the path at written with the words ws, unless it is held
def Kept.write(held: Bool, at: String, ws: List<&2, U32>) -> Disk.Run(Unit):
  match held:
    case True{}:
      Disk.Run.pure(Unit, Unit{})
    case False{}:
      Disk.Disk.write(at, "w", Disk.Words.bytes(ws, []))

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

# the node that the data address a keeps: its name, its facts and its parts
def Node.load(+a: String) -> Disk.Run(Nodes.Raw):
  do Disk.Run<Nodes.Raw>:
    name: List<&2, U32> <- Disk.Disk.read(Path.at(a, "name"))
    ws: List<&2, U32> <- Disk.Disk.words(Path.at(a, "facts"))
    fs: Facts.Plain() <- Disk.Run.of(Facts.Plain(), Log.read(Path.at(a, "facts"), ws))
    ns: List<&2, String> <- Disk.Disk.names(Path.at(a, "parts"))
    ps: Parts.Parts <- Kept.load(ns, Path.at(a, "parts"), Parts.Parts.new())
    return Nodes.Raw{Texts.Bytes.to_text(name), [], [], False{}, fs, ps}

# the node r as a fast node: a new node of its name takes in what r holds
def Node.resume(+r: Nodes.Raw) -> Fasts.Fast:
  Fasts.Fast.does(Fasts.Fast.new(Raw.name(r)), Nodes.Act.Sync{r})

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

# the data address a, which kept the node f0, keeping the node f that f0
# became: the new parts first, then the new facts, then the parts that f let
# go of removed
def Node.save(+a: String, +f0: Fasts.Fast, +f: Fasts.Fast) -> Disk.Run(Unit):
  +d = Path.at(a, "parts")
  do Disk.Run<Unit>:
    Kept.save(Crits.Crit.entries(List<&2, U32>, Node.kept(f)), Node.kept(f0), d)
    Disk.Disk.write(
      Path.at(a, "facts"),
      "a",
      Disk.Words.bytes(
        Log.new(Crits.Crit.entries(Types.Fact, Node.facts(f)), Node.facts(f0), []),
        []
      )
    )
    Disk.Disk.remove(Kept.gone(Crits.Crit.entries(List<&2, U32>, Node.kept(f0)), Node.kept(f), d))

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
    case Cmd.Sync{a}:
      do Disk.Run<Fasts.Fast>:
        r: Nodes.Raw <- Node.load(a)
        return Fasts.Fast.does(f, Nodes.Act.Sync{r})
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
# when it resumed, after the data address a keeps f
def Node.done(+a: String, +w: String, +c: Cmd, +f0: Fasts.Fast, +f: Fasts.Fast) -> Disk.Run(String):
  do Disk.Run<String>:
    Node.save(a, f0, f)
    return Cmd.reply(w, c, f0, f)

# the reply to the command c of the writer w, at the data address a that
# kept the node r: the node resumes, the writer connects, the command does its deeds, the node works
# until a work adds no fact (at most 256 works), the writer leaves, and the
# new facts and parts are kept
def Node.ran(+a: String, +w: String, +c: Cmd, r: Nodes.Raw) -> Disk.Run(String):
  +f0 = Node.resume(r)
  do Disk.Run<String>:
    f1: Fasts.Fast <- Cmd.does(w, c, Fasts.Fast.does(f0, Nodes.Act.Connect{w}))
    Node.done(a, w, c, f0, Fasts.Fast.does(Node.settle(256n, False{}, f1), Nodes.Act.Leave{w}))

# the reply to the command c of the writer w, at the data address a, while
# the node holds its lock
def Node.run(+a: String, +w: String, +c: Cmd) -> Disk.Run(String):
  Node.locked(String, a, Disk.Run.bind(Nodes.Raw, String, Node.load(a), r => Node.ran(a, w, c, r)))

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
        Disk.Disk.write(Path.at(a, "facts"), "x", [])
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
      "  sync <other address>                 take in what the node there holds"
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

# what the command line ws asks for, after the name of the program
def Main.go(ws: List<&2, String>) -> Disk.Run(String):
  match ws:
    case Con{x, Con{a, Con{"init", Con{n, Nil{}}}}}:
      Node.init(a, n)
    case Con{x, Con{+a, Con{+w, rest}}}:
      Main.cmd(a, w, Cmd.read(w, rest))
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
