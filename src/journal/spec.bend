import Base
import ../hash/spec.bend as Hash
import ../history/spec.bend as History
import ../shared/bytes.bend as Octets
import ../shared/resources.bend as Resources
import ../store/spec.bend as Store
import ../views/text/spec.bend as Text

# The journal: the one append-only log of a user's versions. Power can go
# at any moment, so a version counts only once its record is on disk: the
# loop appends the records of a step, syncs the file, and only then reports
# the versions or touches an endpoint. On start, the loop reads the log,
# cuts a torn tail (the part of a record that a power cut left), and
# replays the records.

# Records
# -------

# One change of the state that a power cut must not lose.
# Kept: a version: the line it was kept on, its content (None for a version
# that says the file is gone), and its history node; replaying it puts the
# content in the store, the node in the history, and moves the line it names.
# Saw: the agent caught up with the line whose key (Lines.Line.id) is line,
# as that line is at this point of the journal.
# Marked: a mark named name of the line whose key is line, with its message
# and author, holding that line's heads at this point of the journal.
# Forked: a new line whose key is line, following what the line whose key is
# from followed at this point, or what its mark named by mark holds.
type Record is Data:
  Kept{line: String, content: Maybe<&2, Octets.Bytes()>, node: History.Node}
  Saw{agent: String, line: String}
  Marked{line: String, name: String, message: String, author: History.Author}
  Forked{line: String, from: String, mark: Maybe<&2, String>}

# the bytes of a text: its UTF-8, framed
def Utf8.framed(s: String) -> Octets.Bytes():
  Store.Bytes.framed(Text.Text.encode(s))

# the bytes of a content: 0 for none, or 1 then the content, framed
def Content.encode(c: Maybe<&2, Octets.Bytes()>) -> Octets.Bytes():
  match c:
    case None{}:
      [0]
    case Some{b}:
      1 <> Store.Bytes.framed(b)

# the bytes of a mark name of a fork: 0 for none, or 1 then the name
def MarkName.encode(m: Maybe<&2, String>) -> Octets.Bytes():
  match m:
    case None{}:
      [0]
    case Some{x}:
      1 <> Utf8.framed(x)

# the bytes of a record: a tag (0 Kept, 1 Saw, 2 Marked, 3 Forked), then its
# fields in order; a Kept ends with the node's own bytes
# (History.Node.encode), which run to the end
def Record.payload(r: Record) -> Octets.Bytes():
  match r:
    case Kept{ln, c, v}:
      0
        <> List.append(
          &2,
          U32,
          Utf8.framed(ln),
          List.append(&2, U32, Content.encode(c), History.Node.encode(v))
        )
    case Saw{a, ln}:
      1 <> List.append(&2, U32, Utf8.framed(a), Utf8.framed(ln))
    case Marked{ln, nm, msg, a}:
      2
        <> List.append(
          &2,
          U32,
          Utf8.framed(ln),
          List.append(
            &2,
            U32,
            Utf8.framed(nm),
            List.append(&2, U32, Utf8.framed(msg), History.Author.encode(a))
          )
        )
    case Forked{ln, f, m}:
      3
        <> List.append(
          &2,
          U32,
          Utf8.framed(ln),
          List.append(&2, U32, Utf8.framed(f), MarkName.encode(m))
        )

# the first n bytes of b
def Bytes.take(b: Octets.Bytes(), n: Nat) -> Octets.Bytes():
  List.take(&2, U32, b, n)

# the check of a payload: the first 8 bytes of its BLAKE3 hash
def Record.check(p: Octets.Bytes()) -> Octets.Bytes():
  Bytes.take(Hash.Hash.blake3(p), 8n)

# The bytes of a record in the log: the length of its payload (LEB128),
# the payload, then its check. A record that a power cut tore is shorter
# than its length says, or fails its check, so a reader stops there.
def Record.encode(r: Record) -> Octets.Bytes():
  +p = Record.payload(r)
  List.append(
    &2,
    U32,
    Store.Leb.of(List.length(&2, U32, p)),
    List.append(&2, U32, p, Record.check(p))
  )

# the bytes of records, one after another
def Record.encode_all(rs: List<&2, Record>) -> Octets.Bytes():
  match rs:
    case Nil{}:
      []
    case Con{r, t}:
      List.append(&2, U32, Record.encode(r), Record.encode_all(t))

# both texts of n are valid UTF-8 text
def Name.ok(n: Resources.Name) -> Bool:
  match n:
    case Resources.Name{sp, p}:
      Bool.and(Text.Text.ok(sp), Text.Text.ok(p))

# the moved-from name, if any, is ok
def From.ok(f: Maybe<&2, Resources.Name>) -> Bool:
  match f:
    case None{}:
      True{}
    case Some{m}:
      Name.ok(m)

# the name of an agent, if any, is valid UTF-8 text
def Author.ok(a: History.Author) -> Bool:
  match a:
    case History.Outside{}:
      True{}
    case History.Agent{n}:
      Text.Text.ok(n)

# the mark name of a fork, if any, is valid UTF-8 text
def MarkName.ok(m: Maybe<&2, String>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{x}:
      Text.Text.ok(x)

# every text that record r holds is valid UTF-8 text (Text.ok): its lines,
# names, messages and authors. Only such records read back, since the log
# holds texts as UTF-8.
def Record.ok(r: Record) -> Bool:
  match r:
    case Kept{ln, c, History.Node{n, ps, b, f, a}}:
      Bool.and(Text.Text.ok(ln), Bool.and(Name.ok(n), Bool.and(From.ok(f), Author.ok(a))))
    case Saw{a, ln}:
      Bool.and(Text.Text.ok(a), Text.Text.ok(ln))
    case Marked{ln, nm, msg, a}:
      Bool.and(
        Text.Text.ok(ln),
        Bool.and(Text.Text.ok(nm), Bool.and(Text.Text.ok(msg), Author.ok(a)))
      )
    case Forked{ln, f, m}:
      Bool.and(Text.Text.ok(ln), Bool.and(Text.Text.ok(f), MarkName.ok(m)))

# every record of rs is ok
def Records.ok(rs: List<&2, Record>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case Con{r, t}:
      List.all.if(u => Records.ok(t), Record.ok(r))

# Reading
# -------

# What a reader finds in a log: the records of its whole entries, in order,
# and how many bytes they take from the start. A log whose length is more
# than good has a torn tail there.
type Read is Data:
  Read{records: List<&2, Record>, good: Nat}

# the records of the log b, up to the first entry that is torn or fails
# its check
law Journal.read:
  for b: Octets.Bytes()
  Read

# a log of whole records reads back as those records, all of it good
law read_after_encode:
  for rs: List<&2, Record>
  for o: {Records.ok(rs) == True{}: Bool}
  {
    Journal.read(
      Record.encode_all(rs)
    )
      == Read{rs, List.length(&2, U32, Record.encode_all(rs))}: Read
  }

# a torn tail loses nothing and invents nothing: whole records, then any
# proper prefix of one more record, read back as the whole records alone,
# with good where they end
law read_torn_tail:
  for rs: List<&2, Record>
  for r: Record
  for k: Nat
  for o: {Records.ok(rs) == True{}: Bool}
  for t: {Nat.is_lt(k, List.length(&2, U32, Record.encode(r))) == True{}: Bool}
  {
    Journal.read(
      List.append(&2, U32, Record.encode_all(rs), Bytes.take(Record.encode(r), k))
    )
      == Read{rs, List.length(&2, U32, Record.encode_all(rs))}: Read
  }
