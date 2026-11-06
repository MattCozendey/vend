import Base
import ../hash/spec.bend as Hash
import ../history/spec.bend as History
import ../shared.bend as Shared
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

# One kept version: the line it was kept on, its content (None for a
# version that says the file is gone), and its history node. Replaying it
# puts the content in the store, the node in the history, and moves the
# line it names.
type Record is Data:
  Kept{line: String, content: Maybe<&2, Shared.Bytes()>, node: History.Node}

# the bytes of a text: its UTF-8, framed
def Utf8.framed(s: String) -> Shared.Bytes():
  Store.Bytes.framed(Text.Text.encode(s))

# the bytes of a content: 0 for none, or 1 then the content, framed
def Content.encode(c: Maybe<&2, Shared.Bytes()>) -> Shared.Bytes():
  match c:
    case None{}:
      [0]
    case Some{b}:
      1 <> Store.Bytes.framed(b)

# the bytes of a record: the tag 0 (Kept), the line, the content, then the
# node's own bytes (History.Node.encode), which run to the end
def Record.payload(r: Record) -> Shared.Bytes():
  match r:
    case Kept{ln, c, v}:
      0
        <> List.append(
          &2,
          U32,
          Utf8.framed(ln),
          List.append(&2, U32, Content.encode(c), History.Node.encode(v))
        )

# the first n bytes of b
def Bytes.take(b: Shared.Bytes(), n: Nat) -> Shared.Bytes():
  List.take(&2, U32, b, n)

# the check of a payload: the first 8 bytes of its BLAKE3 hash
def Record.check(p: Shared.Bytes()) -> Shared.Bytes():
  Bytes.take(Hash.Hash.blake3(p), 8n)

# The bytes of a record in the log: the length of its payload (LEB128),
# the payload, then its check. A record that a power cut tore is shorter
# than its length says, or fails its check, so a reader stops there.
def Record.encode(r: Record) -> Shared.Bytes():
  +p = Record.payload(r)
  List.append(
    &2,
    U32,
    Store.Leb.of(List.length(&2, U32, p)),
    List.append(&2, U32, p, Record.check(p))
  )

# the bytes of records, one after another
def Record.encode_all(rs: List<&2, Record>) -> Shared.Bytes():
  match rs:
    case Nil{}:
      []
    case Con{r, t}:
      List.append(&2, U32, Record.encode(r), Record.encode_all(t))

# both texts of n are valid UTF-8 text
def Name.ok(n: Shared.Name) -> Bool:
  match n:
    case Shared.Name{sp, p}:
      Bool.and(Text.Text.ok(sp), Text.Text.ok(p))

# the moved-from name, if any, is ok
def From.ok(f: Maybe<&2, Shared.Name>) -> Bool:
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

# every text that record r holds is valid UTF-8 text (Text.ok): its line,
# its node's name, moved-from name and author. Only such records read back,
# since the log holds texts as UTF-8.
def Record.ok(r: Record) -> Bool:
  match r:
    case Kept{ln, c, History.Node{n, ps, b, f, a}}:
      Bool.and(Text.Text.ok(ln), Bool.and(Name.ok(n), Bool.and(From.ok(f), Author.ok(a))))

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
  for b: Shared.Bytes()
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
