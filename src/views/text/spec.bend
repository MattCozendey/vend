import Base
import ../../shared/bytes.bend as Octets
import ../shared.bend as Views

# Text: a resource whose bytes are UTF-8. Its document is the String of
# Unicode scalar values that the bytes spell, so a line ending is stored
# once, as the characters it is, and lines are a function of the String.

# c is a Unicode scalar value: at most 0x10FFFF, and not a surrogate
# (0xD800 to 0xDFFF)
def Text.is_scalar(c: Char) -> Bool:
  match c:
    case Chr{+x}:
      Bool.and((x <= 1114111: U32), Bool.or((x < 55296: U32), (x > 57343: U32)))

# s can be written as UTF-8: every character is a scalar value
def Text.ok(s: String) -> Bool:
  List.all(~&2, ~Char, ~Text.is_scalar, String.to_list(s))

# How many bytes UTF-8 spends on a scalar value.
type Width is Data:
  W1{}
  W2{}
  W3{}
  W4{}

# the UTF-8 width of the scalar value x (RFC 3629, section 3)
def Text.width(+x: U32) -> Width:
  Bool.pick(
    Width,
    (x < 128: U32),
    W1{},
    Bool.pick(Width, (x < 2048: U32), W2{}, Bool.pick(Width, (x < 65536: U32), W3{}, W4{}))
  )

# the UTF-8 bytes of the scalar value x, w wide (RFC 3629, section 3)
def Text.encode_char.of(w: Width, +x: U32) -> Octets.Bytes():
  match w:
    case W1{}:
      [x]
    case W2{}:
      [(192 .|. (x >> 6n): U32), (128 .|. (x .&. 63): U32)]
    case W3{}:
      [(224 .|. (x >> 12n): U32), (128 .|. ((x >> 6n) .&. 63): U32), (128 .|. (x .&. 63): U32)]
    case W4{}:
      [
        (240 .|. (x >> 18n): U32),
        (128 .|. ((x >> 12n) .&. 63): U32),
        (128 .|. ((x >> 6n) .&. 63): U32),
        (128 .|. (x .&. 63): U32)
      ]

# the UTF-8 bytes of the character c
def Text.encode_char(c: Char) -> Octets.Bytes():
  match c:
    case Chr{+x}:
      Text.encode_char.of(Text.width(x), x)

# the UTF-8 bytes of s
def Text.encode(s: String) -> Octets.Bytes():
  match s:
    case SNil{}:
      []
    case SCon{c, t}:
      List.append(&2, U32, Text.encode_char(c), Text.encode(t))

# the String that UTF-8 bytes b spell, or None when b is not UTF-8
law Text.decode:
  for b: Octets.Bytes()
  Maybe<&2, String>

# Text loses nothing: decode accepts exactly the UTF-8 encodings of valid
# Strings, and gives back the String that encode wrote
law Text.lossless:
  Views.View.Lossless(~String, ~Text.ok, ~Text.decode, ~Text.encode)

# How a line ends.
type End is Data:
  LF{}
  CRLF{}
  CR{}
  Eof{}

# A line: its text, with no '\n' or '\r', and how it ends.
type Line is Data:
  Line{text: String, end: End}

# the text of l, without its end
def Line.text(l: Line) -> String:
  match l:
    case Line{t, e}:
      t

# the role of a character in line splitting
type Brk is Data:
  Nl{}
  Cr{}
  Ch{c: Char}

# the role of c: '\n' (10), '\r' (13), or any other character
def Brk.of(+c: Char) -> Brk:
  Bool.pick(Brk, Char.is_eq(c, Chr{10}), Nl{}, Bool.pick(Brk, Char.is_eq(c, Chr{13}), Cr{}, Ch{c}))

# the roles of the characters of s
def Brk.list(s: String) -> List<&2, Brk>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{c, t}:
      Brk.of(c) <> Brk.list(t)

# the lines of bs, given cur: the text of the current line, last first
def Text.lines.go(bs: List<&2, Brk>, cur: String) -> List<&2, Line>:
  match bs:
    case Nil{}:
      [Line{String.reverse(cur), Eof{}}]
    case Con{Cr{}, Con{Nl{}, t}}:
      Line{String.reverse(cur), CRLF{}} <> Text.lines.go(t, SNil{})
    case Con{Cr{}, t}:
      Line{String.reverse(cur), CR{}} <> Text.lines.go(t, SNil{})
    case Con{Nl{}, t}:
      Line{String.reverse(cur), LF{}} <> Text.lines.go(t, SNil{})
    case Con{Ch{c}, t}:
      Text.lines.go(t, SCon{c, cur})

# The lines of s. A line ends at "\n", "\r\n" or "\r"; a "\r" right before
# a "\n" is one "\r\n". The last line ends at Eof and may be empty, so ""
# is one empty line, and "a\n" is the line "a" then an empty line.
def Text.lines(s: String) -> List<&2, Line>:
  Text.lines.go(Brk.list(s), SNil{})

# the characters of e
def End.text(e: End) -> String:
  match e:
    case LF{}:
      SCon{Chr{10}, SNil{}}
    case CRLF{}:
      SCon{Chr{13}, SCon{Chr{10}, SNil{}}}
    case CR{}:
      SCon{Chr{13}, SNil{}}
    case Eof{}:
      SNil{}

# the text of ls: each line's text, then its end
def Text.join(ls: List<&2, Line>) -> String:
  match ls:
    case Nil{}:
      SNil{}
    case Con{Line{t, e}, r}:
      String.append(t, String.append(End.text(e), Text.join(r)))

# splitting into lines loses nothing: the lines join back to s
law Text.join_after_lines:
  for s: String
  {Text.join(Text.lines(s)) == s: String}

# Meaning, diff and merge
# -----------------------

# a and b mean the same: plain text has no trivia, so only equal text
def Text.same(a: String, b: String) -> Bool:
  String.eq(a, b)

# Text.same is an equivalence
law Text.same_equivalence:
  Views.View.Equivalence(~String, ~Text.same)

# One step of a diff: replace del lines at pos with ins; each pos counts in
# the lines as the steps before it left them.
type LineEdit is Data:
  LineEdit{pos: Nat, del: Nat, ins: List<&2, Line>}

# the steps that turn a into b, line by line
law Text.diff:
  for a: String
  for b: String
  List<&2, LineEdit>

# s after the steps, or None when a step does not fit
law Text.patch:
  for s: String
  for es: List<&2, LineEdit>
  Maybe<&2, String>

# no steps
def LineEdits.is_empty(es: List<&2, LineEdit>) -> Bool:
  List.is_empty(&2, LineEdit, es)

# the three-way merge of x and y from base, line by line: a region changed
# on one side only takes that side; a region changed the same way on both
# takes it; overlapping different changes are a clash (None)
law Text.merge:
  for base: String
  for x: String
  for y: String
  Maybe<&2, String>

# a patch with a diff gives the target
law Text.patches:
  Views.View.Patches(~String, ~List<&2, LineEdit>, ~Text.diff, ~Text.patch)

# a text has no diff to itself
law Text.diffs_nothing:
  Views.View.DiffsNothing(~String, ~List<&2, LineEdit>, ~Text.diff, ~LineEdits.is_empty)

# merge is a three-way merge
law Text.merges:
  Views.View.Merges(~String, ~Text.merge)
