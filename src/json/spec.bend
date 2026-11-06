import Base
import ../shared.bend as Shared

# JSON (RFC 8259), as far as the MCP front needs it. A text is a String of
# Unicode characters; the front decodes and encodes its UTF-8. A number
# keeps its text as the input spells it, so a JSON-RPC id goes back
# exactly as it came, and nothing is lost to rounding.

# A JSON value. The items of an array and the members of an object are
# chains of the same type (JItem and JMember, ended by JEnd), not Lists:
# Bend allows no mutual recursion, and a def cannot recurse through a List
# template, so one type keeps show and the checks structurally recursive.
# An object keeps its members in order, duplicates included. Build arrays
# and objects with Json.arr and Json.obj; Json.ok says a value is well
# formed.
type Json is Data:
  JNull{}
  JBool{b: Bool}
  JNum{text: String}
  JStr{s: String}
  JArr{items: Json}
  JObj{members: Json}
  JEnd{}
  JItem{head: Json, rest: Json}
  JMember{key: String, value: Json, rest: Json}

# A member of an object, as Json.obj takes it.
type Field is Data:
  Field{key: String, value: Json}

# Characters
# ----------

# the code of c
def Ch.code(c: Char) -> U32:
  Char.to_u32(c)

# c has the code x
def Ch.is(c: Char, x: U32) -> Bool:
  U32.is_eq(Char.to_u32(c), x)

# c is JSON whitespace: space, tab, line feed or carriage return
def Ch.is_space(+c: Char) -> Bool:
  Bool.or(Bool.or(Ch.is(c, 32), Ch.is(c, 9)), Bool.or(Ch.is(c, 10), Ch.is(c, 13)))

# s without the whitespace at its start
def Json.skip(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +t}:
      Shared.Bool.when(String, Ch.is_space(c), u => Json.skip(t), u => SCon{c, t})

# Numbers
# -------
# number = [ "-" ] int [ frac ] [ exp ] (RFC 8259, section 6); a scan
# takes the longest numeral at the start of a text.

# c then the cut
def Num.on(c: Char, k: Shared.Cut) -> Shared.Cut:
  match k:
    case Shared.Cut{b, a}:
      Shared.Cut{SCon{c, b}, a}

# the digits at the start of s, and the rest
def Num.digits(s: String) -> Shared.Cut:
  match s:
    case SNil{}:
      Shared.Cut{SNil{}, SNil{}}
    case SCon{+c, +t}:
      Shared.Bool.when(
        Shared.Cut,
        Char.is_digit(c),
        u => Num.on(c, Num.digits(t)),
        u => Shared.Cut{SNil{}, SCon{c, t}}
      )

# the cut, when it took at least one digit
def Num.some(k: Shared.Cut) -> Maybe<&2, Shared.Cut>:
  match k:
    case Shared.Cut{SNil{}, a}:
      None{}
    case Shared.Cut{b, a}:
      Some{Shared.Cut{b, a}}

# a before the cut m
def Num.join(a: String, m: Maybe<&2, Shared.Cut>) -> Maybe<&2, Shared.Cut>:
  match m:
    case None{}:
      None{}
    case Some{Shared.Cut{b, r}}:
      Some{Shared.Cut{String.append(a, b), r}}

# the cut m, then k on its rest
def Num.then(m: Maybe<&2, Shared.Cut>, k: String -> Maybe<&2, Shared.Cut>) -> Maybe<&2, Shared.Cut>:
  match m:
    case None{}:
      None{}
    case Some{Shared.Cut{a, r}}:
      Num.join(a, k(r))

# nothing taken
def Num.none(s: String) -> Maybe<&2, Shared.Cut>:
  Some{Shared.Cut{SNil{}, s}}

# an optional "-"
def Num.minus(s: String) -> Maybe<&2, Shared.Cut>:
  match s:
    case SCon{+c, +t}:
      Shared.Bool.when(
        Maybe<&2, Shared.Cut>,
        Ch.is(c, 45),
        u => Some{Shared.Cut{"-", t}},
        u => Num.none(SCon{c, t})
      )
    case SNil{}:
      Num.none(SNil{})

# "0", or a digit 1 to 9 and more digits
def Num.int(s: String) -> Maybe<&2, Shared.Cut>:
  match s:
    case SCon{+c, +t}:
      Shared.Bool.when(
        Maybe<&2, Shared.Cut>,
        Ch.is(c, 48),
        u => Some{Shared.Cut{"0", t}},
        u => Num.some(Num.digits(SCon{c, t}))
      )
    case SNil{}:
      None{}

# an optional "." and one or more digits
def Num.frac(s: String) -> Maybe<&2, Shared.Cut>:
  match s:
    case SCon{+c, +t}:
      Shared.Bool.when(
        Maybe<&2, Shared.Cut>,
        Ch.is(c, 46),
        u => Num.join(".", Num.some(Num.digits(t))),
        u => Num.none(SCon{c, t})
      )
    case SNil{}:
      Num.none(SNil{})

# an optional "+" or "-", then one or more digits
def Num.exp.digits(s: String) -> Maybe<&2, Shared.Cut>:
  match s:
    case SCon{+c, +t}:
      Shared.Bool.when(
        Maybe<&2, Shared.Cut>,
        Bool.or(Ch.is(c, 43), Ch.is(c, 45)),
        u => Num.join(SCon{c, SNil{}}, Num.some(Num.digits(t))),
        u => Num.some(Num.digits(SCon{c, t}))
      )
    case SNil{}:
      None{}

# an optional "e" or "E" and its exponent
def Num.exp(s: String) -> Maybe<&2, Shared.Cut>:
  match s:
    case SCon{+c, +t}:
      Shared.Bool.when(
        Maybe<&2, Shared.Cut>,
        Bool.or(Ch.is(c, 101), Ch.is(c, 69)),
        u => Num.join(SCon{c, SNil{}}, Num.exp.digits(t)),
        u => Num.none(SCon{c, t})
      )
    case SNil{}:
      Num.none(SNil{})

# the numeral at the start of s, and the rest, or None when s starts with
# none
def Num.scan(s: String) -> Maybe<&2, Shared.Cut>:
  Num.then(Num.minus(s), r => Num.then(Num.int(r), r2 => Num.then(Num.frac(r2), r3 => Num.exp(r3))))

# the scan took a whole text: nothing is left
def Num.whole.of(m: Maybe<&2, Shared.Cut>) -> Bool:
  match m:
    case Some{Shared.Cut{n, SNil{}}}:
      True{}
    case _:
      False{}

# t is exactly one numeral
def Num.whole(t: String) -> Bool:
  Num.whole.of(Num.scan(t))

# Building
# --------

# the chain of the items xs
def Json.items(xs: List<&2, Json>) -> Json:
  match xs:
    case Nil{}:
      JEnd{}
    case Con{h, t}:
      JItem{h, Json.items(t)}

# the chain of the members fs
def Json.members(fs: List<&2, Field>) -> Json:
  match fs:
    case Nil{}:
      JEnd{}
    case Con{Field{k, v}, t}:
      JMember{k, v, Json.members(t)}

# the array of xs
def Json.arr(xs: List<&2, Json>) -> Json:
  JArr{Json.items(xs)}

# the object of fs
def Json.obj(fs: List<&2, Field>) -> Json:
  JObj{Json.members(fs)}

# Reading values out
# ------------------

# the value of the first member named k in the chain ms
def Json.member(ms: Json, +k: String) -> Maybe<&2, Json>:
  match ms:
    case JMember{x, v, t}:
      Shared.Bool.when(Maybe<&2, Json>, String.eq(x, k), u => Some{v}, u => Json.member(t, k))
    case _:
      None{}

# the value of the member named k of the object v, if v is one and has it
def Json.get(v: Json, k: String) -> Maybe<&2, Json>:
  match v:
    case JObj{ms}:
      Json.member(ms, k)
    case _:
      None{}

# the text of a string value
def Json.text(m: Maybe<&2, Json>) -> Maybe<&2, String>:
  match m:
    case Some{JStr{s}}:
      Some{s}
    case _:
      None{}

# Strings
# -------

# the hex digit of c, as its value
def Hex.digit(+c: Char) -> Maybe<&2, U32>:
  +x = Char.to_u32(c)
  Shared.Bool.when(
    Maybe<&2, U32>,
    Char.is_digit(c),
    u => Some{(x - 48: U32)},
    u => Shared.Bool.when(
      Maybe<&2, U32>,
      Bool.and((x >= 97: U32), (x <= 102: U32)),
      v => Some{(x - 87: U32)},
      v => Bool.pick(
        Maybe<&2, U32>,
        Bool.and((x >= 65: U32), (x <= 70: U32)),
        Some{(x - 55: U32)},
        None{}
      )
    )
  )

# A number read from the start of a text, and the rest.
type Code is Data:
  Code{value: U32, rest: String}

# n times 16 plus the digit m, then the rest
def Hex.next(n: U32, m: Maybe<&2, U32>) -> Maybe<&2, U32>:
  match m:
    case None{}:
      None{}
    case Some{d}:
      Some{((n << 4n) .|. d: U32)}

# m times 16 plus the digit c
def Hex.then(m: Maybe<&2, U32>, c: Char) -> Maybe<&2, U32>:
  match m:
    case None{}:
      None{}
    case Some{n}:
      Hex.next(n, Hex.digit(c))

# the code of a value and the rest
def Hex.code(m: Maybe<&2, U32>, t: String) -> Maybe<&2, Code>:
  match m:
    case None{}:
      None{}
    case Some{v}:
      Some{Code{v, t}}

# the value of four hex digits at the start of s
def Hex.four(s: String) -> Maybe<&2, Code>:
  match s:
    case SCon{a, SCon{b, SCon{c, SCon{d, t}}}}:
      m = Hex.next(0, Hex.digit(a))
      Hex.code(Hex.then(Hex.then(Hex.then(m, b), c), d), t)
    case _:
      None{}

# One step of reading a string: its end, or a character and the rest.
type SStep is Data:
  SEnd{rest: String}
  SPush{c: Char, rest: String}

# The code of an escape letter, and the code of the character it stands
# for.
type Swap is Data:
  Swap{from: U32, to: U32}

# the simple escapes (RFC 8259, section 7): ", \, /, b, f, n, r, t
def Esc.table() -> List<&2, Swap>:
  [
    Swap{34, 34},
    Swap{92, 92},
    Swap{47, 47},
    Swap{98, 8},
    Swap{102, 12},
    Swap{110, 10},
    Swap{114, 13},
    Swap{116, 9}
  ]

# the character that the escape letter x stands for, in the table ws
def Esc.find(ws: List<&2, Swap>, +x: U32) -> Maybe<&2, U32>:
  match ws:
    case Nil{}:
      None{}
    case Con{Swap{f, t}, r}:
      Shared.Bool.when(Maybe<&2, U32>, U32.is_eq(f, x), u => Some{t}, u => Esc.find(r, x))

# the character of a high surrogate u and the low one that may follow in
# t as another \u escape, combined; u alone when none follows
def Str.pair(+u: U32, t: String, m: Maybe<&2, Code>) -> SStep:
  match m:
    case Some{Code{+l, r}}:
      low = Bool.and((l >= 56320: U32), (l <= 57343: U32))
      both = ((((u - 55296: U32) << 10n) + (l - 56320: U32): U32) + 65536: U32)
      Shared.Bool.when(SStep, low, v => SPush{Chr{both}, r}, v => SPush{Chr{u}, t})
    case None{}:
      SPush{Chr{u}, t}

# the step of a \u escape: its character, combined with a following low
# surrogate escape when it is a high surrogate
def Str.uni(m: Maybe<&2, Code>) -> Maybe<&2, SStep>:
  match m:
    case None{}:
      None{}
    case Some{Code{+u, +t}}:
      high = Bool.and((u >= 55296: U32), (u <= 56319: U32))
      next = Shared.Bool.when(
        Maybe<&2, Code>,
        String.starts_with(t, SCon{Chr{92}, SCon{Chr{117}, SNil{}}}),
        v => Hex.four(String.drop(t, 2n)),
        v => None{}
      )
      Some{Shared.Bool.when(SStep, high, v => Str.pair(u, t, next), v => SPush{Chr{u}, t})}

# the step of an escape, after the backslash
def Str.esc(s: String) -> Maybe<&2, SStep>:
  match s:
    case SNil{}:
      None{}
    case SCon{+e, +t}:
      Shared.Bool.when(
        Maybe<&2, SStep>,
        Ch.is(e, 117),
        u => Str.uni(Hex.four(t)),
        u => Maybe.map(&2, U32, SStep, x => SPush{Chr{x}, t}, Esc.find(Esc.table(), Char.to_u32(e)))
      )

# the next step of a string, inside its quotes: a raw control character
# (below 32) is not allowed
def Str.step(s: String) -> Maybe<&2, SStep>:
  match s:
    case SNil{}:
      None{}
    case SCon{+c, +t}:
      Shared.Bool.when(
        Maybe<&2, SStep>,
        Ch.is(c, 34),
        u => Some{SEnd{t}},
        u => Shared.Bool.when(
          Maybe<&2, SStep>,
          Ch.is(c, 92),
          v => Str.esc(t),
          v => Bool.pick(Maybe<&2, SStep>, (Char.to_u32(c) < 32: U32), None{}, Some{SPush{c, t}})
        )
      )

# the string read from step m on, its characters so far reversed in acc;
# fuel bounds the steps
def Str.go(fuel: Nat, m: Maybe<&2, SStep>, acc: String) -> Maybe<&2, Shared.Cut>:
  match fuel:
    case 0n:
      None{}
    case 1n+f:
      match m:
        case None{}:
          None{}
        case Some{SEnd{r}}:
          Some{Shared.Cut{String.reverse(acc), r}}
        case Some{SPush{c, r}}:
          Str.go(f, Str.step(r), SCon{c, acc})

# the string at the start of s, after its opening quote, and the rest
def Str.read(+s: String) -> Maybe<&2, Shared.Cut>:
  Str.go(1n+String.length(s), Str.step(s), SNil{})

# the hex digit of the value d (below 16)
def Hex.show(+d: U32) -> Char:
  Chr{Bool.pick(U32, (d < 10: U32), (d + 48: U32), (d + 87: U32))}

# c as JSON writes it inside a string, before the text t
def Str.char(+c: Char, +t: String) -> String:
  +x = Char.to_u32(c)
  +bs = {Chr{92}: Char}
  Shared.Bool.when(
    String,
    Bool.or(U32.is_eq(x, 34), U32.is_eq(x, 92)),
    u => SCon{bs, SCon{c, t}},
    u => Shared.Bool.when(
      String,
      U32.is_eq(x, 10),
      v => SCon{bs, SCon{'n', t}},
      v => Shared.Bool.when(
        String,
        U32.is_eq(x, 13),
        w => SCon{bs, SCon{'r', t}},
        w => Shared.Bool.when(
          String,
          U32.is_eq(x, 9),
          y => SCon{bs, SCon{'t', t}},
          y => Shared.Bool.when(
            String,
            (x < 32: U32),
            z => String.append(
              SCon{bs, "u00"},
              SCon{Hex.show((x >> 4n: U32)), SCon{Hex.show((x .&. 15: U32)), t}}
            ),
            z => SCon{c, t}
          )
        )
      )
    )
  )

# the characters of s as JSON writes them inside a string
def Str.body(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{c, t}:
      Str.char(c, Str.body(t))

# s as a JSON string: quoted, with '"', '\' and characters below 32
# escaped; every other character as it is
def Str.show(s: String) -> String:
  SCon{Chr{34}, String.append(Str.body(s), SCon{Chr{34}, SNil{}})}

# Writing
# -------

# v as JSON text, with no whitespace; a chain writes its elements
# separated by ','
def Json.show(v: Json) -> String:
  match v:
    case JNull{}:
      "null"
    case JBool{True{}}:
      "true"
    case JBool{False{}}:
      "false"
    case JNum{t}:
      t
    case JStr{s}:
      Str.show(s)
    case JArr{l}:
      SCon{Chr{91}, String.append(Json.show(l), SCon{Chr{93}, SNil{}})}
    case JObj{l}:
      SCon{Chr{123}, String.append(Json.show(l), SCon{Chr{125}, SNil{}})}
    case JEnd{}:
      SNil{}
    case JItem{h, JEnd{}}:
      Json.show(h)
    # bend-lint: expect-begin bend-lint-rules/performance/missed_fork@hint -- an MCP message is a few kilobytes, where a fork costs more than it saves
    case JItem{h, r}:
      String.append(Json.show(h), SCon{Chr{44}, Json.show(r)})
    case JMember{k, x, JEnd{}}:
      String.append(Str.show(k), SCon{Chr{58}, Json.show(x)})
    case JMember{k, x, r}:
      String.append(
        Str.show(k),
        SCon{Chr{58}, String.append(Json.show(x), SCon{Chr{44}, Json.show(r)})}
      )
    # bend-lint: expect-end bend-lint-rules/performance/missed_fork@hint

# Where a value stands: as a value, as the items of an array, or as the
# members of an object.
type Place is Data:
  PVal{}
  PItems{}
  PMembers{}

# v is well formed at place p: a value at a value's place, item chains in
# arrays, member chains in objects, and every number text exactly one
# JSON numeral
def Json.ok(v: Json, p: Place) -> Bool:
  match v p:
    case JNull{} PVal{}:
      True{}
    case JBool{b} PVal{}:
      True{}
    case JNum{t} PVal{}:
      Num.whole(t)
    case JStr{s} PVal{}:
      True{}
    case JArr{l} PVal{}:
      Json.ok(l, PItems{})
    case JObj{l} PVal{}:
      Json.ok(l, PMembers{})
    case JEnd{} PItems{}:
      True{}
    case JEnd{} PMembers{}:
      True{}
    case JItem{h, r} PItems{}:
      List.all.if(u => Json.ok(r, PItems{}), Json.ok(h, PVal{}))
    case JMember{k, x, r} PMembers{}:
      List.all.if(u => Json.ok(r, PMembers{}), Json.ok(x, PVal{}))
    case _ _:
      False{}

# Reading
# -------
# One left-to-right pass with a stack of the arrays and objects still
# open, so no def recurses into itself through another.

# What the next character starts: an array, its end, an object, its end, a
# string, a colon, a comma, a number, a word (true, false, null), nothing
# JSON allows there, or the end of the text.
type Lead is Data:
  LArr{}
  LArrEnd{}
  LObj{}
  LObjEnd{}
  LQuote{}
  LColon{}
  LComma{}
  LNum{}
  LWord{}
  LBad{}
  LEof{}

# the lead of a character other than a bracket, a brace, a quote, a colon
# or a comma, with code x
def Lead.rest(c: Char, +x: U32) -> Lead:
  Shared.Bool.when(
    Lead,
    Bool.or(U32.is_eq(x, 45), Char.is_digit(c)),
    d => LNum{},
    d => Bool.pick(
      Lead,
      Bool.or(Bool.or(U32.is_eq(x, 116), U32.is_eq(x, 102)), U32.is_eq(x, 110)),
      LWord{},
      LBad{}
    )
  )

# The lead of each character code that stands for itself.
def Lead.marks() -> List<&2, LeadMark>:
  [
    LeadMark{91, LArr{}},
    LeadMark{93, LArrEnd{}},
    LeadMark{123, LObj{}},
    LeadMark{125, LObjEnd{}},
    LeadMark{34, LQuote{}},
    LeadMark{58, LColon{}},
    LeadMark{44, LComma{}}
  ]

# A character code and the lead it gives.
type LeadMark is Data:
  LeadMark{code: U32, lead: Lead}

# the lead of c (code x) in the marks ms, else Lead.rest
def Lead.find(ms: List<&2, LeadMark>, c: Char, +x: U32) -> Lead:
  match ms:
    case Nil{}:
      Lead.rest(c, x)
    case Con{LeadMark{k, l}, t}:
      Shared.Bool.when(Lead, U32.is_eq(k, x), u => l, u => Lead.find(t, c, x))

# what the first character of s starts
def Lead.of(s: String) -> Lead:
  match s:
    case SNil{}:
      LEof{}
    case SCon{+c, t}:
      Lead.find(Lead.marks(), c, Char.to_u32(c))

# An open array with its items so far, or an open object with its members
# so far and the key whose value comes next; both last first.
type Frame is Data:
  FArr{items: List<&2, Json>}
  FObj{fields: List<&2, Field>, key: String}

# What may come next: a value, a value or the end of the array, a key, a
# key or the end of the object, a colon, or a comma or the end of the open
# array or object.
type Want is Data:
  WVal{}
  WValOrEnd{}
  WKey{}
  WKeyOrEnd{}
  WColon{}
  WNext{}

# Reading goes on with the open frames and what may come next, or has read
# the whole value.
type Phase is Data:
  Run{stack: List<&2, Frame>, want: Want}
  Fin{v: Json}

# The rest of the text, and the phase after a step.
type Moved is Data:
  Moved{rest: String, phase: Phase}

# the value v put in the frame on top of stack, with rest after it: a
# finished read when no frame is open
def Json.put(v: Json, stack: List<&2, Frame>, rest: String) -> Maybe<&2, Moved>:
  match stack:
    case Nil{}:
      Some{Moved{rest, Fin{v}}}
    case Con{FArr{xs}, t}:
      Some{Moved{rest, Run{Con{FArr{v <> xs}, t}, WNext{}}}}
    case Con{FObj{fs, k}, t}:
      Some{Moved{rest, Run{Con{FObj{Field{k, v} <> fs, SNil{}}, t}, WNext{}}}}

# the open array closed
def Json.close_arr(stack: List<&2, Frame>, rest: String) -> Maybe<&2, Moved>:
  match stack:
    case Con{FArr{xs}, t}:
      Json.put(Json.arr(List.reverse(&2, Json, xs)), t, rest)
    case _:
      None{}

# the open object closed
def Json.close_obj(stack: List<&2, Frame>, rest: String) -> Maybe<&2, Moved>:
  match stack:
    case Con{FObj{fs, k}, t}:
      Json.put(Json.obj(List.reverse(&2, Field, fs)), t, rest)
    case _:
      None{}

# the string value read
def Json.string(m: Maybe<&2, Shared.Cut>, stack: List<&2, Frame>) -> Maybe<&2, Moved>:
  match m:
    case None{}:
      None{}
    case Some{Shared.Cut{s, r}}:
      Json.put(JStr{s}, stack, r)

# the number value read
def Json.number(m: Maybe<&2, Shared.Cut>, stack: List<&2, Frame>) -> Maybe<&2, Moved>:
  match m:
    case None{}:
      None{}
    case Some{Shared.Cut{n, r}}:
      Json.put(JNum{n}, stack, r)

# the word value at the start of s: true, false or null
def Json.word(+s: String, +stack: List<&2, Frame>) -> Maybe<&2, Moved>:
  Shared.Bool.when(
    Maybe<&2, Moved>,
    String.starts_with(s, "true"),
    u => Json.put(JBool{True{}}, stack, String.drop(s, 4n)),
    u => Shared.Bool.when(
      Maybe<&2, Moved>,
      String.starts_with(s, "false"),
      v => Json.put(JBool{False{}}, stack, String.drop(s, 5n)),
      v => Shared.Bool.when(
        Maybe<&2, Moved>,
        String.starts_with(s, "null"),
        w => Json.put(JNull{}, stack, String.drop(s, 4n)),
        w => None{}
      )
    )
  )

# the key read for the open object
def Json.key(m: Maybe<&2, Shared.Cut>, stack: List<&2, Frame>) -> Maybe<&2, Moved>:
  match m stack:
    case Some{Shared.Cut{k, r}} Con{FObj{fs, x}, t}:
      Some{Moved{r, Run{Con{FObj{fs, k}, t}, WColon{}}}}
    case _ _:
      None{}

# after a comma: the next item of the open array, or the next key of the
# open object
def Json.comma(stack: List<&2, Frame>, rest: String) -> Maybe<&2, Moved>:
  match stack:
    case Con{FArr{xs}, t}:
      Some{Moved{rest, Run{Con{FArr{xs}, t}, WVal{}}}}
    case Con{FObj{fs, k}, t}:
      Some{Moved{rest, Run{Con{FObj{fs, k}, t}, WKey{}}}}
    case Nil{}:
      None{}

# the step of a value that lead starts in s; t is s after its first
# character
def Json.value(lead: Lead, s: String, t: String, stack: List<&2, Frame>) -> Maybe<&2, Moved>:
  match lead:
    case LArr{}:
      Some{Moved{t, Run{FArr{[]} <> stack, WValOrEnd{}}}}
    case LObj{}:
      Some{Moved{t, Run{FObj{[], SNil{}} <> stack, WKeyOrEnd{}}}}
    case LQuote{}:
      Json.string(Str.read(t), stack)
    case LNum{}:
      Json.number(Num.scan(s), stack)
    case LWord{}:
      Json.word(s, stack)
    case _:
      None{}

# the step at s, whose first character starts lead and t is the rest, with
# what may come next and the open frames; None for text that is not JSON
def Json.step(
  want: Want,
  lead: Lead,
  s: String,
  t: String,
  stack: List<&2, Frame>
) -> Maybe<&2, Moved>:
  match want lead:
    case WVal{} l:
      Json.value(l, s, t, stack)
    case WValOrEnd{} LArrEnd{}:
      Json.close_arr(stack, t)
    case WValOrEnd{} l:
      Json.value(l, s, t, stack)
    case WKey{} LQuote{}:
      Json.key(Str.read(t), stack)
    case WKeyOrEnd{} LQuote{}:
      Json.key(Str.read(t), stack)
    case WKeyOrEnd{} LObjEnd{}:
      Json.close_obj(stack, t)
    case WColon{} LColon{}:
      Some{Moved{t, Run{stack, WVal{}}}}
    case WNext{} LComma{}:
      Json.comma(stack, t)
    case WNext{} LArrEnd{}:
      Json.close_arr(stack, t)
    case WNext{} LObjEnd{}:
      Json.close_obj(stack, t)
    case _ _:
      None{}

# the step at s, after its whitespace
def Json.at(s: String, stack: List<&2, Frame>, want: Want) -> Maybe<&2, Moved>:
  +s = Json.skip(s)
  Json.step(want, Lead.of(s), s, String.drop(s, 1n), stack)

# the value that the steps from m on read; only whitespace may follow it;
# fuel bounds the steps
def Json.go(fuel: Nat, m: Maybe<&2, Moved>) -> Maybe<&2, Json>:
  match fuel:
    case 0n:
      None{}
    case 1n+f:
      match m:
        case None{}:
          None{}
        case Some{Moved{r, Fin{v}}}:
          Bool.pick(Maybe<&2, Json>, String.is_empty(Json.skip(r)), Some{v}, None{})
        case Some{Moved{r, Run{stack, w}}}:
          Json.go(f, Json.at(r, stack, w))

# the JSON value that the text s spells, or None when s is not one JSON
# value (whitespace around it allowed)
def Json.read(+s: String) -> Maybe<&2, Json>:
  Json.go(2n+String.length(s), Some{Moved{s, Run{[], WVal{}}}})

# Laws
# ----

# a well-formed value written as text reads back as itself
law read_after_show:
  for v: Json
  for h: {Json.ok(v, PVal{}) == True{}: Bool}
  {Json.read(Json.show(v)) == Some{v}: Maybe<&2, Json>}
