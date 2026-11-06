import Base
import ../../glob/impl.bend as GlobImpl
import ../../shared.bend as Shared
import ../shared.bend as Views
import ./spec.bend as Spec
# bend-lint: expect-file bend-lint-rules/language/reused_binder@warning -- proof binders whose other use is inside a rewrite motive or an erased argument; the checker accepts them

# The decoder reads one byte at a time. A lead byte gives the width; the
# continuation bytes add six bits each. A finished sequence counts only if
# its value is a scalar value and Text.encode_char writes exactly the bytes
# read, so no overlong form, surrogate or value past 0x10FFFF gets in.

# Between characters, or inside one: the continuation bytes still to read,
# the value so far, and the bytes read so far.
type Dec is Data:
  Start{}
  Mid{left: Nat, value: U32, seen: List<&2, U32>}

# The result of one byte.
type Step is Data:
  Decoded{c: Char}
  Partial{state: Dec}
  Invalid{}

# the step after a lead byte x: its width, or Bad for a byte that cannot
# start a sequence (a continuation byte, or 0xF8 and above)
def Text.lead(+x: U32) -> Step:
  Bool.pick(
    Step,
    (x < 128: U32),
    Decoded{Chr{x}},
    Bool.pick(
      Step,
      (x < 192: U32),
      Invalid{},
      Bool.pick(
        Step,
        (x < 224: U32),
        Partial{Mid{1n, (x .&. 31: U32), [x]}},
        Bool.pick(
          Step,
          (x < 240: U32),
          Partial{Mid{2n, (x .&. 15: U32), [x]}},
          Bool.pick(Step, (x < 248: U32), Partial{Mid{3n, (x .&. 7: U32), [x]}}, Invalid{})
        )
      )
    )
  )

# the character of a finished sequence, if it is the one canonical UTF-8
# encoding of a scalar value
def Text.finish(+value: U32, seen: List<&2, U32>) -> Step:
  ok = List.all.if(
    u => Shared.Bytes.is_eq(Spec.Text.encode_char(Chr{value}), seen),
    Spec.Text.is_scalar(Chr{value})
  )
  Bool.pick(Step, ok, Decoded{Chr{value}}, Invalid{})

# the step after a continuation byte x, with left bytes still to read
def Text.more(left: Nat, value: U32, seen: List<&2, U32>) -> Step:
  match left:
    case 0n:
      Invalid{}
    case 1n+p:
      match p:
        case 0n:
          Text.finish(value, seen)
        case 1n+q:
          Partial{Mid{1n+q, value, seen}}

# the step after a byte that is a continuation byte when cont holds
def Text.cont(cont: Bool, left: Nat, value: U32, seen: List<&2, U32>) -> Step:
  match cont:
    case False{}:
      Invalid{}
    case True{}:
      Text.more(left, value, seen)

# the step after byte x in state st
def Text.step(+x: U32, st: Dec) -> Step:
  match st:
    case Start{}:
      Text.lead(x)
    case Mid{left, value, seen}:
      cont = U32.is_eq((x .&. 192: U32), 128)
      v = (((value << 6n): U32) .|. (x .&. 63): U32)
      s = List.append(&2, U32, seen, [x])
      Text.cont(cont, left, v, s)

# the String of the rest of the bytes, given s, the step of one byte, and
# k, the String of the rest from a state
def Text.after(s: Step, k: Dec -> Maybe<&2, String>) -> Maybe<&2, String>:
  match s:
    case Decoded{c}:
      Maybe.map(&2, String, String, r => SCon{c, r}, k(Start{}))
    case Partial{st}:
      k(st)
    case Invalid{}:
      None{}

# the String at the end of the bytes: none inside a sequence
def Text.decode.end(st: Dec) -> Maybe<&2, String>:
  match st:
    case Start{}:
      Some{SNil{}}
    case Mid{left, value, seen}:
      None{}

# the String that bytes b spell from state st
def Text.decode.go(b: List<&2, U32>, st: Dec) -> Maybe<&2, String>:
  match b:
    case Nil{}:
      Text.decode.end(st)
    case Con{x, t}:
      Text.after(Text.step(x, st), s => Text.decode.go(t, s))

def Spec.Text.decode(b):
  Text.decode.go(b, Start{})

# Lines
# -----
# Splitting into lines loses nothing: Text.join_go says what the splitter
# keeps (the current line, reversed, then the rest), and Brk.text_list that
# the roles of the characters spell them back.

# the character of a line-splitting role
def Brk.char(b: Spec.Brk) -> Char:
  match b:
    case Spec.Nl{}:
      Chr{10}
    case Spec.Cr{}:
      Chr{13}
    case Spec.Ch{c}:
      c

# the characters of roles
def Brk.text(bs: List<&2, Spec.Brk>) -> String:
  match bs:
    case Nil{}:
      SNil{}
    case Con{b, t}:
      SCon{Brk.char(b), Brk.text(t)}

def Str.append_nil(a: String) -> {String.append(a, SNil{}) == a: String}:
  match a:
    case SNil{}:
      {==}
    case SCon{head, tail}:
      %Equal.sym(String, String.append(tail, ""), tail, Str.append_nil(tail)):
        {SCon{head, _} == SCon{head, tail}: String}
      {==}

def Str.append_assoc(
  a: String,
  b: String,
  c: String
) -> {String.append(String.append(a, b), c) == String.append(a, String.append(b, c)): String}:
  match a:
    case SNil{}:
      {==}
    case SCon{head, tail}:
      %Equal.sym(
        String,
        String.append(String.append(tail, b), c),
        String.append(tail, String.append(b, c)),
        Str.append_assoc(tail, b, c)
      ):
        {SCon{head, _} == SCon{head, String.append(tail, String.append(b, c))}: String}
      {==}

def Str.rev_go(
  s: String,
  +acc: String
) -> {String.reverse.go(s, acc) == String.append(String.reverse.go(s, SNil{}), acc): String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      r = String.reverse.go(t, SNil{})
      +h1 = {SCon{h, SNil{}}: String}
      %Equal.sym(String, String.reverse.go(t, h1), String.append(r, h1), Str.rev_go(t, h1)):
        {String.reverse.go(t, SCon{h, acc}) == String.append(_, acc): String}
      %Equal.sym(
        String,
        String.append(String.append(r, h1), acc),
        String.append(r, String.append(h1, acc)),
        Str.append_assoc(r, h1, acc)
      ):
        {String.reverse.go(t, SCon{h, acc}) == _: String}
      Str.rev_go(t, SCon{h, acc})

def Text.join_go(
  bs: List<&2, Spec.Brk>,
  +cur: String
) -> {
  Spec.Text.join(
    Spec.Text.lines.go(bs, cur)
  )
    == String.append(String.reverse(cur), Brk.text(bs)): String
}:
  match bs:
    case Nil{}:
      {==}
    case Con{Spec.Cr{}, Con{Spec.Nl{}, t}}:
      %Equal.sym(
        String,
        Spec.Text.join(Spec.Text.lines.go(t, SNil{})),
        Brk.text(t),
        Text.join_go(t, SNil{})
      ):
        {
          String.append(
            String.reverse(cur),
            String.append(Spec.End.text(Spec.CRLF{}), _)
          )
            == String.append(
              String.reverse(cur),
              Brk.text(Con{Spec.Cr{}, Con{Spec.Nl{}, t}})
            ): String
        }
      {==}
    case Con{Spec.Cr{}, Nil{}}:
      {==}
    case Con{Spec.Cr{}, Con{Spec.Cr{}, +t}}:
      r = {Con{Spec.Cr{}, t}: List<&2, Spec.Brk>}
      %Equal.sym(
        String,
        Spec.Text.join(Spec.Text.lines.go(r, SNil{})),
        Brk.text(r),
        Text.join_go(r, SNil{})
      ):
        {
          String.append(
            String.reverse(cur),
            String.append(Spec.End.text(Spec.CR{}), _)
          )
            == String.append(String.reverse(cur), Brk.text(Con{Spec.Cr{}, r})): String
        }
      {==}
    case Con{Spec.Cr{}, Con{Spec.Ch{c}, +t}}:
      r = {Con{Spec.Ch{c}, t}: List<&2, Spec.Brk>}
      %Equal.sym(
        String,
        Spec.Text.join(Spec.Text.lines.go(r, SNil{})),
        Brk.text(r),
        Text.join_go(r, SNil{})
      ):
        {
          String.append(
            String.reverse(cur),
            String.append(Spec.End.text(Spec.CR{}), _)
          )
            == String.append(String.reverse(cur), Brk.text(Con{Spec.Cr{}, r})): String
        }
      {==}
    case Con{Spec.Nl{}, +t}:
      %Equal.sym(
        String,
        Spec.Text.join(Spec.Text.lines.go(t, SNil{})),
        Brk.text(t),
        Text.join_go(t, SNil{})
      ):
        {
          String.append(
            String.reverse(cur),
            String.append(Spec.End.text(Spec.LF{}), _)
          )
            == String.append(String.reverse(cur), Brk.text(Con{Spec.Nl{}, t})): String
        }
      {==}
    case Con{Spec.Ch{+c}, +t}:
      +c1 = {SCon{c, SNil{}}: String}
      rest = Brk.text(t)
      %Equal.sym(
        String,
        Spec.Text.join(Spec.Text.lines.go(t, SCon{c, cur})),
        String.append(String.reverse(SCon{c, cur}), rest),
        Text.join_go(t, SCon{c, cur})
      ):
        {_ == String.append(String.reverse(cur), SCon{c, rest}): String}
      %Equal.sym(
        String,
        String.reverse.go(cur, c1),
        String.append(String.reverse.go(cur, SNil{}), c1),
        Str.rev_go(cur, c1)
      ):
        {String.append(_, rest) == String.append(String.reverse(cur), SCon{c, rest}): String}
      %Equal.sym(
        String,
        String.append(String.append(String.reverse(cur), c1), rest),
        String.append(String.reverse(cur), String.append(c1, rest)),
        Str.append_assoc(String.reverse(cur), c1, rest)
      ):
        {_ == String.append(String.reverse(cur), SCon{c, rest}): String}
      {==}

def Brk.char_of.cr(
  c: Char,
  b: Bool
) -> {
  Char.is_eq(c, Chr{13}) == b: Bool
} -> {Brk.char(Bool.pick(Spec.Brk, b, Spec.Cr{}, Spec.Ch{c})) == c: Char}:
  match b:
    case True{}:

      e => Equal.sym(Char, c, Chr{13}, GlobImpl.Char.is_eq_sound(c, Chr{13})(e))
    case False{}:
      e => {==}

def Brk.char_of.nl(
  +c: Char,
  b: Bool
) -> {
  Char.is_eq(c, Chr{10}) == b: Bool
} -> {
  Brk.char(
    Bool.pick(
      Spec.Brk,
      b,
      Spec.Nl{},
      Bool.pick(Spec.Brk, Char.is_eq(c, Chr{13}), Spec.Cr{}, Spec.Ch{c})
    )
  )
    == c: Char
}:
  match b:
    case True{}:
      e => Equal.sym(Char, c, Chr{10}, GlobImpl.Char.is_eq_sound(c, Chr{10})(e))
    case False{}:
      e => Brk.char_of.cr(c, Char.is_eq(c, Chr{13}))({==})

def Brk.char_of(+c: Char) -> {Brk.char(Spec.Brk.of(c)) == c: Char}:
  Brk.char_of.nl(c, Char.is_eq(c, Chr{10}))({==})

def Brk.text_list(s: String) -> {Brk.text(Spec.Brk.list(s)) == s: String}:
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      %Equal.sym(
        Char,
        Brk.char(Spec.Brk.of(h)),
        h,
        Brk.char_of(h)
      ): {SCon{_, Brk.text(Spec.Brk.list(t))} == SCon{h, t}: String}
      %Equal.sym(
        String,
        Brk.text(Spec.Brk.list(t)),
        t,
        Brk.text_list(t)
      ): {SCon{h, _} == SCon{h, t}: String}
      {==}

def Spec.Text.join_after_lines(s):
  +s = s
  Equal.trans(
    String,
    Spec.Text.join(Spec.Text.lines(s)),
    Brk.text(Spec.Brk.list(s)),
    s,
    Text.join_go(Spec.Brk.list(s), SNil{}),
    Brk.text_list(s)
  )

# Diff and merge
# --------------
# Line by line, through the views' shared sequence diff and merge.

# a and b end the same way
def End.is_eq(a: Spec.End, b: Spec.End) -> Bool:
  match a b:
    case Spec.LF{} Spec.LF{}:
      True{}
    case Spec.CRLF{} Spec.CRLF{}:
      True{}
    case Spec.CR{} Spec.CR{}:
      True{}
    case Spec.Eof{} Spec.Eof{}:
      True{}
    case _ _:
      False{}

# a and b are the same line: the same text and the same end
def Line.is_eq(a: Spec.Line, b: Spec.Line) -> Bool:
  match a b:
    case Spec.Line{t1, e1} Spec.Line{t2, e2}:
      List.all.if(u => End.is_eq(e1, e2), String.eq(t1, t2))

# the line edits of steps
def Text.edits(hs: List<&2, Views.Hunk<Spec.Line>>) -> List<&2, Spec.LineEdit>:
  match hs:
    case Nil{}:
      Nil{}
    case Con{Views.Hunk{s, d, i}, t}:
      Spec.LineEdit{s, d, i} <> Text.edits(t)

# the steps of line edits
def Text.steps(es: List<&2, Spec.LineEdit>) -> List<&2, Views.Hunk<Spec.Line>>:
  match es:
    case Nil{}:
      Nil{}
    case Con{Spec.LineEdit{s, d, i}, t}:
      Views.Hunk{s, d, i} <> Text.steps(t)

# the text of lines, if there are lines
def Text.joined(m: Maybe<&2, List<&2, Spec.Line>>) -> Maybe<&2, String>:
  match m:
    case None{}:
      None{}
    case Some{ls}:
      Some{Spec.Text.join(ls)}

# a collision of two different line changes is a clash
def Text.no_resolve(
  base: List<&2, Spec.Line>,
  a: Views.Hunk<Spec.Line>,
  b: Views.Hunk<Spec.Line>
) -> Maybe<&2, Views.Hunk<Spec.Line>>:
  None{}

def Spec.Text.diff(a, b):
  hs = Views.Seq.diff(~Spec.Line, ~Line.is_eq, Spec.Text.lines(a), Spec.Text.lines(b))
  Text.edits(Views.Seq.steps(~Spec.Line, hs, 0n, 0n))

def Spec.Text.patch(s, es):
  Text.joined(Views.Seq.patch(~Spec.Line, Text.steps(es), Some{Spec.Text.lines(s)}))

def Spec.Text.merge(base, x, y):
  ls = Views.Seq.merge(
    ~Spec.Line,
    ~Line.is_eq,
    ~Text.no_resolve,
    Spec.Text.lines(base),
    Spec.Text.lines(x),
    Spec.Text.lines(y)
  )
  Text.joined(ls)
