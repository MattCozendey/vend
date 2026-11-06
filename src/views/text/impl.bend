import Base
import ../../shared.bend as Shared
import ./spec.bend as Spec

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
