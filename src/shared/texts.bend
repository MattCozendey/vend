import Base
import ./bools.bend as Bools

# Text
# ----

# A text cut in two at a character: what comes before it, and after it.
type Cut is Data:
  Cut{before: String, after: String}
# the cut of c then a text, given the cut of that text
def Text.cut.on(c: Char, r: Maybe<&2, Cut>) -> Maybe<&2, Cut>:
  match r:
    case None{}:
      None{}
    case Some{Cut{b, a}}:
      Some{Cut{SCon{c, b}, a}}
# s cut at its first character with code x, or None when it has none
def Text.cut(s: String, +x: U32) -> Maybe<&2, Cut>:
  match s:
    case SNil{}:
      None{}
    case SCon{+c, +t}:
      Bools.Bool.when(
        Maybe<&2, Cut>,
        U32.is_eq(Char.to_u32(c), x),
        u => Some{Cut{SNil{}, t}},
        u => Text.cut.on(c, Text.cut(t, x))
      )
# s holds a character with code x
def Text.has(s: String, +x: U32) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      List.any.if(u => Text.has(t, x), U32.is_eq(Char.to_u32(c), x))
