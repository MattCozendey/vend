import Base
import ./bools.bend as Bools
import ./shared.bend as Shared
import ./words.bend as Words

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

# the text before the cut
def Cut.before(c: Cut) -> String:
  match c:
    case Cut{b, a}:
      b

# the text after the cut
def Cut.after(c: Cut) -> String:
  match c:
    case Cut{b, a}:
      a

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# a text after "nothing more" is itself
def Text.drop_none(s: String) -> {String.drop(s, 0n) == s: String}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      {==}

# a text with nothing after it is itself
def Text.append_none(a: String) -> {String.append(a, "") == a: String}:
  match a:
    case SNil{}:
      {==}
    case SCon{c, t}:
      Equal.cong(String, String, z => SCon{c, z}, String.append(t, ""), t, Text.append_none(t))

# Text.cut_none at the first character c, by whether it has the code x (hit)
def Text.cut_none.at(
  hit: Bool,
  c: Char,
  t: String,
  x: U32,
  ih: {Text.has(t, x) == False{}: Bool} -> {Text.cut(t, x) == None{}: Maybe<&2, Cut>}
) -> {
  U32.is_eq(Char.to_u32(c), x) == hit: Bool
} -> {
  List.any.if(u => Text.has(t, x), hit) == False{}: Bool
} -> {
  Bools.Bool.when(
    Maybe<&2, Cut>,
    hit,
    u => Some{Cut{SNil{}, t}},
    u => Text.cut.on(c, Text.cut(t, x))
  )
    == None{}: Maybe<&2, Cut>
}:
  match hit:
    case True{}:
      e => h => Empty.absurd(
        {Some{Cut{SNil{}, t}} == None{}: Maybe<&2, Cut>},
        Shared.Bool.false_ne_true(Equal.sym(Bool, True{}, False{}, h))
      )
    case False{}:
      e => h =>
        %Equal.sym(
          Maybe<&2, Cut>,
          Text.cut(t, x),
          None{},
          ih(h)
        ): {Text.cut.on(c, _) == None{}: Maybe<&2, Cut>}
        {==}

# a text without the code x has no cut at x
def Text.cut_none(
  s: String,
  +x: U32
) -> {Text.has(s, x) == False{}: Bool} -> {Text.cut(s, x) == None{}: Maybe<&2, Cut>}:
  match s:
    case SNil{}:
      h => {==}
    case SCon{+c, +t}:
      Text.cut_none.at(U32.is_eq(Char.to_u32(c), x), c, t, x, Text.cut_none(t, x))({==})

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Text.cut_at at the first character h of a, by whether it has the code x (hit)
def Text.cut_at.at(
  hit: Bool,
  h: Char,
  t: String,
  c: Char,
  b: String,
  x: U32,
  ih: {
    Text.has(t, x) == False{}: Bool
  } -> {Text.cut(String.append(t, SCon{c, b}), x) == Some{Cut{t, b}}: Maybe<&2, Cut>}
) -> {
  U32.is_eq(Char.to_u32(h), x) == hit: Bool
} -> {
  List.any.if(u => Text.has(t, x), hit) == False{}: Bool
} -> {
  Bools.Bool.when(
    Maybe<&2, Cut>,
    hit,
    u => Some{Cut{SNil{}, String.append(t, SCon{c, b})}},
    u => Text.cut.on(h, Text.cut(String.append(t, SCon{c, b}), x))
  )
    == Some{Cut{SCon{h, t}, b}}: Maybe<&2, Cut>
}:
  match hit:
    case True{}:
      e => hh => Empty.absurd(
        {
          Some{
            Cut{SNil{}, String.append(t, SCon{c, b})}
          }
            == Some{Cut{SCon{h, t}, b}}: Maybe<&2, Cut>
        },
        Shared.Bool.false_ne_true(Equal.sym(Bool, True{}, False{}, hh))
      )
    case False{}:
      e => hh =>
        %Equal.sym(
          Maybe<&2, Cut>,
          Text.cut(String.append(t, SCon{c, b}), x),
          Some{Cut{t, b}},
          ih(hh)
        ): {Text.cut.on(h, _) == Some{Cut{SCon{h, t}, b}}: Maybe<&2, Cut>}
        {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# a text a without the code x, then a character c with it, then b, cuts into
# a and b
def Text.cut_at(
  a: String,
  +c: Char,
  +b: String,
  +x: U32
) -> {
  Text.has(a, x) == False{}: Bool
} -> {
  U32.is_eq(Char.to_u32(c), x) == True{}: Bool
} -> {Text.cut(String.append(a, SCon{c, b}), x) == Some{Cut{a, b}}: Maybe<&2, Cut>}:
  match a:
    case SNil{}:
      ha => hc =>
        %Equal.sym(
          Bool,
          U32.is_eq(Char.to_u32(c), x),
          True{},
          hc
        ): {
          Bools.Bool.when(
            Maybe<&2, Cut>,
            _,
            u => Some{Cut{SNil{}, b}},
            u => Text.cut.on(c, Text.cut(b, x))
          )
            == Some{Cut{SNil{}, b}}: Maybe<&2, Cut>
        }
        {==}
    case SCon{+h, +t}:
      ha => +hc => Text.cut_at.at(
        U32.is_eq(Char.to_u32(h), x),
        h,
        t,
        c,
        b,
        x,
        hh => Text.cut_at(t, c, b, x)(hh)(hc)
      )({==})(ha)

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Text.cut_parts once the rest is cut: by what it held (m)
def Text.cut_parts.on(
  m: Maybe<&2, Cut>,
  c: Char,
  t: String,
  x: U32,
  a: String,
  b: String,
  ih: @a2: String -> @b2: String -> {
    Text.cut(t, x) == Some{Cut{a2, b2}}: Maybe<&2, Cut>
  } -> {t == String.append(a2, SCon{Chr{x}, b2}): String}
) -> {
  Text.cut(t, x) == m: Maybe<&2, Cut>
} -> {
  Text.cut.on(c, m) == Some{Cut{a, b}}: Maybe<&2, Cut>
} -> {SCon{c, t} == String.append(a, SCon{Chr{x}, b}): String}:
  match m:
    case None{}:
      e => h => Empty.absurd(
        {SCon{c, t} == String.append(a, SCon{Chr{x}, b}): String},
        Shared.Bool.false_ne_true(
          Equal.cong(
            Maybe<&2, Cut>,
            Bool,
            z => Maybe.is_some(&2, Cut, z),
            None{},
            Some{Cut{a, b}},
            h
          )
        )
      )
    case Some{Cut{a2, b2}}:
      e => +h =>
        %Equal.cong(
          Maybe<&2, Cut>,
          String,
          z => Cut.before(Maybe.default(&2, Cut, z, Cut{"", ""})),
          Some{Cut{SCon{c, a2}, b2}},
          Some{Cut{a, b}},
          h
        ): {SCon{c, t} == String.append(_, SCon{Chr{x}, b}): String}
        %Equal.cong(
          Maybe<&2, Cut>,
          String,
          z => Cut.after(Maybe.default(&2, Cut, z, Cut{"", ""})),
          Some{Cut{SCon{c, a2}, b2}},
          Some{Cut{a, b}},
          h
        ): {SCon{c, t} == String.append(SCon{c, a2}, SCon{Chr{x}, _}): String}
        Equal.cong(
          String,
          String,
          z => SCon{c, z},
          t,
          String.append(a2, SCon{Chr{x}, b2}),
          ih(a2)(b2)(e)
        )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# a character whose code is x is the character x
def Text.cut_parts.chr(
  c: Char,
  t: String,
  x: U32
) -> {U32.is_eq(Char.to_u32(c), x) == True{}: Bool} -> {SCon{c, t} == SCon{Chr{x}, t}: String}:
  match c:
    case Chr{y}:
      e => Equal.cong(U32, String, z => SCon{Chr{z}, t}, y, x, Words.U32.is_eq_sound(y, x)(e))
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Text.cut_parts at the first character c, by whether it has the code x (hit)
def Text.cut_parts.at(
  hit: Bool,
  c: Char,
  +t: String,
  +x: U32,
  a: String,
  b: String,
  ih: @a2: String -> @b2: String -> {
    Text.cut(t, x) == Some{Cut{a2, b2}}: Maybe<&2, Cut>
  } -> {t == String.append(a2, SCon{Chr{x}, b2}): String}
) -> {
  U32.is_eq(Char.to_u32(c), x) == hit: Bool
} -> {
  Bools.Bool.when(
    Maybe<&2, Cut>,
    hit,
    u => Some{Cut{SNil{}, t}},
    u => Text.cut.on(c, Text.cut(t, x))
  )
    == Some{Cut{a, b}}: Maybe<&2, Cut>
} -> {SCon{c, t} == String.append(a, SCon{Chr{x}, b}): String}:
  match hit:
    case True{}:
      +e => +h =>
        %Equal.cong(
          Maybe<&2, Cut>,
          String,
          z => Cut.before(Maybe.default(&2, Cut, z, Cut{"", ""})),
          Some{Cut{SNil{}, t}},
          Some{Cut{a, b}},
          h
        ): {SCon{c, t} == String.append(_, SCon{Chr{x}, b}): String}
        %Equal.cong(
          Maybe<&2, Cut>,
          String,
          z => Cut.after(Maybe.default(&2, Cut, z, Cut{"", ""})),
          Some{Cut{SNil{}, t}},
          Some{Cut{a, b}},
          h
        ): {SCon{c, t} == SCon{Chr{x}, _}: String}
        Text.cut_parts.chr(c, t, x)(e)
    case False{}:
      e => h => Text.cut_parts.on(Text.cut(t, x), c, t, x, a, b, ih)({==})(h)
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# a text cut at the code x is what comes before, that character, and what
# comes after
def Text.cut_parts(
  s: String,
  +x: U32,
  a: String,
  b: String
) -> {
  Text.cut(s, x) == Some{Cut{a, b}}: Maybe<&2, Cut>
} -> {s == String.append(a, SCon{Chr{x}, b}): String}:
  match s:
    case SNil{}:
      h => Empty.absurd(
        {SNil{} == String.append(a, SCon{Chr{x}, b}): String},
        Shared.Bool.false_ne_true(
          Equal.cong(
            Maybe<&2, Cut>,
            Bool,
            z => Maybe.is_some(&2, Cut, z),
            None{},
            Some{Cut{a, b}},
            h
          )
        )
      )
    case SCon{+c, +t}:
      Text.cut_parts.at(
        U32.is_eq(Char.to_u32(c), x),
        c,
        t,
        x,
        a,
        b,
        a2 => b2 => Text.cut_parts(t, x, a2, b2)
      )({==})
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information
