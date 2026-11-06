import Base
import ../../conditions/spec.bend as Cond
import ../../graph/spec.bend as Graph
import ../../shared.bend as Shared
import ../text/spec.bend as Text

# C: a resource whose bytes are UTF-8 C source. Its document is its Text
# (the String), so its codec, meaning, diff and merge are Text's. What C
# adds is the graph: each #include is an edge, active under the conditions
# of the #if, #ifdef, #ifndef, #elif and #else around it. The preprocessor
# is not run: conditions stay formulas, so one graph covers every
# configuration.

# Logical lines
# -------------

# the last character of s is a backslash
def C.ends_bs(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, SNil{}}:
      U32.is_eq(Char.to_u32(c), 92)
    case SCon{c, t}:
      C.ends_bs(t)

# s without its last character
def C.drop_last(+s: String) -> String:
  String.take(s, Nat.sub(String.length(s), 1n))

# the logical lines of lines: a line that ends with a backslash goes on in
# the next one, without the backslash and the line end; acc is the logical
# line so far
def C.logical.go(lines: List<&2, Text.Line>, acc: String) -> List<&2, String>:
  match lines:
    case Nil{}:
      [acc]
    case Con{l, +t}:
      +x = String.append(acc, Text.Line.text(l))
      Shared.Bool.when(
        List<&2, String>,
        C.ends_bs(x),
        u => C.logical.go(t, C.drop_last(x)),
        u => x <> C.logical.go(t, SNil{})
      )

# the logical lines of the text s
def C.logical(s: String) -> List<&2, String>:
  C.logical.go(Text.Text.lines(s), SNil{})

# Expressions
# -----------
# The expression of #if. Grammar, loosest first:
#   or    := and ("||" and)*
#   and   := unary ("&&" unary)*
#   unary := "!" unary | "(" or ")" | "defined" "(" NAME ")" | "defined" NAME
#          | NUMBER | NAME
# "defined(X)" is the atom "defined(X)"; a bare NAME is the atom NAME (its
# value is not zero); a NUMBER of only zeros is Never, any other Always. An
# expression outside this grammar (arithmetic, comparisons) is one opaque
# atom: its own text.

# A token of an #if expression.
type Tok is Data:
  TDefined{}
  TName{name: String}
  TNum{zero: Bool}
  TNot{}
  TAnd{}
  TOr{}
  TOpen{}
  TClose{}
  TOther{}

# c starts a name: a letter or '_'
def C.is_start(+c: Char) -> Bool:
  Bool.or(Char.is_alpha(c), U32.is_eq(Char.to_u32(c), 95))

# c goes on a name: a letter, a digit or '_'
def C.is_name(+c: Char) -> Bool:
  Bool.or(C.is_start(c), Char.is_digit(c))

# the name at the start of s
def C.name.go(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, t}:
      Shared.Bool.when(String, C.is_name(c), u => SCon{c, C.name.go(t)}, u => SNil{})

# the digits at the start of s
def C.digits.go(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, t}:
      Shared.Bool.when(String, Char.is_digit(c), u => SCon{c, C.digits.go(t)}, u => SNil{})

# every character of s is '0'
def C.all_zero(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      List.all.if(u => C.all_zero(t), U32.is_eq(Char.to_u32(c), 48))

# One token at the start of a text and its length, or spaces to skip.
type Lexed is Data:
  Skip{len: Nat}
  Got{tok: Tok, len: Nat}

# the token of a name n: the keyword defined, or a name
def C.word(+n: String) -> Lexed:
  Shared.Bool.when(
    Lexed,
    String.eq(n, "defined"),
    u => Got{TDefined{}, 7n},
    u => Got{TName{n}, String.length(n)}
  )

# the token at the start of s for a character c (code x) that is not a
# space and does not start "&&", "||", "!=" or "!"
def C.token.one(+c: Char, +x: U32, +s: String) -> Lexed:
  Shared.Bool.when(
    Lexed,
    U32.is_eq(x, 40),
    v => Got{TOpen{}, 1n},
    v => Shared.Bool.when(
      Lexed,
      U32.is_eq(x, 41),
      w => Got{TClose{}, 1n},
      w => Shared.Bool.when(
        Lexed,
        C.is_start(c),
        y => C.word(C.name.go(s)),
        y => Shared.Bool.when(
          Lexed,
          Char.is_digit(c),
          z => Got{TNum{C.all_zero(C.digits.go(s))}, String.length(C.digits.go(s))},
          z => Got{TOther{}, 1n}
        )
      )
    )
  )

# the token at the start of s, whose first character is c (with code x)
def C.token(c: Char, +x: U32, +s: String) -> Lexed:
  +two = String.take(s, 2n)
  Shared.Bool.when(
    Lexed,
    Bool.or(U32.is_eq(x, 32), U32.is_eq(x, 9)),
    u => Skip{1n},
    u => Shared.Bool.when(
      Lexed,
      String.eq(two, "&&"),
      v => Got{TAnd{}, 2n},
      v => Shared.Bool.when(
        Lexed,
        String.eq(two, "||"),
        w => Got{TOr{}, 2n},
        w => Shared.Bool.when(
          Lexed,
          String.eq(two, "!="),
          y => Got{TOther{}, 2n},
          y => Shared.Bool.when(
            Lexed,
            U32.is_eq(x, 33),
            z => Got{TNot{}, 1n},
            z => C.token.one(c, x, s)
          )
        )
      )
    )
  )

# the tokens after l, the token at the start, then rest(n) for the text
# after its n characters
def C.lex.next(l: Lexed, rest: Nat -> List<&2, Tok>) -> List<&2, Tok>:
  match l:
    case Skip{n}:
      rest(n)
    case Got{t, n}:
      t <> rest(n)

# the tokens of s; fuel counts the characters left
def C.lex.go(fuel: Nat, +s: String) -> List<&2, Tok>:
  match fuel:
    case 0n:
      Nil{}
    case 1n+f:
      match s:
        case SNil{}:
          Nil{}
        case SCon{+c, t}:
          C.lex.next(C.token(c, Char.to_u32(c), s), n => C.lex.go(f, String.drop(s, n)))

# the tokens of s
def C.lex(+s: String) -> List<&2, Tok>:
  C.lex.go(String.length(s), s)

# A parse: the condition, and the tokens after it.
type Parsed is Data:
  Parsed{c: Cond.Cond, rest: List<&2, Tok>}

# Where the parser is in the grammar. More: after a first operand, acc,
# that more operands may follow.
type Level is Data:
  LOr{}
  LOrMore{acc: Cond.Cond}
  LAnd{}
  LAndMore{acc: Cond.Cond}
  LUnary{}

# k of the condition and the rest of a parse, or None for no parse
def C.then(
  m: Maybe<&2, Parsed>,
  k: Cond.Cond -> List<&2, Tok> -> Maybe<&2, Parsed>
) -> Maybe<&2, Parsed>:
  match m:
    case None{}:
      None{}
    case Some{Parsed{c, r}}:
      k(c, r)

# c, when the tokens go on with ")"
def C.close(c: Cond.Cond, toks: List<&2, Tok>) -> Maybe<&2, Parsed>:
  match toks:
    case Con{TClose{}, r}:
      Some{Parsed{c, r}}
    case _:
      None{}

# the atom "defined(x)"
def C.defined(x: String) -> Cond.Cond:
  Cond.Atom{String.append("defined(", String.append(x, ")"))}

# a parse of toks at the level lv; fuel bounds the steps
def C.parse(fuel: Nat, lv: Level, toks: List<&2, Tok>) -> Maybe<&2, Parsed>:
  match fuel:
    case 0n:
      None{}
    case 1n+(+f):
      match lv toks:
        case LOr{} ts:
          C.then(C.parse(f, LAnd{}, ts), c => r => C.parse(f, LOrMore{c}, r))
        case LOrMore{a} Con{TOr{}, r}:
          C.then(C.parse(f, LAnd{}, r), c => r2 => C.parse(f, LOrMore{Cond.Or{a, c}}, r2))
        case LOrMore{a} ts:
          Some{Parsed{a, ts}}
        case LAnd{} ts:
          C.then(C.parse(f, LUnary{}, ts), c => r => C.parse(f, LAndMore{c}, r))
        case LAndMore{a} Con{TAnd{}, r}:
          C.then(C.parse(f, LUnary{}, r), c => r2 => C.parse(f, LAndMore{Cond.And{a, c}}, r2))
        case LAndMore{a} ts:
          Some{Parsed{a, ts}}
        case LUnary{} Con{TNot{}, r}:
          C.then(C.parse(f, LUnary{}, r), c => r2 => Some{Parsed{Cond.Not{c}, r2}})
        case LUnary{} Con{TOpen{}, r}:
          C.then(C.parse(f, LOr{}, r), c => r2 => C.close(c, r2))
        case LUnary{} Con{TDefined{}, Con{TOpen{}, Con{TName{x}, Con{TClose{}, r}}}}:
          Some{Parsed{C.defined(x), r}}
        case LUnary{} Con{TDefined{}, Con{TName{x}, r}}:
          Some{Parsed{C.defined(x), r}}
        case LUnary{} Con{TName{x}, r}:
          Some{Parsed{Cond.Atom{x}, r}}
        case LUnary{} Con{TNum{z}, r}:
          Some{Parsed{Shared.Bool.when(Cond.Cond, z, u => Cond.Never{}, u => Cond.Always{}), r}}
        case LUnary{} ts:
          None{}

# the condition of a whole parse, or the opaque atom of the text
def C.expr.of(m: Maybe<&2, Parsed>, text: String) -> Cond.Cond:
  match m:
    case Some{Parsed{c, Nil{}}}:
      c
    case _:
      Cond.Atom{text}

# the condition of the #if expression text
def C.expr(t: String) -> Cond.Cond:
  +text = String.trim(t)
  +toks = C.lex(text)
  fuel = Nat.mul(8n, 1n+List.length(&2, Tok, toks))
  C.expr.of(C.parse(fuel, LOr{}, toks), text)

# Directives
# ----------

# A preprocessor line, as far as the graph cares.
type Directive is Data:
  DIf{c: Cond.Cond}
  DElif{c: Cond.Cond}
  DElse{}
  DEndif{}
  DQuote{path: String}
  DAngle{path: String}
  DNone{}

# the text of s up to the first character with code x
def C.until(s: String, +x: U32) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, t}:
      Shared.Bool.when(
        String,
        U32.is_eq(Char.to_u32(c), x),
        u => SNil{},
        u => SCon{c, C.until(t, x)}
      )

# the include of rest: "path" or <path>
def C.include(+rest: String) -> Directive:
  Shared.Bool.when(
    Directive,
    String.starts_with(rest, SCon{Chr{34}, SNil{}}),
    u => DQuote{C.until(String.drop(rest, 1n), 34)},
    u => Shared.Bool.when(
      Directive,
      String.starts_with(rest, "<"),
      v => DAngle{C.until(String.drop(rest, 1n), 62)},
      v => DNone{}
    )
  )

# the directive with keyword w and the text rest after it
def C.keyword(+w: String, +rest: String) -> Directive:
  +name = C.name.go(rest)
  Shared.Bool.when(
    Directive,
    String.eq(w, "if"),
    u => DIf{C.expr(rest)},
    u => Shared.Bool.when(
      Directive,
      String.eq(w, "ifdef"),
      v => DIf{C.defined(name)},
      v => Shared.Bool.when(
        Directive,
        String.eq(w, "ifndef"),
        x => DIf{Cond.Not{C.defined(name)}},
        x => Shared.Bool.when(
          Directive,
          String.eq(w, "elif"),
          y => DElif{C.expr(rest)},
          y => Shared.Bool.when(
            Directive,
            String.eq(w, "else"),
            z => DElse{},
            z => Shared.Bool.when(
              Directive,
              String.eq(w, "endif"),
              q => DEndif{},
              q => Shared.Bool.when(
                Directive,
                String.eq(w, "include"),
                r => C.include(rest),
                r => DNone{}
              )
            )
          )
        )
      )
    )
  )

# the directive of a logical line: '#' after spaces, then a keyword
def C.directive(line: String) -> Directive:
  +t = String.trim_start(line)
  +d = String.trim_start(String.drop(t, 1n))
  +w = C.name.go(d)
  Shared.Bool.when(
    Directive,
    String.starts_with(t, "#"),
    u => C.keyword(w, String.trim(String.drop(d, String.length(w)))),
    u => DNone{}
  )

# Edges
# -----

# An open #if: taken holds when an earlier branch was chosen, cur when the
# current branch is.
type Branch is Data:
  Branch{taken: Cond.Cond, cur: Cond.Cond}

# the condition under the open branches
def C.active(stack: List<&2, Branch>) -> Cond.Cond:
  match stack:
    case Nil{}:
      Cond.Always{}
    case Con{Branch{t, c}, r}:
      Cond.And{c, C.active(r)}

# the directives of logical lines
def C.directives(ls: List<&2, String>) -> List<&2, Directive>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{l, t}:
      C.directive(l) <> C.directives(t)

# the branches after #elif c: the top branch takes c where no earlier
# branch was
def C.elif(stack: List<&2, Branch>, +c: Cond.Cond) -> List<&2, Branch>:
  match stack:
    case Nil{}:
      Nil{}
    case Con{Branch{+tk, cu}, r}:
      Branch{Cond.Or{tk, c}, Cond.And{Cond.Not{tk}, c}} <> r

# the branches after #else: the top branch takes what no earlier branch took
def C.else(stack: List<&2, Branch>) -> List<&2, Branch>:
  match stack:
    case Nil{}:
      Nil{}
    case Con{Branch{tk, cu}, r}:
      Branch{Cond.Always{}, Cond.Not{tk}} <> r

# the edges of the directives from n, under the open branches. #if c opens
# a branch with c; #elif c takes c where no earlier branch was; #else takes
# what no earlier branch took; #endif closes one. An #elif, #else or #endif
# with no open #if is ignored, and an #if left open ends at the end of the
# file.
def C.edges.go(
  ds: List<&2, Directive>,
  +stack: List<&2, Branch>,
  +n: Shared.Name
) -> List<&2, Graph.Edge>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{DIf{+c}, t}:
      C.edges.go(t, Branch{c, c} <> stack, n)
    case Con{DElif{c}, t}:
      C.edges.go(t, C.elif(stack, c), n)
    case Con{DElse{}, t}:
      C.edges.go(t, C.else(stack), n)
    case Con{DEndif{}, t}:
      C.edges.go(t, List.tail(&2, Branch, stack), n)
    case Con{DQuote{p}, t}:
      to = Graph.Target.resolve(n, String.append("./", p))
      Graph.Edge{n, to, Graph.CView{}, Graph.Whole{}, C.active(stack)} <> C.edges.go(t, stack, n)
    case Con{DAngle{p}, t}:
      to = {Graph.Unresolved{String.append("<", String.append(p, ">"))}: Graph.Target}
      Graph.Edge{n, to, Graph.CView{}, Graph.Whole{}, C.active(stack)} <> C.edges.go(t, stack, n)
    case Con{DNone{}, t}:
      C.edges.go(t, stack, n)

# the edges of the C text s of the resource n: one per #include
def C.edges(n: Shared.Name, s: String) -> List<&2, Graph.Edge>:
  C.edges.go(C.directives(C.logical(s)), [], n)
