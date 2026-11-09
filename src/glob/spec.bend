import Base

# A path is a String: segments joined by '/'. It has no leading or trailing
# '/', and no empty, "." or ".." segment. A segment has no NUL and no '\'.
# Case and Unicode form are exact: no folding, no normalization.

# a character that no segment may hold: NUL or '\'
def is_banned(c: Char) -> Bool:
  match c:
    case Chr{+x}:
      Bool.or(U32.is_eq(x, 0), U32.is_eq(x, 92))

# s is a valid segment
def is_segment(s: String) -> Bool:
  +s = s
  ok = Bool.not(List.any(~&2, ~Char, ~is_banned, String.to_list(s)))
  dots = Bool.or(String.eq(s, "."), String.eq(s, ".."))
  Bool.and(Bool.not(String.is_empty(s)), Bool.and(Bool.not(dots), ok))

# s is a valid path
def is_path(s: String) -> Bool:
  List.all(~&2, ~String, ~is_segment, String.split(s, '/'))

# A glob, as a tree. A parser turns glob text into one; Void and Eps let
# matching state what is left of a glob after some characters.
type Glob is Data:
  void{}
  eps{}
  lit{c: Char}
  any{}
  star{}
  class{neg: Bool, cs: List<&2, Char>}
  deep{}
  cat{a: Glob, b: Glob}
  alt{a: Glob, b: Glob}

# Void: no text. Eps: only "". Lit: c. Any (`?`): one character.
# Star (`*`): any text. Class (`[...]`, `[!...]` when neg): one character
# in cs, or not in cs. None of these five matches '/'. Deep (`**`): any
# text, '/' included. Cat: a, then b. Alt (`{a,b}`): a or b.

# Eps for True, Void for False
def Glob.of_bool(b: Bool) -> Glob:
  match b:
    case False{}:
      void{}
    case True{}:
      eps{}

# g matches ""
# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a glob tree is a few nodes, and a short-circuit match would need mutual recursion, which Bend refuses
def Glob.is_nullable(g: Glob) -> Bool:
  match g:
    case void{}:
      False{}
    case eps{}:
      True{}
    case lit{c}:
      False{}
    case any{}:
      False{}
    case star{}:
      True{}
    case class{neg, cs}:
      False{}
    case deep{}:
      True{}
    case cat{a, b}:
      Bool.and(Glob.is_nullable(a), Glob.is_nullable(b))
    case alt{a, b}:
      Bool.or(Glob.is_nullable(a), Glob.is_nullable(b))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# c is not '/'
def is_inner(c: Char) -> Bool:
  Bool.not(Char.is_eq(c, '/'))

# what g must still match after it reads c
def Glob.step(g: Glob, +c: Char) -> Glob:
  match g:
    case void{}:
      void{}
    case eps{}:
      void{}
    case lit{x}:
      Glob.of_bool(Char.is_eq(x, c))
    case any{}:
      Glob.of_bool(is_inner(c))
    case star{}:
      cat{Glob.of_bool(is_inner(c)), star{}}
    case class{neg, cs}:
      hit = Bool.xor(neg, List.contains(~Char, ~Char.is_eq, cs, c))
      Glob.of_bool(Bool.and(is_inner(c), hit))
    case deep{}:
      deep{}
    # bend-lint: expect-begin bend-lint-rules/performance/missed_fork@hint -- a glob tree is a few nodes, where a fork costs more than it saves
    case cat{+a, +b}:
      n = Glob.is_nullable(a)
      alt{cat{Glob.step(a, c), b}, cat{Glob.of_bool(n), Glob.step(b, c)}}
    case alt{a, b}:
      alt{Glob.step(a, c), Glob.step(b, c)}
    # bend-lint: expect-end bend-lint-rules/performance/missed_fork@hint

# g matches all of s
def Glob.matches(s: String, g: Glob) -> Bool:
  match s:
    case SNil{}:
      Glob.is_nullable(g)
    case SCon{c, t}:
      Glob.matches(t, Glob.step(g, c))

# One line of a selector: `g` includes, `!g` excludes.
type Rule is Data:
  include{g: Glob}
  exclude{g: Glob}

# the answer for p after rules, given the answer acc before them
def Rule.selects.go(rules: List<&2, Rule>, +p: String, acc: Bool) -> Bool:
  match rules acc:
    case Nil{} _:
      acc
    case Con{include{g}, t} False{}:
      Rule.selects.go(t, p, Glob.matches(p, g))
    case Con{include{g}, t} True{}:
      Rule.selects.go(t, p, True{})
    case Con{exclude{g}, t} False{}:
      Rule.selects.go(t, p, False{})
    case Con{exclude{g}, t} True{}:
      Rule.selects.go(t, p, Bool.not(Glob.matches(p, g)))

# the last rule that matches p decides; with no match, p is not selected
def Rule.selects(rules: List<&2, Rule>, p: String) -> Bool:
  Rule.selects.go(rules, p, False{})

# A question about two rule lists: is there a valid path that
# Both: a and b select? Only: a selects and b does not?
# "No path for Only{a, b}" means: b covers a.
type Query is Data:
  both{a: List<&2, Rule>, b: List<&2, Rule>}
  only{a: List<&2, Rule>, b: List<&2, Rule>}

# p is a valid path that answers q
def Query.holds(q: Query, +p: String) -> Bool:
  # bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- only laws use it; no program runs it
  match q:
    case both{a, b}:
      Bool.and(is_path(p), Bool.and(Rule.selects(a, p), Rule.selects(b, p)))
    case only{a, b}:
      in_a = Rule.selects(a, p)
      Bool.and(is_path(p), Bool.and(in_a, Bool.not(Rule.selects(b, p))))
  # bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# The answer of a search. Found: a path that answers the query. Absent: no
# path answers it. Unknown: the search ran out of steps; it claims nothing.
type Search is Data:
  found{path: String}
  absent{}
  unknown{}

# the answer to q
law Query.search:
  for q: Query
  Search

# a Found path answers q
law search_found:
  for q: Query
  for p: String
  for h: {Query.search(q) == found{p}: Search}
  {Query.holds(q, p) == True{}: Bool}

# after an Absent answer, no path answers q
law search_absent:
  for q: Query
  for p: String
  for h: {Query.search(q) == absent{}: Search}
  {Query.holds(q, p) == False{}: Bool}

# Glob text. `\c` is the character c. `?`, `*`, `[...]`, `[!...]` and
# `{a,b,...}` are Any, Star, Class and Alt. In a class, `x-y` is every
# character from x to y. `**` is a whole segment: alone it is Deep, and `**/`
# also matches "". A ',' outside braces is itself. Text that starts with '/'
# is an error. A rule line that starts with `!` is an Exclude.

# the role of a character in glob text
type Sym is Data:
  s_esc{}
  s_any{}
  s_star{}
  s_slash{}
  s_open{}
  s_comma{}
  s_close{}
  s_left{}
  s_right{}
  s_bang{}
  s_dash{}
  s_char{c: Char}

# the character of s
def Sym.char(s: Sym) -> Char:
  match s:
    case s_esc{}:
      Chr{92}
    case s_any{}:
      Chr{63}
    case s_star{}:
      Chr{42}
    case s_slash{}:
      Chr{47}
    case s_open{}:
      Chr{123}
    case s_comma{}:
      Chr{44}
    case s_close{}:
      Chr{125}
    case s_left{}:
      Chr{91}
    case s_right{}:
      Chr{93}
    case s_bang{}:
      Chr{33}
    case s_dash{}:
      Chr{45}
    case s_char{c}:
      c

# every role but SChar
def Sym.specials() -> List<&2, Sym>:
  [
    s_esc{},
    s_any{},
    s_star{},
    s_slash{},
    s_open{},
    s_comma{},
    s_close{},
    s_left{},
    s_right{},
    s_bang{},
    s_dash{}
  ]

# s when hit, else rest()
def Sym.of.if(s: Sym, rest: Unit -> Sym, hit: Bool) -> Sym:
  match hit:
    case False{}:
      rest(Unit{})
    case True{}:
      s

# the first role in specials whose character is c, else SChar{c}
def Sym.of.go(specials: List<&2, Sym>, +c: Char) -> Sym:
  match specials:
    case Nil{}:
      s_char{c}
    case Con{+s, t}:
      Sym.of.if(s, u => Sym.of.go(t, c), Char.is_eq(Sym.char(s), c))

# the role of c
def Sym.of(c: Char) -> Sym:
  Sym.of.go(Sym.specials(), c)

# lo, then the next n characters
def Char.range.go(n: Nat, +lo: U32) -> List<&2, Char>:
  match n:
    case 0n:
      [Chr{lo}]
    case 1n+p:
      Chr{lo} <> Char.range.go(p, (lo + 1: U32))

# lo and the n characters after it, or None when ok is False
def Char.range.if(lo: U32, n: Nat, ok: Bool) -> Maybe<&2, List<&2, Char>>:
  match ok:
    case False{}:
      None{}
    case True{}:
      Some{Char.range.go(n, lo)}

# every character from lo to hi, or None when hi comes before lo
def Char.range(lo: Char, hi: Char) -> Maybe<&2, List<&2, Char>>:
  match lo hi:
    case Chr{+a} Chr{+b}:
      Char.range.if(a, U32.to_nat((b - a: U32)), U32.is_le(a, b))

# Inside a `{`: the alternatives so far and the atoms of the current one,
# both last first, and whether the `{` opened at the start of a segment.
# The bottom frame is the whole text.
type Frame is Data:
  Frame{alts: List<&2, Glob>, seq: List<&2, Glob>, start: Bool}

# Out: between atoms. After: just after a `**`, where the segment must end.
# In: inside a class, with its characters so far.
type Mode is Data:
  out{}
  after{}
  in{neg: Bool, cs: List<&2, Char>}

# the atoms, last first, before acc
def Glob.of_seq(atoms: List<&2, Glob>, acc: Glob) -> Glob:
  match atoms:
    case Nil{}:
      acc
    case Con{h, t}:
      Glob.of_seq(t, cat{h, acc})

# the alternatives, last first, before acc
def Glob.of_alts(alts: List<&2, Glob>, acc: Glob) -> Glob:
  match alts:
    case Nil{}:
      acc
    case Con{h, t}:
      Glob.of_alts(t, alt{h, acc})

# the stack with g after the atoms of its top frame
def Frame.add(stack: List<&2, Frame>, g: Glob) -> List<&2, Frame>:
  match stack:
    case Nil{}:
      Nil{}
    case Con{Frame{alts, seq, start}, t}:
      Con{Frame{alts, Con{g, seq}, start}, t}

# the glob at the end of the text: only the bottom frame may be open
def Glob.read.end(stack: List<&2, Frame>) -> Maybe<&2, Glob>:
  match stack:
    case Con{Frame{alts, seq, start}, Nil{}}:
      Some{Glob.of_seq(seq, eps{})}
    case _:
      None{}

# k of the range r, or None when r is None
def Glob.read.range(
  r: Maybe<&2, List<&2, Char>>,
  k: List<&2, Char> -> Maybe<&2, Glob>
) -> Maybe<&2, Glob>:
  match r:
    case None{}:
      None{}
    case Some{cs}:
      k(cs)

# `**/`: "", or any text that ends with '/'
def Glob.dirs() -> Glob:
  alt{eps{}, cat{deep{}, lit{Chr{47}}}}

# k(), or None when seg is False: a `**` must start a segment
def Glob.read.at_seg(seg: Bool, k: Unit -> Maybe<&2, Glob>) -> Maybe<&2, Glob>:
  match seg:
    case False{}:
      None{}
    case True{}:
      k(Unit{})

# k(), or None after a `**`, where a ',' that is itself would continue
# the segment
def Glob.read.mid(m: Mode, k: Unit -> Maybe<&2, Glob>) -> Maybe<&2, Glob>:
  match m:
    case after{}:
      None{}
    case _:
      k(Unit{})

# the glob that syms spell, in mode, inside stack; seg: at a segment start
def Glob.read.go(
  syms: List<&2, Sym>,
  mode: Mode,
  stack: List<&2, Frame>,
  +seg: Bool
) -> Maybe<&2, Glob>:
  match syms mode:
    case Nil{} out{}:
      Glob.read.end(stack)
    case Nil{} in{neg, cs}:
      None{}
    case Con{s_esc{}, Nil{}} _:
      None{}
    case Con{s_esc{}, Con{x, t}} out{}:
      Glob.read.go(t, out{}, Frame.add(stack, lit{Sym.char(x)}), False{})
    case Con{s_esc{}, Con{x, t}} in{neg, cs}:
      Glob.read.go(t, in{neg, Con{Sym.char(x), cs}}, stack, seg)
    case Con{s_right{}, t} out{}:
      None{}
    case Con{s_right{}, t} in{neg, cs}:
      Glob.read.go(t, out{}, Frame.add(stack, class{neg, cs}), False{})
    case Con{x, Con{s_dash{}, Con{s_right{}, t}}} in{neg, cs}:
      None{}
    case Con{x, Con{s_dash{}, Con{s_esc{}, t}}} in{neg, cs}:
      None{}
    case Con{x, Con{s_dash{}, Con{y, t}}} in{neg, cs}:
      r = Char.range(Sym.char(x), Sym.char(y))
      Glob.read.range(r, rs => Glob.read.go(t, in{neg, List.append(&2, Char, rs, cs)}, stack, seg))
    case Con{x, t} in{neg, cs}:
      Glob.read.go(t, in{neg, Con{Sym.char(x), cs}}, stack, seg)
    case Con{s_any{}, t} _:
      Glob.read.go(t, out{}, Frame.add(stack, any{}), False{})
    case Nil{} after{}:
      Glob.read.end(stack)
    case Con{s_comma{}, t} m:
      match stack:
        case Con{Frame{alts, seq, +start}, Con{f, r}}:
          branch = Glob.of_seq(seq, eps{})
          up = {Con{Frame{Con{branch, alts}, [], start}, Con{f, r}}: List<&2, Frame>}
          Glob.read.go(t, out{}, up, start)
        case _:
          Glob.read.mid(m, u => Glob.read.go(t, out{}, Frame.add(stack, lit{Chr{44}}), False{}))
    case Con{s_close{}, t} _:
      match stack:
        case Con{Frame{alts, seq, start}, Con{f, r}}:
          branch = Glob.of_seq(seq, eps{})
          g = Glob.of_alts(Con{branch, alts}, void{})
          Glob.read.go(t, out{}, Frame.add(Con{f, r}, g), False{})
        case _:
          None{}
    case Con{x, t} after{}:
      None{}
    case Con{s_star{}, Con{s_star{}, Con{s_slash{}, t}}} _:
      dirs = Glob.dirs()
      Glob.read.at_seg(seg, u => Glob.read.go(t, out{}, Frame.add(stack, dirs), True{}))
    case Con{s_star{}, Con{s_star{}, t}} _:
      Glob.read.at_seg(seg, u => Glob.read.go(t, after{}, Frame.add(stack, deep{}), False{}))
    case Con{s_star{}, t} _:
      Glob.read.go(t, out{}, Frame.add(stack, star{}), False{})
    case Con{s_slash{}, t} _:
      Glob.read.go(t, out{}, Frame.add(stack, lit{Chr{47}}), True{})
    case Con{s_open{}, t} _:
      Glob.read.go(t, out{}, Con{Frame{[], [], seg}, stack}, seg)
    case Con{s_left{}, Con{s_bang{}, t}} _:
      Glob.read.go(t, in{True{}, []}, stack, seg)
    case Con{s_left{}, t} _:
      Glob.read.go(t, in{False{}, []}, stack, seg)
    case Con{x, t} _:
      Glob.read.go(t, out{}, Frame.add(stack, lit{Sym.char(x)}), False{})

# the glob that syms spell; text that starts with '/' is an error
def Glob.read.syms(+syms: List<&2, Sym>) -> Maybe<&2, Glob>:
  match syms:
    case Con{s_slash{}, t}:
      None{}
    case _:
      Glob.read.go(syms, out{}, [Frame{[], [], True{}}], True{})

# the symbols of text s
def Sym.list(s: String) -> List<&2, Sym>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{c, t}:
      Sym.of(c) <> Sym.list(t)

# the glob that text s spells, or None for bad text
def Glob.read(s: String) -> Maybe<&2, Glob>:
  Glob.read.syms(Sym.list(s))

# the rule that syms spell: a leading `!` excludes
def Rule.read.syms(+syms: List<&2, Sym>) -> Maybe<&2, Rule>:
  match syms:
    case Con{s_bang{}, t}:
      Maybe.map(&2, Glob, Rule, g => exclude{g}, Glob.read.syms(t))
    case _:
      Maybe.map(&2, Glob, Rule, g => include{g}, Glob.read.syms(syms))

# the rule that line s spells, or None for bad text
def Rule.read(s: String) -> Maybe<&2, Rule>:
  Rule.read.syms(Sym.list(s))

# text that spells g
law Glob.show:
  for g: Glob
  String

# text that spells exactly the path p
law Glob.escape:
  for p: String
  String

# g and h match the same strings
def Glob.Same(g: Glob, h: Glob) -> Type:
  @p: String -> {Glob.matches(p, g) == Glob.matches(p, h): Bool}

# the text of g reads back as a glob that matches what g matches
law read_after_show:
  for g: Glob
  exs h: Glob
  {Glob.read(Glob.show(g)) == Some{h}: Maybe<&2, Glob>} & Glob.Same(g, h)

# text that starts with '/' is an error
law read_rejects_root:
  for s: String
  {Glob.read(SCon{'/', s}) == None{}: Maybe<&2, Glob>}

# the escaped text of a valid path p matches p and nothing else
law read_after_escape:
  for p: String
  for v: {is_path(p) == True{}: Bool}
  exs h: Glob
  {Glob.read(Glob.escape(p)) == Some{h}: Maybe<&2, Glob>} &
    (@q: String -> {Glob.matches(q, h) == String.eq(q, p): Bool})
