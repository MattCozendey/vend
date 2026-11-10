import Base
import ../shared/shared/regex.bend as Regex

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

# A glob, as a tree. A parser turns glob text into one.
type Glob is Data:
  Void{}
  Eps{}
  Lit{c: Char}
  Any{}
  Star{}
  Class{neg: Bool, cs: List<&2, Char>}
  Deep{}
  Cat{a: Glob, b: Glob}
  Alt{a: Glob, b: Glob}

# Void: no text. Eps: only "". Lit: c. Any (`?`): one character.
# Star (`*`): any text. Class (`[...]`, `[!...]` when neg): one character
# in cs, or not in cs. None of these five matches '/'. Deep (`**`): any
# text, '/' included. Cat: a, then b. Alt (`{a,b}`): a or b.

# c is not '/'
def is_inner(c: Char) -> Bool:
  Bool.not(Char.is_eq(c, '/'))

# Matching is that of regular expressions (regex.bend): a glob is an
# expression over characters, whose atoms are the three forms that read one
# character.

# What reads one character: the character c, any character but '/', or a
# class (a character in cs, or one not in cs when neg; never '/').
type Atom is Data:
  ALit{c: Char}
  AAny{}
  AClass{neg: Bool, cs: List<&2, Char>}

# t accepts c
def Atom.hit(t: Atom, c: Char) -> Bool:
  match t:
    case ALit{x}:
      Char.is_eq(x, c)
    case AAny{}:
      is_inner(c)
    case AClass{neg, cs}:
      +c = c
      List.all.if(u => Bool.xor(neg, List.contains(~Char, ~Char.is_eq, cs, c)), is_inner(c))

# the regular expression of g
# bend-lint: expect-begin bend-lint-rules/performance/missed_fork@hint -- a glob tree is a few nodes, where a fork costs more than it saves
def Glob.re(g: Glob) -> Regex.Re<Atom>:
  match g:
    case Void{}:
      Regex.Void{}
    case Eps{}:
      Regex.Eps{}
    case Lit{c}:
      Regex.One{ALit{c}}
    case Any{}:
      Regex.One{AAny{}}
    case Star{}:
      Regex.Star{Regex.One{AAny{}}}
    case Class{neg, cs}:
      Regex.One{AClass{neg, cs}}
    case Deep{}:
      Regex.All{}
    case Cat{a, b}:
      Regex.Cat{Glob.re(a), Glob.re(b)}
    case Alt{a, b}:
      Regex.Alt{Glob.re(a), Glob.re(b)}
# bend-lint: expect-end bend-lint-rules/performance/missed_fork@hint

# g matches all of s
def Glob.matches(s: String, g: Glob) -> Bool:
  Regex.Re.matches(~Char, ~Atom, ~Atom.hit, String.to_list(s), Glob.re(g))

# One line of a selector: `g` includes, `!g` excludes.
type Rule is Data:
  Include{g: Glob}
  Exclude{g: Glob}

# the answer for p after rules, given the answer acc before them
def Rule.selects.go(rules: List<&2, Rule>, +p: String, acc: Bool) -> Bool:
  match rules acc:
    case Nil{} _:
      acc
    case Con{Include{g}, t} False{}:
      Rule.selects.go(t, p, Glob.matches(p, g))
    case Con{Include{g}, t} True{}:
      Rule.selects.go(t, p, True{})
    case Con{Exclude{g}, t} False{}:
      Rule.selects.go(t, p, False{})
    case Con{Exclude{g}, t} True{}:
      Rule.selects.go(t, p, Bool.not(Glob.matches(p, g)))

# the last rule that matches p decides; with no match, p is not selected
def Rule.selects(rules: List<&2, Rule>, p: String) -> Bool:
  Rule.selects.go(rules, p, False{})

# A question about two rule lists: is there a valid path that
# Both: a and b select? Only: a selects and b does not?
# "No path for Only{a, b}" means: b covers a.
type Query is Data:
  Both{a: List<&2, Rule>, b: List<&2, Rule>}
  Only{a: List<&2, Rule>, b: List<&2, Rule>}

# p is a valid path that answers q
def Query.holds(q: Query, +p: String) -> Bool:
  # bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- only laws use it; no program runs it
  match q:
    case Both{a, b}:
      Bool.and(is_path(p), Bool.and(Rule.selects(a, p), Rule.selects(b, p)))
    case Only{a, b}:
      in_a = Rule.selects(a, p)
      Bool.and(is_path(p), Bool.and(in_a, Bool.not(Rule.selects(b, p))))
  # bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# The answer of a search. Found: a path that answers the query. Absent: no
# path answers it. Unknown: the search ran out of steps; it claims nothing.
type Search is Data:
  Found{path: String}
  Absent{}
  Unknown{}

# the answer to q
law Query.search:
  for q: Query
  Search

# a Found path answers q
law search_found:
  for q: Query
  for p: String
  for h: {Query.search(q) == Found{p}: Search}
  {Query.holds(q, p) == True{}: Bool}

# after an Absent answer, no path answers q
law search_absent:
  for q: Query
  for p: String
  for h: {Query.search(q) == Absent{}: Search}
  {Query.holds(q, p) == False{}: Bool}

# Glob text. `\c` is the character c. `?`, `*`, `[...]`, `[!...]` and
# `{a,b,...}` are Any, Star, Class and Alt. In a class, `x-y` is every
# character from x to y. `**` is a whole segment: alone it is Deep, and `**/`
# also matches "". A ',' outside braces is itself. Text that starts with '/'
# is an error. A rule line that starts with `!` is an Exclude.

# the role of a character in glob text
type Sym is Data:
  SEsc{}
  SAny{}
  SStar{}
  SSlash{}
  SOpen{}
  SComma{}
  SClose{}
  SLeft{}
  SRight{}
  SBang{}
  SDash{}
  SChar{c: Char}

# the character of s
def Sym.char(s: Sym) -> Char:
  match s:
    case SEsc{}:
      Chr{92}
    case SAny{}:
      Chr{63}
    case SStar{}:
      Chr{42}
    case SSlash{}:
      Chr{47}
    case SOpen{}:
      Chr{123}
    case SComma{}:
      Chr{44}
    case SClose{}:
      Chr{125}
    case SLeft{}:
      Chr{91}
    case SRight{}:
      Chr{93}
    case SBang{}:
      Chr{33}
    case SDash{}:
      Chr{45}
    case SChar{c}:
      c

# every role but SChar
def Sym.specials() -> List<&2, Sym>:
  [
    SEsc{},
    SAny{},
    SStar{},
    SSlash{},
    SOpen{},
    SComma{},
    SClose{},
    SLeft{},
    SRight{},
    SBang{},
    SDash{}
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
      SChar{c}
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
  Out{}
  After{}
  In{neg: Bool, cs: List<&2, Char>}

# the atoms, last first, before acc
def Glob.of_seq(atoms: List<&2, Glob>, acc: Glob) -> Glob:
  match atoms:
    case Nil{}:
      acc
    case Con{h, t}:
      Glob.of_seq(t, Cat{h, acc})

# the alternatives, last first, before acc
def Glob.of_alts(alts: List<&2, Glob>, acc: Glob) -> Glob:
  match alts:
    case Nil{}:
      acc
    case Con{h, t}:
      Glob.of_alts(t, Alt{h, acc})

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
      Some{Glob.of_seq(seq, Eps{})}
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
  Alt{Eps{}, Cat{Deep{}, Lit{Chr{47}}}}

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
    case After{}:
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
    case Nil{} Out{}:
      Glob.read.end(stack)
    case Nil{} In{neg, cs}:
      None{}
    case Con{SEsc{}, Nil{}} _:
      None{}
    case Con{SEsc{}, Con{x, t}} Out{}:
      Glob.read.go(t, Out{}, Frame.add(stack, Lit{Sym.char(x)}), False{})
    case Con{SEsc{}, Con{x, t}} In{neg, cs}:
      Glob.read.go(t, In{neg, Con{Sym.char(x), cs}}, stack, seg)
    case Con{SRight{}, t} Out{}:
      None{}
    case Con{SRight{}, t} In{neg, cs}:
      Glob.read.go(t, Out{}, Frame.add(stack, Class{neg, cs}), False{})
    case Con{x, Con{SDash{}, Con{SRight{}, t}}} In{neg, cs}:
      None{}
    case Con{x, Con{SDash{}, Con{SEsc{}, t}}} In{neg, cs}:
      None{}
    case Con{x, Con{SDash{}, Con{y, t}}} In{neg, cs}:
      r = Char.range(Sym.char(x), Sym.char(y))
      Glob.read.range(r, rs => Glob.read.go(t, In{neg, List.append(&2, Char, rs, cs)}, stack, seg))
    case Con{x, t} In{neg, cs}:
      Glob.read.go(t, In{neg, Con{Sym.char(x), cs}}, stack, seg)
    case Con{SAny{}, t} _:
      Glob.read.go(t, Out{}, Frame.add(stack, Any{}), False{})
    case Nil{} After{}:
      Glob.read.end(stack)
    case Con{SComma{}, t} m:
      match stack:
        case Con{Frame{alts, seq, +start}, Con{f, r}}:
          branch = Glob.of_seq(seq, Eps{})
          up = {Con{Frame{Con{branch, alts}, [], start}, Con{f, r}}: List<&2, Frame>}
          Glob.read.go(t, Out{}, up, start)
        case _:
          Glob.read.mid(m, u => Glob.read.go(t, Out{}, Frame.add(stack, Lit{Chr{44}}), False{}))
    case Con{SClose{}, t} _:
      match stack:
        case Con{Frame{alts, seq, start}, Con{f, r}}:
          branch = Glob.of_seq(seq, Eps{})
          g = Glob.of_alts(Con{branch, alts}, Void{})
          Glob.read.go(t, Out{}, Frame.add(Con{f, r}, g), False{})
        case _:
          None{}
    case Con{x, t} After{}:
      None{}
    case Con{SStar{}, Con{SStar{}, Con{SSlash{}, t}}} _:
      dirs = Glob.dirs()
      Glob.read.at_seg(seg, u => Glob.read.go(t, Out{}, Frame.add(stack, dirs), True{}))
    case Con{SStar{}, Con{SStar{}, t}} _:
      Glob.read.at_seg(seg, u => Glob.read.go(t, After{}, Frame.add(stack, Deep{}), False{}))
    case Con{SStar{}, t} _:
      Glob.read.go(t, Out{}, Frame.add(stack, Star{}), False{})
    case Con{SSlash{}, t} _:
      Glob.read.go(t, Out{}, Frame.add(stack, Lit{Chr{47}}), True{})
    case Con{SOpen{}, t} _:
      Glob.read.go(t, Out{}, Con{Frame{[], [], seg}, stack}, seg)
    case Con{SLeft{}, Con{SBang{}, t}} _:
      Glob.read.go(t, In{True{}, []}, stack, seg)
    case Con{SLeft{}, t} _:
      Glob.read.go(t, In{False{}, []}, stack, seg)
    case Con{x, t} _:
      Glob.read.go(t, Out{}, Frame.add(stack, Lit{Sym.char(x)}), False{})

# the glob that syms spell; text that starts with '/' is an error
def Glob.read.syms(+syms: List<&2, Sym>) -> Maybe<&2, Glob>:
  match syms:
    case Con{SSlash{}, t}:
      None{}
    case _:
      Glob.read.go(syms, Out{}, [Frame{[], [], True{}}], True{})

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
    case Con{SBang{}, t}:
      Maybe.map(&2, Glob, Rule, g => Exclude{g}, Glob.read.syms(t))
    case _:
      Maybe.map(&2, Glob, Rule, g => Include{g}, Glob.read.syms(syms))

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
