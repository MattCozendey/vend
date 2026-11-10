import Base
import ../shared/shared/regex.bend as Regex
import ../shared/shared/search.bend as Searches
import ../shared/shared/shared/keyset.bend as KeySets
import ../shared/shared/shared/reach.bend as Reaches
import ../shared/shared/shared/shared/shared.bend as Shared
import ../shared/shared/shared/shared/trie.bend as Tries
import ../shared/shared/shared/spans.bend as Spans
import ../shared/shared/shared/text.bend as Texts
import ./spec.bend as Spec

# Atom equality and keys
# ----------------------

# a and b are the same atom
def Atom.is_eq(a: Spec.Atom, b: Spec.Atom) -> Bool:
  match a b:
    case Spec.ALit{x} Spec.ALit{y}:
      Char.is_eq(x, y)
    case Spec.AAny{} Spec.AAny{}:
      True{}
    case Spec.AClass{n, xs} Spec.AClass{m, ys}:
      List.all.if(
        u => Shared.List.is_eq(~Spans.Span, ~Spans.Span.is_eq, xs, ys),
        Shared.Bool.is_eq(n, m)
      )
    case _ _:
      False{}

# Atom.is_eq is True for an atom and itself
def Atom.is_eq_refl(a: Spec.Atom) -> {Atom.is_eq(a, a) == True{}: Bool}:
  match a:
    case Spec.ALit{x}:
      Shared.Char.is_eq_refl(x)
    case Spec.AAny{}:
      {==}
    case Spec.AClass{+n, +xs}:
      Shared.List.all.if_both(
        Shared.Bool.is_eq(n, n),
        u => Shared.List.is_eq(~Spans.Span, ~Spans.Span.is_eq, xs, xs)
      )(
        Shared.Bool.is_eq_refl(n)
      )(Shared.List.is_eq_refl(~Spans.Span, ~Spans.Span.is_eq, ~Spans.Span.laws(), xs))

# Atom.is_eq is True only for the same atom
def Atom.is_eq_sound(
  a: Spec.Atom,
  b: Spec.Atom
) -> {Atom.is_eq(a, b) == True{}: Bool} -> {a == b: Spec.Atom}:
  match a b:
    case Spec.ALit{x} Spec.ALit{y}:
      h => Equal.cong(Char, Spec.Atom, u => Spec.ALit{u}, x, y, Shared.Char.is_eq_sound(x, y)(h))
    case Spec.ALit{x} Spec.AAny{}:
      h => Empty.absurd({Spec.ALit{x} == Spec.AAny{}: Spec.Atom}, Shared.Bool.false_ne_true(h))
    case Spec.ALit{x} Spec.AClass{m, ys}:
      h => Empty.absurd(
        {Spec.ALit{x} == Spec.AClass{m, ys}: Spec.Atom},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.AAny{} Spec.ALit{y}:
      h => Empty.absurd({Spec.AAny{} == Spec.ALit{y}: Spec.Atom}, Shared.Bool.false_ne_true(h))
    case Spec.AAny{} Spec.AAny{}:
      h => {==}
    case Spec.AAny{} Spec.AClass{m, ys}:
      h => Empty.absurd(
        {Spec.AAny{} == Spec.AClass{m, ys}: Spec.Atom},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.AClass{n, xs} Spec.ALit{y}:
      h => Empty.absurd(
        {Spec.AClass{n, xs} == Spec.ALit{y}: Spec.Atom},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.AClass{n, xs} Spec.AAny{}:
      h => Empty.absurd(
        {Spec.AClass{n, xs} == Spec.AAny{}: Spec.Atom},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.AClass{+n, +xs} Spec.AClass{+m, +ys}:
      +h =>
        +same_n = Shared.Bool.is_eq(n, m)
        %Shared.Bool.is_eq_sound(
          n,
          m
        )(
          Shared.List.all.if_hit(
            same_n,
            u => Shared.List.is_eq(~Spans.Span, ~Spans.Span.is_eq, xs, ys)
          )(h)
        ): {Spec.AClass{n, xs} == Spec.AClass{_, ys}: Spec.Atom}
        %Shared.List.is_eq_sound(
          ~Spans.Span,
          ~Spans.Span.is_eq,
          ~Spans.Span.laws(),
          xs,
          ys
        )(
          Shared.List.all.if_rest(
            same_n,
            u => Shared.List.is_eq(~Spans.Span, ~Spans.Span.is_eq, xs, ys)
          )(h)
        ): {Spec.AClass{n, xs} == Spec.AClass{n, _}: Spec.Atom}
        {==}

# the laws of Atom.is_eq
def Atom.laws() -> Shared.Eq.Laws(Spec.Atom, Atom.is_eq):
  (Atom.is_eq_refl, Atom.is_eq_sound)

# the key of s: the keys of its ends
def Span.key(s: Spans.Span) -> List<&2, Bool>:
  match s:
    case Spans.Span{Chr{lo}, Chr{hi}}:
      List.append(&2, Bool, Tries.Trie.char(lo), Tries.Trie.char(hi))

# the key of the spans ss of a class: a True and the key of each span, then a
# False
def Class.key(ss: List<&2, Spans.Span>) -> List<&2, Bool>:
  match ss:
    case Nil{}:
      [False{}]
    case Con{s, r}:
      True{} <> List.append(&2, Bool, Span.key(s), Class.key(r))

# the key of t: a bit or two for its form, then its parts
def Atom.key(t: Spec.Atom) -> List<&2, Bool>:
  match t:
    case Spec.ALit{Chr{x}}:
      False{} <> Tries.Trie.char(x)
    case Spec.AAny{}:
      [True{}, False{}]
    case Spec.AClass{neg, ss}:
      True{} <> True{} <> neg <> Class.key(ss)

# Search states
# -------------
# A rule as the derivative lists (Seqs) of its glob, and a state of the
# search as the rules of both lists of a query. A state reads a path one
# character at a time.

# A rule whose glob is a list of Seqs.
type Slot is Data:
  Inc{xs: List<&2, List<&2, Regex.Re<Spec.Atom>>>}
  Exc{xs: List<&2, List<&2, Regex.Re<Spec.Atom>>>}

# the answer for the characters w after slots, given the answer acc before
# them
def Slot.selects.go(slots: List<&2, Slot>, +w: List<&2, Char>, acc: Bool) -> Bool:
  match slots acc:
    case Nil{} _:
      acc
    case Con{Inc{xs}, t} False{}:
      Slot.selects.go(t, w, Regex.Seqs.matches(~Char, ~Spec.Atom, ~Spec.Atom.hit, xs, w))
    case Con{Inc{xs}, t} True{}:
      Slot.selects.go(t, w, True{})
    case Con{Exc{xs}, t} False{}:
      Slot.selects.go(t, w, False{})
    case Con{Exc{xs}, t} True{}:
      Slot.selects.go(t, w, Bool.not(Regex.Seqs.matches(~Char, ~Spec.Atom, ~Spec.Atom.hit, xs, w)))

# the slots of rules
def Slot.of_rules(rules: List<&2, Spec.Rule>) -> List<&2, Slot>:
  match rules:
    case Nil{}:
      Nil{}
    case Con{Spec.Include{g}, t}:
      Con{Inc{[[Spec.Glob.re(g)]]}, Slot.of_rules(t)}
    case Con{Spec.Exclude{g}, t}:
      Con{Exc{[[Spec.Glob.re(g)]]}, Slot.of_rules(t)}

# the slots after c
def Slot.step(slots: List<&2, Slot>, +c: Char) -> List<&2, Slot>:
  match slots:
    case Nil{}:
      Nil{}
    case Con{Inc{xs}, t}:
      Con{
        Inc{Regex.Seqs.step(~Char, ~Spec.Atom, ~Spec.Atom.hit, ~Atom.is_eq, ~Atom.key, xs, c)},
        Slot.step(t, c)
      }
    case Con{Exc{xs}, t}:
      Con{
        Exc{Regex.Seqs.step(~Char, ~Spec.Atom, ~Spec.Atom.hit, ~Atom.is_eq, ~Atom.key, xs, c)},
        Slot.step(t, c)
      }

# the one-Seq list of g matches what g matches
# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- a false positive, as the rule notes: the other use is an erased argument (of Equal.sym or a motive)
def Glob.single_ok(
  p: String,
  g: Spec.Glob
) -> {
  Spec.Glob.matches(
    p,
    g
  )
    == Regex.Seqs.matches(
      ~Char,
      ~Spec.Atom,
      ~Spec.Atom.hit,
      [[Spec.Glob.re(g)]],
      String.to_list(p)
    ): Bool
}:
  Equal.sym(
    Bool,
    Regex.Seqs.matches(~Char, ~Spec.Atom, ~Spec.Atom.hit, [[Spec.Glob.re(g)]], String.to_list(p)),
    Spec.Glob.matches(p, g),
    Regex.Seqs.matches_one(~Char, ~Spec.Atom, ~Spec.Atom.hit, String.to_list(p), Spec.Glob.re(g))
  )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# rules and their slots select the same paths
def Slot.of_rules_ok(
  rules: List<&2, Spec.Rule>,
  +p: String,
  acc: Bool
) -> {
  Spec.Rule.selects.go(
    rules,
    p,
    acc
  )
    == Slot.selects.go(Slot.of_rules(rules), String.to_list(p), acc): Bool
}:
  match rules acc:
    case Nil{} _:
      {==}
    case Con{Spec.Include{+g}, t} False{}:
      %Glob.single_ok(
        p,
        g
      ): {
        Spec.Rule.selects.go(
          t,
          p,
          Spec.Glob.matches(p, g)
        )
          == Slot.selects.go(Slot.of_rules(t), String.to_list(p), _): Bool
      }
      Slot.of_rules_ok(t, p, Spec.Glob.matches(p, g))
    case Con{Spec.Include{g}, t} True{}:
      Slot.of_rules_ok(t, p, True{})
    case Con{Spec.Exclude{g}, t} False{}:
      Slot.of_rules_ok(t, p, False{})
    case Con{Spec.Exclude{+g}, +t} True{}:
      %Glob.single_ok(
        p,
        g
      ): {
        Spec.Rule.selects.go(
          t,
          p,
          Bool.not(Spec.Glob.matches(p, g))
        )
          == Slot.selects.go(Slot.of_rules(t), String.to_list(p), Bool.not(_)): Bool
      }
      Slot.of_rules_ok(t, p, Bool.not(Spec.Glob.matches(p, g)))

# slots select c then t when their step after c selects t
def Slot.step_ok(
  slots: List<&2, Slot>,
  +c: Char,
  +t: List<&2, Char>,
  acc: Bool
) -> {Slot.selects.go(Slot.step(slots, c), t, acc) == Slot.selects.go(slots, c <> t, acc): Bool}:
  match slots acc:
    case Nil{} _:
      {==}
    case Con{Inc{+xs}, r} False{}:
      m = Regex.Seqs.matches(
        ~Char,
        ~Spec.Atom,
        ~Spec.Atom.hit,
        Regex.Seqs.step(~Char, ~Spec.Atom, ~Spec.Atom.hit, ~Atom.is_eq, ~Atom.key, xs, c),
        t
      )
      %Regex.Seqs.matches_step(
        ~Char,
        ~Spec.Atom,
        ~Spec.Atom.hit,
        ~Atom.is_eq,
        ~Atom.key,
        ~Atom.laws(),
        xs,
        c,
        t
      ): {Slot.selects.go(Slot.step(r, c), t, m) == Slot.selects.go(r, c <> t, _): Bool}
      Slot.step_ok(r, c, t, m)
    case Con{Inc{xs}, r} True{}:
      Slot.step_ok(r, c, t, True{})
    case Con{Exc{xs}, r} False{}:
      Slot.step_ok(r, c, t, False{})
    case Con{Exc{+xs}, +r} True{}:
      m = Regex.Seqs.matches(
        ~Char,
        ~Spec.Atom,
        ~Spec.Atom.hit,
        Regex.Seqs.step(~Char, ~Spec.Atom, ~Spec.Atom.hit, ~Atom.is_eq, ~Atom.key, xs, c),
        t
      )
      %Regex.Seqs.matches_step(
        ~Char,
        ~Spec.Atom,
        ~Spec.Atom.hit,
        ~Atom.is_eq,
        ~Atom.key,
        ~Atom.laws(),
        xs,
        c,
        t
      ): {
        Slot.selects.go(
          Slot.step(r, c),
          t,
          Bool.not(m)
        )
          == Slot.selects.go(r, c <> t, Bool.not(_)): Bool
      }
      Slot.step_ok(r, c, t, Bool.not(m))

# A search state: the slots of both rule lists. both: the query asks for a
# path that b selects too; else, one that b does not select.
type St is Data:
  St{both: Bool, a: List<&2, Slot>, b: List<&2, Slot>}

# v when both, else not v
def St.side(both: Bool, v: Bool) -> Bool:
  match both:
    case False{}:
      Bool.not(v)
    case True{}:
      v

# the characters w answer the query of state x
def St.holds(x: St, +w: List<&2, Char>) -> Bool:
  match x:
    case St{both, a, b}:
      List.all.if(
        u => St.side(both, Slot.selects.go(b, w, False{})),
        Slot.selects.go(a, w, False{})
      )

# the state that a query starts in
def St.of(q: Spec.Query) -> St:
  match q:
    case Spec.Both{a, b}:
      St{True{}, Slot.of_rules(a), Slot.of_rules(b)}
    case Spec.Only{a, b}:
      St{False{}, Slot.of_rules(a), Slot.of_rules(b)}

# the state after c
def St.step(x: St, +c: Char) -> St:
  match x:
    case St{both, a, b}:
      St{both, Slot.step(a, c), Slot.step(b, c)}

# the state after c holds for t when the state holds for c then t
def St.step_ok(
  x: St,
  +c: Char,
  +t: List<&2, Char>
) -> {St.holds(St.step(x, c), t) == St.holds(x, c <> t): Bool}:
  match x:
    case St{both, +a, +b}:
      sa = Slot.selects.go(Slot.step(a, c), t, False{})
      sb = Slot.selects.go(Slot.step(b, c), t, False{})
      %Slot.step_ok(
        a,
        c,
        t,
        False{}
      ): {
        List.all.if(
          u => St.side(both, sb),
          sa
        )
          == List.all.if(u => St.side(both, Slot.selects.go(b, c <> t, False{})), _): Bool
      }
      %Slot.step_ok(
        b,
        c,
        t,
        False{}
      ): {List.all.if(u => St.side(both, sb), sa) == List.all.if(u => St.side(both, _), sa): Bool}
      {==}

# a query holds for p when p is a valid path and its start state holds
# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- a false positive, as the rule notes: the other use is an erased argument (of Equal.sym or a motive)
def St.of_ok(
  q: Spec.Query,
  +p: String
) -> {
  Bool.and(Spec.is_path(p), St.holds(St.of(q), String.to_list(p))) == Spec.Query.holds(q, p): Bool
}:
  match q:
    case Spec.Both{+a, +b}:
      v = Spec.is_path(p)
      +w = String.to_list(p)
      sa = Slot.selects.go(Slot.of_rules(a), w, False{})
      sb = Slot.selects.go(Slot.of_rules(b), w, False{})
      r = Spec.Query.holds(Spec.Both{a, b}, p)
      %Equal.sym(
        Bool,
        List.all.if(u => sb, sa),
        Bool.and(sa, sb),
        Shared.List.all.if_and(sa, u => sb)
      ): {Bool.and(v, _) == r: Bool}
      %Slot.of_rules_ok(a, p, False{}): {Bool.and(v, Bool.and(_, sb)) == r: Bool}
      %Slot.of_rules_ok(
        b,
        p,
        False{}
      ): {Bool.and(v, Bool.and(Spec.Rule.selects.go(a, p, False{}), _)) == r: Bool}
      {==}
    case Spec.Only{+a, +b}:
      v = Spec.is_path(p)
      +w = String.to_list(p)
      sa = Slot.selects.go(Slot.of_rules(a), w, False{})
      sb = Slot.selects.go(Slot.of_rules(b), w, False{})
      r = Spec.Query.holds(Spec.Only{a, b}, p)
      %Equal.sym(
        Bool,
        List.all.if(u => Bool.not(sb), sa),
        Bool.and(sa, Bool.not(sb)),
        Shared.List.all.if_and(sa, u => Bool.not(sb))
      ): {Bool.and(v, _) == r: Bool}
      %Slot.of_rules_ok(a, p, False{}): {Bool.and(v, Bool.and(_, Bool.not(sb))) == r: Bool}
      %Slot.of_rules_ok(
        b,
        p,
        False{}
      ): {Bool.and(v, Bool.and(Spec.Rule.selects.go(a, p, False{}), Bool.not(_))) == r: Bool}
      {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# Valid paths
# -----------
# An automaton that reads a path one character at a time. It accepts exactly
# the valid paths (Path.walk_ok).

# What a character is to a path: '/', '.', a banned character, or another.
type Role is Data:
  KSlash{}
  KDot{}
  KBad{}
  KOther{}

# what c is to a path
def Role.of(+c: Char) -> Role:
  Bool.pick(
    Role,
    Char.is_eq(c, '/'),
    KSlash{},
    Bool.pick(
      Role,
      Char.is_eq(c, '.'),
      KDot{},
      Bool.pick(Role, Spec.is_banned(c), KBad{}, KOther{})
    )
  )

# Where a path is: at a segment start, after "." or "..", inside a valid
# segment, or past a mistake.
type Path is Data:
  PStart{}
  PDot{}
  PDots{}
  PSeg{}
  PDead{}

# where a path is after a character of role k
def Path.step(s: Path, k: Role) -> Path:
  match s k:
    case PSeg{} KSlash{}:
      PStart{}
    case _ KSlash{}:
      PDead{}
    case _ KBad{}:
      PDead{}
    case PDead{} _:
      PDead{}
    case PStart{} KDot{}:
      PDot{}
    case PDot{} KDot{}:
      PDots{}
    case _ _:
      PSeg{}

# a valid path can end here
def Path.is_end(s: Path) -> Bool:
  match s:
    case PSeg{}:
      True{}
    case _:
      False{}

# where a path is after the characters w, from s
def Path.walk(w: List<&2, Char>, s: Path) -> Path:
  match w:
    case Nil{}:
      s
    case Con{c, t}:
      Path.walk(t, Path.step(s, Role.of(c)))

# a path that is past a mistake stays there after a character
def Path.step_dead(k: Role) -> {PDead{} == Path.step(PDead{}, k): Path}:
  match k:
    case KSlash{}:
      {==}
    case KDot{}:
      {==}
    case KBad{}:
      {==}
    case KOther{}:
      {==}

# no valid path can end after a mistake
def Path.dead_never(w: List<&2, Char>) -> {False{} == Path.is_end(Path.walk(w, PDead{})): Bool}:
  match w:
    case Nil{}:
      {==}
    case Con{c, t}:
      %Path.step_dead(Role.of(c)): {False{} == Path.is_end(Path.walk(t, _)): Bool}
      Path.dead_never(t)

# the text h ends a valid segment that was read up to s
def Path.seg_ok(s: Path, h: String) -> Bool:
  match s:
    case PStart{}:
      Spec.is_segment(h)
    case PDot{}:
      Spec.is_segment(SCon{'.', h})
    case PDots{}:
      Spec.is_segment(SCon{'.', SCon{'.', h}})
    case PSeg{}:
      Bool.not(List.any(~&2, ~Char, ~Spec.is_banned, String.to_list(h)))
    case PDead{}:
      False{}

# the parts segs are valid segments, when a segment was read up to s before
# the first of them
def Path.fits(s: Path, segs: List<&2, String>) -> Bool:
  match segs:
    case Nil{}:
      True{}
    case Con{h, r}:
      List.all.if(u => List.all(~&2, ~String, ~Spec.is_segment, r), Path.seg_ok(s, h))

# a text that holds a banned character is no segment
def Segment.banned_never(
  +s: String,
  e: {List.any(~&2, ~Char, ~Spec.is_banned, String.to_list(s)) == True{}: Bool}
) -> {Spec.is_segment(s) == False{}: Bool}:
  -dots = Bool.or(String.eq(s, "."), String.eq(s, ".."))
  %Equal.sym(
    Bool,
    List.any(~&2, ~Char, ~Spec.is_banned, String.to_list(s)),
    True{},
    e
  ): {
    Bool.and(Bool.not(String.is_empty(s)), Bool.and(Bool.not(dots), Bool.not(_))) == False{}: Bool
  }
  %Equal.sym(
    Bool,
    Bool.and(Bool.not(dots), False{}),
    False{},
    Shared.Bool.and_false_right(Bool.not(Bool.or(String.eq(s, "."), String.eq(s, ".."))))
  ): {Bool.and(Bool.not(String.is_empty(s)), _) == False{}: Bool}
  Shared.Bool.and_false_right(Bool.not(String.is_empty(s)))

# a '.' moves the automaton as it extends the segment
def Path.seg_ok_dot(
  s: Path,
  h: String
) -> {Path.seg_ok(s, SCon{'.', h}) == Path.seg_ok(Path.step(s, KDot{}), h): Bool}:
  match s:
    case PStart{}:
      {==}
    case PDot{}:
      {==}
    case PDots{}:
      {==}
    case PSeg{}:
      {==}
    case PDead{}:
      {==}

# a banned character moves the automaton as it extends the segment
def Path.seg_ok_bad(
  s: Path,
  c: Char,
  h: String,
  e: {List.any(~&2, ~Char, ~Spec.is_banned, c <> String.to_list(h)) == True{}: Bool}
) -> {Path.seg_ok(s, SCon{c, h}) == Path.seg_ok(Path.step(s, KBad{}), h): Bool}:
  match s:
    case PStart{}:
      Segment.banned_never(SCon{c, h}, e)
    case PDot{}:
      Segment.banned_never(SCon{'.', SCon{c, h}}, e)
    case PDots{}:
      Segment.banned_never(SCon{'.', SCon{'.', SCon{c, h}}}, e)
    case PSeg{}:
      Equal.cong(
        Bool,
        Bool,
        v => Bool.not(v),
        List.any(~&2, ~Char, ~Spec.is_banned, c <> String.to_list(h)),
        True{},
        e
      )
    case PDead{}:
      {==}

# a character that is not '.' and not banned moves the automaton as it
# extends the segment
def Path.seg_ok_other(
  s: Path,
  c: Char,
  +h: String,
  +ed: {Char.is_eq(c, '.') == False{}: Bool},
  eb: {Spec.is_banned(c) == False{}: Bool}
) -> {Path.seg_ok(s, SCon{c, h}) == Path.seg_ok(Path.step(s, KOther{}), h): Bool}:
  match s c:
    case PStart{} Chr{+x}:
      -rest = Bool.not(
        List.any.if(
          u => List.any(~&2, ~Char, ~Spec.is_banned, String.to_list(h)),
          Spec.is_banned(Chr{x})
        )
      )
      %eb: {
        Spec.is_segment(
          SCon{Chr{x}, h}
        )
          == Bool.not(
            List.any.if(u => List.any(~&2, ~Char, ~Spec.is_banned, String.to_list(h)), _)
          ): Bool
      }
      %Texts.String.eq_head_ne(
        Chr{x},
        '.',
        h,
        "",
        ed
      ): {Bool.and(Bool.not(Bool.or(_, String.eq(SCon{Chr{x}, h}, ".."))), rest) == rest: Bool}
      %Texts.String.eq_head_ne(Chr{x}, '.', h, ".", ed): {Bool.and(Bool.not(_), rest) == rest: Bool}
      {==}
    case PDot{} Chr{x}:
      -rest = Bool.not(
        List.any.if(
          u => List.any(~&2, ~Char, ~Spec.is_banned, String.to_list(h)),
          Spec.is_banned(Chr{x})
        )
      )
      %eb: {
        Spec.is_segment(
          SCon{'.', SCon{Chr{x}, h}}
        )
          == Bool.not(
            List.any.if(u => List.any(~&2, ~Char, ~Spec.is_banned, String.to_list(h)), _)
          ): Bool
      }
      %Texts.String.eq_head_ne(Chr{x}, '.', h, "", ed): {Bool.and(Bool.not(_), rest) == rest: Bool}
      {==}
    case PDots{} Chr{x}:
      %eb: {
        Spec.is_segment(
          SCon{'.', SCon{'.', SCon{Chr{x}, h}}}
        )
          == Bool.not(
            List.any.if(u => List.any(~&2, ~Char, ~Spec.is_banned, String.to_list(h)), _)
          ): Bool
      }
      {==}
    case PSeg{} Chr{x}:
      %eb: {
        Bool.not(
          List.any.if(
            u => List.any(~&2, ~Char, ~Spec.is_banned, String.to_list(h)),
            Spec.is_banned(Chr{x})
          )
        )
          == Bool.not(
            List.any.if(u => List.any(~&2, ~Char, ~Spec.is_banned, String.to_list(h)), _)
          ): Bool
      }
      {==}
    case PDead{} Chr{x}:
      {==}

# Path.seg_ok_step, once it is known if c is '.' (dot) and if it is banned
# (bad)
# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- a false positive, as the rule notes: the other use is an erased argument (of Equal.sym or a motive)
def Path.seg_ok_step.at(
  s: Path,
  c: Char,
  h: String,
  dot: Bool,
  bad: Bool
) -> {
  Char.is_eq(c, '.') == dot: Bool
} -> {
  Spec.is_banned(c) == bad: Bool
} -> {
  Path.seg_ok(
    s,
    SCon{c, h}
  )
    == Path.seg_ok(
      Path.step(s, Bool.pick(Role, dot, KDot{}, Bool.pick(Role, bad, KBad{}, KOther{}))),
      h
    ): Bool
}:
  match dot bad:
    case True{} _:
      ed => eb =>
        %Equal.sym(
          Char,
          c,
          '.',
          Shared.Char.is_eq_sound(c, '.')(ed)
        ): {Path.seg_ok(s, SCon{_, h}) == Path.seg_ok(Path.step(s, KDot{}), h): Bool}
        Path.seg_ok_dot(s, h)
    case False{} True{}:
      ed => eb => Path.seg_ok_bad(
        s,
        c,
        h,
        Equal.cong(
          Bool,
          Bool,
          v => List.any.if(u => List.any(~&2, ~Char, ~Spec.is_banned, String.to_list(h)), v),
          Spec.is_banned(c),
          True{},
          eb
        )
      )
    case False{} False{}:
      ed => eb => Path.seg_ok_other(s, c, h, ed, eb)
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# a '/' moves the automaton as it starts a new part
def Path.fits_slash(
  s: Path,
  h: String,
  r: List<&2, String>
) -> {Path.fits(Path.step(s, KSlash{}), h <> r) == Path.fits(s, SNil{} <> h <> r): Bool}:
  match s:
    case PStart{}:
      {==}
    case PDot{}:
      {==}
    case PDots{}:
      {==}
    case PSeg{}:
      {==}
    case PDead{}:
      {==}

# Path.fits_step at the parts h <> r, once it is known if c is '/' (cut)
def Path.fits_step.at(
  s: Path,
  +c: Char,
  h: String,
  r: List<&2, String>,
  cut: Bool
) -> {
  Path.fits(
    Path.step(
      s,
      Bool.pick(
        Role,
        cut,
        KSlash{},
        Bool.pick(
          Role,
          Char.is_eq(c, '.'),
          KDot{},
          Bool.pick(Role, Spec.is_banned(c), KBad{}, KOther{})
        )
      )
    ),
    h <> r
  )
    == Path.fits(s, String.split.fin(c, h <> r, cut)): Bool
}:
  match cut:
    case True{}:
      Path.fits_slash(s, h, r)
    case False{}:
      %Path.seg_ok_step.at(
        s,
        c,
        h,
        Char.is_eq(c, '.'),
        Spec.is_banned(c)
      )(
        {==},
        {==}
      ): {
        List.all.if(
          u => List.all(~&2, ~String, ~Spec.is_segment, r),
          _
        )
          == List.all.if(
            u => List.all(~&2, ~String, ~Spec.is_segment, r),
            Path.seg_ok(s, SCon{c, h})
          ): Bool
      }
      {==}

# a character moves the automaton as it changes the parts of a split
def Path.fits_step(
  s: Path,
  +c: Char,
  segs: List<&2, String>,
  some: {List.is_empty(&2, String, segs) == False{}: Bool}
) -> {
  Path.fits(
    Path.step(s, Role.of(c)),
    segs
  )
    == Path.fits(s, String.split.fin(c, segs, Char.is_eq(c, '/'))): Bool
}:
  match segs:
    case Nil{}:
      Empty.absurd(
        {
          Path.fits(
            Path.step(s, Role.of(c)),
            []
          )
            == Path.fits(s, String.split.fin(c, [], Char.is_eq(c, '/'))): Bool
        },
        Shared.Bool.true_ne_false(some)
      )
    case Con{h, r}:
      Path.fits_step.at(s, c, h, r, Char.is_eq(c, '/'))

# a valid path can end at s exactly when the one part "" fits s
def Path.fits_end(s: Path) -> {Path.is_end(s) == Path.fits(s, [SNil{}]): Bool}:
  match s:
    case PStart{}:
      {==}
    case PDot{}:
      {==}
    case PDots{}:
      {==}
    case PSeg{}:
      {==}
    case PDead{}:
      {==}

# parts fit a segment start exactly when each is a valid segment
def Path.fits_start(
  segs: List<&2, String>
) -> {Path.fits(PStart{}, segs) == List.all(~&2, ~String, ~Spec.is_segment, segs): Bool}:
  match segs:
    case Nil{}:
      {==}
    case Con{head, tail}:
      {==}

# a valid path can end after the text t, from s, exactly when the parts of t
# fit s
def Path.walk_fits(
  t: String,
  +s: Path
) -> {Path.is_end(Path.walk(String.to_list(t), s)) == Path.fits(s, String.split(t, '/')): Bool}:
  match t:
    case SNil{}:
      Path.fits_end(s)
    case SCon{+c, +r}:
      Equal.trans(
        Bool,
        Path.is_end(Path.walk(String.to_list(r), Path.step(s, Role.of(c)))),
        Path.fits(Path.step(s, Role.of(c)), String.split(r, '/')),
        Path.fits(s, String.split.fin(c, String.split(r, '/'), Char.is_eq(c, '/'))),
        Path.walk_fits(r, Path.step(s, Role.of(c))),
        Path.fits_step(s, c, String.split(r, '/'), Texts.String.split_some(r, '/'))
      )

# the automaton accepts exactly the valid paths
law Path.walk_ok:
  for p: String
  {Path.is_end(Path.walk(String.to_list(p), PStart{})) == Spec.is_path(p): Bool}

def Path.walk_ok(p):
  +p = p
  Equal.trans(
    Bool,
    Path.is_end(Path.walk(String.to_list(p), PStart{})),
    Path.fits(PStart{}, String.split(p, '/')),
    Spec.is_path(p),
    Path.walk_fits(p, PStart{}),
    Path.fits_start(String.split(p, '/'))
  )

# The machine
# -----------
# The search runs one machine: the automaton of valid paths, with a state of
# the rules. It accepts the characters of p from the place of a query exactly
# when p answers the query (Query.holds_fast_ok).

# What the machine knows: the spans that the query names, and those of the
# characters with a role of their own (see "Representative characters").
type Abc is Data:
  Abc{ss: List<&2, Spans.Span>}

# A place of the machine: where the path is, with the state; or past a
# mistake of the path (Dead), where the state does not matter.
type Walk is Data:
  Dead{}
  At{at: Path, x: St}

# the place of a path at a with the state x(); Dead past a mistake
def Walk.at(a: Path, x: Unit -> St) -> Walk:
  match a:
    case PDead{}:
      Dead{}
    case other:
      At{other, x(Unit{})}

# the place after c
def Walk.step(g: Abc, w: Walk, c: Char) -> Walk:
  match w:
    case Dead{}:
      Dead{}
    case At{a, x}:
      +c = c
      Walk.at(Path.step(a, Role.of(c)), u => St.step(x, c))

# a valid path that the state holds for can end here
def Walk.ends(g: Abc, w: Walk) -> Bool:
  match w:
    case Dead{}:
      False{}
    case At{a, x}:
      List.all.if(u => St.holds(x, []), Path.is_end(a))

# the place that a query starts in
def Walk.of(q: Spec.Query) -> Walk:
  At{PStart{}, St.of(q)}

# the machine accepts no word from Dead
def Walk.dead_never(
  w: List<&2, Char>,
  g: Abc
) -> {
  Searches.Machine.accepts(
    ~Walk,
    ~Char,
    ~Abc,
    ~Walk.step,
    ~Walk.ends,
    w,
    Dead{},
    g
  )
    == False{}: Bool
}:
  match w:
    case Nil{}:
      {==}
    case Con{c, t}:
      Walk.dead_never(t, g)

# Walk.accepts_ok for the place of a path at a with the state x, given it
# for the place At{a, x}
def Walk.accepts_ok.at(
  +t: List<&2, Char>,
  a: Path,
  x: St,
  g: Abc,
  ih: {
    Searches.Machine.accepts(
      ~Walk,
      ~Char,
      ~Abc,
      ~Walk.step,
      ~Walk.ends,
      t,
      At{a, x},
      g
    )
      == List.all.if(u => St.holds(x, t), Path.is_end(Path.walk(t, a))): Bool
  }
) -> {
  Searches.Machine.accepts(
    ~Walk,
    ~Char,
    ~Abc,
    ~Walk.step,
    ~Walk.ends,
    t,
    Walk.at(a, u => x),
    g
  )
    == List.all.if(u => St.holds(x, t), Path.is_end(Path.walk(t, a))): Bool
}:
  match a:
    case PStart{}:
      ih
    case PDot{}:
      ih
    case PDots{}:
      ih
    case PSeg{}:
      ih
    case PDead{}:
      %Path.dead_never(
        t
      ): {
        Searches.Machine.accepts(
          ~Walk,
          ~Char,
          ~Abc,
          ~Walk.step,
          ~Walk.ends,
          t,
          Dead{},
          g
        )
          == List.all.if(u => St.holds(x, t), _): Bool
      }
      Walk.dead_never(t, g)

# the machine accepts w from the place At{a, x} exactly when a valid path can
# end after w, from a, and x holds for w
def Walk.accepts_ok(
  w: List<&2, Char>,
  +a: Path,
  +x: St,
  +g: Abc
) -> {
  Searches.Machine.accepts(
    ~Walk,
    ~Char,
    ~Abc,
    ~Walk.step,
    ~Walk.ends,
    w,
    At{a, x},
    g
  )
    == List.all.if(u => St.holds(x, w), Path.is_end(Path.walk(w, a))): Bool
}:
  match w:
    case Nil{}:
      {==}
    case Con{+c, +t}:
      %St.step_ok(
        x,
        c,
        t
      ): {
        Searches.Machine.accepts(
          ~Walk,
          ~Char,
          ~Abc,
          ~Walk.step,
          ~Walk.ends,
          t,
          Walk.at(Path.step(a, Role.of(c)), u => St.step(x, c)),
          g
        )
          == List.all.if(u => _, Path.is_end(Path.walk(t, Path.step(a, Role.of(c))))): Bool
      }
      Walk.accepts_ok.at(
        t,
        Path.step(a, Role.of(c)),
        St.step(x, c),
        g,
        Walk.accepts_ok(t, Path.step(a, Role.of(c)), St.step(x, c), g)
      )

# p is a valid path that answers q: Spec.Query.holds, by the machine of the
# search, whose cost does not grow with each character
def Query.holds.fast(q: Spec.Query, p: String, g: Abc) -> Bool:
  Searches.Machine.accepts(
    ~Walk,
    ~Char,
    ~Abc,
    ~Walk.step,
    ~Walk.ends,
    String.to_list(p),
    Walk.of(q),
    g
  )

# Query.holds.fast gives the answer of Spec.Query.holds
def Query.holds_fast_ok(
  +q: Spec.Query,
  +p: String,
  g: Abc
) -> {Query.holds.fast(q, p, g) == Spec.Query.holds(q, p): Bool}:
  +w = String.to_list(p)
  +x = St.of(q)
  %St.of_ok(q, p): {Query.holds.fast(q, p, g) == _: Bool}
  %Path.walk_ok(p): {Query.holds.fast(q, p, g) == Bool.and(_, St.holds(x, w)): Bool}
  %Shared.List.all.if_and(
    Path.is_end(Path.walk(w, PStart{})),
    u => St.holds(x, w)
  ): {Query.holds.fast(q, p, g) == _: Bool}
  Walk.accepts_ok(w, PStart{}, x, g)

# State equality and keys
# -----------------------

# xs and ys are the same Seqs
def Seqs.is_eq(
  xs: List<&2, List<&2, Regex.Re<Spec.Atom>>>,
  ys: List<&2, List<&2, Regex.Re<Spec.Atom>>>
) -> Bool:
  Shared.List.is_eq(
    ~List<&2, Regex.Re<Spec.Atom>>,
    ~Regex.Seq.is_eq(~Spec.Atom, ~Atom.is_eq),
    xs,
    ys
  )

# the laws of Seqs.is_eq
def Seqs.laws() -> Shared.Eq.Laws(List<&2, List<&2, Regex.Re<Spec.Atom>>>, Seqs.is_eq):
  (
    xs => Shared.List.is_eq_refl(
      ~List<&2, Regex.Re<Spec.Atom>>,
      ~Regex.Seq.is_eq(~Spec.Atom, ~Atom.is_eq),
      ~Regex.Seq.laws(~Spec.Atom, ~Atom.is_eq, ~Atom.laws()),
      xs
    ),
    xs => ys => Shared.List.is_eq_sound(
      ~List<&2, Regex.Re<Spec.Atom>>,
      ~Regex.Seq.is_eq(~Spec.Atom, ~Atom.is_eq),
      ~Regex.Seq.laws(~Spec.Atom, ~Atom.is_eq, ~Atom.laws()),
      xs,
      ys
    )
  )

# a and b are the same slot
def Slot.is_eq(a: Slot, b: Slot) -> Bool:
  match a b:
    case Inc{x} Inc{y}:
      Seqs.is_eq(x, y)
    case Exc{x} Exc{y}:
      Seqs.is_eq(x, y)
    case _ _:
      False{}

# Slot.is_eq is True for a slot and itself
def Slot.is_eq_refl(a: Slot) -> {Slot.is_eq(a, a) == True{}: Bool}:
  match a:
    case Inc{x}:
      Shared.Eq.refl(~List<&2, List<&2, Regex.Re<Spec.Atom>>>, ~Seqs.is_eq, Seqs.laws(), x)
    case Exc{x}:
      Shared.Eq.refl(~List<&2, List<&2, Regex.Re<Spec.Atom>>>, ~Seqs.is_eq, Seqs.laws(), x)

# Slot.is_eq is True only for the same slot
def Slot.is_eq_sound(a: Slot, b: Slot) -> {Slot.is_eq(a, b) == True{}: Bool} -> {a == b: Slot}:
  match a b:
    case Inc{x} Inc{y}:
      h => Equal.cong(
        List<&2, List<&2, Regex.Re<Spec.Atom>>>,
        Slot,
        u => Inc{u},
        x,
        y,
        Shared.Eq.sound(~List<&2, List<&2, Regex.Re<Spec.Atom>>>, ~Seqs.is_eq, Seqs.laws(), x, y)(h)
      )
    case Inc{x} Exc{y}:
      h => Empty.absurd({Inc{x} == Exc{y}: Slot}, Shared.Bool.false_ne_true(h))
    case Exc{x} Inc{y}:
      h => Empty.absurd({Exc{x} == Inc{y}: Slot}, Shared.Bool.false_ne_true(h))
    case Exc{x} Exc{y}:
      h => Equal.cong(
        List<&2, List<&2, Regex.Re<Spec.Atom>>>,
        Slot,
        u => Exc{u},
        x,
        y,
        Shared.Eq.sound(~List<&2, List<&2, Regex.Re<Spec.Atom>>>, ~Seqs.is_eq, Seqs.laws(), x, y)(h)
      )

# the laws of Slot.is_eq
def Slot.laws() -> Shared.Eq.Laws(Slot, Slot.is_eq):
  (Slot.is_eq_refl, Slot.is_eq_sound)

# a and b are the same slots
def Slots.is_eq(a: List<&2, Slot>, b: List<&2, Slot>) -> Bool:
  Shared.List.is_eq(~Slot, ~Slot.is_eq, a, b)

# x and y are the same state
def St.is_eq(x: St, y: St) -> Bool:
  match x y:
    case St{n, a, b} St{m, c, d}:
      List.all.if(
        u => List.all.if(u2 => Slots.is_eq(b, d), Slots.is_eq(a, c)),
        Shared.Bool.is_eq(n, m)
      )

# St.is_eq is True for a state and itself
def St.is_eq_refl(x: St) -> {St.is_eq(x, x) == True{}: Bool}:
  match x:
    case St{+n, +a, +b}:
      Shared.List.all.if_both(
        Shared.Bool.is_eq(n, n),
        u => List.all.if(u2 => Slots.is_eq(b, b), Slots.is_eq(a, a))
      )(
        Shared.Bool.is_eq_refl(n)
      )(
        Shared.List.all.if_both(
          Slots.is_eq(a, a),
          u2 => Slots.is_eq(b, b)
        )(
          Shared.List.is_eq_refl(~Slot, ~Slot.is_eq, ~Slot.laws(), a)
        )(Shared.List.is_eq_refl(~Slot, ~Slot.is_eq, ~Slot.laws(), b))
      )

# St.is_eq is True only for the same state
def St.is_eq_sound(x: St, y: St) -> {St.is_eq(x, y) == True{}: Bool} -> {x == y: St}:
  match x y:
    case St{+n, +a, +b} St{+m, +c, +d}:
      +h =>
        +sn = Shared.Bool.is_eq(n, m)
        +sa = Slots.is_eq(a, c)
        +sb = Slots.is_eq(b, d)
        +rest = Shared.List.all.if_rest(sn, u => List.all.if(u2 => sb, sa))(h)
        %Shared.Bool.is_eq_sound(
          n,
          m
        )(
          Shared.List.all.if_hit(sn, u => List.all.if(u2 => sb, sa))(h)
        ): {St{n, a, b} == St{_, c, d}: St}
        %Shared.List.is_eq_sound(
          ~Slot,
          ~Slot.is_eq,
          ~Slot.laws(),
          a,
          c
        )(Shared.List.all.if_hit(sa, u2 => sb)(rest)): {St{n, a, b} == St{n, _, d}: St}
        %Shared.List.is_eq_sound(
          ~Slot,
          ~Slot.is_eq,
          ~Slot.laws(),
          b,
          d
        )(Shared.List.all.if_rest(sa, u2 => sb)(rest)): {St{n, a, b} == St{n, a, _}: St}
        {==}

# the key of xs, then rest: True before each Seq, False after the last
def Seqs.key(xs: List<&2, List<&2, Regex.Re<Spec.Atom>>>, rest: List<&2, Bool>) -> List<&2, Bool>:
  match xs:
    case Nil{}:
      False{} <> rest
    case Con{s, r}:
      True{} <> Regex.Seq.key.go(~Spec.Atom, ~Atom.key, s, Seqs.key(r, rest))

# the key of slots, then rest: True and the kind before each slot, False
# after the last
def Slots.key(slots: List<&2, Slot>, rest: List<&2, Bool>) -> List<&2, Bool>:
  match slots:
    case Nil{}:
      False{} <> rest
    case Con{Inc{xs}, r}:
      True{} <> False{} <> Seqs.key(xs, Slots.key(r, rest))
    case Con{Exc{xs}, r}:
      True{} <> True{} <> Seqs.key(xs, Slots.key(r, rest))

# the key of x
def St.key(x: St) -> List<&2, Bool>:
  match x:
    case St{both, a, b}:
      both <> Slots.key(a, Slots.key(b, []))

# the key of a place of a path
def Path.key(s: Path) -> List<&2, Bool>:
  match s:
    case PStart{}:
      [False{}, False{}, False{}]
    case PDot{}:
      [False{}, False{}, True{}]
    case PDots{}:
      [False{}, True{}, False{}]
    case PSeg{}:
      [False{}, True{}, True{}]
    case PDead{}:
      [True{}, False{}, False{}]

# the place of a path whose key is k
def Path.of_key(k: List<&2, Bool>) -> Path:
  match k:
    case Con{False{}, Con{False{}, Con{False{}, Nil{}}}}:
      PStart{}
    case Con{False{}, Con{False{}, Con{True{}, Nil{}}}}:
      PDot{}
    case Con{False{}, Con{True{}, Con{False{}, Nil{}}}}:
      PDots{}
    case Con{False{}, Con{True{}, Con{True{}, Nil{}}}}:
      PSeg{}
    case _:
      PDead{}

# the key of a place of a path gives the place back
def Path.key_back(s: Path) -> {Path.of_key(Path.key(s)) == s: Path}:
  match s:
    case PStart{}:
      {==}
    case PDot{}:
      {==}
    case PDots{}:
      {==}
    case PSeg{}:
      {==}
    case PDead{}:
      {==}

# a and b are the same place of a path
def Path.is_eq(a: Path, b: Path) -> Bool:
  Tries.Trie.same_key(Path.key(a), Path.key(b))

# Path.is_eq is True for a place and itself
def Path.is_eq_refl(a: Path) -> {Path.is_eq(a, a) == True{}: Bool}:
  Shared.List.is_eq_refl(~Bool, ~Shared.Bool.is_eq, ~Shared.Bool.laws(), Path.key(a))

# Path.is_eq is True only for the same place
def Path.is_eq_sound(+a: Path, +b: Path) -> {Path.is_eq(a, b) == True{}: Bool} -> {a == b: Path}:
  h => Equal.trans(
    Path,
    a,
    Path.of_key(Path.key(b)),
    b,
    Equal.trans(
      Path,
      a,
      Path.of_key(Path.key(a)),
      Path.of_key(Path.key(b)),
      Equal.sym(Path, Path.of_key(Path.key(a)), a, Path.key_back(a)),
      Equal.cong(
        List<&2, Bool>,
        Path,
        k => Path.of_key(k),
        Path.key(a),
        Path.key(b),
        Tries.Trie.same_key_sound(Path.key(a), Path.key(b))(h)
      )
    ),
    Path.key_back(b)
  )

# v and w are the same place
def Walk.is_eq(v: Walk, w: Walk) -> Bool:
  match v w:
    case Dead{} Dead{}:
      True{}
    case At{a, x} At{b, y}:
      List.all.if(u => St.is_eq(x, y), Path.is_eq(a, b))
    case _ _:
      False{}

# Walk.is_eq is True for a place and itself
def Walk.is_eq_refl(w: Walk) -> {Walk.is_eq(w, w) == True{}: Bool}:
  match w:
    case Dead{}:
      {==}
    case At{+a, +x}:
      Shared.List.all.if_both(
        Path.is_eq(a, a),
        u => St.is_eq(x, x)
      )(Path.is_eq_refl(a))(St.is_eq_refl(x))

# Walk.is_eq is True only for the same place
def Walk.is_eq_sound(v: Walk, w: Walk) -> {Walk.is_eq(v, w) == True{}: Bool} -> {v == w: Walk}:
  match v w:
    case Dead{} Dead{}:
      h => {==}
    case Dead{} At{b, y}:
      h => Empty.absurd({Dead{} == At{b, y}: Walk}, Shared.Bool.false_ne_true(h))
    case At{a, x} Dead{}:
      h => Empty.absurd({At{a, x} == Dead{}: Walk}, Shared.Bool.false_ne_true(h))
    case At{+a, +x} At{+b, +y}:
      +h =>
        %Path.is_eq_sound(
          a,
          b
        )(
          Shared.List.all.if_hit(Path.is_eq(a, b), u => St.is_eq(x, y))(h)
        ): {At{a, x} == At{_, y}: Walk}
        %St.is_eq_sound(
          x,
          y
        )(
          Shared.List.all.if_rest(Path.is_eq(a, b), u => St.is_eq(x, y))(h)
        ): {At{a, x} == At{a, _}: Walk}
        {==}

# the laws of Walk.is_eq
def Walk.laws() -> Shared.Eq.Laws(Walk, Walk.is_eq):
  (Walk.is_eq_refl, Walk.is_eq_sound)

# the key of a place
def Walk.key(w: Walk) -> List<&2, Bool>:
  match w:
    case Dead{}:
      [False{}]
    case At{a, x}:
      True{} <> List.append(&2, Bool, Path.key(a), St.key(x))

# Representative characters
# -------------------------
# A character moves the machine as its mark does (Spans.rep): the two are in
# the same spans (Spans.rep_alike). The spans are those of the classes of the
# query, a character of a Lit as a span of one, and the characters with a
# role of their own for a path, each a span of one. The search moves the
# machine only under the marks of those spans, each once.

# the key of c
def Char.key(c: Char) -> List<&2, Bool>:
  match c:
    case Chr{x}:
      Tries.Trie.char(x)

# the marks that the search moves the machine under, each once
def Abc.syms(g: Abc) -> List<&2, Char>:
  match g:
    case Abc{ss}:
      KeySets.KeySet.unique(
        ~Char,
        ~Char.is_eq,
        ~Char.key,
        Spans.Spans.marks(ss),
        Tries.Trie.new(Char)
      )

# the characters with a role of their own for a path, each a span of one
def Role.spans() -> List<&2, Spans.Span>:
  [
    Spans.Span{'/', '/'},
    Spans.Span{'.', '.'},
    Spans.Span{Chr{0}, Chr{0}},
    Spans.Span{Chr{92}, Chr{92}}
  ]

# ss holds the span s
def Span.within(ss: List<&2, Spans.Span>, s: Spans.Span) -> Bool:
  List.contains(~Spans.Span, ~Spans.Span.is_eq, ss, s)

# every span that t names is in ss: a character of a Lit as a span of one;
# '/', which Any and a class name, is a span of Role.spans
def Atom.within(ss: List<&2, Spans.Span>, t: Spec.Atom) -> Bool:
  match t:
    case Spec.ALit{+x}:
      Span.within(ss, Spans.Span{x, x})
    case Spec.AAny{}:
      True{}
    case Spec.AClass{neg, xs}:
      Reaches.Reach.within(~Spans.Span, ~Spans.Span.is_eq, xs, ss)

# every span that slots name is in ss
def Slots.within(slots: List<&2, Slot>, +ss: List<&2, Spans.Span>) -> Bool:
  match slots:
    case Nil{}:
      True{}
    case Con{Inc{xs}, t}:
      List.all.if(
        u => Slots.within(t, ss),
        Regex.Seqs.holds(~Spec.Atom, ~List<&2, Spans.Span>, ~Atom.within, xs, ss)
      )
    case Con{Exc{xs}, t}:
      List.all.if(
        u => Slots.within(t, ss),
        Regex.Seqs.holds(~Spec.Atom, ~List<&2, Spans.Span>, ~Atom.within, xs, ss)
      )

# c and d are in the same spans of ss, and ss holds the spans of Role.spans
def Chars.near(ss: List<&2, Spans.Span>, c: Char, d: Char) -> Bool:
  +ss = ss
  List.all.if(
    u => Spans.Spans.alike(ss, c, d),
    Reaches.Reach.within(~Spans.Span, ~Spans.Span.is_eq, Role.spans(), ss)
  )

# Char.is_eq gives the same either way round
def Char.is_eq_comm(+a: Char, +b: Char) -> {Char.is_eq(a, b) == Char.is_eq(b, a): Bool}:
  Equal.trans(
    Bool,
    Char.is_eq(a, b),
    Nat.is_eq(Spans.Char.code(a), Spans.Char.code(b)),
    Char.is_eq(b, a),
    Spans.Char.is_eq_codes(a, b),
    Equal.trans(
      Bool,
      Nat.is_eq(Spans.Char.code(a), Spans.Char.code(b)),
      Nat.is_eq(Spans.Char.code(b), Spans.Char.code(a)),
      Char.is_eq(b, a),
      Shared.Nat.is_eq_comm(Spans.Char.code(a), Spans.Char.code(b)),
      Equal.sym(
        Bool,
        Char.is_eq(b, a),
        Nat.is_eq(Spans.Char.code(b), Spans.Char.code(a)),
        Spans.Char.is_eq_codes(b, a)
      )
    )
  )

# c is k exactly when the span of one k holds c
def Char.is_eq_span(
  +c: Char,
  +k: Char
) -> {Char.is_eq(c, k) == Spans.Span.has(Spans.Span{k, k}, c): Bool}:
  Equal.trans(
    Bool,
    Char.is_eq(c, k),
    Char.is_eq(k, c),
    Spans.Span.has(Spans.Span{k, k}, c),
    Char.is_eq_comm(c, k),
    Equal.sym(Bool, Spans.Span.has(Spans.Span{k, k}, c), Char.is_eq(k, c), Spans.Span.has_one(k, c))
  )

# two characters in the same spans of ss are both k or neither, when ss
# holds the span of one k
def Char.is_eq_alike(
  ss: List<&2, Spans.Span>,
  +c: Char,
  +d: Char,
  +k: Char,
  hn: {Spans.Spans.alike(ss, c, d) == True{}: Bool},
  hk: {Span.within(ss, Spans.Span{k, k}) == True{}: Bool}
) -> {Char.is_eq(c, k) == Char.is_eq(d, k): Bool}:
  %Equal.sym(
    Bool,
    Char.is_eq(c, k),
    Spans.Span.has(Spans.Span{k, k}, c),
    Char.is_eq_span(c, k)
  ): {_ == Char.is_eq(d, k): Bool}
  %Equal.sym(
    Bool,
    Char.is_eq(d, k),
    Spans.Span.has(Spans.Span{k, k}, d),
    Char.is_eq_span(d, k)
  ): {Spans.Span.has(Spans.Span{k, k}, c) == _: Bool}
  Spans.Spans.alike_has(ss, c, d, Spans.Span{k, k})(hn)(hk)

# the role of c, from whether it is '/', '.', NUL or '\'
def Role.pick(slash: Bool, dot: Bool, nul: Bool, back: Bool) -> Role:
  Bool.pick(
    Role,
    slash,
    KSlash{},
    Bool.pick(Role, dot, KDot{}, Bool.pick(Role, Bool.or(nul, back), KBad{}, KOther{}))
  )

# Role.of by Role.pick
def Role.of_pick(
  c: Char
) -> {
  Role.of(
    c
  )
    == Role.pick(
      Char.is_eq(c, '/'),
      Char.is_eq(c, '.'),
      Char.is_eq(c, Chr{0}),
      Char.is_eq(c, Chr{92})
    ): Role
}:
  match c:
    case Chr{x}:
      {==}

# two characters in the same spans of ss have the same role, when ss holds
# the spans of Role.spans
def Role.alike(
  +ss: List<&2, Spans.Span>,
  +c: Char,
  +d: Char,
  +hn: {Spans.Spans.alike(ss, c, d) == True{}: Bool},
  +hr: {Reaches.Reach.within(~Spans.Span, ~Spans.Span.is_eq, Role.spans(), ss) == True{}: Bool}
) -> {Role.of(c) == Role.of(d): Role}:
  +w0 = Span.within(ss, Spans.Span{'/', '/'})
  +w1 = Span.within(ss, Spans.Span{'.', '.'})
  +w2 = Span.within(ss, Spans.Span{Chr{0}, Chr{0}})
  +w3 = Span.within(ss, Spans.Span{Chr{92}, Chr{92}})
  +r1 = Shared.Bool.and_true_right(w0, Bool.and(w1, Bool.and(w2, Bool.and(w3, True{}))))(hr)
  +r2 = Shared.Bool.and_true_right(w1, Bool.and(w2, Bool.and(w3, True{})))(r1)
  r3 = Shared.Bool.and_true_right(w2, Bool.and(w3, True{}))(r2)
  %Equal.sym(
    Role,
    Role.of(c),
    Role.pick(
      Char.is_eq(c, '/'),
      Char.is_eq(c, '.'),
      Char.is_eq(c, Chr{0}),
      Char.is_eq(c, Chr{92})
    ),
    Role.of_pick(c)
  ): {_ == Role.of(d): Role}
  %Equal.sym(
    Role,
    Role.of(d),
    Role.pick(
      Char.is_eq(d, '/'),
      Char.is_eq(d, '.'),
      Char.is_eq(d, Chr{0}),
      Char.is_eq(d, Chr{92})
    ),
    Role.of_pick(d)
  ): {
    Role.pick(
      Char.is_eq(c, '/'),
      Char.is_eq(c, '.'),
      Char.is_eq(c, Chr{0}),
      Char.is_eq(c, Chr{92})
    )
      == _: Role
  }
  %Equal.sym(
    Bool,
    Char.is_eq(c, '/'),
    Char.is_eq(d, '/'),
    Char.is_eq_alike(
      ss,
      c,
      d,
      '/',
      hn,
      Shared.Bool.and_true_left(w0, Bool.and(w1, Bool.and(w2, Bool.and(w3, True{}))))(hr)
    )
  ): {
    Role.pick(
      _,
      Char.is_eq(c, '.'),
      Char.is_eq(c, Chr{0}),
      Char.is_eq(c, Chr{92})
    )
      == Role.pick(
        Char.is_eq(d, '/'),
        Char.is_eq(d, '.'),
        Char.is_eq(d, Chr{0}),
        Char.is_eq(d, Chr{92})
      ): Role
  }
  %Equal.sym(
    Bool,
    Char.is_eq(c, '.'),
    Char.is_eq(d, '.'),
    Char.is_eq_alike(
      ss,
      c,
      d,
      '.',
      hn,
      Shared.Bool.and_true_left(w1, Bool.and(w2, Bool.and(w3, True{})))(r1)
    )
  ): {
    Role.pick(
      Char.is_eq(d, '/'),
      _,
      Char.is_eq(c, Chr{0}),
      Char.is_eq(c, Chr{92})
    )
      == Role.pick(
        Char.is_eq(d, '/'),
        Char.is_eq(d, '.'),
        Char.is_eq(d, Chr{0}),
        Char.is_eq(d, Chr{92})
      ): Role
  }
  %Equal.sym(
    Bool,
    Char.is_eq(c, Chr{0}),
    Char.is_eq(d, Chr{0}),
    Char.is_eq_alike(ss, c, d, Chr{0}, hn, Shared.Bool.and_true_left(w2, Bool.and(w3, True{}))(r2))
  ): {
    Role.pick(
      Char.is_eq(d, '/'),
      Char.is_eq(d, '.'),
      _,
      Char.is_eq(c, Chr{92})
    )
      == Role.pick(
        Char.is_eq(d, '/'),
        Char.is_eq(d, '.'),
        Char.is_eq(d, Chr{0}),
        Char.is_eq(d, Chr{92})
      ): Role
  }
  %Equal.sym(
    Bool,
    Char.is_eq(c, Chr{92}),
    Char.is_eq(d, Chr{92}),
    Char.is_eq_alike(ss, c, d, Chr{92}, hn, Shared.Bool.and_true_left(w3, True{})(r3))
  ): {
    Role.pick(
      Char.is_eq(d, '/'),
      Char.is_eq(d, '.'),
      Char.is_eq(d, Chr{0}),
      _
    )
      == Role.pick(
        Char.is_eq(d, '/'),
        Char.is_eq(d, '.'),
        Char.is_eq(d, Chr{0}),
        Char.is_eq(d, Chr{92})
      ): Role
  }
  {==}

# two characters in the same spans of ss are both inner or neither, when ss
# holds the spans of Role.spans
def Inner.alike(
  +ss: List<&2, Spans.Span>,
  +c: Char,
  +d: Char,
  +hn: {Chars.near(ss, c, d) == True{}: Bool}
) -> {Spec.is_inner(c) == Spec.is_inner(d): Bool}:
  hr = Shared.List.all.if_hit(
    Reaches.Reach.within(~Spans.Span, ~Spans.Span.is_eq, Role.spans(), ss),
    u => Spans.Spans.alike(ss, c, d)
  )(hn)
  %Equal.sym(
    Bool,
    Char.is_eq(c, '/'),
    Char.is_eq(d, '/'),
    Char.is_eq_alike(
      ss,
      c,
      d,
      '/',
      Shared.List.all.if_rest(
        Reaches.Reach.within(~Spans.Span, ~Spans.Span.is_eq, Role.spans(), ss),
        u => Spans.Spans.alike(ss, c, d)
      )(hn),
      Shared.Bool.and_true_left(
        Span.within(ss, Spans.Span{'/', '/'}),
        Bool.and(
          Span.within(ss, Spans.Span{'.', '.'}),
          Bool.and(
            Span.within(ss, Spans.Span{Chr{0}, Chr{0}}),
            Bool.and(Span.within(ss, Spans.Span{Chr{92}, Chr{92}}), True{})
          )
        )
      )(hr)
    )
  ): {Bool.not(_) == Spec.is_inner(d): Bool}
  {==}

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- only proofs use it; no program runs it
# two characters in the same spans of ss are in the same spans of xs, when ss
# holds each span of xs
def Class.alike(
  xs: List<&2, Spans.Span>,
  +ss: List<&2, Spans.Span>,
  +c: Char,
  +d: Char,
  +hn: {Spans.Spans.alike(ss, c, d) == True{}: Bool}
) -> {
  Reaches.Reach.within(~Spans.Span, ~Spans.Span.is_eq, xs, ss) == True{}: Bool
} -> {Spans.Spans.has(xs, c) == Spans.Spans.has(xs, d): Bool}:
  match xs:
    case Nil{}:
      e => {==}
    case Con{+x, +r}:
      +e =>
        %Equal.sym(
          Bool,
          Spans.Span.has(x, c),
          Spans.Span.has(x, d),
          Spans.Spans.alike_has(
            ss,
            c,
            d,
            x
          )(
            hn
          )(
            Shared.Bool.and_true_left(
              Span.within(ss, x),
              Reaches.Reach.within(~Spans.Span, ~Spans.Span.is_eq, r, ss)
            )(e)
          )
        ): {
          List.any.if(
            u => Spans.Spans.has(r, c),
            _
          )
            == List.any.if(u => Spans.Spans.has(r, d), Spans.Span.has(x, d)): Bool
        }
        %Equal.sym(
          Bool,
          Spans.Spans.has(r, c),
          Spans.Spans.has(r, d),
          Class.alike(
            r,
            ss,
            c,
            d,
            hn
          )(
            Shared.Bool.and_true_right(
              Span.within(ss, x),
              Reaches.Reach.within(~Spans.Span, ~Spans.Span.is_eq, r, ss)
            )(e)
          )
        ): {
          List.any.if(
            u => _,
            Spans.Span.has(x, d)
          )
            == List.any.if(u => Spans.Spans.has(r, d), Spans.Span.has(x, d)): Bool
        }
        {==}
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# an atom whose spans are in ss accepts c exactly when it accepts d, two
# characters in the same spans of ss, when ss holds the spans of Role.spans
def Atom.alike(
  +ss: List<&2, Spans.Span>,
  +c: Char,
  +d: Char,
  t: Spec.Atom,
  +hn: {Chars.near(ss, c, d) == True{}: Bool},
  hp: {Atom.within(ss, t) == True{}: Bool}
) -> {Spec.Atom.hit(t, c) == Spec.Atom.hit(t, d): Bool}:
  match t:
    case Spec.ALit{+x}:
      %Equal.sym(
        Bool,
        Char.is_eq(x, c),
        Char.is_eq(c, x),
        Char.is_eq_comm(x, c)
      ): {_ == Char.is_eq(x, d): Bool}
      %Equal.sym(
        Bool,
        Char.is_eq(x, d),
        Char.is_eq(d, x),
        Char.is_eq_comm(x, d)
      ): {Char.is_eq(c, x) == _: Bool}
      Char.is_eq_alike(
        ss,
        c,
        d,
        x,
        Shared.List.all.if_rest(
          Reaches.Reach.within(~Spans.Span, ~Spans.Span.is_eq, Role.spans(), ss),
          u => Spans.Spans.alike(ss, c, d)
        )(hn),
        hp
      )
    case Spec.AAny{}:
      Inner.alike(ss, c, d, hn)
    case Spec.AClass{neg, xs}:
      %Equal.sym(
        Bool,
        Spans.Spans.has(xs, c),
        Spans.Spans.has(xs, d),
        Class.alike(
          xs,
          ss,
          c,
          d,
          Shared.List.all.if_rest(
            Reaches.Reach.within(~Spans.Span, ~Spans.Span.is_eq, Role.spans(), ss),
            u => Spans.Spans.alike(ss, c, d)
          )(hn)
        )(hp)
      ): {
        List.all.if(
          u => Bool.xor(neg, _),
          Spec.is_inner(c)
        )
          == List.all.if(u => Bool.xor(neg, Spans.Spans.has(xs, d)), Spec.is_inner(d)): Bool
      }
      %Equal.sym(
        Bool,
        Spec.is_inner(c),
        Spec.is_inner(d),
        Inner.alike(ss, c, d, hn)
      ): {
        List.all.if(
          u => Bool.xor(neg, Spans.Spans.has(xs, d)),
          _
        )
          == List.all.if(u => Bool.xor(neg, Spans.Spans.has(xs, d)), Spec.is_inner(d)): Bool
      }
      {==}

# slots step alike under two characters in the same spans of ss, when ss
# holds the spans of Role.spans and every span that the slots name
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- only proofs use it; no program runs it
def Slot.step_alike(
  slots: List<&2, Slot>,
  +ss: List<&2, Spans.Span>,
  +c: Char,
  +d: Char,
  +hn: {Chars.near(ss, c, d) == True{}: Bool}
) -> {
  Slots.within(slots, ss) == True{}: Bool
} -> {Slot.step(slots, c) == Slot.step(slots, d): List<&2, Slot>}:
  match slots:
    case Nil{}:
      _ => {==}
    case Con{Inc{+xs}, +t}:
      +hw =>
        +wx = Regex.Seqs.holds(~Spec.Atom, ~List<&2, Spans.Span>, ~Atom.within, xs, ss)
        +xc = Regex.Seqs.step(~Char, ~Spec.Atom, ~Spec.Atom.hit, ~Atom.is_eq, ~Atom.key, xs, c)
        +tc = Slot.step(t, c)
        %Regex.Seqs.step_alike(
          ~Char,
          ~Spec.Atom,
          ~List<&2, Spans.Span>,
          ~Spec.Atom.hit,
          ~Atom.is_eq,
          ~Atom.key,
          ~Atom.within,
          ~Chars.near,
          ~(g => c2 => d2 => t2 => hn2 => hp2 => Atom.alike(g, c2, d2, t2, hn2, hp2)),
          xs,
          ss,
          c,
          d
        )(
          hn
        )(
          Shared.List.all.if_hit(wx, u => Slots.within(t, ss))(hw)
        ): {Con{Inc{xc}, tc} == Con{Inc{_}, Slot.step(t, d)}: List<&2, Slot>}
        %Slot.step_alike(
          t,
          ss,
          c,
          d,
          hn
        )(
          Shared.List.all.if_rest(wx, u => Slots.within(t, ss))(hw)
        ): {Con{Inc{xc}, tc} == Con{Inc{xc}, _}: List<&2, Slot>}
        {==}
    case Con{Exc{+xs}, +t}:
      +hw =>
        +wx = Regex.Seqs.holds(~Spec.Atom, ~List<&2, Spans.Span>, ~Atom.within, xs, ss)
        +xc = Regex.Seqs.step(~Char, ~Spec.Atom, ~Spec.Atom.hit, ~Atom.is_eq, ~Atom.key, xs, c)
        +tc = Slot.step(t, c)
        %Regex.Seqs.step_alike(
          ~Char,
          ~Spec.Atom,
          ~List<&2, Spans.Span>,
          ~Spec.Atom.hit,
          ~Atom.is_eq,
          ~Atom.key,
          ~Atom.within,
          ~Chars.near,
          ~(g => c2 => d2 => t2 => hn2 => hp2 => Atom.alike(g, c2, d2, t2, hn2, hp2)),
          xs,
          ss,
          c,
          d
        )(
          hn
        )(
          Shared.List.all.if_hit(wx, u => Slots.within(t, ss))(hw)
        ): {Con{Exc{xc}, tc} == Con{Exc{_}, Slot.step(t, d)}: List<&2, Slot>}
        %Slot.step_alike(
          t,
          ss,
          c,
          d,
          hn
        )(
          Shared.List.all.if_rest(wx, u => Slots.within(t, ss))(hw)
        ): {Con{Exc{xc}, tc} == Con{Exc{xc}, _}: List<&2, Slot>}
        {==}
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# a mark of the spans ss is one of the characters that the search moves the
# machine under
def Abc.has_mark(
  ss: List<&2, Spans.Span>,
  +d: Char
) -> {
  List.contains(~Char, ~Char.is_eq, Spans.Spans.marks(ss), d) == True{}: Bool
} -> {List.contains(~Char, ~Char.is_eq, Abc.syms(Abc{ss}), d) == True{}: Bool}:
  e =>
    +ms = Spans.Spans.marks(ss)
    +us = KeySets.KeySet.unique(~Char, ~Char.is_eq, ~Char.key, ms, Tries.Trie.new(Char))
    Equal.trans(
      Bool,
      List.contains(~Char, ~Char.is_eq, us, d),
      Shared.List.some(~Char, ~Char, ~(g => x => Char.is_eq(x, g)), us, d),
      True{},
      Shared.List.contains_some(~Char, ~Char.is_eq, us, d),
      Equal.trans(
        Bool,
        Shared.List.some(~Char, ~Char, ~(g => x => Char.is_eq(x, g)), us, d),
        Shared.List.some(~Char, ~Char, ~(g => x => Char.is_eq(x, g)), ms, d),
        True{},
        KeySets.KeySet.unique_some(
          ~Char,
          ~Char,
          ~Char.is_eq,
          ~Char.key,
          ~(g => x => Char.is_eq(x, g)),
          ~Shared.Char.laws(),
          ms,
          d
        ),
        Equal.trans(
          Bool,
          Shared.List.some(~Char, ~Char, ~(g => x => Char.is_eq(x, g)), ms, d),
          List.contains(~Char, ~Char.is_eq, ms, d),
          True{},
          Equal.sym(
            Bool,
            List.contains(~Char, ~Char.is_eq, ms, d),
            Shared.List.some(~Char, ~Char, ~(g => x => Char.is_eq(x, g)), ms, d),
            Shared.List.contains_some(~Char, ~Char.is_eq, ms, d)
          ),
          e
        )
      )
    )

# w is Dead; or the spans of g hold the spans of Role.spans and every span that
# the state of w names
def Walk.covers(g: Abc, w: Walk) -> Bool:
  match g w:
    case _ Dead{}:
      True{}
    case Abc{+ss} At{p, St{both, a, b}}:
      List.all.if(
        u => List.all.if(u2 => Slots.within(b, ss), Slots.within(a, ss)),
        Reaches.Reach.within(~Spans.Span, ~Spans.Span.is_eq, Role.spans(), ss)
      )

# under a place that g covers, each character moves the machine as its mark
# does, a character of Abc.syms(g)
def Walk.rep(
  g: Abc,
  w: Walk,
  c: Char,
  h: {Walk.covers(g, w) == True{}: Bool}
) -> (
  &d: Char -> {
    List.contains(~Char, ~Char.is_eq, Abc.syms(g), d) == True{}: Bool
  }
    & {Walk.step(g, w, c) == Walk.step(g, w, d): Walk}
):
  match g w:
    case Abc{+ss} Dead{}:
      (Chr{0}, (Abc.has_mark(ss, Chr{0})({==}), {==}))
    case Abc{+ss} At{p, St{both, +a, +b}}:
      +c = c
      +h = h
      +ms = Spans.Spans.marks(ss)
      +d = Spans.Spans.rep(ms, c)
      +roles = Reaches.Reach.within(~Spans.Span, ~Spans.Span.is_eq, Role.spans(), ss)
      +wa = Slots.within(a, ss)
      +wb = Slots.within(b, ss)
      +hr = Shared.List.all.if_hit(roles, u => List.all.if(u2 => wb, wa))(h)
      +hw = Shared.List.all.if_rest(roles, u => List.all.if(u2 => wb, wa))(h)
      +ha = Spans.Spans.rep_alike(ss, ms, c)(Spans.Spans.marks_covered(ss))
      +hn = Shared.List.all.if_both(roles, u => Spans.Spans.alike(ss, c, d))(hr)(ha)
      (d, (Abc.has_mark(ss, d)(Spans.Spans.rep_in(ms, c)({==})), (
            %Equal.sym(Role, Role.of(c), Role.of(d), Role.alike(ss, c, d, ha, hr)): {Walk.at(Path.step(p, _), u => St{both, Slot.step(a, c), Slot.step(b, c)}) == Walk.step(Abc{ss}, At{p, St{both, a, b}}, d): Walk}
            %Equal.sym(List<&2, Slot>, Slot.step(a, c), Slot.step(a, d), Slot.step_alike(a, ss, c, d, hn)(Shared.List.all.if_hit(wa, u2 => wb)(hw))): {Walk.at(Path.step(p, Role.of(d)), u => St{both, _, Slot.step(b, c)}) == Walk.step(Abc{ss}, At{p, St{both, a, b}}, d): Walk}
            %Equal.sym(List<&2, Slot>, Slot.step(b, c), Slot.step(b, d), Slot.step_alike(b, ss, c, d, hn)(Shared.List.all.if_rest(wa, u2 => wb)(hw))): {Walk.at(Path.step(p, Role.of(d)), u => St{both, Slot.step(a, d), _}) == Walk.step(Abc{ss}, At{p, St{both, a, b}}, d): Walk}
            {==})))

# Search
# ------
# The search needs no proof: `decide` checks what it returns. It visits the
# places that the machine can reach from the place of the query. A word that
# the machine accepts is a path to check; when no place accepts, the places
# are a certificate to check.

# the spans that g names, in front of acc: a character of a Lit as a span of
# one
def Glob.spans(g: Spec.Glob, acc: List<&2, Spans.Span>) -> List<&2, Spans.Span>:
  match g:
    case Spec.Void{}:
      acc
    case Spec.Eps{}:
      acc
    case Spec.Lit{+x}:
      Spans.Span{x, x} <> acc
    case Spec.Any{}:
      acc
    case Spec.Star{}:
      acc
    case Spec.Class{n, ss}:
      List.append(&2, Spans.Span, ss, acc)
    case Spec.Deep{}:
      acc
    case Spec.Cat{a, b}:
      Glob.spans(a, Glob.spans(b, acc))
    case Spec.Alt{a, b}:
      Glob.spans(a, Glob.spans(b, acc))

# the spans that the globs of rules name, in front of acc
def Rules.spans(rules: List<&2, Spec.Rule>, acc: List<&2, Spans.Span>) -> List<&2, Spans.Span>:
  match rules:
    case Nil{}:
      acc
    case Con{Spec.Include{g}, t}:
      Glob.spans(g, Rules.spans(t, acc))
    case Con{Spec.Exclude{g}, t}:
      Glob.spans(g, Rules.spans(t, acc))

# the spans of Role.spans and those that the globs of a and b name, each once
def Rules.abc(a: List<&2, Spec.Rule>, b: List<&2, Spec.Rule>) -> Abc:
  Abc{
    KeySets.KeySet.unique(
      ~Spans.Span,
      ~Spans.Span.is_eq,
      ~Span.key,
      List.append(&2, Spans.Span, Role.spans(), Rules.spans(a, Rules.spans(b, []))),
      Tries.Trie.new(Spans.Span)
    )
  }

# what the machine knows for q
def Query.abc(q: Spec.Query) -> Abc:
  match q:
    case Spec.Both{a, b}:
      Rules.abc(a, b)
    case Spec.Only{a, b}:
      Rules.abc(a, b)

# the places a search may visit before it gives up
def Search.fuel() -> Nat:
  4096n

# what the search finds for q, under the characters of g
def Search.run(q: Spec.Query, g: Abc) -> Searches.Found<Walk, Char>:
  Searches.Search.run(
    ~Walk,
    ~Char,
    ~Abc,
    ~Walk.is_eq,
    ~Walk.key,
    ~Walk.step,
    ~Walk.ends,
    ~Abc.syms,
    Search.fuel(),
    Walk.of(q),
    g
  )

# Found{p} when ok, else Unknown
def Search.found_if(p: String, ok: Bool) -> Spec.Search:
  match ok:
    case False{}:
      Spec.Unknown{}
    case True{}:
      Spec.Found{p}

# Absent when ok, else Unknown
def Search.absent_if(ok: Bool) -> Spec.Search:
  match ok:
    case False{}:
      Spec.Unknown{}
    case True{}:
      Spec.Absent{}

# xs is a certificate for q
def Search.proves(q: Spec.Query, xs: List<&2, Walk>, g: Abc) -> Bool:
  Searches.Cert.proves(
    ~Walk,
    ~Char,
    ~Abc,
    ~Walk.is_eq,
    ~Walk.key,
    ~Walk.step,
    ~Walk.ends,
    ~Walk.covers,
    ~Abc.syms,
    xs,
    Walk.of(q),
    g
  )

# the answer to q, from what the search found, once checked
def Search.decide(q: Spec.Query, g: Abc, r: Searches.Found<Walk, Char>) -> Spec.Search:
  match r:
    case Searches.Hit{w}:
      +p = String.from_list(w)
      Search.found_if(p, Query.holds.fast(q, p, g))
    case Searches.Closed{xs}:
      Search.absent_if(Search.proves(q, xs, g))
    case Searches.Out{}:
      Spec.Unknown{}

def Spec.Query.search(q):
  +q = q
  +g = Query.abc(q)
  Search.decide(q, g, Search.run(q, g))

# Empty when s is Found
def Search.NotFound(s: Spec.Search) -> Type:
  match s:
    case Spec.Found{p}:
      Empty
    case Spec.Absent{}:
      Unit
    case Spec.Unknown{}:
      Unit
# Empty when s is Absent
def Search.NotAbsent(s: Spec.Search) -> Type:
  match s:
    case Spec.Found{p}:
      Unit
    case Spec.Absent{}:
      Empty
    case Spec.Unknown{}:
      Unit
# no s that is not Found equals Found{p}
def Search.ne_found(
  -s: Spec.Search,
  -p: String,
  n: Search.NotFound(s),
  e: {s == Spec.Found{p}: Spec.Search}
) -> Empty:
  %e: Search.NotFound(_)
  n
# no s that is not Absent equals Absent
def Search.ne_absent(
  -s: Spec.Search,
  n: Search.NotAbsent(s),
  e: {s == Spec.Absent{}: Spec.Search}
) -> Empty:
  %e: Search.NotAbsent(_)
  n
# the path of a Found answer
def Search.path(s: Spec.Search) -> String:
  match s:
    case Spec.Found{p}:
      p
    case Spec.Absent{}:
      SNil{}
    case Spec.Unknown{}:
      SNil{}
# found_if answers Found{p} only for a path that holds, given b: the fast
# check of p0
# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- a false positive, as the rule notes: the other use is an erased argument (of Equal.sym or a motive)
def Search.found_if_found(
  q: Spec.Query,
  p0: String,
  p: String,
  g: Abc,
  b: Bool
) -> {
  Query.holds.fast(q, p0, g) == b: Bool
} -> {
  Search.found_if(p0, b) == Spec.Found{p}: Spec.Search
} -> {Spec.Query.holds(q, p) == True{}: Bool}:
  match b:
    case False{}:
      e => h => Empty.absurd(
        {Spec.Query.holds(q, p) == True{}: Bool},
        Search.ne_found(Spec.Unknown{}, p, Unit{}, h)
      )
    case True{}:
      e => h =>
        same = Equal.cong(
          Spec.Search,
          String,
          s => Search.path(s),
          Spec.Found{p0},
          Spec.Found{p},
          h
        )
        %same: {Spec.Query.holds(q, _) == True{}: Bool}
        Equal.trans(
          Bool,
          Spec.Query.holds(q, p0),
          Query.holds.fast(q, p0, g),
          True{},
          Equal.sym(
            Bool,
            Query.holds.fast(q, p0, g),
            Spec.Query.holds(q, p0),
            Query.holds_fast_ok(q, p0, g)
          ),
          e
        )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# absent_if never answers Found
def Search.absent_if_found(
  b: Bool,
  -p: String
) -> {Search.absent_if(b) == Spec.Found{p}: Spec.Search} -> Empty:
  match b:
    case False{}:
      h => Search.ne_found(Spec.Unknown{}, p, Unit{}, h)
    case True{}:
      h => Search.ne_found(Spec.Absent{}, p, Unit{}, h)
# found_if never answers Absent
def Search.found_if_absent(
  -p: String,
  b: Bool
) -> {Search.found_if(p, b) == Spec.Absent{}: Spec.Search} -> Empty:
  match b:
    case False{}:
      h => Search.ne_absent(Spec.Unknown{}, Unit{}, h)
    case True{}:
      h => Search.ne_absent(Spec.Found{p}, Unit{}, h)
# a Found answer of decide names a path that holds
def Search.decide_found(
  +q: Spec.Query,
  +g: Abc,
  r: Searches.Found<Walk, Char>,
  p: String
) -> {
  Search.decide(q, g, r) == Spec.Found{p}: Spec.Search
} -> {Spec.Query.holds(q, p) == True{}: Bool}:
  match r:
    case Searches.Hit{w}:
      +p0 = String.from_list(w)
      h => Search.found_if_found(q, p0, p, g, Query.holds.fast(q, p0, g))({==}, h)
    case Searches.Closed{xs}:
      h => Empty.absurd(
        {Spec.Query.holds(q, p) == True{}: Bool},
        Search.absent_if_found(Search.proves(q, xs, g), p)(h)
      )
    case Searches.Out{}:
      h => Empty.absurd(
        {Spec.Query.holds(q, p) == True{}: Bool},
        Search.ne_found(Spec.Unknown{}, p, Unit{}, h)
      )

# absent_if answers Absent only for a certificate for q, given b: its check
def Search.absent_if_absent(
  +q: Spec.Query,
  xs: List<&2, Walk>,
  +g: Abc,
  +p: String,
  b: Bool
) -> {
  Search.proves(q, xs, g) == b: Bool
} -> {
  Search.absent_if(b) == Spec.Absent{}: Spec.Search
} -> {Spec.Query.holds(q, p) == False{}: Bool}:
  match b:
    case False{}:
      e => h => Empty.absurd(
        {Spec.Query.holds(q, p) == False{}: Bool},
        Search.ne_absent(Spec.Unknown{}, Unit{}, h)
      )
    case True{}:
      e => h =>
        %Query.holds_fast_ok(q, p, g): {_ == False{}: Bool}
        Searches.Cert.sound(
          ~Walk,
          ~Char,
          ~Abc,
          ~Walk.is_eq,
          ~Walk.key,
          ~Char.is_eq,
          ~Walk.step,
          ~Walk.ends,
          ~Walk.covers,
          ~Abc.syms,
          ~Walk.laws(),
          ~Shared.Char.laws(),
          ~Walk.rep,
          xs,
          Walk.of(q),
          g,
          String.to_list(p)
        )(e)

# an Absent answer of decide means no path holds
def Search.decide_absent(
  +q: Spec.Query,
  +g: Abc,
  r: Searches.Found<Walk, Char>,
  p: String
) -> {
  Search.decide(q, g, r) == Spec.Absent{}: Spec.Search
} -> {Spec.Query.holds(q, p) == False{}: Bool}:
  match r:
    case Searches.Hit{w}:
      h => Empty.absurd(
        {Spec.Query.holds(q, p) == False{}: Bool},
        Search.found_if_absent(String.from_list(w), Query.holds.fast(q, String.from_list(w), g))(h)
      )
    case Searches.Closed{+xs}:
      h => Search.absent_if_absent(q, xs, g, p, Search.proves(q, xs, g))({==}, h)
    case Searches.Out{}:
      h => Empty.absurd(
        {Spec.Query.holds(q, p) == False{}: Bool},
        Search.ne_absent(Spec.Unknown{}, Unit{}, h)
      )

def Spec.search_found(q, p, h):
  +q = q
  +g = Query.abc(q)
  Search.decide_found(q, g, Search.run(q, g), p)(h)

def Spec.search_absent(q, p, h):
  +q = q
  +g = Query.abc(q)
  Search.decide_absent(q, g, Search.run(q, g), p)(h)

# Text
# ----
# Glob.show writes each glob as text that Spec.Glob.read reads back as one
# atom: Show.glob(g), which matches what g matches. Compound globs go in
# braces, so a text never depends on what follows it.

# a character is the character of its role
# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- a false positive, as the rule notes: the other use is an erased argument (of Equal.sym or a motive)
def Sym.of.go_char.at(
  s: Spec.Sym,
  t: List<&2, Spec.Sym>,
  c: Char,
  hit: Bool,
  ih: {c == Spec.Sym.char(Spec.Sym.of.go(t, c)): Char}
) -> {
  Char.is_eq(Spec.Sym.char(s), c) == hit: Bool
} -> {c == Spec.Sym.char(Spec.Sym.of.if(s, u => Spec.Sym.of.go(t, c), hit)): Char}:
  match hit:
    case False{}:
      e => ih
    case True{}:
      e => Equal.sym(Char, Spec.Sym.char(s), c, Shared.Char.is_eq_sound(Spec.Sym.char(s), c)(e))
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# the role that Sym.of.go finds for c has c as its character
def Sym.of.go_char(
  xs: List<&2, Spec.Sym>,
  +c: Char
) -> {c == Spec.Sym.char(Spec.Sym.of.go(xs, c)): Char}:
  match xs:
    case Nil{}:
      {==}
    case Con{+s, +t}:
      Sym.of.go_char.at(s, t, c, Char.is_eq(Spec.Sym.char(s), c), Sym.of.go_char(t, c))({==})

# the role of c has c as its character
def Sym.char_of(c: Char) -> {c == Spec.Sym.char(Spec.Sym.of(c)): Char}:
  Sym.of.go_char(Spec.Sym.specials(), c)

# c is the character of k, the role of c
# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- a false positive, as the rule notes: the other use is an erased argument (of Equal.sym or a motive)
def Sym.char_is(
  c: Char,
  k: Spec.Sym,
  e: {k == Spec.Sym.of(c): Spec.Sym}
) -> {c == Spec.Sym.char(k): Char}:
  %Equal.sym(Spec.Sym, k, Spec.Sym.of(c), e): {c == Spec.Sym.char(_): Char}
  Sym.char_of(c)
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# the text of c before rest: a character with a role is escaped
def Glob.show.char(c: Char, k: Spec.Sym, rest: String) -> String:
  match k:
    case Spec.SChar{x}:
      SCon{c, rest}
    case _:
      SCon{Chr{92}, SCon{c, rest}}

# the bounds of the parts of a span: the characters before '!', '!', those
# between '!' and '\', '\', ']', and those after ']'
def Span.bounds() -> List<&2, Spans.Span>:
  [
    Spans.Span{Chr{0}, Chr{32}},
    Spans.Span{Chr{33}, Chr{33}},
    Spans.Span{Chr{34}, Chr{91}},
    Spans.Span{Chr{92}, Chr{92}},
    Spans.Span{Chr{93}, Chr{93}},
    Spans.Span{Chr{94}, Chr{4294967295}}
  ]

# the parts of s inside a class, in order: its meets with the bounds. The
# parts of more than one character have no end that the text of a class gives
# a role ('!' at its start, '\' and ']'), so each part reads back as itself
def Span.parts(s: Spans.Span) -> List<&2, Spans.Span>:
  Spans.Span.meets(s, Span.bounds())

# Span.show once it is known whether the span is empty (gap) and whether it is
# one character (one)
def Span.show.at(lo: U32, hi: U32, gap: Bool, one: Bool, rest: String) -> String:
  match gap one:
    case True{} x:
      rest
    case False{} True{}:
      SCon{Chr{92}, SCon{Chr{lo}, rest}}
    case False{} False{}:
      SCon{Chr{lo}, SCon{'-', SCon{Chr{hi}, rest}}}

# the text of the span s in a class, before rest: nothing when it is empty, the
# character escaped when it is one, else `lo-hi`
def Span.show(s: Spans.Span, rest: String) -> String:
  match s:
    case Spans.Span{Chr{+lo}, Chr{+hi}}:
      Span.show.at(lo, hi, U32.is_lt(hi, lo), U32.is_eq(lo, hi), rest)

# the text of each span of ss, before rest
def Span.show.all(ss: List<&2, Spans.Span>, rest: String) -> String:
  match ss:
    case Nil{}:
      rest
    case Con{s, t}:
      Span.show(s, Span.show.all(t, rest))

# the text of each span of ss in a class, part by part, before rest
def Glob.show.spans(ss: List<&2, Spans.Span>, rest: String) -> String:
  match ss:
    case Nil{}:
      rest
    case Con{s, t}:
      Span.show.all(Span.parts(s), Glob.show.spans(t, rest))

# `!` before text when neg
def Glob.show.neg(neg: Bool, text: String) -> String:
  match neg:
    case False{}:
      text
    case True{}:
      SCon{'!', text}

# the text of g before rest
def Glob.show.go(g: Spec.Glob, rest: String) -> String:
  match g:
    case Spec.Void{}:
      "[]" ++ rest
    case Spec.Eps{}:
      "{}" ++ rest
    case Spec.Lit{+c}:
      Glob.show.char(c, Spec.Sym.of(c), rest)
    case Spec.Any{}:
      "?" ++ rest
    case Spec.Star{}:
      "{*}" ++ rest
    case Spec.Class{neg, ss}:
      "[" ++ Glob.show.neg(neg, Glob.show.spans(ss, "]" ++ rest))
    case Spec.Deep{}:
      "{*{,/**}}" ++ rest
    case Spec.Cat{a, b}:
      "{" ++ Glob.show.go(a, Glob.show.go(b, "}" ++ rest))
    case Spec.Alt{a, b}:
      "{" ++ Glob.show.go(a, "," ++ Glob.show.go(b, "}" ++ rest))

def Spec.Glob.show(g):
  Glob.show.go(g, "")

# the glob that the text of Deep reads back as
def Show.deep() -> Spec.Glob:
  dirs = {
    Spec.Alt{
      Spec.Eps{},
      Spec.Alt{Spec.Cat{Spec.Lit{Chr{47}}, Spec.Cat{Spec.Deep{}, Spec.Eps{}}}, Spec.Void{}}
    }: Spec.Glob
  }
  Spec.Alt{Spec.Cat{Spec.Star{}, Spec.Cat{dirs, Spec.Eps{}}}, Spec.Void{}}

# the span s before acc, unless it is empty (gap)
def Span.keep.at(gap: Bool, s: Spans.Span, acc: List<&2, Spans.Span>) -> List<&2, Spans.Span>:
  match gap:
    case True{}:
      acc
    case False{}:
      s <> acc

# the span s before acc, unless it is empty: what the reader keeps of the
# text of s
def Span.keep(s: Spans.Span, acc: List<&2, Spans.Span>) -> List<&2, Spans.Span>:
  match s:
    case Spans.Span{Chr{+lo}, Chr{+hi}}:
      Span.keep.at(U32.is_lt(hi, lo), Spans.Span{Chr{lo}, Chr{hi}}, acc)

# the spans that the reader keeps of the text of the spans xs, after acc
def Span.keep.all(xs: List<&2, Spans.Span>, acc: List<&2, Spans.Span>) -> List<&2, Spans.Span>:
  match xs:
    case Nil{}:
      acc
    case Con{x, t}:
      Span.keep.all(t, Span.keep(x, acc))

# the spans that the reader keeps of the text of the class ss, after acc: the
# parts that are not empty, last first
def Show.spans(ss: List<&2, Spans.Span>, acc: List<&2, Spans.Span>) -> List<&2, Spans.Span>:
  match ss:
    case Nil{}:
      acc
    case Con{s, t}:
      Show.spans(t, Span.keep.all(Span.parts(s), acc))

# the glob that the text of g reads back as
# bend-lint: expect-begin bend-lint-rules/performance/missed_fork@hint -- a glob tree is a few nodes, where a fork costs more than it saves
def Show.glob(g: Spec.Glob) -> Spec.Glob:
  match g:
    case Spec.Void{}:
      Spec.Class{False{}, []}
    case Spec.Eps{}:
      Spec.Alt{Spec.Eps{}, Spec.Void{}}
    case Spec.Lit{c}:
      Spec.Lit{c}
    case Spec.Any{}:
      Spec.Any{}
    case Spec.Star{}:
      Spec.Alt{Spec.Cat{Spec.Star{}, Spec.Eps{}}, Spec.Void{}}
    case Spec.Class{neg, ss}:
      Spec.Class{neg, Show.spans(ss, [])}
    case Spec.Deep{}:
      Show.deep()
    case Spec.Cat{a, b}:
      Spec.Alt{Spec.Cat{Show.glob(a), Spec.Cat{Show.glob(b), Spec.Eps{}}}, Spec.Void{}}
    case Spec.Alt{a, b}:
      Spec.Alt{
        Spec.Cat{Show.glob(a), Spec.Eps{}},
        Spec.Alt{Spec.Cat{Show.glob(b), Spec.Eps{}}, Spec.Void{}}
      }
# bend-lint: expect-end bend-lint-rules/performance/missed_fork@hint

# Parser steps
# ------------
# The parser looks up to three symbols ahead, so each step lemma splits the
# unknown symbols it looks at.

# a plain character is a Lit
def Step.char(
  x: Char,
  l: List<&2, Spec.Sym>,
  st: List<&2, Spec.Frame>,
  seg: Bool
) -> {
  Spec.Glob.read.go(
    l,
    Spec.Out{},
    Spec.Frame.add(st, Spec.Lit{x}),
    False{}
  )
    == Spec.Glob.read.go(Con{Spec.SChar{x}, l}, Spec.Out{}, st, seg): Maybe<&2, Spec.Glob>
}:
  match l:
    case Nil{}:
      {==}
    case Con{y1, l2}:
      match y1:
        case Spec.SEsc{}:
          {==}
        case Spec.SAny{}:
          {==}
        case Spec.SStar{}:
          match l2:
            case Nil{}:
              {==}
            case Con{y6, l7}:
              match y6:
                case Spec.SEsc{}:
                  {==}
                case Spec.SAny{}:
                  {==}
                case Spec.SStar{}:
                  {==}
                case Spec.SSlash{}:
                  {==}
                case Spec.SOpen{}:
                  {==}
                case Spec.SComma{}:
                  {==}
                case Spec.SClose{}:
                  {==}
                case Spec.SLeft{}:
                  {==}
                case Spec.SRight{}:
                  {==}
                case Spec.SBang{}:
                  {==}
                case Spec.SDash{}:
                  {==}
                case Spec.SChar{ch19}:
                  {==}
        case Spec.SSlash{}:
          {==}
        case Spec.SOpen{}:
          {==}
        case Spec.SComma{}:
          {==}
        case Spec.SClose{}:
          {==}
        case Spec.SLeft{}:
          {==}
        case Spec.SRight{}:
          {==}
        case Spec.SBang{}:
          {==}
        case Spec.SDash{}:
          match l2:
            case Nil{}:
              {==}
            case Con{y28, l29}:
              match y28:
                case Spec.SEsc{}:
                  {==}
                case Spec.SAny{}:
                  {==}
                case Spec.SStar{}:
                  {==}
                case Spec.SSlash{}:
                  {==}
                case Spec.SOpen{}:
                  {==}
                case Spec.SComma{}:
                  {==}
                case Spec.SClose{}:
                  {==}
                case Spec.SLeft{}:
                  {==}
                case Spec.SRight{}:
                  {==}
                case Spec.SBang{}:
                  {==}
                case Spec.SDash{}:
                  {==}
                case Spec.SChar{ch41}:
                  {==}
        case Spec.SChar{ch42}:
          {==}

# an escaped symbol is a Lit of its character
def Step.esc(
  y: Spec.Sym,
  l: List<&2, Spec.Sym>,
  st: List<&2, Spec.Frame>,
  seg: Bool
) -> {
  Spec.Glob.read.go(
    l,
    Spec.Out{},
    Spec.Frame.add(st, Spec.Lit{Spec.Sym.char(y)}),
    False{}
  )
    == Spec.Glob.read.go(Con{Spec.SEsc{}, Con{y, l}}, Spec.Out{}, st, seg): Maybe<&2, Spec.Glob>
}:
  match y:
    case Spec.SEsc{}:
      {==}
    case Spec.SAny{}:
      {==}
    case Spec.SStar{}:
      match l:
        case Nil{}:
          {==}
        case Con{y4, l5}:
          match y4:
            case Spec.SEsc{}:
              {==}
            case Spec.SAny{}:
              {==}
            case Spec.SStar{}:
              {==}
            case Spec.SSlash{}:
              {==}
            case Spec.SOpen{}:
              {==}
            case Spec.SComma{}:
              {==}
            case Spec.SClose{}:
              {==}
            case Spec.SLeft{}:
              {==}
            case Spec.SRight{}:
              {==}
            case Spec.SBang{}:
              {==}
            case Spec.SDash{}:
              {==}
            case Spec.SChar{ch17}:
              {==}
    case Spec.SSlash{}:
      {==}
    case Spec.SOpen{}:
      {==}
    case Spec.SComma{}:
      {==}
    case Spec.SClose{}:
      {==}
    case Spec.SLeft{}:
      {==}
    case Spec.SRight{}:
      {==}
    case Spec.SBang{}:
      {==}
    case Spec.SDash{}:
      match l:
        case Nil{}:
          {==}
        case Con{y26, l27}:
          match y26:
            case Spec.SEsc{}:
              {==}
            case Spec.SAny{}:
              {==}
            case Spec.SStar{}:
              {==}
            case Spec.SSlash{}:
              {==}
            case Spec.SOpen{}:
              {==}
            case Spec.SComma{}:
              {==}
            case Spec.SClose{}:
              {==}
            case Spec.SLeft{}:
              {==}
            case Spec.SRight{}:
              {==}
            case Spec.SBang{}:
              {==}
            case Spec.SDash{}:
              {==}
            case Spec.SChar{ch39}:
              {==}
    case Spec.SChar{ch40}:
      {==}

# `?` is Any
def Step.any(
  l: List<&2, Spec.Sym>,
  st: List<&2, Spec.Frame>,
  seg: Bool
) -> {
  Spec.Glob.read.go(
    l,
    Spec.Out{},
    Spec.Frame.add(st, Spec.Any{}),
    False{}
  )
    == Spec.Glob.read.go(Con{Spec.SAny{}, l}, Spec.Out{}, st, seg): Maybe<&2, Spec.Glob>
}:
  match l:
    case Nil{}:
      {==}
    case Con{y1, l2}:
      match y1:
        case Spec.SEsc{}:
          {==}
        case Spec.SAny{}:
          {==}
        case Spec.SStar{}:
          match l2:
            case Nil{}:
              {==}
            case Con{y6, l7}:
              match y6:
                case Spec.SEsc{}:
                  {==}
                case Spec.SAny{}:
                  {==}
                case Spec.SStar{}:
                  {==}
                case Spec.SSlash{}:
                  {==}
                case Spec.SOpen{}:
                  {==}
                case Spec.SComma{}:
                  {==}
                case Spec.SClose{}:
                  {==}
                case Spec.SLeft{}:
                  {==}
                case Spec.SRight{}:
                  {==}
                case Spec.SBang{}:
                  {==}
                case Spec.SDash{}:
                  {==}
                case Spec.SChar{ch19}:
                  {==}
        case Spec.SSlash{}:
          {==}
        case Spec.SOpen{}:
          {==}
        case Spec.SComma{}:
          {==}
        case Spec.SClose{}:
          {==}
        case Spec.SLeft{}:
          {==}
        case Spec.SRight{}:
          {==}
        case Spec.SBang{}:
          {==}
        case Spec.SDash{}:
          match l2:
            case Nil{}:
              {==}
            case Con{y28, l29}:
              match y28:
                case Spec.SEsc{}:
                  {==}
                case Spec.SAny{}:
                  {==}
                case Spec.SStar{}:
                  {==}
                case Spec.SSlash{}:
                  {==}
                case Spec.SOpen{}:
                  {==}
                case Spec.SComma{}:
                  {==}
                case Spec.SClose{}:
                  {==}
                case Spec.SLeft{}:
                  {==}
                case Spec.SRight{}:
                  {==}
                case Spec.SBang{}:
                  {==}
                case Spec.SDash{}:
                  {==}
                case Spec.SChar{ch41}:
                  {==}
        case Spec.SChar{ch42}:
          {==}

# `{` opens a frame
def Step.open(
  l: List<&2, Spec.Sym>,
  st: List<&2, Spec.Frame>,
  seg: Bool
) -> {
  Spec.Glob.read.go(
    l,
    Spec.Out{},
    Con{Spec.Frame{[], [], seg}, st},
    seg
  )
    == Spec.Glob.read.go(Con{Spec.SOpen{}, l}, Spec.Out{}, st, seg): Maybe<&2, Spec.Glob>
}:
  match l:
    case Nil{}:
      {==}
    case Con{y1, l2}:
      match y1:
        case Spec.SEsc{}:
          {==}
        case Spec.SAny{}:
          {==}
        case Spec.SStar{}:
          match l2:
            case Nil{}:
              {==}
            case Con{y6, l7}:
              match y6:
                case Spec.SEsc{}:
                  {==}
                case Spec.SAny{}:
                  {==}
                case Spec.SStar{}:
                  {==}
                case Spec.SSlash{}:
                  {==}
                case Spec.SOpen{}:
                  {==}
                case Spec.SComma{}:
                  {==}
                case Spec.SClose{}:
                  {==}
                case Spec.SLeft{}:
                  {==}
                case Spec.SRight{}:
                  {==}
                case Spec.SBang{}:
                  {==}
                case Spec.SDash{}:
                  {==}
                case Spec.SChar{ch19}:
                  {==}
        case Spec.SSlash{}:
          {==}
        case Spec.SOpen{}:
          {==}
        case Spec.SComma{}:
          {==}
        case Spec.SClose{}:
          {==}
        case Spec.SLeft{}:
          {==}
        case Spec.SRight{}:
          {==}
        case Spec.SBang{}:
          {==}
        case Spec.SDash{}:
          match l2:
            case Nil{}:
              {==}
            case Con{y28, l29}:
              match y28:
                case Spec.SEsc{}:
                  {==}
                case Spec.SAny{}:
                  {==}
                case Spec.SStar{}:
                  {==}
                case Spec.SSlash{}:
                  {==}
                case Spec.SOpen{}:
                  {==}
                case Spec.SComma{}:
                  {==}
                case Spec.SClose{}:
                  {==}
                case Spec.SLeft{}:
                  {==}
                case Spec.SRight{}:
                  {==}
                case Spec.SBang{}:
                  {==}
                case Spec.SDash{}:
                  {==}
                case Spec.SChar{ch41}:
                  {==}
        case Spec.SChar{ch42}:
          {==}

# `}` closes a frame into one Alt
def Step.close(
  l: List<&2, Spec.Sym>,
  a: List<&2, Spec.Glob>,
  s: List<&2, Spec.Glob>,
  b: Bool,
  f: Spec.Frame,
  r: List<&2, Spec.Frame>,
  seg: Bool
) -> {
  Spec.Glob.read.go(
    l,
    Spec.Out{},
    Spec.Frame.add(
      Con{f, r},
      Spec.Glob.of_alts(Con{Spec.Glob.of_seq(s, Spec.Eps{}), a}, Spec.Void{})
    ),
    False{}
  )
    == Spec.Glob.read.go(
      Con{Spec.SClose{}, l},
      Spec.Out{},
      Con{Spec.Frame{a, s, b}, Con{f, r}},
      seg
    ): Maybe<&2, Spec.Glob>
}:
  match l:
    case Nil{}:
      {==}
    case Con{y1, l2}:
      match y1:
        case Spec.SEsc{}:
          {==}
        case Spec.SAny{}:
          {==}
        case Spec.SStar{}:
          match l2:
            case Nil{}:
              {==}
            case Con{y6, l7}:
              match y6:
                case Spec.SEsc{}:
                  {==}
                case Spec.SAny{}:
                  {==}
                case Spec.SStar{}:
                  {==}
                case Spec.SSlash{}:
                  {==}
                case Spec.SOpen{}:
                  {==}
                case Spec.SComma{}:
                  {==}
                case Spec.SClose{}:
                  {==}
                case Spec.SLeft{}:
                  {==}
                case Spec.SRight{}:
                  {==}
                case Spec.SBang{}:
                  {==}
                case Spec.SDash{}:
                  {==}
                case Spec.SChar{ch19}:
                  {==}
        case Spec.SSlash{}:
          {==}
        case Spec.SOpen{}:
          {==}
        case Spec.SComma{}:
          {==}
        case Spec.SClose{}:
          {==}
        case Spec.SLeft{}:
          {==}
        case Spec.SRight{}:
          {==}
        case Spec.SBang{}:
          {==}
        case Spec.SDash{}:
          match l2:
            case Nil{}:
              {==}
            case Con{y28, l29}:
              match y28:
                case Spec.SEsc{}:
                  {==}
                case Spec.SAny{}:
                  {==}
                case Spec.SStar{}:
                  {==}
                case Spec.SSlash{}:
                  {==}
                case Spec.SOpen{}:
                  {==}
                case Spec.SComma{}:
                  {==}
                case Spec.SClose{}:
                  {==}
                case Spec.SLeft{}:
                  {==}
                case Spec.SRight{}:
                  {==}
                case Spec.SBang{}:
                  {==}
                case Spec.SDash{}:
                  {==}
                case Spec.SChar{ch41}:
                  {==}
        case Spec.SChar{ch42}:
          {==}

# `,` starts the next alternative
def Step.comma(
  l: List<&2, Spec.Sym>,
  a: List<&2, Spec.Glob>,
  s: List<&2, Spec.Glob>,
  b: Bool,
  f: Spec.Frame,
  r: List<&2, Spec.Frame>,
  seg: Bool
) -> {
  Spec.Glob.read.go(
    l,
    Spec.Out{},
    Con{Spec.Frame{Con{Spec.Glob.of_seq(s, Spec.Eps{}), a}, [], b}, Con{f, r}},
    b
  )
    == Spec.Glob.read.go(
      Con{Spec.SComma{}, l},
      Spec.Out{},
      Con{Spec.Frame{a, s, b}, Con{f, r}},
      seg
    ): Maybe<&2, Spec.Glob>
}:
  match l:
    case Nil{}:
      {==}
    case Con{y1, l2}:
      match y1:
        case Spec.SEsc{}:
          {==}
        case Spec.SAny{}:
          {==}
        case Spec.SStar{}:
          match l2:
            case Nil{}:
              {==}
            case Con{y6, l7}:
              match y6:
                case Spec.SEsc{}:
                  {==}
                case Spec.SAny{}:
                  {==}
                case Spec.SStar{}:
                  {==}
                case Spec.SSlash{}:
                  {==}
                case Spec.SOpen{}:
                  {==}
                case Spec.SComma{}:
                  {==}
                case Spec.SClose{}:
                  {==}
                case Spec.SLeft{}:
                  {==}
                case Spec.SRight{}:
                  {==}
                case Spec.SBang{}:
                  {==}
                case Spec.SDash{}:
                  {==}
                case Spec.SChar{ch19}:
                  {==}
        case Spec.SSlash{}:
          {==}
        case Spec.SOpen{}:
          {==}
        case Spec.SComma{}:
          {==}
        case Spec.SClose{}:
          {==}
        case Spec.SLeft{}:
          {==}
        case Spec.SRight{}:
          {==}
        case Spec.SBang{}:
          {==}
        case Spec.SDash{}:
          match l2:
            case Nil{}:
              {==}
            case Con{y28, l29}:
              match y28:
                case Spec.SEsc{}:
                  {==}
                case Spec.SAny{}:
                  {==}
                case Spec.SStar{}:
                  {==}
                case Spec.SSlash{}:
                  {==}
                case Spec.SOpen{}:
                  {==}
                case Spec.SComma{}:
                  {==}
                case Spec.SClose{}:
                  {==}
                case Spec.SLeft{}:
                  {==}
                case Spec.SRight{}:
                  {==}
                case Spec.SBang{}:
                  {==}
                case Spec.SDash{}:
                  {==}
                case Spec.SChar{ch41}:
                  {==}
        case Spec.SChar{ch42}:
          {==}

# `*` before `}` is Star
def Step.star(
  l: List<&2, Spec.Sym>,
  st: List<&2, Spec.Frame>,
  seg: Bool
) -> {
  Spec.Glob.read.go(
    Con{Spec.SClose{}, l},
    Spec.Out{},
    Spec.Frame.add(st, Spec.Star{}),
    False{}
  )
    == Spec.Glob.read.go(
      Con{Spec.SStar{}, Con{Spec.SClose{}, l}},
      Spec.Out{},
      st,
      seg
    ): Maybe<&2, Spec.Glob>
}:
  match l:
    case Nil{}:
      {==}
    case Con{y1, l2}:
      match y1:
        case Spec.SEsc{}:
          {==}
        case Spec.SAny{}:
          {==}
        case Spec.SStar{}:
          match l2:
            case Nil{}:
              {==}
            case Con{y6, l7}:
              match y6:
                case Spec.SEsc{}:
                  {==}
                case Spec.SAny{}:
                  {==}
                case Spec.SStar{}:
                  {==}
                case Spec.SSlash{}:
                  {==}
                case Spec.SOpen{}:
                  {==}
                case Spec.SComma{}:
                  {==}
                case Spec.SClose{}:
                  {==}
                case Spec.SLeft{}:
                  {==}
                case Spec.SRight{}:
                  {==}
                case Spec.SBang{}:
                  {==}
                case Spec.SDash{}:
                  {==}
                case Spec.SChar{ch19}:
                  {==}
        case Spec.SSlash{}:
          {==}
        case Spec.SOpen{}:
          {==}
        case Spec.SComma{}:
          {==}
        case Spec.SClose{}:
          {==}
        case Spec.SLeft{}:
          {==}
        case Spec.SRight{}:
          {==}
        case Spec.SBang{}:
          {==}
        case Spec.SDash{}:
          match l2:
            case Nil{}:
              {==}
            case Con{y28, l29}:
              match y28:
                case Spec.SEsc{}:
                  {==}
                case Spec.SAny{}:
                  {==}
                case Spec.SStar{}:
                  {==}
                case Spec.SSlash{}:
                  {==}
                case Spec.SOpen{}:
                  {==}
                case Spec.SComma{}:
                  {==}
                case Spec.SClose{}:
                  {==}
                case Spec.SLeft{}:
                  {==}
                case Spec.SRight{}:
                  {==}
                case Spec.SBang{}:
                  {==}
                case Spec.SDash{}:
                  {==}
                case Spec.SChar{ch41}:
                  {==}
        case Spec.SChar{ch42}:
          {==}

# s is `!`
def Sym.bang(s: Spec.Sym) -> Bool:
  match s:
    case Spec.SBang{}:
      True{}
    case _:
      False{}

# `[` before a symbol that is not `!` opens a class
def Step.left(
  y: Spec.Sym,
  l: List<&2, Spec.Sym>,
  st: List<&2, Spec.Frame>,
  seg: Bool
) -> {
  Sym.bang(y) == False{}: Bool
} -> {
  Spec.Glob.read.go(
    Con{y, l},
    Spec.In{False{}, []},
    st,
    seg
  )
    == Spec.Glob.read.go(Con{Spec.SLeft{}, Con{y, l}}, Spec.Out{}, st, seg): Maybe<&2, Spec.Glob>
}:
  match y:
    case Spec.SEsc{}:
      e => {==}
    case Spec.SAny{}:
      e => {==}
    case Spec.SStar{}:
      e => {==}
    case Spec.SSlash{}:
      e => {==}
    case Spec.SOpen{}:
      e => {==}
    case Spec.SComma{}:
      e => {==}
    case Spec.SClose{}:
      e => {==}
    case Spec.SLeft{}:
      e => {==}
    case Spec.SRight{}:
      e => {==}
    case Spec.SDash{}:
      match l:
        case Nil{}:
          e => {==}
        case Con{z, l2}:
          match z:
            case Spec.SEsc{}:
              e => {==}
            case Spec.SAny{}:
              e => {==}
            case Spec.SStar{}:
              e => {==}
            case Spec.SSlash{}:
              e => {==}
            case Spec.SOpen{}:
              e => {==}
            case Spec.SComma{}:
              e => {==}
            case Spec.SClose{}:
              e => {==}
            case Spec.SLeft{}:
              e => {==}
            case Spec.SRight{}:
              e => {==}
            case Spec.SBang{}:
              e => {==}
            case Spec.SDash{}:
              e => {==}
            case Spec.SChar{c}:
              e => {==}
    case Spec.SChar{c}:
      e => {==}
    case Spec.SBang{}:
      e => Empty.absurd(
        {
          Spec.Glob.read.go(
            Con{Spec.SBang{}, l},
            Spec.In{False{}, []},
            st,
            seg
          )
            == Spec.Glob.read.go(
              Con{Spec.SLeft{}, Con{Spec.SBang{}, l}},
              Spec.Out{},
              st,
              seg
            ): Maybe<&2, Spec.Glob>
        },
        Shared.Bool.true_ne_false(e)
      )

# `[` before `]` opens a class
def Step.left_right(
  l: List<&2, Spec.Sym>,
  st: List<&2, Spec.Frame>,
  seg: Bool
) -> {
  Spec.Glob.read.go(
    Con{Spec.SRight{}, l},
    Spec.In{False{}, []},
    st,
    seg
  )
    == Spec.Glob.read.go(
      Con{Spec.SLeft{}, Con{Spec.SRight{}, l}},
      Spec.Out{},
      st,
      seg
    ): Maybe<&2, Spec.Glob>
}:
  match l:
    case Nil{}:
      {==}
    case Con{y1, l2}:
      match y1:
        case Spec.SEsc{}:
          {==}
        case Spec.SAny{}:
          {==}
        case Spec.SStar{}:
          match l2:
            case Nil{}:
              {==}
            case Con{y6, l7}:
              match y6:
                case Spec.SEsc{}:
                  {==}
                case Spec.SAny{}:
                  {==}
                case Spec.SStar{}:
                  {==}
                case Spec.SSlash{}:
                  {==}
                case Spec.SOpen{}:
                  {==}
                case Spec.SComma{}:
                  {==}
                case Spec.SClose{}:
                  {==}
                case Spec.SLeft{}:
                  {==}
                case Spec.SRight{}:
                  {==}
                case Spec.SBang{}:
                  {==}
                case Spec.SDash{}:
                  {==}
                case Spec.SChar{ch19}:
                  {==}
        case Spec.SSlash{}:
          {==}
        case Spec.SOpen{}:
          {==}
        case Spec.SComma{}:
          {==}
        case Spec.SClose{}:
          {==}
        case Spec.SLeft{}:
          {==}
        case Spec.SRight{}:
          {==}
        case Spec.SBang{}:
          {==}
        case Spec.SDash{}:
          match l2:
            case Nil{}:
              {==}
            case Con{y28, l29}:
              match y28:
                case Spec.SEsc{}:
                  {==}
                case Spec.SAny{}:
                  {==}
                case Spec.SStar{}:
                  {==}
                case Spec.SSlash{}:
                  {==}
                case Spec.SOpen{}:
                  {==}
                case Spec.SComma{}:
                  {==}
                case Spec.SClose{}:
                  {==}
                case Spec.SLeft{}:
                  {==}
                case Spec.SRight{}:
                  {==}
                case Spec.SBang{}:
                  {==}
                case Spec.SDash{}:
                  {==}
                case Spec.SChar{ch41}:
                  {==}
        case Spec.SChar{ch42}:
          {==}

# `[!` opens a negated class
def Step.left_bang(
  l: List<&2, Spec.Sym>,
  st: List<&2, Spec.Frame>,
  seg: Bool
) -> {
  Spec.Glob.read.go(
    l,
    Spec.In{True{}, []},
    st,
    seg
  )
    == Spec.Glob.read.go(
      Con{Spec.SLeft{}, Con{Spec.SBang{}, l}},
      Spec.Out{},
      st,
      seg
    ): Maybe<&2, Spec.Glob>
}:
  match l:
    case Nil{}:
      {==}
    case Con{y1, l2}:
      match y1:
        case Spec.SEsc{}:
          {==}
        case Spec.SAny{}:
          {==}
        case Spec.SStar{}:
          match l2:
            case Nil{}:
              {==}
            case Con{y6, l7}:
              match y6:
                case Spec.SEsc{}:
                  {==}
                case Spec.SAny{}:
                  {==}
                case Spec.SStar{}:
                  {==}
                case Spec.SSlash{}:
                  {==}
                case Spec.SOpen{}:
                  {==}
                case Spec.SComma{}:
                  {==}
                case Spec.SClose{}:
                  {==}
                case Spec.SLeft{}:
                  {==}
                case Spec.SRight{}:
                  {==}
                case Spec.SBang{}:
                  {==}
                case Spec.SDash{}:
                  {==}
                case Spec.SChar{ch19}:
                  {==}
        case Spec.SSlash{}:
          {==}
        case Spec.SOpen{}:
          {==}
        case Spec.SComma{}:
          {==}
        case Spec.SClose{}:
          {==}
        case Spec.SLeft{}:
          {==}
        case Spec.SRight{}:
          {==}
        case Spec.SBang{}:
          {==}
        case Spec.SDash{}:
          match l2:
            case Nil{}:
              {==}
            case Con{y28, l29}:
              match y28:
                case Spec.SEsc{}:
                  {==}
                case Spec.SAny{}:
                  {==}
                case Spec.SStar{}:
                  {==}
                case Spec.SSlash{}:
                  {==}
                case Spec.SOpen{}:
                  {==}
                case Spec.SComma{}:
                  {==}
                case Spec.SClose{}:
                  {==}
                case Spec.SLeft{}:
                  {==}
                case Spec.SRight{}:
                  {==}
                case Spec.SBang{}:
                  {==}
                case Spec.SDash{}:
                  {==}
                case Spec.SChar{ch41}:
                  {==}
        case Spec.SChar{ch42}:
          {==}

# s is none of `\\`, `]` and `!`: at the start or an end of a span of a class
# it stands for its own character
def Sym.plain(s: Spec.Sym) -> Bool:
  match s:
    case Spec.SEsc{}:
      False{}
    case Spec.SRight{}:
      False{}
    case Spec.SBang{}:
      False{}
    case _:
      True{}

# a span `x-y` in a class, of two plain symbols
def Step.range(
  x: Spec.Sym,
  y: Spec.Sym,
  l: List<&2, Spec.Sym>,
  n: Bool,
  cs: List<&2, Spans.Span>,
  st: List<&2, Spec.Frame>,
  seg: Bool
) -> {
  Sym.plain(x) == True{}: Bool
} -> {
  Sym.plain(y) == True{}: Bool
} -> {
  Spec.Glob.read.range(
    Spans.Span.of(Spec.Sym.char(x), Spec.Sym.char(y)),
    s => Spec.Glob.read.go(l, Spec.In{n, Con{s, cs}}, st, seg)
  )
    == Spec.Glob.read.go(
      Con{x, Con{Spec.SDash{}, Con{y, l}}},
      Spec.In{n, cs},
      st,
      seg
    ): Maybe<&2, Spec.Glob>
}:
  match x:
    case Spec.SEsc{}:
      y = y
      l = l
      n = n
      cs = cs
      st = st
      seg = seg
      x => Empty.absurd(
        @_: {
          Sym.plain(y) == True{}: Bool
        } -> {
          Spec.Glob.read.range(
            Spans.Span.of(Spec.Sym.char(Spec.SEsc{}), Spec.Sym.char(y)),
            s => Spec.Glob.read.go(l, Spec.In{n, s <> cs}, st, seg)
          )
            == Spec.Glob.read.go(
              Spec.SEsc{} <> Spec.SDash{} <> y <> l,
              Spec.In{n, cs},
              st,
              seg
            ): Maybe<&2, Spec.Glob>
        },
        {(%x: {\{False: Unit; \{True: Empty; \{}}}: Bool -> Type}(_); Unit{}): Empty}
      )
    case Spec.SAny{}:
      match y:
        case Spec.SEsc{}:
          l = l
          n = n
          cs = cs
          st = st
          seg = seg
          x => x1 => Empty.absurd(
            {
              Spec.Glob.read.range(
                Spans.Span.of(Spec.Sym.char(Spec.SAny{}), Spec.Sym.char(Spec.SEsc{})),
                s => Spec.Glob.read.go(l, Spec.In{n, s <> cs}, st, seg)
              )
                == Spec.Glob.read.go(
                  Spec.SAny{} <> Spec.SDash{} <> Spec.SEsc{} <> l,
                  Spec.In{n, cs},
                  st,
                  seg
                ): Maybe<&2, Spec.Glob>
            },
            {(%x1: {\{False: Unit; \{True: Empty; \{}}}: Bool -> Type}(_); Unit{}): Empty}
          )
        case Spec.SAny{}:
          x => x1 => {==}
        case Spec.SStar{}:
          x => x1 => {==}
        case Spec.SSlash{}:
          x => x1 => {==}
        case Spec.SOpen{}:
          x => x1 => {==}
        case Spec.SComma{}:
          x => x1 => {==}
        case Spec.SClose{}:
          x => x1 => {==}
        case Spec.SLeft{}:
          x => x1 => {==}
        case Spec.SRight{}:
          l = l
          n = n
          cs = cs
          st = st
          seg = seg
          x => x1 => Empty.absurd(
            {
              Spec.Glob.read.range(
                Spans.Span.of(Spec.Sym.char(Spec.SAny{}), Spec.Sym.char(Spec.SRight{})),
                s => Spec.Glob.read.go(l, Spec.In{n, s <> cs}, st, seg)
              )
                == Spec.Glob.read.go(
                  Spec.SAny{} <> Spec.SDash{} <> Spec.SRight{} <> l,
                  Spec.In{n, cs},
                  st,
                  seg
                ): Maybe<&2, Spec.Glob>
            },
            {(%x1: {\{False: Unit; \{True: Empty; \{}}}: Bool -> Type}(_); Unit{}): Empty}
          )
        case Spec.SBang{}:
          x => x1 => {==}
        case Spec.SDash{}:
          x => x1 => {==}
        case Spec.SChar{c}:
          x => x1 => {==}
    case Spec.SStar{}:
      match y:
        case Spec.SEsc{}:
          l = l
          n = n
          cs = cs
          st = st
          seg = seg
          x => x1 => Empty.absurd(
            {
              Spec.Glob.read.range(
                Spans.Span.of(Spec.Sym.char(Spec.SStar{}), Spec.Sym.char(Spec.SEsc{})),
                s => Spec.Glob.read.go(l, Spec.In{n, s <> cs}, st, seg)
              )
                == Spec.Glob.read.go(
                  Spec.SStar{} <> Spec.SDash{} <> Spec.SEsc{} <> l,
                  Spec.In{n, cs},
                  st,
                  seg
                ): Maybe<&2, Spec.Glob>
            },
            {(%x1: {\{False: Unit; \{True: Empty; \{}}}: Bool -> Type}(_); Unit{}): Empty}
          )
        case Spec.SAny{}:
          x => x1 => {==}
        case Spec.SStar{}:
          x => x1 => {==}
        case Spec.SSlash{}:
          x => x1 => {==}
        case Spec.SOpen{}:
          x => x1 => {==}
        case Spec.SComma{}:
          x => x1 => {==}
        case Spec.SClose{}:
          x => x1 => {==}
        case Spec.SLeft{}:
          x => x1 => {==}
        case Spec.SRight{}:
          l = l
          n = n
          cs = cs
          st = st
          seg = seg
          x => x1 => Empty.absurd(
            {
              Spec.Glob.read.range(
                Spans.Span.of(Spec.Sym.char(Spec.SStar{}), Spec.Sym.char(Spec.SRight{})),
                s => Spec.Glob.read.go(l, Spec.In{n, s <> cs}, st, seg)
              )
                == Spec.Glob.read.go(
                  Spec.SStar{} <> Spec.SDash{} <> Spec.SRight{} <> l,
                  Spec.In{n, cs},
                  st,
                  seg
                ): Maybe<&2, Spec.Glob>
            },
            {(%x1: {\{False: Unit; \{True: Empty; \{}}}: Bool -> Type}(_); Unit{}): Empty}
          )
        case Spec.SBang{}:
          x => x1 => {==}
        case Spec.SDash{}:
          x => x1 => {==}
        case Spec.SChar{c}:
          x => x1 => {==}
    case Spec.SSlash{}:
      match y:
        case Spec.SEsc{}:
          l = l
          n = n
          cs = cs
          st = st
          seg = seg
          x => x1 => Empty.absurd(
            {
              Spec.Glob.read.range(
                Spans.Span.of(Spec.Sym.char(Spec.SSlash{}), Spec.Sym.char(Spec.SEsc{})),
                s => Spec.Glob.read.go(l, Spec.In{n, s <> cs}, st, seg)
              )
                == Spec.Glob.read.go(
                  Spec.SSlash{} <> Spec.SDash{} <> Spec.SEsc{} <> l,
                  Spec.In{n, cs},
                  st,
                  seg
                ): Maybe<&2, Spec.Glob>
            },
            {(%x1: {\{False: Unit; \{True: Empty; \{}}}: Bool -> Type}(_); Unit{}): Empty}
          )
        case Spec.SAny{}:
          x => x1 => {==}
        case Spec.SStar{}:
          x => x1 => {==}
        case Spec.SSlash{}:
          x => x1 => {==}
        case Spec.SOpen{}:
          x => x1 => {==}
        case Spec.SComma{}:
          x => x1 => {==}
        case Spec.SClose{}:
          x => x1 => {==}
        case Spec.SLeft{}:
          x => x1 => {==}
        case Spec.SRight{}:
          l = l
          n = n
          cs = cs
          st = st
          seg = seg
          x => x1 => Empty.absurd(
            {
              Spec.Glob.read.range(
                Spans.Span.of(Spec.Sym.char(Spec.SSlash{}), Spec.Sym.char(Spec.SRight{})),
                s => Spec.Glob.read.go(l, Spec.In{n, s <> cs}, st, seg)
              )
                == Spec.Glob.read.go(
                  Spec.SSlash{} <> Spec.SDash{} <> Spec.SRight{} <> l,
                  Spec.In{n, cs},
                  st,
                  seg
                ): Maybe<&2, Spec.Glob>
            },
            {(%x1: {\{False: Unit; \{True: Empty; \{}}}: Bool -> Type}(_); Unit{}): Empty}
          )
        case Spec.SBang{}:
          x => x1 => {==}
        case Spec.SDash{}:
          x => x1 => {==}
        case Spec.SChar{c}:
          x => x1 => {==}
    case Spec.SOpen{}:
      match y:
        case Spec.SEsc{}:
          x => x1 => {==}
        case Spec.SAny{}:
          x => x1 => {==}
        case Spec.SStar{}:
          x => x1 => {==}
        case Spec.SSlash{}:
          x => x1 => {==}
        case Spec.SOpen{}:
          x => x1 => {==}
        case Spec.SComma{}:
          x => x1 => {==}
        case Spec.SClose{}:
          x => x1 => {==}
        case Spec.SLeft{}:
          x => x1 => {==}
        case Spec.SRight{}:
          x => x1 => {==}
        case Spec.SBang{}:
          x => x1 => {==}
        case Spec.SDash{}:
          x => x1 => {==}
        case Spec.SChar{c}:
          x => x1 => {==}
    case Spec.SComma{}:
      match y:
        case Spec.SEsc{}:
          x => x1 => Empty.absurd(
            {
              Spec.Glob.read.range(
                Spans.Span.of(Spec.Sym.char(Spec.SComma{}), Spec.Sym.char(Spec.SEsc{})),
                s => Spec.Glob.read.go(l, Spec.In{n, s <> cs}, st, seg)
              )
                == Spec.Glob.read.go(
                  Spec.SComma{} <> Spec.SDash{} <> Spec.SEsc{} <> l,
                  Spec.In{n, cs},
                  st,
                  seg
                ): Maybe<&2, Spec.Glob>
            },
            {(%x1: {\{False: Unit; \{True: Empty; \{}}}: Bool -> Type}(_); Unit{}): Empty}
          )
        case Spec.SAny{}:
          x => x1 => {==}
        case Spec.SStar{}:
          x => x1 => {==}
        case Spec.SSlash{}:
          x => x1 => {==}
        case Spec.SOpen{}:
          x => x1 => {==}
        case Spec.SComma{}:
          x => x1 => {==}
        case Spec.SClose{}:
          x => x1 => {==}
        case Spec.SLeft{}:
          x => x1 => {==}
        case Spec.SRight{}:
          x => x1 => Empty.absurd(
            {
              Spec.Glob.read.range(
                Spans.Span.of(Spec.Sym.char(Spec.SComma{}), Spec.Sym.char(Spec.SRight{})),
                s => Spec.Glob.read.go(l, Spec.In{n, s <> cs}, st, seg)
              )
                == Spec.Glob.read.go(
                  Spec.SComma{} <> Spec.SDash{} <> Spec.SRight{} <> l,
                  Spec.In{n, cs},
                  st,
                  seg
                ): Maybe<&2, Spec.Glob>
            },
            {(%x1: {\{False: Unit; \{True: Empty; \{}}}: Bool -> Type}(_); Unit{}): Empty}
          )
        case Spec.SBang{}:
          x => x1 => {==}
        case Spec.SDash{}:
          x => x1 => {==}
        case Spec.SChar{c}:
          x => x1 => {==}
    case Spec.SClose{}:
      match y:
        case Spec.SEsc{}:
          x => x1 => {==}
        case Spec.SAny{}:
          x => x1 => {==}
        case Spec.SStar{}:
          x => x1 => {==}
        case Spec.SSlash{}:
          x => x1 => {==}
        case Spec.SOpen{}:
          x => x1 => {==}
        case Spec.SComma{}:
          x => x1 => {==}
        case Spec.SClose{}:
          x => x1 => {==}
        case Spec.SLeft{}:
          x => x1 => {==}
        case Spec.SRight{}:
          x => x1 => {==}
        case Spec.SBang{}:
          x => x1 => {==}
        case Spec.SDash{}:
          x => x1 => {==}
        case Spec.SChar{c}:
          x => x1 => {==}
    case Spec.SLeft{}:
      match y:
        case Spec.SEsc{}:
          x => x1 => Empty.absurd(
            {
              Spec.Glob.read.range(
                Spans.Span.of(Spec.Sym.char(Spec.SLeft{}), Spec.Sym.char(Spec.SEsc{})),
                s => Spec.Glob.read.go(l, Spec.In{n, s <> cs}, st, seg)
              )
                == Spec.Glob.read.go(
                  Spec.SLeft{} <> Spec.SDash{} <> Spec.SEsc{} <> l,
                  Spec.In{n, cs},
                  st,
                  seg
                ): Maybe<&2, Spec.Glob>
            },
            {(%x1: {\{False: Unit; \{True: Empty; \{}}}: Bool -> Type}(_); Unit{}): Empty}
          )
        case Spec.SAny{}:
          x => x1 => {==}
        case Spec.SStar{}:
          x => x1 => {==}
        case Spec.SSlash{}:
          x => x1 => {==}
        case Spec.SOpen{}:
          x => x1 => {==}
        case Spec.SComma{}:
          x => x1 => {==}
        case Spec.SClose{}:
          x => x1 => {==}
        case Spec.SLeft{}:
          x => x1 => {==}
        case Spec.SRight{}:
          x => x1 => Empty.absurd(
            {
              Spec.Glob.read.range(
                Spans.Span.of(Spec.Sym.char(Spec.SLeft{}), Spec.Sym.char(Spec.SRight{})),
                s => Spec.Glob.read.go(l, Spec.In{n, s <> cs}, st, seg)
              )
                == Spec.Glob.read.go(
                  Spec.SLeft{} <> Spec.SDash{} <> Spec.SRight{} <> l,
                  Spec.In{n, cs},
                  st,
                  seg
                ): Maybe<&2, Spec.Glob>
            },
            {(%x1: {\{False: Unit; \{True: Empty; \{}}}: Bool -> Type}(_); Unit{}): Empty}
          )
        case Spec.SBang{}:
          x => x1 => {==}
        case Spec.SDash{}:
          x => x1 => {==}
        case Spec.SChar{c}:
          x => x1 => {==}
    case Spec.SRight{}:
      x => Empty.absurd(
        @_: {
          Sym.plain(y) == True{}: Bool
        } -> {
          Spec.Glob.read.range(
            Spans.Span.of(Spec.Sym.char(Spec.SRight{}), Spec.Sym.char(y)),
            s => Spec.Glob.read.go(l, Spec.In{n, s <> cs}, st, seg)
          )
            == Spec.Glob.read.go(
              Spec.SRight{} <> Spec.SDash{} <> y <> l,
              Spec.In{n, cs},
              st,
              seg
            ): Maybe<&2, Spec.Glob>
        },
        {(%x: {\{False: Unit; \{True: Empty; \{}}}: Bool -> Type}(_); Unit{}): Empty}
      )
    case Spec.SBang{}:
      match y:
        case Spec.SEsc{}:
          x => x1 => Empty.absurd(
            {
              Spec.Glob.read.range(
                Spans.Span.of(Spec.Sym.char(Spec.SBang{}), Spec.Sym.char(Spec.SEsc{})),
                s => Spec.Glob.read.go(l, Spec.In{n, s <> cs}, st, seg)
              )
                == Spec.Glob.read.go(
                  Spec.SBang{} <> Spec.SDash{} <> Spec.SEsc{} <> l,
                  Spec.In{n, cs},
                  st,
                  seg
                ): Maybe<&2, Spec.Glob>
            },
            {(%x1: {\{False: Unit; \{True: Empty; \{}}}: Bool -> Type}(_); Unit{}): Empty}
          )
        case Spec.SAny{}:
          x => x1 => {==}
        case Spec.SStar{}:
          x => x1 => {==}
        case Spec.SSlash{}:
          x => x1 => {==}
        case Spec.SOpen{}:
          x => x1 => {==}
        case Spec.SComma{}:
          x => x1 => {==}
        case Spec.SClose{}:
          x => x1 => {==}
        case Spec.SLeft{}:
          x => x1 => {==}
        case Spec.SRight{}:
          x => x1 => Empty.absurd(
            {
              Spec.Glob.read.range(
                Spans.Span.of(Spec.Sym.char(Spec.SBang{}), Spec.Sym.char(Spec.SRight{})),
                s => Spec.Glob.read.go(l, Spec.In{n, s <> cs}, st, seg)
              )
                == Spec.Glob.read.go(
                  Spec.SBang{} <> Spec.SDash{} <> Spec.SRight{} <> l,
                  Spec.In{n, cs},
                  st,
                  seg
                ): Maybe<&2, Spec.Glob>
            },
            {(%x1: {\{False: Unit; \{True: Empty; \{}}}: Bool -> Type}(_); Unit{}): Empty}
          )
        case Spec.SBang{}:
          x => x1 => {==}
        case Spec.SDash{}:
          x => x1 => {==}
        case Spec.SChar{c}:
          x => x1 => {==}
    case Spec.SDash{}:
      match y:
        case Spec.SEsc{}:
          x => x1 => Empty.absurd(
            {
              Spec.Glob.read.range(
                Spans.Span.of(Spec.Sym.char(Spec.SDash{}), Spec.Sym.char(Spec.SEsc{})),
                s => Spec.Glob.read.go(l, Spec.In{n, s <> cs}, st, seg)
              )
                == Spec.Glob.read.go(
                  Spec.SDash{} <> Spec.SDash{} <> Spec.SEsc{} <> l,
                  Spec.In{n, cs},
                  st,
                  seg
                ): Maybe<&2, Spec.Glob>
            },
            {(%x1: {\{False: Unit; \{True: Empty; \{}}}: Bool -> Type}(_); Unit{}): Empty}
          )
        case Spec.SAny{}:
          x => x1 => {==}
        case Spec.SStar{}:
          x => x1 => {==}
        case Spec.SSlash{}:
          x => x1 => {==}
        case Spec.SOpen{}:
          x => x1 => {==}
        case Spec.SComma{}:
          x => x1 => {==}
        case Spec.SClose{}:
          x => x1 => {==}
        case Spec.SLeft{}:
          x => x1 => {==}
        case Spec.SRight{}:
          x => x1 => Empty.absurd(
            {
              Spec.Glob.read.range(
                Spans.Span.of(Spec.Sym.char(Spec.SDash{}), Spec.Sym.char(Spec.SRight{})),
                s => Spec.Glob.read.go(l, Spec.In{n, s <> cs}, st, seg)
              )
                == Spec.Glob.read.go(
                  Spec.SDash{} <> Spec.SDash{} <> Spec.SRight{} <> l,
                  Spec.In{n, cs},
                  st,
                  seg
                ): Maybe<&2, Spec.Glob>
            },
            {(%x1: {\{False: Unit; \{True: Empty; \{}}}: Bool -> Type}(_); Unit{}): Empty}
          )
        case Spec.SBang{}:
          x => x1 => {==}
        case Spec.SDash{}:
          x => x1 => {==}
        case Spec.SChar{c}:
          x => x1 => {==}
    case Spec.SChar{c}:
      match y:
        case Spec.SEsc{}:
          x => x1 => Empty.absurd(
            {
              Spec.Glob.read.range(
                Spans.Span.of(Spec.Sym.char(Spec.SChar{c}), Spec.Sym.char(Spec.SEsc{})),
                s => Spec.Glob.read.go(l, Spec.In{n, s <> cs}, st, seg)
              )
                == Spec.Glob.read.go(
                  Spec.SChar{c} <> Spec.SDash{} <> Spec.SEsc{} <> l,
                  Spec.In{n, cs},
                  st,
                  seg
                ): Maybe<&2, Spec.Glob>
            },
            {(%x1: {\{False: Unit; \{True: Empty; \{}}}: Bool -> Type}(_); Unit{}): Empty}
          )
        case Spec.SAny{}:
          x => x1 => {==}
        case Spec.SStar{}:
          x => x1 => {==}
        case Spec.SSlash{}:
          x => x1 => {==}
        case Spec.SOpen{}:
          x => x1 => {==}
        case Spec.SComma{}:
          x => x1 => {==}
        case Spec.SClose{}:
          x => x1 => {==}
        case Spec.SLeft{}:
          x => x1 => {==}
        case Spec.SRight{}:
          x => x1 => Empty.absurd(
            {
              Spec.Glob.read.range(
                Spans.Span.of(Spec.Sym.char(Spec.SChar{c}), Spec.Sym.char(Spec.SRight{})),
                s => Spec.Glob.read.go(l, Spec.In{n, s <> cs}, st, seg)
              )
                == Spec.Glob.read.go(
                  Spec.SChar{c} <> Spec.SDash{} <> Spec.SRight{} <> l,
                  Spec.In{n, cs},
                  st,
                  seg
                ): Maybe<&2, Spec.Glob>
            },
            {(%x1: {\{False: Unit; \{True: Empty; \{}}}: Bool -> Type}(_); Unit{}): Empty}
          )
        case Spec.SBang{}:
          x => x1 => {==}
        case Spec.SDash{}:
          x => x1 => {==}
        case Spec.SChar{c1}:
          x => x1 => {==}

# an escaped symbol in a class adds its character
def Step.esc_in(
  y: Spec.Sym,
  l: List<&2, Spec.Sym>,
  n: Bool,
  cs: List<&2, Spans.Span>,
  st: List<&2, Spec.Frame>,
  seg: Bool
) -> {
  Spec.Glob.read.go(
    l,
    Spec.In{n, Con{Spans.Span{Spec.Sym.char(y), Spec.Sym.char(y)}, cs}},
    st,
    seg
  )
    == Spec.Glob.read.go(Con{Spec.SEsc{}, Con{y, l}}, Spec.In{n, cs}, st, seg): Maybe<&2, Spec.Glob>
}:
  match y:
    case Spec.SEsc{}:
      {==}
    case Spec.SAny{}:
      {==}
    case Spec.SStar{}:
      match l:
        case Nil{}:
          {==}
        case Con{y4, l5}:
          match y4:
            case Spec.SEsc{}:
              {==}
            case Spec.SAny{}:
              {==}
            case Spec.SStar{}:
              {==}
            case Spec.SSlash{}:
              {==}
            case Spec.SOpen{}:
              {==}
            case Spec.SComma{}:
              {==}
            case Spec.SClose{}:
              {==}
            case Spec.SLeft{}:
              {==}
            case Spec.SRight{}:
              {==}
            case Spec.SBang{}:
              {==}
            case Spec.SDash{}:
              {==}
            case Spec.SChar{ch17}:
              {==}
    case Spec.SSlash{}:
      {==}
    case Spec.SOpen{}:
      {==}
    case Spec.SComma{}:
      {==}
    case Spec.SClose{}:
      {==}
    case Spec.SLeft{}:
      {==}
    case Spec.SRight{}:
      {==}
    case Spec.SBang{}:
      {==}
    case Spec.SDash{}:
      match l:
        case Nil{}:
          {==}
        case Con{y26, l27}:
          match y26:
            case Spec.SEsc{}:
              {==}
            case Spec.SAny{}:
              {==}
            case Spec.SStar{}:
              {==}
            case Spec.SSlash{}:
              {==}
            case Spec.SOpen{}:
              {==}
            case Spec.SComma{}:
              {==}
            case Spec.SClose{}:
              {==}
            case Spec.SLeft{}:
              {==}
            case Spec.SRight{}:
              {==}
            case Spec.SBang{}:
              {==}
            case Spec.SDash{}:
              {==}
            case Spec.SChar{ch39}:
              {==}
    case Spec.SChar{ch40}:
      {==}

# `]` closes a class
def Step.right(
  l: List<&2, Spec.Sym>,
  n: Bool,
  cs: List<&2, Spans.Span>,
  st: List<&2, Spec.Frame>,
  seg: Bool
) -> {
  Spec.Glob.read.go(
    l,
    Spec.Out{},
    Spec.Frame.add(st, Spec.Class{n, cs}),
    False{}
  )
    == Spec.Glob.read.go(Con{Spec.SRight{}, l}, Spec.In{n, cs}, st, seg): Maybe<&2, Spec.Glob>
}:
  match l:
    case Nil{}:
      {==}
    case Con{y1, l2}:
      match y1:
        case Spec.SEsc{}:
          {==}
        case Spec.SAny{}:
          {==}
        case Spec.SStar{}:
          match l2:
            case Nil{}:
              {==}
            case Con{y6, l7}:
              match y6:
                case Spec.SEsc{}:
                  {==}
                case Spec.SAny{}:
                  {==}
                case Spec.SStar{}:
                  {==}
                case Spec.SSlash{}:
                  {==}
                case Spec.SOpen{}:
                  {==}
                case Spec.SComma{}:
                  {==}
                case Spec.SClose{}:
                  {==}
                case Spec.SLeft{}:
                  {==}
                case Spec.SRight{}:
                  {==}
                case Spec.SBang{}:
                  {==}
                case Spec.SDash{}:
                  {==}
                case Spec.SChar{ch19}:
                  {==}
        case Spec.SSlash{}:
          {==}
        case Spec.SOpen{}:
          {==}
        case Spec.SComma{}:
          {==}
        case Spec.SClose{}:
          {==}
        case Spec.SLeft{}:
          {==}
        case Spec.SRight{}:
          {==}
        case Spec.SBang{}:
          {==}
        case Spec.SDash{}:
          match l2:
            case Nil{}:
              {==}
            case Con{y28, l29}:
              match y28:
                case Spec.SEsc{}:
                  {==}
                case Spec.SAny{}:
                  {==}
                case Spec.SStar{}:
                  {==}
                case Spec.SSlash{}:
                  {==}
                case Spec.SOpen{}:
                  {==}
                case Spec.SComma{}:
                  {==}
                case Spec.SClose{}:
                  {==}
                case Spec.SLeft{}:
                  {==}
                case Spec.SRight{}:
                  {==}
                case Spec.SBang{}:
                  {==}
                case Spec.SDash{}:
                  {==}
                case Spec.SChar{ch41}:
                  {==}
        case Spec.SChar{ch42}:
          {==}

# `/` is a Lit that starts a segment
def Step.slash(
  l: List<&2, Spec.Sym>,
  st: List<&2, Spec.Frame>,
  seg: Bool
) -> {
  Spec.Glob.read.go(
    l,
    Spec.Out{},
    Spec.Frame.add(st, Spec.Lit{Chr{47}}),
    True{}
  )
    == Spec.Glob.read.go(Con{Spec.SSlash{}, l}, Spec.Out{}, st, seg): Maybe<&2, Spec.Glob>
}:
  match l:
    case Nil{}:
      {==}
    case Con{y1, l2}:
      match y1:
        case Spec.SEsc{}:
          {==}
        case Spec.SAny{}:
          {==}
        case Spec.SStar{}:
          match l2:
            case Nil{}:
              {==}
            case Con{y6, l7}:
              match y6:
                case Spec.SEsc{}:
                  {==}
                case Spec.SAny{}:
                  {==}
                case Spec.SStar{}:
                  {==}
                case Spec.SSlash{}:
                  {==}
                case Spec.SOpen{}:
                  {==}
                case Spec.SComma{}:
                  {==}
                case Spec.SClose{}:
                  {==}
                case Spec.SLeft{}:
                  {==}
                case Spec.SRight{}:
                  {==}
                case Spec.SBang{}:
                  {==}
                case Spec.SDash{}:
                  {==}
                case Spec.SChar{ch19}:
                  {==}
        case Spec.SSlash{}:
          {==}
        case Spec.SOpen{}:
          {==}
        case Spec.SComma{}:
          {==}
        case Spec.SClose{}:
          {==}
        case Spec.SLeft{}:
          {==}
        case Spec.SRight{}:
          {==}
        case Spec.SBang{}:
          {==}
        case Spec.SDash{}:
          match l2:
            case Nil{}:
              {==}
            case Con{y28, l29}:
              match y28:
                case Spec.SEsc{}:
                  {==}
                case Spec.SAny{}:
                  {==}
                case Spec.SStar{}:
                  {==}
                case Spec.SSlash{}:
                  {==}
                case Spec.SOpen{}:
                  {==}
                case Spec.SComma{}:
                  {==}
                case Spec.SClose{}:
                  {==}
                case Spec.SLeft{}:
                  {==}
                case Spec.SRight{}:
                  {==}
                case Spec.SBang{}:
                  {==}
                case Spec.SDash{}:
                  {==}
                case Spec.SChar{ch41}:
                  {==}
        case Spec.SChar{ch42}:
          {==}

# the text of Deep is one atom
def Step.deep(
  l: List<&2, Spec.Sym>,
  a: List<&2, Spec.Glob>,
  s: List<&2, Spec.Glob>,
  b: Bool,
  r: List<&2, Spec.Frame>,
  seg: Bool
) -> {
  Spec.Glob.read.go(
    l,
    Spec.Out{},
    Con{Spec.Frame{a, Con{Show.deep(), s}, b}, r},
    False{}
  )
    == Spec.Glob.read.go(
      Con{
        Spec.SOpen{},
        Con{
          Spec.SStar{},
          Con{
            Spec.SOpen{},
            Con{
              Spec.SComma{},
              Con{
                Spec.SSlash{},
                Con{Spec.SStar{}, Con{Spec.SStar{}, Con{Spec.SClose{}, Con{Spec.SClose{}, l}}}}
              }
            }
          }
        }
      },
      Spec.Out{},
      Con{Spec.Frame{a, s, b}, r},
      seg
    ): Maybe<&2, Spec.Glob>
}:
  match l:
    case Nil{}:
      {==}
    case Con{y1, l2}:
      match y1:
        case Spec.SEsc{}:
          {==}
        case Spec.SAny{}:
          {==}
        case Spec.SStar{}:
          match l2:
            case Nil{}:
              {==}
            case Con{y6, l7}:
              match y6:
                case Spec.SEsc{}:
                  {==}
                case Spec.SAny{}:
                  {==}
                case Spec.SStar{}:
                  {==}
                case Spec.SSlash{}:
                  {==}
                case Spec.SOpen{}:
                  {==}
                case Spec.SComma{}:
                  {==}
                case Spec.SClose{}:
                  {==}
                case Spec.SLeft{}:
                  {==}
                case Spec.SRight{}:
                  {==}
                case Spec.SBang{}:
                  {==}
                case Spec.SDash{}:
                  {==}
                case Spec.SChar{ch19}:
                  {==}
        case Spec.SSlash{}:
          {==}
        case Spec.SOpen{}:
          {==}
        case Spec.SComma{}:
          {==}
        case Spec.SClose{}:
          {==}
        case Spec.SLeft{}:
          {==}
        case Spec.SRight{}:
          {==}
        case Spec.SBang{}:
          {==}
        case Spec.SDash{}:
          match l2:
            case Nil{}:
              {==}
            case Con{y28, l29}:
              match y28:
                case Spec.SEsc{}:
                  {==}
                case Spec.SAny{}:
                  {==}
                case Spec.SStar{}:
                  {==}
                case Spec.SSlash{}:
                  {==}
                case Spec.SOpen{}:
                  {==}
                case Spec.SComma{}:
                  {==}
                case Spec.SClose{}:
                  {==}
                case Spec.SLeft{}:
                  {==}
                case Spec.SRight{}:
                  {==}
                case Spec.SBang{}:
                  {==}
                case Spec.SDash{}:
                  {==}
                case Spec.SChar{ch41}:
                  {==}
        case Spec.SChar{ch42}:
          {==}

# Parsing shown text
# ------------------

# the text of s reads back as s: s is empty, or one character, or its ends are
# plain symbols
def Span.fine(s: Spans.Span) -> Bool:
  match s:
    case Spans.Span{Chr{+lo}, Chr{+hi}}:
      List.any.if(
        u => List.any.if(
          u2 => List.all.if(u3 => Sym.plain(Spec.Sym.of(Chr{hi})), Sym.plain(Spec.Sym.of(Chr{lo}))),
          U32.is_eq(lo, hi)
        ),
        U32.is_lt(hi, lo)
      )

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- a false positive, as the rule notes: the other use is an erased argument (of Equal.sym or a motive)
# Span.parse once it is known whether the span is empty (gap) and whether it is
# one character (one)
def Span.parse.at(
  +lo: U32,
  +hi: U32,
  gap: Bool,
  eg: {U32.is_lt(hi, lo) == gap: Bool},
  one: Bool,
  eo: {U32.is_eq(lo, hi) == one: Bool},
  rest: String,
  n: Bool,
  acc: List<&2, Spans.Span>,
  st: List<&2, Spec.Frame>,
  seg: Bool
) -> {
  List.any.if(
    u => List.any.if(
      u2 => List.all.if(u3 => Sym.plain(Spec.Sym.of(Chr{hi})), Sym.plain(Spec.Sym.of(Chr{lo}))),
      one
    ),
    gap
  )
    == True{}: Bool
} -> {
  Spec.Glob.read.go(
    Spec.Sym.list(rest),
    Spec.In{n, Span.keep.at(gap, Spans.Span{Chr{lo}, Chr{hi}}, acc)},
    st,
    seg
  )
    == Spec.Glob.read.go(
      Spec.Sym.list(Span.show.at(lo, hi, gap, one, rest)),
      Spec.In{n, acc},
      st,
      seg
    ): Maybe<&2, Spec.Glob>
}:
  match gap one:
    case True{} x:
      e => {==}
    case False{} True{}:
      e =>
        %Shared.U32.is_eq_sound(
          lo,
          hi
        )(
          eo
        ): {
          Spec.Glob.read.go(
            Spec.Sym.list(rest),
            Spec.In{n, Con{Spans.Span{Chr{lo}, Chr{_}}, acc}},
            st,
            seg
          )
            == Spec.Glob.read.go(
              Spec.Sym.list(SCon{Chr{92}, SCon{Chr{lo}, rest}}),
              Spec.In{n, acc},
              st,
              seg
            ): Maybe<&2, Spec.Glob>
        }
        %Equal.sym(
          Char,
          Chr{lo},
          Spec.Sym.char(Spec.Sym.of(Chr{lo})),
          Sym.char_of(Chr{lo})
        ): {
          Spec.Glob.read.go(
            Spec.Sym.list(rest),
            Spec.In{n, Con{Spans.Span{_, _}, acc}},
            st,
            seg
          )
            == Spec.Glob.read.go(
              Spec.Sym.list(SCon{Chr{92}, SCon{Chr{lo}, rest}}),
              Spec.In{n, acc},
              st,
              seg
            ): Maybe<&2, Spec.Glob>
        }
        Step.esc_in(Spec.Sym.of(Chr{lo}), Spec.Sym.list(rest), n, acc, st, seg)
    case False{} False{}:
      +e =>
        +pl = Shared.List.all.if_hit(
          Sym.plain(Spec.Sym.of(Chr{lo})),
          u3 => Sym.plain(Spec.Sym.of(Chr{hi}))
        )(e)
        +ph = Shared.List.all.if_rest(
          Sym.plain(Spec.Sym.of(Chr{lo})),
          u3 => Sym.plain(Spec.Sym.of(Chr{hi}))
        )(e)
        Equal.trans(
          Maybe<&2, Spec.Glob>,
          Spec.Glob.read.go(
            Spec.Sym.list(rest),
            Spec.In{n, Con{Spans.Span{Chr{lo}, Chr{hi}}, acc}},
            st,
            seg
          ),
          Spec.Glob.read.range(
            Spans.Span.of(Spec.Sym.char(Spec.Sym.of(Chr{lo})), Spec.Sym.char(Spec.Sym.of(Chr{hi}))),
            s => Spec.Glob.read.go(Spec.Sym.list(rest), Spec.In{n, Con{s, acc}}, st, seg)
          ),
          Spec.Glob.read.go(
            Spec.Sym.list(SCon{Chr{lo}, SCon{'-', SCon{Chr{hi}, rest}}}),
            Spec.In{n, acc},
            st,
            seg
          ),
          (
            %Sym.char_of(Chr{lo}): {Spec.Glob.read.go(Spec.Sym.list(rest), Spec.In{n, Con{Spans.Span{Chr{lo}, Chr{hi}}, acc}}, st, seg) == Spec.Glob.read.range(Spans.Span.of(_, Spec.Sym.char(Spec.Sym.of(Chr{hi}))), s => Spec.Glob.read.go(Spec.Sym.list(rest), Spec.In{n, Con{s, acc}}, st, seg)): Maybe<&2, Spec.Glob>}
            %Sym.char_of(Chr{hi}): {Spec.Glob.read.go(Spec.Sym.list(rest), Spec.In{n, Con{Spans.Span{Chr{lo}, Chr{hi}}, acc}}, st, seg) == Spec.Glob.read.range(Spans.Span.of(Chr{lo}, _), s => Spec.Glob.read.go(Spec.Sym.list(rest), Spec.In{n, Con{s, acc}}, st, seg)): Maybe<&2, Spec.Glob>}
            %Equal.sym(Bool, Nat.is_le(U32.to_nat(lo), U32.to_nat(hi)), True{}, Shared.Nat.nlt_le(U32.to_nat(hi), U32.to_nat(lo))(Equal.trans(Bool, Nat.is_lt(U32.to_nat(hi), U32.to_nat(lo)), U32.is_lt(hi, lo), False{}, Equal.cong(Cmp, Bool, Cmp.is_lt, Nat.cmp(U32.to_nat(hi), U32.to_nat(lo)), U32.cmp(hi, lo), Equal.sym(Cmp, U32.cmp(hi, lo), Nat.cmp(U32.to_nat(hi), U32.to_nat(lo)), Shared.U32.cmp_to_nat(hi, lo))), eg))): {Spec.Glob.read.go(Spec.Sym.list(rest), Spec.In{n, Con{Spans.Span{Chr{lo}, Chr{hi}}, acc}}, st, seg) == Spec.Glob.read.range(Shared.Maybe.when(Spans.Span, _, u => Some{Spans.Span{Chr{lo}, Chr{hi}}}), s => Spec.Glob.read.go(Spec.Sym.list(rest), Spec.In{n, Con{s, acc}}, st, seg)): Maybe<&2, Spec.Glob>}
            {==}),
          Step.range(
            Spec.Sym.of(Chr{lo}),
            Spec.Sym.of(Chr{hi}),
            Spec.Sym.list(rest),
            n,
            acc,
            st,
            seg
          )(pl)(ph)
        )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# a span whose text reads back as itself is kept by the reader
def Span.parse(
  p: Spans.Span,
  rest: String,
  n: Bool,
  acc: List<&2, Spans.Span>,
  st: List<&2, Spec.Frame>,
  seg: Bool
) -> {
  Span.fine(p) == True{}: Bool
} -> {
  Spec.Glob.read.go(
    Spec.Sym.list(rest),
    Spec.In{n, Span.keep(p, acc)},
    st,
    seg
  )
    == Spec.Glob.read.go(
      Spec.Sym.list(Span.show(p, rest)),
      Spec.In{n, acc},
      st,
      seg
    ): Maybe<&2, Spec.Glob>
}:
  match p:
    case Spans.Span{Chr{+lo}, Chr{+hi}}:
      Span.parse.at(lo, hi, U32.is_lt(hi, lo), {==}, U32.is_eq(lo, hi), {==}, rest, n, acc, st, seg)

# a symbol whose character is none of '!', '\' and ']' is plain
def Sym.plain_char(
  s: Spec.Sym
) -> {
  Char.is_eq(Spec.Sym.char(s), Chr{33}) == False{}: Bool
} -> {
  Char.is_eq(Spec.Sym.char(s), Chr{92}) == False{}: Bool
} -> {Char.is_eq(Spec.Sym.char(s), Chr{93}) == False{}: Bool} -> {Sym.plain(s) == True{}: Bool}:
  match s:
    case Spec.SEsc{}:
      e1 => e2 => e3 => Empty.absurd(
        {False{} == True{}: Bool},
        Shared.Bool.false_ne_true(Equal.sym(Bool, True{}, False{}, e2))
      )
    case Spec.SAny{}:
      e1 => e2 => e3 => {==}
    case Spec.SStar{}:
      e1 => e2 => e3 => {==}
    case Spec.SSlash{}:
      e1 => e2 => e3 => {==}
    case Spec.SOpen{}:
      e1 => e2 => e3 => {==}
    case Spec.SComma{}:
      e1 => e2 => e3 => {==}
    case Spec.SClose{}:
      e1 => e2 => e3 => {==}
    case Spec.SLeft{}:
      e1 => e2 => e3 => {==}
    case Spec.SRight{}:
      e1 => e2 => e3 => Empty.absurd(
        {False{} == True{}: Bool},
        Shared.Bool.false_ne_true(Equal.sym(Bool, True{}, False{}, e3))
      )
    case Spec.SBang{}:
      e1 => e2 => e3 => Empty.absurd(
        {False{} == True{}: Bool},
        Shared.Bool.false_ne_true(Equal.sym(Bool, True{}, False{}, e1))
      )
    case Spec.SDash{}:
      e1 => e2 => e3 => {==}
    case Spec.SChar{k}:
      e1 => e2 => e3 => {==}

# the role of a character that is none of '!', '\' and ']' is plain
def Sym.plain_of(
  +c: Char
) -> {
  Char.is_eq(c, Chr{33}) == False{}: Bool
} -> {
  Char.is_eq(c, Chr{92}) == False{}: Bool
} -> {Char.is_eq(c, Chr{93}) == False{}: Bool} -> {Sym.plain(Spec.Sym.of(c)) == True{}: Bool}:
  e1 => e2 => e3 =>
    Sym.plain_char(Spec.Sym.of(c))(
      %Sym.char_of(c): {Char.is_eq(_, Chr{33}) == False{}: Bool}
      e1)(
      %Sym.char_of(c): {Char.is_eq(_, Chr{92}) == False{}: Bool}
      e2)(
      %Sym.char_of(c): {Char.is_eq(_, Chr{93}) == False{}: Bool}
      e3)

# r holds none of '!', '\' and ']'
def Span.clear(+r: Spans.Span) -> Bool:
  List.all.if(
    u => List.all.if(
      u2 => Bool.not(Spans.Span.has(r, Chr{93})),
      Bool.not(Spans.Span.has(r, Chr{92}))
    ),
    Bool.not(Spans.Span.has(r, Chr{33}))
  )

# r is one character, or holds none of '!', '\' and ']'
def Span.safe(r: Spans.Span) -> Bool:
  match r:
    case Spans.Span{+a, +b}:
      List.any.if(u => Span.clear(Spans.Span{a, b}), Char.is_eq(a, b))

# the role of a character of a clear span is plain
def Clear.plain(
  +r: Spans.Span,
  +x: Char
) -> {
  Span.clear(r) == True{}: Bool
} -> {Spans.Span.has(r, x) == True{}: Bool} -> {Sym.plain(Spec.Sym.of(x)) == True{}: Bool}:
  +e => +hx =>
    +rest = Shared.List.all.if_rest(
      Bool.not(Spans.Span.has(r, Chr{33})),
      u => List.all.if(
        u2 => Bool.not(Spans.Span.has(r, Chr{93})),
        Bool.not(Spans.Span.has(r, Chr{92}))
      )
    )(e)
    Sym.plain_of(
      x
    )(
      Spans.Span.has_apart(
        r,
        x,
        Chr{33},
        Char.is_eq(x, Chr{33}),
        {==}
      )(
        hx
      )(
        Shared.Bool.not_true(
          Spans.Span.has(r, Chr{33})
        )(
          Shared.List.all.if_hit(
            Bool.not(Spans.Span.has(r, Chr{33})),
            u => List.all.if(
              u2 => Bool.not(Spans.Span.has(r, Chr{93})),
              Bool.not(Spans.Span.has(r, Chr{92}))
            )
          )(e)
        )
      )
    )(
      Spans.Span.has_apart(
        r,
        x,
        Chr{92},
        Char.is_eq(x, Chr{92}),
        {==}
      )(
        hx
      )(
        Shared.Bool.not_true(
          Spans.Span.has(r, Chr{92})
        )(
          Shared.List.all.if_hit(
            Bool.not(Spans.Span.has(r, Chr{92})),
            u2 => Bool.not(Spans.Span.has(r, Chr{93}))
          )(rest)
        )
      )
    )(
      Spans.Span.has_apart(
        r,
        x,
        Chr{93},
        Char.is_eq(x, Chr{93}),
        {==}
      )(
        hx
      )(
        Shared.Bool.not_true(
          Spans.Span.has(r, Chr{93})
        )(
          Shared.List.all.if_rest(
            Bool.not(Spans.Span.has(r, Chr{92})),
            u2 => Bool.not(Spans.Span.has(r, Chr{93}))
          )(rest)
        )
      )
    )

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- a false positive, as the rule notes: the other use is an erased argument (of Equal.sym or a motive)
# Safe.plain once it is known whether the span a..b is one character (k)
def Safe.plain.at(
  +a: Char,
  b: Char,
  +x: Char,
  +y: Char,
  k: Bool,
  ek: {Char.is_eq(a, b) == k: Bool},
  sr: {List.any.if(u => Span.clear(Spans.Span{a, b}), k) == True{}: Bool},
  hx: {Spans.Span.has(Spans.Span{a, b}, x) == True{}: Bool},
  hy: {Spans.Span.has(Spans.Span{a, b}, y) == True{}: Bool},
  ne: {Char.is_eq(x, y) == False{}: Bool}
) -> {Sym.plain(Spec.Sym.of(x)) == True{}: Bool}:
  match k:
    case False{}:
      Clear.plain(Spans.Span{a, b}, x)(sr)(hx)
    case True{}:
      +ab = Shared.Char.is_eq_sound(a, b)(ek)
      xa = Shared.Char.is_eq_sound(
        x,
        a
      )(
        Equal.trans(
          Bool,
          Char.is_eq(x, a),
          Spans.Span.has(Spans.Span{a, a}, x),
          True{},
          Char.is_eq_span(x, a),
          (
            %Equal.sym(Char, a, b, ab): {Spans.Span.has(Spans.Span{a, _}, x) == True{}: Bool}
            hx)
        )
      )
      ya = Shared.Char.is_eq_sound(
        y,
        a
      )(
        Equal.trans(
          Bool,
          Char.is_eq(y, a),
          Spans.Span.has(Spans.Span{a, a}, y),
          True{},
          Char.is_eq_span(y, a),
          (
            %Equal.sym(Char, a, b, ab): {Spans.Span.has(Spans.Span{a, _}, y) == True{}: Bool}
            hy)
        )
      )
      Empty.absurd(
        {Sym.plain(Spec.Sym.of(x)) == True{}: Bool},
        Shared.Bool.false_ne_true(
          Equal.trans(
            Bool,
            False{},
            Char.is_eq(x, y),
            True{},
            Equal.sym(Bool, Char.is_eq(x, y), False{}, ne),
            (
              %Equal.sym(Char, x, a, xa): {Char.is_eq(_, y) == True{}: Bool}
              %Equal.sym(Char, y, a, ya): {Char.is_eq(a, _) == True{}: Bool}
              Shared.Char.is_eq_refl(a))
          )
        )
      )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# the role of a character x of a safe span is plain, when the span holds a
# character y other than x
def Safe.plain(
  r: Spans.Span,
  x: Char,
  y: Char
) -> {
  Span.safe(r) == True{}: Bool
} -> {
  Spans.Span.has(r, x) == True{}: Bool
} -> {
  Spans.Span.has(r, y) == True{}: Bool
} -> {Char.is_eq(x, y) == False{}: Bool} -> {Sym.plain(Spec.Sym.of(x)) == True{}: Bool}:
  match r:
    case Spans.Span{+a, +b}:
      sr => hx => hy => ne => Safe.plain.at(a, b, x, y, Char.is_eq(a, b), {==}, sr, hx, hy, ne)

# Span.fine of the span p..q, once it is known whether it is empty (g) and
# whether it is one character (o), when its ends are in a safe span r
def Fine.in.at(
  +p: U32,
  +q: U32,
  +r: Spans.Span,
  g: Bool,
  +eg: {U32.is_lt(q, p) == g: Bool},
  o: Bool,
  +eo: {U32.is_eq(p, q) == o: Bool},
  +sr: {Span.safe(r) == True{}: Bool},
  hp: {U32.is_lt(q, p) == False{}: Bool} -> {Spans.Span.has(r, Chr{p}) == True{}: Bool},
  hq: {U32.is_lt(q, p) == False{}: Bool} -> {Spans.Span.has(r, Chr{q}) == True{}: Bool}
) -> {Span.fine(Spans.Span{Chr{p}, Chr{q}}) == True{}: Bool}:
  match g o:
    case True{} x:
      %Equal.sym(
        Bool,
        U32.is_lt(q, p),
        True{},
        eg
      ): {
        List.any.if(
          u => List.any.if(
            u2 => List.all.if(u3 => Sym.plain(Spec.Sym.of(Chr{q})), Sym.plain(Spec.Sym.of(Chr{p}))),
            U32.is_eq(p, q)
          ),
          _
        )
          == True{}: Bool
      }
      {==}
    case False{} True{}:
      %Equal.sym(
        Bool,
        U32.is_lt(q, p),
        False{},
        eg
      ): {
        List.any.if(
          u => List.any.if(
            u2 => List.all.if(u3 => Sym.plain(Spec.Sym.of(Chr{q})), Sym.plain(Spec.Sym.of(Chr{p}))),
            U32.is_eq(p, q)
          ),
          _
        )
          == True{}: Bool
      }
      %Equal.sym(
        Bool,
        U32.is_eq(p, q),
        True{},
        eo
      ): {
        List.any.if(
          u2 => List.all.if(u3 => Sym.plain(Spec.Sym.of(Chr{q})), Sym.plain(Spec.Sym.of(Chr{p}))),
          _
        )
          == True{}: Bool
      }
      {==}
    case False{} False{}:
      +xp = hp(eg)
      +xq = hq(eg)
      %Equal.sym(
        Bool,
        U32.is_lt(q, p),
        False{},
        eg
      ): {
        List.any.if(
          u => List.any.if(
            u2 => List.all.if(u3 => Sym.plain(Spec.Sym.of(Chr{q})), Sym.plain(Spec.Sym.of(Chr{p}))),
            U32.is_eq(p, q)
          ),
          _
        )
          == True{}: Bool
      }
      %Equal.sym(
        Bool,
        U32.is_eq(p, q),
        False{},
        eo
      ): {
        List.any.if(
          u2 => List.all.if(u3 => Sym.plain(Spec.Sym.of(Chr{q})), Sym.plain(Spec.Sym.of(Chr{p}))),
          _
        )
          == True{}: Bool
      }
      %Equal.sym(
        Bool,
        Sym.plain(Spec.Sym.of(Chr{p})),
        True{},
        Safe.plain(r, Chr{p}, Chr{q})(sr)(xp)(xq)(eo)
      ): {List.all.if(u3 => Sym.plain(Spec.Sym.of(Chr{q})), _) == True{}: Bool}
      Safe.plain(
        r,
        Chr{q},
        Chr{p}
      )(
        sr
      )(
        xq
      )(
        xp
      )(
        Equal.trans(
          Bool,
          Char.is_eq(Chr{q}, Chr{p}),
          Char.is_eq(Chr{p}, Chr{q}),
          False{},
          Char.is_eq_comm(Chr{q}, Chr{p}),
          eo
        )
      )

# the meet of s with a safe span reads back as itself
def Span.meet_fine(
  s: Spans.Span,
  r: Spans.Span
) -> {Span.safe(r) == True{}: Bool} -> {Span.fine(Spans.Span.meet(s, r)) == True{}: Bool}:
  match s r:
    case Spans.Span{Chr{+lo}, Chr{+hi}} Spans.Span{Chr{+a}, Chr{+b}}:
      sr =>
        Fine.in.at(
          Bool.pick(U32, U32.is_le(lo, a), a, lo),
          Bool.pick(U32, U32.is_le(hi, b), hi, b),
          Spans.Span{Chr{a}, Chr{b}},
          U32.is_lt(
            Bool.pick(U32, U32.is_le(hi, b), hi, b),
            Bool.pick(U32, U32.is_le(lo, a), a, lo)
          ),
          {==},
          U32.is_eq(
            Bool.pick(U32, U32.is_le(lo, a), a, lo),
            Bool.pick(U32, U32.is_le(hi, b), hi, b)
          ),
          {==},
          sr,
          g => Spans.Span.meet_right(
            Spans.Span{Chr{lo}, Chr{hi}},
            Spans.Span{Chr{a}, Chr{b}},
            Chr{Bool.pick(U32, U32.is_le(lo, a), a, lo)}
          )(
            Spans.Span.has_low(
              Bool.pick(U32, U32.is_le(lo, a), a, lo),
              Bool.pick(U32, U32.is_le(hi, b), hi, b)
            )(g)
          ),
          g => Spans.Span.meet_right(
            Spans.Span{Chr{lo}, Chr{hi}},
            Spans.Span{Chr{a}, Chr{b}},
            Chr{Bool.pick(U32, U32.is_le(hi, b), hi, b)}
          )(
            Spans.Span.has_high(
              Bool.pick(U32, U32.is_le(lo, a), a, lo),
              Bool.pick(U32, U32.is_le(hi, b), hi, b)
            )(g)
          )
        )

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- only proofs use it; no program runs it
# the meets of s with safe spans read back as themselves
def Span.meets_fine(
  +s: Spans.Span,
  rs: List<&2, Spans.Span>
) -> {
  List.all(~&2, ~Spans.Span, ~Span.safe, rs) == True{}: Bool
} -> {List.all(~&2, ~Spans.Span, ~Span.fine, Spans.Span.meets(s, rs)) == True{}: Bool}:
  match rs:
    case Nil{}:
      e => {==}
    case Con{+r, +t}:
      +e =>
        %Equal.sym(
          Bool,
          Span.fine(Spans.Span.meet(s, r)),
          True{},
          Span.meet_fine(
            s,
            r
          )(Shared.List.all.if_hit(Span.safe(r), u => List.all(~&2, ~Spans.Span, ~Span.safe, t))(e))
        ): {
          List.all.if(
            u => List.all(~&2, ~Spans.Span, ~Span.fine, Spans.Span.meets(s, t)),
            _
          )
            == True{}: Bool
        }
        Span.meets_fine(
          s,
          t
        )(Shared.List.all.if_rest(Span.safe(r), u => List.all(~&2, ~Spans.Span, ~Span.safe, t))(e))
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# each part of s reads back as itself
def Span.parts_fine(
  s: Spans.Span
) -> {List.all(~&2, ~Spans.Span, ~Span.fine, Span.parts(s)) == True{}: Bool}:
  Span.meets_fine(s, Span.bounds())({==})

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- only proofs use it; no program runs it
# spans whose texts read back as themselves are kept by the reader, in turn
def Span.parse.all(
  xs: List<&2, Spans.Span>,
  +rest: String,
  +n: Bool,
  +acc: List<&2, Spans.Span>,
  +st: List<&2, Spec.Frame>,
  +seg: Bool
) -> {
  List.all(~&2, ~Spans.Span, ~Span.fine, xs) == True{}: Bool
} -> {
  Spec.Glob.read.go(
    Spec.Sym.list(rest),
    Spec.In{n, Span.keep.all(xs, acc)},
    st,
    seg
  )
    == Spec.Glob.read.go(
      Spec.Sym.list(Span.show.all(xs, rest)),
      Spec.In{n, acc},
      st,
      seg
    ): Maybe<&2, Spec.Glob>
}:
  match xs:
    case Nil{}:
      e => {==}
    case Con{+p, +t}:
      +e =>
        Equal.trans(
          Maybe<&2, Spec.Glob>,
          Spec.Glob.read.go(
            Spec.Sym.list(rest),
            Spec.In{n, Span.keep.all(t, Span.keep(p, acc))},
            st,
            seg
          ),
          Spec.Glob.read.go(
            Spec.Sym.list(Span.show.all(t, rest)),
            Spec.In{n, Span.keep(p, acc)},
            st,
            seg
          ),
          Spec.Glob.read.go(
            Spec.Sym.list(Span.show(p, Span.show.all(t, rest))),
            Spec.In{n, acc},
            st,
            seg
          ),
          Span.parse.all(
            t,
            rest,
            n,
            Span.keep(p, acc),
            st,
            seg
          )(
            Shared.List.all.if_rest(Span.fine(p), u => List.all(~&2, ~Spans.Span, ~Span.fine, t))(e)
          ),
          Span.parse(
            p,
            Span.show.all(t, rest),
            n,
            acc,
            st,
            seg
          )(Shared.List.all.if_hit(Span.fine(p), u => List.all(~&2, ~Spans.Span, ~Span.fine, t))(e))
        )
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# reading the text of the spans of a class keeps their parts, last first
def Show.parse_spans(
  ss: List<&2, Spans.Span>,
  +rest: String,
  +n: Bool,
  +acc: List<&2, Spans.Span>,
  +st: List<&2, Spec.Frame>,
  +seg: Bool
) -> {
  Spec.Glob.read.go(
    Spec.Sym.list(rest),
    Spec.In{n, Show.spans(ss, acc)},
    st,
    seg
  )
    == Spec.Glob.read.go(
      Spec.Sym.list(Glob.show.spans(ss, rest)),
      Spec.In{n, acc},
      st,
      seg
    ): Maybe<&2, Spec.Glob>
}:
  match ss:
    case Nil{}:
      {==}
    case Con{+s, +t}:
      Equal.trans(
        Maybe<&2, Spec.Glob>,
        Spec.Glob.read.go(
          Spec.Sym.list(rest),
          Spec.In{n, Show.spans(t, Span.keep.all(Span.parts(s), acc))},
          st,
          seg
        ),
        Spec.Glob.read.go(
          Spec.Sym.list(Glob.show.spans(t, rest)),
          Spec.In{n, Span.keep.all(Span.parts(s), acc)},
          st,
          seg
        ),
        Spec.Glob.read.go(
          Spec.Sym.list(Span.show.all(Span.parts(s), Glob.show.spans(t, rest))),
          Spec.In{n, acc},
          st,
          seg
        ),
        Show.parse_spans(t, rest, n, Span.keep.all(Span.parts(s), acc), st, seg),
        Span.parse.all(Span.parts(s), Glob.show.spans(t, rest), n, acc, st, seg)(Span.parts_fine(s))
      )

# the symbols l do not start with `!`
def Syms.no_bang(l: List<&2, Spec.Sym>) -> Bool:
  match l:
    case Nil{}:
      True{}
    case Con{y, t}:
      Bool.not(Sym.bang(y))

# a plain symbol is not `!`
def Sym.plain_bang(y: Spec.Sym) -> {Sym.plain(y) == True{}: Bool} -> {Sym.bang(y) == False{}: Bool}:
  match y:
    case Spec.SBang{}:
      e => Empty.absurd({True{} == False{}: Bool}, Shared.Bool.false_ne_true(e))
    case Spec.SEsc{}:
      e => {==}
    case Spec.SAny{}:
      e => {==}
    case Spec.SStar{}:
      e => {==}
    case Spec.SSlash{}:
      e => {==}
    case Spec.SOpen{}:
      e => {==}
    case Spec.SComma{}:
      e => {==}
    case Spec.SClose{}:
      e => {==}
    case Spec.SLeft{}:
      e => {==}
    case Spec.SRight{}:
      e => {==}
    case Spec.SDash{}:
      e => {==}
    case Spec.SChar{c}:
      e => {==}

# Span.no_bang once it is known whether the span is empty (gap) and whether it
# is one character (one)
def Span.no_bang.at(
  +lo: U32,
  hi: U32,
  gap: Bool,
  one: Bool,
  rest: String
) -> {
  List.any.if(
    u => List.any.if(
      u2 => List.all.if(u3 => Sym.plain(Spec.Sym.of(Chr{hi})), Sym.plain(Spec.Sym.of(Chr{lo}))),
      one
    ),
    gap
  )
    == True{}: Bool
} -> {
  Syms.no_bang(Spec.Sym.list(rest)) == True{}: Bool
} -> {Syms.no_bang(Spec.Sym.list(Span.show.at(lo, hi, gap, one, rest))) == True{}: Bool}:
  match gap one:
    case True{} x:
      e => h => h
    case False{} True{}:
      e => h => {==}
    case False{} False{}:
      e => h => Equal.cong(
        Bool,
        Bool,
        v => Bool.not(v),
        Sym.bang(Spec.Sym.of(Chr{lo})),
        False{},
        Sym.plain_bang(
          Spec.Sym.of(Chr{lo})
        )(
          Shared.List.all.if_hit(
            Sym.plain(Spec.Sym.of(Chr{lo})),
            u3 => Sym.plain(Spec.Sym.of(Chr{hi}))
          )(e)
        )
      )

# the text of a span whose text reads back as itself does not start with `!`,
# when what follows it does not
def Span.no_bang(
  p: Spans.Span,
  rest: String
) -> {
  Span.fine(p) == True{}: Bool
} -> {
  Syms.no_bang(Spec.Sym.list(rest)) == True{}: Bool
} -> {Syms.no_bang(Spec.Sym.list(Span.show(p, rest))) == True{}: Bool}:
  match p:
    case Spans.Span{Chr{+lo}, Chr{+hi}}:
      Span.no_bang.at(lo, hi, U32.is_lt(hi, lo), U32.is_eq(lo, hi), rest)

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- only proofs use it; no program runs it
# Span.no_bang for each span of xs
def Span.no_bang.all(
  xs: List<&2, Spans.Span>,
  +rest: String
) -> {
  List.all(~&2, ~Spans.Span, ~Span.fine, xs) == True{}: Bool
} -> {
  Syms.no_bang(Spec.Sym.list(rest)) == True{}: Bool
} -> {Syms.no_bang(Spec.Sym.list(Span.show.all(xs, rest))) == True{}: Bool}:
  match xs:
    case Nil{}:
      e => h => h
    case Con{+p, +t}:
      +e => h => Span.no_bang(
        p,
        Span.show.all(t, rest)
      )(
        Shared.List.all.if_hit(Span.fine(p), u => List.all(~&2, ~Spans.Span, ~Span.fine, t))(e)
      )(
        Span.no_bang.all(
          t,
          rest
        )(
          Shared.List.all.if_rest(Span.fine(p), u => List.all(~&2, ~Spans.Span, ~Span.fine, t))(e)
        )(h)
      )
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# the text of the spans of a class does not start with `!`, when what follows
# it does not
def Show.no_bang(
  ss: List<&2, Spans.Span>,
  +rest: String
) -> {
  Syms.no_bang(Spec.Sym.list(rest)) == True{}: Bool
} -> {Syms.no_bang(Spec.Sym.list(Glob.show.spans(ss, rest))) == True{}: Bool}:
  match ss:
    case Nil{}:
      h => h
    case Con{+s, +t}:
      h => Span.no_bang.all(
        Span.parts(s),
        Glob.show.spans(t, rest)
      )(Span.parts_fine(s))(Show.no_bang(t, rest)(h))

# `[` before symbols that do not start with `!` opens a class
def Show.open(
  l: List<&2, Spec.Sym>,
  st: List<&2, Spec.Frame>,
  seg: Bool
) -> {
  Syms.no_bang(l) == True{}: Bool
} -> {
  Spec.Glob.read.go(
    l,
    Spec.In{False{}, []},
    st,
    seg
  )
    == Spec.Glob.read.go(Con{Spec.SLeft{}, l}, Spec.Out{}, st, seg): Maybe<&2, Spec.Glob>
}:
  match l:
    case Nil{}:
      e => {==}
    case Con{+y, t}:
      e => Step.left(y, t, st, seg)(Shared.Bool.not_true(Sym.bang(y))(e))

# the text of Lit{c} reads back as Lit{c}, given k, the role of c
def Show.parse_lit(
  +c: Char,
  k: Spec.Sym,
  rest: String,
  +a: List<&2, Spec.Glob>,
  +s: List<&2, Spec.Glob>,
  +b: Bool,
  +r: List<&2, Spec.Frame>,
  seg: Bool
) -> {
  k == Spec.Sym.of(c): Spec.Sym
} -> {
  Spec.Glob.read.go(
    Spec.Sym.list(rest),
    Spec.Out{},
    Con{Spec.Frame{a, Con{Spec.Lit{c}, s}, b}, r},
    False{}
  )
    == Spec.Glob.read.go(
      Spec.Sym.list(Glob.show.char(c, k, rest)),
      Spec.Out{},
      Con{Spec.Frame{a, s, b}, r},
      seg
    ): Maybe<&2, Spec.Glob>
}:
  match k:
    case Spec.SChar{+x}:
      +e =>
        +l = Spec.Sym.list(rest)
        +st = {Con{Spec.Frame{a, s, b}, r}: List<&2, Spec.Frame>}
        +tgt = Spec.Glob.read.go(
          l,
          Spec.Out{},
          Con{Spec.Frame{a, Con{Spec.Lit{c}, s}, b}, r},
          False{}
        )
        %e: {tgt == Spec.Glob.read.go(Con{_, l}, Spec.Out{}, st, seg): Maybe<&2, Spec.Glob>}
        %Step.char(x, l, st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_is(
          c,
          Spec.SChar{x},
          e
        ): {
          tgt
            == Spec.Glob.read.go(
              l,
              Spec.Out{},
              Spec.Frame.add(st, Spec.Lit{_}),
              False{}
            ): Maybe<&2, Spec.Glob>
        }
        {==}
    case Spec.SEsc{}:
      e =>
        +l = Spec.Sym.list(rest)
        +st = {Con{Spec.Frame{a, s, b}, r}: List<&2, Spec.Frame>}
        +tgt = Spec.Glob.read.go(
          l,
          Spec.Out{},
          Con{Spec.Frame{a, Con{Spec.Lit{c}, s}, b}, r},
          False{}
        )
        %Step.esc(Spec.Sym.of(c), l, st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(
          c
        ): {
          tgt
            == Spec.Glob.read.go(
              l,
              Spec.Out{},
              Spec.Frame.add(st, Spec.Lit{_}),
              False{}
            ): Maybe<&2, Spec.Glob>
        }
        {==}
    case Spec.SAny{}:
      e =>
        +l = Spec.Sym.list(rest)
        +st = {Con{Spec.Frame{a, s, b}, r}: List<&2, Spec.Frame>}
        +tgt = Spec.Glob.read.go(
          l,
          Spec.Out{},
          Con{Spec.Frame{a, Con{Spec.Lit{c}, s}, b}, r},
          False{}
        )
        %Step.esc(Spec.Sym.of(c), l, st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(
          c
        ): {
          tgt
            == Spec.Glob.read.go(
              l,
              Spec.Out{},
              Spec.Frame.add(st, Spec.Lit{_}),
              False{}
            ): Maybe<&2, Spec.Glob>
        }
        {==}
    case Spec.SStar{}:
      e =>
        +l = Spec.Sym.list(rest)
        +st = {Con{Spec.Frame{a, s, b}, r}: List<&2, Spec.Frame>}
        +tgt = Spec.Glob.read.go(
          l,
          Spec.Out{},
          Con{Spec.Frame{a, Con{Spec.Lit{c}, s}, b}, r},
          False{}
        )
        %Step.esc(Spec.Sym.of(c), l, st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(
          c
        ): {
          tgt
            == Spec.Glob.read.go(
              l,
              Spec.Out{},
              Spec.Frame.add(st, Spec.Lit{_}),
              False{}
            ): Maybe<&2, Spec.Glob>
        }
        {==}
    case Spec.SSlash{}:
      e =>
        +l = Spec.Sym.list(rest)
        +st = {Con{Spec.Frame{a, s, b}, r}: List<&2, Spec.Frame>}
        +tgt = Spec.Glob.read.go(
          l,
          Spec.Out{},
          Con{Spec.Frame{a, Con{Spec.Lit{c}, s}, b}, r},
          False{}
        )
        %Step.esc(Spec.Sym.of(c), l, st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(
          c
        ): {
          tgt
            == Spec.Glob.read.go(
              l,
              Spec.Out{},
              Spec.Frame.add(st, Spec.Lit{_}),
              False{}
            ): Maybe<&2, Spec.Glob>
        }
        {==}
    case Spec.SOpen{}:
      e =>
        +l = Spec.Sym.list(rest)
        +st = {Con{Spec.Frame{a, s, b}, r}: List<&2, Spec.Frame>}
        +tgt = Spec.Glob.read.go(
          l,
          Spec.Out{},
          Con{Spec.Frame{a, Con{Spec.Lit{c}, s}, b}, r},
          False{}
        )
        %Step.esc(Spec.Sym.of(c), l, st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(
          c
        ): {
          tgt
            == Spec.Glob.read.go(
              l,
              Spec.Out{},
              Spec.Frame.add(st, Spec.Lit{_}),
              False{}
            ): Maybe<&2, Spec.Glob>
        }
        {==}
    case Spec.SComma{}:
      e =>
        +l = Spec.Sym.list(rest)
        +st = {Con{Spec.Frame{a, s, b}, r}: List<&2, Spec.Frame>}
        +tgt = Spec.Glob.read.go(
          l,
          Spec.Out{},
          Con{Spec.Frame{a, Con{Spec.Lit{c}, s}, b}, r},
          False{}
        )
        %Step.esc(Spec.Sym.of(c), l, st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(
          c
        ): {
          tgt
            == Spec.Glob.read.go(
              l,
              Spec.Out{},
              Spec.Frame.add(st, Spec.Lit{_}),
              False{}
            ): Maybe<&2, Spec.Glob>
        }
        {==}
    case Spec.SClose{}:
      e =>
        +l = Spec.Sym.list(rest)
        +st = {Con{Spec.Frame{a, s, b}, r}: List<&2, Spec.Frame>}
        +tgt = Spec.Glob.read.go(
          l,
          Spec.Out{},
          Con{Spec.Frame{a, Con{Spec.Lit{c}, s}, b}, r},
          False{}
        )
        %Step.esc(Spec.Sym.of(c), l, st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(
          c
        ): {
          tgt
            == Spec.Glob.read.go(
              l,
              Spec.Out{},
              Spec.Frame.add(st, Spec.Lit{_}),
              False{}
            ): Maybe<&2, Spec.Glob>
        }
        {==}
    case Spec.SLeft{}:
      e =>
        +l = Spec.Sym.list(rest)
        +st = {Con{Spec.Frame{a, s, b}, r}: List<&2, Spec.Frame>}
        +tgt = Spec.Glob.read.go(
          l,
          Spec.Out{},
          Con{Spec.Frame{a, Con{Spec.Lit{c}, s}, b}, r},
          False{}
        )
        %Step.esc(Spec.Sym.of(c), l, st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(
          c
        ): {
          tgt
            == Spec.Glob.read.go(
              l,
              Spec.Out{},
              Spec.Frame.add(st, Spec.Lit{_}),
              False{}
            ): Maybe<&2, Spec.Glob>
        }
        {==}
    case Spec.SRight{}:
      e =>
        +l = Spec.Sym.list(rest)
        +st = {Con{Spec.Frame{a, s, b}, r}: List<&2, Spec.Frame>}
        +tgt = Spec.Glob.read.go(
          l,
          Spec.Out{},
          Con{Spec.Frame{a, Con{Spec.Lit{c}, s}, b}, r},
          False{}
        )
        %Step.esc(Spec.Sym.of(c), l, st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(
          c
        ): {
          tgt
            == Spec.Glob.read.go(
              l,
              Spec.Out{},
              Spec.Frame.add(st, Spec.Lit{_}),
              False{}
            ): Maybe<&2, Spec.Glob>
        }
        {==}
    case Spec.SBang{}:
      e =>
        +l = Spec.Sym.list(rest)
        +st = {Con{Spec.Frame{a, s, b}, r}: List<&2, Spec.Frame>}
        +tgt = Spec.Glob.read.go(
          l,
          Spec.Out{},
          Con{Spec.Frame{a, Con{Spec.Lit{c}, s}, b}, r},
          False{}
        )
        %Step.esc(Spec.Sym.of(c), l, st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(
          c
        ): {
          tgt
            == Spec.Glob.read.go(
              l,
              Spec.Out{},
              Spec.Frame.add(st, Spec.Lit{_}),
              False{}
            ): Maybe<&2, Spec.Glob>
        }
        {==}
    case Spec.SDash{}:
      e =>
        +l = Spec.Sym.list(rest)
        +st = {Con{Spec.Frame{a, s, b}, r}: List<&2, Spec.Frame>}
        +tgt = Spec.Glob.read.go(
          l,
          Spec.Out{},
          Con{Spec.Frame{a, Con{Spec.Lit{c}, s}, b}, r},
          False{}
        )
        %Step.esc(Spec.Sym.of(c), l, st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(
          c
        ): {
          tgt
            == Spec.Glob.read.go(
              l,
              Spec.Out{},
              Spec.Frame.add(st, Spec.Lit{_}),
              False{}
            ): Maybe<&2, Spec.Glob>
        }
        {==}

# the text of a class reads back as the class of the parts of its spans that
# are not empty, last first
def Show.parse_class(
  neg: Bool,
  ss: List<&2, Spans.Span>,
  +rest: String,
  +a: List<&2, Spec.Glob>,
  +s: List<&2, Spec.Glob>,
  +b: Bool,
  +r: List<&2, Spec.Frame>,
  +seg: Bool
) -> {
  Spec.Glob.read.go(
    Spec.Sym.list(rest),
    Spec.Out{},
    Con{Spec.Frame{a, Con{Show.glob(Spec.Class{neg, ss}), s}, b}, r},
    False{}
  )
    == Spec.Glob.read.go(
      Spec.Sym.list(Glob.show.go(Spec.Class{neg, ss}, rest)),
      Spec.Out{},
      Con{Spec.Frame{a, s, b}, r},
      seg
    ): Maybe<&2, Spec.Glob>
}:
  match neg:
    case True{}:
      +ss = ss
      +l = Spec.Sym.list(rest)
      +st = {Con{Spec.Frame{a, s, b}, r}: List<&2, Spec.Frame>}
      tgt = Spec.Glob.read.go(
        l,
        Spec.Out{},
        Con{Spec.Frame{a, Con{Spec.Class{True{}, Show.spans(ss, [])}, s}, b}, r},
        False{}
      )
      lc = Spec.Sym.list(Glob.show.spans(ss, "]" ++ rest))
      %Step.left_bang(lc, st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
      %Show.parse_spans(ss, "]" ++ rest, True{}, [], st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
      %Step.right(l, True{}, Show.spans(ss, []), st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
      {==}
    case False{}:
      +ss = ss
      +l = Spec.Sym.list(rest)
      +st = {Con{Spec.Frame{a, s, b}, r}: List<&2, Spec.Frame>}
      tgt = Spec.Glob.read.go(
        l,
        Spec.Out{},
        Con{Spec.Frame{a, Con{Spec.Class{False{}, Show.spans(ss, [])}, s}, b}, r},
        False{}
      )
      lc = Spec.Sym.list(Glob.show.spans(ss, "]" ++ rest))
      %Show.open(lc, st, seg)(Show.no_bang(ss, "]" ++ rest)({==})): {tgt == _: Maybe<&2, Spec.Glob>}
      %Show.parse_spans(ss, "]" ++ rest, False{}, [], st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
      %Step.right(l, False{}, Show.spans(ss, []), st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
      {==}

# the text of g, before rest, reads back as the one atom Show.glob(g)
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- only proofs use it; no program runs it
def Show.parse(
  g: Spec.Glob,
  +rest: String,
  +a: List<&2, Spec.Glob>,
  +s: List<&2, Spec.Glob>,
  +b: Bool,
  +r: List<&2, Spec.Frame>,
  +seg: Bool
) -> {
  Spec.Glob.read.go(
    Spec.Sym.list(rest),
    Spec.Out{},
    Con{Spec.Frame{a, Con{Show.glob(g), s}, b}, r},
    False{}
  )
    == Spec.Glob.read.go(
      Spec.Sym.list(Glob.show.go(g, rest)),
      Spec.Out{},
      Con{Spec.Frame{a, s, b}, r},
      seg
    ): Maybe<&2, Spec.Glob>
}:
  match g:
    case Spec.Void{}:
      +l = Spec.Sym.list(rest)
      +st = {Con{Spec.Frame{a, s, b}, r}: List<&2, Spec.Frame>}
      -tgt = Spec.Glob.read.go(
        l,
        Spec.Out{},
        Con{Spec.Frame{a, Con{Spec.Class{False{}, []}, s}, b}, r},
        False{}
      )
      %Step.left_right(l, st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
      %Step.right(l, False{}, [], st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
      {==}
    case Spec.Eps{}:
      +l = Spec.Sym.list(rest)
      st = {Con{Spec.Frame{a, s, b}, r}: List<&2, Spec.Frame>}
      -tgt = Spec.Glob.read.go(
        l,
        Spec.Out{},
        Con{Spec.Frame{a, Con{Spec.Alt{Spec.Eps{}, Spec.Void{}}, s}, b}, r},
        False{}
      )
      %Step.open(Con{Spec.SClose{}, l}, st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
      %Step.close(l, [], [], seg, Spec.Frame{a, s, b}, r, seg): {tgt == _: Maybe<&2, Spec.Glob>}
      {==}
    case Spec.Lit{+c}:
      Show.parse_lit(c, Spec.Sym.of(c), rest, a, s, b, r, seg)({==})
    case Spec.Any{}:
      Step.any(Spec.Sym.list(rest), Con{Spec.Frame{a, s, b}, r}, seg)
    case Spec.Star{}:
      +l = Spec.Sym.list(rest)
      +st = {Con{Spec.Frame{a, s, b}, r}: List<&2, Spec.Frame>}
      -tgt = Spec.Glob.read.go(
        l,
        Spec.Out{},
        Con{Spec.Frame{a, Con{Show.glob(Spec.Star{}), s}, b}, r},
        False{}
      )
      %Step.open(
        Con{Spec.SStar{}, Con{Spec.SClose{}, l}},
        st,
        seg
      ): {tgt == _: Maybe<&2, Spec.Glob>}
      %Step.star(l, Con{Spec.Frame{[], [], seg}, st}, seg): {tgt == _: Maybe<&2, Spec.Glob>}
      %Step.close(
        l,
        [],
        [Spec.Star{}],
        seg,
        Spec.Frame{a, s, b},
        r,
        False{}
      ): {tgt == _: Maybe<&2, Spec.Glob>}
      {==}
    case Spec.Class{neg, cs}:
      Show.parse_class(neg, cs, rest, a, s, b, r, seg)
    case Spec.Deep{}:
      Step.deep(Spec.Sym.list(rest), a, s, b, r, seg)
    case Spec.Cat{+x, +y}:
      +st = {Con{Spec.Frame{a, s, b}, r}: List<&2, Spec.Frame>}
      +ty = Glob.show.go(y, "}" ++ rest)
      tx = Glob.show.go(x, ty)
      +gx = Show.glob(x)
      gy = Show.glob(y)
      -tgt = Spec.Glob.read.go(
        Spec.Sym.list(rest),
        Spec.Out{},
        Con{Spec.Frame{a, Con{Show.glob(Spec.Cat{x, y}), s}, b}, r},
        False{}
      )
      %Step.open(Spec.Sym.list(tx), st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
      %Show.parse(x, ty, [], [], seg, st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
      %Show.parse(y, "}" ++ rest, [], [gx], seg, st, False{}): {tgt == _: Maybe<&2, Spec.Glob>}
      %Step.close(
        Spec.Sym.list(rest),
        [],
        [gy, gx],
        seg,
        Spec.Frame{a, s, b},
        r,
        False{}
      ): {tgt == _: Maybe<&2, Spec.Glob>}
      {==}
    case Spec.Alt{+x, +y}:
      +st = {Con{Spec.Frame{a, s, b}, r}: List<&2, Spec.Frame>}
      +ty = Glob.show.go(y, "}" ++ rest)
      tx = Glob.show.go(x, "," ++ ty)
      +gx = Show.glob(x)
      gy = Show.glob(y)
      +ax = {Spec.Cat{gx, Spec.Eps{}}: Spec.Glob}
      -tgt = Spec.Glob.read.go(
        Spec.Sym.list(rest),
        Spec.Out{},
        Con{Spec.Frame{a, Con{Show.glob(Spec.Alt{x, y}), s}, b}, r},
        False{}
      )
      %Step.open(Spec.Sym.list(tx), st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
      %Show.parse(x, "," ++ ty, [], [], seg, st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
      %Step.comma(
        Spec.Sym.list(ty),
        [],
        [gx],
        seg,
        Spec.Frame{a, s, b},
        r,
        False{}
      ): {tgt == _: Maybe<&2, Spec.Glob>}
      %Show.parse(y, "}" ++ rest, [ax], [], seg, st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
      %Step.close(
        Spec.Sym.list(rest),
        [ax],
        [gy],
        seg,
        Spec.Frame{a, s, b},
        r,
        False{}
      ): {tgt == _: Maybe<&2, Spec.Glob>}
      {==}
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# Matching shown text
# -------------------
# Spec.Glob.matches is Regex.Re.matches of the glob's expression, so the laws
# of regex.bend hold for globs as they are. Glob.alt_or and Glob.cat_eps_r
# are the two that these proofs use often.

# Alt matches what either side matches
def Glob.alt_or(
  p: String,
  a: Spec.Glob,
  b: Spec.Glob
) -> {
  Bool.or(
    Spec.Glob.matches(p, a),
    Spec.Glob.matches(p, b)
  )
    == Spec.Glob.matches(p, Spec.Alt{a, b}): Bool
}:
  Regex.Re.alt_or(
    ~Char,
    ~Spec.Atom,
    ~Spec.Atom.hit,
    String.to_list(p),
    Spec.Glob.re(a),
    Spec.Glob.re(b)
  )

# Cat before Eps matches what its left side matches
def Glob.cat_eps_r(
  p: String,
  x: Spec.Glob
) -> {Spec.Glob.matches(p, x) == Spec.Glob.matches(p, Spec.Cat{x, Spec.Eps{}}): Bool}:
  Regex.Re.cat_eps_r(~Char, ~Spec.Atom, ~Spec.Atom.hit, String.to_list(p), Spec.Glob.re(x))

# Alt with Void matches what its left side matches
def Glob.alt_void(
  +p: String,
  +x: Spec.Glob
) -> {Spec.Glob.matches(p, x) == Spec.Glob.matches(p, Spec.Alt{x, Spec.Void{}}): Bool}:
  %Glob.alt_or(p, x, Spec.Void{}): {Spec.Glob.matches(p, x) == _: Bool}
  %Regex.Re.void_never(
    ~Char,
    ~Spec.Atom,
    ~Spec.Atom.hit,
    String.to_list(p)
  ): {Spec.Glob.matches(p, x) == Bool.or(Spec.Glob.matches(p, x), _): Bool}
  Shared.Bool.or_false(Spec.Glob.matches(p, x))

# an empty class matches nothing, as Void
def Show.void_point(
  p: String
) -> {Spec.Glob.matches(p, Spec.Class{False{}, []}) == Spec.Glob.matches(p, Spec.Void{}): Bool}:
  match p:
    case SNil{}:
      {==}
    case SCon{c, t}:
      +i = Spec.is_inner(c)
      %Equal.sym(
        Bool,
        List.all.if(u => False{}, i),
        False{},
        Equal.trans(
          Bool,
          List.all.if(u => False{}, i),
          Bool.and(i, False{}),
          False{},
          Shared.List.all.if_and(i, u => False{}),
          Shared.Bool.and_false_right(i)
        )
      ): {
        Regex.Re.matches(
          ~Char,
          ~Spec.Atom,
          ~Spec.Atom.hit,
          String.to_list(t),
          Regex.Re.of_bool(Spec.Atom, _)
        )
          == Spec.Glob.matches(t, Spec.Void{}): Bool
      }
      {==}

# the text of Eps reads back as Eps
# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- a false positive, as the rule notes: the other use is an erased argument (of Equal.sym or a motive)
def Show.eps_point(
  p: String
) -> {
  Spec.Glob.matches(p, Spec.Alt{Spec.Eps{}, Spec.Void{}}) == Spec.Glob.matches(p, Spec.Eps{}): Bool
}:
  Equal.sym(
    Bool,
    Spec.Glob.matches(p, Spec.Eps{}),
    Spec.Glob.matches(p, Spec.Alt{Spec.Eps{}, Spec.Void{}}),
    Glob.alt_void(p, Spec.Eps{})
  )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# the text of Star reads back as Star
def Show.star_point(
  +p: String
) -> {
  Spec.Glob.matches(
    p,
    Spec.Alt{Spec.Cat{Spec.Star{}, Spec.Eps{}}, Spec.Void{}}
  )
    == Spec.Glob.matches(p, Spec.Star{}): Bool
}:
  %Glob.alt_void(
    p,
    Spec.Cat{Spec.Star{}, Spec.Eps{}}
  ): {_ == Spec.Glob.matches(p, Spec.Star{}): Bool}
  %Glob.cat_eps_r(p, Spec.Star{}): {_ == Spec.Glob.matches(p, Spec.Star{}): Bool}
  {==}

# no number from a to x and from x to b, when b is below a
def Nat.gap_out(
  +a: Nat,
  +b: Nat,
  x: Nat,
  la: Bool,
  ela: {Nat.is_le(a, x) == la: Bool},
  lb: Bool,
  elb: {Nat.is_le(x, b) == lb: Bool}
) -> {Nat.is_lt(b, a) == True{}: Bool} -> {Bool.and(la, lb) == False{}: Bool}:
  match la lb:
    case True{} True{}:
      e => Empty.absurd(
        {True{} == False{}: Bool},
        Shared.Bool.true_ne_false(
          Equal.trans(
            Bool,
            True{},
            Nat.is_lt(b, a),
            False{},
            Equal.sym(Bool, Nat.is_lt(b, a), True{}, e),
            Shared.Nat.le_nlt(a, b)(Shared.Nat.le_trans(a, x, b)(ela)(elb))
          )
        )
      )
    case True{} False{}:
      e => {==}
    case False{} y:
      e => {==}

# no character is in a span that ends before it starts
def Span.gap_has(
  +lo: U32,
  +hi: U32,
  +c: Char
) -> {
  U32.is_lt(hi, lo) == True{}: Bool
} -> {Spans.Span.has(Spans.Span{Chr{lo}, Chr{hi}}, c) == False{}: Bool}:
  e =>
    %Equal.sym(
      Bool,
      Spans.Span.has(Spans.Span{Chr{lo}, Chr{hi}}, c),
      Bool.and(
        Nat.is_le(U32.to_nat(lo), Spans.Char.code(c)),
        Nat.is_le(Spans.Char.code(c), U32.to_nat(hi))
      ),
      Spans.Span.has_codes(Chr{lo}, Chr{hi}, c)
    ): {_ == False{}: Bool}
    Nat.gap_out(
      U32.to_nat(lo),
      U32.to_nat(hi),
      Spans.Char.code(c),
      Nat.is_le(U32.to_nat(lo), Spans.Char.code(c)),
      {==},
      Nat.is_le(Spans.Char.code(c), U32.to_nat(hi)),
      {==}
    )(
      %Shared.U32.is_lt_to_nat(hi, lo): {_ == True{}: Bool}
      e)

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- a false positive, as the rule notes: the other use is an erased argument (of Equal.sym or a motive)
# Span.keep_has once it is known whether the span is empty (gap)
def Span.keep_has.at(
  lo: U32,
  hi: U32,
  gap: Bool,
  eg: {U32.is_lt(hi, lo) == gap: Bool},
  acc: List<&2, Spans.Span>,
  +c: Char
) -> {
  Spans.Spans.has(
    Span.keep.at(gap, Spans.Span{Chr{lo}, Chr{hi}}, acc),
    c
  )
    == Bool.or(Spans.Span.has(Spans.Span{Chr{lo}, Chr{hi}}, c), Spans.Spans.has(acc, c)): Bool
}:
  match gap:
    case True{}:
      %Equal.sym(
        Bool,
        Spans.Span.has(Spans.Span{Chr{lo}, Chr{hi}}, c),
        False{},
        Span.gap_has(lo, hi, c)(eg)
      ): {Spans.Spans.has(acc, c) == Bool.or(_, Spans.Spans.has(acc, c)): Bool}
      {==}
    case False{}:
      Shared.List.any.if_or(
        Spans.Span.has(Spans.Span{Chr{lo}, Chr{hi}}, c),
        u => Spans.Spans.has(acc, c)
      )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# a span that the reader keeps is in front of acc, or is empty
def Span.keep_has(
  x: Spans.Span,
  acc: List<&2, Spans.Span>,
  c: Char
) -> {
  Spans.Spans.has(
    Span.keep(x, acc),
    c
  )
    == Bool.or(Spans.Span.has(x, c), Spans.Spans.has(acc, c)): Bool
}:
  match x:
    case Spans.Span{Chr{+lo}, Chr{+hi}}:
      Span.keep_has.at(lo, hi, U32.is_lt(hi, lo), {==}, acc, c)

# or(t, or(x, a)) as or(any.if(u => t, x), a)
def Or.front(
  +x: Bool,
  +t: Bool,
  +a: Bool
) -> {Bool.or(t, Bool.or(x, a)) == Bool.or(List.any.if(u => t, x), a): Bool}:
  Equal.trans(
    Bool,
    Bool.or(t, Bool.or(x, a)),
    Bool.or(x, Bool.or(t, a)),
    Bool.or(List.any.if(u => t, x), a),
    Shared.Bool.or_swap(t, x, a),
    Equal.trans(
      Bool,
      Bool.or(x, Bool.or(t, a)),
      Bool.or(Bool.or(x, t), a),
      Bool.or(List.any.if(u => t, x), a),
      Shared.Bool.or_assoc(x, t, a),
      (
        %Equal.sym(Bool, List.any.if(u => t, x), Bool.or(x, t), Shared.List.any.if_or(x, u => t)): {Bool.or(Bool.or(x, t), a) == Bool.or(_, a): Bool}
        {==})
    )
  )

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- only proofs use it; no program runs it
# the spans that the reader keeps of xs, in front of acc, hold what xs and
# acc hold
def Span.keep_all_has(
  xs: List<&2, Spans.Span>,
  +acc: List<&2, Spans.Span>,
  +c: Char
) -> {
  Spans.Spans.has(
    Span.keep.all(xs, acc),
    c
  )
    == Bool.or(Spans.Spans.has(xs, c), Spans.Spans.has(acc, c)): Bool
}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      Equal.trans(
        Bool,
        Spans.Spans.has(Span.keep.all(t, Span.keep(x, acc)), c),
        Bool.or(Spans.Spans.has(t, c), Spans.Spans.has(Span.keep(x, acc), c)),
        Bool.or(Spans.Spans.has(Con{x, t}, c), Spans.Spans.has(acc, c)),
        Span.keep_all_has(t, Span.keep(x, acc), c),
        (
          %Equal.sym(Bool, Spans.Spans.has(Span.keep(x, acc), c), Bool.or(Spans.Span.has(x, c), Spans.Spans.has(acc, c)), Span.keep_has(x, acc, c)): {Bool.or(Spans.Spans.has(t, c), _) == Bool.or(Spans.Spans.has(Con{x, t}, c), Spans.Spans.has(acc, c)): Bool}
          Or.front(Spans.Span.has(x, c), Spans.Spans.has(t, c), Spans.Spans.has(acc, c)))
      )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the bounds hold each character
def Bounds.has(+c: Char) -> {Spans.Spans.has(Span.bounds(), c) == True{}: Bool}:
  Spans.Spans.chain_covers(Span.bounds(), Chr{0}, c)({==})(Shared.Nat.le_zero(Spans.Char.code(c)))

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- only proofs use it; no program runs it
# the parts of s hold what s holds
def Span.parts_has(
  +s: Spans.Span,
  +c: Char
) -> {Spans.Spans.has(Span.parts(s), c) == Spans.Span.has(s, c): Bool}:
  Equal.trans(
    Bool,
    Spans.Spans.has(Span.parts(s), c),
    Bool.and(Spans.Span.has(s, c), Spans.Spans.has(Span.bounds(), c)),
    Spans.Span.has(s, c),
    Spans.Span.meets_has(s, Span.bounds(), c),
    (
      %Equal.sym(Bool, Spans.Spans.has(Span.bounds(), c), True{}, Bounds.has(c)): {Bool.and(Spans.Span.has(s, c), _) == Spans.Span.has(s, c): Bool}
      Equal.sym(Bool, Spans.Span.has(s, c), Bool.and(Spans.Span.has(s, c), True{}), Shared.Bool.and_true(Spans.Span.has(s, c))))
  )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- only proofs use it; no program runs it
# the spans that the reader keeps of the text of the class ss, in front of
# acc, hold what ss and acc hold
def Show.spans_has(
  ss: List<&2, Spans.Span>,
  +acc: List<&2, Spans.Span>,
  +c: Char
) -> {
  Spans.Spans.has(
    Show.spans(ss, acc),
    c
  )
    == Bool.or(Spans.Spans.has(ss, c), Spans.Spans.has(acc, c)): Bool
}:
  match ss:
    case Nil{}:
      {==}
    case Con{+s, +t}:
      Equal.trans(
        Bool,
        Spans.Spans.has(Show.spans(t, Span.keep.all(Span.parts(s), acc)), c),
        Bool.or(Spans.Spans.has(t, c), Spans.Spans.has(Span.keep.all(Span.parts(s), acc), c)),
        Bool.or(Spans.Spans.has(Con{s, t}, c), Spans.Spans.has(acc, c)),
        Show.spans_has(t, Span.keep.all(Span.parts(s), acc), c),
        (
          %Equal.sym(Bool, Spans.Spans.has(Span.keep.all(Span.parts(s), acc), c), Bool.or(Spans.Spans.has(Span.parts(s), c), Spans.Spans.has(acc, c)), Span.keep_all_has(Span.parts(s), acc, c)): {Bool.or(Spans.Spans.has(t, c), _) == Bool.or(Spans.Spans.has(Con{s, t}, c), Spans.Spans.has(acc, c)): Bool}
          %Equal.sym(Bool, Spans.Spans.has(Span.parts(s), c), Spans.Span.has(s, c), Span.parts_has(s, c)): {Bool.or(Spans.Spans.has(t, c), Bool.or(_, Spans.Spans.has(acc, c))) == Bool.or(Spans.Spans.has(Con{s, t}, c), Spans.Spans.has(acc, c)): Bool}
          Or.front(Spans.Span.has(s, c), Spans.Spans.has(t, c), Spans.Spans.has(acc, c)))
      )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the class that the text of a class reads back as matches the same strings
def Show.class_point(
  p: String,
  n: Bool,
  +ss: List<&2, Spans.Span>
) -> {
  Spec.Glob.matches(
    p,
    Spec.Class{n, Show.spans(ss, [])}
  )
    == Spec.Glob.matches(p, Spec.Class{n, ss}): Bool
}:
  match p:
    case SNil{}:
      {==}
    case SCon{+c, t}:
      i = Spec.is_inner(c)
      w = String.to_list(t)
      +k = Spans.Spans.has(ss, c)
      r = Regex.Re.matches(
        ~Char,
        ~Spec.Atom,
        ~Spec.Atom.hit,
        w,
        Regex.Re.of_bool(Spec.Atom, List.all.if(u => Bool.xor(n, k), i))
      )
      %Equal.trans(
        Bool,
        k,
        Bool.or(k, False{}),
        Spans.Spans.has(Show.spans(ss, []), c),
        Shared.Bool.or_false(k),
        Equal.sym(
          Bool,
          Spans.Spans.has(Show.spans(ss, []), c),
          Bool.or(k, False{}),
          Show.spans_has(ss, [], c)
        )
      ): {
        Regex.Re.matches(
          ~Char,
          ~Spec.Atom,
          ~Spec.Atom.hit,
          w,
          Regex.Re.of_bool(Spec.Atom, List.all.if(u => Bool.xor(n, _), i))
        )
          == r: Bool
      }
      {==}

# Deep matches everything
def Glob.deep_true(p: String) -> {True{} == Spec.Glob.matches(p, Spec.Deep{}): Bool}:
  match p:
    case SNil{}:
      {==}
    case SCon{c, t}:
      Glob.deep_true(t)

# `/**` matches '/' and then anything
def Show.slash_deep(
  +t: String
) -> {
  True{}
    == Spec.Glob.matches(
      SCon{Chr{47}, t},
      Spec.Cat{Spec.Lit{Chr{47}}, Spec.Cat{Spec.Deep{}, Spec.Eps{}}}
    ): Bool
}:
  +w = String.to_list(t)
  +de = {Regex.Cat{Regex.All{}, Regex.Eps{}}: Regex.Re<Spec.Atom>}
  +x = Regex.Re.step(~Char, ~Spec.Atom, ~Spec.Atom.hit, de, Chr{47})
  r = Regex.Re.matches(~Char, ~Spec.Atom, ~Spec.Atom.hit, w, Regex.Cat{Regex.Void{}, x})
  %Regex.Re.alt_or(
    ~Char,
    ~Spec.Atom,
    ~Spec.Atom.hit,
    w,
    Regex.Cat{Regex.Eps{}, de},
    Regex.Cat{Regex.Void{}, x}
  ): {True{} == _: Bool}
  %Regex.Re.cat_eps_l(~Char, ~Spec.Atom, ~Spec.Atom.hit, w, de): {True{} == Bool.or(_, r): Bool}
  %Regex.Re.cat_eps_r(
    ~Char,
    ~Spec.Atom,
    ~Spec.Atom.hit,
    w,
    Regex.All{}
  ): {True{} == Bool.or(_, r): Bool}
  %Glob.deep_true(t): {True{} == Bool.or(_, r): Bool}
  {==}

# Show.star_k, one step, given b, the answer of c == '/'
# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- a false positive, as the rule notes: the other use is an erased argument (of Equal.sym or a motive)
def Show.star_k.at(
  c: Char,
  +t: String,
  b: Bool,
  ih: {
    True{}
      == Spec.Glob.matches(
        t,
        Spec.Cat{
          Spec.Star{},
          Spec.Cat{
            Spec.Alt{
              Spec.Eps{},
              Spec.Alt{Spec.Cat{Spec.Lit{Chr{47}}, Spec.Cat{Spec.Deep{}, Spec.Eps{}}}, Spec.Void{}}
            },
            Spec.Eps{}
          }
        }
      ): Bool
  }
) -> {
  b == Char.is_eq(c, Chr{47}): Bool
} -> {
  True{}
    == Spec.Glob.matches(
      SCon{c, t},
      Spec.Cat{
        Spec.Star{},
        Spec.Cat{
          Spec.Alt{
            Spec.Eps{},
            Spec.Alt{Spec.Cat{Spec.Lit{Chr{47}}, Spec.Cat{Spec.Deep{}, Spec.Eps{}}}, Spec.Void{}}
          },
          Spec.Eps{}
        }
      }
    ): Bool
}:
  match b:
    case False{}:
      e =>
        +w = String.to_list(t)
        +star = Spec.Glob.re(Spec.Star{})
        +ke = Spec.Glob.re(
          Spec.Cat{
            Spec.Alt{
              Spec.Eps{},
              Spec.Alt{Spec.Cat{Spec.Lit{Chr{47}}, Spec.Cat{Spec.Deep{}, Spec.Eps{}}}, Spec.Void{}}
            },
            Spec.Eps{}
          }
        )
        +x = {
          Regex.Cat{
            Regex.Eps{},
            Regex.Re.step(~Char, ~Spec.Atom, ~Spec.Atom.hit, ke, c)
          }: Regex.Re<Spec.Atom>
        }
        r = Regex.Re.matches(~Char, ~Spec.Atom, ~Spec.Atom.hit, w, x)
        %e: {
          True{}
            == Regex.Re.matches(
              ~Char,
              ~Spec.Atom,
              ~Spec.Atom.hit,
              w,
              Regex.Alt{Regex.Cat{Regex.Cat{Regex.Re.of_bool(Spec.Atom, Bool.not(_)), star}, ke}, x}
            ): Bool
        }
        %Regex.Re.alt_or(
          ~Char,
          ~Spec.Atom,
          ~Spec.Atom.hit,
          w,
          Regex.Cat{Regex.Cat{Regex.Eps{}, star}, ke},
          x
        ): {True{} == _: Bool}
        %Regex.Re.cat_assoc(
          ~Char,
          ~Spec.Atom,
          ~Spec.Atom.hit,
          w,
          Regex.Eps{},
          star,
          ke
        ): {True{} == Bool.or(_, r): Bool}
        %Regex.Re.cat_eps_l(
          ~Char,
          ~Spec.Atom,
          ~Spec.Atom.hit,
          w,
          Regex.Cat{star, ke}
        ): {True{} == Bool.or(_, r): Bool}
        %ih: {True{} == Bool.or(_, r): Bool}
        {==}
    case True{}:
      e =>
        +dirs = {
          Spec.Alt{
            Spec.Eps{},
            Spec.Alt{Spec.Cat{Spec.Lit{Chr{47}}, Spec.Cat{Spec.Deep{}, Spec.Eps{}}}, Spec.Void{}}
          }: Spec.Glob
        }
        +ec = Shared.Char.is_eq_sound(
          c,
          Chr{47}
        )(Equal.sym(Bool, True{}, Char.is_eq(c, Chr{47}), e))
        %Equal.sym(
          Char,
          c,
          Chr{47},
          ec
        ): {
          True{}
            == Spec.Glob.matches(
              SCon{_, t},
              Spec.Cat{Spec.Star{}, Spec.Cat{dirs, Spec.Eps{}}}
            ): Bool
        }
        +w = String.to_list(t)
        +p = {SCon{Chr{47}, t}: String}
        +ke = Spec.Glob.re(Spec.Cat{dirs, Spec.Eps{}})
        +st = {
          Regex.Cat{Regex.Cat{Regex.Void{}, Spec.Glob.re(Spec.Star{})}, ke}: Regex.Re<Spec.Atom>
        }
        +x = Regex.Re.step(~Char, ~Spec.Atom, ~Spec.Atom.hit, ke, Chr{47})
        +ms = Regex.Re.matches(~Char, ~Spec.Atom, ~Spec.Atom.hit, w, st)
        %Regex.Re.alt_or(
          ~Char,
          ~Spec.Atom,
          ~Spec.Atom.hit,
          w,
          st,
          Regex.Cat{Regex.Eps{}, x}
        ): {True{} == _: Bool}
        %Regex.Re.cat_eps_l(
          ~Char,
          ~Spec.Atom,
          ~Spec.Atom.hit,
          w,
          x
        ): {True{} == Bool.or(ms, _): Bool}
        %Glob.cat_eps_r(p, dirs): {True{} == Bool.or(ms, _): Bool}
        %Glob.alt_or(
          p,
          Spec.Eps{},
          Spec.Alt{Spec.Cat{Spec.Lit{Chr{47}}, Spec.Cat{Spec.Deep{}, Spec.Eps{}}}, Spec.Void{}}
        ): {True{} == Bool.or(ms, _): Bool}
        %Glob.alt_void(
          p,
          Spec.Cat{Spec.Lit{Chr{47}}, Spec.Cat{Spec.Deep{}, Spec.Eps{}}}
        ): {True{} == Bool.or(ms, Bool.or(Spec.Glob.matches(p, Spec.Eps{}), _)): Bool}
        %Show.slash_deep(
          t
        ): {True{} == Bool.or(ms, Bool.or(Spec.Glob.matches(p, Spec.Eps{}), _)): Bool}
        %Equal.sym(
          Bool,
          Bool.or(Spec.Glob.matches(p, Spec.Eps{}), True{}),
          True{},
          Shared.Bool.or_true_right(Spec.Glob.matches(p, Spec.Eps{}))
        ): {True{} == Bool.or(ms, _): Bool}
        Equal.sym(Bool, Bool.or(ms, True{}), True{}, Shared.Bool.or_true_right(ms))
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# `*` then optionally `/` and anything matches everything
def Show.star_k(
  p: String
) -> {
  True{}
    == Spec.Glob.matches(
      p,
      Spec.Cat{
        Spec.Star{},
        Spec.Cat{
          Spec.Alt{
            Spec.Eps{},
            Spec.Alt{Spec.Cat{Spec.Lit{Chr{47}}, Spec.Cat{Spec.Deep{}, Spec.Eps{}}}, Spec.Void{}}
          },
          Spec.Eps{}
        }
      }
    ): Bool
}:
  match p:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      Show.star_k.at(c, t, Char.is_eq(c, Chr{47}), Show.star_k(t))({==})

# the text of Deep reads back as Deep
def Show.deep_point(
  +p: String
) -> {Spec.Glob.matches(p, Show.deep()) == Spec.Glob.matches(p, Spec.Deep{}): Bool}:
  %Glob.alt_void(
    p,
    Spec.Cat{
      Spec.Star{},
      Spec.Cat{
        Spec.Alt{
          Spec.Eps{},
          Spec.Alt{Spec.Cat{Spec.Lit{Chr{47}}, Spec.Cat{Spec.Deep{}, Spec.Eps{}}}, Spec.Void{}}
        },
        Spec.Eps{}
      }
    }
  ): {_ == Spec.Glob.matches(p, Spec.Deep{}): Bool}
  %Show.star_k(p): {_ == Spec.Glob.matches(p, Spec.Deep{}): Bool}
  Glob.deep_true(p)

# the facts Show.ok gives about g at rank: 0, Show.glob(g) and g agree on suf;
# 1, they agree on pre and each longer prefix within suf; 2, on each suffix
def Show.Ok(+g: Spec.Glob, rank: Nat, suf: String, pre: String) -> Type:
  match rank:
    case 0n:
      {Spec.Glob.matches(suf, Show.glob(g)) == Spec.Glob.matches(suf, g): Bool}
    case 1n+k:
      match k:
        case 0n:
          Regex.Re.AgreePre(
            ~Char,
            ~Spec.Atom,
            ~Spec.Atom.hit,
            Spec.Glob.re(Show.glob(g)),
            Spec.Glob.re(g),
            String.to_list(pre),
            String.to_list(suf)
          )
        case 1n+j:
          match j:
            case 0n:
              Regex.Re.AgreeSuf(
                ~Char,
                ~Spec.Atom,
                ~Spec.Atom.hit,
                Spec.Glob.re(Show.glob(g)),
                Spec.Glob.re(g),
                String.to_list(suf)
              )
            case 1n+i:
              Unit

# Show.glob(g) matches what g matches. One def gives all three ranks, so the
# Cat case can ask for its parts' agreement chains as often as it needs.
# bend-lint: expect-begin bend-lint-rules/performance/append_in_loop@warning -- only proofs use it; no program runs it
# bend-lint: expect-begin bend-lint-rules/performance/missed_fork@hint -- only proofs use it; no program runs it
def Show.ok(+g: Spec.Glob, +rank: Nat, +suf: String, +pre: String) -> Show.Ok(g, rank, suf, pre):
  match g rank:
    case Spec.Void{} 0n:
      Show.void_point(suf)
    case Spec.Eps{} 0n:
      Show.eps_point(suf)
    case Spec.Lit{c} 0n:
      {==}
    case Spec.Any{} 0n:
      {==}
    case Spec.Star{} 0n:
      Show.star_point(suf)
    case Spec.Class{+n, +cs} 0n:
      Show.class_point(suf, n, cs)
    case Spec.Deep{} 0n:
      Show.deep_point(suf)
    case Spec.Cat{+a, +b} 0n:
      +ta = Show.glob(a)
      +tb = Show.glob(b)
      r = Spec.Glob.matches(suf, Spec.Cat{a, b})
      %Glob.alt_void(suf, Spec.Cat{ta, Spec.Cat{tb, Spec.Eps{}}}): {_ == r: Bool}
      %Equal.sym(
        Bool,
        Spec.Glob.matches(suf, Spec.Cat{ta, Spec.Cat{tb, Spec.Eps{}}}),
        Spec.Glob.matches(suf, Spec.Cat{Spec.Cat{ta, tb}, Spec.Eps{}}),
        Regex.Re.cat_assoc(
          ~Char,
          ~Spec.Atom,
          ~Spec.Atom.hit,
          String.to_list(suf),
          Spec.Glob.re(ta),
          Spec.Glob.re(tb),
          Regex.Eps{}
        )
      ): {_ == r: Bool}
      %Glob.cat_eps_r(suf, Spec.Cat{ta, tb}): {_ == r: Bool}
      Regex.Re.cat_agree(
        ~Char,
        ~Spec.Atom,
        ~Spec.Atom.hit,
        String.to_list(suf),
        Spec.Glob.re(ta),
        Spec.Glob.re(a),
        Spec.Glob.re(tb),
        Spec.Glob.re(b),
        Show.ok(a, 1n, suf, SNil{}),
        Show.ok(b, 2n, suf, SNil{})
      )
    case Spec.Alt{+a, +b} 0n:
      +ta = Show.glob(a)
      +tb = Show.glob(b)
      r = Spec.Glob.matches(suf, Spec.Alt{a, b})
      ma = Spec.Glob.matches(suf, ta)
      mb = Spec.Glob.matches(suf, tb)
      %Glob.alt_or(
        suf,
        Spec.Cat{ta, Spec.Eps{}},
        Spec.Alt{Spec.Cat{tb, Spec.Eps{}}, Spec.Void{}}
      ): {_ == r: Bool}
      %Glob.alt_void(
        suf,
        Spec.Cat{tb, Spec.Eps{}}
      ): {Bool.or(Spec.Glob.matches(suf, Spec.Cat{ta, Spec.Eps{}}), _) == r: Bool}
      %Glob.cat_eps_r(
        suf,
        ta
      ): {Bool.or(_, Spec.Glob.matches(suf, Spec.Cat{tb, Spec.Eps{}})) == r: Bool}
      %Glob.cat_eps_r(suf, tb): {Bool.or(ma, _) == r: Bool}
      %Glob.alt_or(suf, a, b): {Bool.or(ma, mb) == _: Bool}
      %Show.ok(a, 0n, suf, SNil{}): {Bool.or(ma, mb) == Bool.or(_, Spec.Glob.matches(suf, b)): Bool}
      %Show.ok(b, 0n, suf, SNil{}): {Bool.or(ma, mb) == Bool.or(ma, _): Bool}
      {==}
    case _ 1n+k:
      match k:
        case 0n:
          match suf:
            case SNil{}:
              Show.ok(g, 0n, pre, SNil{})
            case SCon{c, t}:
              %Texts.String.to_list_append(
                pre,
                SCon{c, SNil{}}
              ): (
                {
                  Spec.Glob.matches(pre, Show.glob(g)) == Spec.Glob.matches(pre, g): Bool
                }
                  & Regex.Re.AgreePre(
                    ~Char,
                    ~Spec.Atom,
                    ~Spec.Atom.hit,
                    Spec.Glob.re(Show.glob(g)),
                    Spec.Glob.re(g),
                    _,
                    String.to_list(t)
                  )
              )
              (Show.ok(g, 0n, pre, SNil{}), Show.ok(g, 1n, t, String.append(pre, SCon{c, SNil{}})))
        case 1n+j:
          match j:
            case 0n:
              match suf:
                case SNil{}:
                  Show.ok(g, 0n, SNil{}, pre)
                case SCon{c, +t}:
                  (Show.ok(g, 0n, SCon{c, t}, pre), Show.ok(g, 2n, t, pre))
            case 1n+i:
              Unit{}
# bend-lint: expect-end bend-lint-rules/performance/append_in_loop@warning
# bend-lint: expect-end bend-lint-rules/performance/missed_fork@hint

# the text of Lit{c} reads back, given k, the role of c
def Show.read_lit(
  +c: Char,
  k: Spec.Sym
) -> {
  k == Spec.Sym.of(c): Spec.Sym
} -> {
  Some{
    Spec.Cat{Spec.Lit{c}, Spec.Eps{}}
  }
    == Spec.Glob.read.syms(Spec.Sym.list(Glob.show.char(c, k, ""))): Maybe<&2, Spec.Glob>
}:
  match k:
    case Spec.SChar{x}:
      +e =>
        +tgt = {Some{Spec.Cat{Spec.Lit{c}, Spec.Eps{}}}: Maybe<&2, Spec.Glob>}
        %e: {tgt == Spec.Glob.read.syms(Con{_, Nil{}}): Maybe<&2, Spec.Glob>}
        %Sym.char_is(
          c,
          Spec.SChar{x},
          e
        ): {tgt == Some{Spec.Cat{Spec.Lit{_}, Spec.Eps{}}}: Maybe<&2, Spec.Glob>}
        {==}
    case Spec.SEsc{}:
      e =>
        +tgt = {Some{Spec.Cat{Spec.Lit{c}, Spec.Eps{}}}: Maybe<&2, Spec.Glob>}
        +f = {[Spec.Frame{[], [], True{}}]: List<&2, Spec.Frame>}
        %Step.esc(Spec.Sym.of(c), Nil{}, f, True{}): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(c): {tgt == Some{Spec.Cat{Spec.Lit{_}, Spec.Eps{}}}: Maybe<&2, Spec.Glob>}
        {==}
    case Spec.SAny{}:
      e =>
        +tgt = {Some{Spec.Cat{Spec.Lit{c}, Spec.Eps{}}}: Maybe<&2, Spec.Glob>}
        +f = {[Spec.Frame{[], [], True{}}]: List<&2, Spec.Frame>}
        %Step.esc(Spec.Sym.of(c), Nil{}, f, True{}): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(c): {tgt == Some{Spec.Cat{Spec.Lit{_}, Spec.Eps{}}}: Maybe<&2, Spec.Glob>}
        {==}
    case Spec.SStar{}:
      e =>
        +tgt = {Some{Spec.Cat{Spec.Lit{c}, Spec.Eps{}}}: Maybe<&2, Spec.Glob>}
        +f = {[Spec.Frame{[], [], True{}}]: List<&2, Spec.Frame>}
        %Step.esc(Spec.Sym.of(c), Nil{}, f, True{}): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(c): {tgt == Some{Spec.Cat{Spec.Lit{_}, Spec.Eps{}}}: Maybe<&2, Spec.Glob>}
        {==}
    case Spec.SSlash{}:
      e =>
        +tgt = {Some{Spec.Cat{Spec.Lit{c}, Spec.Eps{}}}: Maybe<&2, Spec.Glob>}
        +f = {[Spec.Frame{[], [], True{}}]: List<&2, Spec.Frame>}
        %Step.esc(Spec.Sym.of(c), Nil{}, f, True{}): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(c): {tgt == Some{Spec.Cat{Spec.Lit{_}, Spec.Eps{}}}: Maybe<&2, Spec.Glob>}
        {==}
    case Spec.SOpen{}:
      e =>
        +tgt = {Some{Spec.Cat{Spec.Lit{c}, Spec.Eps{}}}: Maybe<&2, Spec.Glob>}
        +f = {[Spec.Frame{[], [], True{}}]: List<&2, Spec.Frame>}
        %Step.esc(Spec.Sym.of(c), Nil{}, f, True{}): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(c): {tgt == Some{Spec.Cat{Spec.Lit{_}, Spec.Eps{}}}: Maybe<&2, Spec.Glob>}
        {==}
    case Spec.SComma{}:
      e =>
        +tgt = {Some{Spec.Cat{Spec.Lit{c}, Spec.Eps{}}}: Maybe<&2, Spec.Glob>}
        +f = {[Spec.Frame{[], [], True{}}]: List<&2, Spec.Frame>}
        %Step.esc(Spec.Sym.of(c), Nil{}, f, True{}): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(c): {tgt == Some{Spec.Cat{Spec.Lit{_}, Spec.Eps{}}}: Maybe<&2, Spec.Glob>}
        {==}
    case Spec.SClose{}:
      e =>
        +tgt = {Some{Spec.Cat{Spec.Lit{c}, Spec.Eps{}}}: Maybe<&2, Spec.Glob>}
        +f = {[Spec.Frame{[], [], True{}}]: List<&2, Spec.Frame>}
        %Step.esc(Spec.Sym.of(c), Nil{}, f, True{}): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(c): {tgt == Some{Spec.Cat{Spec.Lit{_}, Spec.Eps{}}}: Maybe<&2, Spec.Glob>}
        {==}
    case Spec.SLeft{}:
      e =>
        +tgt = {Some{Spec.Cat{Spec.Lit{c}, Spec.Eps{}}}: Maybe<&2, Spec.Glob>}
        +f = {[Spec.Frame{[], [], True{}}]: List<&2, Spec.Frame>}
        %Step.esc(Spec.Sym.of(c), Nil{}, f, True{}): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(c): {tgt == Some{Spec.Cat{Spec.Lit{_}, Spec.Eps{}}}: Maybe<&2, Spec.Glob>}
        {==}
    case Spec.SRight{}:
      e =>
        +tgt = {Some{Spec.Cat{Spec.Lit{c}, Spec.Eps{}}}: Maybe<&2, Spec.Glob>}
        +f = {[Spec.Frame{[], [], True{}}]: List<&2, Spec.Frame>}
        %Step.esc(Spec.Sym.of(c), Nil{}, f, True{}): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(c): {tgt == Some{Spec.Cat{Spec.Lit{_}, Spec.Eps{}}}: Maybe<&2, Spec.Glob>}
        {==}
    case Spec.SBang{}:
      e =>
        +tgt = {Some{Spec.Cat{Spec.Lit{c}, Spec.Eps{}}}: Maybe<&2, Spec.Glob>}
        +f = {[Spec.Frame{[], [], True{}}]: List<&2, Spec.Frame>}
        %Step.esc(Spec.Sym.of(c), Nil{}, f, True{}): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(c): {tgt == Some{Spec.Cat{Spec.Lit{_}, Spec.Eps{}}}: Maybe<&2, Spec.Glob>}
        {==}
    case Spec.SDash{}:
      e =>
        +tgt = {Some{Spec.Cat{Spec.Lit{c}, Spec.Eps{}}}: Maybe<&2, Spec.Glob>}
        +f = {[Spec.Frame{[], [], True{}}]: List<&2, Spec.Frame>}
        %Step.esc(Spec.Sym.of(c), Nil{}, f, True{}): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(c): {tgt == Some{Spec.Cat{Spec.Lit{_}, Spec.Eps{}}}: Maybe<&2, Spec.Glob>}
        {==}

# the text of g reads back as Show.glob(g)
def Show.read(
  g: Spec.Glob
) -> {
  Some{
    Spec.Cat{Show.glob(g), Spec.Eps{}}
  }
    == Spec.Glob.read(Spec.Glob.show(g)): Maybe<&2, Spec.Glob>
}:
  match g:
    case Spec.Void{}:
      Show.parse(Spec.Void{}, "", [], [], True{}, [], True{})
    case Spec.Eps{}:
      Show.parse(Spec.Eps{}, "", [], [], True{}, [], True{})
    case Spec.Any{}:
      Show.parse(Spec.Any{}, "", [], [], True{}, [], True{})
    case Spec.Star{}:
      Show.parse(Spec.Star{}, "", [], [], True{}, [], True{})
    case Spec.Class{n, cs}:
      Show.parse(Spec.Class{n, cs}, "", [], [], True{}, [], True{})
    case Spec.Deep{}:
      Show.parse(Spec.Deep{}, "", [], [], True{}, [], True{})
    case Spec.Cat{x, y}:
      Show.parse(Spec.Cat{x, y}, "", [], [], True{}, [], True{})
    case Spec.Alt{x, y}:
      Show.parse(Spec.Alt{x, y}, "", [], [], True{}, [], True{})
    case Spec.Lit{+c}:
      Show.read_lit(c, Spec.Sym.of(c))({==})

# g matches what the glob its text reads back as matches
def Show.same(
  +g: Spec.Glob,
  +p: String
) -> {Spec.Glob.matches(p, g) == Spec.Glob.matches(p, Spec.Cat{Show.glob(g), Spec.Eps{}}): Bool}:
  %Glob.cat_eps_r(p, Show.glob(g)): {Spec.Glob.matches(p, g) == _: Bool}
  Equal.sym(
    Bool,
    Spec.Glob.matches(p, Show.glob(g)),
    Spec.Glob.matches(p, g),
    Show.ok(g, 0n, p, SNil{})
  )

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- a false positive, as the rule notes: the other use is an erased argument (of Equal.sym or a motive)
def Spec.read_after_show(g):
  +g = g
  h = {Spec.Cat{Show.glob(g), Spec.Eps{}}: Spec.Glob}
  read = Equal.sym(Maybe<&2, Spec.Glob>, Some{h}, Spec.Glob.read(Spec.Glob.show(g)), Show.read(g))
  (h, (read, p => Show.same(g, p)))
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
def Spec.read_rejects_root(s):
  {==}

# Escaped paths
# -------------

# the text of c in an escaped path: a character with a role is escaped,
# except '/', which stays a separator
def Glob.escape.char(c: Char, k: Spec.Sym, rest: String) -> String:
  match k:
    case Spec.SChar{x}:
      SCon{c, rest}
    case Spec.SSlash{}:
      SCon{c, rest}
    case _:
      SCon{Chr{92}, SCon{c, rest}}

def Spec.Glob.escape(p):
  match p:
    case SNil{}:
      SNil{}
    case SCon{+c, t}:
      Glob.escape.char(c, Spec.Sym.of(c), Spec.Glob.escape(t))

# the glob of exactly the text p
def Glob.lits(p: String) -> Spec.Glob:
  match p:
    case SNil{}:
      Spec.Eps{}
    case SCon{c, t}:
      Spec.Cat{Spec.Lit{c}, Glob.lits(t)}

# Esc.parse, one character c, given k, the role of c
def Esc.parse_at(
  +c: Char,
  +t: String,
  k: Spec.Sym,
  +s: List<&2, Spec.Glob>,
  seg: Bool,
  ih: @s2: List<
    &2,
    Spec.Glob> -> @seg2: Bool -> {
    Some{
      Spec.Glob.of_seq(s2, Glob.lits(t))
    }
      == Spec.Glob.read.go(
        Spec.Sym.list(Spec.Glob.escape(t)),
        Spec.Out{},
        [Spec.Frame{[], s2, True{}}],
        seg2
      ): Maybe<&2, Spec.Glob>
  }
) -> {
  k == Spec.Sym.of(c): Spec.Sym
} -> {
  Some{
    Spec.Glob.of_seq(s, Spec.Cat{Spec.Lit{c}, Glob.lits(t)})
  }
    == Spec.Glob.read.go(
      Spec.Sym.list(Glob.escape.char(c, k, Spec.Glob.escape(t))),
      Spec.Out{},
      [Spec.Frame{[], s, True{}}],
      seg
    ): Maybe<&2, Spec.Glob>
}:
  match k:
    case Spec.SChar{+x}:
      +e =>
        +l = Spec.Sym.list(Spec.Glob.escape(t))
        +f = {[Spec.Frame{[], s, True{}}]: List<&2, Spec.Frame>}
        +tgt = {
          Some{Spec.Glob.of_seq(s, Spec.Cat{Spec.Lit{c}, Glob.lits(t)})}: Maybe<&2, Spec.Glob>
        }
        %e: {tgt == Spec.Glob.read.go(Con{_, l}, Spec.Out{}, f, seg): Maybe<&2, Spec.Glob>}
        %Step.char(x, l, f, seg): {tgt == _: Maybe<&2, Spec.Glob>}
        %ih(Con{Spec.Lit{x}, s}, False{}): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_is(
          c,
          Spec.SChar{x},
          e
        ): {
          tgt
            == Some{Spec.Glob.of_seq(s, Spec.Cat{Spec.Lit{_}, Glob.lits(t)})}: Maybe<&2, Spec.Glob>
        }
        {==}
    case Spec.SSlash{}:
      +e =>
        +l = Spec.Sym.list(Spec.Glob.escape(t))
        +f = {[Spec.Frame{[], s, True{}}]: List<&2, Spec.Frame>}
        +tgt = {
          Some{Spec.Glob.of_seq(s, Spec.Cat{Spec.Lit{c}, Glob.lits(t)})}: Maybe<&2, Spec.Glob>
        }
        %e: {tgt == Spec.Glob.read.go(Con{_, l}, Spec.Out{}, f, seg): Maybe<&2, Spec.Glob>}
        %Step.slash(l, f, seg): {tgt == _: Maybe<&2, Spec.Glob>}
        %ih(Con{Spec.Lit{Chr{47}}, s}, True{}): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_is(
          c,
          Spec.SSlash{},
          e
        ): {
          tgt
            == Some{Spec.Glob.of_seq(s, Spec.Cat{Spec.Lit{_}, Glob.lits(t)})}: Maybe<&2, Spec.Glob>
        }
        {==}
    case Spec.SEsc{}:
      e =>
        +l = Spec.Sym.list(Spec.Glob.escape(t))
        +f = {[Spec.Frame{[], s, True{}}]: List<&2, Spec.Frame>}
        +tgt = {
          Some{Spec.Glob.of_seq(s, Spec.Cat{Spec.Lit{c}, Glob.lits(t)})}: Maybe<&2, Spec.Glob>
        }
        %Step.esc(Spec.Sym.of(c), l, f, seg): {tgt == _: Maybe<&2, Spec.Glob>}
        %ih(
          Con{Spec.Lit{Spec.Sym.char(Spec.Sym.of(c))}, s},
          False{}
        ): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(
          c
        ): {
          tgt
            == Some{Spec.Glob.of_seq(s, Spec.Cat{Spec.Lit{_}, Glob.lits(t)})}: Maybe<&2, Spec.Glob>
        }
        {==}
    case Spec.SAny{}:
      e =>
        +l = Spec.Sym.list(Spec.Glob.escape(t))
        +f = {[Spec.Frame{[], s, True{}}]: List<&2, Spec.Frame>}
        +tgt = {
          Some{Spec.Glob.of_seq(s, Spec.Cat{Spec.Lit{c}, Glob.lits(t)})}: Maybe<&2, Spec.Glob>
        }
        %Step.esc(Spec.Sym.of(c), l, f, seg): {tgt == _: Maybe<&2, Spec.Glob>}
        %ih(
          Con{Spec.Lit{Spec.Sym.char(Spec.Sym.of(c))}, s},
          False{}
        ): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(
          c
        ): {
          tgt
            == Some{Spec.Glob.of_seq(s, Spec.Cat{Spec.Lit{_}, Glob.lits(t)})}: Maybe<&2, Spec.Glob>
        }
        {==}
    case Spec.SStar{}:
      e =>
        +l = Spec.Sym.list(Spec.Glob.escape(t))
        +f = {[Spec.Frame{[], s, True{}}]: List<&2, Spec.Frame>}
        +tgt = {
          Some{Spec.Glob.of_seq(s, Spec.Cat{Spec.Lit{c}, Glob.lits(t)})}: Maybe<&2, Spec.Glob>
        }
        %Step.esc(Spec.Sym.of(c), l, f, seg): {tgt == _: Maybe<&2, Spec.Glob>}
        %ih(
          Con{Spec.Lit{Spec.Sym.char(Spec.Sym.of(c))}, s},
          False{}
        ): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(
          c
        ): {
          tgt
            == Some{Spec.Glob.of_seq(s, Spec.Cat{Spec.Lit{_}, Glob.lits(t)})}: Maybe<&2, Spec.Glob>
        }
        {==}
    case Spec.SOpen{}:
      e =>
        +l = Spec.Sym.list(Spec.Glob.escape(t))
        +f = {[Spec.Frame{[], s, True{}}]: List<&2, Spec.Frame>}
        +tgt = {
          Some{Spec.Glob.of_seq(s, Spec.Cat{Spec.Lit{c}, Glob.lits(t)})}: Maybe<&2, Spec.Glob>
        }
        %Step.esc(Spec.Sym.of(c), l, f, seg): {tgt == _: Maybe<&2, Spec.Glob>}
        %ih(
          Con{Spec.Lit{Spec.Sym.char(Spec.Sym.of(c))}, s},
          False{}
        ): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(
          c
        ): {
          tgt
            == Some{Spec.Glob.of_seq(s, Spec.Cat{Spec.Lit{_}, Glob.lits(t)})}: Maybe<&2, Spec.Glob>
        }
        {==}
    case Spec.SComma{}:
      e =>
        +l = Spec.Sym.list(Spec.Glob.escape(t))
        +f = {[Spec.Frame{[], s, True{}}]: List<&2, Spec.Frame>}
        +tgt = {
          Some{Spec.Glob.of_seq(s, Spec.Cat{Spec.Lit{c}, Glob.lits(t)})}: Maybe<&2, Spec.Glob>
        }
        %Step.esc(Spec.Sym.of(c), l, f, seg): {tgt == _: Maybe<&2, Spec.Glob>}
        %ih(
          Con{Spec.Lit{Spec.Sym.char(Spec.Sym.of(c))}, s},
          False{}
        ): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(
          c
        ): {
          tgt
            == Some{Spec.Glob.of_seq(s, Spec.Cat{Spec.Lit{_}, Glob.lits(t)})}: Maybe<&2, Spec.Glob>
        }
        {==}
    case Spec.SClose{}:
      e =>
        +l = Spec.Sym.list(Spec.Glob.escape(t))
        +f = {[Spec.Frame{[], s, True{}}]: List<&2, Spec.Frame>}
        +tgt = {
          Some{Spec.Glob.of_seq(s, Spec.Cat{Spec.Lit{c}, Glob.lits(t)})}: Maybe<&2, Spec.Glob>
        }
        %Step.esc(Spec.Sym.of(c), l, f, seg): {tgt == _: Maybe<&2, Spec.Glob>}
        %ih(
          Con{Spec.Lit{Spec.Sym.char(Spec.Sym.of(c))}, s},
          False{}
        ): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(
          c
        ): {
          tgt
            == Some{Spec.Glob.of_seq(s, Spec.Cat{Spec.Lit{_}, Glob.lits(t)})}: Maybe<&2, Spec.Glob>
        }
        {==}
    case Spec.SLeft{}:
      e =>
        +l = Spec.Sym.list(Spec.Glob.escape(t))
        +f = {[Spec.Frame{[], s, True{}}]: List<&2, Spec.Frame>}
        +tgt = {
          Some{Spec.Glob.of_seq(s, Spec.Cat{Spec.Lit{c}, Glob.lits(t)})}: Maybe<&2, Spec.Glob>
        }
        %Step.esc(Spec.Sym.of(c), l, f, seg): {tgt == _: Maybe<&2, Spec.Glob>}
        %ih(
          Con{Spec.Lit{Spec.Sym.char(Spec.Sym.of(c))}, s},
          False{}
        ): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(
          c
        ): {
          tgt
            == Some{Spec.Glob.of_seq(s, Spec.Cat{Spec.Lit{_}, Glob.lits(t)})}: Maybe<&2, Spec.Glob>
        }
        {==}
    case Spec.SRight{}:
      e =>
        +l = Spec.Sym.list(Spec.Glob.escape(t))
        +f = {[Spec.Frame{[], s, True{}}]: List<&2, Spec.Frame>}
        +tgt = {
          Some{Spec.Glob.of_seq(s, Spec.Cat{Spec.Lit{c}, Glob.lits(t)})}: Maybe<&2, Spec.Glob>
        }
        %Step.esc(Spec.Sym.of(c), l, f, seg): {tgt == _: Maybe<&2, Spec.Glob>}
        %ih(
          Con{Spec.Lit{Spec.Sym.char(Spec.Sym.of(c))}, s},
          False{}
        ): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(
          c
        ): {
          tgt
            == Some{Spec.Glob.of_seq(s, Spec.Cat{Spec.Lit{_}, Glob.lits(t)})}: Maybe<&2, Spec.Glob>
        }
        {==}
    case Spec.SBang{}:
      e =>
        +l = Spec.Sym.list(Spec.Glob.escape(t))
        +f = {[Spec.Frame{[], s, True{}}]: List<&2, Spec.Frame>}
        +tgt = {
          Some{Spec.Glob.of_seq(s, Spec.Cat{Spec.Lit{c}, Glob.lits(t)})}: Maybe<&2, Spec.Glob>
        }
        %Step.esc(Spec.Sym.of(c), l, f, seg): {tgt == _: Maybe<&2, Spec.Glob>}
        %ih(
          Con{Spec.Lit{Spec.Sym.char(Spec.Sym.of(c))}, s},
          False{}
        ): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(
          c
        ): {
          tgt
            == Some{Spec.Glob.of_seq(s, Spec.Cat{Spec.Lit{_}, Glob.lits(t)})}: Maybe<&2, Spec.Glob>
        }
        {==}
    case Spec.SDash{}:
      e =>
        +l = Spec.Sym.list(Spec.Glob.escape(t))
        +f = {[Spec.Frame{[], s, True{}}]: List<&2, Spec.Frame>}
        +tgt = {
          Some{Spec.Glob.of_seq(s, Spec.Cat{Spec.Lit{c}, Glob.lits(t)})}: Maybe<&2, Spec.Glob>
        }
        %Step.esc(Spec.Sym.of(c), l, f, seg): {tgt == _: Maybe<&2, Spec.Glob>}
        %ih(
          Con{Spec.Lit{Spec.Sym.char(Spec.Sym.of(c))}, s},
          False{}
        ): {tgt == _: Maybe<&2, Spec.Glob>}
        %Sym.char_of(
          c
        ): {
          tgt
            == Some{Spec.Glob.of_seq(s, Spec.Cat{Spec.Lit{_}, Glob.lits(t)})}: Maybe<&2, Spec.Glob>
        }
        {==}

# the escaped text of p, after the atoms s, reads back as s then the Lits of p
def Esc.parse(
  p: String,
  s: List<&2, Spec.Glob>,
  seg: Bool
) -> {
  Some{
    Spec.Glob.of_seq(s, Glob.lits(p))
  }
    == Spec.Glob.read.go(
      Spec.Sym.list(Spec.Glob.escape(p)),
      Spec.Out{},
      [Spec.Frame{[], s, True{}}],
      seg
    ): Maybe<&2, Spec.Glob>
}:
  match p:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      Esc.parse_at(c, t, Spec.Sym.of(c), s, seg, s2 => seg2 => Esc.parse(t, s2, seg2))({==})

# syms start with '/'
def Sym.starts_slash(syms: List<&2, Spec.Sym>) -> Bool:
  match syms:
    case Con{Spec.SSlash{}, t}:
      True{}
    case _:
      False{}

# text that does not start with '/' is read from a fresh frame
def Read.syms_go(
  syms: List<&2, Spec.Sym>
) -> {
  Sym.starts_slash(syms) == False{}: Bool
} -> {
  Spec.Glob.read.go(
    syms,
    Spec.Out{},
    [Spec.Frame{[], [], True{}}],
    True{}
  )
    == Spec.Glob.read.syms(syms): Maybe<&2, Spec.Glob>
}:
  match syms:
    case Nil{}:
      h => {==}
    case Con{y, l}:
      match y:
        case Spec.SEsc{}:
          h => {==}
        case Spec.SAny{}:
          h => {==}
        case Spec.SStar{}:
          h => {==}
        case Spec.SSlash{}:
          h => Empty.absurd(
            {
              Spec.Glob.read.go(
                Con{Spec.SSlash{}, l},
                Spec.Out{},
                [Spec.Frame{[], [], True{}}],
                True{}
              )
                == Spec.Glob.read.syms(Con{Spec.SSlash{}, l}): Maybe<&2, Spec.Glob>
            },
            Shared.Bool.true_ne_false(h)
          )
        case Spec.SOpen{}:
          h => {==}
        case Spec.SComma{}:
          h => {==}
        case Spec.SClose{}:
          h => {==}
        case Spec.SLeft{}:
          h => {==}
        case Spec.SRight{}:
          h => {==}
        case Spec.SBang{}:
          h => {==}
        case Spec.SDash{}:
          h => {==}
        case Spec.SChar{x}:
          h => {==}

# a text that starts with '/' is no valid path
def Esc.no_root.path(
  c: Char,
  t: String,
  ec: {Chr{47} == c: Char}
) -> {False{} == Spec.is_path(SCon{c, t}): Bool}:
  %ec: {False{} == Spec.is_path(SCon{_, t}): Bool}
  {==}

# no valid path starts with '/'
# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- a false positive, as the rule notes: the other use is an erased argument (of Equal.sym or a motive)
def Esc.no_root(
  c: Char,
  t: String,
  ec: {Chr{47} == c: Char},
  v: {Spec.is_path(SCon{c, t}) == True{}: Bool}
) -> Empty:
  Shared.Bool.false_ne_true(
    Equal.trans(Bool, False{}, Spec.is_path(SCon{c, t}), True{}, Esc.no_root.path(c, t, ec), v)
  )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# the escaped text of a valid path starting with c does not start with '/',
# given k, the role of c
def Esc.no_slash_at(
  +c: Char,
  t: String,
  k: Spec.Sym,
  v: {Spec.is_path(SCon{c, t}) == True{}: Bool}
) -> {
  k == Spec.Sym.of(c): Spec.Sym
} -> {
  Sym.starts_slash(Spec.Sym.list(Glob.escape.char(c, k, Spec.Glob.escape(t)))) == False{}: Bool
}:
  match k:
    case Spec.SEsc{}:
      e => {==}
    case Spec.SAny{}:
      e => {==}
    case Spec.SStar{}:
      e => {==}
    case Spec.SSlash{}:
      +e =>
        ec = Equal.sym(Char, c, Chr{47}, Sym.char_is(c, Spec.SSlash{}, e))
        Empty.absurd(
          {
            Sym.starts_slash(
              Spec.Sym.list(Glob.escape.char(c, Spec.SSlash{}, Spec.Glob.escape(t)))
            )
              == False{}: Bool
          },
          Esc.no_root(c, t, ec, v)
        )
    case Spec.SOpen{}:
      e => {==}
    case Spec.SComma{}:
      e => {==}
    case Spec.SClose{}:
      e => {==}
    case Spec.SLeft{}:
      e => {==}
    case Spec.SRight{}:
      e => {==}
    case Spec.SBang{}:
      e => {==}
    case Spec.SDash{}:
      e => {==}
    case Spec.SChar{x}:
      +e =>
        %e: {Sym.starts_slash(Con{_, Spec.Sym.list(Spec.Glob.escape(t))}) == False{}: Bool}
        {==}

# the escaped text of a valid path does not start with '/'
def Esc.no_slash(
  p: String,
  v: {Spec.is_path(p) == True{}: Bool}
) -> {Sym.starts_slash(Spec.Sym.list(Spec.Glob.escape(p))) == False{}: Bool}:
  match p:
    case SNil{}:
      Empty.absurd({False{} == False{}: Bool}, Shared.Bool.false_ne_true(v))
    case SCon{+c, t}:
      Esc.no_slash_at(c, t, Spec.Sym.of(c), v)({==})

# the escaped text of a valid path reads back as its Lits
def Esc.read(
  +p: String,
  v: {Spec.is_path(p) == True{}: Bool}
) -> {Some{Glob.lits(p)} == Spec.Glob.read(Spec.Glob.escape(p)): Maybe<&2, Spec.Glob>}:
  syms = Spec.Sym.list(Spec.Glob.escape(p))
  %Read.syms_go(syms)(Esc.no_slash(p, v)): {Some{Glob.lits(p)} == _: Maybe<&2, Spec.Glob>}
  Esc.parse(p, [], True{})

# one character of Lits.match
# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- only proofs use it; no program runs it
def Lits.cons(
  +dx: U32,
  +qt: String,
  +cx: U32,
  +pt: String,
  ih: {String.eq(qt, pt) == Spec.Glob.matches(qt, Glob.lits(pt)): Bool}
) -> {
  String.eq(
    SCon{Chr{dx}, qt},
    SCon{Chr{cx}, pt}
  )
    == Spec.Glob.matches(SCon{Chr{dx}, qt}, Glob.lits(SCon{Chr{cx}, pt})): Bool
}:
  +w = String.to_list(qt)
  +l = Spec.Glob.re(Glob.lits(pt))
  +e1 = Cmp.is_eq(U32.cmp(cx, dx))
  +x = Regex.Re.step(~Char, ~Spec.Atom, ~Spec.Atom.hit, l, Chr{dx})
  s = String.eq(SCon{Chr{dx}, qt}, SCon{Chr{cx}, pt})
  %Regex.Re.alt_or(
    ~Char,
    ~Spec.Atom,
    ~Spec.Atom.hit,
    w,
    Regex.Cat{Regex.Re.of_bool(Spec.Atom, e1), l},
    Regex.Cat{Regex.Void{}, x}
  ): {s == _: Bool}
  %Regex.Re.cat_of_bool(
    ~Char,
    ~Spec.Atom,
    ~Spec.Atom.hit,
    w,
    e1,
    l
  ): {
    s
      == Bool.or(
        _,
        Regex.Re.matches(~Char, ~Spec.Atom, ~Spec.Atom.hit, w, Regex.Cat{Regex.Void{}, x})
      ): Bool
  }
  %Regex.Re.cat_void_l(
    ~Char,
    ~Spec.Atom,
    ~Spec.Atom.hit,
    w,
    x
  ): {s == Bool.or(Bool.and(e1, Spec.Glob.matches(qt, Glob.lits(pt))), _): Bool}
  %Shared.Bool.or_false(Bool.and(e1, Spec.Glob.matches(qt, Glob.lits(pt)))): {s == _: Bool}
  %ih: {s == Bool.and(e1, _): Bool}
  Texts.String.eq_cons(cx, dx, qt, pt)
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the Lits of p match exactly p
def Lits.match(
  q: String,
  p: String
) -> {String.eq(q, p) == Spec.Glob.matches(q, Glob.lits(p)): Bool}:
  match q p:
    case SNil{} SNil{}:
      {==}
    case SCon{d, qt} SNil{}:
      Regex.Re.void_never(~Char, ~Spec.Atom, ~Spec.Atom.hit, String.to_list(qt))
    case SNil{} SCon{c, pt}:
      {==}
    case SCon{Chr{dx}, +qt} SCon{Chr{cx}, +pt}:
      Lits.cons(dx, qt, cx, pt, Lits.match(qt, pt))

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- a false positive, as the rule notes: the other use is an erased argument (of Equal.sym or a motive)
def Spec.read_after_escape(p, v):
  +p = p
  h = Glob.lits(p)
  read = Equal.sym(
    Maybe<&2, Spec.Glob>,
    Some{h},
    Spec.Glob.read(Spec.Glob.escape(p)),
    Esc.read(p, v)
  )
  (h, (read, q => Equal.sym(Bool, String.eq(q, p), Spec.Glob.matches(q, h), Lits.match(q, p))))
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
