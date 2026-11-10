import Base
import ../shared/shared/regex.bend as Regex
import ../shared/shared/search.bend as Searches
import ../shared/shared/shared/keyset.bend as KeySets
import ../shared/shared/shared/reach.bend as Reaches
import ../shared/shared/shared/shared/shared.bend as Shared
import ../shared/shared/shared/shared/trie.bend as Tries
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
      List.all.if(u => Shared.List.is_eq(~Char, ~Char.is_eq, xs, ys), Shared.Bool.is_eq(n, m))
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
        u => Shared.List.is_eq(~Char, ~Char.is_eq, xs, xs)
      )(
        Shared.Bool.is_eq_refl(n)
      )(Shared.List.is_eq_refl(~Char, ~Char.is_eq, ~Shared.Char.laws(), xs))

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
          Shared.List.all.if_hit(same_n, u => Shared.List.is_eq(~Char, ~Char.is_eq, xs, ys))(h)
        ): {Spec.AClass{n, xs} == Spec.AClass{_, ys}: Spec.Atom}
        %Shared.List.is_eq_sound(
          ~Char,
          ~Char.is_eq,
          ~Shared.Char.laws(),
          xs,
          ys
        )(
          Shared.List.all.if_rest(same_n, u => Shared.List.is_eq(~Char, ~Char.is_eq, xs, ys))(h)
        ): {Spec.AClass{n, xs} == Spec.AClass{n, _}: Spec.Atom}
        {==}

# the laws of Atom.is_eq
def Atom.laws() -> Shared.Eq.Laws(Spec.Atom, Atom.is_eq):
  (Atom.is_eq_refl, Atom.is_eq_sound)

# the key of t: a bit or two for its form, then its parts
def Atom.key(t: Spec.Atom) -> List<&2, Bool>:
  match t:
    case Spec.ALit{Chr{x}}:
      False{} <> Tries.Trie.char(x)
    case Spec.AAny{}:
      [True{}, False{}]
    case Spec.AClass{neg, cs}:
      True{} <> True{} <> neg <> Tries.Trie.text(String.from_list(cs))

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

# What the machine knows: the characters cs that the search moves it under,
# and one more, f (see "Representative characters").
type Abc is Data:
  Abc{cs: List<&2, Char>, f: Char}

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
# The search moves the machine only under the characters cs, and one more
# character f. cs holds the characters that the globs of the query name, and
# those with a role of their own for a path. A character that cs lacks moves
# the machine as f does.

# the characters that the search moves the machine under
def Abc.syms(g: Abc) -> List<&2, Char>:
  match g:
    case Abc{cs, f}:
      f <> cs

# the characters with a role of their own
def Role.chars() -> List<&2, Char>:
  ['/', '.', Chr{0}, Chr{92}]

# cs holds c
def Chars.has(cs: List<&2, Char>, c: Char) -> Bool:
  List.contains(~Char, ~Char.is_eq, cs, c)

# every character that t names is in cs
def Atom.within(cs: List<&2, Char>, t: Spec.Atom) -> Bool:
  match t:
    case Spec.ALit{x}:
      Chars.has(cs, x)
    case Spec.AAny{}:
      True{}
    case Spec.AClass{neg, xs}:
      Reaches.Reach.within(~Char, ~Char.is_eq, xs, cs)

# every character that slots name is in cs
def Slots.within(slots: List<&2, Slot>, +cs: List<&2, Char>) -> Bool:
  match slots:
    case Nil{}:
      True{}
    case Con{Inc{xs}, t}:
      List.all.if(
        u => Slots.within(t, cs),
        Regex.Seqs.holds(~Spec.Atom, ~List<&2, Char>, ~Atom.within, xs, cs)
      )
    case Con{Exc{xs}, t}:
      List.all.if(
        u => Slots.within(t, cs),
        Regex.Seqs.holds(~Spec.Atom, ~List<&2, Char>, ~Atom.within, xs, cs)
      )

# cs holds '/', and not c or f
def Chars.near(cs: List<&2, Char>, c: Char, f: Char) -> Bool:
  +cs = cs
  List.all.if(
    u => List.all.if(u2 => Bool.not(Chars.has(cs, f)), Bool.not(Chars.has(cs, c))),
    Chars.has(cs, '/')
  )

# cs holds '/', when c and f are near
def Chars.near_slash(
  +cs: List<&2, Char>,
  c: Char,
  f: Char,
  hn: {Chars.near(cs, c, f) == True{}: Bool}
) -> {Chars.has(cs, '/') == True{}: Bool}:
  Shared.List.all.if_hit(
    Chars.has(cs, '/'),
    u => List.all.if(u2 => Bool.not(Chars.has(cs, f)), Bool.not(Chars.has(cs, c)))
  )(hn)

# cs does not hold c, when c and f are near
def Chars.near_left(
  +cs: List<&2, Char>,
  +c: Char,
  +f: Char,
  hn: {Chars.near(cs, c, f) == True{}: Bool}
) -> {Chars.has(cs, c) == False{}: Bool}:
  Shared.Bool.not_true(
    Chars.has(cs, c)
  )(
    Shared.List.all.if_hit(
      Bool.not(Chars.has(cs, c)),
      u2 => Bool.not(Chars.has(cs, f))
    )(
      Shared.List.all.if_rest(
        Chars.has(cs, '/'),
        u => List.all.if(u2 => Bool.not(Chars.has(cs, f)), Bool.not(Chars.has(cs, c)))
      )(hn)
    )
  )

# cs does not hold f, when c and f are near
def Chars.near_right(
  +cs: List<&2, Char>,
  +c: Char,
  +f: Char,
  hn: {Chars.near(cs, c, f) == True{}: Bool}
) -> {Chars.has(cs, f) == False{}: Bool}:
  Shared.Bool.not_true(
    Chars.has(cs, f)
  )(
    Shared.List.all.if_rest(
      Bool.not(Chars.has(cs, c)),
      u2 => Bool.not(Chars.has(cs, f))
    )(
      Shared.List.all.if_rest(
        Chars.has(cs, '/'),
        u => List.all.if(u2 => Bool.not(Chars.has(cs, f)), Bool.not(Chars.has(cs, c)))
      )(hn)
    )
  )

# a character c that cs lacks is not a character r that cs holds
def Chars.out_ne(
  cs: List<&2, Char>,
  +r: Char,
  +c: Char,
  hr: {Chars.has(cs, r) == True{}: Bool},
  hc: {Chars.has(cs, c) == False{}: Bool}
) -> {False{} == Char.is_eq(c, r): Bool}:
  Equal.sym(
    Bool,
    Char.is_eq(c, r),
    False{},
    Shared.Eq.ne_flip(
      ~Char,
      ~Char.is_eq,
      ~Shared.Char.laws(),
      r,
      c,
      Shared.List.contains_ne(~Char, ~Char.is_eq, ~Shared.Char.laws(), cs, r, c, hr, hc)
    )
  )

# a character that cs lacks is not '/', when cs holds '/'
def Char.inner_out(
  cs: List<&2, Char>,
  c: Char,
  hs: {Chars.has(cs, '/') == True{}: Bool},
  hc: {Chars.has(cs, c) == False{}: Bool}
) -> {Spec.is_inner(c) == True{}: Bool}:
  %Chars.out_ne(cs, '/', c, hs, hc): {Bool.not(_) == True{}: Bool}
  {==}

# a character that is none of Role.chars has no role of its own
def Role.of_other(
  c: Char,
  +h: {Chars.has(Role.chars(), c) == False{}: Bool}
) -> {KOther{} == Role.of(c): Role}:
  match c:
    case Chr{+x}:
      %Chars.out_ne(
        Role.chars(),
        '/',
        Chr{x},
        {==},
        h
      ): {
        KOther{}
          == Bool.pick(
            Role,
            _,
            KSlash{},
            Bool.pick(
              Role,
              U32.is_eq(x, 46),
              KDot{},
              Bool.pick(Role, Spec.is_banned(Chr{x}), KBad{}, KOther{})
            )
          ): Role
      }
      %Chars.out_ne(
        Role.chars(),
        '.',
        Chr{x},
        {==},
        h
      ): {
        KOther{}
          == Bool.pick(
            Role,
            _,
            KDot{},
            Bool.pick(Role, Spec.is_banned(Chr{x}), KBad{}, KOther{})
          ): Role
      }
      %Chars.out_ne(
        Role.chars(),
        Chr{0},
        Chr{x},
        {==},
        h
      ): {KOther{} == Bool.pick(Role, Bool.or(_, U32.is_eq(x, 92)), KBad{}, KOther{}): Role}
      %Chars.out_ne(
        Role.chars(),
        Chr{92},
        Chr{x},
        {==},
        h
      ): {KOther{} == Bool.pick(Role, _, KBad{}, KOther{}): Role}
      {==}

# an atom whose characters are in cs accepts c exactly when it accepts f,
# two characters that cs lacks, when cs holds '/'
def Atom.alike(
  +cs: List<&2, Char>,
  +c: Char,
  +f: Char,
  t: Spec.Atom,
  +hn: {Chars.near(cs, c, f) == True{}: Bool},
  hp: {Atom.within(cs, t) == True{}: Bool}
) -> {Spec.Atom.hit(t, c) == Spec.Atom.hit(t, f): Bool}:
  match t:
    case Spec.ALit{+x}:
      +hp = hp
      Equal.trans(
        Bool,
        Char.is_eq(x, c),
        False{},
        Char.is_eq(x, f),
        Shared.List.contains_ne(
          ~Char,
          ~Char.is_eq,
          ~Shared.Char.laws(),
          cs,
          x,
          c,
          hp,
          Chars.near_left(cs, c, f, hn)
        ),
        Equal.sym(
          Bool,
          Char.is_eq(x, f),
          False{},
          Shared.List.contains_ne(
            ~Char,
            ~Char.is_eq,
            ~Shared.Char.laws(),
            cs,
            x,
            f,
            hp,
            Chars.near_right(cs, c, f, hn)
          )
        )
      )
    case Spec.AAny{}:
      Equal.trans(
        Bool,
        Spec.is_inner(c),
        True{},
        Spec.is_inner(f),
        Char.inner_out(cs, c, Chars.near_slash(cs, c, f, hn), Chars.near_left(cs, c, f, hn)),
        Equal.sym(
          Bool,
          Spec.is_inner(f),
          True{},
          Char.inner_out(cs, f, Chars.near_slash(cs, c, f, hn), Chars.near_right(cs, c, f, hn))
        )
      )
    case Spec.AClass{neg, +xs}:
      +hp = hp
      ic = Spec.is_inner(c)
      xf = Bool.xor(neg, List.contains(~Char, ~Char.is_eq, xs, f))
      %Equal.sym(
        Bool,
        List.contains(~Char, ~Char.is_eq, xs, c),
        False{},
        Reaches.Reach.within_out(
          ~Char,
          ~Char.is_eq,
          ~Shared.Char.laws(),
          xs,
          cs,
          c,
          hp,
          Chars.near_left(cs, c, f, hn)
        )
      ): {List.all.if(u => Bool.xor(neg, _), ic) == List.all.if(u => xf, Spec.is_inner(f)): Bool}
      %Equal.sym(
        Bool,
        List.contains(~Char, ~Char.is_eq, xs, f),
        False{},
        Reaches.Reach.within_out(
          ~Char,
          ~Char.is_eq,
          ~Shared.Char.laws(),
          xs,
          cs,
          f,
          hp,
          Chars.near_right(cs, c, f, hn)
        )
      ): {
        List.all.if(
          u => Bool.xor(neg, False{}),
          ic
        )
          == List.all.if(u => Bool.xor(neg, _), Spec.is_inner(f)): Bool
      }
      %Equal.sym(
        Bool,
        ic,
        True{},
        Char.inner_out(cs, c, Chars.near_slash(cs, c, f, hn), Chars.near_left(cs, c, f, hn))
      ): {
        List.all.if(
          u => Bool.xor(neg, False{}),
          _
        )
          == List.all.if(u => Bool.xor(neg, False{}), Spec.is_inner(f)): Bool
      }
      %Equal.sym(
        Bool,
        Spec.is_inner(f),
        True{},
        Char.inner_out(cs, f, Chars.near_slash(cs, c, f, hn), Chars.near_right(cs, c, f, hn))
      ): {
        List.all.if(
          u => Bool.xor(neg, False{}),
          True{}
        )
          == List.all.if(u => Bool.xor(neg, False{}), _): Bool
      }
      {==}

# slots step alike under two characters that cs lacks, when cs holds '/' and
# every character that the slots name
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- only proofs use it; no program runs it
def Slot.step_alike(
  slots: List<&2, Slot>,
  +cs: List<&2, Char>,
  +c: Char,
  +f: Char,
  +hn: {Chars.near(cs, c, f) == True{}: Bool}
) -> {
  Slots.within(slots, cs) == True{}: Bool
} -> {Slot.step(slots, c) == Slot.step(slots, f): List<&2, Slot>}:
  match slots:
    case Nil{}:
      _ => {==}
    case Con{Inc{+xs}, +t}:
      +hw =>
        +wx = Regex.Seqs.holds(~Spec.Atom, ~List<&2, Char>, ~Atom.within, xs, cs)
        +xc = Regex.Seqs.step(~Char, ~Spec.Atom, ~Spec.Atom.hit, ~Atom.is_eq, ~Atom.key, xs, c)
        +tc = Slot.step(t, c)
        %Regex.Seqs.step_alike(
          ~Char,
          ~Spec.Atom,
          ~List<&2, Char>,
          ~Spec.Atom.hit,
          ~Atom.is_eq,
          ~Atom.key,
          ~Atom.within,
          ~Chars.near,
          ~(g => c2 => f2 => t2 => hn2 => hp2 => Atom.alike(g, c2, f2, t2, hn2, hp2)),
          xs,
          cs,
          c,
          f
        )(
          hn
        )(
          Shared.List.all.if_hit(wx, u => Slots.within(t, cs))(hw)
        ): {Con{Inc{xc}, tc} == Con{Inc{_}, Slot.step(t, f)}: List<&2, Slot>}
        %Slot.step_alike(
          t,
          cs,
          c,
          f,
          hn
        )(
          Shared.List.all.if_rest(wx, u => Slots.within(t, cs))(hw)
        ): {Con{Inc{xc}, tc} == Con{Inc{xc}, _}: List<&2, Slot>}
        {==}
    case Con{Exc{+xs}, +t}:
      +hw =>
        +wx = Regex.Seqs.holds(~Spec.Atom, ~List<&2, Char>, ~Atom.within, xs, cs)
        +xc = Regex.Seqs.step(~Char, ~Spec.Atom, ~Spec.Atom.hit, ~Atom.is_eq, ~Atom.key, xs, c)
        +tc = Slot.step(t, c)
        %Regex.Seqs.step_alike(
          ~Char,
          ~Spec.Atom,
          ~List<&2, Char>,
          ~Spec.Atom.hit,
          ~Atom.is_eq,
          ~Atom.key,
          ~Atom.within,
          ~Chars.near,
          ~(g => c2 => f2 => t2 => hn2 => hp2 => Atom.alike(g, c2, f2, t2, hn2, hp2)),
          xs,
          cs,
          c,
          f
        )(
          hn
        )(
          Shared.List.all.if_hit(wx, u => Slots.within(t, cs))(hw)
        ): {Con{Exc{xc}, tc} == Con{Exc{_}, Slot.step(t, f)}: List<&2, Slot>}
        %Slot.step_alike(
          t,
          cs,
          c,
          f,
          hn
        )(
          Shared.List.all.if_rest(wx, u => Slots.within(t, cs))(hw)
        ): {Con{Exc{xc}, tc} == Con{Exc{xc}, _}: List<&2, Slot>}
        {==}
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# f <> cs holds f
# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- a false positive, as the rule notes: the other use is an erased argument (of Equal.sym or a motive)
def Chars.has_head(f: Char, cs: List<&2, Char>) -> {Chars.has(f <> cs, f) == True{}: Bool}:
  %Equal.sym(
    Bool,
    Char.is_eq(f, f),
    True{},
    Shared.Char.is_eq_refl(f)
  ): {List.any.if(u => Chars.has(cs, f), _) == True{}: Bool}
  {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# cs holds each character with a role of its own, and not f
def Abc.fits(g: Abc) -> Bool:
  match g:
    case Abc{+cs, f}:
      List.all.if(
        u => Bool.not(Chars.has(cs, f)),
        Reaches.Reach.within(~Char, ~Char.is_eq, Role.chars(), cs)
      )

# w is Dead; or g fits, and every character that the state of w names is in
# its cs
def Walk.covers(g: Abc, w: Walk) -> Bool:
  match g w:
    case _ Dead{}:
      True{}
    case Abc{+cs, f} At{p, St{both, a, b}}:
      List.all.if(
        u => List.all.if(u2 => Slots.within(b, cs), Slots.within(a, cs)),
        Abc.fits(Abc{cs, f})
      )

# Walk.rep at a place that is not Dead, once it is known if f <> cs holds c
# (known)
def Walk.rep.at(
  +cs: List<&2, Char>,
  +f: Char,
  p: Path,
  both: Bool,
  +a: List<&2, Slot>,
  +b: List<&2, Slot>,
  +c: Char,
  known: Bool,
  +h: {Walk.covers(Abc{cs, f}, At{p, St{both, a, b}}) == True{}: Bool}
) -> {
  Chars.has(f <> cs, c) == known: Bool
} -> (
  &d: Char -> {
    List.contains(~Char, ~Char.is_eq, f <> cs, d) == True{}: Bool
  }
    & {
      Walk.step(
        Abc{cs, f},
        At{p, St{both, a, b}},
        c
      )
        == Walk.step(Abc{cs, f}, At{p, St{both, a, b}}, d): Walk
    }
):
  match known:
    case True{}:
      e => (c, (e, {==}))
    case False{}:
      e =>
        +wa = Slots.within(a, cs)
        +wb = Slots.within(b, cs)
        +roles = Reaches.Reach.within(~Char, ~Char.is_eq, Role.chars(), cs)
        +no_f = Bool.not(Chars.has(cs, f))
        +no_c = Bool.not(Chars.has(cs, c))
        +fits = Shared.List.all.if_hit(
          List.all.if(u => no_f, roles),
          u => List.all.if(u2 => wb, wa)
        )(h)
        +within = Shared.List.all.if_rest(
          List.all.if(u => no_f, roles),
          u => List.all.if(u2 => wb, wa)
        )(h)
        +hr = Shared.List.all.if_hit(roles, u => no_f)(fits)
        +hf = Shared.List.all.if_rest(roles, u => no_f)(fits)
        +hc = Shared.List.any.if_false_rest(Char.is_eq(f, c), u => Chars.has(cs, c))(e)
        +hn = {
          Shared.List.all.if_both(
            Chars.has(cs, '/'),
            u => List.all.if(u2 => no_f, no_c)
          )(
            Shared.Bool.and_true_left(
              Chars.has(cs, '/'),
              Reaches.Reach.within(~Char, ~Char.is_eq, ['.', Chr{0}, Chr{92}], cs)
            )(hr)
          )(
            Shared.List.all.if_both(
              no_c,
              u2 => no_f
            )(Equal.cong(Bool, Bool, v => Bool.not(v), Chars.has(cs, c), False{}, hc))(hf)
          ): {Chars.near(cs, c, f) == True{}: Bool}
        }
        -ac = Slot.step(a, c)
        -bc = Slot.step(b, c)
        -to = Path.step(p, KOther{})
        (f, (Chars.has_head(f, cs), {
              %Role.of_other(c, Reaches.Reach.within_out(~Char, ~Char.is_eq, ~Shared.Char.laws(), Role.chars(), cs, c, hr, hc)): {Walk.at(Path.step(p, _), u => St{both, ac, bc}) == Walk.at(Path.step(p, Role.of(f)), u => St{both, Slot.step(a, f), Slot.step(b, f)}): Walk}
              %Role.of_other(f, Reaches.Reach.within_out(~Char, ~Char.is_eq, ~Shared.Char.laws(), Role.chars(), cs, f, hr, Shared.Bool.not_true(Chars.has(cs, f))(hf))): {Walk.at(to, u => St{both, ac, bc}) == Walk.at(Path.step(p, _), u => St{both, Slot.step(a, f), Slot.step(b, f)}): Walk}
              %Slot.step_alike(a, cs, c, f, hn)(Shared.List.all.if_hit(wa, u2 => wb)(within)): {Walk.at(to, u => St{both, ac, bc}) == Walk.at(to, u => St{both, _, Slot.step(b, f)}): Walk}
              %Slot.step_alike(b, cs, c, f, hn)(Shared.List.all.if_rest(wa, u2 => wb)(within)): {Walk.at(to, u => St{both, ac, bc}) == Walk.at(to, u => St{both, ac, _}): Walk}
              {==}
              : {Walk.step(Abc{cs, f}, At{p, St{both, a, b}}, c) == Walk.step(Abc{cs, f}, At{p, St{both, a, b}}, f): Walk}}))

# under a place that g covers, each character moves the machine as some
# character of Abc.syms(g) does
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
    case Abc{cs, +f} Dead{}:
      (f, (Chars.has_head(f, cs), {==}))
    case Abc{+cs, +f} At{p, St{both, a, b}}:
      +c = c
      Walk.rep.at(cs, f, p, both, a, b, c, Chars.has(f <> cs, c), h)({==})

# Search
# ------
# The search needs no proof: `decide` checks what it returns. It visits the
# places that the machine can reach from the place of the query. A word that
# the machine accepts is a path to check; when no place accepts, the places
# are a certificate to check.

# the characters that g names, in front of acc
def Glob.chars(g: Spec.Glob, acc: List<&2, Char>) -> List<&2, Char>:
  match g:
    case Spec.Void{}:
      acc
    case Spec.Eps{}:
      acc
    case Spec.Lit{x}:
      x <> acc
    case Spec.Any{}:
      acc
    case Spec.Star{}:
      acc
    case Spec.Class{n, xs}:
      List.append(&2, Char, xs, acc)
    case Spec.Deep{}:
      acc
    case Spec.Cat{a, b}:
      Glob.chars(a, Glob.chars(b, acc))
    case Spec.Alt{a, b}:
      Glob.chars(a, Glob.chars(b, acc))

# the characters that the globs of rules name, in front of acc
def Rules.chars(rules: List<&2, Spec.Rule>, acc: List<&2, Char>) -> List<&2, Char>:
  match rules:
    case Nil{}:
      acc
    case Con{Spec.Include{g}, t}:
      Glob.chars(g, Rules.chars(t, acc))
    case Con{Spec.Exclude{g}, t}:
      Glob.chars(g, Rules.chars(t, acc))

# the key of c
def Char.key(c: Char) -> List<&2, Bool>:
  match c:
    case Chr{x}:
      Tries.Trie.char(x)

# the characters of Role.chars and those that the globs of a and b name,
# each once
def Rules.abc_chars(a: List<&2, Spec.Rule>, b: List<&2, Spec.Rule>) -> List<&2, Char>:
  KeySets.KeySet.unique(
    ~Char,
    ~Char.is_eq,
    ~Char.key,
    List.append(&2, Char, Role.chars(), Rules.chars(a, Rules.chars(b, []))),
    Tries.Trie.new(Char)
  )

# the characters of Role.chars and those that the globs of q name, each once
def Query.chars(q: Spec.Query) -> List<&2, Char>:
  match q:
    case Spec.Both{a, b}:
      Rules.abc_chars(a, b)
    case Spec.Only{a, b}:
      Rules.abc_chars(a, b)

# the largest code in cs, or acc
def Chars.max(cs: List<&2, Char>, +acc: U32) -> U32:
  match cs:
    case Nil{}:
      acc
    case Con{Chr{+x}, t}:
      Chars.max(t, Bool.pick(U32, U32.is_gt(x, acc), x, acc))
# a character after every character of cs
def Chars.fresh(cs: List<&2, Char>) -> Char:
  Chr{(Chars.max(cs, 0) + 1: U32)}
# the named characters of q, and one more
def Query.abc(q: Spec.Query) -> Abc:
  +cs = Query.chars(q)
  Abc{cs, Chars.fresh(cs)}

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

# each character of cs, escaped, before rest
def Glob.show.chars(cs: List<&2, Char>, rest: String) -> String:
  match cs:
    case Nil{}:
      rest
    case Con{h, t}:
      SCon{Chr{92}, SCon{h, Glob.show.chars(t, rest)}}

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
    case Spec.Class{neg, cs}:
      "[" ++ Glob.show.neg(neg, Glob.show.chars(cs, "]" ++ rest))
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
    case Spec.Class{neg, cs}:
      Spec.Class{neg, List.reverse(&2, Char, cs)}
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

# `[` before an escape opens a class
def Step.left_esc(
  l: List<&2, Spec.Sym>,
  st: List<&2, Spec.Frame>,
  seg: Bool
) -> {
  Spec.Glob.read.go(
    Con{Spec.SEsc{}, l},
    Spec.In{False{}, []},
    st,
    seg
  )
    == Spec.Glob.read.go(
      Con{Spec.SLeft{}, Con{Spec.SEsc{}, l}},
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

# an escaped symbol in a class adds its character
def Step.esc_in(
  y: Spec.Sym,
  l: List<&2, Spec.Sym>,
  n: Bool,
  cs: List<&2, Char>,
  st: List<&2, Spec.Frame>,
  seg: Bool
) -> {
  Spec.Glob.read.go(
    l,
    Spec.In{n, Con{Spec.Sym.char(y), cs}},
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
  cs: List<&2, Char>,
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

# reading escaped characters in a class conses each onto the class
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- only proofs use it; no program runs it
def Show.parse_chars(
  cs: List<&2, Char>,
  +rest: String,
  +n: Bool,
  +acc: List<&2, Char>,
  +st: List<&2, Spec.Frame>,
  +seg: Bool
) -> {
  Spec.Glob.read.go(
    Spec.Sym.list(rest),
    Spec.In{n, List.reverse.go(&2, Char, cs, acc)},
    st,
    seg
  )
    == Spec.Glob.read.go(
      Spec.Sym.list(Glob.show.chars(cs, rest)),
      Spec.In{n, acc},
      st,
      seg
    ): Maybe<&2, Spec.Glob>
}:
  match cs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      l = Spec.Sym.list(Glob.show.chars(t, rest))
      -tgt = Spec.Glob.read.go(
        Spec.Sym.list(rest),
        Spec.In{n, List.reverse.go(&2, Char, t, Con{h, acc})},
        st,
        seg
      )
      %Step.esc_in(Spec.Sym.of(h), l, n, acc, st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
      %Sym.char_of(
        h
      ): {tgt == Spec.Glob.read.go(l, Spec.In{n, Con{_, acc}}, st, seg): Maybe<&2, Spec.Glob>}
      Show.parse_chars(t, rest, n, Con{h, acc}, st, seg)
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

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

# the text of a class reads back as the class, its characters reversed
def Show.parse_class(
  neg: Bool,
  cs: List<&2, Char>,
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
    Con{Spec.Frame{a, Con{Show.glob(Spec.Class{neg, cs}), s}, b}, r},
    False{}
  )
    == Spec.Glob.read.go(
      Spec.Sym.list(Glob.show.go(Spec.Class{neg, cs}, rest)),
      Spec.Out{},
      Con{Spec.Frame{a, s, b}, r},
      seg
    ): Maybe<&2, Spec.Glob>
}:
  match neg cs:
    case True{} +cs:
      +l = Spec.Sym.list(rest)
      +st = {Con{Spec.Frame{a, s, b}, r}: List<&2, Spec.Frame>}
      tgt = Spec.Glob.read.go(
        l,
        Spec.Out{},
        Con{Spec.Frame{a, Con{Spec.Class{True{}, List.reverse(&2, Char, cs)}, s}, b}, r},
        False{}
      )
      lc = Spec.Sym.list(Glob.show.chars(cs, "]" ++ rest))
      %Step.left_bang(lc, st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
      %Show.parse_chars(cs, "]" ++ rest, True{}, [], st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
      %Step.right(l, True{}, List.reverse(&2, Char, cs), st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
      {==}
    case False{} Nil{}:
      +l = Spec.Sym.list(rest)
      +st = {Con{Spec.Frame{a, s, b}, r}: List<&2, Spec.Frame>}
      tgt = Spec.Glob.read.go(
        l,
        Spec.Out{},
        Con{Spec.Frame{a, Con{Spec.Class{False{}, []}, s}, b}, r},
        False{}
      )
      %Step.left_right(l, st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
      %Step.right(l, False{}, [], st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
      {==}
    case False{} Con{+h, +t}:
      +l = Spec.Sym.list(rest)
      +st = {Con{Spec.Frame{a, s, b}, r}: List<&2, Spec.Frame>}
      +rv = List.reverse(&2, Char, Con{h, t})
      tgt = Spec.Glob.read.go(
        l,
        Spec.Out{},
        Con{Spec.Frame{a, Con{Spec.Class{False{}, rv}, s}, b}, r},
        False{}
      )
      lc = Spec.Sym.list(SCon{h, Glob.show.chars(t, "]" ++ rest)})
      %Step.left_esc(lc, st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
      %Show.parse_chars(
        Con{h, t},
        "]" ++ rest,
        False{},
        [],
        st,
        seg
      ): {tgt == _: Maybe<&2, Spec.Glob>}
      %Step.right(l, False{}, rv, st, seg): {tgt == _: Maybe<&2, Spec.Glob>}
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

# a class with its characters reversed matches the same strings
def Show.class_point(
  p: String,
  n: Bool,
  +cs: List<&2, Char>
) -> {
  Spec.Glob.matches(
    p,
    Spec.Class{n, List.reverse(&2, Char, cs)}
  )
    == Spec.Glob.matches(p, Spec.Class{n, cs}): Bool
}:
  match p:
    case SNil{}:
      {==}
    case SCon{+c, t}:
      i = Spec.is_inner(c)
      w = String.to_list(t)
      +k = List.contains(~Char, ~Char.is_eq, cs, c)
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
        List.contains(~Char, ~Char.is_eq, List.reverse(&2, Char, cs), c),
        Shared.Bool.or_false(k),
        Shared.List.contains_reverse(~Char, ~Char.is_eq, cs, [], c)
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
