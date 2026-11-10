import Base
import ../shared/shared/regex.bend as Regex
import ../shared/shared/search.bend as Searches
import ../shared/shared/shared/keyset.bend as KeySets
import ../shared/shared/shared/reach.bend as Reaches
import ../shared/shared/shared/shared/shared.bend as Shared
import ../shared/shared/shared/shared/trie.bend as Tries
import ../shared/shared/shared/text.bend as Texts
import ./spec.bend as Spec

# Globs as regular expressions
# ----------------------------
# A glob is a regular expression over characters (regex.bend) whose atoms
# are the three glob forms that read one character. Glob.re_matches says
# that the expression matches what Spec.Glob.matches says the glob matches,
# so the laws of regex.bend hold for globs.

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
      Spec.is_inner(c)
    case AClass{neg, cs}:
      +c = c
      List.all.if(u => Bool.xor(neg, List.contains(~Char, ~Char.is_eq, cs, c)), Spec.is_inner(c))

# the regular expression of g
# bend-lint: expect-begin bend-lint-rules/performance/missed_fork@hint -- a glob tree is a few nodes, where a fork costs more than it saves
def Glob.re(g: Spec.Glob) -> Regex.Re<Atom>:
  match g:
    case Spec.Void{}:
      Regex.Void{}
    case Spec.Eps{}:
      Regex.Eps{}
    case Spec.Lit{c}:
      Regex.One{ALit{c}}
    case Spec.Any{}:
      Regex.One{AAny{}}
    case Spec.Star{}:
      Regex.Star{Regex.One{AAny{}}}
    case Spec.Class{neg, cs}:
      Regex.One{AClass{neg, cs}}
    case Spec.Deep{}:
      Regex.All{}
    case Spec.Cat{a, b}:
      Regex.Cat{Glob.re(a), Glob.re(b)}
    case Spec.Alt{a, b}:
      Regex.Alt{Glob.re(a), Glob.re(b)}
# bend-lint: expect-end bend-lint-rules/performance/missed_fork@hint

# the expression of Glob.of_bool(b) is Re.of_bool(b)
def Glob.re_of_bool(
  b: Bool
) -> {Glob.re(Spec.Glob.of_bool(b)) == Regex.Re.of_bool(Atom, b): Regex.Re<Atom>}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

# a glob matches "" exactly when its expression does
def Glob.re_nullable(
  g: Spec.Glob
) -> {Spec.Glob.is_nullable(g) == Regex.Re.is_nullable(Atom, Glob.re(g)): Bool}:
  match g:
    case Spec.Void{}:
      {==}
    case Spec.Eps{}:
      {==}
    case Spec.Lit{c}:
      {==}
    case Spec.Any{}:
      {==}
    case Spec.Star{}:
      {==}
    case Spec.Class{neg, cs}:
      {==}
    case Spec.Deep{}:
      {==}
    case Spec.Cat{+a, +b}:
      na = Spec.Glob.is_nullable(a)
      nb = Spec.Glob.is_nullable(b)
      %Glob.re_nullable(
        a
      ): {Bool.and(na, nb) == List.all.if(u => Regex.Re.is_nullable(Atom, Glob.re(b)), _): Bool}
      %Glob.re_nullable(b): {Bool.and(na, nb) == List.all.if(u => _, na): Bool}
      %Shared.List.all.if_and(na, u => nb): {_ == List.all.if(u => nb, na): Bool}
      {==}
    case Spec.Alt{+a, +b}:
      na = Spec.Glob.is_nullable(a)
      nb = Spec.Glob.is_nullable(b)
      %Glob.re_nullable(
        a
      ): {Bool.or(na, nb) == List.any.if(u => Regex.Re.is_nullable(Atom, Glob.re(b)), _): Bool}
      %Glob.re_nullable(b): {Bool.or(na, nb) == List.any.if(u => _, na): Bool}
      %Shared.List.any.if_or(na, u => nb): {_ == List.any.if(u => nb, na): Bool}
      {==}

# the expression of a glob after c is its expression, after c
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- only proofs use it; no program runs it
def Glob.re_step(
  g: Spec.Glob,
  +c: Char
) -> {
  Glob.re(
    Spec.Glob.step(g, c)
  )
    == Regex.Re.step(~Char, ~Atom, ~Atom.hit, Glob.re(g), c): Regex.Re<Atom>
}:
  match g:
    case Spec.Void{}:
      {==}
    case Spec.Eps{}:
      {==}
    case Spec.Lit{x}:
      Glob.re_of_bool(Char.is_eq(x, c))
    case Spec.Any{}:
      Glob.re_of_bool(Spec.is_inner(c))
    case Spec.Star{}:
      i = Spec.is_inner(c)
      star = {Regex.Star{Regex.One{AAny{}}}: Regex.Re<Atom>}
      %Glob.re_of_bool(
        i
      ): {Regex.Cat{Glob.re(Spec.Glob.of_bool(i)), star} == Regex.Cat{_, star}: Regex.Re<Atom>}
      {==}
    case Spec.Class{neg, cs}:
      +i = Spec.is_inner(c)
      +x = Bool.xor(neg, List.contains(~Char, ~Char.is_eq, cs, c))
      %Shared.List.all.if_and(
        i,
        u => x
      ): {
        Glob.re(
          Spec.Glob.of_bool(_)
        )
          == Regex.Re.of_bool(Atom, List.all.if(u => x, i)): Regex.Re<Atom>
      }
      Glob.re_of_bool(List.all.if(u => x, i))
    case Spec.Deep{}:
      {==}
    case Spec.Cat{+a, +b}:
      ra = Glob.re(a)
      rb = Glob.re(b)
      sa = Glob.re(Spec.Glob.step(a, c))
      sb = Glob.re(Spec.Glob.step(b, c))
      +na = Spec.Glob.is_nullable(a)
      lhs = {
        Regex.Alt{Regex.Cat{sa, rb}, Regex.Cat{Glob.re(Spec.Glob.of_bool(na)), sb}}: Regex.Re<Atom>
      }
      %Glob.re_step(
        a,
        c
      ): {
        lhs
          == Regex.Alt{
            Regex.Cat{_, rb},
            Regex.Cat{
              Regex.Re.of_bool(Atom, Regex.Re.is_nullable(Atom, ra)),
              Regex.Re.step(~Char, ~Atom, ~Atom.hit, rb, c)
            }
          }: Regex.Re<Atom>
      }
      %Glob.re_step(
        b,
        c
      ): {
        lhs
          == Regex.Alt{
            Regex.Cat{sa, rb},
            Regex.Cat{Regex.Re.of_bool(Atom, Regex.Re.is_nullable(Atom, ra)), _}
          }: Regex.Re<Atom>
      }
      %Glob.re_nullable(
        a
      ): {
        lhs
          == Regex.Alt{Regex.Cat{sa, rb}, Regex.Cat{Regex.Re.of_bool(Atom, _), sb}}: Regex.Re<Atom>
      }
      %Glob.re_of_bool(na): {lhs == Regex.Alt{Regex.Cat{sa, rb}, Regex.Cat{_, sb}}: Regex.Re<Atom>}
      {==}
    case Spec.Alt{+a, +b}:
      sa = Glob.re(Spec.Glob.step(a, c))
      sb = Glob.re(Spec.Glob.step(b, c))
      %Glob.re_step(
        a,
        c
      ): {
        Regex.Alt{
          sa,
          sb
        }
          == Regex.Alt{_, Regex.Re.step(~Char, ~Atom, ~Atom.hit, Glob.re(b), c)}: Regex.Re<Atom>
      }
      %Glob.re_step(b, c): {Regex.Alt{sa, sb} == Regex.Alt{sa, _}: Regex.Re<Atom>}
      {==}
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# a glob matches p exactly when its expression matches the characters of p
def Glob.re_matches(
  p: String,
  +g: Spec.Glob
) -> {
  Regex.Re.matches(
    ~Char,
    ~Atom,
    ~Atom.hit,
    String.to_list(p),
    Glob.re(g)
  )
    == Spec.Glob.matches(p, g): Bool
}:
  match p:
    case SNil{}:
      Equal.sym(
        Bool,
        Spec.Glob.is_nullable(g),
        Regex.Re.is_nullable(Atom, Glob.re(g)),
        Glob.re_nullable(g)
      )
    case SCon{+c, t}:
      %Glob.re_step(
        g,
        c
      ): {
        Regex.Re.matches(
          ~Char,
          ~Atom,
          ~Atom.hit,
          String.to_list(t),
          _
        )
          == Spec.Glob.matches(t, Spec.Glob.step(g, c)): Bool
      }
      Glob.re_matches(t, Spec.Glob.step(g, c))

# Matching algebra
# ----------------
# The laws of regex.bend, for globs. Each states the simpler side first, so a
# rewrite with it turns a glob into its simpler meaning.

# Void matches nothing
def Glob.void_never(+p: String) -> {False{} == Spec.Glob.matches(p, Spec.Void{}): Bool}:
  %Glob.re_matches(p, Spec.Void{}): {False{} == _: Bool}
  Regex.Re.void_never(~Char, ~Atom, ~Atom.hit, String.to_list(p))

# Alt matches what either side matches
def Glob.alt_or(
  +p: String,
  +a: Spec.Glob,
  +b: Spec.Glob
) -> {
  Bool.or(
    Spec.Glob.matches(p, a),
    Spec.Glob.matches(p, b)
  )
    == Spec.Glob.matches(p, Spec.Alt{a, b}): Bool
}:
  +w = String.to_list(p)
  ma = Regex.Re.matches(~Char, ~Atom, ~Atom.hit, w, Glob.re(a))
  mb = Regex.Re.matches(~Char, ~Atom, ~Atom.hit, w, Glob.re(b))
  %Glob.re_matches(
    p,
    a
  ): {Bool.or(_, Spec.Glob.matches(p, b)) == Spec.Glob.matches(p, Spec.Alt{a, b}): Bool}
  %Glob.re_matches(p, b): {Bool.or(ma, _) == Spec.Glob.matches(p, Spec.Alt{a, b}): Bool}
  %Glob.re_matches(p, Spec.Alt{a, b}): {Bool.or(ma, mb) == _: Bool}
  Regex.Re.alt_or(~Char, ~Atom, ~Atom.hit, w, Glob.re(a), Glob.re(b))

# Cat after Void matches nothing
def Glob.cat_void_l(
  +p: String,
  +x: Spec.Glob
) -> {False{} == Spec.Glob.matches(p, Spec.Cat{Spec.Void{}, x}): Bool}:
  %Glob.re_matches(p, Spec.Cat{Spec.Void{}, x}): {False{} == _: Bool}
  Regex.Re.cat_void_l(~Char, ~Atom, ~Atom.hit, String.to_list(p), Glob.re(x))

# Cat after Eps matches what its right side matches
def Glob.cat_eps_l(
  +p: String,
  +x: Spec.Glob
) -> {Spec.Glob.matches(p, x) == Spec.Glob.matches(p, Spec.Cat{Spec.Eps{}, x}): Bool}:
  %Glob.re_matches(p, x): {_ == Spec.Glob.matches(p, Spec.Cat{Spec.Eps{}, x}): Bool}
  %Glob.re_matches(
    p,
    Spec.Cat{Spec.Eps{}, x}
  ): {Regex.Re.matches(~Char, ~Atom, ~Atom.hit, String.to_list(p), Glob.re(x)) == _: Bool}
  Regex.Re.cat_eps_l(~Char, ~Atom, ~Atom.hit, String.to_list(p), Glob.re(x))

# Cat before Eps matches what its left side matches
def Glob.cat_eps_r(
  +p: String,
  +x: Spec.Glob
) -> {Spec.Glob.matches(p, x) == Spec.Glob.matches(p, Spec.Cat{x, Spec.Eps{}}): Bool}:
  %Glob.re_matches(p, x): {_ == Spec.Glob.matches(p, Spec.Cat{x, Spec.Eps{}}): Bool}
  %Glob.re_matches(
    p,
    Spec.Cat{x, Spec.Eps{}}
  ): {Regex.Re.matches(~Char, ~Atom, ~Atom.hit, String.to_list(p), Glob.re(x)) == _: Bool}
  Regex.Re.cat_eps_r(~Char, ~Atom, ~Atom.hit, String.to_list(p), Glob.re(x))

# Cat after of_bool(b) matches what its right side matches, when b holds
def Glob.cat_of_bool(
  +p: String,
  +b: Bool,
  +r: Spec.Glob
) -> {
  Bool.and(
    b,
    Spec.Glob.matches(p, r)
  )
    == Spec.Glob.matches(p, Spec.Cat{Spec.Glob.of_bool(b), r}): Bool
}:
  +w = String.to_list(p)
  mr = Regex.Re.matches(~Char, ~Atom, ~Atom.hit, w, Glob.re(r))
  %Glob.re_matches(
    p,
    r
  ): {Bool.and(b, _) == Spec.Glob.matches(p, Spec.Cat{Spec.Glob.of_bool(b), r}): Bool}
  %Glob.re_matches(p, Spec.Cat{Spec.Glob.of_bool(b), r}): {Bool.and(b, mr) == _: Bool}
  %Equal.sym(
    Regex.Re<Atom>,
    Glob.re(Spec.Glob.of_bool(b)),
    Regex.Re.of_bool(Atom, b),
    Glob.re_of_bool(b)
  ): {
    Bool.and(b, mr) == Regex.Re.matches(~Char, ~Atom, ~Atom.hit, w, Regex.Cat{_, Glob.re(r)}): Bool
  }
  Regex.Re.cat_of_bool(~Char, ~Atom, ~Atom.hit, w, b, Glob.re(r))

# Cat is associative
def Glob.cat_assoc(
  +p: String,
  +a: Spec.Glob,
  +b: Spec.Glob,
  +r: Spec.Glob
) -> {
  Spec.Glob.matches(
    p,
    Spec.Cat{a, Spec.Cat{b, r}}
  )
    == Spec.Glob.matches(p, Spec.Cat{Spec.Cat{a, b}, r}): Bool
}:
  w = String.to_list(p)
  %Glob.re_matches(
    p,
    Spec.Cat{a, Spec.Cat{b, r}}
  ): {_ == Spec.Glob.matches(p, Spec.Cat{Spec.Cat{a, b}, r}): Bool}
  %Glob.re_matches(
    p,
    Spec.Cat{Spec.Cat{a, b}, r}
  ): {Regex.Re.matches(~Char, ~Atom, ~Atom.hit, w, Glob.re(Spec.Cat{a, Spec.Cat{b, r}})) == _: Bool}
  Regex.Re.cat_assoc(~Char, ~Atom, ~Atom.hit, w, Glob.re(a), Glob.re(b), Glob.re(r))

# Atom equality and keys
# ----------------------

# a and b are the same atom
def Atom.is_eq(a: Atom, b: Atom) -> Bool:
  match a b:
    case ALit{x} ALit{y}:
      Char.is_eq(x, y)
    case AAny{} AAny{}:
      True{}
    case AClass{n, xs} AClass{m, ys}:
      List.all.if(u => Shared.List.is_eq(~Char, ~Char.is_eq, xs, ys), Shared.Bool.is_eq(n, m))
    case _ _:
      False{}

# Atom.is_eq is True for an atom and itself
def Atom.is_eq_refl(a: Atom) -> {Atom.is_eq(a, a) == True{}: Bool}:
  match a:
    case ALit{x}:
      Shared.Char.is_eq_refl(x)
    case AAny{}:
      {==}
    case AClass{+n, +xs}:
      Shared.List.all.if_both(
        Shared.Bool.is_eq(n, n),
        u => Shared.List.is_eq(~Char, ~Char.is_eq, xs, xs)
      )(
        Shared.Bool.is_eq_refl(n)
      )(Shared.List.is_eq_refl(~Char, ~Char.is_eq, ~Shared.Char.laws(), xs))

# Atom.is_eq is True only for the same atom
def Atom.is_eq_sound(a: Atom, b: Atom) -> {Atom.is_eq(a, b) == True{}: Bool} -> {a == b: Atom}:
  match a b:
    case ALit{x} ALit{y}:
      h => Equal.cong(Char, Atom, u => ALit{u}, x, y, Shared.Char.is_eq_sound(x, y)(h))
    case ALit{x} AAny{}:
      h => Empty.absurd({ALit{x} == AAny{}: Atom}, Shared.Bool.false_ne_true(h))
    case ALit{x} AClass{m, ys}:
      h => Empty.absurd({ALit{x} == AClass{m, ys}: Atom}, Shared.Bool.false_ne_true(h))
    case AAny{} ALit{y}:
      h => Empty.absurd({AAny{} == ALit{y}: Atom}, Shared.Bool.false_ne_true(h))
    case AAny{} AAny{}:
      h => {==}
    case AAny{} AClass{m, ys}:
      h => Empty.absurd({AAny{} == AClass{m, ys}: Atom}, Shared.Bool.false_ne_true(h))
    case AClass{n, xs} ALit{y}:
      h => Empty.absurd({AClass{n, xs} == ALit{y}: Atom}, Shared.Bool.false_ne_true(h))
    case AClass{n, xs} AAny{}:
      h => Empty.absurd({AClass{n, xs} == AAny{}: Atom}, Shared.Bool.false_ne_true(h))
    case AClass{+n, +xs} AClass{+m, +ys}:
      +h =>
        +same_n = Shared.Bool.is_eq(n, m)
        %Shared.Bool.is_eq_sound(
          n,
          m
        )(
          Shared.List.all.if_hit(same_n, u => Shared.List.is_eq(~Char, ~Char.is_eq, xs, ys))(h)
        ): {AClass{n, xs} == AClass{_, ys}: Atom}
        %Shared.List.is_eq_sound(
          ~Char,
          ~Char.is_eq,
          ~Shared.Char.laws(),
          xs,
          ys
        )(
          Shared.List.all.if_rest(same_n, u => Shared.List.is_eq(~Char, ~Char.is_eq, xs, ys))(h)
        ): {AClass{n, xs} == AClass{n, _}: Atom}
        {==}

# the laws of Atom.is_eq
def Atom.laws() -> Shared.Eq.Laws(Atom, Atom.is_eq):
  (Atom.is_eq_refl, Atom.is_eq_sound)

# the key of t: a bit or two for its form, then its parts
def Atom.key(t: Atom) -> List<&2, Bool>:
  match t:
    case ALit{Chr{x}}:
      False{} <> Tries.Trie.char(x)
    case AAny{}:
      [True{}, False{}]
    case AClass{neg, cs}:
      True{} <> True{} <> neg <> Tries.Trie.text(String.from_list(cs))

# Fast matching
# -------------
# Spec.Rule.selects asks each glob through Spec.Glob.matches, whose
# derivatives are not normalized, so a '*' makes its cost grow fast with the
# path. Glob.accepts steps the deduplicated derivative lists of regex.bend,
# for the same answer.

# g matches the characters w
def Glob.accepts(w: List<&2, Char>, g: Spec.Glob) -> Bool:
  Regex.Re.accepts(~Char, ~Atom, ~Atom.hit, ~Atom.is_eq, ~Atom.key, w, Glob.re(g))

# Glob.accepts gives the answer of Spec.Glob.matches
def Glob.accepts_ok(
  +p: String,
  +g: Spec.Glob
) -> {Glob.accepts(String.to_list(p), g) == Spec.Glob.matches(p, g): Bool}:
  Equal.trans(
    Bool,
    Glob.accepts(String.to_list(p), g),
    Regex.Re.matches(~Char, ~Atom, ~Atom.hit, String.to_list(p), Glob.re(g)),
    Spec.Glob.matches(p, g),
    Regex.Re.accepts_matches(
      ~Char,
      ~Atom,
      ~Atom.hit,
      ~Atom.is_eq,
      ~Atom.key,
      ~Atom.laws(),
      String.to_list(p),
      Glob.re(g)
    ),
    Glob.re_matches(p, g)
  )

# the answer for the characters w after rules, given the answer acc before
# them
def Rule.selects.fast.go(rules: List<&2, Spec.Rule>, +w: List<&2, Char>, acc: Bool) -> Bool:
  match rules acc:
    case Nil{} _:
      acc
    case Con{Spec.Include{g}, t} False{}:
      Rule.selects.fast.go(t, w, Glob.accepts(w, g))
    case Con{Spec.Include{g}, t} True{}:
      Rule.selects.fast.go(t, w, True{})
    case Con{Spec.Exclude{g}, t} False{}:
      Rule.selects.fast.go(t, w, False{})
    case Con{Spec.Exclude{g}, t} True{}:
      Rule.selects.fast.go(t, w, Bool.not(Glob.accepts(w, g)))

# Rule.selects.fast.go gives the answer of Spec.Rule.selects.go
def Rule.selects_fast_ok.go(
  rules: List<&2, Spec.Rule>,
  +p: String,
  acc: Bool
) -> {
  Rule.selects.fast.go(rules, String.to_list(p), acc) == Spec.Rule.selects.go(rules, p, acc): Bool
}:
  match rules acc:
    case Nil{} _:
      {==}
    case Con{Spec.Include{+g}, t} False{}:
      %Glob.accepts_ok(
        p,
        g
      ): {
        Rule.selects.fast.go(
          t,
          String.to_list(p),
          Glob.accepts(String.to_list(p), g)
        )
          == Spec.Rule.selects.go(t, p, _): Bool
      }
      Rule.selects_fast_ok.go(t, p, Glob.accepts(String.to_list(p), g))
    case Con{Spec.Include{g}, t} True{}:
      Rule.selects_fast_ok.go(t, p, True{})
    case Con{Spec.Exclude{g}, t} False{}:
      Rule.selects_fast_ok.go(t, p, False{})
    case Con{Spec.Exclude{+g}, +t} True{}:
      %Glob.accepts_ok(
        p,
        g
      ): {
        Rule.selects.fast.go(
          t,
          String.to_list(p),
          Bool.not(Glob.accepts(String.to_list(p), g))
        )
          == Spec.Rule.selects.go(t, p, Bool.not(_)): Bool
      }
      Rule.selects_fast_ok.go(t, p, Bool.not(Glob.accepts(String.to_list(p), g)))

# rules select p: Spec.Rule.selects, by Glob.accepts
def Rule.selects.fast(rules: List<&2, Spec.Rule>, p: String) -> Bool:
  Rule.selects.fast.go(rules, String.to_list(p), False{})

# the fast selection gives the answer of Spec.Rule.selects
def Rule.selects_fast_ok(
  rules: List<&2, Spec.Rule>,
  p: String
) -> {Rule.selects.fast(rules, p) == Spec.Rule.selects(rules, p): Bool}:
  Rule.selects_fast_ok.go(rules, p, False{})

# p is a valid path that answers q: Spec.Query.holds, by the fast selection
def Query.holds.fast(q: Spec.Query, +p: String) -> Bool:
  match q:
    case Spec.Both{a, b}:
      List.all.if(
        u => List.all.if(u2 => Rule.selects.fast(b, p), Rule.selects.fast(a, p)),
        Spec.is_path(p)
      )
    case Spec.Only{a, b}:
      List.all.if(
        u => List.all.if(u2 => Bool.not(Rule.selects.fast(b, p)), Rule.selects.fast(a, p)),
        Spec.is_path(p)
      )

# Query.holds.fast gives the answer of Spec.Query.holds
def Query.holds_fast_ok(
  q: Spec.Query,
  +p: String
) -> {Query.holds.fast(q, p) == Spec.Query.holds(q, p): Bool}:
  match q:
    case Spec.Both{+a, +b}:
      v = Spec.is_path(p)
      +sa = Spec.Rule.selects(a, p)
      +sb = Spec.Rule.selects(b, p)
      fa = Rule.selects.fast(a, p)
      fb = Rule.selects.fast(b, p)
      %Shared.List.all.if_and(
        sa,
        u => sb
      ): {List.all.if(u => List.all.if(u2 => fb, fa), v) == Bool.and(v, _): Bool}
      %Shared.List.all.if_and(
        v,
        u => List.all.if(u2 => sb, sa)
      ): {List.all.if(u => List.all.if(u2 => fb, fa), v) == _: Bool}
      %Rule.selects_fast_ok(
        a,
        p
      ): {
        List.all.if(
          u => List.all.if(u2 => fb, fa),
          v
        )
          == List.all.if(u => List.all.if(u2 => sb, _), v): Bool
      }
      %Rule.selects_fast_ok(
        b,
        p
      ): {
        List.all.if(
          u => List.all.if(u2 => fb, fa),
          v
        )
          == List.all.if(u => List.all.if(u2 => _, fa), v): Bool
      }
      {==}
    case Spec.Only{+a, +b}:
      v = Spec.is_path(p)
      +sa = Spec.Rule.selects(a, p)
      +sb = Bool.not(Spec.Rule.selects(b, p))
      fa = Rule.selects.fast(a, p)
      fb = Rule.selects.fast(b, p)
      %Shared.List.all.if_and(
        sa,
        u => sb
      ): {List.all.if(u => List.all.if(u2 => Bool.not(fb), fa), v) == Bool.and(v, _): Bool}
      %Shared.List.all.if_and(
        v,
        u => List.all.if(u2 => sb, sa)
      ): {List.all.if(u => List.all.if(u2 => Bool.not(fb), fa), v) == _: Bool}
      %Rule.selects_fast_ok(
        a,
        p
      ): {
        List.all.if(
          u => List.all.if(u2 => Bool.not(fb), fa),
          v
        )
          == List.all.if(u => List.all.if(u2 => sb, _), v): Bool
      }
      %Rule.selects_fast_ok(
        b,
        p
      ): {
        List.all.if(
          u => List.all.if(u2 => Bool.not(fb), fa),
          v
        )
          == List.all.if(u => List.all.if(u2 => Bool.not(_), fa), v): Bool
      }
      {==}

# Search states
# -------------
# A rule as the derivative lists (Seqs) of its glob, and a state of the
# search as the rules of both lists of a query. A state reads a path one
# character at a time.

# A rule whose glob is a list of Seqs.
type Slot is Data:
  Inc{xs: List<&2, List<&2, Regex.Re<Atom>>>}
  Exc{xs: List<&2, List<&2, Regex.Re<Atom>>>}

# the answer for the characters w after slots, given the answer acc before
# them
def Slot.selects.go(slots: List<&2, Slot>, +w: List<&2, Char>, acc: Bool) -> Bool:
  match slots acc:
    case Nil{} _:
      acc
    case Con{Inc{xs}, t} False{}:
      Slot.selects.go(t, w, Regex.Seqs.matches(~Char, ~Atom, ~Atom.hit, xs, w))
    case Con{Inc{xs}, t} True{}:
      Slot.selects.go(t, w, True{})
    case Con{Exc{xs}, t} False{}:
      Slot.selects.go(t, w, False{})
    case Con{Exc{xs}, t} True{}:
      Slot.selects.go(t, w, Bool.not(Regex.Seqs.matches(~Char, ~Atom, ~Atom.hit, xs, w)))

# the slots of rules
def Slot.of_rules(rules: List<&2, Spec.Rule>) -> List<&2, Slot>:
  match rules:
    case Nil{}:
      Nil{}
    case Con{Spec.Include{g}, t}:
      Con{Inc{[[Glob.re(g)]]}, Slot.of_rules(t)}
    case Con{Spec.Exclude{g}, t}:
      Con{Exc{[[Glob.re(g)]]}, Slot.of_rules(t)}

# the slots after c
def Slot.step(slots: List<&2, Slot>, +c: Char) -> List<&2, Slot>:
  match slots:
    case Nil{}:
      Nil{}
    case Con{Inc{xs}, t}:
      Con{
        Inc{Regex.Seqs.step(~Char, ~Atom, ~Atom.hit, ~Atom.is_eq, ~Atom.key, xs, c)},
        Slot.step(t, c)
      }
    case Con{Exc{xs}, t}:
      Con{
        Exc{Regex.Seqs.step(~Char, ~Atom, ~Atom.hit, ~Atom.is_eq, ~Atom.key, xs, c)},
        Slot.step(t, c)
      }

# the one-Seq list of g matches what g matches
def Glob.single_ok(
  +p: String,
  +g: Spec.Glob
) -> {
  Spec.Glob.matches(
    p,
    g
  )
    == Regex.Seqs.matches(~Char, ~Atom, ~Atom.hit, [[Glob.re(g)]], String.to_list(p)): Bool
}:
  Equal.sym(
    Bool,
    Regex.Seqs.matches(~Char, ~Atom, ~Atom.hit, [[Glob.re(g)]], String.to_list(p)),
    Spec.Glob.matches(p, g),
    Equal.trans(
      Bool,
      Regex.Seqs.matches(~Char, ~Atom, ~Atom.hit, [[Glob.re(g)]], String.to_list(p)),
      Regex.Re.matches(~Char, ~Atom, ~Atom.hit, String.to_list(p), Glob.re(g)),
      Spec.Glob.matches(p, g),
      Regex.Seqs.matches_one(~Char, ~Atom, ~Atom.hit, String.to_list(p), Glob.re(g)),
      Glob.re_matches(p, g)
    )
  )

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
        ~Atom,
        ~Atom.hit,
        Regex.Seqs.step(~Char, ~Atom, ~Atom.hit, ~Atom.is_eq, ~Atom.key, xs, c),
        t
      )
      %Regex.Seqs.matches_step(
        ~Char,
        ~Atom,
        ~Atom.hit,
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
        ~Atom,
        ~Atom.hit,
        Regex.Seqs.step(~Char, ~Atom, ~Atom.hit, ~Atom.is_eq, ~Atom.key, xs, c),
        t
      )
      %Regex.Seqs.matches_step(
        ~Char,
        ~Atom,
        ~Atom.hit,
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

# State equality and keys
# -----------------------

# xs and ys are the same Seqs
def Seqs.is_eq(
  xs: List<&2, List<&2, Regex.Re<Atom>>>,
  ys: List<&2, List<&2, Regex.Re<Atom>>>
) -> Bool:
  Shared.List.is_eq(~List<&2, Regex.Re<Atom>>, ~Regex.Seq.is_eq(~Atom, ~Atom.is_eq), xs, ys)

# the laws of Seqs.is_eq
def Seqs.laws() -> Shared.Eq.Laws(List<&2, List<&2, Regex.Re<Atom>>>, Seqs.is_eq):
  (
    xs => Shared.List.is_eq_refl(
      ~List<&2, Regex.Re<Atom>>,
      ~Regex.Seq.is_eq(~Atom, ~Atom.is_eq),
      ~Regex.Seq.laws(~Atom, ~Atom.is_eq, ~Atom.laws()),
      xs
    ),
    xs => ys => Shared.List.is_eq_sound(
      ~List<&2, Regex.Re<Atom>>,
      ~Regex.Seq.is_eq(~Atom, ~Atom.is_eq),
      ~Regex.Seq.laws(~Atom, ~Atom.is_eq, ~Atom.laws()),
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
      Shared.Eq.refl(~List<&2, List<&2, Regex.Re<Atom>>>, ~Seqs.is_eq, Seqs.laws(), x)
    case Exc{x}:
      Shared.Eq.refl(~List<&2, List<&2, Regex.Re<Atom>>>, ~Seqs.is_eq, Seqs.laws(), x)

# Slot.is_eq is True only for the same slot
def Slot.is_eq_sound(a: Slot, b: Slot) -> {Slot.is_eq(a, b) == True{}: Bool} -> {a == b: Slot}:
  match a b:
    case Inc{x} Inc{y}:
      h => Equal.cong(
        List<&2, List<&2, Regex.Re<Atom>>>,
        Slot,
        u => Inc{u},
        x,
        y,
        Shared.Eq.sound(~List<&2, List<&2, Regex.Re<Atom>>>, ~Seqs.is_eq, Seqs.laws(), x, y)(h)
      )
    case Inc{x} Exc{y}:
      h => Empty.absurd({Inc{x} == Exc{y}: Slot}, Shared.Bool.false_ne_true(h))
    case Exc{x} Inc{y}:
      h => Empty.absurd({Exc{x} == Inc{y}: Slot}, Shared.Bool.false_ne_true(h))
    case Exc{x} Exc{y}:
      h => Equal.cong(
        List<&2, List<&2, Regex.Re<Atom>>>,
        Slot,
        u => Exc{u},
        x,
        y,
        Shared.Eq.sound(~List<&2, List<&2, Regex.Re<Atom>>>, ~Seqs.is_eq, Seqs.laws(), x, y)(h)
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

# the laws of St.is_eq
def St.laws() -> Shared.Eq.Laws(St, St.is_eq):
  (St.is_eq_refl, St.is_eq_sound)

# the key of xs, then rest: True before each Seq, False after the last
def Seqs.key(xs: List<&2, List<&2, Regex.Re<Atom>>>, rest: List<&2, Bool>) -> List<&2, Bool>:
  match xs:
    case Nil{}:
      False{} <> rest
    case Con{s, r}:
      True{} <> Regex.Seq.key.go(~Atom, ~Atom.key, s, Seqs.key(r, rest))

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

# Representative characters
# -------------------------
# The search moves a state only under the characters that the globs of the
# query name, '/', and one more character f that they do not name. A
# character that is not named moves a state as f does.

# The named characters cs, and the character f.
type Abc is Data:
  Abc{cs: List<&2, Char>, f: Char}

# the characters that the search moves a state under
def Abc.syms(g: Abc) -> List<&2, Char>:
  match g:
    case Abc{cs, f}:
      f <> cs

# The machine that the search runs: a state reads one character.
def Abc.step(g: Abc, x: St, c: Char) -> St:
  St.step(x, c)

# the machine accepts at x when x holds for ""
def Abc.ends(g: Abc, x: St) -> Bool:
  St.holds(x, [])

# cs holds c
def Chars.has(cs: List<&2, Char>, c: Char) -> Bool:
  List.contains(~Char, ~Char.is_eq, cs, c)

# every character that t names is in cs
def Atom.within(cs: List<&2, Char>, t: Atom) -> Bool:
  match t:
    case ALit{x}:
      Chars.has(cs, x)
    case AAny{}:
      True{}
    case AClass{neg, xs}:
      Reaches.Reach.within(~Char, ~Char.is_eq, xs, cs)

# every character that slots name is in cs
def Slots.within(slots: List<&2, Slot>, +cs: List<&2, Char>) -> Bool:
  match slots:
    case Nil{}:
      True{}
    case Con{Inc{xs}, t}:
      List.all.if(
        u => Slots.within(t, cs),
        Regex.Seqs.holds(~Atom, ~List<&2, Char>, ~Atom.within, xs, cs)
      )
    case Con{Exc{xs}, t}:
      List.all.if(
        u => Slots.within(t, cs),
        Regex.Seqs.holds(~Atom, ~List<&2, Char>, ~Atom.within, xs, cs)
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

# a character that cs lacks is not '/', when cs holds '/'
def Char.inner_out(
  cs: List<&2, Char>,
  +c: Char,
  hs: {Chars.has(cs, '/') == True{}: Bool},
  hc: {Chars.has(cs, c) == False{}: Bool}
) -> {Spec.is_inner(c) == True{}: Bool}:
  %Equal.sym(
    Bool,
    Char.is_eq(c, '/'),
    False{},
    Shared.Eq.ne_flip(
      ~Char,
      ~Char.is_eq,
      ~Shared.Char.laws(),
      '/',
      c,
      Shared.List.contains_ne(~Char, ~Char.is_eq, ~Shared.Char.laws(), cs, '/', c, hs, hc)
    )
  ): {Bool.not(_) == True{}: Bool}
  {==}

# an atom whose characters are in cs accepts c exactly when it accepts f,
# two characters that cs lacks, when cs holds '/'
def Atom.alike(
  +cs: List<&2, Char>,
  +c: Char,
  +f: Char,
  t: Atom,
  +hn: {Chars.near(cs, c, f) == True{}: Bool},
  hp: {Atom.within(cs, t) == True{}: Bool}
) -> {Atom.hit(t, c) == Atom.hit(t, f): Bool}:
  match t:
    case ALit{+x}:
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
    case AAny{}:
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
    case AClass{neg, +xs}:
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
        +wx = Regex.Seqs.holds(~Atom, ~List<&2, Char>, ~Atom.within, xs, cs)
        +xc = Regex.Seqs.step(~Char, ~Atom, ~Atom.hit, ~Atom.is_eq, ~Atom.key, xs, c)
        +tc = Slot.step(t, c)
        %Regex.Seqs.step_alike(
          ~Char,
          ~Atom,
          ~List<&2, Char>,
          ~Atom.hit,
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
        +wx = Regex.Seqs.holds(~Atom, ~List<&2, Char>, ~Atom.within, xs, cs)
        +xc = Regex.Seqs.step(~Char, ~Atom, ~Atom.hit, ~Atom.is_eq, ~Atom.key, xs, c)
        +tc = Slot.step(t, c)
        %Regex.Seqs.step_alike(
          ~Char,
          ~Atom,
          ~List<&2, Char>,
          ~Atom.hit,
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

# cs holds '/' and not f
def Abc.fits(g: Abc) -> Bool:
  match g:
    case Abc{+cs, f}:
      List.all.if(u => Bool.not(Chars.has(cs, f)), Chars.has(cs, '/'))

# g fits, and every character that x names is in its cs
def St.covers(g: Abc, x: St) -> Bool:
  match g x:
    case Abc{+cs, f} St{both, a, b}:
      List.all.if(
        u => List.all.if(u2 => Slots.within(b, cs), Slots.within(a, cs)),
        Abc.fits(Abc{cs, f})
      )

# St.rep, once it is known if f <> cs holds c (known)
def St.rep.at(
  +cs: List<&2, Char>,
  +f: Char,
  both: Bool,
  +a: List<&2, Slot>,
  +b: List<&2, Slot>,
  +c: Char,
  known: Bool,
  +h: {St.covers(Abc{cs, f}, St{both, a, b}) == True{}: Bool}
) -> {
  Chars.has(f <> cs, c) == known: Bool
} -> (
  &d: Char -> {
    List.contains(~Char, ~Char.is_eq, f <> cs, d) == True{}: Bool
  }
    & {St.step(St{both, a, b}, c) == St.step(St{both, a, b}, d): St}
):
  match known:
    case True{}:
      e => (c, (e, {==}))
    case False{}:
      e =>
        +wa = Slots.within(a, cs)
        +wb = Slots.within(b, cs)
        +has_s = Chars.has(cs, '/')
        +no_f = Bool.not(Chars.has(cs, f))
        +no_c = Bool.not(Chars.has(cs, c))
        +fits = Shared.List.all.if_hit(
          List.all.if(u => no_f, has_s),
          u => List.all.if(u2 => wb, wa)
        )(h)
        +within = Shared.List.all.if_rest(
          List.all.if(u => no_f, has_s),
          u => List.all.if(u2 => wb, wa)
        )(h)
        hc = Shared.List.any.if_false_rest(Char.is_eq(f, c), u => Chars.has(cs, c))(e)
        +hn = {
          Shared.List.all.if_both(
            has_s,
            u => List.all.if(u2 => no_f, no_c)
          )(
            Shared.List.all.if_hit(has_s, u => no_f)(fits)
          )(
            Shared.List.all.if_both(
              no_c,
              u2 => no_f
            )(
              Equal.cong(Bool, Bool, v => Bool.not(v), Chars.has(cs, c), False{}, hc)
            )(Shared.List.all.if_rest(has_s, u => no_f)(fits))
          ): {Chars.near(cs, c, f) == True{}: Bool}
        }
        +ac = Slot.step(a, c)
        +bc = Slot.step(b, c)
        (f, ({
              %Equal.sym(Bool, Char.is_eq(f, f), True{}, Shared.Char.is_eq_refl(f)): {List.any.if(u => List.contains(~Char, ~Char.is_eq, cs, f), _) == True{}: Bool}
              {==}
              : {List.contains(~Char, ~Char.is_eq, f <> cs, f) == True{}: Bool}}, {
              %Slot.step_alike(a, cs, c, f, hn)(Shared.List.all.if_hit(wa, u2 => wb)(within)): {St{both, ac, bc} == St{both, _, Slot.step(b, f)}: St}
              %Slot.step_alike(b, cs, c, f, hn)(Shared.List.all.if_rest(wa, u2 => wb)(within)): {St{both, ac, bc} == St{both, ac, _}: St}
              {==}
              : {St{both, ac, bc} == St{both, Slot.step(a, f), Slot.step(b, f)}: St}}))

# under a state that g covers, each character moves the machine as some
# character of Abc.syms(g) does
def St.rep(
  g: Abc,
  x: St,
  c: Char,
  h: {St.covers(g, x) == True{}: Bool}
) -> (
  &d: Char -> {
    List.contains(~Char, ~Char.is_eq, Abc.syms(g), d) == True{}: Bool
  }
    & {Abc.step(g, x, c) == Abc.step(g, x, d): St}
):
  match g x:
    case Abc{+cs, +f} St{both, a, b}:
      +c = c
      St.rep.at(cs, f, both, a, b, c, Chars.has(f <> cs, c), h)({==})

# the machine accepts w from x exactly when x holds for w
def St.accepts_ok(
  w: List<&2, Char>,
  +x: St,
  g: Abc
) -> {
  Searches.Machine.accepts(~St, ~Char, ~Abc, ~Abc.step, ~Abc.ends, w, x, g) == St.holds(x, w): Bool
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
          ~St,
          ~Char,
          ~Abc,
          ~Abc.step,
          ~Abc.ends,
          t,
          St.step(x, c),
          g
        )
          == _: Bool
      }
      St.accepts_ok(t, St.step(x, c), g)

# Search
# ------
# The search needs no proof: `decide` checks what it returns. Phase one
# visits the states that the start state can reach; when none holds for "",
# they are a certificate. Else phase two looks for a valid path that holds,
# guided by an automaton of valid paths.

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

# '/' and the characters that the globs of a and b name, each once
def Rules.abc_chars(a: List<&2, Spec.Rule>, b: List<&2, Spec.Rule>) -> List<&2, Char>:
  KeySets.KeySet.unique(
    ~Char,
    ~Char.is_eq,
    ~Char.key,
    '/' <> Rules.chars(a, Rules.chars(b, [])),
    Tries.Trie.new(Char)
  )

# '/' and the characters that the globs of q name, each once
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

# Where a valid path is: at a segment start, after "." or "..", inside a
# valid segment, or past a mistake.
type Path is Data:
  PStart{}
  PDot{}
  PDots{}
  PSeg{}
  PDead{}
# What a character is to a path: '/', '.', a banned character, or another.
type Role is Data:
  KSlash{}
  KDot{}
  KBad{}
  KOther{}
# what c is to a path
def Role.of(c: Char) -> Role:
  match c:
    case Chr{+x}:
      Bool.pick(
        Role,
        U32.is_eq(x, 47),
        KSlash{},
        Bool.pick(
          Role,
          U32.is_eq(x, 46),
          KDot{},
          Bool.pick(Role, Bool.or(U32.is_eq(x, 0), U32.is_eq(x, 92)), KBad{}, KOther{})
        )
      )
# where a path is after a character of kind k
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
# a and b are the same place
def Path.is_eq(a: Path, b: Path) -> Bool:
  match a b:
    case PStart{} PStart{}:
      True{}
    case PDot{} PDot{}:
      True{}
    case PDots{} PDots{}:
      True{}
    case PSeg{} PSeg{}:
      True{}
    case PDead{} PDead{}:
      True{}
    case _ _:
      False{}
# a valid path can end here
def Path.is_end(s: Path) -> Bool:
  match s:
    case PSeg{}:
      True{}
    case _:
      False{}
# the key of a place
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

# A place of phase two: where the path is, with the state; or past a
# mistake of the path (Dead), where the state does not matter.
type Walk is Data:
  Dead{}
  At{at: Path, x: St}

# the place after c, once the path is at a
def Walk.at(a: Path, x: St, c: Char) -> Walk:
  match a:
    case PDead{}:
      Dead{}
    case other:
      At{other, St.step(x, c)}

# The machine of phase two: the place after c.
def Walk.step(g: Abc, w: Walk, c: Char) -> Walk:
  match w:
    case Dead{}:
      Dead{}
    case At{a, x}:
      +c = c
      Walk.at(Path.step(a, Role.of(c)), x, c)

# a valid path that the state holds for can end here
def Walk.ends(g: Abc, w: Walk) -> Bool:
  match w:
    case Dead{}:
      False{}
    case At{a, x}:
      List.all.if(u => St.holds(x, []), Path.is_end(a))

# v and w are the same place
def Walk.is_eq(v: Walk, w: Walk) -> Bool:
  match v w:
    case Dead{} Dead{}:
      True{}
    case At{a, x} At{b, y}:
      List.all.if(u => St.is_eq(x, y), Path.is_eq(a, b))
    case _ _:
      False{}

# the key of a place
def Walk.key(w: Walk) -> List<&2, Bool>:
  match w:
    case Dead{}:
      [False{}]
    case At{a, x}:
      True{} <> List.append(&2, Bool, Path.key(a), St.key(x))

# the characters that phase two moves under: those of phase one, and a
# letter, as f may be a character that a path may not hold
def Abc.path_syms(g: Abc) -> List<&2, Char>:
  'x' <> Abc.syms(g)

# What the search found: a path to check, a certificate to check, or neither.
type Outcome is Data:
  Witness{path: String}
  Proof{xs: List<&2, St>, g: Abc}
  NoAnswer{}

# the states a search may visit before it gives up
def Search.fuel() -> Nat:
  4096n
# what phase two found
def Search.run.walked(found: Searches.Found<Walk, Char>) -> Outcome:
  match found:
    case Searches.Hit{w}:
      Witness{String.from_list(w)}
    case Searches.Closed{xs}:
      NoAnswer{}
    case Searches.Out{}:
      NoAnswer{}

# phase two, from the state x0
def Search.run.paths(x0: St, g: Abc) -> Outcome:
  Search.run.walked(
    Searches.Search.run(
      ~Walk,
      ~Char,
      ~Abc,
      ~Walk.is_eq,
      ~Walk.key,
      ~Walk.step,
      ~Walk.ends,
      ~Abc.path_syms,
      Search.fuel(),
      At{PStart{}, x0},
      g
    )
  )

# the certificate of phase one, or phase two when there is none
def Search.run.closed(x0: St, g: Abc, found: Searches.Found<St, Char>) -> Outcome:
  match found:
    case Searches.Closed{xs}:
      Proof{xs, g}
    case Searches.Hit{w}:
      Search.run.paths(x0, g)
    case Searches.Out{}:
      Search.run.paths(x0, g)

# what the search finds for q
def Search.run(+q: Spec.Query) -> Outcome:
  +x0 = St.of(q)
  +g = Query.abc(q)
  Search.run.closed(
    x0,
    g,
    Searches.Search.run(
      ~St,
      ~Char,
      ~Abc,
      ~St.is_eq,
      ~St.key,
      ~Abc.step,
      ~Abc.ends,
      ~Abc.syms,
      Search.fuel(),
      x0,
      g
    )
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
def Search.proves(q: Spec.Query, xs: List<&2, St>, g: Abc) -> Bool:
  Searches.Cert.proves(
    ~St,
    ~Char,
    ~Abc,
    ~St.is_eq,
    ~St.key,
    ~Abc.step,
    ~Abc.ends,
    ~St.covers,
    ~Abc.syms,
    xs,
    St.of(q),
    g
  )

# the answer to q, from what the search found, once checked
def Search.decide(q: Spec.Query, r: Outcome) -> Spec.Search:
  match r:
    case Witness{+p}:
      Search.found_if(p, Query.holds.fast(q, p))
    case Proof{xs, g}:
      Search.absent_if(Search.proves(q, xs, g))
    case NoAnswer{}:
      Spec.Unknown{}

def Spec.Query.search(q):
  +q = q
  Search.decide(q, Search.run(q))

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
  b: Bool
) -> {
  Query.holds.fast(q, p0) == b: Bool
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
          Query.holds.fast(q, p0),
          True{},
          Equal.sym(
            Bool,
            Query.holds.fast(q, p0),
            Spec.Query.holds(q, p0),
            Query.holds_fast_ok(q, p0)
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
  r: Outcome,
  p: String
) -> {
  Search.decide(q, r) == Spec.Found{p}: Spec.Search
} -> {Spec.Query.holds(q, p) == True{}: Bool}:
  match r:
    case Witness{+p0}:
      h => Search.found_if_found(q, p0, p, Query.holds.fast(q, p0))({==}, h)
    case Proof{xs, g}:
      h => Empty.absurd(
        {Spec.Query.holds(q, p) == True{}: Bool},
        Search.absent_if_found(Search.proves(q, xs, g), p)(h)
      )
    case NoAnswer{}:
      h => Empty.absurd(
        {Spec.Query.holds(q, p) == True{}: Bool},
        Search.ne_found(Spec.Unknown{}, p, Unit{}, h)
      )

# absent_if answers Absent only for a certificate for q, given b: its check
def Search.absent_if_absent(
  +q: Spec.Query,
  xs: List<&2, St>,
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
        +w = String.to_list(p)
        none = Equal.trans(
          Bool,
          St.holds(St.of(q), w),
          Searches.Machine.accepts(~St, ~Char, ~Abc, ~Abc.step, ~Abc.ends, w, St.of(q), g),
          False{},
          Equal.sym(
            Bool,
            Searches.Machine.accepts(~St, ~Char, ~Abc, ~Abc.step, ~Abc.ends, w, St.of(q), g),
            St.holds(St.of(q), w),
            St.accepts_ok(w, St.of(q), g)
          ),
          Searches.Cert.sound(
            ~St,
            ~Char,
            ~Abc,
            ~St.is_eq,
            ~St.key,
            ~Char.is_eq,
            ~Abc.step,
            ~Abc.ends,
            ~St.covers,
            ~Abc.syms,
            ~St.laws(),
            ~Shared.Char.laws(),
            ~St.rep,
            xs,
            St.of(q),
            g,
            w
          )(e)
        )
        %St.of_ok(q, p): {_ == False{}: Bool}
        %Equal.sym(
          Bool,
          St.holds(St.of(q), w),
          False{},
          none
        ): {Bool.and(Spec.is_path(p), _) == False{}: Bool}
        Shared.Bool.and_false_right(Spec.is_path(p))

# an Absent answer of decide means no path holds
def Search.decide_absent(
  +q: Spec.Query,
  r: Outcome,
  p: String
) -> {
  Search.decide(q, r) == Spec.Absent{}: Spec.Search
} -> {Spec.Query.holds(q, p) == False{}: Bool}:
  match r:
    case Witness{p0}:
      h => Empty.absurd(
        {Spec.Query.holds(q, p) == False{}: Bool},
        Search.found_if_absent(p0, Query.holds.fast(q, p0))(h)
      )
    case Proof{+xs, +g}:
      h => Search.absent_if_absent(q, xs, g, p, Search.proves(q, xs, g))({==}, h)
    case NoAnswer{}:
      h => Empty.absurd(
        {Spec.Query.holds(q, p) == False{}: Bool},
        Search.ne_absent(Spec.Unknown{}, Unit{}, h)
      )

def Spec.search_found(q, p, h):
  +q = q
  Search.decide_found(q, Search.run(q), p)(h)

def Spec.search_absent(q, p, h):
  +q = q
  Search.decide_absent(q, Search.run(q), p)(h)

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

# Cat congruence
# --------------
# A proof that two globs match the same strings is a function, which Bend
# may use only once. So Cat congruence takes the finitely many equalities it
# needs for one string as data: the left sides agree on each prefix, the
# right sides on each suffix.

# what x must still match after it reads w
def Glob.walk(w: String, x: Spec.Glob) -> Spec.Glob:
  match w:
    case SNil{}:
      x
    case SCon{c, t}:
      Glob.walk(t, Spec.Glob.step(x, c))

# x matches w when what x must match after w matches ""
def Glob.walk_null(
  w: String,
  x: Spec.Glob
) -> {Spec.Glob.matches(w, x) == Spec.Glob.is_nullable(Glob.walk(w, x)): Bool}:
  match w:
    case SNil{}:
      {==}
    case SCon{c, t}:
      Glob.walk_null(t, Spec.Glob.step(x, c))

# walking pre then c is stepping by c after walking pre
def Glob.walk_snoc(
  pre: String,
  c: Char,
  x: Spec.Glob
) -> {
  Glob.walk(
    String.append(pre, SCon{c, SNil{}}),
    x
  )
    == Spec.Glob.step(Glob.walk(pre, x), c): Spec.Glob
}:
  match pre:
    case SNil{}:
      {==}
    case SCon{d, t}:
      Glob.walk_snoc(t, c, Spec.Glob.step(x, d))

# x matches pre and y matches what follows, at some cut of suf after pre
# bend-lint: expect-begin bend-lint-rules/performance/append_in_loop@warning -- only proofs use it; no program runs it
# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- only proofs use it; no program runs it
def Glob.split(suf: String, +pre: String, +x: Spec.Glob, +y: Spec.Glob) -> Bool:
  match suf:
    case SNil{}:
      Bool.or(Bool.and(Spec.Glob.matches(pre, x), Spec.Glob.matches(SNil{}, y)), False{})
    case SCon{+c, +t}:
      here = Bool.and(Spec.Glob.matches(pre, x), Spec.Glob.matches(SCon{c, t}, y))
      Bool.or(here, Glob.split(t, String.append(pre, SCon{c, SNil{}}), x, y))
# bend-lint: expect-end bend-lint-rules/performance/append_in_loop@warning
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# Cat{x after pre, y} matches suf exactly when some cut does
# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- only proofs use it; no program runs it
def Glob.cat_split(
  suf: String,
  +pre: String,
  +x: Spec.Glob,
  +y: Spec.Glob
) -> {Glob.split(suf, pre, x, y) == Spec.Glob.matches(suf, Spec.Cat{Glob.walk(pre, x), y}): Bool}:
  match suf:
    case SNil{}:
      l = Glob.split(SNil{}, pre, x, y)
      %Glob.walk_null(pre, x): {l == Bool.and(_, Spec.Glob.is_nullable(y)): Bool}
      +m = Bool.and(Spec.Glob.matches(pre, x), Spec.Glob.is_nullable(y))
      Equal.sym(Bool, m, Bool.or(m, False{}), Shared.Bool.or_false(m))
    case SCon{+c, +t}:
      +wx = Glob.walk(pre, x)
      +pc = String.append(pre, SCon{c, SNil{}})
      +ny = Spec.Glob.step(y, c)
      l = Glob.split(SCon{c, t}, pre, x, y)
      %Glob.alt_or(
        t,
        Spec.Cat{Spec.Glob.step(wx, c), y},
        Spec.Cat{Spec.Glob.of_bool(Spec.Glob.is_nullable(wx)), ny}
      ): {l == _: Bool}
      %Glob.cat_of_bool(
        t,
        Spec.Glob.is_nullable(wx),
        ny
      ): {l == Bool.or(Spec.Glob.matches(t, Spec.Cat{Spec.Glob.step(wx, c), y}), _): Bool}
      %Glob.walk_snoc(
        pre,
        c,
        x
      ): {
        l
          == Bool.or(
            Spec.Glob.matches(t, Spec.Cat{_, y}),
            Bool.and(Spec.Glob.is_nullable(wx), Spec.Glob.matches(t, ny))
          ): Bool
      }
      %Glob.cat_split(
        t,
        pc,
        x,
        y
      ): {l == Bool.or(_, Bool.and(Spec.Glob.is_nullable(wx), Spec.Glob.matches(t, ny))): Bool}
      %Glob.walk_null(
        pre,
        x
      ): {l == Bool.or(Glob.split(t, pc, x, y), Bool.and(_, Spec.Glob.matches(t, ny))): Bool}
      Shared.Bool.or_comm(
        Bool.and(Spec.Glob.matches(pre, x), Spec.Glob.matches(SCon{c, t}, y)),
        Glob.split(t, pc, x, y)
      )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# x and x2 agree on pre, and on pre followed by each prefix of suf
# bend-lint: expect-begin bend-lint-rules/performance/append_in_loop@warning -- only proofs use it; no program runs it
def Glob.AgreePre(x: Spec.Glob, x2: Spec.Glob, pre: String, suf: String) -> Type:
  match suf:
    case SNil{}:
      ({Spec.Glob.matches(pre, x) == Spec.Glob.matches(pre, x2): Bool} & Unit)
    case SCon{c, t}:
      (
        {
          Spec.Glob.matches(pre, x) == Spec.Glob.matches(pre, x2): Bool
        }
          & Glob.AgreePre(x, x2, String.append(pre, SCon{c, SNil{}}), t)
      )
# bend-lint: expect-end bend-lint-rules/performance/append_in_loop@warning

# y and y2 agree on each suffix of suf
def Glob.AgreeSuf(y: Spec.Glob, y2: Spec.Glob, suf: String) -> Type:
  match suf:
    case SNil{}:
      ({Spec.Glob.matches(SNil{}, y) == Spec.Glob.matches(SNil{}, y2): Bool} & Unit)
    case SCon{c, t}:
      (
        {
          Spec.Glob.matches(SCon{c, t}, y) == Spec.Glob.matches(SCon{c, t}, y2): Bool
        }
          & Glob.AgreeSuf(y, y2, t)
      )

# the cuts agree when the parts agree
def Glob.split_agree(
  suf: String,
  +pre: String,
  +x: Spec.Glob,
  x2: Spec.Glob,
  +y: Spec.Glob,
  y2: Spec.Glob,
  ea: Glob.AgreePre(x, x2, pre, suf),
  eb: Glob.AgreeSuf(y, y2, suf)
) -> {Glob.split(suf, pre, x, y) == Glob.split(suf, pre, x2, y2): Bool}:
  match suf:
    case SNil{}:
      (e1, u1) = ea
      (e2, u2) = eb
      l = Glob.split(SNil{}, pre, x, y)
      %e1: {l == Bool.or(Bool.and(_, Spec.Glob.matches(SNil{}, y2)), False{}): Bool}
      %e2: {l == Bool.or(Bool.and(Spec.Glob.matches(pre, x), _), False{}): Bool}
      {==}
    case SCon{+c, +t}:
      (e1, ra) = ea
      (e2, rb) = eb
      pc = String.append(pre, SCon{c, SNil{}})
      l = Glob.split(SCon{c, t}, pre, x, y)
      %e1: {
        l
          == Bool.or(
            Bool.and(_, Spec.Glob.matches(SCon{c, t}, y2)),
            Glob.split(t, pc, x2, y2)
          ): Bool
      }
      %e2: {l == Bool.or(Bool.and(Spec.Glob.matches(pre, x), _), Glob.split(t, pc, x2, y2)): Bool}
      %Glob.split_agree(
        t,
        pc,
        x,
        x2,
        y,
        y2,
        ra,
        rb
      ): {
        l == Bool.or(Bool.and(Spec.Glob.matches(pre, x), Spec.Glob.matches(SCon{c, t}, y)), _): Bool
      }
      {==}

# Cat of agreeing parts matches p the same way
def Glob.cat_agree(
  p: String,
  +x: Spec.Glob,
  +x2: Spec.Glob,
  +y: Spec.Glob,
  +y2: Spec.Glob,
  ea: Glob.AgreePre(x, x2, SNil{}, p),
  eb: Glob.AgreeSuf(y, y2, p)
) -> {Spec.Glob.matches(p, Spec.Cat{x, y}) == Spec.Glob.matches(p, Spec.Cat{x2, y2}): Bool}:
  +p = p
  %Glob.cat_split(p, SNil{}, x, y): {_ == Spec.Glob.matches(p, Spec.Cat{x2, y2}): Bool}
  %Glob.cat_split(p, SNil{}, x2, y2): {Glob.split(p, SNil{}, x, y) == _: Bool}
  Glob.split_agree(p, SNil{}, x, x2, y, y2, ea, eb)

# the Bool shape of one step of Chars.contains_rev
def Bool.contains_rev_step(
  e: Bool,
  t: Bool,
  a: Bool
) -> {Bool.or(Bool.or(e, t), a) == Bool.or(t, Bool.or(e, a)): Bool}:
  match e t a:
    case False{} False{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} True{} True{}:
      {==}

# Alt with Void matches what its left side matches
def Glob.alt_void(
  +p: String,
  +x: Spec.Glob
) -> {Spec.Glob.matches(p, x) == Spec.Glob.matches(p, Spec.Alt{x, Spec.Void{}}): Bool}:
  %Glob.alt_or(p, x, Spec.Void{}): {Spec.Glob.matches(p, x) == _: Bool}
  %Glob.void_never(p): {Spec.Glob.matches(p, x) == Bool.or(Spec.Glob.matches(p, x), _): Bool}
  Shared.Bool.or_false(Spec.Glob.matches(p, x))

# an empty class matches nothing, as Void
# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- a false positive, as the rule notes: the other use is an erased argument (of Equal.sym or a motive)
def Show.void_point(
  p: String
) -> {Spec.Glob.matches(p, Spec.Class{False{}, []}) == Spec.Glob.matches(p, Spec.Void{}): Bool}:
  match p:
    case SNil{}:
      {==}
    case SCon{c, t}:
      i = Spec.is_inner(c)
      %Equal.sym(
        Bool,
        Bool.and(i, False{}),
        False{},
        Shared.Bool.and_false_right(i)
      ): {Spec.Glob.matches(t, Spec.Glob.of_bool(_)) == Spec.Glob.matches(t, Spec.Void{}): Bool}
      {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

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

# a list holds c when its head is c or its tail holds c, given b, the first
def Chars.contains_con.at(
  h: Char,
  t: List<&2, Char>,
  c: Char,
  b: Bool
) -> {
  b == Char.is_eq(h, c): Bool
} -> {
  Bool.or(
    Char.is_eq(h, c),
    List.contains(~Char, ~Char.is_eq, t, c)
  )
    == List.contains(~Char, ~Char.is_eq, Con{h, t}, c): Bool
}:
  match b:
    case False{}:
      e =>
        %e: {
          Bool.or(
            _,
            List.contains(~Char, ~Char.is_eq, t, c)
          )
            == List.any.if(u => List.contains(~Char, ~Char.is_eq, t, c), _): Bool
        }
        {==}
    case True{}:
      e =>
        %e: {
          Bool.or(
            _,
            List.contains(~Char, ~Char.is_eq, t, c)
          )
            == List.any.if(u => List.contains(~Char, ~Char.is_eq, t, c), _): Bool
        }
        {==}

# a list holds c when its head is c or its tail holds c
def Chars.contains_con(
  +h: Char,
  t: List<&2, Char>,
  +c: Char
) -> {
  Bool.or(
    Char.is_eq(h, c),
    List.contains(~Char, ~Char.is_eq, t, c)
  )
    == List.contains(~Char, ~Char.is_eq, Con{h, t}, c): Bool
}:
  Chars.contains_con.at(h, t, c, Char.is_eq(h, c))({==})

# reversing xs onto acc holds c when xs or acc holds c
def Chars.contains_rev(
  xs: List<&2, Char>,
  +acc: List<&2, Char>,
  +c: Char
) -> {
  Bool.or(
    List.contains(~Char, ~Char.is_eq, xs, c),
    List.contains(~Char, ~Char.is_eq, acc, c)
  )
    == List.contains(~Char, ~Char.is_eq, List.reverse.go(&2, Char, xs, acc), c): Bool
}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      e = Char.is_eq(h, c)
      ct = List.contains(~Char, ~Char.is_eq, t, c)
      +ca = List.contains(~Char, ~Char.is_eq, acc, c)
      l = Bool.or(List.contains(~Char, ~Char.is_eq, Con{h, t}, c), ca)
      %Chars.contains_rev(t, Con{h, acc}, c): {l == _: Bool}
      %Chars.contains_con(h, acc, c): {l == Bool.or(ct, _): Bool}
      %Chars.contains_con(h, t, c): {Bool.or(_, ca) == Bool.or(ct, Bool.or(e, ca)): Bool}
      Bool.contains_rev_step(e, ct, ca)

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
      +k = List.contains(~Char, ~Char.is_eq, cs, c)
      r = Spec.Glob.matches(t, Spec.Glob.of_bool(Bool.and(i, Bool.xor(n, k))))
      %Chars.contains_rev(
        cs,
        [],
        c
      ): {Spec.Glob.matches(t, Spec.Glob.of_bool(Bool.and(i, Bool.xor(n, _)))) == r: Bool}
      %Shared.Bool.or_false(
        k
      ): {Spec.Glob.matches(t, Spec.Glob.of_bool(Bool.and(i, Bool.xor(n, _)))) == r: Bool}
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
  +de = {Spec.Cat{Spec.Deep{}, Spec.Eps{}}: Spec.Glob}
  x = Spec.Glob.step(de, Chr{47})
  %Glob.alt_or(t, Spec.Cat{Spec.Eps{}, de}, Spec.Cat{Spec.Void{}, x}): {True{} == _: Bool}
  %Glob.cat_eps_l(
    t,
    de
  ): {True{} == Bool.or(_, Spec.Glob.matches(t, Spec.Cat{Spec.Void{}, x})): Bool}
  %Glob.cat_eps_r(
    t,
    Spec.Deep{}
  ): {True{} == Bool.or(_, Spec.Glob.matches(t, Spec.Cat{Spec.Void{}, x})): Bool}
  %Glob.deep_true(t): {True{} == Bool.or(_, Spec.Glob.matches(t, Spec.Cat{Spec.Void{}, x})): Bool}
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
        +ke = {
          Spec.Cat{
            Spec.Alt{
              Spec.Eps{},
              Spec.Alt{Spec.Cat{Spec.Lit{Chr{47}}, Spec.Cat{Spec.Deep{}, Spec.Eps{}}}, Spec.Void{}}
            },
            Spec.Eps{}
          }: Spec.Glob
        }
        +sk = {
          Spec.Cat{
            Spec.Star{},
            Spec.Cat{
              Spec.Alt{
                Spec.Eps{},
                Spec.Alt{
                  Spec.Cat{Spec.Lit{Chr{47}}, Spec.Cat{Spec.Deep{}, Spec.Eps{}}},
                  Spec.Void{}
                }
              },
              Spec.Eps{}
            }
          }: Spec.Glob
        }
        %e: {
          True{}
            == Spec.Glob.matches(
              t,
              Spec.Alt{
                Spec.Cat{Spec.Cat{Spec.Glob.of_bool(Bool.not(_)), Spec.Star{}}, ke},
                Spec.Cat{Spec.Eps{}, Spec.Glob.step(ke, c)}
              }
            ): Bool
        }
        %Glob.alt_or(
          t,
          Spec.Cat{Spec.Cat{Spec.Eps{}, Spec.Star{}}, ke},
          Spec.Cat{Spec.Eps{}, Spec.Glob.step(ke, c)}
        ):
          {True{} == _: Bool}
        %Glob.cat_assoc(t, Spec.Eps{}, Spec.Star{}, ke):
          {
            True{}
              == Bool.or(_, Spec.Glob.matches(t, Spec.Cat{Spec.Eps{}, Spec.Glob.step(ke, c)})): Bool
          }
        %Glob.cat_eps_l(
          t,
          sk
        ): {
          True{}
            == Bool.or(_, Spec.Glob.matches(t, Spec.Cat{Spec.Eps{}, Spec.Glob.step(ke, c)})): Bool
        }
        %ih: {
          True{}
            == Bool.or(_, Spec.Glob.matches(t, Spec.Cat{Spec.Eps{}, Spec.Glob.step(ke, c)})): Bool
        }
        {==}
    case True{}:
      e =>
        +ke = {
          Spec.Cat{
            Spec.Alt{
              Spec.Eps{},
              Spec.Alt{Spec.Cat{Spec.Lit{Chr{47}}, Spec.Cat{Spec.Deep{}, Spec.Eps{}}}, Spec.Void{}}
            },
            Spec.Eps{}
          }: Spec.Glob
        }
        +sk = {
          Spec.Cat{
            Spec.Star{},
            Spec.Cat{
              Spec.Alt{
                Spec.Eps{},
                Spec.Alt{
                  Spec.Cat{Spec.Lit{Chr{47}}, Spec.Cat{Spec.Deep{}, Spec.Eps{}}},
                  Spec.Void{}
                }
              },
              Spec.Eps{}
            }
          }: Spec.Glob
        }
        +ec = Shared.Char.is_eq_sound(
          c,
          Chr{47}
        )(Equal.sym(Bool, True{}, Char.is_eq(c, Chr{47}), e))
        %Equal.sym(Char, c, Chr{47}, ec): {True{} == Spec.Glob.matches(SCon{_, t}, sk): Bool}
        +st = {Spec.Cat{Spec.Cat{Spec.Void{}, Spec.Star{}}, ke}: Spec.Glob}
        +x = Spec.Glob.step(ke, Chr{47})
        +p = {SCon{Chr{47}, t}: String}
        %Glob.alt_or(t, st, Spec.Cat{Spec.Eps{}, x}): {True{} == _: Bool}
        %Glob.cat_eps_l(t, x): {True{} == Bool.or(Spec.Glob.matches(t, st), _): Bool}
        %Glob.cat_eps_r(
          p,
          Spec.Alt{
            Spec.Eps{},
            Spec.Alt{Spec.Cat{Spec.Lit{Chr{47}}, Spec.Cat{Spec.Deep{}, Spec.Eps{}}}, Spec.Void{}}
          }
        ): {True{} == Bool.or(Spec.Glob.matches(t, st), _): Bool}
        %Glob.alt_or(
          p,
          Spec.Eps{},
          Spec.Alt{Spec.Cat{Spec.Lit{Chr{47}}, Spec.Cat{Spec.Deep{}, Spec.Eps{}}}, Spec.Void{}}
        ): {True{} == Bool.or(Spec.Glob.matches(t, st), _): Bool}
        %Glob.alt_void(
          p,
          Spec.Cat{Spec.Lit{Chr{47}}, Spec.Cat{Spec.Deep{}, Spec.Eps{}}}
        ): {
          True{}
            == Bool.or(Spec.Glob.matches(t, st), Bool.or(Spec.Glob.matches(p, Spec.Eps{}), _)): Bool
        }
        %Show.slash_deep(
          t
        ): {
          True{}
            == Bool.or(Spec.Glob.matches(t, st), Bool.or(Spec.Glob.matches(p, Spec.Eps{}), _)): Bool
        }
        %Equal.sym(
          Bool,
          Bool.or(Spec.Glob.matches(p, Spec.Eps{}), True{}),
          True{},
          Shared.Bool.or_true_right(Spec.Glob.matches(p, Spec.Eps{}))
        ): {True{} == Bool.or(Spec.Glob.matches(t, st), _): Bool}
        Equal.sym(
          Bool,
          Bool.or(Spec.Glob.matches(t, st), True{}),
          True{},
          Shared.Bool.or_true_right(Spec.Glob.matches(t, st))
        )
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
          Glob.AgreePre(Show.glob(g), g, pre, suf)
        case 1n+j:
          match j:
            case 0n:
              Glob.AgreeSuf(Show.glob(g), g, suf)
            case 1n+i:
              Unit

# Show.glob(g) matches what g matches. One def gives all three ranks, so the
# Cat case can ask for its parts' agreement chains as often as it needs.
# bend-lint: expect-begin bend-lint-rules/performance/append_in_loop@warning -- only proofs use it; no program runs it
# bend-lint: expect-begin bend-lint-rules/performance/missed_fork@hint -- only proofs use it; no program runs it
def Show.ok(+g: Spec.Glob, +rank: Nat, +suf: String, +pre: String) -> Show.Ok(g, rank, suf, pre):
  match g:
    case Spec.Void{}:
      match rank:
        case 0n:
          Show.void_point(suf)
        case 1n+k:
          match k:
            case 0n:
              match suf:
                case SNil{}:
                  (Show.ok(g, 0n, pre, SNil{}), Unit{})
                case SCon{c2, t}:
                  (
                    Show.ok(g, 0n, pre, SNil{}),
                    Show.ok(g, 1n, t, String.append(pre, SCon{c2, SNil{}}))
                  )
            case 1n+j:
              match j:
                case 0n:
                  match suf:
                    case SNil{}:
                      (Show.ok(g, 0n, SNil{}, pre), Unit{})
                    case SCon{c2, +t}:
                      (Show.ok(g, 0n, SCon{c2, t}, pre), Show.ok(g, 2n, t, pre))
                case 1n+i:
                  Unit{}
    case Spec.Eps{}:
      match rank:
        case 0n:
          Show.eps_point(suf)
        case 1n+k:
          match k:
            case 0n:
              match suf:
                case SNil{}:
                  (Show.ok(g, 0n, pre, SNil{}), Unit{})
                case SCon{c2, t}:
                  (
                    Show.ok(g, 0n, pre, SNil{}),
                    Show.ok(g, 1n, t, String.append(pre, SCon{c2, SNil{}}))
                  )
            case 1n+j:
              match j:
                case 0n:
                  match suf:
                    case SNil{}:
                      (Show.ok(g, 0n, SNil{}, pre), Unit{})
                    case SCon{c2, +t}:
                      (Show.ok(g, 0n, SCon{c2, t}, pre), Show.ok(g, 2n, t, pre))
                case 1n+i:
                  Unit{}
    case Spec.Lit{c}:
      match rank:
        case 0n:
          {==}
        case 1n+k:
          match k:
            case 0n:
              match suf:
                case SNil{}:
                  (Show.ok(g, 0n, pre, SNil{}), Unit{})
                case SCon{c2, t}:
                  (
                    Show.ok(g, 0n, pre, SNil{}),
                    Show.ok(g, 1n, t, String.append(pre, SCon{c2, SNil{}}))
                  )
            case 1n+j:
              match j:
                case 0n:
                  match suf:
                    case SNil{}:
                      (Show.ok(g, 0n, SNil{}, pre), Unit{})
                    case SCon{c2, +t}:
                      (Show.ok(g, 0n, SCon{c2, t}, pre), Show.ok(g, 2n, t, pre))
                case 1n+i:
                  Unit{}
    case Spec.Any{}:
      match rank:
        case 0n:
          {==}
        case 1n+k:
          match k:
            case 0n:
              match suf:
                case SNil{}:
                  (Show.ok(g, 0n, pre, SNil{}), Unit{})
                case SCon{c2, t}:
                  (
                    Show.ok(g, 0n, pre, SNil{}),
                    Show.ok(g, 1n, t, String.append(pre, SCon{c2, SNil{}}))
                  )
            case 1n+j:
              match j:
                case 0n:
                  match suf:
                    case SNil{}:
                      (Show.ok(g, 0n, SNil{}, pre), Unit{})
                    case SCon{c2, +t}:
                      (Show.ok(g, 0n, SCon{c2, t}, pre), Show.ok(g, 2n, t, pre))
                case 1n+i:
                  Unit{}
    case Spec.Star{}:
      match rank:
        case 0n:
          Show.star_point(suf)
        case 1n+k:
          match k:
            case 0n:
              match suf:
                case SNil{}:
                  (Show.ok(g, 0n, pre, SNil{}), Unit{})
                case SCon{c2, t}:
                  (
                    Show.ok(g, 0n, pre, SNil{}),
                    Show.ok(g, 1n, t, String.append(pre, SCon{c2, SNil{}}))
                  )
            case 1n+j:
              match j:
                case 0n:
                  match suf:
                    case SNil{}:
                      (Show.ok(g, 0n, SNil{}, pre), Unit{})
                    case SCon{c2, +t}:
                      (Show.ok(g, 0n, SCon{c2, t}, pre), Show.ok(g, 2n, t, pre))
                case 1n+i:
                  Unit{}
    case Spec.Class{+n, +cs}:
      match rank:
        case 0n:
          Show.class_point(suf, n, cs)
        case 1n+k:
          match k:
            case 0n:
              match suf:
                case SNil{}:
                  (Show.ok(g, 0n, pre, SNil{}), Unit{})
                case SCon{c2, t}:
                  (
                    Show.ok(g, 0n, pre, SNil{}),
                    Show.ok(g, 1n, t, String.append(pre, SCon{c2, SNil{}}))
                  )
            case 1n+j:
              match j:
                case 0n:
                  match suf:
                    case SNil{}:
                      (Show.ok(g, 0n, SNil{}, pre), Unit{})
                    case SCon{c2, +t}:
                      (Show.ok(g, 0n, SCon{c2, t}, pre), Show.ok(g, 2n, t, pre))
                case 1n+i:
                  Unit{}
    case Spec.Deep{}:
      match rank:
        case 0n:
          Show.deep_point(suf)
        case 1n+k:
          match k:
            case 0n:
              match suf:
                case SNil{}:
                  (Show.ok(g, 0n, pre, SNil{}), Unit{})
                case SCon{c2, t}:
                  (
                    Show.ok(g, 0n, pre, SNil{}),
                    Show.ok(g, 1n, t, String.append(pre, SCon{c2, SNil{}}))
                  )
            case 1n+j:
              match j:
                case 0n:
                  match suf:
                    case SNil{}:
                      (Show.ok(g, 0n, SNil{}, pre), Unit{})
                    case SCon{c2, +t}:
                      (Show.ok(g, 0n, SCon{c2, t}, pre), Show.ok(g, 2n, t, pre))
                case 1n+i:
                  Unit{}
    case Spec.Cat{+a, +b}:
      match rank:
        case 0n:
          +ta = Show.glob(a)
          +tb = Show.glob(b)
          r = Spec.Glob.matches(suf, Spec.Cat{a, b})
          %Glob.alt_void(suf, Spec.Cat{ta, Spec.Cat{tb, Spec.Eps{}}}): {_ == r: Bool}
          %Equal.sym(
            Bool,
            Spec.Glob.matches(suf, Spec.Cat{ta, Spec.Cat{tb, Spec.Eps{}}}),
            Spec.Glob.matches(suf, Spec.Cat{Spec.Cat{ta, tb}, Spec.Eps{}}),
            Glob.cat_assoc(suf, ta, tb, Spec.Eps{})
          ): {_ == r: Bool}
          %Glob.cat_eps_r(suf, Spec.Cat{ta, tb}): {_ == r: Bool}
          Glob.cat_agree(
            suf,
            ta,
            a,
            tb,
            b,
            Show.ok(a, 1n, suf, SNil{}),
            Show.ok(b, 2n, suf, SNil{})
          )
        case 1n+k:
          match k:
            case 0n:
              match suf:
                case SNil{}:
                  (Show.ok(g, 0n, pre, SNil{}), Unit{})
                case SCon{c2, t}:
                  (
                    Show.ok(g, 0n, pre, SNil{}),
                    Show.ok(g, 1n, t, String.append(pre, SCon{c2, SNil{}}))
                  )
            case 1n+j:
              match j:
                case 0n:
                  match suf:
                    case SNil{}:
                      (Show.ok(g, 0n, SNil{}, pre), Unit{})
                    case SCon{c2, +t}:
                      (Show.ok(g, 0n, SCon{c2, t}, pre), Show.ok(g, 2n, t, pre))
                case 1n+i:
                  Unit{}
    case Spec.Alt{+a, +b}:
      match rank:
        case 0n:
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
          %Show.ok(
            a,
            0n,
            suf,
            SNil{}
          ): {Bool.or(ma, mb) == Bool.or(_, Spec.Glob.matches(suf, b)): Bool}
          %Show.ok(b, 0n, suf, SNil{}): {Bool.or(ma, mb) == Bool.or(ma, _): Bool}
          {==}
        case 1n+k:
          match k:
            case 0n:
              match suf:
                case SNil{}:
                  (Show.ok(g, 0n, pre, SNil{}), Unit{})
                case SCon{c2, t}:
                  (
                    Show.ok(g, 0n, pre, SNil{}),
                    Show.ok(g, 1n, t, String.append(pre, SCon{c2, SNil{}}))
                  )
            case 1n+j:
              match j:
                case 0n:
                  match suf:
                    case SNil{}:
                      (Show.ok(g, 0n, SNil{}, pre), Unit{})
                    case SCon{c2, +t}:
                      (Show.ok(g, 0n, SCon{c2, t}, pre), Show.ok(g, 2n, t, pre))
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

# Lits.cons, given o1 and o2, the comparisons of the two characters
# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- a false positive, as the rule notes: the other use is an erased argument (of Equal.sym or a motive)
def Lits.cmp_case(
  cx: U32,
  dx: U32,
  o1: Cmp,
  o2: Cmp,
  qt: String,
  pt: String
) -> {
  o1 == U32.cmp(cx, dx): Cmp
} -> {
  o2 == U32.cmp(dx, cx): Cmp
} -> {
  Cmp.is_eq(
    String.order.go(qt, pt, U32.cmp(dx, cx))
  )
    == Bool.and(Cmp.is_eq(U32.cmp(cx, dx)), String.eq(qt, pt)): Bool
}:
  match o1 o2:
    case LT{} LT{}:
      e1 => e2 =>
        %e1: {
          Cmp.is_eq(
            String.order.go(qt, pt, U32.cmp(dx, cx))
          )
            == Bool.and(Cmp.is_eq(_), String.eq(qt, pt)): Bool
        }
        %e2: {
          Cmp.is_eq(
            String.order.go(qt, pt, _)
          )
            == Bool.and(Cmp.is_eq(LT{}), String.eq(qt, pt)): Bool
        }
        Texts.String.order_ne_lt(qt, pt)
    case LT{} EQ{}:
      e1 => e2 =>
        z = Shared.Cmp.ne_eq(
          LT{},
          Unit{},
          Equal.trans(
            Cmp,
            LT{},
            U32.cmp(cx, dx),
            EQ{},
            e1,
            Equal.sym(Cmp, EQ{}, U32.cmp(cx, dx), Shared.U32.cmp_swap_eq(dx, cx, e2))
          )
        )
        Empty.absurd(
          {
            Cmp.is_eq(
              String.order.go(qt, pt, U32.cmp(dx, cx))
            )
              == Bool.and(Cmp.is_eq(U32.cmp(cx, dx)), String.eq(qt, pt)): Bool
          },
          z
        )
    case LT{} GT{}:
      e1 => e2 =>
        %e1: {
          Cmp.is_eq(
            String.order.go(qt, pt, U32.cmp(dx, cx))
          )
            == Bool.and(Cmp.is_eq(_), String.eq(qt, pt)): Bool
        }
        %e2: {
          Cmp.is_eq(
            String.order.go(qt, pt, _)
          )
            == Bool.and(Cmp.is_eq(LT{}), String.eq(qt, pt)): Bool
        }
        Texts.String.order_ne_gt(qt, pt)
    case EQ{} LT{}:
      e1 => e2 =>
        z = Shared.Cmp.ne_eq(
          LT{},
          Unit{},
          Equal.trans(
            Cmp,
            LT{},
            U32.cmp(dx, cx),
            EQ{},
            e2,
            Equal.sym(Cmp, EQ{}, U32.cmp(dx, cx), Shared.U32.cmp_swap_eq(cx, dx, e1))
          )
        )
        Empty.absurd(
          {
            Cmp.is_eq(
              String.order.go(qt, pt, U32.cmp(dx, cx))
            )
              == Bool.and(Cmp.is_eq(U32.cmp(cx, dx)), String.eq(qt, pt)): Bool
          },
          z
        )
    case EQ{} EQ{}:
      e1 => e2 =>
        %e1: {
          Cmp.is_eq(
            String.order.go(qt, pt, U32.cmp(dx, cx))
          )
            == Bool.and(Cmp.is_eq(_), String.eq(qt, pt)): Bool
        }
        %e2: {
          Cmp.is_eq(
            String.order.go(qt, pt, _)
          )
            == Bool.and(Cmp.is_eq(EQ{}), String.eq(qt, pt)): Bool
        }
        {==}
    case EQ{} GT{}:
      e1 => e2 =>
        z = Shared.Cmp.ne_eq(
          GT{},
          Unit{},
          Equal.trans(
            Cmp,
            GT{},
            U32.cmp(dx, cx),
            EQ{},
            e2,
            Equal.sym(Cmp, EQ{}, U32.cmp(dx, cx), Shared.U32.cmp_swap_eq(cx, dx, e1))
          )
        )
        Empty.absurd(
          {
            Cmp.is_eq(
              String.order.go(qt, pt, U32.cmp(dx, cx))
            )
              == Bool.and(Cmp.is_eq(U32.cmp(cx, dx)), String.eq(qt, pt)): Bool
          },
          z
        )
    case GT{} LT{}:
      e1 => e2 =>
        %e1: {
          Cmp.is_eq(
            String.order.go(qt, pt, U32.cmp(dx, cx))
          )
            == Bool.and(Cmp.is_eq(_), String.eq(qt, pt)): Bool
        }
        %e2: {
          Cmp.is_eq(
            String.order.go(qt, pt, _)
          )
            == Bool.and(Cmp.is_eq(GT{}), String.eq(qt, pt)): Bool
        }
        Texts.String.order_ne_lt(qt, pt)
    case GT{} EQ{}:
      e1 => e2 =>
        z = Shared.Cmp.ne_eq(
          GT{},
          Unit{},
          Equal.trans(
            Cmp,
            GT{},
            U32.cmp(cx, dx),
            EQ{},
            e1,
            Equal.sym(Cmp, EQ{}, U32.cmp(cx, dx), Shared.U32.cmp_swap_eq(dx, cx, e2))
          )
        )
        Empty.absurd(
          {
            Cmp.is_eq(
              String.order.go(qt, pt, U32.cmp(dx, cx))
            )
              == Bool.and(Cmp.is_eq(U32.cmp(cx, dx)), String.eq(qt, pt)): Bool
          },
          z
        )
    case GT{} GT{}:
      e1 => e2 =>
        %e1: {
          Cmp.is_eq(
            String.order.go(qt, pt, U32.cmp(dx, cx))
          )
            == Bool.and(Cmp.is_eq(_), String.eq(qt, pt)): Bool
        }
        %e2: {
          Cmp.is_eq(
            String.order.go(qt, pt, _)
          )
            == Bool.and(Cmp.is_eq(GT{}), String.eq(qt, pt)): Bool
        }
        Texts.String.order_ne_gt(qt, pt)
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

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
  +l = Glob.lits(pt)
  +e1 = Cmp.is_eq(U32.cmp(cx, dx))
  +x = Spec.Glob.step(l, Chr{dx})
  s = String.eq(SCon{Chr{dx}, qt}, SCon{Chr{cx}, pt})
  %Glob.alt_or(qt, Spec.Cat{Spec.Glob.of_bool(e1), l}, Spec.Cat{Spec.Void{}, x}): {s == _: Bool}
  %Glob.cat_of_bool(
    qt,
    e1,
    l
  ): {s == Bool.or(_, Spec.Glob.matches(qt, Spec.Cat{Spec.Void{}, x})): Bool}
  %Glob.cat_void_l(qt, x): {s == Bool.or(Bool.and(e1, Spec.Glob.matches(qt, l)), _): Bool}
  %Shared.Bool.or_false(Bool.and(e1, Spec.Glob.matches(qt, l))): {s == _: Bool}
  %ih: {s == Bool.and(e1, _): Bool}
  Lits.cmp_case(cx, dx, U32.cmp(cx, dx), U32.cmp(dx, cx), qt, pt)({==}, {==})
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the Lits of p match exactly p
def Lits.match(
  q: String,
  p: String
) -> {String.eq(q, p) == Spec.Glob.matches(q, Glob.lits(p)): Bool}:
  match q p:
    case SNil{} SNil{}:
      {==}
    case SCon{d, +qt} SNil{}:
      Glob.void_never(qt)
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

# Fast selection
# --------------
