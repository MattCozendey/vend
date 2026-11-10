import Base
import ./shared/shared.bend as Shared

# Spans
# -----
# A set of characters as a list of spans. A check of one character compares
# codes: it costs the number of spans, not the number of characters in them.
# A few characters, the marks, stand for all the others: a character is in the
# same spans as the nearest mark that is not above it.

# A span is the characters from lo to hi, both included; it is empty when hi
# is before lo.
type Span is Data:
  Span{lo: Char, hi: Char}

# the code of c: its place in the order of characters
def Char.code(c: Char) -> Nat:
  match c:
    case Chr{x}:
      U32.to_nat(x)

# c is the last character: no code is above its code
def Char.is_last(c: Char) -> Bool:
  match c:
    case Chr{x}:
      U32.is_eq(x, 4294967295)

# the character after c; after the last character, the character of code 0
def Char.after(c: Char) -> Char:
  match c:
    case Chr{x}:
      Chr{U32.inc(x)}

# c is in s: the code of c is not below the code of lo and not above the code
# of hi
def Span.has(s: Span, c: Char) -> Bool:
  match s c:
    case Span{Chr{lo}, Chr{hi}} Chr{+x}:
      List.all.if(u => U32.is_le(x, hi), U32.is_le(lo, x))

# the span from lo to hi, or None when hi is before lo
def Span.of(+lo: Char, +hi: Char) -> Maybe<&2, Span>:
  Shared.Maybe.when(Span, Nat.is_le(Char.code(lo), Char.code(hi)), u => Some{Span{lo, hi}})

# some span of ss holds c
def Spans.has(ss: List<&2, Span>, c: Char) -> Bool:
  Shared.List.some(~Span, ~Char, ~(c => s => Span.has(s, c)), ss, c)

# a and b are the same span
def Span.is_eq(a: Span, b: Span) -> Bool:
  match a b:
    case Span{al, ah} Span{bl, bh}:
      List.all.if(u => Char.is_eq(ah, bh), Char.is_eq(al, bl))

# each span of ss holds both c and d, or neither
def Spans.alike(ss: List<&2, Span>, +c: Char, +d: Char) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case Con{+s, r}:
      List.all.if(u => Spans.alike(r, c, d), Shared.Bool.is_eq(Span.has(s, c), Span.has(s, d)))

# the marks of s, before rest: lo and the character after hi. After the last
# character that is the character of code 0, which is a mark of every list.
def Span.marks(s: Span, rest: List<&2, Char>) -> List<&2, Char>:
  match s:
    case Span{lo, hi}:
      lo <> Char.after(hi) <> rest

# the marks of each span of ss
def Spans.marks.go(ss: List<&2, Span>) -> List<&2, Char>:
  match ss:
    case Nil{}:
      []
    case Con{s, r}:
      Span.marks(s, Spans.marks.go(r))

# The marks of ss: characters that together stand for every character under
# ss. The character of code 0, the lo of each span, and the character after the
# hi of each span. A mark can come more than once.
def Spans.marks(ss: List<&2, Span>) -> List<&2, Char>:
  Chr{0} <> Spans.marks.go(ss)

# ms holds a character of code n; one scan of ms
def Spans.marked(ms: List<&2, Char>, n: Nat) -> Bool:
  Shared.List.some(~Char, ~Nat, ~(n => m => Nat.is_eq(Char.code(m), n)), ms, n)

# ms holds a mark for each end of s: a character of the code of lo and, when
# hi is not the last character, one of the code after the code of hi; two
# scans of ms
def Span.covered(+ms: List<&2, Char>, s: Span) -> Bool:
  match s:
    case Span{lo, +hi}:
      List.all.if(
        u => List.any.if(u => Spans.marked(ms, 1n+Char.code(hi)), Char.is_last(hi)),
        Spans.marked(ms, Char.code(lo))
      )

# ms holds a mark for each end of each span of ss
def Spans.covered.go(ss: List<&2, Span>, +ms: List<&2, Char>) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case Con{s, r}:
      List.all.if(u => Spans.covered.go(r, ms), Span.covered(ms, s))

# ms can stand for every character under ss: it holds the character of code 0
# and a mark for each end of each span of ss; two scans of ms for each span
def Spans.covered(ss: List<&2, Span>, +ms: List<&2, Char>) -> Bool:
  List.all.if(u => Spans.covered.go(ss, ms), List.contains(~Char, ~Char.is_eq, ms, Chr{0}))

# m, when its code is not above the code of c and not below the code of best;
# else best
def Spans.rep.pick(+m: Char, +best: Char, c: Char) -> Char:
  Bool.pick(
    Char,
    Bool.and(Nat.is_le(Char.code(m), Char.code(c)), Nat.is_le(Char.code(best), Char.code(m))),
    m,
    best
  )

# the mark that stands for c: the mark of ms with the largest code that is not
# above the code of c, or the character of code 0 when there is none. Only
# proofs use it.
def Spans.rep(ms: List<&2, Char>, +c: Char) -> Char:
  match ms:
    case Nil{}:
      Chr{0}
    case Con{m, r}:
      Spans.rep.pick(m, Spans.rep(r, c), c)

# Equality of spans
# -----------------
# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof does not run
# bend-lint: expect-begin bend-lint-rules/performance/loop_invariant_call@information -- a proof does not run
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run

# Span.is_eq is True for a span and itself
def Span.is_eq_refl(a: Span) -> {Span.is_eq(a, a) == True{}: Bool}:
  match a:
    case Span{+lo, +hi}:
      Shared.List.all.if_both(
        Char.is_eq(lo, lo),
        u => Char.is_eq(hi, hi)
      )(Shared.Char.is_eq_refl(lo))(Shared.Char.is_eq_refl(hi))

# Span.is_eq is True only for equal spans
def Span.is_eq_sound(a: Span, b: Span) -> {Span.is_eq(a, b) == True{}: Bool} -> {a == b: Span}:
  match a b:
    case Span{+al, +ah} Span{+bl, +bh}:
      +e =>
        %Shared.Char.is_eq_sound(
          al,
          bl
        )(
          Shared.List.all.if_hit(Char.is_eq(al, bl), u => Char.is_eq(ah, bh))(e)
        ): {Span{al, ah} == Span{_, bh}: Span}
        %Shared.Char.is_eq_sound(
          ah,
          bh
        )(
          Shared.List.all.if_rest(Char.is_eq(al, bl), u => Char.is_eq(ah, bh))(e)
        ): {Span{al, ah} == Span{al, _}: Span}
        {==}

# the laws of Span.is_eq
def Span.laws() -> Shared.Eq.Laws(Span, Span.is_eq):
  (Span.is_eq_refl, Span.is_eq_sound)

# Spans by codes
# --------------
# The proofs below reason on codes, with the order lemmas of Nat.

# a span holds c when the code of c is between the codes of its ends
def Span.has_codes(
  lo: Char,
  hi: Char,
  c: Char
) -> {
  Span.has(
    Span{lo, hi},
    c
  )
    == Bool.and(
      Nat.is_le(Char.code(lo), Char.code(c)),
      Nat.is_le(Char.code(c), Char.code(hi))
    ): Bool
}:
  match lo:
    case Chr{+code}:
      match hi:
        case Chr{+code1}:
          match c:
            case Chr{+code2}:
              %Equal.sym(
                Bool,
                U32.is_le(code, code2),
                Nat.is_le(U32.to_nat(code), U32.to_nat(code2)),
                Shared.U32.is_le_to_nat(code, code2)
              ):
                {
                  List.all.if(
                    u => U32.is_le(code2, code1),
                    _
                  )
                    == Bool.and(
                      Cmp.is_le(Nat.cmp(U32.to_nat(code), U32.to_nat(code2))),
                      Cmp.is_le(Nat.cmp(U32.to_nat(code2), U32.to_nat(code1)))
                    ): Bool
                }
              %Shared.U32.cmp_to_nat(code2, code1):
                {
                  List.all.if(
                    u => U32.is_le(code2, code1),
                    Cmp.is_le(Nat.cmp(U32.to_nat(code), U32.to_nat(code2)))
                  )
                    == Bool.and(
                      Cmp.is_le(Nat.cmp(U32.to_nat(code), U32.to_nat(code2))),
                      Cmp.is_le(_)
                    ): Bool
                }
              %Equal.sym(
                Bool,
                List.all.if(
                  u => U32.is_le(code2, code1),
                  Nat.is_le(U32.to_nat(code), U32.to_nat(code2))
                ),
                Bool.and(Nat.is_le(U32.to_nat(code), U32.to_nat(code2)), U32.is_le(code2, code1)),
                Shared.List.all.if_and(
                  Nat.is_le(U32.to_nat(code), U32.to_nat(code2)),
                  u => U32.is_le(code2, code1)
                )
              ):
                {
                  _
                    == Bool.and(
                      Nat.is_le(U32.to_nat(code), U32.to_nat(code2)),
                      U32.is_le(code2, code1)
                    ): Bool
                }
              {==}

# two characters are the same when their codes are
def Char.is_eq_codes(
  a: Char,
  b: Char
) -> {Char.is_eq(a, b) == Nat.is_eq(Char.code(a), Char.code(b)): Bool}:
  match a:
    case Chr{code}:
      match b:
        case Chr{code1}:
          %Equal.sym(
            Cmp,
            U32.cmp(code, code1),
            Nat.cmp(U32.to_nat(code), U32.to_nat(code1)),
            Shared.U32.cmp_to_nat(code, code1)
          ):
            {Cmp.is_eq(_) == Cmp.is_eq(Nat.cmp(U32.to_nat(code), U32.to_nat(code1))): Bool}
          {==}

# a single character is a span
law Span.has_one:
  for x: Char
  for c: Char
  {Span.has(Span{x, x}, c) == Char.is_eq(x, c): Bool}

def Span.has_one(x, c):
  match x:
    case Chr{+code}:
      match c:
        case Chr{+code1}:
          %Equal.sym(
            Cmp,
            U32.cmp(code, code1),
            Nat.cmp(U32.to_nat(code), U32.to_nat(code1)),
            Shared.U32.cmp_to_nat(code, code1)
          ):
            {List.all.if(u => U32.is_le(code1, code), Cmp.is_le(_)) == Cmp.is_eq(_): Bool}
          %Equal.sym(
            Bool,
            List.all.if(
              u => U32.is_le(code1, code),
              Cmp.is_le(Nat.cmp(U32.to_nat(code), U32.to_nat(code1)))
            ),
            Bool.and(
              Cmp.is_le(Nat.cmp(U32.to_nat(code), U32.to_nat(code1))),
              U32.is_le(code1, code)
            ),
            Shared.List.all.if_and(
              Cmp.is_le(Nat.cmp(U32.to_nat(code), U32.to_nat(code1))),
              u => U32.is_le(code1, code)
            )
          ):
            {_ == Cmp.is_eq(Nat.cmp(U32.to_nat(code), U32.to_nat(code1))): Bool}
          %Equal.sym(
            Cmp,
            U32.cmp(code1, code),
            Nat.cmp(U32.to_nat(code1), U32.to_nat(code)),
            Shared.U32.cmp_to_nat(code1, code)
          ):
            {
              Bool.and(
                Cmp.is_le(Nat.cmp(U32.to_nat(code), U32.to_nat(code1))),
                Cmp.is_le(_)
              )
                == Cmp.is_eq(Nat.cmp(U32.to_nat(code), U32.to_nat(code1))): Bool
            }
          Shared.Nat.le_both(U32.to_nat(code), U32.to_nat(code1))

# no code is above the code of the last character
def Char.le_last(
  hi: Char,
  c: Char
) -> {Char.is_last(hi) == True{}: Bool} -> {Nat.is_le(Char.code(c), Char.code(hi)) == True{}: Bool}:
  match hi c:
    case Chr{+x} Chr{+y}:
      e =>
        Equal.trans(
          Bool,
          Nat.is_le(U32.to_nat(y), U32.to_nat(x)),
          U32.is_le(y, x),
          True{},
          Equal.sym(
            Bool,
            U32.is_le(y, x),
            Nat.is_le(U32.to_nat(y), U32.to_nat(x)),
            Shared.U32.is_le_to_nat(y, x)
          ),
          (
            %Equal.sym(U32, x, 4294967295, Shared.U32.is_eq_sound(x, 4294967295)(e)): {U32.is_le(y, _) == True{}: Bool}
            Shared.U32.le_last(y))
        )

# the code of the character after c is one more than the code of c, when c is
# not the last character
def Char.after_code(
  c: Char
) -> {Char.is_last(c) == False{}: Bool} -> {Char.code(Char.after(c)) == 1n+Char.code(c): Nat}:
  match c:
    case Chr{code}:
      x => (%Equal.sym(
        Nat,
        U32.to_nat(U32.inc(code)),
        1n+U32.to_nat(code),
        Shared.U32.inc_to_nat(code)(x)
      ): {_ == 1n+U32.to_nat(code): Nat}; {==})

# Alike characters
# ----------------

# Spans.alike_has at the first span t, by whether it is s (hit)
def Spans.alike_has.at(
  hit: Bool,
  +t: Span,
  r: List<&2, Span>,
  +c: Char,
  +d: Char,
  s: Span,
  et: {Span.is_eq(t, s) == hit: Bool},
  ha: {
    List.all.if(
      u => Spans.alike(r, c, d),
      Shared.Bool.is_eq(Span.has(t, c), Span.has(t, d))
    )
      == True{}: Bool
  },
  hc: {List.any.if(u => List.contains(~Span, ~Span.is_eq, r, s), hit) == True{}: Bool},
  ih: {
    Spans.alike(r, c, d) == True{}: Bool
  } -> {
    List.contains(~Span, ~Span.is_eq, r, s) == True{}: Bool
  } -> {Span.has(s, c) == Span.has(s, d): Bool}
) -> {Span.has(s, c) == Span.has(s, d): Bool}:
  match hit:
    case True{}:
      %Span.is_eq_sound(t, s)(et): {Span.has(_, c) == Span.has(_, d): Bool}
      Shared.Bool.is_eq_sound(
        Span.has(t, c),
        Span.has(t, d)
      )(
        Shared.List.all.if_hit(
          Shared.Bool.is_eq(Span.has(t, c), Span.has(t, d)),
          u => Spans.alike(r, c, d)
        )(ha)
      )
    case False{}:
      ih(
        Shared.List.all.if_rest(
          Shared.Bool.is_eq(Span.has(t, c), Span.has(t, d)),
          u => Spans.alike(r, c, d)
        )(ha)
      )(hc)

# alike characters are on the same side of each span of the list
law Spans.alike_has:
  for ss: List<&2, Span>
  for c: Char
  for d: Char
  for s: Span
  {
    Spans.alike(ss, c, d) == True{}: Bool
  } -> {
    List.contains(~Span, ~Span.is_eq, ss, s) == True{}: Bool
  } -> {Span.has(s, c) == Span.has(s, d): Bool}

def Spans.alike_has(ss, c, d, s):
  match ss:
    case Nil{}:
      ha => hc => Empty.absurd(
        {Span.has(s, c) == Span.has(s, d): Bool},
        Shared.Bool.false_ne_true(hc)
      )
    case Con{+t, +r}:
      +c = c
      +d = d
      +s = s
      ha => hc => Spans.alike_has.at(
        Span.is_eq(t, s),
        t,
        r,
        c,
        d,
        s,
        {==},
        ha,
        hc,
        Spans.alike_has(r, c, d, s)
      )

# The mark of a character
# -----------------------
# The mark for c is not above c, and no mark lies between the two. So a span
# end with a mark is on the same side of both.

# the picked mark is not above c when best is not
def Spans.rep.pick_le(
  k1: Bool,
  k2: Bool,
  -m: Char,
  -best: Char,
  -c: Char,
  e1: {Nat.is_le(Char.code(m), Char.code(c)) == k1: Bool},
  ih: {Nat.is_le(Char.code(best), Char.code(c)) == True{}: Bool}
) -> {
  Nat.is_le(Char.code(Bool.pick(Char, Bool.and(k1, k2), m, best)), Char.code(c)) == True{}: Bool
}:
  match k1:
    case False{}:
      ih
    case True{}:
      match k2:
        case False{}:
          ih
        case True{}:
          e1

# the picked mark is not below best
def Spans.rep.pick_ge(
  k1: Bool,
  k2: Bool,
  -m: Char,
  best: Char,
  e2: {Nat.is_le(Char.code(best), Char.code(m)) == k2: Bool}
) -> {
  Nat.is_le(Char.code(best), Char.code(Bool.pick(Char, Bool.and(k1, k2), m, best))) == True{}: Bool
}:
  match k1:
    case False{}:
      Shared.Nat.le_refl(Char.code(best))
    case True{}:
      match k2:
        case False{}:
          Shared.Nat.le_refl(Char.code(best))
        case True{}:
          e2

# the picked mark is not below a mark m that is not above c
def Spans.rep.pick_takes(
  k1: Bool,
  k2: Bool,
  m: Char,
  best: Char,
  e2: {Nat.is_le(Char.code(best), Char.code(m)) == k2: Bool}
) -> {
  k1 == True{}: Bool
} -> {
  Nat.is_le(Char.code(m), Char.code(Bool.pick(Char, Bool.and(k1, k2), m, best))) == True{}: Bool
}:
  match k1:
    case False{}:
      x => Empty.absurd(
        {
          Nat.is_le(
            Char.code(m),
            Char.code(Bool.pick(Char, Bool.and(False{}, k2), m, best))
          )
            == True{}: Bool
        },
        {(%x: {\{False: Unit; \{True: Empty; \{}}}: Bool -> Type}(_); Unit{}): Empty}
      )
    case True{}:
      match k2:
        case False{}:
          x => Shared.Nat.nle_le(Char.code(best), Char.code(m))(e2)
        case True{}:
          x => Shared.Nat.le_refl(Char.code(m))

# the mark for c is not above c
def Spans.rep_le(
  ms: List<&2, Char>,
  +c: Char
) -> {Nat.is_le(Char.code(Spans.rep(ms, c)), Char.code(c)) == True{}: Bool}:
  match ms:
    case Nil{}:
      Shared.Nat.le_zero(Char.code(c))
    case Con{+head, +tail}:
      Spans.rep.pick_le(
        Nat.is_le(Char.code(head), Char.code(c)),
        Nat.is_le(Char.code(Spans.rep(tail, c)), Char.code(head)),
        head,
        Spans.rep(tail, c),
        c,
        {==},
        Spans.rep_le(tail, c)
      )

# Spans.rep_max at the first mark m, by whether its code is n (hit)
def Spans.rep_max.at(
  hit: Bool,
  +m: Char,
  +r: List<&2, Char>,
  +c: Char,
  +n: Nat,
  +eh: {Nat.is_eq(Char.code(m), n) == hit: Bool},
  hm: {List.any.if(u => Spans.marked(r, n), hit) == True{}: Bool},
  hn: {Nat.is_le(n, Char.code(c)) == True{}: Bool},
  ih: {
    Spans.marked(r, n) == True{}: Bool
  } -> {
    Nat.is_le(n, Char.code(c)) == True{}: Bool
  } -> {Nat.is_le(n, Char.code(Spans.rep(r, c))) == True{}: Bool}
) -> {Nat.is_le(n, Char.code(Spans.rep.pick(m, Spans.rep(r, c), c))) == True{}: Bool}:
  match hit:
    case True{}:
      k1 = Nat.is_le(Char.code(m), Char.code(c))
      k2 = Nat.is_le(Char.code(Spans.rep(r, c)), Char.code(m))
      %Shared.Nat.is_eq_sound(
        Char.code(m),
        n
      )(eh): {Nat.is_le(_, Char.code(Spans.rep.pick(m, Spans.rep(r, c), c))) == True{}: Bool}
      Spans.rep.pick_takes(k1, k2, m, Spans.rep(r, c), {==})(
        %Equal.sym(Nat, Char.code(m), n, Shared.Nat.is_eq_sound(Char.code(m), n)(eh)): {Nat.is_le(_, Char.code(c)) == True{}: Bool}
        hn)
    case False{}:
      Shared.Nat.le_trans(
        n,
        Char.code(Spans.rep(r, c)),
        Char.code(Spans.rep.pick(m, Spans.rep(r, c), c))
      )(
        ih(hm)(hn)
      )(
        Spans.rep.pick_ge(
          Nat.is_le(Char.code(m), Char.code(c)),
          Nat.is_le(Char.code(Spans.rep(r, c)), Char.code(m)),
          m,
          Spans.rep(r, c),
          {==}
        )
      )

# the code n of a mark that is not above c is not above the mark for c
def Spans.rep_max(
  ms: List<&2, Char>,
  +c: Char,
  +n: Nat
) -> {
  Spans.marked(ms, n) == True{}: Bool
} -> {
  Nat.is_le(n, Char.code(c)) == True{}: Bool
} -> {Nat.is_le(n, Char.code(Spans.rep(ms, c))) == True{}: Bool}:
  match ms:
    case Nil{}:
      hm => hn => Empty.absurd(
        {Nat.is_le(n, Char.code(Chr{0})) == True{}: Bool},
        Shared.Bool.false_ne_true(hm)
      )
    case Con{+m, +r}:
      hm => hn => Spans.rep_max.at(
        Nat.is_eq(Char.code(m), n),
        m,
        r,
        c,
        n,
        {==},
        hm,
        hn,
        Spans.rep_max(r, c, n)
      )

# Spans.rep_hi with a mark after hi, by whether c is above hi (x False): then
# the mark after hi is not above c, so it is not above the mark for c
def Spans.rep_hi.above(
  x: Bool,
  +ms: List<&2, Char>,
  +hi: Char,
  +c: Char,
  ex: {Nat.is_le(Char.code(c), Char.code(hi)) == x: Bool},
  hm: {Spans.marked(ms, 1n+Char.code(hi)) == True{}: Bool},
  hr: {Nat.is_le(Char.code(Spans.rep(ms, c)), Char.code(hi)) == True{}: Bool}
) -> {x == True{}: Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      Empty.absurd(
        {False{} == True{}: Bool},
        Shared.Bool.true_ne_false(
          Equal.trans(
            Bool,
            True{},
            Nat.is_le(1n+Char.code(hi), Char.code(hi)),
            False{},
            Equal.sym(
              Bool,
              Nat.is_le(1n+Char.code(hi), Char.code(hi)),
              True{},
              Shared.Nat.le_trans(
                1n+Char.code(hi),
                Char.code(Spans.rep(ms, c)),
                Char.code(hi)
              )(
                Spans.rep_max(
                  ms,
                  c,
                  1n+Char.code(hi)
                )(hm)(Shared.Nat.nle_succ_le(Char.code(c), Char.code(hi))(ex))
              )(hr)
            ),
            Shared.Nat.succ_nle(Char.code(hi))
          )
        )
      )

# c is not above hi when the mark for c is not, by whether hi is the last
# character (last)
def Spans.rep_hi(
  last: Bool,
  ms: List<&2, Char>,
  +hi: Char,
  +c: Char,
  el: {Char.is_last(hi) == last: Bool},
  he: {List.any.if(u => Spans.marked(ms, 1n+Char.code(hi)), last) == True{}: Bool},
  hr: {Nat.is_le(Char.code(Spans.rep(ms, c)), Char.code(hi)) == True{}: Bool}
) -> {Nat.is_le(Char.code(c), Char.code(hi)) == True{}: Bool}:
  match last:
    case True{}:
      Char.le_last(hi, c)(el)
    case False{}:
      Spans.rep_hi.above(Nat.is_le(Char.code(c), Char.code(hi)), ms, hi, c, {==}, he, hr)

# a span holds both c and d, or neither, when each of its ends is on the same
# side of both
def Span.has_ends(
  +lo: Char,
  +hi: Char,
  c: Char,
  d: Char,
  e1: {Nat.is_le(Char.code(lo), Char.code(c)) == Nat.is_le(Char.code(lo), Char.code(d)): Bool},
  e2: {Nat.is_le(Char.code(c), Char.code(hi)) == Nat.is_le(Char.code(d), Char.code(hi)): Bool}
) -> {Span.has(Span{lo, hi}, c) == Span.has(Span{lo, hi}, d): Bool}:
  Equal.trans(
    Bool,
    Span.has(Span{lo, hi}, c),
    Bool.and(Nat.is_le(Char.code(lo), Char.code(c)), Nat.is_le(Char.code(c), Char.code(hi))),
    Span.has(Span{lo, hi}, d),
    Span.has_codes(lo, hi, c),
    (
      %Equal.sym(Bool, Nat.is_le(Char.code(lo), Char.code(c)), Nat.is_le(Char.code(lo), Char.code(d)), e1): {Bool.and(_, Nat.is_le(Char.code(c), Char.code(hi))) == Span.has(Span{lo, hi}, d): Bool}
      %Equal.sym(Bool, Nat.is_le(Char.code(c), Char.code(hi)), Nat.is_le(Char.code(d), Char.code(hi)), e2): {Bool.and(Nat.is_le(Char.code(lo), Char.code(d)), _) == Span.has(Span{lo, hi}, d): Bool}
      Equal.sym(Bool, Span.has(Span{lo, hi}, d), Bool.and(Nat.is_le(Char.code(lo), Char.code(d)), Nat.is_le(Char.code(d), Char.code(hi))), Span.has_codes(lo, hi, d)))
  )

# Span.has_rep at lo: lo is not above c (a) when it is not above the mark for
# c (b): a mark of lo that is not above c is not above the mark for c, which
# is not above c
def Span.has_rep.lo(
  +ms: List<&2, Char>,
  lo: Char,
  +c: Char,
  a: Bool,
  ea: {Nat.is_le(Char.code(lo), Char.code(c)) == a: Bool},
  b: Bool,
  eb: {Nat.is_le(Char.code(lo), Char.code(Spans.rep(ms, c))) == b: Bool},
  hm: {Spans.marked(ms, Char.code(lo)) == True{}: Bool}
) -> {a == b: Bool}:
  match a b:
    case True{} True{}:
      {==}
    case False{} False{}:
      {==}
    case True{} False{}:
      Empty.absurd(
        {True{} == False{}: Bool},
        Shared.Bool.true_ne_false(
          Equal.trans(
            Bool,
            True{},
            Nat.is_le(Char.code(lo), Char.code(Spans.rep(ms, c))),
            False{},
            Equal.sym(
              Bool,
              Nat.is_le(Char.code(lo), Char.code(Spans.rep(ms, c))),
              True{},
              Spans.rep_max(ms, c, Char.code(lo))(hm)(ea)
            ),
            eb
          )
        )
      )
    case False{} True{}:
      Empty.absurd(
        {False{} == True{}: Bool},
        Shared.Bool.true_ne_false(
          Equal.trans(
            Bool,
            True{},
            Nat.is_le(Char.code(lo), Char.code(c)),
            False{},
            Equal.sym(
              Bool,
              Nat.is_le(Char.code(lo), Char.code(c)),
              True{},
              Shared.Nat.le_trans(
                Char.code(lo),
                Char.code(Spans.rep(ms, c)),
                Char.code(c)
              )(eb)(Spans.rep_le(ms, c))
            ),
            ea
          )
        )
      )

# Span.has_rep at hi: c is not above hi (a) when the mark for c is not (b)
def Span.has_rep.hi(
  +ms: List<&2, Char>,
  +hi: Char,
  +c: Char,
  a: Bool,
  ea: {Nat.is_le(Char.code(c), Char.code(hi)) == a: Bool},
  b: Bool,
  eb: {Nat.is_le(Char.code(Spans.rep(ms, c)), Char.code(hi)) == b: Bool},
  he: {List.any.if(u => Spans.marked(ms, 1n+Char.code(hi)), Char.is_last(hi)) == True{}: Bool}
) -> {a == b: Bool}:
  match a b:
    case True{} True{}:
      {==}
    case False{} False{}:
      {==}
    case True{} False{}:
      Empty.absurd(
        {True{} == False{}: Bool},
        Shared.Bool.true_ne_false(
          Equal.trans(
            Bool,
            True{},
            Nat.is_le(Char.code(Spans.rep(ms, c)), Char.code(hi)),
            False{},
            Equal.sym(
              Bool,
              Nat.is_le(Char.code(Spans.rep(ms, c)), Char.code(hi)),
              True{},
              Shared.Nat.le_trans(
                Char.code(Spans.rep(ms, c)),
                Char.code(c),
                Char.code(hi)
              )(Spans.rep_le(ms, c))(ea)
            ),
            eb
          )
        )
      )
    case False{} True{}:
      Empty.absurd(
        {False{} == True{}: Bool},
        Shared.Bool.true_ne_false(
          Equal.trans(
            Bool,
            True{},
            Nat.is_le(Char.code(c), Char.code(hi)),
            False{},
            Equal.sym(
              Bool,
              Nat.is_le(Char.code(c), Char.code(hi)),
              True{},
              Spans.rep_hi(Char.is_last(hi), ms, hi, c, {==}, he, eb)
            ),
            ea
          )
        )
      )

# a span with a mark for each end holds both c and the mark for c, or neither
def Span.has_rep(
  +ms: List<&2, Char>,
  s: Span,
  +c: Char
) -> {
  Span.covered(ms, s) == True{}: Bool
} -> {Span.has(s, c) == Span.has(s, Spans.rep(ms, c)): Bool}:
  match s:
    case Span{+lo, +hi}:
      +e =>
        +r = Spans.rep(ms, c)
        +he = List.any.if(u => Spans.marked(ms, 1n+Char.code(hi)), Char.is_last(hi))
        Span.has_ends(
          lo,
          hi,
          c,
          r,
          Span.has_rep.lo(
            ms,
            lo,
            c,
            Nat.is_le(Char.code(lo), Char.code(c)),
            {==},
            Nat.is_le(Char.code(lo), Char.code(r)),
            {==},
            Shared.List.all.if_hit(Spans.marked(ms, Char.code(lo)), u => he)(e)
          ),
          Span.has_rep.hi(
            ms,
            hi,
            c,
            Nat.is_le(Char.code(c), Char.code(hi)),
            {==},
            Nat.is_le(Char.code(r), Char.code(hi)),
            {==},
            Shared.List.all.if_rest(Spans.marked(ms, Char.code(lo)), u => he)(e)
          )
        )

# Spans.rep_alike from the marks for the ends of the spans alone
def Spans.rep_alike.go(
  ss: List<&2, Span>,
  +ms: List<&2, Char>,
  +c: Char
) -> {
  Spans.covered.go(ss, ms) == True{}: Bool
} -> {Spans.alike(ss, c, Spans.rep(ms, c)) == True{}: Bool}:
  match ss:
    case Nil{}:
      e => {==}
    case Con{+s, +r}:
      +e =>
        Shared.List.all.if_both(
          Shared.Bool.is_eq(Span.has(s, c), Span.has(s, Spans.rep(ms, c))),
          u => Spans.alike(r, c, Spans.rep(ms, c))
        )(
          %Span.has_rep(ms, s, c)(Shared.List.all.if_hit(Span.covered(ms, s), u => Spans.covered.go(r, ms))(e)): {Shared.Bool.is_eq(Span.has(s, c), _) == True{}: Bool}
          Shared.Bool.is_eq_refl(Span.has(s, c)))(
          Spans.rep_alike.go(
            r,
            ms,
            c
          )(Shared.List.all.if_rest(Span.covered(ms, s), u => Spans.covered.go(r, ms))(e))
        )

# a character and its mark are in the same spans
law Spans.rep_alike:
  for ss: List<&2, Span>
  for +ms: List<&2, Char>
  for +c: Char
  {Spans.covered(ss, ms) == True{}: Bool} -> {Spans.alike(ss, c, Spans.rep(ms, c)) == True{}: Bool}

def Spans.rep_alike(ss, ms, c):
  +ss = ss
  e => Spans.rep_alike.go(
    ss,
    ms,
    c
  )(
    Shared.List.all.if_rest(
      List.contains(~Char, ~Char.is_eq, ms, Chr{0}),
      u => Spans.covered.go(ss, ms)
    )(e)
  )

# Spans.rep_in.pick when the mark kept is best, by whether best is the
# character of code 0 (z)
def Spans.rep_in.pick.best(
  z: Bool,
  m: Char,
  r: List<&2, Char>,
  best: Char,
  +ez: {Char.is_eq(Chr{0}, best) == z: Bool}
) -> {
  List.contains(~Char, ~Char.is_eq, Chr{0} <> r, best) == True{}: Bool
} -> {List.contains(~Char, ~Char.is_eq, Chr{0} <> m <> r, best) == True{}: Bool}:
  match z:
    case True{}:
      e =>
        %Equal.sym(
          Bool,
          Char.is_eq(Chr{0}, best),
          True{},
          ez
        ): {
          List.any.if(
            u => List.any.if(u => List.contains(~Char, ~Char.is_eq, r, best), Char.is_eq(m, best)),
            _
          )
            == True{}: Bool
        }
        {==}
    case False{}:
      e =>
        %Equal.sym(
          Bool,
          Char.is_eq(Chr{0}, best),
          False{},
          ez
        ): {
          List.any.if(
            u => List.any.if(u => List.contains(~Char, ~Char.is_eq, r, best), Char.is_eq(m, best)),
            _
          )
            == True{}: Bool
        }
        %Equal.sym(Bool, List.contains(~Char, ~Char.is_eq, r, best), True{}, (
            %ez: {List.any.if(u => List.contains(~Char, ~Char.is_eq, r, best), _) == True{}: Bool}
            e)): {List.any.if(u => List.any.if(u => _, Char.is_eq(m, best)), False{}) == True{}: Bool}
        Shared.List.any.if_true(Char.is_eq(m, best))

# Spans.rep_in.go at the first mark m, by whether it is picked (k)
def Spans.rep_in.pick(
  k: Bool,
  +m: Char,
  r: List<&2, Char>,
  +best: Char
) -> {
  List.contains(~Char, ~Char.is_eq, Chr{0} <> r, best) == True{}: Bool
} -> {
  List.contains(~Char, ~Char.is_eq, Chr{0} <> m <> r, Bool.pick(Char, k, m, best)) == True{}: Bool
}:
  match k:
    case True{}:
      e =>
        %Equal.sym(
          Bool,
          Char.is_eq(m, m),
          True{},
          Shared.Char.is_eq_refl(m)
        ): {
          List.any.if(
            u => List.any.if(u => List.contains(~Char, ~Char.is_eq, r, m), _),
            Char.is_eq(Chr{0}, m)
          )
            == True{}: Bool
        }
        Shared.List.any.if_true(Char.is_eq(Chr{0}, m))
    case False{}:
      Spans.rep_in.pick.best(Char.is_eq(Chr{0}, best), m, r, best, {==})

# the mark for c is a mark of ms or the character of code 0
def Spans.rep_in.go(
  ms: List<&2, Char>,
  +c: Char
) -> {List.contains(~Char, ~Char.is_eq, Chr{0} <> ms, Spans.rep(ms, c)) == True{}: Bool}:
  match ms:
    case Nil{}:
      {==}
    case Con{+m, +r}:
      Spans.rep_in.pick(
        Bool.and(
          Nat.is_le(Char.code(m), Char.code(c)),
          Nat.is_le(Char.code(Spans.rep(r, c)), Char.code(m))
        ),
        m,
        r,
        Spans.rep(r, c)
      )(Spans.rep_in.go(r, c))

# Spans.rep_in for a character x that is in ms or is the character of code 0,
# by whether it is that character (z)
def Spans.rep_in.at(
  z: Bool,
  -ms: List<&2, Char>,
  x: Char,
  ez: {Char.is_eq(Chr{0}, x) == z: Bool},
  hx: {List.any.if(u => List.contains(~Char, ~Char.is_eq, ms, x), z) == True{}: Bool},
  h0: {List.contains(~Char, ~Char.is_eq, ms, Chr{0}) == True{}: Bool}
) -> {List.contains(~Char, ~Char.is_eq, ms, x) == True{}: Bool}:
  match z:
    case False{}:
      hx
    case True{}:
      %Shared.Char.is_eq_sound('\0', x)(ez):
        {List.contains(Char, Char.is_eq, ms, _) == True{}: Bool}
      h0

# the mark for c is a mark of ms, when ms holds the character of code 0
law Spans.rep_in:
  for ms: List<&2, Char>
  for +c: Char
  {
    List.contains(~Char, ~Char.is_eq, ms, Chr{0}) == True{}: Bool
  } -> {List.contains(~Char, ~Char.is_eq, ms, Spans.rep(ms, c)) == True{}: Bool}

def Spans.rep_in(ms, c):
  +ms = ms
  h0 => Spans.rep_in.at(
    Char.is_eq(Chr{0}, Spans.rep(ms, c)),
    ms,
    Spans.rep(ms, c),
    {==},
    Spans.rep_in.go(ms, c),
    h0
  )

# The marks stand for every character
# -----------------------------------

# a list of marks holds the code of its first mark
def Spans.marked_head(
  m: Char,
  -ms: List<&2, Char>
) -> {Spans.marked(m <> ms, Char.code(m)) == True{}: Bool}:
  +m = m
  %Equal.sym(
    Bool,
    Cmp.is_eq(Nat.cmp(Char.code(m), Char.code(m))),
    True{},
    Shared.Cmp.is_eq_of(
      Nat.cmp(Char.code(m), Char.code(m)),
      Equal.sym(
        Cmp,
        Nat.cmp(Char.code(m), Char.code(m)),
        EQ{},
        Shared.Cmp.is_eq_sound(
          Nat.cmp(Char.code(m), Char.code(m))
        )(Shared.Nat.is_eq_refl(Char.code(m)))
      )
    )
  ):
    {
      List.any.if(
        u => Shared.List.some(Char, Nat, n => m => Nat.is_eq(Char.code(m), n), ms, Char.code(m)),
        _
      )
        == True{}: Bool
    }
  {==}

# a list of marks holds a code that the marks after its first hold
def Spans.marked_more(
  m: Char,
  -ms: List<&2, Char>,
  n: Nat
) -> {Spans.marked(ms, n) == True{}: Bool} -> {Spans.marked(m <> ms, n) == True{}: Bool}:
  e =>
    %Equal.sym(
      Bool,
      Spans.marked(ms, n),
      True{},
      e
    ): {List.any.if(u => _, Nat.is_eq(Char.code(m), n)) == True{}: Bool}
    Shared.List.any.if_true(Nat.is_eq(Char.code(m), n))

# Span.covered_more for the mark after hi, by whether hi is the last character
# (last)
def Span.covered_more.end(
  last: Bool,
  m: Char,
  -ms: List<&2, Char>,
  n: Nat
) -> {
  List.any.if(u => Spans.marked(ms, n), last) == True{}: Bool
} -> {List.any.if(u => Spans.marked(m <> ms, n), last) == True{}: Bool}:
  match last:
    case True{}:
      e => {==}
    case False{}:
      e => Spans.marked_more(m, ms, n)(e)

# one more mark keeps a mark for each end of s
def Span.covered_more(
  +m: Char,
  +ms: List<&2, Char>,
  s: Span
) -> {Span.covered(ms, s) == True{}: Bool} -> {Span.covered(m <> ms, s) == True{}: Bool}:
  match s:
    case Span{+lo, +hi}:
      +e =>
        +he = List.any.if(u => Spans.marked(ms, 1n+Char.code(hi)), Char.is_last(hi))
        Shared.List.all.if_both(
          Spans.marked(m <> ms, Char.code(lo)),
          u => List.any.if(u => Spans.marked(m <> ms, 1n+Char.code(hi)), Char.is_last(hi))
        )(
          Spans.marked_more(
            m,
            ms,
            Char.code(lo)
          )(Shared.List.all.if_hit(Spans.marked(ms, Char.code(lo)), u => he)(e))
        )(
          Span.covered_more.end(
            Char.is_last(hi),
            m,
            ms,
            1n+Char.code(hi)
          )(Shared.List.all.if_rest(Spans.marked(ms, Char.code(lo)), u => he)(e))
        )

# one more mark keeps a mark for each end of each span of ss
def Spans.covered_more(
  ss: List<&2, Span>,
  +m: Char,
  +ms: List<&2, Char>
) -> {Spans.covered.go(ss, ms) == True{}: Bool} -> {Spans.covered.go(ss, m <> ms) == True{}: Bool}:
  match ss:
    case Nil{}:
      e => {==}
    case Con{+s, +r}:
      +e => Shared.List.all.if_both(
        Span.covered(m <> ms, s),
        u => Spans.covered.go(r, m <> ms)
      )(
        Span.covered_more(
          m,
          ms,
          s
        )(Shared.List.all.if_hit(Span.covered(ms, s), u => Spans.covered.go(r, ms))(e))
      )(
        Spans.covered_more(
          r,
          m,
          ms
        )(Shared.List.all.if_rest(Span.covered(ms, s), u => Spans.covered.go(r, ms))(e))
      )

# Span.marks_covered for the mark after hi, by whether hi is the last
# character (last)
def Span.marks_covered.end(
  last: Bool,
  lo: Char,
  +hi: Char,
  rest: List<&2, Char>,
  el: {Char.is_last(hi) == last: Bool}
) -> {
  List.any.if(
    u => Spans.marked(lo <> Char.after(hi) <> rest, 1n+Char.code(hi)),
    last
  )
    == True{}: Bool
}:
  match last:
    case True{}:
      {==}
    case False{}:
      Spans.marked_more(lo, Char.after(hi) <> rest, 1n+Char.code(hi))(
        %Char.after_code(hi)(el): {Spans.marked(Char.after(hi) <> rest, _) == True{}: Bool}
        Spans.marked_head(Char.after(hi), rest))

# the marks of s hold a mark for each end of s
def Span.marks_covered(
  s: Span,
  +rest: List<&2, Char>
) -> {Span.covered(Span.marks(s, rest), s) == True{}: Bool}:
  match s:
    case Span{+lo, +hi}:
      +l = {lo <> Char.after(hi) <> rest: List<&2, Char>}
      Shared.List.all.if_both(
        Spans.marked(l, Char.code(lo)),
        u => List.any.if(u => Spans.marked(l, 1n+Char.code(hi)), Char.is_last(hi))
      )(
        Spans.marked_head(lo, Char.after(hi) <> rest)
      )(Span.marks_covered.end(Char.is_last(hi), lo, hi, rest, {==}))

# the marks of each span of ss hold a mark for each end of each span of ss
def Spans.marks_covered.go(
  ss: List<&2, Span>
) -> {Spans.covered.go(ss, Spans.marks.go(ss)) == True{}: Bool}:
  match ss:
    case Nil{}:
      {==}
    case Con{Span{+lo, +hi}, +r}:
      +l = {lo <> Char.after(hi) <> Spans.marks.go(r): List<&2, Char>}
      Shared.List.all.if_both(
        Span.covered(l, Span{lo, hi}),
        u => Spans.covered.go(r, l)
      )(
        Span.marks_covered(Span{lo, hi}, Spans.marks.go(r))
      )(
        Spans.covered_more(
          r,
          lo,
          Char.after(hi) <> Spans.marks.go(r)
        )(Spans.covered_more(r, Char.after(hi), Spans.marks.go(r))(Spans.marks_covered.go(r)))
      )

# the marks of ss can stand for every character under ss
law Spans.marks_covered:
  for ss: List<&2, Span>
  {Spans.covered(ss, Spans.marks(ss)) == True{}: Bool}

def Spans.marks_covered(ss):
  +ss = ss
  Shared.List.all.if_both(
    List.contains(~Char, ~Char.is_eq, Chr{0} <> Spans.marks.go(ss), Chr{0}),
    u => Spans.covered.go(ss, Chr{0} <> Spans.marks.go(ss))
  )({==})(Spans.covered_more(ss, Chr{0}, Spans.marks.go(ss))(Spans.marks_covered.go(ss)))
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information
# bend-lint: expect-end bend-lint-rules/performance/loop_invariant_call@information
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information
