import Base
import ../shared/shared/ledger.bend as Ledgers
import ../shared/shared/shared/shared/shared.bend as Shared
import ../shared/shared/shared/text.bend as Texts
import ./answers.bend as Answers
import ./content.bend as Contents
import ./facts.bend as Facts
import ./mirror.bend as Mirror
import ./shared/files.bend as Files
import ./shared/format.bend as Formats
import ./shared/lists.bend as Lists
import ./spec.bend as Spec

# What a writer is told: the laws
# -------------------------------
# The reply to Affects is the paths seen from us in the newer content whose
# words differ in the two contents. Seen holds only paths reached from us
# (affects_only), and, being closed under imports, each of them (affects_all).

# Members
# -------

# the path x is among xs
def In(xs: List<&2, String>, x: String) -> Data:
  {List.contains(~String, ~String.eq, xs, x) == True{}: Bool}

# a list holds its first path
def In.head(h: String, -t: List<&2, String>) -> In(h <> t, h):
  Lists.List.contains_head(~String, ~String.eq, ~Texts.String.laws(), h, t)

# a member of t is a member of h <> t
def In.tail(h: String, t: List<&2, String>, x: String) -> In(t, x) -> In(h <> t, x):
  Shared.List.contains_cons(~String, ~String.eq, h, t, x)

# a member of h <> t is h or a member of t: what follows from each follows
def In.cases(
  -P: Type,
  +h: String,
  -t: List<&2, String>,
  +x: String,
  hin: In(h <> t, x),
  a: {h == x: String} -> P,
  b: In(t, x) -> P
) -> P:
  Lists.List.contains_cons_by(~String, ~String.eq, ~Texts.String.laws(), P, h, t, x, hin, a, b)

# the empty list has no member
def In.nil(-P: Type, -x: String, h: In([], x)) -> P:
  Empty.absurd(P, Shared.Bool.false_ne_true(h))

# a member of xs is a member of the equal list ys
def In.cast(-xs: List<&2, String>, -ys: List<&2, String>, -x: String, e: {xs == ys: List<&2, String>}, h: In(xs, x)) -> In(ys, x):
  %e: In(_, x)
  h

# each member of ps is a member of ks when ps is within ks
def In.within(ps: List<&2, String>, +ks: List<&2, String>, +x: String) -> {
  Shared.List.within(~String, ~String.eq, ps, ks) == True{}: Bool
} -> In(ps, x) -> In(ks, x):
  match ps:
    case Nil{}:
      hw => h => In.nil(In(ks, x), x, h)
    case Con{+p, +r}:
      +hw => h => In.cases(
        In(ks, x),
        p,
        r,
        x,
        h,
        e => (
          %e: In(ks, _)
          Shared.Bool.and_true_left(List.contains(~String, ~String.eq, ks, p), Shared.List.within(~String, ~String.eq, r, ks))(hw)
        ),
        t => In.within(r, ks, x)(Shared.Bool.and_true_right(List.contains(~String, ~String.eq, ks, p), Shared.List.within(~String, ~String.eq, r, ks))(hw))(t)
      )

# Adding paths to the seen ones
# -----------------------------

# seen with the path q, if it lacks it: one step of Reach.add
def Reach.put(+seen: List<&2, String>, +q: String) -> List<&2, String>:
  Shared.Bool.when(
    List<&2, String>,
    List.contains(~String, ~String.eq, seen, q),
    u => seen,
    u => List.append(&2, String, seen, [q])
  )

# a seen path stays seen when q is put
def Reach.put_keeps(+seen: List<&2, String>, +q: String, +x: String) -> In(seen, x) -> In(Reach.put(seen, q), x):
  Lists.Bool.by(
    c => In(seen, x) -> In(Shared.Bool.when(List<&2, String>, c, u => seen, u => List.append(&2, String, seen, [q])), x),
    List.contains(~String, ~String.eq, seen, q),
    e => h => h,
    e => h => Shared.List.contains_left(~String, ~String.eq, seen, [q], x, h)
  )

# the path that is put is seen
def Reach.put_has(+seen: List<&2, String>, +q: String) -> In(Reach.put(seen, q), q):
  Lists.Bool.by(
    c => In(Shared.Bool.when(List<&2, String>, c, u => seen, u => List.append(&2, String, seen, [q])), q),
    List.contains(~String, ~String.eq, seen, q),
    e => e,
    e => Shared.List.contains_right(~String, ~String.eq, seen, [q], q, In.head(q, []))
  )

# a member of seen ++ [q] was seen or is q
def Reach.put_in.at(+seen: List<&2, String>, +q: String, +x: String) -> In(List.append(&2, String, seen, [q]), x) -> In(seen, x) | {q == x: String}:
  h => Lists.Bool.by(
    c => {Bool.or(c, List.contains(~String, ~String.eq, [q], x)) == True{}: Bool} -> In(seen, x) | {q == x: String},
    List.contains(~String, ~String.eq, seen, x),
    e => g => Inl{e},
    e => g => Inr{In.cases({q == x: String}, q, [], x, g, a => a, b => In.nil({q == x: String}, x, b))}
  )(
    Equal.trans(
      Bool,
      Bool.or(List.contains(~String, ~String.eq, seen, x), List.contains(~String, ~String.eq, [q], x)),
      List.contains(~String, ~String.eq, List.append(&2, String, seen, [q]), x),
      True{},
      Equal.sym(
        Bool,
        List.contains(~String, ~String.eq, List.append(&2, String, seen, [q]), x),
        Bool.or(List.contains(~String, ~String.eq, seen, x), List.contains(~String, ~String.eq, [q], x)),
        Shared.List.contains_append(~String, ~String.eq, seen, [q], x)
      ),
      h
    )
  )

# a path seen after q is put was seen or is q
def Reach.put_in(+seen: List<&2, String>, +q: String, +x: String) -> In(Reach.put(seen, q), x) -> In(seen, x) | {q == x: String}:
  Lists.Bool.by(
    c => In(Shared.Bool.when(List<&2, String>, c, u => seen, u => List.append(&2, String, seen, [q])), x) -> In(seen, x) | {q == x: String},
    List.contains(~String, ~String.eq, seen, q),
    e => h => Inl{h},
    e => h => Reach.put_in.at(seen, q, x)(h)
  )

# a seen path stays seen when the paths qs are added
def Reach.add_keeps(qs: List<&2, String>, +seen: List<&2, String>, +x: String) -> In(seen, x) -> In(Answers.Reach.add(qs, seen), x):
  match qs:
    case Nil{}:
      h => h
    case Con{+q, rest}:
      h => Reach.add_keeps(rest, Reach.put(seen, q), x)(Reach.put_keeps(seen, q, x)(h))

# each added path is seen
def Reach.add_has(qs: List<&2, String>, +seen: List<&2, String>, +x: String) -> In(qs, x) -> In(Answers.Reach.add(qs, seen), x):
  match qs:
    case Nil{}:
      h => In.nil(In(seen, x), x, h)
    case Con{+q, +rest}:
      h => In.cases(
        In(Answers.Reach.add(rest, Reach.put(seen, q)), x),
        q,
        rest,
        x,
        h,
        e => (
          %e: In(Answers.Reach.add(rest, Reach.put(seen, q)), _)
          Reach.add_keeps(rest, Reach.put(seen, q), q)(Reach.put_has(seen, q))
        ),
        t => Reach.add_has(rest, Reach.put(seen, q), x)(t)
      )

# Reach.add_in, once x is known to have been seen or to be q
def Reach.add_in.at(-seen: List<&2, String>, q: String, -rest: List<&2, String>, -x: String, r: In(seen, x) | {q == x: String}) -> In(seen, x) | In(q <> rest, x):
  match r:
    case Inl{h}:
      Inl{h}
    case Inr{e}:
      Inr{
        (
          %e: In(q <> rest, _)
          In.head(q, rest)
        )
      }

# Reach.add_in, by where the rest of the paths found x
def Reach.add_in.of(+seen: List<&2, String>, +q: String, +rest: List<&2, String>, +x: String, r: In(Reach.put(seen, q), x) | In(rest, x)) -> In(seen, x) | In(q <> rest, x):
  match r:
    case Inl{h}:
      Reach.add_in.at(seen, q, rest, x, Reach.put_in(seen, q, x)(h))
    case Inr{h}:
      Inr{In.tail(q, rest, x)(h)}

# a path seen after the paths qs are added was seen or is one of them
def Reach.add_in(qs: List<&2, String>, +seen: List<&2, String>, +x: String) -> In(Answers.Reach.add(qs, seen), x) -> In(seen, x) | In(qs, x):
  match qs:
    case Nil{}:
      h => Inl{h}
    case Con{+q, +rest}:
      h => Reach.add_in.of(seen, q, rest, x, Reach.add_in(rest, Reach.put(seen, q), x)(h))

# Growing by the imports
# ----------------------

# a seen path stays seen when seen grows by the imports of ps
def Reach.grow_keeps(+b: Files.Files(), +bs: List<&2, String>, ps: List<&2, String>, +seen: List<&2, String>, +x: String) -> In(seen, x) -> In(
  Answers.Reach.grow(b, bs, ps, seen),
  x
):
  match ps:
    case Nil{}:
      h => h
    case Con{+p, rest}:
      h => Reach.grow_keeps(b, bs, rest, Answers.Reach.add(Answers.Reach.imports(b, bs, p), seen), x)(
        Reach.add_keeps(Answers.Reach.imports(b, bs, p), seen, x)(h)
      )

# a seen path stays seen through the rounds
def Reach.go_keeps(fuel: Nat, +b: Files.Files(), +bs: List<&2, String>, +seen: List<&2, String>, +x: String) -> In(seen, x) -> In(
  Answers.Reach.go(fuel, b, bs, seen),
  x
):
  match fuel:
    case 0n:
      h => h
    case 1n+f:
      h => Reach.go_keeps(f, b, bs, Answers.Reach.grow(b, bs, seen, seen), x)(Reach.grow_keeps(b, bs, seen, seen, x)(h))

# x was seen, or is an import of one of the paths ps
def Reach.Grown(b: Files.Files(), bs: List<&2, String>, ps: List<&2, String>, seen: List<&2, String>, x: String) -> Type:
  In(seen, x) | Exists(String, p => In(ps, p) & In(Answers.Reach.imports(b, bs, p), x))

# Reach.grow_in, once x is known to have been seen or to be an import of p
def Reach.grow_in.at(
  -b: Files.Files(),
  -bs: List<&2, String>,
  p: String,
  -rest: List<&2, String>,
  -seen: List<&2, String>,
  -x: String,
  r: In(seen, x) | In(Answers.Reach.imports(b, bs, p), x)
) -> Reach.Grown(b, bs, p <> rest, seen, x):
  match r:
    case Inl{h}:
      Inl{h}
    case Inr{h}:
      +p = p
      Inr{(p, (In.head(p, rest), h))}

# Reach.grow_in, by where the rest of the paths found x
def Reach.grow_in.of(
  +b: Files.Files(),
  +bs: List<&2, String>,
  +p: String,
  +rest: List<&2, String>,
  +seen: List<&2, String>,
  +x: String,
  r: Reach.Grown(b, bs, rest, Answers.Reach.add(Answers.Reach.imports(b, bs, p), seen), x)
) -> Reach.Grown(b, bs, p <> rest, seen, x):
  match r:
    case Inl{h}:
      Reach.grow_in.at(b, bs, p, rest, seen, x, Reach.add_in(Answers.Reach.imports(b, bs, p), seen, x)(h))
    case Inr{w}:
      (+p2, w2) = w
      (h1, h2) = w2
      Inr{(p2, (In.tail(p, rest, p2)(h1), h2))}

# a path seen after seen grows by the imports of ps was seen or is an import
# of one of ps
def Reach.grow_in(+b: Files.Files(), +bs: List<&2, String>, ps: List<&2, String>, +seen: List<&2, String>, +x: String) -> In(
  Answers.Reach.grow(b, bs, ps, seen),
  x
) -> Reach.Grown(b, bs, ps, seen, x):
  match ps:
    case Nil{}:
      h => Inl{h}
    case Con{+p, +rest}:
      h => Reach.grow_in.of(
        b,
        bs,
        p,
        rest,
        seen,
        x,
        Reach.grow_in(b, bs, rest, Answers.Reach.add(Answers.Reach.imports(b, bs, p), seen), x)(h)
      )

# Reads and imports
# -----------------

# a read of a version whose content is b is a read of b
def Content.read_of(+s: Facts.Facts(), +c: Ledgers.Line, +k: Nat, +b: Files.Files(), +p: String) -> {
  Contents.Content.of(s, c, k) == Some{b}: Maybe<&2, Files.Files()>
} -> {
  Contents.Content.read(s, c, k, p) == Some{Files.Files.get(b, p)}: Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  hb => Equal.cong(
    Maybe<&2, Files.Files()>,
    Maybe<&2, Maybe<&2, List<&2, U32>>>,
    m => Contents.Content.get(m, p),
    Contents.Content.of(s, c, k),
    Some{b},
    hb
  )

# the words that a read of a version gives are those of its content b
def Content.read_get(+s: Facts.Facts(), +c: Ledgers.Line, +k: Nat, +b: Files.Files(), +p: String, +x: Maybe<&2, List<&2, U32>>) -> {
  Contents.Content.of(s, c, k) == Some{b}: Maybe<&2, Files.Files()>
} -> {
  Contents.Content.read(s, c, k, p) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
} -> {Files.Files.get(b, p) == x: Maybe<&2, List<&2, U32>>}:
  hb => er => Shared.Maybe.some_inj(
    Maybe<&2, List<&2, U32>>,
    Files.Files.get(b, p),
    x,
    Equal.trans(
      Maybe<&2, Maybe<&2, List<&2, U32>>>,
      Some{Files.Files.get(b, p)},
      Contents.Content.read(s, c, k, p),
      Some{x},
      Equal.sym(
        Maybe<&2, Maybe<&2, List<&2, U32>>>,
        Contents.Content.read(s, c, k, p),
        Some{Files.Files.get(b, p)},
        Content.read_of(s, c, k, b, p)(hb)
      ),
      er
    )
  )

# an import of the words m at p, if any, is an import of words that m holds
def Reach.imports.of_in(m: Maybe<&2, List<&2, U32>>, +p: String, +bs: List<&2, String>, +x: String) -> In(
  Answers.Reach.imports.of(p, bs, m),
  x
) -> Exists(
  List<&2, U32>,
  ws => {m == Some{ws}: Maybe<&2, List<&2, U32>>} & In(Formats.Format.imports(p, ws, bs), x)
):
  match m:
    case None{}:
      h => In.nil(
        Exists(List<&2, U32>, ws => {None{} == Some{ws}: Maybe<&2, List<&2, U32>>} & In(Formats.Format.imports(p, ws, bs), x)),
        x,
        h
      )
    case Some{ws}:
      h => (ws, ({==}, h))

# Imports.step, once the words of p are known
def Imports.step.of(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +bs: List<&2, String>,
  +b: Files.Files(),
  +p: String,
  +q: String,
  +rest: List<&2, String>,
  +x: String,
  hb: {Contents.Content.of(s, c, k) == Some{b}: Maybe<&2, Files.Files()>},
  ch: Mirror.Imports(s, c, k, bs, q, rest, x),
  w: Exists(List<&2, U32>, ws => {Files.Files.get(b, p) == Some{ws}: Maybe<&2, List<&2, U32>>} & In(Formats.Format.imports(p, ws, bs), q))
) -> Mirror.Imports(s, c, k, bs, p, q <> rest, x):
  (+ws, w2) = w
  (e, hi) = w2
  (
    ws,
    (
      (
        %e: {Contents.Content.read(s, c, k, p) == Some{_}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
        Content.read_of(s, c, k, b, p)(hb)
      ),
      (hi, ch)
    )
  )

# a chain of imports from q, after an import q of p in the content b of the
# version, is a chain from p
def Imports.step(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +bs: List<&2, String>,
  +b: Files.Files(),
  +p: String,
  +q: String,
  +rest: List<&2, String>,
  +x: String,
  hb: {Contents.Content.of(s, c, k) == Some{b}: Maybe<&2, Files.Files()>},
  hi: In(Answers.Reach.imports(b, bs, p), q),
  ch: Mirror.Imports(s, c, k, bs, q, rest, x)
) -> Mirror.Imports(s, c, k, bs, p, q <> rest, x):
  Imports.step.of(s, c, k, bs, b, p, q, rest, x, hb, ch, Reach.imports.of_in(Files.Files.get(b, p), p, bs, q)(hi))

# Each seen path is reached
# -------------------------

# the path x is reached from one of the paths us, in version k of c
def Reach.From(s: Facts.Facts(), c: Ledgers.Line, k: Nat, bs: List<&2, String>, us: List<&2, String>, x: String) -> Type:
  Exists(
    String,
    u => In(us, u) & Exists(List<&2, String>, ps => Mirror.Imports(s, c, k, bs, u, ps, x))
  )

# Reach.go_in, once the path u that x is reached from is known to have been
# seen or to be an import of a seen path
def Reach.go_in.at(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +bs: List<&2, String>,
  +b: Files.Files(),
  +seen: List<&2, String>,
  +x: String,
  +u: String,
  hb: {Contents.Content.of(s, c, k) == Some{b}: Maybe<&2, Files.Files()>},
  r: Reach.Grown(b, bs, seen, seen, u),
  w: Exists(List<&2, String>, ps => Mirror.Imports(s, c, k, bs, u, ps, x))
) -> Reach.From(s, c, k, bs, seen, x):
  match r:
    case Inl{h}:
      (u, (h, w))
    case Inr{v}:
      (+p, v1) = v
      (hp, hi) = v1
      (+ps, ch) = w
      (p, (hp, (u <> ps, Imports.step(s, c, k, bs, b, p, u, ps, x, hb, hi, ch))))

# Reach.go_in, from what the later rounds give
def Reach.go_in.of(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +bs: List<&2, String>,
  +b: Files.Files(),
  +seen: List<&2, String>,
  +x: String,
  hb: {Contents.Content.of(s, c, k) == Some{b}: Maybe<&2, Files.Files()>},
  w: Reach.From(s, c, k, bs, Answers.Reach.grow(b, bs, seen, seen), x)
) -> Reach.From(s, c, k, bs, seen, x):
  (+u, w1) = w
  (hu, w2) = w1
  Reach.go_in.at(s, c, k, bs, b, seen, x, u, hb, Reach.grow_in(b, bs, seen, seen, u)(hu), w2)

# a path seen after the rounds is reached from a path seen before them, in a
# version whose content is b
def Reach.go_in(
  fuel: Nat,
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +bs: List<&2, String>,
  +b: Files.Files(),
  +seen: List<&2, String>,
  +x: String,
  +hb: {Contents.Content.of(s, c, k) == Some{b}: Maybe<&2, Files.Files()>}
) -> In(Answers.Reach.go(fuel, b, bs, seen), x) -> Reach.From(s, c, k, bs, seen, x):
  match fuel:
    case 0n:
      h => (x, (h, ([], {==})))
    case 1n+f:
      h => Reach.go_in.of(
        s,
        c,
        k,
        bs,
        b,
        seen,
        x,
        hb,
        Reach.go_in(f, s, c, k, bs, b, Answers.Reach.grow(b, bs, seen, seen), x, hb)(h)
      )

# the paths seen from us in the content b: what Reach.of answers
def Reach.seen(+b: Files.Files(), +bs: List<&2, String>, +us: List<&2, String>) -> List<&2, String>:
  Answers.Reach.go(
    1n+Nat.add(
      List.length(&2, String, Answers.Reach.add(us, [])),
      List.length(&2, String, Files.Files.paths(b))
    ),
    b,
    bs,
    Answers.Reach.add(us, [])
  )

# Reach.start_in, by where Reach.add found u
def Reach.start_in.of(-us: List<&2, String>, -u: String, r: In([], u) | In(us, u)) -> In(us, u):
  match r:
    case Inl{h}:
      In.nil(In(us, u), u, h)
    case Inr{h}:
      h

# a path of the first seen ones is one of us
def Reach.start_in(+us: List<&2, String>, +u: String) -> In(Answers.Reach.add(us, []), u) -> In(us, u):
  h => Reach.start_in.of(us, u, Reach.add_in(us, [], u)(h))

# Reach.seen_in, from what Reach.go_in gives
def Reach.seen_in.of(
  -s: Facts.Facts(),
  -c: Ledgers.Line,
  -k: Nat,
  -bs: List<&2, String>,
  +us: List<&2, String>,
  -x: String,
  w: Reach.From(s, c, k, bs, Answers.Reach.add(us, []), x)
) -> Mirror.Reaches(s, c, k, bs, us, x):
  (+u, w1) = w
  (hu, w2) = w1
  (u, (Reach.start_in(us, u)(hu), w2))

# each seen path is reached from us, in a version whose content is b
def Reach.seen_in(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +bs: List<&2, String>,
  +b: Files.Files(),
  +us: List<&2, String>,
  +x: String,
  +hb: {Contents.Content.of(s, c, k) == Some{b}: Maybe<&2, Files.Files()>}
) -> In(Reach.seen(b, bs, us), x) -> Mirror.Reaches(s, c, k, bs, us, x):
  h => Reach.seen_in.of(
    s,
    c,
    k,
    bs,
    us,
    x,
    Reach.go_in(
      1n+Nat.add(
        List.length(&2, String, Answers.Reach.add(us, [])),
        List.length(&2, String, Files.Files.paths(b))
      ),
      s,
      c,
      k,
      bs,
      b,
      Answers.Reach.add(us, []),
      x,
      hb
    )(h)
  )

# Each reached path is seen
# -------------------------

# the seen paths are closed under imports in the content b
def Reach.Closed(b: Files.Files(), bs: List<&2, String>, seen: List<&2, String>) -> Data:
  {
    Shared.List.holds(~String, ~Answers.Reached, ~Answers.Reached.closed, seen, Answers.Reached{b, bs, seen}) == True{}: Bool
  }

# an import of a seen path is seen, when the seen paths are closed
def Reach.closed_in(+b: Files.Files(), +bs: List<&2, String>, +seen: List<&2, String>, +p: String, +x: String) -> Reach.Closed(b, bs, seen) -> In(
  seen,
  p
) -> In(Answers.Reach.imports(b, bs, p), x) -> In(seen, x):
  hc => hp => hi => In.within(Answers.Reach.imports(b, bs, p), seen, x)(
    Lists.List.holds_in(
      ~String,
      ~Answers.Reached,
      ~Answers.Reached.closed,
      ~String.eq,
      ~Texts.String.laws(),
      seen,
      Answers.Reached{b, bs, seen},
      p
    )(hc)(hp)
  )(hi)

# the path q is an import of a in the content b, as a step of a chain says
def Reach.imports_of(+s: Facts.Facts(), +c: Ledgers.Line, +k: Nat, +bs: List<&2, String>, +b: Files.Files(), +a: String, +q: String, +ws: List<&2, U32>) -> {
  Contents.Content.of(s, c, k) == Some{b}: Maybe<&2, Files.Files()>
} -> {
  Contents.Content.read(s, c, k, a) == Some{Some{ws}}: Maybe<&2, Maybe<&2, List<&2, U32>>>
} -> In(Formats.Format.imports(a, ws, bs), q) -> In(Answers.Reach.imports(b, bs, a), q):
  hb => er => hi =>
    %Equal.sym(
      Maybe<&2, List<&2, U32>>,
      Files.Files.get(b, a),
      Some{ws},
      Content.read_get(s, c, k, b, a, Some{ws})(hb)(er)
    ): In(Answers.Reach.imports.of(a, bs, _), q)
    hi

# Reach.chain_in at a step of the chain w, given the rest of the chain (ih)
def Reach.chain_in.at(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +bs: List<&2, String>,
  +b: Files.Files(),
  +seen: List<&2, String>,
  +a: String,
  +q: String,
  -rest: List<&2, String>,
  -x: String,
  hb: {Contents.Content.of(s, c, k) == Some{b}: Maybe<&2, Files.Files()>},
  hc: Reach.Closed(b, bs, seen),
  ih: Mirror.Imports(s, c, k, bs, q, rest, x) -> In(seen, q) -> In(seen, x),
  ha: In(seen, a),
  w: Exists(
    List<&2, U32>,
    ws => {
      Contents.Content.read(s, c, k, a) == Some{Some{ws}}: Maybe<&2, Maybe<&2, List<&2, U32>>>
    }
      & (In(Formats.Format.imports(a, ws, bs), q) & Mirror.Imports(s, c, k, bs, q, rest, x))
  )
) -> In(seen, x):
  (+ws, w1) = w
  (er, w2) = w1
  (hi, ch2) = w2
  ih(ch2)(Reach.closed_in(b, bs, seen, a, q)(hc)(ha)(Reach.imports_of(s, c, k, bs, b, a, q, ws)(hb)(er)(hi)))

# the end of a chain of imports from a seen path is seen, when the seen paths
# are closed in the content b of the version
def Reach.chain_in(
  ps: List<&2, String>,
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +bs: List<&2, String>,
  +b: Files.Files(),
  +seen: List<&2, String>,
  +a: String,
  +x: String,
  +hb: {Contents.Content.of(s, c, k) == Some{b}: Maybe<&2, Files.Files()>},
  +hc: Reach.Closed(b, bs, seen)
) -> Mirror.Imports(s, c, k, bs, a, ps, x) -> In(seen, a) -> In(seen, x):
  match ps:
    case Nil{}:
      ch => ha =>
        %ch: In(seen, _)
        ha
    case Con{+q, rest}:
      ch => ha => Reach.chain_in.at(
        s,
        c,
        k,
        bs,
        b,
        seen,
        a,
        q,
        rest,
        x,
        hb,
        hc,
        Reach.chain_in(rest, s, c, k, bs, b, seen, q, x, hb, hc),
        ha,
        ch
      )

# The paths whose words differ
# ----------------------------

# a member of r is a member of r with h put, or not
def Delta.put_skip(keep: Bool, h: String, r: List<&2, String>, x: String) -> In(r, x) -> In(List.filter.put(String, h, r, keep), x):
  match keep:
    case False{}:
      i => i
    case True{}:
      In.tail(h, r, x)

# the first path is among the changed ones when it differs
def Delta.changed_head(+g: Answers.Delta, +h: String, +rest: List<&2, String>) -> {Answers.Delta.differ(g, h) == True{}: Bool} -> In(
  List.filter.put(String, h, Answers.Delta.changed(g, rest), Answers.Delta.differ(g, h)),
  h
):
  d =>
    %Equal.sym(Bool, Answers.Delta.differ(g, h), True{}, d): In(List.filter.put(String, h, Answers.Delta.changed(g, rest), _), h)
    In.head(h, Answers.Delta.changed(g, rest))

# a path of ps that differs is among the changed ones
def Delta.changed_has(ps: List<&2, String>, +g: Answers.Delta, +p: String) -> In(ps, p) -> {Answers.Delta.differ(g, p) == True{}: Bool} -> In(
  Answers.Delta.changed(g, ps),
  p
):
  match ps:
    case Nil{}:
      hin => d => In.nil(In([], p), p, hin)
    case Con{+h, +rest}:
      hin => In.cases(
        {Answers.Delta.differ(g, p) == True{}: Bool} -> In(
          List.filter.put(String, h, Answers.Delta.changed(g, rest), Answers.Delta.differ(g, h)),
          p
        ),
        h,
        rest,
        p,
        hin,
        e => (
          %e: {Answers.Delta.differ(g, _) == True{}: Bool} -> In(
            List.filter.put(String, h, Answers.Delta.changed(g, rest), Answers.Delta.differ(g, h)),
            _
          )
          Delta.changed_head(g, h, rest)
        ),
        t => d => Delta.put_skip(Answers.Delta.differ(g, h), h, Answers.Delta.changed(g, rest), p)(Delta.changed_has(rest, g, p)(t)(d))
      )

# Delta.changed_in, from what the rest of the paths give
def Delta.changed_in.up(
  -g: Answers.Delta,
  h: String,
  rest: List<&2, String>,
  p: String,
  w: In(rest, p) & {Answers.Delta.differ(g, p) == True{}: Bool}
) -> In(h <> rest, p) & {Answers.Delta.differ(g, p) == True{}: Bool}:
  (a, d) = w
  (In.tail(h, rest, p)(a), d)

# a changed path is one of ps, and differs
def Delta.changed_in(ps: List<&2, String>, +g: Answers.Delta, +p: String) -> In(Answers.Delta.changed(g, ps), p) -> In(ps, p) & {
  Answers.Delta.differ(g, p) == True{}: Bool
}:
  match ps:
    case Nil{}:
      hin => In.nil(In([], p) & {Answers.Delta.differ(g, p) == True{}: Bool}, p, hin)
    case Con{+h, +rest}:
      Lists.Bool.by(
        k => In(List.filter.put(String, h, Answers.Delta.changed(g, rest), k), p) -> In(h <> rest, p) & {
          Answers.Delta.differ(g, p) == True{}: Bool
        },
        Answers.Delta.differ(g, h),
        e => hin => In.cases(
          In(h <> rest, p) & {Answers.Delta.differ(g, p) == True{}: Bool},
          h,
          Answers.Delta.changed(g, rest),
          p,
          hin,
          eq => (
            %eq: In(h <> rest, _) & {Answers.Delta.differ(g, _) == True{}: Bool}
            (In.head(h, rest), e)
          ),
          t => Delta.changed_in.up(g, h, rest, p, Delta.changed_in(rest, g, p)(t))
        ),
        e => hin => Delta.changed_in.up(g, h, rest, p, Delta.changed_in(rest, g, p)(hin))
      )

# the words x, if any, are the same as the words y, if any
def Words.same(x: Maybe<&2, List<&2, U32>>, y: Maybe<&2, List<&2, U32>>) -> Bool:
  Shared.Maybe.is_eq(~List<&2, U32>, ~Facts.Words.is_eq, x, y)

# words, if any, are the same as themselves
def Words.same_refl(x: Maybe<&2, List<&2, U32>>) -> {Words.same(x, x) == True{}: Bool}:
  match x:
    case None{}:
      {==}
    case Some{ws}:
      Facts.Words.is_eq_refl(ws)

# only equal words are the same
def Words.same_sound(x: Maybe<&2, List<&2, U32>>, y: Maybe<&2, List<&2, U32>>) -> {Words.same(x, y) == True{}: Bool} -> {
  x == y: Maybe<&2, List<&2, U32>>
}:
  Shared.Maybe.is_eq_sound(~List<&2, U32>, ~Facts.Words.is_eq, a => b => Facts.Words.is_eq_sound(a, b), x, y)

# words do not differ from themselves
def Words.same_not(x: Maybe<&2, List<&2, U32>>) -> {Bool.not(Words.same(x, x)) == False{}: Bool}:
  %Equal.sym(Bool, Words.same(x, x), True{}, Words.same_refl(x)): {Bool.not(_) == False{}: Bool}
  {==}

# equal words do not differ
def Words.differ_ne(+x: Maybe<&2, List<&2, U32>>, +y: Maybe<&2, List<&2, U32>>) -> {x == y: Maybe<&2, List<&2, U32>>} -> {
  Bool.not(Words.same(x, y)) == True{}: Bool
} -> Empty:
  e =>
    %e: {Bool.not(Words.same(x, _)) == True{}: Bool} -> Empty
    d => Shared.Bool.false_ne_true(
      Equal.trans(
        Bool,
        False{},
        Bool.not(Words.same(x, x)),
        True{},
        Equal.sym(Bool, Bool.not(Words.same(x, x)), False{}, Words.same_not(x)),
        d
      )
    )

# words that are not equal differ
def Words.ne_differ(+x: Maybe<&2, List<&2, U32>>, +y: Maybe<&2, List<&2, U32>>) -> ({x == y: Maybe<&2, List<&2, U32>>} -> Empty) -> {
  Bool.not(Words.same(x, y)) == True{}: Bool
}:
  ne => Lists.Bool.by(
    k => {Bool.not(k) == True{}: Bool},
    Words.same(x, y),
    e => Empty.absurd({False{} == True{}: Bool}, ne(Words.same_sound(x, y)(e))),
    e => {==}
  )

# a path whose words differ in the contents fa and fb of two versions changed
# from one version to the other
def Changed.of_differ(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +a: Nat,
  +b: Nat,
  +fa: Files.Files(),
  +fb: Files.Files(),
  +p: String,
  ea: {Contents.Content.of(s, c, a) == Some{fa}: Maybe<&2, Files.Files()>},
  eb: {Contents.Content.of(s, c, b) == Some{fb}: Maybe<&2, Files.Files()>},
  d: {Answers.Delta.differ(Answers.Delta{fa, fb}, p) == True{}: Bool}
) -> Mirror.Changed(s, c, a, b, p):
  (
    Files.Files.get(fa, p),
    (
      Files.Files.get(fb, p),
      (
        Content.read_of(s, c, a, fa, p)(ea),
        (
          Content.read_of(s, c, b, fb, p)(eb),
          e => Words.differ_ne(Files.Files.get(fa, p), Files.Files.get(fb, p))(e)(d)
        )
      )
    )
  )

# Changed.differ, once the words x and y that the reads give are known
def Changed.differ.at(
  +fa: Files.Files(),
  +fb: Files.Files(),
  +p: String,
  -x: Maybe<&2, List<&2, U32>>,
  -y: Maybe<&2, List<&2, U32>>,
  ex: {Files.Files.get(fa, p) == x: Maybe<&2, List<&2, U32>>},
  ey: {Files.Files.get(fb, p) == y: Maybe<&2, List<&2, U32>>},
  ne: {x == y: Maybe<&2, List<&2, U32>>} -> Empty
) -> {Answers.Delta.differ(Answers.Delta{fa, fb}, p) == True{}: Bool}:
  Words.ne_differ(Files.Files.get(fa, p), Files.Files.get(fb, p))(
    e => ne(
      Equal.trans(
        Maybe<&2, List<&2, U32>>,
        x,
        Files.Files.get(fa, p),
        y,
        Equal.sym(Maybe<&2, List<&2, U32>>, Files.Files.get(fa, p), x, ex),
        Equal.trans(Maybe<&2, List<&2, U32>>, Files.Files.get(fa, p), Files.Files.get(fb, p), y, e, ey)
      )
    )
  )

# the words of a path that changed from one version to another differ in
# their contents fa and fb
def Changed.differ(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +a: Nat,
  +b: Nat,
  +fa: Files.Files(),
  +fb: Files.Files(),
  +p: String,
  ea: {Contents.Content.of(s, c, a) == Some{fa}: Maybe<&2, Files.Files()>},
  eb: {Contents.Content.of(s, c, b) == Some{fb}: Maybe<&2, Files.Files()>},
  ch: Mirror.Changed(s, c, a, b, p)
) -> {Answers.Delta.differ(Answers.Delta{fa, fb}, p) == True{}: Bool}:
  (+x, w) = ch
  (+y, w2) = w
  (ra, w3) = w2
  (rb, ne) = w3
  Changed.differ.at(
    fa,
    fb,
    p,
    x,
    y,
    Content.read_get(s, c, a, fa, p, x)(ea)(ra),
    Content.read_get(s, c, b, fb, p, y)(eb)(rb),
    ne
  )

# What the reply says
# -------------------

# the names of a reply of names
def Reply.names(r: Spec.Reply) -> List<&2, String>:
  match r:
    case Spec.Reply.Names{ns}:
      ns
    case _:
      []

# what Reach.of answers is Reach.seen, and it is closed
def Reach.of_some(+b: Files.Files(), +bs: List<&2, String>, +us: List<&2, String>, +seen: List<&2, String>) -> {
  Answers.Reach.of(b, bs, us) == Some{seen}: Maybe<&2, List<&2, String>>
} -> {Reach.seen(b, bs, us) == seen: List<&2, String>} & Reach.Closed(b, bs, Reach.seen(b, bs, us)):
  Lists.Bool.by(
    k => {
      Shared.Maybe.when(List<&2, String>, k, u => Some{Reach.seen(b, bs, us)}) == Some{seen}: Maybe<&2, List<&2, String>>
    } -> {Reach.seen(b, bs, us) == seen: List<&2, String>} & {k == True{}: Bool},
    Shared.List.holds(
      ~String,
      ~Answers.Reached,
      ~Answers.Reached.closed,
      Reach.seen(b, bs, us),
      Answers.Reached{b, bs, Reach.seen(b, bs, us)}
    ),
    e => h => (Shared.Maybe.some_inj(List<&2, String>, Reach.seen(b, bs, us), seen, h), {==}),
    e => h => Empty.absurd(
      {Reach.seen(b, bs, us) == seen: List<&2, String>} & {False{} == True{}: Bool},
      Shared.Maybe.none_ne_some(List<&2, String>, seen, h)
    )
  )

# what a reply of the names ps to Affects says, of the contents fa and fb
def Affects.Told(fa: Files.Files(), fb: Files.Files(), us: List<&2, String>, bs: List<&2, String>, ps: List<&2, String>) -> Type:
  Exists(
    List<&2, String>,
    seen => {
      Answers.Reach.of(fb, bs, us) == Some{seen}: Maybe<&2, List<&2, String>>
    }
      & {Answers.Delta.changed(Answers.Delta{fa, fb}, seen) == ps: List<&2, String>}
  )

# a reply of the names ps is the changed ones among the reached paths m
def Affects.at_some(m: Maybe<&2, List<&2, String>>, +fa: Files.Files(), +fb: Files.Files(), +ps: List<&2, String>) -> {
  Answers.Affects.at(fa, fb, m) == Some{Spec.Reply.Names{ps}}: Maybe<&2, Spec.Reply>
} -> Exists(
  List<&2, String>,
  seen => {
    m == Some{seen}: Maybe<&2, List<&2, String>>
  }
    & {Answers.Delta.changed(Answers.Delta{fa, fb}, seen) == ps: List<&2, String>}
):
  match m:
    case None{}:
      h => Empty.absurd(
        Exists(
          List<&2, String>,
          seen => {
            None{} == Some{seen}: Maybe<&2, List<&2, String>>
          }
            & {Answers.Delta.changed(Answers.Delta{fa, fb}, seen) == ps: List<&2, String>}
        ),
        Shared.Maybe.none_ne_some(Spec.Reply, Spec.Reply.Names{ps}, h)
      )
    case Some{+seen}:
      h => (
        seen,
        (
          {==},
          Equal.cong(
            Spec.Reply,
            List<&2, String>,
            r => Reply.names(r),
            Spec.Reply.Names{Answers.Delta.changed(Answers.Delta{fa, fb}, seen)},
            Spec.Reply.Names{ps},
            Shared.Maybe.some_inj(
              Spec.Reply,
              Spec.Reply.Names{Answers.Delta.changed(Answers.Delta{fa, fb}, seen)},
              Spec.Reply.Names{ps},
              h
            )
          )
        )
      )

# what a reply of names to Affects says of the two contents old and new
def Affects.Some(old: Maybe<&2, Files.Files()>, new: Maybe<&2, Files.Files()>, us: List<&2, String>, bs: List<&2, String>, ps: List<&2, String>) -> Type:
  Exists(
    Files.Files(),
    fa => Exists(
      Files.Files(),
      fb => {
        old == Some{fa}: Maybe<&2, Files.Files()>
      }
        & ({new == Some{fb}: Maybe<&2, Files.Files()>} & Affects.Told(fa, fb, us, bs, ps))
    )
  )

# a reply of names to Affects is given of two contents that the node holds
def Affects.of_some(
  old: Maybe<&2, Files.Files()>,
  new: Maybe<&2, Files.Files()>,
  +us: List<&2, String>,
  +bs: List<&2, String>,
  +ps: List<&2, String>
) -> {Answers.Affects.of(old, new, us, bs) == Some{Spec.Reply.Names{ps}}: Maybe<&2, Spec.Reply>} -> Affects.Some(old, new, us, bs, ps):
  match old new:
    case Some{+fa} Some{+fb}:
      h => (fa, (fb, ({==}, ({==}, Affects.at_some(Answers.Reach.of(fb, bs, us), fa, fb, ps)(h)))))
    case Some{fa} None{}:
      h => Empty.absurd(
        Affects.Some(Some{fa}, None{}, us, bs, ps),
        Shared.Maybe.none_ne_some(Spec.Reply, Spec.Reply.Names{ps}, h)
      )
    case None{} Some{fb}:
      h => Empty.absurd(
        Affects.Some(None{}, Some{fb}, us, bs, ps),
        Shared.Maybe.none_ne_some(Spec.Reply, Spec.Reply.Names{ps}, h)
      )
    case None{} None{}:
      h => Empty.absurd(
        Affects.Some(None{}, None{}, us, bs, ps),
        Shared.Maybe.none_ne_some(Spec.Reply, Spec.Reply.Names{ps}, h)
      )

# the names ps of the reply are the changed ones among Reach.seen
def Affects.names(
  +fa: Files.Files(),
  +fb: Files.Files(),
  +us: List<&2, String>,
  +bs: List<&2, String>,
  +ps: List<&2, String>,
  +seen: List<&2, String>,
  es: {Reach.seen(fb, bs, us) == seen: List<&2, String>},
  ep: {Answers.Delta.changed(Answers.Delta{fa, fb}, seen) == ps: List<&2, String>}
) -> {Answers.Delta.changed(Answers.Delta{fa, fb}, Reach.seen(fb, bs, us)) == ps: List<&2, String>}:
  Equal.trans(
    List<&2, String>,
    Answers.Delta.changed(Answers.Delta{fa, fb}, Reach.seen(fb, bs, us)),
    Answers.Delta.changed(Answers.Delta{fa, fb}, seen),
    ps,
    Equal.cong(
      List<&2, String>,
      List<&2, String>,
      z => Answers.Delta.changed(Answers.Delta{fa, fb}, z),
      Reach.seen(fb, bs, us),
      seen,
      es
    ),
    ep
  )

# The two laws
# ------------

# a member of the names ps of the reply is a seen path that differs
def Affects.told_in(
  +fa: Files.Files(),
  +fb: Files.Files(),
  +us: List<&2, String>,
  +bs: List<&2, String>,
  +ps: List<&2, String>,
  +p: String,
  +seen: List<&2, String>,
  er: {Answers.Reach.of(fb, bs, us) == Some{seen}: Maybe<&2, List<&2, String>>},
  ep: {Answers.Delta.changed(Answers.Delta{fa, fb}, seen) == ps: List<&2, String>},
  hin: In(ps, p)
) -> In(Reach.seen(fb, bs, us), p) & {Answers.Delta.differ(Answers.Delta{fa, fb}, p) == True{}: Bool}:
  Delta.changed_in(Reach.seen(fb, bs, us), Answers.Delta{fa, fb}, p)(
    In.cast(
      ps,
      Answers.Delta.changed(Answers.Delta{fa, fb}, Reach.seen(fb, bs, us)),
      p,
      Equal.sym(
        List<&2, String>,
        Answers.Delta.changed(Answers.Delta{fa, fb}, Reach.seen(fb, bs, us)),
        ps,
        Affects.names(
          fa,
          fb,
          us,
          bs,
          ps,
          seen,
          Pair.fst(
            {Reach.seen(fb, bs, us) == seen: List<&2, String>},
            Reach.Closed(fb, bs, Reach.seen(fb, bs, us)),
            Reach.of_some(fb, bs, us, seen)(er)
          ),
          ep
        )
      ),
      hin
    )
  )

# Core.affects_only, once the contents are known and p is known to be seen
# and to differ
def Core.affects_only.at(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +a: Nat,
  +b: Nat,
  +us: List<&2, String>,
  +bs: List<&2, String>,
  +p: String,
  +fa: Files.Files(),
  +fb: Files.Files(),
  ea: {Contents.Content.of(s, c, a) == Some{fa}: Maybe<&2, Files.Files()>},
  +eb: {Contents.Content.of(s, c, b) == Some{fb}: Maybe<&2, Files.Files()>},
  w: In(Reach.seen(fb, bs, us), p) & {Answers.Delta.differ(Answers.Delta{fa, fb}, p) == True{}: Bool}
) -> Mirror.Changed(s, c, a, b, p) & Mirror.Reaches(s, c, b, bs, us, p):
  (hs, d) = w
  (Changed.of_differ(s, c, a, b, fa, fb, p, ea, eb, d), Reach.seen_in(s, c, b, bs, fb, us, p, eb)(hs))

# Core.affects_only, from what the reply says
def Core.affects_only.of(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +a: Nat,
  +b: Nat,
  +us: List<&2, String>,
  +bs: List<&2, String>,
  +ps: List<&2, String>,
  +p: String,
  hin: In(ps, p),
  w: Affects.Some(Contents.Content.of(s, c, a), Contents.Content.of(s, c, b), us, bs, ps)
) -> Mirror.Changed(s, c, a, b, p) & Mirror.Reaches(s, c, b, bs, us, p):
  (+fa, w1) = w
  (+fb, w2) = w1
  (ea, w3) = w2
  (eb, w4) = w3
  (+seen, w5) = w4
  (er, ep) = w5
  Core.affects_only.at(s, c, a, b, us, bs, p, fa, fb, ea, eb, Affects.told_in(fa, fb, us, bs, ps, p, seen, er, ep, hin))

# A writer is told only about changes to what its work uses.
def Core.affects_only(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +a: Nat,
  +b: Nat,
  +us: List<&2, String>,
  +bs: List<&2, String>,
  +ps: List<&2, String>,
  +p: String
) -> {
  Answers.Answer.of(s, Spec.Question.Affects{c, a, b, us, bs}) == Some{Spec.Reply.Names{ps}}: Maybe<&2, Spec.Reply>
} -> {List.contains(~String, ~String.eq, ps, p) == True{}: Bool} -> Mirror.Changed(s, c, a, b, p) & Mirror.Reaches(s, c, b, bs, us, p):
  h => hin => Core.affects_only.of(
    s,
    c,
    a,
    b,
    us,
    bs,
    ps,
    p,
    hin,
    Affects.of_some(Contents.Content.of(s, c, a), Contents.Content.of(s, c, b), us, bs, ps)(h)
  )

# Core.affects_all, once the path u that reaches p and its chain are known
def Core.affects_all.at(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +a: Nat,
  +b: Nat,
  +us: List<&2, String>,
  +bs: List<&2, String>,
  +ps: List<&2, String>,
  +p: String,
  +fa: Files.Files(),
  +fb: Files.Files(),
  +u: String,
  +qs: List<&2, String>,
  +seen: List<&2, String>,
  ea: {Contents.Content.of(s, c, a) == Some{fa}: Maybe<&2, Files.Files()>},
  +eb: {Contents.Content.of(s, c, b) == Some{fb}: Maybe<&2, Files.Files()>},
  +er: {Answers.Reach.of(fb, bs, us) == Some{seen}: Maybe<&2, List<&2, String>>},
  ep: {Answers.Delta.changed(Answers.Delta{fa, fb}, seen) == ps: List<&2, String>},
  ch: Mirror.Changed(s, c, a, b, p),
  hu: In(us, u),
  chain: Mirror.Imports(s, c, b, bs, u, qs, p)
) -> In(ps, p):
  In.cast(
    Answers.Delta.changed(Answers.Delta{fa, fb}, Reach.seen(fb, bs, us)),
    ps,
    p,
    Affects.names(fa, fb, us, bs, ps, seen, Pair.fst(
      {Reach.seen(fb, bs, us) == seen: List<&2, String>},
      Reach.Closed(fb, bs, Reach.seen(fb, bs, us)),
      Reach.of_some(fb, bs, us, seen)(er)
    ), ep),
    Delta.changed_has(Reach.seen(fb, bs, us), Answers.Delta{fa, fb}, p)(
      Reach.chain_in(qs, s, c, b, bs, fb, Reach.seen(fb, bs, us), u, p, eb, Pair.snd(
      {Reach.seen(fb, bs, us) == seen: List<&2, String>},
      Reach.Closed(fb, bs, Reach.seen(fb, bs, us)),
      Reach.of_some(fb, bs, us, seen)(er)
    ))(chain)(
        Reach.go_keeps(
          1n+Nat.add(
            List.length(&2, String, Answers.Reach.add(us, [])),
            List.length(&2, String, Files.Files.paths(fb))
          ),
          fb,
          bs,
          Answers.Reach.add(us, []),
          u
        )(Reach.add_has(us, [], u)(hu))
      )
    )(Changed.differ(s, c, a, b, fa, fb, p, ea, eb, ch))
  )

# Core.affects_all, from what the reply says
def Core.affects_all.of(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +a: Nat,
  +b: Nat,
  +us: List<&2, String>,
  +bs: List<&2, String>,
  +ps: List<&2, String>,
  +p: String,
  w: Affects.Some(Contents.Content.of(s, c, a), Contents.Content.of(s, c, b), us, bs, ps),
  ch: Mirror.Changed(s, c, a, b, p),
  rc: Mirror.Reaches(s, c, b, bs, us, p)
) -> In(ps, p):
  (+fa, w1) = w
  (+fb, w2) = w1
  (ea, w3) = w2
  (eb, w4) = w3
  (+seen, w5) = w4
  (er, ep) = w5
  (+u, r1) = rc
  (hu, r2) = r1
  (+qs, chain) = r2
  Core.affects_all.at(
    s,
    c,
    a,
    b,
    us,
    bs,
    ps,
    p,
    fa,
    fb,
    u,
    qs,
    seen,
    ea,
    eb,
    er,
    ep,
    ch,
    hu,
    chain
  )

# And it is told about each of them.
def Core.affects_all(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +a: Nat,
  +b: Nat,
  +us: List<&2, String>,
  +bs: List<&2, String>,
  +ps: List<&2, String>,
  +p: String
) -> {
  Answers.Answer.of(s, Spec.Question.Affects{c, a, b, us, bs}) == Some{Spec.Reply.Names{ps}}: Maybe<&2, Spec.Reply>
} -> Mirror.Changed(s, c, a, b, p) -> Mirror.Reaches(s, c, b, bs, us, p) -> {List.contains(~String, ~String.eq, ps, p) == True{}: Bool}:
  h => ch => rc => Core.affects_all.of(
    s,
    c,
    a,
    b,
    us,
    bs,
    ps,
    p,
    Affects.of_some(Contents.Content.of(s, c, a), Contents.Content.of(s, c, b), us, bs, ps)(h),
    ch,
    rc
  )
