import Base
import ../../shared.bend as Shared
import ../shared/formats.bend as Formats
import ../shared/replica.bend as Replicas
import ../shared/resources.bend as Resources
import ../shared/shared/reach.bend as Reaches
import ../shared/shared/text.bend as Texts
import ../shared/shared/trie.bend as Tries
import ./spec.bend as Spec

# The pure core of a Vend Node.

# Equality
# --------

# Chain.is_eq is True for a chain and itself
def Chain.is_eq_refl(a: Spec.Chain) -> {Spec.Chain.is_eq(a, a) == True{}: Bool}:
  match a:
    case Spec.Chain.branch{x}:
      Texts.String.eq_refl(x)
    case Spec.Chain.group{x}:
      Texts.String.eq_refl(x)

# Chain.is_eq is True only for equal chains
def Chain.is_eq_sound(
  a: Spec.Chain,
  b: Spec.Chain
) -> {Spec.Chain.is_eq(a, b) == True{}: Bool} -> {a == b: Spec.Chain}:
  match a b:
    case Spec.Chain.branch{x} Spec.Chain.branch{y}:
      h =>
        %Texts.String.eq_sound(x, y)(h): {Spec.Chain.branch{x} == Spec.Chain.branch{_}: Spec.Chain}
        {==}
    case Spec.Chain.group{x} Spec.Chain.group{y}:
      h =>
        %Texts.String.eq_sound(x, y)(h): {Spec.Chain.group{x} == Spec.Chain.group{_}: Spec.Chain}
        {==}
    case Spec.Chain.branch{x} Spec.Chain.group{y}:
      h => Empty.absurd(
        {Spec.Chain.branch{x} == Spec.Chain.group{y}: Spec.Chain},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Chain.group{x} Spec.Chain.branch{y}:
      h => Empty.absurd(
        {Spec.Chain.group{x} == Spec.Chain.branch{y}: Spec.Chain},
        Shared.Bool.false_ne_true(h)
      )

# Member.is_eq is True for a member and itself
def Member.is_eq_refl(a: Spec.Member) -> {Spec.Member.is_eq(a, a) == True{}: Bool}:
  match a:
    case Spec.Member.node{x}:
      Texts.String.eq_refl(x)
    case Spec.Member.group{x}:
      Texts.String.eq_refl(x)

# Member.is_eq is True only for equal members
def Member.is_eq_sound(
  a: Spec.Member,
  b: Spec.Member
) -> {Spec.Member.is_eq(a, b) == True{}: Bool} -> {a == b: Spec.Member}:
  match a b:
    case Spec.Member.node{x} Spec.Member.node{y}:
      h =>
        %Texts.String.eq_sound(x, y)(h): {Spec.Member.node{x} == Spec.Member.node{_}: Spec.Member}
        {==}
    case Spec.Member.group{x} Spec.Member.group{y}:
      h =>
        %Texts.String.eq_sound(x, y)(h): {Spec.Member.group{x} == Spec.Member.group{_}: Spec.Member}
        {==}
    case Spec.Member.node{x} Spec.Member.group{y}:
      h => Empty.absurd(
        {Spec.Member.node{x} == Spec.Member.group{y}: Spec.Member},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Member.group{x} Spec.Member.node{y}:
      h => Empty.absurd(
        {Spec.Member.group{x} == Spec.Member.node{y}: Spec.Member},
        Shared.Bool.false_ne_true(h)
      )

# the laws of Spec.Member.is_eq
def Member.laws() -> Shared.Eq.Laws(Spec.Member, Spec.Member.is_eq):
  (Member.is_eq_refl, Member.is_eq_sound)

# Content.is_eq is True for a content and itself
def Content.is_eq_refl(a: Spec.Content) -> {Spec.Content.is_eq(a, a) == True{}: Bool}:
  match a:
    case Spec.Content.bytes{x}:
      Shared.List.is_eq_refl(~U32, ~U32.is_eq, ~Shared.U32.laws(), x)
    case Spec.Content.of{v}:
      Replicas.Id.is_eq_refl(v)

# Content.is_eq is True only for equal contents
def Content.is_eq_sound(
  a: Spec.Content,
  b: Spec.Content
) -> {Spec.Content.is_eq(a, b) == True{}: Bool} -> {a == b: Spec.Content}:
  match a b:
    case Spec.Content.bytes{x} Spec.Content.bytes{y}:
      h =>
        %Shared.List.is_eq_sound(
          ~U32,
          ~U32.is_eq,
          ~Shared.U32.laws(),
          x,
          y
        )(h): {Spec.Content.bytes{x} == Spec.Content.bytes{_}: Spec.Content}
        {==}
    case Spec.Content.of{x} Spec.Content.of{y}:
      h =>
        %Replicas.Id.is_eq_sound(x, y)(h): {Spec.Content.of{x} == Spec.Content.of{_}: Spec.Content}
        {==}
    case Spec.Content.bytes{x} Spec.Content.of{y}:
      h => Empty.absurd(
        {Spec.Content.bytes{x} == Spec.Content.of{y}: Spec.Content},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Content.of{x} Spec.Content.bytes{y}:
      h => Empty.absurd(
        {Spec.Content.of{x} == Spec.Content.bytes{y}: Spec.Content},
        Shared.Bool.false_ne_true(h)
      )

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- an equality, or a proof, keeps each and/or as one value for the proofs to split on
# Ask.is_eq is True for a change and itself
def Ask.is_eq_refl(a: Spec.Ask) -> {Spec.Ask.is_eq(a, a) == True{}: Bool}:
  match a:
    case Spec.Ask.write{+b, +n, +v, +c}:
      Shared.Bool.and_both(
        String.eq(b, b),
        Bool.and(
          Resources.Name.is_eq(n, n),
          Bool.and(
            Shared.Maybe.is_eq(~Replicas.Id, ~Replicas.Id.is_eq, v, v),
            Spec.Content.is_eq(c, c)
          )
        )
      )(
        Texts.String.eq_refl(b)
      )(
        Shared.Bool.and_both(
          Resources.Name.is_eq(n, n),
          Bool.and(
            Shared.Maybe.is_eq(~Replicas.Id, ~Replicas.Id.is_eq, v, v),
            Spec.Content.is_eq(c, c)
          )
        )(
          Resources.Name.is_eq_refl(n)
        )(
          Shared.Bool.and_both(
            Shared.Maybe.is_eq(~Replicas.Id, ~Replicas.Id.is_eq, v, v),
            Spec.Content.is_eq(c, c)
          )(
            Shared.Maybe.is_eq_refl(~Replicas.Id, ~Replicas.Id.is_eq, ~Replicas.Id.laws(), v)
          )(Content.is_eq_refl(c))
        )
      )
    case Spec.Ask.set_branch{+b, +v}:
      Shared.Bool.and_both(
        String.eq(b, b),
        Replicas.Id.is_eq(v, v)
      )(Texts.String.eq_refl(b))(Replicas.Id.is_eq_refl(v))
    case Spec.Ask.merge{+b, +v}:
      Shared.Bool.and_both(
        String.eq(b, b),
        Replicas.Id.is_eq(v, v)
      )(Texts.String.eq_refl(b))(Replicas.Id.is_eq_refl(v))
    case Spec.Ask.resolve{+b, +k, +n, +c}:
      Shared.Bool.and_both(
        String.eq(b, b),
        Bool.and(
          Replicas.Id.is_eq(k, k),
          Bool.and(Resources.Name.is_eq(n, n), Spec.Content.is_eq(c, c))
        )
      )(
        Texts.String.eq_refl(b)
      )(
        Shared.Bool.and_both(
          Replicas.Id.is_eq(k, k),
          Bool.and(Resources.Name.is_eq(n, n), Spec.Content.is_eq(c, c))
        )(
          Replicas.Id.is_eq_refl(k)
        )(
          Shared.Bool.and_both(
            Resources.Name.is_eq(n, n),
            Spec.Content.is_eq(c, c)
          )(Resources.Name.is_eq_refl(n))(Content.is_eq_refl(c))
        )
      )
    case Spec.Ask.mark{+b, +m, +t}:
      Shared.Bool.and_both(
        String.eq(b, b),
        Bool.and(String.eq(m, m), String.eq(t, t))
      )(
        Texts.String.eq_refl(b)
      )(
        Shared.Bool.and_both(
          String.eq(m, m),
          String.eq(t, t)
        )(Texts.String.eq_refl(m))(Texts.String.eq_refl(t))
      )
    case Spec.Ask.set_owner{+c, +ms}:
      Shared.Bool.and_both(
        Spec.Chain.is_eq(c, c),
        Shared.List.is_eq(~String, ~String.eq, ms, ms)
      )(Chain.is_eq_refl(c))(Shared.List.is_eq_refl(~String, ~String.eq, ~Texts.String.laws(), ms))
    case Spec.Ask.set_group{+g, +ms}:
      Shared.Bool.and_both(
        String.eq(g, g),
        Shared.List.is_eq(~Spec.Member, ~Spec.Member.is_eq, ms, ms)
      )(
        Texts.String.eq_refl(g)
      )(Shared.List.is_eq_refl(~Spec.Member, ~Spec.Member.is_eq, ~Member.laws(), ms))

# Ask.is_eq is True only for equal changes
def Ask.is_eq_sound(
  a: Spec.Ask,
  b: Spec.Ask
) -> {Spec.Ask.is_eq(a, b) == True{}: Bool} -> {a == b: Spec.Ask}:
  match a b:
    case Spec.Ask.write{+b1, +n1, +v1, +c1} Spec.Ask.write{+b2, +n2, +v2, +c2}:
      +h =>
        +r1 = Bool.and(
          Resources.Name.is_eq(n1, n2),
          Bool.and(
            Shared.Maybe.is_eq(~Replicas.Id, ~Replicas.Id.is_eq, v1, v2),
            Spec.Content.is_eq(c1, c2)
          )
        )
        +r2 = Bool.and(
          Shared.Maybe.is_eq(~Replicas.Id, ~Replicas.Id.is_eq, v1, v2),
          Spec.Content.is_eq(c1, c2)
        )
        +h1 = Shared.Bool.and_true_right(String.eq(b1, b2), r1)(h)
        +h2 = Shared.Bool.and_true_right(Resources.Name.is_eq(n1, n2), r2)(h1)
        %Texts.String.eq_sound(b1, b2)(Shared.Bool.and_true_left(String.eq(b1, b2), r1)(h)):
          {Spec.Ask.write{b1, n1, v1, c1} == Spec.Ask.write{_, n2, v2, c2}: Spec.Ask}
        %Resources.Name.is_eq_sound(
          n1,
          n2
        )(Shared.Bool.and_true_left(Resources.Name.is_eq(n1, n2), r2)(h1)):
          {Spec.Ask.write{b1, n1, v1, c1} == Spec.Ask.write{b1, _, v2, c2}: Spec.Ask}
        %Shared.Maybe.is_eq_sound(
          ~Replicas.Id,
          ~Replicas.Id.is_eq,
          Replicas.Id.is_eq_sound,
          v1,
          v2
        )(
          Shared.Bool.and_true_left(
            Shared.Maybe.is_eq(~Replicas.Id, ~Replicas.Id.is_eq, v1, v2),
            Spec.Content.is_eq(c1, c2)
          )(h2)
        ):
          {Spec.Ask.write{b1, n1, v1, c1} == Spec.Ask.write{b1, n1, _, c2}: Spec.Ask}
        %Content.is_eq_sound(
          c1,
          c2
        )(
          Shared.Bool.and_true_right(
            Shared.Maybe.is_eq(~Replicas.Id, ~Replicas.Id.is_eq, v1, v2),
            Spec.Content.is_eq(c1, c2)
          )(h2)
        ):
          {Spec.Ask.write{b1, n1, v1, c1} == Spec.Ask.write{b1, n1, v1, _}: Spec.Ask}
        {==}
    case Spec.Ask.set_branch{+b1, +v1} Spec.Ask.set_branch{+b2, +v2}:
      +h =>
        %Texts.String.eq_sound(
          b1,
          b2
        )(Shared.Bool.and_true_left(String.eq(b1, b2), Replicas.Id.is_eq(v1, v2))(h)):
          {Spec.Ask.set_branch{b1, v1} == Spec.Ask.set_branch{_, v2}: Spec.Ask}
        %Replicas.Id.is_eq_sound(
          v1,
          v2
        )(Shared.Bool.and_true_right(String.eq(b1, b2), Replicas.Id.is_eq(v1, v2))(h)):
          {Spec.Ask.set_branch{b1, v1} == Spec.Ask.set_branch{b1, _}: Spec.Ask}
        {==}
    case Spec.Ask.merge{+b1, +v1} Spec.Ask.merge{+b2, +v2}:
      +h =>
        %Texts.String.eq_sound(
          b1,
          b2
        )(Shared.Bool.and_true_left(String.eq(b1, b2), Replicas.Id.is_eq(v1, v2))(h)):
          {Spec.Ask.merge{b1, v1} == Spec.Ask.merge{_, v2}: Spec.Ask}
        %Replicas.Id.is_eq_sound(
          v1,
          v2
        )(Shared.Bool.and_true_right(String.eq(b1, b2), Replicas.Id.is_eq(v1, v2))(h)):
          {Spec.Ask.merge{b1, v1} == Spec.Ask.merge{b1, _}: Spec.Ask}
        {==}
    case Spec.Ask.resolve{+b1, +k1, +n1, +c1} Spec.Ask.resolve{+b2, +k2, +n2, +c2}:
      +h =>
        +r1 = Bool.and(
          Replicas.Id.is_eq(k1, k2),
          Bool.and(Resources.Name.is_eq(n1, n2), Spec.Content.is_eq(c1, c2))
        )
        +r2 = Bool.and(Resources.Name.is_eq(n1, n2), Spec.Content.is_eq(c1, c2))
        +h1 = Shared.Bool.and_true_right(String.eq(b1, b2), r1)(h)
        +h2 = Shared.Bool.and_true_right(Replicas.Id.is_eq(k1, k2), r2)(h1)
        %Texts.String.eq_sound(b1, b2)(Shared.Bool.and_true_left(String.eq(b1, b2), r1)(h)):
          {Spec.Ask.resolve{b1, k1, n1, c1} == Spec.Ask.resolve{_, k2, n2, c2}: Spec.Ask}
        %Replicas.Id.is_eq_sound(
          k1,
          k2
        )(Shared.Bool.and_true_left(Replicas.Id.is_eq(k1, k2), r2)(h1)):
          {Spec.Ask.resolve{b1, k1, n1, c1} == Spec.Ask.resolve{b1, _, n2, c2}: Spec.Ask}
        %Resources.Name.is_eq_sound(
          n1,
          n2
        )(Shared.Bool.and_true_left(Resources.Name.is_eq(n1, n2), Spec.Content.is_eq(c1, c2))(h2)):
          {Spec.Ask.resolve{b1, k1, n1, c1} == Spec.Ask.resolve{b1, k1, _, c2}: Spec.Ask}
        %Content.is_eq_sound(
          c1,
          c2
        )(Shared.Bool.and_true_right(Resources.Name.is_eq(n1, n2), Spec.Content.is_eq(c1, c2))(h2)):
          {Spec.Ask.resolve{b1, k1, n1, c1} == Spec.Ask.resolve{b1, k1, n1, _}: Spec.Ask}
        {==}
    case Spec.Ask.mark{+b1, +m1, +t1} Spec.Ask.mark{+b2, +m2, +t2}:
      +h =>
        +r1 = Bool.and(String.eq(m1, m2), String.eq(t1, t2))
        +h1 = Shared.Bool.and_true_right(String.eq(b1, b2), r1)(h)
        %Texts.String.eq_sound(b1, b2)(Shared.Bool.and_true_left(String.eq(b1, b2), r1)(h)):
          {Spec.Ask.mark{b1, m1, t1} == Spec.Ask.mark{_, m2, t2}: Spec.Ask}
        %Texts.String.eq_sound(
          m1,
          m2
        )(Shared.Bool.and_true_left(String.eq(m1, m2), String.eq(t1, t2))(h1)):
          {Spec.Ask.mark{b1, m1, t1} == Spec.Ask.mark{b1, _, t2}: Spec.Ask}
        %Texts.String.eq_sound(
          t1,
          t2
        )(Shared.Bool.and_true_right(String.eq(m1, m2), String.eq(t1, t2))(h1)):
          {Spec.Ask.mark{b1, m1, t1} == Spec.Ask.mark{b1, m1, _}: Spec.Ask}
        {==}
    case Spec.Ask.set_owner{+c1, +ms1} Spec.Ask.set_owner{+c2, +ms2}:
      +h =>
        %Chain.is_eq_sound(
          c1,
          c2
        )(
          Shared.Bool.and_true_left(
            Spec.Chain.is_eq(c1, c2),
            Shared.List.is_eq(~String, ~String.eq, ms1, ms2)
          )(h)
        ):
          {Spec.Ask.set_owner{c1, ms1} == Spec.Ask.set_owner{_, ms2}: Spec.Ask}
        %Shared.List.is_eq_sound(
          ~String,
          ~String.eq,
          ~Texts.String.laws(),
          ms1,
          ms2
        )(
          Shared.Bool.and_true_right(
            Spec.Chain.is_eq(c1, c2),
            Shared.List.is_eq(~String, ~String.eq, ms1, ms2)
          )(h)
        ):
          {Spec.Ask.set_owner{c1, ms1} == Spec.Ask.set_owner{c1, _}: Spec.Ask}
        {==}
    case Spec.Ask.set_group{+g1, +ms1} Spec.Ask.set_group{+g2, +ms2}:
      +h =>
        %Texts.String.eq_sound(
          g1,
          g2
        )(
          Shared.Bool.and_true_left(
            String.eq(g1, g2),
            Shared.List.is_eq(~Spec.Member, ~Spec.Member.is_eq, ms1, ms2)
          )(h)
        ):
          {Spec.Ask.set_group{g1, ms1} == Spec.Ask.set_group{_, ms2}: Spec.Ask}
        %Shared.List.is_eq_sound(
          ~Spec.Member,
          ~Spec.Member.is_eq,
          ~Member.laws(),
          ms1,
          ms2
        )(
          Shared.Bool.and_true_right(
            String.eq(g1, g2),
            Shared.List.is_eq(~Spec.Member, ~Spec.Member.is_eq, ms1, ms2)
          )(h)
        ):
          {Spec.Ask.set_group{g1, ms1} == Spec.Ask.set_group{g1, _}: Spec.Ask}
        {==}
    case Spec.Ask.write{p0, p1, p2, p3} Spec.Ask.set_branch{q0, q1}:
      h => Empty.absurd(
        {Spec.Ask.write{p0, p1, p2, p3} == Spec.Ask.set_branch{q0, q1}: Spec.Ask},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Ask.write{p0, p1, p2, p3} Spec.Ask.merge{q0, q1}:
      h => Empty.absurd(
        {Spec.Ask.write{p0, p1, p2, p3} == Spec.Ask.merge{q0, q1}: Spec.Ask},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Ask.write{p0, p1, p2, p3} Spec.Ask.resolve{q0, q1, q2, q3}:
      h => Empty.absurd(
        {Spec.Ask.write{p0, p1, p2, p3} == Spec.Ask.resolve{q0, q1, q2, q3}: Spec.Ask},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Ask.write{p0, p1, p2, p3} Spec.Ask.mark{q0, q1, q2}:
      h => Empty.absurd(
        {Spec.Ask.write{p0, p1, p2, p3} == Spec.Ask.mark{q0, q1, q2}: Spec.Ask},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Ask.write{p0, p1, p2, p3} Spec.Ask.set_owner{q0, q1}:
      h => Empty.absurd(
        {Spec.Ask.write{p0, p1, p2, p3} == Spec.Ask.set_owner{q0, q1}: Spec.Ask},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Ask.write{p0, p1, p2, p3} Spec.Ask.set_group{q0, q1}:
      h => Empty.absurd(
        {Spec.Ask.write{p0, p1, p2, p3} == Spec.Ask.set_group{q0, q1}: Spec.Ask},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Ask.set_branch{p0, p1} Spec.Ask.write{q0, q1, q2, q3}:
      h => Empty.absurd(
        {Spec.Ask.set_branch{p0, p1} == Spec.Ask.write{q0, q1, q2, q3}: Spec.Ask},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Ask.set_branch{p0, p1} Spec.Ask.merge{q0, q1}:
      h => Empty.absurd(
        {Spec.Ask.set_branch{p0, p1} == Spec.Ask.merge{q0, q1}: Spec.Ask},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Ask.set_branch{p0, p1} Spec.Ask.resolve{q0, q1, q2, q3}:
      h => Empty.absurd(
        {Spec.Ask.set_branch{p0, p1} == Spec.Ask.resolve{q0, q1, q2, q3}: Spec.Ask},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Ask.set_branch{p0, p1} Spec.Ask.mark{q0, q1, q2}:
      h => Empty.absurd(
        {Spec.Ask.set_branch{p0, p1} == Spec.Ask.mark{q0, q1, q2}: Spec.Ask},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Ask.set_branch{p0, p1} Spec.Ask.set_owner{q0, q1}:
      h => Empty.absurd(
        {Spec.Ask.set_branch{p0, p1} == Spec.Ask.set_owner{q0, q1}: Spec.Ask},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Ask.set_branch{p0, p1} Spec.Ask.set_group{q0, q1}:
      h => Empty.absurd(
        {Spec.Ask.set_branch{p0, p1} == Spec.Ask.set_group{q0, q1}: Spec.Ask},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Ask.merge{p0, p1} Spec.Ask.write{q0, q1, q2, q3}:
      h => Empty.absurd(
        {Spec.Ask.merge{p0, p1} == Spec.Ask.write{q0, q1, q2, q3}: Spec.Ask},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Ask.merge{p0, p1} Spec.Ask.set_branch{q0, q1}:
      h => Empty.absurd(
        {Spec.Ask.merge{p0, p1} == Spec.Ask.set_branch{q0, q1}: Spec.Ask},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Ask.merge{p0, p1} Spec.Ask.resolve{q0, q1, q2, q3}:
      h => Empty.absurd(
        {Spec.Ask.merge{p0, p1} == Spec.Ask.resolve{q0, q1, q2, q3}: Spec.Ask},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Ask.merge{p0, p1} Spec.Ask.mark{q0, q1, q2}:
      h => Empty.absurd(
        {Spec.Ask.merge{p0, p1} == Spec.Ask.mark{q0, q1, q2}: Spec.Ask},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Ask.merge{p0, p1} Spec.Ask.set_owner{q0, q1}:
      h => Empty.absurd(
        {Spec.Ask.merge{p0, p1} == Spec.Ask.set_owner{q0, q1}: Spec.Ask},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Ask.merge{p0, p1} Spec.Ask.set_group{q0, q1}:
      h => Empty.absurd(
        {Spec.Ask.merge{p0, p1} == Spec.Ask.set_group{q0, q1}: Spec.Ask},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Ask.resolve{p0, p1, p2, p3} Spec.Ask.write{q0, q1, q2, q3}:
      h => Empty.absurd(
        {Spec.Ask.resolve{p0, p1, p2, p3} == Spec.Ask.write{q0, q1, q2, q3}: Spec.Ask},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Ask.resolve{p0, p1, p2, p3} Spec.Ask.set_branch{q0, q1}:
      h => Empty.absurd(
        {Spec.Ask.resolve{p0, p1, p2, p3} == Spec.Ask.set_branch{q0, q1}: Spec.Ask},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Ask.resolve{p0, p1, p2, p3} Spec.Ask.merge{q0, q1}:
      h => Empty.absurd(
        {Spec.Ask.resolve{p0, p1, p2, p3} == Spec.Ask.merge{q0, q1}: Spec.Ask},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Ask.resolve{p0, p1, p2, p3} Spec.Ask.mark{q0, q1, q2}:
      h => Empty.absurd(
        {Spec.Ask.resolve{p0, p1, p2, p3} == Spec.Ask.mark{q0, q1, q2}: Spec.Ask},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Ask.resolve{p0, p1, p2, p3} Spec.Ask.set_owner{q0, q1}:
      h => Empty.absurd(
        {Spec.Ask.resolve{p0, p1, p2, p3} == Spec.Ask.set_owner{q0, q1}: Spec.Ask},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Ask.resolve{p0, p1, p2, p3} Spec.Ask.set_group{q0, q1}:
      h => Empty.absurd(
        {Spec.Ask.resolve{p0, p1, p2, p3} == Spec.Ask.set_group{q0, q1}: Spec.Ask},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Ask.mark{p0, p1, p2} Spec.Ask.write{q0, q1, q2, q3}:
      h => Empty.absurd(
        {Spec.Ask.mark{p0, p1, p2} == Spec.Ask.write{q0, q1, q2, q3}: Spec.Ask},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Ask.mark{p0, p1, p2} Spec.Ask.set_branch{q0, q1}:
      h => Empty.absurd(
        {Spec.Ask.mark{p0, p1, p2} == Spec.Ask.set_branch{q0, q1}: Spec.Ask},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Ask.mark{p0, p1, p2} Spec.Ask.merge{q0, q1}:
      h => Empty.absurd(
        {Spec.Ask.mark{p0, p1, p2} == Spec.Ask.merge{q0, q1}: Spec.Ask},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Ask.mark{p0, p1, p2} Spec.Ask.resolve{q0, q1, q2, q3}:
      h => Empty.absurd(
        {Spec.Ask.mark{p0, p1, p2} == Spec.Ask.resolve{q0, q1, q2, q3}: Spec.Ask},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Ask.mark{p0, p1, p2} Spec.Ask.set_owner{q0, q1}:
      h => Empty.absurd(
        {Spec.Ask.mark{p0, p1, p2} == Spec.Ask.set_owner{q0, q1}: Spec.Ask},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Ask.mark{p0, p1, p2} Spec.Ask.set_group{q0, q1}:
      h => Empty.absurd(
        {Spec.Ask.mark{p0, p1, p2} == Spec.Ask.set_group{q0, q1}: Spec.Ask},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Ask.set_owner{p0, p1} Spec.Ask.write{q0, q1, q2, q3}:
      h => Empty.absurd(
        {Spec.Ask.set_owner{p0, p1} == Spec.Ask.write{q0, q1, q2, q3}: Spec.Ask},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Ask.set_owner{p0, p1} Spec.Ask.set_branch{q0, q1}:
      h => Empty.absurd(
        {Spec.Ask.set_owner{p0, p1} == Spec.Ask.set_branch{q0, q1}: Spec.Ask},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Ask.set_owner{p0, p1} Spec.Ask.merge{q0, q1}:
      h => Empty.absurd(
        {Spec.Ask.set_owner{p0, p1} == Spec.Ask.merge{q0, q1}: Spec.Ask},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Ask.set_owner{p0, p1} Spec.Ask.resolve{q0, q1, q2, q3}:
      h => Empty.absurd(
        {Spec.Ask.set_owner{p0, p1} == Spec.Ask.resolve{q0, q1, q2, q3}: Spec.Ask},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Ask.set_owner{p0, p1} Spec.Ask.mark{q0, q1, q2}:
      h => Empty.absurd(
        {Spec.Ask.set_owner{p0, p1} == Spec.Ask.mark{q0, q1, q2}: Spec.Ask},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Ask.set_owner{p0, p1} Spec.Ask.set_group{q0, q1}:
      h => Empty.absurd(
        {Spec.Ask.set_owner{p0, p1} == Spec.Ask.set_group{q0, q1}: Spec.Ask},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Ask.set_group{p0, p1} Spec.Ask.write{q0, q1, q2, q3}:
      h => Empty.absurd(
        {Spec.Ask.set_group{p0, p1} == Spec.Ask.write{q0, q1, q2, q3}: Spec.Ask},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Ask.set_group{p0, p1} Spec.Ask.set_branch{q0, q1}:
      h => Empty.absurd(
        {Spec.Ask.set_group{p0, p1} == Spec.Ask.set_branch{q0, q1}: Spec.Ask},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Ask.set_group{p0, p1} Spec.Ask.merge{q0, q1}:
      h => Empty.absurd(
        {Spec.Ask.set_group{p0, p1} == Spec.Ask.merge{q0, q1}: Spec.Ask},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Ask.set_group{p0, p1} Spec.Ask.resolve{q0, q1, q2, q3}:
      h => Empty.absurd(
        {Spec.Ask.set_group{p0, p1} == Spec.Ask.resolve{q0, q1, q2, q3}: Spec.Ask},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Ask.set_group{p0, p1} Spec.Ask.mark{q0, q1, q2}:
      h => Empty.absurd(
        {Spec.Ask.set_group{p0, p1} == Spec.Ask.mark{q0, q1, q2}: Spec.Ask},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Ask.set_group{p0, p1} Spec.Ask.set_owner{q0, q1}:
      h => Empty.absurd(
        {Spec.Ask.set_group{p0, p1} == Spec.Ask.set_owner{q0, q1}: Spec.Ask},
        Shared.Bool.false_ne_true(h)
      )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the laws of Spec.Ask.is_eq, for the replica
def Ask.laws() -> Shared.Eq.Laws(Spec.Ask, Spec.Ask.is_eq):
  (Ask.is_eq_refl, Ask.is_eq_sound)

# Versions
# --------

# the requests among the cells cs
def Entry.ids(cs: List<&2, Replicas.Cell<Replicas.Entry<Spec.Ask>>>) -> List<&2, Replicas.Id>:
  match cs:
    case Nil{}:
      []
    case Con{Replicas.one{Replicas.Entry.ask{i, t, q}}, r}:
      i <> Entry.ids(r)
    case Con{c, r}:
      Entry.ids(r)

# every request that s holds
def State.versions(s: Spec.State()) -> List<&2, Replicas.Id>:
  Entry.ids(Tries.Trie.values(Replicas.Cell<Replicas.Entry<Spec.Ask>>, s))

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- the rest is one walk of the list; it costs the same with or without the pick
# the version before v in xs, after prev; none when v is first or not there
def List.before(
  xs: List<&2, Replicas.Id>,
  prev: Maybe<&2, Replicas.Id>,
  +v: Replicas.Id
) -> Maybe<&2, Replicas.Id>:
  match xs:
    case Nil{}:
      None{}
    case Con{+x, r}:
      Bool.pick(Maybe<&2, Replicas.Id>, Replicas.Id.is_eq(x, v), prev, List.before(r, Some{x}, v))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the version before v on its chain c
def Chain.before(s: Spec.State(), c: Spec.Chain, v: Replicas.Id) -> Maybe<&2, Replicas.Id>:
  List.before(Spec.Node.chain(s, c), None{}, v)

# the versions that the change q of v names besides the one before it
def Ask.refs(q: Spec.Ask) -> List<&2, Replicas.Id>:
  match q:
    case Spec.Ask.set_branch{b, to}:
      [to]
    case Spec.Ask.merge{b, from}:
      [from]
    case _:
      []

# the versions that v came from, when s holds its request r
def Version.parents.of(
  s: Spec.State(),
  v: Replicas.Id,
  r: Maybe<&2, Replicas.Asked<Spec.Ask>>
) -> List<&2, Replicas.Id>:
  match r:
    case None{}:
      []
    case Some{Replicas.Asked{t, +q}}:
      List.append(
        &2,
        Replicas.Id,
        Maybe.default(
          &2,
          List<&2, Replicas.Id>,
          Maybe.map(
            &2,
            Replicas.Id,
            List<&2, Replicas.Id>,
            x => [x],
            Chain.before(s, Spec.Ask.chain(q), v)
          ),
          []
        ),
        Ask.refs(q)
      )

# the versions that v came from
def Version.parents(s: Spec.State(), v: Replicas.Id) -> List<&2, Replicas.Id>:
  +s = s
  +v = v
  Version.parents.of(s, v, Replicas.State.asked(~Spec.Ask, s, v))

# x is v (held), or a version that v came from
def Version.is_from.if(held: Bool, s: Spec.State(), x: Replicas.Id, v: Replicas.Id) -> Bool:
  match held:
    case True{}:
      True{}
    case False{}:
      Reaches.Reach.in(
        ~Replicas.Id,
        ~Spec.State(),
        ~Replicas.Id.is_eq,
        ~Version.parents,
        ~State.versions,
        s,
        v,
        x
      )

# x is v, or a version that v came from
def Version.is_from(s: Spec.State(), +x: Replicas.Id, +v: Replicas.Id) -> Bool:
  Version.is_from.if(Replicas.Id.is_eq(x, v), s, x, v)

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- the rest is one walk of the list; it costs the same with or without the pick
# the first version of xs that v came from
def Version.base.go(
  +s: Spec.State(),
  xs: List<&2, Replicas.Id>,
  +v: Replicas.Id
) -> Maybe<&2, Replicas.Id>:
  match xs:
    case Nil{}:
      None{}
    case Con{+x, r}:
      Bool.pick(Maybe<&2, Replicas.Id>, Version.is_from(s, x, v), Some{x}, Version.base.go(s, r, v))

# the versions of xs up to v
def List.upto(xs: List<&2, Replicas.Id>, +v: Replicas.Id) -> List<&2, Replicas.Id>:
  match xs:
    case Nil{}:
      []
    case Con{+x, r}:
      x <> Bool.pick(List<&2, Replicas.Id>, Replicas.Id.is_eq(x, v), [], List.upto(r, v))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the base of a merge of from into the chain c, whose head was ours: the newest
# version of c up to ours that from came from
def Version.base(
  +s: Spec.State(),
  c: Spec.Chain,
  ours: Maybe<&2, Replicas.Id>,
  from: Replicas.Id
) -> Maybe<&2, Replicas.Id>:
  match ours:
    case None{}:
      None{}
    case Some{o}:
      Version.base.go(s, List.reverse(&2, Replicas.Id, List.upto(Spec.Node.chain(s, c), o)), from)

# the newer of x and y, once y is known to come from x or not (held)
def Forward.if(
  held: Bool,
  s: Spec.State(),
  +x: Replicas.Id,
  y: Replicas.Id
) -> Maybe<&2, Replicas.Id>:
  match held:
    case True{}:
      Some{y}
    case False{}:
      Shared.Bool.when(Maybe<&2, Replicas.Id>, Version.is_from(s, y, x), u => Some{x}, u => None{})

def Spec.Node.forward(s, x, y):
  +s = s
  +x = x
  +y = y
  Forward.if(Version.is_from(s, x, y), s, x, y)

# Content
# -------
# The bytes of a resource at a version, found one resource at a time: a write
# or a resolve of it holds them, a set-branch takes them from its target, a
# merge merges its base, the version before it and the one merged in, and
# every other change keeps the version before it.

# the request r names the resource n
def Asked.hits(r: Maybe<&2, Replicas.Asked<Spec.Ask>>, n: Resources.Name) -> Bool:
  match r:
    case Some{Replicas.Asked{t, Spec.Ask.write{b, m, base, c}}}:
      Resources.Name.is_eq(m, n)
    case Some{Replicas.Asked{t, Spec.Ask.resolve{b, k, m, c}}}:
      Resources.Name.is_eq(m, n)
    case _:
      False{}

# the request of v, when there is one
def State.asked.of(
  s: Spec.State(),
  v: Maybe<&2, Replicas.Id>
) -> Maybe<&2, Replicas.Asked<Spec.Ask>>:
  match v:
    case None{}:
      None{}
    case Some{i}:
      Replicas.State.asked(~Spec.Ask, s, i)

# what a merge keeps of a resource: its bytes or none, or a clash
type Pick is Data:
  Pick.take{bytes: Maybe<&2, Texts.Bytes()>}
  Pick.clash{}

# the merge of a resource's bytes, when all three hold it
def Pick.bytes(m: Formats.Merged) -> Pick:
  match m:
    case Formats.Merged.clean{x}:
      Pick.take{Some{x}}
    case Formats.Merged.clash{}:
      Pick.clash{}

# the merge of the submodules px and py: the one at the newer version m, if
# there is one
def Pick.module(m: Maybe<&2, Replicas.Id>, px: Spec.Pointer, +py: Spec.Pointer) -> Pick:
  match m:
    case None{}:
      Pick.clash{}
    case Some{k}:
      Pick.take{
        Some{
          Spec.Pointer.show(
            Shared.Bool.when(
              Spec.Pointer,
              Replicas.Id.is_eq(k, Spec.Pointer.version(py)),
              u => py,
              u => px
            )
          )
        }
      }

# the merge of two submodules that point as x and y
def Pick.pointers(s: Spec.State(), x: Maybe<&2, Spec.Pointer>, y: Maybe<&2, Spec.Pointer>) -> Pick:
  match x y:
    case Some{+px} Some{+py}:
      Pick.module(Spec.Node.forward(s, Spec.Pointer.version(px), Spec.Pointer.version(py)), px, py)
    case _ _:
      Pick.clash{}

# the merge of x and y, two changes of b, in the format f
def Pick.format(
  f: Formats.Format,
  s: Spec.State(),
  b: Texts.Bytes(),
  x: Texts.Bytes(),
  y: Texts.Bytes()
) -> Pick:
  match f:
    case Formats.Format.leaf{Formats.Leaf.module{}}:
      Pick.pointers(s, Spec.Pointer.read(x), Spec.Pointer.read(y))
    case g:
      Pick.bytes(Formats.Format.merge(g, b, x, y))

# the merge of a resource that the base, ours and theirs hold or not, when
# both sides changed it, in the format f
def Pick.both(
  f: Formats.Format,
  s: Spec.State(),
  b: Maybe<&2, Texts.Bytes()>,
  o: Maybe<&2, Texts.Bytes()>,
  t: Maybe<&2, Texts.Bytes()>
) -> Pick:
  match o t:
    case Some{x} Some{y}:
      Pick.format(f, s, Maybe.default(&2, Texts.Bytes(), b, []), x, y)
    case _ _:
      Pick.clash{}

# the merge of a resource, once both sides are known to agree or not (held)
def Pick.of.same(
  held: Bool,
  f: Formats.Format,
  s: Spec.State(),
  b: Maybe<&2, Texts.Bytes()>,
  o: Maybe<&2, Texts.Bytes()>,
  t: Maybe<&2, Texts.Bytes()>
) -> Pick:
  match held:
    case True{}:
      Pick.take{o}
    case False{}:
      Pick.both(f, s, b, o, t)

# the merge of a resource, once theirs is known to be the base or not (held)
def Pick.of.right(
  held: Bool,
  f: Formats.Format,
  s: Spec.State(),
  b: Maybe<&2, Texts.Bytes()>,
  +o: Maybe<&2, Texts.Bytes()>,
  +t: Maybe<&2, Texts.Bytes()>
) -> Pick:
  match held:
    case True{}:
      Pick.take{o}
    case False{}:
      Pick.of.same(
        Shared.Maybe.is_eq(~Texts.Bytes(), ~Shared.List.is_eq(~U32, ~U32.is_eq), o, t),
        f,
        s,
        b,
        o,
        t
      )

# the merge of a resource, once ours is known to be the base or not (held)
def Pick.of(
  held: Bool,
  f: Formats.Format,
  s: Spec.State(),
  +b: Maybe<&2, Texts.Bytes()>,
  o: Maybe<&2, Texts.Bytes()>,
  +t: Maybe<&2, Texts.Bytes()>
) -> Pick:
  match held:
    case True{}:
      Pick.take{t}
    case False{}:
      Pick.of.right(
        Shared.Maybe.is_eq(~Texts.Bytes(), ~Shared.List.is_eq(~U32, ~U32.is_eq), t, b),
        f,
        s,
        b,
        o,
        t
      )

# what a merge of the base b, ours o and theirs t keeps of a resource in the
# format f
def Pick.merge(
  f: Formats.Format,
  s: Spec.State(),
  +b: Maybe<&2, Texts.Bytes()>,
  +o: Maybe<&2, Texts.Bytes()>,
  t: Maybe<&2, Texts.Bytes()>
) -> Pick:
  Pick.of(
    Shared.Maybe.is_eq(~Texts.Bytes(), ~Shared.List.is_eq(~U32, ~U32.is_eq), o, b),
    f,
    s,
    b,
    o,
    t
  )

# the bytes of a merge: ours on a clash
def Pick.kept(p: Pick, o: Maybe<&2, Texts.Bytes()>) -> Maybe<&2, Texts.Bytes()>:
  match p:
    case Pick.take{x}:
      x
    case Pick.clash{}:
      o

# the bytes of the resource n at the version v, whose request is r and names n
# or not (hit); f steps at most
def Res.at(
  +f: Nat,
  +s: Spec.State(),
  v: Maybe<&2, Replicas.Id>,
  +n: Resources.Name,
  r: Maybe<&2, Replicas.Asked<Spec.Ask>>,
  hit: Bool
) -> Maybe<&2, Texts.Bytes()>:
  match f v r hit:
    case 0n w m h:
      None{}
    case 1n+e None{} m h:
      None{}
    case 1n+e Some{i} None{} h:
      None{}
    case 1n+e Some{
      i
    } Some{Replicas.Asked{t, Spec.Ask.write{b, m, base, Spec.Content.bytes{x}}}} True{}:
      Some{x}
    case 1n+e Some{
      i
    } Some{Replicas.Asked{t, Spec.Ask.write{b, m, base, Spec.Content.of{+w}}}} True{}:
      Res.at(
        e,
        s,
        Some{w},
        n,
        Replicas.State.asked(~Spec.Ask, s, w),
        Asked.hits(Replicas.State.asked(~Spec.Ask, s, w), n)
      )
    case 1n+e Some{
      i
    } Some{Replicas.Asked{t, Spec.Ask.resolve{b, k, m, Spec.Content.bytes{x}}}} True{}:
      Some{x}
    case 1n+e Some{
      i
    } Some{Replicas.Asked{t, Spec.Ask.resolve{b, k, m, Spec.Content.of{+w}}}} True{}:
      Res.at(
        e,
        s,
        Some{w},
        n,
        Replicas.State.asked(~Spec.Ask, s, w),
        Asked.hits(Replicas.State.asked(~Spec.Ask, s, w), n)
      )
    case 1n+e Some{i} Some{Replicas.Asked{t, Spec.Ask.set_branch{b, +to}}} h:
      Res.at(
        e,
        s,
        Some{to},
        n,
        Replicas.State.asked(~Spec.Ask, s, to),
        Asked.hits(Replicas.State.asked(~Spec.Ask, s, to), n)
      )
    case 1n+e Some{+i} Some{Replicas.Asked{t, Spec.Ask.merge{+b, +from}}} h:
      +ours = Chain.before(s, Spec.Chain.branch{b}, i)
      +base = Version.base(s, Spec.Chain.branch{b}, ours, from)
      +o = Res.at(e, s, ours, n, State.asked.of(s, ours), Asked.hits(State.asked.of(s, ours), n))
      bs fs = Res.at(
        e,
        s,
        base,
        n,
        State.asked.of(s, base),
        Asked.hits(State.asked.of(s, base), n)
      ) Res.at(
        e,
        s,
        Some{from},
        n,
        Replicas.State.asked(~Spec.Ask, s, from),
        Asked.hits(Replicas.State.asked(~Spec.Ask, s, from), n)
      )
      Pick.kept(Pick.merge(Formats.Format.of(Resources.Name.path(n)), s, bs, o, fs), o)
    case 1n+e Some{+i} Some{Replicas.Asked{t, +q}} h:
      +before = Chain.before(s, Spec.Ask.chain(q), i)
      Res.at(e, s, before, n, State.asked.of(s, before), Asked.hits(State.asked.of(s, before), n))

# the bytes of the resource n at the version v of s
def Res.of(
  +s: Spec.State(),
  +n: Resources.Name,
  +v: Maybe<&2, Replicas.Id>
) -> Maybe<&2, Texts.Bytes()>:
  Res.at(
    Replicas.State.fuel(~Spec.Ask, s),
    s,
    v,
    n,
    State.asked.of(s, v),
    Asked.hits(State.asked.of(s, v), n)
  )

# the request r names the mark m
def Mark.is_named(r: Maybe<&2, Replicas.Asked<Spec.Ask>>, m: String) -> Bool:
  match r:
    case Some{Replicas.Asked{t, Spec.Ask.mark{b, k, x}}}:
      String.eq(k, m)
    case _:
      False{}

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- the rest is one walk of the list; it costs the same with or without the pick
# the version that the first mark m of xs names: the one before it, after prev
def Mark.first(
  +s: Spec.State(),
  xs: List<&2, Replicas.Id>,
  prev: Maybe<&2, Replicas.Id>,
  +m: String
) -> Maybe<&2, Replicas.Id>:
  match xs:
    case Nil{}:
      None{}
    case Con{+x, r}:
      Bool.pick(
        Maybe<&2, Replicas.Id>,
        Mark.is_named(Replicas.State.asked(~Spec.Ask, s, x), m),
        prev,
        Mark.first(s, r, Some{x}, m)
      )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the version that the mark m of the branch b names
def Mark.of(+s: Spec.State(), b: String, m: String) -> Maybe<&2, Replicas.Id>:
  Mark.first(s, Spec.Node.chain(s, Spec.Chain.branch{b}), None{}, m)

# the version at the point p of s
def Point.version(s: Spec.State(), p: Spec.Point) -> Maybe<&2, Replicas.Id>:
  match p:
    case Spec.Point.at{v}:
      Some{v}
    case Spec.Point.head{b}:
      Spec.Node.head(s, b)
    case Spec.Point.mark{b, m}:
      Mark.of(s, b, m)

def Spec.Node.content(s, n, p):
  +s = s
  Res.of(s, n, Point.version(s, p))

def Spec.Node.content_at(s, n, base):
  Res.of(s, n, base)

# Names
# -----

# the texts of the resources at the version v, whose request is r; f steps at
# most
def Res.names(
  +f: Nat,
  +s: Spec.State(),
  v: Maybe<&2, Replicas.Id>,
  r: Maybe<&2, Replicas.Asked<Spec.Ask>>
) -> List<&2, String>:
  match f v r:
    case 0n w m:
      []
    case 1n+e None{} m:
      []
    case 1n+e Some{i} None{}:
      []
    case 1n+e Some{i} Some{Replicas.Asked{t, Spec.Ask.set_branch{b, +to}}}:
      Res.names(e, s, Some{to}, Replicas.State.asked(~Spec.Ask, s, to))
    case 1n+e Some{+i} Some{Replicas.Asked{t, Spec.Ask.merge{b, +from}}}:
      +ours = Chain.before(s, Spec.Chain.branch{b}, i)
      fs os = Res.names(
        e,
        s,
        Some{from},
        Replicas.State.asked(~Spec.Ask, s, from)
      ) Res.names(e, s, ours, State.asked.of(s, ours))
      Shared.List.union(~String, ~String.eq, fs, os)
    case 1n+e Some{+i} Some{Replicas.Asked{t, Spec.Ask.write{b, m, base, c}}}:
      +before = Chain.before(s, Spec.Chain.branch{b}, i)
      Shared.List.union(
        ~String,
        ~String.eq,
        [Resources.Name.show(m)],
        Res.names(e, s, before, State.asked.of(s, before))
      )
    case 1n+e Some{+i} Some{Replicas.Asked{t, +q}}:
      +before = Chain.before(s, Spec.Ask.chain(q), i)
      Res.names(e, s, before, State.asked.of(s, before))

# p is a clash
def Pick.is_clash(p: Pick) -> Bool:
  match p:
    case Pick.take{x}:
      False{}
    case Pick.clash{}:
      True{}

# the resources of the names ns that clash when from merges into ours over base
def Res.clashes(
  +s: Spec.State(),
  ns: List<&2, String>,
  +base: Maybe<&2, Replicas.Id>,
  +ours: Maybe<&2, Replicas.Id>,
  +from: Replicas.Id
) -> List<&2, Resources.Name>:
  match ns:
    case Nil{}:
      []
    case Con{t, r}:
      +n = {Resources.Name{t}: Resources.Name}
      List.filter.put(
        Resources.Name,
        n,
        Res.clashes(s, r, base, ours, from),
        Pick.is_clash(
          Pick.merge(
            Formats.Format.of(Resources.Name.path(n)),
            s,
            Res.of(s, n, base),
            Res.of(s, n, ours),
            Res.of(s, n, Some{from})
          )
        )
      )

# Conflicts
# ---------

# the texts of the resources at the version v of s
def Res.of.names(+s: Spec.State(), +v: Maybe<&2, Replicas.Id>) -> List<&2, String>:
  Res.names(Replicas.State.fuel(~Spec.Ask, s), s, v, State.asked.of(s, v))

# the resources that clash at the merge k, whose request is r
def Merge.clashes(
  +s: Spec.State(),
  k: Replicas.Id,
  r: Maybe<&2, Replicas.Asked<Spec.Ask>>
) -> List<&2, Resources.Name>:
  match r:
    case Some{Replicas.Asked{t, Spec.Ask.merge{+b, +from}}}:
      +ours = Chain.before(s, Spec.Chain.branch{b}, k)
      Res.clashes(
        s,
        Shared.List.union(~String, ~String.eq, Res.of.names(s, Some{from}), Res.of.names(s, ours)),
        Version.base(s, Spec.Chain.branch{b}, ours, from),
        ours,
        from
      )
    case _:
      []

# the text that the request r settles of k
def Merge.settles(r: Maybe<&2, Replicas.Asked<Spec.Ask>>, k: Replicas.Id) -> List<&2, String>:
  match r:
    case Some{Replicas.Asked{t, Spec.Ask.resolve{b, j, n, c}}}:
      List.filter.put(String, Resources.Name.show(n), [], Replicas.Id.is_eq(j, k))
    case _:
      []

# the texts that the resolves of k among xs settle
def Merge.settled(+s: Spec.State(), xs: List<&2, Replicas.Id>, +k: Replicas.Id) -> List<&2, String>:
  match xs:
    case Nil{}:
      []
    case Con{x, r}:
      List.append(
        &2,
        String,
        Merge.settles(Replicas.State.asked(~Spec.Ask, s, x), k),
        Merge.settled(s, r, k)
      )

# the names of ns whose texts ts does not hold
def Names.unsettled(
  ns: List<&2, Resources.Name>,
  +ts: List<&2, String>
) -> List<&2, Resources.Name>:
  match ns:
    case Nil{}:
      []
    case Con{+n, r}:
      List.filter.put(
        Resources.Name,
        n,
        Names.unsettled(r, ts),
        Bool.not(List.contains(~String, ~String.eq, ts, Resources.Name.show(n)))
      )

# the resources that still clash after the merge k, whose request is r
def Merge.left(
  +s: Spec.State(),
  +k: Replicas.Id,
  +r: Maybe<&2, Replicas.Asked<Spec.Ask>>
) -> List<&2, Resources.Name>:
  match r:
    case Some{Replicas.Asked{t, Spec.Ask.merge{+b, from}}}:
      Names.unsettled(
        Merge.clashes(s, k, r),
        Merge.settled(s, Spec.Node.chain(s, Spec.Chain.branch{b}), k)
      )
    case _:
      []

def Spec.Node.conflict(s, k):
  +s = s
  +k = k
  Merge.left(s, k, Replicas.State.asked(~Spec.Ask, s, k))

# Groups
# ------

# the chain of the first request of a root, when s holds it (m): a chain
# whose root names a request of another chain does not exist
def Root.chain(m: Maybe<&2, Replicas.Asked<Spec.Ask>>) -> Maybe<&2, Spec.Chain>:
  match m:
    case Some{Replicas.Asked{t, q}}:
      Some{Spec.Ask.chain(q)}
    case None{}:
      None{}

# the members that the request r sets, else found
def Group.set(
  r: Maybe<&2, Replicas.Asked<Spec.Ask>>,
  found: Maybe<&2, List<&2, Spec.Member>>
) -> Maybe<&2, List<&2, Spec.Member>>:
  match r:
    case Some{Replicas.Asked{t, Spec.Ask.set_group{g, ms}}}:
      Some{ms}
    case _:
      found

# the members that the last set-group of xs sets, else found
def Group.last(
  +s: Spec.State(),
  xs: List<&2, Replicas.Id>,
  found: Maybe<&2, List<&2, Spec.Member>>
) -> Maybe<&2, List<&2, Spec.Member>>:
  match xs:
    case Nil{}:
      found
    case Con{x, r}:
      Group.last(s, r, Group.set(Replicas.State.asked(~Spec.Ask, s, x), found))

def Spec.Node.members(s, g):
  +s = s
  Group.last(s, Spec.Node.chain(s, Spec.Chain.group{g}), None{})

# the members of m, when it is a group
def Group.succ(s: Spec.State(), m: Spec.Member) -> List<&2, Spec.Member>:
  match m:
    case Spec.Member.node{n}:
      []
    case Spec.Member.group{g}:
      Maybe.default(&2, List<&2, Spec.Member>, Spec.Node.members(s, g), [])

# the group of the chain m, as a member, then rest
def Group.put(m: Maybe<&2, Spec.Chain>, +rest: List<&2, Spec.Member>) -> List<&2, Spec.Member>:
  match m:
    case Some{Spec.Chain.group{+g}}:
      List.filter.put(
        Spec.Member,
        Spec.Member.group{g},
        rest,
        Bool.not(List.contains(~Spec.Member, ~Spec.Member.is_eq, rest, Spec.Member.group{g}))
      )
    case _:
      rest

# the groups whose roots are among the cells cs of s, as members
def Group.roots(
  +s: Spec.State(),
  cs: List<&2, Replicas.Cell<Replicas.Entry<Spec.Ask>>>
) -> List<&2, Spec.Member>:
  match cs:
    case Nil{}:
      []
    case Con{Replicas.one{Replicas.Entry.root{k, i, n}}, r}:
      Group.put(Root.chain(Replicas.State.asked(~Spec.Ask, s, i)), Group.roots(s, r))
    case Con{c, r}:
      Group.roots(s, r)

# every group of s, as a member
def Group.all(s: Spec.State()) -> List<&2, Spec.Member>:
  +s = s
  Group.roots(s, Tries.Trie.values(Replicas.Cell<Replicas.Entry<Spec.Ask>>, s))

def Spec.Node.is_inside(s, m, g):
  Reaches.Reach.in(
    ~Spec.Member,
    ~Spec.State(),
    ~Spec.Member.is_eq,
    ~Group.succ,
    ~Group.all,
    s,
    Spec.Member.group{g},
    m
  )

# the nodes among the members ms
def Group.nodes.of(ms: List<&2, Spec.Member>) -> List<&2, String>:
  match ms:
    case Nil{}:
      []
    case Con{Spec.Member.node{n}, r}:
      n <> Group.nodes.of(r)
    case Con{Spec.Member.group{g}, r}:
      Group.nodes.of(r)

# the nodes that some group of gs names
def Group.named(+s: Spec.State(), gs: List<&2, Spec.Member>) -> List<&2, String>:
  match gs:
    case Nil{}:
      []
    case Con{g, r}:
      Shared.List.union(~String, ~String.eq, Group.nodes.of(Group.succ(s, g)), Group.named(s, r))

# the nodes of ns that are inside the group g
def Group.inside(+s: Spec.State(), ns: List<&2, String>, +g: String) -> List<&2, String>:
  match ns:
    case Nil{}:
      []
    case Con{+n, r}:
      List.filter.put(
        String,
        n,
        Group.inside(s, r, g),
        Spec.Node.is_inside(s, Spec.Member.node{n}, g)
      )

def Spec.Node.nodes(s, g):
  +s = s
  Group.inside(s, Group.named(s, Group.all(s)), g)

# the member m of a new set of the group g makes g contain itself
def Group.loops(s: Spec.State(), +g: String, m: Spec.Member) -> Bool:
  match m:
    case Spec.Member.node{n}:
      False{}
    case Spec.Member.group{+h}:
      List.any.if(u => Spec.Node.is_inside(s, Spec.Member.group{g}, h), String.eq(h, g))

# some member of ms makes the group g contain itself
def Group.loops.any(+s: Spec.State(), +g: String, ms: List<&2, Spec.Member>) -> Bool:
  match ms:
    case Nil{}:
      False{}
    case Con{m, r}:
      List.any.if(u => Group.loops.any(s, g, r), Group.loops(s, g, m))

# Status
# ------

# the change q fits the head h of its chain: the owners may vote for it there
def Spec.Node.fits(s, q, h):
  match q:
    case Spec.Ask.write{b, +n, base, c}:
      +s = s
      Shared.Maybe.is_eq(
        ~Texts.Bytes(),
        ~Shared.List.is_eq(~U32, ~U32.is_eq),
        Res.of(s, n, Some{h}),
        Res.of(s, n, base)
      )
    case Spec.Ask.set_branch{b, to}:
      Maybe.is_some(&2, Replicas.Asked<Spec.Ask>, Replicas.State.asked(~Spec.Ask, s, to))
    case Spec.Ask.merge{b, from}:
      Maybe.is_some(&2, Replicas.Asked<Spec.Ask>, Replicas.State.asked(~Spec.Ask, s, from))
    case Spec.Ask.resolve{b, k, n, c}:
      List.contains(~Resources.Name, ~Resources.Name.is_eq, Spec.Node.conflict(s, k), n)
    case Spec.Ask.mark{b, m, t}:
      Maybe.is_none(&2, Replicas.Id, Mark.of(s, b, m))
    case Spec.Ask.set_owner{c, ms}:
      Bool.not(List.is_empty(&2, String, ms))
    case Spec.Ask.set_group{g, ms}:
      Bool.not(Group.loops.any(s, g, ms))

# Written, or Conflicted when the merge k still clashes (left)
def Done.of.if(left: List<&2, Resources.Name>, i: Replicas.Id, k: Replicas.Id) -> Spec.Done:
  match left:
    case Nil{}:
      Spec.Done.written{i}
    case Con{n, r}:
      Spec.Done.conflicted{k}

# the answer to the request i in its chain, whose change is q
def Done.of(s: Spec.State(), +i: Replicas.Id, q: Spec.Ask) -> Spec.Done:
  match q:
    case Spec.Ask.merge{b, from}:
      Done.of.if(Spec.Node.conflict(s, i), i, i)
    case Spec.Ask.resolve{b, +k, n, c}:
      Done.of.if(Spec.Node.conflict(s, k), i, k)
    case _:
      Spec.Done.written{i}

# the answer to the request i, whose status is st
def Done.status(
  s: Spec.State(),
  i: Replicas.Id,
  st: Replicas.Status<Spec.Ask>
) -> Replicas.Status<Spec.Done>:
  match st:
    case Replicas.Status.done{q}:
      Replicas.Status.done{Done.of(s, i, q)}
    case Replicas.Status.pending{}:
      Replicas.Status.pending{}
    case Replicas.Status.stale{h}:
      Replicas.Status.stale{h}
    case Replicas.Status.refused{w}:
      Replicas.Status.refused{w}
    case Replicas.Status.not_seen{}:
      Replicas.Status.not_seen{}

def Spec.Node.answer(s, i):
  +s = s
  +i = i
  Done.status(s, i, Replicas.State.status(~Spec.Ask, ~Spec.Ask.view, ~Spec.Node.fits, s, i))

# Changes
# -------
def Spec.Node.ask(n, s, e, q):
  +e = e
  Replicas.State.ask(
    ~Spec.Ask,
    ~Spec.Ask.is_eq,
    ~Spec.Ask.view,
    ~Spec.Node.fits,
    n,
    s,
    Spec.Envelope.of(e),
    Spec.Envelope.time(e),
    q
  )

def Spec.Node.vote(n, s):
  Replicas.State.vote(~Spec.Ask, ~Spec.Ask.is_eq, ~Spec.Ask.view, ~Spec.Node.fits, n, s)

def Spec.Node.ask_exactly(n, s, e, q):
  {==}

def Spec.Node.vote_exactly(n, s):
  {==}

def Spec.Node.fits_write(s, b, name, base, x, h):
  {==}

# Listings
# --------

# the branch b, at its last step m, then rest
def Branches.at(
  b: String,
  m: Maybe<&2, Replicas.Step>,
  rest: List<&2, Spec.BranchEntry>
) -> List<&2, Spec.BranchEntry>:
  match m:
    case None{}:
      rest
    case Some{Replicas.Step{h, ms}}:
      Spec.BranchEntry{b, ms, h} <> rest

# the name of the branch m, then rest
def Branches.put(m: Maybe<&2, Spec.Chain>, rest: List<&2, String>) -> List<&2, String>:
  match m:
    case Some{Spec.Chain.branch{b}}:
      Shared.List.union(~String, ~String.eq, [b], rest)
    case _:
      rest

# the names of the branches that some cell of cs of s claims
def Branches.named(
  +s: Spec.State(),
  cs: List<&2, Replicas.Cell<Replicas.Entry<Spec.Ask>>>
) -> List<&2, String>:
  match cs:
    case Nil{}:
      []
    case Con{Replicas.one{Replicas.Entry.root{k, i, n}}, r}:
      Branches.put(Root.chain(Replicas.State.asked(~Spec.Ask, s, i)), Branches.named(s, r))
    case Con{c, r}:
      Branches.named(s, r)

# the branches of the names bs
def Branches.of(+s: Spec.State(), bs: List<&2, String>) -> List<&2, Spec.BranchEntry>:
  match bs:
    case Nil{}:
      []
    case Con{+b, r}:
      Branches.at(
        b,
        Replicas.Chain.cursor(~Spec.Ask, ~Spec.Ask.view, s, Spec.Chain.key(Spec.Chain.branch{b})),
        Branches.of(s, r)
      )

def Spec.Node.branches(s):
  +s = s
  Branches.of(s, Branches.named(s, Tries.Trie.values(Replicas.Cell<Replicas.Entry<Spec.Ask>>, s)))

# the version x, when it changed the resource (held), then rest
def Log.at(
  held: Bool,
  x: Replicas.Id,
  r: Maybe<&2, Replicas.Asked<Spec.Ask>>,
  rest: List<&2, Spec.LogEntry>
) -> List<&2, Spec.LogEntry>:
  match held r:
    case True{} Some{Replicas.Asked{t, q}}:
      Spec.LogEntry{x, t} <> rest
    case h m:
      rest

# the versions of xs, after prev, that changed the resource n
def Log.of(
  +s: Spec.State(),
  +n: Resources.Name,
  xs: List<&2, Replicas.Id>,
  prev: Maybe<&2, Replicas.Id>
) -> List<&2, Spec.LogEntry>:
  match xs:
    case Nil{}:
      []
    case Con{+x, r}:
      Log.at(
        Bool.not(
          Shared.Maybe.is_eq(
            ~Texts.Bytes(),
            ~Shared.List.is_eq(~U32, ~U32.is_eq),
            Res.of(s, n, Some{x}),
            Res.of(s, n, prev)
          )
        ),
        x,
        Replicas.State.asked(~Spec.Ask, s, x),
        Log.of(s, n, r, Some{x})
      )

def Spec.Node.log(s, n, b):
  +s = s
  Log.of(s, n, Spec.Node.chain(s, Spec.Chain.branch{b}), None{})

def Spec.Node.diff(s, n, a, b):
  +s = s
  +n = n
  Formats.Format.changes(
    Formats.Format.of(Resources.Name.path(n)),
    Maybe.default(&2, Texts.Bytes(), Spec.Node.content(s, n, a), []),
    Maybe.default(&2, Texts.Bytes(), Spec.Node.content(s, n, b), [])
  )

# Uses
# ----
# A Uses is the graph Spec.Uses, with the head of its branch found once, not
# at each import.

# the resources of the texts ts
def Names.of(ts: List<&2, String>) -> List<&2, Resources.Name>:
  match ts:
    case Nil{}:
      []
    case Con{t, r}:
      Resources.Name{t} <> Names.of(r)

def Spec.Node.resources(s, b):
  +s = s
  Names.of(Res.of.names(s, Spec.Node.head(s, b)))

# a branch of s at its head, with its resources
type Uses is Data:
  Uses{state: Spec.State(), head: Maybe<&2, Replicas.Id>, names: List<&2, Resources.Name>}

# the graph g, with the head of its branch
def Uses.at(g: Spec.Uses) -> Uses:
  match g:
    case Spec.Uses{+s, b, ns}:
      Uses{s, Spec.Node.head(s, b), ns}

# the resources of the branch of g
def Uses.nodes(g: Uses) -> List<&2, Resources.Name>:
  match g:
    case Uses{s, h, ns}:
      ns

# the bytes m, as a list of one item or none
def Uses.items(m: Maybe<&2, Texts.Bytes()>) -> List<&2, Texts.Bytes()>:
  match m:
    case None{}:
      []
    case Some{b}:
      [b]

# the resources that the edges es of the resource n name
def Uses.named(es: List<&2, Formats.Edge>, +n: Resources.Name) -> List<&2, Resources.Name>:
  match es:
    case Nil{}:
      []
    case Con{Formats.Edge{t, a, cs}, r}:
      Resources.Name.at(n, Texts.Bytes.to_text(t)) <> Uses.named(r, n)

# what the resource n imports at the version h of s
def Uses.targets(
  s: Spec.State(),
  h: Maybe<&2, Replicas.Id>,
  +n: Resources.Name
) -> List<&2, Resources.Name>:
  Uses.named(
    Formats.Format.uses(Formats.Format.of(Resources.Name.path(n)), Uses.items(Res.of(s, n, h))),
    n
  )

# what n imports in g, when it is a resource of g
def Uses.succ(g: Uses, n: Resources.Name) -> List<&2, Resources.Name>:
  match g:
    case Uses{s, h, ns}:
      +n = n
      Shared.Bool.when(
        List<&2, Resources.Name>,
        List.contains(~Resources.Name, ~Resources.Name.is_eq, ns, n),
        u => Uses.targets(s, h, n),
        u => []
      )

def Spec.Node.imports(s, b, u):
  +s = s
  Uses.targets(s, Spec.Node.head(s, b), u)

def Spec.Node.uses(s, b, u, c):
  +s = s
  +b = b
  Reaches.Reach.in(
    ~Resources.Name,
    ~Uses,
    ~Resources.Name.is_eq,
    ~Uses.succ,
    ~Uses.nodes,
    Uses.at(Spec.Uses{s, b, Spec.Node.resources(s, b)}),
    u,
    c
  )

# Touches
# -------

# the resource that the request r wrote: of a write or a resolve
def Wrote.of(r: Maybe<&2, Replicas.Asked<Spec.Ask>>) -> Maybe<&2, Resources.Name>:
  match r:
    case Some{Replicas.Asked{t, Spec.Ask.write{b, m, base, c}}}:
      Some{m}
    case Some{Replicas.Asked{t, Spec.Ask.resolve{b, k, m, c}}}:
      Some{m}
    case _:
      None{}

def Spec.Node.wrote(s, v):
  Wrote.of(Replicas.State.asked(~Spec.Ask, s, v))

def Spec.Node.has(s, v, x):
  Version.is_from(s, x, v)

def Spec.Node.version(s, p):
  Point.version(s, p)

# the versions of every branch of s
def Touch.versions(+s: Spec.State()) -> List<&2, Replicas.Id>:
  Shared.List.flat(
    ~String,
    ~Replicas.Id,
    ~Spec.State(),
    ~(t => x => Spec.Node.chain(t, Spec.Chain.branch{x})),
    Spec.Branch.names(Spec.Node.branches(s)),
    s
  )

# the branch b is a branch of s
def Touch.named(s: Spec.State(), b: String) -> Bool:
  List.contains(~String, ~String.eq, Spec.Branch.names(Spec.Node.branches(s)), b)

# v is a version of a branch of s
def Touch.made(s: Spec.State(), v: Replicas.Id) -> Bool:
  List.contains(~Replicas.Id, ~Replicas.Id.is_eq, Touch.versions(s), v)

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- it runs only after Touch.named holds, so the head is there and both sides are needed
# the branch b lacks the version v
def Touch.lacks(+s: Spec.State(), +b: String, +v: Replicas.Id) -> Bool:
  Bool.and(
    Maybe.is_some(&2, Replicas.Id, Spec.Node.head(s, b)),
    Bool.not(Spec.Node.has(s, Maybe.default(&2, Replicas.Id, Spec.Node.head(s, b), v), v))
  )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the version v wrote the resource c
def Touch.wrote(s: Spec.State(), v: Replicas.Id, c: Resources.Name) -> Bool:
  Shared.Maybe.is_eq(~Resources.Name, ~Resources.Name.is_eq, Spec.Node.wrote(s, v), Some{c})

# u is a resource of the branch b
def Touch.held(s: Spec.State(), b: String, u: Resources.Name) -> Bool:
  List.contains(~Resources.Name, ~Resources.Name.is_eq, Spec.Node.resources(s, b), u)

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- the law's own form, for the proofs; Spec.Node.touches runs the lazy one
# the resource u of the branch b is c, or uses it
def Touch.reaches(s: Spec.State(), b: String, +u: Resources.Name, +c: Resources.Name) -> Bool:
  Bool.or(Resources.Name.is_eq(u, c), Spec.Node.uses(s, b, u, c))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# each part of a touch, from the cheapest; a part runs only when the ones
# before it hold
def Spec.Node.touches(s, t):
  match t:
    case Spec.Touch{+v, +c, +b, +u}:
      +s = s
      List.all.if(
        w => List.all.if(
          w => List.all.if(
            w => List.all.if(
              w => List.all.if(
                w => List.any.if(w => Spec.Node.uses(s, b, u, c), Resources.Name.is_eq(u, c)),
                Touch.held(s, b, u)
              ),
              Touch.wrote(s, v, c)
            ),
            Touch.lacks(s, b, v)
          ),
          Touch.made(s, v)
        ),
        Touch.named(s, b)
      )

# the touches of the version v that wrote c, on the branch b, one for each of
# its resources us
def Touch.each(
  us: List<&2, Resources.Name>,
  +v: Replicas.Id,
  +c: Resources.Name,
  +b: String
) -> List<&2, Spec.Touch>:
  match us:
    case Nil{}:
      []
    case Con{u, r}:
      Spec.Touch{v, c, b, u} <> Touch.each(r, v, c, b)

# the touches of the version v that wrote the resource m (if any), on the
# branch b, one for each of its resources us
def Touch.of(
  m: Maybe<&2, Resources.Name>,
  v: Replicas.Id,
  b: String,
  us: List<&2, Resources.Name>
) -> List<&2, Spec.Touch>:
  match m:
    case None{}:
      []
    case Some{c}:
      Touch.each(us, v, c, b)

# a branch of s, with its resources
type Affects is Data:
  Affects{state: Spec.State(), branch: String, resources: List<&2, Resources.Name>}

# the branch b of s, with its resources
def Affects.of(+s: Spec.State(), +b: String) -> Affects:
  Affects{s, b, Spec.Node.resources(s, b)}

# the touches of the version v on the branch of g
def Affects.at(g: Affects, v: Replicas.Id) -> List<&2, Spec.Touch>:
  match g:
    case Affects{s, b, us}:
      +v = v
      Touch.of(Spec.Node.wrote(s, v), v, b, us)

# the touch t is of the branch of g, and holds
def Affects.keeps(g: Affects, t: Spec.Touch) -> Bool:
  match g:
    case Affects{s, b, us}:
      +t = t
      List.all.if(w => Spec.Node.touches(s, t), String.eq(Spec.Touch.branch(t), b))

# the touches that may hold of the branch b
def Affects.cands(s: Spec.State(), b: String) -> List<&2, Spec.Touch>:
  +s = s
  b = b
  Shared.List.flat(
    ~Replicas.Id,
    ~Spec.Touch,
    ~Affects,
    ~Affects.at,
    Touch.versions(s),
    Affects.of(s, b)
  )

def Spec.Node.affects(s, b):
  +s = s
  +b = b
  Shared.List.keep(~Spec.Touch, ~Affects, ~Affects.keeps, Affects.cands(s, b), Affects.of(s, b))

# the version of a point of s
type Impact is Data:
  Impact{state: Spec.State(), version: Maybe<&2, Replicas.Id>}

# the touch t is of the version of g, or a version that it came from, and
# holds
def Impact.keeps(g: Impact, t: Spec.Touch) -> Bool:
  match g:
    case Impact{+s, +m}:
      +t = t
      List.all.if(
        w => Spec.Node.touches(s, t),
        List.all.if(
          w => Spec.Node.has(
            s,
            Maybe.default(&2, Replicas.Id, m, Spec.Touch.version(t)),
            Spec.Touch.version(t)
          ),
          Maybe.is_some(&2, Replicas.Id, m)
        )
      )

# the touches that may hold of any branch of s
def Impact.cands(+s: Spec.State()) -> List<&2, Spec.Touch>:
  Shared.List.flat(
    ~String,
    ~Spec.Touch,
    ~Spec.State(),
    ~Affects.cands,
    Spec.Branch.names(Spec.Node.branches(s)),
    s
  )

def Spec.Node.impact(s, p):
  +s = s
  Shared.List.keep(
    ~Spec.Touch,
    ~Impact,
    ~Impact.keeps,
    Impact.cands(s),
    Impact{s, Spec.Node.version(s, p)}
  )

# Notices
# -------

# a and b are the same notice
def Notice.is_eq(a: Spec.Notice, b: Spec.Notice) -> Bool:
  match a b:
    case Spec.Notice.versioned{b1, v1} Spec.Notice.versioned{b2, v2}:
      Bool.and(String.eq(b1, b2), Replicas.Id.is_eq(v1, v2))
    case Spec.Notice.conflicted{b1, v1} Spec.Notice.conflicted{b2, v2}:
      Bool.and(String.eq(b1, b2), Replicas.Id.is_eq(v1, v2))
    case Spec.Notice.touched{t1} Spec.Notice.touched{t2}:
      Spec.Touch.is_eq(t1, t2)
    case Spec.Notice.group_cycle{g1} Spec.Notice.group_cycle{g2}:
      String.eq(g1, g2)
    case _ _:
      False{}

# the versions of the branch b among xs, as notices
def Notice.versions(+b: String, xs: List<&2, Replicas.Id>) -> List<&2, Spec.Notice>:
  match xs:
    case Nil{}:
      []
    case Con{x, r}:
      Spec.Notice.versioned{b, x} <> Notice.versions(b, r)

# the merges of the branch b among xs that clashed, as notices
def Notice.conflicts(
  +s: Spec.State(),
  +b: String,
  xs: List<&2, Replicas.Id>
) -> List<&2, Spec.Notice>:
  match xs:
    case Nil{}:
      []
    case Con{+x, r}:
      List.filter.put(
        Spec.Notice,
        Spec.Notice.conflicted{b, x},
        Notice.conflicts(s, b, r),
        Bool.not(
          List.is_empty(
            &2,
            Resources.Name,
            Merge.clashes(s, x, Replicas.State.asked(~Spec.Ask, s, x))
          )
        )
      )

# the touches ts, as notices
def Notice.touches(ts: List<&2, Spec.Touch>) -> List<&2, Spec.Notice>:
  match ts:
    case Nil{}:
      []
    case Con{t, r}:
      Spec.Notice.touched{t} <> Notice.touches(r)

# the groups of gs inside themselves, as notices
def Notice.cycles(+s: Spec.State(), gs: List<&2, Spec.Member>) -> List<&2, Spec.Notice>:
  match gs:
    case Nil{}:
      []
    case Con{Spec.Member.group{+g}, r}:
      List.filter.put(
        Spec.Notice,
        Spec.Notice.group_cycle{g},
        Notice.cycles(s, r),
        Spec.Node.is_inside(s, Spec.Member.group{g}, g)
      )
    case Con{m, r}:
      Notice.cycles(s, r)

# the notices of the topic t in s
def Notice.all(+s: Spec.State(), t: Spec.Topic) -> List<&2, Spec.Notice>:
  match t:
    case Spec.Topic.versions{+b}:
      Notice.versions(b, Spec.Node.chain(s, Spec.Chain.branch{b}))
    case Spec.Topic.conflicts{+b}:
      Notice.conflicts(s, b, Spec.Node.chain(s, Spec.Chain.branch{b}))
    case Spec.Topic.affects{b}:
      Notice.touches(Spec.Node.affects(s, b))
    case Spec.Topic.groups{}:
      Notice.cycles(s, Group.all(s))

# the notices of ns that old does not hold
def Notice.new(ns: List<&2, Spec.Notice>, +old: List<&2, Spec.Notice>) -> List<&2, Spec.Notice>:
  match ns:
    case Nil{}:
      []
    case Con{+n, r}:
      List.filter.put(
        Spec.Notice,
        n,
        Notice.new(r, old),
        Bool.not(List.contains(~Spec.Notice, ~Notice.is_eq, old, n))
      )

def Spec.Node.notices(s, t, since):
  +t = t
  Notice.new(Notice.all(s, t), Notice.all(since, t))

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# the sole owner's vote at its head v puts the request i in the chain: it is
# Written, and its version holds the bytes x
def Written.at(
  +n: String,
  +s1: Spec.State(),
  +i: Replicas.Id,
  +t: String,
  +b: String,
  +name: Resources.Name,
  base: Maybe<&2, Replicas.Id>,
  x: Texts.Bytes(),
  +v: Replicas.Id,
  ecur1: {
    Replicas.Chain.cursor(
      ~Spec.Ask,
      ~Spec.Ask.view,
      s1,
      Spec.Chain.key(Spec.Chain.branch{b})
    )
      == Some{Replicas.Step{v, [n]}}: Maybe<&2, Replicas.Step>
  },
  +f4: {
    Tries.Trie.get(
      Replicas.Cell<Replicas.Entry<Spec.Ask>>,
      s1,
      Replicas.Slot.key(Replicas.Slot.vote{n, Spec.Chain.key(Spec.Chain.branch{b}), v})
    )
      == None{}: Maybe<&2, Replicas.Cell<Replicas.Entry<Spec.Ask>>>
  },
  cell1a: {
    Tries.Trie.get(
      Replicas.Cell<Replicas.Entry<Spec.Ask>>,
      s1,
      Replicas.Slot.key(Replicas.Slot.ask{i})
    )
      == Some{
        Replicas.one{Replicas.Entry.ask{i, t, Spec.Ask.write{b, name, base, Spec.Content.bytes{x}}}}
      }: Maybe<&2, Replicas.Cell<Replicas.Entry<Spec.Ask>>>
  }
) -> {
  Spec.Node.answer(
    Spec.Node.join(
      s1,
      Tries.Trie.one(
        Replicas.Cell<Replicas.Entry<Spec.Ask>>,
        Replicas.Slot.key(Replicas.Slot.vote{n, Spec.Chain.key(Spec.Chain.branch{b}), v}),
        Replicas.one{Replicas.Entry.vote{i}}
      )
    ),
    i
  )
    == Replicas.Status.done{Spec.Done.written{i}}: Replicas.Status<Spec.Done>
}
  & {
    Spec.Node.content(
      Spec.Node.join(
        s1,
        Tries.Trie.one(
          Replicas.Cell<Replicas.Entry<Spec.Ask>>,
          Replicas.Slot.key(Replicas.Slot.vote{n, Spec.Chain.key(Spec.Chain.branch{b}), v}),
          Replicas.one{Replicas.Entry.vote{i}}
        )
      ),
      name,
      Spec.Point.at{i}
    )
      == Some{x}: Maybe<&2, Texts.Bytes()>
  }:
  +c = {Spec.Chain.branch{b}: Spec.Chain}
  +q = {Spec.Ask.write{b, name, base, Spec.Content.bytes{x}}: Spec.Ask}
  l = {Replicas.Step{v, [n]}: Replicas.Step}
  ka = Replicas.Slot.key(Replicas.Slot.ask{i})
  +kv = Replicas.Slot.key(Replicas.Slot.vote{n, Spec.Chain.key(c), v})
  ea = {Replicas.one{Replicas.Entry.ask{i, t, q}}: Replicas.Cell<Replicas.Entry<Spec.Ask>>}
  +ev = {Replicas.one{Replicas.Entry.vote{i}}: Replicas.Cell<Replicas.Entry<Spec.Ask>>}
  +tv = Tries.Trie.one(Replicas.Cell<Replicas.Entry<Spec.Ask>>, kv, ev)
  s2 = Spec.Node.join(s1, tv)
  a2 = Replicas.Cell.agrees_one(
    ~Replicas.Entry<Spec.Ask>,
    ~Replicas.Entry.is_eq(~Spec.Ask, ~Spec.Ask.is_eq),
    s1,
    kv,
    ev
  )(f4)
  hc2 = Replicas.Fresh.claim(~Spec.Ask, ~Spec.Ask.is_eq, s1, kv, Spec.Chain.key(c), ev)({==})
  cell2v = Equal.trans(
    Maybe<&2, Replicas.Cell<Replicas.Entry<Spec.Ask>>>,
    Tries.Trie.get(Replicas.Cell<Replicas.Entry<Spec.Ask>>, s2, kv),
    Tries.Trie.pick(~Replicas.Cell<Replicas.Entry<Spec.Ask>>, ~Replicas.Cell.join(~Replicas.Entry<Spec.Ask>, ~Replicas.Entry.is_eq(~Spec.Ask, ~Spec.Ask.is_eq)), Tries.Trie.get(Replicas.Cell<Replicas.Entry<Spec.Ask>>, s1, kv), Tries.Trie.get(Replicas.Cell<Replicas.Entry<Spec.Ask>>, tv, kv)),
    Some{ev},
    Tries.Trie.get_union(~Replicas.Cell<Replicas.Entry<Spec.Ask>>, ~Replicas.Cell.join(~Replicas.Entry<Spec.Ask>, ~Replicas.Entry.is_eq(~Spec.Ask, ~Spec.Ask.is_eq)), s1, tv, kv),
    %Equal.sym(Maybe<&2, Replicas.Cell<Replicas.Entry<Spec.Ask>>>, Tries.Trie.get(Replicas.Cell<Replicas.Entry<Spec.Ask>>, s1, kv), None{}, f4):
      {Tries.Trie.pick(~Replicas.Cell<Replicas.Entry<Spec.Ask>>, ~Replicas.Cell.join(~Replicas.Entry<Spec.Ask>, ~Replicas.Entry.is_eq(~Spec.Ask, ~Spec.Ask.is_eq)), _, Tries.Trie.get(Replicas.Cell<Replicas.Entry<Spec.Ask>>, tv, kv)) == Some{ev}: Maybe<&2, Replicas.Cell<Replicas.Entry<Spec.Ask>>>}
    Tries.Trie.get_one(Replicas.Cell<Replicas.Entry<Spec.Ask>>, kv, ev))
  +cell2a = Equal.trans(
    Maybe<&2, Replicas.Cell<Replicas.Entry<Spec.Ask>>>,
    Tries.Trie.get(Replicas.Cell<Replicas.Entry<Spec.Ask>>, s2, ka),
    Tries.Trie.get(Replicas.Cell<Replicas.Entry<Spec.Ask>>, s1, ka),
    Some{ea},
    Replicas.Fresh.cell(~Spec.Ask, ~Spec.Ask.is_eq, s1, kv, ka, ev)({==}),
    cell1a
  )
  +asked2 = Equal.cong(
    Maybe<&2, Replicas.Cell<Replicas.Entry<Spec.Ask>>>,
    Maybe<&2, Replicas.Asked<Spec.Ask>>,
    z => Replicas.Asked.of(~Spec.Ask, Replicas.Cell.entry(~Spec.Ask, z)),
    Tries.Trie.get(Replicas.Cell<Replicas.Entry<Spec.Ask>>, s2, ka),
    Some{ea},
    cell2a
  )
  next2 = Replicas.Next.one(
    ~Spec.Ask,
    ~Spec.Ask.view,
    s2,
    Spec.Chain.key(c),
    v,
    n,
    i,
    t,
    q
  )(cell2v)(asked2)(Replicas.Key.is_eq_refl(Spec.Chain.key(c)))
  grow = Replicas.Grow.fuel(~Spec.Ask, ~Spec.Ask.is_eq, s1, kv, ev)(f4)
  has = Replicas.Owner.puts(
    ~Spec.Ask,
    ~Spec.Ask.is_eq,
    ~Ask.laws(),
    ~Spec.Ask.view,
    n,
    s1,
    i,
    Spec.Chain.key(c),
    v,
    tv,
    a2,
    hc2,
    next2,
    grow,
    Replicas.Start.of(
      ~Spec.Ask,
      ~Spec.Ask.view,
      s1,
      Spec.Chain.key(c),
      Replicas.Chain.root(~Spec.Ask, ~Spec.Ask.view, s1, Spec.Chain.key(c)),
      l
    )(ecur1)
  )
  (
    %Equal.sym(Maybe<&2, Replicas.Cell<Replicas.Entry<Spec.Ask>>>, Tries.Trie.get(Replicas.Cell<Replicas.Entry<Spec.Ask>>, s2, ka), Some{ea}, cell2a):
      {Done.status(s2, i, Replicas.Status.of(~Spec.Ask, ~Spec.Ask.view, ~Spec.Node.fits, s2, i, _)) == Replicas.Status.done{Spec.Done.written{i}}: Replicas.Status<Spec.Done>}
    %Equal.sym(Bool, List.contains(~Replicas.Id, ~Replicas.Id.is_eq, Spec.Node.chain(s2, c), i), True{}, has):
      {Done.status(s2, i, Replicas.Status.in(~Spec.Ask, ~Spec.Ask.view, ~Spec.Node.fits, s2, q, _)) == Replicas.Status.done{Spec.Done.written{i}}: Replicas.Status<Spec.Done>}
    {==},
    %Equal.sym(Maybe<&2, Replicas.Asked<Spec.Ask>>, Replicas.State.asked(~Spec.Ask, s2, i), Some{Replicas.Asked{t, q}}, asked2):
      {Res.at(Replicas.State.fuel(~Spec.Ask, s2), s2, Some{i}, name, _, Asked.hits(_, name)) == Some{x}: Maybe<&2, Texts.Bytes()>}
    %Equal.sym(Bool, Resources.Name.is_eq(name, name), True{}, Resources.Name.is_eq_refl(name)):
      {Res.at(Replicas.State.fuel(~Spec.Ask, s2), s2, Some{i}, name, Some{Replicas.Asked{t, q}}, _) == Some{x}: Maybe<&2, Texts.Bytes()>}
    {==})

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- an equality, or a proof, keeps each and/or as one value for the proofs to split on
def Spec.Node.write_written(n, s, e, b, name, base, x, v):
  match e:
    case Spec.Envelope{r, w, +t}:
      +n = n
      +s = s
      +b = b
      +name = name
      +base = base
      +x = x
      +v = v
      +i = {Replicas.Id{w, r}: Replicas.Id}
      +c = {Spec.Chain.branch{b}: Spec.Chain}
      +q = {Spec.Ask.write{b, name, base, Spec.Content.bytes{x}}: Spec.Ask}
      l = {Replicas.Step{v, [n]}: Replicas.Step}
      +ka = Replicas.Slot.key(Replicas.Slot.ask{i})
      +kv = Replicas.Slot.key(Replicas.Slot.vote{n, Spec.Chain.key(c), v})
      +ea = {Replicas.one{Replicas.Entry.ask{i, t, q}}: Replicas.Cell<Replicas.Entry<Spec.Ask>>}
      ev = {Replicas.one{Replicas.Entry.vote{i}}: Replicas.Cell<Replicas.Entry<Spec.Ask>>}
      +ta = Tries.Trie.one(Replicas.Cell<Replicas.Entry<Spec.Ask>>, ka, ea)
      tv = Tries.Trie.one(Replicas.Cell<Replicas.Entry<Spec.Ask>>, kv, ev)
      +s1 = Spec.Node.join(s, ta)
      s2 = Spec.Node.join(s1, tv)
      +h1 => +h2 => +h3 => +h4 => h5 =>
        +ecur = Replicas.Owner.cursor(
          Replicas.Chain.cursor(~Spec.Ask, ~Spec.Ask.view, s, Spec.Chain.key(c)),
          n,
          v
        )(h1)(h2)
        +a = Replicas.Cell.agrees_one(
          ~Replicas.Entry<Spec.Ask>,
          ~Replicas.Entry.is_eq(~Spec.Ask, ~Spec.Ask.is_eq),
          s,
          ka,
          ea
        )(h3)
        +hc = Replicas.Fresh.claim(~Spec.Ask, ~Spec.Ask.is_eq, s, ka, Spec.Chain.key(c), ea)({==})
        +f4 = Equal.trans(
          Maybe<&2, Replicas.Cell<Replicas.Entry<Spec.Ask>>>,
          Tries.Trie.get(Replicas.Cell<Replicas.Entry<Spec.Ask>>, s1, kv),
          Tries.Trie.get(Replicas.Cell<Replicas.Entry<Spec.Ask>>, s, kv),
          None{},
          Replicas.Fresh.cell(~Spec.Ask, ~Spec.Ask.is_eq, s, ka, kv, ea)({==}),
          h4
        )
        +ecur1 = Replicas.Stay.cursor(
          ~Spec.Ask,
          ~Spec.Ask.is_eq,
          ~Ask.laws(),
          ~Spec.Ask.view,
          s,
          ta,
          Spec.Chain.key(c),
          a,
          hc,
          l,
          ecur,
          Replicas.Next.none(~Spec.Ask, ~Spec.Ask.view, s1, Spec.Chain.key(c), v, n)(f4)
        )
        +base_bytes = Res.of(s, name, base)
        +fits = Equal.trans(
          Bool,
          Spec.Node.fits(s, q, v),
          Shared.Maybe.is_eq(
            ~Texts.Bytes(),
            ~Shared.List.is_eq(~U32, ~U32.is_eq),
            base_bytes,
            base_bytes
          ),
          True{},
          Equal.cong(
            Maybe<&2, Texts.Bytes()>,
            Bool,
            z => Shared.Maybe.is_eq(
              ~Texts.Bytes(),
              ~Shared.List.is_eq(~U32, ~U32.is_eq),
              z,
              base_bytes
            ),
            Res.of(s, name, Some{v}),
            base_bytes,
            Equal.trans(
              Maybe<&2, Texts.Bytes()>,
              Res.of(s, name, Some{v}),
              Spec.Node.content(s, name, Spec.Point.head{b}),
              base_bytes,
              Equal.sym(
                Maybe<&2, Texts.Bytes()>,
                Spec.Node.content(s, name, Spec.Point.head{b}),
                Res.of(s, name, Some{v}),
                Equal.cong(
                  Maybe<&2, Replicas.Id>,
                  Maybe<&2, Texts.Bytes()>,
                  z => Res.of(s, name, z),
                  Spec.Node.head(s, b),
                  Some{v},
                  h2
                )
              ),
              h5
            )
          ),
          Shared.Maybe.is_eq_refl(
            ~Texts.Bytes(),
            ~Shared.List.is_eq(~U32, ~U32.is_eq),
            ~Shared.List.laws(~U32, ~U32.is_eq, ~Shared.U32.laws()),
            base_bytes
          )
        )
        +may = Equal.trans(
          Bool,
          Replicas.State.may_vote(~Spec.Ask, n, s, Spec.Chain.key(c), v, [n]),
          Bool.and(
            True{},
            Maybe.is_none(
              &2,
              Replicas.Cell<Replicas.Entry<Spec.Ask>>,
              Replicas.State.cell(~Spec.Ask, s, Replicas.Slot.vote{n, Spec.Chain.key(c), v})
            )
          ),
          True{},
          Equal.cong(
            Bool,
            Bool,
            z => Bool.and(
              z,
              Maybe.is_none(
                &2,
                Replicas.Cell<Replicas.Entry<Spec.Ask>>,
                Replicas.State.cell(~Spec.Ask, s, Replicas.Slot.vote{n, Spec.Chain.key(c), v})
              )
            ),
            List.contains(~String, ~String.eq, [n], n),
            True{},
            Replicas.Owners.has(n)
          ),
          Equal.cong(
            Maybe<&2, Replicas.Cell<Replicas.Entry<Spec.Ask>>>,
            Bool,
            z => Maybe.is_none(&2, Replicas.Cell<Replicas.Entry<Spec.Ask>>, z),
            Replicas.State.cell(~Spec.Ask, s, Replicas.Slot.vote{n, Spec.Chain.key(c), v}),
            None{},
            h4
          )
        )
        +ask = Equal.trans(
          Spec.State(),
          Spec.Node.ask(n, s, Spec.Envelope{r, w, t}, q),
          Replicas.State.ask.root(
            ~Spec.Ask,
            ~Spec.Ask.is_eq,
            ~Spec.Ask.view,
            ~Spec.Node.fits,
            n,
            s,
            s1,
            i,
            q,
            Replicas.State.claim(~Spec.Ask, s, Spec.Chain.key(c))
          ),
          s2,
          Equal.cong(
            Maybe<&2, Replicas.Cell<Replicas.Entry<Spec.Ask>>>,
            Spec.State(),
            z => Replicas.State.ask.fresh(
              ~Spec.Ask,
              ~Spec.Ask.is_eq,
              ~Spec.Ask.view,
              ~Spec.Node.fits,
              n,
              s,
              i,
              t,
              q,
              z
            ),
            Replicas.State.cell(~Spec.Ask, s, Replicas.Slot.ask{i}),
            None{},
            h3
          ),
          Equal.trans(
            Spec.State(),
            Replicas.State.ask.root(
              ~Spec.Ask,
              ~Spec.Ask.is_eq,
              ~Spec.Ask.view,
              ~Spec.Node.fits,
              n,
              s,
              s1,
              i,
              q,
              Replicas.State.claim(~Spec.Ask, s, Spec.Chain.key(c))
            ),
            Replicas.State.ask.at(
              ~Spec.Ask,
              ~Spec.Ask.is_eq,
              ~Spec.Ask.view,
              ~Spec.Node.fits,
              n,
              s,
              s1,
              i,
              q,
              Replicas.Chain.cursor(~Spec.Ask, ~Spec.Ask.view, s, Spec.Chain.key(c))
            ),
            s2,
            Replicas.Owner.ask(
              ~Spec.Ask,
              ~Spec.Ask.is_eq,
              ~Spec.Ask.view,
              ~Spec.Node.fits,
              n,
              s,
              i,
              t,
              q,
              Replicas.State.claim(~Spec.Ask, s, Spec.Chain.key(c)),
              Replicas.Claim.of(
                ~Spec.Ask,
                ~Spec.Ask.view,
                s,
                Spec.Chain.key(c),
                Replicas.State.claim(~Spec.Ask, s, Spec.Chain.key(c)),
                {==},
                l
              )(ecur)
            ),
            Equal.trans(
              Spec.State(),
              Replicas.State.ask.at(
                ~Spec.Ask,
                ~Spec.Ask.is_eq,
                ~Spec.Ask.view,
                ~Spec.Node.fits,
                n,
                s,
                s1,
                i,
                q,
                Replicas.Chain.cursor(~Spec.Ask, ~Spec.Ask.view, s, Spec.Chain.key(c))
              ),
              Replicas.State.ask.at(
                ~Spec.Ask,
                ~Spec.Ask.is_eq,
                ~Spec.Ask.view,
                ~Spec.Node.fits,
                n,
                s,
                s1,
                i,
                q,
                Some{l}
              ),
              s2,
              Equal.cong(
                Maybe<&2, Replicas.Step>,
                Spec.State(),
                z => Replicas.State.ask.at(
                  ~Spec.Ask,
                  ~Spec.Ask.is_eq,
                  ~Spec.Ask.view,
                  ~Spec.Node.fits,
                  n,
                  s,
                  s1,
                  i,
                  q,
                  z
                ),
                Replicas.Chain.cursor(~Spec.Ask, ~Spec.Ask.view, s, Spec.Chain.key(c)),
                Some{l},
                ecur
              ),
              Equal.cong(
                Bool,
                Spec.State(),
                z => Bool.pick(Spec.State(), z, Replicas.State.put(~Spec.Ask, ~Spec.Ask.is_eq, s1, Replicas.Slot.vote{n, Spec.Chain.key(c), v}, Replicas.Entry.vote{i}), s1),
                Bool.and(Replicas.State.may_vote(~Spec.Ask, n, s, Spec.Chain.key(c), v, [n]), Spec.Node.fits(s, q, v)),
                True{},
                %Equal.sym(Bool, Replicas.State.may_vote(~Spec.Ask, n, s, Spec.Chain.key(c), v, [n]), True{}, may): {Bool.and(_, Spec.Node.fits(s, q, v)) == True{}: Bool}
                fits)
            )
          )
        )
        +cell1a = Equal.trans(
          Maybe<&2, Replicas.Cell<Replicas.Entry<Spec.Ask>>>,
          Tries.Trie.get(Replicas.Cell<Replicas.Entry<Spec.Ask>>, s1, ka),
          Tries.Trie.pick(~Replicas.Cell<Replicas.Entry<Spec.Ask>>, ~Replicas.Cell.join(~Replicas.Entry<Spec.Ask>, ~Replicas.Entry.is_eq(~Spec.Ask, ~Spec.Ask.is_eq)), Tries.Trie.get(Replicas.Cell<Replicas.Entry<Spec.Ask>>, s, ka), Tries.Trie.get(Replicas.Cell<Replicas.Entry<Spec.Ask>>, ta, ka)),
          Some{ea},
          Tries.Trie.get_union(~Replicas.Cell<Replicas.Entry<Spec.Ask>>, ~Replicas.Cell.join(~Replicas.Entry<Spec.Ask>, ~Replicas.Entry.is_eq(~Spec.Ask, ~Spec.Ask.is_eq)), s, ta, ka),
          %Equal.sym(Maybe<&2, Replicas.Cell<Replicas.Entry<Spec.Ask>>>, Tries.Trie.get(Replicas.Cell<Replicas.Entry<Spec.Ask>>, s, ka), None{}, h3):
            {Tries.Trie.pick(~Replicas.Cell<Replicas.Entry<Spec.Ask>>, ~Replicas.Cell.join(~Replicas.Entry<Spec.Ask>, ~Replicas.Entry.is_eq(~Spec.Ask, ~Spec.Ask.is_eq)), _, Tries.Trie.get(Replicas.Cell<Replicas.Entry<Spec.Ask>>, ta, ka)) == Some{ea}: Maybe<&2, Replicas.Cell<Replicas.Entry<Spec.Ask>>>}
          Tries.Trie.get_one(Replicas.Cell<Replicas.Entry<Spec.Ask>>, ka, ea))
        %Equal.sym(Spec.State(), Spec.Node.ask(n, s, Spec.Envelope{r, w, t}, q), s2, ask):
          (
            {
              Spec.Node.answer(
                _,
                i
              )
                == Replicas.Status.done{Spec.Done.written{i}}: Replicas.Status<Spec.Done>
            }
              & {Spec.Node.content(_, name, Spec.Point.at{i}) == Some{x}: Maybe<&2, Texts.Bytes()>}
          )
        Written.at(n, s1, i, t, b, name, base, x, v, ecur1, f4, cell1a)
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# Forward laws
# ------------

# a lazy choice of x or none is the eager one
def Forward.ours_pick(
  b: Bool,
  x: Replicas.Id
) -> {
  Shared.Bool.when(
    Maybe<&2, Replicas.Id>,
    b,
    u => Some{x},
    u => None{}
  )
    == Bool.pick(Maybe<&2, Replicas.Id>, b, Some{x}, None{}): Maybe<&2, Replicas.Id>
}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# Forward.if is the choice of the law, whatever held is
def Forward.if_pick(
  held: Bool,
  s: Spec.State(),
  +x: Replicas.Id,
  y: Replicas.Id
) -> {
  Forward.if(
    held,
    s,
    x,
    y
  )
    == Bool.pick(
      Maybe<&2, Replicas.Id>,
      held,
      Some{y},
      Bool.pick(Maybe<&2, Replicas.Id>, Version.is_from(s, y, x), Some{x}, None{})
    ): Maybe<&2, Replicas.Id>
}:
  match held:
    case True{}:
      {==}
    case False{}:
      Forward.ours_pick(Version.is_from(s, y, x), x)

def Spec.Node.forward_exactly(s, x, y):
  +s = s
  +x = x
  +y = y
  Forward.if_pick(Version.is_from(s, x, y), s, x, y)

# Uses laws
# ---------

# what n imports is the same in the graph g and in Uses.at(g)
def Uses.succ_at(
  g: Spec.Uses,
  n: Resources.Name
) -> {
  Shared.Bool.when(
    List<&2, Resources.Name>,
    List.contains(~Resources.Name, ~Resources.Name.is_eq, Spec.Uses.names(g), n),
    w => Spec.Node.imports(Spec.Uses.state(g), Spec.Uses.branch(g), n),
    w => []
  )
    == Uses.succ(Uses.at(g), n): List<&2, Resources.Name>
}:
  match g:
    case Spec.Uses{s, b, ns}:
      {==}

# the resources are the same in the graph g and in Uses.at(g)
def Uses.nodes_at(
  g: Spec.Uses
) -> {Spec.Uses.names(g) == Uses.nodes(Uses.at(g)): List<&2, Resources.Name>}:
  match g:
    case Spec.Uses{s, b, ns}:
      {==}

def Spec.Node.uses_exactly(s, b, u, c):
  +s = s
  +b = b
  Equal.sym(
    Bool,
    Reaches.Reach.in(
      ~Resources.Name,
      ~Spec.Uses,
      ~Resources.Name.is_eq,
      ~(
        +g => +n => Shared.Bool.when(
          List<&2, Resources.Name>,
          List.contains(~Resources.Name, ~Resources.Name.is_eq, Spec.Uses.names(g), n),
          w => Spec.Node.imports(Spec.Uses.state(g), Spec.Uses.branch(g), n),
          w => []
        )
      ),
      ~Spec.Uses.names,
      Spec.Uses{s, b, Spec.Node.resources(s, b)},
      u,
      c
    ),
    Spec.Node.uses(s, b, u, c),
    Reaches.Reach.in_same(
      ~Resources.Name,
      ~Spec.Uses,
      ~Uses,
      ~Resources.Name.is_eq,
      ~(
        +g => +n => Shared.Bool.when(
          List<&2, Resources.Name>,
          List.contains(~Resources.Name, ~Resources.Name.is_eq, Spec.Uses.names(g), n),
          w => Spec.Node.imports(Spec.Uses.state(g), Spec.Uses.branch(g), n),
          w => []
        )
      ),
      ~Uses.succ,
      ~Spec.Uses.names,
      ~Uses.nodes,
      ~Uses.at,
      ~Uses.succ_at,
      ~Uses.nodes_at,
      Spec.Uses{s, b, Spec.Node.resources(s, b)},
      u,
      c
    )
  )

# Touch laws
# ----------
# a chain of lazy "and"s is the chain of "and"s
def Touch.lazy(
  a: Bool,
  b: Bool,
  c: Bool,
  d: Bool,
  e: Bool,
  -f: Bool
) -> {
  List.all.if(
    w => List.all.if(w => List.all.if(w => List.all.if(w => List.all.if(w => f, e), d), c), b),
    a
  )
    == Bool.and(a, Bool.and(b, Bool.and(c, Bool.and(d, Bool.and(e, f))))): Bool
}:
  match a:
    case False{}:
      {==}
    case True{}:
      match b:
        case False{}:
          {==}
        case True{}:
          match c:
            case False{}:
              {==}
            case True{}:
              match d:
                case False{}:
                  {==}
                case True{}:
                  match e:
                    case False{}:
                      {==}
                    case True{}:
                      {==}

def Spec.Node.touches_exactly(s, v, c, b, u):
  +s = s
  +v = v
  +c = c
  +b = b
  +u = u
  %Shared.Bool.or_lazy(
    Resources.Name.is_eq(u, c),
    Spec.Node.uses(s, b, u, c)
  ): {
    Spec.Node.touches(
      s,
      Spec.Touch{v, c, b, u}
    )
      == Bool.and(
        Touch.named(s, b),
        Bool.and(
          Touch.made(s, v),
          Bool.and(
            Touch.lacks(s, b, v),
            Bool.and(Touch.wrote(s, v, c), Bool.and(Touch.held(s, b, u), _))
          )
        )
      ): Bool
  }
  Touch.lazy(
    Touch.named(s, b),
    Touch.made(s, v),
    Touch.lacks(s, b, v),
    Touch.wrote(s, v, c),
    Touch.held(s, b, u),
    List.any.if(w => Spec.Node.uses(s, b, u, c), Resources.Name.is_eq(u, c))
  )

# Touch.is_eq is True only for equal touches
def Touch.is_eq_sound(
  a: Spec.Touch,
  b: Spec.Touch
) -> {Spec.Touch.is_eq(a, b) == True{}: Bool} -> {a == b: Spec.Touch}:
  match a b:
    case Spec.Touch{+v1, +c1, +b1, +u1} Spec.Touch{+v2, +c2, +b2, +u2}:
      +h =>
        +r1 = Bool.and(
          Resources.Name.is_eq(c1, c2),
          Bool.and(String.eq(b1, b2), Resources.Name.is_eq(u1, u2))
        )
        +r2 = Bool.and(String.eq(b1, b2), Resources.Name.is_eq(u1, u2))
        +h1 = Shared.Bool.and_true_right(Replicas.Id.is_eq(v1, v2), r1)(h)
        +h2 = Shared.Bool.and_true_right(Resources.Name.is_eq(c1, c2), r2)(h1)
        %Equal.sym(
          Replicas.Id,
          v1,
          v2,
          Replicas.Id.is_eq_sound(
            v1,
            v2
          )(Shared.Bool.and_true_left(Replicas.Id.is_eq(v1, v2), r1)(h))
        ):
          {Spec.Touch{_, c1, b1, u1} == Spec.Touch{v2, c2, b2, u2}: Spec.Touch}
        %Equal.sym(
          Resources.Name,
          c1,
          c2,
          Resources.Name.is_eq_sound(
            c1,
            c2
          )(Shared.Bool.and_true_left(Resources.Name.is_eq(c1, c2), r2)(h1))
        ): {Spec.Touch{v2, _, b1, u1} == Spec.Touch{v2, c2, b2, u2}: Spec.Touch}
        %Equal.sym(
          String,
          b1,
          b2,
          Texts.String.eq_sound(
            b1,
            b2
          )(Shared.Bool.and_true_left(String.eq(b1, b2), Resources.Name.is_eq(u1, u2))(h2))
        ): {Spec.Touch{v2, c2, _, u1} == Spec.Touch{v2, c2, b2, u2}: Spec.Touch}
        %Equal.sym(
          Resources.Name,
          u1,
          u2,
          Resources.Name.is_eq_sound(
            u1,
            u2
          )(Shared.Bool.and_true_right(String.eq(b1, b2), Resources.Name.is_eq(u1, u2))(h2))
        ): {Spec.Touch{v2, c2, b2, _} == Spec.Touch{v2, c2, b2, u2}: Spec.Touch}
        {==}

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Touch.is_eq is True for a touch and itself
def Touch.is_eq_refl(a: Spec.Touch) -> {Spec.Touch.is_eq(a, a) == True{}: Bool}:
  match a:
    case Spec.Touch{+v, +c, +b, +u}:
      Shared.Bool.and_both(
        Replicas.Id.is_eq(v, v),
        Bool.and(Resources.Name.is_eq(c, c), Bool.and(String.eq(b, b), Resources.Name.is_eq(u, u)))
      )(
        Replicas.Id.is_eq_refl(v)
      )(
        Shared.Bool.and_both(
          Resources.Name.is_eq(c, c),
          Bool.and(String.eq(b, b), Resources.Name.is_eq(u, u))
        )(
          Resources.Name.is_eq_refl(c)
        )(
          Shared.Bool.and_both(
            String.eq(b, b),
            Resources.Name.is_eq(u, u)
          )(Texts.String.eq_refl(b))(Resources.Name.is_eq_refl(u))
        )
      )

# the laws of Spec.Touch.is_eq
def Touch.laws() -> Shared.Eq.Laws(Spec.Touch, Spec.Touch.is_eq):
  (Touch.is_eq_refl, Touch.is_eq_sound)

# two touches that differ at most in the resource used are the same as those
# resources are
def Touch.is_eq_at(
  v: Replicas.Id,
  c: Resources.Name,
  b: String,
  x: Resources.Name,
  u: Resources.Name
) -> {
  Spec.Touch.is_eq(
    Spec.Touch{v, c, b, x},
    Spec.Touch{v, c, b, u}
  )
    == Resources.Name.is_eq(x, u): Bool
}:
  %Equal.sym(Bool, Replicas.Id.is_eq(v, v), True{}, Replicas.Id.is_eq_refl(v)):
    {
      Bool.and(
        _,
        Bool.and(Resources.Name.is_eq(c, c), Bool.and(String.eq(b, b), Resources.Name.is_eq(x, u)))
      )
        == Resources.Name.is_eq(x, u): Bool
    }
  %Equal.sym(Bool, Resources.Name.is_eq(c, c), True{}, Resources.Name.is_eq_refl(c)):
    {
      Bool.and(
        _,
        Bool.and(String.eq(b, b), Resources.Name.is_eq(x, u))
      )
        == Resources.Name.is_eq(x, u): Bool
    }
  %Equal.sym(Bool, String.eq(b, b), True{}, Texts.String.eq_refl(b)):
    {Bool.and(_, Resources.Name.is_eq(x, u)) == Resources.Name.is_eq(x, u): Bool}
  {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# Touch.each_has at the first resource, once it is known to be u or not (hit)
def Touch.each_has.at(
  hit: Bool,
  -r: List<&2, Resources.Name>,
  -ts: List<&2, Spec.Touch>,
  -u: Resources.Name,
  -t: Spec.Touch,
  h: {
    List.any.if(
      w => List.contains(~Resources.Name, ~Resources.Name.is_eq, r, u),
      hit
    )
      == True{}: Bool
  },
  ih: {
    List.contains(~Resources.Name, ~Resources.Name.is_eq, r, u) == True{}: Bool
  } -> {List.contains(~Spec.Touch, ~Spec.Touch.is_eq, ts, t) == True{}: Bool}
) -> {List.any.if(w => List.contains(~Spec.Touch, ~Spec.Touch.is_eq, ts, t), hit) == True{}: Bool}:
  match hit:
    case True{}:
      {==}
    case False{}:
      ih(h)

# a resource u of us gives the touch of u
def Touch.each_has(
  us: List<&2, Resources.Name>,
  +v: Replicas.Id,
  +c: Resources.Name,
  +b: String,
  +u: Resources.Name
) -> {
  List.contains(~Resources.Name, ~Resources.Name.is_eq, us, u) == True{}: Bool
} -> {
  List.contains(
    ~Spec.Touch,
    ~Spec.Touch.is_eq,
    Touch.each(us, v, c, b),
    Spec.Touch{v, c, b, u}
  )
    == True{}: Bool
}:
  match us:
    case Nil{}:
      h => Empty.absurd(
        {
          List.contains(
            ~Spec.Touch,
            ~Spec.Touch.is_eq,
            Touch.each([], v, c, b),
            Spec.Touch{v, c, b, u}
          )
            == True{}: Bool
        },
        Shared.Bool.false_ne_true(h)
      )
    case Con{+x, r}:
      h =>
        %Equal.sym(
          Bool,
          Spec.Touch.is_eq(Spec.Touch{v, c, b, x}, Spec.Touch{v, c, b, u}),
          Resources.Name.is_eq(x, u),
          Touch.is_eq_at(v, c, b, x, u)
        ): {
          List.any.if(
            w => List.contains(
              ~Spec.Touch,
              ~Spec.Touch.is_eq,
              Touch.each(r, v, c, b),
              Spec.Touch{v, c, b, u}
            ),
            _
          )
            == True{}: Bool
        }
        Touch.each_has.at(
          Resources.Name.is_eq(x, u),
          r,
          Touch.each(r, v, c, b),
          u,
          Spec.Touch{v, c, b, u},
          h,
          Touch.each_has(r, v, c, b, u)
        )

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof's statement keeps each and/or as one value for the proof to split on; a proof does not run
# a touch that holds is among the touches that may hold of its branch
# a touch that holds holds part by part
def Touch.whole(
  s: Spec.State(),
  v: Replicas.Id,
  c: Resources.Name,
  d: String,
  u: Resources.Name
) -> {
  Spec.Node.touches(s, Spec.Touch{v, c, d, u}) == True{}: Bool
} -> {
  Bool.and(
    Touch.named(s, d),
    Bool.and(
      Touch.made(s, v),
      Bool.and(
        Touch.lacks(s, d, v),
        Bool.and(Touch.wrote(s, v, c), Bool.and(Touch.held(s, d, u), Touch.reaches(s, d, u, c)))
      )
    )
  )
    == True{}: Bool
}:
  h => Equal.trans(
    Bool,
    Bool.and(
      Touch.named(s, d),
      Bool.and(
        Touch.made(s, v),
        Bool.and(
          Touch.lacks(s, d, v),
          Bool.and(Touch.wrote(s, v, c), Bool.and(Touch.held(s, d, u), Touch.reaches(s, d, u, c)))
        )
      )
    ),
    Spec.Node.touches(s, Spec.Touch{v, c, d, u}),
    True{},
    Equal.sym(
      Bool,
      Spec.Node.touches(s, Spec.Touch{v, c, d, u}),
      Bool.and(
        Touch.named(s, d),
        Bool.and(
          Touch.made(s, v),
          Bool.and(
            Touch.lacks(s, d, v),
            Bool.and(Touch.wrote(s, v, c), Bool.and(Touch.held(s, d, u), Touch.reaches(s, d, u, c)))
          )
        )
      ),
      Spec.Node.touches_exactly(s, v, c, d, u)
    ),
    h
  )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information
def Touch.complete(
  +s: Spec.State(),
  +v: Replicas.Id,
  +c: Resources.Name,
  +d: String,
  +u: Resources.Name
) -> {
  Spec.Node.touches(s, Spec.Touch{v, c, d, u}) == True{}: Bool
} -> {
  List.contains(
    ~Spec.Touch,
    ~Spec.Touch.is_eq,
    Affects.cands(s, d),
    Spec.Touch{v, c, d, u}
  )
    == True{}: Bool
}:
  +hb = Touch.made(s, v)
  +hc = Touch.lacks(s, d, v)
  +hd = Touch.wrote(s, v, c)
  +he = Touch.held(s, d, u)
  +hf = Touch.reaches(s, d, u, c)
  rest = Bool.and(hb, Bool.and(hc, Bool.and(hd, Bool.and(he, hf))))
  h =>
    +h1 = Shared.Bool.and_true_right(Touch.named(s, d), rest)(Touch.whole(s, v, c, d, u)(h))
    +h3 = Shared.Bool.and_true_right(
      hc,
      Bool.and(hd, Bool.and(he, hf))
    )(Shared.Bool.and_true_right(hb, Bool.and(hc, Bool.and(hd, Bool.and(he, hf))))(h1))
    +ew = Shared.Maybe.is_eq_sound(
      ~Resources.Name,
      ~Resources.Name.is_eq,
      Resources.Name.is_eq_sound,
      Spec.Node.wrote(s, v),
      Some{c}
    )(Shared.Bool.and_true_left(hd, Bool.and(he, hf))(h3))
    Shared.List.contains_flat(
      ~Replicas.Id,
      ~Spec.Touch,
      ~Affects,
      ~Replicas.Id.is_eq,
      ~Spec.Touch.is_eq,
      ~Affects.at,
      ~Replicas.Id.laws(),
      Touch.versions(s),
      Affects.of(s, d),
      v,
      Spec.Touch{v, c, d, u}
    )(Shared.Bool.and_true_left(hb, Bool.and(hc, Bool.and(hd, Bool.and(he, hf))))(h1))(
      %Equal.sym(Maybe<&2, Resources.Name>, Spec.Node.wrote(s, v), Some{c}, ew): {List.contains(~Spec.Touch, ~Spec.Touch.is_eq, Touch.of(_, v, d, Spec.Node.resources(s, d)), Spec.Touch{v, c, d, u}) == True{}: Bool}
      Touch.each_has(Spec.Node.resources(s, d), v, c, d, u)(Shared.Bool.and_true_left(he, hf)(Shared.Bool.and_true_right(hd, Bool.and(he, hf))(h3))))

# a touch of the branch b that holds may hold of b
def Affects.complete(
  +s: Spec.State(),
  +b: String,
  t: Spec.Touch
) -> {
  Bool.and(String.eq(Spec.Touch.branch(t), b), Spec.Node.touches(s, t)) == True{}: Bool
} -> {List.contains(~Spec.Touch, ~Spec.Touch.is_eq, Affects.cands(s, b), t) == True{}: Bool}:
  match t:
    case Spec.Touch{+v, +c, +d, +u}:
      +h =>
        %Texts.String.eq_sound(
          d,
          b
        )(
          Shared.Bool.and_true_left(
            String.eq(d, b),
            Spec.Node.touches(s, Spec.Touch{v, c, d, u})
          )(h)
        ): {
          List.contains(
            ~Spec.Touch,
            ~Spec.Touch.is_eq,
            Affects.cands(s, _),
            Spec.Touch{v, c, d, u}
          )
            == True{}: Bool
        }
        Touch.complete(
          s,
          v,
          c,
          d,
          u
        )(
          Shared.Bool.and_true_right(
            String.eq(d, b),
            Spec.Node.touches(s, Spec.Touch{v, c, d, u})
          )(h)
        )

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
def Spec.Node.affects_exactly(s, b, t):
  +s = s
  +b = b
  +t = t
  +e = String.eq(Spec.Touch.branch(t), b)
  k = Spec.Node.touches(s, t)
  %Shared.Bool.and_lazy(e, k):
    {List.contains(~Spec.Touch, ~Spec.Touch.is_eq, Spec.Node.affects(s, b), t) == _: Bool}
  Shared.List.keep_exactly(
    ~Spec.Touch,
    ~Affects,
    ~Spec.Touch.is_eq,
    ~Affects.keeps,
    ~Touch.laws(),
    Affects.cands(s, b),
    Affects.of(s, b),
    t,
    h => Affects.complete(
      s,
      b,
      t
    )(
      Equal.trans(
        Bool,
        Bool.and(e, k),
        List.all.if(w => k, e),
        True{},
        Equal.sym(Bool, List.all.if(w => k, e), Bool.and(e, k), Shared.Bool.and_lazy(e, k)),
        h
      )
    )
  )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof's statement keeps each and/or as one value for the proof to split on; a proof does not run
# a touch that holds may hold of some branch
def Impact.complete(
  +s: Spec.State(),
  t: Spec.Touch
) -> {
  Spec.Node.touches(s, t) == True{}: Bool
} -> {List.contains(~Spec.Touch, ~Spec.Touch.is_eq, Impact.cands(s), t) == True{}: Bool}:
  match t:
    case Spec.Touch{+v, +c, +d, +u}:
      +ht =>
        Shared.List.contains_flat(
          ~String,
          ~Spec.Touch,
          ~Spec.State(),
          ~String.eq,
          ~Spec.Touch.is_eq,
          ~Affects.cands,
          ~Texts.String.laws(),
          Spec.Branch.names(Spec.Node.branches(s)),
          s,
          d,
          Spec.Touch{v, c, d, u}
        )(
          Shared.Bool.and_true_left(
            Touch.named(s, d),
            Bool.and(
              Touch.made(s, v),
              Bool.and(
                Touch.lacks(s, d, v),
                Bool.and(
                  Touch.wrote(s, v, c),
                  Bool.and(Touch.held(s, d, u), Touch.reaches(s, d, u, c))
                )
              )
            )
          )(Touch.whole(s, v, c, d, u)(ht))
        )(Touch.complete(s, v, c, d, u)(ht))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
def Spec.Node.impact_exactly(s, p, t):
  +s = s
  p = p
  +t = t
  +m = Spec.Node.version(s, p)
  +i = Maybe.is_some(&2, Replicas.Id, m)
  +o = Spec.Node.has(
    s,
    Maybe.default(&2, Replicas.Id, m, Spec.Touch.version(t)),
    Spec.Touch.version(t)
  )
  k = Spec.Node.touches(s, t)
  +e = Equal.trans(
    Bool,
    List.all.if(w => k, List.all.if(w => o, i)),
    Bool.and(List.all.if(w => o, i), k),
    Bool.and(Bool.and(i, o), k),
    Shared.Bool.and_lazy(List.all.if(w => o, i), k),
    Equal.cong(
      Bool,
      Bool,
      z => Bool.and(z, k),
      List.all.if(w => o, i),
      Bool.and(i, o),
      Shared.Bool.and_lazy(i, o)
    )
  )
  %e:
    {List.contains(~Spec.Touch, ~Spec.Touch.is_eq, Spec.Node.impact(s, p), t) == _: Bool}
  Shared.List.keep_exactly(
    ~Spec.Touch,
    ~Impact,
    ~Spec.Touch.is_eq,
    ~Impact.keeps,
    ~Touch.laws(),
    Impact.cands(s),
    Impact{s, m},
    t,
    h => Impact.complete(
      s,
      t
    )(
      Shared.Bool.and_true_right(
        Bool.and(i, o),
        k
      )(
        Equal.trans(
          Bool,
          Bool.and(Bool.and(i, o), k),
          List.all.if(w => k, List.all.if(w => o, i)),
          True{},
          Equal.sym(
            Bool,
            List.all.if(w => k, List.all.if(w => o, i)),
            Bool.and(Bool.and(i, o), k),
            e
          ),
          h
        )
      )
    )
  )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# Set-group fits
# --------------

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Group.loops_has at the first member m, once it is known to be the group h or
# not (hit)
def Group.loops_has.at(
  hit: Bool,
  s: Spec.State(),
  g: String,
  h: String,
  m: Spec.Member,
  r: List<&2, Spec.Member>,
  em: {Spec.Member.is_eq(m, Spec.Member.group{h}) == hit: Bool},
  hm: {
    List.any.if(
      u => List.contains(~Spec.Member, ~Spec.Member.is_eq, r, Spec.Member.group{h}),
      hit
    )
      == True{}: Bool
  },
  hl: {
    List.any.if(
      u => Spec.Node.is_inside(s, Spec.Member.group{g}, h),
      String.eq(h, g)
    )
      == True{}: Bool
  },
  ih: {
    List.contains(~Spec.Member, ~Spec.Member.is_eq, r, Spec.Member.group{h}) == True{}: Bool
  } -> {Group.loops.any(s, g, r) == True{}: Bool}
) -> {List.any.if(u => Group.loops.any(s, g, r), Group.loops(s, g, m)) == True{}: Bool}:
  match hit:
    case True{}:
      %Equal.sym(
        Spec.Member,
        m,
        Spec.Member.group{h},
        Member.is_eq_sound(m, Spec.Member.group{h})(em)
      ):
        {List.any.if(u => Group.loops.any(s, g, r), Group.loops(s, g, _)) == True{}: Bool}
      %Equal.sym(
        Bool,
        List.any.if(u => Spec.Node.is_inside(s, Spec.Member.group{g}, h), String.eq(h, g)),
        True{},
        hl
      ): {List.any.if(u => Group.loops.any(s, g, r), _) == True{}: Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, Group.loops.any(s, g, r), True{}, ih(hm)):
        {List.any.if(u => _, Group.loops(s, g, m)) == True{}: Bool}
      Shared.List.any.if_true(Group.loops(s, g, m))
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# a member of ms that is the group g, or holds it, makes g contain itself
def Group.loops_has(
  ms: List<&2, Spec.Member>,
  +s: Spec.State(),
  +g: String,
  +h: String
) -> {
  List.contains(~Spec.Member, ~Spec.Member.is_eq, ms, Spec.Member.group{h}) == True{}: Bool
} -> {
  List.any.if(u => Spec.Node.is_inside(s, Spec.Member.group{g}, h), String.eq(h, g)) == True{}: Bool
} -> {Group.loops.any(s, g, ms) == True{}: Bool}:
  match ms:
    case Nil{}:
      hm => hl => Empty.absurd(
        {Group.loops.any(s, g, []) == True{}: Bool},
        Shared.Bool.false_ne_true(hm)
      )
    case Con{+m, +r}:
      hm => +hl =>
        Group.loops_has.at(
          Spec.Member.is_eq(m, Spec.Member.group{h}),
          s,
          g,
          h,
          m,
          r,
          {==},
          hm,
          hl,
          x => Group.loops_has(r, s, g, h)(x)(hl)
        )
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof's statement keeps each and/or as one value for the proof to split on; a proof does not run
def Spec.Node.fits_set_group(s, g, ms, h, v):
  +g = g
  +h = h
  h5 => h6 =>
    +lazy = Equal.trans(
      Bool,
      List.any.if(u => Spec.Node.is_inside(s, Spec.Member.group{g}, h), String.eq(h, g)),
      Bool.or(String.eq(h, g), Spec.Node.is_inside(s, Spec.Member.group{g}, h)),
      True{},
      Shared.Bool.or_lazy(String.eq(h, g), Spec.Node.is_inside(s, Spec.Member.group{g}, h)),
      h6
    )
    %Equal.sym(Bool, Group.loops.any(s, g, ms), True{}, Group.loops_has(ms, s, g, h)(h5)(lazy)):
      {Bool.not(_) == False{}: Bool}
    {==}
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information
