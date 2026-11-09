import Base
import ../../shared/formats.bend as Formats
import ../../shared/reach.bend as Reaches
import ../../shared/replica.bend as Replica
import ../../shared/resources.bend as Resources
import ../../shared/shared.bend as Shared
import ./spec.bend as Spec

# The pure core of a Vend Node.

# Equality
# --------

# Chain.same is True for a chain and itself
def Chain.same_refl(a: Spec.Chain) -> {Spec.Chain.same(a, a) == True{}: Bool}:
  match a:
    case Spec.Chain.branch{x}:
      Shared.String.eq_refl(x)
    case Spec.Chain.group{x}:
      Shared.String.eq_refl(x)

# Chain.same is True only for equal chains
def Chain.same_sound(
  a: Spec.Chain,
  b: Spec.Chain
) -> {Spec.Chain.same(a, b) == True{}: Bool} -> {a == b: Spec.Chain}:
  match a b:
    case Spec.Chain.branch{x} Spec.Chain.branch{y}:
      h =>
        %Shared.String.eq_sound(x, y)(h): {Spec.Chain.branch{x} == Spec.Chain.branch{_}: Spec.Chain}
        {==}
    case Spec.Chain.group{x} Spec.Chain.group{y}:
      h =>
        %Shared.String.eq_sound(x, y)(h): {Spec.Chain.group{x} == Spec.Chain.group{_}: Spec.Chain}
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

# Member.same is True for a member and itself
def Member.same_refl(a: Spec.Member) -> {Spec.Member.same(a, a) == True{}: Bool}:
  match a:
    case Spec.Member.node{x}:
      Shared.String.eq_refl(x)
    case Spec.Member.group{x}:
      Shared.String.eq_refl(x)

# Member.same is True only for equal members
def Member.same_sound(
  a: Spec.Member,
  b: Spec.Member
) -> {Spec.Member.same(a, b) == True{}: Bool} -> {a == b: Spec.Member}:
  match a b:
    case Spec.Member.node{x} Spec.Member.node{y}:
      h =>
        %Shared.String.eq_sound(x, y)(h): {Spec.Member.node{x} == Spec.Member.node{_}: Spec.Member}
        {==}
    case Spec.Member.group{x} Spec.Member.group{y}:
      h =>
        %Shared.String.eq_sound(
          x,
          y
        )(h): {Spec.Member.group{x} == Spec.Member.group{_}: Spec.Member}
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

# the laws of Spec.Member.same
def Member.laws() -> Shared.Eq.Laws(Spec.Member, Spec.Member.same):
  (Member.same_refl, Member.same_sound)

# Content.same is True for a content and itself
def Content.same_refl(a: Spec.Content) -> {Spec.Content.same(a, a) == True{}: Bool}:
  match a:
    case Spec.Content.bytes{x}:
      Shared.Bytes.is_eq_refl(x)
    case Spec.Content.of{v}:
      Replica.Id.same_refl(v)

# Content.same is True only for equal contents
def Content.same_sound(
  a: Spec.Content,
  b: Spec.Content
) -> {Spec.Content.same(a, b) == True{}: Bool} -> {a == b: Spec.Content}:
  match a b:
    case Spec.Content.bytes{x} Spec.Content.bytes{y}:
      h =>
        %Shared.Bytes.is_eq_sound(
          x,
          y
        )(h): {Spec.Content.bytes{x} == Spec.Content.bytes{_}: Spec.Content}
        {==}
    case Spec.Content.of{x} Spec.Content.of{y}:
      h =>
        %Replica.Id.same_sound(x, y)(h): {Spec.Content.of{x} == Spec.Content.of{_}: Spec.Content}
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
# Ask.same is True for a change and itself
def Ask.same_refl(a: Spec.Ask) -> {Spec.Ask.same(a, a) == True{}: Bool}:
  match a:
    case Spec.Ask.write{+b, +n, +v, +c}:
      Shared.Bool.and_both(
        String.eq(b, b),
        Bool.and(
          Resources.Name.same(n, n),
          Bool.and(Shared.Maybe.same(~Replica.Id, ~Replica.Id.same, v, v), Spec.Content.same(c, c))
        )
      )(
        Shared.String.eq_refl(b)
      )(
        Shared.Bool.and_both(
          Resources.Name.same(n, n),
          Bool.and(Shared.Maybe.same(~Replica.Id, ~Replica.Id.same, v, v), Spec.Content.same(c, c))
        )(
          Resources.Name.same_refl(n)
        )(
          Shared.Bool.and_both(
            Shared.Maybe.same(~Replica.Id, ~Replica.Id.same, v, v),
            Spec.Content.same(c, c)
          )(
            Shared.Maybe.same_refl(~Replica.Id, ~Replica.Id.same, ~Replica.Id.laws(), v)
          )(Content.same_refl(c))
        )
      )
    case Spec.Ask.set_branch{+b, +v}:
      Shared.Bool.and_both(
        String.eq(b, b),
        Replica.Id.same(v, v)
      )(Shared.String.eq_refl(b))(Replica.Id.same_refl(v))
    case Spec.Ask.merge{+b, +v}:
      Shared.Bool.and_both(
        String.eq(b, b),
        Replica.Id.same(v, v)
      )(Shared.String.eq_refl(b))(Replica.Id.same_refl(v))
    case Spec.Ask.resolve{+b, +k, +n, +c}:
      Shared.Bool.and_both(
        String.eq(b, b),
        Bool.and(
          Replica.Id.same(k, k),
          Bool.and(Resources.Name.same(n, n), Spec.Content.same(c, c))
        )
      )(
        Shared.String.eq_refl(b)
      )(
        Shared.Bool.and_both(
          Replica.Id.same(k, k),
          Bool.and(Resources.Name.same(n, n), Spec.Content.same(c, c))
        )(
          Replica.Id.same_refl(k)
        )(
          Shared.Bool.and_both(
            Resources.Name.same(n, n),
            Spec.Content.same(c, c)
          )(Resources.Name.same_refl(n))(Content.same_refl(c))
        )
      )
    case Spec.Ask.mark{+b, +m, +t}:
      Shared.Bool.and_both(
        String.eq(b, b),
        Bool.and(String.eq(m, m), String.eq(t, t))
      )(
        Shared.String.eq_refl(b)
      )(
        Shared.Bool.and_both(
          String.eq(m, m),
          String.eq(t, t)
        )(Shared.String.eq_refl(m))(Shared.String.eq_refl(t))
      )
    case Spec.Ask.set_owner{+c, +ms}:
      Shared.Bool.and_both(
        Spec.Chain.same(c, c),
        Shared.List.same(~String, ~String.eq, ms, ms)
      )(Chain.same_refl(c))(Shared.List.same_refl(~String, ~String.eq, ~Shared.String.laws(), ms))
    case Spec.Ask.set_group{+g, +ms}:
      Shared.Bool.and_both(
        String.eq(g, g),
        Shared.List.same(~Spec.Member, ~Spec.Member.same, ms, ms)
      )(
        Shared.String.eq_refl(g)
      )(Shared.List.same_refl(~Spec.Member, ~Spec.Member.same, ~Member.laws(), ms))

# Ask.same is True only for equal changes
def Ask.same_sound(
  a: Spec.Ask,
  b: Spec.Ask
) -> {Spec.Ask.same(a, b) == True{}: Bool} -> {a == b: Spec.Ask}:
  match a b:
    case Spec.Ask.write{+b1, +n1, +v1, +c1} Spec.Ask.write{+b2, +n2, +v2, +c2}:
      +h =>
        +r1 = Bool.and(
          Resources.Name.same(n1, n2),
          Bool.and(
            Shared.Maybe.same(~Replica.Id, ~Replica.Id.same, v1, v2),
            Spec.Content.same(c1, c2)
          )
        )
        +r2 = Bool.and(
          Shared.Maybe.same(~Replica.Id, ~Replica.Id.same, v1, v2),
          Spec.Content.same(c1, c2)
        )
        +h1 = Shared.Bool.and_true_right(String.eq(b1, b2), r1)(h)
        +h2 = Shared.Bool.and_true_right(Resources.Name.same(n1, n2), r2)(h1)
        %Shared.String.eq_sound(b1, b2)(Shared.Bool.and_true_left(String.eq(b1, b2), r1)(h)):
          {Spec.Ask.write{b1, n1, v1, c1} == Spec.Ask.write{_, n2, v2, c2}: Spec.Ask}
        %Resources.Name.same_sound(
          n1,
          n2
        )(Shared.Bool.and_true_left(Resources.Name.same(n1, n2), r2)(h1)):
          {Spec.Ask.write{b1, n1, v1, c1} == Spec.Ask.write{b1, _, v2, c2}: Spec.Ask}
        %Shared.Maybe.same_sound(
          ~Replica.Id,
          ~Replica.Id.same,
          Replica.Id.same_sound,
          v1,
          v2
        )(
          Shared.Bool.and_true_left(
            Shared.Maybe.same(~Replica.Id, ~Replica.Id.same, v1, v2),
            Spec.Content.same(c1, c2)
          )(h2)
        ):
          {Spec.Ask.write{b1, n1, v1, c1} == Spec.Ask.write{b1, n1, _, c2}: Spec.Ask}
        %Content.same_sound(
          c1,
          c2
        )(
          Shared.Bool.and_true_right(
            Shared.Maybe.same(~Replica.Id, ~Replica.Id.same, v1, v2),
            Spec.Content.same(c1, c2)
          )(h2)
        ):
          {Spec.Ask.write{b1, n1, v1, c1} == Spec.Ask.write{b1, n1, v1, _}: Spec.Ask}
        {==}
    case Spec.Ask.set_branch{+b1, +v1} Spec.Ask.set_branch{+b2, +v2}:
      +h =>
        %Shared.String.eq_sound(
          b1,
          b2
        )(Shared.Bool.and_true_left(String.eq(b1, b2), Replica.Id.same(v1, v2))(h)):
          {Spec.Ask.set_branch{b1, v1} == Spec.Ask.set_branch{_, v2}: Spec.Ask}
        %Replica.Id.same_sound(
          v1,
          v2
        )(Shared.Bool.and_true_right(String.eq(b1, b2), Replica.Id.same(v1, v2))(h)):
          {Spec.Ask.set_branch{b1, v1} == Spec.Ask.set_branch{b1, _}: Spec.Ask}
        {==}
    case Spec.Ask.merge{+b1, +v1} Spec.Ask.merge{+b2, +v2}:
      +h =>
        %Shared.String.eq_sound(
          b1,
          b2
        )(Shared.Bool.and_true_left(String.eq(b1, b2), Replica.Id.same(v1, v2))(h)):
          {Spec.Ask.merge{b1, v1} == Spec.Ask.merge{_, v2}: Spec.Ask}
        %Replica.Id.same_sound(
          v1,
          v2
        )(Shared.Bool.and_true_right(String.eq(b1, b2), Replica.Id.same(v1, v2))(h)):
          {Spec.Ask.merge{b1, v1} == Spec.Ask.merge{b1, _}: Spec.Ask}
        {==}
    case Spec.Ask.resolve{+b1, +k1, +n1, +c1} Spec.Ask.resolve{+b2, +k2, +n2, +c2}:
      +h =>
        +r1 = Bool.and(
          Replica.Id.same(k1, k2),
          Bool.and(Resources.Name.same(n1, n2), Spec.Content.same(c1, c2))
        )
        +r2 = Bool.and(Resources.Name.same(n1, n2), Spec.Content.same(c1, c2))
        +h1 = Shared.Bool.and_true_right(String.eq(b1, b2), r1)(h)
        +h2 = Shared.Bool.and_true_right(Replica.Id.same(k1, k2), r2)(h1)
        %Shared.String.eq_sound(b1, b2)(Shared.Bool.and_true_left(String.eq(b1, b2), r1)(h)):
          {Spec.Ask.resolve{b1, k1, n1, c1} == Spec.Ask.resolve{_, k2, n2, c2}: Spec.Ask}
        %Replica.Id.same_sound(k1, k2)(Shared.Bool.and_true_left(Replica.Id.same(k1, k2), r2)(h1)):
          {Spec.Ask.resolve{b1, k1, n1, c1} == Spec.Ask.resolve{b1, _, n2, c2}: Spec.Ask}
        %Resources.Name.same_sound(
          n1,
          n2
        )(Shared.Bool.and_true_left(Resources.Name.same(n1, n2), Spec.Content.same(c1, c2))(h2)):
          {Spec.Ask.resolve{b1, k1, n1, c1} == Spec.Ask.resolve{b1, k1, _, c2}: Spec.Ask}
        %Content.same_sound(
          c1,
          c2
        )(Shared.Bool.and_true_right(Resources.Name.same(n1, n2), Spec.Content.same(c1, c2))(h2)):
          {Spec.Ask.resolve{b1, k1, n1, c1} == Spec.Ask.resolve{b1, k1, n1, _}: Spec.Ask}
        {==}
    case Spec.Ask.mark{+b1, +m1, +t1} Spec.Ask.mark{+b2, +m2, +t2}:
      +h =>
        +r1 = Bool.and(String.eq(m1, m2), String.eq(t1, t2))
        +h1 = Shared.Bool.and_true_right(String.eq(b1, b2), r1)(h)
        %Shared.String.eq_sound(b1, b2)(Shared.Bool.and_true_left(String.eq(b1, b2), r1)(h)):
          {Spec.Ask.mark{b1, m1, t1} == Spec.Ask.mark{_, m2, t2}: Spec.Ask}
        %Shared.String.eq_sound(
          m1,
          m2
        )(Shared.Bool.and_true_left(String.eq(m1, m2), String.eq(t1, t2))(h1)):
          {Spec.Ask.mark{b1, m1, t1} == Spec.Ask.mark{b1, _, t2}: Spec.Ask}
        %Shared.String.eq_sound(
          t1,
          t2
        )(Shared.Bool.and_true_right(String.eq(m1, m2), String.eq(t1, t2))(h1)):
          {Spec.Ask.mark{b1, m1, t1} == Spec.Ask.mark{b1, m1, _}: Spec.Ask}
        {==}
    case Spec.Ask.set_owner{+c1, +ms1} Spec.Ask.set_owner{+c2, +ms2}:
      +h =>
        %Chain.same_sound(
          c1,
          c2
        )(
          Shared.Bool.and_true_left(
            Spec.Chain.same(c1, c2),
            Shared.List.same(~String, ~String.eq, ms1, ms2)
          )(h)
        ):
          {Spec.Ask.set_owner{c1, ms1} == Spec.Ask.set_owner{_, ms2}: Spec.Ask}
        %Shared.List.same_sound(
          ~String,
          ~String.eq,
          ~Shared.String.laws(),
          ms1,
          ms2
        )(
          Shared.Bool.and_true_right(
            Spec.Chain.same(c1, c2),
            Shared.List.same(~String, ~String.eq, ms1, ms2)
          )(h)
        ):
          {Spec.Ask.set_owner{c1, ms1} == Spec.Ask.set_owner{c1, _}: Spec.Ask}
        {==}
    case Spec.Ask.set_group{+g1, +ms1} Spec.Ask.set_group{+g2, +ms2}:
      +h =>
        %Shared.String.eq_sound(
          g1,
          g2
        )(
          Shared.Bool.and_true_left(
            String.eq(g1, g2),
            Shared.List.same(~Spec.Member, ~Spec.Member.same, ms1, ms2)
          )(h)
        ):
          {Spec.Ask.set_group{g1, ms1} == Spec.Ask.set_group{_, ms2}: Spec.Ask}
        %Shared.List.same_sound(
          ~Spec.Member,
          ~Spec.Member.same,
          ~Member.laws(),
          ms1,
          ms2
        )(
          Shared.Bool.and_true_right(
            String.eq(g1, g2),
            Shared.List.same(~Spec.Member, ~Spec.Member.same, ms1, ms2)
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

# the laws of Spec.Ask.same, for the replica
def Ask.laws() -> Shared.Eq.Laws(Spec.Ask, Spec.Ask.same):
  (Ask.same_refl, Ask.same_sound)

# Versions
# --------

# the requests among the cells cs
def Entry.ids(cs: List<&2, Replica.Cell<Replica.Entry<Spec.Ask>>>) -> List<&2, Replica.Id>:
  match cs:
    case Nil{}:
      []
    case Con{Replica.one{Replica.Entry.ask{i, t, q}}, r}:
      i <> Entry.ids(r)
    case Con{c, r}:
      Entry.ids(r)

# every request that s holds
def State.versions(s: Spec.State()) -> List<&2, Replica.Id>:
  Entry.ids(Shared.Trie.values(Replica.Cell<Replica.Entry<Spec.Ask>>, s))

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- the rest is one walk of the list; it costs the same with or without the pick
# the version before v in xs, after prev; none when v is first or not there
def List.before(
  xs: List<&2, Replica.Id>,
  prev: Maybe<&2, Replica.Id>,
  +v: Replica.Id
) -> Maybe<&2, Replica.Id>:
  match xs:
    case Nil{}:
      None{}
    case Con{+x, r}:
      Bool.pick(Maybe<&2, Replica.Id>, Replica.Id.same(x, v), prev, List.before(r, Some{x}, v))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the version before v on its chain c
def Chain.before(s: Spec.State(), c: Spec.Chain, v: Replica.Id) -> Maybe<&2, Replica.Id>:
  List.before(Spec.Node.chain(s, c), None{}, v)

# the versions that the change q of v names besides the one before it
def Ask.refs(q: Spec.Ask) -> List<&2, Replica.Id>:
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
  v: Replica.Id,
  r: Maybe<&2, Replica.Asked<Spec.Ask>>
) -> List<&2, Replica.Id>:
  match r:
    case None{}:
      []
    case Some{Replica.Asked{t, +q}}:
      List.append(
        &2,
        Replica.Id,
        Maybe.default(
          &2,
          List<&2, Replica.Id>,
          Maybe.map(
            &2,
            Replica.Id,
            List<&2, Replica.Id>,
            x => [x],
            Chain.before(s, Spec.Ask.chain(q), v)
          ),
          []
        ),
        Ask.refs(q)
      )

# the versions that v came from
def Version.parents(s: Spec.State(), v: Replica.Id) -> List<&2, Replica.Id>:
  +s = s
  +v = v
  Version.parents.of(s, v, Replica.State.asked(~Spec.Ask, s, v))

# x is v (held), or a version that v came from
def Version.is_from.if(held: Bool, s: Spec.State(), x: Replica.Id, v: Replica.Id) -> Bool:
  match held:
    case True{}:
      True{}
    case False{}:
      Reaches.Reach.in(
        ~Replica.Id,
        ~Spec.State(),
        ~Replica.Id.same,
        ~Version.parents,
        ~State.versions,
        s,
        v,
        x
      )

# x is v, or a version that v came from
def Version.is_from(s: Spec.State(), +x: Replica.Id, +v: Replica.Id) -> Bool:
  Version.is_from.if(Replica.Id.same(x, v), s, x, v)

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- the rest is one walk of the list; it costs the same with or without the pick
# the first version of xs that v came from
def Version.base.go(
  +s: Spec.State(),
  xs: List<&2, Replica.Id>,
  +v: Replica.Id
) -> Maybe<&2, Replica.Id>:
  match xs:
    case Nil{}:
      None{}
    case Con{+x, r}:
      Bool.pick(Maybe<&2, Replica.Id>, Version.is_from(s, x, v), Some{x}, Version.base.go(s, r, v))

# the versions of xs up to v
def List.upto(xs: List<&2, Replica.Id>, +v: Replica.Id) -> List<&2, Replica.Id>:
  match xs:
    case Nil{}:
      []
    case Con{+x, r}:
      x <> Bool.pick(List<&2, Replica.Id>, Replica.Id.same(x, v), [], List.upto(r, v))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the base of a merge of from into the chain c, whose head was ours: the newest
# version of c up to ours that from came from
def Version.base(
  +s: Spec.State(),
  c: Spec.Chain,
  ours: Maybe<&2, Replica.Id>,
  from: Replica.Id
) -> Maybe<&2, Replica.Id>:
  match ours:
    case None{}:
      None{}
    case Some{o}:
      Version.base.go(s, List.reverse(&2, Replica.Id, List.upto(Spec.Node.chain(s, c), o)), from)

# the newer of x and y, once y is known to come from x or not (held)
def Forward.if(held: Bool, s: Spec.State(), +x: Replica.Id, y: Replica.Id) -> Maybe<&2, Replica.Id>:
  match held:
    case True{}:
      Some{y}
    case False{}:
      Shared.Bool.when(Maybe<&2, Replica.Id>, Version.is_from(s, y, x), u => Some{x}, u => None{})

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
def Asked.hits(r: Maybe<&2, Replica.Asked<Spec.Ask>>, n: Resources.Name) -> Bool:
  match r:
    case Some{Replica.Asked{t, Spec.Ask.write{b, m, base, c}}}:
      Resources.Name.same(m, n)
    case Some{Replica.Asked{t, Spec.Ask.resolve{b, k, m, c}}}:
      Resources.Name.same(m, n)
    case _:
      False{}

# the request of v, when there is one
def State.asked.of(s: Spec.State(), v: Maybe<&2, Replica.Id>) -> Maybe<&2, Replica.Asked<Spec.Ask>>:
  match v:
    case None{}:
      None{}
    case Some{i}:
      Replica.State.asked(~Spec.Ask, s, i)

# what a merge keeps of a resource: its bytes or none, or a clash
type Pick is Data:
  Pick.take{bytes: Maybe<&2, Shared.Bytes()>}
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
def Pick.module(m: Maybe<&2, Replica.Id>, px: Spec.Pointer, +py: Spec.Pointer) -> Pick:
  match m:
    case None{}:
      Pick.clash{}
    case Some{k}:
      Pick.take{
        Some{
          Spec.Pointer.show(
            Shared.Bool.when(
              Spec.Pointer,
              Replica.Id.same(k, Spec.Pointer.version(py)),
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
  b: Shared.Bytes(),
  x: Shared.Bytes(),
  y: Shared.Bytes()
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
  b: Maybe<&2, Shared.Bytes()>,
  o: Maybe<&2, Shared.Bytes()>,
  t: Maybe<&2, Shared.Bytes()>
) -> Pick:
  match o t:
    case Some{x} Some{y}:
      Pick.format(f, s, Maybe.default(&2, Shared.Bytes(), b, []), x, y)
    case _ _:
      Pick.clash{}

# the merge of a resource, once both sides are known to agree or not (held)
def Pick.of.same(
  held: Bool,
  f: Formats.Format,
  s: Spec.State(),
  b: Maybe<&2, Shared.Bytes()>,
  o: Maybe<&2, Shared.Bytes()>,
  t: Maybe<&2, Shared.Bytes()>
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
  b: Maybe<&2, Shared.Bytes()>,
  +o: Maybe<&2, Shared.Bytes()>,
  +t: Maybe<&2, Shared.Bytes()>
) -> Pick:
  match held:
    case True{}:
      Pick.take{o}
    case False{}:
      Pick.of.same(Shared.Maybe.same(~Shared.Bytes(), ~Shared.Bytes.is_eq, o, t), f, s, b, o, t)

# the merge of a resource, once ours is known to be the base or not (held)
def Pick.of(
  held: Bool,
  f: Formats.Format,
  s: Spec.State(),
  +b: Maybe<&2, Shared.Bytes()>,
  o: Maybe<&2, Shared.Bytes()>,
  +t: Maybe<&2, Shared.Bytes()>
) -> Pick:
  match held:
    case True{}:
      Pick.take{t}
    case False{}:
      Pick.of.right(Shared.Maybe.same(~Shared.Bytes(), ~Shared.Bytes.is_eq, t, b), f, s, b, o, t)

# what a merge of the base b, ours o and theirs t keeps of a resource in the
# format f
def Pick.merge(
  f: Formats.Format,
  s: Spec.State(),
  +b: Maybe<&2, Shared.Bytes()>,
  +o: Maybe<&2, Shared.Bytes()>,
  t: Maybe<&2, Shared.Bytes()>
) -> Pick:
  Pick.of(Shared.Maybe.same(~Shared.Bytes(), ~Shared.Bytes.is_eq, o, b), f, s, b, o, t)

# the bytes of a merge: ours on a clash
def Pick.kept(p: Pick, o: Maybe<&2, Shared.Bytes()>) -> Maybe<&2, Shared.Bytes()>:
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
  v: Maybe<&2, Replica.Id>,
  +n: Resources.Name,
  r: Maybe<&2, Replica.Asked<Spec.Ask>>,
  hit: Bool
) -> Maybe<&2, Shared.Bytes()>:
  match f v r hit:
    case 0n w m h:
      None{}
    case 1n+e None{} m h:
      None{}
    case 1n+e Some{i} None{} h:
      None{}
    case 1n+e Some{
      i
    } Some{Replica.Asked{t, Spec.Ask.write{b, m, base, Spec.Content.bytes{x}}}} True{}:
      Some{x}
    case 1n+e Some{
      i
    } Some{Replica.Asked{t, Spec.Ask.write{b, m, base, Spec.Content.of{+w}}}} True{}:
      Res.at(
        e,
        s,
        Some{w},
        n,
        Replica.State.asked(~Spec.Ask, s, w),
        Asked.hits(Replica.State.asked(~Spec.Ask, s, w), n)
      )
    case 1n+e Some{
      i
    } Some{Replica.Asked{t, Spec.Ask.resolve{b, k, m, Spec.Content.bytes{x}}}} True{}:
      Some{x}
    case 1n+e Some{i} Some{Replica.Asked{t, Spec.Ask.resolve{b, k, m, Spec.Content.of{+w}}}} True{}:
      Res.at(
        e,
        s,
        Some{w},
        n,
        Replica.State.asked(~Spec.Ask, s, w),
        Asked.hits(Replica.State.asked(~Spec.Ask, s, w), n)
      )
    case 1n+e Some{i} Some{Replica.Asked{t, Spec.Ask.set_branch{b, +to}}} h:
      Res.at(
        e,
        s,
        Some{to},
        n,
        Replica.State.asked(~Spec.Ask, s, to),
        Asked.hits(Replica.State.asked(~Spec.Ask, s, to), n)
      )
    case 1n+e Some{+i} Some{Replica.Asked{t, Spec.Ask.merge{+b, +from}}} h:
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
        Replica.State.asked(~Spec.Ask, s, from),
        Asked.hits(Replica.State.asked(~Spec.Ask, s, from), n)
      )
      Pick.kept(Pick.merge(Formats.Format.of(Resources.Name.path(n)), s, bs, o, fs), o)
    case 1n+e Some{+i} Some{Replica.Asked{t, +q}} h:
      +before = Chain.before(s, Spec.Ask.chain(q), i)
      Res.at(e, s, before, n, State.asked.of(s, before), Asked.hits(State.asked.of(s, before), n))

# the bytes of the resource n at the version v of s
def Res.of(
  +s: Spec.State(),
  +n: Resources.Name,
  +v: Maybe<&2, Replica.Id>
) -> Maybe<&2, Shared.Bytes()>:
  Res.at(
    Replica.State.fuel(~Spec.Ask, s),
    s,
    v,
    n,
    State.asked.of(s, v),
    Asked.hits(State.asked.of(s, v), n)
  )

# the request r names the mark m
def Mark.is(r: Maybe<&2, Replica.Asked<Spec.Ask>>, m: String) -> Bool:
  match r:
    case Some{Replica.Asked{t, Spec.Ask.mark{b, k, x}}}:
      String.eq(k, m)
    case _:
      False{}

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- the rest is one walk of the list; it costs the same with or without the pick
# the version that the first mark m of xs names: the one before it, after prev
def Mark.first(
  +s: Spec.State(),
  xs: List<&2, Replica.Id>,
  prev: Maybe<&2, Replica.Id>,
  +m: String
) -> Maybe<&2, Replica.Id>:
  match xs:
    case Nil{}:
      None{}
    case Con{+x, r}:
      Bool.pick(
        Maybe<&2, Replica.Id>,
        Mark.is(Replica.State.asked(~Spec.Ask, s, x), m),
        prev,
        Mark.first(s, r, Some{x}, m)
      )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the version that the mark m of the branch b names
def Mark.of(+s: Spec.State(), b: String, m: String) -> Maybe<&2, Replica.Id>:
  Mark.first(s, Spec.Node.chain(s, Spec.Chain.branch{b}), None{}, m)

# the version at the point p of s
def Point.version(s: Spec.State(), p: Spec.Point) -> Maybe<&2, Replica.Id>:
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
  v: Maybe<&2, Replica.Id>,
  r: Maybe<&2, Replica.Asked<Spec.Ask>>
) -> List<&2, String>:
  match f v r:
    case 0n w m:
      []
    case 1n+e None{} m:
      []
    case 1n+e Some{i} None{}:
      []
    case 1n+e Some{i} Some{Replica.Asked{t, Spec.Ask.set_branch{b, +to}}}:
      Res.names(e, s, Some{to}, Replica.State.asked(~Spec.Ask, s, to))
    case 1n+e Some{+i} Some{Replica.Asked{t, Spec.Ask.merge{b, +from}}}:
      +ours = Chain.before(s, Spec.Chain.branch{b}, i)
      fs os = Res.names(
        e,
        s,
        Some{from},
        Replica.State.asked(~Spec.Ask, s, from)
      ) Res.names(e, s, ours, State.asked.of(s, ours))
      Shared.union(fs, os)
    case 1n+e Some{+i} Some{Replica.Asked{t, Spec.Ask.write{b, m, base, c}}}:
      +before = Chain.before(s, Spec.Chain.branch{b}, i)
      Shared.union([Resources.Name.show(m)], Res.names(e, s, before, State.asked.of(s, before)))
    case 1n+e Some{+i} Some{Replica.Asked{t, +q}}:
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
  +base: Maybe<&2, Replica.Id>,
  +ours: Maybe<&2, Replica.Id>,
  +from: Replica.Id
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
def Res.of.names(+s: Spec.State(), +v: Maybe<&2, Replica.Id>) -> List<&2, String>:
  Res.names(Replica.State.fuel(~Spec.Ask, s), s, v, State.asked.of(s, v))

# the resources that clash at the merge k, whose request is r
def Merge.clashes(
  +s: Spec.State(),
  k: Replica.Id,
  r: Maybe<&2, Replica.Asked<Spec.Ask>>
) -> List<&2, Resources.Name>:
  match r:
    case Some{Replica.Asked{t, Spec.Ask.merge{+b, +from}}}:
      +ours = Chain.before(s, Spec.Chain.branch{b}, k)
      Res.clashes(
        s,
        Shared.union(Res.of.names(s, Some{from}), Res.of.names(s, ours)),
        Version.base(s, Spec.Chain.branch{b}, ours, from),
        ours,
        from
      )
    case _:
      []

# the text that the request r settles of k
def Merge.settles(r: Maybe<&2, Replica.Asked<Spec.Ask>>, k: Replica.Id) -> List<&2, String>:
  match r:
    case Some{Replica.Asked{t, Spec.Ask.resolve{b, j, n, c}}}:
      List.filter.put(String, Resources.Name.show(n), [], Replica.Id.same(j, k))
    case _:
      []

# the texts that the resolves of k among xs settle
def Merge.settled(+s: Spec.State(), xs: List<&2, Replica.Id>, +k: Replica.Id) -> List<&2, String>:
  match xs:
    case Nil{}:
      []
    case Con{x, r}:
      List.append(
        &2,
        String,
        Merge.settles(Replica.State.asked(~Spec.Ask, s, x), k),
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
        Bool.not(Shared.List.has(~String, ~String.eq, ts, Resources.Name.show(n)))
      )

# the resources that still clash after the merge k, whose request is r
def Merge.left(
  +s: Spec.State(),
  +k: Replica.Id,
  +r: Maybe<&2, Replica.Asked<Spec.Ask>>
) -> List<&2, Resources.Name>:
  match r:
    case Some{Replica.Asked{t, Spec.Ask.merge{+b, from}}}:
      Names.unsettled(
        Merge.clashes(s, k, r),
        Merge.settled(s, Spec.Node.chain(s, Spec.Chain.branch{b}), k)
      )
    case _:
      []

def Spec.Node.conflict(s, k):
  +s = s
  +k = k
  Merge.left(s, k, Replica.State.asked(~Spec.Ask, s, k))

# Groups
# ------

# the chain of the first request of a root, when s holds it (m): a chain
# whose root names a request of another chain does not exist
def Root.chain(m: Maybe<&2, Replica.Asked<Spec.Ask>>) -> Maybe<&2, Spec.Chain>:
  match m:
    case Some{Replica.Asked{t, q}}:
      Some{Spec.Ask.chain(q)}
    case None{}:
      None{}

# the members that the request r sets, else found
def Group.set(
  r: Maybe<&2, Replica.Asked<Spec.Ask>>,
  found: Maybe<&2, List<&2, Spec.Member>>
) -> Maybe<&2, List<&2, Spec.Member>>:
  match r:
    case Some{Replica.Asked{t, Spec.Ask.set_group{g, ms}}}:
      Some{ms}
    case _:
      found

# the members that the last set-group of xs sets, else found
def Group.last(
  +s: Spec.State(),
  xs: List<&2, Replica.Id>,
  found: Maybe<&2, List<&2, Spec.Member>>
) -> Maybe<&2, List<&2, Spec.Member>>:
  match xs:
    case Nil{}:
      found
    case Con{x, r}:
      Group.last(s, r, Group.set(Replica.State.asked(~Spec.Ask, s, x), found))

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
        Bool.not(Shared.List.has(~Spec.Member, ~Spec.Member.same, rest, Spec.Member.group{g}))
      )
    case _:
      rest

# the groups whose roots are among the cells cs of s, as members
def Group.roots(
  +s: Spec.State(),
  cs: List<&2, Replica.Cell<Replica.Entry<Spec.Ask>>>
) -> List<&2, Spec.Member>:
  match cs:
    case Nil{}:
      []
    case Con{Replica.one{Replica.Entry.root{k, i, n}}, r}:
      Group.put(Root.chain(Replica.State.asked(~Spec.Ask, s, i)), Group.roots(s, r))
    case Con{c, r}:
      Group.roots(s, r)

# every group of s, as a member
def Group.all(s: Spec.State()) -> List<&2, Spec.Member>:
  +s = s
  Group.roots(s, Shared.Trie.values(Replica.Cell<Replica.Entry<Spec.Ask>>, s))

def Spec.Node.is_inside(s, m, g):
  Reaches.Reach.in(
    ~Spec.Member,
    ~Spec.State(),
    ~Spec.Member.same,
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
      Shared.union(Group.nodes.of(Group.succ(s, g)), Group.named(s, r))

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

# Answers
# -------

# the change q fits the head h of its chain: the owners may vote for it there
def Spec.Node.fits(s, q, h):
  match q:
    case Spec.Ask.write{b, +n, base, c}:
      +s = s
      Shared.Maybe.same(
        ~Shared.Bytes(),
        ~Shared.Bytes.is_eq,
        Res.of(s, n, Some{h}),
        Res.of(s, n, base)
      )
    case Spec.Ask.set_branch{b, to}:
      Maybe.is_some(&2, Replica.Asked<Spec.Ask>, Replica.State.asked(~Spec.Ask, s, to))
    case Spec.Ask.merge{b, from}:
      Maybe.is_some(&2, Replica.Asked<Spec.Ask>, Replica.State.asked(~Spec.Ask, s, from))
    case Spec.Ask.resolve{b, k, n, c}:
      Shared.List.has(~Resources.Name, ~Resources.Name.same, Spec.Node.conflict(s, k), n)
    case Spec.Ask.mark{b, m, t}:
      Maybe.is_none(&2, Replica.Id, Mark.of(s, b, m))
    case Spec.Ask.set_owner{c, ms}:
      Bool.not(List.is_empty(&2, String, ms))
    case Spec.Ask.set_group{g, ms}:
      Bool.not(Group.loops.any(s, g, ms))

# Written, or Conflicted when the merge k still clashes (left)
def Answer.done.if(left: List<&2, Resources.Name>, i: Replica.Id, k: Replica.Id) -> Spec.Done:
  match left:
    case Nil{}:
      Spec.Done.written{i}
    case Con{n, r}:
      Spec.Done.conflicted{k}

# the answer to the request i in its chain, whose change is q
def Answer.done(s: Spec.State(), +i: Replica.Id, q: Spec.Ask) -> Spec.Done:
  match q:
    case Spec.Ask.merge{b, from}:
      Answer.done.if(Spec.Node.conflict(s, i), i, i)
    case Spec.Ask.resolve{b, +k, n, c}:
      Answer.done.if(Spec.Node.conflict(s, k), i, k)
    case _:
      Spec.Done.written{i}

# the answer to the request i, whose status is st
def Answer.of(
  s: Spec.State(),
  i: Replica.Id,
  st: Replica.Status<Spec.Ask>
) -> Replica.Status<Spec.Done>:
  match st:
    case Replica.Status.done{q}:
      Replica.Status.done{Answer.done(s, i, q)}
    case Replica.Status.pending{}:
      Replica.Status.pending{}
    case Replica.Status.stale{h}:
      Replica.Status.stale{h}
    case Replica.Status.refused{w}:
      Replica.Status.refused{w}
    case Replica.Status.not_seen{}:
      Replica.Status.not_seen{}

def Spec.Node.answer(s, i):
  +s = s
  +i = i
  Answer.of(s, i, Replica.State.status(~Spec.Ask, ~Spec.Ask.view, ~Spec.Node.fits, s, i))

# Changes
# -------
def Spec.Node.ask(n, s, e, q):
  +e = e
  Replica.State.ask(
    ~Spec.Ask,
    ~Spec.Ask.same,
    ~Spec.Ask.view,
    ~Spec.Node.fits,
    n,
    s,
    Spec.Envelope.of(e),
    Spec.Envelope.time(e),
    q
  )

def Spec.Node.vote(n, s):
  Replica.State.vote(~Spec.Ask, ~Spec.Ask.same, ~Spec.Ask.view, ~Spec.Node.fits, n, s)

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
  m: Maybe<&2, Replica.Step>,
  rest: List<&2, Spec.BranchEntry>
) -> List<&2, Spec.BranchEntry>:
  match m:
    case None{}:
      rest
    case Some{Replica.Step{h, ms}}:
      Spec.BranchEntry{b, ms, h} <> rest

# the name of the branch m, then rest
def Branches.put(m: Maybe<&2, Spec.Chain>, rest: List<&2, String>) -> List<&2, String>:
  match m:
    case Some{Spec.Chain.branch{b}}:
      Shared.union([b], rest)
    case _:
      rest

# the names of the branches that some cell of cs of s claims
def Branches.named(
  +s: Spec.State(),
  cs: List<&2, Replica.Cell<Replica.Entry<Spec.Ask>>>
) -> List<&2, String>:
  match cs:
    case Nil{}:
      []
    case Con{Replica.one{Replica.Entry.root{k, i, n}}, r}:
      Branches.put(Root.chain(Replica.State.asked(~Spec.Ask, s, i)), Branches.named(s, r))
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
        Replica.Chain.cursor(~Spec.Ask, ~Spec.Ask.view, s, Spec.Chain.key(Spec.Chain.branch{b})),
        Branches.of(s, r)
      )

def Spec.Node.branches(s):
  +s = s
  Branches.of(s, Branches.named(s, Shared.Trie.values(Replica.Cell<Replica.Entry<Spec.Ask>>, s)))

# the version x, when it changed the resource (held), then rest
def Log.at(
  held: Bool,
  x: Replica.Id,
  r: Maybe<&2, Replica.Asked<Spec.Ask>>,
  rest: List<&2, Spec.LogEntry>
) -> List<&2, Spec.LogEntry>:
  match held r:
    case True{} Some{Replica.Asked{t, q}}:
      Spec.LogEntry{x, t} <> rest
    case h m:
      rest

# the versions of xs, after prev, that changed the resource n
def Log.of(
  +s: Spec.State(),
  +n: Resources.Name,
  xs: List<&2, Replica.Id>,
  prev: Maybe<&2, Replica.Id>
) -> List<&2, Spec.LogEntry>:
  match xs:
    case Nil{}:
      []
    case Con{+x, r}:
      Log.at(
        Bool.not(
          Shared.Maybe.same(
            ~Shared.Bytes(),
            ~Shared.Bytes.is_eq,
            Res.of(s, n, Some{x}),
            Res.of(s, n, prev)
          )
        ),
        x,
        Replica.State.asked(~Spec.Ask, s, x),
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
    Maybe.default(&2, Shared.Bytes(), Spec.Node.content(s, n, a), []),
    Maybe.default(&2, Shared.Bytes(), Spec.Node.content(s, n, b), [])
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
  Uses{state: Spec.State(), head: Maybe<&2, Replica.Id>, names: List<&2, Resources.Name>}

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
def Uses.items(m: Maybe<&2, Shared.Bytes()>) -> List<&2, Shared.Bytes()>:
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
      Resources.Name.at(n, Shared.Bytes.to_text(t)) <> Uses.named(r, n)

# what the resource n imports at the version h of s
def Uses.targets(
  s: Spec.State(),
  h: Maybe<&2, Replica.Id>,
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
        Shared.List.has(~Resources.Name, ~Resources.Name.same, ns, n),
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
    ~Resources.Name.same,
    ~Uses.succ,
    ~Uses.nodes,
    Uses.at(Spec.Uses{s, b, Spec.Node.resources(s, b)}),
    u,
    c
  )

# Touches
# -------

# the resource that the request r wrote: of a write or a resolve
def Wrote.of(r: Maybe<&2, Replica.Asked<Spec.Ask>>) -> Maybe<&2, Resources.Name>:
  match r:
    case Some{Replica.Asked{t, Spec.Ask.write{b, m, base, c}}}:
      Some{m}
    case Some{Replica.Asked{t, Spec.Ask.resolve{b, k, m, c}}}:
      Some{m}
    case _:
      None{}

def Spec.Node.wrote(s, v):
  Wrote.of(Replica.State.asked(~Spec.Ask, s, v))

def Spec.Node.has(s, v, x):
  Version.is_from(s, x, v)

def Spec.Node.version(s, p):
  Point.version(s, p)

# the versions of every branch of s
def Touch.versions(+s: Spec.State()) -> List<&2, Replica.Id>:
  Shared.List.flat(
    ~String,
    ~Replica.Id,
    ~Spec.State(),
    ~(t => x => Spec.Node.chain(t, Spec.Chain.branch{x})),
    Spec.Branch.names(Spec.Node.branches(s)),
    s
  )

# the branch b is a branch of s
def Touch.named(s: Spec.State(), b: String) -> Bool:
  Shared.List.has(~String, ~String.eq, Spec.Branch.names(Spec.Node.branches(s)), b)

# v is a version of a branch of s
def Touch.made(s: Spec.State(), v: Replica.Id) -> Bool:
  Shared.List.has(~Replica.Id, ~Replica.Id.same, Touch.versions(s), v)

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- it runs only after Touch.named holds, so the head is there and both sides are needed
# the branch b lacks the version v
def Touch.lacks(+s: Spec.State(), +b: String, +v: Replica.Id) -> Bool:
  Bool.and(
    Maybe.is_some(&2, Replica.Id, Spec.Node.head(s, b)),
    Bool.not(Spec.Node.has(s, Maybe.default(&2, Replica.Id, Spec.Node.head(s, b), v), v))
  )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the version v wrote the resource c
def Touch.wrote(s: Spec.State(), v: Replica.Id, c: Resources.Name) -> Bool:
  Shared.Maybe.same(~Resources.Name, ~Resources.Name.same, Spec.Node.wrote(s, v), Some{c})

# u is a resource of the branch b
def Touch.held(s: Spec.State(), b: String, u: Resources.Name) -> Bool:
  Shared.List.has(~Resources.Name, ~Resources.Name.same, Spec.Node.resources(s, b), u)

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- the law's own form, for the proofs; Spec.Node.touches runs the lazy one
# the resource u of the branch b is c, or uses it
def Touch.reaches(s: Spec.State(), b: String, +u: Resources.Name, +c: Resources.Name) -> Bool:
  Bool.or(Resources.Name.same(u, c), Spec.Node.uses(s, b, u, c))
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
                w => List.any.if(w => Spec.Node.uses(s, b, u, c), Resources.Name.same(u, c)),
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
  +v: Replica.Id,
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
  v: Replica.Id,
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
def Affects.at(g: Affects, v: Replica.Id) -> List<&2, Spec.Touch>:
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
    ~Replica.Id,
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
  Impact{state: Spec.State(), version: Maybe<&2, Replica.Id>}

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
            Maybe.default(&2, Replica.Id, m, Spec.Touch.version(t)),
            Spec.Touch.version(t)
          ),
          Maybe.is_some(&2, Replica.Id, m)
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
def Notice.same(a: Spec.Notice, b: Spec.Notice) -> Bool:
  match a b:
    case Spec.Notice.versioned{b1, v1} Spec.Notice.versioned{b2, v2}:
      Bool.and(String.eq(b1, b2), Replica.Id.same(v1, v2))
    case Spec.Notice.conflicted{b1, v1} Spec.Notice.conflicted{b2, v2}:
      Bool.and(String.eq(b1, b2), Replica.Id.same(v1, v2))
    case Spec.Notice.touched{t1} Spec.Notice.touched{t2}:
      Spec.Touch.same(t1, t2)
    case Spec.Notice.group_cycle{g1} Spec.Notice.group_cycle{g2}:
      String.eq(g1, g2)
    case _ _:
      False{}

# the versions of the branch b among xs, as notices
def Notice.versions(+b: String, xs: List<&2, Replica.Id>) -> List<&2, Spec.Notice>:
  match xs:
    case Nil{}:
      []
    case Con{x, r}:
      Spec.Notice.versioned{b, x} <> Notice.versions(b, r)

# the merges of the branch b among xs that clashed, as notices
def Notice.conflicts(
  +s: Spec.State(),
  +b: String,
  xs: List<&2, Replica.Id>
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
            Merge.clashes(s, x, Replica.State.asked(~Spec.Ask, s, x))
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
        Bool.not(Shared.List.has(~Spec.Notice, ~Notice.same, old, n))
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
  +i: Replica.Id,
  +t: String,
  +b: String,
  +name: Resources.Name,
  base: Maybe<&2, Replica.Id>,
  x: Shared.Bytes(),
  +v: Replica.Id,
  ecur1: {
    Replica.Chain.cursor(
      ~Spec.Ask,
      ~Spec.Ask.view,
      s1,
      Spec.Chain.key(Spec.Chain.branch{b})
    )
      == Some{Replica.Step{v, [n]}}: Maybe<&2, Replica.Step>
  },
  +f4: {
    Shared.Trie.get(
      Replica.Cell<Replica.Entry<Spec.Ask>>,
      s1,
      Replica.Slot.key(Replica.Slot.vote{n, Spec.Chain.key(Spec.Chain.branch{b}), v})
    )
      == None{}: Maybe<&2, Replica.Cell<Replica.Entry<Spec.Ask>>>
  },
  cell1a: {
    Shared.Trie.get(
      Replica.Cell<Replica.Entry<Spec.Ask>>,
      s1,
      Replica.Slot.key(Replica.Slot.ask{i})
    )
      == Some{
        Replica.one{Replica.Entry.ask{i, t, Spec.Ask.write{b, name, base, Spec.Content.bytes{x}}}}
      }: Maybe<&2, Replica.Cell<Replica.Entry<Spec.Ask>>>
  }
) -> {
  Spec.Node.answer(
    Spec.Node.join(
      s1,
      Shared.Trie.one(
        Replica.Cell<Replica.Entry<Spec.Ask>>,
        Replica.Slot.key(Replica.Slot.vote{n, Spec.Chain.key(Spec.Chain.branch{b}), v}),
        Replica.one{Replica.Entry.vote{i}}
      )
    ),
    i
  )
    == Replica.Status.done{Spec.Done.written{i}}: Replica.Status<Spec.Done>
}
  & {
    Spec.Node.content(
      Spec.Node.join(
        s1,
        Shared.Trie.one(
          Replica.Cell<Replica.Entry<Spec.Ask>>,
          Replica.Slot.key(Replica.Slot.vote{n, Spec.Chain.key(Spec.Chain.branch{b}), v}),
          Replica.one{Replica.Entry.vote{i}}
        )
      ),
      name,
      Spec.Point.at{i}
    )
      == Some{x}: Maybe<&2, Shared.Bytes()>
  }:
  +c = {Spec.Chain.branch{b}: Spec.Chain}
  +q = {Spec.Ask.write{b, name, base, Spec.Content.bytes{x}}: Spec.Ask}
  l = {Replica.Step{v, [n]}: Replica.Step}
  ka = Replica.Slot.key(Replica.Slot.ask{i})
  +kv = Replica.Slot.key(Replica.Slot.vote{n, Spec.Chain.key(c), v})
  ea = {Replica.one{Replica.Entry.ask{i, t, q}}: Replica.Cell<Replica.Entry<Spec.Ask>>}
  +ev = {Replica.one{Replica.Entry.vote{i}}: Replica.Cell<Replica.Entry<Spec.Ask>>}
  +tv = Shared.Trie.one(Replica.Cell<Replica.Entry<Spec.Ask>>, kv, ev)
  s2 = Spec.Node.join(s1, tv)
  a2 = Replica.Cell.agrees_one(
    ~Replica.Entry<Spec.Ask>,
    ~Replica.Entry.same(~Spec.Ask, ~Spec.Ask.same),
    s1,
    kv,
    ev
  )(f4)
  hc2 = Replica.Fresh.claim(~Spec.Ask, ~Spec.Ask.same, s1, kv, Spec.Chain.key(c), ev)({==})
  cell2v = Equal.trans(
    Maybe<&2, Replica.Cell<Replica.Entry<Spec.Ask>>>,
    Shared.Trie.get(Replica.Cell<Replica.Entry<Spec.Ask>>, s2, kv),
    Shared.Trie.pick(~Replica.Cell<Replica.Entry<Spec.Ask>>, ~Replica.Cell.join(~Replica.Entry<Spec.Ask>, ~Replica.Entry.same(~Spec.Ask, ~Spec.Ask.same)), Shared.Trie.get(Replica.Cell<Replica.Entry<Spec.Ask>>, s1, kv), Shared.Trie.get(Replica.Cell<Replica.Entry<Spec.Ask>>, tv, kv)),
    Some{ev},
    Shared.Trie.get_union(~Replica.Cell<Replica.Entry<Spec.Ask>>, ~Replica.Cell.join(~Replica.Entry<Spec.Ask>, ~Replica.Entry.same(~Spec.Ask, ~Spec.Ask.same)), s1, tv, kv),
    %Equal.sym(Maybe<&2, Replica.Cell<Replica.Entry<Spec.Ask>>>, Shared.Trie.get(Replica.Cell<Replica.Entry<Spec.Ask>>, s1, kv), None{}, f4):
      {Shared.Trie.pick(~Replica.Cell<Replica.Entry<Spec.Ask>>, ~Replica.Cell.join(~Replica.Entry<Spec.Ask>, ~Replica.Entry.same(~Spec.Ask, ~Spec.Ask.same)), _, Shared.Trie.get(Replica.Cell<Replica.Entry<Spec.Ask>>, tv, kv)) == Some{ev}: Maybe<&2, Replica.Cell<Replica.Entry<Spec.Ask>>>}
    Shared.Trie.get_one(Replica.Cell<Replica.Entry<Spec.Ask>>, kv, ev))
  +cell2a = Equal.trans(
    Maybe<&2, Replica.Cell<Replica.Entry<Spec.Ask>>>,
    Shared.Trie.get(Replica.Cell<Replica.Entry<Spec.Ask>>, s2, ka),
    Shared.Trie.get(Replica.Cell<Replica.Entry<Spec.Ask>>, s1, ka),
    Some{ea},
    Replica.Fresh.cell(~Spec.Ask, ~Spec.Ask.same, s1, kv, ka, ev)({==}),
    cell1a
  )
  +asked2 = Equal.cong(
    Maybe<&2, Replica.Cell<Replica.Entry<Spec.Ask>>>,
    Maybe<&2, Replica.Asked<Spec.Ask>>,
    z => Replica.Asked.of(~Spec.Ask, Replica.Cell.entry(~Spec.Ask, z)),
    Shared.Trie.get(Replica.Cell<Replica.Entry<Spec.Ask>>, s2, ka),
    Some{ea},
    cell2a
  )
  next2 = Replica.Next.one(
    ~Spec.Ask,
    ~Spec.Ask.view,
    s2,
    Spec.Chain.key(c),
    v,
    n,
    i,
    t,
    q
  )(cell2v)(asked2)(Replica.Key.same_refl(Spec.Chain.key(c)))
  grow = Replica.Grow.fuel(~Spec.Ask, ~Spec.Ask.same, s1, kv, ev)(f4)
  has = Replica.Owner.puts(
    ~Spec.Ask,
    ~Spec.Ask.same,
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
    Replica.Start.of(
      ~Spec.Ask,
      ~Spec.Ask.view,
      s1,
      Spec.Chain.key(c),
      Replica.Chain.root(~Spec.Ask, ~Spec.Ask.view, s1, Spec.Chain.key(c)),
      l
    )(ecur1)
  )
  (
    %Equal.sym(Maybe<&2, Replica.Cell<Replica.Entry<Spec.Ask>>>, Shared.Trie.get(Replica.Cell<Replica.Entry<Spec.Ask>>, s2, ka), Some{ea}, cell2a):
      {Answer.of(s2, i, Replica.Status.of(~Spec.Ask, ~Spec.Ask.view, ~Spec.Node.fits, s2, i, _)) == Replica.Status.done{Spec.Done.written{i}}: Replica.Status<Spec.Done>}
    %Equal.sym(Bool, Shared.List.has(~Replica.Id, ~Replica.Id.same, Spec.Node.chain(s2, c), i), True{}, has):
      {Answer.of(s2, i, Replica.Status.in(~Spec.Ask, ~Spec.Ask.view, ~Spec.Node.fits, s2, q, _)) == Replica.Status.done{Spec.Done.written{i}}: Replica.Status<Spec.Done>}
    {==},
    %Equal.sym(Maybe<&2, Replica.Asked<Spec.Ask>>, Replica.State.asked(~Spec.Ask, s2, i), Some{Replica.Asked{t, q}}, asked2):
      {Res.at(Replica.State.fuel(~Spec.Ask, s2), s2, Some{i}, name, _, Asked.hits(_, name)) == Some{x}: Maybe<&2, Shared.Bytes()>}
    %Equal.sym(Bool, Resources.Name.same(name, name), True{}, Resources.Name.same_refl(name)):
      {Res.at(Replica.State.fuel(~Spec.Ask, s2), s2, Some{i}, name, Some{Replica.Asked{t, q}}, _) == Some{x}: Maybe<&2, Shared.Bytes()>}
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
      +i = {Replica.Id{w, r}: Replica.Id}
      +c = {Spec.Chain.branch{b}: Spec.Chain}
      +q = {Spec.Ask.write{b, name, base, Spec.Content.bytes{x}}: Spec.Ask}
      l = {Replica.Step{v, [n]}: Replica.Step}
      +ka = Replica.Slot.key(Replica.Slot.ask{i})
      +kv = Replica.Slot.key(Replica.Slot.vote{n, Spec.Chain.key(c), v})
      +ea = {Replica.one{Replica.Entry.ask{i, t, q}}: Replica.Cell<Replica.Entry<Spec.Ask>>}
      ev = {Replica.one{Replica.Entry.vote{i}}: Replica.Cell<Replica.Entry<Spec.Ask>>}
      +ta = Shared.Trie.one(Replica.Cell<Replica.Entry<Spec.Ask>>, ka, ea)
      tv = Shared.Trie.one(Replica.Cell<Replica.Entry<Spec.Ask>>, kv, ev)
      +s1 = Spec.Node.join(s, ta)
      s2 = Spec.Node.join(s1, tv)
      +h1 => +h2 => +h3 => +h4 => h5 =>
        +ecur = Replica.Owner.cursor(
          Replica.Chain.cursor(~Spec.Ask, ~Spec.Ask.view, s, Spec.Chain.key(c)),
          n,
          v
        )(h1)(h2)
        +a = Replica.Cell.agrees_one(
          ~Replica.Entry<Spec.Ask>,
          ~Replica.Entry.same(~Spec.Ask, ~Spec.Ask.same),
          s,
          ka,
          ea
        )(h3)
        +hc = Replica.Fresh.claim(~Spec.Ask, ~Spec.Ask.same, s, ka, Spec.Chain.key(c), ea)({==})
        +f4 = Equal.trans(
          Maybe<&2, Replica.Cell<Replica.Entry<Spec.Ask>>>,
          Shared.Trie.get(Replica.Cell<Replica.Entry<Spec.Ask>>, s1, kv),
          Shared.Trie.get(Replica.Cell<Replica.Entry<Spec.Ask>>, s, kv),
          None{},
          Replica.Fresh.cell(~Spec.Ask, ~Spec.Ask.same, s, ka, kv, ea)({==}),
          h4
        )
        +ecur1 = Replica.Stay.cursor(
          ~Spec.Ask,
          ~Spec.Ask.same,
          ~Ask.laws(),
          ~Spec.Ask.view,
          s,
          ta,
          Spec.Chain.key(c),
          a,
          hc,
          l,
          ecur,
          Replica.Next.none(~Spec.Ask, ~Spec.Ask.view, s1, Spec.Chain.key(c), v, n)(f4)
        )
        +base_bytes = Res.of(s, name, base)
        +fits = Equal.trans(
          Bool,
          Spec.Node.fits(s, q, v),
          Shared.Maybe.same(~Shared.Bytes(), ~Shared.Bytes.is_eq, base_bytes, base_bytes),
          True{},
          Equal.cong(
            Maybe<&2, Shared.Bytes()>,
            Bool,
            z => Shared.Maybe.same(~Shared.Bytes(), ~Shared.Bytes.is_eq, z, base_bytes),
            Res.of(s, name, Some{v}),
            base_bytes,
            Equal.trans(
              Maybe<&2, Shared.Bytes()>,
              Res.of(s, name, Some{v}),
              Spec.Node.content(s, name, Spec.Point.head{b}),
              base_bytes,
              Equal.sym(
                Maybe<&2, Shared.Bytes()>,
                Spec.Node.content(s, name, Spec.Point.head{b}),
                Res.of(s, name, Some{v}),
                Equal.cong(
                  Maybe<&2, Replica.Id>,
                  Maybe<&2, Shared.Bytes()>,
                  z => Res.of(s, name, z),
                  Spec.Node.head(s, b),
                  Some{v},
                  h2
                )
              ),
              h5
            )
          ),
          Shared.Maybe.same_refl(
            ~Shared.Bytes(),
            ~Shared.Bytes.is_eq,
            ~Shared.Bytes.laws(),
            base_bytes
          )
        )
        +may = Equal.trans(
          Bool,
          Replica.State.may_vote(~Spec.Ask, n, s, Spec.Chain.key(c), v, [n]),
          Bool.and(
            True{},
            Maybe.is_none(
              &2,
              Replica.Cell<Replica.Entry<Spec.Ask>>,
              Replica.State.cell(~Spec.Ask, s, Replica.Slot.vote{n, Spec.Chain.key(c), v})
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
                Replica.Cell<Replica.Entry<Spec.Ask>>,
                Replica.State.cell(~Spec.Ask, s, Replica.Slot.vote{n, Spec.Chain.key(c), v})
              )
            ),
            Shared.List.has(~String, ~String.eq, [n], n),
            True{},
            Replica.Owners.has(n)
          ),
          Equal.cong(
            Maybe<&2, Replica.Cell<Replica.Entry<Spec.Ask>>>,
            Bool,
            z => Maybe.is_none(&2, Replica.Cell<Replica.Entry<Spec.Ask>>, z),
            Replica.State.cell(~Spec.Ask, s, Replica.Slot.vote{n, Spec.Chain.key(c), v}),
            None{},
            h4
          )
        )
        +ask = Equal.trans(
          Spec.State(),
          Spec.Node.ask(n, s, Spec.Envelope{r, w, t}, q),
          Replica.State.ask.root(
            ~Spec.Ask,
            ~Spec.Ask.same,
            ~Spec.Ask.view,
            ~Spec.Node.fits,
            n,
            s,
            s1,
            i,
            q,
            Replica.State.claim(~Spec.Ask, s, Spec.Chain.key(c))
          ),
          s2,
          Equal.cong(
            Maybe<&2, Replica.Cell<Replica.Entry<Spec.Ask>>>,
            Spec.State(),
            z => Replica.State.ask.fresh(
              ~Spec.Ask,
              ~Spec.Ask.same,
              ~Spec.Ask.view,
              ~Spec.Node.fits,
              n,
              s,
              i,
              t,
              q,
              z
            ),
            Replica.State.cell(~Spec.Ask, s, Replica.Slot.ask{i}),
            None{},
            h3
          ),
          Equal.trans(
            Spec.State(),
            Replica.State.ask.root(
              ~Spec.Ask,
              ~Spec.Ask.same,
              ~Spec.Ask.view,
              ~Spec.Node.fits,
              n,
              s,
              s1,
              i,
              q,
              Replica.State.claim(~Spec.Ask, s, Spec.Chain.key(c))
            ),
            Replica.State.ask.at(
              ~Spec.Ask,
              ~Spec.Ask.same,
              ~Spec.Ask.view,
              ~Spec.Node.fits,
              n,
              s,
              s1,
              i,
              q,
              Replica.Chain.cursor(~Spec.Ask, ~Spec.Ask.view, s, Spec.Chain.key(c))
            ),
            s2,
            Replica.Owner.ask(
              ~Spec.Ask,
              ~Spec.Ask.same,
              ~Spec.Ask.view,
              ~Spec.Node.fits,
              n,
              s,
              i,
              t,
              q,
              Replica.State.claim(~Spec.Ask, s, Spec.Chain.key(c)),
              Replica.Claim.of(
                ~Spec.Ask,
                ~Spec.Ask.view,
                s,
                Spec.Chain.key(c),
                Replica.State.claim(~Spec.Ask, s, Spec.Chain.key(c)),
                {==},
                l
              )(ecur)
            ),
            Equal.trans(
              Spec.State(),
              Replica.State.ask.at(
                ~Spec.Ask,
                ~Spec.Ask.same,
                ~Spec.Ask.view,
                ~Spec.Node.fits,
                n,
                s,
                s1,
                i,
                q,
                Replica.Chain.cursor(~Spec.Ask, ~Spec.Ask.view, s, Spec.Chain.key(c))
              ),
              Replica.State.ask.at(
                ~Spec.Ask,
                ~Spec.Ask.same,
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
                Maybe<&2, Replica.Step>,
                Spec.State(),
                z => Replica.State.ask.at(
                  ~Spec.Ask,
                  ~Spec.Ask.same,
                  ~Spec.Ask.view,
                  ~Spec.Node.fits,
                  n,
                  s,
                  s1,
                  i,
                  q,
                  z
                ),
                Replica.Chain.cursor(~Spec.Ask, ~Spec.Ask.view, s, Spec.Chain.key(c)),
                Some{l},
                ecur
              ),
              Equal.cong(
                Bool,
                Spec.State(),
                z => Bool.pick(Spec.State(), z, Replica.State.put(~Spec.Ask, ~Spec.Ask.same, s1, Replica.Slot.vote{n, Spec.Chain.key(c), v}, Replica.Entry.vote{i}), s1),
                Bool.and(Replica.State.may_vote(~Spec.Ask, n, s, Spec.Chain.key(c), v, [n]), Spec.Node.fits(s, q, v)),
                True{},
                %Equal.sym(Bool, Replica.State.may_vote(~Spec.Ask, n, s, Spec.Chain.key(c), v, [n]), True{}, may): {Bool.and(_, Spec.Node.fits(s, q, v)) == True{}: Bool}
                fits)
            )
          )
        )
        +cell1a = Equal.trans(
          Maybe<&2, Replica.Cell<Replica.Entry<Spec.Ask>>>,
          Shared.Trie.get(Replica.Cell<Replica.Entry<Spec.Ask>>, s1, ka),
          Shared.Trie.pick(~Replica.Cell<Replica.Entry<Spec.Ask>>, ~Replica.Cell.join(~Replica.Entry<Spec.Ask>, ~Replica.Entry.same(~Spec.Ask, ~Spec.Ask.same)), Shared.Trie.get(Replica.Cell<Replica.Entry<Spec.Ask>>, s, ka), Shared.Trie.get(Replica.Cell<Replica.Entry<Spec.Ask>>, ta, ka)),
          Some{ea},
          Shared.Trie.get_union(~Replica.Cell<Replica.Entry<Spec.Ask>>, ~Replica.Cell.join(~Replica.Entry<Spec.Ask>, ~Replica.Entry.same(~Spec.Ask, ~Spec.Ask.same)), s, ta, ka),
          %Equal.sym(Maybe<&2, Replica.Cell<Replica.Entry<Spec.Ask>>>, Shared.Trie.get(Replica.Cell<Replica.Entry<Spec.Ask>>, s, ka), None{}, h3):
            {Shared.Trie.pick(~Replica.Cell<Replica.Entry<Spec.Ask>>, ~Replica.Cell.join(~Replica.Entry<Spec.Ask>, ~Replica.Entry.same(~Spec.Ask, ~Spec.Ask.same)), _, Shared.Trie.get(Replica.Cell<Replica.Entry<Spec.Ask>>, ta, ka)) == Some{ea}: Maybe<&2, Replica.Cell<Replica.Entry<Spec.Ask>>>}
          Shared.Trie.get_one(Replica.Cell<Replica.Entry<Spec.Ask>>, ka, ea))
        %Equal.sym(Spec.State(), Spec.Node.ask(n, s, Spec.Envelope{r, w, t}, q), s2, ask):
          (
            {
              Spec.Node.answer(
                _,
                i
              )
                == Replica.Status.done{Spec.Done.written{i}}: Replica.Status<Spec.Done>
            }
              & {Spec.Node.content(_, name, Spec.Point.at{i}) == Some{x}: Maybe<&2, Shared.Bytes()>}
          )
        Written.at(n, s1, i, t, b, name, base, x, v, ecur1, f4, cell1a)
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# Forward laws
# ------------

# a lazy choice of x or none is the eager one
def Forward.ours_pick(
  b: Bool,
  x: Replica.Id
) -> {
  Shared.Bool.when(
    Maybe<&2, Replica.Id>,
    b,
    u => Some{x},
    u => None{}
  )
    == Bool.pick(Maybe<&2, Replica.Id>, b, Some{x}, None{}): Maybe<&2, Replica.Id>
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
  +x: Replica.Id,
  y: Replica.Id
) -> {
  Forward.if(
    held,
    s,
    x,
    y
  )
    == Bool.pick(
      Maybe<&2, Replica.Id>,
      held,
      Some{y},
      Bool.pick(Maybe<&2, Replica.Id>, Version.is_from(s, y, x), Some{x}, None{})
    ): Maybe<&2, Replica.Id>
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
    Shared.List.has(~Resources.Name, ~Resources.Name.same, Spec.Uses.names(g), n),
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
      ~Resources.Name.same,
      ~(
        +g => +n => Shared.Bool.when(
          List<&2, Resources.Name>,
          Shared.List.has(~Resources.Name, ~Resources.Name.same, Spec.Uses.names(g), n),
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
      ~Resources.Name.same,
      ~(
        +g => +n => Shared.Bool.when(
          List<&2, Resources.Name>,
          Shared.List.has(~Resources.Name, ~Resources.Name.same, Spec.Uses.names(g), n),
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
    Resources.Name.same(u, c),
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
    List.any.if(w => Spec.Node.uses(s, b, u, c), Resources.Name.same(u, c))
  )

# Touch.same is True only for equal touches
def Touch.same_sound(
  a: Spec.Touch,
  b: Spec.Touch
) -> {Spec.Touch.same(a, b) == True{}: Bool} -> {a == b: Spec.Touch}:
  match a b:
    case Spec.Touch{+v1, +c1, +b1, +u1} Spec.Touch{+v2, +c2, +b2, +u2}:
      +h =>
        +r1 = Bool.and(
          Resources.Name.same(c1, c2),
          Bool.and(String.eq(b1, b2), Resources.Name.same(u1, u2))
        )
        +r2 = Bool.and(String.eq(b1, b2), Resources.Name.same(u1, u2))
        +h1 = Shared.Bool.and_true_right(Replica.Id.same(v1, v2), r1)(h)
        +h2 = Shared.Bool.and_true_right(Resources.Name.same(c1, c2), r2)(h1)
        %Equal.sym(
          Replica.Id,
          v1,
          v2,
          Replica.Id.same_sound(v1, v2)(Shared.Bool.and_true_left(Replica.Id.same(v1, v2), r1)(h))
        ):
          {Spec.Touch{_, c1, b1, u1} == Spec.Touch{v2, c2, b2, u2}: Spec.Touch}
        %Equal.sym(
          Resources.Name,
          c1,
          c2,
          Resources.Name.same_sound(
            c1,
            c2
          )(Shared.Bool.and_true_left(Resources.Name.same(c1, c2), r2)(h1))
        ): {Spec.Touch{v2, _, b1, u1} == Spec.Touch{v2, c2, b2, u2}: Spec.Touch}
        %Equal.sym(
          String,
          b1,
          b2,
          Shared.String.eq_sound(
            b1,
            b2
          )(Shared.Bool.and_true_left(String.eq(b1, b2), Resources.Name.same(u1, u2))(h2))
        ): {Spec.Touch{v2, c2, _, u1} == Spec.Touch{v2, c2, b2, u2}: Spec.Touch}
        %Equal.sym(
          Resources.Name,
          u1,
          u2,
          Resources.Name.same_sound(
            u1,
            u2
          )(Shared.Bool.and_true_right(String.eq(b1, b2), Resources.Name.same(u1, u2))(h2))
        ): {Spec.Touch{v2, c2, b2, _} == Spec.Touch{v2, c2, b2, u2}: Spec.Touch}
        {==}

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Touch.same is True for a touch and itself
def Touch.same_refl(a: Spec.Touch) -> {Spec.Touch.same(a, a) == True{}: Bool}:
  match a:
    case Spec.Touch{+v, +c, +b, +u}:
      Shared.Bool.and_both(
        Replica.Id.same(v, v),
        Bool.and(Resources.Name.same(c, c), Bool.and(String.eq(b, b), Resources.Name.same(u, u)))
      )(
        Replica.Id.same_refl(v)
      )(
        Shared.Bool.and_both(
          Resources.Name.same(c, c),
          Bool.and(String.eq(b, b), Resources.Name.same(u, u))
        )(
          Resources.Name.same_refl(c)
        )(
          Shared.Bool.and_both(
            String.eq(b, b),
            Resources.Name.same(u, u)
          )(Shared.String.eq_refl(b))(Resources.Name.same_refl(u))
        )
      )

# the laws of Spec.Touch.same
def Touch.laws() -> Shared.Eq.Laws(Spec.Touch, Spec.Touch.same):
  (Touch.same_refl, Touch.same_sound)

# two touches that differ at most in the resource used are the same as those
# resources are
def Touch.same_at(
  v: Replica.Id,
  c: Resources.Name,
  b: String,
  x: Resources.Name,
  u: Resources.Name
) -> {
  Spec.Touch.same(Spec.Touch{v, c, b, x}, Spec.Touch{v, c, b, u}) == Resources.Name.same(x, u): Bool
}:
  %Equal.sym(Bool, Replica.Id.same(v, v), True{}, Replica.Id.same_refl(v)):
    {
      Bool.and(
        _,
        Bool.and(Resources.Name.same(c, c), Bool.and(String.eq(b, b), Resources.Name.same(x, u)))
      )
        == Resources.Name.same(x, u): Bool
    }
  %Equal.sym(Bool, Resources.Name.same(c, c), True{}, Resources.Name.same_refl(c)):
    {
      Bool.and(
        _,
        Bool.and(String.eq(b, b), Resources.Name.same(x, u))
      )
        == Resources.Name.same(x, u): Bool
    }
  %Equal.sym(Bool, String.eq(b, b), True{}, Shared.String.eq_refl(b)):
    {Bool.and(_, Resources.Name.same(x, u)) == Resources.Name.same(x, u): Bool}
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
      w => Shared.List.has(~Resources.Name, ~Resources.Name.same, r, u),
      hit
    )
      == True{}: Bool
  },
  ih: {
    Shared.List.has(~Resources.Name, ~Resources.Name.same, r, u) == True{}: Bool
  } -> {Shared.List.has(~Spec.Touch, ~Spec.Touch.same, ts, t) == True{}: Bool}
) -> {List.any.if(w => Shared.List.has(~Spec.Touch, ~Spec.Touch.same, ts, t), hit) == True{}: Bool}:
  match hit:
    case True{}:
      {==}
    case False{}:
      ih(h)

# a resource u of us gives the touch of u
def Touch.each_has(
  us: List<&2, Resources.Name>,
  +v: Replica.Id,
  +c: Resources.Name,
  +b: String,
  +u: Resources.Name
) -> {
  Shared.List.has(~Resources.Name, ~Resources.Name.same, us, u) == True{}: Bool
} -> {
  Shared.List.has(
    ~Spec.Touch,
    ~Spec.Touch.same,
    Touch.each(us, v, c, b),
    Spec.Touch{v, c, b, u}
  )
    == True{}: Bool
}:
  match us:
    case Nil{}:
      h => Empty.absurd(
        {
          Shared.List.has(
            ~Spec.Touch,
            ~Spec.Touch.same,
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
          Spec.Touch.same(Spec.Touch{v, c, b, x}, Spec.Touch{v, c, b, u}),
          Resources.Name.same(x, u),
          Touch.same_at(v, c, b, x, u)
        ): {
          List.any.if(
            w => Shared.List.has(
              ~Spec.Touch,
              ~Spec.Touch.same,
              Touch.each(r, v, c, b),
              Spec.Touch{v, c, b, u}
            ),
            _
          )
            == True{}: Bool
        }
        Touch.each_has.at(
          Resources.Name.same(x, u),
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
  v: Replica.Id,
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
  +v: Replica.Id,
  +c: Resources.Name,
  +d: String,
  +u: Resources.Name
) -> {
  Spec.Node.touches(s, Spec.Touch{v, c, d, u}) == True{}: Bool
} -> {
  Shared.List.has(
    ~Spec.Touch,
    ~Spec.Touch.same,
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
    +ew = Shared.Maybe.same_sound(
      ~Resources.Name,
      ~Resources.Name.same,
      Resources.Name.same_sound,
      Spec.Node.wrote(s, v),
      Some{c}
    )(Shared.Bool.and_true_left(hd, Bool.and(he, hf))(h3))
    Shared.List.has_flat(
      ~Replica.Id,
      ~Spec.Touch,
      ~Affects,
      ~Replica.Id.same,
      ~Spec.Touch.same,
      ~Affects.at,
      ~Replica.Id.laws(),
      Touch.versions(s),
      Affects.of(s, d),
      v,
      Spec.Touch{v, c, d, u}
    )(Shared.Bool.and_true_left(hb, Bool.and(hc, Bool.and(hd, Bool.and(he, hf))))(h1))(
      %Equal.sym(Maybe<&2, Resources.Name>, Spec.Node.wrote(s, v), Some{c}, ew): {Shared.List.has(~Spec.Touch, ~Spec.Touch.same, Touch.of(_, v, d, Spec.Node.resources(s, d)), Spec.Touch{v, c, d, u}) == True{}: Bool}
      Touch.each_has(Spec.Node.resources(s, d), v, c, d, u)(Shared.Bool.and_true_left(he, hf)(Shared.Bool.and_true_right(hd, Bool.and(he, hf))(h3))))

# a touch of the branch b that holds may hold of b
def Affects.complete(
  +s: Spec.State(),
  +b: String,
  t: Spec.Touch
) -> {
  Bool.and(String.eq(Spec.Touch.branch(t), b), Spec.Node.touches(s, t)) == True{}: Bool
} -> {Shared.List.has(~Spec.Touch, ~Spec.Touch.same, Affects.cands(s, b), t) == True{}: Bool}:
  match t:
    case Spec.Touch{+v, +c, +d, +u}:
      +h =>
        %Shared.String.eq_sound(
          d,
          b
        )(
          Shared.Bool.and_true_left(
            String.eq(d, b),
            Spec.Node.touches(s, Spec.Touch{v, c, d, u})
          )(h)
        ): {
          Shared.List.has(
            ~Spec.Touch,
            ~Spec.Touch.same,
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
    {Shared.List.has(~Spec.Touch, ~Spec.Touch.same, Spec.Node.affects(s, b), t) == _: Bool}
  Shared.List.keep_exactly(
    ~Spec.Touch,
    ~Affects,
    ~Spec.Touch.same,
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
} -> {Shared.List.has(~Spec.Touch, ~Spec.Touch.same, Impact.cands(s), t) == True{}: Bool}:
  match t:
    case Spec.Touch{+v, +c, +d, +u}:
      +ht =>
        Shared.List.has_flat(
          ~String,
          ~Spec.Touch,
          ~Spec.State(),
          ~String.eq,
          ~Spec.Touch.same,
          ~Affects.cands,
          ~Shared.String.laws(),
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
  +i = Maybe.is_some(&2, Replica.Id, m)
  +o = Spec.Node.has(
    s,
    Maybe.default(&2, Replica.Id, m, Spec.Touch.version(t)),
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
    {Shared.List.has(~Spec.Touch, ~Spec.Touch.same, Spec.Node.impact(s, p), t) == _: Bool}
  Shared.List.keep_exactly(
    ~Spec.Touch,
    ~Impact,
    ~Spec.Touch.same,
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
  em: {Spec.Member.same(m, Spec.Member.group{h}) == hit: Bool},
  hm: {
    List.any.if(
      u => Shared.List.has(~Spec.Member, ~Spec.Member.same, r, Spec.Member.group{h}),
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
    Shared.List.has(~Spec.Member, ~Spec.Member.same, r, Spec.Member.group{h}) == True{}: Bool
  } -> {Group.loops.any(s, g, r) == True{}: Bool}
) -> {List.any.if(u => Group.loops.any(s, g, r), Group.loops(s, g, m)) == True{}: Bool}:
  match hit:
    case True{}:
      %Equal.sym(
        Spec.Member,
        m,
        Spec.Member.group{h},
        Member.same_sound(m, Spec.Member.group{h})(em)
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
  Shared.List.has(~Spec.Member, ~Spec.Member.same, ms, Spec.Member.group{h}) == True{}: Bool
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
          Spec.Member.same(m, Spec.Member.group{h}),
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
