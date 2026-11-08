import Base
import ../../shared/bools.bend as Bools
import ../../shared/bytes.bend as Octets
import ../../shared/cells.bend as Cells
import ../../shared/formats.bend as Formats
import ../../shared/lists.bend as Lists
import ../../shared/maybes.bend as Maybes
import ../../shared/nats.bend as Nats
import ../../shared/quorum.bend as Quorums
import ../../shared/reach.bend as Reaches
import ../../shared/resources.bend as Resources
import ../../shared/shared.bend as Shared
import ../../shared/strings.bend as Strings
import ../../shared/tries.bend as Tries
import ./spec.bend as Spec

# The pure core of a Vend Node.

# Equality
# --------

# String.eq is True only for equal texts. String.eq_sound takes its texts as
# +a and +b; a template that wants a sound check takes plain ones
def Text.sound(a: String, b: String) -> {String.eq(a, b) == True{}: Bool} -> {a == b: String}:
  Strings.String.eq_sound(a, b)

# Id.same is True for a request and itself
def Id.same_refl(a: Spec.Id) -> {Spec.Id.same(a, a) == True{}: Bool}:
  match a:
    case Spec.Id{+w, +r}:
      Bools.Bool.and_both(
        String.eq(w, w),
        String.eq(r, r)
      )(Strings.String.eq_refl(w))(Strings.String.eq_refl(r))

# Id.same is True only for equal requests
def Id.same_sound(
  a: Spec.Id,
  b: Spec.Id
) -> {Spec.Id.same(a, b) == True{}: Bool} -> {a == b: Spec.Id}:
  match a b:
    case Spec.Id{+w1, +r1} Spec.Id{+w2, +r2}:
      +h =>
        %Strings.String.eq_sound(
          w1,
          w2
        )(Bools.Bool.and_true_left(String.eq(w1, w2), String.eq(r1, r2))(h)):
          {Spec.Id{w1, r1} == Spec.Id{_, r2}: Spec.Id}
        %Strings.String.eq_sound(
          r1,
          r2
        )(Bools.Bool.and_true_right(String.eq(w1, w2), String.eq(r1, r2))(h)):
          {Spec.Id{w1, r1} == Spec.Id{w1, _}: Spec.Id}
        {==}

# Chain.same is True for a chain and itself
def Chain.same_refl(a: Spec.Chain) -> {Spec.Chain.same(a, a) == True{}: Bool}:
  match a:
    case Spec.Chain.branch{x}:
      Strings.String.eq_refl(x)
    case Spec.Chain.group{x}:
      Strings.String.eq_refl(x)

# Chain.same is True only for equal chains
def Chain.same_sound(
  a: Spec.Chain,
  b: Spec.Chain
) -> {Spec.Chain.same(a, b) == True{}: Bool} -> {a == b: Spec.Chain}:
  match a b:
    case Spec.Chain.branch{x} Spec.Chain.branch{y}:
      h =>
        %Strings.String.eq_sound(
          x,
          y
        )(h): {Spec.Chain.branch{x} == Spec.Chain.branch{_}: Spec.Chain}
        {==}
    case Spec.Chain.group{x} Spec.Chain.group{y}:
      h =>
        %Strings.String.eq_sound(x, y)(h): {Spec.Chain.group{x} == Spec.Chain.group{_}: Spec.Chain}
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
      Strings.String.eq_refl(x)
    case Spec.Member.group{x}:
      Strings.String.eq_refl(x)

# Member.same is True only for equal members
def Member.same_sound(
  a: Spec.Member,
  b: Spec.Member
) -> {Spec.Member.same(a, b) == True{}: Bool} -> {a == b: Spec.Member}:
  match a b:
    case Spec.Member.node{x} Spec.Member.node{y}:
      h =>
        %Strings.String.eq_sound(x, y)(h): {Spec.Member.node{x} == Spec.Member.node{_}: Spec.Member}
        {==}
    case Spec.Member.group{x} Spec.Member.group{y}:
      h =>
        %Strings.String.eq_sound(
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

# Content.same is True for a content and itself
def Content.same_refl(a: Spec.Content) -> {Spec.Content.same(a, a) == True{}: Bool}:
  match a:
    case Spec.Content.bytes{x}:
      Octets.Bytes.is_eq_refl(x)
    case Spec.Content.of{v}:
      Id.same_refl(v)

# Content.same is True only for equal contents
def Content.same_sound(
  a: Spec.Content,
  b: Spec.Content
) -> {Spec.Content.same(a, b) == True{}: Bool} -> {a == b: Spec.Content}:
  match a b:
    case Spec.Content.bytes{x} Spec.Content.bytes{y}:
      h =>
        %Octets.Bytes.is_eq_sound(
          x,
          y
        )(h): {Spec.Content.bytes{x} == Spec.Content.bytes{_}: Spec.Content}
        {==}
    case Spec.Content.of{x} Spec.Content.of{y}:
      h =>
        %Id.same_sound(x, y)(h): {Spec.Content.of{x} == Spec.Content.of{_}: Spec.Content}
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
      Bools.Bool.and_both(
        String.eq(b, b),
        Bool.and(
          Resources.Name.same(n, n),
          Bool.and(Maybes.Maybe.same(~Spec.Id, ~Spec.Id.same, v, v), Spec.Content.same(c, c))
        )
      )(
        Strings.String.eq_refl(b)
      )(
        Bools.Bool.and_both(
          Resources.Name.same(n, n),
          Bool.and(Maybes.Maybe.same(~Spec.Id, ~Spec.Id.same, v, v), Spec.Content.same(c, c))
        )(
          Resources.Name.same_refl(n)
        )(
          Bools.Bool.and_both(
            Maybes.Maybe.same(~Spec.Id, ~Spec.Id.same, v, v),
            Spec.Content.same(c, c)
          )(Maybes.Maybe.same_refl(~Spec.Id, ~Spec.Id.same, ~Id.same_refl, v))(Content.same_refl(c))
        )
      )
    case Spec.Ask.set_branch{+b, +v}:
      Bools.Bool.and_both(
        String.eq(b, b),
        Spec.Id.same(v, v)
      )(Strings.String.eq_refl(b))(Id.same_refl(v))
    case Spec.Ask.merge{+b, +v}:
      Bools.Bool.and_both(
        String.eq(b, b),
        Spec.Id.same(v, v)
      )(Strings.String.eq_refl(b))(Id.same_refl(v))
    case Spec.Ask.resolve{+b, +k, +n, +c}:
      Bools.Bool.and_both(
        String.eq(b, b),
        Bool.and(Spec.Id.same(k, k), Bool.and(Resources.Name.same(n, n), Spec.Content.same(c, c)))
      )(
        Strings.String.eq_refl(b)
      )(
        Bools.Bool.and_both(
          Spec.Id.same(k, k),
          Bool.and(Resources.Name.same(n, n), Spec.Content.same(c, c))
        )(
          Id.same_refl(k)
        )(
          Bools.Bool.and_both(
            Resources.Name.same(n, n),
            Spec.Content.same(c, c)
          )(Resources.Name.same_refl(n))(Content.same_refl(c))
        )
      )
    case Spec.Ask.mark{+b, +m, +t}:
      Bools.Bool.and_both(
        String.eq(b, b),
        Bool.and(String.eq(m, m), String.eq(t, t))
      )(
        Strings.String.eq_refl(b)
      )(
        Bools.Bool.and_both(
          String.eq(m, m),
          String.eq(t, t)
        )(Strings.String.eq_refl(m))(Strings.String.eq_refl(t))
      )
    case Spec.Ask.set_owner{+c, +ms}:
      Bools.Bool.and_both(
        Spec.Chain.same(c, c),
        Lists.List.same(~String, ~String.eq, ms, ms)
      )(Chain.same_refl(c))(Lists.List.same_refl(~String, ~String.eq, ~Strings.String.eq_refl, ms))
    case Spec.Ask.set_group{+g, +ms}:
      Bools.Bool.and_both(
        String.eq(g, g),
        Lists.List.same(~Spec.Member, ~Spec.Member.same, ms, ms)
      )(
        Strings.String.eq_refl(g)
      )(Lists.List.same_refl(~Spec.Member, ~Spec.Member.same, ~Member.same_refl, ms))

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
          Bool.and(Maybes.Maybe.same(~Spec.Id, ~Spec.Id.same, v1, v2), Spec.Content.same(c1, c2))
        )
        +r2 = Bool.and(
          Maybes.Maybe.same(~Spec.Id, ~Spec.Id.same, v1, v2),
          Spec.Content.same(c1, c2)
        )
        +h1 = Bools.Bool.and_true_right(String.eq(b1, b2), r1)(h)
        +h2 = Bools.Bool.and_true_right(Resources.Name.same(n1, n2), r2)(h1)
        %Strings.String.eq_sound(b1, b2)(Bools.Bool.and_true_left(String.eq(b1, b2), r1)(h)):
          {Spec.Ask.write{b1, n1, v1, c1} == Spec.Ask.write{_, n2, v2, c2}: Spec.Ask}
        %Resources.Name.same_sound(
          n1,
          n2
        )(Bools.Bool.and_true_left(Resources.Name.same(n1, n2), r2)(h1)):
          {Spec.Ask.write{b1, n1, v1, c1} == Spec.Ask.write{b1, _, v2, c2}: Spec.Ask}
        %Maybes.Maybe.same_sound(
          ~Spec.Id,
          ~Spec.Id.same,
          Id.same_sound,
          v1,
          v2
        )(
          Bools.Bool.and_true_left(
            Maybes.Maybe.same(~Spec.Id, ~Spec.Id.same, v1, v2),
            Spec.Content.same(c1, c2)
          )(h2)
        ):
          {Spec.Ask.write{b1, n1, v1, c1} == Spec.Ask.write{b1, n1, _, c2}: Spec.Ask}
        %Content.same_sound(
          c1,
          c2
        )(
          Bools.Bool.and_true_right(
            Maybes.Maybe.same(~Spec.Id, ~Spec.Id.same, v1, v2),
            Spec.Content.same(c1, c2)
          )(h2)
        ):
          {Spec.Ask.write{b1, n1, v1, c1} == Spec.Ask.write{b1, n1, v1, _}: Spec.Ask}
        {==}
    case Spec.Ask.set_branch{+b1, +v1} Spec.Ask.set_branch{+b2, +v2}:
      +h =>
        %Strings.String.eq_sound(
          b1,
          b2
        )(Bools.Bool.and_true_left(String.eq(b1, b2), Spec.Id.same(v1, v2))(h)):
          {Spec.Ask.set_branch{b1, v1} == Spec.Ask.set_branch{_, v2}: Spec.Ask}
        %Id.same_sound(
          v1,
          v2
        )(Bools.Bool.and_true_right(String.eq(b1, b2), Spec.Id.same(v1, v2))(h)):
          {Spec.Ask.set_branch{b1, v1} == Spec.Ask.set_branch{b1, _}: Spec.Ask}
        {==}
    case Spec.Ask.merge{+b1, +v1} Spec.Ask.merge{+b2, +v2}:
      +h =>
        %Strings.String.eq_sound(
          b1,
          b2
        )(Bools.Bool.and_true_left(String.eq(b1, b2), Spec.Id.same(v1, v2))(h)):
          {Spec.Ask.merge{b1, v1} == Spec.Ask.merge{_, v2}: Spec.Ask}
        %Id.same_sound(
          v1,
          v2
        )(Bools.Bool.and_true_right(String.eq(b1, b2), Spec.Id.same(v1, v2))(h)):
          {Spec.Ask.merge{b1, v1} == Spec.Ask.merge{b1, _}: Spec.Ask}
        {==}
    case Spec.Ask.resolve{+b1, +k1, +n1, +c1} Spec.Ask.resolve{+b2, +k2, +n2, +c2}:
      +h =>
        +r1 = Bool.and(
          Spec.Id.same(k1, k2),
          Bool.and(Resources.Name.same(n1, n2), Spec.Content.same(c1, c2))
        )
        +r2 = Bool.and(Resources.Name.same(n1, n2), Spec.Content.same(c1, c2))
        +h1 = Bools.Bool.and_true_right(String.eq(b1, b2), r1)(h)
        +h2 = Bools.Bool.and_true_right(Spec.Id.same(k1, k2), r2)(h1)
        %Strings.String.eq_sound(b1, b2)(Bools.Bool.and_true_left(String.eq(b1, b2), r1)(h)):
          {Spec.Ask.resolve{b1, k1, n1, c1} == Spec.Ask.resolve{_, k2, n2, c2}: Spec.Ask}
        %Id.same_sound(k1, k2)(Bools.Bool.and_true_left(Spec.Id.same(k1, k2), r2)(h1)):
          {Spec.Ask.resolve{b1, k1, n1, c1} == Spec.Ask.resolve{b1, _, n2, c2}: Spec.Ask}
        %Resources.Name.same_sound(
          n1,
          n2
        )(Bools.Bool.and_true_left(Resources.Name.same(n1, n2), Spec.Content.same(c1, c2))(h2)):
          {Spec.Ask.resolve{b1, k1, n1, c1} == Spec.Ask.resolve{b1, k1, _, c2}: Spec.Ask}
        %Content.same_sound(
          c1,
          c2
        )(Bools.Bool.and_true_right(Resources.Name.same(n1, n2), Spec.Content.same(c1, c2))(h2)):
          {Spec.Ask.resolve{b1, k1, n1, c1} == Spec.Ask.resolve{b1, k1, n1, _}: Spec.Ask}
        {==}
    case Spec.Ask.mark{+b1, +m1, +t1} Spec.Ask.mark{+b2, +m2, +t2}:
      +h =>
        +r1 = Bool.and(String.eq(m1, m2), String.eq(t1, t2))
        +h1 = Bools.Bool.and_true_right(String.eq(b1, b2), r1)(h)
        %Strings.String.eq_sound(b1, b2)(Bools.Bool.and_true_left(String.eq(b1, b2), r1)(h)):
          {Spec.Ask.mark{b1, m1, t1} == Spec.Ask.mark{_, m2, t2}: Spec.Ask}
        %Strings.String.eq_sound(
          m1,
          m2
        )(Bools.Bool.and_true_left(String.eq(m1, m2), String.eq(t1, t2))(h1)):
          {Spec.Ask.mark{b1, m1, t1} == Spec.Ask.mark{b1, _, t2}: Spec.Ask}
        %Strings.String.eq_sound(
          t1,
          t2
        )(Bools.Bool.and_true_right(String.eq(m1, m2), String.eq(t1, t2))(h1)):
          {Spec.Ask.mark{b1, m1, t1} == Spec.Ask.mark{b1, m1, _}: Spec.Ask}
        {==}
    case Spec.Ask.set_owner{+c1, +ms1} Spec.Ask.set_owner{+c2, +ms2}:
      +h =>
        %Chain.same_sound(
          c1,
          c2
        )(
          Bools.Bool.and_true_left(
            Spec.Chain.same(c1, c2),
            Lists.List.same(~String, ~String.eq, ms1, ms2)
          )(h)
        ):
          {Spec.Ask.set_owner{c1, ms1} == Spec.Ask.set_owner{_, ms2}: Spec.Ask}
        %Lists.List.same_sound(
          ~String,
          ~String.eq,
          ~Text.sound,
          ms1,
          ms2
        )(
          Bools.Bool.and_true_right(
            Spec.Chain.same(c1, c2),
            Lists.List.same(~String, ~String.eq, ms1, ms2)
          )(h)
        ):
          {Spec.Ask.set_owner{c1, ms1} == Spec.Ask.set_owner{c1, _}: Spec.Ask}
        {==}
    case Spec.Ask.set_group{+g1, +ms1} Spec.Ask.set_group{+g2, +ms2}:
      +h =>
        %Strings.String.eq_sound(
          g1,
          g2
        )(
          Bools.Bool.and_true_left(
            String.eq(g1, g2),
            Lists.List.same(~Spec.Member, ~Spec.Member.same, ms1, ms2)
          )(h)
        ):
          {Spec.Ask.set_group{g1, ms1} == Spec.Ask.set_group{_, ms2}: Spec.Ask}
        %Lists.List.same_sound(
          ~Spec.Member,
          ~Spec.Member.same,
          ~Member.same_sound,
          ms1,
          ms2
        )(
          Bools.Bool.and_true_right(
            String.eq(g1, g2),
            Lists.List.same(~Spec.Member, ~Spec.Member.same, ms1, ms2)
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

def Spec.Entry.same_refl(a):
  match a:
    case Spec.Entry.ask{+i, +t, +q}:
      Bools.Bool.and_both(
        Spec.Id.same(i, i),
        Bool.and(String.eq(t, t), Spec.Ask.same(q, q))
      )(
        Id.same_refl(i)
      )(
        Bools.Bool.and_both(
          String.eq(t, t),
          Spec.Ask.same(q, q)
        )(Strings.String.eq_refl(t))(Ask.same_refl(q))
      )
    case Spec.Entry.vote{i}:
      Id.same_refl(i)
    case Spec.Entry.root{+c, +i, +n}:
      Bools.Bool.and_both(
        Spec.Chain.same(c, c),
        Bool.and(Spec.Id.same(i, i), String.eq(n, n))
      )(
        Chain.same_refl(c)
      )(
        Bools.Bool.and_both(
          Spec.Id.same(i, i),
          String.eq(n, n)
        )(Id.same_refl(i))(Strings.String.eq_refl(n))
      )

def Spec.Entry.same_sound(a, b):
  match a b:
    case Spec.Entry.ask{+i1, +t1, +q1} Spec.Entry.ask{+i2, +t2, +q2}:
      +h =>
        +r1 = Bool.and(String.eq(t1, t2), Spec.Ask.same(q1, q2))
        +h1 = Bools.Bool.and_true_right(Spec.Id.same(i1, i2), r1)(h)
        %Id.same_sound(i1, i2)(Bools.Bool.and_true_left(Spec.Id.same(i1, i2), r1)(h)):
          {Spec.Entry.ask{i1, t1, q1} == Spec.Entry.ask{_, t2, q2}: Spec.Entry}
        %Strings.String.eq_sound(
          t1,
          t2
        )(Bools.Bool.and_true_left(String.eq(t1, t2), Spec.Ask.same(q1, q2))(h1)):
          {Spec.Entry.ask{i1, t1, q1} == Spec.Entry.ask{i1, _, q2}: Spec.Entry}
        %Ask.same_sound(
          q1,
          q2
        )(Bools.Bool.and_true_right(String.eq(t1, t2), Spec.Ask.same(q1, q2))(h1)):
          {Spec.Entry.ask{i1, t1, q1} == Spec.Entry.ask{i1, t1, _}: Spec.Entry}
        {==}
    case Spec.Entry.vote{i1} Spec.Entry.vote{i2}:
      h =>
        %Id.same_sound(i1, i2)(h): {Spec.Entry.vote{i1} == Spec.Entry.vote{_}: Spec.Entry}
        {==}
    case Spec.Entry.root{+c1, +i1, +n1} Spec.Entry.root{+c2, +i2, +n2}:
      +h =>
        +r1 = Bool.and(Spec.Id.same(i1, i2), String.eq(n1, n2))
        +h1 = Bools.Bool.and_true_right(Spec.Chain.same(c1, c2), r1)(h)
        %Chain.same_sound(c1, c2)(Bools.Bool.and_true_left(Spec.Chain.same(c1, c2), r1)(h)):
          {Spec.Entry.root{c1, i1, n1} == Spec.Entry.root{_, i2, n2}: Spec.Entry}
        %Id.same_sound(
          i1,
          i2
        )(Bools.Bool.and_true_left(Spec.Id.same(i1, i2), String.eq(n1, n2))(h1)):
          {Spec.Entry.root{c1, i1, n1} == Spec.Entry.root{c1, _, n2}: Spec.Entry}
        %Strings.String.eq_sound(
          n1,
          n2
        )(Bools.Bool.and_true_right(Spec.Id.same(i1, i2), String.eq(n1, n2))(h1)):
          {Spec.Entry.root{c1, i1, n1} == Spec.Entry.root{c1, i1, _}: Spec.Entry}
        {==}
    case Spec.Entry.ask{p0, p1, p2} Spec.Entry.vote{q0}:
      h => Empty.absurd(
        {Spec.Entry.ask{p0, p1, p2} == Spec.Entry.vote{q0}: Spec.Entry},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Entry.ask{p0, p1, p2} Spec.Entry.root{q0, q1, q2}:
      h => Empty.absurd(
        {Spec.Entry.ask{p0, p1, p2} == Spec.Entry.root{q0, q1, q2}: Spec.Entry},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Entry.vote{p0} Spec.Entry.ask{q0, q1, q2}:
      h => Empty.absurd(
        {Spec.Entry.vote{p0} == Spec.Entry.ask{q0, q1, q2}: Spec.Entry},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Entry.vote{p0} Spec.Entry.root{q0, q1, q2}:
      h => Empty.absurd(
        {Spec.Entry.vote{p0} == Spec.Entry.root{q0, q1, q2}: Spec.Entry},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Entry.root{p0, p1, p2} Spec.Entry.ask{q0, q1, q2}:
      h => Empty.absurd(
        {Spec.Entry.root{p0, p1, p2} == Spec.Entry.ask{q0, q1, q2}: Spec.Entry},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Entry.root{p0, p1, p2} Spec.Entry.vote{q0}:
      h => Empty.absurd(
        {Spec.Entry.root{p0, p1, p2} == Spec.Entry.vote{q0}: Spec.Entry},
        Shared.Bool.false_ne_true(h)
      )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# Lookups
# -------

# the entry of a cell, when every holder agrees on it
def Cell.entry(m: Maybe<&2, Cells.Cell<Spec.Entry>>) -> Maybe<&2, Spec.Entry>:
  match m:
    case Some{Cells.one{e}}:
      Some{e}
    case _:
      None{}

# the cell of the slot k in s
def State.cell(s: Spec.State(), k: Spec.Slot) -> Maybe<&2, Cells.Cell<Spec.Entry>>:
  Tries.Trie.get(Cells.Cell<Spec.Entry>, s, Spec.Slot.key(k))

# a request that s holds: its time and change
type Asked is Data:
  Asked{time: String, ask: Spec.Ask}

# the request in the entry m
def Asked.of(m: Maybe<&2, Spec.Entry>) -> Maybe<&2, Asked>:
  match m:
    case Some{Spec.Entry.ask{i, t, q}}:
      Some{Asked{t, q}}
    case _:
      None{}

# the request i, when s holds it
def State.asked(s: Spec.State(), i: Spec.Id) -> Maybe<&2, Asked>:
  Asked.of(Cell.entry(State.cell(s, Spec.Slot.ask{i})))

# the version that the entry m votes for
def Vote.of(m: Maybe<&2, Spec.Entry>) -> Maybe<&2, Spec.Id>:
  match m:
    case Some{Spec.Entry.vote{i}}:
      Some{i}
    case _:
      None{}

# where a node votes: in s, on the chain c, after the version v
type Spot is Data:
  Spot{state: Spec.State(), chain: Spec.Chain, after: Spec.Id}

# the version that the node m votes for at the spot g
def Spot.vote(g: Spot, m: String) -> Maybe<&2, Spec.Id>:
  match g:
    case Spot{s, c, v}:
      Vote.of(Cell.entry(State.cell(s, Spec.Slot.vote{m, c, v})))

# Chains
# ------

# a version of a chain, and the nodes that vote for the next one
type Step is Data:
  Step{version: Spec.Id, owners: List<&2, String>}

# the owners after the change q, which ms owned
def Ask.owners(q: Spec.Ask, ms: List<&2, String>) -> List<&2, String>:
  match q:
    case Spec.Ask.set_owner{c, ns}:
      ns
    case _:
      ms

# the step to i, when its change q is on the chain (held)
def Step.if(held: Bool, i: Spec.Id, q: Spec.Ask, ms: List<&2, String>) -> Maybe<&2, Step>:
  match held:
    case True{}:
      Some{Step{i, Ask.owners(q, ms)}}
    case False{}:
      None{}

# the step to i, when s holds its request r on the chain c
def Step.ask(
  c: Spec.Chain,
  i: Spec.Id,
  ms: List<&2, String>,
  r: Maybe<&2, Asked>
) -> Maybe<&2, Step>:
  match r:
    case None{}:
      None{}
    case Some{Asked{t, +q}}:
      Step.if(Spec.Chain.same(Spec.Ask.chain(q), c), i, q, ms)

# the step to the winner w of a vote, on the chain c of s
def Step.won(
  s: Spec.State(),
  c: Spec.Chain,
  ms: List<&2, String>,
  w: Maybe<&2, Spec.Id>
) -> Maybe<&2, Step>:
  match w:
    case None{}:
      None{}
    case Some{+i}:
      Step.ask(c, i, ms, State.asked(s, i))

# the next step of the chain c of s, after the step k
def Chain.next(+s: Spec.State(), +c: Spec.Chain, k: Step) -> Maybe<&2, Step>:
  match k:
    case Step{v, +ms}:
      Step.won(
        s,
        c,
        ms,
        Quorums.Quorum.winner(
          ~String,
          ~Spec.Id,
          ~Spot,
          ~Spot.vote,
          ~Spec.Id.same,
          ms,
          ms,
          Spot{s, c, v}
        )
      )

# the versions of the chain c of s from the step nx on, f steps at most
def Chain.walk(f: Nat, +s: Spec.State(), +c: Spec.Chain, nx: Maybe<&2, Step>) -> List<&2, Spec.Id>:
  match f nx:
    case 0n m:
      []
    case 1n+e None{}:
      []
    case 1n+e Some{Step{+i, ms}}:
      i <> Chain.walk(e, s, c, Chain.next(s, c, Step{i, ms}))

# the last step of the chain c of s, from k with the next step nx, f steps at
# most
def Chain.last(f: Nat, +s: Spec.State(), +c: Spec.Chain, k: Step, nx: Maybe<&2, Step>) -> Step:
  match f nx:
    case 0n m:
      k
    case 1n+e None{}:
      k
    case 1n+e Some{+st}:
      Chain.last(e, s, c, st, Chain.next(s, c, st))

# enough steps for any chain of s: one more than it has entries
def State.fuel(s: Spec.State()) -> Nat:
  1n+Tries.Trie.size(Cells.Cell<Spec.Entry>, s)

# the first step of a chain, from its root entry m
def Root.of(m: Maybe<&2, Spec.Entry>) -> Maybe<&2, Step>:
  match m:
    case Some{Spec.Entry.root{c, i, n}}:
      Some{Step{i, [n]}}
    case _:
      None{}

# the first step of the chain c, when s holds its root and its request
def Chain.root.of(s: Spec.State(), c: Spec.Chain, m: Maybe<&2, Step>) -> Maybe<&2, Step>:
  match m:
    case None{}:
      None{}
    case Some{Step{+i, ms}}:
      Step.ask(c, i, ms, State.asked(s, i))

# the first step of the chain c of s
def Chain.root(+s: Spec.State(), +c: Spec.Chain) -> Maybe<&2, Step>:
  Chain.root.of(s, c, Root.of(Spec.Node.claim(s, c)))

# the versions of the chain c of s, from its first step r
def Chain.from(+s: Spec.State(), +c: Spec.Chain, r: Maybe<&2, Step>) -> List<&2, Spec.Id>:
  match r:
    case None{}:
      []
    case Some{Step{+i, ms}}:
      i <> Chain.walk(State.fuel(s), s, c, Chain.next(s, c, Step{i, ms}))

# the last step of the chain c of s, from its first step r
def Chain.cursor.of(+s: Spec.State(), +c: Spec.Chain, r: Maybe<&2, Step>) -> Maybe<&2, Step>:
  match r:
    case None{}:
      None{}
    case Some{+st}:
      Some{Chain.last(State.fuel(s), s, c, st, Chain.next(s, c, st))}

# the last step of the chain c of s, if c exists
def Chain.cursor(+s: Spec.State(), +c: Spec.Chain) -> Maybe<&2, Step>:
  Chain.cursor.of(s, c, Chain.root(s, c))

def Spec.Node.chain(s, c):
  +s = s
  +c = c
  Chain.from(s, c, Chain.root(s, c))

# the version of a step
def Step.version(k: Step) -> Spec.Id:
  match k:
    case Step{v, ms}:
      v

# the owners of a step
def Step.owners(k: Step) -> List<&2, String>:
  match k:
    case Step{v, ms}:
      ms

# the owners at the last step m, none without one
def Step.owners.of(m: Maybe<&2, Step>) -> List<&2, String>:
  match m:
    case None{}:
      []
    case Some{k}:
      Step.owners(k)

def Spec.Node.owners(s, c):
  Step.owners.of(Chain.cursor(s, c))

def Spec.Node.head(s, b):
  Maybe.map(&2, Step, Spec.Id, k => Step.version(k), Chain.cursor(s, Spec.Chain.branch{b}))

# Versions
# --------

# the requests among the cells cs
def Entry.ids(cs: List<&2, Cells.Cell<Spec.Entry>>) -> List<&2, Spec.Id>:
  match cs:
    case Nil{}:
      []
    case Con{Cells.one{Spec.Entry.ask{i, t, q}}, r}:
      i <> Entry.ids(r)
    case Con{c, r}:
      Entry.ids(r)

# every request that s holds
def State.versions(s: Spec.State()) -> List<&2, Spec.Id>:
  Entry.ids(Tries.Trie.values(Cells.Cell<Spec.Entry>, s))

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- the rest is one walk of the list; it costs the same with or without the pick
# the version before v in xs, after prev; none when v is first or not there
def List.before(xs: List<&2, Spec.Id>, prev: Maybe<&2, Spec.Id>, +v: Spec.Id) -> Maybe<&2, Spec.Id>:
  match xs:
    case Nil{}:
      None{}
    case Con{+x, r}:
      Bool.pick(Maybe<&2, Spec.Id>, Spec.Id.same(x, v), prev, List.before(r, Some{x}, v))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the version before v on its chain c
def Chain.before(s: Spec.State(), c: Spec.Chain, v: Spec.Id) -> Maybe<&2, Spec.Id>:
  List.before(Spec.Node.chain(s, c), None{}, v)

# the versions that the change q of v names besides the one before it
def Ask.refs(q: Spec.Ask) -> List<&2, Spec.Id>:
  match q:
    case Spec.Ask.set_branch{b, to}:
      [to]
    case Spec.Ask.merge{b, from}:
      [from]
    case _:
      []

# the versions that v came from, when s holds its request r
def Version.parents.of(s: Spec.State(), v: Spec.Id, r: Maybe<&2, Asked>) -> List<&2, Spec.Id>:
  match r:
    case None{}:
      []
    case Some{Asked{t, +q}}:
      List.append(
        &2,
        Spec.Id,
        Maybe.default(
          &2,
          List<&2, Spec.Id>,
          Maybe.map(
            &2,
            Spec.Id,
            List<&2, Spec.Id>,
            x => [x],
            Chain.before(s, Spec.Ask.chain(q), v)
          ),
          []
        ),
        Ask.refs(q)
      )

# the versions that v came from
def Version.parents(s: Spec.State(), v: Spec.Id) -> List<&2, Spec.Id>:
  +s = s
  +v = v
  Version.parents.of(s, v, State.asked(s, v))

# x is v (held), or a version that v came from
def Version.is_from.if(held: Bool, s: Spec.State(), x: Spec.Id, v: Spec.Id) -> Bool:
  match held:
    case True{}:
      True{}
    case False{}:
      Reaches.Reach.in(
        ~Spec.Id,
        ~Spec.State(),
        ~Spec.Id.same,
        ~Version.parents,
        ~State.versions,
        s,
        v,
        x
      )

# x is v, or a version that v came from
def Version.is_from(s: Spec.State(), +x: Spec.Id, +v: Spec.Id) -> Bool:
  Version.is_from.if(Spec.Id.same(x, v), s, x, v)

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- the rest is one walk of the list; it costs the same with or without the pick
# the first version of xs that v came from
def Version.base.go(+s: Spec.State(), xs: List<&2, Spec.Id>, +v: Spec.Id) -> Maybe<&2, Spec.Id>:
  match xs:
    case Nil{}:
      None{}
    case Con{+x, r}:
      Bool.pick(Maybe<&2, Spec.Id>, Version.is_from(s, x, v), Some{x}, Version.base.go(s, r, v))

# the versions of xs up to v
def List.upto(xs: List<&2, Spec.Id>, +v: Spec.Id) -> List<&2, Spec.Id>:
  match xs:
    case Nil{}:
      []
    case Con{+x, r}:
      x <> Bool.pick(List<&2, Spec.Id>, Spec.Id.same(x, v), [], List.upto(r, v))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the base of a merge of from into the chain c, whose head was ours: the newest
# version of c up to ours that from came from
def Version.base(
  +s: Spec.State(),
  c: Spec.Chain,
  ours: Maybe<&2, Spec.Id>,
  from: Spec.Id
) -> Maybe<&2, Spec.Id>:
  match ours:
    case None{}:
      None{}
    case Some{o}:
      Version.base.go(s, List.reverse(&2, Spec.Id, List.upto(Spec.Node.chain(s, c), o)), from)

# Content
# -------
# The bytes of a resource at a version, found one resource at a time: a write
# or a resolve of it holds them, a set-branch takes them from its target, a
# merge merges its base, the version before it and the one merged in, and
# every other change keeps the version before it.

# the request r names the resource n
def Asked.hits(r: Maybe<&2, Asked>, n: Resources.Name) -> Bool:
  match r:
    case Some{Asked{t, Spec.Ask.write{b, m, base, c}}}:
      Resources.Name.same(m, n)
    case Some{Asked{t, Spec.Ask.resolve{b, k, m, c}}}:
      Resources.Name.same(m, n)
    case _:
      False{}

# the request of v, when there is one
def State.asked.of(s: Spec.State(), v: Maybe<&2, Spec.Id>) -> Maybe<&2, Asked>:
  match v:
    case None{}:
      None{}
    case Some{i}:
      State.asked(s, i)

# what a merge keeps of a resource: its bytes or none, or a clash
type Pick is Data:
  Pick.take{bytes: Maybe<&2, Octets.Bytes()>}
  Pick.clash{}

# the merge of a resource's bytes, when all three hold it
def Pick.bytes(m: Formats.Merged) -> Pick:
  match m:
    case Formats.Merged.clean{x}:
      Pick.take{Some{x}}
    case Formats.Merged.clash{}:
      Pick.clash{}

# the merge of a resource that the base, ours and theirs hold or not, when
# both sides changed it
def Pick.both(
  b: Maybe<&2, Octets.Bytes()>,
  o: Maybe<&2, Octets.Bytes()>,
  t: Maybe<&2, Octets.Bytes()>
) -> Pick:
  match o t:
    case Some{x} Some{y}:
      Pick.bytes(Formats.Format.merge(Maybe.default(&2, Octets.Bytes(), b, []), x, y))
    case _ _:
      Pick.clash{}

# the merge of a resource, once both sides are known to agree or not (held)
def Pick.of.same(
  held: Bool,
  b: Maybe<&2, Octets.Bytes()>,
  o: Maybe<&2, Octets.Bytes()>,
  t: Maybe<&2, Octets.Bytes()>
) -> Pick:
  match held:
    case True{}:
      Pick.take{o}
    case False{}:
      Pick.both(b, o, t)

# the merge of a resource, once theirs is known to be the base or not (held)
def Pick.of.right(
  held: Bool,
  b: Maybe<&2, Octets.Bytes()>,
  +o: Maybe<&2, Octets.Bytes()>,
  +t: Maybe<&2, Octets.Bytes()>
) -> Pick:
  match held:
    case True{}:
      Pick.take{o}
    case False{}:
      Pick.of.same(Maybes.Maybe.same(~Octets.Bytes(), ~Octets.Bytes.is_eq, o, t), b, o, t)

# the merge of a resource, once ours is known to be the base or not (held)
def Pick.of(
  held: Bool,
  +b: Maybe<&2, Octets.Bytes()>,
  o: Maybe<&2, Octets.Bytes()>,
  +t: Maybe<&2, Octets.Bytes()>
) -> Pick:
  match held:
    case True{}:
      Pick.take{t}
    case False{}:
      Pick.of.right(Maybes.Maybe.same(~Octets.Bytes(), ~Octets.Bytes.is_eq, t, b), b, o, t)

# what a merge of the base b, ours o and theirs t keeps of a resource
def Pick.merge(
  +b: Maybe<&2, Octets.Bytes()>,
  +o: Maybe<&2, Octets.Bytes()>,
  t: Maybe<&2, Octets.Bytes()>
) -> Pick:
  Pick.of(Maybes.Maybe.same(~Octets.Bytes(), ~Octets.Bytes.is_eq, o, b), b, o, t)

# the bytes of a merge: ours on a clash
def Pick.kept(p: Pick, o: Maybe<&2, Octets.Bytes()>) -> Maybe<&2, Octets.Bytes()>:
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
  v: Maybe<&2, Spec.Id>,
  +n: Resources.Name,
  r: Maybe<&2, Asked>,
  hit: Bool
) -> Maybe<&2, Octets.Bytes()>:
  match f v r hit:
    case 0n w m h:
      None{}
    case 1n+e None{} m h:
      None{}
    case 1n+e Some{i} None{} h:
      None{}
    case 1n+e Some{i} Some{Asked{t, Spec.Ask.write{b, m, base, Spec.Content.bytes{x}}}} True{}:
      Some{x}
    case 1n+e Some{i} Some{Asked{t, Spec.Ask.write{b, m, base, Spec.Content.of{+w}}}} True{}:
      Res.at(e, s, Some{w}, n, State.asked(s, w), Asked.hits(State.asked(s, w), n))
    case 1n+e Some{i} Some{Asked{t, Spec.Ask.resolve{b, k, m, Spec.Content.bytes{x}}}} True{}:
      Some{x}
    case 1n+e Some{i} Some{Asked{t, Spec.Ask.resolve{b, k, m, Spec.Content.of{+w}}}} True{}:
      Res.at(e, s, Some{w}, n, State.asked(s, w), Asked.hits(State.asked(s, w), n))
    case 1n+e Some{i} Some{Asked{t, Spec.Ask.set_branch{b, +to}}} h:
      Res.at(e, s, Some{to}, n, State.asked(s, to), Asked.hits(State.asked(s, to), n))
    case 1n+e Some{+i} Some{Asked{t, Spec.Ask.merge{+b, +from}}} h:
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
      ) Res.at(e, s, Some{from}, n, State.asked(s, from), Asked.hits(State.asked(s, from), n))
      Pick.kept(Pick.merge(bs, o, fs), o)
    case 1n+e Some{+i} Some{Asked{t, +q}} h:
      +before = Chain.before(s, Spec.Ask.chain(q), i)
      Res.at(e, s, before, n, State.asked.of(s, before), Asked.hits(State.asked.of(s, before), n))

# the bytes of the resource n at the version v of s
def Res.of(
  +s: Spec.State(),
  +n: Resources.Name,
  +v: Maybe<&2, Spec.Id>
) -> Maybe<&2, Octets.Bytes()>:
  Res.at(State.fuel(s), s, v, n, State.asked.of(s, v), Asked.hits(State.asked.of(s, v), n))

# the request r names the mark m
def Mark.is(r: Maybe<&2, Asked>, m: String) -> Bool:
  match r:
    case Some{Asked{t, Spec.Ask.mark{b, k, x}}}:
      String.eq(k, m)
    case _:
      False{}

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- the rest is one walk of the list; it costs the same with or without the pick
# the version that the first mark m of xs names: the one before it, after prev
def Mark.first(
  +s: Spec.State(),
  xs: List<&2, Spec.Id>,
  prev: Maybe<&2, Spec.Id>,
  +m: String
) -> Maybe<&2, Spec.Id>:
  match xs:
    case Nil{}:
      None{}
    case Con{+x, r}:
      Bool.pick(
        Maybe<&2, Spec.Id>,
        Mark.is(State.asked(s, x), m),
        prev,
        Mark.first(s, r, Some{x}, m)
      )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the version that the mark m of the branch b names
def Mark.of(+s: Spec.State(), b: String, m: String) -> Maybe<&2, Spec.Id>:
  Mark.first(s, Spec.Node.chain(s, Spec.Chain.branch{b}), None{}, m)

# the version at the point p of s
def Point.version(s: Spec.State(), p: Spec.Point) -> Maybe<&2, Spec.Id>:
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
  v: Maybe<&2, Spec.Id>,
  r: Maybe<&2, Asked>
) -> List<&2, String>:
  match f v r:
    case 0n w m:
      []
    case 1n+e None{} m:
      []
    case 1n+e Some{i} None{}:
      []
    case 1n+e Some{i} Some{Asked{t, Spec.Ask.set_branch{b, +to}}}:
      Res.names(e, s, Some{to}, State.asked(s, to))
    case 1n+e Some{+i} Some{Asked{t, Spec.Ask.merge{b, +from}}}:
      +ours = Chain.before(s, Spec.Chain.branch{b}, i)
      fs os = Res.names(
        e,
        s,
        Some{from},
        State.asked(s, from)
      ) Res.names(e, s, ours, State.asked.of(s, ours))
      Strings.union(fs, os)
    case 1n+e Some{+i} Some{Asked{t, Spec.Ask.write{b, m, base, c}}}:
      +before = Chain.before(s, Spec.Chain.branch{b}, i)
      Strings.union([Resources.Name.show(m)], Res.names(e, s, before, State.asked.of(s, before)))
    case 1n+e Some{+i} Some{Asked{t, +q}}:
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
  +base: Maybe<&2, Spec.Id>,
  +ours: Maybe<&2, Spec.Id>,
  +from: Spec.Id
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
        Pick.is_clash(Pick.merge(Res.of(s, n, base), Res.of(s, n, ours), Res.of(s, n, Some{from})))
      )

# Conflicts
# ---------

# the texts of the resources at the version v of s
def Res.of.names(+s: Spec.State(), +v: Maybe<&2, Spec.Id>) -> List<&2, String>:
  Res.names(State.fuel(s), s, v, State.asked.of(s, v))

# the resources that clash at the merge k, whose request is r
def Merge.clashes(+s: Spec.State(), k: Spec.Id, r: Maybe<&2, Asked>) -> List<&2, Resources.Name>:
  match r:
    case Some{Asked{t, Spec.Ask.merge{+b, +from}}}:
      +ours = Chain.before(s, Spec.Chain.branch{b}, k)
      Res.clashes(
        s,
        Strings.union(Res.of.names(s, Some{from}), Res.of.names(s, ours)),
        Version.base(s, Spec.Chain.branch{b}, ours, from),
        ours,
        from
      )
    case _:
      []

# the text that the request r settles of k
def Merge.settles(r: Maybe<&2, Asked>, k: Spec.Id) -> List<&2, String>:
  match r:
    case Some{Asked{t, Spec.Ask.resolve{b, j, n, c}}}:
      List.filter.put(String, Resources.Name.show(n), [], Spec.Id.same(j, k))
    case _:
      []

# the texts that the resolves of k among xs settle
def Merge.settled(+s: Spec.State(), xs: List<&2, Spec.Id>, +k: Spec.Id) -> List<&2, String>:
  match xs:
    case Nil{}:
      []
    case Con{x, r}:
      List.append(&2, String, Merge.settles(State.asked(s, x), k), Merge.settled(s, r, k))

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
def Merge.left(+s: Spec.State(), +k: Spec.Id, +r: Maybe<&2, Asked>) -> List<&2, Resources.Name>:
  match r:
    case Some{Asked{t, Spec.Ask.merge{+b, from}}}:
      Names.unsettled(
        Merge.clashes(s, k, r),
        Merge.settled(s, Spec.Node.chain(s, Spec.Chain.branch{b}), k)
      )
    case _:
      []

def Spec.Node.conflict(s, k):
  +s = s
  +k = k
  Merge.left(s, k, State.asked(s, k))

# Answers
# -------

# the change q fits the head h of its chain: the owners may vote for it there
def Ask.fits(+s: Spec.State(), q: Spec.Ask, h: Spec.Id) -> Bool:
  match q:
    case Spec.Ask.write{b, +n, base, c}:
      Maybes.Maybe.same(
        ~Octets.Bytes(),
        ~Octets.Bytes.is_eq,
        Res.of(s, n, Some{h}),
        Res.of(s, n, base)
      )
    case Spec.Ask.set_branch{b, to}:
      Maybe.is_some(&2, Asked, State.asked(s, to))
    case Spec.Ask.merge{b, from}:
      Maybe.is_some(&2, Asked, State.asked(s, from))
    case Spec.Ask.resolve{b, k, n, c}:
      Shared.List.has(~Resources.Name, ~Resources.Name.same, Spec.Node.conflict(s, k), n)
    case Spec.Ask.mark{b, m, t}:
      Maybe.is_none(&2, Spec.Id, Mark.of(s, b, m))
    case Spec.Ask.set_owner{c, ms}:
      Bool.not(List.is_empty(&2, String, ms))
    case Spec.Ask.set_group{g, ms}:
      True{}

# the change q makes its chain when the chain does not exist
def Ask.creates(q: Spec.Ask) -> Bool:
  match q:
    case Spec.Ask.write{b, n, None{}, c}:
      True{}
    case Spec.Ask.set_branch{b, to}:
      True{}
    case Spec.Ask.set_group{g, ms}:
      True{}
    case _:
      False{}

# Written, or Conflicted when the merge k still clashes (left)
def Answer.done.if(left: List<&2, Resources.Name>, i: Spec.Id, k: Spec.Id) -> Spec.Answer:
  match left:
    case Nil{}:
      Spec.Answer.written{i}
    case Con{n, r}:
      Spec.Answer.conflicted{k}

# the answer to the request i in its chain, whose change is q
def Answer.done(s: Spec.State(), +i: Spec.Id, q: Spec.Ask) -> Spec.Answer:
  match q:
    case Spec.Ask.merge{b, from}:
      Answer.done.if(Spec.Node.conflict(s, i), i, i)
    case Spec.Ask.resolve{b, +k, n, c}:
      Answer.done.if(Spec.Node.conflict(s, k), i, k)
    case _:
      Spec.Answer.written{i}

# the answer to a request of q outside its chain, whose claim is m and last
# step k
def Answer.open(
  s: Spec.State(),
  q: Spec.Ask,
  m: Maybe<&2, Spec.Entry>,
  k: Maybe<&2, Step>
) -> Spec.Answer:
  match m k:
    case w Some{Step{+h, ms}}:
      Bool.pick(Spec.Answer, Ask.fits(s, q, h), Spec.Answer.pending{}, Spec.Answer.stale{h})
    case None{} None{}:
      Bool.pick(
        Spec.Answer,
        Ask.creates(q),
        Spec.Answer.pending{},
        Spec.Answer.refused{"no such chain"}
      )
    case Some{e} None{}:
      Spec.Answer.pending{}

# the answer to the request i of q, in its chain or not (held)
def Answer.in(+s: Spec.State(), i: Spec.Id, +q: Spec.Ask, held: Bool) -> Spec.Answer:
  match held:
    case True{}:
      Answer.done(s, i, q)
    case False{}:
      Answer.open(s, q, Spec.Node.claim(s, Spec.Ask.chain(q)), Chain.cursor(s, Spec.Ask.chain(q)))

# the answer to the request i, whose cell is m
def Answer.of(+s: Spec.State(), +i: Spec.Id, m: Maybe<&2, Cells.Cell<Spec.Entry>>) -> Spec.Answer:
  match m:
    case None{}:
      Spec.Answer.not_seen{}
    case Some{Cells.many{}}:
      Spec.Answer.refused{"the request is contradicted"}
    case Some{Cells.one{Spec.Entry.ask{j, t, +q}}}:
      Answer.in(
        s,
        i,
        q,
        Shared.List.has(~Spec.Id, ~Spec.Id.same, Spec.Node.chain(s, Spec.Ask.chain(q)), i)
      )
    case Some{Cells.one{e}}:
      Spec.Answer.not_seen{}

def Spec.Node.answer(s, i):
  +s = s
  +i = i
  Answer.of(s, i, State.cell(s, Spec.Slot.ask{i}))

# Listings
# --------

# the branch b, at its last step m, then rest
def Branches.at(
  b: String,
  m: Maybe<&2, Step>,
  rest: List<&2, Spec.BranchEntry>
) -> List<&2, Spec.BranchEntry>:
  match m:
    case None{}:
      rest
    case Some{Step{h, ms}}:
      Spec.BranchEntry{b, ms, h} <> rest

# the names of the branches that some cell of cs claims
def Branches.named(cs: List<&2, Cells.Cell<Spec.Entry>>) -> List<&2, String>:
  match cs:
    case Nil{}:
      []
    case Con{Cells.one{Spec.Entry.root{Spec.Chain.branch{b}, i, n}}, r}:
      Strings.union([b], Branches.named(r))
    case Con{c, r}:
      Branches.named(r)

# the branches of the names bs
def Branches.of(+s: Spec.State(), bs: List<&2, String>) -> List<&2, Spec.BranchEntry>:
  match bs:
    case Nil{}:
      []
    case Con{+b, r}:
      Branches.at(b, Chain.cursor(s, Spec.Chain.branch{b}), Branches.of(s, r))

def Spec.Node.branches(s):
  +s = s
  Branches.of(s, Branches.named(Tries.Trie.values(Cells.Cell<Spec.Entry>, s)))

# the version x, when it changed the resource (held), then rest
def Log.at(
  held: Bool,
  x: Spec.Id,
  r: Maybe<&2, Asked>,
  rest: List<&2, Spec.LogEntry>
) -> List<&2, Spec.LogEntry>:
  match held r:
    case True{} Some{Asked{t, q}}:
      Spec.LogEntry{x, t} <> rest
    case h m:
      rest

# the versions of xs, after prev, that changed the resource n
def Log.of(
  +s: Spec.State(),
  +n: Resources.Name,
  xs: List<&2, Spec.Id>,
  prev: Maybe<&2, Spec.Id>
) -> List<&2, Spec.LogEntry>:
  match xs:
    case Nil{}:
      []
    case Con{+x, r}:
      Log.at(
        Bool.not(
          Maybes.Maybe.same(
            ~Octets.Bytes(),
            ~Octets.Bytes.is_eq,
            Res.of(s, n, Some{x}),
            Res.of(s, n, prev)
          )
        ),
        x,
        State.asked(s, x),
        Log.of(s, n, r, Some{x})
      )

def Spec.Node.log(s, n, b):
  +s = s
  Log.of(s, n, Spec.Node.chain(s, Spec.Chain.branch{b}), None{})

def Spec.Node.diff(s, n, a, b):
  +s = s
  +n = n
  Formats.Format.changes(
    Maybe.default(&2, Octets.Bytes(), Spec.Node.content(s, n, a), []),
    Maybe.default(&2, Octets.Bytes(), Spec.Node.content(s, n, b), [])
  )

# Groups
# ------

# the members that the request r sets, else found
def Group.set(
  r: Maybe<&2, Asked>,
  found: Maybe<&2, List<&2, Spec.Member>>
) -> Maybe<&2, List<&2, Spec.Member>>:
  match r:
    case Some{Asked{t, Spec.Ask.set_group{g, ms}}}:
      Some{ms}
    case _:
      found

# the members that the last set-group of xs sets, else found
def Group.last(
  +s: Spec.State(),
  xs: List<&2, Spec.Id>,
  found: Maybe<&2, List<&2, Spec.Member>>
) -> Maybe<&2, List<&2, Spec.Member>>:
  match xs:
    case Nil{}:
      found
    case Con{x, r}:
      Group.last(s, r, Group.set(State.asked(s, x), found))

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

# the groups whose roots are among the cells cs, as members
def Group.roots(cs: List<&2, Cells.Cell<Spec.Entry>>) -> List<&2, Spec.Member>:
  match cs:
    case Nil{}:
      []
    case Con{Cells.one{Spec.Entry.root{Spec.Chain.group{+g}, i, n}}, r}:
      +rest = Group.roots(r)
      List.filter.put(
        Spec.Member,
        Spec.Member.group{g},
        rest,
        Bool.not(Shared.List.has(~Spec.Member, ~Spec.Member.same, rest, Spec.Member.group{g}))
      )
    case Con{c, r}:
      Group.roots(r)

# every group of s, as a member
def Group.all(s: Spec.State()) -> List<&2, Spec.Member>:
  Group.roots(Tries.Trie.values(Cells.Cell<Spec.Entry>, s))

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
      Strings.union(Group.nodes.of(Group.succ(s, g)), Group.named(s, r))

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

# Notices
# -------

# a and b are the same notice
def Notice.same(a: Spec.Notice, b: Spec.Notice) -> Bool:
  match a b:
    case Spec.Notice.versioned{b1, v1} Spec.Notice.versioned{b2, v2}:
      Bool.and(String.eq(b1, b2), Spec.Id.same(v1, v2))
    case Spec.Notice.conflicted{b1, v1} Spec.Notice.conflicted{b2, v2}:
      Bool.and(String.eq(b1, b2), Spec.Id.same(v1, v2))
    case Spec.Notice.group_cycle{g1} Spec.Notice.group_cycle{g2}:
      String.eq(g1, g2)
    case _ _:
      False{}

# the versions of the branch b among xs, as notices
def Notice.versions(+b: String, xs: List<&2, Spec.Id>) -> List<&2, Spec.Notice>:
  match xs:
    case Nil{}:
      []
    case Con{x, r}:
      Spec.Notice.versioned{b, x} <> Notice.versions(b, r)

# the merges of the branch b among xs that clashed, as notices
def Notice.conflicts(+s: Spec.State(), +b: String, xs: List<&2, Spec.Id>) -> List<&2, Spec.Notice>:
  match xs:
    case Nil{}:
      []
    case Con{+x, r}:
      List.filter.put(
        Spec.Notice,
        Spec.Notice.conflicted{b, x},
        Notice.conflicts(s, b, r),
        Bool.not(List.is_empty(&2, Resources.Name, Merge.clashes(s, x, State.asked(s, x))))
      )

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

# Changes
# -------

# s with the entry e in the slot k
def State.put(s: Spec.State(), k: Spec.Slot, e: Spec.Entry) -> Spec.State():
  Spec.Node.join(s, Tries.Trie.one(Cells.Cell<Spec.Entry>, Spec.Slot.key(k), Cells.one{e}))

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- the laws of Node.ask split on this and; a request is taken in once
# the node n may vote at the step h of the chain c, whose owners are ms
def Node.may_vote(
  +n: String,
  s: Spec.State(),
  c: Spec.Chain,
  h: Spec.Id,
  ms: List<&2, String>
) -> Bool:
  Bool.and(
    Shared.List.has(~String, ~String.eq, ms, n),
    Maybe.is_none(&2, Cells.Cell<Spec.Entry>, State.cell(s, Spec.Slot.vote{n, c, h}))
  )

# s1 after the node n voted for the request i of q, at the last step m of its
# chain in s
def Node.ask.at(
  +n: String,
  +s: Spec.State(),
  +s1: Spec.State(),
  i: Spec.Id,
  +q: Spec.Ask,
  m: Maybe<&2, Step>
) -> Spec.State():
  match m:
    case None{}:
      s1
    case Some{Step{+h, ms}}:
      +c = Spec.Ask.chain(q)
      Bool.pick(
        Spec.State(),
        Bool.and(Node.may_vote(n, s, c, h, ms), Ask.fits(s, q, h)),
        State.put(s1, Spec.Slot.vote{n, c, h}, Spec.Entry.vote{i}),
        s1
      )

# s1 after the node n took in the request i of q, whose chain has the claim m
# in s
def Node.ask.root(
  +n: String,
  +s: Spec.State(),
  +s1: Spec.State(),
  i: Spec.Id,
  +q: Spec.Ask,
  m: Maybe<&2, Spec.Entry>
) -> Spec.State():
  match m:
    case None{}:
      Bool.pick(
        Spec.State(),
        Ask.creates(q),
        State.put(
          s1,
          Spec.Slot.root{Spec.Ask.chain(q), n},
          Spec.Entry.root{Spec.Ask.chain(q), i, n}
        ),
        s1
      )
    case Some{x}:
      Node.ask.at(n, s, s1, i, q, Chain.cursor(s, Spec.Ask.chain(q)))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# s after the node n took in the request i of q at the time t, whose cell in s
# is m
def Node.ask.fresh(
  n: String,
  +s: Spec.State(),
  +i: Spec.Id,
  t: String,
  +q: Spec.Ask,
  m: Maybe<&2, Cells.Cell<Spec.Entry>>
) -> Spec.State():
  match m:
    case Some{x}:
      s
    case None{}:
      Node.ask.root(
        n,
        s,
        State.put(s, Spec.Slot.ask{i}, Spec.Entry.ask{i, t, q}),
        i,
        q,
        Spec.Node.claim(s, Spec.Ask.chain(q))
      )

def Spec.Node.ask(n, s, e, q):
  match e:
    case Spec.Envelope{r, w, t}:
      +s = s
      +i = {Spec.Id{w, r}: Spec.Id}
      Node.ask.fresh(n, s, i, t, q, State.cell(s, Spec.Slot.ask{i}))

# the first request among the cells cs that changes the chain c, is not among
# Ask.fits of q at the head h, when the request is not in its chain yet
# (outside)
def Vote.open.on(outside: Bool, s: Spec.State(), q: Spec.Ask, h: Spec.Id) -> Bool:
  match outside:
    case True{}:
      Ask.fits(s, q, h)
    case False{}:
      False{}

# the request i of q is on the chain (held), is not among its versions xs and
# fits its head h
def Vote.open(
  held: Bool,
  s: Spec.State(),
  q: Spec.Ask,
  xs: List<&2, Spec.Id>,
  i: Spec.Id,
  h: Spec.Id
) -> Bool:
  match held:
    case True{}:
      Vote.open.on(Bool.not(Shared.List.has(~Spec.Id, ~Spec.Id.same, xs, i)), s, q, h)
    case False{}:
      False{}

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- the rest is one walk of the list; it costs the same with or without the pick
# its versions xs, and fits its head h
def Vote.pick(
  +s: Spec.State(),
  cs: List<&2, Cells.Cell<Spec.Entry>>,
  +c: Spec.Chain,
  +xs: List<&2, Spec.Id>,
  +h: Spec.Id
) -> Maybe<&2, Spec.Id>:
  match cs:
    case Nil{}:
      None{}
    case Con{Cells.one{Spec.Entry.ask{+i, t, +q}}, r}:
      Bool.pick(
        Maybe<&2, Spec.Id>,
        Vote.open(Spec.Chain.same(Spec.Ask.chain(q), c), s, q, xs, i, h),
        Some{i},
        Vote.pick(s, r, c, xs, h)
      )
    case Con{x, r}:
      Vote.pick(s, r, c, xs, h)
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the vote in the slot k for the choice m, when the node may vote (held)
def Vote.cast(held: Bool, k: Spec.Slot, m: Maybe<&2, Spec.Id>) -> Spec.State():
  match held m:
    case True{} Some{i}:
      Tries.Trie.one(Cells.Cell<Spec.Entry>, Spec.Slot.key(k), Cells.one{Spec.Entry.vote{i}})
    case h w:
      Tries.tip{}

# the vote of the node n on the chain c of s, at its last step m
def Vote.at(+n: String, +s: Spec.State(), +c: Spec.Chain, m: Maybe<&2, Step>) -> Spec.State():
  match m:
    case None{}:
      Tries.tip{}
    case Some{Step{+h, ms}}:
      Vote.cast(
        Node.may_vote(n, s, c, h, ms),
        Spec.Slot.vote{n, c, h},
        Vote.pick(s, Tries.Trie.values(Cells.Cell<Spec.Entry>, s), c, Spec.Node.chain(s, c), h)
      )

# the chains whose roots are among the cells cs
def Vote.chains(cs: List<&2, Cells.Cell<Spec.Entry>>) -> List<&2, Spec.Chain>:
  match cs:
    case Nil{}:
      []
    case Con{Cells.one{Spec.Entry.root{+c, i, n}}, r}:
      +rest = Vote.chains(r)
      List.filter.put(
        Spec.Chain,
        c,
        rest,
        Bool.not(Shared.List.has(~Spec.Chain, ~Spec.Chain.same, rest, c))
      )
    case Con{x, r}:
      Vote.chains(r)

# the votes of the node n on each chain of cs
def Vote.all(+n: String, +s: Spec.State(), cs: List<&2, Spec.Chain>) -> Spec.State():
  match cs:
    case Nil{}:
      Tries.tip{}
    case Con{+c, r}:
      Spec.Node.join(Vote.at(n, s, c, Chain.cursor(s, c)), Vote.all(n, s, r))

def Spec.Node.vote(n, s):
  +s = s
  Spec.Node.join(s, Vote.all(n, s, Vote.chains(Tries.Trie.values(Cells.Cell<Spec.Entry>, s))))

# Kept entries
# ------------
# What a node holds stays when it takes in entries that agree with it.

# the cell of a slot is kept by an agreeing join
def Kept.cell(
  s: Spec.State(),
  t: Spec.State(),
  k: Spec.Slot,
  -e: Spec.Entry,
  a: {Spec.Node.agrees(s, t) == True{}: Bool}
) -> {
  State.cell(s, k) == Some{Cells.one{e}}: Maybe<&2, Cells.Cell<Spec.Entry>>
} -> {State.cell(Spec.Node.join(s, t), k) == Some{Cells.one{e}}: Maybe<&2, Cells.Cell<Spec.Entry>>}:
  Cells.Cell.agrees_kept(
    ~Spec.Entry,
    ~Spec.Entry.same,
    ~Spec.Entry.same_sound,
    s,
    t,
    Spec.Slot.key(k),
    e
  )(a)

# the entry of a cell m is kept in m2, when m2 keeps the value of m
def Kept.entry(
  m: Maybe<&2, Cells.Cell<Spec.Entry>>,
  m2: Maybe<&2, Cells.Cell<Spec.Entry>>,
  -e: Spec.Entry,
  keep: {
    m == Some{Cells.one{e}}: Maybe<&2, Cells.Cell<Spec.Entry>>
  } -> {m2 == Some{Cells.one{e}}: Maybe<&2, Cells.Cell<Spec.Entry>>}
) -> {
  Cell.entry(m) == Some{e}: Maybe<&2, Spec.Entry>
} -> {Cell.entry(m2) == Some{e}: Maybe<&2, Spec.Entry>}:
  match m:
    case None{}:
      h => Empty.absurd(
        {Cell.entry(m2) == Some{e}: Maybe<&2, Spec.Entry>},
        Maybes.Maybe.none_ne_some(Spec.Entry, e, h)
      )
    case Some{Cells.many{}}:
      h => Empty.absurd(
        {Cell.entry(m2) == Some{e}: Maybe<&2, Spec.Entry>},
        Maybes.Maybe.none_ne_some(Spec.Entry, e, h)
      )
    case Some{Cells.one{x}}:
      h =>
        +xe = Maybes.Maybe.some_inj(Spec.Entry, x, e, h)
        %Equal.sym(
          Maybe<&2, Cells.Cell<Spec.Entry>>,
          m2,
          Some{Cells.one{e}},
          keep(%xe: {
            Some{Cells.one{x}} == Some{Cells.one{_}}: Maybe<&2, Cells.Cell<Spec.Entry>>
          }; {==})
        ):
          {Cell.entry(_) == Some{e}: Maybe<&2, Spec.Entry>}
        {==}

# the entry of the slot k is kept by an agreeing join
def Kept.slot(
  +s: Spec.State(),
  +t: Spec.State(),
  +k: Spec.Slot,
  -e: Spec.Entry,
  a: {Spec.Node.agrees(s, t) == True{}: Bool}
) -> {
  Cell.entry(State.cell(s, k)) == Some{e}: Maybe<&2, Spec.Entry>
} -> {Cell.entry(State.cell(Spec.Node.join(s, t), k)) == Some{e}: Maybe<&2, Spec.Entry>}:
  Kept.entry(State.cell(s, k), State.cell(Spec.Node.join(s, t), k), e, Kept.cell(s, t, k, e, a))

# a request that x names is named by y, when y keeps the entry of x
def Kept.asked.of(
  x: Maybe<&2, Spec.Entry>,
  y: Maybe<&2, Spec.Entry>,
  -r: Asked,
  keep: @e: Spec.Entry -> {
    x == Some{e}: Maybe<&2, Spec.Entry>
  } -> {y == Some{e}: Maybe<&2, Spec.Entry>}
) -> {Asked.of(x) == Some{r}: Maybe<&2, Asked>} -> {Asked.of(y) == Some{r}: Maybe<&2, Asked>}:
  match x:
    case None{}:
      h => Empty.absurd(
        {Asked.of(y) == Some{r}: Maybe<&2, Asked>},
        Maybes.Maybe.none_ne_some(Asked, r, h)
      )
    case Some{e}:
      h =>
        %Equal.sym(
          Maybe<&2, Spec.Entry>,
          y,
          Some{e},
          keep(e)({==})
        ): {Asked.of(_) == Some{r}: Maybe<&2, Asked>}
        h

# a request that s holds is kept by an agreeing join
def Kept.asked(
  +s: Spec.State(),
  +t: Spec.State(),
  +i: Spec.Id,
  -r: Asked,
  a: {Spec.Node.agrees(s, t) == True{}: Bool}
) -> {
  State.asked(s, i) == Some{r}: Maybe<&2, Asked>
} -> {State.asked(Spec.Node.join(s, t), i) == Some{r}: Maybe<&2, Asked>}:
  Kept.asked.of(
    Cell.entry(State.cell(s, Spec.Slot.ask{i})),
    Cell.entry(State.cell(Spec.Node.join(s, t), Spec.Slot.ask{i})),
    r,
    e => Kept.slot(s, t, Spec.Slot.ask{i}, e, a)
  )

# a vote that x holds is held by y, when y keeps the entry of x
def Kept.vote.of(
  x: Maybe<&2, Spec.Entry>,
  y: Maybe<&2, Spec.Entry>,
  -j: Spec.Id,
  keep: @e: Spec.Entry -> {
    x == Some{e}: Maybe<&2, Spec.Entry>
  } -> {y == Some{e}: Maybe<&2, Spec.Entry>}
) -> {Vote.of(x) == Some{j}: Maybe<&2, Spec.Id>} -> {Vote.of(y) == Some{j}: Maybe<&2, Spec.Id>}:
  match x:
    case None{}:
      h => Empty.absurd(
        {Vote.of(y) == Some{j}: Maybe<&2, Spec.Id>},
        Maybes.Maybe.none_ne_some(Spec.Id, j, h)
      )
    case Some{e}:
      h =>
        %Equal.sym(
          Maybe<&2, Spec.Entry>,
          y,
          Some{e},
          keep(e)({==})
        ): {Vote.of(_) == Some{j}: Maybe<&2, Spec.Id>}
        h

# a vote kept as y is a vote that the quorum keeps
def Kept.one.at(
  x: Maybe<&2, Spec.Id>,
  y: Maybe<&2, Spec.Id>,
  keep: @j: Spec.Id -> {x == Some{j}: Maybe<&2, Spec.Id>} -> {y == Some{j}: Maybe<&2, Spec.Id>}
) -> {Quorums.Quorum.kept(~Spec.Id, ~Spec.Id.same, x, y) == True{}: Bool}:
  match x:
    case None{}:
      {==}
    case Some{+j}:
      %Equal.sym(Maybe<&2, Spec.Id>, y, Some{j}, keep(j)({==})):
        {Quorums.Quorum.hit(~Spec.Id, ~Spec.Id.same, _, j) == True{}: Bool}
      Id.same_refl(j)

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# every vote at the spot of s is kept by an agreeing join
def Kept.keeps(
  +s: Spec.State(),
  +t: Spec.State(),
  +c: Spec.Chain,
  +v: Spec.Id,
  ms: List<&2, String>,
  +a: {Spec.Node.agrees(s, t) == True{}: Bool}
) -> {
  Quorums.Quorum.keeps(
    ~String,
    ~Spec.Id,
    ~Spot,
    ~Spot.vote,
    ~Spec.Id.same,
    ms,
    Spot{s, c, v},
    Spot{Spec.Node.join(s, t), c, v}
  )
    == True{}: Bool
}:
  match ms:
    case Nil{}:
      {==}
    case Con{+m, +r}:
      Bools.Bool.and_both(
        Quorums.Quorum.kept(
          ~Spec.Id,
          ~Spec.Id.same,
          Spot.vote(Spot{s, c, v}, m),
          Spot.vote(Spot{Spec.Node.join(s, t), c, v}, m)
        ),
        Quorums.Quorum.keeps(
          ~String,
          ~Spec.Id,
          ~Spot,
          ~Spot.vote,
          ~Spec.Id.same,
          r,
          Spot{s, c, v},
          Spot{Spec.Node.join(s, t), c, v}
        )
      )(
        Kept.one.at(
          Spot.vote(Spot{s, c, v}, m),
          Spot.vote(Spot{Spec.Node.join(s, t), c, v}, m),
          j => Kept.vote.of(
            Cell.entry(State.cell(s, Spec.Slot.vote{m, c, v})),
            Cell.entry(State.cell(Spec.Node.join(s, t), Spec.Slot.vote{m, c, v})),
            j,
            e => Kept.slot(s, t, Spec.Slot.vote{m, c, v}, e, a)
          )
        )
      )(Kept.keeps(s, t, c, v, r, a))
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# a step to i that s holds the request of is kept by an agreeing join
def Kept.step.ask(
  s: Spec.State(),
  t: Spec.State(),
  c: Spec.Chain,
  i: Spec.Id,
  ms: List<&2, String>,
  -st: Step,
  a: {Spec.Node.agrees(s, t) == True{}: Bool},
  r: Maybe<&2, Asked>,
  er: {State.asked(s, i) == r: Maybe<&2, Asked>}
) -> {
  Step.ask(c, i, ms, r) == Some{st}: Maybe<&2, Step>
} -> {Step.ask(c, i, ms, State.asked(Spec.Node.join(s, t), i)) == Some{st}: Maybe<&2, Step>}:
  match r:
    case None{}:
      h => Empty.absurd(
        {Step.ask(c, i, ms, State.asked(Spec.Node.join(s, t), i)) == Some{st}: Maybe<&2, Step>},
        Maybes.Maybe.none_ne_some(Step, st, h)
      )
    case Some{x}:
      h =>
        %Equal.sym(
          Maybe<&2, Asked>,
          State.asked(Spec.Node.join(s, t), i),
          Some{x},
          Kept.asked(s, t, i, x, a)(er)
        ):
          {Step.ask(c, i, ms, _) == Some{st}: Maybe<&2, Step>}
        h
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# Kept.next once the winner w of the vote in s is known
def Kept.next.won(
  +s: Spec.State(),
  +t: Spec.State(),
  +c: Spec.Chain,
  +v: Spec.Id,
  +ms: List<&2, String>,
  -st: Step,
  +a: {Spec.Node.agrees(s, t) == True{}: Bool},
  w: Maybe<&2, Spec.Id>,
  ew: {
    Quorums.Quorum.winner(
      ~String,
      ~Spec.Id,
      ~Spot,
      ~Spot.vote,
      ~Spec.Id.same,
      ms,
      ms,
      Spot{s, c, v}
    )
      == w: Maybe<&2, Spec.Id>
  }
) -> {
  Step.won(s, c, ms, w) == Some{st}: Maybe<&2, Step>
} -> {
  Step.won(
    Spec.Node.join(s, t),
    c,
    ms,
    Quorums.Quorum.winner(
      ~String,
      ~Spec.Id,
      ~Spot,
      ~Spot.vote,
      ~Spec.Id.same,
      ms,
      ms,
      Spot{Spec.Node.join(s, t), c, v}
    )
  )
    == Some{st}: Maybe<&2, Step>
}:
  match w:
    case None{}:
      h => Empty.absurd(
        {
          Step.won(
            Spec.Node.join(s, t),
            c,
            ms,
            Quorums.Quorum.winner(
              ~String,
              ~Spec.Id,
              ~Spot,
              ~Spot.vote,
              ~Spec.Id.same,
              ms,
              ms,
              Spot{Spec.Node.join(s, t), c, v}
            )
          )
            == Some{st}: Maybe<&2, Step>
        },
        Maybes.Maybe.none_ne_some(Step, st, h)
      )
    case Some{+i}:
      h =>
        +g = {Spot{s, c, v}: Spot}
        +g2 = {Spot{Spec.Node.join(s, t), c, v}: Spot}
        +won = Quorums.Quorum.winner_of(
          ~String,
          ~Spec.Id,
          ~Spot,
          ~Spot.vote,
          ~Spec.Id.same,
          ~Id.same_refl,
          ~Id.same_sound,
          ms,
          g2,
          i
        )(
          Quorums.Quorum.has_more(
            ~String,
            ~Spec.Id,
            ~Spot,
            ~Spot.vote,
            ~Spec.Id.same,
            ~Id.same_sound,
            ms,
            g,
            g2,
            i
          )(
            Kept.keeps(s, t, c, v, ms, a)
          )(
            Quorums.Quorum.has_winner(
              ~String,
              ~Spec.Id,
              ~Spot,
              ~Spot.vote,
              ~Spec.Id.same,
              ms,
              ms,
              g,
              i
            )(ew)
          )
        )
        %Equal.sym(
          Maybe<&2, Spec.Id>,
          Quorums.Quorum.winner(~String, ~Spec.Id, ~Spot, ~Spot.vote, ~Spec.Id.same, ms, ms, g2),
          Some{i},
          won
        ):
          {Step.won(Spec.Node.join(s, t), c, ms, _) == Some{st}: Maybe<&2, Step>}
        Kept.step.ask(s, t, c, i, ms, st, a, State.asked(s, i), {==})(h)

# a next step of s is kept by an agreeing join
def Kept.next(
  +s: Spec.State(),
  t: Spec.State(),
  +c: Spec.Chain,
  k: Step,
  -st: Step,
  a: {Spec.Node.agrees(s, t) == True{}: Bool}
) -> {
  Chain.next(s, c, k) == Some{st}: Maybe<&2, Step>
} -> {Chain.next(Spec.Node.join(s, t), c, k) == Some{st}: Maybe<&2, Step>}:
  match k:
    case Step{+v, +ms}:
      Kept.next.won(
        s,
        t,
        c,
        v,
        ms,
        st,
        a,
        Quorums.Quorum.winner(
          ~String,
          ~Spec.Id,
          ~Spot,
          ~Spot.vote,
          ~Spec.Id.same,
          ms,
          ms,
          Spot{s, c, v}
        ),
        {==}
      )

# Walks
# -----

# a walk from no next step is empty
def Walk.none(
  +g: Nat,
  s: Spec.State(),
  c: Spec.Chain
) -> {Chain.walk(g, s, c, None{}) == []: List<&2, Spec.Id>}:
  match g:
    case 0n:
      {==}
    case 1n+e:
      {==}

# a walk from no next step ends where it starts
def Last.none(
  +g: Nat,
  s: Spec.State(),
  c: Spec.Chain,
  k: Step
) -> {Chain.last(g, s, c, k, None{}) == k: Step}:
  match g:
    case 0n:
      {==}
    case 1n+e:
      {==}

# a walk of f steps has at most f versions
def Walk.length(
  +f: Nat,
  +s: Spec.State(),
  +c: Spec.Chain,
  nx: Maybe<&2, Step>
) -> {Nat.is_le(List.length(&2, Spec.Id, Chain.walk(f, s, c, nx)), f) == True{}: Bool}:
  match f nx:
    case 0n m:
      {==}
    case 1n+e None{}:
      {==}
    case 1n+e Some{Step{i, ms}}:
      Walk.length(e, s, c, Chain.next(s, c, Step{i, ms}))

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Ext.walk once the next step nx after k in s is known
def Ext.walk.at(
  e: Nat,
  g: Nat,
  s: Spec.State(),
  t: Spec.State(),
  c: Spec.Chain,
  k: Step,
  a: {Spec.Node.agrees(s, t) == True{}: Bool},
  nx: Maybe<&2, Step>,
  enx: {Chain.next(s, c, k) == nx: Maybe<&2, Step>},
  ih: @k2: Step -> {
    Nat.is_le(e, g) == True{}: Bool
  } -> {
    Chain.walk(
      g,
      Spec.Node.join(s, t),
      c,
      Chain.next(Spec.Node.join(s, t), c, k2)
    )
      == List.append(
        &2,
        Spec.Id,
        Chain.walk(e, s, c, Chain.next(s, c, k2)),
        Chain.walk(
          Nat.sub(g, List.length(&2, Spec.Id, Chain.walk(e, s, c, Chain.next(s, c, k2)))),
          Spec.Node.join(s, t),
          c,
          Chain.next(Spec.Node.join(s, t), c, Chain.last(e, s, c, k2, Chain.next(s, c, k2)))
        )
      ): List<&2, Spec.Id>
  }
) -> {
  Nat.is_le(e, g) == True{}: Bool
} -> {
  Chain.walk(
    1n+g,
    Spec.Node.join(s, t),
    c,
    Chain.next(Spec.Node.join(s, t), c, k)
  )
    == List.append(
      &2,
      Spec.Id,
      Chain.walk(1n+e, s, c, nx),
      Chain.walk(
        Nat.sub(1n+g, List.length(&2, Spec.Id, Chain.walk(1n+e, s, c, nx))),
        Spec.Node.join(s, t),
        c,
        Chain.next(Spec.Node.join(s, t), c, Chain.last(1n+e, s, c, k, nx))
      )
    ): List<&2, Spec.Id>
}:
  match nx:
    case None{}:
      le =>
        %Equal.sym(Nat, Nat.sub(1n+g, 0n), 1n+g, Nats.Nat.sub_zero(1n+g)):
          {
            Chain.walk(
              1n+g,
              Spec.Node.join(s, t),
              c,
              Chain.next(Spec.Node.join(s, t), c, k)
            )
              == Chain.walk(
                _,
                Spec.Node.join(s, t),
                c,
                Chain.next(Spec.Node.join(s, t), c, k)
              ): List<&2, Spec.Id>
          }
        {==}
    case Some{Step{i, ms}}:
      le =>
        %Equal.sym(
          Maybe<&2, Step>,
          Chain.next(Spec.Node.join(s, t), c, k),
          Some{Step{i, ms}},
          Kept.next(s, t, c, k, Step{i, ms}, a)(enx)
        ):
          {
            Chain.walk(
              1n+g,
              Spec.Node.join(s, t),
              c,
              _
            )
              == List.append(
                &2,
                Spec.Id,
                i <> Chain.walk(e, s, c, Chain.next(s, c, Step{i, ms})),
                Chain.walk(
                  Nat.sub(
                    1n+g,
                    1n+List.length(&2, Spec.Id, Chain.walk(e, s, c, Chain.next(s, c, Step{i, ms})))
                  ),
                  Spec.Node.join(s, t),
                  c,
                  Chain.next(
                    Spec.Node.join(s, t),
                    c,
                    Chain.last(e, s, c, Step{i, ms}, Chain.next(s, c, Step{i, ms}))
                  )
                )
              ): List<&2, Spec.Id>
          }
        %ih(Step{i, ms})(le):
          {
            i
              <> Chain.walk(
                g,
                Spec.Node.join(s, t),
                c,
                Chain.next(Spec.Node.join(s, t), c, Step{i, ms})
              )
              == i
              <> _: List<&2, Spec.Id>
          }
        {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# a walk of s, then the walk of s and t from where it ended, is the walk of s
# and t: when t agrees with s, and s and t walk at least as far
def Ext.walk(
  +f: Nat,
  +g: Nat,
  +s: Spec.State(),
  +t: Spec.State(),
  +c: Spec.Chain,
  +k: Step,
  +a: {Spec.Node.agrees(s, t) == True{}: Bool}
) -> {
  Nat.is_le(f, g) == True{}: Bool
} -> {
  Chain.walk(
    g,
    Spec.Node.join(s, t),
    c,
    Chain.next(Spec.Node.join(s, t), c, k)
  )
    == List.append(
      &2,
      Spec.Id,
      Chain.walk(f, s, c, Chain.next(s, c, k)),
      Chain.walk(
        Nat.sub(g, List.length(&2, Spec.Id, Chain.walk(f, s, c, Chain.next(s, c, k)))),
        Spec.Node.join(s, t),
        c,
        Chain.next(Spec.Node.join(s, t), c, Chain.last(f, s, c, k, Chain.next(s, c, k)))
      )
    ): List<&2, Spec.Id>
}:
  match f g:
    case 0n w:
      le =>
        %Equal.sym(Nat, Nat.sub(w, 0n), w, Nats.Nat.sub_zero(w)):
          {
            Chain.walk(
              w,
              Spec.Node.join(s, t),
              c,
              Chain.next(Spec.Node.join(s, t), c, k)
            )
              == Chain.walk(
                _,
                Spec.Node.join(s, t),
                c,
                Chain.next(Spec.Node.join(s, t), c, k)
              ): List<&2, Spec.Id>
          }
        {==}
    case 1n+e 0n:
      le => Empty.absurd(
        {
          Chain.walk(
            0n,
            Spec.Node.join(s, t),
            c,
            Chain.next(Spec.Node.join(s, t), c, k)
          )
            == List.append(
              &2,
              Spec.Id,
              Chain.walk(1n+e, s, c, Chain.next(s, c, k)),
              Chain.walk(
                Nat.sub(0n, List.length(&2, Spec.Id, Chain.walk(1n+e, s, c, Chain.next(s, c, k)))),
                Spec.Node.join(s, t),
                c,
                Chain.next(Spec.Node.join(s, t), c, Chain.last(1n+e, s, c, k, Chain.next(s, c, k)))
              )
            ): List<&2, Spec.Id>
        },
        Shared.Bool.false_ne_true(le)
      )
    case 1n+e 1n+h:
      Ext.walk.at(
        e,
        h,
        s,
        t,
        c,
        k,
        a,
        Chain.next(s, c, k),
        {==},
        k2 => Ext.walk(e, h, s, t, c, k2, a)
      )
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Ext.last once the next step nx after k in s is known
def Ext.last.at(
  e: Nat,
  g: Nat,
  s: Spec.State(),
  t: Spec.State(),
  c: Spec.Chain,
  k: Step,
  a: {Spec.Node.agrees(s, t) == True{}: Bool},
  nx: Maybe<&2, Step>,
  enx: {Chain.next(s, c, k) == nx: Maybe<&2, Step>},
  ih: @k2: Step -> {
    Nat.is_le(e, g) == True{}: Bool
  } -> {
    Chain.last(
      g,
      Spec.Node.join(s, t),
      c,
      k2,
      Chain.next(Spec.Node.join(s, t), c, k2)
    )
      == Chain.last(
        Nat.sub(g, List.length(&2, Spec.Id, Chain.walk(e, s, c, Chain.next(s, c, k2)))),
        Spec.Node.join(s, t),
        c,
        Chain.last(e, s, c, k2, Chain.next(s, c, k2)),
        Chain.next(Spec.Node.join(s, t), c, Chain.last(e, s, c, k2, Chain.next(s, c, k2)))
      ): Step
  }
) -> {
  Nat.is_le(e, g) == True{}: Bool
} -> {
  Chain.last(
    1n+g,
    Spec.Node.join(s, t),
    c,
    k,
    Chain.next(Spec.Node.join(s, t), c, k)
  )
    == Chain.last(
      Nat.sub(1n+g, List.length(&2, Spec.Id, Chain.walk(1n+e, s, c, nx))),
      Spec.Node.join(s, t),
      c,
      Chain.last(1n+e, s, c, k, nx),
      Chain.next(Spec.Node.join(s, t), c, Chain.last(1n+e, s, c, k, nx))
    ): Step
}:
  match nx:
    case None{}:
      le => {==}
    case Some{Step{i, ms}}:
      le =>
        %Equal.sym(
          Maybe<&2, Step>,
          Chain.next(Spec.Node.join(s, t), c, k),
          Some{Step{i, ms}},
          Kept.next(s, t, c, k, Step{i, ms}, a)(enx)
        ):
          {
            Chain.last(
              1n+g,
              Spec.Node.join(s, t),
              c,
              k,
              _
            )
              == Chain.last(
                Nat.sub(
                  g,
                  List.length(&2, Spec.Id, Chain.walk(e, s, c, Chain.next(s, c, Step{i, ms})))
                ),
                Spec.Node.join(s, t),
                c,
                Chain.last(e, s, c, Step{i, ms}, Chain.next(s, c, Step{i, ms})),
                Chain.next(
                  Spec.Node.join(s, t),
                  c,
                  Chain.last(e, s, c, Step{i, ms}, Chain.next(s, c, Step{i, ms}))
                )
              ): Step
          }
        ih(Step{i, ms})(le)
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# the last step of s, walked on in s and t, is the last step of s and t: when t
# agrees with s, and s and t walk at least as far
def Ext.last(
  +f: Nat,
  +g: Nat,
  +s: Spec.State(),
  +t: Spec.State(),
  +c: Spec.Chain,
  +k: Step,
  +a: {Spec.Node.agrees(s, t) == True{}: Bool}
) -> {
  Nat.is_le(f, g) == True{}: Bool
} -> {
  Chain.last(
    g,
    Spec.Node.join(s, t),
    c,
    k,
    Chain.next(Spec.Node.join(s, t), c, k)
  )
    == Chain.last(
      Nat.sub(g, List.length(&2, Spec.Id, Chain.walk(f, s, c, Chain.next(s, c, k)))),
      Spec.Node.join(s, t),
      c,
      Chain.last(f, s, c, k, Chain.next(s, c, k)),
      Chain.next(Spec.Node.join(s, t), c, Chain.last(f, s, c, k, Chain.next(s, c, k)))
    ): Step
}:
  match f g:
    case 0n w:
      le =>
        %Equal.sym(Nat, Nat.sub(w, 0n), w, Nats.Nat.sub_zero(w)):
          {
            Chain.last(
              w,
              Spec.Node.join(s, t),
              c,
              k,
              Chain.next(Spec.Node.join(s, t), c, k)
            )
              == Chain.last(
                _,
                Spec.Node.join(s, t),
                c,
                k,
                Chain.next(Spec.Node.join(s, t), c, k)
              ): Step
          }
        {==}
    case 1n+e 0n:
      le => Empty.absurd(
        {
          Chain.last(
            0n,
            Spec.Node.join(s, t),
            c,
            k,
            Chain.next(Spec.Node.join(s, t), c, k)
          )
            == Chain.last(
              Nat.sub(0n, List.length(&2, Spec.Id, Chain.walk(1n+e, s, c, Chain.next(s, c, k)))),
              Spec.Node.join(s, t),
              c,
              Chain.last(1n+e, s, c, k, Chain.next(s, c, k)),
              Chain.next(Spec.Node.join(s, t), c, Chain.last(1n+e, s, c, k, Chain.next(s, c, k)))
            ): Step
        },
        Shared.Bool.false_ne_true(le)
      )
    case 1n+e 1n+h:
      Ext.last.at(
        e,
        h,
        s,
        t,
        c,
        k,
        a,
        Chain.next(s, c, k),
        {==},
        k2 => Ext.last(e, h, s, t, c, k2, a)
      )
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# Chains kept
# -----------

# nothing taken of a list is nothing
def List.take_zero(
  xs: List<&2, Spec.Id>
) -> {List.take(&2, Spec.Id, xs, 0n) == []: List<&2, Spec.Id>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, r}:
      {==}

# an agreeing join walks at least as far
def State.fuel_le(
  s: Spec.State(),
  t: Spec.State()
) -> {Nat.is_le(State.fuel(s), State.fuel(Spec.Node.join(s, t))) == True{}: Bool}:
  Tries.Trie.size_union(
    ~Cells.Cell<Spec.Entry>,
    ~Cells.Cell.join(~Spec.Entry, ~Spec.Entry.same),
    s,
    t
  )

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Spec.Node.chain_kept from the first step m
def Kept.chain.from(
  +s: Spec.State(),
  +t: Spec.State(),
  +c: Spec.Chain,
  a: {Spec.Node.agrees(s, t) == True{}: Bool},
  m: Maybe<&2, Step>
) -> {
  List.take(
    &2,
    Spec.Id,
    Chain.from(Spec.Node.join(s, t), c, m),
    List.length(&2, Spec.Id, Chain.from(s, c, m))
  )
    == Chain.from(s, c, m): List<&2, Spec.Id>
}:
  match m:
    case None{}:
      {==}
    case Some{Step{+i, +ms}}:
      +w = Chain.walk(State.fuel(s), s, c, Chain.next(s, c, Step{i, ms}))
      x = Chain.walk(
        Nat.sub(State.fuel(Spec.Node.join(s, t)), List.length(&2, Spec.Id, w)),
        Spec.Node.join(s, t),
        c,
        Chain.next(
          Spec.Node.join(s, t),
          c,
          Chain.last(State.fuel(s), s, c, Step{i, ms}, Chain.next(s, c, Step{i, ms}))
        )
      )
      %Equal.sym(
        List<&2, Spec.Id>,
        Chain.walk(
          State.fuel(Spec.Node.join(s, t)),
          Spec.Node.join(s, t),
          c,
          Chain.next(Spec.Node.join(s, t), c, Step{i, ms})
        ),
        List.append(&2, Spec.Id, w, x),
        Ext.walk(
          State.fuel(s),
          State.fuel(Spec.Node.join(s, t)),
          s,
          t,
          c,
          Step{i, ms},
          a
        )(State.fuel_le(s, t))
      ):
        {
          List.take(
            &2,
            Spec.Id,
            i <> _,
            1n+List.length(&2, Spec.Id, w)
          )
            == i
            <> w: List<&2, Spec.Id>
        }
      %Lists.List.take_append(
        Spec.Id,
        w,
        x
      ): {
        i
          <> List.take(&2, Spec.Id, List.append(&2, Spec.Id, w, x), List.length(&2, Spec.Id, w))
          == i
          <> _: List<&2, Spec.Id>
      }
      {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# Spec.Node.chain_kept once the request r of the first version i is known
def Kept.chain.ask(
  +s: Spec.State(),
  +t: Spec.State(),
  +c: Spec.Chain,
  +a: {Spec.Node.agrees(s, t) == True{}: Bool},
  +i: Spec.Id,
  ms: List<&2, String>,
  r: Maybe<&2, Asked>,
  er: {State.asked(s, i) == r: Maybe<&2, Asked>}
) -> {
  List.take(
    &2,
    Spec.Id,
    Chain.from(Spec.Node.join(s, t), c, Step.ask(c, i, ms, State.asked(Spec.Node.join(s, t), i))),
    List.length(&2, Spec.Id, Chain.from(s, c, Step.ask(c, i, ms, r)))
  )
    == Chain.from(s, c, Step.ask(c, i, ms, r)): List<&2, Spec.Id>
}:
  match r:
    case None{}:
      List.take_zero(
        Chain.from(
          Spec.Node.join(s, t),
          c,
          Step.ask(c, i, ms, State.asked(Spec.Node.join(s, t), i))
        )
      )
    case Some{x}:
      %Equal.sym(
        Maybe<&2, Asked>,
        State.asked(Spec.Node.join(s, t), i),
        Some{x},
        Kept.asked(s, t, i, x, a)(er)
      ):
        {
          List.take(
            &2,
            Spec.Id,
            Chain.from(Spec.Node.join(s, t), c, Step.ask(c, i, ms, _)),
            List.length(&2, Spec.Id, Chain.from(s, c, Step.ask(c, i, ms, Some{x})))
          )
            == Chain.from(s, c, Step.ask(c, i, ms, Some{x})): List<&2, Spec.Id>
        }
      Kept.chain.from(s, t, c, a, Step.ask(c, i, ms, Some{x}))

# Spec.Node.chain_kept once the first step mr of the claim is known
def Kept.chain.root(
  +s: Spec.State(),
  t: Spec.State(),
  c: Spec.Chain,
  a: {Spec.Node.agrees(s, t) == True{}: Bool},
  mr: Maybe<&2, Step>
) -> {
  List.take(
    &2,
    Spec.Id,
    Chain.from(Spec.Node.join(s, t), c, Chain.root.of(Spec.Node.join(s, t), c, mr)),
    List.length(&2, Spec.Id, Chain.from(s, c, Chain.root.of(s, c, mr)))
  )
    == Chain.from(s, c, Chain.root.of(s, c, mr)): List<&2, Spec.Id>
}:
  match mr:
    case None{}:
      {==}
    case Some{Step{+i, ms}}:
      Kept.chain.ask(s, t, c, a, i, ms, State.asked(s, i), {==})

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
def Spec.Node.chain_kept(s, t, c):
  +s = s
  t = t
  +c = c
  +a => hc =>
    %Equal.sym(
      Maybe<&2, Spec.Entry>,
      Spec.Node.claim(Spec.Node.join(s, t), c),
      Spec.Node.claim(s, c),
      hc
    ):
      {
        List.take(
          &2,
          Spec.Id,
          Chain.from(Spec.Node.join(s, t), c, Chain.root.of(Spec.Node.join(s, t), c, Root.of(_))),
          List.length(&2, Spec.Id, Spec.Node.chain(s, c))
        )
          == Spec.Node.chain(s, c): List<&2, Spec.Id>
      }
    Kept.chain.root(s, t, c, a, Root.of(Spec.Node.claim(s, c)))
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# Growth
# ------

# a chain of s and t, from its first step st, is the chain of s, then the walk
# of s and t from the last step L of s
def Grow.from(
  +s: Spec.State(),
  +t: Spec.State(),
  +c: Spec.Chain,
  a: {Spec.Node.agrees(s, t) == True{}: Bool},
  st: Step,
  -l: Step,
  el: {Chain.last(State.fuel(s), s, c, st, Chain.next(s, c, st)) == l: Step}
) -> {
  Chain.from(
    Spec.Node.join(s, t),
    c,
    Some{st}
  )
    == List.append(
      &2,
      Spec.Id,
      Chain.from(s, c, Some{st}),
      Chain.walk(
        Nat.sub(
          State.fuel(Spec.Node.join(s, t)),
          List.length(&2, Spec.Id, Chain.walk(State.fuel(s), s, c, Chain.next(s, c, st)))
        ),
        Spec.Node.join(s, t),
        c,
        Chain.next(Spec.Node.join(s, t), c, l)
      )
    ): List<&2, Spec.Id>
}:
  match st:
    case Step{+i, +ms}:
      w = Chain.walk(State.fuel(s), s, c, Chain.next(s, c, Step{i, ms}))
      g = Nat.sub(State.fuel(Spec.Node.join(s, t)), List.length(&2, Spec.Id, w))
      %el:
        {
          i
            <> Chain.walk(
              State.fuel(Spec.Node.join(s, t)),
              Spec.Node.join(s, t),
              c,
              Chain.next(Spec.Node.join(s, t), c, Step{i, ms})
            )
            == i
            <> List.append(
              &2,
              Spec.Id,
              w,
              Chain.walk(g, Spec.Node.join(s, t), c, Chain.next(Spec.Node.join(s, t), c, _))
            ): List<&2, Spec.Id>
        }
      %Ext.walk(
        State.fuel(s),
        State.fuel(Spec.Node.join(s, t)),
        s,
        t,
        c,
        Step{i, ms},
        a
      )(State.fuel_le(s, t)):
        {
          i
            <> Chain.walk(
              State.fuel(Spec.Node.join(s, t)),
              Spec.Node.join(s, t),
              c,
              Chain.next(Spec.Node.join(s, t), c, Step{i, ms})
            )
            == i
            <> _: List<&2, Spec.Id>
        }
      {==}

# the last step of s and t, from the first step st, is the last step of the
# walk of s and t from the last step l of s
def Grow.last(
  +s: Spec.State(),
  +t: Spec.State(),
  +c: Spec.Chain,
  a: {Spec.Node.agrees(s, t) == True{}: Bool},
  +st: Step,
  -l: Step,
  el: {Chain.last(State.fuel(s), s, c, st, Chain.next(s, c, st)) == l: Step}
) -> {
  Chain.last(
    State.fuel(Spec.Node.join(s, t)),
    Spec.Node.join(s, t),
    c,
    st,
    Chain.next(Spec.Node.join(s, t), c, st)
  )
    == Chain.last(
      Nat.sub(
        State.fuel(Spec.Node.join(s, t)),
        List.length(&2, Spec.Id, Chain.walk(State.fuel(s), s, c, Chain.next(s, c, st)))
      ),
      Spec.Node.join(s, t),
      c,
      l,
      Chain.next(Spec.Node.join(s, t), c, l)
    ): Step
}:
  g = Nat.sub(
    State.fuel(Spec.Node.join(s, t)),
    List.length(&2, Spec.Id, Chain.walk(State.fuel(s), s, c, Chain.next(s, c, st)))
  )
  %el:
    {
      Chain.last(
        State.fuel(Spec.Node.join(s, t)),
        Spec.Node.join(s, t),
        c,
        st,
        Chain.next(Spec.Node.join(s, t), c, st)
      )
        == Chain.last(g, Spec.Node.join(s, t), c, _, Chain.next(Spec.Node.join(s, t), c, _)): Step
    }
  Ext.last(State.fuel(s), State.fuel(Spec.Node.join(s, t)), s, t, c, st, a)(State.fuel_le(s, t))

# a first step of s stays when the claim stays
def Grow.root.of(
  +s: Spec.State(),
  t: Spec.State(),
  c: Spec.Chain,
  a: {Spec.Node.agrees(s, t) == True{}: Bool},
  mr: Maybe<&2, Step>,
  -st: Step
) -> {
  Chain.root.of(s, c, mr) == Some{st}: Maybe<&2, Step>
} -> {Chain.root.of(Spec.Node.join(s, t), c, mr) == Some{st}: Maybe<&2, Step>}:
  match mr:
    case None{}:
      h => Empty.absurd(
        {Chain.root.of(Spec.Node.join(s, t), c, None{}) == Some{st}: Maybe<&2, Step>},
        Maybes.Maybe.none_ne_some(Step, st, h)
      )
    case Some{Step{+i, ms}}:
      Kept.step.ask(s, t, c, i, ms, st, a, State.asked(s, i), {==})

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# a first step of s stays in s and t when the claim stays
def Grow.root(
  +s: Spec.State(),
  t: Spec.State(),
  +c: Spec.Chain,
  a: {Spec.Node.agrees(s, t) == True{}: Bool},
  hc: {Spec.Node.claim(Spec.Node.join(s, t), c) == Spec.Node.claim(s, c): Maybe<&2, Spec.Entry>},
  -st: Step
) -> {
  Chain.root(s, c) == Some{st}: Maybe<&2, Step>
} -> {Chain.root(Spec.Node.join(s, t), c) == Some{st}: Maybe<&2, Step>}:
  h =>
    %Equal.sym(
      Maybe<&2, Spec.Entry>,
      Spec.Node.claim(Spec.Node.join(s, t), c),
      Spec.Node.claim(s, c),
      hc
    ):
      {Chain.root.of(Spec.Node.join(s, t), c, Root.of(_)) == Some{st}: Maybe<&2, Step>}
    Grow.root.of(s, t, c, a, Root.of(Spec.Node.claim(s, c)), st)(h)

# a chain whose last step is l has a first step that leads to l, when r is its
# first step
def Start.of(
  s: Spec.State(),
  c: Spec.Chain,
  r: Maybe<&2, Step>,
  -l: Step
) -> {
  Chain.cursor.of(s, c, r) == Some{l}: Maybe<&2, Step>
} -> (
  &st: Step -> {
    r == Some{st}: Maybe<&2, Step>
  }
    & {Chain.last(State.fuel(s), s, c, st, Chain.next(s, c, st)) == l: Step}
):
  match r:
    case None{}:
      h => Empty.absurd(
        &st: Step -> {
          None{} == Some{st}: Maybe<&2, Step>
        }
          & {Chain.last(State.fuel(s), s, c, st, Chain.next(s, c, st)) == l: Step},
        Maybes.Maybe.none_ne_some(Step, l, h)
      )
    case Some{st}:
      h => (
        st,
        (
          {==},
          Maybes.Maybe.some_inj(
            Step,
            Chain.last(State.fuel(s), s, c, st, Chain.next(s, c, st)),
            l,
            h
          )
        )
      )

# Stay.chain once the first step st of the chain is known
def Stay.chain.of(
  +s: Spec.State(),
  +t: Spec.State(),
  +c: Spec.Chain,
  +a: {Spec.Node.agrees(s, t) == True{}: Bool},
  hc: {Spec.Node.claim(Spec.Node.join(s, t), c) == Spec.Node.claim(s, c): Maybe<&2, Spec.Entry>},
  l: Step,
  en: {Chain.next(Spec.Node.join(s, t), c, l) == None{}: Maybe<&2, Step>},
  pr: &st: Step -> {
    Chain.root(s, c) == Some{st}: Maybe<&2, Step>
  }
    & {Chain.last(State.fuel(s), s, c, st, Chain.next(s, c, st)) == l: Step}
) -> {Spec.Node.chain(Spec.Node.join(s, t), c) == Spec.Node.chain(s, c): List<&2, Spec.Id>}:
  match pr:
    case (+st, (+er, el)):
      +j = Spec.Node.join(s, t)
      g = Nat.sub(
        State.fuel(j),
        List.length(&2, Spec.Id, Chain.walk(State.fuel(s), s, c, Chain.next(s, c, st)))
      )
      x = Chain.from(s, c, Some{st})
      Equal.trans(
        List<&2, Spec.Id>,
        Chain.from(j, c, Chain.root(j, c)),
        Chain.from(j, c, Some{st}),
        Chain.from(s, c, Chain.root(s, c)),
        Equal.cong(
          Maybe<&2, Step>,
          List<&2, Spec.Id>,
          z => Chain.from(j, c, z),
          Chain.root(j, c),
          Some{st},
          Grow.root(s, t, c, a, hc, st)(er)
        ),
        Equal.trans(
          List<&2, Spec.Id>,
          Chain.from(j, c, Some{st}),
          List.append(&2, Spec.Id, x, Chain.walk(g, j, c, Chain.next(j, c, l))),
          Chain.from(s, c, Chain.root(s, c)),
          Grow.from(s, t, c, a, st, l, el),
          Equal.trans(
            List<&2, Spec.Id>,
            List.append(&2, Spec.Id, x, Chain.walk(g, j, c, Chain.next(j, c, l))),
            List.append(&2, Spec.Id, x, []),
            Chain.from(s, c, Chain.root(s, c)),
            %Equal.sym(Maybe<&2, Step>, Chain.next(j, c, l), None{}, en):
              {List.append(&2, Spec.Id, x, Chain.walk(g, j, c, _)) == List.append(&2, Spec.Id, x, []): List<&2, Spec.Id>}
            Equal.cong(List<&2, Spec.Id>, List<&2, Spec.Id>, z => List.append(&2, Spec.Id, x, z), Chain.walk(g, j, c, None{}), [], Walk.none(g, j, c)),
            Equal.trans(List<&2, Spec.Id>, List.append(&2, Spec.Id, x, []), x, Chain.from(s, c, Chain.root(s, c)), Lists.List.append_nil(Spec.Id, x), Equal.sym(List<&2, Spec.Id>, Chain.from(s, c, Chain.root(s, c)), x, Equal.cong(Maybe<&2, Step>, List<&2, Spec.Id>, z => Chain.from(s, c, z), Chain.root(s, c), Some{st}, er))))
        )
      )

# a chain stays as it was when nothing follows its last step l in s and t
def Stay.chain(
  +s: Spec.State(),
  t: Spec.State(),
  +c: Spec.Chain,
  a: {Spec.Node.agrees(s, t) == True{}: Bool},
  hc: {Spec.Node.claim(Spec.Node.join(s, t), c) == Spec.Node.claim(s, c): Maybe<&2, Spec.Entry>},
  l: Step,
  ecur: {Chain.cursor(s, c) == Some{l}: Maybe<&2, Step>},
  en: {Chain.next(Spec.Node.join(s, t), c, l) == None{}: Maybe<&2, Step>}
) -> {Spec.Node.chain(Spec.Node.join(s, t), c) == Spec.Node.chain(s, c): List<&2, Spec.Id>}:
  Stay.chain.of(s, t, c, a, hc, l, en, Start.of(s, c, Chain.root(s, c), l)(ecur))

# Stay.cursor once the first step st of the chain is known
def Stay.cursor.of(
  +s: Spec.State(),
  +t: Spec.State(),
  +c: Spec.Chain,
  +a: {Spec.Node.agrees(s, t) == True{}: Bool},
  hc: {Spec.Node.claim(Spec.Node.join(s, t), c) == Spec.Node.claim(s, c): Maybe<&2, Spec.Entry>},
  l: Step,
  en: {Chain.next(Spec.Node.join(s, t), c, l) == None{}: Maybe<&2, Step>},
  pr: &st: Step -> {
    Chain.root(s, c) == Some{st}: Maybe<&2, Step>
  }
    & {Chain.last(State.fuel(s), s, c, st, Chain.next(s, c, st)) == l: Step}
) -> {Chain.cursor(Spec.Node.join(s, t), c) == Some{l}: Maybe<&2, Step>}:
  match pr:
    case (+st, (er, el)):
      +j = Spec.Node.join(s, t)
      g = Nat.sub(
        State.fuel(j),
        List.length(&2, Spec.Id, Chain.walk(State.fuel(s), s, c, Chain.next(s, c, st)))
      )
      %Equal.sym(Maybe<&2, Step>, Chain.root(j, c), Some{st}, Grow.root(s, t, c, a, hc, st)(er)):
        {Chain.cursor.of(j, c, _) == Some{l}: Maybe<&2, Step>}
      %Equal.sym(
        Step,
        Chain.last(State.fuel(j), j, c, st, Chain.next(j, c, st)),
        Chain.last(g, j, c, l, Chain.next(j, c, l)),
        Grow.last(s, t, c, a, st, l, el)
      ):
        {Some{_} == Some{l}: Maybe<&2, Step>}
      %Equal.sym(
        Maybe<&2, Step>,
        Chain.next(j, c, l),
        None{},
        en
      ): {Some{Chain.last(g, j, c, l, _)} == Some{l}: Maybe<&2, Step>}
      %Equal.sym(
        Step,
        Chain.last(g, j, c, l, None{}),
        l,
        Last.none(g, j, c, l)
      ): {Some{_} == Some{l}: Maybe<&2, Step>}
      {==}

# the last step of a chain stays when nothing follows it in s and t
def Stay.cursor(
  +s: Spec.State(),
  t: Spec.State(),
  +c: Spec.Chain,
  a: {Spec.Node.agrees(s, t) == True{}: Bool},
  hc: {Spec.Node.claim(Spec.Node.join(s, t), c) == Spec.Node.claim(s, c): Maybe<&2, Spec.Entry>},
  l: Step,
  ecur: {Chain.cursor(s, c) == Some{l}: Maybe<&2, Step>},
  en: {Chain.next(Spec.Node.join(s, t), c, l) == None{}: Maybe<&2, Step>}
) -> {Chain.cursor(Spec.Node.join(s, t), c) == Some{l}: Maybe<&2, Step>}:
  Stay.cursor.of(s, t, c, a, hc, l, en, Start.of(s, c, Chain.root(s, c), l)(ecur))
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# Owner steps
# -----------

# the vote of n at the spot of s is the entry of its slot
def Spot.vote_of(
  s: Spec.State(),
  c: Spec.Chain,
  v: Spec.Id,
  n: String,
  -m: Maybe<&2, Cells.Cell<Spec.Entry>>
) -> {
  State.cell(s, Spec.Slot.vote{n, c, v}) == m: Maybe<&2, Cells.Cell<Spec.Entry>>
} -> {Spot.vote(Spot{s, c, v}, n) == Vote.of(Cell.entry(m)): Maybe<&2, Spec.Id>}:
  h => Equal.cong(
    Maybe<&2, Cells.Cell<Spec.Entry>>,
    Maybe<&2, Spec.Id>,
    z => Vote.of(Cell.entry(z)),
    State.cell(s, Spec.Slot.vote{n, c, v}),
    m,
    h
  )

# nothing follows the step to v when its sole owner n has not voted after it
def Next.none(
  +s: Spec.State(),
  +c: Spec.Chain,
  +v: Spec.Id,
  +n: String
) -> {
  State.cell(s, Spec.Slot.vote{n, c, v}) == None{}: Maybe<&2, Cells.Cell<Spec.Entry>>
} -> {Chain.next(s, c, Step{v, [n]}) == None{}: Maybe<&2, Step>}:
  h =>
    %Equal.sym(
      Maybe<&2, Spec.Id>,
      Quorums.Quorum.winner(
        ~String,
        ~Spec.Id,
        ~Spot,
        ~Spot.vote,
        ~Spec.Id.same,
        [n],
        [n],
        Spot{s, c, v}
      ),
      None{},
      Quorums.Quorum.winner_none(
        ~String,
        ~Spec.Id,
        ~Spot,
        ~Spot.vote,
        ~Spec.Id.same,
        n,
        Spot{s, c, v}
      )(Spot.vote_of(s, c, v, n, None{})(h))
    ):
      {Step.won(s, c, [n], _) == None{}: Maybe<&2, Step>}
    {==}

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# the version i follows v when its sole owner n voted for it, and its change q
# is on the chain
def Next.one(
  +s: Spec.State(),
  +c: Spec.Chain,
  +v: Spec.Id,
  +n: String,
  i: Spec.Id,
  t: String,
  q: Spec.Ask
) -> {
  State.cell(
    s,
    Spec.Slot.vote{n, c, v}
  )
    == Some{Cells.one{Spec.Entry.vote{i}}}: Maybe<&2, Cells.Cell<Spec.Entry>>
} -> {
  State.asked(s, i) == Some{Asked{t, q}}: Maybe<&2, Asked>
} -> {
  Spec.Chain.same(Spec.Ask.chain(q), c) == True{}: Bool
} -> {Chain.next(s, c, Step{v, [n]}) == Some{Step{i, Ask.owners(q, [n])}}: Maybe<&2, Step>}:
  hv => ha => hq =>
    %Equal.sym(
      Maybe<&2, Spec.Id>,
      Quorums.Quorum.winner(
        ~String,
        ~Spec.Id,
        ~Spot,
        ~Spot.vote,
        ~Spec.Id.same,
        [n],
        [n],
        Spot{s, c, v}
      ),
      Some{i},
      Quorums.Quorum.winner_one(
        ~String,
        ~Spec.Id,
        ~Spot,
        ~Spot.vote,
        ~Spec.Id.same,
        ~Id.same_refl,
        n,
        Spot{s, c, v},
        i
      )(Spot.vote_of(s, c, v, n, Some{Cells.one{Spec.Entry.vote{i}}})(hv))
    ):
      {Step.won(s, c, [n], _) == Some{Step{i, Ask.owners(q, [n])}}: Maybe<&2, Step>}
    %Equal.sym(Maybe<&2, Asked>, State.asked(s, i), Some{Asked{t, q}}, ha):
      {Step.ask(c, i, [n], _) == Some{Step{i, Ask.owners(q, [n])}}: Maybe<&2, Step>}
    %Equal.sym(Bool, Spec.Chain.same(Spec.Ask.chain(q), c), True{}, hq):
      {Step.if(_, i, q, [n]) == Some{Step{i, Ask.owners(q, [n])}}: Maybe<&2, Step>}
    {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# the last step of a chain with the head v and the sole owner n is the step to v
def Owner.cursor(
  +m: Maybe<&2, Step>,
  n: String,
  v: Spec.Id
) -> {
  Step.owners.of(m) == [n]: List<&2, String>
} -> {
  Maybe.map(&2, Step, Spec.Id, k => Step.version(k), m) == Some{v}: Maybe<&2, Spec.Id>
} -> {m == Some{Step{v, [n]}}: Maybe<&2, Step>}:
  match m:
    case None{}:
      ho => hh => Empty.absurd(
        {None{} == Some{Step{v, [n]}}: Maybe<&2, Step>},
        Maybes.Maybe.none_ne_some(Spec.Id, v, hh)
      )
    case Some{Step{kv, kms}}:
      ho => hh =>
        %Maybes.Maybe.some_inj(
          Spec.Id,
          kv,
          v,
          hh
        ): {Some{Step{kv, kms}} == Some{Step{_, [n]}}: Maybe<&2, Step>}
        %ho: {Some{Step{kv, kms}} == Some{Step{kv, _}}: Maybe<&2, Step>}
        {==}

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# a chain that has a last step has a claim
def Claim.of(
  s: Spec.State(),
  c: Spec.Chain,
  m: Maybe<&2, Spec.Entry>,
  em: {Spec.Node.claim(s, c) == m: Maybe<&2, Spec.Entry>},
  -l: Step
) -> {
  Chain.cursor(s, c) == Some{l}: Maybe<&2, Step>
} -> (&x: Spec.Entry -> {m == Some{x}: Maybe<&2, Spec.Entry>}):
  match m:
    case None{}:
      h => Empty.absurd(
        &x: Spec.Entry -> {None{} == Some{x}: Maybe<&2, Spec.Entry>},
        Maybes.Maybe.none_ne_some(
          Step,
          l,
          Equal.trans(
            Maybe<&2, Step>,
            None{},
            Chain.cursor(s, c),
            Some{l},
            Equal.sym(
              Maybe<&2, Step>,
              Chain.cursor(s, c),
              None{},
              Equal.cong(
                Maybe<&2, Spec.Entry>,
                Maybe<&2, Step>,
                z => Chain.cursor.of(s, c, Chain.root.of(s, c, Root.of(z))),
                Spec.Node.claim(s, c),
                None{},
                em
              )
            ),
            h
          )
        )
      )
    case Some{x}:
      h => (x, {==})
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# a node that took in a new request q of i at the time t, whose chain has the
# claim m, votes or not as Node.ask.at says
def Owner.ask(
  n: String,
  s: Spec.State(),
  i: Spec.Id,
  t: String,
  q: Spec.Ask,
  m: Maybe<&2, Spec.Entry>,
  hm: &x: Spec.Entry -> {m == Some{x}: Maybe<&2, Spec.Entry>}
) -> {
  Node.ask.root(
    n,
    s,
    State.put(s, Spec.Slot.ask{i}, Spec.Entry.ask{i, t, q}),
    i,
    q,
    m
  )
    == Node.ask.at(
      n,
      s,
      State.put(s, Spec.Slot.ask{i}, Spec.Entry.ask{i, t, q}),
      i,
      q,
      Chain.cursor(s, Spec.Ask.chain(q))
    ): Spec.State()
}:
  match hm:
    case (x, ex):
      %Equal.sym(Maybe<&2, Spec.Entry>, m, Some{x}, ex):
        {
          Node.ask.root(
            n,
            s,
            State.put(s, Spec.Slot.ask{i}, Spec.Entry.ask{i, t, q}),
            i,
            q,
            _
          )
            == Node.ask.at(
              n,
              s,
              State.put(s, Spec.Slot.ask{i}, Spec.Entry.ask{i, t, q}),
              i,
              q,
              Chain.cursor(s, Spec.Ask.chain(q))
            ): Spec.State()
        }
      {==}

# an "and" with False is False
def And.false_right(a: Bool) -> {Bool.and(a, False{}) == False{}: Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# the cell of s and one entry at k, at a key p apart from k, is the cell of s
def Fresh.cell(
  +s: Spec.State(),
  +k: List<&2, Bool>,
  +p: List<&2, Bool>,
  +x: Cells.Cell<Spec.Entry>
) -> {
  Tries.Trie.apart(k, p) == True{}: Bool
} -> {
  Tries.Trie.get(
    Cells.Cell<Spec.Entry>,
    Spec.Node.join(s, Tries.Trie.one(Cells.Cell<Spec.Entry>, k, x)),
    p
  )
    == Tries.Trie.get(Cells.Cell<Spec.Entry>, s, p): Maybe<&2, Cells.Cell<Spec.Entry>>
}:
  ap =>
    %Equal.sym(
      Maybe<&2, Cells.Cell<Spec.Entry>>,
      Tries.Trie.get(
        Cells.Cell<Spec.Entry>,
        Spec.Node.join(s, Tries.Trie.one(Cells.Cell<Spec.Entry>, k, x)),
        p
      ),
      Tries.Trie.pick(
        ~Cells.Cell<Spec.Entry>,
        ~Cells.Cell.join(~Spec.Entry, ~Spec.Entry.same),
        Tries.Trie.get(Cells.Cell<Spec.Entry>, s, p),
        Tries.Trie.get(Cells.Cell<Spec.Entry>, Tries.Trie.one(Cells.Cell<Spec.Entry>, k, x), p)
      ),
      Tries.Trie.get_union(
        ~Cells.Cell<Spec.Entry>,
        ~Cells.Cell.join(~Spec.Entry, ~Spec.Entry.same),
        s,
        Tries.Trie.one(Cells.Cell<Spec.Entry>, k, x),
        p
      )
    ):
      {_ == Tries.Trie.get(Cells.Cell<Spec.Entry>, s, p): Maybe<&2, Cells.Cell<Spec.Entry>>}
    %Equal.sym(
      Maybe<&2, Cells.Cell<Spec.Entry>>,
      Tries.Trie.get(Cells.Cell<Spec.Entry>, Tries.Trie.one(Cells.Cell<Spec.Entry>, k, x), p),
      None{},
      Tries.Trie.get_one_apart(Cells.Cell<Spec.Entry>, k, p, x)(ap)
    ):
      {
        Tries.Trie.pick(
          ~Cells.Cell<Spec.Entry>,
          ~Cells.Cell.join(~Spec.Entry, ~Spec.Entry.same),
          Tries.Trie.get(Cells.Cell<Spec.Entry>, s, p),
          _
        )
          == Tries.Trie.get(Cells.Cell<Spec.Entry>, s, p): Maybe<&2, Cells.Cell<Spec.Entry>>
      }
    Tries.Trie.pick_none(
      ~Cells.Cell<Spec.Entry>,
      ~Cells.Cell.join(~Spec.Entry, ~Spec.Entry.same),
      Tries.Trie.get(Cells.Cell<Spec.Entry>, s, p)
    )

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# the claim of a chain stays when one entry joins apart from its roots
def Fresh.claim(
  s: Spec.State(),
  k: List<&2, Bool>,
  c: Spec.Chain,
  x: Cells.Cell<Spec.Entry>
) -> {
  Tries.Trie.apart(k, Spec.Root.key(c)) == True{}: Bool
} -> {
  Spec.Node.claim(
    Spec.Node.join(s, Tries.Trie.one(Cells.Cell<Spec.Entry>, k, x)),
    c
  )
    == Spec.Node.claim(s, c): Maybe<&2, Spec.Entry>
}:
  ap => Equal.cong(
    Tries.Trie<Cells.Cell<Spec.Entry>>,
    Maybe<&2, Spec.Entry>,
    z => Spec.Root.first(Tries.Trie.values(Cells.Cell<Spec.Entry>, z)),
    Tries.Trie.under(
      Cells.Cell<Spec.Entry>,
      Spec.Node.join(s, Tries.Trie.one(Cells.Cell<Spec.Entry>, k, x)),
      Spec.Root.key(c)
    ),
    Tries.Trie.under(Cells.Cell<Spec.Entry>, s, Spec.Root.key(c)),
    Tries.Trie.under_union_apart(
      ~Cells.Cell<Spec.Entry>,
      ~Cells.Cell.join(~Spec.Entry, ~Spec.Entry.same),
      s,
      k,
      Spec.Root.key(c),
      x
    )(ap)
  )

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- an equality, or a proof, keeps each and/or as one value for the proofs to split on
def Spec.Node.write_stale(n, s, e, b, name, base, x, v):
  match e:
    case Spec.Envelope{r, w, +t}:
      +n = n
      +s = s
      +b = b
      name = name
      base = base
      x = x
      +v = v
      +i = {Spec.Id{w, r}: Spec.Id}
      +c = {Spec.Chain.branch{b}: Spec.Chain}
      +q = {Spec.Ask.write{b, name, base, x}: Spec.Ask}
      l = {Step{v, [n]}: Step}
      +ka = Spec.Slot.key(Spec.Slot.ask{i})
      kv = Spec.Slot.key(Spec.Slot.vote{n, c, v})
      +ea = {Cells.one{Spec.Entry.ask{i, t, q}}: Cells.Cell<Spec.Entry>}
      +ta = Tries.Trie.one(Cells.Cell<Spec.Entry>, ka, ea)
      s1 = Spec.Node.join(s, ta)
      +h1 => +h2 => +h3 => +h4 => h5 =>
        +ecur = Owner.cursor(Chain.cursor(s, c), n, v)(h1)(h2)
        +a = Cells.Cell.agrees_one(~Spec.Entry, ~Spec.Entry.same, s, ka, ea)(h3)
        +hc = Fresh.claim(s, ka, c, ea)({==})
        +f4 = Equal.trans(
          Maybe<&2, Cells.Cell<Spec.Entry>>,
          Tries.Trie.get(Cells.Cell<Spec.Entry>, s1, kv),
          Tries.Trie.get(Cells.Cell<Spec.Entry>, s, kv),
          None{},
          Fresh.cell(s, ka, kv, ea)({==}),
          h4
        )
        +same = Stay.chain(s, ta, c, a, hc, l, ecur, Next.none(s1, c, v, n)(f4))
        +fits = Equal.trans(
          Bool,
          Ask.fits(s, q, v),
          Maybes.Maybe.same(
            ~Octets.Bytes(),
            ~Octets.Bytes.is_eq,
            Spec.Node.content(s, name, Spec.Point.head{b}),
            Spec.Node.content_at(s, name, base)
          ),
          False{},
          Equal.sym(
            Bool,
            Maybes.Maybe.same(
              ~Octets.Bytes(),
              ~Octets.Bytes.is_eq,
              Spec.Node.content(s, name, Spec.Point.head{b}),
              Spec.Node.content_at(s, name, base)
            ),
            Ask.fits(s, q, v),
            Equal.cong(
              Maybe<&2, Spec.Id>,
              Bool,
              z => Maybes.Maybe.same(
                ~Octets.Bytes(),
                ~Octets.Bytes.is_eq,
                Res.of(s, name, z),
                Res.of(s, name, base)
              ),
              Spec.Node.head(s, b),
              Some{v},
              h2
            )
          ),
          h5
        )
        +may = Node.may_vote(n, s, c, v, [n])
        +ask = Equal.trans(
          Spec.State(),
          Spec.Node.ask(n, s, Spec.Envelope{r, w, t}, q),
          Node.ask.root(n, s, s1, i, q, Spec.Node.claim(s, c)),
          s1,
          Equal.cong(
            Maybe<&2, Cells.Cell<Spec.Entry>>,
            Spec.State(),
            z => Node.ask.fresh(n, s, i, t, q, z),
            State.cell(s, Spec.Slot.ask{i}),
            None{},
            h3
          ),
          Equal.trans(
            Spec.State(),
            Node.ask.root(n, s, s1, i, q, Spec.Node.claim(s, c)),
            Node.ask.at(n, s, s1, i, q, Chain.cursor(s, c)),
            s1,
            Owner.ask(
              n,
              s,
              i,
              t,
              q,
              Spec.Node.claim(s, c),
              Claim.of(s, c, Spec.Node.claim(s, c), {==}, l)(ecur)
            ),
            Equal.trans(
              Spec.State(),
              Node.ask.at(n, s, s1, i, q, Chain.cursor(s, c)),
              Node.ask.at(n, s, s1, i, q, Some{l}),
              s1,
              Equal.cong(
                Maybe<&2, Step>,
                Spec.State(),
                z => Node.ask.at(n, s, s1, i, q, z),
                Chain.cursor(s, c),
                Some{l},
                ecur
              ),
              Equal.cong(
                Bool,
                Spec.State(),
                z => Bool.pick(
                  Spec.State(),
                  z,
                  State.put(s1, Spec.Slot.vote{n, c, v}, Spec.Entry.vote{i}),
                  s1
                ),
                Bool.and(may, Ask.fits(s, q, v)),
                False{},
                Equal.trans(
                  Bool,
                  Bool.and(may, Ask.fits(s, q, v)),
                  Bool.and(may, False{}),
                  False{},
                  Equal.cong(Bool, Bool, z => Bool.and(may, z), Ask.fits(s, q, v), False{}, fits),
                  And.false_right(may)
                )
              )
            )
          )
        )
        Equal.trans(
          List<&2, Spec.Id>,
          Spec.Node.chain(Spec.Node.ask(n, s, Spec.Envelope{r, w, t}, q), c),
          Spec.Node.chain(s1, c),
          Spec.Node.chain(s, c),
          Equal.cong(
            Spec.State(),
            List<&2, Spec.Id>,
            z => Spec.Node.chain(z, c),
            Spec.Node.ask(n, s, Spec.Envelope{r, w, t}, q),
            s1,
            ask
          ),
          same
        )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# a list that holds a node holds it
def Owners.has(n: String) -> {Shared.List.has(~String, ~String.eq, [n], n) == True{}: Bool}:
  %Equal.sym(Bool, String.eq(n, n), True{}, Strings.String.eq_refl(n)):
    {List.any.if(u => Shared.List.has(~String, ~String.eq, [], n), _) == True{}: Bool}
  {==}

# one entry at a free key walks one step further
def Grow.fuel(
  +s: Spec.State(),
  k: List<&2, Bool>,
  x: Cells.Cell<Spec.Entry>
) -> {
  Tries.Trie.get(Cells.Cell<Spec.Entry>, s, k) == None{}: Maybe<&2, Cells.Cell<Spec.Entry>>
} -> {
  Nat.is_lt(
    State.fuel(s),
    State.fuel(Spec.Node.join(s, Tries.Trie.one(Cells.Cell<Spec.Entry>, k, x)))
  )
    == True{}: Bool
}:
  h =>
    %Equal.sym(
      Nat,
      Tries.Trie.size(
        Cells.Cell<Spec.Entry>,
        Spec.Node.join(s, Tries.Trie.one(Cells.Cell<Spec.Entry>, k, x))
      ),
      1n+Tries.Trie.size(Cells.Cell<Spec.Entry>, s),
      Tries.Trie.size_union_one(
        ~Cells.Cell<Spec.Entry>,
        ~Cells.Cell.join(~Spec.Entry, ~Spec.Entry.same),
        s,
        k,
        x
      )(h)
    ):
      {Nat.is_lt(State.fuel(s), 1n+_) == True{}: Bool}
    Nats.Nat.lt_succ(Tries.Trie.size(Cells.Cell<Spec.Entry>, s))

# the request i is in the chain of s2, s1 and the sole owner's vote for it
# after v, once the first step of the chain of s1 is known
def Written.has(
  n: String,
  +s1: Spec.State(),
  +i: Spec.Id,
  +c: Spec.Chain,
  v: Spec.Id,
  +tv: Spec.State(),
  +a2: {Spec.Node.agrees(s1, tv) == True{}: Bool},
  hc2: {
    Spec.Node.claim(Spec.Node.join(s1, tv), c) == Spec.Node.claim(s1, c): Maybe<&2, Spec.Entry>
  },
  next2: {
    Chain.next(Spec.Node.join(s1, tv), c, Step{v, [n]}) == Some{Step{i, [n]}}: Maybe<&2, Step>
  },
  grow: {Nat.is_lt(State.fuel(s1), State.fuel(Spec.Node.join(s1, tv))) == True{}: Bool},
  pr: &st: Step -> {
    Chain.root(s1, c) == Some{st}: Maybe<&2, Step>
  }
    & {Chain.last(State.fuel(s1), s1, c, st, Chain.next(s1, c, st)) == Step{v, [n]}: Step}
) -> {
  Shared.List.has(
    ~Spec.Id,
    ~Spec.Id.same,
    Spec.Node.chain(Spec.Node.join(s1, tv), c),
    i
  )
    == True{}: Bool
}:
  match pr:
    case (+st, (er, el)):
      +s2 = Spec.Node.join(s1, tv)
      +w1 = Chain.walk(State.fuel(s1), s1, c, Chain.next(s1, c, st))
      x1 = Chain.from(s1, c, Some{st})
      g = Nat.sub(State.fuel(s2), List.length(&2, Spec.Id, w1))
      g1 = Nat.sub(State.fuel(s2), 1n+List.length(&2, Spec.Id, w1))
      rest = Chain.walk(g1, s2, c, Chain.next(s2, c, Step{i, [n]}))
      gs = Nats.Nat.sub_pos(
        List.length(&2, Spec.Id, w1),
        State.fuel(s2)
      )(
        Nats.Nat.le_lt(
          List.length(&2, Spec.Id, w1),
          State.fuel(s1),
          State.fuel(s2)
        )(Walk.length(State.fuel(s1), s1, c, Chain.next(s1, c, st)))(grow)
      )
      shape = Equal.trans(
        List<&2, Spec.Id>,
        Chain.from(s2, c, Chain.root(s2, c)),
        Chain.from(s2, c, Some{st}),
        List.append(&2, Spec.Id, x1, i <> rest),
        Equal.cong(
          Maybe<&2, Step>,
          List<&2, Spec.Id>,
          z => Chain.from(s2, c, z),
          Chain.root(s2, c),
          Some{st},
          Grow.root(s1, tv, c, a2, hc2, st)(er)
        ),
        Equal.trans(
          List<&2, Spec.Id>,
          Chain.from(s2, c, Some{st}),
          List.append(&2, Spec.Id, x1, Chain.walk(g, s2, c, Chain.next(s2, c, Step{v, [n]}))),
          List.append(&2, Spec.Id, x1, i <> rest),
          Grow.from(s1, tv, c, a2, st, Step{v, [n]}, el),
          %Equal.sym(Maybe<&2, Step>, Chain.next(s2, c, Step{v, [n]}), Some{Step{i, [n]}}, next2):
            {List.append(&2, Spec.Id, x1, Chain.walk(g, s2, c, _)) == List.append(&2, Spec.Id, x1, i <> rest): List<&2, Spec.Id>}
          %Equal.sym(Nat, g, 1n+g1, gs):
            {List.append(&2, Spec.Id, x1, Chain.walk(_, s2, c, Some{Step{i, [n]}})) == List.append(&2, Spec.Id, x1, i <> rest): List<&2, Spec.Id>}
          {==})
      )
      %Equal.sym(
        List<&2, Spec.Id>,
        Spec.Node.chain(s2, c),
        List.append(&2, Spec.Id, x1, i <> rest),
        shape
      ):
        {Shared.List.has(~Spec.Id, ~Spec.Id.same, _, i) == True{}: Bool}
      Shared.List.has_middle(~Spec.Id, ~Spec.Id.same, ~Id.same_refl, x1, i, rest)

# the sole owner's vote at its head v puts the request i in the chain: it is
# Written, and its version holds the bytes x
def Written.at(
  +n: String,
  +s1: Spec.State(),
  +i: Spec.Id,
  +t: String,
  +b: String,
  +name: Resources.Name,
  base: Maybe<&2, Spec.Id>,
  x: Octets.Bytes(),
  +v: Spec.Id,
  ecur1: {Chain.cursor(s1, Spec.Chain.branch{b}) == Some{Step{v, [n]}}: Maybe<&2, Step>},
  +f4: {
    Tries.Trie.get(
      Cells.Cell<Spec.Entry>,
      s1,
      Spec.Slot.key(Spec.Slot.vote{n, Spec.Chain.branch{b}, v})
    )
      == None{}: Maybe<&2, Cells.Cell<Spec.Entry>>
  },
  cell1a: {
    Tries.Trie.get(
      Cells.Cell<Spec.Entry>,
      s1,
      Spec.Slot.key(Spec.Slot.ask{i})
    )
      == Some{
        Cells.one{Spec.Entry.ask{i, t, Spec.Ask.write{b, name, base, Spec.Content.bytes{x}}}}
      }: Maybe<&2, Cells.Cell<Spec.Entry>>
  }
) -> {
  Spec.Node.answer(
    Spec.Node.join(
      s1,
      Tries.Trie.one(
        Cells.Cell<Spec.Entry>,
        Spec.Slot.key(Spec.Slot.vote{n, Spec.Chain.branch{b}, v}),
        Cells.one{Spec.Entry.vote{i}}
      )
    ),
    i
  )
    == Spec.Answer.written{i}: Spec.Answer
}
  & {
    Spec.Node.content(
      Spec.Node.join(
        s1,
        Tries.Trie.one(
          Cells.Cell<Spec.Entry>,
          Spec.Slot.key(Spec.Slot.vote{n, Spec.Chain.branch{b}, v}),
          Cells.one{Spec.Entry.vote{i}}
        )
      ),
      name,
      Spec.Point.at{i}
    )
      == Some{x}: Maybe<&2, Octets.Bytes()>
  }:
  +c = {Spec.Chain.branch{b}: Spec.Chain}
  +q = {Spec.Ask.write{b, name, base, Spec.Content.bytes{x}}: Spec.Ask}
  l = {Step{v, [n]}: Step}
  ka = Spec.Slot.key(Spec.Slot.ask{i})
  +kv = Spec.Slot.key(Spec.Slot.vote{n, c, v})
  ea = {Cells.one{Spec.Entry.ask{i, t, q}}: Cells.Cell<Spec.Entry>}
  +ev = {Cells.one{Spec.Entry.vote{i}}: Cells.Cell<Spec.Entry>}
  +tv = Tries.Trie.one(Cells.Cell<Spec.Entry>, kv, ev)
  s2 = Spec.Node.join(s1, tv)
  a2 = Cells.Cell.agrees_one(~Spec.Entry, ~Spec.Entry.same, s1, kv, ev)(f4)
  hc2 = Fresh.claim(s1, kv, c, ev)({==})
  cell2v = Equal.trans(
    Maybe<&2, Cells.Cell<Spec.Entry>>,
    Tries.Trie.get(Cells.Cell<Spec.Entry>, s2, kv),
    Tries.Trie.pick(~Cells.Cell<Spec.Entry>, ~Cells.Cell.join(~Spec.Entry, ~Spec.Entry.same), Tries.Trie.get(Cells.Cell<Spec.Entry>, s1, kv), Tries.Trie.get(Cells.Cell<Spec.Entry>, tv, kv)),
    Some{ev},
    Tries.Trie.get_union(~Cells.Cell<Spec.Entry>, ~Cells.Cell.join(~Spec.Entry, ~Spec.Entry.same), s1, tv, kv),
    %Equal.sym(Maybe<&2, Cells.Cell<Spec.Entry>>, Tries.Trie.get(Cells.Cell<Spec.Entry>, s1, kv), None{}, f4):
      {Tries.Trie.pick(~Cells.Cell<Spec.Entry>, ~Cells.Cell.join(~Spec.Entry, ~Spec.Entry.same), _, Tries.Trie.get(Cells.Cell<Spec.Entry>, tv, kv)) == Some{ev}: Maybe<&2, Cells.Cell<Spec.Entry>>}
    Tries.Trie.get_one(Cells.Cell<Spec.Entry>, kv, ev))
  +cell2a = Equal.trans(
    Maybe<&2, Cells.Cell<Spec.Entry>>,
    Tries.Trie.get(Cells.Cell<Spec.Entry>, s2, ka),
    Tries.Trie.get(Cells.Cell<Spec.Entry>, s1, ka),
    Some{ea},
    Fresh.cell(s1, kv, ka, ev)({==}),
    cell1a
  )
  +asked2 = Equal.cong(
    Maybe<&2, Cells.Cell<Spec.Entry>>,
    Maybe<&2, Asked>,
    z => Asked.of(Cell.entry(z)),
    Tries.Trie.get(Cells.Cell<Spec.Entry>, s2, ka),
    Some{ea},
    cell2a
  )
  next2 = Next.one(s2, c, v, n, i, t, q)(cell2v)(asked2)(Chain.same_refl(c))
  grow = Grow.fuel(s1, kv, ev)(f4)
  has = Written.has(
    n,
    s1,
    i,
    c,
    v,
    tv,
    a2,
    hc2,
    next2,
    grow,
    Start.of(s1, c, Chain.root(s1, c), l)(ecur1)
  )
  (
    %Equal.sym(Maybe<&2, Cells.Cell<Spec.Entry>>, Tries.Trie.get(Cells.Cell<Spec.Entry>, s2, ka), Some{ea}, cell2a):
      {Answer.of(s2, i, _) == Spec.Answer.written{i}: Spec.Answer}
    %Equal.sym(Bool, Shared.List.has(~Spec.Id, ~Spec.Id.same, Spec.Node.chain(s2, c), i), True{}, has):
      {Answer.in(s2, i, q, _) == Spec.Answer.written{i}: Spec.Answer}
    {==},
    %Equal.sym(Maybe<&2, Asked>, State.asked(s2, i), Some{Asked{t, q}}, asked2):
      {Res.at(State.fuel(s2), s2, Some{i}, name, _, Asked.hits(_, name)) == Some{x}: Maybe<&2, Octets.Bytes()>}
    %Equal.sym(Bool, Resources.Name.same(name, name), True{}, Resources.Name.same_refl(name)):
      {Res.at(State.fuel(s2), s2, Some{i}, name, Some{Asked{t, q}}, _) == Some{x}: Maybe<&2, Octets.Bytes()>}
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
      +i = {Spec.Id{w, r}: Spec.Id}
      +c = {Spec.Chain.branch{b}: Spec.Chain}
      +q = {Spec.Ask.write{b, name, base, Spec.Content.bytes{x}}: Spec.Ask}
      l = {Step{v, [n]}: Step}
      +ka = Spec.Slot.key(Spec.Slot.ask{i})
      +kv = Spec.Slot.key(Spec.Slot.vote{n, c, v})
      +ea = {Cells.one{Spec.Entry.ask{i, t, q}}: Cells.Cell<Spec.Entry>}
      ev = {Cells.one{Spec.Entry.vote{i}}: Cells.Cell<Spec.Entry>}
      +ta = Tries.Trie.one(Cells.Cell<Spec.Entry>, ka, ea)
      tv = Tries.Trie.one(Cells.Cell<Spec.Entry>, kv, ev)
      +s1 = Spec.Node.join(s, ta)
      s2 = Spec.Node.join(s1, tv)
      +h1 => +h2 => +h3 => +h4 => h5 =>
        +ecur = Owner.cursor(Chain.cursor(s, c), n, v)(h1)(h2)
        +a = Cells.Cell.agrees_one(~Spec.Entry, ~Spec.Entry.same, s, ka, ea)(h3)
        +hc = Fresh.claim(s, ka, c, ea)({==})
        +f4 = Equal.trans(
          Maybe<&2, Cells.Cell<Spec.Entry>>,
          Tries.Trie.get(Cells.Cell<Spec.Entry>, s1, kv),
          Tries.Trie.get(Cells.Cell<Spec.Entry>, s, kv),
          None{},
          Fresh.cell(s, ka, kv, ea)({==}),
          h4
        )
        +ecur1 = Stay.cursor(s, ta, c, a, hc, l, ecur, Next.none(s1, c, v, n)(f4))
        +base_bytes = Res.of(s, name, base)
        +fits = Equal.trans(
          Bool,
          Ask.fits(s, q, v),
          Maybes.Maybe.same(~Octets.Bytes(), ~Octets.Bytes.is_eq, base_bytes, base_bytes),
          True{},
          Equal.cong(
            Maybe<&2, Octets.Bytes()>,
            Bool,
            z => Maybes.Maybe.same(~Octets.Bytes(), ~Octets.Bytes.is_eq, z, base_bytes),
            Res.of(s, name, Some{v}),
            base_bytes,
            Equal.trans(
              Maybe<&2, Octets.Bytes()>,
              Res.of(s, name, Some{v}),
              Spec.Node.content(s, name, Spec.Point.head{b}),
              base_bytes,
              Equal.sym(
                Maybe<&2, Octets.Bytes()>,
                Spec.Node.content(s, name, Spec.Point.head{b}),
                Res.of(s, name, Some{v}),
                Equal.cong(
                  Maybe<&2, Spec.Id>,
                  Maybe<&2, Octets.Bytes()>,
                  z => Res.of(s, name, z),
                  Spec.Node.head(s, b),
                  Some{v},
                  h2
                )
              ),
              h5
            )
          ),
          Maybes.Maybe.same_refl(
            ~Octets.Bytes(),
            ~Octets.Bytes.is_eq,
            ~Octets.Bytes.is_eq_refl,
            base_bytes
          )
        )
        +may = Equal.trans(
          Bool,
          Node.may_vote(n, s, c, v, [n]),
          Bool.and(
            True{},
            Maybe.is_none(&2, Cells.Cell<Spec.Entry>, State.cell(s, Spec.Slot.vote{n, c, v}))
          ),
          True{},
          Equal.cong(
            Bool,
            Bool,
            z => Bool.and(
              z,
              Maybe.is_none(&2, Cells.Cell<Spec.Entry>, State.cell(s, Spec.Slot.vote{n, c, v}))
            ),
            Shared.List.has(~String, ~String.eq, [n], n),
            True{},
            Owners.has(n)
          ),
          Equal.cong(
            Maybe<&2, Cells.Cell<Spec.Entry>>,
            Bool,
            z => Maybe.is_none(&2, Cells.Cell<Spec.Entry>, z),
            State.cell(s, Spec.Slot.vote{n, c, v}),
            None{},
            h4
          )
        )
        +ask = Equal.trans(
          Spec.State(),
          Spec.Node.ask(n, s, Spec.Envelope{r, w, t}, q),
          Node.ask.root(n, s, s1, i, q, Spec.Node.claim(s, c)),
          s2,
          Equal.cong(
            Maybe<&2, Cells.Cell<Spec.Entry>>,
            Spec.State(),
            z => Node.ask.fresh(n, s, i, t, q, z),
            State.cell(s, Spec.Slot.ask{i}),
            None{},
            h3
          ),
          Equal.trans(
            Spec.State(),
            Node.ask.root(n, s, s1, i, q, Spec.Node.claim(s, c)),
            Node.ask.at(n, s, s1, i, q, Chain.cursor(s, c)),
            s2,
            Owner.ask(
              n,
              s,
              i,
              t,
              q,
              Spec.Node.claim(s, c),
              Claim.of(s, c, Spec.Node.claim(s, c), {==}, l)(ecur)
            ),
            Equal.trans(
              Spec.State(),
              Node.ask.at(n, s, s1, i, q, Chain.cursor(s, c)),
              Node.ask.at(n, s, s1, i, q, Some{l}),
              s2,
              Equal.cong(
                Maybe<&2, Step>,
                Spec.State(),
                z => Node.ask.at(n, s, s1, i, q, z),
                Chain.cursor(s, c),
                Some{l},
                ecur
              ),
              Equal.cong(
                Bool,
                Spec.State(),
                z => Bool.pick(Spec.State(), z, State.put(s1, Spec.Slot.vote{n, c, v}, Spec.Entry.vote{i}), s1),
                Bool.and(Node.may_vote(n, s, c, v, [n]), Ask.fits(s, q, v)),
                True{},
                %Equal.sym(Bool, Node.may_vote(n, s, c, v, [n]), True{}, may): {Bool.and(_, Ask.fits(s, q, v)) == True{}: Bool}
                fits)
            )
          )
        )
        +cell1a = Equal.trans(
          Maybe<&2, Cells.Cell<Spec.Entry>>,
          Tries.Trie.get(Cells.Cell<Spec.Entry>, s1, ka),
          Tries.Trie.pick(~Cells.Cell<Spec.Entry>, ~Cells.Cell.join(~Spec.Entry, ~Spec.Entry.same), Tries.Trie.get(Cells.Cell<Spec.Entry>, s, ka), Tries.Trie.get(Cells.Cell<Spec.Entry>, ta, ka)),
          Some{ea},
          Tries.Trie.get_union(~Cells.Cell<Spec.Entry>, ~Cells.Cell.join(~Spec.Entry, ~Spec.Entry.same), s, ta, ka),
          %Equal.sym(Maybe<&2, Cells.Cell<Spec.Entry>>, Tries.Trie.get(Cells.Cell<Spec.Entry>, s, ka), None{}, h3):
            {Tries.Trie.pick(~Cells.Cell<Spec.Entry>, ~Cells.Cell.join(~Spec.Entry, ~Spec.Entry.same), _, Tries.Trie.get(Cells.Cell<Spec.Entry>, ta, ka)) == Some{ea}: Maybe<&2, Cells.Cell<Spec.Entry>>}
          Tries.Trie.get_one(Cells.Cell<Spec.Entry>, ka, ea))
        %Equal.sym(Spec.State(), Spec.Node.ask(n, s, Spec.Envelope{r, w, t}, q), s2, ask):
          (
            {
              Spec.Node.answer(_, i) == Spec.Answer.written{i}: Spec.Answer
            }
              & {Spec.Node.content(_, name, Spec.Point.at{i}) == Some{x}: Maybe<&2, Octets.Bytes()>}
          )
        Written.at(n, s1, i, t, b, name, base, x, v, ecur1, f4, cell1a)
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information
