import Base
import ../../shared.bend as Shared
import ../shared/ledger.bend as Ledgers
import ../shared/resources.bend as Resources
import ../shared/shared/text.bend as Texts
import ./spec.bend as Spec

# The proofs of the core's laws.

# Equality
# --------

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- an equality proof keeps each and as one value to split on
# Line.is_eq is True for a value and itself
def Line.is_eq_refl(a: Spec.Line) -> {Spec.Line.is_eq(a, a) == True{}: Bool}:
  match a:
    case Spec.Line.branch{x0}:
      Texts.String.eq_refl(x0)
    case Spec.Line.group{x0}:
      Texts.String.eq_refl(x0)

# Line.is_eq is True only for equal values
def Line.is_eq_sound(
  a: Spec.Line,
  b: Spec.Line
) -> {Spec.Line.is_eq(a, b) == True{}: Bool} -> {a == b: Spec.Line}:
  match a b:
    case Spec.Line.branch{x0} Spec.Line.branch{y0}:
      +h0 =>
        %Texts.String.eq_sound(x0, y0)(h0): {Spec.Line.branch{x0} == Spec.Line.branch{_}: Spec.Line}
        {==}
    case Spec.Line.group{x0} Spec.Line.group{y0}:
      +h0 =>
        %Texts.String.eq_sound(x0, y0)(h0): {Spec.Line.group{x0} == Spec.Line.group{_}: Spec.Line}
        {==}
    case Spec.Line.branch{a0} Spec.Line.group{b0}:
      h => Empty.absurd(
        {Spec.Line.branch{a0} == Spec.Line.group{b0}: Spec.Line},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Line.group{a0} Spec.Line.branch{b0}:
      h => Empty.absurd(
        {Spec.Line.group{a0} == Spec.Line.branch{b0}: Spec.Line},
        Shared.Bool.false_ne_true(h)
      )

# the laws of Spec.Line.is_eq
def Line.laws() -> Shared.Eq.Laws(Spec.Line, Spec.Line.is_eq):
  (Line.is_eq_refl, a => b => Line.is_eq_sound(a, b))

# Member.is_eq is True for a value and itself
def Member.is_eq_refl(a: Spec.Member) -> {Spec.Member.is_eq(a, a) == True{}: Bool}:
  match a:
    case Spec.Member.node{x0}:
      Texts.String.eq_refl(x0)
    case Spec.Member.group{x0}:
      Texts.String.eq_refl(x0)

# Member.is_eq is True only for equal values
def Member.is_eq_sound(
  a: Spec.Member,
  b: Spec.Member
) -> {Spec.Member.is_eq(a, b) == True{}: Bool} -> {a == b: Spec.Member}:
  match a b:
    case Spec.Member.node{x0} Spec.Member.node{y0}:
      +h0 =>
        %Texts.String.eq_sound(
          x0,
          y0
        )(h0): {Spec.Member.node{x0} == Spec.Member.node{_}: Spec.Member}
        {==}
    case Spec.Member.group{x0} Spec.Member.group{y0}:
      +h0 =>
        %Texts.String.eq_sound(
          x0,
          y0
        )(h0): {Spec.Member.group{x0} == Spec.Member.group{_}: Spec.Member}
        {==}
    case Spec.Member.node{a0} Spec.Member.group{b0}:
      h => Empty.absurd(
        {Spec.Member.node{a0} == Spec.Member.group{b0}: Spec.Member},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Member.group{a0} Spec.Member.node{b0}:
      h => Empty.absurd(
        {Spec.Member.group{a0} == Spec.Member.node{b0}: Spec.Member},
        Shared.Bool.false_ne_true(h)
      )

# the laws of Spec.Member.is_eq
def Member.laws() -> Shared.Eq.Laws(Spec.Member, Spec.Member.is_eq):
  (Member.is_eq_refl, a => b => Member.is_eq_sound(a, b))

# Content.is_eq is True for a value and itself
def Content.is_eq_refl(a: Spec.Content) -> {Spec.Content.is_eq(a, a) == True{}: Bool}:
  match a:
    case Spec.Content.bytes{x0}:
      Shared.List.is_eq_refl(~U32, ~U32.is_eq, ~Shared.U32.laws(), x0)
    case Spec.Content.of{x0}:
      Ledgers.Id.is_eq_refl(x0)

# Content.is_eq is True only for equal values
def Content.is_eq_sound(
  a: Spec.Content,
  b: Spec.Content
) -> {Spec.Content.is_eq(a, b) == True{}: Bool} -> {a == b: Spec.Content}:
  match a b:
    case Spec.Content.bytes{x0} Spec.Content.bytes{y0}:
      +h0 =>
        %Shared.List.is_eq_sound(
          ~U32,
          ~U32.is_eq,
          ~Shared.U32.laws(),
          x0,
          y0
        )(h0): {Spec.Content.bytes{x0} == Spec.Content.bytes{_}: Spec.Content}
        {==}
    case Spec.Content.of{x0} Spec.Content.of{y0}:
      +h0 =>
        %Ledgers.Id.is_eq_sound(
          x0,
          y0
        )(h0): {Spec.Content.of{x0} == Spec.Content.of{_}: Spec.Content}
        {==}
    case Spec.Content.bytes{a0} Spec.Content.of{b0}:
      h => Empty.absurd(
        {Spec.Content.bytes{a0} == Spec.Content.of{b0}: Spec.Content},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Content.of{a0} Spec.Content.bytes{b0}:
      h => Empty.absurd(
        {Spec.Content.of{a0} == Spec.Content.bytes{b0}: Spec.Content},
        Shared.Bool.false_ne_true(h)
      )

# the laws of Spec.Content.is_eq
def Content.laws() -> Shared.Eq.Laws(Spec.Content, Spec.Content.is_eq):
  (Content.is_eq_refl, a => b => Content.is_eq_sound(a, b))

# Change.is_eq is True for a value and itself
def Change.is_eq_refl(a: Spec.Change) -> {Spec.Change.is_eq(a, a) == True{}: Bool}:
  match a:
    case Spec.Change.make{+x0, +x1, +x2}:
      Shared.Bool.and_both(
        Spec.Line.is_eq(x0, x0),
        Bool.and(
          Shared.Maybe.is_eq(~Ledgers.Id, ~Ledgers.Id.is_eq, x1, x1),
          Shared.List.is_eq(~Spec.Member, ~Spec.Member.is_eq, x2, x2)
        )
      )(
        Line.is_eq_refl(x0)
      )(
        Shared.Bool.and_both(
          Shared.Maybe.is_eq(~Ledgers.Id, ~Ledgers.Id.is_eq, x1, x1),
          Shared.List.is_eq(~Spec.Member, ~Spec.Member.is_eq, x2, x2)
        )(
          Shared.Maybe.is_eq_refl(~Ledgers.Id, ~Ledgers.Id.is_eq, ~Ledgers.Id.laws(), x1)
        )(Shared.List.is_eq_refl(~Spec.Member, ~Spec.Member.is_eq, ~Member.laws(), x2))
      )
    case Spec.Change.own{x0}:
      Shared.List.is_eq_refl(~String, ~String.eq, ~Texts.String.laws(), x0)
    case Spec.Change.write{+x0, +x1, +x2}:
      Shared.Bool.and_both(
        Resources.Name.is_eq(x0, x0),
        Bool.and(
          Shared.Maybe.is_eq(~Ledgers.Id, ~Ledgers.Id.is_eq, x1, x1),
          Spec.Content.is_eq(x2, x2)
        )
      )(
        Resources.Name.is_eq_refl(x0)
      )(
        Shared.Bool.and_both(
          Shared.Maybe.is_eq(~Ledgers.Id, ~Ledgers.Id.is_eq, x1, x1),
          Spec.Content.is_eq(x2, x2)
        )(
          Shared.Maybe.is_eq_refl(~Ledgers.Id, ~Ledgers.Id.is_eq, ~Ledgers.Id.laws(), x1)
        )(Content.is_eq_refl(x2))
      )
    case Spec.Change.resolve{+x0, +x1, +x2}:
      Shared.Bool.and_both(
        Ledgers.Id.is_eq(x0, x0),
        Bool.and(Resources.Name.is_eq(x1, x1), Spec.Content.is_eq(x2, x2))
      )(
        Ledgers.Id.is_eq_refl(x0)
      )(
        Shared.Bool.and_both(
          Resources.Name.is_eq(x1, x1),
          Spec.Content.is_eq(x2, x2)
        )(Resources.Name.is_eq_refl(x1))(Content.is_eq_refl(x2))
      )
    case Spec.Change.merge{x0}:
      Ledgers.Id.is_eq_refl(x0)
    case Spec.Change.move{x0}:
      Ledgers.Id.is_eq_refl(x0)
    case Spec.Change.mark{+x0, +x1}:
      Shared.Bool.and_both(
        String.eq(x0, x0),
        String.eq(x1, x1)
      )(Texts.String.eq_refl(x0))(Texts.String.eq_refl(x1))
    case Spec.Change.members{x0}:
      Shared.List.is_eq_refl(~Spec.Member, ~Spec.Member.is_eq, ~Member.laws(), x0)

# Change.is_eq is True only for equal values
def Change.is_eq_sound(
  a: Spec.Change,
  b: Spec.Change
) -> {Spec.Change.is_eq(a, b) == True{}: Bool} -> {a == b: Spec.Change}:
  match a b:
    case Spec.Change.make{+x0, +x1, +x2} Spec.Change.make{+y0, +y1, +y2}:
      +h0 =>
        +h1 = Shared.Bool.and_true_right(
          Spec.Line.is_eq(x0, y0),
          Bool.and(
            Shared.Maybe.is_eq(~Ledgers.Id, ~Ledgers.Id.is_eq, x1, y1),
            Shared.List.is_eq(~Spec.Member, ~Spec.Member.is_eq, x2, y2)
          )
        )(h0)
        +h2 = Shared.Bool.and_true_right(
          Shared.Maybe.is_eq(~Ledgers.Id, ~Ledgers.Id.is_eq, x1, y1),
          Shared.List.is_eq(~Spec.Member, ~Spec.Member.is_eq, x2, y2)
        )(h1)
        %Line.is_eq_sound(
          x0,
          y0
        )(
          Shared.Bool.and_true_left(
            Spec.Line.is_eq(x0, y0),
            Bool.and(
              Shared.Maybe.is_eq(~Ledgers.Id, ~Ledgers.Id.is_eq, x1, y1),
              Shared.List.is_eq(~Spec.Member, ~Spec.Member.is_eq, x2, y2)
            )
          )(h0)
        ): {Spec.Change.make{x0, x1, x2} == Spec.Change.make{_, y1, y2}: Spec.Change}
        %Shared.Maybe.is_eq_sound(
          ~Ledgers.Id,
          ~Ledgers.Id.is_eq,
          Ledgers.Id.is_eq_sound,
          x1,
          y1
        )(
          Shared.Bool.and_true_left(
            Shared.Maybe.is_eq(~Ledgers.Id, ~Ledgers.Id.is_eq, x1, y1),
            Shared.List.is_eq(~Spec.Member, ~Spec.Member.is_eq, x2, y2)
          )(h1)
        ): {Spec.Change.make{x0, x1, x2} == Spec.Change.make{x0, _, y2}: Spec.Change}
        %Shared.List.is_eq_sound(
          ~Spec.Member,
          ~Spec.Member.is_eq,
          ~Member.laws(),
          x2,
          y2
        )(h2): {Spec.Change.make{x0, x1, x2} == Spec.Change.make{x0, x1, _}: Spec.Change}
        {==}
    case Spec.Change.own{x0} Spec.Change.own{y0}:
      +h0 =>
        %Shared.List.is_eq_sound(
          ~String,
          ~String.eq,
          ~Texts.String.laws(),
          x0,
          y0
        )(h0): {Spec.Change.own{x0} == Spec.Change.own{_}: Spec.Change}
        {==}
    case Spec.Change.write{+x0, +x1, +x2} Spec.Change.write{+y0, +y1, +y2}:
      +h0 =>
        +h1 = Shared.Bool.and_true_right(
          Resources.Name.is_eq(x0, y0),
          Bool.and(
            Shared.Maybe.is_eq(~Ledgers.Id, ~Ledgers.Id.is_eq, x1, y1),
            Spec.Content.is_eq(x2, y2)
          )
        )(h0)
        +h2 = Shared.Bool.and_true_right(
          Shared.Maybe.is_eq(~Ledgers.Id, ~Ledgers.Id.is_eq, x1, y1),
          Spec.Content.is_eq(x2, y2)
        )(h1)
        %Resources.Name.is_eq_sound(
          x0,
          y0
        )(
          Shared.Bool.and_true_left(
            Resources.Name.is_eq(x0, y0),
            Bool.and(
              Shared.Maybe.is_eq(~Ledgers.Id, ~Ledgers.Id.is_eq, x1, y1),
              Spec.Content.is_eq(x2, y2)
            )
          )(h0)
        ): {Spec.Change.write{x0, x1, x2} == Spec.Change.write{_, y1, y2}: Spec.Change}
        %Shared.Maybe.is_eq_sound(
          ~Ledgers.Id,
          ~Ledgers.Id.is_eq,
          Ledgers.Id.is_eq_sound,
          x1,
          y1
        )(
          Shared.Bool.and_true_left(
            Shared.Maybe.is_eq(~Ledgers.Id, ~Ledgers.Id.is_eq, x1, y1),
            Spec.Content.is_eq(x2, y2)
          )(h1)
        ): {Spec.Change.write{x0, x1, x2} == Spec.Change.write{x0, _, y2}: Spec.Change}
        %Content.is_eq_sound(
          x2,
          y2
        )(h2): {Spec.Change.write{x0, x1, x2} == Spec.Change.write{x0, x1, _}: Spec.Change}
        {==}
    case Spec.Change.resolve{+x0, +x1, +x2} Spec.Change.resolve{+y0, +y1, +y2}:
      +h0 =>
        +h1 = Shared.Bool.and_true_right(
          Ledgers.Id.is_eq(x0, y0),
          Bool.and(Resources.Name.is_eq(x1, y1), Spec.Content.is_eq(x2, y2))
        )(h0)
        +h2 = Shared.Bool.and_true_right(
          Resources.Name.is_eq(x1, y1),
          Spec.Content.is_eq(x2, y2)
        )(h1)
        %Ledgers.Id.is_eq_sound(
          x0,
          y0
        )(
          Shared.Bool.and_true_left(
            Ledgers.Id.is_eq(x0, y0),
            Bool.and(Resources.Name.is_eq(x1, y1), Spec.Content.is_eq(x2, y2))
          )(h0)
        ): {Spec.Change.resolve{x0, x1, x2} == Spec.Change.resolve{_, y1, y2}: Spec.Change}
        %Resources.Name.is_eq_sound(
          x1,
          y1
        )(
          Shared.Bool.and_true_left(Resources.Name.is_eq(x1, y1), Spec.Content.is_eq(x2, y2))(h1)
        ): {Spec.Change.resolve{x0, x1, x2} == Spec.Change.resolve{x0, _, y2}: Spec.Change}
        %Content.is_eq_sound(
          x2,
          y2
        )(h2): {Spec.Change.resolve{x0, x1, x2} == Spec.Change.resolve{x0, x1, _}: Spec.Change}
        {==}
    case Spec.Change.merge{x0} Spec.Change.merge{y0}:
      +h0 =>
        %Ledgers.Id.is_eq_sound(
          x0,
          y0
        )(h0): {Spec.Change.merge{x0} == Spec.Change.merge{_}: Spec.Change}
        {==}
    case Spec.Change.move{x0} Spec.Change.move{y0}:
      +h0 =>
        %Ledgers.Id.is_eq_sound(
          x0,
          y0
        )(h0): {Spec.Change.move{x0} == Spec.Change.move{_}: Spec.Change}
        {==}
    case Spec.Change.mark{+x0, +x1} Spec.Change.mark{+y0, +y1}:
      +h0 =>
        +h1 = Shared.Bool.and_true_right(String.eq(x0, y0), String.eq(x1, y1))(h0)
        %Texts.String.eq_sound(
          x0,
          y0
        )(
          Shared.Bool.and_true_left(String.eq(x0, y0), String.eq(x1, y1))(h0)
        ): {Spec.Change.mark{x0, x1} == Spec.Change.mark{_, y1}: Spec.Change}
        %Texts.String.eq_sound(
          x1,
          y1
        )(h1): {Spec.Change.mark{x0, x1} == Spec.Change.mark{x0, _}: Spec.Change}
        {==}
    case Spec.Change.members{x0} Spec.Change.members{y0}:
      +h0 =>
        %Shared.List.is_eq_sound(
          ~Spec.Member,
          ~Spec.Member.is_eq,
          ~Member.laws(),
          x0,
          y0
        )(h0): {Spec.Change.members{x0} == Spec.Change.members{_}: Spec.Change}
        {==}
    case Spec.Change.make{a0, a1, a2} Spec.Change.own{b0}:
      h => Empty.absurd(
        {Spec.Change.make{a0, a1, a2} == Spec.Change.own{b0}: Spec.Change},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Change.make{a0, a1, a2} Spec.Change.write{b0, b1, b2}:
      h => Empty.absurd(
        {Spec.Change.make{a0, a1, a2} == Spec.Change.write{b0, b1, b2}: Spec.Change},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Change.make{a0, a1, a2} Spec.Change.resolve{b0, b1, b2}:
      h => Empty.absurd(
        {Spec.Change.make{a0, a1, a2} == Spec.Change.resolve{b0, b1, b2}: Spec.Change},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Change.make{a0, a1, a2} Spec.Change.merge{b0}:
      h => Empty.absurd(
        {Spec.Change.make{a0, a1, a2} == Spec.Change.merge{b0}: Spec.Change},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Change.make{a0, a1, a2} Spec.Change.move{b0}:
      h => Empty.absurd(
        {Spec.Change.make{a0, a1, a2} == Spec.Change.move{b0}: Spec.Change},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Change.make{a0, a1, a2} Spec.Change.mark{b0, b1}:
      h => Empty.absurd(
        {Spec.Change.make{a0, a1, a2} == Spec.Change.mark{b0, b1}: Spec.Change},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Change.make{a0, a1, a2} Spec.Change.members{b0}:
      h => Empty.absurd(
        {Spec.Change.make{a0, a1, a2} == Spec.Change.members{b0}: Spec.Change},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Change.own{a0} Spec.Change.make{b0, b1, b2}:
      h => Empty.absurd(
        {Spec.Change.own{a0} == Spec.Change.make{b0, b1, b2}: Spec.Change},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Change.own{a0} Spec.Change.write{b0, b1, b2}:
      h => Empty.absurd(
        {Spec.Change.own{a0} == Spec.Change.write{b0, b1, b2}: Spec.Change},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Change.own{a0} Spec.Change.resolve{b0, b1, b2}:
      h => Empty.absurd(
        {Spec.Change.own{a0} == Spec.Change.resolve{b0, b1, b2}: Spec.Change},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Change.own{a0} Spec.Change.merge{b0}:
      h => Empty.absurd(
        {Spec.Change.own{a0} == Spec.Change.merge{b0}: Spec.Change},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Change.own{a0} Spec.Change.move{b0}:
      h => Empty.absurd(
        {Spec.Change.own{a0} == Spec.Change.move{b0}: Spec.Change},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Change.own{a0} Spec.Change.mark{b0, b1}:
      h => Empty.absurd(
        {Spec.Change.own{a0} == Spec.Change.mark{b0, b1}: Spec.Change},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Change.own{a0} Spec.Change.members{b0}:
      h => Empty.absurd(
        {Spec.Change.own{a0} == Spec.Change.members{b0}: Spec.Change},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Change.write{a0, a1, a2} Spec.Change.make{b0, b1, b2}:
      h => Empty.absurd(
        {Spec.Change.write{a0, a1, a2} == Spec.Change.make{b0, b1, b2}: Spec.Change},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Change.write{a0, a1, a2} Spec.Change.own{b0}:
      h => Empty.absurd(
        {Spec.Change.write{a0, a1, a2} == Spec.Change.own{b0}: Spec.Change},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Change.write{a0, a1, a2} Spec.Change.resolve{b0, b1, b2}:
      h => Empty.absurd(
        {Spec.Change.write{a0, a1, a2} == Spec.Change.resolve{b0, b1, b2}: Spec.Change},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Change.write{a0, a1, a2} Spec.Change.merge{b0}:
      h => Empty.absurd(
        {Spec.Change.write{a0, a1, a2} == Spec.Change.merge{b0}: Spec.Change},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Change.write{a0, a1, a2} Spec.Change.move{b0}:
      h => Empty.absurd(
        {Spec.Change.write{a0, a1, a2} == Spec.Change.move{b0}: Spec.Change},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Change.write{a0, a1, a2} Spec.Change.mark{b0, b1}:
      h => Empty.absurd(
        {Spec.Change.write{a0, a1, a2} == Spec.Change.mark{b0, b1}: Spec.Change},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Change.write{a0, a1, a2} Spec.Change.members{b0}:
      h => Empty.absurd(
        {Spec.Change.write{a0, a1, a2} == Spec.Change.members{b0}: Spec.Change},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Change.resolve{a0, a1, a2} Spec.Change.make{b0, b1, b2}:
      h => Empty.absurd(
        {Spec.Change.resolve{a0, a1, a2} == Spec.Change.make{b0, b1, b2}: Spec.Change},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Change.resolve{a0, a1, a2} Spec.Change.own{b0}:
      h => Empty.absurd(
        {Spec.Change.resolve{a0, a1, a2} == Spec.Change.own{b0}: Spec.Change},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Change.resolve{a0, a1, a2} Spec.Change.write{b0, b1, b2}:
      h => Empty.absurd(
        {Spec.Change.resolve{a0, a1, a2} == Spec.Change.write{b0, b1, b2}: Spec.Change},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Change.resolve{a0, a1, a2} Spec.Change.merge{b0}:
      h => Empty.absurd(
        {Spec.Change.resolve{a0, a1, a2} == Spec.Change.merge{b0}: Spec.Change},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Change.resolve{a0, a1, a2} Spec.Change.move{b0}:
      h => Empty.absurd(
        {Spec.Change.resolve{a0, a1, a2} == Spec.Change.move{b0}: Spec.Change},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Change.resolve{a0, a1, a2} Spec.Change.mark{b0, b1}:
      h => Empty.absurd(
        {Spec.Change.resolve{a0, a1, a2} == Spec.Change.mark{b0, b1}: Spec.Change},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Change.resolve{a0, a1, a2} Spec.Change.members{b0}:
      h => Empty.absurd(
        {Spec.Change.resolve{a0, a1, a2} == Spec.Change.members{b0}: Spec.Change},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Change.merge{a0} Spec.Change.make{b0, b1, b2}:
      h => Empty.absurd(
        {Spec.Change.merge{a0} == Spec.Change.make{b0, b1, b2}: Spec.Change},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Change.merge{a0} Spec.Change.own{b0}:
      h => Empty.absurd(
        {Spec.Change.merge{a0} == Spec.Change.own{b0}: Spec.Change},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Change.merge{a0} Spec.Change.write{b0, b1, b2}:
      h => Empty.absurd(
        {Spec.Change.merge{a0} == Spec.Change.write{b0, b1, b2}: Spec.Change},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Change.merge{a0} Spec.Change.resolve{b0, b1, b2}:
      h => Empty.absurd(
        {Spec.Change.merge{a0} == Spec.Change.resolve{b0, b1, b2}: Spec.Change},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Change.merge{a0} Spec.Change.move{b0}:
      h => Empty.absurd(
        {Spec.Change.merge{a0} == Spec.Change.move{b0}: Spec.Change},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Change.merge{a0} Spec.Change.mark{b0, b1}:
      h => Empty.absurd(
        {Spec.Change.merge{a0} == Spec.Change.mark{b0, b1}: Spec.Change},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Change.merge{a0} Spec.Change.members{b0}:
      h => Empty.absurd(
        {Spec.Change.merge{a0} == Spec.Change.members{b0}: Spec.Change},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Change.move{a0} Spec.Change.make{b0, b1, b2}:
      h => Empty.absurd(
        {Spec.Change.move{a0} == Spec.Change.make{b0, b1, b2}: Spec.Change},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Change.move{a0} Spec.Change.own{b0}:
      h => Empty.absurd(
        {Spec.Change.move{a0} == Spec.Change.own{b0}: Spec.Change},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Change.move{a0} Spec.Change.write{b0, b1, b2}:
      h => Empty.absurd(
        {Spec.Change.move{a0} == Spec.Change.write{b0, b1, b2}: Spec.Change},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Change.move{a0} Spec.Change.resolve{b0, b1, b2}:
      h => Empty.absurd(
        {Spec.Change.move{a0} == Spec.Change.resolve{b0, b1, b2}: Spec.Change},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Change.move{a0} Spec.Change.merge{b0}:
      h => Empty.absurd(
        {Spec.Change.move{a0} == Spec.Change.merge{b0}: Spec.Change},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Change.move{a0} Spec.Change.mark{b0, b1}:
      h => Empty.absurd(
        {Spec.Change.move{a0} == Spec.Change.mark{b0, b1}: Spec.Change},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Change.move{a0} Spec.Change.members{b0}:
      h => Empty.absurd(
        {Spec.Change.move{a0} == Spec.Change.members{b0}: Spec.Change},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Change.mark{a0, a1} Spec.Change.make{b0, b1, b2}:
      h => Empty.absurd(
        {Spec.Change.mark{a0, a1} == Spec.Change.make{b0, b1, b2}: Spec.Change},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Change.mark{a0, a1} Spec.Change.own{b0}:
      h => Empty.absurd(
        {Spec.Change.mark{a0, a1} == Spec.Change.own{b0}: Spec.Change},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Change.mark{a0, a1} Spec.Change.write{b0, b1, b2}:
      h => Empty.absurd(
        {Spec.Change.mark{a0, a1} == Spec.Change.write{b0, b1, b2}: Spec.Change},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Change.mark{a0, a1} Spec.Change.resolve{b0, b1, b2}:
      h => Empty.absurd(
        {Spec.Change.mark{a0, a1} == Spec.Change.resolve{b0, b1, b2}: Spec.Change},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Change.mark{a0, a1} Spec.Change.merge{b0}:
      h => Empty.absurd(
        {Spec.Change.mark{a0, a1} == Spec.Change.merge{b0}: Spec.Change},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Change.mark{a0, a1} Spec.Change.move{b0}:
      h => Empty.absurd(
        {Spec.Change.mark{a0, a1} == Spec.Change.move{b0}: Spec.Change},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Change.mark{a0, a1} Spec.Change.members{b0}:
      h => Empty.absurd(
        {Spec.Change.mark{a0, a1} == Spec.Change.members{b0}: Spec.Change},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Change.members{a0} Spec.Change.make{b0, b1, b2}:
      h => Empty.absurd(
        {Spec.Change.members{a0} == Spec.Change.make{b0, b1, b2}: Spec.Change},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Change.members{a0} Spec.Change.own{b0}:
      h => Empty.absurd(
        {Spec.Change.members{a0} == Spec.Change.own{b0}: Spec.Change},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Change.members{a0} Spec.Change.write{b0, b1, b2}:
      h => Empty.absurd(
        {Spec.Change.members{a0} == Spec.Change.write{b0, b1, b2}: Spec.Change},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Change.members{a0} Spec.Change.resolve{b0, b1, b2}:
      h => Empty.absurd(
        {Spec.Change.members{a0} == Spec.Change.resolve{b0, b1, b2}: Spec.Change},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Change.members{a0} Spec.Change.merge{b0}:
      h => Empty.absurd(
        {Spec.Change.members{a0} == Spec.Change.merge{b0}: Spec.Change},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Change.members{a0} Spec.Change.move{b0}:
      h => Empty.absurd(
        {Spec.Change.members{a0} == Spec.Change.move{b0}: Spec.Change},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Change.members{a0} Spec.Change.mark{b0, b1}:
      h => Empty.absurd(
        {Spec.Change.members{a0} == Spec.Change.mark{b0, b1}: Spec.Change},
        Shared.Bool.false_ne_true(h)
      )

# the laws of Spec.Change.is_eq
def Change.laws() -> Shared.Eq.Laws(Spec.Change, Spec.Change.is_eq):
  (Change.is_eq_refl, a => b => Change.is_eq_sound(a, b))

# Ask.is_eq is True for a value and itself
def Ask.is_eq_refl(a: Spec.Ask) -> {Spec.Ask.is_eq(a, a) == True{}: Bool}:
  match a:
    case Spec.Ask.start{x0}:
      Shared.List.is_eq_refl(~String, ~String.eq, ~Texts.String.laws(), x0)
    case Spec.Ask.on{+x0, +x1, +x2}:
      Shared.Bool.and_both(
        Ledgers.Id.is_eq(x0, x0),
        Bool.and(
          Shared.Maybe.is_eq(~Spec.Line, ~Spec.Line.is_eq, x1, x1),
          Spec.Change.is_eq(x2, x2)
        )
      )(
        Ledgers.Id.is_eq_refl(x0)
      )(
        Shared.Bool.and_both(
          Shared.Maybe.is_eq(~Spec.Line, ~Spec.Line.is_eq, x1, x1),
          Spec.Change.is_eq(x2, x2)
        )(
          Shared.Maybe.is_eq_refl(~Spec.Line, ~Spec.Line.is_eq, ~Line.laws(), x1)
        )(Change.is_eq_refl(x2))
      )

# Ask.is_eq is True only for equal values
def Ask.is_eq_sound(
  a: Spec.Ask,
  b: Spec.Ask
) -> {Spec.Ask.is_eq(a, b) == True{}: Bool} -> {a == b: Spec.Ask}:
  match a b:
    case Spec.Ask.start{x0} Spec.Ask.start{y0}:
      +h0 =>
        %Shared.List.is_eq_sound(
          ~String,
          ~String.eq,
          ~Texts.String.laws(),
          x0,
          y0
        )(h0): {Spec.Ask.start{x0} == Spec.Ask.start{_}: Spec.Ask}
        {==}
    case Spec.Ask.on{+x0, +x1, +x2} Spec.Ask.on{+y0, +y1, +y2}:
      +h0 =>
        +h1 = Shared.Bool.and_true_right(
          Ledgers.Id.is_eq(x0, y0),
          Bool.and(
            Shared.Maybe.is_eq(~Spec.Line, ~Spec.Line.is_eq, x1, y1),
            Spec.Change.is_eq(x2, y2)
          )
        )(h0)
        +h2 = Shared.Bool.and_true_right(
          Shared.Maybe.is_eq(~Spec.Line, ~Spec.Line.is_eq, x1, y1),
          Spec.Change.is_eq(x2, y2)
        )(h1)
        %Ledgers.Id.is_eq_sound(
          x0,
          y0
        )(
          Shared.Bool.and_true_left(
            Ledgers.Id.is_eq(x0, y0),
            Bool.and(
              Shared.Maybe.is_eq(~Spec.Line, ~Spec.Line.is_eq, x1, y1),
              Spec.Change.is_eq(x2, y2)
            )
          )(h0)
        ): {Spec.Ask.on{x0, x1, x2} == Spec.Ask.on{_, y1, y2}: Spec.Ask}
        %Shared.Maybe.is_eq_sound(
          ~Spec.Line,
          ~Spec.Line.is_eq,
          Line.is_eq_sound,
          x1,
          y1
        )(
          Shared.Bool.and_true_left(
            Shared.Maybe.is_eq(~Spec.Line, ~Spec.Line.is_eq, x1, y1),
            Spec.Change.is_eq(x2, y2)
          )(h1)
        ): {Spec.Ask.on{x0, x1, x2} == Spec.Ask.on{x0, _, y2}: Spec.Ask}
        %Change.is_eq_sound(
          x2,
          y2
        )(h2): {Spec.Ask.on{x0, x1, x2} == Spec.Ask.on{x0, x1, _}: Spec.Ask}
        {==}
    case Spec.Ask.start{a0} Spec.Ask.on{b0, b1, b2}:
      h => Empty.absurd(
        {Spec.Ask.start{a0} == Spec.Ask.on{b0, b1, b2}: Spec.Ask},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Ask.on{a0, a1, a2} Spec.Ask.start{b0}:
      h => Empty.absurd(
        {Spec.Ask.on{a0, a1, a2} == Spec.Ask.start{b0}: Spec.Ask},
        Shared.Bool.false_ne_true(h)
      )

# the laws of Spec.Ask.is_eq
def Ask.laws() -> Shared.Eq.Laws(Spec.Ask, Spec.Ask.is_eq):
  (Ask.is_eq_refl, a => b => Ask.is_eq_sound(a, b))

# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# Laws
# ----

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# the owners take a write whose base is ready and whose resource did not change
def Write.takes(
  s: Spec.State(),
  r: Ledgers.Id,
  b: String,
  name: Resources.Name,
  base: Maybe<&2, Ledgers.Id>,
  x: Texts.Bytes(),
  xs: List<&2, Ledgers.Step<Spec.Ask>>
) -> {
  Spec.Judge.ready_maybe(s, base) == Some{True{}}: Maybe<&2, Bool>
} -> {
  Spec.Bytes.same(
    Spec.Res.of(s, name, Spec.Ids.last(Spec.Steps.taken(xs))),
    Spec.Res.of(s, name, base)
  )
    == True{}: Bool
} -> {
  Spec.Node.judge(
    s,
    Spec.Ask.on{r, Some{Spec.Line.branch{b}}, Spec.Change.write{name, base, Spec.Content.bytes{x}}},
    xs
  )
    == Some{True{}}: Maybe<&2, Bool>
}:
  hr => hc =>
    %Equal.sym(Maybe<&2, Bool>, Spec.Judge.ready_maybe(s, base), Some{True{}}, hr):
      {
        Spec.Judge.then(
          _,
          u => Spec.Judge.then(
            Spec.Judge.content(s, Spec.Content.bytes{x}),
            w => Some{
              Spec.Bytes.same(
                Spec.Res.of(s, name, Spec.Ids.last(Spec.Steps.taken(xs))),
                Spec.Res.of(s, name, base)
              )
            }
          )
        )
          == Some{True{}}: Maybe<&2, Bool>
      }
    %Equal.sym(
      Bool,
      Spec.Bytes.same(
        Spec.Res.of(s, name, Spec.Ids.last(Spec.Steps.taken(xs))),
        Spec.Res.of(s, name, base)
      ),
      True{},
      hc
    ):
      {Some{_} == Some{True{}}: Maybe<&2, Bool>}
    {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
def Spec.Node.write_written(n, s, e, r, b, name, base, x, h):
  +h1 => ht => hg => hv => hr => hc =>
    +hs = Ledgers.State.ask_decides(
      ~Spec.Ask,
      ~Spec.Ask.is_eq,
      ~Ask.laws(),
      ~Spec.Ask.view,
      ~Spec.Node.judge,
      n,
      s,
      Spec.Envelope.of(e),
      Spec.Envelope.time(e),
      Spec.Ask.on{
        r,
        Some{Spec.Line.branch{b}},
        Spec.Change.write{name, base, Spec.Content.bytes{x}}
      },
      Spec.Line.chain(r, Some{Spec.Line.branch{b}}),
      None{},
      None{},
      h,
      True{}
    )(
      h1
    )(
      {==}
    )(
      ht
    )(
      hg
    )(
      hv
    )(
      Write.takes(
        Spec.Node.taken(
          s,
          e,
          Spec.Ask.on{
            r,
            Some{Spec.Line.branch{b}},
            Spec.Change.write{name, base, Spec.Content.bytes{x}}
          }
        ),
        r,
        b,
        name,
        base,
        x,
        Spec.Node.steps(
          Spec.Node.taken(
            s,
            e,
            Spec.Ask.on{
              r,
              Some{Spec.Line.branch{b}},
              Spec.Change.write{name, base, Spec.Content.bytes{x}}
            }
          ),
          r,
          Some{Spec.Line.branch{b}}
        )
      )(hr)(hc)
    )
    +ha = Ledgers.State.ask_holds(
      ~Spec.Ask,
      ~Spec.Ask.is_eq,
      ~Spec.Ask.view,
      ~Spec.Node.judge,
      n,
      s,
      Spec.Envelope.of(e),
      Spec.Envelope.time(e),
      Spec.Ask.on{
        r,
        Some{Spec.Line.branch{b}},
        Spec.Change.write{name, base, Spec.Content.bytes{x}}
      }
    )(h1)
    ((
        %Equal.sym(Ledgers.Status, Ledgers.State.status(~Spec.Ask, ~Spec.Ask.view, Spec.Node.ask(n, s, e, Spec.Ask.on{r, Some{Spec.Line.branch{b}}, Spec.Change.write{name, base, Spec.Content.bytes{x}}}), Spec.Envelope.of(e)), Ledgers.Status.done{True{}}, hs):
          {Spec.Answer.of(Spec.Node.ask(n, s, e, Spec.Ask.on{r, Some{Spec.Line.branch{b}}, Spec.Change.write{name, base, Spec.Content.bytes{x}}}), Spec.Envelope.of(e), _) == Spec.Answer.written{Spec.Envelope.of(e)}: Spec.Answer}
        %Equal.sym(Maybe<&2, Ledgers.Asked<Spec.Ask>>, Ledgers.State.asked(~Spec.Ask, Spec.Node.ask(n, s, e, Spec.Ask.on{r, Some{Spec.Line.branch{b}}, Spec.Change.write{name, base, Spec.Content.bytes{x}}}), Spec.Envelope.of(e)), Some{Ledgers.Asked{Spec.Envelope.time(e), Spec.Ask.on{r, Some{Spec.Line.branch{b}}, Spec.Change.write{name, base, Spec.Content.bytes{x}}}}}, ha):
          {Spec.Answer.taken(Spec.Node.ask(n, s, e, Spec.Ask.on{r, Some{Spec.Line.branch{b}}, Spec.Change.write{name, base, Spec.Content.bytes{x}}}), Spec.Envelope.of(e), _) == Spec.Answer.written{Spec.Envelope.of(e)}: Spec.Answer}
        {==}), (
        %Equal.sym(Ledgers.Status, Ledgers.State.status(~Spec.Ask, ~Spec.Ask.view, Spec.Node.ask(n, s, e, Spec.Ask.on{r, Some{Spec.Line.branch{b}}, Spec.Change.write{name, base, Spec.Content.bytes{x}}}), Spec.Envelope.of(e)), Ledgers.Status.done{True{}}, hs):
          {Spec.Res.of(Spec.Node.ask(n, s, e, Spec.Ask.on{r, Some{Spec.Line.branch{b}}, Spec.Change.write{name, base, Spec.Content.bytes{x}}}), name, Shared.Bool.when(Maybe<&2, Ledgers.Id>, Shared.Maybe.is_eq(~Bool, ~Shared.Bool.is_eq, Ledgers.Status.verdict(_), Some{True{}}), u => Some{Spec.Envelope.of(e)}, u => None{})) == Some{x}: Maybe<&2, Texts.Bytes()>}
        %Equal.sym(Maybe<&2, Ledgers.Asked<Spec.Ask>>, Ledgers.State.asked(~Spec.Ask, Spec.Node.ask(n, s, e, Spec.Ask.on{r, Some{Spec.Line.branch{b}}, Spec.Change.write{name, base, Spec.Content.bytes{x}}}), Spec.Envelope.of(e)), Some{Ledgers.Asked{Spec.Envelope.time(e), Spec.Ask.on{r, Some{Spec.Line.branch{b}}, Spec.Change.write{name, base, Spec.Content.bytes{x}}}}}, ha):
          {Spec.Res.at(Spec.State.fuel(Spec.Node.ask(n, s, e, Spec.Ask.on{r, Some{Spec.Line.branch{b}}, Spec.Change.write{name, base, Spec.Content.bytes{x}}})), Spec.Node.ask(n, s, e, Spec.Ask.on{r, Some{Spec.Line.branch{b}}, Spec.Change.write{name, base, Spec.Content.bytes{x}}}), Some{Spec.Envelope.of(e)}, name, _, Spec.Asked.hits(_, name)) == Some{x}: Maybe<&2, Texts.Bytes()>}
        %Equal.sym(Bool, Resources.Name.is_eq(name, name), True{}, Resources.Name.is_eq_refl(name)):
          {Spec.Res.at(Spec.State.fuel(Spec.Node.ask(n, s, e, Spec.Ask.on{r, Some{Spec.Line.branch{b}}, Spec.Change.write{name, base, Spec.Content.bytes{x}}})), Spec.Node.ask(n, s, e, Spec.Ask.on{r, Some{Spec.Line.branch{b}}, Spec.Change.write{name, base, Spec.Content.bytes{x}}}), Some{Spec.Envelope.of(e)}, name, Some{Ledgers.Asked{Spec.Envelope.time(e), Spec.Ask.on{r, Some{Spec.Line.branch{b}}, Spec.Change.write{name, base, Spec.Content.bytes{x}}}}}, _) == Some{x}: Maybe<&2, Texts.Bytes()>}
        {==}))
