import Base
import ../shared/shared/ledger.bend as Ledgers
import ../shared/shared/shared/shared/hash.bend as Hashes
import ../shared/shared/shared/shared/shared.bend as Shared
import ../shared/shared/shared/text.bend as Texts
import ./codes.bend as Coded
import ./facts.bend as Facts
import ./groups.bend as Groups
import ./lines.bend as Lines
import ./shared/lists.bend as Lists
import ./spec.bend as Spec
import ./types.bend as Types

# What stays as the facts grow
# ----------------------------
# The versions that a set of facts decides stay when the set grows, while the
# larger set names no liar and is sound for its node: two picks cannot both
# have more than half of the votes of a slot unless a voter cast two votes.
# Premises, each an equation: w says that s2 is wider than s, h that s2 names
# no liar, o that s2 is sound for the node name.

# a decided pick stays decided
def Votes.decided_stays(+s: Facts.Facts(), +s2: Facts.Facts(), +st: Types.Step, +ds: List<&2, String>, +pk: Types.Pick) -> {
  Facts.Facts.wider(s, s2) == True{}: Bool
} -> {Facts.Facts.liars(s2) == []: List<&2, String>} -> {
  Lines.Votes.decided(s, st, ds) == Some{pk}: Maybe<&2, Types.Pick>
} -> {Lines.Votes.decided(s2, st, ds) == Some{pk}: Maybe<&2, Types.Pick>}:
  ?TODO

# the versions of a line stay: the larger set decides them, and maybe more
# after them
def Line.versions_stay(+name: String, +s: Facts.Facts(), +s2: Facts.Facts(), +c: Ledgers.Line, +vs: List<&2, Types.Entry>) -> {
  Facts.Facts.wider(s, s2) == True{}: Bool
} -> {Facts.Facts.liars(s2) == []: List<&2, String>} -> {Facts.Facts.ok(name, s2) == True{}: Bool} -> {
  Lines.Line.versions(s, c) == Some{vs}: Maybe<&2, List<&2, Types.Entry>>
} -> Exists(
  List<&2, Types.Entry>,
  vs2 => {
    Lines.Line.versions(s2, c) == Some{vs2}: Maybe<&2, List<&2, Types.Entry>>
  }
    & Lists.List.Ext(Types.Entry, vs, vs2)
):
  ?TODO

# a version of a line stays
def Line.at_stays(+name: String, +s: Facts.Facts(), +s2: Facts.Facts(), +c: Ledgers.Line, +k: Nat, +e: Types.Entry) -> {
  Facts.Facts.wider(s, s2) == True{}: Bool
} -> {Facts.Facts.liars(s2) == []: List<&2, String>} -> {Facts.Facts.ok(name, s2) == True{}: Bool} -> {
  Lines.Line.at(s, c, k) == Some{e}: Maybe<&2, Types.Entry>
} -> {Lines.Line.at(s2, c, k) == Some{e}: Maybe<&2, Types.Entry>}:
  ?TODO

# the rule of the version after some versions stays
def Rule.after_stays(+name: String, +s: Facts.Facts(), +s2: Facts.Facts(), +c: Ledgers.Line, +vs: List<&2, Types.Entry>, +u: Lines.Rule) -> {
  Facts.Facts.wider(s, s2) == True{}: Bool
} -> {Facts.Facts.liars(s2) == []: List<&2, String>} -> {Facts.Facts.ok(name, s2) == True{}: Bool} -> {
  Lines.Rule.after(s, c, vs) == Some{u}: Maybe<&2, Lines.Rule>
} -> {Lines.Rule.after(s2, c, vs) == Some{u}: Maybe<&2, Lines.Rule>}:
  ?TODO
