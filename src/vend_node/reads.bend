import Base
import ../shared/shared/ledger.bend as Ledgers
import ../shared/shared/shared/shared/hash.bend as Hashes
import ../shared/shared/shared/shared/shared.bend as Shared
import ../shared/shared/shared/text.bend as Texts
import ./answers.bend as Answers
import ./codes.bend as Coded
import ./content.bend as Contents
import ./facts.bend as Facts
import ./lines.bend as Lines
import ./mirror.bend as Mirror
import ./shared/files.bend as Files
import ./shared/format.bend as Formats
import ./shared/lists.bend as Lists
import ./spec.bend as Spec
import ./stays.bend as Stays
import ./types.bend as Types
import ./versions.bend as Versions

# What the content of a version is
# --------------------------------

# the content of a version stays as the facts grow, while the larger set
# names no liar and is sound for its node
def Content.of_stays(+name: String, +s: Facts.Facts(), +s2: Facts.Facts(), +c: Ledgers.Line, +k: Nat, +t: Files.Files) -> {
  Facts.Facts.wider(s, s2) == True{}: Bool
} -> {Facts.Facts.liars(s2) == []: List<&2, String>} -> {Facts.Facts.ok(name, s2) == True{}: Bool} -> {
  Contents.Content.of(s, c, k) == Some{t}: Maybe<&2, Files.Files>
} -> {Contents.Content.of(s2, c, k) == Some{t}: Maybe<&2, Files.Files>}:
  ?TODO

# whether a merge fits stays, once it does
def Merge.fits_stays(+name: String, +s: Facts.Facts(), +s2: Facts.Facts(), +c: Ledgers.Line, +j: Nat, +e: Types.Entry) -> {
  Facts.Facts.wider(s, s2) == True{}: Bool
} -> {Facts.Facts.liars(s2) == []: List<&2, String>} -> {Facts.Facts.ok(name, s2) == True{}: Bool} -> {
  Contents.Merge.fits(s, c, j, e) == True{}: Bool
} -> {Contents.Merge.fits(s2, c, j, e) == True{}: Bool}:
  ?TODO
