import Base
import ../shared/shared/ledger.bend as Ledgers
import ../shared/shared/shared/shared/shared.bend as Shared
import ./facts.bend as Facts
import ./lines.bend as Lines
import ./run/content.bend as RContents
import ./run/facts.bend as RFacts
import ./run/known.bend as RKnown
import ./run/files.bend as Files
import ./run/lines.bend as RLines
import ./shared/files.bend as FileLaws
import ./shared/format.bend as Formats
import ./spec.bend as Spec
import ./types.bend as Types

# Content
# -------
# The content of a version is read from the versions of its line: what the
# version before held, changed by the request of the version. A move and a
# merge read a version of another line, so a read goes from line to line, at
# most as many times as the node holds facts (Facts.fuel).
#
# The code that runs is in run/content.bend: it reads the plain map of the facts
# and builds no proof. Here each def that reads the facts is that code on the
# map of a set of facts (Facts.crit), so the laws said of the set are laws of
# the code that runs.

# Ways
# ----
# A merge pins its base, and a way back to it from each side: points, each
# reached from the one before by going down its line, or by the version that
# it takes from another line. A node checks the ways; it does not search.

# the point w is reached in one hop from version k of the line c
def Way.hop(+s: Facts.Facts(), +c: Ledgers.Line, +k: Nat, w: Spec.Point) -> Bool:
  RContents.Way.hop(RKnown.Known.none(), Facts.Facts.crit(s), c, k, w)

# ws is a way from version k of the line c back to the point a
def Way.ok(
  +s: Facts.Facts(),
  +a: Spec.Point,
  ws: List<&2, Spec.Point>,
  +c: Ledgers.Line,
  +k: Nat
) -> Bool:
  RContents.Way.ok(RKnown.Known.none(), Facts.Facts.crit(s), a, ws, c, k)

# the ways ours and theirs lead to the base m, if any, from version j of the
# line c and from the point t
def Merge.fits.of(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +j: Nat,
  m: Maybe<&2, Spec.Point>,
  ours: List<&2, Spec.Point>,
  theirs: List<&2, Spec.Point>,
  t: Spec.Point
) -> Bool:
  RContents.Merge.fits.of(RKnown.Known.none(), Facts.Facts.crit(s), c, j, m, ours, theirs, t)

# the entry e, version 1+j of the line c, pins a base that both merged
# versions come from, or none
def Merge.fits(+s: Facts.Facts(), +c: Ledgers.Line, +j: Nat, +e: Types.Entry) -> Bool:
  RContents.Merge.fits(RKnown.Known.none(), Facts.Facts.crit(s), c, j, e)

# The content of a version
# ------------------------

# the merge that the entry m, if any, is fits
def Entry.fits(+s: Facts.Facts(), +c: Ledgers.Line, +j: Nat, m: Maybe<&2, Types.Entry>) -> Bool:
  RContents.Entry.fits(RKnown.Known.none(), Facts.Facts.crit(s), c, j, m)

# the content of version k of the line c in the facts s, read through at most
# fuel versions (nothing while the node does not hold enough)
def Content.at(
  +fuel: Nat,
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat
) -> Maybe<&2, Files.Files()>:
  RContents.Content.at(fuel, RKnown.Known.none(), Facts.Facts.crit(s), c, k)

# the content of version k of the line c in the facts s
def Content.of(+s: Facts.Facts(), +c: Ledgers.Line, +k: Nat) -> Maybe<&2, Files.Files()>:
  RContents.Content.of(RKnown.Known.none(), Facts.Facts.crit(s), c, k)

# the words of the resource at the path p in version k of the line c
def Content.read(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +p: String
) -> Maybe<&2, Maybe<&2, List<&2, U32>>>:
  RContents.Content.read(RKnown.Known.none(), Facts.Facts.crit(s), c, k, p)

# Laws of well-formed content
# ---------------------------
# The files of a version are a plain map, and the code that runs builds no
# proof that it is well formed. It is: the content of a version is made from
# no file by writes, and each write keeps the map well formed. The laws of
# files (FileLaws) ask for this.

# the content m, if the node holds it, is well formed
def Content.sound(m: Maybe<&2, Files.Files>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{t}:
      FileLaws.Files.wf(t)

# a content that is well formed, when it is the files t, gives t well formed
def Content.sound_some(
  -m: Maybe<&2, Files.Files>,
  -t: Files.Files,
  e: {m == Some{t}: Maybe<&2, Files.Files>}
) -> {Content.sound(m) == True{}: Bool} -> {FileLaws.Files.wf(t) == True{}: Bool}:
  %e: {Content.sound(m) == True{}: Bool} -> {Content.sound(_) == True{}: Bool}
  h => h

# a merge put keeps the files well formed
def Merge.put_wf(
  acc: Files.Files,
  +p: String,
  m: Maybe<&2, Maybe<&2, List<&2, U32>>>
) -> {
  FileLaws.Files.wf(acc) == True{}: Bool
} -> {FileLaws.Files.wf(RContents.Merge.put(acc, p, m)) == True{}: Bool}:
  match m:
    case None{}:
      h => h
    case Some{x}:
      h => FileLaws.Files.set_wf(acc, p, x)(h)

# the merge of each of the paths ps keeps the files well formed
def Merge.fold_wf(
  +b: Files.Files,
  +o: Files.Files,
  +t: Files.Files,
  ps: List<&2, String>,
  +acc: Files.Files
) -> {
  FileLaws.Files.wf(acc) == True{}: Bool
} -> {FileLaws.Files.wf(RContents.Merge.fold(b, o, t, ps, acc)) == True{}: Bool}:
  match ps:
    case Nil{}:
      h => h
    case Con{+p, rest}:
      h => Merge.fold_wf(
        b,
        o,
        t,
        rest,
        RContents.Merge.put(acc, p, RContents.Merge.at(b, o, t, p))
      )(Merge.put_wf(acc, p, RContents.Merge.at(b, o, t, p))(h))

# the merge of well formed files is well formed
def Merge.files_wf(
  +b: Files.Files,
  +o: Files.Files,
  +t: Files.Files
) -> {
  FileLaws.Files.wf(o) == True{}: Bool
} -> {FileLaws.Files.wf(RContents.Merge.files(b, o, t)) == True{}: Bool}:
  h => Merge.fold_wf(b, o, t, RContents.Merge.paths(b, o, t), o)(h)

# the merge of a well formed content is well formed
def Merge.of_sound(
  fits: Bool,
  ours: Maybe<&2, Files.Files>,
  theirs: Maybe<&2, Files.Files>,
  base: Maybe<&2, Files.Files>
) -> {
  Content.sound(ours) == True{}: Bool
} -> {Content.sound(RContents.Merge.of(fits, ours, theirs, base)) == True{}: Bool}:
  match fits ours theirs base:
    case True{} Some{+o} Some{+t} Some{+b}:
      h => Merge.files_wf(b, o, t)(h)
    case True{} Some{o} Some{t} None{}:
      h => {==}
    case True{} Some{o} None{} base:
      h => {==}
    case True{} None{} theirs base:
      h => {==}
    case False{} ours theirs base:
      h => {==}

# a write keeps a content well formed
def Content.write_sound(
  +p: String,
  w: Maybe<&2, List<&2, U32>>,
  m: Maybe<&2, Files.Files>
) -> {
  Content.sound(m) == True{}: Bool
} -> {Content.sound(RContents.Content.write(p, w, m)) == True{}: Bool}:
  match m:
    case None{}:
      h => {==}
    case Some{t}:
      h => FileLaws.Files.set_wf(t, p, w)(h)

# a request keeps a content well formed
def Content.apply_sound(
  r: Spec.Request,
  fits: Bool,
  prev: Maybe<&2, Files.Files>,
  other: Maybe<&2, Files.Files>,
  base: Maybe<&2, Files.Files>
) -> {
  Content.sound(prev) == True{}: Bool
} -> {
  Content.sound(other) == True{}: Bool
} -> {Content.sound(RContents.Content.apply(r, fits, prev, other, base)) == True{}: Bool}:
  match r:
    case Spec.Request.Start{os}:
      hp => ho => hp
    case Spec.Request.Write{b, p, w}:
      hp => ho => Content.write_sound(p, w, prev)(hp)
    case Spec.Request.Merge{f, x}:
      hp => ho => Merge.of_sound(fits, prev, other, base)(hp)
    case Spec.Request.Resolve{m, p, w}:
      hp => ho => Content.write_sound(p, w, prev)(hp)
    case Spec.Request.Mark{b, m, v}:
      hp => ho => hp
    case Spec.Request.Move{b, t, v}:
      hp => ho => ho
    case Spec.Request.Group{h, g, ms}:
      hp => ho => hp
    case Spec.Request.Own{c, g}:
      hp => ho => hp

# a version keeps a content well formed
def Content.next_sound(
  m: Maybe<&2, Types.Entry>,
  fits: Bool,
  prev: Maybe<&2, Files.Files>,
  other: Maybe<&2, Files.Files>,
  base: Maybe<&2, Files.Files>
) -> {
  Content.sound(prev) == True{}: Bool
} -> {
  Content.sound(other) == True{}: Bool
} -> {Content.sound(RContents.Content.next(m, fits, prev, other, base)) == True{}: Bool}:
  match m:
    case None{}:
      hp => ho => {==}
    case Some{e}:
      hp => ho => Content.apply_sound(
        RLines.Ask.request(RLines.Entry.ask(e)),
        fits,
        prev,
        other,
        base
      )(hp)(ho)

# the content of version 0 is well formed
def Content.first_sound(
  m: Maybe<&2, Types.Entry>
) -> {Content.sound(RContents.Content.first(m)) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{e}:
      FileLaws.Files.new_wf()

# the content of a version, as the code that runs reads it from a map of
# facts, is well formed
def Content.at_sound(
  +fuel: Nat,
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +k: Nat
) -> {Content.sound(RContents.Content.at(fuel, RKnown.Known.none(), s, c, k)) == True{}: Bool}:
  match fuel k:
    case 0n k:
      {==}
    case 1n+f 0n:
      Content.first_sound(RLines.Line.at(s, c, 0n))
    case 1n+f 1n+j:
      Content.next_sound(
        RLines.Line.at(s, c, 1n+j),
        RContents.Entry.fits(RKnown.Known.none(), s, c, j, RLines.Line.at(s, c, 1n+j)),
        RContents.Content.at(f, RKnown.Known.none(), s, c, j),
        RContents.Content.at(
          f,
          RKnown.Known.none(),
          s,
          Spec.Point.line(RContents.Entry.taken(c, RLines.Line.at(s, c, 1n+j))),
          Spec.Point.n(RContents.Entry.taken(c, RLines.Line.at(s, c, 1n+j)))
        ),
        RContents.Content.at(
          f,
          RKnown.Known.none(),
          s,
          Spec.Point.line(RContents.Entry.based(c, RLines.Line.at(s, c, 1n+j))),
          Spec.Point.n(RContents.Entry.based(c, RLines.Line.at(s, c, 1n+j)))
        )
      )(
        Content.at_sound(f, s, c, j)
      )(
        Content.at_sound(
          f,
          s,
          Spec.Point.line(RContents.Entry.taken(c, RLines.Line.at(s, c, 1n+j))),
          Spec.Point.n(RContents.Entry.taken(c, RLines.Line.at(s, c, 1n+j)))
        )
      )

# the files that are the content of a version are well formed
def Content.at_wf(
  +fuel: Nat,
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  -t: Files.Files
) -> {
  Content.at(fuel, s, c, k) == Some{t}: Maybe<&2, Files.Files>
} -> {FileLaws.Files.wf(t) == True{}: Bool}:
  e => Content.sound_some(
    Content.at(fuel, s, c, k),
    t,
    e
  )(Content.at_sound(fuel, Facts.Facts.crit(s), c, k))

# the files that are the content of a version are well formed
def Content.of_wf(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  -t: Files.Files
) -> {
  Content.of(s, c, k) == Some{t}: Maybe<&2, Files.Files>
} -> {FileLaws.Files.wf(t) == True{}: Bool}:
  e => Content.at_wf(Facts.Facts.fuel(s), s, c, k, t)(e)
