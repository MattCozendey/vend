import Base
import ../../shared/shared/ledger.bend as Ledgers
import ../../shared/shared/shared/shared/code.bend as Codes
import ../../shared/shared/shared/shared/crit.bend as Crits
import ../../shared/shared/shared/shared/crit_order.bend as Orders
import ../../shared/shared/shared/shared/hash.bend as Hashes
import ../../shared/shared/shared/shared/shared.bend as Shared
import ../codes.bend as Coded
import ../spec.bend as Spec
import ../types.bend as Types
import ./facts.bend as Facts
import ./files.bend as Files
import ./lines.bend as Lines

# Known states
# ------------
# The state of a line (its versions and its next slot) is read from all the
# facts. A node keeps the states that it has read in a table, and reads a
# line through it: the state that the table holds for the line, else the
# state that the facts give. Every def of run/ that reads the state of a line
# takes the table. With the empty table (Known.none) each read is the read
# from the facts, by computation: this is what the laws are said of.
# fast.bend proves that a table whose entries are what the facts give
# (Known.ok) changes no read.

# The node also keeps the content of versions that it has read (Held): the
# files of a version, with the fuel that reads them from the facts (depth).
# A read of a content with at least that fuel takes the files from the table.

# The node also keeps, for a line, the ids of the requests that made its
# versions, as a set (Made): whether a request made a version of the line is
# then one read of the set, not a read of each version.

# The node also keeps the facts that a work may still act on (Open): the asks
# whose request made no version of its line yet, and the ballots for a slot
# that is not decided yet, in the order of the facts. A work walks them, not
# all the facts. With them it keeps the greatest number of an ask among all
# the facts, so the next ask gets its number without a walk. Only the first
# such entry, before the contents, is read.

# a version of a line: its number and its entry
type Found is Data:
  Found{n: Nat, entry: Types.Entry}

# the versions of a line by the id of the request that made each: a map from
# a short key (Id.key) to the versions of that key, the newest first; and
# the count of the versions
type Ids is Data:
  Ids{map: Crits.Crit<List<&2, Found>>, count: Nat}

# the content of a version of a line, which a read with the fuel depth gives
type Held is Data:
  Held{line: Ledgers.Line, version: Nat, depth: Nat, files: Files.Files()}

# what a table says of the facts of a node: the state of a line, or the era
# and the rule of its next version, or the ids of its versions, or the facts
# that a work may still act on (with the greatest number of an ask, the
# newest writes, and the line of each merge), or the contents of versions,
# each under the key of its line and version (Held.key), with a number that
# is at most the count of the facts of the node (low): a content read with a
# fuel of at most low is what a read with the fuel of the facts gives
type Kept is Data:
  Kept{line: Ledgers.Line, state: Lines.State}
  Ruled{line: Ledgers.Line, era: Nat, rule: Lines.Rule}
  Made{line: Ledgers.Line, ids: Ids}
  Open{
    facts: List<&2, Types.Fact>,
    peak: Nat,
    tops: Crits.Crit<Types.Ask>,
    merges: Crits.Crit<Ledgers.Line>
  }
  Stock{held: Crits.Crit<Held>, low: Nat}

# the era and the rule of the next version of a line
type Mark is Data:
  Mark{era: Nat, rule: Lines.Rule}

# what a node keeps of a line: its state, the era and the rule of its next
# version, and the ids of its versions, each if the node has read it
type Info is Data:
  Info{
    line: Ledgers.Line,
    state: Maybe<&2, Lines.State>,
    mark: Maybe<&2, Mark>,
    ids: Maybe<&2, Ids>
  }

# what a node keeps: what it has read of each line, under the key of the
# line (Line.key); what it holds for a work, if any; and the contents of
# versions with their number low
type Table is Data:
  Table{lines: Crits.Crit<Info>, shelf: Maybe<&2, Kept>, held: Crits.Crit<Held>, low: Nat}

# what a node keeps
def Known() -> Data:
  Table

# the table that holds nothing
def Known.none() -> Known():
  Table{Crits.Crit.new(Info), None{}, Crits.Crit.new(Held), 0n}

# the key of the line c in a table: its code, so two lines have two keys
def Line.key(c: Ledgers.Line) -> List<&2, U32>:
  Ledgers.Line.code(c, [])

# what a node that has read nothing of the line c keeps of it
def Info.blank(c: Ledgers.Line) -> Info:
  Info{c, None{}, None{}, None{}}

# the line of i
def Info.line(i: Info) -> Ledgers.Line:
  match i:
    case Info{c, m, r, x}:
      c

# the state of i, if any
def Info.state(i: Info) -> Maybe<&2, Lines.State>:
  match i:
    case Info{c, m, r, x}:
      m

# the era and the rule of i, if any
def Info.mark(i: Info) -> Maybe<&2, Mark>:
  match i:
    case Info{c, m, r, x}:
      r

# the ids of i, if any
def Info.ids(i: Info) -> Maybe<&2, Ids>:
  match i:
    case Info{c, m, r, x}:
      x

# the key of i in a table: the key of its line
def Info.key(i: Info) -> List<&2, U32>:
  Line.key(Info.line(i))

# i with the state st
def Info.state.set(i: Info, st: Lines.State) -> Info:
  match i:
    case Info{c, m, r, x}:
      Info{c, Some{st}, r, x}

# i with the era n and the rule u
def Info.mark.set(i: Info, n: Nat, u: Lines.Rule) -> Info:
  match i:
    case Info{c, m, r, x}:
      Info{c, m, Some{Mark{n, u}}, x}

# i with the ids y
def Info.ids.set(i: Info, y: Ids) -> Info:
  match i:
    case Info{c, m, r, x}:
      Info{c, m, r, Some{y}}

# m, or else what a node that has read nothing of the line c keeps of it
def Info.or(m: Maybe<&2, Info>, c: Ledgers.Line) -> Info:
  match m:
    case None{}:
      Info.blank(c)
    case Some{i}:
      i

# what the lines l hold of the line c
def Infos.of(l: Crits.Crit<Info>, +c: Ledgers.Line) -> Info:
  Info.or(Crits.Crit.get(Info, l, Line.key(c)), c)

# the lines l with i, under the key of its line
def Infos.with(+l: Crits.Crit<Info>, +i: Info) -> Crits.Crit<Info>:
  Crits.Crit.set(~Info, l, Info.key(i), i)

# what the table kn holds of the line c
def Known.info(kn: Known(), +c: Ledgers.Line) -> Info:
  match kn:
    case Table{l, sh, h, q}:
      Infos.of(l, c)

# the state that the table kn holds for the line c, if any
def Known.find(kn: Known(), +c: Ledgers.Line) -> Maybe<&2, Lines.State>:
  Info.state(Known.info(kn, c))

# the rule of m, if any
def Mark.rule(m: Maybe<&2, Mark>) -> Maybe<&2, Lines.Rule>:
  match m:
    case None{}:
      None{}
    case Some{Mark{n, u}}:
      Some{u}

# the era of m, if any
def Mark.era(m: Maybe<&2, Mark>) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      None{}
    case Some{Mark{n, u}}:
      Some{n}

# the rule of the next version of the line c that the table kn holds, if any
def Known.ruled(kn: Known(), +c: Ledgers.Line) -> Maybe<&2, Lines.Rule>:
  Mark.rule(Info.mark(Known.info(kn, c)))

# the key of the content of version k of the line c: the version first, so
# that the keys of two versions differ in their first word
def Held.key(c: Ledgers.Line, k: Nat) -> List<&2, U32>:
  Codes.Code.count(k, Ledgers.Line.code(c, []))

# the era of the next version of the line c that the table kn holds, if any
def Known.era(kn: Known(), +c: Ledgers.Line) -> Maybe<&2, Nat>:
  Mark.era(Info.mark(Known.info(kn, c)))

# the content m, when it is of version k of the line c
def Held.of(m: Maybe<&2, Held>, c: Ledgers.Line, k: Nat) -> Maybe<&2, Held>:
  match m:
    case None{}:
      None{}
    case Some{Held{+c2, +k2, d, x}}:
      Shared.Maybe.when(
        Held,
        List.all.if(u2 => Ledgers.Line.is_eq(c2, c), Nat.is_eq(k2, k)),
        u => Some{Held{c2, k2, d, x}}
      )

# the content of version k of the line c among the contents m
def Stock.get(m: Crits.Crit<Held>, +c: Ledgers.Line, +k: Nat) -> Maybe<&2, Held>:
  Held.of(Crits.Crit.get(Held, m, Held.key(c, k)), c, k)

# the content of version k of the line c that the table kn holds, with the
# fuel that reads it
def Known.held(kn: Known(), +c: Ledgers.Line, +k: Nat) -> Maybe<&2, Held>:
  match kn:
    case Table{l, sh, h, q}:
      Stock.get(h, c, k)

# the files of the content m, if a read with the fuel f gives it
def Known.files.of(m: Maybe<&2, Held>, f: Nat) -> Maybe<&2, Files.Files()>:
  match m:
    case Some{Held{c, k, d, x}}:
      Shared.Maybe.when(Files.Files(), Nat.is_le(d, f), u => Some{x})
    case None{}:
      None{}

# the content of version k of the line c that the table kn holds, if a read
# with the fuel f gives it
def Known.files(kn: Known(), +c: Ledgers.Line, +k: Nat, f: Nat) -> Maybe<&2, Files.Files()>:
  Known.files.of(Known.held(kn, c, k), f)

# the fuel of the content m, if any
def Known.depth.of(m: Maybe<&2, Held>) -> Maybe<&2, Nat>:
  match m:
    case Some{Held{c, k, d, x}}:
      Some{d}
    case None{}:
      None{}

# the fuel that reads the content of version k of the line c that the table
# kn holds
def Known.depth(kn: Known(), +c: Ledgers.Line, +k: Nat) -> Maybe<&2, Nat>:
  Known.depth.of(Known.held(kn, c, k))

# the contents m with the content e, under its key
def Stock.put(+m: Crits.Crit<Held>, e: Held) -> Crits.Crit<Held>:
  match e:
    case Held{+c, +k, d, x}:
      Crits.Crit.set(~Held, m, Held.key(c, k), Held{c, k, d, x})

# the table kn with the content e
def Known.hold(kn: Known(), e: Held) -> Known():
  match kn:
    case Table{l, sh, h, q}:
      Table{l, sh, Stock.put(h, e), q}

# the contents that the table kn holds, and nothing else
def Known.contents(kn: Known()) -> Known():
  match kn:
    case Table{l, sh, h, q}:
      Table{Crits.Crit.new(Info), None{}, h, q}

# the number that is at most the count of the facts, that the table kn holds
# with its contents
def Known.low(kn: Known()) -> Nat:
  match kn:
    case Table{l, sh, h, q}:
      q

# the table kn with one more as the number of its contents: for facts with
# one more fact
def Known.deeper(kn: Known()) -> Known():
  match kn:
    case Table{l, sh, h, q}:
      Table{l, sh, h, 1n+q}

# the table kn with the number g, the count of the facts, with its contents
def Known.sync(kn: Known(), g: Nat) -> Known():
  match kn:
    case Table{l, sh, h, q}:
      Table{l, sh, h, g}

# the table a with the contents of the table b in the place of its own
def Known.join(a: Known(), b: Known()) -> Known():
  match a b:
    case Table{l, sh, h, q} Table{l2, sh2, h2, q2}:
      Table{l, sh, h2, q2}

# the table kn that also says e: the state, the rule or the ids of a line
# with what it holds of the line; the contents, or what it holds for a work,
# in the place of its own
def Known.add(e: Kept, kn: Known()) -> Known():
  match e kn:
    case Kept{+c, st} Table{+l, sh, h, q}:
      Table{Infos.with(l, Info.state.set(Infos.of(l, c), st)), sh, h, q}
    case Ruled{+c, n, u} Table{+l, sh, h, q}:
      Table{Infos.with(l, Info.mark.set(Infos.of(l, c), n, u)), sh, h, q}
    case Made{+c, x} Table{+l, sh, h, q}:
      Table{Infos.with(l, Info.ids.set(Infos.of(l, c), x)), sh, h, q}
    case Open{fs, n, tx, mx} Table{l, sh, h, q}:
      Table{l, Some{Open{fs, n, tx, mx}}, h, q}
    case Stock{m, g} Table{l, sh, h, q}:
      Table{l, sh, m, g}

# Open facts
# ----------

# what the table kn holds for a work, if any
def Known.shelf(kn: Known()) -> Maybe<&2, Kept>:
  match kn:
    case Table{l, sh, h, q}:
      sh

# the facts that a work may still act on, of the entry m, if it holds them
def Shelf.facts(m: Maybe<&2, Kept>) -> Maybe<&2, List<&2, Types.Fact>>:
  match m:
    case Some{Open{fs, n, tx, mx}}:
      Some{fs}
    case _:
      None{}

# the facts that a work may still act on, that the table kn holds
def Known.open(kn: Known()) -> Maybe<&2, List<&2, Types.Fact>>:
  Shelf.facts(Known.shelf(kn))

# the facts m that a work may act on, or else all the facts of s
def Open.or(m: Maybe<&2, List<&2, Types.Fact>>, s: Facts.Plain()) -> List<&2, Types.Fact>:
  match m:
    case None{}:
      Facts.Facts.list(s)
    case Some{fs}:
      fs

# the facts that a work walks: those that the table kn holds for it, else
# all the facts of s
def Known.facts(kn: Known(), s: Facts.Plain()) -> List<&2, Types.Fact>:
  Open.or(Known.open(kn), s)

# the greatest number of an ask in the facts s: as the entry m holds it, else
# read from the facts
def Shelf.peak(m: Maybe<&2, Kept>, s: Facts.Plain()) -> Nat:
  match m:
    case Some{Open{fs, n, tx, mx}}:
      n
    case _:
      Facts.Seq.peak(Facts.Facts.list(s))

# the greatest number of an ask in the facts s, read through the table kn
def Known.peak(kn: Known(), s: Facts.Plain()) -> Nat:
  Shelf.peak(Known.shelf(kn), s)

# the greatest number of an ask that the entry m holds; else 0
def Shelf.top(m: Maybe<&2, Kept>) -> Nat:
  match m:
    case Some{Open{fs, n, tx, mx}}:
      n
    case _:
      0n

# the table kn with the facts fs, the number n, the newest writes tx and the
# lines mx of merges in the place of what it holds for a work, if it holds it
def Known.reopen(
  kn: Known(),
  fs: List<&2, Types.Fact>,
  n: Nat,
  tx: Crits.Crit<Types.Ask>,
  mx: Crits.Crit<Ledgers.Line>
) -> Known():
  match kn:
    case Table{l, Some{Open{old, m, old2, old3}}, h, q}:
      Table{l, Some{Open{fs, n, tx, mx}}, h, q}
    case Table{l, sh, h, q}:
      Table{l, sh, h, q}

# the number h, mixed with the characters of t
def Id.mix(t: String, h: U32) -> U32:
  match t:
    case SNil{}:
      h
    case SCon{Chr{x}, rest}:
      Id.mix(rest, ((h * 31) + x: U32))

# Newest writes
# -------------
# A writer reads its own newest write at a path of a branch (View). The node
# keeps, with the facts that a work may act on, the newest write of each
# writer at each path of each branch, in a map: a view is then one read of
# the map, not a walk of all the facts.

# a writer, a branch and a path
type Place is Data:
  Place{writer: String, branch: Ledgers.Line, path: String}

# the place that the request r of the writer w writes, if it is a write
def Request.place(w: String, r: Spec.Request) -> Maybe<&2, Place>:
  match r:
    case Spec.Request.Write{c, q, ws}:
      Some{Place{w, c, q}}
    case _:
      None{}

# the place that the ask a writes, if it is a write
def Ask.place(a: Types.Ask) -> Maybe<&2, Place>:
  match a:
    case Types.Ask{Ledgers.Id{author, name}, k, r}:
      Request.place(author, r)

# an ask that writes the place g: asks of two places differ
def Place.ask(g: Place) -> Types.Ask:
  match g:
    case Place{w, b, p}:
      Types.Ask{Ledgers.Id{w, ""}, 0n, Spec.Request.Write{b, p, None{}}}

# a number that differs for most places
def Place.mix(g: Place) -> U32:
  match g:
    case Place{w, Ledgers.Line{h, None{}}, p}:
      Id.mix(p, Id.mix(w, 0))
    case Place{w, Ledgers.Line{h, Some{b}}, p}:
      Id.mix(p, Id.mix(b, Id.mix(w, 0)))

# the key of the place g in a map: a number that differs for most places,
# then the words of an ask that writes it, so two places have two keys
def Place.key(+g: Place) -> List<&2, U32>:
  Place.mix(g) <> Coded.Ask.words(Place.ask(g))

# the newer of two asks: new, when the node took it in after old
def Ask.later(old: Types.Ask, new: Types.Ask) -> Types.Ask:
  +old = old
  +new = new
  Bool.pick(Types.Ask, Nat.is_lt(Facts.Ask.seq(old), Facts.Ask.seq(new)), new, old)

# the newest writes tx with the ask a at the place m, if any, unless tx
# holds a write there that is not older
def Tops.put(
  +tx: Crits.Crit<Types.Ask>,
  a: Types.Ask,
  m: Maybe<&2, Place>
) -> Crits.Crit<Types.Ask>:
  match m:
    case None{}:
      tx
    case Some{+g}:
      Crits.Crit.upsert(~Types.Ask, ~Ask.later, tx, Place.key(g), a)

# the newest writes tx with the fact f
def Tops.step(tx: Crits.Crit<Types.Ask>, f: Types.Fact) -> Crits.Crit<Types.Ask>:
  match f:
    case Types.Fact.Vote{v, st, x}:
      tx
    case Types.Fact.Ask{+a}:
      Tops.put(tx, a, Ask.place(a))

# the newest writes tx with each of the facts fs, in their order
def Tops.go(fs: List<&2, Types.Fact>, tx: Crits.Crit<Types.Ask>) -> Crits.Crit<Types.Ask>:
  match fs:
    case Nil{}:
      tx
    case Con{f, rest}:
      Tops.go(rest, Tops.step(tx, f))

# the newest write of each writer at each path of each branch, among the
# facts fs: of two writes with one number, the first
def Tops.of(fs: List<&2, Types.Fact>) -> Crits.Crit<Types.Ask>:
  Tops.go(fs, Crits.Crit.new(Types.Ask))

# the newest writes tx with the ask a at the place m, if any: for an ask
# that is newer than each ask that tx was read from
def Tops.set(
  +tx: Crits.Crit<Types.Ask>,
  a: Types.Ask,
  m: Maybe<&2, Place>
) -> Crits.Crit<Types.Ask>:
  match m:
    case None{}:
      tx
    case Some{+g}:
      Crits.Crit.set(~Types.Ask, tx, Place.key(g), a)

# the newest writes tx with the fact f, which is newer than each ask that tx
# was read from
def Tops.join(tx: Crits.Crit<Types.Ask>, f: Types.Fact) -> Crits.Crit<Types.Ask>:
  match f:
    case Types.Fact.Vote{v, st, x}:
      tx
    case Types.Fact.Ask{+a}:
      Tops.set(tx, a, Ask.place(a))

# the newest write at the place g among the newest writes tx
def Tops.get(tx: Crits.Crit<Types.Ask>, +g: Place) -> Maybe<&2, Types.Ask>:
  Crits.Crit.get(Types.Ask, tx, Place.key(g))

# the newest writes that the entry m holds, if it holds them
def Shelf.tops(m: Maybe<&2, Kept>) -> Maybe<&2, Crits.Crit<Types.Ask>>:
  match m:
    case Some{Open{fs, n, tx, mx}}:
      Some{tx}
    case _:
      None{}

# Lines of merges
# ---------------
# A request that resolves a merge is for the line that the merge merges into:
# the line of the first ask of a merge of its id, in the order of the facts.
# The node keeps, with the facts that a work may act on, that line for each
# id, in a map: the line of a merge is then one read of the map, not a walk
# of the facts.

# the line that the merge of the id i merges into, as an ask among fs says
def Merge.line(fs: List<&2, Types.Fact>, +i: Ledgers.Id) -> Maybe<&2, Ledgers.Line>:
  match fs:
    case Nil{}:
      None{}
    case Con{Types.Fact.Vote{v, st, pk}, rest}:
      Merge.line(rest, i)
    case Con{Types.Fact.Ask{Types.Ask{j, k, Spec.Request.Merge{f, x}}}, rest}:
      Shared.Bool.when(
        Maybe<&2, Ledgers.Line>,
        Ledgers.Id.is_eq(j, i),
        u => Some{x},
        u => Merge.line(rest, i)
      )
    case Con{Types.Fact.Ask{a}, rest}:
      Merge.line(rest, i)

# the key of the id i in a map: its code, so two ids have two keys
def Id.code(i: Ledgers.Id) -> List<&2, U32>:
  Ledgers.Id.code(i, [])

# of two lines of one id, the one that the map held
def Line.first(old: Ledgers.Line, new: Ledgers.Line) -> Ledgers.Line:
  old

# the lines mx of merges with the line of the request r of the id i, if r is
# a merge, unless mx holds a line for i
def Mergers.put(
  mx: Crits.Crit<Ledgers.Line>,
  i: Ledgers.Id,
  r: Spec.Request
) -> Crits.Crit<Ledgers.Line>:
  match r:
    case Spec.Request.Merge{f, x}:
      Crits.Crit.upsert(~Ledgers.Line, ~Line.first, mx, Id.code(i), x)
    case _:
      mx

# the lines mx of merges with the fact f
def Mergers.step(mx: Crits.Crit<Ledgers.Line>, f: Types.Fact) -> Crits.Crit<Ledgers.Line>:
  match f:
    case Types.Fact.Vote{v, st, x}:
      mx
    case Types.Fact.Ask{Types.Ask{i, n, r}}:
      Mergers.put(mx, i, r)

# the lines mx of merges with each of the facts fs, in their order
def Mergers.go(fs: List<&2, Types.Fact>, mx: Crits.Crit<Ledgers.Line>) -> Crits.Crit<Ledgers.Line>:
  match fs:
    case Nil{}:
      mx
    case Con{f, rest}:
      Mergers.go(rest, Mergers.step(mx, f))

# the line of each merge among the facts fs, by its id: of two merges of one
# id, the first
def Mergers.of(fs: List<&2, Types.Fact>) -> Crits.Crit<Ledgers.Line>:
  Mergers.go(fs, Crits.Crit.new(Ledgers.Line))

# the line of the merge of the id i among the lines mx
def Mergers.get(mx: Crits.Crit<Ledgers.Line>, i: Ledgers.Id) -> Maybe<&2, Ledgers.Line>:
  Crits.Crit.get(Ledgers.Line, mx, Id.code(i))

# the request r of the id i gives the lines mx no line for an id that they
# hold one for
def Mergers.free(mx: Crits.Crit<Ledgers.Line>, i: Ledgers.Id, r: Spec.Request) -> Bool:
  match r:
    case Spec.Request.Merge{f, x}:
      Maybe.is_none(&2, Ledgers.Line, Mergers.get(mx, i))
    case _:
      True{}

# the fact f gives the lines mx no line for an id that they hold one for:
# then mx with f is the lines of the facts with f
def Mergers.fresh(mx: Crits.Crit<Ledgers.Line>, f: Types.Fact) -> Bool:
  match f:
    case Types.Fact.Vote{v, st, x}:
      True{}
    case Types.Fact.Ask{Types.Ask{i, n, r}}:
      Mergers.free(mx, i, r)

# the lines of merges that the entry m holds, if it holds them
def Shelf.merges(m: Maybe<&2, Kept>) -> Maybe<&2, Crits.Crit<Ledgers.Line>>:
  match m:
    case Some{Open{fs, n, tx, mx}}:
      Some{mx}
    case _:
      None{}

# the line of the merge of the id i: as the entry m holds it, else as an ask
# among the facts that all gives says
def Shelf.line(
  m: Maybe<&2, Kept>,
  all: Unit -> List<&2, Types.Fact>,
  i: Ledgers.Id
) -> Maybe<&2, Ledgers.Line>:
  match m:
    case Some{Open{fs, n, tx, mx}}:
      Mergers.get(mx, i)
    case _:
      Merge.line(all(Unit{}), i)

# Known ids
# ---------

# a short key of the id i: one word; ids of one key share an entry of a set
def Id.key(i: Ledgers.Id) -> List<&2, U32>:
  match i:
    case Ledgers.Id{w, q}:
      [Id.mix(q, Id.mix(w, 0))]

# the versions new, then the versions old
def Ids.join(old: List<&2, Found>, new: List<&2, Found>) -> List<&2, Found>:
  List.append(&2, Found, new, old)

# the request of the id i made one of the versions b
def Ids.holds(b: List<&2, Found>, +i: Ledgers.Id) -> Bool:
  match b:
    case Nil{}:
      False{}
    case Con{Found{n, e}, rest}:
      List.any.if(u => Ids.holds(rest, i), Lines.Entry.is_of(i, e))

# the request of the id i made one of the versions m, if any
def Ids.has.of(m: Maybe<&2, List<&2, Found>>, i: Ledgers.Id) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{b}:
      Ids.holds(b, i)

# the request of the id i made one of the versions of x
def Ids.has(x: Ids, +i: Ledgers.Id) -> Bool:
  match x:
    case Ids{m, n}:
      Ids.has.of(Crits.Crit.get(List<&2, Found>, m, Id.key(i)), i)

# the version m, or else the version f when the request of the id i made it
def Found.or(m: Maybe<&2, Found>, f: Found, i: Ledgers.Id) -> Maybe<&2, Found>:
  match m f:
    case Some{g} _:
      Some{g}
    case None{} Found{n, +e}:
      Shared.Maybe.when(Found, Lines.Entry.is_of(i, e), u => Some{Found{n, e}})

# the oldest of the versions b that the request of the id i made
def Ids.first(b: List<&2, Found>, +i: Ledgers.Id) -> Maybe<&2, Found>:
  match b:
    case Nil{}:
      None{}
    case Con{f, rest}:
      Found.or(Ids.first(rest, i), f, i)

# the oldest of the versions m, if any, that the request of the id i made
def Ids.find.of(m: Maybe<&2, List<&2, Found>>, i: Ledgers.Id) -> Maybe<&2, Found>:
  match m:
    case None{}:
      None{}
    case Some{b}:
      Ids.first(b, i)

# the oldest version of x that the request of the id i made
def Ids.find(x: Ids, +i: Ledgers.Id) -> Maybe<&2, Found>:
  match x:
    case Ids{m, n}:
      Ids.find.of(Crits.Crit.get(List<&2, Found>, m, Id.key(i)), i)

# the ask b is the ask a: the asks are read only when they are of one id
def Ask.is(+a: Types.Ask, +b: Types.Ask) -> Bool:
  List.all.if(u => Coded.Ask.is_eq(b, a), Ledgers.Id.is_eq(Lines.Ask.id(b), Lines.Ask.id(a)))

# the entry e was made by the ask a
def Entry.made_by(a: Types.Ask, e: Types.Entry) -> Bool:
  Ask.is(a, Lines.Entry.ask(e))

# one of the versions b was made by the ask a
def Ids.made.in(b: List<&2, Found>, +a: Types.Ask) -> Bool:
  match b:
    case Nil{}:
      False{}
    case Con{Found{n, e}, rest}:
      List.any.if(u => Ids.made.in(rest, a), Entry.made_by(a, e))

# one of the versions m, if any, was made by the ask a
def Ids.made.of(m: Maybe<&2, List<&2, Found>>, a: Types.Ask) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{b}:
      Ids.made.in(b, a)

# one of the versions of x was made by the ask a
def Ids.made(x: Ids, +a: Types.Ask) -> Bool:
  match x:
    case Ids{m, n}:
      Ids.made.of(Crits.Crit.get(List<&2, Found>, m, Id.key(Lines.Ask.id(a))), a)

# the count of the versions of x
def Ids.count(x: Ids) -> Nat:
  match x:
    case Ids{m, n}:
      n

# the versions of no line
def Ids.new() -> Ids:
  Ids{Crits.Crit.new(List<&2, Found>), 0n}

# the versions acc with the entry e as the next version
def Ids.put(acc: Ids, +e: Types.Entry) -> Ids:
  match acc:
    case Ids{+m, +n}:
      Ids{
        Crits.Crit.upsert(~List<&2, Found>, ~Ids.join, m, Id.key(Lines.Entry.id(e)), [Found{n, e}]),
        1n+n
      }

# the versions acc with each of the entries vs as the next version
def Ids.go(vs: List<&2, Types.Entry>, acc: Ids) -> Ids:
  match vs:
    case Nil{}:
      acc
    case Con{+e, rest}:
      Ids.go(rest, Ids.put(acc, e))

# the versions vs, by the id of the request that made each
def Ids.of(vs: List<&2, Types.Entry>) -> Ids:
  Ids.go(vs, Ids.new())

# ys without as many of its first items as xs has
def Entries.past(xs: List<&2, Types.Entry>, ys: List<&2, Types.Entry>) -> List<&2, Types.Entry>:
  match xs ys:
    case Nil{} ys:
      ys
    case Con{x, xr} Nil{}:
      []
    case Con{x, xr} Con{y, yr}:
      Entries.past(xr, yr)

# the ids that the table kn holds for the line c, if any
def Known.ids(kn: Known(), +c: Ledgers.Line) -> Maybe<&2, Ids>:
  Info.ids(Known.info(kn, c))

# the request of the id i made one of the versions vs: read from their ids
# m, if known
def Made.in(m: Maybe<&2, Ids>, vs: List<&2, Types.Entry>, i: Ledgers.Id) -> Bool:
  match m:
    case None{}:
      Shared.List.some(~Types.Entry, ~Ledgers.Id, ~Lines.Entry.is_of, vs, i)
    case Some{x}:
      Ids.has(x, i)

# the request of the id i made one of the versions vs of the line c, read
# through the table kn
def Known.made(kn: Known(), +c: Ledgers.Line, vs: List<&2, Types.Entry>, i: Ledgers.Id) -> Bool:
  Made.in(Known.ids(kn, c), vs, i)

# the store of the line c
def Known.root(c: Ledgers.Line) -> Ledgers.Line:
  Ledgers.Line{Lines.Line.root(c), None{}}

# the state of the line c, when the state of its store is rs and k
def Known.fresh.at(
  +s: Facts.Plain(),
  c: Ledgers.Line,
  rs: List<&2, Types.Entry>,
  k: Nat
) -> Maybe<&2, Lines.State>:
  match c:
    case Ledgers.Line{h, None{}}:
      Some{Lines.State{rs, k}}
    case Ledgers.Line{h, Some{b}}:
      Lines.Branch.state(s, Ledgers.Line{h, Some{b}}, Some{rs})

# the state of the line c in the facts s: with the state m of its store if
# the table holds it
def Known.fresh.of(
  m: Maybe<&2, Lines.State>,
  +s: Facts.Plain(),
  +c: Ledgers.Line
) -> Maybe<&2, Lines.State>:
  match m:
    case None{}:
      Lines.Line.state(s, c)
    case Some{Lines.State{R, k}}:
      Known.fresh.at(s, c, R, k)

# the state of the line c in the facts s, computed with the state that the
# table kn holds for its store
def Known.fresh(kn: Known(), +s: Facts.Plain(), +c: Ledgers.Line) -> Maybe<&2, Lines.State>:
  Known.fresh.of(Known.find(kn, Known.root(c)), s, c)

# the state of the line c in the facts s, read through the table kn: the
# state that the table holds for it, else (m is none) as the facts give it
def Known.state.of(
  m: Maybe<&2, Lines.State>,
  +kn: Known(),
  +s: Facts.Plain(),
  +c: Ledgers.Line
) -> Maybe<&2, Lines.State>:
  match m:
    case None{}:
      Known.fresh(kn, s, c)
    case Some{st}:
      Some{st}

# the state of the line c in the facts s, read through the table kn
def Known.state(+kn: Known(), +s: Facts.Plain(), +c: Ledgers.Line) -> Maybe<&2, Lines.State>:
  Known.state.of(Known.find(kn, c), kn, s, c)

# the versions of the line c in the facts s, read through the table kn
def Known.versions(
  +kn: Known(),
  +s: Facts.Plain(),
  +c: Ledgers.Line
) -> Maybe<&2, List<&2, Types.Entry>>:
  Maybe.map(&2, Lines.State, List<&2, Types.Entry>, Lines.State.versions, Known.state(kn, s, c))

# version k of the line c in the facts s, read through the table kn
def Known.at(+kn: Known(), +s: Facts.Plain(), +c: Ledgers.Line, k: Nat) -> Maybe<&2, Types.Entry>:
  Lines.Line.at.of(Known.versions(kn, s, c), k)

# the versions of the store of the root h, read through the table kn
def Known.store(
  +kn: Known(),
  +s: Facts.Plain(),
  +h: Hashes.Hash
) -> Maybe<&2, List<&2, Types.Entry>>:
  Known.versions(kn, s, Ledgers.Line{h, None{}})

# the rule after the versions vs of the line c, with the versions rs of its
# store
def Known.rule.at(
  c: Ledgers.Line,
  +vs: List<&2, Types.Entry>,
  rs: List<&2, Types.Entry>
) -> Maybe<&2, Lines.Rule>:
  match c:
    case Ledgers.Line{h, None{}}:
      Lines.Line.rule(None{}, Ledgers.Line{h, None{}}, vs)
    case Ledgers.Line{h, Some{b}}:
      Lines.Line.rule(Some{rs}, Ledgers.Line{h, Some{b}}, vs)

# the rule after the versions vs of the line c: with the state m of its
# store if the table holds it, else as the facts s give it
def Known.rule.of(
  m: Maybe<&2, Lines.State>,
  +s: Facts.Plain(),
  +c: Ledgers.Line,
  +vs: List<&2, Types.Entry>
) -> Maybe<&2, Lines.Rule>:
  match m:
    case None{}:
      Lines.Rule.after(s, c, vs)
    case Some{Lines.State{R, k}}:
      Known.rule.at(c, vs, R)

# the rule of the version of the line c that comes after the versions vs,
# read through the table kn
def Known.rule(
  kn: Known(),
  +s: Facts.Plain(),
  +c: Ledgers.Line,
  +vs: List<&2, Types.Entry>
) -> Maybe<&2, Lines.Rule>:
  Known.rule.of(Known.find(kn, Known.root(c)), s, c, vs)

# the rule of the next version of the line c in the state m, read through
# the table kn
def Known.rule.next(
  kn: Known(),
  +s: Facts.Plain(),
  +c: Ledgers.Line,
  m: Maybe<&2, Lines.State>
) -> Maybe<&2, Lines.Rule>:
  match m:
    case None{}:
      None{}
    case Some{Lines.State{vs, k}}:
      Known.rule(kn, s, c, vs)

# What a work may still act on
# ----------------------------
# A work casts a ballot for an ask only while its request made no version of
# its line, and at the slot of a ballot only while that slot is the next one
# of its line. So a fact that waits no more never gives a ballot again: the
# versions and the next slot of a line only grow. A request that resolves a
# merge is for the line of the merge, read from the lines of merges: it
# waits while the node holds no ask of the merge.

# the facts of a node, and the table through which they are read
type Scene is Data:
  Scene{known: Known(), facts: Facts.Plain()}

# a ballot for the slot k of a line in the state m waits: the next slot of
# the line is not past k
def Slot.waits(m: Maybe<&2, Lines.State>, k: Nat) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{Lines.State{vs, j}}:
      Nat.is_le(j, k)

# the request of the id i waits on the line c in the state m: it made no
# version of the line, as read through the table kn
def Id.waits(m: Maybe<&2, Lines.State>, kn: Known(), +c: Ledgers.Line, i: Ledgers.Id) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{Lines.State{vs, k}}:
      Bool.not(Known.made(kn, c, vs, i))

# the request of the id i waits on the line c in the facts s
def Line.waits(+kn: Known(), +s: Facts.Plain(), +c: Ledgers.Line, i: Ledgers.Id) -> Bool:
  Id.waits(Known.state(kn, s, c), kn, c, i)

# the request of the id i, that resolves a merge of the line m, if the node
# holds an ask of the merge, waits: it made no version of the line
def Resolve.waits(
  m: Maybe<&2, Ledgers.Line>,
  +kn: Known(),
  +s: Facts.Plain(),
  i: Ledgers.Id
) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{+c}:
      Line.waits(kn, s, c, i)

# the request r of the id i waits: it made no version of the line that it is
# for; a start never waits
def Request.waits(+kn: Known(), +s: Facts.Plain(), i: Ledgers.Id, r: Spec.Request) -> Bool:
  match r:
    case Spec.Request.Start{os}:
      False{}
    case Spec.Request.Write{+b, p, w}:
      Line.waits(kn, s, b, i)
    case Spec.Request.Merge{f, +x}:
      Line.waits(kn, s, x, i)
    case Spec.Request.Resolve{m, p, w}:
      Resolve.waits(Shelf.line(Known.shelf(kn), u => Facts.Facts.list(s), m), kn, s, i)
    case Spec.Request.Mark{+b, m, v}:
      Line.waits(kn, s, b, i)
    case Spec.Request.Move{+b, t, v}:
      Line.waits(kn, s, b, i)
    case Spec.Request.Group{h, g, ms}:
      Line.waits(kn, s, Ledgers.Line{h, None{}}, i)
    case Spec.Request.Own{Ledgers.Line{h, b}, g}:
      Line.waits(kn, s, Ledgers.Line{h, None{}}, i)

# a work may still act on the fact f, in the scene g
def Fact.waits(g: Scene, f: Types.Fact) -> Bool:
  match g f:
    case Scene{kn, s} Types.Fact.Vote{v, Types.Step.Broken{}, x}:
      False{}
    case Scene{+kn, +s} Types.Fact.Vote{v, Types.Step.At{+c, k, t}, x}:
      Slot.waits(Known.state(kn, s, c), k)
    case Scene{+kn, +s} Types.Fact.Ask{Types.Ask{i, n, r}}:
      Request.waits(kn, s, i, r)

# the facts among fs that a work may still act on, in the scene g
def Open.of(fs: List<&2, Types.Fact>, +g: Scene) -> List<&2, Types.Fact>:
  Orders.Values.keep(~Types.Fact, ~Scene, ~Fact.waits, fs, g)

# the facts fs, in the order of the facts of a node, with the fact f: an
# insert (Orders.Values.insert) that reads the key of f once
def Open.put(fs: List<&2, Types.Fact>, +f: Types.Fact) -> List<&2, Types.Fact>:
  Orders.Values.put(~Types.Fact, ~Coded.Fact.words, fs, f, Coded.Fact.words(f))

# the facts fs that a work may act on, with the fact f if a work may act on
# it in the scene g
def Open.with(+fs: List<&2, Types.Fact>, +f: Types.Fact, g: Scene) -> List<&2, Types.Fact>:
  Shared.Bool.when(List<&2, Types.Fact>, Fact.waits(g, f), u => Open.put(fs, f), u => fs)

# the request r is a merge
def Request.merges(r: Spec.Request) -> Bool:
  match r:
    case Spec.Request.Merge{f, x}:
      True{}
    case _:
      False{}

# the fact f is the ask of a merge
def Fact.merges(f: Types.Fact) -> Bool:
  match f:
    case Types.Fact.Vote{v, st, x}:
      False{}
    case Types.Fact.Ask{Types.Ask{i, n, r}}:
      Request.merges(r)

# the facts fs that a work may act on, with the fact f if a work may act on
# it in the scene g: when f is the ask of a merge, a request among fs that
# resolves it may wait no more, so each of fs is tested again
def Open.join(
  merges: Bool,
  +fs: List<&2, Types.Fact>,
  +f: Types.Fact,
  +g: Scene
) -> List<&2, Types.Fact>:
  match merges:
    case True{}:
      Open.of(Open.with(fs, f, g), g)
    case False{}:
      Open.with(fs, f, g)

# the table kn without what it holds for a work
def Known.shut(kn: Known()) -> Known():
  match kn:
    case Table{l, sh, h, q}:
      Table{l, None{}, h, q}

# the table kn, whose entry for a work m holds the facts that a work could
# act on before the fact f joined the facts, and the lines of the merges of
# the facts s with f: with the facts that a work may act on in s
def Known.sift.of(m: Maybe<&2, Kept>, +kn: Known(), +s: Facts.Plain(), +f: Types.Fact) -> Known():
  match m:
    case Some{Open{fs, n, tx, mx}}:
      Known.reopen(kn, Open.join(Fact.merges(f), fs, f, Scene{kn, s}), n, tx, mx)
    case _:
      kn

# the table kn, that holds for a work the facts that it could act on before
# the fact f joined the facts, and the lines of the merges of the facts s
# with f: with the facts that a work may act on in s
def Known.sift(+kn: Known(), +s: Facts.Plain(), +f: Types.Fact) -> Known():
  Known.sift.of(Known.shelf(kn), kn, s, f)

# the table kn, when the fact f joins the facts and leaves each line as it
# is: what the entry m holds for a work, with f; s is the facts with f. When
# f is a merge of an id that the table holds a line for, the table lets go of
# what it holds for a work: the next work reads it again
def Known.joined.of(m: Maybe<&2, Kept>, +kn: Known(), +s: Facts.Plain(), +f: Types.Fact) -> Known():
  match m:
    case Some{Open{+fs, +n, +tx, +mx}}:
      Shared.Bool.when(
        Known(),
        Mergers.fresh(mx, f),
        u => Known.sift(
          Known.reopen(
            kn,
            fs,
            Nat.max(Facts.Seq.of(f), n),
            Shared.Bool.when(
              Crits.Crit<Types.Ask>,
              Nat.is_lt(n, Facts.Seq.of(f)),
              u2 => Tops.join(tx, f),
              u2 => Tops.of(Facts.Facts.list(s))
            ),
            Mergers.step(mx, f)
          ),
          s,
          f
        ),
        u => Known.shut(kn)
      )
    case _:
      kn

# the table kn, when the fact f joins the facts and leaves each line as it
# is; s is the facts with f
def Known.joined(+kn: Known(), +s: Facts.Plain(), +f: Types.Fact) -> Known():
  Known.joined.of(Known.shelf(kn), kn, s, f)

# the table kn with the facts of s that a work may act on, the greatest
# number of an ask among all, the facts of s, and the lines mx of their
# merges: a work may act on a fact as read through kn and mx
def Known.opened.by(
  +kn: Known(),
  +s: Facts.Plain(),
  +all: List<&2, Types.Fact>,
  +mx: Crits.Crit<Ledgers.Line>
) -> Known():
  Known.add(
    Open{
      Open.of(all, Scene{Known.add(Open{[], 0n, Crits.Crit.new(Types.Ask), mx}, kn), s}),
      Facts.Seq.peak(all),
      Tops.of(all),
      mx
    },
    kn
  )

# the table kn with the facts of s that a work may act on, and the greatest
# number of an ask among all, the facts of s
def Known.opened.of(+kn: Known(), +s: Facts.Plain(), +all: List<&2, Types.Fact>) -> Known():
  Known.opened.by(kn, s, all, Mergers.of(all))

# the table kn with the facts of s that a work may act on
def Known.opened(+kn: Known(), +s: Facts.Plain()) -> Known():
  Known.opened.of(kn, s, Facts.Facts.list(s))

# the facts m that a work could act on, if known, with the fact f
def Known.walk.of(
  m: Maybe<&2, List<&2, Types.Fact>>,
  f: Types.Fact
) -> Maybe<&2, List<&2, Types.Fact>>:
  match m:
    case None{}:
      None{}
    case Some{fs}:
      Some{Open.put(fs, f)}

# the facts that the table kn holds for a work, if any, with the fact f
def Known.walk(kn: Known(), f: Types.Fact) -> Maybe<&2, List<&2, Types.Fact>>:
  Known.walk.of(Known.open(kn), f)

# the facts w, when a ballot leaves the other lines as they are (safe); else
# none
def Known.walk.if(
  safe: Bool,
  w: Maybe<&2, List<&2, Types.Fact>>
) -> Maybe<&2, List<&2, Types.Fact>>:
  match safe:
    case True{}:
      w
    case False{}:
      None{}

# the table kn with the facts that a work may act on in the facts s, among
# the facts m that it could act on before with the fact that joined them, if
# known; n is the greatest number of an ask in s, t the newest writes of s,
# and x the lines of the merges of s, if known
def Known.moved(
  +kn: Known(),
  +s: Facts.Plain(),
  m: Maybe<&2, List<&2, Types.Fact>>,
  +n: Nat,
  t: Maybe<&2, Crits.Crit<Types.Ask>>,
  x: Maybe<&2, Crits.Crit<Ledgers.Line>>
) -> Known():
  match m t x:
    case Some{fs} Some{+tx} Some{+mx}:
      Known.add(
        Open{Open.of(fs, Scene{Known.add(Open{[], n, tx, mx}, kn), s}), n, tx, mx},
        kn
      )
    case _ _ _:
      kn

# the table kn with the state m, if any, of the line c
def Known.put(kn: Known(), c: Ledgers.Line, m: Maybe<&2, Lines.State>) -> Known():
  match m:
    case None{}:
      kn
    case Some{st}:
      Known.add(Kept{c, st}, kn)

# the table kn with the state of the line c, computed unless the table holds
# it (old)
def Known.learn.of(
  +kn: Known(),
  +s: Facts.Plain(),
  +c: Ledgers.Line,
  old: Maybe<&2, Lines.State>
) -> Known():
  match old:
    case Some{st}:
      kn
    case None{}:
      Known.put(kn, c, Known.fresh(kn, s, c))

# the table kn with the state of the line c in the facts s
def Known.learn.one(+kn: Known(), +s: Facts.Plain(), +c: Ledgers.Line) -> Known():
  Known.learn.of(kn, s, c, Known.find(kn, c))

# the table kn with the rule m, if any, of the next version of the line c,
# which is of the era n
def Known.rule.put(kn: Known(), c: Ledgers.Line, n: Nat, m: Maybe<&2, Lines.Rule>) -> Known():
  match m:
    case None{}:
      kn
    case Some{u}:
      Known.add(Ruled{c, n, u}, kn)

# the era of the next version of the line c in the state m; 0 for none
def Era.next(c: Ledgers.Line, m: Maybe<&2, Lines.State>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{Lines.State{vs, k}}:
      Lines.Line.era(c, vs)

# the table kn with the rule of the next version of the line c, after the
# state that kn holds for c, unless the table holds the rule (old)
def Known.rule.learn.if(old: Bool, +kn: Known(), +s: Facts.Plain(), +c: Ledgers.Line) -> Known():
  match old:
    case True{}:
      kn
    case False{}:
      Known.rule.put(
        kn,
        c,
        Era.next(c, Known.find(kn, c)),
        Known.rule.next(kn, s, c, Known.find(kn, c))
      )

# the table kn with the rule of the next version of the line c, after the
# state that kn holds for c
def Known.rule.learn(+kn: Known(), +s: Facts.Plain(), +c: Ledgers.Line) -> Known():
  Known.rule.learn.if(Maybe.is_some(&2, Lines.Rule, Known.ruled(kn, c)), kn, s, c)

# the table kn with the ids of the versions of the state m, if any, of the
# line c
def Known.ids.put(kn: Known(), c: Ledgers.Line, m: Maybe<&2, Lines.State>) -> Known():
  match m:
    case None{}:
      kn
    case Some{Lines.State{vs, k}}:
      Known.add(Made{c, Ids.of(vs)}, kn)

# the table kn with the ids of the versions of the state that kn holds for
# the line c, unless the table holds them (old)
def Known.ids.learn.if(old: Bool, +kn: Known(), +c: Ledgers.Line) -> Known():
  match old:
    case True{}:
      kn
    case False{}:
      Known.ids.put(kn, c, Known.find(kn, c))

# the table kn with the ids of the versions of the state that kn holds for
# the line c
def Known.ids.learn(+kn: Known(), +c: Ledgers.Line) -> Known():
  Known.ids.learn.if(Maybe.is_some(&2, Ids, Known.ids(kn, c)), kn, c)

# the table kn with the states of the line c and of its store in the facts s,
# with the rule of the next version of c, and with the ids of its versions
def Known.learn(kn: Known(), +s: Facts.Plain(), +c: Ledgers.Line) -> Known():
  Known.ids.learn(
    Known.rule.learn(Known.learn.one(Known.learn.one(kn, s, Known.root(c)), s, c), s, c),
    c
  )

# What a vote forgets
# -------------------

# a vote for a slot of the line c may change the state of the line c2: it is
# c, or c is its store
def Known.hit(c: Ledgers.Line, +c2: Ledgers.Line) -> Bool:
  +c = c
  Bool.or(Ledgers.Line.is_eq(c2, c), Ledgers.Line.is_eq(Known.root(c2), c))

# the lines l without what a vote for a slot of the line c may change: what
# they hold of c, when c is a branch; all of them, when c is a store
def Infos.voted(+l: Crits.Crit<Info>, c: Ledgers.Line) -> Crits.Crit<Info>:
  match c:
    case Ledgers.Line{h, None{}}:
      Crits.Crit.new(Info)
    case Ledgers.Line{h, Some{b}}:
      Infos.with(l, Info.blank(Ledgers.Line{h, Some{b}}))

# the table kn after a vote for a slot of the line c: without the states and
# the rules that the vote may change, without the contents, and without the
# facts that a work may act on
def Known.voted(kn: Known(), c: Ledgers.Line) -> Known():
  match kn:
    case Table{+l, sh, h, q}:
      Table{Infos.voted(l, c), None{}, Crits.Crit.new(Held), 0n}

# the entries a and b are the same
def Entry.same(a: Types.Entry, b: Types.Entry) -> Bool:
  match a b:
    case Types.Entry{p1, k1} Types.Entry{p2, k2}:
      Bool.and(Coded.Pick.is_eq(p1, p2), Nat.is_eq(k1, k2))

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- the left side fails only for versions that differ, which then costs no more than equal versions, where both sides run
# the versions xs and ys are the same
def Entries.same(xs: List<&2, Types.Entry>, ys: List<&2, Types.Entry>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{x, xr} Con{y, yr}:
      Bool.and(Entry.same(x, y), Entries.same(xr, yr))
    case _ _:
      False{}
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the states a and b are the same
def State.same(a: Lines.State, b: Lines.State) -> Bool:
  match a b:
    case Lines.State{v1, k1} Lines.State{v2, k2}:
      Bool.and(Entries.same(v1, v2), Nat.is_eq(k1, k2))

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- the left side fails only for rules that differ, which then costs no more than equal rules, where both sides run
# the rules a and b are the same
def Rule.same(a: Lines.Rule, b: Lines.Rule) -> Bool:
  match a b:
    case Lines.Rule{g1, n1} Lines.Rule{g2, n2}:
      Bool.and(
        Shared.Maybe.is_eq(~String, ~String.eq, g1, g2),
        Shared.List.is_eq(~String, ~String.eq, n1, n2)
      )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# m is the rule u
def Rule.fits(m: Maybe<&2, Lines.Rule>, u: Lines.Rule) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      Rule.same(x, u)

# m is a state of the line c whose next version is of the era n
def Era.fits(m: Maybe<&2, Lines.State>, c: Ledgers.Line, n: Nat) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{Lines.State{vs, k}}:
      Nat.is_eq(n, Lines.Line.era(c, vs))

# m is the state st
def State.fits(m: Maybe<&2, Lines.State>, st: Lines.State) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      State.same(x, st)

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- the left side fails only for versions that differ, which then costs no more than equal versions, where both sides run
# the versions a and b, each with its number, are the same
def Found.same(a: Found, b: Found) -> Bool:
  match a b:
    case Found{n1, e1} Found{n2, e2}:
      Bool.and(Nat.is_eq(n1, n2), Entry.same(e1, e2))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the versions a and b are the same
def Bucket.same(a: List<&2, Found>, b: List<&2, Found>) -> Bool:
  Shared.List.is_eq(~Found, ~Found.same, a, b)

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- the left side fails only for sets that differ, which then costs no more than equal sets, where both sides run
# the sets a and b are the same: key by key, in the same shape
def Map.same(a: Crits.Crit<List<&2, Found>>, b: Crits.Crit<List<&2, Found>>) -> Bool:
  match a b:
    case Crits.Crit.Tip{} Crits.Crit.Tip{}:
      True{}
    case Crits.Crit.Leaf{k1, v1} Crits.Crit.Leaf{k2, v2}:
      Bool.and(Crits.Key.is_eq(k1, k2), Bucket.same(v1, v2))
    case Crits.Crit.Fork{r1, p1, e1, z1, o1} Crits.Crit.Fork{r2, p2, e2, z2, o2}:
      Bool.and(
        Crits.Key.is_eq(r1, r2),
        Bool.and(
          Nat.is_eq(p1, p2),
          Bool.and(
            Shared.Maybe.is_eq(~List<&2, Found>, ~Bucket.same, e1, e2),
            Bool.and(Map.same(z1, z2), Map.same(o1, o2))
          )
        )
      )
    case _ _:
      False{}
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- the left side fails only for maps that differ, which then costs no more than equal maps, where both sides run
# the newest writes a and b are the same: key by key, in the same shape
def Tops.same(a: Crits.Crit<Types.Ask>, b: Crits.Crit<Types.Ask>) -> Bool:
  match a b:
    case Crits.Crit.Tip{} Crits.Crit.Tip{}:
      True{}
    case Crits.Crit.Leaf{k1, v1} Crits.Crit.Leaf{k2, v2}:
      Bool.and(Crits.Key.is_eq(k1, k2), Coded.Ask.is_eq(v1, v2))
    case Crits.Crit.Fork{r1, p1, e1, z1, o1} Crits.Crit.Fork{r2, p2, e2, z2, o2}:
      Bool.and(
        Crits.Key.is_eq(r1, r2),
        Bool.and(
          Nat.is_eq(p1, p2),
          Bool.and(
            Shared.Maybe.is_eq(~Types.Ask, ~Coded.Ask.is_eq, e1, e2),
            Bool.and(Tops.same(z1, z2), Tops.same(o1, o2))
          )
        )
      )
    case _ _:
      False{}
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- the left side fails only for maps that differ, which then costs no more than equal maps, where both sides run
# the lines of merges a and b are the same: key by key, in the same shape
def Mergers.same(a: Crits.Crit<Ledgers.Line>, b: Crits.Crit<Ledgers.Line>) -> Bool:
  match a b:
    case Crits.Crit.Tip{} Crits.Crit.Tip{}:
      True{}
    case Crits.Crit.Leaf{k1, v1} Crits.Crit.Leaf{k2, v2}:
      Bool.and(Crits.Key.is_eq(k1, k2), Ledgers.Line.is_eq(v1, v2))
    case Crits.Crit.Fork{r1, p1, e1, z1, o1} Crits.Crit.Fork{r2, p2, e2, z2, o2}:
      Bool.and(
        Crits.Key.is_eq(r1, r2),
        Bool.and(
          Nat.is_eq(p1, p2),
          Bool.and(
            Shared.Maybe.is_eq(~Ledgers.Line, ~Ledgers.Line.is_eq, e1, e2),
            Bool.and(Mergers.same(z1, z2), Mergers.same(o1, o2))
          )
        )
      )
    case _ _:
      False{}
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the versions a and b, by id, are the same
def Ids.same(a: Ids, b: Ids) -> Bool:
  match a b:
    case Ids{m1, n1} Ids{m2, n2}:
      Bool.and(Map.same(m1, m2), Nat.is_eq(n1, n2))

# m is a state whose versions have the ids x
def Made.fits(m: Maybe<&2, Lines.State>, x: Ids) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{Lines.State{vs, k}}:
      Ids.same(x, Ids.of(vs))

# What a vote continues
# ---------------------
# A node casts a ballot for the next slot of a line whose state it knows. No
# slot below it changes, so the state after the ballot is the run of the
# slots from the known state on: the line is not read again from version 0.

# the state of the line c after each decided slot from st on, in the facts s,
# with the versions r of its store (none for a store): a run that may go one
# slot past the bound of the line
def Known.go.at(
  +s: Facts.Plain(),
  +c: Ledgers.Line,
  +st: Lines.State,
  +r: Maybe<&2, List<&2, Types.Entry>>
) -> Lines.State:
  Lines.Line.run(
    1n+Lines.Line.bound(Facts.Facts.list(s), c),
    s,
    r,
    c,
    st,
    Lines.Line.step(s, r, c, st)
  )

# the versions of its store that a run of a branch reads, from the state m
# of the store, if known
def Known.over.of(m: Maybe<&2, Lines.State>) -> Maybe<&2, Maybe<&2, List<&2, Types.Entry>>>:
  match m:
    case None{}:
      None{}
    case Some{Lines.State{R, j}}:
      Some{Some{R}}

# the versions of its store that a run of the line c reads (none for a
# store), with the state m of the store of c, if known
def Known.over(
  c: Ledgers.Line,
  m: Maybe<&2, Lines.State>
) -> Maybe<&2, Maybe<&2, List<&2, Types.Entry>>>:
  match c:
    case Ledgers.Line{h, None{}}:
      Some{None{}}
    case Ledgers.Line{h, Some{b}}:
      Known.over.of(m)

# the state of the line c after each decided slot from st on, read from the
# facts fs: a run that may go one slot past the greatest slot of c that a
# ballot among fs is for
def Known.go.in(
  +fs: List<&2, Types.Fact>,
  +c: Ledgers.Line,
  +st: Lines.State,
  +r: Maybe<&2, List<&2, Types.Entry>>
) -> Lines.State:
  Lines.Line.run.in(1n+Lines.Line.bound(fs, c), fs, r, c, st, Lines.Line.step.in(fs, r, c, st))

# the state of the line c after each decided slot from st on, in the facts
# s: read from the facts w that hold each ballot that still counts, if known
def Known.go.of(
  w: Maybe<&2, List<&2, Types.Fact>>,
  +s: Facts.Plain(),
  +c: Ledgers.Line,
  +st: Lines.State,
  +r: Maybe<&2, List<&2, Types.Entry>>
) -> Lines.State:
  match w:
    case None{}:
      Known.go.at(s, c, st, r)
    case Some{+fs}:
      Known.go.in(fs, c, st, r)

# the state of the line c in the facts s, after a ballot for its slot k:
# the run from its known state m, when k is the next slot of m and the
# versions r that the run reads are known; the run reads the facts w, if
# known
def Known.next.of(
  w: Maybe<&2, List<&2, Types.Fact>>,
  +s: Facts.Plain(),
  +c: Ledgers.Line,
  k: Nat,
  m: Maybe<&2, Lines.State>,
  r: Maybe<&2, Maybe<&2, List<&2, Types.Entry>>>
) -> Maybe<&2, Lines.State>:
  match m r:
    case Some{+st} Some{+rr}:
      Shared.Maybe.when(
        Lines.State,
        Nat.is_eq(Lines.State.slot(st), k),
        u => Some{Known.go.of(w, s, c, st, rr)}
      )
    case _ _:
      None{}

# a ballot for the slot k of the line c continues the versions of c and
# changes no other line: c is a branch, k is the next slot of its state m,
# and the state ms of its store is known
def Known.safe(
  c: Ledgers.Line,
  m: Maybe<&2, Lines.State>,
  ms: Maybe<&2, Lines.State>,
  k: Nat
) -> Bool:
  match c m ms:
    case Ledgers.Line{h, Some{b}} Some{st} Some{y}:
      Nat.is_eq(Lines.State.slot(st), k)
    case _ _ _:
      False{}

# the contents of the table kn, when a ballot leaves them as they are (safe),
# for the facts with the ballot, one more fact; else none
def Known.spared(safe: Bool, kn: Known()) -> Known():
  match safe:
    case True{}:
      Known.deeper(Known.contents(kn))
    case False{}:
      Known.none()

# the ids of the versions of the state new of a line, from the ids of the
# versions of the state old that it continues, if the three are known: with
# the ids of the versions that old has not
def Made.next(
  new: Maybe<&2, Lines.State>,
  old: Maybe<&2, Lines.State>,
  ids: Maybe<&2, Ids>
) -> Maybe<&2, Ids>:
  match new old ids:
    case Some{Lines.State{vs2, k2}} Some{Lines.State{vs, k}} Some{x}:
      Some{Ids.go(Entries.past(vs, vs2), x)}
    case _ _ _:
      None{}

# the table kn with the ids m, if any, of the versions of the line c
def Known.made.put(kn: Known(), c: Ledgers.Line, m: Maybe<&2, Ids>) -> Known():
  match m:
    case None{}:
      kn
    case Some{x}:
      Known.add(Made{c, x}, kn)

# the table rest with the state m, if any, of the line c after a ballot, and
# with the ids of its versions, continued from those that the table kn held
def Known.cast.to(
  +kn: Known(),
  +c: Ledgers.Line,
  rest: Known(),
  +m: Maybe<&2, Lines.State>
) -> Known():
  Known.made.put(Known.put(rest, c, m), c, Made.next(m, Known.find(kn, c), Known.ids(kn, c)))

# the table kn after a ballot for the slot k of the line c, where s is the
# facts with the ballot: without the states that the ballot may change, with
# the state of c continued from the state that kn holds for it, with the ids
# of its versions, and with the contents that the ballot leaves as they are;
# w is the facts that a work could act on, with the ballot, if known
def Known.cast.plain(
  +kn: Known(),
  +s: Facts.Plain(),
  +c: Ledgers.Line,
  +k: Nat,
  w: Maybe<&2, List<&2, Types.Fact>>
) -> Known():
  Known.cast.to(
    kn,
    c,
    Known.join(
      Known.voted(kn, c),
      Known.spared(Known.safe(c, Known.find(kn, c), Known.find(kn, Known.root(c)), k), kn)
    ),
    Known.next.of(w, s, c, k, Known.find(kn, c), Known.over(c, Known.find(kn, Known.root(c))))
  )

# what a run leaves of a line: its state, the era and the rule of its next
# version, and the ids of its versions
type Run is Data:
  Run{state: Lines.State, era: Nat, rule: Maybe<&2, Lines.Rule>, ids: Ids}

# the rule at the era m of the branch c, with the versions r of its store:
# the rule u before, when the era is as before (same)
def Run.rule(
  same: Bool,
  r: List<&2, Types.Entry>,
  c: Ledgers.Line,
  m: Nat,
  u: Maybe<&2, Lines.Rule>
) -> Maybe<&2, Lines.Rule>:
  match same:
    case True{}:
      u
    case False{}:
      Lines.Rule.at(r, c, m)

# the run of the branch c after the slot k decided the pick pk: a new
# version, unless the id of pk already made one (dup)
def Run.put(
  dup: Bool,
  r: List<&2, Types.Entry>,
  c: Ledgers.Line,
  vs: List<&2, Types.Entry>,
  +k: Nat,
  +m: Nat,
  u: Maybe<&2, Lines.Rule>,
  +x: Ids,
  +pk: Types.Pick
) -> Run:
  match dup:
    case True{}:
      Run{Lines.State{vs, 1n+k}, m, u, x}
    case False{}:
      +m2 = Nat.max(Lines.Entry.era(Types.Entry{pk, k}), m)
      Run{
        Lines.State{List.append(&2, Types.Entry, vs, [Types.Entry{pk, k}]), 1n+k},
        m2,
        Run.rule(Nat.is_eq(m2, m), r, c, m2, u),
        Ids.put(x, Types.Entry{pk, k})
      }

# the run after the next slot of the run q of the branch c, once its decided
# pick p is known
def Run.step.of(
  r: List<&2, Types.Entry>,
  c: Ledgers.Line,
  q: Run,
  p: Maybe<&2, Types.Pick>
) -> Maybe<&2, Run>:
  match q p:
    case Run{st, m, u, x} None{}:
      None{}
    case Run{Lines.State{vs, k}, m, u, +x} Some{+pk}:
      Some{Run.put(Ids.has(x, Lines.Pick.id(pk)), r, c, vs, k, m, u, x, pk)}

# the nodes that decide the next slot of the run q, if its rule is known
def Run.nodes(q: Run) -> Maybe<&2, List<&2, String>>:
  match q:
    case Run{st, m, None{}, x}:
      None{}
    case Run{st, m, Some{u}, x}:
      Some{Lines.Rule.nodes(u)}

# the next slot of the run q
def Run.slot(q: Run) -> Nat:
  match q:
    case Run{st, m, u, x}:
      Lines.State.slot(st)

# the run after the next slot of the run q of the branch c, read from the
# facts fs, once the nodes ns that decide the slot are known
def Run.step.at(
  fs: List<&2, Types.Fact>,
  r: List<&2, Types.Entry>,
  +c: Ledgers.Line,
  +q: Run,
  ns: Maybe<&2, List<&2, String>>
) -> Maybe<&2, Run>:
  match ns:
    case None{}:
      None{}
    case Some{ds}:
      Run.step.of(r, c, q, Lines.Votes.decided.in(fs, c, Run.slot(q), ds))

# the run after the next slot of the run q of the branch c, with the
# versions r of its store, read from the facts fs
def Run.step(
  fs: List<&2, Types.Fact>,
  r: List<&2, Types.Entry>,
  +c: Ledgers.Line,
  +q: Run
) -> Maybe<&2, Run>:
  Run.step.at(fs, r, c, q, Run.nodes(q))

# the run of the branch c after each decided slot from q on, read from the
# facts fs, at most fuel of them; m is the run after the next slot of q, if
# it is decided
def Run.go(
  fuel: Nat,
  +fs: List<&2, Types.Fact>,
  +r: List<&2, Types.Entry>,
  +c: Ledgers.Line,
  q: Run,
  m: Maybe<&2, Run>
) -> Run:
  match fuel m:
    case 0n _:
      q
    case 1n+f None{}:
      q
    case 1n+f Some{+q2}:
      Run.go(f, fs, r, c, q2, Run.step(fs, r, c, q2))

# the run of the branch c from q on, read from the facts fs: as Known.go.in
# runs it
def Run.from(
  +fs: List<&2, Types.Fact>,
  +r: List<&2, Types.Entry>,
  +c: Ledgers.Line,
  +q: Run
) -> Run:
  Run.go(1n+Lines.Line.bound(fs, c), fs, r, c, q, Run.step(fs, r, c, q))

# the run that a ballot for the slot k of the line c continues, read from
# the facts w, when the table holds all that it reads: c is a branch, k is
# the next slot of its state m, ms is the state of its store, and n, u and x
# are the era and the rule of its next version and the ids of its versions
def Known.quick.of(
  w: Maybe<&2, List<&2, Types.Fact>>,
  c: Ledgers.Line,
  k: Nat,
  m: Maybe<&2, Lines.State>,
  ms: Maybe<&2, Lines.State>,
  n: Maybe<&2, Nat>,
  u: Maybe<&2, Lines.Rule>,
  x: Maybe<&2, Ids>
) -> Maybe<&2, Run>:
  match w c m ms n u x:
    case Some{
      +fs
    } Ledgers.Line{
      +h,
      Some{+b}
    } Some{+st} Some{Lines.State{+r, j}} Some{+era} Some{+rule} Some{+ids}:
      Shared.Maybe.when(
        Run,
        Nat.is_eq(Lines.State.slot(st), k),
        z => Some{Run.from(fs, r, Ledgers.Line{h, Some{b}}, Run{st, era, Some{rule}, ids})}
      )
    case _ _ _ _ _ _ _:
      None{}

# the run that a ballot for the slot k of the line c continues, read from
# the facts w, when the table kn holds all that it reads
def Known.quick(
  +kn: Known(),
  +c: Ledgers.Line,
  k: Nat,
  w: Maybe<&2, List<&2, Types.Fact>>
) -> Maybe<&2, Run>:
  Known.quick.of(
    w,
    c,
    k,
    Known.find(kn, c),
    Known.find(kn, Known.root(c)),
    Known.era(kn, c),
    Known.ruled(kn, c),
    Known.ids(kn, c)
  )

# the table rest with what the run q leaves of the line c
def Known.ran(rest: Known(), +c: Ledgers.Line, q: Run) -> Known():
  match q:
    case Run{st, m, u, x}:
      Known.rule.put(Known.add(Made{c, x}, Known.add(Kept{c, st}, rest)), c, m, u)

# the table kn after a ballot for the slot k of the line c, where s is the
# facts with the ballot, once the run q that the ballot continues is known,
# if the table holds all that the run reads: with what the run leaves of c;
# else as Known.cast.plain gives it
def Known.cast.as(
  q: Maybe<&2, Run>,
  +kn: Known(),
  +s: Facts.Plain(),
  +c: Ledgers.Line,
  +k: Nat,
  w: Maybe<&2, List<&2, Types.Fact>>
) -> Known():
  match q:
    case None{}:
      Known.cast.plain(kn, s, c, k, w)
    case Some{run}:
      Known.ran(
        Known.join(
          Known.voted(kn, c),
          Known.spared(Known.safe(c, Known.find(kn, c), Known.find(kn, Known.root(c)), k), kn)
        ),
        c,
        run
      )

# the table kn after a ballot for the slot k of the line c, where s is the
# facts with the ballot: without the states that the ballot may change, with
# the state of c continued from the state that kn holds for it, with the
# rule of its next version and the ids of its versions, and with the
# contents that the ballot leaves as they are; w is the facts that a work
# could act on, with the ballot, if known
def Known.cast(
  +kn: Known(),
  +s: Facts.Plain(),
  +c: Ledgers.Line,
  +k: Nat,
  +w: Maybe<&2, List<&2, Types.Fact>>
) -> Known():
  Known.cast.as(Known.quick(kn, c, k, w), kn, s, c, k, w)
