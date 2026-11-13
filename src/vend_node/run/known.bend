import Base
import ../../shared/shared/ledger.bend as Ledgers
import ../../shared/shared/shared/shared/hash.bend as Hashes
import ../../shared/shared/shared/shared/shared.bend as Shared
import ../codes.bend as Coded
import ./facts.bend as Facts
import ./lines.bend as Lines
import ../types.bend as Types

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

# a line and its state
type Kept is Data:
  Kept{line: Ledgers.Line, state: Lines.State}

# the states that a node keeps: the newest entry of a line first
def Known() -> Data:
  List<&2, Kept>

# the table that holds no state
def Known.none() -> Known():
  []

# the state that the table kn holds for the line c, if any
def Known.find(kn: Known(), +c: Ledgers.Line) -> Maybe<&2, Lines.State>:
  match kn:
    case Nil{}:
      None{}
    case Con{Kept{c2, st}, rest}:
      Shared.Bool.when(
        Maybe<&2, Lines.State>,
        Ledgers.Line.is_eq(c2, c),
        u => Some{st},
        u => Known.find(rest, c)
      )

# the store of the line c
def Known.root(c: Ledgers.Line) -> Ledgers.Line:
  Ledgers.Line{Lines.Line.root(c), None{}}

# the state of the line c, when the state of its store is R and k
def Known.fresh.at(
  +s: Facts.Plain(),
  c: Ledgers.Line,
  R: List<&2, Types.Entry>,
  k: Nat
) -> Maybe<&2, Lines.State>:
  match c:
    case Ledgers.Line{h, None{}}:
      Some{Lines.State{R, k}}
    case Ledgers.Line{h, Some{b}}:
      Lines.Branch.state(s, Ledgers.Line{h, Some{b}}, Some{R})

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

# the rule after the versions vs of the line c, with the versions R of its
# store
def Known.rule.at(
  c: Ledgers.Line,
  +vs: List<&2, Types.Entry>,
  R: List<&2, Types.Entry>
) -> Maybe<&2, Lines.Rule>:
  match c:
    case Ledgers.Line{h, None{}}:
      Lines.Line.rule(None{}, Ledgers.Line{h, None{}}, vs)
    case Ledgers.Line{h, Some{b}}:
      Lines.Line.rule(Some{R}, Ledgers.Line{h, Some{b}}, vs)

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

# What a node learns
# ------------------

# the table kn with the state m, if any, of the line c
def Known.put(kn: Known(), c: Ledgers.Line, m: Maybe<&2, Lines.State>) -> Known():
  match m:
    case None{}:
      kn
    case Some{st}:
      Kept{c, st} <> kn

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

# the table kn with the states of the line c and of its store in the facts s
def Known.learn(kn: Known(), +s: Facts.Plain(), +c: Ledgers.Line) -> Known():
  Known.learn.one(Known.learn.one(kn, s, Known.root(c)), s, c)

# What a vote forgets
# -------------------

# a vote for a slot of the line c may change the state of the line c2: it is
# c, or c is its store
def Known.hit(c: Ledgers.Line, +c2: Ledgers.Line) -> Bool:
  +c = c
  Bool.or(Ledgers.Line.is_eq(c2, c), Ledgers.Line.is_eq(Known.root(c2), c))

# the entry e before rest, unless a vote for the line c may change it
def Known.voted.put(c: Ledgers.Line, +e: Kept, rest: Known()) -> Known():
  match e:
    case Kept{c2, st}:
      List.filter.put(Kept, e, rest, Bool.not(Known.hit(c, c2)))

# the table kn after a vote for a slot of the line c: without the states that
# the vote may change
def Known.voted(kn: Known(), +c: Ledgers.Line) -> Known():
  match kn:
    case Nil{}:
      []
    case Con{+e, rest}:
      Known.voted.put(c, e, Known.voted(rest, c))

# A table that is right
# ---------------------

# the entries a and b are the same
def Entry.same(a: Types.Entry, b: Types.Entry) -> Bool:
  match a b:
    case Types.Entry{p1, k1} Types.Entry{p2, k2}:
      Bool.and(Coded.Pick.is_eq(p1, p2), Nat.is_eq(k1, k2))

# the versions xs and ys are the same
def Entries.same(xs: List<&2, Types.Entry>, ys: List<&2, Types.Entry>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{x, xr} Con{y, yr}:
      Bool.and(Entry.same(x, y), Entries.same(xr, yr))
    case _ _:
      False{}

# the states a and b are the same
def State.same(a: Lines.State, b: Lines.State) -> Bool:
  match a b:
    case Lines.State{v1, k1} Lines.State{v2, k2}:
      Bool.and(Entries.same(v1, v2), Nat.is_eq(k1, k2))

# m is the state st
def State.fits(m: Maybe<&2, Lines.State>, st: Lines.State) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      State.same(x, st)

# the entry e is right: its state is the state that the facts s give its line
def Kept.ok(+s: Facts.Plain(), e: Kept) -> Bool:
  match e:
    case Kept{c, st}:
      State.fits(Lines.Line.state(s, c), st)

# the table kn is right for the facts s: each state that it holds is the
# state that s gives the line
def Known.ok(kn: Known(), +s: Facts.Plain()) -> Bool:
  match kn:
    case Nil{}:
      True{}
    case Con{e, rest}:
      Bool.and(Kept.ok(s, e), Known.ok(rest, s))

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

# the state of the line c in the facts s, after a ballot for its slot k:
# the run from its known state m, when k is the next slot of m and the
# versions r that the run reads are known
def Known.next.of(
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
        u => Some{Known.go.at(s, c, st, rr)}
      )
    case _ _:
      None{}

# the table kn after a ballot for the slot k of the line c, where s is the
# facts with the ballot: without the states that the ballot may change, and
# with the state of c continued from the state that kn holds for it
def Known.cast(+kn: Known(), +s: Facts.Plain(), +c: Ledgers.Line, k: Nat) -> Known():
  Known.put(
    Known.voted(kn, c),
    c,
    Known.next.of(s, c, k, Known.find(kn, c), Known.over(c, Known.find(kn, Known.root(c))))
  )
