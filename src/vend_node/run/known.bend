import Base
import ../../shared/shared/ledger.bend as Ledgers
import ../../shared/shared/shared/shared/crit.bend as Crits
import ../../shared/shared/shared/shared/hash.bend as Hashes
import ../../shared/shared/shared/shared/shared.bend as Shared
import ../codes.bend as Coded
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

# what a node keeps: a line and its state, or a version of a line and its
# content, which a read with the fuel depth gives, or a line and the rule of
# its next version, or a line and the ids of its versions
type Kept is Data:
  Kept{line: Ledgers.Line, state: Lines.State}
  Held{line: Ledgers.Line, version: Nat, depth: Nat, files: Files.Files()}
  Ruled{line: Ledgers.Line, rule: Lines.Rule}
  Made{line: Ledgers.Line, ids: Crits.Crit<List<&2, Ledgers.Id>>}

# what a node keeps: the newest entry of a line first; the states before the
# contents
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
    case Con{Held{c2, k, d, x}, rest}:
      Known.find(rest, c)
    case Con{Ruled{c2, u}, rest}:
      Known.find(rest, c)
    case Con{Made{c2, x}, rest}:
      Known.find(rest, c)

# the rule of the next version of the line c that the table kn holds, if any
def Known.ruled(kn: Known(), +c: Ledgers.Line) -> Maybe<&2, Lines.Rule>:
  match kn:
    case Nil{}:
      None{}
    case Con{Kept{c2, st}, rest}:
      Known.ruled(rest, c)
    case Con{Held{c2, k, d, x}, rest}:
      Known.ruled(rest, c)
    case Con{Ruled{c2, u}, rest}:
      Shared.Bool.when(
        Maybe<&2, Lines.Rule>,
        Ledgers.Line.is_eq(c2, c),
        u2 => Some{u},
        u2 => Known.ruled(rest, c)
      )
    case Con{Made{c2, x}, rest}:
      Known.ruled(rest, c)

# the content of version k of the line c that the table kn holds, with the
# fuel that reads it
def Known.held(kn: Known(), +c: Ledgers.Line, +k: Nat) -> Maybe<&2, Kept>:
  match kn:
    case Nil{}:
      None{}
    case Con{Kept{c2, st}, rest}:
      Known.held(rest, c, k)
    case Con{Held{+c2, +k2, +d, +x}, rest}:
      Shared.Bool.when(
        Maybe<&2, Kept>,
        List.all.if(u2 => Ledgers.Line.is_eq(c2, c), Nat.is_eq(k2, k)),
        u => Some{Held{c2, k2, d, x}},
        u => Known.held(rest, c, k)
      )
    case Con{Ruled{c2, u}, rest}:
      Known.held(rest, c, k)
    case Con{Made{c2, y}, rest}:
      Known.held(rest, c, k)

# the files of the entry m, if it is a content that a read with the fuel f
# gives
def Known.files.of(m: Maybe<&2, Kept>, f: Nat) -> Maybe<&2, Files.Files()>:
  match m:
    case Some{Held{c, k, d, x}}:
      Shared.Maybe.when(Files.Files(), Nat.is_le(d, f), u => Some{x})
    case _:
      None{}

# the content of version k of the line c that the table kn holds, if a read
# with the fuel f gives it
def Known.files(kn: Known(), +c: Ledgers.Line, +k: Nat, f: Nat) -> Maybe<&2, Files.Files()>:
  Known.files.of(Known.held(kn, c, k), f)

# the fuel of the content m, if any
def Known.depth.of(m: Maybe<&2, Kept>) -> Maybe<&2, Nat>:
  match m:
    case Some{Held{c, k, d, x}}:
      Some{d}
    case _:
      None{}

# the fuel that reads the content of version k of the line c that the table
# kn holds
def Known.depth(kn: Known(), +c: Ledgers.Line, +k: Nat) -> Maybe<&2, Nat>:
  Known.depth.of(Known.held(kn, c, k))

# the table kn with the entry e, a content: after the states, before the
# other contents
def Known.hold(kn: Known(), e: Kept) -> Known():
  match kn:
    case Nil{}:
      [e]
    case Con{Kept{c, st}, rest}:
      Kept{c, st} <> Known.hold(rest, e)
    case Con{Ruled{c, u}, rest}:
      Ruled{c, u} <> Known.hold(rest, e)
    case Con{Made{c, x}, rest}:
      Made{c, x} <> Known.hold(rest, e)
    case Con{Held{c, k, d, x}, rest}:
      e <> Held{c, k, d, x} <> rest

# the contents that the table kn holds
def Known.contents(kn: Known()) -> Known():
  match kn:
    case Nil{}:
      []
    case Con{Kept{c, st}, rest}:
      Known.contents(rest)
    case Con{Held{c, k, d, x}, rest}:
      Held{c, k, d, x} <> Known.contents(rest)
    case Con{Ruled{c, u}, rest}:
      Known.contents(rest)
    case Con{Made{c, x}, rest}:
      Known.contents(rest)

# Known ids
# ---------

# the ids of the requests that made the versions of a line, as a set: a map
# from a short key (Id.key) to the ids of that key
def Ids() -> Data:
  Crits.Crit<List<&2, Ledgers.Id>>

# the number h, mixed with the characters of t
def Id.mix(t: String, h: U32) -> U32:
  match t:
    case SNil{}:
      h
    case SCon{Chr{x}, rest}:
      Id.mix(rest, ((h * 31) + x: U32))

# a short key of the id i: one word; ids of one key share an entry of a set
def Id.key(i: Ledgers.Id) -> List<&2, U32>:
  match i:
    case Ledgers.Id{w, q}:
      [Id.mix(q, Id.mix(w, 0))]

# the ids new, then the ids old
def Ids.join(old: List<&2, Ledgers.Id>, new: List<&2, Ledgers.Id>) -> List<&2, Ledgers.Id>:
  List.append(&2, Ledgers.Id, new, old)

# the id i is among the ids b
def Ids.holds(b: List<&2, Ledgers.Id>, +i: Ledgers.Id) -> Bool:
  match b:
    case Nil{}:
      False{}
    case Con{j, rest}:
      List.any.if(u => Ids.holds(rest, i), Ledgers.Id.is_eq(j, i))

# the id i is among the ids m, if any
def Ids.has.of(m: Maybe<&2, List<&2, Ledgers.Id>>, i: Ledgers.Id) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{b}:
      Ids.holds(b, i)

# the set x holds the id i
def Ids.has(x: Crits.Crit<List<&2, Ledgers.Id>>, +i: Ledgers.Id) -> Bool:
  Ids.has.of(Crits.Crit.get(List<&2, Ledgers.Id>, x, Id.key(i)), i)

# the set acc with the id i
def Ids.put(+acc: Ids(), +i: Ledgers.Id) -> Ids():
  Crits.Crit.upsert(~List<&2, Ledgers.Id>, ~Ids.join, acc, Id.key(i), [i])

# the set acc with the id of each of the versions vs
def Ids.go(vs: List<&2, Types.Entry>, acc: Ids()) -> Ids():
  match vs:
    case Nil{}:
      acc
    case Con{e, rest}:
      Ids.go(rest, Ids.put(acc, Lines.Entry.id(e)))

# the ids of the versions vs
def Ids.of(vs: List<&2, Types.Entry>) -> Ids():
  Ids.go(vs, Crits.Crit.new(List<&2, Ledgers.Id>))

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
def Known.ids(kn: Known(), +c: Ledgers.Line) -> Maybe<&2, Ids()>:
  match kn:
    case Nil{}:
      None{}
    case Con{Kept{c2, st}, rest}:
      Known.ids(rest, c)
    case Con{Held{c2, k, d, x}, rest}:
      Known.ids(rest, c)
    case Con{Ruled{c2, u}, rest}:
      Known.ids(rest, c)
    case Con{Made{c2, x}, rest}:
      Shared.Bool.when(
        Maybe<&2, Ids()>,
        Ledgers.Line.is_eq(c2, c),
        u2 => Some{x},
        u2 => Known.ids(rest, c)
      )

# the request of the id i made one of the versions vs: read from their ids
# m, if known
def Made.in(m: Maybe<&2, Ids()>, vs: List<&2, Types.Entry>, i: Ledgers.Id) -> Bool:
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

# the table kn with the rule m, if any, of the next version of the line c
def Known.rule.put(kn: Known(), c: Ledgers.Line, m: Maybe<&2, Lines.Rule>) -> Known():
  match m:
    case None{}:
      kn
    case Some{u}:
      Ruled{c, u} <> kn

# the table kn with the rule of the next version of the line c, after the
# state that kn holds for c, unless the table holds the rule (old)
def Known.rule.learn.if(old: Bool, +kn: Known(), +s: Facts.Plain(), +c: Ledgers.Line) -> Known():
  match old:
    case True{}:
      kn
    case False{}:
      Known.rule.put(kn, c, Known.rule.next(kn, s, c, Known.find(kn, c)))

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
      Made{c, Ids.of(vs)} <> kn

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
  Known.ids.learn.if(Maybe.is_some(&2, Ids(), Known.ids(kn, c)), kn, c)

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

# the entry e before rest, when it is a state or a rule that a vote for the
# line c cannot change
def Known.voted.put(c: Ledgers.Line, e: Kept, rest: Known()) -> Known():
  match e:
    case Kept{+c2, +st}:
      List.filter.put(Kept, Kept{c2, st}, rest, Bool.not(Known.hit(c, c2)))
    case Held{c2, k, d, x}:
      rest
    case Ruled{+c2, +u}:
      List.filter.put(Kept, Ruled{c2, u}, rest, Bool.not(Known.hit(c, c2)))
    case Made{+c2, +y}:
      List.filter.put(Kept, Made{c2, y}, rest, Bool.not(Known.hit(c, c2)))

# the table kn after a vote for a slot of the line c: without the states and
# the rules that the vote may change, and without the contents
def Known.voted(kn: Known(), +c: Ledgers.Line) -> Known():
  match kn:
    case Nil{}:
      []
    case Con{+e, rest}:
      Known.voted.put(c, e, Known.voted(rest, c))

# Same states
# -----------

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

# the rules a and b are the same
def Rule.same(a: Lines.Rule, b: Lines.Rule) -> Bool:
  match a b:
    case Lines.Rule{g1, n1} Lines.Rule{g2, n2}:
      Bool.and(
        Shared.Maybe.is_eq(~String, ~String.eq, g1, g2),
        Shared.List.is_eq(~String, ~String.eq, n1, n2)
      )

# m is the rule u
def Rule.fits(m: Maybe<&2, Lines.Rule>, u: Lines.Rule) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      Rule.same(x, u)

# m is the state st
def State.fits(m: Maybe<&2, Lines.State>, st: Lines.State) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      State.same(x, st)

# the ids a and b are the same
def Bucket.same(a: List<&2, Ledgers.Id>, b: List<&2, Ledgers.Id>) -> Bool:
  Shared.List.is_eq(~Ledgers.Id, ~Ledgers.Id.is_eq, a, b)

# the sets a and b are the same: key by key, in the same shape
def Ids.same(a: Ids(), b: Ids()) -> Bool:
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
            Shared.Maybe.is_eq(~List<&2, Ledgers.Id>, ~Bucket.same, e1, e2),
            Bool.and(Ids.same(z1, z2), Ids.same(o1, o2))
          )
        )
      )
    case _ _:
      False{}

# m is a state whose versions have the ids x
def Made.fits(m: Maybe<&2, Lines.State>, x: Ids()) -> Bool:
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

# the contents of the table kn, when a ballot leaves them as they are (safe);
# else none
def Known.spared(safe: Bool, kn: Known()) -> Known():
  match safe:
    case True{}:
      Known.contents(kn)
    case False{}:
      []

# the ids of the versions of the state new of a line, from the ids of the
# versions of the state old that it continues, if the three are known: with
# the ids of the versions that old has not
def Made.next(
  new: Maybe<&2, Lines.State>,
  old: Maybe<&2, Lines.State>,
  ids: Maybe<&2, Ids()>
) -> Maybe<&2, Ids()>:
  match new old ids:
    case Some{Lines.State{vs2, k2}} Some{Lines.State{vs, k}} Some{x}:
      Some{Ids.go(Entries.past(vs, vs2), x)}
    case _ _ _:
      None{}

# the table kn with the ids m, if any, of the versions of the line c
def Known.made.put(kn: Known(), c: Ledgers.Line, m: Maybe<&2, Ids()>) -> Known():
  match m:
    case None{}:
      kn
    case Some{x}:
      Made{c, x} <> kn

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
# of its versions, and with the contents that the ballot leaves as they are
def Known.cast(+kn: Known(), +s: Facts.Plain(), +c: Ledgers.Line, +k: Nat) -> Known():
  Known.cast.to(
    kn,
    c,
    List.append(
      &2,
      Kept,
      Known.voted(kn, c),
      Known.spared(Known.safe(c, Known.find(kn, c), Known.find(kn, Known.root(c)), k), kn)
    ),
    Known.next.of(s, c, k, Known.find(kn, c), Known.over(c, Known.find(kn, Known.root(c))))
  )
