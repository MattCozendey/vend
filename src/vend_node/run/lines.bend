import Base
import ../../shared/shared/ledger.bend as Ledgers
import ../../shared/shared/shared/shared/hash.bend as Hashes
import ../../shared/shared/shared/shared/shared.bend as Shared
import ../codes.bend as Coded
import ./facts.bend as Facts
import ./rounds.bend as Rounds
import ../groups.bend as Groups
import ../shared/lists.bend as Lists
import ../spec.bend as Spec
import ../types.bend as Types

# Lines
# -----
# The versions of a line are read from the facts. Version 0 needs no vote: of
# a store, it is the request that started it; of a branch, the first request
# of the store that owns it. Each later version is made by a slot of the line:
# the pick that more than half of the nodes that decide the slot voted for,
# when no other pick has as much. A slot whose request already made a version
# of the line makes none, so a request counts once. Owners are trusted only
# to cast no two votes for one slot: what a decided request does is read by
# every node, from the versions.

# Entries
# -------

# the ask of the entry e
def Entry.ask(e: Types.Entry) -> Types.Ask:
  match e:
    case Types.Entry{Types.Pick{a, pins}, k}:
      a

# the pins of the entry e
def Entry.pins(e: Types.Entry) -> Types.Pins:
  match e:
    case Types.Entry{Types.Pick{a, pins}, k}:
      pins

# the slot that decided the entry e
def Entry.slot(e: Types.Entry) -> Nat:
  match e:
    case Types.Entry{pk, k}:
      k

# the id of the ask a
def Ask.id(a: Types.Ask) -> Ledgers.Id:
  match a:
    case Types.Ask{i, k, r}:
      i

# the request of the ask a
def Ask.request(a: Types.Ask) -> Spec.Request:
  match a:
    case Types.Ask{i, k, r}:
      r

# the id of the entry e
def Entry.id(e: Types.Entry) -> Ledgers.Id:
  Ask.id(Entry.ask(e))

# the era that the entry e pins
def Entry.era(e: Types.Entry) -> Nat:
  match e:
    case Types.Entry{Types.Pick{a, Types.Pins{era, from, base, ours, theirs}}, k}:
      era

# the entry e is of the id i
def Entry.is_of(i: Ledgers.Id, e: Types.Entry) -> Bool:
  Ledgers.Id.is_eq(Entry.id(e), i)

# the pins of a request that takes nothing from another line, with the era m
def Pins.plain(m: Nat) -> Types.Pins:
  Types.Pins{m, 0n, None{}, [], []}

# version 0 of a line: the request r of the id i, with the era m
def Entry.first(i: Ledgers.Id, r: Spec.Request, m: Nat) -> Types.Entry:
  Types.Entry{Types.Pick{Types.Ask{i, 0n, r}, Pins.plain(m)}, 0n}

# Votes
# -----

# the pick that the nodes ds decided for the slot k of the line c, in the
# facts s
def Votes.decided(
  +s: Facts.Plain(),
  c: Ledgers.Line,
  +k: Nat,
  +ds: List<&2, String>
) -> Maybe<&2, Types.Pick>:
  Rounds.Slot.decided(Rounds.Slot.ballots(Facts.Facts.list(s), c, k), ds, k)

# Who decides
# -----------

# the store of the line c
def Line.root(c: Ledgers.Line) -> Hashes.Hash:
  match c:
    case Ledgers.Line{r, b}:
      r

# the line c is a store itself
def Line.is_root(c: Ledgers.Line) -> Bool:
  match c:
    case Ledgers.Line{r, None{}}:
      True{}
    case Ledgers.Line{r, Some{b}}:
      False{}

# the era of the next version of the line c, after the versions vs: for a
# store, its newest version; for a branch, the greatest era that a version
# pinned, so the era never goes back
def Line.era(c: Ledgers.Line, vs: List<&2, Types.Entry>) -> Nat:
  match c:
    case Ledgers.Line{r, None{}}:
      Nat.sub(List.length(&2, Types.Entry, vs), 1n)
    case Ledgers.Line{r, Some{b}}:
      Lists.List.peak(~Types.Entry, ~Entry.era, vs)

# the owners that the request r starts a store with
def Request.owners(r: Spec.Request) -> List<&2, String>:
  match r:
    case Spec.Request.Start{os}:
      os
    case _:
      []

# the owners that the store of the versions r started with
def Store.owners(r: List<&2, Types.Entry>) -> List<&2, String>:
  match r:
    case Nil{}:
      []
    case Con{e, rest}:
      Request.owners(Ask.request(Entry.ask(e)))

# who decides a version: the owner group of the line, if the store named one,
# and its nodes
type Rule is Data:
  Rule{owner: Maybe<&2, String>, nodes: List<&2, String>}

# the nodes of the rule u
def Rule.nodes(u: Rule) -> List<&2, String>:
  match u:
    case Rule{g, ns}:
      ns

# the rule of the owner group g, if any, of the line c, at the era m of the
# versions r of its store: the nodes of g; or, while a store named no owner
# group of its own, the owners that it started with
def Rule.of(
  +r: List<&2, Types.Entry>,
  +c: Ledgers.Line,
  +m: Nat,
  g: Maybe<&2, String>
) -> Maybe<&2, Rule>:
  match g:
    case Some{+name}:
      Maybe.map(
        &2,
        List<&2, String>,
        Rule,
        ns => Rule{Some{name}, ns},
        Groups.Groups.nodes(r, Line.root(c), name, m)
      )
    case None{}:
      Shared.Maybe.when(Rule, Line.is_root(c), u => Some{Rule{None{}, Store.owners(r)}})

# the rule of the version of the line c that the era m decides, with the
# versions r of its store (nothing while r does not reach m)
def Rule.at(+r: List<&2, Types.Entry>, +c: Ledgers.Line, +m: Nat) -> Maybe<&2, Rule>:
  Shared.Maybe.when(
    Rule,
    Nat.is_lt(m, List.length(&2, Types.Entry, r)),
    u => Rule.of(r, c, m, Groups.Groups.owner(r, c, m))
  )

# the versions of the store of a line whose versions are vs: rs, or vs itself
# when the line is the store (rs is none)
def Line.store(
  rs: Maybe<&2, List<&2, Types.Entry>>,
  vs: List<&2, Types.Entry>
) -> List<&2, Types.Entry>:
  match rs:
    case None{}:
      vs
    case Some{r}:
      r

# the rule of the next version of the line c, after its versions vs
def Line.rule(
  r: Maybe<&2, List<&2, Types.Entry>>,
  +c: Ledgers.Line,
  +vs: List<&2, Types.Entry>
) -> Maybe<&2, Rule>:
  Rule.at(Line.store(r, vs), c, Line.era(c, vs))

# Slots
# -----

# how far a line is read: its versions, oldest first, and its next slot
type State is Data:
  State{versions: List<&2, Types.Entry>, slot: Nat}

# the versions of the state st
def State.versions(st: State) -> List<&2, Types.Entry>:
  match st:
    case State{vs, k}:
      vs

# the next slot of the state st
def State.slot(st: State) -> Nat:
  match st:
    case State{vs, k}:
      k

# the versions vs after the slot k decided the pick pk: a new version, unless
# the id of pk already made one (dup)
def State.put.if(vs: List<&2, Types.Entry>, +k: Nat, pk: Types.Pick, dup: Bool) -> State:
  match dup:
    case True{}:
      State{vs, 1n+k}
    case False{}:
      State{List.append(&2, Types.Entry, vs, [Types.Entry{pk, k}]), 1n+k}

# the pick pk is of the id i
def Pick.id(pk: Types.Pick) -> Ledgers.Id:
  match pk:
    case Types.Pick{a, pins}:
      Ask.id(a)

# the versions vs after the slot k decided the pick pk
def State.put(+vs: List<&2, Types.Entry>, +k: Nat, +pk: Types.Pick) -> State:
  State.put.if(
    vs,
    k,
    pk,
    Shared.List.some(~Types.Entry, ~Ledgers.Id, ~Entry.is_of, vs, Pick.id(pk))
  )

# the state after the next slot of st, once its decided pick m is known
def Line.step.of(st: State, m: Maybe<&2, Types.Pick>) -> Maybe<&2, State>:
  match st m:
    case State{vs, k} None{}:
      None{}
    case State{vs, k} Some{pk}:
      Some{State.put(vs, k, pk)}

# the state after the next slot of st, once the rule u of the slot is known
def Line.step.at(
  +s: Facts.Plain(),
  +c: Ledgers.Line,
  +st: State,
  u: Maybe<&2, Rule>
) -> Maybe<&2, State>:
  match u:
    case None{}:
      None{}
    case Some{rule}:
      Line.step.of(st, Votes.decided(s, c, State.slot(st), Rule.nodes(rule)))

# the state of the line c after the next slot of st (nothing while the slot is
# not decided, or who decides it is not known)
def Line.step(
  +s: Facts.Plain(),
  r: Maybe<&2, List<&2, Types.Entry>>,
  +c: Ledgers.Line,
  +st: State
) -> Maybe<&2, State>:
  Line.step.at(s, c, st, Line.rule(r, c, State.versions(st)))

# the state of the line c after each decided slot from st on, at most fuel of
# them; m is the state after the next slot of st, if it is decided
def Line.run(
  fuel: Nat,
  +s: Facts.Plain(),
  +r: Maybe<&2, List<&2, Types.Entry>>,
  +c: Ledgers.Line,
  st: State,
  m: Maybe<&2, State>
) -> State:
  match fuel m:
    case 0n _:
      st
    case 1n+f None{}:
      st
    case 1n+f Some{+st2}:
      Line.run(f, s, r, c, st2, Line.step(s, r, c, st2))

# one more than the slot k, when it is a slot of the line (hit)
def Line.bound.at(hit: Bool, k: Nat) -> Nat:
  match hit:
    case True{}:
      1n+k
    case False{}:
      0n

# a bound of the slots of the line c that the facts fs decide: one more than
# the greatest slot of c that a vote among fs is for
def Line.bound(fs: List<&2, Types.Fact>, +c: Ledgers.Line) -> Nat:
  match fs:
    case Nil{}:
      1n
    case Con{Types.Fact.Ask{a}, rest}:
      Line.bound(rest, c)
    case Con{Types.Fact.Vote{v, Types.Step.Broken{}, pk}, rest}:
      Line.bound(rest, c)
    case Con{Types.Fact.Vote{v, Types.Step.At{c2, k, t}, pk}, rest}:
      Nat.max(Line.bound.at(Ledgers.Line.is_eq(c2, c), k), Line.bound(rest, c))

# Version 0
# ---------

# the asks among fs that start the store of the root h
def Starts.of(fs: List<&2, Types.Fact>, +h: Hashes.Hash) -> List<&2, Types.Ask>:
  match fs:
    case Nil{}:
      []
    case Con{Types.Fact.Vote{v, st, pk}, rest}:
      Starts.of(rest, h)
    case Con{Types.Fact.Ask{+a}, rest}:
      List.filter.put(Types.Ask, a, Starts.of(rest, h), Facts.Ask.starts(h, a))

# version 0 of a store, from the ask m that starts it, if any
def Store.first.of(m: Maybe<&2, Types.Ask>) -> Maybe<&2, Types.Entry>:
  match m:
    case None{}:
      None{}
    case Some{Types.Ask{i, k, r}}:
      Some{Entry.first(i, r, 0n)}

# the ask b does not stand against the ask a: it is of the same id and
# request, or of a lesser number
def Ask.led(a: Types.Ask, b: Types.Ask) -> Bool:
  +a = a
  +b = b
  Bool.or(Facts.Ask.alike(a, b), Nat.is_lt(Facts.Ask.seq(b), Facts.Ask.seq(a)))

# no ask of all stands against the ask a
def Ask.leads(all: List<&2, Types.Ask>, a: Types.Ask) -> Bool:
  Shared.List.holds(~Types.Ask, ~Types.Ask, ~Ask.led, all, a)

# version 0 of the store of the root h: the request that started it, as the
# ask among fs that no other start of the store stands against gives it
def Store.first(fs: List<&2, Types.Fact>, +h: Hashes.Hash) -> Maybe<&2, Types.Entry>:
  +st = Starts.of(fs, h)
  Store.first.of(Lists.List.pick(~Types.Ask, ~List<&2, Types.Ask>, ~Ask.leads, st, st))

# the request r makes a group the owner of the line c
def Request.owns(c: Ledgers.Line, r: Spec.Request) -> Bool:
  match r:
    case Spec.Request.Own{c2, g}:
      Ledgers.Line.is_eq(c2, c)
    case _:
      False{}

# the entry e makes a group the owner of the line c
def Entry.owns(c: Ledgers.Line, e: Types.Entry) -> Bool:
  Request.owns(c, Ask.request(Entry.ask(e)))

# version 0 of a branch, from the version j of its store that first owned it,
# and that version m, if any
def Branch.first.of(+j: Nat, m: Maybe<&2, Types.Entry>) -> Maybe<&2, Types.Entry>:
  match m:
    case None{}:
      None{}
    case Some{Types.Entry{Types.Pick{Types.Ask{i, k, r}, pins}, slot}}:
      Some{Entry.first(i, r, j)}

# version 0 of a branch, once the version j of its store that first owned it
# is known
def Branch.first.at(+r: List<&2, Types.Entry>, j: Maybe<&2, Nat>) -> Maybe<&2, Types.Entry>:
  match j:
    case None{}:
      None{}
    case Some{+n}:
      Branch.first.of(n, List.get(&2, Types.Entry, r, n))

# version 0 of the branch c: the first request of its store, of the versions
# r, that made a group its owner
def Branch.first(+r: List<&2, Types.Entry>, +c: Ledgers.Line) -> Maybe<&2, Types.Entry>:
  Branch.first.at(r, Lists.List.index(~Types.Entry, ~Ledgers.Line, ~Entry.owns, r, c))

# The versions of a line
# ----------------------

# the state of the line c after each decided slot from st on
def Line.start(
  +s: Facts.Plain(),
  +r: Maybe<&2, List<&2, Types.Entry>>,
  +c: Ledgers.Line,
  +st: State
) -> State:
  Line.run(Line.bound(Facts.Facts.list(s), c), s, r, c, st, Line.step(s, r, c, st))

# the state of a line from its version 0 on, if it has one
def Line.from(
  +s: Facts.Plain(),
  +r: Maybe<&2, List<&2, Types.Entry>>,
  +c: Ledgers.Line,
  m: Maybe<&2, Types.Entry>
) -> Maybe<&2, State>:
  match m:
    case None{}:
      None{}
    case Some{e}:
      Some{Line.start(s, r, c, State{[e], 1n})}

# the state of the store of the root h
def Store.state(+s: Facts.Plain(), +h: Hashes.Hash) -> Maybe<&2, State>:
  Line.from(s, None{}, Ledgers.Line{h, None{}}, Store.first(Facts.Facts.list(s), h))

# the versions of the store of the root h
def Store.versions(+s: Facts.Plain(), +h: Hashes.Hash) -> Maybe<&2, List<&2, Types.Entry>>:
  Maybe.map(&2, State, List<&2, Types.Entry>, State.versions, Store.state(s, h))

# the state of the branch c, once the versions m of its store are known
def Branch.state(
  +s: Facts.Plain(),
  +c: Ledgers.Line,
  m: Maybe<&2, List<&2, Types.Entry>>
) -> Maybe<&2, State>:
  match m:
    case None{}:
      None{}
    case Some{+R}:
      Line.from(s, Some{R}, c, Branch.first(R, c))

# the state of the line c in the facts s (nothing while s does not hold its
# version 0)
def Line.state(+s: Facts.Plain(), +c: Ledgers.Line) -> Maybe<&2, State>:
  match c:
    case Ledgers.Line{+h, None{}}:
      Store.state(s, h)
    case Ledgers.Line{+h, Some{+b}}:
      Branch.state(s, Ledgers.Line{h, Some{b}}, Store.versions(s, h))

# the versions of the line c in the facts s, oldest first
def Line.versions(+s: Facts.Plain(), +c: Ledgers.Line) -> Maybe<&2, List<&2, Types.Entry>>:
  Maybe.map(&2, State, List<&2, Types.Entry>, State.versions, Line.state(s, c))

# version k of the line c, once its versions m are known
def Line.at.of(m: Maybe<&2, List<&2, Types.Entry>>, k: Nat) -> Maybe<&2, Types.Entry>:
  match m:
    case None{}:
      None{}
    case Some{vs}:
      List.get(&2, Types.Entry, vs, k)

# version k of the line c in the facts s
def Line.at(+s: Facts.Plain(), +c: Ledgers.Line, k: Nat) -> Maybe<&2, Types.Entry>:
  Line.at.of(Line.versions(s, c), k)

# The rule of the next version
# ----------------------------

# the rule after the versions vs of the branch c, once the versions m of its
# store are known
def Rule.after.of(
  +c: Ledgers.Line,
  +vs: List<&2, Types.Entry>,
  m: Maybe<&2, List<&2, Types.Entry>>
) -> Maybe<&2, Rule>:
  match m:
    case None{}:
      None{}
    case Some{R}:
      Line.rule(Some{R}, c, vs)

# the rule of the version of the line c that comes after the versions vs
def Rule.after(+s: Facts.Plain(), +c: Ledgers.Line, +vs: List<&2, Types.Entry>) -> Maybe<&2, Rule>:
  match c:
    case Ledgers.Line{+h, None{}}:
      Line.rule(None{}, Ledgers.Line{h, None{}}, vs)
    case Ledgers.Line{+h, Some{+b}}:
      Rule.after.of(Ledgers.Line{h, Some{b}}, vs, Store.versions(s, h))

# the state of the line c after the next slot of st
def Line.next(+s: Facts.Plain(), +c: Ledgers.Line, +st: State) -> Maybe<&2, State>:
  Line.step.at(s, c, st, Rule.after(s, c, State.versions(st)))

# the pick of the entry e
def Entry.pick(e: Types.Entry) -> Types.Pick:
  match e:
    case Types.Entry{pk, k}:
      pk

# the request r opens a line: it starts a store, or names the owner of a line
def Request.opens(r: Spec.Request) -> Bool:
  match r:
    case Spec.Request.Start{os}:
      True{}
    case Spec.Request.Own{c, g}:
      True{}
    case _:
      False{}
