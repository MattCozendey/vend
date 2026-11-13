import Base
import ../shared/shared/ledger.bend as Ledgers
import ../shared/shared/shared/shared/hash.bend as Hashes
import ../shared/shared/shared/shared/shared.bend as Shared
import ./answers.bend as Answers
import ./codes.bend as Coded
import ./content.bend as Contents
import ./facts.bend as Facts
import ./lines.bend as Lines
import ./shared/lists.bend as Lists
import ./spec.bend as Spec
import ./types.bend as Types

# Work
# ----
# What a node does by itself: it casts at most one vote per work, under its
# own name, for the next slot of a line that it decides, and only when it
# holds no vote of its own for that slot. So it never casts two votes for one
# slot. The nodes of a slot take turns: the node whose turn it is proposes the
# request that it took in last; the others vote as it did. So the votes of
# nodes that follow this never split.

# Turns
# -----

# the node whose turn is k steps after y, in the round of x then ns, where r
# are the nodes after y
def Turn.go(k: Nat, +x: String, +ns: List<&2, String>, y: String, r: List<&2, String>) -> String:
  match k r:
    case 0n _:
      y
    case 1n+j Nil{}:
      Turn.go(j, x, ns, x, ns)
    case 1n+j Con{z, r2}:
      Turn.go(j, x, ns, z, r2)

# the node among ns whose turn the slot k is
def Turn.of(ns: List<&2, String>, k: Nat) -> String:
  match ns:
    case Nil{}:
      ""
    case Con{+x, +r}:
      Turn.go(k, x, r, x, r)

# Where a request goes
# --------------------

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

# the line whose versions the request r is for
def Request.line(fs: List<&2, Types.Fact>, r: Spec.Request) -> Maybe<&2, Ledgers.Line>:
  match r:
    case Spec.Request.Start{os}:
      None{}
    case Spec.Request.Write{b, p, w}:
      Some{b}
    case Spec.Request.Merge{f, x}:
      Some{x}
    case Spec.Request.Resolve{m, p, w}:
      Merge.line(fs, m)
    case Spec.Request.Mark{b, m, v}:
      Some{b}
    case Spec.Request.Move{b, t, v}:
      Some{b}
    case Spec.Request.Group{h, g, ms}:
      Some{Ledgers.Line{h, None{}}}
    case Spec.Request.Own{Ledgers.Line{h, b}, g}:
      Some{Ledgers.Line{h, None{}}}

# Pins
# ----

# a version that takes a version of another line: its number, and the number
# of the version that it takes
type Took is Data:
  Took{at: Nat, version: Nat}

# found, or the version k when it takes a version of the line c (m)
def Takes.pick(c: Ledgers.Line, k: Nat, m: Maybe<&2, Spec.Point>, found: Maybe<&2, Took>) -> Maybe<&2, Took>:
  match m:
    case None{}:
      found
    case Some{Spec.Point{t, v}}:
      Bool.pick(Maybe<&2, Took>, Ledgers.Line.is_eq(t, c), Some{Took{k, v}}, found)

# the newest version among vs, from the version k on, that takes a version of
# the line c: its number, and the version that it takes
def Takes.last(vs: List<&2, Types.Entry>, +c: Ledgers.Line, +k: Nat, found: Maybe<&2, Took>) -> Maybe<&2, Took>:
  match vs:
    case Nil{}:
      found
    case Con{e, rest}:
      Takes.last(rest, c, 1n+k, Takes.pick(c, k, Contents.Entry.takes(e), found))

# the pins of a merge of the line f into the line c: the newest version of f,
# and as base the newest version of c that f took, else the newest version of
# f that c took, else none
def Pins.merge.of(m: Nat, +c: Ledgers.Line, +f: Ledgers.Line, from: Nat, theirs: Maybe<&2, Took>, ours: Maybe<&2, Took>) -> Types.Pins:
  match theirs ours:
    case Some{Took{+j, +v}} _:
      Types.Pins{m, from, Some{Spec.Point{c, v}}, [Spec.Point{c, v}], [Spec.Point{f, j}, Spec.Point{c, v}]}
    case None{} Some{Took{+j, +v}}:
      Types.Pins{m, from, Some{Spec.Point{f, v}}, [Spec.Point{c, j}, Spec.Point{f, v}], [Spec.Point{f, v}]}
    case None{} None{}:
      Types.Pins{m, from, None{}, [], []}

# the pins of a merge of the line f, of the versions fv if known, into the
# line c, of the versions vs
def Pins.merge(m: Nat, +c: Ledgers.Line, +f: Ledgers.Line, +vs: List<&2, Types.Entry>, fv: Maybe<&2, List<&2, Types.Entry>>) -> Types.Pins:
  match fv:
    case None{}:
      Lines.Pins.plain(m)
    case Some{+fs}:
      Pins.merge.of(
        m,
        c,
        f,
        Nat.sub(List.length(&2, Types.Entry, fs), 1n),
        Takes.last(fs, c, 0n, None{}),
        Takes.last(vs, f, 0n, None{})
      )

# the pins that the node gives the request r for the line c, of the versions
# vs, at the era m
def Pins.for(+s: Facts.Facts(), +c: Ledgers.Line, +vs: List<&2, Types.Entry>, m: Nat, r: Spec.Request) -> Types.Pins:
  match r:
    case Spec.Request.Merge{+f, x}:
      Pins.merge(m, c, f, vs, Lines.Line.versions(s, f))
    case _:
      Lines.Pins.plain(m)

# the newest of the versions m
def Era.now.of(m: Maybe<&2, List<&2, Types.Entry>>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{R}:
      Nat.sub(List.length(&2, Types.Entry, R), 1n)

# the era that the node pins for the line c: the newest version of its store
# that it holds
def Era.now(+s: Facts.Facts(), c: Ledgers.Line) -> Nat:
  match c:
    case Ledgers.Line{h, b}:
      Era.now.of(Lines.Store.versions(s, h))

# The next vote
# -------------

# the node name may vote for the next slot of the line c, in the state st: it
# is one of the nodes of the rule u, and holds no vote of its own for the slot
def Work.free(+s: Facts.Facts(), +name: String, +c: Ledgers.Line, k: Nat, ns: List<&2, String>) -> Bool:
  Bool.and(
    List.contains(~String, ~String.eq, ns, name),
    Bool.not(Facts.Facts.cast(s, name, Types.Step.At{c, k}))
  )

# the vote of the node name for the ask a at the next slot of the line c, in
# the state m with the rule u, when it is its turn, it may vote, and the
# request made no version of the line yet
def Work.offer.at(+s: Facts.Facts(), +name: String, +c: Ledgers.Line, +a: Types.Ask, m: Maybe<&2, Lines.State>, u: Maybe<&2, Lines.Rule>) -> Maybe<&2, Types.Fact>:
  match m u:
    case Some{Lines.State{+vs, +k}} Some{Lines.Rule{g, +ns}}:
      Shared.Maybe.when(
        Types.Fact,
        Bool.and(
          Bool.and(String.eq(Turn.of(ns, k), name), Work.free(s, name, c, k, ns)),
          Bool.not(Shared.List.some(~Types.Entry, ~Ledgers.Id, ~Lines.Entry.is_of, vs, Lines.Ask.id(a)))
        ),
        u2 => Some{
          Types.Fact.Vote{
            name,
            Types.Step.At{c, k},
            Types.Pick{a, Pins.for(s, c, vs, Era.now(s, c), Lines.Ask.request(a))}
          }
        }
      )
    case _ _:
      None{}

# the rule of the next version of the line c, in the state m
def Work.rule(+s: Facts.Facts(), +c: Ledgers.Line, m: Maybe<&2, Lines.State>) -> Maybe<&2, Lines.Rule>:
  match m:
    case None{}:
      None{}
    case Some{Lines.State{vs, k}}:
      Lines.Rule.after(s, c, vs)

# the vote of the node name for the ask a, on the line m that it is for
def Work.offer.on(+s: Facts.Facts(), +name: String, +a: Types.Ask, m: Maybe<&2, Ledgers.Line>) -> Maybe<&2, Types.Fact>:
  match m:
    case None{}:
      None{}
    case Some{+c}:
      +st = Lines.Line.state(s, c)
      Work.offer.at(s, name, c, a, st, Work.rule(s, c, st))

# the vote that the node name may cast for the ask a
def Work.offer(+s: Facts.Facts(), +name: String, +a: Types.Ask) -> Maybe<&2, Types.Fact>:
  Work.offer.on(s, name, a, Request.line(Facts.Facts.list(s), Lines.Ask.request(a)))

# the asks among fs that the node name may vote for
def Work.ready(+s: Facts.Facts(), +name: String, fs: List<&2, Types.Fact>) -> List<&2, Types.Ask>:
  match fs:
    case Nil{}:
      []
    case Con{Types.Fact.Vote{v, st, pk}, rest}:
      Work.ready(s, name, rest)
    case Con{Types.Fact.Ask{+a}, rest}:
      List.filter.put(
        Types.Ask,
        a,
        Work.ready(s, name, rest),
        Maybe.is_some(&2, Types.Fact, Work.offer(s, name, a))
      )

# the vote of the node name for the ask m, if any
def Work.propose.of(+s: Facts.Facts(), +name: String, m: Maybe<&2, Types.Ask>) -> Maybe<&2, Types.Fact>:
  match m:
    case None{}:
      None{}
    case Some{a}:
      Work.offer(s, name, a)

# the vote that the node name proposes: for the ask that it took in last,
# among those that it may vote for
def Work.propose(+s: Facts.Facts(), +name: String) -> Maybe<&2, Types.Fact>:
  Work.propose.of(
    s,
    name,
    Lists.List.top(~Types.Ask, ~Facts.Ask.seq, Work.ready(s, name, Facts.Facts.list(s)))
  )

# the vote of the node name that follows the vote of v for the pick pk at the
# slot k of the line c, in the state m with the rule u: when the slot is the
# next one, it was the turn of v, and the node may vote
def Work.follow.at(+s: Facts.Facts(), +name: String, v: String, +c: Ledgers.Line, +k: Nat, pk: Types.Pick, m: Maybe<&2, Lines.State>, u: Maybe<&2, Lines.Rule>) -> Maybe<&2, Types.Fact>:
  match m u:
    case Some{Lines.State{vs, k2}} Some{Lines.Rule{g, +ns}}:
      Shared.Maybe.when(
        Types.Fact,
        Bool.and(
          Bool.and(Nat.is_eq(k2, k), String.eq(Turn.of(ns, k), v)),
          Work.free(s, name, c, k, ns)
        ),
        u2 => Some{Types.Fact.Vote{name, Types.Step.At{c, k}, pk}}
      )
    case _ _:
      None{}

# the vote of the node name that follows the fact f, if f is a vote to follow
def Work.follow.of(+s: Facts.Facts(), +name: String, f: Types.Fact) -> Maybe<&2, Types.Fact>:
  match f:
    case Types.Fact.Vote{v, Types.Step.At{+c, k}, pk}:
      +st = Lines.Line.state(s, c)
      Work.follow.at(s, name, v, c, k, pk, st, Work.rule(s, c, st))
    case _:
      None{}

# the vote m, or else the one that rest gives
def Work.follow.or(m: Maybe<&2, Types.Fact>, rest: Unit -> Maybe<&2, Types.Fact>) -> Maybe<&2, Types.Fact>:
  match m:
    case Some{f}:
      Some{f}
    case None{}:
      rest(Unit{})

# the first vote that the node name may cast to follow a vote among fs
def Work.follow(+s: Facts.Facts(), +name: String, fs: List<&2, Types.Fact>) -> Maybe<&2, Types.Fact>:
  match fs:
    case Nil{}:
      None{}
    case Con{f, rest}:
      Work.follow.or(Work.follow.of(s, name, f), u => Work.follow(s, name, rest))

# the vote that the node name casts next: the one that it proposes, else one
# that follows a vote that it holds
def Work.vote(+s: Facts.Facts(), +name: String) -> Maybe<&2, Types.Fact>:
  Work.follow.or(Work.propose(s, name), u => Work.follow(s, name, Facts.Facts.list(s)))

# the facts s after a work of the node name
def Work.does.of(s: Facts.Facts(), m: Maybe<&2, Types.Fact>) -> Facts.Facts():
  match m:
    case None{}:
      s
    case Some{f}:
      Facts.Facts.add(s, f)

# the facts s after a work of the node name
def Work.does(+s: Facts.Facts(), +name: String) -> Facts.Facts():
  Work.does.of(s, Work.vote(s, name))
