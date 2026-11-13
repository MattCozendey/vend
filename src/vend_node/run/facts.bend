import Base
import ../../shared/shared/ledger.bend as Ledgers
import ../../shared/shared/shared/shared/crit.bend as Crits
import ../../shared/shared/shared/shared/hash.bend as Hashes
import ../../shared/shared/shared/shared/shared.bend as Shared
import ../../shared/shared/shared/text.bend as Texts
import ../codes.bend as Coded
import ../shared/lists.bend as Lists
import ../spec.bend as Spec
import ../types.bend as Types

# The facts of a node, plain
# --------------------------
# This is the code that runs: the facts are a plain crit-bit map from the key
# of each fact to the fact, and no proof is built on the way. The proofs that
# the map is a set are in facts.bend, said of the same map.

# the facts of a node: a map from the key of each fact to the fact
def Plain() -> Data:
  Crits.Crit<Types.Fact>

# no fact
def Facts.new() -> Plain():
  Crits.Crit.new(Types.Fact)

# s holds the fact f
def Facts.has(s: Plain(), +f: Types.Fact) -> Bool:
  Crits.Crit.has(Types.Fact, s, Coded.Fact.words(f))

# s with the fact f
def Facts.add(+s: Plain(), +f: Types.Fact) -> Plain():
  Crits.Crit.set(~Types.Fact, s, Coded.Fact.words(f), f)

# the facts of s, each once
def Facts.list(s: Plain()) -> List<&2, Types.Fact>:
  Crits.Binds.values(Types.Fact, Crits.Crit.entries(Types.Fact, s))

# how far a read of s may go from line to line: the count of its facts
def Facts.fuel(s: Plain()) -> Nat:
  List.length(&2, Types.Fact, Facts.list(s))

# Changes
# -------

# the ballot that the fact f is, if it is a vote: its step and its pick, as
# words
def Fact.ballot(f: Types.Fact) -> Maybe<&2, Spec.Ballot>:
  match f:
    case Types.Fact.Ask{a}:
      None{}
    case Types.Fact.Vote{v, st, pk}:
      Some{Spec.Ballot{v, Coded.Step.words(st), Coded.Pick.words(pk)}}

# the ballot that the change c is, if it is one
def Change.ballot(c: Types.Change) -> Maybe<&2, Spec.Ballot>:
  match c:
    case Types.Change.Fact{f}:
      Fact.ballot(f)
    case Types.Change.Lie{v, st, one, two}:
      None{}

# s holds the change c: the fact, or both votes of the lie, which differ
def Facts.holds(+s: Plain(), c: Types.Change) -> Bool:
  match c:
    case Types.Change.Fact{f}:
      Facts.has(s, f)
    case Types.Change.Lie{+v, +st, +one, +two}:
      Bool.and(
        Bool.and(
          Facts.has(s, Types.Fact.Vote{v, st, one}),
          Facts.has(s, Types.Fact.Vote{v, st, two})
        ),
        Bool.not(Coded.Pick.is_eq(one, two))
      )

# Liars
# -----

# a and b are the same words
def Words.is_eq(a: List<&2, U32>, b: List<&2, U32>) -> Bool:
  Shared.List.is_eq(~U32, ~U32.is_eq, a, b)

# the ballots a and b contradict each other: one voter, one step, two choices
def Ballot.clash(a: Spec.Ballot, b: Spec.Ballot) -> Bool:
  match a b:
    case Spec.Ballot{v, s, x} Spec.Ballot{w, t, y}:
      Bool.and(String.eq(v, w), Bool.and(Words.is_eq(s, t), Bool.not(Words.is_eq(x, y))))

# the ballot m, if any, contradicts b
def Fact.clashes.at(b: Spec.Ballot, m: Maybe<&2, Spec.Ballot>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{a}:
      Ballot.clash(b, a)

# the fact f is a vote that contradicts the ballot b
def Fact.clashes(b: Spec.Ballot, f: Types.Fact) -> Bool:
  Fact.clashes.at(b, Fact.ballot(f))

# the voter of the ballot b
def Ballot.voter(b: Spec.Ballot) -> String:
  match b:
    case Spec.Ballot{v, s, x}:
      v

# the voter of the ballot m, if any, when a fact of all contradicts it
def Fact.liar.at(+all: List<&2, Types.Fact>, m: Maybe<&2, Spec.Ballot>) -> Maybe<&2, String>:
  match m:
    case None{}:
      None{}
    case Some{+b}:
      Shared.Maybe.when(
        String,
        Shared.List.some(~Types.Fact, ~Spec.Ballot, ~Fact.clashes, all, b),
        u => Some{Ballot.voter(b)}
      )

# the voter of the fact f, when f is a vote that a fact of all contradicts
def Fact.liar(+all: List<&2, Types.Fact>, f: Types.Fact) -> Maybe<&2, String>:
  Fact.liar.at(all, Fact.ballot(f))

# the voters of the votes among fs that a fact of all contradicts
def Facts.liars.go(+all: List<&2, Types.Fact>, fs: List<&2, Types.Fact>) -> List<&2, String>:
  match fs:
    case Nil{}:
      []
    case Con{f, rest}:
      Shared.Maybe.cons(String, Fact.liar(all, f), Facts.liars.go(all, rest))

# the voters that s proves to be liars: those with two votes that contradict
# each other
def Facts.liars(s: Plain()) -> List<&2, String>:
  +fs = Facts.list(s)
  Facts.liars.go(fs, fs)

# Trust
# -----
# A node trusts two things that no proof gives: that nobody else casts a vote
# under its name, and that no two requests start one store (SHA-256). When a
# node sees either broken, it says so with two votes that contradict each
# other, under a name of its own that is not its name. So it names a liar,
# and no law about a node that names no liar binds it any more. The names
# that start with '~' are reserved: no node has one, so the name under which
# a node says that its trust broke is never the name of a node.

# the name under which the node name says that its trust broke
def Trust.voter(name: String) -> String:
  SCon{'~', name}

# the name name is reserved: it starts with '~', so no node has it
def Trust.reserved(name: String) -> Bool:
  match name:
    case SNil{}:
      False{}
    case SCon{c, rest}:
      Char.is_eq(c, '~')

# a pick that is for nothing, of the number k
def Trust.pick(k: Nat) -> Types.Pick:
  Types.Pick{
    Types.Ask{Ledgers.Id{"", ""}, k, Spec.Request.Start{[]}},
    Types.Pins{0n, 0n, None{}, [], []}
  }

# the first vote of a broken trust
def Trust.one(name: String) -> Types.Fact:
  Types.Fact.Vote{Trust.voter(name), Types.Step.Broken{}, Trust.pick(0n)}

# the second vote of a broken trust
def Trust.two(name: String) -> Types.Fact:
  Types.Fact.Vote{Trust.voter(name), Types.Step.Broken{}, Trust.pick(1n)}

# s, where the trust of the node name broke
def Trust.break(s: Plain(), +name: String) -> Plain():
  Facts.add(Facts.add(s, Trust.one(name)), Trust.two(name))

# s says that the trust of the node name broke
def Trust.broken(+s: Plain(), +name: String) -> Bool:
  Bool.and(Facts.has(s, Trust.one(name)), Facts.has(s, Trust.two(name)))

# Starts
# ------

# the root of the store that the request r of the id i starts: the hash of
# its name
def Start.root(i: Ledgers.Id, r: Spec.Request) -> Hashes.Hash:
  Hashes.Sha.hash(Coded.Named.code(i, r))

# the request r starts a store
def Request.is_start(r: Spec.Request) -> Bool:
  match r:
    case Spec.Request.Start{os}:
      True{}
    case _:
      False{}

# the ask a starts the store of the root h
def Ask.starts(+h: Hashes.Hash, a: Types.Ask) -> Bool:
  match a:
    case Types.Ask{+i, k, +r}:
      Bool.and(Request.is_start(r), Hashes.Hash.is_eq(Start.root(i, r), h))

# the asks a and b are of one id and one request
def Ask.alike(a: Types.Ask, b: Types.Ask) -> Bool:
  match a b:
    case Types.Ask{i, k, r} Types.Ask{j, l, q}:
      Bool.and(Ledgers.Id.is_eq(i, j), Coded.Request.is_eq(r, q))

# the root of the store that the ask a starts
def Ask.root(a: Types.Ask) -> Hashes.Hash:
  match a:
    case Types.Ask{i, k, r}:
      Start.root(i, r)

# the ask a starts a store, and b starts the same store with another id or
# request: SHA-256 is broken
def Ask.collides(+a: Types.Ask, +b: Types.Ask) -> Bool:
  Bool.and(
    Ask.starts(Ask.root(a), a),
    Bool.and(Ask.starts(Ask.root(a), b), Bool.not(Ask.alike(a, b)))
  )

# the fact f is an ask that collides with the ask a
def Fact.collides(a: Types.Ask, f: Types.Fact) -> Bool:
  match f:
    case Types.Fact.Ask{+b}:
      Ask.collides(a, b)
    case Types.Fact.Vote{v, st, pk}:
      False{}

# the fact f is an ask that collides with a fact of all
def Fact.collided(all: List<&2, Types.Fact>, f: Types.Fact) -> Bool:
  match f:
    case Types.Fact.Ask{+a}:
      Shared.List.some(~Types.Fact, ~Types.Ask, ~Fact.collides, all, a)
    case Types.Fact.Vote{v, st, pk}:
      False{}

# two asks of s start one store with different ids or requests
def Facts.collide(s: Plain()) -> Bool:
  +fs = Facts.list(s)
  Shared.List.some(~Types.Fact, ~List<&2, Types.Fact>, ~Fact.collided, fs, fs)

# Taking a fact in
# ----------------

# the fact f is a vote under the name of the node that contradicts a vote that
# s holds: the node did not cast it
def Facts.refuses(+name: String, s: Plain(), f: Types.Fact) -> Bool:
  match f:
    case Types.Fact.Ask{a}:
      False{}
    case Types.Fact.Vote{+v, +st, +pk}:
      Bool.and(
        String.eq(v, name),
        Shared.List.some(
          ~Types.Fact,
          ~Spec.Ballot,
          ~Fact.clashes,
          Facts.list(s),
          Spec.Ballot{v, Coded.Step.words(st), Coded.Pick.words(pk)}
        )
      )

# s with the fact f, as the node name takes it in: it does not take a vote
# under its own name that contradicts one that it holds, and it says that its
# trust broke when it sees such a vote, or a second start of one store
def Facts.take(+name: String, +s: Plain(), +f: Types.Fact) -> Plain():
  Shared.Bool.when(
    Plain(),
    Facts.refuses(name, s, f),
    u => Trust.break(s, name),
    u => Shared.Bool.when(
      Plain(),
      Fact.collided(Facts.list(s), f),
      u => Trust.break(Facts.add(s, f), name),
      u => Facts.add(s, f)
    )
  )

# s with each of the facts fs, as the node name takes them in
def Facts.take_all(+name: String, fs: List<&2, Types.Fact>, +s: Plain()) -> Plain():
  match fs:
    case Nil{}:
      s
    case Con{f, rest}:
      Facts.take_all(name, rest, Facts.take(name, s, f))

# the facts s are sound for the node name: s does not name the node a liar,
# and, if two asks of s start one store, s says that the trust of the node
# broke
def Facts.ok(+name: String, +s: Plain()) -> Bool:
  Bool.and(
    Bool.not(List.contains(~String, ~String.eq, Facts.liars(s), name)),
    Bool.or(Bool.not(Facts.collide(s)), Trust.broken(s, name))
  )

# Votes of the node
# -----------------

# a node and a step
type Seat is Data:
  Seat{name: String, step: Types.Step}

# the fact f is a vote of the node of g for the step of g
def Fact.is_cast(g: Seat, f: Types.Fact) -> Bool:
  match g f:
    case Seat{name, st} Types.Fact.Vote{v, st2, pk}:
      Bool.and(String.eq(v, name), Coded.Step.is_eq(st2, st))
    case Seat{name, st} Types.Fact.Ask{a}:
      False{}

# s holds a vote of the node name for the step st
def Facts.cast(s: Plain(), name: String, st: Types.Step) -> Bool:
  Shared.List.some(~Types.Fact, ~Seat, ~Fact.is_cast, Facts.list(s), Seat{name, st})

# Asks
# ----

# the number of the ask a
def Ask.seq(a: Types.Ask) -> Nat:
  match a:
    case Types.Ask{i, k, r}:
      k

# the greatest number of an ask among fs, as an ask or in a vote
def Seq.peak(fs: List<&2, Types.Fact>) -> Nat:
  match fs:
    case Nil{}:
      0n
    case Con{Types.Fact.Ask{a}, rest}:
      Nat.max(Ask.seq(a), Seq.peak(rest))
    case Con{Types.Fact.Vote{v, st, Types.Pick{a, pins}}, rest}:
      Nat.max(Ask.seq(a), Seq.peak(rest))

# the ask of the request r of the id i, as a node that holds s takes it in:
# with a number above every number in s
def Facts.asked(s: Plain(), i: Ledgers.Id, r: Spec.Request) -> Types.Ask:
  Types.Ask{i, 1n+Seq.peak(Facts.list(s)), r}

# s after the node name takes in the request r of the id i
def Facts.ask(+name: String, +s: Plain(), i: Ledgers.Id, r: Spec.Request) -> Plain():
  Facts.take(name, s, Types.Fact.Ask{Facts.asked(s, i, r)})

# Wider sets
# ----------

# b holds the fact f
def Fact.held(b: Plain(), f: Types.Fact) -> Bool:
  Facts.has(b, f)

# b holds each fact of a, and a read of b may go as far as one of a
def Facts.wider(+a: Plain(), +b: Plain()) -> Bool:
  Bool.and(
    Shared.List.holds(~Types.Fact, ~Plain(), ~Fact.held, Facts.list(a), b),
    Nat.is_le(Facts.fuel(a), Facts.fuel(b))
  )
