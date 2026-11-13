import Base
import ../shared/shared/ledger.bend as Ledgers
import ../shared/shared/shared/shared/hash.bend as Hashes
import ../shared/shared/shared/shared/shared.bend as Shared
import ./codes.bend as Coded
import ./shared/set.bend as Sets
import ./spec.bend as Spec
import ./types.bend as Types

# The facts of a node
# -------------------
# The facts are a set with one shape for its content (Sets), so two nodes that
# hold the same facts hold equal sets, and all that is read from the set is the
# same at both.

# the facts of a node
def Facts() -> Data:
  Sets.ValSet(~Types.Fact, ~Coded.Fact.words)

# no fact
def Facts.new() -> Facts():
  Sets.ValSet.new(~Types.Fact, ~Coded.Fact.words)

# s holds the fact f
def Facts.has(s: Facts(), +f: Types.Fact) -> Bool:
  Sets.ValSet.has(~Types.Fact, ~Coded.Fact.is_eq, ~Coded.Fact.words, s, f)

# s with the fact f
def Facts.add(+s: Facts(), +f: Types.Fact) -> Facts():
  Sets.ValSet.add(~Types.Fact, ~Coded.Fact.words, s, f)

# the facts of s, each once
def Facts.list(s: Facts()) -> List<&2, Types.Fact>:
  Sets.ValSet.list(~Types.Fact, ~Coded.Fact.words, s)

# how far a read of s may go from line to line: the count of its facts
def Facts.fuel(s: Facts()) -> Nat:
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
def Facts.holds(+s: Facts(), c: Types.Change) -> Bool:
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
def Facts.liars(s: Facts()) -> List<&2, String>:
  +fs = Facts.list(s)
  Facts.liars.go(fs, fs)

# Trust
# -----
# A node trusts two things that no proof gives: that nobody else casts a vote
# under its name, and that no two requests start one store (SHA-256). When a
# node sees either broken, it says so with two votes that contradict each
# other, under a name of its own that is not its name. So it names a liar,
# and no law about a node that names no liar binds it any more.

# the name under which the node name says that its trust broke
def Trust.voter(name: String) -> String:
  SCon{'~', name}

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
def Trust.break(s: Facts(), +name: String) -> Facts():
  Facts.add(Facts.add(s, Trust.one(name)), Trust.two(name))

# s says that the trust of the node name broke
def Trust.broken(+s: Facts(), +name: String) -> Bool:
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
def Facts.collide(s: Facts()) -> Bool:
  +fs = Facts.list(s)
  Shared.List.some(~Types.Fact, ~List<&2, Types.Fact>, ~Fact.collided, fs, fs)

# Taking a fact in
# ----------------

# the fact f is a vote under the name of the node that contradicts a vote that
# s holds: the node did not cast it
def Facts.refuses(+name: String, s: Facts(), f: Types.Fact) -> Bool:
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
def Facts.take(+name: String, +s: Facts(), +f: Types.Fact) -> Facts():
  Shared.Bool.when(
    Facts(),
    Facts.refuses(name, s, f),
    u => Trust.break(s, name),
    u => Shared.Bool.when(
      Facts(),
      Fact.collided(Facts.list(s), f),
      u => Trust.break(Facts.add(s, f), name),
      u => Facts.add(s, f)
    )
  )

# s with each of the facts fs, as the node name takes them in
def Facts.take_all(+name: String, fs: List<&2, Types.Fact>, +s: Facts()) -> Facts():
  match fs:
    case Nil{}:
      s
    case Con{f, rest}:
      Facts.take_all(name, rest, Facts.take(name, s, f))

# the facts s are sound for the node name: s does not name the node a liar,
# and, if two asks of s start one store, s says that the trust of the node
# broke
def Facts.ok(+name: String, +s: Facts()) -> Bool:
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
def Facts.cast(s: Facts(), name: String, st: Types.Step) -> Bool:
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
def Facts.asked(s: Facts(), i: Ledgers.Id, r: Spec.Request) -> Types.Ask:
  Types.Ask{i, 1n+Seq.peak(Facts.list(s)), r}

# s after the node name takes in the request r of the id i
def Facts.ask(+name: String, +s: Facts(), i: Ledgers.Id, r: Spec.Request) -> Facts():
  Facts.take(name, s, Types.Fact.Ask{Facts.asked(s, i, r)})

# Laws of the facts
# -----------------

# what a set with a fact holds: the fact, and what it held
def Facts.has_add(+s: Facts(), +y: Types.Fact, +x: Types.Fact) -> {
  Facts.has(Facts.add(s, y), x) == Bool.or(Coded.Fact.is_eq(x, y), Facts.has(s, x)): Bool
}:
  ?TODO

# a set holds the facts of its list
def Facts.has_list(+s: Facts(), +x: Types.Fact) -> {
  Facts.has(s, x) == List.contains(~Types.Fact, ~Coded.Fact.is_eq, Facts.list(s), x): Bool
}:
  ?TODO

# two sets that hold the same facts are one set
def Facts.ext(a: Facts(), b: Facts()) -> (@f: Types.Fact -> {Facts.has(a, f) == Facts.has(b, f): Bool}) -> {
  a == b: Facts()
}:
  ?TODO

# two sets that hold the same changes are one set
def Facts.same(a: Facts(), b: Facts()) -> (
  @c: Types.Change -> {Facts.holds(a, c) == Facts.holds(b, c): Bool}
) -> {a == b: Facts()}:
  ?TODO

# b holds each fact that a holds
def Facts.Grows(a: Facts(), b: Facts()) -> Type:
  @f: Types.Fact -> {Facts.has(a, f) == True{}: Bool} -> {Facts.has(b, f) == True{}: Bool}

# b holds each fact that a holds, and a read of b may go as far as one of a
def Facts.Wider(a: Facts(), b: Facts()) -> Type:
  Facts.Grows(a, b) & {Nat.is_le(Facts.fuel(a), Facts.fuel(b)) == True{}: Bool}

# a set is wider than itself
def Facts.wider_refl(+s: Facts()) -> Facts.Wider(s, s):
  ?TODO

# wider goes through
def Facts.wider_trans(+a: Facts(), +b: Facts(), +c: Facts()) -> Facts.Wider(a, b) -> Facts.Wider(b, c) -> Facts.Wider(
  a,
  c
):
  ?TODO

# a set with a fact is wider
def Facts.add_wider(+s: Facts(), +f: Types.Fact) -> Facts.Wider(s, Facts.add(s, f)):
  ?TODO

# a set that grows holds each change that it held
def Facts.grows_holds(+a: Facts(), +b: Facts(), +c: Types.Change) -> Facts.Grows(a, b) -> {
  Facts.holds(a, c) == True{}: Bool
} -> {Facts.holds(b, c) == True{}: Bool}:
  ?TODO

# a set that grows lists each fact that it listed
def Facts.grows_list(+a: Facts(), +b: Facts(), +f: Types.Fact) -> Facts.Grows(a, b) -> {
  List.contains(~Types.Fact, ~Coded.Fact.is_eq, Facts.list(a), f) == True{}: Bool
} -> {List.contains(~Types.Fact, ~Coded.Fact.is_eq, Facts.list(b), f) == True{}: Bool}:
  ?TODO

# a set that holds two ballots of one voter for one step with two choices names
# the voter a liar
def Facts.liars_found(
  +s: Facts(),
  +a: Types.Change,
  +b: Types.Change,
  +v: String,
  +st: List<&2, U32>,
  +x: List<&2, U32>,
  +y: List<&2, U32>
) -> {Facts.holds(s, a) == True{}: Bool} -> {Facts.holds(s, b) == True{}: Bool} -> {
  Change.ballot(a) == Some{Spec.Ballot{v, st, x}}: Maybe<&2, Spec.Ballot>
} -> {Change.ballot(b) == Some{Spec.Ballot{v, st, y}}: Maybe<&2, Spec.Ballot>} -> (
  {x == y: List<&2, U32>} -> Empty
) -> {List.contains(~String, ~String.eq, Facts.liars(s), v) == True{}: Bool}:
  ?TODO

# a set names a voter a liar only when it holds two ballots of the voter for
# one step with two choices
def Facts.liars_are(+s: Facts(), +v: String) -> {
  List.contains(~String, ~String.eq, Facts.liars(s), v) == True{}: Bool
} -> Exists(
  Types.Change,
  a => Exists(
    Types.Change,
    b => {
      Facts.holds(s, a) == True{}: Bool
    }
      & (
        {
          Facts.holds(s, b) == True{}: Bool
        }
          & Exists(
            List<&2, U32>,
            st => Exists(
              List<&2, U32>,
              x => Exists(
                List<&2, U32>,
                y => {
                  Change.ballot(a) == Some{Spec.Ballot{v, st, x}}: Maybe<&2, Spec.Ballot>
                }
                  & (
                    {
                      Change.ballot(b) == Some{Spec.Ballot{v, st, y}}: Maybe<&2, Spec.Ballot>
                    }
                      & ({x == y: List<&2, U32>} -> Empty)
                  )
              )
            )
          )
      )
  )
):
  ?TODO

# in a set that names no liar, a voter has one pick for a step
def Facts.honest_one(+s: Facts(), +v: String, +st: Types.Step, +p: Types.Pick, +q: Types.Pick) -> {
  Facts.liars(s) == []: List<&2, String>
} -> {Facts.has(s, Types.Fact.Vote{v, st, p}) == True{}: Bool} -> {
  Facts.has(s, Types.Fact.Vote{v, st, q}) == True{}: Bool
} -> {p == q: Types.Pick}:
  ?TODO

# a set that is sound for a node does not name the node a liar
def Facts.ok_never(+name: String, +s: Facts()) -> {Facts.ok(name, s) == True{}: Bool} -> {
  List.contains(~String, ~String.eq, Facts.liars(s), name) == False{}: Bool
}:
  ?TODO

# in a set that is sound for a node and names no liar, two asks that start
# one store are of one id and one request
def Facts.honest_starts(+name: String, +s: Facts(), +h: Hashes.Hash, +a: Types.Ask, +b: Types.Ask) -> {
  Facts.ok(name, s) == True{}: Bool
} -> {Facts.liars(s) == []: List<&2, String>} -> {Facts.has(s, Types.Fact.Ask{a}) == True{}: Bool} -> {
  Facts.has(s, Types.Fact.Ask{b}) == True{}: Bool
} -> {Ask.starts(h, a) == True{}: Bool} -> {Ask.starts(h, b) == True{}: Bool} -> {
  Ask.alike(a, b) == True{}: Bool
}:
  ?TODO

# the empty set is sound for every node
def Facts.new_ok(+name: String) -> {Facts.ok(name, Facts.new()) == True{}: Bool}:
  ?TODO

# a set is wider after it takes a fact in
def Facts.take_wider(+name: String, +s: Facts(), +f: Types.Fact) -> Facts.Wider(s, Facts.take(name, s, f)):
  ?TODO

# a set is wider after it takes facts in
def Facts.take_all_wider(+name: String, +fs: List<&2, Types.Fact>, +s: Facts()) -> Facts.Wider(
  s,
  Facts.take_all(name, fs, s)
):
  ?TODO

# a set stays sound when it takes a fact in
def Facts.take_ok(+name: String, +s: Facts(), +f: Types.Fact) -> {Facts.ok(name, s) == True{}: Bool} -> {
  Facts.ok(name, Facts.take(name, s, f)) == True{}: Bool
}:
  ?TODO

# a set stays sound when it takes facts in
def Facts.take_all_ok(+name: String, +fs: List<&2, Types.Fact>, +s: Facts()) -> {
  Facts.ok(name, s) == True{}: Bool
} -> {Facts.ok(name, Facts.take_all(name, fs, s)) == True{}: Bool}:
  ?TODO

# a set that took facts in holds each of them, while it names no liar
def Facts.take_all_has(+name: String, +fs: List<&2, Types.Fact>, +s: Facts(), +f: Types.Fact) -> {
  Facts.liars(Facts.take_all(name, fs, s)) == []: List<&2, String>
} -> {List.contains(~Types.Fact, ~Coded.Fact.is_eq, fs, f) == True{}: Bool} -> {
  Facts.has(Facts.take_all(name, fs, s), f) == True{}: Bool
}:
  ?TODO

# a set stays sound with a vote of the node for a step that it held no vote
# of the node for
def Facts.add_cast_ok(+name: String, +s: Facts(), +st: Types.Step, +pk: Types.Pick) -> {
  Facts.ok(name, s) == True{}: Bool
} -> {Facts.cast(s, name, st) == False{}: Bool} -> {
  Facts.ok(name, Facts.add(s, Types.Fact.Vote{name, st, pk})) == True{}: Bool
}:
  ?TODO

# a set that takes an ask in holds it
def Facts.take_ask_has(+name: String, +s: Facts(), +a: Types.Ask) -> {
  Facts.has(Facts.take(name, s, Types.Fact.Ask{a}), Types.Fact.Ask{a}) == True{}: Bool
}:
  ?TODO

# a set that takes an ask in holds the votes for slots that it held
def Facts.take_ask_votes(
  +name: String,
  +s: Facts(),
  +a: Types.Ask,
  +v: String,
  +c: Ledgers.Line,
  +k: Nat,
  +pk: Types.Pick
) -> {
  Facts.has(Facts.take(name, s, Types.Fact.Ask{a}), Types.Fact.Vote{v, Types.Step.At{c, k}, pk})
    == Facts.has(s, Types.Fact.Vote{v, Types.Step.At{c, k}, pk}): Bool
}:
  ?TODO

# a set that takes an ask in holds that ask, and the asks that it held
def Facts.take_ask_asks(+name: String, +s: Facts(), +a: Types.Ask, +b: Types.Ask) -> {
  Facts.has(Facts.take(name, s, Types.Fact.Ask{a}), Types.Fact.Ask{b})
    == Bool.or(Coded.Ask.is_eq(b, a), Facts.has(s, Types.Fact.Ask{b})): Bool
}:
  ?TODO

# the number of each ask that a set holds, as an ask or in a vote, is at most
# the greatest number of the set
def Facts.seq_ask(+s: Facts(), +a: Types.Ask) -> {Facts.has(s, Types.Fact.Ask{a}) == True{}: Bool} -> {
  Nat.is_le(Ask.seq(a), Seq.peak(Facts.list(s))) == True{}: Bool
}:
  ?TODO

# the number of the ask of each vote that a set holds is at most the greatest
# number of the set
def Facts.seq_vote(+s: Facts(), +v: String, +st: Types.Step, +a: Types.Ask, +pins: Types.Pins) -> {
  Facts.has(s, Types.Fact.Vote{v, st, Types.Pick{a, pins}}) == True{}: Bool
} -> {Nat.is_le(Ask.seq(a), Seq.peak(Facts.list(s))) == True{}: Bool}:
  ?TODO
