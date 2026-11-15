import Base
import ../../shared/shared/ledger.bend as Ledgers
import ../../shared/shared/shared/shared/crit.bend as Crits
import ../../shared/shared/shared/shared/hash.bend as Hashes
import ../../shared/shared/shared/shared/shared.bend as Shared
import ../codes.bend as Coded
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

# the fact m, if any, is the fact f
def Facts.held.of(m: Maybe<&2, Types.Fact>, +f: Types.Fact) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{v}:
      Coded.Fact.is_eq(v, f)

# s holds the fact f under the key k: a read of one key, with no code of f
def Facts.held(s: Plain(), +k: List<&2, U32>, +f: Types.Fact) -> Bool:
  Facts.held.of(Crits.Crit.get(Types.Fact, s, k), f)

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

# the ballot that the fact f is, if it is one: its step and what it casts, as
# words
def Fact.ballot(f: Types.Fact) -> Maybe<&2, Spec.Ballot>:
  match f:
    case Types.Fact.Ask{a}:
      None{}
    case Types.Fact.Vote{v, st, pk}:
      Some{Spec.Ballot{v, Coded.Step.words(st), Coded.Cast.words(pk)}}

# the ballot that the change c is, if it is one
def Change.ballot(c: Types.Change) -> Maybe<&2, Spec.Ballot>:
  match c:
    case Types.Change.Fact{f}:
      Fact.ballot(f)
    case Types.Change.Lie{v, st, one, two}:
      None{}

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- measured: not in the main9/10/11/16 builds, so no driver runs it; each right side is one lookup in the set, or one compare of two casts
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
        Bool.not(Coded.Cast.is_eq(one, two))
      )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# Liars
# -----

# a and b are the same words
def Words.is_eq(a: List<&2, U32>, b: List<&2, U32>) -> Bool:
  Shared.List.is_eq(~U32, ~U32.is_eq, a, b)

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- measured: not in the main9/10/11/16 builds, so no driver runs it (Facts.liars is not in them); each right side compares two short lists of words
# the ballots a and b contradict each other: one voter, one step, two choices
def Ballot.clash(a: Spec.Ballot, b: Spec.Ballot) -> Bool:
  match a b:
    case Spec.Ballot{v, s, x} Spec.Ballot{w, t, y}:
      Bool.and(String.eq(v, w), Bool.and(Words.is_eq(s, t), Bool.not(Words.is_eq(x, y))))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

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

# a cast that is for nothing, of the number k
def Trust.cast(k: Nat) -> Types.Cast:
  Types.Cast.Pass{k}

# the first vote of a broken trust
def Trust.one(name: String) -> Types.Fact:
  Types.Fact.Vote{Trust.voter(name), Types.Step.Broken{}, Trust.cast(0n)}

# the second vote of a broken trust
def Trust.two(name: String) -> Types.Fact:
  Types.Fact.Vote{Trust.voter(name), Types.Step.Broken{}, Trust.cast(1n)}

# s, where the trust of the node name broke
def Trust.break(s: Plain(), +name: String) -> Plain():
  Facts.add(Facts.add(s, Trust.one(name)), Trust.two(name))

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- measured: not in the main9/10/11/16 builds, so no driver runs it; the right side is one lookup in the set
# s says that the trust of the node name broke
def Trust.broken(+s: Plain(), +name: String) -> Bool:
  Bool.and(Facts.has(s, Trust.one(name)), Facts.has(s, Trust.two(name)))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

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
      Shared.Bool.when(
        Bool,
        Request.is_start(r),
        u => Hashes.Hash.is_eq(Start.root(i, r), h),
        u => False{}
      )

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- measured (callgrind, main16 n=5, Start and Work): under 0.1k of 211k instructions per call; the right side compares two requests and stops at the first difference
# the asks a and b are of one id and one request
def Ask.alike(a: Types.Ask, b: Types.Ask) -> Bool:
  match a b:
    case Types.Ask{i, k, r} Types.Ask{j, l, q}:
      Bool.and(Ledgers.Id.is_eq(i, j), Coded.Request.is_eq(r, q))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the root of the store that the ask a starts
def Ask.root(a: Types.Ask) -> Hashes.Hash:
  match a:
    case Types.Ask{i, k, r}:
      Start.root(i, r)

# the ask a starts a store, and b starts the same store with another id or
# request: SHA-256 is broken
def Ask.collides(+a: Types.Ask, +b: Types.Ask) -> Bool:
  Shared.Bool.when(
    Bool,
    Ask.starts(Ask.root(a), a),
    un => Shared.Bool.when(
      Bool,
      Ask.starts(Ask.root(a), b),
      u => Bool.not(Ask.alike(a, b)),
      u => False{}
    ),
    un => False{}
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
      Shared.Bool.when(
        Bool,
        String.eq(v, name),
        u => Shared.List.some(
          ~Types.Fact,
          ~Spec.Ballot,
          ~Fact.clashes,
          Facts.list(s),
          Spec.Ballot{v, Coded.Step.words(st), Coded.Cast.words(pk)}
        ),
        u => False{}
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

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- measured: not in the main9/10/11/16 builds, so no driver runs it; it is said only in laws (Raw.ok)
# the facts s are sound for the node name: s does not name the node a liar,
# and, if two asks of s start one store, s says that the trust of the node
# broke
def Facts.ok(+name: String, +s: Plain()) -> Bool:
  Bool.and(
    Bool.not(List.contains(~String, ~String.eq, Facts.liars(s), name)),
    Bool.or(Bool.not(Facts.collide(s)), Trust.broken(s, name))
  )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# Soundness, read fast
# --------------------
# Facts.ok reads each fact against each fact, and builds the words of each
# ballot again each time. Only two votes of the node at one step name it a
# liar, and only two starts collide, so Facts.ok.fast reads those only, each
# ballot built once and compared with those of its step only (the starts,
# a few, each with each). fast.bend proves that it is Facts.ok
# (Sound.ok_fast).

# the ballot m, if any, before the ballots rest, when its voter is name
def Own.put(
  +name: String,
  m: Maybe<&2, Spec.Ballot>,
  rest: List<&2, Spec.Ballot>
) -> List<&2, Spec.Ballot>:
  match m:
    case None{}:
      rest
    case Some{+b}:
      List.filter.put(Spec.Ballot, b, rest, String.eq(Ballot.voter(b), name))

# the ballots of the votes of the voter name among fs
def Facts.own(+name: String, fs: List<&2, Types.Fact>) -> List<&2, Spec.Ballot>:
  match fs:
    case Nil{}:
      []
    case Con{f, rest}:
      Own.put(name, Fact.ballot(f), Facts.own(name, rest))

# Ballot.clash, which compares the steps only of one voter, and the casts
# only at one step
def Ballot.clash.lazy(a: Spec.Ballot, b: Spec.Ballot) -> Bool:
  match a b:
    case Spec.Ballot{v, s, x} Spec.Ballot{w, t, y}:
      Shared.Bool.when(
        Bool,
        String.eq(v, w),
        u => Shared.Bool.when(
          Bool,
          Words.is_eq(s, t),
          u2 => Bool.not(Words.is_eq(x, y)),
          u2 => False{}
        ),
        u => False{}
      )

# some ballot of bs contradicts a ballot of all
def Ballots.clash(+all: List<&2, Spec.Ballot>, bs: List<&2, Spec.Ballot>) -> Bool:
  match bs:
    case Nil{}:
      False{}
    case Con{+b, rest}:
      List.any.if(
        u => Ballots.clash(all, rest),
        Shared.List.some(~Spec.Ballot, ~Spec.Ballot, ~Ballot.clash.lazy, all, b)
      )

# the ballots that m holds, if any
def Bucket.of(m: Maybe<&2, List<&2, Spec.Ballot>>) -> List<&2, Spec.Ballot>:
  match m:
    case None{}:
      []
    case Some{bs}:
      bs

# the ballots bs by the words of their step: under each, those of that step
def Ballots.by_step(bs: List<&2, Spec.Ballot>) -> Crits.Crit<List<&2, Spec.Ballot>>:
  match bs:
    case Nil{}:
      Crits.Crit.new(List<&2, Spec.Ballot>)
    case Con{Spec.Ballot{+v, +st, +x}, rest}:
      +m = Ballots.by_step(rest)
      Crits.Crit.set(
        ~List<&2, Spec.Ballot>,
        m,
        st,
        Spec.Ballot{v, st, x} <> Bucket.of(Crits.Crit.get(List<&2, Spec.Ballot>, m, st))
      )

# some ballot of bs contradicts a ballot of its step in m: Ballots.clash,
# where m holds the ballots of all by step (fast.bend: Steps.clash_by), so
# that a ballot is compared only with those of its step
def Ballots.clash.by(+m: Crits.Crit<List<&2, Spec.Ballot>>, bs: List<&2, Spec.Ballot>) -> Bool:
  match bs:
    case Nil{}:
      False{}
    case Con{Spec.Ballot{+v, +st, +x}, rest}:
      List.any.if(
        u => Ballots.clash.by(m, rest),
        Shared.List.some(
          ~Spec.Ballot,
          ~Spec.Ballot,
          ~Ballot.clash.lazy,
          Bucket.of(Crits.Crit.get(List<&2, Spec.Ballot>, m, st)),
          Spec.Ballot{v, st, x}
        )
      )

# the ask of the fact f before the asks rest, when it starts a store
def Start.put(f: Types.Fact, rest: List<&2, Types.Ask>) -> List<&2, Types.Ask>:
  match f:
    case Types.Fact.Ask{Types.Ask{i, k, +r}}:
      List.filter.put(Types.Ask, Types.Ask{i, k, r}, rest, Request.is_start(r))
    case Types.Fact.Vote{v, st, pk}:
      rest

# the asks among fs that start a store
def Facts.starts(fs: List<&2, Types.Fact>) -> List<&2, Types.Ask>:
  match fs:
    case Nil{}:
      []
    case Con{f, rest}:
      Start.put(f, Facts.starts(rest))

# some ask of xs collides with an ask of all
def Asks.collide(+all: List<&2, Types.Ask>, xs: List<&2, Types.Ask>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{+a, rest}:
      List.any.if(
        u => Asks.collide(all, rest),
        Shared.List.some(~Types.Ask, ~Types.Ask, ~(x => y => Ask.collides(x, y)), all, a)
      )

# Facts.ok, read from the votes of the node and the starts only
def Facts.ok.fast(+name: String, +s: Plain()) -> Bool:
  +fs = Facts.list(s)
  +own = Facts.own(name, fs)
  +st = Facts.starts(fs)
  Shared.Bool.when(
    Bool,
    Ballots.clash.by(Ballots.by_step(own), own),
    u => False{},
    u => Shared.Bool.when(Bool, Asks.collide(st, st), u2 => Trust.broken(s, name), u2 => True{})
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

# the number of the ask that the fact f is or votes for; else 0
def Seq.of(f: Types.Fact) -> Nat:
  match f:
    case Types.Fact.Ask{a}:
      Ask.seq(a)
    case Types.Fact.Vote{v, st, Types.Cast.Vote{r, Types.Pick{a, pins}, b}}:
      Ask.seq(a)
    case Types.Fact.Vote{v, st, Types.Cast.Pass{r}}:
      0n

# the greatest number of an ask among fs, as an ask or in a vote
def Seq.peak(fs: List<&2, Types.Fact>) -> Nat:
  match fs:
    case Nil{}:
      0n
    case Con{Types.Fact.Ask{a}, rest}:
      Nat.max(Ask.seq(a), Seq.peak(rest))
    case Con{Types.Fact.Vote{v, st, Types.Cast.Vote{r, Types.Pick{a, pins}, b}}, rest}:
      Nat.max(Ask.seq(a), Seq.peak(rest))
    case Con{Types.Fact.Vote{v, st, Types.Cast.Pass{r}}, rest}:
      Seq.peak(rest)

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

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- measured: not in the main9/10/11/16 builds, so no driver runs it; it is said only in laws
# b holds each fact of a, and a read of b may go as far as one of a
def Facts.wider(+a: Plain(), +b: Plain()) -> Bool:
  Bool.and(
    Shared.List.holds(~Types.Fact, ~Plain(), ~Fact.held, Facts.list(a), b),
    Nat.is_le(Facts.fuel(a), Facts.fuel(b))
  )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information
