import Base
import ./shared/ledger.bend as Ledgers
import ./shared/shared/depot.bend as Depots
import ./shared/shared/quorum.bend as Quorums
import ./shared/shared/text.bend as Texts
import ./shared/shared/shared/cell.bend as Cells
import ./shared/shared/shared/code.bend as Codes
import ./shared/shared/shared/hash.bend as Hashes
import ./shared/shared/shared/seal.bend as Seals
import ./shared/shared/shared/shared.bend as Shared
import ./shared/tree.bend as Trees

# Replicas
# ========
# A replica is one holder of a replicated machine. The replicas of a machine
# hold a ledger in common (Ledgers), and every answer of a replica is a
# function of its ledger alone: so two replicas that hold the same entries
# give the same answers, whatever the order in which they got them, and a
# replica that is behind has nothing to do but take entries in.
#
# A line is a sequence of steps. The voters of a line cast ballots for its
# next step; a step that the rules of rounds decide (Round.decide), and that
# runs to the tip that it names (Line.next), is the next step of the line.
# What a line holds is a tip: its content, a tree; its log, a tree that only
# gains keys; the count of the requests that it took; and the voters of its
# next step.
#
# This file is generic: a machine gives the requests and what a request does
# (its kernel), and a ledger gives the way to keep entries.

# Machines
# --------

# a first voter of a root line: its name, and the key that signs its first
# ballot under the root
type Voter is Data:
  Voter{name: String, key: Hashes.Hash}

# the first voter o, then r
def Voter.code(o: Voter, r: List<&2, U32>) -> List<&2, U32>:
  match o:
    case Voter{n, k}:
      Codes.Code.text(n, Hashes.Hash.code(k, r))

# a first voter
def Voter.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Voter>>:
  Codes.Code.two.read(
    ~String,
    ~Hashes.Hash,
    ~Voter,
    ~Codes.Code.text.read,
    ~Hashes.Hash.code.read,
    n => k => Voter{n, k},
    ts
  )

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in a proof a second use sits in a rewrite motive or an erased argument, and the checker accepts it
# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof does not run
# bend-lint: expect-begin bend-lint-rules/performance/missed_fork@hint -- a proof does not run
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- in a proof an unused binder is a premise of the proof's own type; a proof does not run
# a first voter reads back
def Voter.code_read(
  x: Voter,
  r: List<&2, U32>
) -> {Voter.code.read(Voter.code(x, r)) == Some{Codes.Read{x, r}}: Maybe<&2, Codes.Read<Voter>>}:
  match x:
    case Voter{n, k}:
      Codes.Code.two_read(
        ~String,
        ~Hashes.Hash,
        ~Voter,
        ~Codes.Code.text.codec(),
        ~Hashes.Hash.codec(),
        a => b => Voter{a, b},
        n,
        k,
        r
      )

# the code of first voters
def Voter.codec() -> Codes.Codec(Voter):
  (Voter.code, (Voter.code.read, x => r => Voter.code_read(x, r)))

# how a request arrives: it starts a root line, with its first voters, or it
# waits on a line
type Arrival is Data:
  Arrival.Starts{voters: List<&2, Voter>}
  Arrival.Waits{line: Ledgers.Line}

# a machine: its requests; their code (two requests are the same when their
# codes are); how a request arrives; whether it changes who votes; and the
# key, in the content of a root line, of the first key of a voter
def Machine() -> Type:
  &Q: Data -> Codes.Codec(Q) & ((Q -> Arrival) & ((Q -> Bool) & (String -> List<&2, U32>)))

# the requests of the machine m
def Machine.Q(m: Machine()) -> Data:
  match m:
    case Tuple{q, r}:
      q

# the code of the requests of the machine m
def Machine.code(m: Machine()) -> Codes.Codec(Machine.Q(m)):
  match m:
    case Tuple{q, Tuple{c, r}}:
      c

# how a request of the machine m arrives
def Machine.arrival(m: Machine()) -> Machine.Q(m) -> Arrival:
  match m:
    case Tuple{q, Tuple{c, Tuple{a, r}}}:
      a

# a request of the machine m changes who votes
def Machine.governs(m: Machine()) -> Machine.Q(m) -> Bool:
  match m:
    case Tuple{q, Tuple{c, Tuple{a, Tuple{g, k}}}}:
      g

# the key of the first key of a voter, in the content of a root line of the
# machine m
def Machine.seal(m: Machine()) -> String -> List<&2, U32>:
  match m:
    case Tuple{q, Tuple{c, Tuple{a, Tuple{g, k}}}}:
      k

# The ledger of a machine
# -----------------------

# a ledger for the requests of the machine mach, and a tree whose nodes it
# keeps as data: the trees of every line are kept in the ledger itself
def Led(-mach: Machine()) -> Type:
  &x: Ledgers.Ledger(Machine.Q(mach), Machine.code(mach)) -> Trees.Tree(
    Ledgers.Kind.L(Machine.Q(mach), Ledgers.Ledger.kind(Machine.Q(mach), Machine.code(mach), x)),
    Ledgers.Kind.data(Machine.Q(mach), Ledgers.Ledger.kind(Machine.Q(mach), Machine.code(mach), x)),
    a => b => Ledgers.Kind.Grows(
      Machine.Q(mach),
      Ledgers.Ledger.kind(Machine.Q(mach), Machine.code(mach), x),
      a,
      b
    )
  )

# the kind of the ledger d
def Led.kind(-mach: Machine(), d: Led(mach)) -> Ledgers.Ledger.Kind(Machine.Q(mach)):
  match d:
    case Tuple{x, t}:
      Ledgers.Ledger.kind(Machine.Q(mach), Machine.code(mach), x)

# what the ledger d is kept as
def Led.L(-mach: Machine(), d: Led(mach)) -> Data:
  Ledgers.Kind.L(Machine.Q(mach), Led.kind(mach, d))

# the operations of the tree of the ledger d
def Led.tree(-mach: Machine(), d: Led(mach)) -> Trees.Tree.Ops(Led.L(mach, d)):
  match d:
    case Tuple{x, t}:
      Trees.Tree.ops(
        Ledgers.Kind.L(Machine.Q(mach), Ledgers.Ledger.kind(Machine.Q(mach), Machine.code(mach), x)),
        Ledgers.Kind.data(Machine.Q(mach), Ledgers.Ledger.kind(Machine.Q(mach), Machine.code(mach), x)),
        a => b => Ledgers.Kind.Grows(
          Machine.Q(mach),
          Ledgers.Ledger.kind(Machine.Q(mach), Machine.code(mach), x),
          a,
          b
        ),
        t
      )

# an entry of the machine mach
def Entry(-mach: Machine()) -> Data:
  Ledgers.Entry<Machine.Q(mach)>

# the entry that l holds under the name n
def Led.get(
  ~mach: Machine(),
  ~d: Led(mach),
  l: Led.L(mach, d),
  n: Ledgers.Name
) -> Maybe<&2, Entry(mach)>:
  Ledgers.Kind.get(Machine.Q(mach), Led.kind(mach, d))(l)(n)

# l with the entry e
def Led.add(~mach: Machine(), ~d: Led(mach), l: Led.L(mach, d), e: Entry(mach)) -> Led.L(mach, d):
  Ledgers.Kind.add(Machine.Q(mach), Led.kind(mach, d))(l)(e)

# l holds the entry e
def Led.has(~mach: Machine(), ~d: Led(mach), l: Led.L(mach, d), e: Entry(mach)) -> Bool:
  Ledgers.Kind.has(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), l, e)

# that the ledger b holds each entry that a holds
def Led.Grows(-mach: Machine(), -d: Led(mach), -a: Led.L(mach, d), -b: Led.L(mach, d)) -> Type:
  Ledgers.Kind.Grows(Machine.Q(mach), Led.kind(mach, d), a, b)

# the data of l whose hash is h
def Led.fetch(
  ~mach: Machine(),
  ~d: Led(mach),
  l: Led.L(mach, d),
  h: Hashes.Hash
) -> Maybe<&2, List<&2, U32>>:
  Ledgers.Kind.data(Machine.Q(mach), Led.kind(mach, d))(l)(h)

# l with each of the words ns as data
def Led.puts(
  ~mach: Machine(),
  ~d: Led(mach),
  ns: List<&2, List<&2, U32>>,
  l: Led.L(mach, d)
) -> Led.L(mach, d):
  match ns:
    case Nil{}:
      l
    case Con{ws, rest}:
      Led.puts(~mach, ~d, rest, Led.add(~mach, ~d, l, Ledgers.Entry.Data{ws}))

# the step that the voter cast at the place w, when it cast one
def Led.voted(
  ~mach: Machine(),
  ~d: Led(mach),
  l: Led.L(mach, d),
  w: Ledgers.Place,
  voter: String
) -> Maybe<&2, Ledgers.Step>:
  Ledgers.Kind.voted(~Machine.Q(mach), ~Led.kind(mach, d), l, w, voter)

# the vote of the voter at the place w, with the voters whose passes allow it,
# when it cast one
def Led.cast(
  ~mach: Machine(),
  ~d: Led(mach),
  l: Led.L(mach, d),
  w: Ledgers.Place,
  voter: String
) -> Maybe<&2, Ledgers.Cast>:
  Ledgers.Kind.cast(~Machine.Q(mach), ~Led.kind(mach, d), l, w, voter)

# the last vote that the voter named when it passed to the place w, when l
# holds one pass of it
def Led.passed(
  ~mach: Machine(),
  ~d: Led(mach),
  l: Led.L(mach, d),
  w: Ledgers.Place,
  voter: String
) -> Maybe<&2, Maybe<&2, Ledgers.Last>>:
  Ledgers.Kind.passed(~Machine.Q(mach), ~Led.kind(mach, d), l, w, voter)

# the step that a majority of the voters cast at the place w of l, if one did
def Led.tally(
  ~mach: Machine(),
  ~d: Led(mach),
  l: Led.L(mach, d),
  w: Ledgers.Place,
  voters: List<&2, String>
) -> Maybe<&2, Ledgers.Step>:
  Ledgers.Kind.tally(~Machine.Q(mach), ~Led.kind(mach, d), l, w, voters)

# Trees in a ledger
# -----------------

# what a read of the key k finds in the tree whose root is h, in l
def Tree.look(
  ~mach: Machine(),
  ~d: Led(mach),
  l: Led.L(mach, d),
  h: Maybe<&2, Hashes.Hash>,
  k: List<&2, U32>
) -> Trees.Look:
  Trees.Ops.look(Led.L(mach, d), Led.tree(mach, d))(l)(h)(k)

# what the tree whose root is h holds under the key k, in the data of l
def Tree.get(
  ~mach: Machine(),
  ~d: Led(mach),
  l: Led.L(mach, d),
  h: Maybe<&2, Hashes.Hash>,
  k: List<&2, U32>
) -> Maybe<&2, List<&2, U32>>:
  Trees.Look.value(Tree.look(~mach, ~d, l, h, k))

# what the tree whose root is h holds under the key k, or that it holds
# nothing there (none: l lacks a node of the tree). A kernel reads with this:
# it refuses only on what it knows, and waits for what it lacks
def Tree.find(
  ~mach: Machine(),
  ~d: Led(mach),
  l: Led.L(mach, d),
  h: Maybe<&2, Hashes.Hash>,
  k: List<&2, U32>
) -> Maybe<&2, Maybe<&2, List<&2, U32>>>:
  Trees.Look.known(Tree.look(~mach, ~d, l, h, k))

# the tree whose root is h with the key k set to the value m (none: deleted):
# its new root, and the nodes that it adds (none: l lacks a node of the tree)
def Tree.put(
  ~mach: Machine(),
  ~d: Led(mach),
  l: Led.L(mach, d),
  h: Maybe<&2, Hashes.Hash>,
  k: List<&2, U32>,
  m: Maybe<&2, List<&2, U32>>
) -> Maybe<&2, Trees.Edit>:
  Trees.Ops.put(Led.L(mach, d), Led.tree(mach, d))(l)(h)(k)(m)

# the bindings of the tree whose root is h whose keys start with p, in the
# order of their keys (none: l lacks a node of the tree)
def Tree.range(
  ~mach: Machine(),
  ~d: Led(mach),
  l: Led.L(mach, d),
  h: Maybe<&2, Hashes.Hash>,
  p: List<&2, U32>
) -> Maybe<&2, List<&2, Trees.Binding>>:
  Trees.Ops.range(Led.L(mach, d), Led.tree(mach, d))(l)(h)(p)

# the keys that the trees whose roots are a and b read differently (none: l
# lacks a node)
def Tree.diff(
  ~mach: Machine(),
  ~d: Led(mach),
  l: Led.L(mach, d),
  a: Maybe<&2, Hashes.Hash>,
  b: Maybe<&2, Hashes.Hash>
) -> Maybe<&2, List<&2, List<&2, U32>>>:
  Trees.Ops.diff(Led.L(mach, d), Led.tree(mach, d))(l)(a)(b)

# Tips
# ----

# what a line holds: the root of its content, the root of its log, the count
# of the requests that it took, and the voters of its next step. A read of the
# count or of the voters costs no node of a tree
type Tip is Data:
  Tip{
    content: Maybe<&2, Hashes.Hash>,
    log: Maybe<&2, Hashes.Hash>,
    count: U32,
    voters: List<&2, String>
  }

# the content of the tip t
def Tip.content(t: Tip) -> Maybe<&2, Hashes.Hash>:
  match t:
    case Tip{c, l, n, vs}:
      c

# the log of the tip t
def Tip.log(t: Tip) -> Maybe<&2, Hashes.Hash>:
  match t:
    case Tip{c, l, n, vs}:
      l

# the count of the requests that a line took, at the tip t
def Tip.count(t: Tip) -> U32:
  match t:
    case Tip{c, l, n, vs}:
      n

# the voters of the next step of a line at the tip t
def Tip.voters(t: Tip) -> List<&2, String>:
  match t:
    case Tip{c, l, n, vs}:
      vs

# the tip t, then r
def Tip.code(t: Tip, r: List<&2, U32>) -> List<&2, U32>:
  match t:
    case Tip{c, l, n, vs}:
      Codes.Code.maybe(
        ~Hashes.Hash,
        ~Hashes.Hash.code,
        c,
        Codes.Code.maybe(
          ~Hashes.Hash,
          ~Hashes.Hash.code,
          l,
          Codes.Code.token(n, Ledgers.Voters.code(vs, r))
        )
      )

# a tip
def Tip.code.read(ws: List<&2, U32>) -> Maybe<&2, Codes.Read<Tip>>:
  Codes.Code.four.read(
    ~Maybe<&2, Hashes.Hash>,
    ~Maybe<&2, Hashes.Hash>,
    ~U32,
    ~List<&2, String>,
    ~Tip,
    ~(m => Codes.Code.maybe.read(~Hashes.Hash, ~Hashes.Hash.code.read, m)),
    ~(m => Codes.Code.maybe.read(~Hashes.Hash, ~Hashes.Hash.code.read, m)),
    ~Codes.Code.token.read,
    ~Ledgers.Voters.code.read,
    c => l => n => vs => Tip{c, l, n, vs},
    ws
  )

# a tip reads back
def Tip.code_read(
  t: Tip,
  r: List<&2, U32>
) -> {Tip.code.read(Tip.code(t, r)) == Some{Codes.Read{t, r}}: Maybe<&2, Codes.Read<Tip>>}:
  match t:
    case Tip{c, l, n, vs}:
      Codes.Code.four_read(
        ~Maybe<&2, Hashes.Hash>,
        ~Maybe<&2, Hashes.Hash>,
        ~U32,
        ~List<&2, String>,
        ~Tip,
        ~Codes.Code.maybe.codec(~Hashes.Hash, ~Hashes.Hash.codec()),
        ~Codes.Code.maybe.codec(~Hashes.Hash, ~Hashes.Hash.codec()),
        ~Codes.Code.token.codec(),
        ~Codes.Code.list.codec(~String, ~Codes.Code.text.codec()),
        w => x => y => z => Tip{w, x, y, z},
        c,
        l,
        n,
        vs,
        r
      )

# the hash of the tip t: what a step names
def Tip.hash(t: Tip) -> Hashes.Hash:
  Hashes.Sha.hash(Tip.code(t, []))

# the tip that l holds under the hash h
def Tip.at(~mach: Machine(), ~d: Led(mach), l: Led.L(mach, d), h: Hashes.Hash) -> Maybe<&2, Tip>:
  Codes.Code.whole.of(~Tip, ~Tip.code, ~Tip.code.read, Led.fetch(~mach, ~d)(l)(h))

# the tip that a step names, in l (none: the step names none, or l lacks it)
def Tip.of(
  ~mach: Machine(),
  ~d: Led(mach),
  l: Led.L(mach, d),
  m: Maybe<&2, Hashes.Hash>
) -> Maybe<&2, Tip>:
  Maybe.bind(&2, Hashes.Hash, Tip, m, h => Tip.at(~mach, ~d, l, h))

# Logs
# ----
# The log of a line only gains keys (Run.add is the one def that writes it):
# the outcome of each request, each taken request by its number, each label,
# and the first tip of each sub line.

# the key of the outcome of the request i
def Log.out(i: Ledgers.Id) -> List<&2, U32>:
  2 <> Ledgers.Id.code(i, [])

# the key of the request that a line took as the number n
def Log.taken(n: U32) -> List<&2, U32>:
  [3, n]

# the key of the label m
def Log.label(m: String) -> List<&2, U32>:
  4 <> Codes.Code.text(m, [])

# the key of the first tip of the sub line of the name b, in the log of its
# root line
def Log.start(b: String) -> List<&2, U32>:
  5 <> Codes.Code.text(b, [])

# the outcome of a request ID: the entry that the line gave it to (its hash),
# and what the line did with it: it refused it as stale, or took it as the
# number of a count. Another entry with the same ID has no outcome: the ID
# names one request for good
type Out is Data:
  Out.Stale{ask: Hashes.Hash}
  Out.Taken{ask: Hashes.Hash, number: U32}

# the outcome o, then r
def Out.code(o: Out, r: List<&2, U32>) -> List<&2, U32>:
  match o:
    case Out.Stale{a}:
      0 <> Hashes.Hash.code(a, r)
    case Out.Taken{a, n}:
      1 <> n <> Hashes.Hash.code(a, r)

# an outcome
def Out.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Out>>:
  match ts:
    case Con{0, r}:
      Codes.Code.one.read(~Hashes.Hash, ~Out, ~Hashes.Hash.code.read, a => Out.Stale{a}, r)
    case Con{1, Con{n, r}}:
      Codes.Code.one.read(~Hashes.Hash, ~Out, ~Hashes.Hash.code.read, a => Out.Taken{a, n}, r)
    case _:
      None{}

# an outcome reads back
def Out.code_read(
  o: Out,
  r: List<&2, U32>
) -> {Out.code.read(Out.code(o, r)) == Some{Codes.Read{o, r}}: Maybe<&2, Codes.Read<Out>>}:
  match o:
    case Out.Stale{a}:
      Codes.Code.one_read(~Hashes.Hash, ~Out, ~Hashes.Hash.codec(), x => Out.Stale{x}, a, r)
    case Out.Taken{a, n}:
      Codes.Code.one_read(~Hashes.Hash, ~Out, ~Hashes.Hash.codec(), x => Out.Taken{x, n}, a, r)

# a taken request: its ID, and the root of the content after it
type Taken is Data:
  Taken{id: Ledgers.Id, root: Maybe<&2, Hashes.Hash>}

# the taken request x, then r
def Taken.code(x: Taken, r: List<&2, U32>) -> List<&2, U32>:
  match x:
    case Taken{i, h}:
      Ledgers.Id.code(i, Codes.Code.maybe(~Hashes.Hash, ~Hashes.Hash.code, h, r))

# a taken request
def Taken.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Taken>>:
  Codes.Code.two.read(
    ~Ledgers.Id,
    ~Maybe<&2, Hashes.Hash>,
    ~Taken,
    ~Ledgers.Id.code.read,
    ~(m => Codes.Code.maybe.read(~Hashes.Hash, ~Hashes.Hash.code.read, m)),
    i => h => Taken{i, h},
    ts
  )

# a taken request reads back
def Taken.code_read(
  x: Taken,
  r: List<&2, U32>
) -> {Taken.code.read(Taken.code(x, r)) == Some{Codes.Read{x, r}}: Maybe<&2, Codes.Read<Taken>>}:
  match x:
    case Taken{i, h}:
      Codes.Code.two_read(
        ~Ledgers.Id,
        ~Maybe<&2, Hashes.Hash>,
        ~Taken,
        ~Ledgers.Id.codec(),
        ~Codes.Code.maybe.codec(~Hashes.Hash, ~Hashes.Hash.codec()),
        a => b => Taken{a, b},
        i,
        h,
        r
      )

# the ID of the taken request x
def Taken.id(x: Taken) -> Ledgers.Id:
  match x:
    case Taken{i, r}:
      i

# what the log of the tip t holds under the key k, in l
def Tip.get(
  ~mach: Machine(),
  ~d: Led(mach),
  l: Led.L(mach, d),
  t: Tip,
  k: List<&2, U32>
) -> Maybe<&2, List<&2, U32>>:
  Tree.get(~mach, ~d, l, Tip.log(t), k)

# what the log of the tip t holds under the key k, or that it holds nothing
# there (none: l lacks a node of the log). A run reads with this: it decides
# only on what it knows, and waits for what it lacks
def Tip.find(
  ~mach: Machine(),
  ~d: Led(mach),
  l: Led.L(mach, d),
  t: Tip,
  k: List<&2, U32>
) -> Maybe<&2, Maybe<&2, List<&2, U32>>>:
  Tree.find(~mach, ~d, l, Tip.log(t), k)

# the value of A whose code a known read m gives, or that there is none
# (none: the read cannot tell)
def Tip.known(
  ~A: Data,
  ~enc: A -> List<&2, U32> -> List<&2, U32>,
  ~dec: List<&2, U32> -> Maybe<&2, Codes.Read<A>>,
  m: Maybe<&2, Maybe<&2, List<&2, U32>>>
) -> Maybe<&2, Maybe<&2, A>>:
  match m:
    case None{}:
      None{}
    case Some{w}:
      Some{Codes.Code.whole.of(~A, ~enc, ~dec, w)}

# the outcome of the request ID i at the tip t
def Tip.out(~mach: Machine(), ~d: Led(mach), l: Led.L(mach, d), t: Tip, i: Ledgers.Id) -> Maybe<&2, Out>:
  Codes.Code.whole.of(~Out, ~Out.code, ~Out.code.read, Tip.get(~mach, ~d, l, t, Log.out(i)))

# the request that the line took as the number n, at the tip t
def Tip.taken(~mach: Machine(), ~d: Led(mach), l: Led.L(mach, d), t: Tip, n: U32) -> Maybe<&2, Taken>:
  Codes.Code.whole.of(~Taken, ~Taken.code, ~Taken.code.read, Tip.get(~mach, ~d, l, t, Log.taken(n)))

# the request that the label m names, at the tip t
def Tip.label(
  ~mach: Machine(),
  ~d: Led(mach),
  l: Led.L(mach, d),
  t: Tip,
  m: String
) -> Maybe<&2, Ledgers.Id>:
  Codes.Code.whole.of(~Ledgers.Id, ~Ledgers.Id.code, ~Ledgers.Id.code.read, Tip.get(~mach, ~d, l, t, Log.label(m)))

# Rounds
# ------
# The voters of a line decide its next step in rounds. One voter proposes in
# each round; a round decides the step that a majority cast there, when the
# rules allow it. A voter that gives up a round passes to the next one, and
# names its last vote: so a later round decides no other step than an earlier
# one did.

# the vote m of the round r, as a last vote, else what rest gives
def Last.or(
  r: Nat,
  m: Maybe<&2, Ledgers.Step>,
  rest: Unit -> Maybe<&2, Ledgers.Last>
) -> Maybe<&2, Ledgers.Last>:
  match m:
    case Some{v}:
      Some{Ledgers.Last{r, v}}
    case None{}:
      rest(Unit{})

# the last vote of the voter n at the height h of the line c, in a round up to
# k, if it cast one
def Last.mine(
  ~mach: Machine(),
  ~d: Led(mach),
  +n: String,
  +l: Led.L(mach, d),
  +c: Ledgers.Line,
  +h: U32,
  k: Nat
) -> Maybe<&2, Ledgers.Last>:
  match k:
    case 0n:
      Last.or(0n, Led.voted(~mach, ~d, l, Ledgers.Place{c, h, 0n}, n), u => None{})
    case 1n+(+p):
      Last.or(
        1n+p,
        Led.voted(~mach, ~d, l, Ledgers.Place{c, h, 1n+p}, n),
        u => Last.mine(~mach, ~d, n, l, c, h, p)
      )

# the last vote of the voter n at the height h of the line c, in a round below
# r, if it cast one
def Last.below(
  ~mach: Machine(),
  ~d: Led(mach),
  n: String,
  l: Led.L(mach, d),
  c: Ledgers.Line,
  h: U32,
  r: Nat
) -> Maybe<&2, Ledgers.Last>:
  match r:
    case 0n:
      None{}
    case 1n+p:
      Last.mine(~mach, ~d, n, l, c, h, p)

# the voter whose turn it is to propose the step in the round r of the height
# h, among the voters os: each in turn, by the height and the round. One voter
# proposes a step and the others cast for the same step, so the voters do not
# split over what waits at each of them
def Voters.turn(+os: List<&2, String>, h: U32, r: Nat) -> Maybe<&2, String>:
  List.get(
    &2,
    String,
    os,
    U32.to_nat(U32.mod(U32.add(h, U32.from_nat(r)), U32.from_nat(List.length(&2, String, os))))
  )

# the act m is a vote for the step v, and rest holds of the voters whose passes
# the vote names
def Cast.casts(m: Maybe<&2, Ledgers.Cast>, v: Ledgers.Step, rest: List<&2, String> -> Bool) -> Bool:
  match m:
    case Some{Ledgers.Cast.Vote{x, from}}:
      List.all.if(u => rest(from), Ledgers.Step.is_eq(x, v))
    case y:
      False{}

# the last vote of the higher round of a and b
def Last.newer(a: Maybe<&2, Ledgers.Last>, b: Maybe<&2, Ledgers.Last>) -> Maybe<&2, Ledgers.Last>:
  match a b:
    case None{} y:
      y
    case Some{x} None{}:
      Some{x}
    case Some{Ledgers.Last{+r1, v1}} Some{Ledgers.Last{+r2, v2}}:
      Shared.Bool.when(
        Maybe<&2, Ledgers.Last>,
        Nat.is_lt(r1, r2),
        u => Some{Ledgers.Last{r2, v2}},
        u => Some{Ledgers.Last{r1, v1}}
      )

# the last vote that a pass names, flattened
def Passed.last(m: Maybe<&2, Maybe<&2, Ledgers.Last>>) -> Maybe<&2, Ledgers.Last>:
  match m:
    case Some{x}:
      x
    case None{}:
      None{}

# the last vote of the highest round that the passes of the voters from to the
# place w name, if any names one
def Passes.last(
  ~mach: Machine(),
  ~d: Led(mach),
  +l: Led.L(mach, d),
  +w: Ledgers.Place,
  from: List<&2, String>
) -> Maybe<&2, Ledgers.Last>:
  match from:
    case Nil{}:
      None{}
    case Con{o, r}:
      Last.newer(
        Passed.last(Led.passed(~mach, ~d, l, w, o)),
        Passes.last(~mach, ~d, l, w, r)
      )

# the voters from are a majority of the voters os
def Voters.major(os: List<&2, String>, +from: List<&2, String>) -> Bool:
  Nat.is_lt(
    List.length(&2, String, os),
    Nat.add(List.length(&2, String, from), List.length(&2, String, from))
  )

# the last vote m, if any, is for the step v
def Last.is(m: Maybe<&2, Ledgers.Last>, v: Ledgers.Step) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{Ledgers.Last{r, x}}:
      Ledgers.Step.is_eq(x, v)

# the last vote m is of the round r
def Last.in(m: Maybe<&2, Ledgers.Last>, r: Nat) -> Bool:
  match m:
    case Some{Ledgers.Last{k, v}}:
      Nat.is_eq(k, r)
    case None{}:
      False{}

# rest holds of the round of the last vote m, if there is one
def Last.holds(m: Maybe<&2, Ledgers.Last>, rest: Nat -> Bool) -> Bool:
  match m:
    case Some{Ledgers.Last{r, v}}:
      rest(r)
    case None{}:
      True{}

# the ledger l holds the pass to the place w of each of the voters from
def Passed.all(
  ~mach: Machine(),
  ~d: Led(mach),
  +l: Led.L(mach, d),
  +w: Ledgers.Place,
  from: List<&2, String>
) -> Bool:
  match from:
    case Nil{}:
      True{}
    case Con{o, r}:
      List.all.if(
        u => Passed.all(~mach, ~d, l, w, r),
        Maybe.is_some(
          &2,
          Maybe<&2, Ledgers.Last>,
          Led.passed(~mach, ~d, l, w, o)
        )
      )

# the voters from are some of the voters os, each once, in their order
def Voters.sub(os: List<&2, String>, from: List<&2, String>) -> Bool:
  match os from:
    case Nil{} Nil{}:
      True{}
    case Nil{} Con{f, fs}:
      False{}
    case Con{o, r} Nil{}:
      True{}
    case Con{o, +r} Con{+f, +fs}:
      Shared.Bool.when(Bool, String.eq(f, o), u => Voters.sub(r, fs), u => Voters.sub(r, f <> fs))

# the ledger l holds the pass to the place w of each of the voters from, and they
# are some of the voters os, and a majority of them
def Passed.major(
  ~mach: Machine(),
  ~d: Led(mach),
  l: Led.L(mach, d),
  w: Ledgers.Place,
  +os: List<&2, String>,
  +from: List<&2, String>
) -> Bool:
  List.all.if(
    u => List.all.if(u2 => Voters.major(os, from), Voters.sub(os, from)),
    Passed.all(~mach, ~d, l, w, from)
  )

# the last vote l names no other step than v in the round r
def Last.allows(+l: Maybe<&2, Ledgers.Last>, r: Nat, v: Ledgers.Step) -> Bool:
  List.any.if(u => Last.is(l, v), Bool.not(Last.in(l, r)))

# each last vote of the round r that the passes of the voters from to the place
# w name is for the step v
def Passes.agree(
  ~mach: Machine(),
  ~d: Led(mach),
  +l: Led.L(mach, d),
  +w: Ledgers.Place,
  from: List<&2, String>,
  +r: Nat,
  +v: Ledgers.Step
) -> Bool:
  match from:
    case Nil{}:
      True{}
    case Con{o, rest}:
      List.all.if(
        u => Passes.agree(~mach, ~d, l, w, rest, r, v),
        Last.allows(
          Passed.last(Led.passed(~mach, ~d, l, w, o)),
          r,
          v
        )
      )

# what the first of the voters from whose pass to the round r names a vote of
# the round k did in the round k, at the height h of the line c (none: no pass
# names a vote of k, or l does not hold the ballot of that voter in k)
def Passes.act(
  ~mach: Machine(),
  ~d: Led(mach),
  +l: Led.L(mach, d),
  +c: Ledgers.Line,
  +h: U32,
  +r: Nat,
  from: List<&2, String>,
  +k: Nat
) -> Maybe<&2, Ledgers.Cast>:
  match from:
    case Nil{}:
      None{}
    case Con{+o, rest}:
      Shared.Bool.when(
        Maybe<&2, Ledgers.Cast>,
        Last.in(
          Passed.last(
            Led.passed(~mach, ~d, l, Ledgers.Place{c, h, r},
              o
            )
          ),
          k
        ),
        u => Led.cast(~mach, ~d, l, Ledgers.Place{c, h, k}, o),
        u => Passes.act(~mach, ~d, l, c, h, r, rest, k)
      )

# Step.allowed in the round r of the height h of the line c. Each step back to
# the round of a named vote takes one of k: a pass names a round below its own,
# so the number of the round is enough
def Step.allowed.in(
  ~mach: Machine(),
  ~d: Led(mach),
  +l: Led.L(mach, d),
  +c: Ledgers.Line,
  +h: U32,
  +os: List<&2, String>,
  +v: Ledgers.Step,
  k: Nat,
  r: Nat,
  +from: List<&2, String>
) -> Bool:
  match k r:
    case 0n 0n:
      True{}
    case 1n+j 0n:
      True{}
    case 0n 1n+p:
      False{}
    case 1n+(+j) 1n+(+p):
      +w = {Ledgers.Place{c, h, 1n+p}: Ledgers.Place}
      List.all.if(
        u => Last.holds(
          Passes.last(~mach, ~d, l, w, from),
          +t => List.all.if(
            u2 => Cast.casts(
              Passes.act(~mach, ~d, l, c, h, 1n+p, from, t),
              v,
              +f => Step.allowed.in(~mach, ~d, l, c, h, os, v, j, t, f)
            ),
            Passes.agree(~mach, ~d, l, w, from, t, v)
          )
        ),
        Passed.major(~mach, ~d, l, w, os, from)
      )

# the passes of the voters from allow a vote for the step v at the place w of
# the voters os. In the first round, any step. Later: the voter holds the pass
# to w of each of them, and they are voters and a majority. When their passes
# name a last vote, take the highest round that they name: each last vote of
# that round is for v, and v was allowed there: the voter holds the vote for v,
# in that round, of the first of them that names it, and the passes that this
# vote names allow v in that round. So an allowed vote leads back, round by
# round, to a vote that a majority left free
def Step.allowed(
  ~mach: Machine(),
  ~d: Led(mach),
  l: Led.L(mach, d),
  w: Ledgers.Place,
  os: List<&2, String>,
  v: Ledgers.Step,
  from: List<&2, String>
) -> Bool:
  match w:
    case Ledgers.Place{c, h, +r}:
      Step.allowed.in(~mach, ~d, l, c, h, os, v, r, r, from)

# the step m, if any, else the step that rest gives
def Step.first(
  m: Maybe<&2, Ledgers.Step>,
  rest: Unit -> Maybe<&2, Ledgers.Step>
) -> Maybe<&2, Ledgers.Step>:
  match m:
    case Some{v}:
      Some{v}
    case None{}:
      rest(Unit{})

# the step v, when the voter p cast it at the place w with passes that allow
# it there, for the voters os (Step.allowed)
def Round.led(
  ~mach: Machine(),
  ~d: Led(mach),
  +l: Led.L(mach, d),
  +w: Ledgers.Place,
  os: List<&2, String>,
  +v: Ledgers.Step,
  p: String
) -> Maybe<&2, Ledgers.Step>:
  Shared.Maybe.when(
    Ledgers.Step,
    Cast.casts(Led.cast(~mach, ~d, l, w, p), v, f => Step.allowed(~mach, ~d, l, w, os, v, f)),
    u => Some{v}
  )

# the step that the voters os decided in the round r of the height h of the
# line c, if they did: a majority of them cast it there, and so did the voter
# whose turn it is, with passes that allow it. So a round decides only a step
# that the rules of rounds allow, and the rounds of a height decide one step
# (Height.One)
def Round.decide(
  ~mach: Machine(),
  ~d: Led(mach),
  +l: Led.L(mach, d),
  +c: Ledgers.Line,
  +h: U32,
  +os: List<&2, String>,
  +r: Nat
) -> Maybe<&2, Ledgers.Step>:
  Maybe.bind(
    &2,
    Ledgers.Step,
    Ledgers.Step,
    Led.tally(~mach, ~d, l, Ledgers.Place{c, h, r}, os),
    +v => Maybe.bind(
      &2,
      String,
      Ledgers.Step,
      Voters.turn(os, h, r),
      p => Round.led(~mach, ~d, l, Ledgers.Place{c, h, r}, os, v, p)
    )
  )

# the step that the voters os decided at the height h of the line c, in a
# round up to k, the highest first, if they did. The rounds of a height decide
# one step (Height.One), so the order does not matter
def Height.decide(
  ~mach: Machine(),
  ~d: Led(mach),
  +l: Led.L(mach, d),
  +c: Ledgers.Line,
  +h: U32,
  +os: List<&2, String>,
  k: Nat
) -> Maybe<&2, Ledgers.Step>:
  match k:
    case 0n:
      Round.decide(~mach, ~d, l, c, h, os, 0n)
    case 1n+(+p):
      Step.first(Round.decide(~mach, ~d, l, c, h, os, 1n+p), u => Height.decide(~mach, ~d, l, c, h, os, p))

# that a pass names the last vote of its voter below its round: a voter that
# passed to a round casts no vote below it
def Rounds.Last(
  -mach: Machine(),
  -d: Led(mach),
  -l: Led.L(mach, d),
  -c: Ledgers.Line,
  -h: U32
) -> Type:
  @r: Nat -> @q: String -> @x: Maybe<
    &2,
    Ledgers.Last> -> {
    Led.passed(~mach, ~d, l, Ledgers.Place{c, h, r}, q) == Some{x}: Maybe<&2, Maybe<&2, Ledgers.Last>>
  } -> {x == Last.below(~mach, ~d, q, l, c, h, r): Maybe<&2, Ledgers.Last>}

# Trust
# -----
# What the voters of a line are trusted for, and nothing else: a voter casts
# one vote at a place and one pass to it (Led.Single), and its pass names its
# last vote (Rounds.Last). A ledger whose ballots obey both is honest. No law
# asks more of a voter, and no law asks anything of another sender.

# c is a vote
def Cast.is_vote(c: Ledgers.Cast) -> Bool:
  match c:
    case Ledgers.Cast.Vote{v, from}:
      True{}
    case Ledgers.Cast.Pass{p}:
      False{}

# that a voter cast one vote at a place, and one pass to it: two ballots of
# l that are of one voter, at one place, and of one kind, cast the same
def Led.Single(-mach: Machine(), -d: Led(mach), -l: Led.L(mach, d)) -> Type:
  @a: Ledgers.Ballot -> @b: Ledgers.Ballot -> {
    Led.has(~mach, ~d, l, Ledgers.Entry.Ballot{a}) == True{}: Bool
  } -> {
    Led.has(~mach, ~d, l, Ledgers.Entry.Ballot{b}) == True{}: Bool
  } -> {
    Ledgers.Ballot.is_at(b, Ledgers.Ballot.at(a), Ledgers.Ballot.voter(a)) == True{}: Bool
  } -> {
    Cast.is_vote(Ledgers.Ballot.cast(a)) == Cast.is_vote(Ledgers.Ballot.cast(b)): Bool
  } -> {Ledgers.Ballot.cast(a) == Ledgers.Ballot.cast(b): Ledgers.Cast}

# the ballots among the entries es
def Led.ballots.of(-Q: Data, es: List<&2, Ledgers.Entry<Q>>) -> List<&2, Ledgers.Ballot>:
  match es:
    case Nil{}:
      []
    case Con{Ledgers.Entry.Ballot{b}, r}:
      b <> Led.ballots.of(Q, r)
    case Con{e, r}:
      Led.ballots.of(Q, r)

# the ballots of l
def Led.ballots(~mach: Machine(), ~d: Led(mach), l: Led.L(mach, d)) -> List<&2, Ledgers.Ballot>:
  Led.ballots.of(Machine.Q(mach), Ledgers.Kind.entries(~Machine.Q(mach), ~Led.kind(mach, d), l))

# a and b do not break the promise of one vote and one pass: unless they are
# of one voter, at one place, and of one kind, they cast the same
def Ballots.agree(+a: Ledgers.Ballot, +b: Ledgers.Ballot) -> Bool:
  Bool.or(
    Bool.not(
      Bool.and(
        Ledgers.Ballot.is_at(b, Ledgers.Ballot.at(a), Ledgers.Ballot.voter(a)),
        Shared.Bool.is_eq(Cast.is_vote(Ledgers.Ballot.cast(a)), Cast.is_vote(Ledgers.Ballot.cast(b)))
      )
    ),
    Ledgers.Cast.is_eq(Ledgers.Ballot.cast(a), Ledgers.Ballot.cast(b))
  )

# the ballot a agrees with each of bs
def Ballots.agree_all(bs: List<&2, Ledgers.Ballot>, +a: Ledgers.Ballot) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case Con{b, r}:
      List.all.if(u => Ballots.agree_all(r, a), Ballots.agree(a, b))

# each ballot of as agrees with each of bs
def Ballots.single(as: List<&2, Ledgers.Ballot>, +bs: List<&2, Ledgers.Ballot>) -> Bool:
  match as:
    case Nil{}:
      True{}
    case Con{a, r}:
      List.all.if(u => Ballots.single(r, bs), Ballots.agree_all(bs, a))

# the pass p of the voter q at the place w, if b is one, names the last vote
# of q below its round
def Ballot.last.at(
  ~mach: Machine(),
  ~d: Led(mach),
  +l: Led.L(mach, d),
  q: String,
  w: Ledgers.Place,
  p: Maybe<&2, Maybe<&2, Ledgers.Last>>
) -> Bool:
  match w p:
    case x None{}:
      True{}
    case Ledgers.Place{c, h, rd} Some{y}:
      Ledgers.Last.is_eq(y, Last.below(~mach, ~d, q, l, c, h, rd))

# the pass b, if it is one, names the last vote of its voter below its round
def Ballot.last(~mach: Machine(), ~d: Led(mach), +l: Led.L(mach, d), +b: Ledgers.Ballot) -> Bool:
  Ballot.last.at(~mach, ~d, l, Ledgers.Ballot.voter(b), Ledgers.Ballot.at(b), Ledgers.Ballot.pass(b))

# the ballots bs of l: each pass names the last vote of its voter
def Ballots.last(~mach: Machine(), ~d: Led(mach), bs: List<&2, Ledgers.Ballot>, +l: Led.L(mach, d)) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case Con{b, r}:
      List.all.if(u => Ballots.last(~mach, ~d, r, l), Ballot.last(~mach, ~d, l, b))

# the ballots of l keep both promises: a check, so a law can use it as often
# as it needs
def Led.honest(~mach: Machine(), ~d: Led(mach), +l: Led.L(mach, d)) -> Bool:
  +bs = Led.ballots(~mach, ~d, l)
  List.all.if(u => Ballots.last(~mach, ~d, bs, l), Ballots.single(bs, bs))

# that the ballots of l are those of voters that keep their two promises
def Led.Honest(-mach: Machine(), -d: Led(mach), -l: Led.L(mach, d)) -> Type:
  Led.Single(mach, d, l) & (@c: Ledgers.Line -> @h: U32 -> Rounds.Last(mach, d, l, c, h))

# Reads of a log by number
# ------------------------
# A line takes requests one after another: the log holds each by its number.

# the root of the content of the taken request x
def Taken.root(x: Taken) -> Maybe<&2, Hashes.Hash>:
  match x:
    case Taken{i, r}:
      r

# the root of the content that the outcome o names at the tip t (none: the
# outcome is a refusal, or l lacks a node)
def Out.root(~mach: Machine(),
  ~d: Led(mach), l: Led.L(mach, d), t: Tip, o: Out) -> Maybe<&2, Maybe<&2, Hashes.Hash>>:
  match o:
    case Out.Stale{a}:
      None{}
    case Out.Taken{a, n}:
      Maybe.bind(
        &2,
        Taken,
        Maybe<&2, Hashes.Hash>,
        Tip.taken(~mach, ~d, l, t, n),
        x => Some{Taken.root(x)}
      )

# the root of the content of the version of the request i, at the tip t of
# its line (none: the line did not take it, or l lacks a node)
def Tip.version(
  ~mach: Machine(),
  ~d: Led(mach),
  +l: Led.L(mach, d),
  +t: Tip,
  i: Ledgers.Id
) -> Maybe<&2, Maybe<&2, Hashes.Hash>>:
  Maybe.bind(
    &2,
    Out,
    Maybe<&2, Hashes.Hash>,
    Tip.out(~mach, ~d, l, t, i),
    o => Out.root(~mach, ~d, l, t, o)
  )

# the IDs of the taken requests xs
def Taken.ids(xs: List<&2, Taken>) -> List<&2, Ledgers.Id>:
  match xs:
    case Nil{}:
      []
    case Con{Taken{i, r}, rest}:
      i <> Taken.ids(rest)

# the taken request x, if any, before what rest gives; nothing after a
# missing one
def Taken.con(m: Maybe<&2, Taken>, rest: Unit -> List<&2, Taken>) -> List<&2, Taken>:
  match m:
    case None{}:
      []
    case Some{x}:
      x <> rest(Unit{})

# k versions from the number n, in order, at the tip t
def Tip.versions(~mach: Machine(),
  ~d: Led(mach), k: Nat, +l: Led.L(mach, d), +t: Tip, +n: U32) -> List<&2, Taken>:
  match k:
    case 0n:
      []
    case 1n+p:
      Taken.con(
        Tip.taken(~mach, ~d, l, t, n),
        u => Tip.versions(~mach, ~d, p, l, t, U32.inc(n))
      )

# the ID of the newest version at the tip t
def Tip.newest(~mach: Machine(),
  ~d: Led(mach), l: Led.L(mach, d), +t: Tip) -> Maybe<&2, Ledgers.Id>:
  Shared.Maybe.when(
    Ledgers.Id,
    Bool.not(U32.is_eq(Tip.count(t), 0)),
    u => Maybe.bind(
      &2,
      Taken,
      Ledgers.Id,
      Tip.taken(~mach, ~d, l, t, U32.sub(Tip.count(t), 1)),
      x => Some{Taken.id(x)}
    )
  )

# the root of the content before the version of the number n, at the tip t:
# the empty tree before the first one
def Tip.before(~mach: Machine(),
  ~d: Led(mach), l: Led.L(mach, d), t: Tip, +n: U32) -> Maybe<&2, Maybe<&2, Hashes.Hash>>:
  Shared.Bool.when(
    Maybe<&2, Maybe<&2, Hashes.Hash>>,
    U32.is_eq(n, 0),
    u => Some{None{}},
    u => Maybe.bind(
      &2,
      Taken,
      Maybe<&2, Hashes.Hash>,
      Tip.taken(~mach, ~d, l, t, U32.sub(n, 1)),
      x => Some{Taken.root(x)}
    )
  )

# the time of the request of the entry m (none: it is not a request)
def Entry.time(-mach: Machine(), m: Maybe<&2, Ledgers.Entry<Machine.Q(mach)>>) -> String:
  match m:
    case Some{Ledgers.Entry.Ask{i, time, q}}:
      time
    case _:
      ""

# the time of the request that the outcome m is of, in l
def Out.time(~mach: Machine(),
  ~d: Led(mach), l: Led.L(mach, d), m: Maybe<&2, Out>) -> String:
  match m:
    case Some{Out.Taken{a, n}}:
      Entry.time(mach, Led.get(~mach, ~d, l, Ledgers.Name.Ask{a}))
    case _:
      ""

# Kernels
# -------
# A kernel says what a request does to a line. It reads the ledger and gives
# an act: data to add and a result, and nothing else. So a kernel cannot
# change a log, a ballot or a request, whatever it gives.

# what a request does to a line: it is refused as stale; it labels the newest
# taken request; it is taken, with the root of the content after it, the
# nodes that the content adds, and the voters that it gives, if any; or it
# opens the sub line of a name, with its first tip and the nodes of that tip
type Act is Data:
  Act.Stale{}
  Act.Label{label: String}
  Act.Taken{
    voters: Maybe<&2, List<&2, String>>,
    root: Maybe<&2, Hashes.Hash>,
    nodes: List<&2, List<&2, U32>>
  }
  Act.Opens{sub: String, tip: Tip, nodes: List<&2, List<&2, U32>>}

# what a request does: the act of the request of an ID on a line, at a tip, by
# what the ledger holds (none: wait, the ledger lacks what the act reads)
def Kernel.Change(-mach: Machine(), -d: Led(mach)) -> Type:
  Led.L(mach, d) -> Tip -> Ledgers.Line -> Ledgers.Id -> Machine.Q(mach) -> Maybe<&2, Act>

# that an act stays as the ledger grows: a kernel reads the ledger and the
# tip that it is given, waits for what it lacks, and does not answer on what
# it cannot read. So every replica that runs a request gets the same act
def Kernel.Stable(-mach: Machine(), -d: Led(mach), -f: Kernel.Change(mach, d)) -> Type:
  @t: Tip -> @c: Ledgers.Line -> @i: Ledgers.Id -> @q: Machine.Q(mach) -> Shared.Read.Stable(
    Led.L(mach, d),
    a => b => Led.Grows(mach, d, a, b),
    Act,
    l => f(l)(t)(c)(i)(q)
  )

# a request, with its ID and its time
type Request<-Q: Data> is Data:
  Request{id: Ledgers.Id, time: String, ask: Q}

# the request, if any, that a replica asks by itself after a line moves
def Kernel.Follow(-mach: Machine(), -d: Led(mach)) -> Type:
  Led.L(mach, d) -> Ledgers.Line -> Maybe<&2, Request<Machine.Q(mach)>>

# the kernel of a machine: what a request does, the proof that its acts stay
# as the ledger grows, and what a replica asks by itself
def Kernel(-mach: Machine(), -d: Led(mach)) -> Type:
  &f: Kernel.Change(mach, d) -> Kernel.Stable(mach, d, f) & Kernel.Follow(mach, d)

# what a request does, by the kernel k
def Kernel.change(-mach: Machine(), -d: Led(mach), k: Kernel(mach, d)) -> Kernel.Change(mach, d):
  match k:
    case Tuple{f, r}:
      f

# what a replica asks by itself, by the kernel k
def Kernel.follow(-mach: Machine(), -d: Led(mach), k: Kernel(mach, d)) -> Kernel.Follow(mach, d):
  match k:
    case Tuple{f, Tuple{s, w}}:
      w

# Steps
# -----
# A step runs its requests in order from a tip. Each request gets one
# outcome in the log; a request ID that has one is skipped, so a request
# counts once.

# a run: the ledger with the data that the run added, and the tip so far
type Run<-L: Data> is Data:
  Run{ledger: L, tip: Tip, added: List<&2, List<&2, U32>>}

# the ledger of the run r
def Run.ledger(-L: Data, r: Run<L>) -> L:
  match r:
    case Run{l, t, a}:
      l

# the tip of the run r
def Run.tip(-L: Data, r: Run<L>) -> Tip:
  match r:
    case Run{l, t, a}:
      t

# the nodes that the run r added, each as words: a line moves only once its
# ledger holds them
def Run.added(-L: Data, r: Run<L>) -> List<&2, List<&2, U32>>:
  match r:
    case Run{l, t, a}:
      a

# the tip t with the log h (none: the empty log)
def Tip.logged(t: Tip, h: Maybe<&2, Hashes.Hash>) -> Tip:
  match t:
    case Tip{c, old, n, vs}:
      Tip{c, h, n, vs}

# the run on l at the tip t, which added the nodes a, with the new log p
def Run.logged(
  ~mach: Machine(),
  ~d: Led(mach),
  l: Led.L(mach, d),
  t: Tip,
  a: List<&2, List<&2, U32>>,
  p: Maybe<&2, Trees.Edit>
) -> Maybe<&2, Run<Led.L(mach, d)>>:
  match p:
    case None{}:
      None{}
    case Some{+x}:
      Some{
        Run{
          Led.puts(~mach, ~d, Trees.Edit.nodes(x), l),
          Tip.logged(t, Trees.Edit.root(x)),
          List.append(&2, List<&2, U32>, Trees.Edit.nodes(x), a)
        }
      }

# Run.add once a read of the key in the log tells what it holds (m; none: the
# ledger lacks a node, so the run waits)
def Run.add.at(
  ~mach: Machine(),
  ~d: Led(mach),
  r: Run<Led.L(mach, d)>,
  k: List<&2, U32>,
  x: List<&2, U32>,
  m: Maybe<&2, Maybe<&2, List<&2, U32>>>
) -> Maybe<&2, Run<Led.L(mach, d)>>:
  match r m:
    case Run{+l, +t, a} Some{None{}}:
      Run.logged(~mach, ~d, l, t, a, Tree.put(~mach, ~d, l, Tip.log(t), k, Some{x}))
    case y Some{Some{old}}:
      None{}
    case y None{}:
      None{}

# the run r with the new key k of its log set to x (none: the log holds k, or
# the ledger lacks a node). A log only gains keys: no other def writes a log
def Run.add(
  ~mach: Machine(),
  ~d: Led(mach),
  +r: Run<Led.L(mach, d)>,
  +k: List<&2, U32>,
  x: List<&2, U32>
) -> Maybe<&2, Run<Led.L(mach, d)>>:
  Run.add.at(
    ~mach,
    ~d,
    r,
    k,
    x,
    Tip.find(~mach, ~d, Run.ledger(Led.L(mach, d), r), Run.tip(Led.L(mach, d), r), k)
  )

# the run r, after it refused the request i, whose entry is a, as stale
def Step.stale(
  ~mach: Machine(),
  ~d: Led(mach),
  r: Run<Led.L(mach, d)>,
  i: Ledgers.Id,
  a: Hashes.Hash
) -> Maybe<&2, Run<Led.L(mach, d)>>:
  Run.add(~mach, ~d, r, Log.out(i), Out.code(Out.Stale{a}, []))

# the tip t one request on, with the voters that the request gives, if any
def Tip.next(t: Tip, vs: Maybe<&2, List<&2, String>>) -> Tip:
  match t:
    case Tip{c, l, n, old}:
      Tip{c, l, U32.inc(n), Maybe.default(&2, List<&2, String>, vs, old)}

# the run r one request on (Tip.next)
def Run.next(-L: Data, r: Run<L>, vs: Maybe<&2, List<&2, String>>) -> Run<L>:
  match r:
    case Run{l, t, a}:
      Run{l, Tip.next(t, vs), a}

# the run r, after it took the request i, whose entry is a, as the number n:
# its outcome, its record (the content of r), the count, and the voters that
# it gives
def Step.taken.at(
  ~mach: Machine(),
  ~d: Led(mach),
  r: Run<Led.L(mach, d)>,
  +i: Ledgers.Id,
  a: Hashes.Hash,
  +n: U32,
  vs: Maybe<&2, List<&2, String>>
) -> Maybe<&2, Run<Led.L(mach, d)>>:
  Maybe.bind(
    &2,
    Run<Led.L(mach, d)>,
    Run<Led.L(mach, d)>,
    Run.add(~mach, ~d, r, Log.out(i), Out.code(Out.Taken{a, n}, [])),
    +r1 => Maybe.bind(
      &2,
      Run<Led.L(mach, d)>,
      Run<Led.L(mach, d)>,
      Run.add(
        ~mach,
        ~d,
        r1,
        Log.taken(n),
        Taken.code(Taken{i, Tip.content(Run.tip(Led.L(mach, d), r1))}, [])
      ),
      r2 => Some{Run.next(Led.L(mach, d), r2, vs)}
    )
  )

# the run r, after it took the request i, whose entry is a, as its next number
def Step.taken(
  ~mach: Machine(),
  ~d: Led(mach),
  +r: Run<Led.L(mach, d)>,
  i: Ledgers.Id,
  a: Hashes.Hash,
  vs: Maybe<&2, List<&2, String>>
) -> Maybe<&2, Run<Led.L(mach, d)>>:
  Step.taken.at(~mach, ~d, r, i, a, Tip.count(Run.tip(Led.L(mach, d), r)), vs)

# the tip t with the content h
def Tip.over(t: Tip, h: Maybe<&2, Hashes.Hash>) -> Tip:
  match t:
    case Tip{c, l, n, vs}:
      Tip{h, l, n, vs}

# the run r with the nodes ns as data, and the content h
def Run.over(
  ~mach: Machine(),
  ~d: Led(mach),
  r: Run<Led.L(mach, d)>,
  +ns: List<&2, List<&2, U32>>,
  h: Maybe<&2, Hashes.Hash>
) -> Run<Led.L(mach, d)>:
  match r:
    case Run{l, t, a}:
      Run{Led.puts(~mach, ~d, ns, l), Tip.over(t, h), List.append(&2, List<&2, U32>, ns, a)}

# the run r with the label m on the taken request v, then the request i taken
def Step.labelled(
  ~mach: Machine(),
  ~d: Led(mach),
  r: Run<Led.L(mach, d)>,
  i: Ledgers.Id,
  a: Hashes.Hash,
  m: String,
  v: Maybe<&2, Taken>
) -> Maybe<&2, Run<Led.L(mach, d)>>:
  match v:
    case None{}:
      None{}
    case Some{x}:
      Maybe.bind(
        &2,
        Run<Led.L(mach, d)>,
        Run<Led.L(mach, d)>,
        Run.add(~mach, ~d, r, Log.label(m), Ledgers.Id.code(Taken.id(x), [])),
        r2 => Step.taken(~mach, ~d, r2, i, a, None{})
      )

# Step.label once a read of the label m tells whether the line has it (k;
# none: the ledger lacks a node, so the run waits)
def Step.label.at(
  ~mach: Machine(),
  ~d: Led(mach),
  +r: Run<Led.L(mach, d)>,
  +i: Ledgers.Id,
  +a: Hashes.Hash,
  +m: String,
  k: Maybe<&2, Maybe<&2, Ledgers.Id>>
) -> Maybe<&2, Run<Led.L(mach, d)>>:
  match k:
    case None{}:
      None{}
    case Some{Some{x}}:
      Step.stale(~mach, ~d, r, i, a)
    case Some{None{}}:
      +l = Run.ledger(Led.L(mach, d), r)
      +t = Run.tip(Led.L(mach, d), r)
      +n = Tip.count(t)
      Shared.Bool.when(
        Maybe<&2, Run<Led.L(mach, d)>>,
        U32.is_eq(n, 0),
        u => Step.stale(~mach, ~d, r, i, a),
        u => Step.labelled(~mach, ~d, r, i, a, m, Tip.taken(~mach, ~d, l, t, U32.sub(n, 1)))
      )

# the run r, after a request i for the label m: it names the newest taken
# request, for good; a label that the line has, or a line that took no
# request, refuses it
def Step.label(
  ~mach: Machine(),
  ~d: Led(mach),
  +r: Run<Led.L(mach, d)>,
  +i: Ledgers.Id,
  +a: Hashes.Hash,
  +m: String
) -> Maybe<&2, Run<Led.L(mach, d)>>:
  Step.label.at(
    ~mach,
    ~d,
    r,
    i,
    a,
    m,
    Tip.known(
      ~Ledgers.Id,
      ~Ledgers.Id.code,
      ~Ledgers.Id.code.read,
      Tip.find(~mach, ~d, Run.ledger(Led.L(mach, d), r), Run.tip(Led.L(mach, d), r), Log.label(m))
    )
  )

# the run r with the first tip t of the new sub line b in its log, and the
# nodes ns and the tip as data, then the request i taken
def Step.opens(
  ~mach: Machine(),
  ~d: Led(mach),
  +r: Run<Led.L(mach, d)>,
  i: Ledgers.Id,
  a: Hashes.Hash,
  b: String,
  +t: Tip,
  ns: List<&2, List<&2, U32>>
) -> Maybe<&2, Run<Led.L(mach, d)>>:
  Maybe.bind(
    &2,
    Run<Led.L(mach, d)>,
    Run<Led.L(mach, d)>,
    Run.add(
      ~mach,
      ~d,
      Run.over(~mach, ~d, r, Tip.code(t, []) <> ns, Tip.content(Run.tip(Led.L(mach, d), r))),
      Log.start(b),
      Hashes.Hash.code(Tip.hash(t), [])
    ),
    r2 => Step.taken(~mach, ~d, r2, i, a, None{})
  )

# the run r after the request i, whose entry is a, by the act m of a kernel
# (none: wait). The replica does the act: a kernel gives data and a result
def Act.run(
  ~mach: Machine(),
  ~d: Led(mach),
  +r: Run<Led.L(mach, d)>,
  i: Ledgers.Id,
  a: Hashes.Hash,
  m: Maybe<&2, Act>
) -> Maybe<&2, Run<Led.L(mach, d)>>:
  match m:
    case None{}:
      None{}
    case Some{Act.Stale{}}:
      Step.stale(~mach, ~d, r, i, a)
    case Some{Act.Label{x}}:
      Step.label(~mach, ~d, r, i, a, x)
    case Some{Act.Taken{vs, h, ns}}:
      Step.taken(~mach, ~d, Run.over(~mach, ~d, r, ns, h), i, a, vs)
    case Some{Act.Opens{b, t, ns}}:
      Step.opens(~mach, ~d, r, i, a, b, t, ns)

# the run r of the line c after the request of the ID i, whose entry is a and
# whose outcome in the log is o: an ID that has one is skipped
def Step.fresh(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  +r: Run<Led.L(mach, d)>,
  c: Ledgers.Line,
  +i: Ledgers.Id,
  a: Hashes.Hash,
  q: Machine.Q(mach),
  o: Maybe<&2, Maybe<&2, Out>>
) -> Maybe<&2, Run<Led.L(mach, d)>>:
  match o:
    case None{}:
      None{}
    case Some{Some{x}}:
      Some{r}
    case Some{None{}}:
      Act.run(
        ~mach,
        ~d,
        r,
        i,
        a,
        Kernel.change(mach, d, kern)(Run.ledger(Led.L(mach, d), r))(Run.tip(Led.L(mach, d), r))(c)(i)(q)
      )

# the run r of the line c after the entry m, whose hash is a (none: the
# ledger lacks the request)
def Step.asked(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  +r: Run<Led.L(mach, d)>,
  c: Ledgers.Line,
  a: Hashes.Hash,
  m: Maybe<&2, Entry(mach)>
) -> Maybe<&2, Run<Led.L(mach, d)>>:
  match m:
    case Some{Ledgers.Entry.Ask{+i, t, q}}:
      Step.fresh(
        ~mach,
        ~d,
        ~kern,
        r,
        c,
        i,
        a,
        q,
        Tip.known(
          ~Out,
          ~Out.code,
          ~Out.code.read,
          Tip.find(~mach, ~d, Run.ledger(Led.L(mach, d), r), Run.tip(Led.L(mach, d), r), Log.out(i))
        )
      )
    case _:
      None{}

# the run r of the line c after the request whose entry has the hash a
def Step.one(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  +r: Run<Led.L(mach, d)>,
  c: Ledgers.Line,
  +a: Hashes.Hash
) -> Maybe<&2, Run<Led.L(mach, d)>>:
  Step.asked(
    ~mach,
    ~d,
    ~kern,
    r,
    c,
    a,
    Led.get(~mach, ~d, Run.ledger(Led.L(mach, d), r), Ledgers.Name.Ask{a})
  )

# the run m of the line c after each request of qs, in order
def Step.all(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  +c: Ledgers.Line,
  qs: List<&2, Hashes.Hash>,
  m: Maybe<&2, Run<Led.L(mach, d)>>
) -> Maybe<&2, Run<Led.L(mach, d)>>:
  match qs:
    case Nil{}:
      m
    case Con{a, rest}:
      Step.all(
        ~mach,
        ~d,
        ~kern,
        c,
        rest,
        Maybe.bind(
          &2,
          Run<Led.L(mach, d)>,
          Run<Led.L(mach, d)>,
          m,
          r => Step.one(~mach, ~d, ~kern, r, c, a)
        )
      )

# the step of the line c that runs the requests qs from the tip t, in l (none:
# wait for a request or a node)
def Step.run(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  l: Led.L(mach, d),
  c: Ledgers.Line,
  t: Tip,
  qs: List<&2, Hashes.Hash>
) -> Maybe<&2, Run<Led.L(mach, d)>>:
  Step.all(~mach, ~d, ~kern, c, qs, Some{Run{l, t, []}})

# that b grows from a, and its ballots are honest: a later state of a ledger,
# as the laws of a history read it. An equation of checks, so a proof can use
# it as often as it needs (Led.later_grows, Led.later_honest)
def Led.Later(~mach: Machine(), ~d: Led(mach), a: Led.L(mach, d), +b: Led.L(mach, d)) -> Type:
  {
    Bool.and(
      Ledgers.Kind.grows(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), a, b),
      Led.honest(~mach, ~d, b)
    )
      == True{}: Bool
  }

# a later ledger holds each entry of the earlier one
law Led.later_grows:
  for ~mach: Machine()
  for ~d: Led(mach)
  for a: Led.L(mach, d)
  for b: Led.L(mach, d)
  Led.Later(~mach, ~d, a, b) -> Led.Grows(mach, d, a, b)

def Led.later_grows(mach, d, a, b):
  ?TODO

# the ballots of a later ledger cast one vote at a place and one pass to it
law Led.later_single:
  for ~mach: Machine()
  for ~d: Led(mach)
  for a: Led.L(mach, d)
  for b: Led.L(mach, d)
  Led.Later(~mach, ~d, a, b) -> Led.Single(mach, d, b)

def Led.later_single(mach, d, a, b):
  ?TODO

# the passes of a later ledger name the last vote of their voter
law Led.later_last:
  for ~mach: Machine()
  for ~d: Led(mach)
  for a: Led.L(mach, d)
  for b: Led.L(mach, d)
  for c: Ledgers.Line
  for h: U32
  Led.Later(~mach, ~d, a, b) -> Rounds.Last(mach, d, b, c, h)

def Led.later_last(mach, d, a, b, c, h):
  ?TODO

# Histories
# ---------
# The history of a line is a function of a ledger: its start, then each step
# that the rules decide and that runs to the tip that it names. No replica
# keeps a history apart from its ledger: a head that a replica keeps is this
# function, kept to save work.

# the names of the first voters vs
def Voter.names(vs: List<&2, Voter>) -> List<&2, String>:
  match vs:
    case Nil{}:
      []
    case Con{Voter{n, k}, r}:
      n <> Voter.names(r)

# the first tip of a root line that the arrival a starts
def Root.first(a: Arrival) -> Maybe<&2, Tip>:
  match a:
    case Arrival.Starts{vs}:
      Some{Tip{None{}, None{}, 0, Voter.names(vs)}}
    case Arrival.Waits{c}:
      None{}

# the first tip of the root line that the entry m starts
def Root.start.of(~mach: Machine(), m: Maybe<&2, Entry(mach)>) -> Maybe<&2, Tip>:
  match m:
    case Some{Ledgers.Entry.Ask{i, t, q}}:
      Root.first(Machine.arrival(mach)(q))
    case _:
      None{}

# the first tip of the root line of the root r: its voters are the first
# voters of the request whose hash is r
def Root.start(
  ~mach: Machine(),
  ~d: Led(mach),
  l: Led.L(mach, d),
  r: Hashes.Hash
) -> Maybe<&2, Tip>:
  Root.start.of(~mach, Led.get(~mach, ~d, l, Ledgers.Name.Ask{r}))

# a and b are the same hash, or both none
def Tips.same(a: Maybe<&2, Hashes.Hash>, b: Maybe<&2, Hashes.Hash>) -> Bool:
  Shared.Maybe.is_eq(~Hashes.Hash, ~Hashes.Hash.is_eq, a, b)

# the tip of the run m, when it is the tip that the hash after names and the
# ledger l holds each node that the run added: what a line reads after a step
# is data of the ledger, not of a run
def Line.landed(
  ~mach: Machine(),
  ~d: Led(mach),
  +l: Led.L(mach, d),
  m: Maybe<&2, Run<Led.L(mach, d)>>,
  after: Maybe<&2, Hashes.Hash>
) -> Maybe<&2, Tip>:
  match m:
    case None{}:
      None{}
    case Some{Run{l2, +t, a}}:
      Shared.Maybe.when(
        Tip,
        Bool.and(
          Tips.same(Some{Tip.hash(t)}, after),
          Depots.Depot.holds(~Led.L(mach, d), ~(s => h => Led.fetch(~mach, ~d, s, h)), l, a)
        ),
        u => Some{t}
      )

# the tip of the line c after the step m, from the tip t: the step names t,
# and its requests run, in l, to the tip that it names. So no replica takes a
# result on trust: a step that does not run to its tip moves no line
def Line.moved(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  +l: Led.L(mach, d),
  c: Ledgers.Line,
  +t: Tip,
  m: Maybe<&2, Ledgers.Step>
) -> Maybe<&2, Tip>:
  match m:
    case None{}:
      None{}
    case Some{Ledgers.Step{before, qs, after}}:
      Shared.Maybe.when(
        Tip,
        Tips.same(before, Some{Tip.hash(t)}),
        u => Line.landed(~mach, ~d, l, Step.run(~mach, ~d, ~kern, l, c, t, qs), after)
      )

# the tip of the line c after its step at the height h, from the tip t, in l
# (none: no step is decided there, or l lacks what the step reads)
def Line.next(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  +l: Led.L(mach, d),
  +c: Ledgers.Line,
  +h: U32,
  +t: Tip
) -> Maybe<&2, Tip>:
  Line.moved(
    ~mach,
    ~d,
    ~kern,
    l,
    c,
    t,
    Height.decide(
      ~mach,
      ~d,
      l,
      c,
      h,
      Tip.voters(t),
      Ledgers.Kind.rounds(Machine.Q(mach), Led.kind(mach, d))(l)(c)(h)
    )
  )

# the newest tip of the line c from the tip t at the height h, whose next tip
# is m, in at most fuel steps: one walk, each step once
def Line.walk(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  fuel: Nat,
  +l: Led.L(mach, d),
  +c: Ledgers.Line,
  +h: U32,
  t: Tip,
  m: Maybe<&2, Tip>
) -> Tip:
  match fuel m:
    case 0n x:
      t
    case 1n+f None{}:
      t
    case 1n+f Some{+t2}:
      Line.walk(
        ~mach,
        ~d,
        ~kern,
        f,
        l,
        c,
        U32.inc(h),
        t2,
        Line.next(~mach, ~d, ~kern, l, c, U32.inc(h), t2)
      )

# the newest tip of the line c, from its first tip m (none: the line has no
# start in l). No ballot of the line is above the bound of l, so the walk
# sees every step
def Line.head.of(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  +l: Led.L(mach, d),
  +c: Ledgers.Line,
  m: Maybe<&2, Tip>
) -> Maybe<&2, Tip>:
  match m:
    case None{}:
      None{}
    case Some{+t}:
      Some{
        Line.walk(
          ~mach,
          ~d,
          ~kern,
          1n+Ledgers.Kind.heights(Machine.Q(mach), Led.kind(mach, d))(l)(c),
          l,
          c,
          0,
          t,
          Line.next(~mach, ~d, ~kern, l, c, 0, t)
        )
      }

# the newest tip of the root line of the root r
def Root.head(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  +l: Led.L(mach, d),
  +r: Hashes.Hash
) -> Maybe<&2, Tip>:
  Line.head.of(~mach, ~d, ~kern, l, Ledgers.Line{r, None{}}, Root.start(~mach, ~d, l, r))

# the tip that some words name by its hash, in l
def Tip.named(
  ~mach: Machine(),
  ~d: Led(mach),
  l: Led.L(mach, d),
  ws: List<&2, U32>
) -> Maybe<&2, Tip>:
  Tip.of(~mach, ~d, l, Codes.Code.whole.read(~Hashes.Hash, ~Hashes.Hash.code, ~Hashes.Hash.code.read, ws))

# the first tip of the sub line b, which the log of its root line holds at
# the tip m
def Sub.start(
  ~mach: Machine(),
  ~d: Led(mach),
  +l: Led.L(mach, d),
  b: String,
  m: Maybe<&2, Tip>
) -> Maybe<&2, Tip>:
  Maybe.bind(
    &2,
    Tip,
    Tip,
    m,
    t => Maybe.bind(
      &2,
      List<&2, U32>,
      Tip,
      Tip.get(~mach, ~d, l, t, Log.start(b)),
      ws => Tip.named(~mach, ~d, l, ws)
    )
  )

# the first tip of the line c: of a root line, what its request starts; of a
# sub line, the tip that the log of its root line holds for it
def Line.start(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  +l: Led.L(mach, d),
  c: Ledgers.Line
) -> Maybe<&2, Tip>:
  match c:
    case Ledgers.Line{r, None{}}:
      Root.start(~mach, ~d, l, r)
    case Ledgers.Line{r, Some{b}}:
      Sub.start(~mach, ~d, l, b, Root.head(~mach, ~d, ~kern, l, r))

# the newest tip of the line c, in l
def Line.head(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  +l: Led.L(mach, d),
  +c: Ledgers.Line
) -> Maybe<&2, Tip>:
  Line.head.of(~mach, ~d, ~kern, l, c, Line.start(~mach, ~d, ~kern, l, c))

# the tip of the line c after k steps, in l (none: l holds fewer). A law's
# measure: no replica runs it
def Line.at(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  k: Nat,
  +l: Led.L(mach, d),
  +c: Ledgers.Line
) -> Maybe<&2, Tip>:
  match k:
    case 0n:
      Line.start(~mach, ~d, ~kern, l, c)
    case 1n+(+p):
      Maybe.bind(
        &2,
        Tip,
        Tip,
        Line.at(~mach, ~d, ~kern, p, l, c),
        +t => Line.next(~mach, ~d, ~kern, l, c, U32.from_nat(p), t)
      )

# what the log of the line c holds under the key k, in l
def Line.get(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  +l: Led.L(mach, d),
  c: Ledgers.Line,
  k: List<&2, U32>
) -> Maybe<&2, List<&2, U32>>:
  Maybe.bind(
    &2,
    Tip,
    List<&2, U32>,
    Line.head(~mach, ~d, ~kern, l, c),
    t => Tip.get(~mach, ~d, l, t, k)
  )

# Seals
# -----
# A ballot counts only when a key of its voter signs it. The ballots of a
# voter under a root are a chain: the first is signed by a key that the root
# line gives the voter, and each next one by the key that the ballot before
# it names. So each key signs once, and two ballots that one key signs are the
# proof of a lie.

# the key of the voter among the first voters vs
def Voter.key(vs: List<&2, Voter>, +voter: String) -> Maybe<&2, Hashes.Hash>:
  match vs:
    case Nil{}:
      None{}
    case Con{Voter{n, k}, r}:
      Shared.Bool.when(Maybe<&2, Hashes.Hash>, String.eq(n, voter), u => Some{k}, u => Voter.key(r, voter))

# the key that the arrival a gives the voter
def Root.key.of(a: Arrival, voter: String) -> Maybe<&2, Hashes.Hash>:
  match a:
    case Arrival.Starts{vs}:
      Voter.key(vs, voter)
    case Arrival.Waits{c}:
      None{}

# the key that the entry m, which starts a root line, gives the voter
def Root.key.at(~mach: Machine(), m: Maybe<&2, Entry(mach)>, voter: String) -> Maybe<&2, Hashes.Hash>:
  match m:
    case Some{Ledgers.Entry.Ask{i, t, q}}:
      Root.key.of(Machine.arrival(mach)(q), voter)
    case _:
      None{}

# the key that the content of the tip m gives the voter, in l
def Tip.key(
  ~mach: Machine(),
  ~d: Led(mach),
  +l: Led.L(mach, d),
  m: Maybe<&2, Tip>,
  voter: String
) -> Maybe<&2, Hashes.Hash>:
  Maybe.bind(
    &2,
    Tip,
    Hashes.Hash,
    m,
    t => Codes.Code.whole.of(
      ~Hashes.Hash,
      ~Hashes.Hash.code,
      ~Hashes.Hash.code.read,
      Tree.get(~mach, ~d, l, Tip.content(t), Machine.seal(mach)(voter))
    )
  )

# that the root line of the root r gives the voter the key k as the first key
# of a chain: the request that starts the line does, or the content of the
# line does after some steps
def Root.Gives(
  -mach: Machine(),
  -d: Led(mach),
  -kern: Kernel(mach, d),
  -l: Led.L(mach, d),
  -r: Hashes.Hash,
  -voter: String,
  -k: Hashes.Hash
) -> Type:
  {
    Root.key.at(~mach, Led.get(~mach, ~d, l, Ledgers.Name.Ask{r}), voter) == Some{k}: Maybe<&2, Hashes.Hash>
  }
    | Exists(
      Nat,
      n => {
        Tip.key(
          ~mach,
          ~d,
          l,
          Line.at(~mach, ~d, ~kern, n, l, Ledgers.Line{r, None{}}),
          voter
        )
          == Some{k}: Maybe<&2, Hashes.Hash>
      }
    )

# the key of the next ballot of the chain, which the ballot b names
def Ballot.next(b: Ledgers.Ballot) -> Hashes.Hash:
  match b:
    case Ledgers.Ballot{x, Ledgers.Link{p, k, z}}:
      k

# the place of the ballot before b in its chain (none: b is the first)
def Ballot.prev(b: Ledgers.Ballot) -> Maybe<&2, Ledgers.Place>:
  match b:
    case Ledgers.Ballot{x, Ledgers.Link{p, k, z}}:
      p

# that a key of the chain of its voter signs the ballot b, in l: the key that
# the ballot before it names, when it names one that l holds; else a first key
# that its root line gives its voter
def Ballot.Linked(
  -mach: Machine(),
  -d: Led(mach),
  -kern: Kernel(mach, d),
  -l: Led.L(mach, d),
  -b: Ledgers.Ballot,
  p: Maybe<&2, Ledgers.Place>
) -> Type:
  match p:
    case None{}:
      Exists(
        Hashes.Hash,
        k => {
          Ledgers.Ballot.sealed(k, b) == True{}: Bool
        }
          & Root.Gives(mach, d, kern, l, Ledgers.Ballot.root(b), Ledgers.Ballot.voter(b), k)
      )
    case Some{w}:
      Exists(
        Ledgers.Ballot,
        b0 => {
          Led.has(~mach, ~d, l, Ledgers.Entry.Ballot{b0}) == True{}: Bool
        }
          & (
            {
              Ledgers.Ballot.is_at(b0, w, Ledgers.Ballot.voter(b)) == True{}: Bool
            }
              & {Ledgers.Ballot.sealed(Ballot.next(b0), b) == True{}: Bool}
          )
      )

# that the lie x is a proof: its key signs its two ballots, and they are not
# the same ballot
def Lie.Proves(x: Ledgers.Lie) -> Type:
  match x:
    case Ledgers.Lie{k, a, b}:
      {
        Ledgers.Ballot.sealed(k, a) == True{}: Bool
      }
        & ({Ledgers.Ballot.sealed(k, b) == True{}: Bool} & {a != b: Ledgers.Ballot})

# that l holds only what checks: a key of its voter's chain signs each ballot,
# and each proof of a lie is a proof
def Led.Sound(-mach: Machine(), -d: Led(mach), -kern: Kernel(mach, d), -l: Led.L(mach, d)) -> Type:
  (
    @b: Ledgers.Ballot -> {
      Led.has(~mach, ~d, l, Ledgers.Entry.Ballot{b}) == True{}: Bool
    } -> Ballot.Linked(mach, d, kern, l, b, Ballot.prev(b))
  )
    & (
      @x: Ledgers.Lie -> {
        Led.has(~mach, ~d, l, Ledgers.Entry.Lie{x}) == True{}: Bool
      } -> Lie.Proves(x)
    )

# Replicas
# --------
# A replica is a way to hold a ledger and act on it (Replica.Kind), with the
# proof that it obeys the laws of a replica (Replica.Laws). What a replica
# answers is a read of its ledger (Line.head, Line.get): the laws say how the
# ledger of a replica changes, and nothing else needs a law.

# what a replica does next: a request arrives; it takes in the entries that
# another replica sent; it keeps words as data; a client that is connected to
# it asks for a request that changes who votes; it passes to the next round on
# a line; or it lets go of what it no longer uses
type Deed<-Q: Data> is Data:
  Deed.Ask{id: Ledgers.Id, time: String, ask: Q}
  Deed.Take{sent: List<&2, Ledgers.Entry<Q>>}
  Deed.Keep{words: List<&2, List<&2, U32>>}
  Deed.Consent{ask: Hashes.Hash}
  Deed.Pass{line: Ledgers.Line}
  Deed.Drop{names: List<&2, Ledgers.Name>}

# the entries that the deed x brings
def Deed.entries(-Q: Data, x: Deed<Q>) -> List<&2, Ledgers.Entry<Q>>:
  match x:
    case Deed.Ask{i, t, q}:
      [Ledgers.Entry.Ask{i, t, q}]
    case Deed.Take{es}:
      es
    case Deed.Keep{Nil{}}:
      []
    case Deed.Keep{Con{ws, rest}}:
      Ledgers.Entry.Data{ws} <> Deed.entries(Q, Deed.Keep{rest})
    case Deed.Consent{a}:
      []
    case Deed.Pass{c}:
      []
    case Deed.Drop{ns}:
      []

# the deed x lets go of entries
def Deed.is_drop(-Q: Data, x: Deed<Q>) -> Bool:
  match x:
    case Deed.Drop{ns}:
      True{}
    case _:
      False{}

# the deed x asks for the request whose entry has the hash a
def Deed.consents(-Q: Data, x: Deed<Q>, a: Hashes.Hash) -> Bool:
  match x:
    case Deed.Consent{b}:
      Hashes.Hash.is_eq(a, b)
    case _:
      False{}

# the operations of a replica kept as R: the replica of a name and a secret
# seed that holds nothing; its name; its ledger; the replica after a deed;
# whether a client that is connected to it asked for a request; its secret
# seed; and how many ballots it cast under a root, which numbers its next one
def Replica.Ops(-mach: Machine(), -d: Led(mach), -R: Data) -> Type:
  (String -> Hashes.Hash -> R)
    & (
      (R -> String)
        & (
          (R -> Led.L(mach, d))
            & (
              (R -> Deed<Machine.Q(mach)> -> R)
                & ((R -> Hashes.Hash -> Bool) & ((R -> Hashes.Hash) & (R -> Hashes.Hash -> U32)))
            )
        )
    )

# a way to hold a ledger and act on it: what a replica is kept as, and its
# operations
def Replica.Kind(-mach: Machine(), -d: Led(mach)) -> Type:
  &R: Data -> Replica.Ops(mach, d, R)

# what a replica of the kind k is kept as
def Kind.R(-mach: Machine(), -d: Led(mach), k: Replica.Kind(mach, d)) -> Data:
  match k:
    case Tuple{r, ops}:
      r

# the replica of a name and a seed that holds nothing
def Kind.empty(
  -mach: Machine(),
  -d: Led(mach),
  k: Replica.Kind(mach, d)
) -> String -> Hashes.Hash -> Kind.R(mach, d, k):
  match k:
    case Tuple{r, Tuple{e, ops}}:
      e

# the name of a replica
def Kind.name(-mach: Machine(), -d: Led(mach), k: Replica.Kind(mach, d)) -> Kind.R(mach, d, k) -> String:
  match k:
    case Tuple{r, Tuple{e, Tuple{n, ops}}}:
      n

# the ledger of a replica
def Kind.ledger(
  -mach: Machine(),
  -d: Led(mach),
  k: Replica.Kind(mach, d)
) -> Kind.R(mach, d, k) -> Led.L(mach, d):
  match k:
    case Tuple{r, Tuple{e, Tuple{n, Tuple{l, ops}}}}:
      l

# a replica after a deed
def Kind.does(
  -mach: Machine(),
  -d: Led(mach),
  k: Replica.Kind(mach, d)
) -> Kind.R(mach, d, k) -> Deed<Machine.Q(mach)> -> Kind.R(mach, d, k):
  match k:
    case Tuple{r, Tuple{e, Tuple{n, Tuple{l, Tuple{f, rest}}}}}:
      f

# a client that is connected to a replica asked for a request
def Kind.consented(
  -mach: Machine(),
  -d: Led(mach),
  k: Replica.Kind(mach, d)
) -> Kind.R(mach, d, k) -> Hashes.Hash -> Bool:
  match k:
    case Tuple{r, Tuple{e, Tuple{n, Tuple{l, Tuple{f, Tuple{c, Tuple{h, cn}}}}}}}:
      c

# the secret seed of a replica
def Kind.seed(-mach: Machine(), -d: Led(mach), k: Replica.Kind(mach, d)) -> Kind.R(mach, d, k) -> Hashes.Hash:
  match k:
    case Tuple{r, Tuple{e, Tuple{n, Tuple{l, Tuple{f, Tuple{c, Tuple{h, cn}}}}}}}:
      h

# how many ballots a replica cast under a root
def Kind.count(
  -mach: Machine(),
  -d: Led(mach),
  k: Replica.Kind(mach, d)
) -> Kind.R(mach, d, k) -> Hashes.Hash -> U32:
  match k:
    case Tuple{r, Tuple{e, Tuple{n, Tuple{l, Tuple{f, Tuple{c, Tuple{h, cn}}}}}}}:
      cn

# the replica s after each deed of xs, in order: any later state of it
def Kind.after(
  ~mach: Machine(),
  ~d: Led(mach),
  ~k: Replica.Kind(mach, d),
  xs: List<&2, Deed<Machine.Q(mach)>>,
  s: Kind.R(mach, d, k)
) -> Kind.R(mach, d, k):
  match xs:
    case Nil{}:
      s
    case Con{x, rest}:
      Kind.after(~mach, ~d, ~k, rest, Kind.does(mach, d, k)(s)(x))

# The laws of a replica
# ---------------------
# Each is a proposition about a kind k of replica, for a kernel kern.

# e is in the list es
def Entries.has(~mach: Machine(), es: List<&2, Entry(mach)>, e: Entry(mach)) -> Bool:
  List.contains(
    ~Entry(mach),
    ~Ledgers.Entry.same(~Machine.Q(mach), ~Machine.code(mach)),
    es,
    e
  )

# the name of the entry e
def Entry.name(~mach: Machine(), e: Entry(mach)) -> Ledgers.Name:
  Ledgers.Entry.name(~Machine.Q(mach), ~Machine.code(mach), e)

# that no entry of es clashes with the entry e: each one that has the name of
# e is e
def Entries.Agree(-mach: Machine(), -es: List<&2, Entry(mach)>, -e: Entry(mach)) -> Type:
  @x: Entry(
    mach
  ) -> {
    Entries.has(~mach, es, x) == True{}: Bool
  } -> Ledgers.Entry.Agrees(~Machine.Q(mach), ~Machine.code(mach), e, x)

# that the entry e checks in l: a request and data always do; a ballot does
# when l with it is honest and sound; a proof of a lie does when it is a proof
def Entry.Checks(
  -mach: Machine(),
  -d: Led(mach),
  -kern: Kernel(mach, d),
  -l: Led.L(mach, d),
  e: Entry(mach)
) -> Type:
  match e:
    case Ledgers.Entry.Ask{i, t, q}:
      Unit
    case Ledgers.Entry.Data{ws}:
      Unit
    case Ledgers.Entry.Ballot{b}:
      Led.Honest(mach, d, Led.add(~mach, ~d, l, Ledgers.Entry.Ballot{b}))
        & Led.Sound(mach, d, kern, Led.add(~mach, ~d, l, Ledgers.Entry.Ballot{b}))
    case Ledgers.Entry.Lie{x}:
      Lie.Proves(x)

# that a client that is connected to s asked for each request among qs that
# changes who votes
def Replica.Consents(
  -mach: Machine(),
  -d: Led(mach),
  -k: Replica.Kind(mach, d),
  -s: Kind.R(mach, d, k),
  -qs: List<&2, Hashes.Hash>
) -> Type:
  @a: Hashes.Hash -> @i: Ledgers.Id -> @time: String -> @q: Machine.Q(
    mach
  ) -> {
    List.contains(~Hashes.Hash, ~Hashes.Hash.is_eq, qs, a) == True{}: Bool
  } -> {
    Led.get(~mach, ~d, Kind.ledger(mach, d, k)(s), Ledgers.Name.Ask{a})
      == Some{Ledgers.Entry.Ask{i, time, q}}: Maybe<&2, Entry(mach)>
  } -> {
    Machine.governs(mach)(q) == True{}: Bool
  } -> {Kind.consented(mach, d, k)(s)(a) == True{}: Bool}

# the line of the ballot b
def Ballot.line(b: Ledgers.Ballot) -> Ledgers.Line:
  match b:
    case Ledgers.Ballot{Ledgers.Signed{Ledgers.Place{c, h, r}, n, x}, l}:
      c

# that the replica s can run each step that it voted for, and holds what the
# run adds: so a majority of the voters holds each part of a decided step. And
# that it voted for a request that changes who votes only when a client that
# is connected to it asked for that request
def Replica.Runs(
  -mach: Machine(),
  -d: Led(mach),
  -kern: Kernel(mach, d),
  -k: Replica.Kind(mach, d),
  -s: Kind.R(mach, d, k)
) -> Type:
  @b: Ledgers.Ballot -> @bf: Maybe<
    &2,
    Hashes.Hash> -> @qs: List<
    &2,
    Hashes.Hash> -> @af: Maybe<
    &2,
    Hashes.Hash> -> @from: List<
    &2,
    String> -> {
    Led.has(~mach, ~d, Kind.ledger(mach, d, k)(s), Ledgers.Entry.Ballot{b}) == True{}: Bool
  } -> {
    String.eq(Ledgers.Ballot.voter(b), Kind.name(mach, d, k)(s)) == True{}: Bool
  } -> {
    Ledgers.Ballot.cast(b) == Ledgers.Cast.Vote{Ledgers.Step{bf, qs, af}, from}: Ledgers.Cast
  } -> (
    Exists(
      Tip,
      t => Exists(
        Run<Led.L(mach, d)>,
        r => {
          Tip.of(~mach, ~d, Kind.ledger(mach, d, k)(s), bf) == Some{t}: Maybe<&2, Tip>
        }
          & (
            {
              Step.run(
                ~mach,
                ~d,
                ~kern,
                Kind.ledger(mach, d, k)(s),
                Ballot.line(b),
                t,
                qs
              )
                == Some{r}: Maybe<&2, Run<Led.L(mach, d)>>
            }
              & (
                {
                  Some{Tip.hash(Run.tip(Led.L(mach, d), r))} == af: Maybe<&2, Hashes.Hash>
                }
                  & Led.Grows(mach, d, Run.ledger(Led.L(mach, d), r), Kind.ledger(mach, d, k)(s))
              )
          )
      )
    )
      & Replica.Consents(mach, d, k, s, qs)
  )

# that the replica s asks by itself: for each line, it holds an entry under
# the name of the request that the kernel says to ask for that line
def Replica.Asks(
  -mach: Machine(),
  -d: Led(mach),
  -kern: Kernel(mach, d),
  -k: Replica.Kind(mach, d),
  -s: Kind.R(mach, d, k)
) -> Type:
  @c: Ledgers.Line -> @i: Ledgers.Id -> @time: String -> @q: Machine.Q(
    mach
  ) -> {
    Kernel.follow(mach, d, kern)(Kind.ledger(mach, d, k)(s))(c)
      == Some{Request{i, time, q}}: Maybe<&2, Request<Machine.Q(mach)>>
  } -> {
    Maybe.is_some(
      &2,
      Entry(mach),
      Led.get(
        ~mach,
        ~d,
        Kind.ledger(mach, d, k)(s),
        Entry.name(~mach, Ledgers.Entry.Ask{i, time, q})
      )
    )
      == True{}: Bool
  }

# Keys of a replica
# -----------------
# The secret that signs each ballot of a replica is a hash of its seed, the
# root and the number of the ballot. So each ballot has its own key, and a
# replica keeps only its seed.

# the secret that signs the ballot of the number n of a replica under a root
def Key.secret(seed: Hashes.Hash, root: Hashes.Hash, n: U32) -> Hashes.Hash:
  Hashes.Sha.hash(Hashes.Hash.code(seed, Hashes.Hash.code(root, [n])))

# the key that checks the ballot of the number n of a replica under a root
def Key.public(seed: Hashes.Hash, root: Hashes.Hash, n: U32) -> Hashes.Hash:
  Seals.Seal.public(Key.secret(seed, root, n))

# the root of the line c
def Line.root(c: Ledgers.Line) -> Hashes.Hash:
  match c:
    case Ledgers.Line{r, b}:
      r

# that the replica s has a key under the root r: the root line gives its name
# the key of its first ballot
def Replica.Keyed(
  -mach: Machine(),
  -d: Led(mach),
  -kern: Kernel(mach, d),
  -k: Replica.Kind(mach, d),
  -s: Kind.R(mach, d, k),
  -r: Hashes.Hash
) -> Type:
  Root.Gives(
    mach,
    d,
    kern,
    Kind.ledger(mach, d, k)(s),
    r,
    Kind.name(mach, d, k)(s),
    Key.public(Kind.seed(mach, d, k)(s), r, 0)
  )

# the requests of the step v
def Step.asks(v: Ledgers.Step) -> List<&2, Hashes.Hash>:
  match v:
    case Ledgers.Step{before, qs, after}:
      qs

# Progress
# --------
# What a good replica does without being asked: it votes with the voter whose
# turn it is, and it proposes when the turn is its own.

# that t is the newest tip of the line c in l, at the height h: the tip after
# h steps, with no step decided after it
def Line.Top(
  -mach: Machine(),
  -d: Led(mach),
  -kern: Kernel(mach, d),
  -l: Led.L(mach, d),
  -c: Ledgers.Line,
  -h: U32,
  -t: Tip
) -> Type:
  {
    Line.at(~mach, ~d, ~kern, U32.to_nat(h), l, c) == Some{t}: Maybe<&2, Tip>
  }
    & {Line.next(~mach, ~d, ~kern, l, c, h, t) == None{}: Maybe<&2, Tip>}

# the highest round, up to k, that the voter passed to at the height h of the
# line c (0: it passed to none)
def Round.of(
  ~mach: Machine(),
  ~d: Led(mach),
  k: Nat,
  +l: Led.L(mach, d),
  +c: Ledgers.Line,
  +h: U32,
  +voter: String
) -> Nat:
  match k:
    case 0n:
      0n
    case 1n+(+p):
      Shared.Bool.when(
        Nat,
        Maybe.is_some(
          &2,
          Maybe<&2, Ledgers.Last>,
          Led.passed(~mach, ~d, l, Ledgers.Place{c, h, 1n+p}, voter)
        ),
        u => 1n+p,
        u => Round.of(~mach, ~d, p, l, c, h, voter)
      )

# the round that the voter is in at the height h of the line c: the highest
# round that it passed to
def Round.now(
  ~mach: Machine(),
  ~d: Led(mach),
  +l: Led.L(mach, d),
  +c: Ledgers.Line,
  +h: U32,
  voter: String
) -> Nat:
  Round.of(
    ~mach,
    ~d,
    Ledgers.Kind.rounds(Machine.Q(mach), Led.kind(mach, d))(l)(c)(h),
    l,
    c,
    h,
    voter
  )

# that the replica s follows: at the newest tip of a line where it is a voter
# and has a key, in the round that it is in, it holds its own vote for the
# step that the voter whose turn it is cast there, when the rules allow that
# step, the replica can run it to the tip that it names, and a client asked
# for each request of it that changes who votes
def Replica.Follows(
  -mach: Machine(),
  -d: Led(mach),
  -kern: Kernel(mach, d),
  -k: Replica.Kind(mach, d),
  -s: Kind.R(mach, d, k)
) -> Type:
  @c: Ledgers.Line -> @h: U32 -> @t: Tip -> @p: String -> @v: Ledgers.Step -> @from: List<
    &2,
    String> -> Line.Top(
    mach,
    d,
    kern,
    Kind.ledger(mach, d, k)(s),
    c,
    h,
    t
  ) -> {
    List.contains(~String, ~String.eq, Tip.voters(t), Kind.name(mach, d, k)(s)) == True{}: Bool
  } -> Replica.Keyed(
    mach,
    d,
    kern,
    k,
    s,
    Line.root(c)
  ) -> {
    Voters.turn(
      Tip.voters(t),
      h,
      Round.now(~mach, ~d, Kind.ledger(mach, d, k)(s), c, h, Kind.name(mach, d, k)(s))
    )
      == Some{p}: Maybe<&2, String>
  } -> {
    Led.cast(
      ~mach,
      ~d,
      Kind.ledger(mach, d, k)(s),
      Ledgers.Place{
        c,
        h,
        Round.now(~mach, ~d, Kind.ledger(mach, d, k)(s), c, h, Kind.name(mach, d, k)(s))
      },
      p
    )
      == Some{Ledgers.Cast.Vote{v, from}}: Maybe<&2, Ledgers.Cast>
  } -> {
    Step.allowed(
      ~mach,
      ~d,
      Kind.ledger(mach, d, k)(s),
      Ledgers.Place{
        c,
        h,
        Round.now(~mach, ~d, Kind.ledger(mach, d, k)(s), c, h, Kind.name(mach, d, k)(s))
      },
      Tip.voters(t),
      v,
      from
    )
      == True{}: Bool
  } -> {
    Maybe.is_some(&2, Tip, Line.moved(~mach, ~d, ~kern, Kind.ledger(mach, d, k)(s), c, t, Some{v}))
      == True{}: Bool
  } -> Replica.Consents(
    mach,
    d,
    k,
    s,
    Step.asks(v)
  ) -> {
    Led.voted(
      ~mach,
      ~d,
      Kind.ledger(mach, d, k)(s),
      Ledgers.Place{
        c,
        h,
        Round.now(~mach, ~d, Kind.ledger(mach, d, k)(s), c, h, Kind.name(mach, d, k)(s))
      },
      Kind.name(mach, d, k)(s)
    )
      == Some{v}: Maybe<&2, Ledgers.Step>
  }

# the replica s holds a vote of its own at the height h of the line c, in the
# round that it is in
def Replica.voted(
  ~mach: Machine(),
  ~d: Led(mach),
  ~k: Replica.Kind(mach, d),
  +s: Kind.R(mach, d, k),
  +c: Ledgers.Line,
  +h: U32
) -> Bool:
  +l = Kind.ledger(mach, d, k)(s)
  +n = Kind.name(mach, d, k)(s)
  Maybe.is_some(
    &2,
    Ledgers.Step,
    Led.voted(~mach, ~d, l, Ledgers.Place{c, h, Round.now(~mach, ~d, l, c, h, n)}, n)
  )

# that the replica s leads: at the newest tip of a line where it is a voter
# and has a key, when the turn is its own in the round that it is in, it holds
# a vote of its own there. In the first round: when a request waits on the
# line that it can run alone, and that a client asked for if it changes who
# votes. In a later round: when the rules allow some step that it can run to
# the tip that the step names, and whose requests a client asked for
def Replica.Leads(
  -mach: Machine(),
  -d: Led(mach),
  -kern: Kernel(mach, d),
  -k: Replica.Kind(mach, d),
  -s: Kind.R(mach, d, k)
) -> Type:
  @c: Ledgers.Line -> @h: U32 -> @t: Tip -> Line.Top(
    mach,
    d,
    kern,
    Kind.ledger(mach, d, k)(s),
    c,
    h,
    t
  ) -> {
    List.contains(~String, ~String.eq, Tip.voters(t), Kind.name(mach, d, k)(s)) == True{}: Bool
  } -> Replica.Keyed(
    mach,
    d,
    kern,
    k,
    s,
    Line.root(c)
  ) -> {
    Voters.turn(
      Tip.voters(t),
      h,
      Round.now(~mach, ~d, Kind.ledger(mach, d, k)(s), c, h, Kind.name(mach, d, k)(s))
    )
      == Some{Kind.name(mach, d, k)(s)}: Maybe<&2, String>
  } -> (
    (
      @a: Hashes.Hash -> @i: Ledgers.Id -> @time: String -> @q: Machine.Q(
        mach
      ) -> {
        Round.now(~mach, ~d, Kind.ledger(mach, d, k)(s), c, h, Kind.name(mach, d, k)(s)) == 0n: Nat
      } -> {
        Led.get(~mach, ~d, Kind.ledger(mach, d, k)(s), Ledgers.Name.Ask{a})
          == Some{Ledgers.Entry.Ask{i, time, q}}: Maybe<&2, Entry(mach)>
      } -> {
        Machine.arrival(mach)(q) == Arrival.Waits{c}: Arrival
      } -> {
        Tip.out(~mach, ~d, Kind.ledger(mach, d, k)(s), t, i) == None{}: Maybe<&2, Out>
      } -> {
        Maybe.is_some(
          &2,
          Run<Led.L(mach, d)>,
          Step.run(~mach, ~d, ~kern, Kind.ledger(mach, d, k)(s), c, t, [a])
        )
          == True{}: Bool
      } -> Replica.Consents(
        mach,
        d,
        k,
        s,
        [a]
      ) -> {Replica.voted(~mach, ~d, ~k, s, c, h) == True{}: Bool}
    )
      & (
        @v: Ledgers.Step -> @from: List<
          &2,
          String> -> {
          Nat.is_eq(
            Round.now(~mach, ~d, Kind.ledger(mach, d, k)(s), c, h, Kind.name(mach, d, k)(s)),
            0n
          )
            == False{}: Bool
        } -> {
          Step.allowed(
            ~mach,
            ~d,
            Kind.ledger(mach, d, k)(s),
            Ledgers.Place{
              c,
              h,
              Round.now(~mach, ~d, Kind.ledger(mach, d, k)(s), c, h, Kind.name(mach, d, k)(s))
            },
            Tip.voters(t),
            v,
            from
          )
            == True{}: Bool
        } -> {
          Maybe.is_some(
            &2,
            Tip,
            Line.moved(~mach, ~d, ~kern, Kind.ledger(mach, d, k)(s), c, t, Some{v})
          )
            == True{}: Bool
        } -> Replica.Consents(
          mach,
          d,
          k,
          s,
          Step.asks(v)
        ) -> {Replica.voted(~mach, ~d, ~k, s, c, h) == True{}: Bool}
      )
  )

# that the replica s is good: its ledger is honest and sound; it runs what it
# votes for; it asks what the kernel says to ask; and it follows and leads
def Replica.Good(
  -mach: Machine(),
  -d: Led(mach),
  -kern: Kernel(mach, d),
  -k: Replica.Kind(mach, d),
  -s: Kind.R(mach, d, k)
) -> Type:
  Led.Honest(mach, d, Kind.ledger(mach, d, k)(s))
    & (
      Led.Sound(mach, d, kern, Kind.ledger(mach, d, k)(s))
        & (
          Replica.Runs(mach, d, kern, k, s)
            & (
              Replica.Asks(mach, d, kern, k, s)
                & (Replica.Follows(mach, d, kern, k, s) & Replica.Leads(mach, d, kern, k, s))
            )
        )
    )

# a replica that holds nothing has its name, its seed, an empty ledger and no
# consent
def Laws.Empty(-mach: Machine(), -d: Led(mach), -k: Replica.Kind(mach, d)) -> Type:
  @name: String -> @seed: Hashes.Hash -> (
    {
      Kind.name(mach, d, k)(Kind.empty(mach, d, k)(name)(seed)) == name: String
    }
      & {Kind.seed(mach, d, k)(Kind.empty(mach, d, k)(name)(seed)) == seed: Hashes.Hash}
  )
    & (
      (
        @n: Ledgers.Name -> {
          Led.get(
            ~mach,
            ~d,
            Kind.ledger(mach, d, k)(Kind.empty(mach, d, k)(name)(seed)),
            n
          )
            == None{}: Maybe<&2, Entry(mach)>
        }
      )
        & (
          @a: Hashes.Hash -> {
            Kind.consented(mach, d, k)(Kind.empty(mach, d, k)(name)(seed))(a) == False{}: Bool
          }
        )
    )

# a deed changes neither the name of a replica, nor its seed, nor what its
# clients asked for, but for the request that the deed asks for
def Laws.Keeps(-mach: Machine(), -d: Led(mach), -k: Replica.Kind(mach, d)) -> Type:
  @s: Kind.R(
    mach,
    d,
    k
  ) -> @x: Deed<
    Machine.Q(mach)> -> (
    {
      Kind.name(mach, d, k)(Kind.does(mach, d, k)(s)(x)) == Kind.name(mach, d, k)(s): String
    }
      & {Kind.seed(mach, d, k)(Kind.does(mach, d, k)(s)(x)) == Kind.seed(mach, d, k)(s): Hashes.Hash}
  )
    & (
      @a: Hashes.Hash -> {
        Kind.consented(mach, d, k)(Kind.does(mach, d, k)(s)(x))(a)
          == Bool.or(
            Kind.consented(mach, d, k)(s)(a),
            Deed.consents(Machine.Q(mach), x, a)
          ): Bool
      }
    )

# a replica only grows, whatever it does but let go: it never loses or
# changes an entry
def Laws.Grows(-mach: Machine(), -d: Led(mach), -k: Replica.Kind(mach, d)) -> Type:
  @s: Kind.R(
    mach,
    d,
    k
  ) -> @x: Deed<
    Machine.Q(mach)> -> {
    Deed.is_drop(Machine.Q(mach), x) == False{}: Bool
  } -> Led.Grows(
    mach,
    d,
    Kind.ledger(mach, d, k)(s),
    Kind.ledger(mach, d, k)(Kind.does(mach, d, k)(s)(x))
  )

# the entry e must stay at a replica of the name voter: a request, a proof of
# a lie, or a ballot of its own. These are what the history of every line
# rests on, and what keeps the replica's own promises
def Entry.stays(-mach: Machine(), e: Entry(mach), voter: String) -> Bool:
  match e:
    case Ledgers.Entry.Ask{i, t, q}:
      True{}
    case Ledgers.Entry.Lie{x}:
      True{}
    case Ledgers.Entry.Ballot{b}:
      String.eq(Ledgers.Ballot.voter(b), voter)
    case Ledgers.Entry.Data{ws}:
      False{}

# a replica lets go only of what it may: what it held, it holds after a drop
# but for the names that the drop gives; it keeps every request, proof of a
# lie and ballot of its own; and it keeps all that the lines it votes on rest
# on: the newest tip of such a line is the same after a drop. So every part of
# a decided step stays with a majority of its voters, and a drop never makes
# a replica break a promise
def Laws.Drops(
  -mach: Machine(),
  -d: Led(mach),
  -kern: Kernel(mach, d),
  -k: Replica.Kind(mach, d)
) -> Type:
  @s: Kind.R(mach, d, k) -> @ns: List<&2, Ledgers.Name> -> (
    @n: Ledgers.Name -> @e: Entry(mach) -> {
      Led.get(~mach, ~d, Kind.ledger(mach, d, k)(s), n) == Some{e}: Maybe<&2, Entry(mach)>
    } -> {
      Bool.or(
        Entry.stays(mach, e, Kind.name(mach, d, k)(s)),
        Bool.not(List.contains(~Ledgers.Name, ~Ledgers.Name.is_eq, ns, n))
      )
        == True{}: Bool
    } -> {
      Led.get(~mach, ~d, Kind.ledger(mach, d, k)(Kind.does(mach, d, k)(s)(Deed.Drop{ns})), n)
        == Some{e}: Maybe<&2, Entry(mach)>
    }
  )
    & (
      @c: Ledgers.Line -> @t: Tip -> {
        Line.head(~mach, ~d, ~kern, Kind.ledger(mach, d, k)(s), c) == Some{t}: Maybe<&2, Tip>
      } -> {
        List.contains(~String, ~String.eq, Tip.voters(t), Kind.name(mach, d, k)(s)) == True{}: Bool
      } -> {
        Line.head(~mach, ~d, ~kern, Kind.ledger(mach, d, k)(Kind.does(mach, d, k)(s)(Deed.Drop{ns})), c)
          == Some{t}: Maybe<&2, Tip>
      }
    )

# a replica never signs twice with one key: the count of its ballots under a
# root never falls, and each ballot of its own under a root is signed with the
# key of a number below the count, one number for each ballot. A replica keeps
# its count where it keeps its data, before a ballot leaves it, so a replica
# that restarts never numbers a ballot again
def Laws.Count(-mach: Machine(), -d: Led(mach), -k: Replica.Kind(mach, d)) -> Type:
  (
    @s: Kind.R(mach, d, k) -> @x: Deed<Machine.Q(mach)> -> @r: Hashes.Hash -> {
      U32.is_le(Kind.count(mach, d, k)(s)(r), Kind.count(mach, d, k)(Kind.does(mach, d, k)(s)(x))(r))
        == True{}: Bool
    }
  )
    & (
      @s: Kind.R(mach, d, k) -> @b: Ledgers.Ballot -> {
        Led.has(~mach, ~d, Kind.ledger(mach, d, k)(s), Ledgers.Entry.Ballot{b}) == True{}: Bool
      } -> {
        String.eq(Ledgers.Ballot.voter(b), Kind.name(mach, d, k)(s)) == True{}: Bool
      } -> Exists(
        U32,
        n => {
          U32.is_lt(n, Kind.count(mach, d, k)(s)(Ledgers.Ballot.root(b))) == True{}: Bool
        }
          & {
            Ledgers.Ballot.sealed(Key.public(Kind.seed(mach, d, k)(s), Ledgers.Ballot.root(b), n), b) == True{}: Bool
          }
      )
    )
    & (
      @s: Kind.R(mach, d, k) -> @a: Ledgers.Ballot -> @b: Ledgers.Ballot -> @n: U32 -> {
        Led.has(~mach, ~d, Kind.ledger(mach, d, k)(s), Ledgers.Entry.Ballot{a}) == True{}: Bool
      } -> {
        Led.has(~mach, ~d, Kind.ledger(mach, d, k)(s), Ledgers.Entry.Ballot{b}) == True{}: Bool
      } -> {
        Ledgers.Ballot.sealed(Key.public(Kind.seed(mach, d, k)(s), Ledgers.Ballot.root(a), n), a) == True{}: Bool
      } -> {
        Ledgers.Ballot.sealed(Key.public(Kind.seed(mach, d, k)(s), Ledgers.Ballot.root(b), n), b) == True{}: Bool
      } -> {Hashes.Hash.is_eq(Ledgers.Ballot.root(a), Ledgers.Ballot.root(b)) == True{}: Bool} -> {a == b: Ledgers.Ballot}
    )

# a replica that holds nothing is good, and a good replica stays good,
# whatever it does and whatever is sent to it: it keeps nothing that does not
# check, and casts no ballot that breaks a promise
def Laws.Good(
  -mach: Machine(),
  -d: Led(mach),
  -kern: Kernel(mach, d),
  -k: Replica.Kind(mach, d)
) -> Type:
  (
    @name: String -> @seed: Hashes.Hash -> Replica.Good(
      mach,
      d,
      kern,
      k,
      Kind.empty(mach, d, k)(name)(seed)
    )
  )
    & (
      @s: Kind.R(
        mach,
        d,
        k
      ) -> @x: Deed<
        Machine.Q(
          mach
        )> -> Replica.Good(
        mach,
        d,
        kern,
        k,
        s
      ) -> Replica.Good(mach, d, kern, k, Kind.does(mach, d, k)(s)(x))
    )

# a replica holds what it takes in: an entry that a deed brings, that checks,
# that no other entry of the deed clashes with, and whose name the replica
# lacks, it then holds
def Laws.Takes(
  -mach: Machine(),
  -d: Led(mach),
  -kern: Kernel(mach, d),
  -k: Replica.Kind(mach, d)
) -> Type:
  @s: Kind.R(
    mach,
    d,
    k
  ) -> @x: Deed<
    Machine.Q(
      mach
    )> -> @e: Entry(
    mach
  ) -> {
    Entries.has(~mach, Deed.entries(Machine.Q(mach), x), e) == True{}: Bool
  } -> {
    Led.get(~mach, ~d, Kind.ledger(mach, d, k)(s), Entry.name(~mach, e)) == None{}: Maybe<&2, Entry(mach)>
  } -> Entries.Agree(
    mach,
    Deed.entries(Machine.Q(mach), x),
    e
  ) -> Entry.Checks(
    mach,
    d,
    kern,
    Kind.ledger(mach, d, k)(s),
    e
  ) -> {Led.has(~mach, ~d, Kind.ledger(mach, d, k)(Kind.does(mach, d, k)(s)(x)), e) == True{}: Bool}

# a replica sees a lie: when it holds the ballot a, and a deed brings another
# ballot b that the same key signs, the replica then names the voter of a a
# liar. (When the name of the proof is free: no entry that the replica holds
# or that the deed brings clashes with the proof)
def Laws.Detects(-mach: Machine(), -d: Led(mach), -k: Replica.Kind(mach, d)) -> Type:
  @s: Kind.R(
    mach,
    d,
    k
  ) -> @x: Deed<
    Machine.Q(
      mach
    )> -> @a: Ledgers.Ballot -> @b: Ledgers.Ballot -> @key: Hashes.Hash -> {
    Led.has(~mach, ~d, Kind.ledger(mach, d, k)(s), Ledgers.Entry.Ballot{a}) == True{}: Bool
  } -> {
    Entries.has(~mach, Deed.entries(Machine.Q(mach), x), Ledgers.Entry.Ballot{b}) == True{}: Bool
  } -> {
    Ledgers.Ballot.sealed(key, a) == True{}: Bool
  } -> {
    Ledgers.Ballot.sealed(key, b) == True{}: Bool
  } -> {
    a != b: Ledgers.Ballot
  } -> {
    Led.get(
      ~mach,
      ~d,
      Kind.ledger(mach, d, k)(s),
      Entry.name(~mach, Ledgers.Entry.Lie{Ledgers.Lie{key, a, b}})
    )
      == None{}: Maybe<&2, Entry(mach)>
  } -> Entries.Agree(
    mach,
    Deed.entries(Machine.Q(mach), x),
    Ledgers.Entry.Lie{Ledgers.Lie{key, a, b}}
  ) -> {
    List.contains(
      ~String,
      ~String.eq,
      Ledgers.Kind.liars(
        Machine.Q(mach),
        Led.kind(mach, d)
      )(
        Kind.ledger(mach, d, k)(Kind.does(mach, d, k)(s)(x))
      )(Ledgers.Ballot.root(a)),
      Ledgers.Ballot.voter(a)
    )
      == True{}: Bool
  }

# a replica that passes on a line is then in a higher round: at the newest
# tip of a line where it is a voter and has a key, after the deed of a pass,
# the round that it is in is above the round that it was in
def Laws.Passes(
  -mach: Machine(),
  -d: Led(mach),
  -kern: Kernel(mach, d),
  -k: Replica.Kind(mach, d)
) -> Type:
  @s: Kind.R(
    mach,
    d,
    k
  ) -> @c: Ledgers.Line -> @h: U32 -> @t: Tip -> Line.Top(
    mach,
    d,
    kern,
    Kind.ledger(mach, d, k)(s),
    c,
    h,
    t
  ) -> {
    List.contains(~String, ~String.eq, Tip.voters(t), Kind.name(mach, d, k)(s)) == True{}: Bool
  } -> Replica.Keyed(
    mach,
    d,
    kern,
    k,
    s,
    Line.root(c)
  ) -> {
    Nat.is_lt(
      Round.now(~mach, ~d, Kind.ledger(mach, d, k)(s), c, h, Kind.name(mach, d, k)(s)),
      Round.now(
        ~mach,
        ~d,
        Kind.ledger(mach, d, k)(Kind.does(mach, d, k)(s)(Deed.Pass{c})),
        c,
        h,
        Kind.name(mach, d, k)(s)
      )
    )
      == True{}: Bool
  }

# the laws of a replica of the kind k, for the kernel kern
def Replica.Laws(
  -mach: Machine(),
  -d: Led(mach),
  -kern: Kernel(mach, d),
  -k: Replica.Kind(mach, d)
) -> Type:
  Laws.Empty(mach, d, k)
    & (
      Laws.Keeps(mach, d, k)
        & (
          Laws.Grows(mach, d, k)
            & (
              Laws.Good(mach, d, kern, k)
                & (
                  Laws.Takes(mach, d, kern, k)
                    & (
                      Laws.Detects(mach, d, k)
                        & (
                          Laws.Passes(mach, d, kern, k)
                            & (Laws.Drops(mach, d, kern, k) & Laws.Count(mach, d, k))
                        )
                    )
                )
            )
        )
    )

# a replica of a machine, for a ledger and a kernel: a way to hold a ledger
# and act on it, and the proof that it obeys the laws
def Replica(-mach: Machine(), -d: Led(mach), -kern: Kernel(mach, d)) -> Type:
  &k: Replica.Kind(mach, d) -> Replica.Laws(mach, d, kern, k)

# Laws
# ----
# What holds of every ledger and every kernel, by the defs above.

# Proofs of the laws
# ------------------
# Growth of a ledger, and the laws of its parts, as the proofs below use them.

# the laws of the ledger d
def Hist.laws(-mach: Machine(), d: Led(mach)) -> Ledgers.Ledger.Laws(
  Machine.Q(mach),
  Machine.code(mach),
  Led.kind(mach, d)
):
  match d:
    case Tuple{x, t}:
      Ledgers.Ledger.laws(Machine.Q(mach), Machine.code(mach), x)

# the law of an added entry, of the laws ls
def Hist.laws.add(
  -Q: Data,
  -c: Codes.Codec(Q),
  -k: Ledgers.Ledger.Kind(Q),
  ls: Ledgers.Ledger.Laws(Q, c, k)
) -> Ledgers.Laws.GetAdd(Q, c, k):
  match ls:
    case Tuple{e, Tuple{a, r}}:
      a

# the law of an added entry, of the ledger d
def Hist.get_add(-mach: Machine(), d: Led(mach)) -> Ledgers.Laws.GetAdd(
  Machine.Q(mach),
  Machine.code(mach),
  Led.kind(mach, d)
):
  Hist.laws.add(Machine.Q(mach), Machine.code(mach), Led.kind(mach, d), Hist.laws(mach, d))

# a ledger grows from itself
def Hist.refl(-mach: Machine(), -d: Led(mach), -l: Led.L(mach, d)) -> Led.Grows(mach, d, l, l):
  n => e => h => h

# growth is transitive
def Hist.trans(
  -mach: Machine(),
  -d: Led(mach),
  -a: Led.L(mach, d),
  -b: Led.L(mach, d),
  -c: Led.L(mach, d),
  g1: Led.Grows(mach, d, a, b),
  g2: Led.Grows(mach, d, b, c)
) -> Led.Grows(mach, d, a, c):
  +n => +e => h => g2(n)(e)(g1(n)(e)(h))

# a ledger grows by an entry
def Hist.add(~mach: Machine(), ~d: Led(mach), l: Led.L(mach, d), x: Entry(mach)) -> Led.Grows(
  mach,
  d,
  l,
  Led.add(~mach, ~d, l, x)
):
  +n => +e => h =>
    %Equal.sym(
      Maybe<&2, Entry(mach)>,
      Led.get(~mach, ~d, Led.add(~mach, ~d, l, x), n),
      Maybe.or(
        &2,
        Entry(mach),
        Led.get(~mach, ~d, l, n),
        Shared.Maybe.when(
          Entry(mach),
          Ledgers.Name.is_eq(Entry.name(~mach, x), n),
          u => Some{x}
        )
      ),
      Hist.get_add(mach, d)(l)(x)(n)
    ): {_ == Some{e}: Maybe<&2, Entry(mach)>}
    %Equal.sym(Maybe<&2, Entry(mach)>, Led.get(~mach, ~d, l, n), Some{e}, h): {
      Maybe.or(
        &2,
        Entry(mach),
        _,
        Shared.Maybe.when(
          Entry(mach),
          Ledgers.Name.is_eq(Entry.name(~mach, x), n),
          u => Some{x}
        )
      )
        == Some{e}: Maybe<&2, Entry(mach)>
    }
    {==}

# a ledger grows by the data ns
def Hist.puts(~mach: Machine(), ~d: Led(mach), ns: List<&2, List<&2, U32>>, +l: Led.L(mach, d)) -> Led.Grows(
  mach,
  d,
  l,
  Led.puts(~mach, ~d, ns, l)
):
  match ns:
    case Nil{}:
      Hist.refl(mach, d, l)
    case Con{+ws, rest}:
      Hist.trans(
        mach,
        d,
        l,
        Led.add(~mach, ~d, l, Ledgers.Entry.Data{ws}),
        Led.puts(~mach, ~d, rest, Led.add(~mach, ~d, l, Ledgers.Entry.Data{ws})),
        Hist.add(~mach, ~d, l, Ledgers.Entry.Data{ws}),
        Hist.puts(~mach, ~d, rest, Led.add(~mach, ~d, l, Ledgers.Entry.Data{ws}))
      )

# the words of an entry that grows stay
def Hist.words(
  -mach: Machine(),
  m: Maybe<&2, Entry(mach)>,
  -m2: Maybe<&2, Entry(mach)>,
  -w: List<&2, U32>,
  hm: @e: Entry(mach) -> {m == Some{e}: Maybe<&2, Entry(mach)>} -> {m2 == Some{e}: Maybe<&2, Entry(mach)>}
) -> {Ledgers.Entry.words(Machine.Q(mach), m) == Some{w}: Maybe<&2, List<&2, U32>>}
  -> {Ledgers.Entry.words(Machine.Q(mach), m2) == Some{w}: Maybe<&2, List<&2, U32>>}:
  match m:
    case None{}:
      e => Empty.absurd(
        {Ledgers.Entry.words(Machine.Q(mach), m2) == Some{w}: Maybe<&2, List<&2, U32>>},
        Shared.Maybe.none_ne_some(List<&2, U32>, w, e)
      )
    case Some{x}:
      e =>
        %Equal.sym(Maybe<&2, Entry(mach)>, m2, Some{x}, hm(x)({==})): {
          Ledgers.Entry.words(Machine.Q(mach), _) == Some{w}: Maybe<&2, List<&2, U32>>
        }
        e

# the data of a ledger stays as it grows
def Hist.fetch(
  ~mach: Machine(),
  ~d: Led(mach),
  a: Led.L(mach, d),
  -b: Led.L(mach, d),
  +h: Hashes.Hash,
  -w: List<&2, U32>,
  g: Led.Grows(mach, d, a, b)
) -> {Led.fetch(~mach, ~d, a, h) == Some{w}: Maybe<&2, List<&2, U32>>}
  -> {Led.fetch(~mach, ~d, b, h) == Some{w}: Maybe<&2, List<&2, U32>>}:
  Hist.words(
    mach,
    Led.get(~mach, ~d, a, Ledgers.Name.Data{h}),
    Led.get(~mach, ~d, b, Ledgers.Name.Data{h}),
    w,
    e => g(Ledgers.Name.Data{h})(e)
  )

# a ledger that holds some words gives them under their hash
def Hist.has(
  ~mach: Machine(),
  ~d: Led(mach),
  l: Led.L(mach, d),
  +ws: List<&2, U32>
) -> {
  Depots.Depot.has(~Led.L(mach, d), ~(s => h => Led.fetch(~mach, ~d, s, h)), l, ws) == True{}: Bool
} -> {Led.fetch(~mach, ~d, l, Hashes.Sha.hash(ws)) == Some{ws}: Maybe<&2, List<&2, U32>>}:
  h => Shared.Maybe.is_eq_sound(
    ~List<&2, U32>,
    ~Shared.List.is_eq(~U32, ~U32.is_eq),
    x => y => Shared.List.is_eq_sound(~U32, ~U32.is_eq, ~Shared.U32.laws(), x, y),
    Led.fetch(~mach, ~d, l, Hashes.Sha.hash(ws)),
    Some{ws}
  )(h)

# and a ledger that gives some words under their hash holds them
def Hist.has.of(
  ~mach: Machine(),
  ~d: Led(mach),
  -l: Led.L(mach, d),
  +ws: List<&2, U32>
) -> {Led.fetch(~mach, ~d, l, Hashes.Sha.hash(ws)) == Some{ws}: Maybe<&2, List<&2, U32>>}
  -> {Depots.Depot.has(~Led.L(mach, d), ~(s => h => Led.fetch(~mach, ~d, s, h)), l, ws) == True{}: Bool}:
  h =>
    %Equal.sym(Maybe<&2, List<&2, U32>>, Led.fetch(~mach, ~d, l, Hashes.Sha.hash(ws)), Some{ws}, h): {
      Shared.Maybe.is_eq(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), _, Some{ws}) == True{}: Bool
    }
    Shared.List.is_eq_refl(~U32, ~U32.is_eq, ~Shared.U32.laws(), ws)

# the law that a read stays, of a tree t
def Hist.final.of(
  -S: Data,
  -fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  -grows: S -> S -> Type,
  t: Trees.Tree(S, fetch, grows)
) -> Trees.Laws.Final(S, grows, Trees.Tree.ops(S, fetch, grows, t)):
  match t:
    case Tuple{o, Tuple{f, r}}:
      f

# the law that a write stays, of a tree t
def Hist.put_final.of(
  -S: Data,
  -fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  -grows: S -> S -> Type,
  t: Trees.Tree(S, fetch, grows)
) -> Trees.Laws.PutFinal(S, grows, Trees.Tree.ops(S, fetch, grows, t)):
  match t:
    case Tuple{o, Tuple{f, Tuple{p, r}}}:
      p

# the law of a write, of a tree t
def Hist.write.of(
  -S: Data,
  -fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  -grows: S -> S -> Type,
  t: Trees.Tree(S, fetch, grows)
) -> Trees.Laws.Write(S, fetch, grows, Trees.Tree.ops(S, fetch, grows, t)):
  match t:
    case Tuple{o, Tuple{f, Tuple{p, Tuple{w, r}}}}:
      w

# the law that a read stays, of the tree of the ledger d
def Hist.final(-mach: Machine(), d: Led(mach)) -> Trees.Laws.Final(
  Led.L(mach, d),
  a => b => Led.Grows(mach, d, a, b),
  Led.tree(mach, d)
):
  match d:
    case Tuple{x, t}:
      Hist.final.of(
        Ledgers.Kind.L(Machine.Q(mach), Ledgers.Ledger.kind(Machine.Q(mach), Machine.code(mach), x)),
        Ledgers.Kind.data(Machine.Q(mach), Ledgers.Ledger.kind(Machine.Q(mach), Machine.code(mach), x)),
        a => b => Ledgers.Kind.Grows(
          Machine.Q(mach),
          Ledgers.Ledger.kind(Machine.Q(mach), Machine.code(mach), x),
          a,
          b
        ),
        t
      )

# the law that a write stays, of the tree of the ledger d
def Hist.put_final(-mach: Machine(), d: Led(mach)) -> Trees.Laws.PutFinal(
  Led.L(mach, d),
  a => b => Led.Grows(mach, d, a, b),
  Led.tree(mach, d)
):
  match d:
    case Tuple{x, t}:
      Hist.put_final.of(
        Ledgers.Kind.L(Machine.Q(mach), Ledgers.Ledger.kind(Machine.Q(mach), Machine.code(mach), x)),
        Ledgers.Kind.data(Machine.Q(mach), Ledgers.Ledger.kind(Machine.Q(mach), Machine.code(mach), x)),
        a => b => Ledgers.Kind.Grows(
          Machine.Q(mach),
          Ledgers.Ledger.kind(Machine.Q(mach), Machine.code(mach), x),
          a,
          b
        ),
        t
      )

# the law of a write, of the tree of the ledger d
def Hist.write(-mach: Machine(), d: Led(mach)) -> Trees.Laws.Write(
  Led.L(mach, d),
  l => h => Led.fetch(~mach, ~d, l, h),
  a => b => Led.Grows(mach, d, a, b),
  Led.tree(mach, d)
):
  match d:
    case Tuple{x, t}:
      Hist.write.of(
        Ledgers.Kind.L(Machine.Q(mach), Ledgers.Ledger.kind(Machine.Q(mach), Machine.code(mach), x)),
        Ledgers.Kind.data(Machine.Q(mach), Ledgers.Ledger.kind(Machine.Q(mach), Machine.code(mach), x)),
        a => b => Ledgers.Kind.Grows(
          Machine.Q(mach),
          Ledgers.Ledger.kind(Machine.Q(mach), Machine.code(mach), x),
          a,
          b
        ),
        t
      )

# what a read of a tree tells stays as the ledger grows
def Hist.find(
  ~mach: Machine(),
  ~d: Led(mach),
  a: Led.L(mach, d),
  b: Led.L(mach, d),
  h: Maybe<&2, Hashes.Hash>,
  k: List<&2, U32>,
  x: Maybe<&2, List<&2, U32>>,
  g: Led.Grows(mach, d, a, b)
) -> {Tree.find(~mach, ~d, a, h, k) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
  -> {Tree.find(~mach, ~d, b, h, k) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}:
  e => Hist.final(mach, d)(h)(k)(a)(b)(x)(g)(e)

# a write to a tree stays as the ledger grows
def Hist.put(
  ~mach: Machine(),
  ~d: Led(mach),
  a: Led.L(mach, d),
  b: Led.L(mach, d),
  h: Maybe<&2, Hashes.Hash>,
  k: List<&2, U32>,
  m: Maybe<&2, List<&2, U32>>,
  x: Trees.Edit,
  g: Led.Grows(mach, d, a, b)
) -> {Tree.put(~mach, ~d, a, h, k, m) == Some{x}: Maybe<&2, Trees.Edit>}
  -> {Tree.put(~mach, ~d, b, h, k, m) == Some{x}: Maybe<&2, Trees.Edit>}:
  e => Hist.put_final(mach, d)(a)(b)(h)(k)(m)(x)(e)(g)

# the law that an act stays, of the kernel kern
def Hist.kern(-mach: Machine(), -d: Led(mach), kern: Kernel(mach, d)) -> Kernel.Stable(
  mach,
  d,
  Kernel.change(mach, d, kern)
):
  match kern:
    case Tuple{f, Tuple{s, w}}:
      s

# Safety of rounds
# ----------------
# Two majorities of the voters of a height share a voter: the voters whose
# passes allow a step, and the voters that cast the step of an earlier round.

# the ballots of the voters os at the place w, for the step v and against it,
# count the voters
def Safe.yes_no.at(+h: Bool, a: Nat, b: Nat) -> {
  Nat.add(Shared.Nat.add_if(h, a), Shared.Nat.add_if(Bool.not(h), b)) == 1n+Nat.add(a, b): Nat
}:
  match h:
    case True{}:
      {==}
    case False{}:
      Shared.Nat.add_succ(a, b)

# the ballots for the step v and against it count the voters os
def Safe.yes_no(
  ~mach: Machine(),
  ~d: Led(mach),
  +l: Led.L(mach, d),
  +w: Ledgers.Place,
  os: List<&2, String>,
  +v: Ledgers.Step
) -> {
  Nat.add(
    Quorums.Quorum.yes(~Ledgers.Step, ~Ledgers.Step.is_eq, Ledgers.Kind.cells(~Machine.Q(mach), ~Led.kind(mach, d), l, w, os), v),
    Quorums.Quorum.no(~Ledgers.Step, ~Ledgers.Step.is_eq, Ledgers.Kind.cells(~Machine.Q(mach), ~Led.kind(mach, d), l, w, os), v)
  )
    == List.length(&2, String, os): Nat
}:
  match os:
    case Nil{}:
      {==}
    case Con{o, +r}:
      +y = Quorums.Quorum.yes(~Ledgers.Step, ~Ledgers.Step.is_eq, Ledgers.Kind.cells(~Machine.Q(mach), ~Led.kind(mach, d), l, w, r), v)
      +n = Quorums.Quorum.no(~Ledgers.Step, ~Ledgers.Step.is_eq, Ledgers.Kind.cells(~Machine.Q(mach), ~Led.kind(mach, d), l, w, r), v)
      Equal.trans(
        Nat,
        Nat.add(
          Shared.Nat.add_if(
            Quorums.Quorum.hit(~Ledgers.Step, ~Ledgers.Step.is_eq, Ledgers.Kind.cell(~Machine.Q(mach), ~Led.kind(mach, d), l, w, o), v),
            y
          ),
          Shared.Nat.add_if(
            Bool.not(
              Quorums.Quorum.hit(~Ledgers.Step, ~Ledgers.Step.is_eq, Ledgers.Kind.cell(~Machine.Q(mach), ~Led.kind(mach, d), l, w, o), v)
            ),
            n
          )
        ),
        1n+Nat.add(y, n),
        1n+List.length(&2, String, r),
        Safe.yes_no.at(
          Quorums.Quorum.hit(~Ledgers.Step, ~Ledgers.Step.is_eq, Ledgers.Kind.cell(~Machine.Q(mach), ~Led.kind(mach, d), l, w, o), v),
          y,
          n
        ),
        Equal.cong(Nat, Nat, x => 1n+x, Nat.add(y, n), List.length(&2, String, r), Safe.yes_no(~mach, ~d, l, w, r, v))
      )

# one more voter, for or against: the bound grows by one
def Safe.count_step(+hb: Bool, a: Nat, b: Nat, n: Nat) -> {Nat.is_le(n, Nat.add(a, b)) == True{}: Bool}
  -> {Nat.is_le(1n+n, Nat.add(Shared.Nat.add_if(Bool.not(hb), a), Shared.Nat.add_if(hb, b))) == True{}: Bool}:
  match hb:
    case True{}:
      h =>
        %Equal.sym(Nat, Nat.add(a, 1n+b), 1n+Nat.add(a, b), Shared.Nat.add_succ(a, b)): {
          Nat.is_le(1n+n, _) == True{}: Bool
        }
        h
    case False{}:
      h => h

# a voter more against: the bound stays
def Safe.count_skip(+hb: Bool, +a: Nat, +c: Nat, n: Nat) -> {Nat.is_le(n, Nat.add(a, c)) == True{}: Bool}
  -> {Nat.is_le(n, Nat.add(Shared.Nat.add_if(hb, a), c)) == True{}: Bool}:
  h => Shared.Nat.le_trans(
    n,
    Nat.add(a, c),
    Nat.add(Shared.Nat.add_if(hb, a), c)
  )(h)(
    Shared.Nat.add_le_right(
      Shared.Nat.add_if(hb, a),
      a,
      c
    )(Shared.Nat.le_add_if(hb, a, a)(Shared.Nat.le_refl(a)))
  )

# some of the voters os are at most the voters os against v, and those of
# them for v
def Safe.sub_count(
  ~mach: Machine(),
  ~d: Led(mach),
  +l: Led.L(mach, d),
  +w: Ledgers.Place,
  os: List<&2, String>,
  from: List<&2, String>,
  +v: Ledgers.Step
) -> {Voters.sub(os, from) == True{}: Bool} -> {
  Nat.is_le(
    List.length(&2, String, from),
    Nat.add(
      Quorums.Quorum.no(~Ledgers.Step, ~Ledgers.Step.is_eq, Ledgers.Kind.cells(~Machine.Q(mach), ~Led.kind(mach, d), l, w, os), v),
      Quorums.Quorum.yes(~Ledgers.Step, ~Ledgers.Step.is_eq, Ledgers.Kind.cells(~Machine.Q(mach), ~Led.kind(mach, d), l, w, from), v)
    )
  )
    == True{}: Bool
}:
  match os from:
    case Nil{} Nil{}:
      h => {==}
    case Nil{} Con{f, fs}:
      h => Empty.absurd(
        {
          Nat.is_le(
            List.length(&2, String, f <> fs),
            Nat.add(
              0n,
              Quorums.Quorum.yes(
                ~Ledgers.Step,
                ~Ledgers.Step.is_eq,
                Ledgers.Kind.cells(~Machine.Q(mach), ~Led.kind(mach, d), l, w, f <> fs),
                v
              )
            )
          )
            == True{}: Bool
        },
        Shared.Bool.false_ne_true(h)
      )
    case Con{o, r} Nil{}:
      h => Shared.Nat.le_zero(
        Nat.add(
          Quorums.Quorum.no(
            ~Ledgers.Step,
            ~Ledgers.Step.is_eq,
            Ledgers.Kind.cells(~Machine.Q(mach), ~Led.kind(mach, d), l, w, o <> r),
            v
          ),
          0n
        )
      )
    case Con{+o, +r} Con{+f, +fs}:
      Shared.Bool.when_cases(
        Bool,
        x => {x == True{}: Bool} -> {
          Nat.is_le(
            List.length(&2, String, f <> fs),
            Nat.add(
              Quorums.Quorum.no(
                ~Ledgers.Step,
                ~Ledgers.Step.is_eq,
                Ledgers.Kind.cells(~Machine.Q(mach), ~Led.kind(mach, d), l, w, o <> r),
                v
              ),
              Quorums.Quorum.yes(
                ~Ledgers.Step,
                ~Ledgers.Step.is_eq,
                Ledgers.Kind.cells(~Machine.Q(mach), ~Led.kind(mach, d), l, w, f <> fs),
                v
              )
            )
          )
            == True{}: Bool
        },
        String.eq(f, o),
        u => Voters.sub(r, fs),
        u => Voters.sub(r, f <> fs),
        ef => h =>
          %Equal.sym(String, f, o, Texts.String.eq_sound(f, o)(ef)): {
            Nat.is_le(
              1n+List.length(&2, String, fs),
              Nat.add(
                Quorums.Quorum.no(
                  ~Ledgers.Step,
                  ~Ledgers.Step.is_eq,
                  Ledgers.Kind.cells(~Machine.Q(mach), ~Led.kind(mach, d), l, w, o <> r),
                  v
                ),
                Quorums.Quorum.yes(
                  ~Ledgers.Step,
                  ~Ledgers.Step.is_eq,
                  Ledgers.Kind.cells(~Machine.Q(mach), ~Led.kind(mach, d), l, w, _ <> fs),
                  v
                )
              )
            )
              == True{}: Bool
          }
          Safe.count_step(
            Quorums.Quorum.hit(~Ledgers.Step, ~Ledgers.Step.is_eq, Ledgers.Kind.cell(~Machine.Q(mach), ~Led.kind(mach, d), l, w, o), v),
            Quorums.Quorum.no(~Ledgers.Step, ~Ledgers.Step.is_eq, Ledgers.Kind.cells(~Machine.Q(mach), ~Led.kind(mach, d), l, w, r), v),
            Quorums.Quorum.yes(~Ledgers.Step, ~Ledgers.Step.is_eq, Ledgers.Kind.cells(~Machine.Q(mach), ~Led.kind(mach, d), l, w, fs), v),
            List.length(&2, String, fs)
          )(Safe.sub_count(~mach, ~d, l, w, r, fs, v)(h)),
        ef => h => Safe.count_skip(
          Bool.not(
            Quorums.Quorum.hit(~Ledgers.Step, ~Ledgers.Step.is_eq, Ledgers.Kind.cell(~Machine.Q(mach), ~Led.kind(mach, d), l, w, o), v)
          ),
          Quorums.Quorum.no(~Ledgers.Step, ~Ledgers.Step.is_eq, Ledgers.Kind.cells(~Machine.Q(mach), ~Led.kind(mach, d), l, w, r), v),
          Quorums.Quorum.yes(~Ledgers.Step, ~Ledgers.Step.is_eq, Ledgers.Kind.cells(~Machine.Q(mach), ~Led.kind(mach, d), l, w, f <> fs), v),
          List.length(&2, String, f <> fs)
        )(Safe.sub_count(~mach, ~d, l, w, r, f <> fs, v)(h))
      )

# what the laws of a later ledger give, as premises: a proof takes each as a
# template, so it may use it as often as it needs (Led.later_grows,
# Led.later_single, Led.later_last)
def Hist.LaterGrows(-mach: Machine(), -d: Led(mach)) -> Type:
  @a: Led.L(mach, d) -> @b: Led.L(mach, d) -> Led.Later(~mach, ~d, a, b) -> Led.Grows(mach, d, a, b)

# that the ballots of a later ledger cast one vote at a place and one pass
def Hist.LaterSingle(-mach: Machine(), -d: Led(mach)) -> Type:
  @a: Led.L(mach, d) -> @b: Led.L(mach, d) -> Led.Later(~mach, ~d, a, b) -> Led.Single(mach, d, b)

# that the passes of a later ledger name the last vote of their voter
def Hist.LaterLast(-mach: Machine(), -d: Led(mach)) -> Type:
  @a: Led.L(mach, d) -> @b: Led.L(mach, d) -> @c: Ledgers.Line -> @h: U32 -> Led.Later(~mach, ~d, a, b)
    -> Rounds.Last(mach, d, b, c, h)

# Safety of rounds: the decision of a height
# -------------------------------------------

# a height decides the same step in a later ledger
def Safe.decide(
  ~mach: Machine(),
  ~d: Led(mach),
  ~lg: Hist.LaterGrows(mach, d),
  ~ls: Hist.LaterSingle(mach, d),
  ~ll: Hist.LaterLast(mach, d),
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  +later: {
    Bool.and(
      Ledgers.Kind.grows(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), a, b),
      Led.honest(~mach, ~d, b)
    )
      == True{}: Bool
  },
  +c: Ledgers.Line,
  +h: U32,
  +os: List<&2, String>,
  +v: Ledgers.Step
) -> {
  Height.decide(
    ~mach,
    ~d,
    a,
    c,
    h,
    os,
    Ledgers.Kind.rounds(Machine.Q(mach), Led.kind(mach, d))(a)(c)(h)
  )
    == Some{v}: Maybe<&2, Ledgers.Step>
} -> {
  Height.decide(
    ~mach,
    ~d,
    b,
    c,
    h,
    os,
    Ledgers.Kind.rounds(Machine.Q(mach), Led.kind(mach, d))(b)(c)(h)
  )
    == Some{v}: Maybe<&2, Ledgers.Step>
}:
  ?TODO

# Runs of a step
# --------------

# Gains of a run
# --------------
# A run only adds: its added nodes grow at their front, and its ledger is the
# ledger before with some data put, the same nodes in another order.

# the ledger l holds each of the words ns, under their hashes
def Ext.holds(~mach: Machine(), ~d: Led(mach), +l: Led.L(mach, d), ns: List<&2, List<&2, U32>>) -> Bool:
  Depots.Depot.holds(~Led.L(mach, d), ~(s => h => Led.fetch(~mach, ~d, s, h)), l, ns)

# that the run r2 follows the run r: it added ys at the front of what r added,
# and its ledger is that of r with zs put, where s holds zs when it holds ys
def Ext.Gain(
  -mach: Machine(),
  -d: Led(mach),
  -s: Led.L(mach, d),
  -r: Run<Led.L(mach, d)>,
  -r2: Run<Led.L(mach, d)>
) -> Data:
  +Sigma<List<&2, List<&2, U32>>, ys => +Sigma<List<&2, List<&2, U32>>, zs => +Sigma<
    {
      Run.added(Led.L(mach, d), r2)
        == List.append(&2, List<&2, U32>, ys, Run.added(Led.L(mach, d), r)): List<&2, List<&2, U32>>
    },
    e1 => +Sigma<
      {Run.ledger(Led.L(mach, d), r2) == Led.puts(~mach, ~d, zs, Run.ledger(Led.L(mach, d), r)): Led.L(mach, d)},
      e2 => {Ext.holds(~mach, ~d, s, zs) == Ext.holds(~mach, ~d, s, ys): Bool}>>>>

# Ext.Gain of the run r and the result m of a run, when there is one
def Ext.GainM(
  -mach: Machine(),
  -d: Led(mach),
  -s: Led.L(mach, d),
  -r: Run<Led.L(mach, d)>,
  m: Maybe<&2, Run<Led.L(mach, d)>>
) -> Data:
  match m:
    case None{}:
      Unit
    case Some{r2}:
      Ext.Gain(mach, d, s, r, r2)

# an "and" is the same either way round
def Ext.and_comm(a: Bool, b: Bool) -> {Bool.and(a, b) == Bool.and(b, a): Bool}:
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

# the ledger l holds the words ws, under their hash
def Ext.has(~mach: Machine(), ~d: Led(mach), l: Led.L(mach, d), +ws: List<&2, U32>) -> Bool:
  Depots.Depot.has(~Led.L(mach, d), ~(s => h => Led.fetch(~mach, ~d, s, h)), l, ws)

# Ext.holds_append once whether l holds w is known (hb)
def Ext.holds_append.at(
  ~mach: Machine(),
  ~d: Led(mach),
  +l: Led.L(mach, d),
  +w: List<&2, U32>,
  r: List<&2, List<&2, U32>>,
  +ys: List<&2, List<&2, U32>>,
  hb: Bool,
  eh: {Ext.has(~mach, ~d, l, w) == hb: Bool},
  ih: {
    Ext.holds(~mach, ~d, l, List.append(&2, List<&2, U32>, r, ys))
      == Bool.and(Ext.holds(~mach, ~d, l, r), Ext.holds(~mach, ~d, l, ys)): Bool
  }
) -> {
  List.all.if(u => Ext.holds(~mach, ~d, l, List.append(&2, List<&2, U32>, r, ys)), Ext.has(~mach, ~d, l, w))
    == Bool.and(
      List.all.if(u => Ext.holds(~mach, ~d, l, r), Ext.has(~mach, ~d, l, w)),
      Ext.holds(~mach, ~d, l, ys)
    ): Bool
}:
  match hb:
    case True{}:
      %Equal.sym(Bool, Ext.has(~mach, ~d, l, w), True{}, eh): {
        List.all.if(u => Ext.holds(~mach, ~d, l, List.append(&2, List<&2, U32>, r, ys)), _)
          == Bool.and(List.all.if(u => Ext.holds(~mach, ~d, l, r), _), Ext.holds(~mach, ~d, l, ys)): Bool
      }
      ih
    case False{}:
      %Equal.sym(Bool, Ext.has(~mach, ~d, l, w), False{}, eh): {
        List.all.if(u => Ext.holds(~mach, ~d, l, List.append(&2, List<&2, U32>, r, ys)), _)
          == Bool.and(List.all.if(u => Ext.holds(~mach, ~d, l, r), _), Ext.holds(~mach, ~d, l, ys)): Bool
      }
      {==}

# a ledger holds two lists of words when it holds each
def Ext.holds_append(
  ~mach: Machine(),
  ~d: Led(mach),
  +l: Led.L(mach, d),
  xs: List<&2, List<&2, U32>>,
  +ys: List<&2, List<&2, U32>>
) -> {
  Ext.holds(~mach, ~d, l, List.append(&2, List<&2, U32>, xs, ys))
    == Bool.and(Ext.holds(~mach, ~d, l, xs), Ext.holds(~mach, ~d, l, ys)): Bool
}:
  match xs:
    case Nil{}:
      {==}
    case Con{+w, +r}:
      Ext.holds_append.at(
        ~mach,
        ~d,
        l,
        w,
        r,
        ys,
        Ext.has(~mach, ~d, l, w),
        {==},
        Ext.holds_append(~mach, ~d, l, r, ys)
      )

# a ledger that holds two lists of words holds the first
def Ext.holds_left(
  ~mach: Machine(),
  ~d: Led(mach),
  +l: Led.L(mach, d),
  +xs: List<&2, List<&2, U32>>,
  +ys: List<&2, List<&2, U32>>
) -> {Ext.holds(~mach, ~d, l, List.append(&2, List<&2, U32>, xs, ys)) == True{}: Bool}
  -> {Ext.holds(~mach, ~d, l, xs) == True{}: Bool}:
  h => Shared.Bool.and_true_left(
    Ext.holds(~mach, ~d, l, xs),
    Ext.holds(~mach, ~d, l, ys)
  )(
    Equal.trans(
      Bool,
      Bool.and(Ext.holds(~mach, ~d, l, xs), Ext.holds(~mach, ~d, l, ys)),
      Ext.holds(~mach, ~d, l, List.append(&2, List<&2, U32>, xs, ys)),
      True{},
      Equal.sym(
        Bool,
        Ext.holds(~mach, ~d, l, List.append(&2, List<&2, U32>, xs, ys)),
        Bool.and(Ext.holds(~mach, ~d, l, xs), Ext.holds(~mach, ~d, l, ys)),
        Ext.holds_append(~mach, ~d, l, xs, ys)
      ),
      h
    )
  )

# a ledger that holds two lists of words holds the second
def Ext.holds_right(
  ~mach: Machine(),
  ~d: Led(mach),
  +l: Led.L(mach, d),
  +xs: List<&2, List<&2, U32>>,
  +ys: List<&2, List<&2, U32>>
) -> {Ext.holds(~mach, ~d, l, List.append(&2, List<&2, U32>, xs, ys)) == True{}: Bool}
  -> {Ext.holds(~mach, ~d, l, ys) == True{}: Bool}:
  h => Shared.Bool.and_true_right(
    Ext.holds(~mach, ~d, l, xs),
    Ext.holds(~mach, ~d, l, ys)
  )(
    Equal.trans(
      Bool,
      Bool.and(Ext.holds(~mach, ~d, l, xs), Ext.holds(~mach, ~d, l, ys)),
      Ext.holds(~mach, ~d, l, List.append(&2, List<&2, U32>, xs, ys)),
      True{},
      Equal.sym(
        Bool,
        Ext.holds(~mach, ~d, l, List.append(&2, List<&2, U32>, xs, ys)),
        Bool.and(Ext.holds(~mach, ~d, l, xs), Ext.holds(~mach, ~d, l, ys)),
        Ext.holds_append(~mach, ~d, l, xs, ys)
      ),
      h
    )
  )

# putting xs, then ys, is putting xs then ys at once
def Ext.puts_append(
  ~mach: Machine(),
  ~d: Led(mach),
  xs: List<&2, List<&2, U32>>,
  +ys: List<&2, List<&2, U32>>,
  +l: Led.L(mach, d)
) -> {
  Led.puts(~mach, ~d, ys, Led.puts(~mach, ~d, xs, l))
    == Led.puts(~mach, ~d, List.append(&2, List<&2, U32>, xs, ys), l): Led.L(mach, d)
}:
  match xs:
    case Nil{}:
      {==}
    case Con{+w, r}:
      Ext.puts_append(~mach, ~d, r, ys, Led.add(~mach, ~d, l, Ledgers.Entry.Data{w}))

# the check of two gains: s holds the puts when it holds the added nodes
def Ext.trans.holds(
  ~mach: Machine(),
  ~d: Led(mach),
  +s: Led.L(mach, d),
  +ys1: List<&2, List<&2, U32>>,
  +zs1: List<&2, List<&2, U32>>,
  +ys2: List<&2, List<&2, U32>>,
  +zs2: List<&2, List<&2, U32>>,
  h1: {Ext.holds(~mach, ~d, s, zs1) == Ext.holds(~mach, ~d, s, ys1): Bool},
  h2: {Ext.holds(~mach, ~d, s, zs2) == Ext.holds(~mach, ~d, s, ys2): Bool}
) -> {
  Ext.holds(~mach, ~d, s, List.append(&2, List<&2, U32>, zs1, zs2))
    == Ext.holds(~mach, ~d, s, List.append(&2, List<&2, U32>, ys2, ys1)): Bool
}:
  %Equal.sym(
    Bool,
    Ext.holds(~mach, ~d, s, List.append(&2, List<&2, U32>, zs1, zs2)),
    Bool.and(Ext.holds(~mach, ~d, s, zs1), Ext.holds(~mach, ~d, s, zs2)),
    Ext.holds_append(~mach, ~d, s, zs1, zs2)
  ): {_ == Ext.holds(~mach, ~d, s, List.append(&2, List<&2, U32>, ys2, ys1)): Bool}
  %Equal.sym(Bool, Ext.holds(~mach, ~d, s, zs1), Ext.holds(~mach, ~d, s, ys1), h1): {
    Bool.and(_, Ext.holds(~mach, ~d, s, zs2)) == Ext.holds(~mach, ~d, s, List.append(&2, List<&2, U32>, ys2, ys1)): Bool
  }
  %Equal.sym(Bool, Ext.holds(~mach, ~d, s, zs2), Ext.holds(~mach, ~d, s, ys2), h2): {
    Bool.and(Ext.holds(~mach, ~d, s, ys1), _) == Ext.holds(~mach, ~d, s, List.append(&2, List<&2, U32>, ys2, ys1)): Bool
  }
  %Equal.sym(
    Bool,
    Ext.holds(~mach, ~d, s, List.append(&2, List<&2, U32>, ys2, ys1)),
    Bool.and(Ext.holds(~mach, ~d, s, ys2), Ext.holds(~mach, ~d, s, ys1)),
    Ext.holds_append(~mach, ~d, s, ys2, ys1)
  ): {Bool.and(Ext.holds(~mach, ~d, s, ys1), Ext.holds(~mach, ~d, s, ys2)) == _: Bool}
  Ext.and_comm(Ext.holds(~mach, ~d, s, ys1), Ext.holds(~mach, ~d, s, ys2))

# a run follows itself
def Ext.refl(-mach: Machine(), -d: Led(mach), -s: Led.L(mach, d), -r: Run<Led.L(mach, d)>) -> Ext.Gain(mach, d, s, r, r):
  Tuple{[], Tuple{[], Tuple{{==}, Tuple{{==}, {==}}}}}

# a run that follows a run that follows r follows r
def Ext.trans(
  ~mach: Machine(),
  ~d: Led(mach),
  +s: Led.L(mach, d),
  +r: Run<Led.L(mach, d)>,
  +r1: Run<Led.L(mach, d)>,
  +r2: Run<Led.L(mach, d)>,
  g1: Ext.Gain(mach, d, s, r, r1),
  g2: Ext.Gain(mach, d, s, r1, r2)
) -> Ext.Gain(mach, d, s, r, r2):
  match g1:
    case Tuple{+ys1, Tuple{+zs1, Tuple{a1, Tuple{l1, h1}}}}:
      match g2:
        case Tuple{+ys2, Tuple{+zs2, Tuple{a2, Tuple{l2, h2}}}}:
          Tuple{
            List.append(&2, List<&2, U32>, ys2, ys1),
            Tuple{
              List.append(&2, List<&2, U32>, zs1, zs2),
              Tuple{
                Equal.trans(
                  List<&2, List<&2, U32>>,
                  Run.added(Led.L(mach, d), r2),
                  List.append(&2, List<&2, U32>, ys2, Run.added(Led.L(mach, d), r1)),
                  List.append(&2, List<&2, U32>, List.append(&2, List<&2, U32>, ys2, ys1), Run.added(Led.L(mach, d), r)),
                  a2,
                  Equal.trans(
                    List<&2, List<&2, U32>>,
                    List.append(&2, List<&2, U32>, ys2, Run.added(Led.L(mach, d), r1)),
                    List.append(&2, List<&2, U32>, ys2, List.append(&2, List<&2, U32>, ys1, Run.added(Led.L(mach, d), r))),
                    List.append(&2, List<&2, U32>, List.append(&2, List<&2, U32>, ys2, ys1), Run.added(Led.L(mach, d), r)),
                    Equal.cong(
                      List<&2, List<&2, U32>>,
                      List<&2, List<&2, U32>>,
                      z => List.append(&2, List<&2, U32>, ys2, z),
                      Run.added(Led.L(mach, d), r1),
                      List.append(&2, List<&2, U32>, ys1, Run.added(Led.L(mach, d), r)),
                      a1
                    ),
                    Equal.sym(
                      List<&2, List<&2, U32>>,
                      List.append(&2, List<&2, U32>, List.append(&2, List<&2, U32>, ys2, ys1), Run.added(Led.L(mach, d), r)),
                      List.append(&2, List<&2, U32>, ys2, List.append(&2, List<&2, U32>, ys1, Run.added(Led.L(mach, d), r))),
                      Shared.List.append_assoc(List<&2, U32>, ys2, ys1, Run.added(Led.L(mach, d), r))
                    )
                  )
                ),
                Tuple{
                  Equal.trans(
                    Led.L(mach, d),
                    Run.ledger(Led.L(mach, d), r2),
                    Led.puts(~mach, ~d, zs2, Run.ledger(Led.L(mach, d), r1)),
                    Led.puts(~mach, ~d, List.append(&2, List<&2, U32>, zs1, zs2), Run.ledger(Led.L(mach, d), r)),
                    l2,
                    Equal.trans(
                      Led.L(mach, d),
                      Led.puts(~mach, ~d, zs2, Run.ledger(Led.L(mach, d), r1)),
                      Led.puts(~mach, ~d, zs2, Led.puts(~mach, ~d, zs1, Run.ledger(Led.L(mach, d), r))),
                      Led.puts(~mach, ~d, List.append(&2, List<&2, U32>, zs1, zs2), Run.ledger(Led.L(mach, d), r)),
                      Equal.cong(
                        Led.L(mach, d),
                        Led.L(mach, d),
                        z => Led.puts(~mach, ~d, zs2, z),
                        Run.ledger(Led.L(mach, d), r1),
                        Led.puts(~mach, ~d, zs1, Run.ledger(Led.L(mach, d), r)),
                        l1
                      ),
                      Ext.puts_append(~mach, ~d, zs1, zs2, Run.ledger(Led.L(mach, d), r))
                    )
                  ),
                  Ext.trans.holds(~mach, ~d, s, ys1, zs1, ys2, zs2, h1, h2)
                }
              }
            }
          }

# Ext.trans, when the second run may be none
def Ext.transM(
  ~mach: Machine(),
  ~d: Led(mach),
  +s: Led.L(mach, d),
  +r: Run<Led.L(mach, d)>,
  +r1: Run<Led.L(mach, d)>,
  m: Maybe<&2, Run<Led.L(mach, d)>>,
  g: Ext.Gain(mach, d, s, r, r1),
  gm: Ext.GainM(mach, d, s, r1, m)
) -> Ext.GainM(mach, d, s, r, m):
  match m:
    case None{}:
      Unit{}
    case Some{r2}:
      Ext.trans(~mach, ~d, s, r, r1, r2, g, gm)

# a run then a step that follows its run follows r
def Ext.bind(
  ~mach: Machine(),
  ~d: Led(mach),
  +s: Led.L(mach, d),
  +r: Run<Led.L(mach, d)>,
  m: Maybe<&2, Run<Led.L(mach, d)>>,
  g: Run<Led.L(mach, d)> -> Maybe<&2, Run<Led.L(mach, d)>>,
  hm: Ext.GainM(mach, d, s, r, m),
  hg: @r1: Run<Led.L(mach, d)> -> Ext.GainM(mach, d, s, r1, g(r1))
) -> Ext.GainM(mach, d, s, r, Maybe.bind(&2, Run<Led.L(mach, d)>, Run<Led.L(mach, d)>, m, g)):
  match m:
    case None{}:
      Unit{}
    case Some{+r1}:
      Ext.transM(~mach, ~d, s, r, r1, g(r1), hm, hg(r1))

# a run on l at t follows itself after a write to its log
def Ext.logged(
  ~mach: Machine(),
  ~d: Led(mach),
  -s: Led.L(mach, d),
  -l: Led.L(mach, d),
  -t: Tip,
  -a: List<&2, List<&2, U32>>,
  p: Maybe<&2, Trees.Edit>
) -> Ext.GainM(mach, d, s, Run{l, t, a}, Run.logged(~mach, ~d, l, t, a, p)):
  match p:
    case None{}:
      Unit{}
    case Some{+x}:
      Tuple{Trees.Edit.nodes(x), Tuple{Trees.Edit.nodes(x), Tuple{{==}, Tuple{{==}, {==}}}}}

# a run follows itself after Run.add.at
def Ext.add.at(
  ~mach: Machine(),
  ~d: Led(mach),
  -s: Led.L(mach, d),
  r: Run<Led.L(mach, d)>,
  k: List<&2, U32>,
  x: List<&2, U32>,
  m: Maybe<&2, Maybe<&2, List<&2, U32>>>
) -> Ext.GainM(mach, d, s, r, Run.add.at(~mach, ~d, r, k, x, m)):
  match r m:
    case Run{+l, +t, a} Some{None{}}:
      Ext.logged(~mach, ~d, s, l, t, a, Tree.put(~mach, ~d, l, Tip.log(t), k, Some{x}))
    case y Some{Some{old}}:
      Unit{}
    case y None{}:
      Unit{}

# a run follows itself after Run.add
def Ext.add(
  ~mach: Machine(),
  ~d: Led(mach),
  -s: Led.L(mach, d),
  +r: Run<Led.L(mach, d)>,
  +k: List<&2, U32>,
  x: List<&2, U32>
) -> Ext.GainM(mach, d, s, r, Run.add(~mach, ~d, r, k, x)):
  Ext.add.at(
    ~mach,
    ~d,
    s,
    r,
    k,
    x,
    Tip.find(~mach, ~d, Run.ledger(Led.L(mach, d), r), Run.tip(Led.L(mach, d), r), k)
  )

# a run follows itself after a refusal
def Ext.stale(
  ~mach: Machine(),
  ~d: Led(mach),
  -s: Led.L(mach, d),
  +r: Run<Led.L(mach, d)>,
  +i: Ledgers.Id,
  a: Hashes.Hash
) -> Ext.GainM(mach, d, s, r, Step.stale(~mach, ~d, r, i, a)):
  Ext.add(~mach, ~d, s, r, Log.out(i), Out.code(Out.Stale{a}, []))

# a run follows itself one request on
def Ext.next(
  -mach: Machine(),
  -d: Led(mach),
  -s: Led.L(mach, d),
  r: Run<Led.L(mach, d)>,
  -vs: Maybe<&2, List<&2, String>>
) -> Ext.Gain(mach, d, s, r, Run.next(Led.L(mach, d), r, vs)):
  match r:
    case Run{l, t, a}:
      Tuple{[], Tuple{[], Tuple{{==}, Tuple{{==}, {==}}}}}

# a run follows itself with new content
def Ext.over(
  ~mach: Machine(),
  ~d: Led(mach),
  -s: Led.L(mach, d),
  r: Run<Led.L(mach, d)>,
  +ns: List<&2, List<&2, U32>>,
  -h: Maybe<&2, Hashes.Hash>
) -> Ext.Gain(mach, d, s, r, Run.over(~mach, ~d, r, ns, h)):
  match r:
    case Run{l, t, a}:
      Tuple{ns, Tuple{ns, Tuple{{==}, Tuple{{==}, {==}}}}}

# a run follows itself after it took a request
def Ext.taken.at(
  ~mach: Machine(),
  ~d: Led(mach),
  +s: Led.L(mach, d),
  +r: Run<Led.L(mach, d)>,
  +i: Ledgers.Id,
  +a: Hashes.Hash,
  +n: U32,
  +vs: Maybe<&2, List<&2, String>>
) -> Ext.GainM(mach, d, s, r, Step.taken.at(~mach, ~d, r, i, a, n, vs)):
  Ext.bind(
    ~mach,
    ~d,
    s,
    r,
    Run.add(~mach, ~d, r, Log.out(i), Out.code(Out.Taken{a, n}, [])),
    +r1 => Maybe.bind(
      &2,
      Run<Led.L(mach, d)>,
      Run<Led.L(mach, d)>,
      Run.add(
        ~mach,
        ~d,
        r1,
        Log.taken(n),
        Taken.code(Taken{i, Tip.content(Run.tip(Led.L(mach, d), r1))}, [])
      ),
      r2 => Some{Run.next(Led.L(mach, d), r2, vs)}
    ),
    Ext.add(~mach, ~d, s, r, Log.out(i), Out.code(Out.Taken{a, n}, [])),
    +r1 => Ext.bind(
      ~mach,
      ~d,
      s,
      r1,
      Run.add(
        ~mach,
        ~d,
        r1,
        Log.taken(n),
        Taken.code(Taken{i, Tip.content(Run.tip(Led.L(mach, d), r1))}, [])
      ),
      r2 => Some{Run.next(Led.L(mach, d), r2, vs)},
      Ext.add(
        ~mach,
        ~d,
        s,
        r1,
        Log.taken(n),
        Taken.code(Taken{i, Tip.content(Run.tip(Led.L(mach, d), r1))}, [])
      ),
      r2 => Ext.next(mach, d, s, r2, vs)
    )
  )

# a run follows itself after it took a request as its next number
def Ext.taken(
  ~mach: Machine(),
  ~d: Led(mach),
  +s: Led.L(mach, d),
  +r: Run<Led.L(mach, d)>,
  +i: Ledgers.Id,
  +a: Hashes.Hash,
  +vs: Maybe<&2, List<&2, String>>
) -> Ext.GainM(mach, d, s, r, Step.taken(~mach, ~d, r, i, a, vs)):
  Ext.taken.at(~mach, ~d, s, r, i, a, Tip.count(Run.tip(Led.L(mach, d), r)), vs)

# a run follows itself after a label
def Ext.labelled(
  ~mach: Machine(),
  ~d: Led(mach),
  +s: Led.L(mach, d),
  +r: Run<Led.L(mach, d)>,
  +i: Ledgers.Id,
  +a: Hashes.Hash,
  +m: String,
  v: Maybe<&2, Taken>
) -> Ext.GainM(mach, d, s, r, Step.labelled(~mach, ~d, r, i, a, m, v)):
  match v:
    case None{}:
      Unit{}
    case Some{+x}:
      Ext.bind(
        ~mach,
        ~d,
        s,
        r,
        Run.add(~mach, ~d, r, Log.label(m), Ledgers.Id.code(Taken.id(x), [])),
        r2 => Step.taken(~mach, ~d, r2, i, a, None{}),
        Ext.add(~mach, ~d, s, r, Log.label(m), Ledgers.Id.code(Taken.id(x), [])),
        r2 => Ext.taken(~mach, ~d, s, r2, i, a, None{})
      )

# a run follows itself after Step.label.at
def Ext.label.at(
  ~mach: Machine(),
  ~d: Led(mach),
  +s: Led.L(mach, d),
  +r: Run<Led.L(mach, d)>,
  +i: Ledgers.Id,
  +a: Hashes.Hash,
  +m: String,
  k: Maybe<&2, Maybe<&2, Ledgers.Id>>
) -> Ext.GainM(mach, d, s, r, Step.label.at(~mach, ~d, r, i, a, m, k)):
  match k:
    case None{}:
      Unit{}
    case Some{Some{x}}:
      Ext.stale(~mach, ~d, s, r, i, a)
    case Some{None{}}:
      Shared.Bool.when_cases(
        Maybe<&2, Run<Led.L(mach, d)>>,
        x => Ext.GainM(mach, d, s, r, x),
        U32.is_eq(Tip.count(Run.tip(Led.L(mach, d), r)), 0),
        u => Step.stale(~mach, ~d, r, i, a),
        u => Step.labelled(
          ~mach,
          ~d,
          r,
          i,
          a,
          m,
          Tip.taken(
            ~mach,
            ~d,
            Run.ledger(Led.L(mach, d), r),
            Run.tip(Led.L(mach, d), r),
            U32.sub(Tip.count(Run.tip(Led.L(mach, d), r)), 1)
          )
        ),
        e => Ext.stale(~mach, ~d, s, r, i, a),
        e => Ext.labelled(
          ~mach,
          ~d,
          s,
          r,
          i,
          a,
          m,
          Tip.taken(
            ~mach,
            ~d,
            Run.ledger(Led.L(mach, d), r),
            Run.tip(Led.L(mach, d), r),
            U32.sub(Tip.count(Run.tip(Led.L(mach, d), r)), 1)
          )
        )
      )

# a run follows itself after a request for a label
def Ext.label(
  ~mach: Machine(),
  ~d: Led(mach),
  +s: Led.L(mach, d),
  +r: Run<Led.L(mach, d)>,
  +i: Ledgers.Id,
  +a: Hashes.Hash,
  +m: String
) -> Ext.GainM(mach, d, s, r, Step.label(~mach, ~d, r, i, a, m)):
  Ext.label.at(
    ~mach,
    ~d,
    s,
    r,
    i,
    a,
    m,
    Tip.known(
      ~Ledgers.Id,
      ~Ledgers.Id.code,
      ~Ledgers.Id.code.read,
      Tip.find(~mach, ~d, Run.ledger(Led.L(mach, d), r), Run.tip(Led.L(mach, d), r), Log.label(m))
    )
  )

# a run follows itself after it opened a sub line
def Ext.opens(
  ~mach: Machine(),
  ~d: Led(mach),
  +s: Led.L(mach, d),
  +r: Run<Led.L(mach, d)>,
  +i: Ledgers.Id,
  +a: Hashes.Hash,
  +b: String,
  +t: Tip,
  +ns: List<&2, List<&2, U32>>
) -> Ext.GainM(mach, d, s, r, Step.opens(~mach, ~d, r, i, a, b, t, ns)):
  +r0 = Run.over(~mach, ~d, r, Tip.code(t, []) <> ns, Tip.content(Run.tip(Led.L(mach, d), r)))
  Ext.bind(
    ~mach,
    ~d,
    s,
    r,
    Run.add(~mach, ~d, r0, Log.start(b), Hashes.Hash.code(Tip.hash(t), [])),
    r2 => Step.taken(~mach, ~d, r2, i, a, None{}),
    Ext.transM(
      ~mach,
      ~d,
      s,
      r,
      r0,
      Run.add(~mach, ~d, r0, Log.start(b), Hashes.Hash.code(Tip.hash(t), [])),
      Ext.over(~mach, ~d, s, r, Tip.code(t, []) <> ns, Tip.content(Run.tip(Led.L(mach, d), r))),
      Ext.add(~mach, ~d, s, r0, Log.start(b), Hashes.Hash.code(Tip.hash(t), []))
    ),
    r2 => Ext.taken(~mach, ~d, s, r2, i, a, None{})
  )

# a run follows itself after an act of a kernel
def Ext.act(
  ~mach: Machine(),
  ~d: Led(mach),
  +s: Led.L(mach, d),
  +r: Run<Led.L(mach, d)>,
  +i: Ledgers.Id,
  +a: Hashes.Hash,
  m: Maybe<&2, Act>
) -> Ext.GainM(mach, d, s, r, Act.run(~mach, ~d, r, i, a, m)):
  match m:
    case None{}:
      Unit{}
    case Some{Act.Stale{}}:
      Ext.stale(~mach, ~d, s, r, i, a)
    case Some{Act.Label{x}}:
      Ext.label(~mach, ~d, s, r, i, a, x)
    case Some{Act.Taken{+vs, +h, +ns}}:
      Ext.transM(
        ~mach,
        ~d,
        s,
        r,
        Run.over(~mach, ~d, r, ns, h),
        Step.taken(~mach, ~d, Run.over(~mach, ~d, r, ns, h), i, a, vs),
        Ext.over(~mach, ~d, s, r, ns, h),
        Ext.taken(~mach, ~d, s, Run.over(~mach, ~d, r, ns, h), i, a, vs)
      )
    case Some{Act.Opens{b, t, ns}}:
      Ext.opens(~mach, ~d, s, r, i, a, b, t, ns)

# a run follows itself after a request with the outcome o
def Ext.fresh(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  +s: Led.L(mach, d),
  +r: Run<Led.L(mach, d)>,
  +c: Ledgers.Line,
  +i: Ledgers.Id,
  +a: Hashes.Hash,
  +q: Machine.Q(mach),
  o: Maybe<&2, Maybe<&2, Out>>
) -> Ext.GainM(mach, d, s, r, Step.fresh(~mach, ~d, ~kern, r, c, i, a, q, o)):
  match o:
    case None{}:
      Unit{}
    case Some{Some{x}}:
      Ext.refl(mach, d, s, r)
    case Some{None{}}:
      Ext.act(
        ~mach,
        ~d,
        s,
        r,
        i,
        a,
        Kernel.change(mach, d, kern)(Run.ledger(Led.L(mach, d), r))(Run.tip(Led.L(mach, d), r))(c)(i)(q)
      )

# a run follows itself after the entry m
def Ext.asked(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  +s: Led.L(mach, d),
  +r: Run<Led.L(mach, d)>,
  +c: Ledgers.Line,
  +a: Hashes.Hash,
  m: Maybe<&2, Entry(mach)>
) -> Ext.GainM(mach, d, s, r, Step.asked(~mach, ~d, ~kern, r, c, a, m)):
  match m:
    case Some{Ledgers.Entry.Ask{+i, t, q}}:
      Ext.fresh(
        ~mach,
        ~d,
        ~kern,
        s,
        r,
        c,
        i,
        a,
        q,
        Tip.known(
          ~Out,
          ~Out.code,
          ~Out.code.read,
          Tip.find(~mach, ~d, Run.ledger(Led.L(mach, d), r), Run.tip(Led.L(mach, d), r), Log.out(i))
        )
      )
    case None{}:
      Unit{}
    case Some{Ledgers.Entry.Ballot{x}}:
      Unit{}
    case Some{Ledgers.Entry.Data{x}}:
      Unit{}
    case Some{Ledgers.Entry.Lie{x}}:
      Unit{}

# a run follows itself after one request
def Ext.one(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  +s: Led.L(mach, d),
  +r: Run<Led.L(mach, d)>,
  +c: Ledgers.Line,
  +a: Hashes.Hash
) -> Ext.GainM(mach, d, s, r, Step.one(~mach, ~d, ~kern, r, c, a)):
  Ext.asked(~mach, ~d, ~kern, s, r, c, a, Led.get(~mach, ~d, Run.ledger(Led.L(mach, d), r), Ledgers.Name.Ask{a}))

# a run m that follows r follows it after the requests qs
def Ext.all(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  +s: Led.L(mach, d),
  +r: Run<Led.L(mach, d)>,
  +c: Ledgers.Line,
  qs: List<&2, Hashes.Hash>,
  +m: Maybe<&2, Run<Led.L(mach, d)>>,
  hm: Ext.GainM(mach, d, s, r, m)
) -> Ext.GainM(mach, d, s, r, Step.all(~mach, ~d, ~kern, c, qs, m)):
  match qs:
    case Nil{}:
      hm
    case Con{+q, rest}:
      Ext.all(
        ~mach,
        ~d,
        ~kern,
        s,
        r,
        c,
        rest,
        Maybe.bind(&2, Run<Led.L(mach, d)>, Run<Led.L(mach, d)>, m, x => Step.one(~mach, ~d, ~kern, x, c, q)),
        Ext.bind(
          ~mach,
          ~d,
          s,
          r,
          m,
          x => Step.one(~mach, ~d, ~kern, x, c, q),
          hm,
          x => Ext.one(~mach, ~d, ~kern, s, x, c, q)
        )
      )

# that the ledger of the run r is base with some data put, which base holds
# when it holds what r added
def Ext.Based(-mach: Machine(), -d: Led(mach), -base: Led.L(mach, d), -r: Run<Led.L(mach, d)>) -> Data:
  +Sigma<List<&2, List<&2, U32>>, xs => +Sigma<
    {Run.ledger(Led.L(mach, d), r) == Led.puts(~mach, ~d, xs, base): Led.L(mach, d)},
    e => {Ext.holds(~mach, ~d, base, xs) == Ext.holds(~mach, ~d, base, Run.added(Led.L(mach, d), r)): Bool}>>

# the check of Ext.based: base holds the puts when it holds the added nodes
def Ext.based.holds(
  ~mach: Machine(),
  ~d: Led(mach),
  +base: Led.L(mach, d),
  +xs: List<&2, List<&2, U32>>,
  +ys: List<&2, List<&2, U32>>,
  +zs: List<&2, List<&2, U32>>,
  +a: List<&2, List<&2, U32>>,
  +a2: List<&2, List<&2, U32>>,
  e2: {Ext.holds(~mach, ~d, base, xs) == Ext.holds(~mach, ~d, base, a): Bool},
  h1: {Ext.holds(~mach, ~d, base, zs) == Ext.holds(~mach, ~d, base, ys): Bool},
  a1: {a2 == List.append(&2, List<&2, U32>, ys, a): List<&2, List<&2, U32>>}
) -> {
  Ext.holds(~mach, ~d, base, List.append(&2, List<&2, U32>, xs, zs)) == Ext.holds(~mach, ~d, base, a2): Bool
}:
  %Equal.sym(List<&2, List<&2, U32>>, a2, List.append(&2, List<&2, U32>, ys, a), a1): {
    Ext.holds(~mach, ~d, base, List.append(&2, List<&2, U32>, xs, zs)) == Ext.holds(~mach, ~d, base, _): Bool
  }
  %Equal.sym(
    Bool,
    Ext.holds(~mach, ~d, base, List.append(&2, List<&2, U32>, xs, zs)),
    Bool.and(Ext.holds(~mach, ~d, base, xs), Ext.holds(~mach, ~d, base, zs)),
    Ext.holds_append(~mach, ~d, base, xs, zs)
  ): {_ == Ext.holds(~mach, ~d, base, List.append(&2, List<&2, U32>, ys, a)): Bool}
  %Equal.sym(
    Bool,
    Ext.holds(~mach, ~d, base, List.append(&2, List<&2, U32>, ys, a)),
    Bool.and(Ext.holds(~mach, ~d, base, ys), Ext.holds(~mach, ~d, base, a)),
    Ext.holds_append(~mach, ~d, base, ys, a)
  ): {Bool.and(Ext.holds(~mach, ~d, base, xs), Ext.holds(~mach, ~d, base, zs)) == _: Bool}
  %Equal.sym(Bool, Ext.holds(~mach, ~d, base, xs), Ext.holds(~mach, ~d, base, a), e2): {
    Bool.and(_, Ext.holds(~mach, ~d, base, zs))
      == Bool.and(Ext.holds(~mach, ~d, base, ys), Ext.holds(~mach, ~d, base, a)): Bool
  }
  %Equal.sym(Bool, Ext.holds(~mach, ~d, base, zs), Ext.holds(~mach, ~d, base, ys), h1): {
    Bool.and(Ext.holds(~mach, ~d, base, a), _)
      == Bool.and(Ext.holds(~mach, ~d, base, ys), Ext.holds(~mach, ~d, base, a)): Bool
  }
  Ext.and_comm(Ext.holds(~mach, ~d, base, a), Ext.holds(~mach, ~d, base, ys))

# a run that follows a run based on base is based on base
def Ext.based(
  ~mach: Machine(),
  ~d: Led(mach),
  +base: Led.L(mach, d),
  +r: Run<Led.L(mach, d)>,
  +r2: Run<Led.L(mach, d)>,
  bd: Ext.Based(mach, d, base, r),
  g: Ext.Gain(mach, d, base, r, r2)
) -> Ext.Based(mach, d, base, r2):
  match bd:
    case Tuple{+xs, Tuple{e1, e2}}:
      match g:
        case Tuple{+ys, Tuple{+zs, Tuple{a1, Tuple{l1, h1}}}}:
          Tuple{
            List.append(&2, List<&2, U32>, xs, zs),
            Tuple{
              Equal.trans(
                Led.L(mach, d),
                Run.ledger(Led.L(mach, d), r2),
                Led.puts(~mach, ~d, zs, Run.ledger(Led.L(mach, d), r)),
                Led.puts(~mach, ~d, List.append(&2, List<&2, U32>, xs, zs), base),
                l1,
                Equal.trans(
                  Led.L(mach, d),
                  Led.puts(~mach, ~d, zs, Run.ledger(Led.L(mach, d), r)),
                  Led.puts(~mach, ~d, zs, Led.puts(~mach, ~d, xs, base)),
                  Led.puts(~mach, ~d, List.append(&2, List<&2, U32>, xs, zs), base),
                  Equal.cong(
                    Led.L(mach, d),
                    Led.L(mach, d),
                    z => Led.puts(~mach, ~d, zs, z),
                    Run.ledger(Led.L(mach, d), r),
                    Led.puts(~mach, ~d, xs, base),
                    e1
                  ),
                  Ext.puts_append(~mach, ~d, xs, zs, base)
                )
              ),
              Ext.based.holds(
                ~mach,
                ~d,
                base,
                xs,
                ys,
                zs,
                Run.added(Led.L(mach, d), r),
                Run.added(Led.L(mach, d), r2),
                e2,
                h1,
                a1
              )
            }
          }

# a run whose added nodes s holds: s holds what the run before it added
def Ext.gain_holds(
  ~mach: Machine(),
  ~d: Led(mach),
  +s: Led.L(mach, d),
  +r: Run<Led.L(mach, d)>,
  r2: Run<Led.L(mach, d)>,
  g: Ext.Gain(mach, d, s, r, r2),
  h: {Ext.holds(~mach, ~d, s, Run.added(Led.L(mach, d), r2)) == True{}: Bool}
) -> {Ext.holds(~mach, ~d, s, Run.added(Led.L(mach, d), r)) == True{}: Bool}:
  match g:
    case Tuple{+ys, Tuple{zs, Tuple{a1, Tuple{l1, h1}}}}:
      Ext.holds_right(
        ~mach,
        ~d,
        s,
        ys,
        Run.added(Led.L(mach, d), r)
      )(
        Equal.trans(
          Bool,
          Ext.holds(~mach, ~d, s, List.append(&2, List<&2, U32>, ys, Run.added(Led.L(mach, d), r))),
          Ext.holds(~mach, ~d, s, Run.added(Led.L(mach, d), r2)),
          True{},
          Equal.cong(
            List<&2, List<&2, U32>>,
            Bool,
            z => Ext.holds(~mach, ~d, s, z),
            List.append(&2, List<&2, U32>, ys, Run.added(Led.L(mach, d), r)),
            Run.added(Led.L(mach, d), r2),
            Equal.sym(
              List<&2, List<&2, U32>>,
              Run.added(Led.L(mach, d), r2),
              List.append(&2, List<&2, U32>, ys, Run.added(Led.L(mach, d), r)),
              a1
            )
          ),
          h
        )
      )

# the entry m whose words are w is the data w
def Ext.words_data(
  -mach: Machine(),
  m: Maybe<&2, Entry(mach)>,
  -w: List<&2, U32>,
  h: {Ledgers.Entry.words(Machine.Q(mach), m) == Some{w}: Maybe<&2, List<&2, U32>>}
) -> {m == Some{Ledgers.Entry.Data{w}}: Maybe<&2, Entry(mach)>}:
  match m:
    case None{}:
      Empty.absurd(
        {None{} == Some{Ledgers.Entry.Data{w}}: Maybe<&2, Entry(mach)>},
        Shared.Maybe.none_ne_some(List<&2, U32>, w, h)
      )
    case Some{Ledgers.Entry.Data{ws}}:
      Equal.cong(
        List<&2, U32>,
        Maybe<&2, Entry(mach)>,
        z => Some{Ledgers.Entry.Data{z}},
        ws,
        w,
        Shared.Maybe.some_inj(List<&2, U32>, ws, w, h)
      )
    case Some{Ledgers.Entry.Ask{i, t, q}}:
      Empty.absurd(
        {Some{Ledgers.Entry.Ask{i, t, q}} == Some{Ledgers.Entry.Data{w}}: Maybe<&2, Entry(mach)>},
        Shared.Maybe.none_ne_some(List<&2, U32>, w, h)
      )
    case Some{Ledgers.Entry.Ballot{b}}:
      Empty.absurd(
        {Some{Ledgers.Entry.Ballot{b}} == Some{Ledgers.Entry.Data{w}}: Maybe<&2, Entry(mach)>},
        Shared.Maybe.none_ne_some(List<&2, U32>, w, h)
      )
    case Some{Ledgers.Entry.Lie{x}}:
      Empty.absurd(
        {Some{Ledgers.Entry.Lie{x}} == Some{Ledgers.Entry.Data{w}}: Maybe<&2, Entry(mach)>},
        Shared.Maybe.none_ne_some(List<&2, U32>, w, h)
      )

# Ext.add_into at a data name, once whether its hash is that of w is known (b)
def Ext.add_into.data(
  ~mach: Machine(),
  ~d: Led(mach),
  +lb: Led.L(mach, d),
  +w: List<&2, U32>,
  +y: Hashes.Hash,
  -e: Entry(mach),
  b: Bool,
  eb: {Hashes.Hash.is_eq(Hashes.Sha.hash(w), y) == b: Bool},
  hw: {Ext.has(~mach, ~d, lb, w) == True{}: Bool},
  h: {Shared.Maybe.when(Entry(mach), b, u => Some{Ledgers.Entry.Data{w}}) == Some{e}: Maybe<&2, Entry(mach)>}
) -> {Led.get(~mach, ~d, lb, Ledgers.Name.Data{y}) == Some{e}: Maybe<&2, Entry(mach)>}:
  match b:
    case True{}:
      %Hashes.Hash.is_eq_sound(Hashes.Sha.hash(w), y)(eb): {
        Led.get(~mach, ~d, lb, Ledgers.Name.Data{_}) == Some{e}: Maybe<&2, Entry(mach)>
      }
      %Shared.Maybe.some_inj(Entry(mach), Ledgers.Entry.Data{w}, e, h): {
        Led.get(~mach, ~d, lb, Ledgers.Name.Data{Hashes.Sha.hash(w)}) == Some{_}: Maybe<&2, Entry(mach)>
      }
      Ext.words_data(
        mach,
        Led.get(~mach, ~d, lb, Ledgers.Name.Data{Hashes.Sha.hash(w)}),
        w,
        Hist.has(~mach, ~d, lb, w)(hw)
      )
    case False{}:
      Empty.absurd(
        {Led.get(~mach, ~d, lb, Ledgers.Name.Data{y}) == Some{e}: Maybe<&2, Entry(mach)>},
        Shared.Maybe.none_ne_some(Entry(mach), e, h)
      )

# Ext.add_into at a name that the ledger before lacked
def Ext.add_into.none(
  ~mach: Machine(),
  ~d: Led(mach),
  +lb: Led.L(mach, d),
  +w: List<&2, U32>,
  n: Ledgers.Name,
  -e: Entry(mach),
  hw: {Ext.has(~mach, ~d, lb, w) == True{}: Bool},
  h: {
    Shared.Maybe.when(
      Entry(mach),
      Ledgers.Name.is_eq(Ledgers.Name.Data{Hashes.Sha.hash(w)}, n),
      u => Some{Ledgers.Entry.Data{w}}
    )
      == Some{e}: Maybe<&2, Entry(mach)>
  }
) -> {Led.get(~mach, ~d, lb, n) == Some{e}: Maybe<&2, Entry(mach)>}:
  match n:
    case Ledgers.Name.Data{+y}:
      Ext.add_into.data(~mach, ~d, lb, w, y, e, Hashes.Hash.is_eq(Hashes.Sha.hash(w), y), {==}, hw, h)
    case Ledgers.Name.Ask{y}:
      Empty.absurd(
        {Led.get(~mach, ~d, lb, Ledgers.Name.Ask{y}) == Some{e}: Maybe<&2, Entry(mach)>},
        Shared.Maybe.none_ne_some(Entry(mach), e, h)
      )
    case Ledgers.Name.Ballot{y}:
      Empty.absurd(
        {Led.get(~mach, ~d, lb, Ledgers.Name.Ballot{y}) == Some{e}: Maybe<&2, Entry(mach)>},
        Shared.Maybe.none_ne_some(Entry(mach), e, h)
      )
    case Ledgers.Name.Lie{y}:
      Empty.absurd(
        {Led.get(~mach, ~d, lb, Ledgers.Name.Lie{y}) == Some{e}: Maybe<&2, Entry(mach)>},
        Shared.Maybe.none_ne_some(Entry(mach), e, h)
      )

# Ext.add_into once what the ledger before held under the name is known (m)
def Ext.add_into.at(
  ~mach: Machine(),
  ~d: Led(mach),
  -la: Led.L(mach, d),
  +lb: Led.L(mach, d),
  +w: List<&2, U32>,
  +n: Ledgers.Name,
  +e: Entry(mach),
  m: Maybe<&2, Entry(mach)>,
  em: {Led.get(~mach, ~d, la, n) == m: Maybe<&2, Entry(mach)>},
  g: Led.Grows(mach, d, la, lb),
  hw: {Ext.has(~mach, ~d, lb, w) == True{}: Bool},
  h: {
    Maybe.or(
      &2,
      Entry(mach),
      m,
      Shared.Maybe.when(
        Entry(mach),
        Ledgers.Name.is_eq(Entry.name(~mach, Ledgers.Entry.Data{w}), n),
        u => Some{Ledgers.Entry.Data{w}}
      )
    )
      == Some{e}: Maybe<&2, Entry(mach)>
  }
) -> {Led.get(~mach, ~d, lb, n) == Some{e}: Maybe<&2, Entry(mach)>}:
  match m:
    case Some{x}:
      g(n)(e)(Equal.trans(Maybe<&2, Entry(mach)>, Led.get(~mach, ~d, la, n), Some{x}, Some{e}, em, h))
    case None{}:
      Ext.add_into.none(~mach, ~d, lb, w, n, e, hw, h)

# a ledger with data that lb holds still grows into lb
def Ext.add_into(
  ~mach: Machine(),
  ~d: Led(mach),
  +la: Led.L(mach, d),
  +lb: Led.L(mach, d),
  +w: List<&2, U32>,
  g: Led.Grows(mach, d, la, lb),
  hw: {Ext.has(~mach, ~d, lb, w) == True{}: Bool}
) -> Led.Grows(mach, d, Led.add(~mach, ~d, la, Ledgers.Entry.Data{w}), lb):
  +n => +e => h => Ext.add_into.at(
    ~mach,
    ~d,
    la,
    lb,
    w,
    n,
    e,
    Led.get(~mach, ~d, la, n),
    {==},
    g,
    hw,
    Equal.trans(
      Maybe<&2, Entry(mach)>,
      Maybe.or(
        &2,
        Entry(mach),
        Led.get(~mach, ~d, la, n),
        Shared.Maybe.when(
          Entry(mach),
          Ledgers.Name.is_eq(Entry.name(~mach, Ledgers.Entry.Data{w}), n),
          u => Some{Ledgers.Entry.Data{w}}
        )
      ),
      Led.get(~mach, ~d, Led.add(~mach, ~d, la, Ledgers.Entry.Data{w}), n),
      Some{e},
      Equal.sym(
        Maybe<&2, Entry(mach)>,
        Led.get(~mach, ~d, Led.add(~mach, ~d, la, Ledgers.Entry.Data{w}), n),
        Maybe.or(
          &2,
          Entry(mach),
          Led.get(~mach, ~d, la, n),
          Shared.Maybe.when(
            Entry(mach),
            Ledgers.Name.is_eq(Entry.name(~mach, Ledgers.Entry.Data{w}), n),
            u => Some{Ledgers.Entry.Data{w}}
          )
        ),
        Hist.get_add(mach, d)(la)(Ledgers.Entry.Data{w})(n)
      ),
      h
    )
  )

# a ledger with data ns that lb holds still grows into lb
def Ext.puts_into(
  ~mach: Machine(),
  ~d: Led(mach),
  ns: List<&2, List<&2, U32>>,
  +la: Led.L(mach, d),
  +lb: Led.L(mach, d),
  g: Led.Grows(mach, d, la, lb),
  +h: {Ext.holds(~mach, ~d, lb, ns) == True{}: Bool}
) -> Led.Grows(mach, d, Led.puts(~mach, ~d, ns, la), lb):
  match ns:
    case Nil{}:
      g
    case Con{+w, +r}:
      Ext.puts_into(
        ~mach,
        ~d,
        r,
        Led.add(~mach, ~d, la, Ledgers.Entry.Data{w}),
        lb,
        Ext.add_into(
          ~mach,
          ~d,
          la,
          lb,
          w,
          g,
          Shared.List.all.if_hit(Ext.has(~mach, ~d, lb, w), u => Ext.holds(~mach, ~d, lb, r))(h)
        ),
        Shared.List.all.if_rest(Ext.has(~mach, ~d, lb, w), u => Ext.holds(~mach, ~d, lb, r))(h)
      )

# a run based on base, whose added nodes base holds: its ledger grows into base
def Ext.based_grows(
  ~mach: Machine(),
  ~d: Led(mach),
  +base: Led.L(mach, d),
  r: Run<Led.L(mach, d)>,
  bd: Ext.Based(mach, d, base, r),
  h: {Ext.holds(~mach, ~d, base, Run.added(Led.L(mach, d), r)) == True{}: Bool}
) -> Led.Grows(mach, d, Run.ledger(Led.L(mach, d), r), base):
  match bd:
    case Tuple{+xs, Tuple{e1, e2}}:
      %Equal.sym(Led.L(mach, d), Run.ledger(Led.L(mach, d), r), Led.puts(~mach, ~d, xs, base), e1): Led.Grows(
        mach,
        d,
        _,
        base
      )
      Ext.puts_into(
        ~mach,
        ~d,
        xs,
        base,
        base,
        Hist.refl(mach, d, base),
        Equal.trans(
          Bool,
          Ext.holds(~mach, ~d, base, xs),
          Ext.holds(~mach, ~d, base, Run.added(Led.L(mach, d), r)),
          True{},
          e2,
          h
        )
      )

# the ledger of a run based on base grows from base
def Ext.based_from(
  ~mach: Machine(),
  ~d: Led(mach),
  +base: Led.L(mach, d),
  r: Run<Led.L(mach, d)>,
  bd: Ext.Based(mach, d, base, r)
) -> Led.Grows(mach, d, base, Run.ledger(Led.L(mach, d), r)):
  match bd:
    case Tuple{+xs, Tuple{e1, e2}}:
      %Equal.sym(Led.L(mach, d), Run.ledger(Led.L(mach, d), r), Led.puts(~mach, ~d, xs, base), e1): Led.Grows(
        mach,
        d,
        base,
        _
      )
      Hist.puts(~mach, ~d, xs, base)

# a case of an "or": the hit, or the rest
def Ext.any_cases(
  hit: Bool,
  -rest: Unit -> Bool,
  -P: Type,
  ph: {hit == True{}: Bool} -> P,
  pr: {rest(Unit{}) == True{}: Bool} -> P,
  h: {List.any.if(rest, hit) == True{}: Bool}
) -> P:
  match hit:
    case True{}:
      ph({==})
    case False{}:
      pr(h)

# a ledger gives each of the words that it holds, under their hash
def Ext.held.of(
  ~mach: Machine(),
  ~d: Led(mach),
  +l: Led.L(mach, d),
  ns: List<&2, List<&2, U32>>,
  +w: List<&2, U32>,
  +h: {Ext.holds(~mach, ~d, l, ns) == True{}: Bool},
  hc: {
    List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), ns, w) == True{}: Bool
  }
) -> {Led.fetch(~mach, ~d, l, Hashes.Sha.hash(w)) == Some{w}: Maybe<&2, List<&2, U32>>}:
  match ns:
    case Nil{}:
      Empty.absurd(
        {Led.fetch(~mach, ~d, l, Hashes.Sha.hash(w)) == Some{w}: Maybe<&2, List<&2, U32>>},
        Shared.Bool.false_ne_true(hc)
      )
    case Con{+ws, +r}:
      Ext.any_cases(
        Shared.List.is_eq(~U32, ~U32.is_eq, ws, w),
        u => List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), r, w),
        {Led.fetch(~mach, ~d, l, Hashes.Sha.hash(w)) == Some{w}: Maybe<&2, List<&2, U32>>},
        he =>
          %Shared.List.is_eq_sound(~U32, ~U32.is_eq, ~Shared.U32.laws(), ws, w)(he): {
            Led.fetch(~mach, ~d, l, Hashes.Sha.hash(_)) == Some{_}: Maybe<&2, List<&2, U32>>
          }
          Hist.has(
            ~mach,
            ~d,
            l,
            ws
          )(Shared.List.all.if_hit(Ext.has(~mach, ~d, l, ws), u => Ext.holds(~mach, ~d, l, r))(h)),
        hr => Ext.held.of(
          ~mach,
          ~d,
          l,
          r,
          w,
          Shared.List.all.if_rest(Ext.has(~mach, ~d, l, ws), u => Ext.holds(~mach, ~d, l, r))(h),
          hr
        ),
        hc
      )

# a ledger that holds the nodes of an edit holds the edit
def Ext.held(
  ~mach: Machine(),
  ~d: Led(mach),
  +l: Led.L(mach, d),
  +e: Trees.Edit,
  h: {Ext.holds(~mach, ~d, l, Trees.Edit.nodes(e)) == True{}: Bool}
) -> Trees.Edit.Held(Led.L(mach, d), x => y => Led.fetch(~mach, ~d, x, y), l, e):
  +w => hc => Ext.held.of(~mach, ~d, l, Trees.Edit.nodes(e), w, h, hc)

# the log of a tip with a new log
def Keep.log_logged(t: Tip, -h: Maybe<&2, Hashes.Hash>) -> {Tip.log(Tip.logged(t, h)) == h: Maybe<&2, Hashes.Hash>}:
  match t:
    case Tip{c, o, n, vs}:
      {==}

# the log of a tip with new content
def Keep.log_over(t: Tip, -h: Maybe<&2, Hashes.Hash>) -> {
  Tip.log(Tip.over(t, h)) == Tip.log(t): Maybe<&2, Hashes.Hash>
}:
  match t:
    case Tip{c, o, n, vs}:
      {==}

# the log of a tip one request on
def Keep.log_next(t: Tip, -vs: Maybe<&2, List<&2, String>>) -> {
  Tip.log(Tip.next(t, vs)) == Tip.log(t): Maybe<&2, Hashes.Hash>
}:
  match t:
    case Tip{c, o, n, x}:
      {==}

# a read that found a value knows it
def Keep.found(
  m: Trees.Look,
  -v: List<&2, U32>,
  h: {Trees.Look.value(m) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> {Trees.Look.known(m) == Some{Some{v}}: Maybe<&2, Maybe<&2, List<&2, U32>>>}:
  match m:
    case Trees.Look.Found{x}:
      Equal.cong(
        List<&2, U32>,
        Maybe<&2, Maybe<&2, List<&2, U32>>>,
        z => Some{Some{z}},
        x,
        v,
        Shared.Maybe.some_inj(List<&2, U32>, x, v, h)
      )
    case Trees.Look.Absent{}:
      Empty.absurd(
        {Some{None{}} == Some{Some{v}}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
        Shared.Maybe.none_ne_some(List<&2, U32>, v, h)
      )
    case Trees.Look.Missing{x}:
      Empty.absurd(
        {None{} == Some{Some{v}}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
        Shared.Maybe.none_ne_some(List<&2, U32>, v, h)
      )

# a read that knows a value found it
def Keep.found_back(
  m: Trees.Look,
  -v: List<&2, U32>,
  h: {Trees.Look.known(m) == Some{Some{v}}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
) -> {Trees.Look.value(m) == Some{v}: Maybe<&2, List<&2, U32>>}:
  match m:
    case Trees.Look.Found{x}:
      Shared.Maybe.some_inj(Maybe<&2, List<&2, U32>>, Some{x}, Some{v}, h)
    case Trees.Look.Absent{}:
      Empty.absurd(
        {None{} == Some{v}: Maybe<&2, List<&2, U32>>},
        Shared.Maybe.none_ne_some(
          List<&2, U32>,
          v,
          Shared.Maybe.some_inj(Maybe<&2, List<&2, U32>>, None{}, Some{v}, h)
        )
      )
    case Trees.Look.Missing{x}:
      Empty.absurd(
        {None{} == Some{v}: Maybe<&2, List<&2, U32>>},
        Shared.Maybe.none_ne_some(Maybe<&2, List<&2, U32>>, Some{v}, h)
      )

# Logs that keep their keys
# -------------------------
# A run whose nodes a ledger l holds keeps, in l, each key that its log holds.

# that the log of the run r reads the value val under key in l, once l holds
# what r added
def Keep.Has(
  -mach: Machine(),
  -d: Led(mach),
  -l: Led.L(mach, d),
  -key: List<&2, U32>,
  -val: List<&2, U32>,
  -r: Run<Led.L(mach, d)>
) -> Type:
  {Ext.holds(~mach, ~d, l, Run.added(Led.L(mach, d), r)) == True{}: Bool}
    -> {Tip.get(~mach, ~d, l, Run.tip(Led.L(mach, d), r), key) == Some{val}: Maybe<&2, List<&2, U32>>}

# Keep.Has of the result m of a run, when there is one
def Keep.Out(
  -mach: Machine(),
  -d: Led(mach),
  -l: Led.L(mach, d),
  -key: List<&2, U32>,
  -val: List<&2, U32>,
  m: Maybe<&2, Run<Led.L(mach, d)>>
) -> Type:
  match m:
    case None{}:
      Unit
    case Some{r2}:
      Keep.Has(mach, d, l, key, val, r2)

# a key that the log holds is not the key of a write that found nothing there
def Keep.ne.at(
  ~mach: Machine(),
  ~d: Led(mach),
  +l: Led.L(mach, d),
  +lr: Led.L(mach, d),
  +t: Tip,
  +k: List<&2, U32>,
  +key: List<&2, U32>,
  +val: List<&2, U32>,
  +a: List<&2, List<&2, U32>>,
  +bd: Ext.Based(mach, d, l, Run{lr, t, a}),
  +ha: {Ext.holds(~mach, ~d, l, a) == True{}: Bool},
  b: Bool,
  eb: {Shared.List.is_eq(~U32, ~U32.is_eq, k, key) == b: Bool},
  em: {Tip.find(~mach, ~d, lr, t, k) == Some{None{}}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
  hg: {Tip.get(~mach, ~d, l, t, key) == Some{val}: Maybe<&2, List<&2, U32>>}
) -> {b == False{}: Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Empty.absurd(
        {True{} == False{}: Bool},
        Shared.Maybe.none_ne_some(
          List<&2, U32>,
          val,
          Shared.Maybe.some_inj(
            Maybe<&2, List<&2, U32>>,
            None{},
            Some{val},
            Equal.trans(
              Maybe<&2, Maybe<&2, List<&2, U32>>>,
              Some{None{}},
              Tip.find(~mach, ~d, l, t, key),
              Some{Some{val}},
              Equal.sym(
                Maybe<&2, Maybe<&2, List<&2, U32>>>,
                Tip.find(~mach, ~d, l, t, key),
                Some{None{}},
                Equal.trans(
                  Maybe<&2, Maybe<&2, List<&2, U32>>>,
                  Tip.find(~mach, ~d, l, t, key),
                  Tip.find(~mach, ~d, l, t, k),
                  Some{None{}},
                  Equal.cong(
                    List<&2, U32>,
                    Maybe<&2, Maybe<&2, List<&2, U32>>>,
                    z => Tip.find(~mach, ~d, l, t, z),
                    key,
                    k,
                    Equal.sym(
                      List<&2, U32>,
                      k,
                      key,
                      Shared.List.is_eq_sound(~U32, ~U32.is_eq, ~Shared.U32.laws(), k, key)(eb)
                    )
                  ),
                  Hist.find(
                    ~mach,
                    ~d,
                    lr,
                    l,
                    Tip.log(t),
                    k,
                    None{},
                    Ext.based_grows(~mach, ~d, l, Run{lr, t, a}, bd, ha)
                  )(em)
                )
              ),
              Keep.found(
                Trees.Ops.look(Led.L(mach, d), Led.tree(mach, d))(l)(Tip.log(t))(key),
                val,
                hg
              )
            )
          )
        )
      )

# after a write that the ledger l holds, the log reads each other key as
# before, in l (w: the law of the write)
def Keep.fin.of(
  ~mach: Machine(),
  ~d: Led(mach),
  +l: Led.L(mach, d),
  +t: Tip,
  +k: List<&2, U32>,
  +key: List<&2, U32>,
  +val: List<&2, U32>,
  +x: List<&2, U32>,
  +e: Trees.Edit,
  ne: {Shared.List.is_eq(~U32, ~U32.is_eq, k, key) == False{}: Bool},
  hg: {Tip.get(~mach, ~d, l, t, key) == Some{val}: Maybe<&2, List<&2, U32>>},
  w: {
    Trees.Ops.look(Led.L(mach, d), Led.tree(mach, d))(l)(Trees.Edit.root(e))(k)
      == Trees.Look.of(Some{x}): Trees.Look
  }
    & (
      @k2: List<&2, U32> -> {
        Shared.List.is_eq(~U32, ~U32.is_eq, k, k2) == False{}: Bool
      } -> {
        Trees.Ops.look(Led.L(mach, d), Led.tree(mach, d))(l)(Trees.Edit.root(e))(k2)
          == Trees.Ops.look(Led.L(mach, d), Led.tree(mach, d))(l)(Tip.log(t))(k2): Trees.Look
      }
    )
) -> {Tip.get(~mach, ~d, l, Tip.logged(t, Trees.Edit.root(e)), key) == Some{val}: Maybe<&2, List<&2, U32>>}:
  match w:
    case Tuple{w1, w2}:
      %Equal.sym(
        Maybe<&2, Hashes.Hash>,
        Tip.log(Tip.logged(t, Trees.Edit.root(e))),
        Trees.Edit.root(e),
        Keep.log_logged(t, Trees.Edit.root(e))
      ): {Tree.get(~mach, ~d, l, _, key) == Some{val}: Maybe<&2, List<&2, U32>>}
      %Equal.sym(
        Trees.Look,
        Trees.Ops.look(Led.L(mach, d), Led.tree(mach, d))(l)(Trees.Edit.root(e))(key),
        Trees.Ops.look(Led.L(mach, d), Led.tree(mach, d))(l)(Tip.log(t))(key),
        w2(key)(ne)
      ): {Trees.Look.value(_) == Some{val}: Maybe<&2, List<&2, U32>>}
      hg

# after a write of an absent key, whose nodes l holds, the log reads key as before
def Keep.fin(
  ~mach: Machine(),
  ~d: Led(mach),
  +l: Led.L(mach, d),
  +lr: Led.L(mach, d),
  +t: Tip,
  +a: List<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +x: List<&2, U32>,
  +key: List<&2, U32>,
  +val: List<&2, U32>,
  +e: Trees.Edit,
  ep: {Tree.put(~mach, ~d, lr, Tip.log(t), k, Some{x}) == Some{e}: Maybe<&2, Trees.Edit>},
  em: {Tip.find(~mach, ~d, lr, t, k) == Some{None{}}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
  +bd: Ext.Based(mach, d, l, Run{lr, t, a}),
  +hg: {Tip.get(~mach, ~d, l, t, key) == Some{val}: Maybe<&2, List<&2, U32>>},
  hn: {Ext.holds(~mach, ~d, l, Trees.Edit.nodes(e)) == True{}: Bool},
  +ha: {Ext.holds(~mach, ~d, l, a) == True{}: Bool}
) -> {Tip.get(~mach, ~d, l, Tip.logged(t, Trees.Edit.root(e)), key) == Some{val}: Maybe<&2, List<&2, U32>>}:
  Keep.fin.of(
    ~mach,
    ~d,
    l,
    t,
    k,
    key,
    val,
    x,
    e,
    Keep.ne.at(
      ~mach,
      ~d,
      l,
      lr,
      t,
      k,
      key,
      val,
      a,
      bd,
      ha,
      Shared.List.is_eq(~U32, ~U32.is_eq, k, key),
      {==},
      em,
      hg
    ),
    hg,
    Hist.write(mach, d)(lr)(l)(Tip.log(t))(k)(Some{x})(e)(ep)(Ext.based_grows(~mach, ~d, l, Run{lr, t, a}, bd, ha))(
      Ext.held(~mach, ~d, l, e, hn)
    )
  )

# a write of an absent key keeps each other key
def Keep.logged(
  ~mach: Machine(),
  ~d: Led(mach),
  +l: Led.L(mach, d),
  +key: List<&2, U32>,
  +val: List<&2, U32>,
  +lr: Led.L(mach, d),
  +t: Tip,
  +a: List<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +x: List<&2, U32>,
  p: Maybe<&2, Trees.Edit>,
  ep: {Tree.put(~mach, ~d, lr, Tip.log(t), k, Some{x}) == p: Maybe<&2, Trees.Edit>},
  em: {Tip.find(~mach, ~d, lr, t, k) == Some{None{}}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
  +bd: Ext.Based(mach, d, l, Run{lr, t, a}),
  kh: Keep.Has(mach, d, l, key, val, Run{lr, t, a})
) -> Keep.Out(mach, d, l, key, val, Run.logged(~mach, ~d, lr, t, a, p)):
  match p:
    case None{}:
      Unit{}
    case Some{+e}:
      +hh => Keep.fin(
        ~mach,
        ~d,
        l,
        lr,
        t,
        a,
        k,
        x,
        key,
        val,
        e,
        ep,
        em,
        bd,
        kh(Ext.holds_right(~mach, ~d, l, Trees.Edit.nodes(e), a)(hh)),
        Ext.holds_left(~mach, ~d, l, Trees.Edit.nodes(e), a)(hh),
        Ext.holds_right(~mach, ~d, l, Trees.Edit.nodes(e), a)(hh)
      )

# Run.add.at keeps each other key
def Keep.add.at(
  ~mach: Machine(),
  ~d: Led(mach),
  +l: Led.L(mach, d),
  +key: List<&2, U32>,
  +val: List<&2, U32>,
  r: Run<Led.L(mach, d)>,
  +k: List<&2, U32>,
  +x: List<&2, U32>,
  m: Maybe<&2, Maybe<&2, List<&2, U32>>>,
  em: {
    Tip.find(~mach, ~d, Run.ledger(Led.L(mach, d), r), Run.tip(Led.L(mach, d), r), k) == m: Maybe<&2, Maybe<&2, List<&2, U32>>>
  },
  bd: Ext.Based(mach, d, l, r),
  kh: Keep.Has(mach, d, l, key, val, r)
) -> Keep.Out(mach, d, l, key, val, Run.add.at(~mach, ~d, r, k, x, m)):
  match r m:
    case Run{+lr, +t, +a} Some{None{}}:
      Keep.logged(~mach, ~d, l, key, val, lr, t, a, k, x, Tree.put(~mach, ~d, lr, Tip.log(t), k, Some{x}), {==}, em, bd, kh)
    case y Some{Some{old}}:
      Unit{}
    case y None{}:
      Unit{}

# Run.add keeps each other key
def Keep.add(
  ~mach: Machine(),
  ~d: Led(mach),
  +l: Led.L(mach, d),
  +key: List<&2, U32>,
  +val: List<&2, U32>,
  +r: Run<Led.L(mach, d)>,
  +k: List<&2, U32>,
  +x: List<&2, U32>,
  bd: Ext.Based(mach, d, l, r),
  kh: Keep.Has(mach, d, l, key, val, r)
) -> Keep.Out(mach, d, l, key, val, Run.add(~mach, ~d, r, k, x)):
  Keep.add.at(
    ~mach,
    ~d,
    l,
    key,
    val,
    r,
    k,
    x,
    Tip.find(~mach, ~d, Run.ledger(Led.L(mach, d), r), Run.tip(Led.L(mach, d), r), k),
    {==},
    bd,
    kh
  )

# a refusal keeps each key
def Keep.stale(
  ~mach: Machine(),
  ~d: Led(mach),
  +l: Led.L(mach, d),
  +key: List<&2, U32>,
  +val: List<&2, U32>,
  +r: Run<Led.L(mach, d)>,
  +i: Ledgers.Id,
  +a: Hashes.Hash,
  bd: Ext.Based(mach, d, l, r),
  kh: Keep.Has(mach, d, l, key, val, r)
) -> Keep.Out(mach, d, l, key, val, Step.stale(~mach, ~d, r, i, a)):
  Keep.add(~mach, ~d, l, key, val, r, Log.out(i), Out.code(Out.Stale{a}, []), bd, kh)

# one request on keeps each key
def Keep.step_next(
  ~mach: Machine(),
  ~d: Led(mach),
  +l: Led.L(mach, d),
  +key: List<&2, U32>,
  +val: List<&2, U32>,
  r: Run<Led.L(mach, d)>,
  +vs: Maybe<&2, List<&2, String>>,
  kh: Keep.Has(mach, d, l, key, val, r)
) -> Keep.Has(mach, d, l, key, val, Run.next(Led.L(mach, d), r, vs)):
  match r:
    case Run{lr, +t, a}:
      hh =>
        %Equal.sym(Maybe<&2, Hashes.Hash>, Tip.log(Tip.next(t, vs)), Tip.log(t), Keep.log_next(t, vs)): {
          Tree.get(~mach, ~d, l, _, key) == Some{val}: Maybe<&2, List<&2, U32>>
        }
        kh(hh)

# new content keeps each key
def Keep.over(
  ~mach: Machine(),
  ~d: Led(mach),
  +l: Led.L(mach, d),
  +key: List<&2, U32>,
  +val: List<&2, U32>,
  r: Run<Led.L(mach, d)>,
  +ns: List<&2, List<&2, U32>>,
  +h: Maybe<&2, Hashes.Hash>,
  kh: Keep.Has(mach, d, l, key, val, r)
) -> Keep.Has(mach, d, l, key, val, Run.over(~mach, ~d, r, ns, h)):
  match r:
    case Run{lr, +t, +a}:
      hh =>
        %Equal.sym(Maybe<&2, Hashes.Hash>, Tip.log(Tip.over(t, h)), Tip.log(t), Keep.log_over(t, h)): {
          Tree.get(~mach, ~d, l, _, key) == Some{val}: Maybe<&2, List<&2, U32>>
        }
        kh(Ext.holds_right(~mach, ~d, l, ns, a)(hh))

# a run then a step that keeps each key keeps each key
def Keep.bind(
  ~mach: Machine(),
  ~d: Led(mach),
  +l: Led.L(mach, d),
  -key: List<&2, U32>,
  -val: List<&2, U32>,
  +r: Run<Led.L(mach, d)>,
  m: Maybe<&2, Run<Led.L(mach, d)>>,
  g: Run<Led.L(mach, d)> -> Maybe<&2, Run<Led.L(mach, d)>>,
  hm: Keep.Out(mach, d, l, key, val, m),
  gm: Ext.GainM(mach, d, l, r, m),
  bd: Ext.Based(mach, d, l, r),
  hg: @r1: Run<Led.L(mach, d)> -> Ext.Based(mach, d, l, r1) -> Keep.Has(mach, d, l, key, val, r1)
    -> Keep.Out(mach, d, l, key, val, g(r1))
) -> Keep.Out(mach, d, l, key, val, Maybe.bind(&2, Run<Led.L(mach, d)>, Run<Led.L(mach, d)>, m, g)):
  match m:
    case None{}:
      Unit{}
    case Some{+r1}:
      hg(r1)(Ext.based(~mach, ~d, l, r, r1, bd, gm))(hm)

# taking a request keeps each key
def Keep.taken.at(
  ~mach: Machine(),
  ~d: Led(mach),
  +l: Led.L(mach, d),
  +key: List<&2, U32>,
  +val: List<&2, U32>,
  +r: Run<Led.L(mach, d)>,
  +i: Ledgers.Id,
  +a: Hashes.Hash,
  +n: U32,
  +vs: Maybe<&2, List<&2, String>>,
  +bd: Ext.Based(mach, d, l, r),
  kh: Keep.Has(mach, d, l, key, val, r)
) -> Keep.Out(mach, d, l, key, val, Step.taken.at(~mach, ~d, r, i, a, n, vs)):
  Keep.bind(
    ~mach,
    ~d,
    l,
    key,
    val,
    r,
    Run.add(~mach, ~d, r, Log.out(i), Out.code(Out.Taken{a, n}, [])),
    +r1 => Maybe.bind(
      &2,
      Run<Led.L(mach, d)>,
      Run<Led.L(mach, d)>,
      Run.add(
        ~mach,
        ~d,
        r1,
        Log.taken(n),
        Taken.code(Taken{i, Tip.content(Run.tip(Led.L(mach, d), r1))}, [])
      ),
      r2 => Some{Run.next(Led.L(mach, d), r2, vs)}
    ),
    Keep.add(~mach, ~d, l, key, val, r, Log.out(i), Out.code(Out.Taken{a, n}, []), bd, kh),
    Ext.add(~mach, ~d, l, r, Log.out(i), Out.code(Out.Taken{a, n}, [])),
    bd,
    +r1 => +bd1 => kh1 => Keep.bind(
      ~mach,
      ~d,
      l,
      key,
      val,
      r1,
      Run.add(
        ~mach,
        ~d,
        r1,
        Log.taken(n),
        Taken.code(Taken{i, Tip.content(Run.tip(Led.L(mach, d), r1))}, [])
      ),
      r2 => Some{Run.next(Led.L(mach, d), r2, vs)},
      Keep.add(
        ~mach,
        ~d,
        l,
        key,
        val,
        r1,
        Log.taken(n),
        Taken.code(Taken{i, Tip.content(Run.tip(Led.L(mach, d), r1))}, []),
        bd1,
        kh1
      ),
      Ext.add(
        ~mach,
        ~d,
        l,
        r1,
        Log.taken(n),
        Taken.code(Taken{i, Tip.content(Run.tip(Led.L(mach, d), r1))}, [])
      ),
      bd1,
      r2 => bd2 => kh2 => Keep.step_next(~mach, ~d, l, key, val, r2, vs, kh2)
    )
  )

# taking a request as the next number keeps each key
def Keep.taken(
  ~mach: Machine(),
  ~d: Led(mach),
  +l: Led.L(mach, d),
  +key: List<&2, U32>,
  +val: List<&2, U32>,
  +r: Run<Led.L(mach, d)>,
  +i: Ledgers.Id,
  +a: Hashes.Hash,
  +vs: Maybe<&2, List<&2, String>>,
  bd: Ext.Based(mach, d, l, r),
  kh: Keep.Has(mach, d, l, key, val, r)
) -> Keep.Out(mach, d, l, key, val, Step.taken(~mach, ~d, r, i, a, vs)):
  Keep.taken.at(~mach, ~d, l, key, val, r, i, a, Tip.count(Run.tip(Led.L(mach, d), r)), vs, bd, kh)

# a label keeps each key
def Keep.labelled(
  ~mach: Machine(),
  ~d: Led(mach),
  +l: Led.L(mach, d),
  +key: List<&2, U32>,
  +val: List<&2, U32>,
  +r: Run<Led.L(mach, d)>,
  +i: Ledgers.Id,
  +a: Hashes.Hash,
  +m: String,
  v: Maybe<&2, Taken>,
  +bd: Ext.Based(mach, d, l, r),
  kh: Keep.Has(mach, d, l, key, val, r)
) -> Keep.Out(mach, d, l, key, val, Step.labelled(~mach, ~d, r, i, a, m, v)):
  match v:
    case None{}:
      Unit{}
    case Some{+x}:
      Keep.bind(
        ~mach,
        ~d,
        l,
        key,
        val,
        r,
        Run.add(~mach, ~d, r, Log.label(m), Ledgers.Id.code(Taken.id(x), [])),
        r2 => Step.taken(~mach, ~d, r2, i, a, None{}),
        Keep.add(~mach, ~d, l, key, val, r, Log.label(m), Ledgers.Id.code(Taken.id(x), []), bd, kh),
        Ext.add(~mach, ~d, l, r, Log.label(m), Ledgers.Id.code(Taken.id(x), [])),
        bd,
        r2 => bd2 => kh2 => Keep.taken(~mach, ~d, l, key, val, r2, i, a, None{}, bd2, kh2)
      )

# Step.label.at keeps each key
def Keep.label.at(
  ~mach: Machine(),
  ~d: Led(mach),
  +l: Led.L(mach, d),
  +key: List<&2, U32>,
  +val: List<&2, U32>,
  +r: Run<Led.L(mach, d)>,
  +i: Ledgers.Id,
  +a: Hashes.Hash,
  +m: String,
  k: Maybe<&2, Maybe<&2, Ledgers.Id>>,
  +bd: Ext.Based(mach, d, l, r),
  kh: Keep.Has(mach, d, l, key, val, r)
) -> Keep.Out(mach, d, l, key, val, Step.label.at(~mach, ~d, r, i, a, m, k)):
  match k:
    case None{}:
      Unit{}
    case Some{Some{x}}:
      Keep.stale(~mach, ~d, l, key, val, r, i, a, bd, kh)
    case Some{None{}}:
      Shared.Bool.when_cases(
        Maybe<&2, Run<Led.L(mach, d)>>,
        z => Keep.Has(mach, d, l, key, val, r) -> Keep.Out(mach, d, l, key, val, z),
        U32.is_eq(Tip.count(Run.tip(Led.L(mach, d), r)), 0),
        u => Step.stale(~mach, ~d, r, i, a),
        u => Step.labelled(
          ~mach,
          ~d,
          r,
          i,
          a,
          m,
          Tip.taken(
            ~mach,
            ~d,
            Run.ledger(Led.L(mach, d), r),
            Run.tip(Led.L(mach, d), r),
            U32.sub(Tip.count(Run.tip(Led.L(mach, d), r)), 1)
          )
        ),
        e => kh1 => Keep.stale(~mach, ~d, l, key, val, r, i, a, bd, kh1),
        e => kh1 => Keep.labelled(
          ~mach,
          ~d,
          l,
          key,
          val,
          r,
          i,
          a,
          m,
          Tip.taken(
            ~mach,
            ~d,
            Run.ledger(Led.L(mach, d), r),
            Run.tip(Led.L(mach, d), r),
            U32.sub(Tip.count(Run.tip(Led.L(mach, d), r)), 1)
          ),
          bd,
          kh1
        )
      )(kh)

# a request for a label keeps each key
def Keep.label(
  ~mach: Machine(),
  ~d: Led(mach),
  +l: Led.L(mach, d),
  +key: List<&2, U32>,
  +val: List<&2, U32>,
  +r: Run<Led.L(mach, d)>,
  +i: Ledgers.Id,
  +a: Hashes.Hash,
  +m: String,
  bd: Ext.Based(mach, d, l, r),
  kh: Keep.Has(mach, d, l, key, val, r)
) -> Keep.Out(mach, d, l, key, val, Step.label(~mach, ~d, r, i, a, m)):
  Keep.label.at(
    ~mach,
    ~d,
    l,
    key,
    val,
    r,
    i,
    a,
    m,
    Tip.known(
      ~Ledgers.Id,
      ~Ledgers.Id.code,
      ~Ledgers.Id.code.read,
      Tip.find(~mach, ~d, Run.ledger(Led.L(mach, d), r), Run.tip(Led.L(mach, d), r), Log.label(m))
    ),
    bd,
    kh
  )

# opening a sub line keeps each key
def Keep.opens(
  ~mach: Machine(),
  ~d: Led(mach),
  +l: Led.L(mach, d),
  +key: List<&2, U32>,
  +val: List<&2, U32>,
  +r: Run<Led.L(mach, d)>,
  +i: Ledgers.Id,
  +a: Hashes.Hash,
  +b: String,
  +t: Tip,
  +ns: List<&2, List<&2, U32>>,
  +bd: Ext.Based(mach, d, l, r),
  kh: Keep.Has(mach, d, l, key, val, r)
) -> Keep.Out(mach, d, l, key, val, Step.opens(~mach, ~d, r, i, a, b, t, ns)):
  +r0 = Run.over(~mach, ~d, r, Tip.code(t, []) <> ns, Tip.content(Run.tip(Led.L(mach, d), r)))
  Keep.bind(
    ~mach,
    ~d,
    l,
    key,
    val,
    r,
    Run.add(~mach, ~d, r0, Log.start(b), Hashes.Hash.code(Tip.hash(t), [])),
    r2 => Step.taken(~mach, ~d, r2, i, a, None{}),
    Keep.add(
      ~mach,
      ~d,
      l,
      key,
      val,
      r0,
      Log.start(b),
      Hashes.Hash.code(Tip.hash(t), []),
      Ext.based(
        ~mach,
        ~d,
        l,
        r,
        r0,
        bd,
        Ext.over(~mach, ~d, l, r, Tip.code(t, []) <> ns, Tip.content(Run.tip(Led.L(mach, d), r)))
      ),
      Keep.over(~mach, ~d, l, key, val, r, Tip.code(t, []) <> ns, Tip.content(Run.tip(Led.L(mach, d), r)), kh)
    ),
    Ext.transM(
      ~mach,
      ~d,
      l,
      r,
      r0,
      Run.add(~mach, ~d, r0, Log.start(b), Hashes.Hash.code(Tip.hash(t), [])),
      Ext.over(~mach, ~d, l, r, Tip.code(t, []) <> ns, Tip.content(Run.tip(Led.L(mach, d), r))),
      Ext.add(~mach, ~d, l, r0, Log.start(b), Hashes.Hash.code(Tip.hash(t), []))
    ),
    bd,
    r2 => bd2 => kh2 => Keep.taken(~mach, ~d, l, key, val, r2, i, a, None{}, bd2, kh2)
  )

# an act of a kernel keeps each key
def Keep.act(
  ~mach: Machine(),
  ~d: Led(mach),
  +l: Led.L(mach, d),
  +key: List<&2, U32>,
  +val: List<&2, U32>,
  +r: Run<Led.L(mach, d)>,
  +i: Ledgers.Id,
  +a: Hashes.Hash,
  m: Maybe<&2, Act>,
  +bd: Ext.Based(mach, d, l, r),
  kh: Keep.Has(mach, d, l, key, val, r)
) -> Keep.Out(mach, d, l, key, val, Act.run(~mach, ~d, r, i, a, m)):
  match m:
    case None{}:
      Unit{}
    case Some{Act.Stale{}}:
      Keep.stale(~mach, ~d, l, key, val, r, i, a, bd, kh)
    case Some{Act.Label{x}}:
      Keep.label(~mach, ~d, l, key, val, r, i, a, x, bd, kh)
    case Some{Act.Taken{+vs, +h, +ns}}:
      Keep.taken(
        ~mach,
        ~d,
        l,
        key,
        val,
        Run.over(~mach, ~d, r, ns, h),
        i,
        a,
        vs,
        Ext.based(~mach, ~d, l, r, Run.over(~mach, ~d, r, ns, h), bd, Ext.over(~mach, ~d, l, r, ns, h)),
        Keep.over(~mach, ~d, l, key, val, r, ns, h, kh)
      )
    case Some{Act.Opens{b, t, ns}}:
      Keep.opens(~mach, ~d, l, key, val, r, i, a, b, t, ns, bd, kh)

# a request with the outcome o keeps each key
def Keep.fresh(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  +l: Led.L(mach, d),
  +key: List<&2, U32>,
  +val: List<&2, U32>,
  +r: Run<Led.L(mach, d)>,
  +c: Ledgers.Line,
  +i: Ledgers.Id,
  +a: Hashes.Hash,
  +q: Machine.Q(mach),
  o: Maybe<&2, Maybe<&2, Out>>,
  bd: Ext.Based(mach, d, l, r),
  kh: Keep.Has(mach, d, l, key, val, r)
) -> Keep.Out(mach, d, l, key, val, Step.fresh(~mach, ~d, ~kern, r, c, i, a, q, o)):
  match o:
    case None{}:
      Unit{}
    case Some{Some{x}}:
      kh
    case Some{None{}}:
      Keep.act(
        ~mach,
        ~d,
        l,
        key,
        val,
        r,
        i,
        a,
        Kernel.change(mach, d, kern)(Run.ledger(Led.L(mach, d), r))(Run.tip(Led.L(mach, d), r))(c)(i)(q),
        bd,
        kh
      )

# the entry m keeps each key
def Keep.asked(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  +l: Led.L(mach, d),
  +key: List<&2, U32>,
  +val: List<&2, U32>,
  +r: Run<Led.L(mach, d)>,
  +c: Ledgers.Line,
  +a: Hashes.Hash,
  m: Maybe<&2, Entry(mach)>,
  bd: Ext.Based(mach, d, l, r),
  kh: Keep.Has(mach, d, l, key, val, r)
) -> Keep.Out(mach, d, l, key, val, Step.asked(~mach, ~d, ~kern, r, c, a, m)):
  match m:
    case Some{Ledgers.Entry.Ask{+i, t, q}}:
      Keep.fresh(
        ~mach,
        ~d,
        ~kern,
        l,
        key,
        val,
        r,
        c,
        i,
        a,
        q,
        Tip.known(
          ~Out,
          ~Out.code,
          ~Out.code.read,
          Tip.find(~mach, ~d, Run.ledger(Led.L(mach, d), r), Run.tip(Led.L(mach, d), r), Log.out(i))
        ),
        bd,
        kh
      )
    case None{}:
      Unit{}
    case Some{Ledgers.Entry.Ballot{x}}:
      Unit{}
    case Some{Ledgers.Entry.Data{x}}:
      Unit{}
    case Some{Ledgers.Entry.Lie{x}}:
      Unit{}

# one request keeps each key
def Keep.one(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  +l: Led.L(mach, d),
  +key: List<&2, U32>,
  +val: List<&2, U32>,
  +r: Run<Led.L(mach, d)>,
  +c: Ledgers.Line,
  +a: Hashes.Hash,
  bd: Ext.Based(mach, d, l, r),
  kh: Keep.Has(mach, d, l, key, val, r)
) -> Keep.Out(mach, d, l, key, val, Step.one(~mach, ~d, ~kern, r, c, a)):
  Keep.asked(
    ~mach,
    ~d,
    ~kern,
    l,
    key,
    val,
    r,
    c,
    a,
    Led.get(~mach, ~d, Run.ledger(Led.L(mach, d), r), Ledgers.Name.Ask{a}),
    bd,
    kh
  )

# that the run m, when there is one, is based on l and keeps the key
def Keep.All(
  -mach: Machine(),
  -d: Led(mach),
  -l: Led.L(mach, d),
  -key: List<&2, U32>,
  -val: List<&2, U32>,
  m: Maybe<&2, Run<Led.L(mach, d)>>
) -> Type:
  match m:
    case None{}:
      Unit
    case Some{r}:
      Ext.Based(mach, d, l, r) & Keep.Has(mach, d, l, key, val, r)

# Keep.All of a run m2 that follows r1
def Keep.all_pair(
  ~mach: Machine(),
  ~d: Led(mach),
  +l: Led.L(mach, d),
  -key: List<&2, U32>,
  -val: List<&2, U32>,
  +r1: Run<Led.L(mach, d)>,
  m2: Maybe<&2, Run<Led.L(mach, d)>>,
  ko: Keep.Out(mach, d, l, key, val, m2),
  gm: Ext.GainM(mach, d, l, r1, m2),
  bd: Ext.Based(mach, d, l, r1)
) -> Keep.All(mach, d, l, key, val, m2):
  match m2:
    case None{}:
      Unit{}
    case Some{+r2}:
      Tuple{Ext.based(~mach, ~d, l, r1, r2, bd, gm), ko}

# Keep.All after one more request
def Keep.all_step(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  +l: Led.L(mach, d),
  +key: List<&2, U32>,
  +val: List<&2, U32>,
  +c: Ledgers.Line,
  +q: Hashes.Hash,
  m: Maybe<&2, Run<Led.L(mach, d)>>,
  hm: Keep.All(mach, d, l, key, val, m)
) -> Keep.All(
  mach,
  d,
  l,
  key,
  val,
  Maybe.bind(&2, Run<Led.L(mach, d)>, Run<Led.L(mach, d)>, m, x => Step.one(~mach, ~d, ~kern, x, c, q))
):
  match m:
    case None{}:
      Unit{}
    case Some{+r1}:
      match hm:
        case Tuple{+bd, kh}:
          Keep.all_pair(
            ~mach,
            ~d,
            l,
            key,
            val,
            r1,
            Step.one(~mach, ~d, ~kern, r1, c, q),
            Keep.one(~mach, ~d, ~kern, l, key, val, r1, c, q, bd, kh),
            Ext.one(~mach, ~d, ~kern, l, r1, c, q),
            bd
          )

# Keep.All gives Keep.Out
def Keep.all_out(
  -mach: Machine(),
  -d: Led(mach),
  -l: Led.L(mach, d),
  -key: List<&2, U32>,
  -val: List<&2, U32>,
  m: Maybe<&2, Run<Led.L(mach, d)>>,
  hm: Keep.All(mach, d, l, key, val, m)
) -> Keep.Out(mach, d, l, key, val, m):
  match m:
    case None{}:
      Unit{}
    case Some{r}:
      match hm:
        case Tuple{bd, kh}:
          kh

# the requests qs keep each key
def Keep.all(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  +l: Led.L(mach, d),
  +key: List<&2, U32>,
  +val: List<&2, U32>,
  +c: Ledgers.Line,
  qs: List<&2, Hashes.Hash>,
  +m: Maybe<&2, Run<Led.L(mach, d)>>,
  hm: Keep.All(mach, d, l, key, val, m)
) -> Keep.Out(mach, d, l, key, val, Step.all(~mach, ~d, ~kern, c, qs, m)):
  match qs:
    case Nil{}:
      Keep.all_out(mach, d, l, key, val, m, hm)
    case Con{+q, rest}:
      Keep.all(
        ~mach,
        ~d,
        ~kern,
        l,
        key,
        val,
        c,
        rest,
        Maybe.bind(&2, Run<Led.L(mach, d)>, Run<Led.L(mach, d)>, m, x => Step.one(~mach, ~d, ~kern, x, c, q)),
        Keep.all_step(~mach, ~d, ~kern, l, key, val, c, q, m, hm)
      )

# Line.landed once the check of its run is known (b)
def Keep.landed.at(
  ~mach: Machine(),
  ~d: Led(mach),
  +l: Led.L(mach, d),
  +tr: Tip,
  +a: List<&2, List<&2, U32>>,
  after: Maybe<&2, Hashes.Hash>,
  -x: Tip,
  +key: List<&2, U32>,
  +val: List<&2, U32>,
  b: Bool,
  eb: {
    Bool.and(Tips.same(Some{Tip.hash(tr)}, after), Ext.holds(~mach, ~d, l, a)) == b: Bool
  },
  ko: {Ext.holds(~mach, ~d, l, a) == True{}: Bool}
    -> {Tip.get(~mach, ~d, l, tr, key) == Some{val}: Maybe<&2, List<&2, U32>>},
  e: {Shared.Maybe.when(Tip, b, u => Some{tr}) == Some{x}: Maybe<&2, Tip>}
) -> {Tip.get(~mach, ~d, l, x, key) == Some{val}: Maybe<&2, List<&2, U32>>}:
  match b:
    case True{}:
      %Shared.Maybe.some_inj(Tip, tr, x, e): {Tip.get(~mach, ~d, l, _, key) == Some{val}: Maybe<&2, List<&2, U32>>}
      ko(
        Shared.Bool.and_true_right(
          Tips.same(Some{Tip.hash(tr)}, after),
          Ext.holds(~mach, ~d, l, a)
        )(eb)
      )
    case False{}:
      Empty.absurd(
        {Tip.get(~mach, ~d, l, x, key) == Some{val}: Maybe<&2, List<&2, U32>>},
        Shared.Maybe.none_ne_some(Tip, x, e)
      )

# a run that lands keeps each key
def Keep.landed(
  ~mach: Machine(),
  ~d: Led(mach),
  +l: Led.L(mach, d),
  ma: Maybe<&2, Run<Led.L(mach, d)>>,
  +after: Maybe<&2, Hashes.Hash>,
  +x: Tip,
  +key: List<&2, U32>,
  +val: List<&2, U32>,
  ko: Keep.Out(mach, d, l, key, val, ma),
  e: {Line.landed(~mach, ~d, l, ma, after) == Some{x}: Maybe<&2, Tip>}
) -> {Tip.get(~mach, ~d, l, x, key) == Some{val}: Maybe<&2, List<&2, U32>>}:
  match ma:
    case None{}:
      Empty.absurd(
        {Tip.get(~mach, ~d, l, x, key) == Some{val}: Maybe<&2, List<&2, U32>>},
        Shared.Maybe.none_ne_some(Tip, x, e)
      )
    case Some{Run{lr, +tr, +a}}:
      Keep.landed.at(
        ~mach,
        ~d,
        l,
        tr,
        a,
        after,
        x,
        key,
        val,
        Bool.and(Tips.same(Some{Tip.hash(tr)}, after), Ext.holds(~mach, ~d, l, a)),
        {==},
        ko,
        e
      )

# Line.moved once whether the step names the tip is known (b)
def Keep.moved.at(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  +l: Led.L(mach, d),
  +c: Ledgers.Line,
  +t: Tip,
  +qs: List<&2, Hashes.Hash>,
  +after: Maybe<&2, Hashes.Hash>,
  +x: Tip,
  +key: List<&2, U32>,
  +val: List<&2, U32>,
  b: Bool,
  e: {
    Shared.Maybe.when(
      Tip,
      b,
      u => Line.landed(~mach, ~d, l, Step.run(~mach, ~d, ~kern, l, c, t, qs), after)
    )
      == Some{x}: Maybe<&2, Tip>
  },
  hg: {Tip.get(~mach, ~d, l, t, key) == Some{val}: Maybe<&2, List<&2, U32>>}
) -> {Tip.get(~mach, ~d, l, x, key) == Some{val}: Maybe<&2, List<&2, U32>>}:
  match b:
    case True{}:
      Keep.landed(
        ~mach,
        ~d,
        l,
        Step.run(~mach, ~d, ~kern, l, c, t, qs),
        after,
        x,
        key,
        val,
        Keep.all(
          ~mach,
          ~d,
          ~kern,
          l,
          key,
          val,
          c,
          qs,
          Some{Run{l, t, []}},
          Tuple{Tuple{[], Tuple{{==}, {==}}}, u => hg}
        ),
        e
      )
    case False{}:
      Empty.absurd(
        {Tip.get(~mach, ~d, l, x, key) == Some{val}: Maybe<&2, List<&2, U32>>},
        Shared.Maybe.none_ne_some(Tip, x, e)
      )

# a step that moves a line keeps each key of its log
def Keep.moved(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  +l: Led.L(mach, d),
  +c: Ledgers.Line,
  +t: Tip,
  m: Maybe<&2, Ledgers.Step>,
  +x: Tip,
  +key: List<&2, U32>,
  +val: List<&2, U32>,
  e: {Line.moved(~mach, ~d, ~kern, l, c, t, m) == Some{x}: Maybe<&2, Tip>},
  hg: {Tip.get(~mach, ~d, l, t, key) == Some{val}: Maybe<&2, List<&2, U32>>}
) -> {Tip.get(~mach, ~d, l, x, key) == Some{val}: Maybe<&2, List<&2, U32>>}:
  match m:
    case None{}:
      Empty.absurd(
        {Tip.get(~mach, ~d, l, x, key) == Some{val}: Maybe<&2, List<&2, U32>>},
        Shared.Maybe.none_ne_some(Tip, x, e)
      )
    case Some{Ledgers.Step{before, qs, after}}:
      Keep.moved.at(
        ~mach,
        ~d,
        ~kern,
        l,
        c,
        t,
        qs,
        after,
        x,
        key,
        val,
        Tips.same(before, Some{Tip.hash(t)}),
        e,
        hg
      )

# Runs in a later ledger
# ----------------------
# A run in a and the same run in a later ledger b reach the same tip, with the
# same added nodes, while a holds what the run in a added.

# that the run rb in b is the run ra in a: the same tip and added nodes, and
# each ledger is its own ledger with the same data put
def Sim.Rel(
  -mach: Machine(),
  -d: Led(mach),
  -a: Led.L(mach, d),
  -b: Led.L(mach, d),
  ra: Run<Led.L(mach, d)>,
  -rb: Run<Led.L(mach, d)>
) -> Data:
  match ra:
    case Run{la, ta, aa}:
      +Sigma<Led.L(mach, d), lb => +Sigma<
        {rb == Run{lb, ta, aa}: Run<Led.L(mach, d)>},
        e => +Sigma<Ext.Based(mach, d, a, Run{la, ta, aa}), x => Ext.Based(mach, d, b, Run{lb, ta, aa})>>>

# Sim.Rel of the run ra and the result mb of a run in b: none breaks it
def Sim.R2(
  -mach: Machine(),
  -d: Led(mach),
  -a: Led.L(mach, d),
  -b: Led.L(mach, d),
  ra: Run<Led.L(mach, d)>,
  mb: Maybe<&2, Run<Led.L(mach, d)>>
) -> Data:
  match mb:
    case None{}:
      Empty
    case Some{rb}:
      Sim.Rel(mach, d, a, b, ra, rb)

# that the result mb in b of a run is that of ma in a, once a holds what ma
# added
def Sim.Out(
  -mach: Machine(),
  -d: Led(mach),
  -a: Led.L(mach, d),
  -b: Led.L(mach, d),
  ma: Maybe<&2, Run<Led.L(mach, d)>>,
  mb: Maybe<&2, Run<Led.L(mach, d)>>
) -> Type:
  match ma:
    case None{}:
      Unit
    case Some{ra}:
      {Ext.holds(~mach, ~d, a, Run.added(Led.L(mach, d), ra)) == True{}: Bool} -> Sim.R2(mach, d, a, b, ra, mb)

# that the run rb in b is the run ra in a, once a holds what ra added
def Sim.Has(
  -mach: Machine(),
  -d: Led(mach),
  -a: Led.L(mach, d),
  -b: Led.L(mach, d),
  ra: Run<Led.L(mach, d)>,
  rb: Run<Led.L(mach, d)>
) -> Type:
  Sim.Out(mach, d, a, b, Some{ra}, Some{rb})

# the ledger of a run in a, whose nodes a holds, grows into that of the same
# run in b
def Sim.grows(
  ~mach: Machine(),
  ~d: Led(mach),
  ~lg: Hist.LaterGrows(mach, d),
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  +later: {
    Bool.and(
      Ledgers.Kind.grows(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), a, b),
      Led.honest(~mach, ~d, b)
    )
      == True{}: Bool
  },
  +la: Led.L(mach, d),
  +ta: Tip,
  +aa: List<&2, List<&2, U32>>,
  +lb: Led.L(mach, d),
  bda: Ext.Based(mach, d, a, Run{la, ta, aa}),
  bdb: Ext.Based(mach, d, b, Run{lb, ta, aa}),
  ha: {Ext.holds(~mach, ~d, a, aa) == True{}: Bool}
) -> Led.Grows(mach, d, la, lb):
  Hist.trans(
    mach,
    d,
    la,
    a,
    lb,
    Ext.based_grows(~mach, ~d, a, Run{la, ta, aa}, bda, ha),
    Hist.trans(mach, d, a, b, lb, lg(a)(b)(later), Ext.based_from(~mach, ~d, b, Run{lb, ta, aa}, bdb))
  )

# b holds what a holds
def Sim.holds_b(
  ~mach: Machine(),
  ~d: Led(mach),
  ~lg: Hist.LaterGrows(mach, d),
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  +later: {
    Bool.and(
      Ledgers.Kind.grows(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), a, b),
      Led.honest(~mach, ~d, b)
    )
      == True{}: Bool
  },
  ns: List<&2, List<&2, U32>>,
  +h: {Ext.holds(~mach, ~d, a, ns) == True{}: Bool}
) -> {Ext.holds(~mach, ~d, b, ns) == True{}: Bool}:
  match ns:
    case Nil{}:
      {==}
    case Con{+w, +r}:
      Shared.List.all.if_both(
        Ext.has(~mach, ~d, b, w),
        u => Ext.holds(~mach, ~d, b, r)
      )(
        Hist.has.of(
          ~mach,
          ~d,
          b,
          w
        )(
          Hist.fetch(
            ~mach,
            ~d,
            a,
            b,
            Hashes.Sha.hash(w),
            w,
            lg(a)(b)(later)
          )(Hist.has(~mach, ~d, a, w)(Shared.List.all.if_hit(Ext.has(~mach, ~d, a, w), u => Ext.holds(~mach, ~d, a, r))(h)))
        )
      )(
        Sim.holds_b(
          ~mach,
          ~d,
          ~lg,
          a,
          b,
          later,
          r,
          Shared.List.all.if_rest(Ext.has(~mach, ~d, a, w), u => Ext.holds(~mach, ~d, a, r))(h)
        )
      )

# the ledgers of two related runs grow, once a holds what the run in a added
def Sim.grow_of(
  ~mach: Machine(),
  ~d: Led(mach),
  ~lg: Hist.LaterGrows(mach, d),
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  +later: {
    Bool.and(
      Ledgers.Kind.grows(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), a, b),
      Led.honest(~mach, ~d, b)
    )
      == True{}: Bool
  },
  ra: Run<Led.L(mach, d)>,
  rb: Run<Led.L(mach, d)>,
  rel: Sim.Rel(mach, d, a, b, ra, rb),
  ha: {Ext.holds(~mach, ~d, a, Run.added(Led.L(mach, d), ra)) == True{}: Bool}
) -> Led.Grows(mach, d, Run.ledger(Led.L(mach, d), ra), Run.ledger(Led.L(mach, d), rb)):
  match ra:
    case Run{+la, +ta, +aa}:
      match rel:
        case Tuple{+lb, Tuple{erb, Tuple{bda, bdb}}}:
          %Equal.sym(Run<Led.L(mach, d)>, rb, Run{lb, ta, aa}, erb): Led.Grows(
            mach,
            d,
            la,
            Run.ledger(Led.L(mach, d), _)
          )
          Sim.grows(~mach, ~d, ~lg, a, b, later, la, ta, aa, lb, bda, bdb, ha)

# two related runs have the same tip
def Sim.tip_of(
  -mach: Machine(),
  -d: Led(mach),
  -a: Led.L(mach, d),
  -b: Led.L(mach, d),
  ra: Run<Led.L(mach, d)>,
  -rb: Run<Led.L(mach, d)>,
  rel: Sim.Rel(mach, d, a, b, ra, rb)
) -> {Run.tip(Led.L(mach, d), ra) == Run.tip(Led.L(mach, d), rb): Tip}:
  match ra:
    case Run{la, ta, aa}:
      match rel:
        case Tuple{lb, Tuple{erb, x}}:
          %Equal.sym(Run<Led.L(mach, d)>, rb, Run{lb, ta, aa}, erb): {ta == Run.tip(Led.L(mach, d), _): Tip}
          {==}

# a result in b that equals the result in a run shaped like the one in a,
# once a holds what that run added: the result in a is the same (gm: the run
# in a follows ra; heq: the two results in b are equal; inner: the shaped one
# is related)
def Sim.cond(
  ~mach: Machine(),
  ~d: Led(mach),
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  +ra: Run<Led.L(mach, d)>,
  -rb: Run<Led.L(mach, d)>,
  ma: Maybe<&2, Run<Led.L(mach, d)>>,
  -mb: Maybe<&2, Run<Led.L(mach, d)>>,
  -mb2: Maybe<&2, Run<Led.L(mach, d)>>,
  gm: Ext.GainM(mach, d, a, ra, ma),
  sh: Sim.Has(mach, d, a, b, ra, rb),
  heq: Sim.Rel(mach, d, a, b, ra, rb) -> {Ext.holds(~mach, ~d, a, Run.added(Led.L(mach, d), ra)) == True{}: Bool}
    -> {mb2 == mb: Maybe<&2, Run<Led.L(mach, d)>>},
  inner: Sim.Has(mach, d, a, b, ra, rb) -> Sim.Out(mach, d, a, b, ma, mb2)
) -> Sim.Out(mach, d, a, b, ma, mb):
  match ma:
    case None{}:
      Unit{}
    case Some{+ra2}:
      +hh =>
        +hr = Ext.gain_holds(~mach, ~d, a, ra, ra2, gm, hh)
        +rel = sh(hr)
        %heq(rel)(hr): Sim.R2(mach, d, a, b, ra2, _)
        inner(u => rel)(hh)

# Sim.bind once the step in a is known (m2)
def Sim.bind.at(
  ~mach: Machine(),
  ~d: Led(mach),
  +a: Led.L(mach, d),
  -b: Led.L(mach, d),
  +r1: Run<Led.L(mach, d)>,
  m2: Maybe<&2, Run<Led.L(mach, d)>>,
  mb: Maybe<&2, Run<Led.L(mach, d)>>,
  -g: Run<Led.L(mach, d)> -> Maybe<&2, Run<Led.L(mach, d)>>,
  hm: Sim.Out(mach, d, a, b, Some{r1}, mb),
  gn: Ext.GainM(mach, d, a, r1, m2),
  hg1: @rb1: Run<Led.L(mach, d)> -> Sim.Has(mach, d, a, b, r1, rb1) -> Sim.Out(mach, d, a, b, m2, g(rb1))
) -> Sim.Out(mach, d, a, b, m2, Maybe.bind(&2, Run<Led.L(mach, d)>, Run<Led.L(mach, d)>, mb, g)):
  match m2 mb:
    case None{} y:
      Unit{}
    case Some{+r2} None{}:
      hh => hm(Ext.gain_holds(~mach, ~d, a, r1, r2, gn, hh))
    case Some{r2} Some{rb1}:
      hg1(rb1)(hm)

# a run then the same step, in a and in b, stay related
def Sim.bind(
  ~mach: Machine(),
  ~d: Led(mach),
  +a: Led.L(mach, d),
  -b: Led.L(mach, d),
  ma: Maybe<&2, Run<Led.L(mach, d)>>,
  mb: Maybe<&2, Run<Led.L(mach, d)>>,
  g: Run<Led.L(mach, d)> -> Maybe<&2, Run<Led.L(mach, d)>>,
  hm: Sim.Out(mach, d, a, b, ma, mb),
  gg: @r1: Run<Led.L(mach, d)> -> Ext.GainM(mach, d, a, r1, g(r1)),
  hg: @r1: Run<Led.L(mach, d)> -> @rb1: Run<Led.L(mach, d)> -> Sim.Has(mach, d, a, b, r1, rb1)
    -> Sim.Out(mach, d, a, b, g(r1), g(rb1))
) -> Sim.Out(
  mach,
  d,
  a,
  b,
  Maybe.bind(&2, Run<Led.L(mach, d)>, Run<Led.L(mach, d)>, ma, g),
  Maybe.bind(&2, Run<Led.L(mach, d)>, Run<Led.L(mach, d)>, mb, g)
):
  match ma:
    case None{}:
      Unit{}
    case Some{+r1}:
      Sim.bind.at(~mach, ~d, a, b, r1, g(r1), mb, g, hm, gg(r1), rb1 => hg(r1)(rb1))

# a step lands on the same tip in a later ledger
def Sim.moved(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  ~lg: Hist.LaterGrows(mach, d),
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  +later: {
    Bool.and(
      Ledgers.Kind.grows(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), a, b),
      Led.honest(~mach, ~d, b)
    )
      == True{}: Bool
  },
  +c: Ledgers.Line,
  +t: Tip,
  +v: Ledgers.Step,
  +x: Tip
) -> {Line.moved(~mach, ~d, ~kern, a, c, t, Some{v}) == Some{x}: Maybe<&2, Tip>}
  -> {Line.moved(~mach, ~d, ~kern, b, c, t, Some{v}) == Some{x}: Maybe<&2, Tip>}:
  ?TODO

# a step keeps each key that the log of its line holds, with its value
def Keep.next(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  +l: Led.L(mach, d),
  +c: Ledgers.Line,
  +h: U32,
  +t: Tip,
  +x: Tip,
  +key: List<&2, U32>,
  +v: List<&2, U32>
) -> {Line.next(~mach, ~d, ~kern, l, c, h, t) == Some{x}: Maybe<&2, Tip>}
  -> {Tip.get(~mach, ~d, l, t, key) == Some{v}: Maybe<&2, List<&2, U32>>}
  -> {Tip.get(~mach, ~d, l, x, key) == Some{v}: Maybe<&2, List<&2, U32>>}:
  e => hg => Keep.moved(
    ~mach,
    ~d,
    ~kern,
    l,
    c,
    t,
    Height.decide(
      ~mach,
      ~d,
      l,
      c,
      h,
      Tip.voters(t),
      Ledgers.Kind.rounds(Machine.Q(mach), Led.kind(mach, d))(l)(c)(h)
    ),
    x,
    key,
    v,
    e,
    hg
  )

# Histories that stay
# -------------------

# one history: the tip of a line after a number of steps stays as the ledger
# grows, while its ballots are honest. So two replicas whose ledgers an
# honest ledger holds are, after the same number of steps, at the same tip:
# no line has two histories, whatever the round of each step and whatever
# the order in which the entries came
law Line.at_grows:
  for ~mach: Machine()
  for ~d: Led(mach)
  for ~kern: Kernel(mach, d)
  for k: Nat
  for c: Ledgers.Line
  Shared.Read.Stable(
    Led.L(mach, d),
    a => b => Led.Later(~mach, ~d, a, b),
    Tip,
    l => Line.at(~mach, ~d, ~kern, k, l, c)
  )

# what a line knows is final: what the log of a line holds under a key, it
# holds for good, as the ledger grows and while its ballots are honest. An
# outcome, a taken request, a label and the first tip of a sub line are each
# one key of a log
law Line.get_grows:
  for ~mach: Machine()
  for ~d: Led(mach)
  for ~kern: Kernel(mach, d)
  for c: Ledgers.Line
  for key: List<&2, U32>
  Shared.Read.Stable(
    Led.L(mach, d),
    a => b => Led.Later(~mach, ~d, a, b),
    List<&2, U32>,
    l => Line.get(~mach, ~d, ~kern, l, c, key)
  )

# a step gives each of its requests an outcome: after a run, the log holds an
# outcome of the ID of each request of the step
law Step.run_outs:
  for ~mach: Machine()
  for ~d: Led(mach)
  for ~kern: Kernel(mach, d)
  for l: Led.L(mach, d)
  for c: Ledgers.Line
  for t: Tip
  for qs: List<&2, Hashes.Hash>
  for r: Run<Led.L(mach, d)>
  for a: Hashes.Hash
  for i: Ledgers.Id
  for time: String
  for q: Machine.Q(mach)
  {Step.run(~mach, ~d, ~kern, l, c, t, qs) == Some{r}: Maybe<&2, Run<Led.L(mach, d)>>}
    -> {List.contains(~Hashes.Hash, ~Hashes.Hash.is_eq, qs, a) == True{}: Bool}
    -> {
      Led.get(~mach, ~d, l, Ledgers.Name.Ask{a}) == Some{Ledgers.Entry.Ask{i, time, q}}: Maybe<&2, Entry(mach)>
    }
    -> {
      Maybe.is_some(
        &2,
        Out,
        Tip.out(~mach, ~d, Run.ledger(Led.L(mach, d), r), Run.tip(Led.L(mach, d), r), i)
      )
        == True{}: Bool
    }
