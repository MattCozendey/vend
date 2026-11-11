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

# the value m, if any, is x, as same says
def Safe.of_is(~B: Data, ~same: B -> B -> Bool, m: Maybe<&2, B>, +x: B) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{y}:
      same(y, x)

# each ballot of bs that holds a value, as of reads it, holds x
def Safe.all_of(
  ~B: Data,
  ~same: B -> B -> Bool,
  ~of: Ledgers.Ballot -> Maybe<&2, B>,
  bs: List<&2, Ledgers.Ballot>,
  +x: B
) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case Con{e, r}:
      List.all.if(u => Safe.all_of(~B, ~same, ~of, r, x), Safe.of_is(~B, ~same, of(e), x))

# the cell m holds nothing, or only x
def Safe.most(~B: Data, ~same: B -> B -> Bool, m: Maybe<&2, Cells.Cell<B>>, +x: B) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{Cells.One{y}}:
      same(y, x)
    case Some{Cells.Many{}}:
      False{}

# the cell of one value holds only x when the value is x
def Safe.most_one(~B: Data, ~same: B -> B -> Bool, m: Maybe<&2, B>, +x: B) -> {
  Safe.most(~B, ~same, Maybe.bind(&2, B, Cells.Cell<B>, m, y => Some{Cells.One{y}}), x)
    == Safe.of_is(~B, ~same, m, x): Bool
}:
  match m:
    case None{}:
      {==}
    case Some{y}:
      {==}

# two cells that hold only x join to a cell that holds only x
def Safe.most_join(
  ~B: Data,
  ~same: B -> B -> Bool,
  ~sl: Shared.Eq.Laws(B, same),
  p: Maybe<&2, Cells.Cell<B>>,
  q: Maybe<&2, Cells.Cell<B>>,
  +x: B
) -> {Safe.most(~B, ~same, p, x) == True{}: Bool}
  -> {Safe.most(~B, ~same, q, x) == True{}: Bool}
  -> {
    Safe.most(~B, ~same, Shared.Maybe.join(~Cells.Cell<B>, ~Cells.Cell.join(~B, ~same), p, q), x) == True{}: Bool
  }:
  match p q:
    case None{} y:
      hp => hq => hq
    case Some{c} None{}:
      hp => hq => hp
    case Some{Cells.One{+y1}} Some{Cells.One{+y2}}:
      +hp => hq =>
        %Equal.trans(
          B,
          y1,
          x,
          y2,
          Shared.Eq.sound(~B, ~same, sl, y1, x)(hp),
          Equal.sym(B, y2, x, Shared.Eq.sound(~B, ~same, sl, y2, x)(hq))
        ): {
          Safe.most(~B, ~same, Some{Bool.pick(Cells.Cell<B>, same(y1, _), Cells.One{y1}, Cells.Many{})}, x) == True{}: Bool
        }
        %Equal.sym(Bool, same(y1, y1), True{}, Shared.Eq.refl(~B, ~same, sl, y1)): {
          Safe.most(~B, ~same, Some{Bool.pick(Cells.Cell<B>, _, Cells.One{y1}, Cells.Many{})}, x) == True{}: Bool
        }
        hp
    case Some{Cells.One{y1}} Some{Cells.Many{}}:
      hp => hq => Empty.absurd(
        {
          Safe.most(
            ~B,
            ~same,
            Shared.Maybe.join(~Cells.Cell<B>, ~Cells.Cell.join(~B, ~same), Some{Cells.One{y1}}, Some{Cells.Many{}}),
            x
          )
            == True{}: Bool
        },
        Shared.Bool.false_ne_true(hq)
      )
    case Some{Cells.Many{}} Some{c}:
      hp => hq => Empty.absurd(
        {
          Safe.most(
            ~B,
            ~same,
            Shared.Maybe.join(~Cells.Cell<B>, ~Cells.Cell.join(~B, ~same), Some{Cells.Many{}}, Some{c}),
            x
          )
            == True{}: Bool
        },
        Shared.Bool.false_ne_true(hp)
      )

# ballots that each hold only x make a cell that holds only x
def Safe.cell_most(
  ~B: Data,
  ~same: B -> B -> Bool,
  ~sl: Shared.Eq.Laws(B, same),
  ~of: Ledgers.Ballot -> Maybe<&2, B>,
  bs: List<&2, Ledgers.Ballot>,
  +x: B
) -> {Safe.all_of(~B, ~same, ~of, bs, x) == True{}: Bool}
  -> {Safe.most(~B, ~same, Ledgers.Ballots.cell(~B, ~same, ~of, bs), x) == True{}: Bool}:
  match bs:
    case Nil{}:
      h => {==}
    case Con{+e, +r}:
      +h => Safe.most_join(
        ~B,
        ~same,
        ~sl,
        Maybe.bind(&2, B, Cells.Cell<B>, of(e), y => Some{Cells.One{y}}),
        Ledgers.Ballots.cell(~B, ~same, ~of, r),
        x
      )(
        Equal.trans(
          Bool,
          Safe.most(~B, ~same, Maybe.bind(&2, B, Cells.Cell<B>, of(e), y => Some{Cells.One{y}}), x),
          Safe.of_is(~B, ~same, of(e), x),
          True{},
          Safe.most_one(~B, ~same, of(e), x),
          Shared.List.all.if_hit(Safe.of_is(~B, ~same, of(e), x), u => Safe.all_of(~B, ~same, ~of, r, x))(h)
        )
      )(
        Safe.cell_most(
          ~B,
          ~same,
          ~sl,
          ~of,
          r,
          x
        )(Shared.List.all.if_rest(Safe.of_is(~B, ~same, of(e), x), u => Safe.all_of(~B, ~same, ~of, r, x))(h))
      )

# a join with a cell on the left holds a cell
def Safe.join_some_left(~B: Data, ~same: B -> B -> Bool, p: Cells.Cell<B>, q: Maybe<&2, Cells.Cell<B>>) -> {
  Maybe.is_some(
    &2,
    Cells.Cell<B>,
    Shared.Maybe.join(~Cells.Cell<B>, ~Cells.Cell.join(~B, ~same), Some{p}, q)
  )
    == True{}: Bool
}:
  match q:
    case None{}:
      {==}
    case Some{y}:
      {==}

# a join with a cell on the right holds a cell
def Safe.join_some_right(~B: Data, ~same: B -> B -> Bool, p: Maybe<&2, Cells.Cell<B>>, q: Maybe<&2, Cells.Cell<B>>) -> {
  Maybe.is_some(&2, Cells.Cell<B>, q) == True{}: Bool
} -> {
  Maybe.is_some(&2, Cells.Cell<B>, Shared.Maybe.join(~Cells.Cell<B>, ~Cells.Cell.join(~B, ~same), p, q))
    == True{}: Bool
}:
  match p q:
    case None{} y:
      h => h
    case Some{x} None{}:
      h => {==}
    case Some{x} Some{y}:
      h => {==}

# Safe.cell_some once it is known whether the first ballot is e0 (hb)
def Safe.cell_some.at(
  ~B: Data,
  ~same: B -> B -> Bool,
  ~of: Ledgers.Ballot -> Maybe<&2, B>,
  +h: Ledgers.Ballot,
  +t: List<&2, Ledgers.Ballot>,
  +e0: Ledgers.Ballot,
  +x: B,
  +hb: Bool,
  eb: {Ledgers.Ballot.is_eq(h, e0) == hb: Bool},
  ih: {List.contains(~Ledgers.Ballot, ~Ledgers.Ballot.is_eq, t, e0) == True{}: Bool}
    -> {Maybe.is_some(&2, Cells.Cell<B>, Ledgers.Ballots.cell(~B, ~same, ~of, t)) == True{}: Bool}
) -> {List.any.if(u => List.contains(~Ledgers.Ballot, ~Ledgers.Ballot.is_eq, t, e0), hb) == True{}: Bool}
  -> {of(e0) == Some{x}: Maybe<&2, B>}
  -> {
    Maybe.is_some(
      &2,
      Cells.Cell<B>,
      Shared.Maybe.join(
        ~Cells.Cell<B>,
        ~Cells.Cell.join(~B, ~same),
        Maybe.bind(&2, B, Cells.Cell<B>, of(h), y => Some{Cells.One{y}}),
        Ledgers.Ballots.cell(~B, ~same, ~of, t)
      )
    )
      == True{}: Bool
  }:
  match hb:
    case True{}:
      hc => hx =>
        %Equal.sym(Ledgers.Ballot, h, e0, Ledgers.Ballot.is_eq_sound(h, e0)(eb)): {
          Maybe.is_some(
            &2,
            Cells.Cell<B>,
            Shared.Maybe.join(
              ~Cells.Cell<B>,
              ~Cells.Cell.join(~B, ~same),
              Maybe.bind(&2, B, Cells.Cell<B>, of(_), y => Some{Cells.One{y}}),
              Ledgers.Ballots.cell(~B, ~same, ~of, t)
            )
          )
            == True{}: Bool
        }
        %Equal.sym(Maybe<&2, B>, of(e0), Some{x}, hx): {
          Maybe.is_some(
            &2,
            Cells.Cell<B>,
            Shared.Maybe.join(
              ~Cells.Cell<B>,
              ~Cells.Cell.join(~B, ~same),
              Maybe.bind(&2, B, Cells.Cell<B>, _, y => Some{Cells.One{y}}),
              Ledgers.Ballots.cell(~B, ~same, ~of, t)
            )
          )
            == True{}: Bool
        }
        Safe.join_some_left(~B, ~same, Cells.One{x}, Ledgers.Ballots.cell(~B, ~same, ~of, t))
    case False{}:
      hc => hx => Safe.join_some_right(
        ~B,
        ~same,
        Maybe.bind(&2, B, Cells.Cell<B>, of(h), y => Some{Cells.One{y}}),
        Ledgers.Ballots.cell(~B, ~same, ~of, t)
      )(ih(hc))

# ballots of which one holds a value make a cell
def Safe.cell_some(
  ~B: Data,
  ~same: B -> B -> Bool,
  ~of: Ledgers.Ballot -> Maybe<&2, B>,
  bs: List<&2, Ledgers.Ballot>,
  +e0: Ledgers.Ballot,
  +x: B
) -> {List.contains(~Ledgers.Ballot, ~Ledgers.Ballot.is_eq, bs, e0) == True{}: Bool}
  -> {of(e0) == Some{x}: Maybe<&2, B>}
  -> {Maybe.is_some(&2, Cells.Cell<B>, Ledgers.Ballots.cell(~B, ~same, ~of, bs)) == True{}: Bool}:
  match bs:
    case Nil{}:
      hc => hx => Empty.absurd(
        {Maybe.is_some(&2, Cells.Cell<B>, Ledgers.Ballots.cell(~B, ~same, ~of, [])) == True{}: Bool},
        Shared.Bool.false_ne_true(hc)
      )
    case Con{+h, +t}:
      hc => +hx => Safe.cell_some.at(
        ~B,
        ~same,
        ~of,
        h,
        t,
        e0,
        x,
        Ledgers.Ballot.is_eq(h, e0),
        {==},
        c => Safe.cell_some(~B, ~same, ~of, t, e0, x)(c)(hx)
      )(hc)(hx)

# a cell that holds only x, and holds a cell, holds x
def Safe.most_some(
  ~B: Data,
  ~same: B -> B -> Bool,
  ~sl: Shared.Eq.Laws(B, same),
  m: Maybe<&2, Cells.Cell<B>>,
  +x: B
) -> {Safe.most(~B, ~same, m, x) == True{}: Bool}
  -> {Maybe.is_some(&2, Cells.Cell<B>, m) == True{}: Bool}
  -> {m == Some{Cells.One{x}}: Maybe<&2, Cells.Cell<B>>}:
  match m:
    case None{}:
      h1 => h2 => Empty.absurd(
        {None{} == Some{Cells.One{x}}: Maybe<&2, Cells.Cell<B>>},
        Shared.Bool.false_ne_true(h2)
      )
    case Some{Cells.One{+y}}:
      h1 => h2 =>
        %Shared.Eq.sound(~B, ~same, sl, y, x)(h1): {Some{Cells.One{y}} == Some{Cells.One{_}}: Maybe<&2, Cells.Cell<B>>}
        {==}
    case Some{Cells.Many{}}:
      h1 => h2 => Empty.absurd(
        {Some{Cells.Many{}} == Some{Cells.One{x}}: Maybe<&2, Cells.Cell<B>>},
        Shared.Bool.false_ne_true(h1)
      )

# a ballot heads a list that it starts
def Safe.contains_head(+h: Ledgers.Ballot, t: List<&2, Ledgers.Ballot>) -> {
  List.contains(~Ledgers.Ballot, ~Ledgers.Ballot.is_eq, h <> t, h) == True{}: Bool
}:
  %Equal.sym(Bool, Ledgers.Ballot.is_eq(h, h), True{}, Ledgers.Ballot.is_eq_refl(h)): {
    List.any.if(u => List.contains(~Ledgers.Ballot, ~Ledgers.Ballot.is_eq, t, h), _) == True{}: Bool
  }
  {==}

# a ballot of a list that holds a value, as of reads it
def Safe.Wit(~B: Data, ~of: Ledgers.Ballot -> Maybe<&2, B>, bs: List<&2, Ledgers.Ballot>) -> Type:
  Exists(
    Ledgers.Ballot,
    e => {List.contains(~Ledgers.Ballot, ~Ledgers.Ballot.is_eq, bs, e) == True{}: Bool}
      & Exists(B, y => {of(e) == Some{y}: Maybe<&2, B>})
  )

# a ballot of the tail is a ballot of the list
def Safe.wit_cons(~B: Data, ~of: Ledgers.Ballot -> Maybe<&2, B>, h: Ledgers.Ballot, t: List<&2, Ledgers.Ballot>, w: Safe.Wit(~B, ~of, t)) -> Safe.Wit(
  ~B,
  ~of,
  h <> t
):
  match w:
    case Tuple{+e, Tuple{c, r}}:
      Tuple{e, Tuple{Shared.List.contains_cons(~Ledgers.Ballot, ~Ledgers.Ballot.is_eq, h, t, e)(c), r}}

# Safe.witness once the value m of the first ballot is known
def Safe.witness.at(
  ~B: Data,
  ~same: B -> B -> Bool,
  ~of: Ledgers.Ballot -> Maybe<&2, B>,
  +h: Ledgers.Ballot,
  t: List<&2, Ledgers.Ballot>,
  -c: Cells.Cell<B>,
  m: Maybe<&2, B>,
  em: {of(h) == m: Maybe<&2, B>},
  ih: {Ledgers.Ballots.cell(~B, ~same, ~of, t) == Some{c}: Maybe<&2, Cells.Cell<B>>} -> Safe.Wit(~B, ~of, t)
) -> {
  Shared.Maybe.join(
    ~Cells.Cell<B>,
    ~Cells.Cell.join(~B, ~same),
    Maybe.bind(&2, B, Cells.Cell<B>, m, y => Some{Cells.One{y}}),
    Ledgers.Ballots.cell(~B, ~same, ~of, t)
  )
    == Some{c}: Maybe<&2, Cells.Cell<B>>
} -> Safe.Wit(~B, ~of, h <> t):
  match m:
    case Some{y}:
      e => Tuple{h, Tuple{Safe.contains_head(h, t), Tuple{y, em}}}
    case None{}:
      e => Safe.wit_cons(~B, ~of, h, t, ih(e))

# a cell that holds something has a ballot that holds a value
def Safe.witness(
  ~B: Data,
  ~same: B -> B -> Bool,
  ~of: Ledgers.Ballot -> Maybe<&2, B>,
  bs: List<&2, Ledgers.Ballot>,
  -c: Cells.Cell<B>
) -> {Ledgers.Ballots.cell(~B, ~same, ~of, bs) == Some{c}: Maybe<&2, Cells.Cell<B>>} -> Safe.Wit(~B, ~of, bs):
  match bs:
    case Nil{}:
      e => Empty.absurd(Safe.Wit(~B, ~of, []), Shared.Maybe.none_ne_some(Cells.Cell<B>, c, e))
    case Con{+h, +t}:
      Safe.witness.at(
        ~B,
        ~same,
        ~of,
        h,
        t,
        c,
        of(h),
        {==},
        Safe.witness(~B, ~same, ~of, t, c)
      )

# two lines that Line.is_eq calls the same are the same
def Safe.line_sound(a: Ledgers.Line, b: Ledgers.Line) -> {Ledgers.Line.is_eq(a, b) == True{}: Bool} -> {a == b: Ledgers.Line}:
  match a b:
    case Ledgers.Line{+i1, +k1} Ledgers.Line{+i2, +k2}:
      +h => Ledgers.Eq.both(
        Hashes.Hash,
        Maybe<&2, String>,
        Ledgers.Line,
        x => y => Ledgers.Line{x, y},
        i1,
        i2,
        k1,
        k2,
        Hashes.Hash.is_eq_sound(
          i1,
          i2
        )(Shared.List.all.if_hit(Hashes.Hash.is_eq(i1, i2), u => Ledgers.Sub.is_eq(k1, k2))(h)),
        Shared.Maybe.is_eq_sound(
          ~String,
          ~String.eq,
          x => y => Texts.String.eq_sound(x, y),
          k1,
          k2
        )(Shared.List.all.if_rest(Hashes.Hash.is_eq(i1, i2), u => Ledgers.Sub.is_eq(k1, k2))(h))
      )

# two places that Place.is_eq calls the same are the same
def Safe.place_sound(a: Ledgers.Place, b: Ledgers.Place) -> {Ledgers.Place.is_eq(a, b) == True{}: Bool} -> {a == b: Ledgers.Place}:
  match a b:
    case Ledgers.Place{+c1, +h1, +r1} Ledgers.Place{+c2, +h2, +r2}:
      +h =>
        +x = Shared.List.all.if_rest(
          Ledgers.Line.is_eq(c1, c2),
          u => List.all.if(u2 => Nat.is_eq(r1, r2), U32.is_eq(h1, h2))
        )(h)
        Ledgers.Eq.three(
          Ledgers.Line,
          U32,
          Nat,
          Ledgers.Place,
          x => y => z => Ledgers.Place{x, y, z},
          c1,
          c2,
          h1,
          h2,
          r1,
          r2,
          Safe.line_sound(
            c1,
            c2
          )(
            Shared.List.all.if_hit(
              Ledgers.Line.is_eq(c1, c2),
              u => List.all.if(u2 => Nat.is_eq(r1, r2), U32.is_eq(h1, h2))
            )(h)
          ),
          Shared.U32.is_eq_sound(h1, h2)(Shared.List.all.if_hit(U32.is_eq(h1, h2), u2 => Nat.is_eq(r1, r2))(x)),
          Shared.Nat.is_eq_sound(r1, r2)(Shared.List.all.if_rest(U32.is_eq(h1, h2), u2 => Nat.is_eq(r1, r2))(x))
        )

# a ballot at the place w is at w
def Safe.at_of(e: Ledgers.Ballot, +w: Ledgers.Place, +voter: String) -> {
  Ledgers.Ballot.is_at(e, w, voter) == True{}: Bool
} -> {Ledgers.Ballot.at(e) == w: Ledgers.Place}:
  match e:
    case Ledgers.Ballot{Ledgers.Signed{+w2, +n, a}, l}:
      h => Safe.place_sound(w2, w)(Shared.List.all.if_hit(Ledgers.Place.is_eq(w2, w), u => String.eq(n, voter))(h))

# a ballot of the voter is of the voter
def Safe.voter_of(e: Ledgers.Ballot, +w: Ledgers.Place, +voter: String) -> {
  Ledgers.Ballot.is_at(e, w, voter) == True{}: Bool
} -> {Ledgers.Ballot.voter(e) == voter: String}:
  match e:
    case Ledgers.Ballot{Ledgers.Signed{+w2, +n, a}, l}:
      h => Texts.String.eq_sound(n, voter)(Shared.List.all.if_rest(Ledgers.Place.is_eq(w2, w), u => String.eq(n, voter))(h))

# the law of the ballots of a voter, of the laws ls
def Safe.laws.ballots(
  -Q: Data,
  -c: Codes.Codec(Q),
  -k: Ledgers.Ledger.Kind(Q),
  ls: Ledgers.Ledger.Laws(Q, c, k)
) -> Ledgers.Laws.Ballots(Q, c, k):
  match ls:
    case Tuple{e, Tuple{a, Tuple{n, Tuple{cm, Tuple{tw, Tuple{m, Tuple{bl, r}}}}}}}:
      bl

# the law of the bound of rounds, of the laws ls
def Safe.laws.rounds(
  -Q: Data,
  -c: Codes.Codec(Q),
  -k: Ledgers.Ledger.Kind(Q),
  ls: Ledgers.Ledger.Laws(Q, c, k)
) -> Ledgers.Laws.Rounds(Q, c, k):
  match ls:
    case Tuple{e, Tuple{a, Tuple{n, Tuple{cm, Tuple{tw, Tuple{m, Tuple{bl, Tuple{rd, r}}}}}}}}:
      rd

# the law of the ballots of a voter, of the ledger d
def Safe.ballots_law(-mach: Machine(), d: Led(mach)) -> Ledgers.Laws.Ballots(
  Machine.Q(mach),
  Machine.code(mach),
  Led.kind(mach, d)
):
  Safe.laws.ballots(Machine.Q(mach), Machine.code(mach), Led.kind(mach, d), Hist.laws(mach, d))

# the law of the bound of rounds, of the ledger d
def Safe.rounds_law(-mach: Machine(), d: Led(mach)) -> Ledgers.Laws.Rounds(
  Machine.Q(mach),
  Machine.code(mach),
  Led.kind(mach, d)
):
  Safe.laws.rounds(Machine.Q(mach), Machine.code(mach), Led.kind(mach, d), Hist.laws(mach, d))

# a read that holds y stays so when its value is kept
def Safe.is_eq_kept(
  ~A: Data,
  ~eq: A -> A -> Bool,
  m: Maybe<&2, A>,
  -m2: Maybe<&2, A>,
  -y: A,
  hm: @x: A -> {m == Some{x}: Maybe<&2, A>} -> {m2 == Some{x}: Maybe<&2, A>}
) -> {Shared.Maybe.is_eq(~A, ~eq, m, Some{y}) == True{}: Bool}
  -> {Shared.Maybe.is_eq(~A, ~eq, m2, Some{y}) == True{}: Bool}:
  match m:
    case None{}:
      h => Empty.absurd({Shared.Maybe.is_eq(~A, ~eq, m2, Some{y}) == True{}: Bool}, Shared.Bool.false_ne_true(h))
    case Some{x}:
      h =>
        %Equal.sym(Maybe<&2, A>, m2, Some{x}, hm(x)({==})): {
          Shared.Maybe.is_eq(~A, ~eq, _, Some{y}) == True{}: Bool
        }
        h

# what a ledger holds, a later ledger holds
def Safe.has_grows(
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
  +e: Entry(mach)
) -> {Led.has(~mach, ~d, a, e) == True{}: Bool} -> {Led.has(~mach, ~d, b, e) == True{}: Bool}:
  Safe.is_eq_kept(
    ~Entry(mach),
    ~Ledgers.Entry.same(~Machine.Q(mach), ~Machine.code(mach)),
    Ledgers.Kind.get(Machine.Q(mach), Led.kind(mach, d))(a)(Entry.name(~mach, e)),
    Ledgers.Kind.get(Machine.Q(mach), Led.kind(mach, d))(b)(Entry.name(~mach, e)),
    e,
    x => lg(a)(b)(later)(Entry.name(~mach, e))(x)
  )

# a ballot of a voter at a place in a ledger is one in a later ledger
def Safe.in_b(
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
  +w: Ledgers.Place,
  +voter: String,
  +e: Ledgers.Ballot
) -> {
  List.contains(
    ~Ledgers.Ballot,
    ~Ledgers.Ballot.is_eq,
    Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(a)(w)(voter),
    e
  )
    == True{}: Bool
} -> {
  List.contains(
    ~Ledgers.Ballot,
    ~Ledgers.Ballot.is_eq,
    Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(b)(w)(voter),
    e
  )
    == True{}: Bool
}:
  +h =>
    +x = Equal.trans(
      Bool,
      Bool.and(
        Led.has(~mach, ~d, a, Ledgers.Entry.Ballot{e}),
        Ledgers.Ballot.is_at(e, w, voter)
      ),
      List.contains(
        ~Ledgers.Ballot,
        ~Ledgers.Ballot.is_eq,
        Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(a)(w)(voter),
        e
      ),
      True{},
      Equal.sym(
        Bool,
        List.contains(
          ~Ledgers.Ballot,
          ~Ledgers.Ballot.is_eq,
          Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(a)(w)(voter),
          e
        ),
        Bool.and(
          Led.has(~mach, ~d, a, Ledgers.Entry.Ballot{e}),
          Ledgers.Ballot.is_at(e, w, voter)
        ),
        Safe.ballots_law(mach, d)(a)(w)(voter)(e)
      ),
      h
    )
    Equal.trans(
      Bool,
      List.contains(
        ~Ledgers.Ballot,
        ~Ledgers.Ballot.is_eq,
        Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(b)(w)(voter),
        e
      ),
      Bool.and(
        Led.has(~mach, ~d, b, Ledgers.Entry.Ballot{e}),
        Ledgers.Ballot.is_at(e, w, voter)
      ),
      True{},
      Safe.ballots_law(mach, d)(b)(w)(voter)(e),
      Shared.Bool.and_both(
        Led.has(~mach, ~d, b, Ledgers.Entry.Ballot{e}),
        Ledgers.Ballot.is_at(e, w, voter)
      )(
        Safe.has_grows(
          ~mach,
          ~d,
          ~lg,
          a,
          b,
          later,
          Ledgers.Entry.Ballot{e}
        )(
          Shared.Bool.and_true_left(
            Led.has(~mach, ~d, a, Ledgers.Entry.Ballot{e}),
            Ledgers.Ballot.is_at(e, w, voter)
          )(x)
        )
      )(
        Shared.Bool.and_true_right(
          Led.has(~mach, ~d, a, Ledgers.Entry.Ballot{e}),
          Ledgers.Ballot.is_at(e, w, voter)
        )(x)
      )
    )

# a ballot of a voter at a place: the ledger holds it, and it is at the place
def Safe.held(
  ~mach: Machine(),
  ~d: Led(mach),
  +l: Led.L(mach, d),
  +w: Ledgers.Place,
  +voter: String,
  +e: Ledgers.Ballot
) -> {
  List.contains(
    ~Ledgers.Ballot,
    ~Ledgers.Ballot.is_eq,
    Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(l)(w)(voter),
    e
  )
    == True{}: Bool
} -> {Bool.and(Led.has(~mach, ~d, l, Ledgers.Entry.Ballot{e}), Ledgers.Ballot.is_at(e, w, voter)) == True{}: Bool}:
  h => Equal.trans(
    Bool,
    Bool.and(Led.has(~mach, ~d, l, Ledgers.Entry.Ballot{e}), Ledgers.Ballot.is_at(e, w, voter)),
    List.contains(
      ~Ledgers.Ballot,
      ~Ledgers.Ballot.is_eq,
      Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(l)(w)(voter),
      e
    ),
    True{},
    Equal.sym(
      Bool,
      List.contains(
        ~Ledgers.Ballot,
        ~Ledgers.Ballot.is_eq,
        Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(l)(w)(voter),
        e
      ),
      Bool.and(Led.has(~mach, ~d, l, Ledgers.Entry.Ballot{e}), Ledgers.Ballot.is_at(e, w, voter)),
      Safe.ballots_law(mach, d)(l)(w)(voter)(e)
    ),
    h
  )

# Safe.of_in_b once the value m of the ballot e is known
def Safe.of_in_b.at(
  ~mach: Machine(),
  ~d: Led(mach),
  ~B: Data,
  ~same: B -> B -> Bool,
  ~sl: Shared.Eq.Laws(B, same),
  ~of: Ledgers.Ballot -> Maybe<&2, B>,
  ~kd: Bool,
  ~ofc: @e1: Ledgers.Ballot -> @e2: Ledgers.Ballot -> {
    Ledgers.Ballot.cast(e1) == Ledgers.Ballot.cast(e2): Ledgers.Cast
  } -> {of(e1) == of(e2): Maybe<&2, B>},
  ~ofk: @e1: Ledgers.Ballot -> @y: B -> {of(e1) == Some{y}: Maybe<&2, B>} -> {
    Cast.is_vote(Ledgers.Ballot.cast(e1)) == kd: Bool
  },
  -b: Led.L(mach, d),
  +e0: Ledgers.Ballot,
  +e: Ledgers.Ballot,
  +x: B,
  m: Maybe<&2, B>,
  +em: {of(e) == m: Maybe<&2, B>},
  +hx: {of(e0) == Some{x}: Maybe<&2, B>},
  h0: {Led.has(~mach, ~d, b, Ledgers.Entry.Ballot{e0}) == True{}: Bool},
  h1: {Led.has(~mach, ~d, b, Ledgers.Entry.Ballot{e}) == True{}: Bool},
  hat: {Ledgers.Ballot.is_at(e, Ledgers.Ballot.at(e0), Ledgers.Ballot.voter(e0)) == True{}: Bool},
  sg: Led.Single(mach, d, b)
) -> {Safe.of_is(~B, ~same, m, x) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{+y}:
      +ce = sg(e0)(e)(h0)(h1)(hat)(
        Equal.trans(
          Bool,
          Cast.is_vote(Ledgers.Ballot.cast(e0)),
          kd,
          Cast.is_vote(Ledgers.Ballot.cast(e)),
          ofk(e0)(x)(hx),
          Equal.sym(Bool, Cast.is_vote(Ledgers.Ballot.cast(e)), kd, ofk(e)(y)(em))
        )
      )
      %Shared.Maybe.some_inj(
        B,
        x,
        y,
        Equal.trans(
          Maybe<&2, B>,
          Some{x},
          of(e0),
          Some{y},
          Equal.sym(Maybe<&2, B>, of(e0), Some{x}, hx),
          Equal.trans(Maybe<&2, B>, of(e0), of(e), Some{y}, ofc(e0)(e)(ce), em)
        )
      ): {same(_, x) == True{}: Bool}
      Shared.Eq.refl(~B, ~same, sl, x)

# each ballot of a voter at a place holds what one of them holds, in an honest
# ledger
def Safe.of_in_b(
  ~mach: Machine(),
  ~d: Led(mach),
  ~ls: Hist.LaterSingle(mach, d),
  ~B: Data,
  ~same: B -> B -> Bool,
  ~sl: Shared.Eq.Laws(B, same),
  ~of: Ledgers.Ballot -> Maybe<&2, B>,
  ~kd: Bool,
  ~ofc: @e1: Ledgers.Ballot -> @e2: Ledgers.Ballot -> {
    Ledgers.Ballot.cast(e1) == Ledgers.Ballot.cast(e2): Ledgers.Cast
  } -> {of(e1) == of(e2): Maybe<&2, B>},
  ~ofk: @e1: Ledgers.Ballot -> @y: B -> {of(e1) == Some{y}: Maybe<&2, B>} -> {
    Cast.is_vote(Ledgers.Ballot.cast(e1)) == kd: Bool
  },
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  +later: {
    Bool.and(
      Ledgers.Kind.grows(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), a, b),
      Led.honest(~mach, ~d, b)
    )
      == True{}: Bool
  },
  +w: Ledgers.Place,
  +voter: String,
  +e0: Ledgers.Ballot,
  +x: B,
  +e: Ledgers.Ballot
) -> {
  List.contains(
    ~Ledgers.Ballot,
    ~Ledgers.Ballot.is_eq,
    Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(b)(w)(voter),
    e0
  )
    == True{}: Bool
} -> {of(e0) == Some{x}: Maybe<&2, B>} -> {
  List.contains(
    ~Ledgers.Ballot,
    ~Ledgers.Ballot.is_eq,
    Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(b)(w)(voter),
    e
  )
    == True{}: Bool
} -> {Safe.of_is(~B, ~same, of(e), x) == True{}: Bool}:
  hc0 => +hx => hc =>
    +k0 = Safe.held(~mach, ~d, b, w, voter, e0)(hc0)
    +k1 = Safe.held(~mach, ~d, b, w, voter, e)(hc)
    +i0 = Shared.Bool.and_true_right(Led.has(~mach, ~d, b, Ledgers.Entry.Ballot{e0}), Ledgers.Ballot.is_at(e0, w, voter))(k0)
    Safe.of_in_b.at(
      ~mach,
      ~d,
      ~B,
      ~same,
      ~sl,
      ~of,
      ~kd,
      ~ofc,
      ~ofk,
      b,
      e0,
      e,
      x,
      of(e),
      {==},
      hx,
      Shared.Bool.and_true_left(Led.has(~mach, ~d, b, Ledgers.Entry.Ballot{e0}), Ledgers.Ballot.is_at(e0, w, voter))(k0),
      Shared.Bool.and_true_left(Led.has(~mach, ~d, b, Ledgers.Entry.Ballot{e}), Ledgers.Ballot.is_at(e, w, voter))(k1),
      %Equal.sym(Ledgers.Place, Ledgers.Ballot.at(e0), w, Safe.at_of(e0, w, voter)(i0)): {
        Ledgers.Ballot.is_at(e, _, Ledgers.Ballot.voter(e0)) == True{}: Bool
      }
      %Equal.sym(String, Ledgers.Ballot.voter(e0), voter, Safe.voter_of(e0, w, voter)(i0)): {
        Ledgers.Ballot.is_at(e, w, _) == True{}: Bool
      }
      Shared.Bool.and_true_right(Led.has(~mach, ~d, b, Ledgers.Entry.Ballot{e}), Ledgers.Ballot.is_at(e, w, voter))(k1),
      ls(a)(b)(later)
    )

# a list within ks is within ks with one more element
def Safe.within_cons(~A: Data, ~same: A -> A -> Bool, ps: List<&2, A>, +k: A, +ks: List<&2, A>) -> {
  Shared.List.within(~A, ~same, ps, ks) == True{}: Bool
} -> {Shared.List.within(~A, ~same, ps, k <> ks) == True{}: Bool}:
  match ps:
    case Nil{}:
      h => {==}
    case Con{+p, +r}:
      +h => Shared.Bool.and_both(
        List.contains(~A, ~same, k <> ks, p),
        Shared.List.within(~A, ~same, r, k <> ks)
      )(
        Shared.List.contains_cons(~A, ~same, k, ks, p)(
          Shared.Bool.and_true_left(List.contains(~A, ~same, ks, p), Shared.List.within(~A, ~same, r, ks))(h)
        )
      )(
        Safe.within_cons(~A, ~same, r, k, ks)(
          Shared.Bool.and_true_right(List.contains(~A, ~same, ks, p), Shared.List.within(~A, ~same, r, ks))(h)
        )
      )

# an element heads a list that it starts
def Safe.contains_self(~A: Data, ~same: A -> A -> Bool, ~laws: Shared.Eq.Laws(A, same), +x: A, r: List<&2, A>) -> {
  List.contains(~A, ~same, x <> r, x) == True{}: Bool
}:
  %Equal.sym(Bool, same(x, x), True{}, Shared.Eq.refl(~A, ~same, laws, x)): {
    List.any.if(u => List.contains(~A, ~same, r, x), _) == True{}: Bool
  }
  {==}

# a list is within itself
def Safe.within_refl(~A: Data, ~same: A -> A -> Bool, ~laws: Shared.Eq.Laws(A, same), xs: List<&2, A>) -> {
  Shared.List.within(~A, ~same, xs, xs) == True{}: Bool
}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      Shared.Bool.and_both(
        List.contains(~A, ~same, x <> r, x),
        Shared.List.within(~A, ~same, r, x <> r)
      )(Safe.contains_self(~A, ~same, ~laws, x, r))(
        Safe.within_cons(~A, ~same, r, x, r)(Safe.within_refl(~A, ~same, ~laws, r))
      )

# the ballots of a voter at a place, in a later ledger, each hold what one of
# them holds
def Safe.all_in_b(
  ~mach: Machine(),
  ~d: Led(mach),
  ~ls: Hist.LaterSingle(mach, d),
  ~B: Data,
  ~same: B -> B -> Bool,
  ~sl: Shared.Eq.Laws(B, same),
  ~of: Ledgers.Ballot -> Maybe<&2, B>,
  ~kd: Bool,
  ~ofc: @e1: Ledgers.Ballot -> @e2: Ledgers.Ballot -> {
    Ledgers.Ballot.cast(e1) == Ledgers.Ballot.cast(e2): Ledgers.Cast
  } -> {of(e1) == of(e2): Maybe<&2, B>},
  ~ofk: @e1: Ledgers.Ballot -> @y: B -> {of(e1) == Some{y}: Maybe<&2, B>} -> {
    Cast.is_vote(Ledgers.Ballot.cast(e1)) == kd: Bool
  },
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  +later: {
    Bool.and(
      Ledgers.Kind.grows(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), a, b),
      Led.honest(~mach, ~d, b)
    )
      == True{}: Bool
  },
  +w: Ledgers.Place,
  +voter: String,
  +e0: Ledgers.Ballot,
  +x: B,
  sfx: List<&2, Ledgers.Ballot>
) -> {List.contains(~Ledgers.Ballot, ~Ledgers.Ballot.is_eq, Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(b)(w)(voter), e0) == True{}: Bool}
  -> {of(e0) == Some{x}: Maybe<&2, B>}
  -> {Shared.List.within(~Ledgers.Ballot, ~Ledgers.Ballot.is_eq, sfx, Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(b)(w)(voter)) == True{}: Bool}
  -> {Safe.all_of(~B, ~same, ~of, sfx, x) == True{}: Bool}:
  match sfx:
    case Nil{}:
      h0 => hx => h => {==}
    case Con{+e, +r}:
      +h0 => +hx => +h => Shared.List.all.if_both(
        Safe.of_is(~B, ~same, of(e), x),
        u => Safe.all_of(~B, ~same, ~of, r, x)
      )(
        Safe.of_in_b(~mach, ~d, ~ls, ~B, ~same, ~sl, ~of, ~kd, ~ofc, ~ofk, a, b, later, w, voter, e0, x, e)(h0)(hx)(
          Shared.Bool.and_true_left(List.contains(~Ledgers.Ballot, ~Ledgers.Ballot.is_eq, Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(b)(w)(voter), e), Shared.List.within(~Ledgers.Ballot, ~Ledgers.Ballot.is_eq, r, Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(b)(w)(voter)))(h)
        )
      )(
        Safe.all_in_b(~mach, ~d, ~ls, ~B, ~same, ~sl, ~of, ~kd, ~ofc, ~ofk, a, b, later, w, voter, e0, x, r)(h0)(hx)(
          Shared.Bool.and_true_right(List.contains(~Ledgers.Ballot, ~Ledgers.Ballot.is_eq, Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(b)(w)(voter), e), Shared.List.within(~Ledgers.Ballot, ~Ledgers.Ballot.is_eq, r, Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(b)(w)(voter)))(h)
        )
      )

# and so do those of the earlier ledger
def Safe.all_in_a(
  ~mach: Machine(),
  ~d: Led(mach),
  ~lg: Hist.LaterGrows(mach, d),
  ~ls: Hist.LaterSingle(mach, d),
  ~B: Data,
  ~same: B -> B -> Bool,
  ~sl: Shared.Eq.Laws(B, same),
  ~of: Ledgers.Ballot -> Maybe<&2, B>,
  ~kd: Bool,
  ~ofc: @e1: Ledgers.Ballot -> @e2: Ledgers.Ballot -> {
    Ledgers.Ballot.cast(e1) == Ledgers.Ballot.cast(e2): Ledgers.Cast
  } -> {of(e1) == of(e2): Maybe<&2, B>},
  ~ofk: @e1: Ledgers.Ballot -> @y: B -> {of(e1) == Some{y}: Maybe<&2, B>} -> {
    Cast.is_vote(Ledgers.Ballot.cast(e1)) == kd: Bool
  },
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  +later: {
    Bool.and(
      Ledgers.Kind.grows(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), a, b),
      Led.honest(~mach, ~d, b)
    )
      == True{}: Bool
  },
  +w: Ledgers.Place,
  +voter: String,
  +e0: Ledgers.Ballot,
  +x: B,
  sfx: List<&2, Ledgers.Ballot>
) -> {List.contains(~Ledgers.Ballot, ~Ledgers.Ballot.is_eq, Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(b)(w)(voter), e0) == True{}: Bool}
  -> {of(e0) == Some{x}: Maybe<&2, B>}
  -> {Shared.List.within(~Ledgers.Ballot, ~Ledgers.Ballot.is_eq, sfx, Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(a)(w)(voter)) == True{}: Bool}
  -> {Safe.all_of(~B, ~same, ~of, sfx, x) == True{}: Bool}:
  match sfx:
    case Nil{}:
      h0 => hx => h => {==}
    case Con{+e, +r}:
      +h0 => +hx => +h => Shared.List.all.if_both(
        Safe.of_is(~B, ~same, of(e), x),
        u => Safe.all_of(~B, ~same, ~of, r, x)
      )(
        Safe.of_in_b(~mach, ~d, ~ls, ~B, ~same, ~sl, ~of, ~kd, ~ofc, ~ofk, a, b, later, w, voter, e0, x, e)(h0)(hx)(
          Safe.in_b(~mach, ~d, ~lg, a, b, later, w, voter, e)(
            Shared.Bool.and_true_left(List.contains(~Ledgers.Ballot, ~Ledgers.Ballot.is_eq, Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(a)(w)(voter), e), Shared.List.within(~Ledgers.Ballot, ~Ledgers.Ballot.is_eq, r, Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(a)(w)(voter)))(h)
          )
        )
      )(
        Safe.all_in_a(~mach, ~d, ~lg, ~ls, ~B, ~same, ~sl, ~of, ~kd, ~ofc, ~ofk, a, b, later, w, voter, e0, x, r)(h0)(hx)(
          Shared.Bool.and_true_right(List.contains(~Ledgers.Ballot, ~Ledgers.Ballot.is_eq, Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(a)(w)(voter), e), Shared.List.within(~Ledgers.Ballot, ~Ledgers.Ballot.is_eq, r, Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(a)(w)(voter)))(h)
        )
      )

# what is some value holds something
def Safe.some_of(-A: Data, m: Maybe<&2, A>, -c: A) -> {m == Some{c}: Maybe<&2, A>} -> {Maybe.is_some(&2, A, m) == True{}: Bool}:
  match m:
    case None{}:
      e => Empty.absurd({False{} == True{}: Bool}, Shared.Maybe.none_ne_some(A, c, e))
    case Some{y}:
      e => {==}

# Safe.cell_kept from a ballot e0 of the earlier ledger, and its value
def Safe.cell_kept.of(
  ~mach: Machine(),
  ~d: Led(mach),
  ~lg: Hist.LaterGrows(mach, d),
  ~ls: Hist.LaterSingle(mach, d),
  ~B: Data,
  ~same: B -> B -> Bool,
  ~sl: Shared.Eq.Laws(B, same),
  ~of: Ledgers.Ballot -> Maybe<&2, B>,
  ~kd: Bool,
  ~ofc: @e1: Ledgers.Ballot -> @e2: Ledgers.Ballot -> {
    Ledgers.Ballot.cast(e1) == Ledgers.Ballot.cast(e2): Ledgers.Cast
  } -> {of(e1) == of(e2): Maybe<&2, B>},
  ~ofk: @e1: Ledgers.Ballot -> @y: B -> {of(e1) == Some{y}: Maybe<&2, B>} -> {
    Cast.is_vote(Ledgers.Ballot.cast(e1)) == kd: Bool
  },
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  +later: {
    Bool.and(
      Ledgers.Kind.grows(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), a, b),
      Led.honest(~mach, ~d, b)
    )
      == True{}: Bool
  },
  +w: Ledgers.Place,
  +voter: String,
  -c: Cells.Cell<B>,
  +h: {Ledgers.Ballots.cell(~B, ~same, ~of, Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(a)(w)(voter)) == Some{c}: Maybe<&2, Cells.Cell<B>>},
  +e0: Ledgers.Ballot,
  hc: {List.contains(~Ledgers.Ballot, ~Ledgers.Ballot.is_eq, Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(a)(w)(voter), e0) == True{}: Bool},
  q: Exists(B, y => {of(e0) == Some{y}: Maybe<&2, B>})
) -> {Ledgers.Ballots.cell(~B, ~same, ~of, Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(b)(w)(voter)) == Some{c}: Maybe<&2, Cells.Cell<B>>}:
  match q:
    case Tuple{+x, hx1}:
      +hx = {hx1 : {of(e0) == Some{x}: Maybe<&2, B>}}
      +hcb = Safe.in_b(~mach, ~d, ~lg, a, b, later, w, voter, e0)(hc)
      +caA = Safe.most_some(~B, ~same, ~sl, Ledgers.Ballots.cell(~B, ~same, ~of, Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(a)(w)(voter)), x)(
        Safe.cell_most(~B, ~same, ~sl, ~of, Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(a)(w)(voter), x)(
          Safe.all_in_a(~mach, ~d, ~lg, ~ls, ~B, ~same, ~sl, ~of, ~kd, ~ofc, ~ofk, a, b, later, w, voter, e0, x, Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(a)(w)(voter))(hcb)(hx)(
            Safe.within_refl(~Ledgers.Ballot, ~Ledgers.Ballot.is_eq, ~Ledgers.Ballot.laws(), Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(a)(w)(voter))
          )
        )
      )(Safe.some_of(Cells.Cell<B>, Ledgers.Ballots.cell(~B, ~same, ~of, Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(a)(w)(voter)), c, h))
      +cb = Safe.most_some(~B, ~same, ~sl, Ledgers.Ballots.cell(~B, ~same, ~of, Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(b)(w)(voter)), x)(
        Safe.cell_most(~B, ~same, ~sl, ~of, Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(b)(w)(voter), x)(
          Safe.all_in_b(~mach, ~d, ~ls, ~B, ~same, ~sl, ~of, ~kd, ~ofc, ~ofk, a, b, later, w, voter, e0, x, Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(b)(w)(voter))(hcb)(hx)(
            Safe.within_refl(~Ledgers.Ballot, ~Ledgers.Ballot.is_eq, ~Ledgers.Ballot.laws(), Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(b)(w)(voter))
          )
        )
      )(Safe.cell_some(~B, ~same, ~of, Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(b)(w)(voter), e0, x)(hcb)(hx))
      Equal.trans(
        Maybe<&2, Cells.Cell<B>>,
        Ledgers.Ballots.cell(~B, ~same, ~of, Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(b)(w)(voter)),
        Some{Cells.One{x}},
        Some{c},
        cb,
        Equal.trans(
          Maybe<&2, Cells.Cell<B>>,
          Some{Cells.One{x}},
          Ledgers.Ballots.cell(~B, ~same, ~of, Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(a)(w)(voter)),
          Some{c},
          Equal.sym(Maybe<&2, Cells.Cell<B>>, Ledgers.Ballots.cell(~B, ~same, ~of, Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(a)(w)(voter)), Some{Cells.One{x}}, caA),
          h
        )
      )

# Safe.cell_kept from a ballot of the earlier ledger that holds a value
def Safe.cell_kept.at(
  ~mach: Machine(),
  ~d: Led(mach),
  ~lg: Hist.LaterGrows(mach, d),
  ~ls: Hist.LaterSingle(mach, d),
  ~B: Data,
  ~same: B -> B -> Bool,
  ~sl: Shared.Eq.Laws(B, same),
  ~of: Ledgers.Ballot -> Maybe<&2, B>,
  ~kd: Bool,
  ~ofc: @e1: Ledgers.Ballot -> @e2: Ledgers.Ballot -> {
    Ledgers.Ballot.cast(e1) == Ledgers.Ballot.cast(e2): Ledgers.Cast
  } -> {of(e1) == of(e2): Maybe<&2, B>},
  ~ofk: @e1: Ledgers.Ballot -> @y: B -> {of(e1) == Some{y}: Maybe<&2, B>} -> {
    Cast.is_vote(Ledgers.Ballot.cast(e1)) == kd: Bool
  },
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  +later: {
    Bool.and(
      Ledgers.Kind.grows(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), a, b),
      Led.honest(~mach, ~d, b)
    )
      == True{}: Bool
  },
  +w: Ledgers.Place,
  +voter: String,
  -c: Cells.Cell<B>,
  +h: {Ledgers.Ballots.cell(~B, ~same, ~of, Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(a)(w)(voter)) == Some{c}: Maybe<&2, Cells.Cell<B>>},
  wt: Safe.Wit(~B, ~of, Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(a)(w)(voter))
) -> {Ledgers.Ballots.cell(~B, ~same, ~of, Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(b)(w)(voter)) == Some{c}: Maybe<&2, Cells.Cell<B>>}:
  match wt:
    case Tuple{+e0, Tuple{hc, q}}:
      Safe.cell_kept.of(~mach, ~d, ~lg, ~ls, ~B, ~same, ~sl, ~of, ~kd, ~ofc, ~ofk, a, b, later, w, voter, c, h, e0, hc, q)

# the cell of a voter at a place stays in a later ledger: an honest later
# ledger holds no ballot of the voter there that disagrees
def Safe.cell_kept(
  ~mach: Machine(),
  ~d: Led(mach),
  ~lg: Hist.LaterGrows(mach, d),
  ~ls: Hist.LaterSingle(mach, d),
  ~B: Data,
  ~same: B -> B -> Bool,
  ~sl: Shared.Eq.Laws(B, same),
  ~of: Ledgers.Ballot -> Maybe<&2, B>,
  ~kd: Bool,
  ~ofc: @e1: Ledgers.Ballot -> @e2: Ledgers.Ballot -> {
    Ledgers.Ballot.cast(e1) == Ledgers.Ballot.cast(e2): Ledgers.Cast
  } -> {of(e1) == of(e2): Maybe<&2, B>},
  ~ofk: @e1: Ledgers.Ballot -> @y: B -> {of(e1) == Some{y}: Maybe<&2, B>} -> {
    Cast.is_vote(Ledgers.Ballot.cast(e1)) == kd: Bool
  },
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  +later: {
    Bool.and(
      Ledgers.Kind.grows(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), a, b),
      Led.honest(~mach, ~d, b)
    )
      == True{}: Bool
  },
  +w: Ledgers.Place,
  +voter: String,
  -c: Cells.Cell<B>
) -> {Ledgers.Ballots.cell(~B, ~same, ~of, Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(a)(w)(voter)) == Some{c}: Maybe<&2, Cells.Cell<B>>}
  -> {Ledgers.Ballots.cell(~B, ~same, ~of, Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(b)(w)(voter)) == Some{c}: Maybe<&2, Cells.Cell<B>>}:
  +h => Safe.cell_kept.at(
    ~mach,
    ~d,
    ~lg,
    ~ls,
    ~B, ~same, ~sl, ~of, ~kd, ~ofc, ~ofk,
    a,
    b,
    later,
    w,
    voter,
    c,
    h,
    Safe.witness(~B, ~same, ~of, Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(a)(w)(voter), c)(h)
  )

# the laws of Cast.is_eq
def Safe.cast_laws() -> Shared.Eq.Laws(Ledgers.Cast, Ledgers.Cast.is_eq):
  Codes.Code.eq_laws(~Ledgers.Cast, ~Ledgers.Cast.codec())

# Last.is_eq is True for a last vote and itself
def Safe.last_refl(a: Maybe<&2, Ledgers.Last>) -> {Ledgers.Last.is_eq(a, a) == True{}: Bool}:
  match a:
    case None{}:
      {==}
    case Some{x}:
      Shared.Eq.refl(
        ~Ledgers.Last,
        ~(x => y => Codes.Code.is_eq(~Ledgers.Last, ~Ledgers.Last.code, x, y)),
        Codes.Code.eq_laws(~Ledgers.Last, ~Ledgers.Last.codec()),
        x
      )

# the laws of Last.is_eq
def Safe.last_laws() -> Shared.Eq.Laws(Maybe<&2, Ledgers.Last>, Ledgers.Last.is_eq):
  (
    a => Safe.last_refl(a),
    a => b => Shared.Maybe.is_eq_sound(
      ~Ledgers.Last,
      ~(x => y => Codes.Code.is_eq(~Ledgers.Last, ~Ledgers.Last.code, x, y)),
      x => y => Shared.Eq.sound(
        ~Ledgers.Last,
        ~(x => y => Codes.Code.is_eq(~Ledgers.Last, ~Ledgers.Last.code, x, y)),
        Codes.Code.eq_laws(~Ledgers.Last, ~Ledgers.Last.codec()),
        x,
        y
      ),
      a,
      b
    )
  )

# what Ledgers.Ballot.step reads of a ballot is what its cast says
def Safe.step_same(
  a: Ledgers.Cast,
  -w1: Ledgers.Place,
  -n1: String,
  -l1: Ledgers.Link,
  -w2: Ledgers.Place,
  -n2: String,
  -l2: Ledgers.Link
) -> {
  Ledgers.Ballot.step(Ledgers.Ballot{Ledgers.Signed{w1, n1, a}, l1}) == Ledgers.Ballot.step(Ledgers.Ballot{Ledgers.Signed{w2, n2, a}, l2}): Maybe<&2, Ledgers.Step>
}:
  match a:
    case Ledgers.Cast.Vote{v, f}:
      {==}
    case Ledgers.Cast.Pass{p}:
      {==}

# two ballots that cast the same read the same
def Safe.step_cast(e1: Ledgers.Ballot, e2: Ledgers.Ballot) -> {
  Ledgers.Ballot.cast(e1) == Ledgers.Ballot.cast(e2): Ledgers.Cast
} -> {Ledgers.Ballot.step(e1) == Ledgers.Ballot.step(e2): Maybe<&2, Ledgers.Step>}:
  match e1 e2:
    case Ledgers.Ballot{Ledgers.Signed{w1, n1, +a1}, l1} Ledgers.Ballot{Ledgers.Signed{w2, n2, a2}, l2}:
      h =>
        %h: {
          Ledgers.Ballot.step(Ledgers.Ballot{Ledgers.Signed{w1, n1, a1}, l1}) == Ledgers.Ballot.step(Ledgers.Ballot{Ledgers.Signed{w2, n2, _}, l2}): Maybe<&2, Ledgers.Step>
        }
        Safe.step_same(a1, w1, n1, l1, w2, n2, l2)

# what Ledgers.Ballot.vote reads of a ballot is what its cast says
def Safe.vote_same(
  a: Ledgers.Cast,
  -w1: Ledgers.Place,
  -n1: String,
  -l1: Ledgers.Link,
  -w2: Ledgers.Place,
  -n2: String,
  -l2: Ledgers.Link
) -> {
  Ledgers.Ballot.vote(Ledgers.Ballot{Ledgers.Signed{w1, n1, a}, l1}) == Ledgers.Ballot.vote(Ledgers.Ballot{Ledgers.Signed{w2, n2, a}, l2}): Maybe<&2, Ledgers.Cast>
}:
  match a:
    case Ledgers.Cast.Vote{v, f}:
      {==}
    case Ledgers.Cast.Pass{p}:
      {==}

# two ballots that cast the same read the same
def Safe.vote_cast(e1: Ledgers.Ballot, e2: Ledgers.Ballot) -> {
  Ledgers.Ballot.cast(e1) == Ledgers.Ballot.cast(e2): Ledgers.Cast
} -> {Ledgers.Ballot.vote(e1) == Ledgers.Ballot.vote(e2): Maybe<&2, Ledgers.Cast>}:
  match e1 e2:
    case Ledgers.Ballot{Ledgers.Signed{w1, n1, +a1}, l1} Ledgers.Ballot{Ledgers.Signed{w2, n2, a2}, l2}:
      h =>
        %h: {
          Ledgers.Ballot.vote(Ledgers.Ballot{Ledgers.Signed{w1, n1, a1}, l1}) == Ledgers.Ballot.vote(Ledgers.Ballot{Ledgers.Signed{w2, n2, _}, l2}): Maybe<&2, Ledgers.Cast>
        }
        Safe.vote_same(a1, w1, n1, l1, w2, n2, l2)

# what Ledgers.Ballot.pass reads of a ballot is what its cast says
def Safe.pass_same(
  a: Ledgers.Cast,
  -w1: Ledgers.Place,
  -n1: String,
  -l1: Ledgers.Link,
  -w2: Ledgers.Place,
  -n2: String,
  -l2: Ledgers.Link
) -> {
  Ledgers.Ballot.pass(Ledgers.Ballot{Ledgers.Signed{w1, n1, a}, l1}) == Ledgers.Ballot.pass(Ledgers.Ballot{Ledgers.Signed{w2, n2, a}, l2}): Maybe<&2, Maybe<&2, Ledgers.Last>>
}:
  match a:
    case Ledgers.Cast.Vote{v, f}:
      {==}
    case Ledgers.Cast.Pass{p}:
      {==}

# two ballots that cast the same read the same
def Safe.pass_cast(e1: Ledgers.Ballot, e2: Ledgers.Ballot) -> {
  Ledgers.Ballot.cast(e1) == Ledgers.Ballot.cast(e2): Ledgers.Cast
} -> {Ledgers.Ballot.pass(e1) == Ledgers.Ballot.pass(e2): Maybe<&2, Maybe<&2, Ledgers.Last>>}:
  match e1 e2:
    case Ledgers.Ballot{Ledgers.Signed{w1, n1, +a1}, l1} Ledgers.Ballot{Ledgers.Signed{w2, n2, a2}, l2}:
      h =>
        %h: {
          Ledgers.Ballot.pass(Ledgers.Ballot{Ledgers.Signed{w1, n1, a1}, l1}) == Ledgers.Ballot.pass(Ledgers.Ballot{Ledgers.Signed{w2, n2, _}, l2}): Maybe<&2, Maybe<&2, Ledgers.Last>>
        }
        Safe.pass_same(a1, w1, n1, l1, w2, n2, l2)

# a ballot for a step is a vote
def Safe.step_kind(e: Ledgers.Ballot, -y: Ledgers.Step) -> {Ledgers.Ballot.step(e) == Some{y}: Maybe<&2, Ledgers.Step>}
  -> {Cast.is_vote(Ledgers.Ballot.cast(e)) == True{}: Bool}:
  match e:
    case Ledgers.Ballot{Ledgers.Signed{w, n, Ledgers.Cast.Vote{v, f}}, l}:
      h => {==}
    case Ledgers.Ballot{Ledgers.Signed{w, n, Ledgers.Cast.Pass{p}}, l}:
      h => Empty.absurd({False{} == True{}: Bool}, Shared.Maybe.none_ne_some(Ledgers.Step, y, h))

# a ballot that reads as a vote is a vote
def Safe.vote_kind(e: Ledgers.Ballot, -y: Ledgers.Cast) -> {Ledgers.Ballot.vote(e) == Some{y}: Maybe<&2, Ledgers.Cast>}
  -> {Cast.is_vote(Ledgers.Ballot.cast(e)) == True{}: Bool}:
  match e:
    case Ledgers.Ballot{Ledgers.Signed{w, n, Ledgers.Cast.Vote{v, f}}, l}:
      h => {==}
    case Ledgers.Ballot{Ledgers.Signed{w, n, Ledgers.Cast.Pass{p}}, l}:
      h => Empty.absurd({False{} == True{}: Bool}, Shared.Maybe.none_ne_some(Ledgers.Cast, y, h))

# a ballot that reads as a pass is not a vote
def Safe.pass_kind(e: Ledgers.Ballot, -y: Maybe<&2, Ledgers.Last>) -> {
  Ledgers.Ballot.pass(e) == Some{y}: Maybe<&2, Maybe<&2, Ledgers.Last>>
} -> {Cast.is_vote(Ledgers.Ballot.cast(e)) == False{}: Bool}:
  match e:
    case Ledgers.Ballot{Ledgers.Signed{w, n, Ledgers.Cast.Pass{p}}, l}:
      h => {==}
    case Ledgers.Ballot{Ledgers.Signed{w, n, Ledgers.Cast.Vote{v, f}}, l}:
      h => Empty.absurd({True{} == False{}: Bool}, Shared.Maybe.none_ne_some(Maybe<&2, Ledgers.Last>, y, h))

# the value of a cell that stays stays
def Safe.value_kept(
  -B: Data,
  m: Maybe<&2, Cells.Cell<B>>,
  -m2: Maybe<&2, Cells.Cell<B>>,
  -v: B,
  hm: @c: Cells.Cell<B> -> {m == Some{c}: Maybe<&2, Cells.Cell<B>>} -> {m2 == Some{c}: Maybe<&2, Cells.Cell<B>>}
) -> {Cells.Cell.value(B, m) == Some{v}: Maybe<&2, B>} -> {Cells.Cell.value(B, m2) == Some{v}: Maybe<&2, B>}:
  match m:
    case None{}:
      h => Empty.absurd({Cells.Cell.value(B, m2) == Some{v}: Maybe<&2, B>}, Shared.Maybe.none_ne_some(B, v, h))
    case Some{c}:
      h =>
        %Equal.sym(Maybe<&2, Cells.Cell<B>>, m2, Some{c}, hm(c)({==})): {
          Cells.Cell.value(B, _) == Some{v}: Maybe<&2, B>
        }
        h

# a slot that stays keeps what it holds
def Safe.keeps_kept(
  ~B: Data,
  ~same: B -> B -> Bool,
  ~sl: Shared.Eq.Laws(B, same),
  m: Maybe<&2, Cells.Cell<B>>,
  -m2: Maybe<&2, Cells.Cell<B>>,
  hm: @c: Cells.Cell<B> -> {m == Some{c}: Maybe<&2, Cells.Cell<B>>} -> {m2 == Some{c}: Maybe<&2, Cells.Cell<B>>}
) -> {Cells.Cell.keeps(~B, ~same, m, m2) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{Cells.One{+x}}:
      %Equal.sym(Maybe<&2, Cells.Cell<B>>, m2, Some{Cells.One{x}}, hm(Cells.One{x})({==})): {
        Cells.Cell.keeps(~B, ~same, Some{Cells.One{x}}, _) == True{}: Bool
      }
      Shared.Eq.refl(~B, ~same, sl, x)
    case Some{Cells.Many{}}:
      %Equal.sym(Maybe<&2, Cells.Cell<B>>, m2, Some{Cells.Many{}}, hm(Cells.Many{})({==})): {
        Cells.Cell.keeps(~B, ~same, Some{Cells.Many{}}, _) == True{}: Bool
      }
      {==}

# the step that a voter cast at a place stays in a later ledger
def Safe.step_kept(
  ~mach: Machine(),
  ~d: Led(mach),
  ~lg: Hist.LaterGrows(mach, d),
  ~ls: Hist.LaterSingle(mach, d),
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  +later: {
    Bool.and(
      Ledgers.Kind.grows(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), a, b),
      Led.honest(~mach, ~d, b)
    )
      == True{}: Bool
  },
  +w: Ledgers.Place,
  +voter: String,
  -v: Ledgers.Step
) -> {Led.voted(~mach, ~d, a, w, voter) == Some{v}: Maybe<&2, Ledgers.Step>}
  -> {Led.voted(~mach, ~d, b, w, voter) == Some{v}: Maybe<&2, Ledgers.Step>}:
  Safe.value_kept(
    Ledgers.Step,
    Ledgers.Ballots.cell(~Ledgers.Step, ~Ledgers.Step.is_eq, ~Ledgers.Ballot.step, Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(a)(w)(voter)),
    Ledgers.Ballots.cell(~Ledgers.Step, ~Ledgers.Step.is_eq, ~Ledgers.Ballot.step, Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(b)(w)(voter)),
    v,
    c => Safe.cell_kept(
      ~mach,
      ~d,
      ~lg,
      ~ls,
      ~Ledgers.Step, ~Ledgers.Step.is_eq, ~Ledgers.Step.laws(), ~Ledgers.Ballot.step, ~True{}, ~(x => y => Safe.step_cast(x, y)), ~(x => y => Safe.step_kind(x, y)),
      a,
      b,
      later,
      w,
      voter,
      c
    )
  )

# the vote of a voter at a place stays in a later ledger
def Safe.vote_kept(
  ~mach: Machine(),
  ~d: Led(mach),
  ~lg: Hist.LaterGrows(mach, d),
  ~ls: Hist.LaterSingle(mach, d),
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  +later: {
    Bool.and(
      Ledgers.Kind.grows(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), a, b),
      Led.honest(~mach, ~d, b)
    )
      == True{}: Bool
  },
  +w: Ledgers.Place,
  +voter: String,
  -v: Ledgers.Cast
) -> {Led.cast(~mach, ~d, a, w, voter) == Some{v}: Maybe<&2, Ledgers.Cast>}
  -> {Led.cast(~mach, ~d, b, w, voter) == Some{v}: Maybe<&2, Ledgers.Cast>}:
  Safe.value_kept(
    Ledgers.Cast,
    Ledgers.Ballots.cell(~Ledgers.Cast, ~Ledgers.Cast.is_eq, ~Ledgers.Ballot.vote, Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(a)(w)(voter)),
    Ledgers.Ballots.cell(~Ledgers.Cast, ~Ledgers.Cast.is_eq, ~Ledgers.Ballot.vote, Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(b)(w)(voter)),
    v,
    c => Safe.cell_kept(
      ~mach,
      ~d,
      ~lg,
      ~ls,
      ~Ledgers.Cast, ~Ledgers.Cast.is_eq, ~Safe.cast_laws(), ~Ledgers.Ballot.vote, ~True{}, ~(x => y => Safe.vote_cast(x, y)), ~(x => y => Safe.vote_kind(x, y)),
      a,
      b,
      later,
      w,
      voter,
      c
    )
  )

# the pass of a voter to a place stays in a later ledger
def Safe.pass_kept(
  ~mach: Machine(),
  ~d: Led(mach),
  ~lg: Hist.LaterGrows(mach, d),
  ~ls: Hist.LaterSingle(mach, d),
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  +later: {
    Bool.and(
      Ledgers.Kind.grows(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), a, b),
      Led.honest(~mach, ~d, b)
    )
      == True{}: Bool
  },
  +w: Ledgers.Place,
  +voter: String,
  -v: Maybe<&2, Ledgers.Last>
) -> {Led.passed(~mach, ~d, a, w, voter) == Some{v}: Maybe<&2, Maybe<&2, Ledgers.Last>>}
  -> {Led.passed(~mach, ~d, b, w, voter) == Some{v}: Maybe<&2, Maybe<&2, Ledgers.Last>>}:
  Safe.value_kept(
    Maybe<&2, Ledgers.Last>,
    Ledgers.Ballots.cell(~Maybe<&2, Ledgers.Last>, ~Ledgers.Last.is_eq, ~Ledgers.Ballot.pass, Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(a)(w)(voter)),
    Ledgers.Ballots.cell(~Maybe<&2, Ledgers.Last>, ~Ledgers.Last.is_eq, ~Ledgers.Ballot.pass, Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(b)(w)(voter)),
    v,
    c => Safe.cell_kept(
      ~mach,
      ~d,
      ~lg,
      ~ls,
      ~Maybe<&2, Ledgers.Last>, ~Ledgers.Last.is_eq, ~Safe.last_laws(), ~Ledgers.Ballot.pass, ~False{}, ~(x => y => Safe.pass_cast(x, y)), ~(x => y => Safe.pass_kind(x, y)),
      a,
      b,
      later,
      w,
      voter,
      c
    )
  )

# the cells of the voters os at a place keep what they hold in a later
# ledger
def Safe.cells_keep(
  ~mach: Machine(),
  ~d: Led(mach),
  ~lg: Hist.LaterGrows(mach, d),
  ~ls: Hist.LaterSingle(mach, d),
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  +later: {
    Bool.and(
      Ledgers.Kind.grows(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), a, b),
      Led.honest(~mach, ~d, b)
    )
      == True{}: Bool
  },
  +w: Ledgers.Place,
  os: List<&2, String>
) -> {
  Shared.List.all2(
    ~Maybe<&2, Cells.Cell<Ledgers.Step>>,
    ~Maybe<&2, Cells.Cell<Ledgers.Step>>,
    ~Cells.Cell.keeps(~Ledgers.Step, ~Ledgers.Step.is_eq),
    Ledgers.Kind.cells(~Machine.Q(mach), ~Led.kind(mach, d), a, w, os),
    Ledgers.Kind.cells(~Machine.Q(mach), ~Led.kind(mach, d), b, w, os)
  )
    == True{}: Bool
}:
  match os:
    case Nil{}:
      {==}
    case Con{+o, +r}:
      Shared.Bool.and_both(
        Cells.Cell.keeps(
          ~Ledgers.Step,
          ~Ledgers.Step.is_eq,
          Ledgers.Kind.cell(~Machine.Q(mach), ~Led.kind(mach, d), a, w, o),
          Ledgers.Kind.cell(~Machine.Q(mach), ~Led.kind(mach, d), b, w, o)
        ),
        Shared.List.all2(
          ~Maybe<&2, Cells.Cell<Ledgers.Step>>,
          ~Maybe<&2, Cells.Cell<Ledgers.Step>>,
          ~Cells.Cell.keeps(~Ledgers.Step, ~Ledgers.Step.is_eq),
          Ledgers.Kind.cells(~Machine.Q(mach), ~Led.kind(mach, d), a, w, r),
          Ledgers.Kind.cells(~Machine.Q(mach), ~Led.kind(mach, d), b, w, r)
        )
      )(
        Safe.keeps_kept(
          ~Ledgers.Step,
          ~Ledgers.Step.is_eq,
          ~Ledgers.Step.laws(),
          Ledgers.Kind.cell(~Machine.Q(mach), ~Led.kind(mach, d), a, w, o),
          Ledgers.Kind.cell(~Machine.Q(mach), ~Led.kind(mach, d), b, w, o),
          c => Safe.cell_kept(~mach, ~d, ~lg, ~ls, ~Ledgers.Step, ~Ledgers.Step.is_eq, ~Ledgers.Step.laws(), ~Ledgers.Ballot.step, ~True{}, ~(x => y => Safe.step_cast(x, y)), ~(x => y => Safe.step_kind(x, y)), a, b, later, w, o, c)
        )
      )(Safe.cells_keep(~mach, ~d, ~lg, ~ls, a, b, later, w, r))

# the step that a majority cast at a place stays in a later ledger
def Safe.tally_kept(
  ~mach: Machine(),
  ~d: Led(mach),
  ~lg: Hist.LaterGrows(mach, d),
  ~ls: Hist.LaterSingle(mach, d),
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  +later: {
    Bool.and(
      Ledgers.Kind.grows(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), a, b),
      Led.honest(~mach, ~d, b)
    )
      == True{}: Bool
  },
  +w: Ledgers.Place,
  +os: List<&2, String>,
  +v: Ledgers.Step
) -> {Led.tally(~mach, ~d, a, w, os) == Some{v}: Maybe<&2, Ledgers.Step>}
  -> {Led.tally(~mach, ~d, b, w, os) == Some{v}: Maybe<&2, Ledgers.Step>}:
  h => Quorums.Quorum.major_kept(~Ledgers.Step, ~Ledgers.Step.is_eq, ~Ledgers.Step.laws())(
    Ledgers.Kind.cells(~Machine.Q(mach), ~Led.kind(mach, d), a, w, os)
  )(Ledgers.Kind.cells(~Machine.Q(mach), ~Led.kind(mach, d), b, w, os))(v)(Safe.cells_keep(~mach, ~d, ~lg, ~ls, a, b, later, w, os))(h)

# a read that holds something stays so when its value is kept
def Safe.is_some_kept(
  -A: Data,
  m: Maybe<&2, A>,
  -m2: Maybe<&2, A>,
  hm: @y: A -> {m == Some{y}: Maybe<&2, A>} -> {m2 == Some{y}: Maybe<&2, A>}
) -> {Maybe.is_some(&2, A, m) == True{}: Bool} -> {Maybe.is_some(&2, A, m2) == True{}: Bool}:
  match m:
    case None{}:
      h => Empty.absurd({Maybe.is_some(&2, A, m2) == True{}: Bool}, Shared.Bool.false_ne_true(h))
    case Some{y}:
      h =>
        %Equal.sym(Maybe<&2, A>, m2, Some{y}, hm(y)({==})): {Maybe.is_some(&2, A, _) == True{}: Bool}
        {==}

# a read that holds something is the same read when its value is kept
def Safe.eq_kept(
  -A: Data,
  m: Maybe<&2, A>,
  -m2: Maybe<&2, A>,
  hm: @y: A -> {m == Some{y}: Maybe<&2, A>} -> {m2 == Some{y}: Maybe<&2, A>}
) -> {Maybe.is_some(&2, A, m) == True{}: Bool} -> {m2 == m: Maybe<&2, A>}:
  match m:
    case None{}:
      h => Empty.absurd({m2 == None{}: Maybe<&2, A>}, Shared.Bool.false_ne_true(h))
    case Some{y}:
      h => hm(y)({==})

# the passes that a ledger holds of some voters, a later ledger holds
def Safe.passed_all_kept(
  ~mach: Machine(),
  ~d: Led(mach),
  ~lg: Hist.LaterGrows(mach, d),
  ~ls: Hist.LaterSingle(mach, d),
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  +later: {
    Bool.and(
      Ledgers.Kind.grows(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), a, b),
      Led.honest(~mach, ~d, b)
    )
      == True{}: Bool
  },
  +w: Ledgers.Place,
  from: List<&2, String>
) -> {Passed.all(~mach, ~d, a, w, from) == True{}: Bool} -> {Passed.all(~mach, ~d, b, w, from) == True{}: Bool}:
  match from:
    case Nil{}:
      e => {==}
    case Con{+o, +r}:
      +e => Shared.List.all.if_both(
        Maybe.is_some(&2, Maybe<&2, Ledgers.Last>, Led.passed(~mach, ~d, b, w, o)),
        u => Passed.all(~mach, ~d, b, w, r)
      )(
        Safe.is_some_kept(
          Maybe<&2, Ledgers.Last>,
          Led.passed(~mach, ~d, a, w, o),
          Led.passed(~mach, ~d, b, w, o),
          y => Safe.pass_kept(~mach, ~d, ~lg, ~ls, a, b, later, w, o, y)
        )(Shared.List.all.if_hit(Maybe.is_some(&2, Maybe<&2, Ledgers.Last>, Led.passed(~mach, ~d, a, w, o)), u => Passed.all(~mach, ~d, a, w, r))(e))
      )(
        Safe.passed_all_kept(~mach, ~d, ~lg, ~ls, a, b, later, w, r)(
          Shared.List.all.if_rest(Maybe.is_some(&2, Maybe<&2, Ledgers.Last>, Led.passed(~mach, ~d, a, w, o)), u => Passed.all(~mach, ~d, a, w, r))(e)
        )
      )

# a pass that a ledger holds is the same pass in a later ledger
def Safe.passed_eq(
  ~mach: Machine(),
  ~d: Led(mach),
  ~lg: Hist.LaterGrows(mach, d),
  ~ls: Hist.LaterSingle(mach, d),
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  +later: {
    Bool.and(
      Ledgers.Kind.grows(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), a, b),
      Led.honest(~mach, ~d, b)
    )
      == True{}: Bool
  },
  +w: Ledgers.Place,
  +o: String
) -> {Maybe.is_some(&2, Maybe<&2, Ledgers.Last>, Led.passed(~mach, ~d, a, w, o)) == True{}: Bool}
  -> {Led.passed(~mach, ~d, b, w, o) == Led.passed(~mach, ~d, a, w, o): Maybe<&2, Maybe<&2, Ledgers.Last>>}:
  Safe.eq_kept(
    Maybe<&2, Ledgers.Last>,
    Led.passed(~mach, ~d, a, w, o),
    Led.passed(~mach, ~d, b, w, o),
    y => Safe.pass_kept(~mach, ~d, ~lg, ~ls, a, b, later, w, o, y)
  )

# the highest last vote that the passes of some voters name is the same in a
# later ledger, when the ledger holds each of the passes
def Safe.last_eq(
  ~mach: Machine(),
  ~d: Led(mach),
  ~lg: Hist.LaterGrows(mach, d),
  ~ls: Hist.LaterSingle(mach, d),
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  +later: {
    Bool.and(
      Ledgers.Kind.grows(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), a, b),
      Led.honest(~mach, ~d, b)
    )
      == True{}: Bool
  },
  +w: Ledgers.Place,
  from: List<&2, String>
) -> {Passed.all(~mach, ~d, a, w, from) == True{}: Bool}
  -> {Passes.last(~mach, ~d, b, w, from) == Passes.last(~mach, ~d, a, w, from): Maybe<&2, Ledgers.Last>}:
  match from:
    case Nil{}:
      e => {==}
    case Con{+o, +r}:
      +e =>
        %Equal.sym(
          Maybe<&2, Maybe<&2, Ledgers.Last>>,
          Led.passed(~mach, ~d, b, w, o),
          Led.passed(~mach, ~d, a, w, o),
          Safe.passed_eq(~mach, ~d, ~lg, ~ls, a, b, later, w, o)(
            Shared.List.all.if_hit(Maybe.is_some(&2, Maybe<&2, Ledgers.Last>, Led.passed(~mach, ~d, a, w, o)), u => Passed.all(~mach, ~d, a, w, r))(e)
          )
        ): {
          Last.newer(Passed.last(_), Passes.last(~mach, ~d, b, w, r))
            == Last.newer(Passed.last(Led.passed(~mach, ~d, a, w, o)), Passes.last(~mach, ~d, a, w, r)): Maybe<&2, Ledgers.Last>
        }
        %Equal.sym(
          Maybe<&2, Ledgers.Last>,
          Passes.last(~mach, ~d, b, w, r),
          Passes.last(~mach, ~d, a, w, r),
          Safe.last_eq(~mach, ~d, ~lg, ~ls, a, b, later, w, r)(
            Shared.List.all.if_rest(Maybe.is_some(&2, Maybe<&2, Ledgers.Last>, Led.passed(~mach, ~d, a, w, o)), u => Passed.all(~mach, ~d, a, w, r))(e)
          )
        ): {
          Last.newer(Passed.last(Led.passed(~mach, ~d, a, w, o)), _)
            == Last.newer(Passed.last(Led.passed(~mach, ~d, a, w, o)), Passes.last(~mach, ~d, a, w, r)): Maybe<&2, Ledgers.Last>
        }
        {==}

# the passes of some voters agree on a step in a later ledger as they do in
# the earlier one, when the ledger holds each of them
def Safe.agree_eq(
  ~mach: Machine(),
  ~d: Led(mach),
  ~lg: Hist.LaterGrows(mach, d),
  ~ls: Hist.LaterSingle(mach, d),
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  +later: {
    Bool.and(
      Ledgers.Kind.grows(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), a, b),
      Led.honest(~mach, ~d, b)
    )
      == True{}: Bool
  },
  +w: Ledgers.Place,
  from: List<&2, String>,
  +t: Nat,
  +v: Ledgers.Step
) -> {Passed.all(~mach, ~d, a, w, from) == True{}: Bool}
  -> {Passes.agree(~mach, ~d, b, w, from, t, v) == Passes.agree(~mach, ~d, a, w, from, t, v): Bool}:
  match from:
    case Nil{}:
      e => {==}
    case Con{+o, +r}:
      +e =>
        %Equal.sym(
          Maybe<&2, Maybe<&2, Ledgers.Last>>,
          Led.passed(~mach, ~d, b, w, o),
          Led.passed(~mach, ~d, a, w, o),
          Safe.passed_eq(~mach, ~d, ~lg, ~ls, a, b, later, w, o)(
            Shared.List.all.if_hit(Maybe.is_some(&2, Maybe<&2, Ledgers.Last>, Led.passed(~mach, ~d, a, w, o)), u => Passed.all(~mach, ~d, a, w, r))(e)
          )
        ): {
          List.all.if(u => Passes.agree(~mach, ~d, b, w, r, t, v), Last.allows(Passed.last(_), t, v))
            == List.all.if(u => Passes.agree(~mach, ~d, a, w, r, t, v), Last.allows(Passed.last(Led.passed(~mach, ~d, a, w, o)), t, v)): Bool
        }
        %Equal.sym(
          Bool,
          Passes.agree(~mach, ~d, b, w, r, t, v),
          Passes.agree(~mach, ~d, a, w, r, t, v),
          Safe.agree_eq(~mach, ~d, ~lg, ~ls, a, b, later, w, r, t, v)(
            Shared.List.all.if_rest(Maybe.is_some(&2, Maybe<&2, Ledgers.Last>, Led.passed(~mach, ~d, a, w, o)), u => Passed.all(~mach, ~d, a, w, r))(e)
          )
        ): {
          List.all.if(u => _, Last.allows(Passed.last(Led.passed(~mach, ~d, a, w, o)), t, v))
            == List.all.if(u => Passes.agree(~mach, ~d, a, w, r, t, v), Last.allows(Passed.last(Led.passed(~mach, ~d, a, w, o)), t, v)): Bool
        }
        {==}

# Safe.act_kept once the test of the first voter is known
def Safe.act_kept.at(
  ~mach: Machine(),
  ~d: Led(mach),
  ~lg: Hist.LaterGrows(mach, d),
  ~ls: Hist.LaterSingle(mach, d),
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
  +r: Nat,
  rest: List<&2, String>,
  +k: Nat,
  +o: String,
  -y: Ledgers.Cast,
  cond: Bool,
  ih: {Passes.act(~mach, ~d, a, c, h, r, rest, k) == Some{y}: Maybe<&2, Ledgers.Cast>}
    -> {Passes.act(~mach, ~d, b, c, h, r, rest, k) == Some{y}: Maybe<&2, Ledgers.Cast>}
) -> {
  Shared.Bool.when(
    Maybe<&2, Ledgers.Cast>,
    cond,
    u => Led.cast(~mach, ~d, a, Ledgers.Place{c, h, k}, o),
    u => Passes.act(~mach, ~d, a, c, h, r, rest, k)
  )
    == Some{y}: Maybe<&2, Ledgers.Cast>
} -> {
  Shared.Bool.when(
    Maybe<&2, Ledgers.Cast>,
    cond,
    u => Led.cast(~mach, ~d, b, Ledgers.Place{c, h, k}, o),
    u => Passes.act(~mach, ~d, b, c, h, r, rest, k)
  )
    == Some{y}: Maybe<&2, Ledgers.Cast>
}:
  match cond:
    case True{}:
      Safe.vote_kept(~mach, ~d, ~lg, ~ls, a, b, later, Ledgers.Place{c, h, k}, o, y)
    case False{}:
      ih

# the vote that the passes of some voters lead back to is the same in a later
# ledger, when the ledger holds each of the passes
def Safe.act_kept(
  ~mach: Machine(),
  ~d: Led(mach),
  ~lg: Hist.LaterGrows(mach, d),
  ~ls: Hist.LaterSingle(mach, d),
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
  +r: Nat,
  from: List<&2, String>,
  +k: Nat,
  -y: Ledgers.Cast
) -> {Passed.all(~mach, ~d, a, Ledgers.Place{c, h, r}, from) == True{}: Bool}
  -> {Passes.act(~mach, ~d, a, c, h, r, from, k) == Some{y}: Maybe<&2, Ledgers.Cast>}
  -> {Passes.act(~mach, ~d, b, c, h, r, from, k) == Some{y}: Maybe<&2, Ledgers.Cast>}:
  match from:
    case Nil{}:
      e => x => x
    case Con{+o, +rest}:
      +e =>
        %Equal.sym(
          Maybe<&2, Maybe<&2, Ledgers.Last>>,
          Led.passed(~mach, ~d, b, Ledgers.Place{c, h, r}, o),
          Led.passed(~mach, ~d, a, Ledgers.Place{c, h, r}, o),
          Safe.passed_eq(~mach, ~d, ~lg, ~ls, a, b, later, Ledgers.Place{c, h, r}, o)(
            Shared.List.all.if_hit(
              Maybe.is_some(&2, Maybe<&2, Ledgers.Last>, Led.passed(~mach, ~d, a, Ledgers.Place{c, h, r}, o)),
              u => Passed.all(~mach, ~d, a, Ledgers.Place{c, h, r}, rest)
            )(e)
          )
        ): {
            Shared.Bool.when(
              Maybe<&2, Ledgers.Cast>,
              Last.in(Passed.last(Led.passed(~mach, ~d, a, Ledgers.Place{c, h, r}, o)), k),
              u => Led.cast(~mach, ~d, a, Ledgers.Place{c, h, k}, o),
              u => Passes.act(~mach, ~d, a, c, h, r, rest, k)
            )
              == Some{y}: Maybe<&2, Ledgers.Cast>
          } -> {
            Shared.Bool.when(
              Maybe<&2, Ledgers.Cast>,
              Last.in(Passed.last(_), k),
              u => Led.cast(~mach, ~d, b, Ledgers.Place{c, h, k}, o),
              u => Passes.act(~mach, ~d, b, c, h, r, rest, k)
            )
              == Some{y}: Maybe<&2, Ledgers.Cast>
          }
        Safe.act_kept.at(
          ~mach, ~d, ~lg, ~ls,
          a,
          b,
          later,
          c,
          h,
          r,
          rest,
          k,
          o,
          y,
          Last.in(Passed.last(Led.passed(~mach, ~d, a, Ledgers.Place{c, h, r}, o)), k),
          Safe.act_kept(~mach, ~d, ~lg, ~ls, a, b, later, c, h, r, rest, k, y)(
            Shared.List.all.if_rest(
              Maybe.is_some(&2, Maybe<&2, Ledgers.Last>, Led.passed(~mach, ~d, a, Ledgers.Place{c, h, r}, o)),
              u => Passed.all(~mach, ~d, a, Ledgers.Place{c, h, r}, rest)
            )(e)
          )
        )

# an all.if holds when its test and its rest do (rest only in the type)
def Safe.and_both(hit: Bool, -rest: Unit -> Bool) -> {hit == True{}: Bool}
  -> {rest(Unit{}) == True{}: Bool}
  -> {List.all.if(rest, hit) == True{}: Bool}:
  match hit:
    case True{}:
      h => r => r
    case False{}:
      h => r => h

# the test of an all.if that holds holds (rest only in the type)
def Safe.and_hit(hit: Bool, -rest: Unit -> Bool) -> {List.all.if(rest, hit) == True{}: Bool}
  -> {hit == True{}: Bool}:
  match hit:
    case True{}:
      h => {==}
    case False{}:
      h => h

# the rest of an all.if that holds holds (rest only in the type)
def Safe.and_rest(hit: Bool, -rest: Unit -> Bool) -> {List.all.if(rest, hit) == True{}: Bool}
  -> {rest(Unit{}) == True{}: Bool}:
  match hit:
    case True{}:
      h => h
    case False{}:
      h => Empty.absurd({rest(Unit{}) == True{}: Bool}, Shared.Bool.false_ne_true(h))

# a vote for v whose passes allow it stays one when its act stays and its
# passes stay allowed
def Safe.casts_kept(
  m: Maybe<&2, Ledgers.Cast>,
  -m2: Maybe<&2, Ledgers.Cast>,
  +v: Ledgers.Step,
  -ra: List<&2, String> -> Bool,
  -rb: List<&2, String> -> Bool,
  hm: @y: Ledgers.Cast -> {m == Some{y}: Maybe<&2, Ledgers.Cast>} -> {m2 == Some{y}: Maybe<&2, Ledgers.Cast>},
  ih: @f: List<&2, String> -> {ra(f) == True{}: Bool} -> {rb(f) == True{}: Bool}
) -> {Cast.casts(m, v, ra) == True{}: Bool} -> {Cast.casts(m2, v, rb) == True{}: Bool}:
  match m:
    case Some{Ledgers.Cast.Vote{+x, +f}}:
      +e =>
        %Equal.sym(
          Maybe<&2, Ledgers.Cast>,
          m2,
          Some{Ledgers.Cast.Vote{x, f}},
          hm(Ledgers.Cast.Vote{x, f})({==})
        ): {Cast.casts(_, v, rb) == True{}: Bool}
        Safe.and_both(Ledgers.Step.is_eq(x, v), u => rb(f))(
          Safe.and_hit(Ledgers.Step.is_eq(x, v), u => ra(f))(e)
        )(ih(f)(Safe.and_rest(Ledgers.Step.is_eq(x, v), u => ra(f))(e)))
    case Some{Ledgers.Cast.Pass{p}}:
      e => Empty.absurd({Cast.casts(m2, v, rb) == True{}: Bool}, Shared.Bool.false_ne_true(e))
    case None{}:
      e => Empty.absurd({Cast.casts(m2, v, rb) == True{}: Bool}, Shared.Bool.false_ne_true(e))

# what holds of the round of a last vote holds of it by a weaker test
def Safe.holds_kept(
  m: Maybe<&2, Ledgers.Last>,
  -ga: Nat -> Bool,
  -gb: Nat -> Bool,
  ih: @t: Nat -> {ga(t) == True{}: Bool} -> {gb(t) == True{}: Bool}
) -> {Last.holds(m, ga) == True{}: Bool} -> {Last.holds(m, gb) == True{}: Bool}:
  match m:
    case Some{Ledgers.Last{t, x}}:
      ih(t)
    case None{}:
      e => {==}

# a step that the rules allow in a round stays allowed in a later ledger
def Safe.allowed_kept(
  ~mach: Machine(),
  ~d: Led(mach),
  ~lg: Hist.LaterGrows(mach, d),
  ~ls: Hist.LaterSingle(mach, d),
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
  +v: Ledgers.Step,
  k: Nat,
  r: Nat,
  +from: List<&2, String>
) -> {Step.allowed.in(~mach, ~d, a, c, h, os, v, k, r, from) == True{}: Bool}
  -> {Step.allowed.in(~mach, ~d, b, c, h, os, v, k, r, from) == True{}: Bool}:
  match k r:
    case 0n 0n:
      e => {==}
    case 1n+j 0n:
      e => {==}
    case 0n 1n+p:
      e => Empty.absurd({False{} == True{}: Bool}, Shared.Bool.false_ne_true(e))
    case 1n+(+j) 1n+(+p):
      +e =>
        +pm = Shared.List.all.if_hit(
          Passed.major(~mach, ~d, a, Ledgers.Place{c, h, 1n+p}, os, from),
          u => Last.holds(Passes.last(~mach, ~d, a, Ledgers.Place{c, h, 1n+p}, from), +t => List.all.if(u2 => Cast.casts(Passes.act(~mach, ~d, a, c, h, 1n+p, from, t), v, +f => Step.allowed.in(~mach, ~d, a, c, h, os, v, j, t, f)), Passes.agree(~mach, ~d, a, Ledgers.Place{c, h, 1n+p}, from, t, v)))
        )(e)
        +pall = Shared.List.all.if_hit(
          Passed.all(~mach, ~d, a, Ledgers.Place{c, h, 1n+p}, from),
          u => List.all.if(u2 => Voters.major(os, from), Voters.sub(os, from))
        )(pm)
        Shared.List.all.if_both(
          Passed.major(~mach, ~d, b, Ledgers.Place{c, h, 1n+p}, os, from),
          u => Last.holds(Passes.last(~mach, ~d, b, Ledgers.Place{c, h, 1n+p}, from), +t => List.all.if(u2 => Cast.casts(Passes.act(~mach, ~d, b, c, h, 1n+p, from, t), v, +f => Step.allowed.in(~mach, ~d, b, c, h, os, v, j, t, f)), Passes.agree(~mach, ~d, b, Ledgers.Place{c, h, 1n+p}, from, t, v)))
        )(
          Shared.List.all.if_both(
            Passed.all(~mach, ~d, b, Ledgers.Place{c, h, 1n+p}, from),
            u => List.all.if(u2 => Voters.major(os, from), Voters.sub(os, from))
          )(Safe.passed_all_kept(~mach, ~d, ~lg, ~ls, a, b, later, Ledgers.Place{c, h, 1n+p}, from)(pall))(
            Shared.List.all.if_rest(
              Passed.all(~mach, ~d, a, Ledgers.Place{c, h, 1n+p}, from),
              u => List.all.if(u2 => Voters.major(os, from), Voters.sub(os, from))
            )(pm)
          )
        )(
          %Equal.sym(
            Maybe<&2, Ledgers.Last>,
            Passes.last(~mach, ~d, b, Ledgers.Place{c, h, 1n+p}, from),
            Passes.last(~mach, ~d, a, Ledgers.Place{c, h, 1n+p}, from),
            Safe.last_eq(~mach, ~d, ~lg, ~ls, a, b, later, Ledgers.Place{c, h, 1n+p}, from)(pall)
          ): {
            Last.holds(_, +t => List.all.if(u2 => Cast.casts(Passes.act(~mach, ~d, b, c, h, 1n+p, from, t), v, +f => Step.allowed.in(~mach, ~d, b, c, h, os, v, j, t, f)), Passes.agree(~mach, ~d, b, Ledgers.Place{c, h, 1n+p}, from, t, v))) == True{}: Bool
          }
          Safe.holds_kept(
            Passes.last(~mach, ~d, a, Ledgers.Place{c, h, 1n+p}, from),
            +t => List.all.if(u2 => Cast.casts(Passes.act(~mach, ~d, a, c, h, 1n+p, from, t), v, +f => Step.allowed.in(~mach, ~d, a, c, h, os, v, j, t, f)), Passes.agree(~mach, ~d, a, Ledgers.Place{c, h, 1n+p}, from, t, v)),
            +t => List.all.if(u2 => Cast.casts(Passes.act(~mach, ~d, b, c, h, 1n+p, from, t), v, +f => Step.allowed.in(~mach, ~d, b, c, h, os, v, j, t, f)), Passes.agree(~mach, ~d, b, Ledgers.Place{c, h, 1n+p}, from, t, v)),
            +t => +g => Shared.List.all.if_both(
              Passes.agree(~mach, ~d, b, Ledgers.Place{c, h, 1n+p}, from, t, v),
              u2 => Cast.casts(
                Passes.act(~mach, ~d, b, c, h, 1n+p, from, t),
                v,
                +f => Step.allowed.in(~mach, ~d, b, c, h, os, v, j, t, f)
              )
            )(
              %Equal.sym(
                Bool,
                Passes.agree(~mach, ~d, b, Ledgers.Place{c, h, 1n+p}, from, t, v),
                Passes.agree(~mach, ~d, a, Ledgers.Place{c, h, 1n+p}, from, t, v),
                Safe.agree_eq(~mach, ~d, ~lg, ~ls, a, b, later, Ledgers.Place{c, h, 1n+p}, from, t, v)(pall)
              ): {_ == True{}: Bool}
              Shared.List.all.if_hit(
                Passes.agree(~mach, ~d, a, Ledgers.Place{c, h, 1n+p}, from, t, v),
                u2 => Cast.casts(
                  Passes.act(~mach, ~d, a, c, h, 1n+p, from, t),
                  v,
                  +f => Step.allowed.in(~mach, ~d, a, c, h, os, v, j, t, f)
                )
              )(g)
            )(
              Safe.casts_kept(
                Passes.act(~mach, ~d, a, c, h, 1n+p, from, t),
                Passes.act(~mach, ~d, b, c, h, 1n+p, from, t),
                v,
                +f => Step.allowed.in(~mach, ~d, a, c, h, os, v, j, t, f),
                +f => Step.allowed.in(~mach, ~d, b, c, h, os, v, j, t, f),
                y => Safe.act_kept(~mach, ~d, ~lg, ~ls, a, b, later, c, h, 1n+p, from, t, y)(pall),
                f => Safe.allowed_kept(~mach, ~d, ~lg, ~ls, a, b, later, c, h, os, v, j, t, f)
              )(
                Shared.List.all.if_rest(
                  Passes.agree(~mach, ~d, a, Ledgers.Place{c, h, 1n+p}, from, t, v),
                  u2 => Cast.casts(
                    Passes.act(~mach, ~d, a, c, h, 1n+p, from, t),
                    v,
                    +f => Step.allowed.in(~mach, ~d, a, c, h, os, v, j, t, f)
                  )
                )(g)
              )
            )
          )(
            Shared.List.all.if_rest(
              Passed.major(~mach, ~d, a, Ledgers.Place{c, h, 1n+p}, os, from),
              u => Last.holds(Passes.last(~mach, ~d, a, Ledgers.Place{c, h, 1n+p}, from), +t => List.all.if(u2 => Cast.casts(Passes.act(~mach, ~d, a, c, h, 1n+p, from, t), v, +f => Step.allowed.in(~mach, ~d, a, c, h, os, v, j, t, f)), Passes.agree(~mach, ~d, a, Ledgers.Place{c, h, 1n+p}, from, t, v)))
            )(e)
          )
        )

# Step.allowed at a place stays in a later ledger
def Safe.allowed_at(
  ~mach: Machine(),
  ~d: Led(mach),
  ~lg: Hist.LaterGrows(mach, d),
  ~ls: Hist.LaterSingle(mach, d),
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  +later: {
    Bool.and(
      Ledgers.Kind.grows(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), a, b),
      Led.honest(~mach, ~d, b)
    )
      == True{}: Bool
  },
  w: Ledgers.Place,
  +os: List<&2, String>,
  +v: Ledgers.Step,
  +from: List<&2, String>
) -> {Step.allowed(~mach, ~d, a, w, os, v, from) == True{}: Bool}
  -> {Step.allowed(~mach, ~d, b, w, os, v, from) == True{}: Bool}:
  match w:
    case Ledgers.Place{+c, +h, +r}:
      Safe.allowed_kept(~mach, ~d, ~lg, ~ls, a, b, later, c, h, os, v, r, r, from)

# a when that holds stays so under a weaker test
def Safe.when_kept(
  -B: Data,
  ba: Bool,
  -bb: Bool,
  -k: Unit -> Maybe<&2, B>,
  -x: B,
  hb: {ba == True{}: Bool} -> {bb == True{}: Bool}
) -> {Shared.Maybe.when(B, ba, k) == Some{x}: Maybe<&2, B>} -> {Shared.Maybe.when(B, bb, k) == Some{x}: Maybe<&2, B>}:
  match ba:
    case True{}:
      e =>
        %Equal.sym(Bool, bb, True{}, hb({==})): {Shared.Maybe.when(B, _, k) == Some{x}: Maybe<&2, B>}
        e
    case False{}:
      e => Empty.absurd({Shared.Maybe.when(B, bb, k) == Some{x}: Maybe<&2, B>}, Shared.Maybe.none_ne_some(B, x, e))

# the step that a round decides once its tally is known stays in a later
# ledger
def Safe.led_kept(
  ~mach: Machine(),
  ~d: Led(mach),
  ~lg: Hist.LaterGrows(mach, d),
  ~ls: Hist.LaterSingle(mach, d),
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  +later: {
    Bool.and(
      Ledgers.Kind.grows(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), a, b),
      Led.honest(~mach, ~d, b)
    )
      == True{}: Bool
  },
  +w: Ledgers.Place,
  +os: List<&2, String>,
  +v: Ledgers.Step,
  +p: String,
  -x: Ledgers.Step
) -> {Round.led(~mach, ~d, a, w, os, v, p) == Some{x}: Maybe<&2, Ledgers.Step>}
  -> {Round.led(~mach, ~d, b, w, os, v, p) == Some{x}: Maybe<&2, Ledgers.Step>}:
  Safe.when_kept(
    Ledgers.Step,
    Cast.casts(Led.cast(~mach, ~d, a, w, p), v, f => Step.allowed(~mach, ~d, a, w, os, v, f)),
    Cast.casts(Led.cast(~mach, ~d, b, w, p), v, f => Step.allowed(~mach, ~d, b, w, os, v, f)),
    u => Some{v},
    x,
    Safe.casts_kept(
      Led.cast(~mach, ~d, a, w, p),
      Led.cast(~mach, ~d, b, w, p),
      v,
      f => Step.allowed(~mach, ~d, a, w, os, v, f),
      f => Step.allowed(~mach, ~d, b, w, os, v, f),
      y => Safe.vote_kept(~mach, ~d, ~lg, ~ls, a, b, later, w, p, y),
      f => Safe.allowed_at(~mach, ~d, ~lg, ~ls, a, b, later, w, os, v, f)
    )
  )

# the step that a round decides stays in a later ledger
def Safe.decide_kept(
  ~mach: Machine(),
  ~d: Led(mach),
  ~lg: Hist.LaterGrows(mach, d),
  ~ls: Hist.LaterSingle(mach, d),
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
  +r: Nat,
  -x: Ledgers.Step
) -> {Round.decide(~mach, ~d, a, c, h, os, r) == Some{x}: Maybe<&2, Ledgers.Step>}
  -> {Round.decide(~mach, ~d, b, c, h, os, r) == Some{x}: Maybe<&2, Ledgers.Step>}:
  Shared.Maybe.bind_kept(
    Ledgers.Step,
    Ledgers.Step,
    Led.tally(~mach, ~d, a, Ledgers.Place{c, h, r}, os),
    Led.tally(~mach, ~d, b, Ledgers.Place{c, h, r}, os),
    +v => Maybe.bind(
      &2,
      String,
      Ledgers.Step,
      Voters.turn(os, h, r),
      p => Round.led(~mach, ~d, a, Ledgers.Place{c, h, r}, os, v, p)
    ),
    +v => Maybe.bind(
      &2,
      String,
      Ledgers.Step,
      Voters.turn(os, h, r),
      p => Round.led(~mach, ~d, b, Ledgers.Place{c, h, r}, os, v, p)
    ),
    x,
    v => Safe.tally_kept(~mach, ~d, ~lg, ~ls, a, b, later, Ledgers.Place{c, h, r}, os, v),
    +v => Shared.Maybe.bind_kept(
      String,
      Ledgers.Step,
      Voters.turn(os, h, r),
      Voters.turn(os, h, r),
      p => Round.led(~mach, ~d, a, Ledgers.Place{c, h, r}, os, v, p),
      p => Round.led(~mach, ~d, b, Ledgers.Place{c, h, r}, os, v, p),
      x,
      p => e => e,
      p => Safe.led_kept(~mach, ~d, ~lg, ~ls, a, b, later, Ledgers.Place{c, h, r}, os, v, p, x)
    )
  )

# a cell that counts for the step v holds v
def Safe.hit_value(m: Maybe<&2, Cells.Cell<Ledgers.Step>>, +v: Ledgers.Step) -> {
  Quorums.Quorum.hit(~Ledgers.Step, ~Ledgers.Step.is_eq, m, v) == True{}: Bool
} -> {Cells.Cell.value(Ledgers.Step, m) == Some{v}: Maybe<&2, Ledgers.Step>}:
  match m:
    case Some{Cells.One{+x}}:
      h => Equal.cong(Ledgers.Step, Maybe<&2, Ledgers.Step>, z => Some{z}, x, v, Ledgers.Step.is_eq_sound(x, v)(h))
    case Some{Cells.Many{}}:
      h => Empty.absurd({None{} == Some{v}: Maybe<&2, Ledgers.Step>}, Shared.Bool.false_ne_true(h))
    case None{}:
      h => Empty.absurd({None{} == Some{v}: Maybe<&2, Ledgers.Step>}, Shared.Bool.false_ne_true(h))

# the last vote m is of the round r1 or later, and for v1 when of r1
def Safe.after(m: Maybe<&2, Ledgers.Last>, +r1: Nat, v1: Ledgers.Step) -> Bool:
  match m:
    case Some{Ledgers.Last{+t, x}}:
      List.all.if(
        u => List.any.if(u2 => Ledgers.Step.is_eq(x, v1), Bool.not(Nat.is_eq(t, r1))),
        Nat.is_le(r1, t)
      )
    case None{}:
      False{}

# no number is below 0
def Safe.lt_zero(a: Nat) -> {Nat.is_lt(a, 0n) == False{}: Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

# a number at most 0 is 0
def Safe.le_zero_eq(a: Nat) -> {Nat.is_le(a, 0n) == True{}: Bool} -> {a == 0n: Nat}:
  match a:
    case 0n:
      h => {==}
    case 1n+p:
      h => Empty.absurd({1n+p == 0n: Nat}, Shared.Bool.false_ne_true(h))

# a number at most b, and not b, is below b
def Safe.le_ne_lt(a: Nat, b: Nat) -> {Nat.is_le(a, b) == True{}: Bool}
  -> {Nat.is_eq(a, b) == False{}: Bool}
  -> {Nat.is_lt(a, b) == True{}: Bool}:
  match a b:
    case 0n 0n:
      h1 => h2 => Empty.absurd({False{} == True{}: Bool}, Shared.Bool.true_ne_false(h2))
    case 0n 1n+q:
      h1 => h2 => {==}
    case 1n+p 0n:
      h1 => h2 => h1
    case 1n+p 1n+q:
      Safe.le_ne_lt(p, q)

# Safe.mine when the voter cast no vote in the round k, once it is known
# whether k is r1 (eb)
def Safe.mine.none(
  ~mach: Machine(),
  ~d: Led(mach),
  +n: String,
  +l: Led.L(mach, d),
  +c: Ledgers.Line,
  +h: U32,
  +k: Nat,
  +r1: Nat,
  +v1: Ledgers.Step,
  -rest: Maybe<&2, Ledgers.Last>,
  eb: Bool,
  ee: {Nat.is_eq(r1, k) == eb: Bool},
  em: {Led.voted(~mach, ~d, l, Ledgers.Place{c, h, k}, n) == None{}: Maybe<&2, Ledgers.Step>},
  hv: {Led.voted(~mach, ~d, l, Ledgers.Place{c, h, r1}, n) == Some{v1}: Maybe<&2, Ledgers.Step>},
  ih: {Nat.is_eq(r1, k) == False{}: Bool} -> {Safe.after(rest, r1, v1) == True{}: Bool}
) -> {Safe.after(rest, r1, v1) == True{}: Bool}:
  match eb:
    case True{}:
      Empty.absurd(
        {Safe.after(rest, r1, v1) == True{}: Bool},
        Shared.Maybe.none_ne_some(
          Ledgers.Step,
          v1,
          Equal.trans(
            Maybe<&2, Ledgers.Step>,
            None{},
            Led.voted(~mach, ~d, l, Ledgers.Place{c, h, k}, n),
            Some{v1},
            Equal.sym(Maybe<&2, Ledgers.Step>, Led.voted(~mach, ~d, l, Ledgers.Place{c, h, k}, n), None{}, em),
            %Shared.Nat.is_eq_sound(r1, k)(ee): {Led.voted(~mach, ~d, l, Ledgers.Place{c, h, _}, n) == Some{v1}: Maybe<&2, Ledgers.Step>}
            hv
          )
        )
      )
    case False{}:
      ih(ee)

# Safe.mine when the voter cast y in the round k, once it is known whether k
# is r1 (eb)
def Safe.mine.some(
  ~mach: Machine(),
  ~d: Led(mach),
  +n: String,
  +l: Led.L(mach, d),
  +c: Ledgers.Line,
  +h: U32,
  +k: Nat,
  +r1: Nat,
  +v1: Ledgers.Step,
  +y: Ledgers.Step,
  eb: Bool,
  ee: {Nat.is_eq(k, r1) == eb: Bool},
  em: {Led.voted(~mach, ~d, l, Ledgers.Place{c, h, k}, n) == Some{y}: Maybe<&2, Ledgers.Step>},
  hv: {Led.voted(~mach, ~d, l, Ledgers.Place{c, h, r1}, n) == Some{v1}: Maybe<&2, Ledgers.Step>}
) -> {List.any.if(u2 => Ledgers.Step.is_eq(y, v1), Bool.not(eb)) == True{}: Bool}:
  match eb:
    case True{}:
      %Shared.Maybe.some_inj(
        Ledgers.Step,
        y,
        v1,
        Equal.trans(
          Maybe<&2, Ledgers.Step>,
          Some{y},
          Led.voted(~mach, ~d, l, Ledgers.Place{c, h, k}, n),
          Some{v1},
          Equal.sym(Maybe<&2, Ledgers.Step>, Led.voted(~mach, ~d, l, Ledgers.Place{c, h, k}, n), Some{y}, em),
          %Equal.sym(Nat, k, r1, Shared.Nat.is_eq_sound(k, r1)(ee)): {Led.voted(~mach, ~d, l, Ledgers.Place{c, h, _}, n) == Some{v1}: Maybe<&2, Ledgers.Step>}
          hv
        )
      ): {Ledgers.Step.is_eq(y, _) == True{}: Bool}
      Ledgers.Step.is_eq_refl(y)
    case False{}:
      {==}

# Safe.mine once the vote m of the voter in the round k is known
def Safe.mine.at(
  ~mach: Machine(),
  ~d: Led(mach),
  +n: String,
  +l: Led.L(mach, d),
  +c: Ledgers.Line,
  +h: U32,
  +k: Nat,
  +r1: Nat,
  +v1: Ledgers.Step,
  m: Maybe<&2, Ledgers.Step>,
  em: {Led.voted(~mach, ~d, l, Ledgers.Place{c, h, k}, n) == m: Maybe<&2, Ledgers.Step>},
  +hv: {Led.voted(~mach, ~d, l, Ledgers.Place{c, h, r1}, n) == Some{v1}: Maybe<&2, Ledgers.Step>},
  hle: {Nat.is_le(r1, k) == True{}: Bool},
  -rest: Unit -> Maybe<&2, Ledgers.Last>,
  ih: {Nat.is_eq(r1, k) == False{}: Bool} -> {Safe.after(rest(Unit{}), r1, v1) == True{}: Bool}
) -> {Safe.after(Last.or(k, m, rest), r1, v1) == True{}: Bool}:
  match m:
    case Some{+y}:
      Shared.List.all.if_both(
        Nat.is_le(r1, k),
        u => List.any.if(u2 => Ledgers.Step.is_eq(y, v1), Bool.not(Nat.is_eq(k, r1)))
      )(hle)(Safe.mine.some(~mach, ~d, n, l, c, h, k, r1, v1, y, Nat.is_eq(k, r1), {==}, em, hv))
    case None{}:
      Safe.mine.none(~mach, ~d, n, l, c, h, k, r1, v1, rest(Unit{}), Nat.is_eq(r1, k), {==}, em, hv, ih)

# the last vote of a voter up to the round k, when it cast v1 in a round r1
# up to k, is of r1 or later, and for v1 when of r1
def Safe.mine(
  ~mach: Machine(),
  ~d: Led(mach),
  +n: String,
  +l: Led.L(mach, d),
  +c: Ledgers.Line,
  +h: U32,
  k: Nat,
  +r1: Nat,
  +v1: Ledgers.Step
) -> {Led.voted(~mach, ~d, l, Ledgers.Place{c, h, r1}, n) == Some{v1}: Maybe<&2, Ledgers.Step>}
  -> {Nat.is_le(r1, k) == True{}: Bool}
  -> {Safe.after(Last.mine(~mach, ~d, n, l, c, h, k), r1, v1) == True{}: Bool}:
  match k:
    case 0n:
      +hv => +hle => Safe.mine.at(
        ~mach,
        ~d,
        n,
        l,
        c,
        h,
        0n,
        r1,
        v1,
        Led.voted(~mach, ~d, l, Ledgers.Place{c, h, 0n}, n),
        {==},
        hv,
        hle,
        u => None{},
        ne => Empty.absurd(
          {Safe.after(None{}, r1, v1) == True{}: Bool},
          Shared.Bool.true_ne_false(
            %Safe.le_zero_eq(r1)(hle): {Nat.is_eq(_, 0n) == False{}: Bool}
            ne
          )
        )
      )
    case 1n+(+p):
      +hv => +hle => Safe.mine.at(
        ~mach,
        ~d,
        n,
        l,
        c,
        h,
        1n+p,
        r1,
        v1,
        Led.voted(~mach, ~d, l, Ledgers.Place{c, h, 1n+p}, n),
        {==},
        hv,
        hle,
        u => Last.mine(~mach, ~d, n, l, c, h, p),
        ne => Safe.mine(~mach, ~d, n, l, c, h, p, r1, v1)(hv)(Shared.Nat.le_step(r1, p)(hle)(ne))
      )

# the last vote a is of a round at most that of b
def Safe.le(a: Maybe<&2, Ledgers.Last>, b: Maybe<&2, Ledgers.Last>) -> Bool:
  match a b:
    case None{} y:
      True{}
    case Some{x} None{}:
      False{}
    case Some{Ledgers.Last{r1, v1}} Some{Ledgers.Last{r2, v2}}:
      Nat.is_le(r1, r2)

# a last vote is at most the newer of it and another
def Safe.le_newer_left(x: Maybe<&2, Ledgers.Last>, y: Maybe<&2, Ledgers.Last>) -> {
  Safe.le(x, Last.newer(x, y)) == True{}: Bool
}:
  match x y:
    case None{} y:
      {==}
    case Some{Ledgers.Last{+r, v}} None{}:
      Shared.Nat.le_refl(r)
    case Some{Ledgers.Last{+r1, +v1}} Some{Ledgers.Last{+r2, +v2}}:
      Shared.Bool.when_cases(
        Maybe<&2, Ledgers.Last>,
        m => {Safe.le(Some{Ledgers.Last{r1, v1}}, m) == True{}: Bool},
        Nat.is_lt(r1, r2),
        u => Some{Ledgers.Last{r2, v2}},
        u => Some{Ledgers.Last{r1, v1}},
        e => Shared.Nat.lt_weak(r1, r2)(e),
        e => Shared.Nat.le_refl(r1)
      )

# a last vote at most y is at most the newer of x and y
def Safe.le_newer_right(z: Maybe<&2, Ledgers.Last>, x: Maybe<&2, Ledgers.Last>, y: Maybe<&2, Ledgers.Last>) -> {
  Safe.le(z, y) == True{}: Bool
} -> {Safe.le(z, Last.newer(x, y)) == True{}: Bool}:
  match z x y:
    case None{} x y:
      h => {==}
    case Some{q} None{} y:
      h => h
    case Some{q} Some{p} None{}:
      h => Empty.absurd({Safe.le(Some{q}, Some{p}) == True{}: Bool}, Shared.Bool.false_ne_true(h))
    case Some{Ledgers.Last{+rz, vz}} Some{Ledgers.Last{+r1, +v1}} Some{Ledgers.Last{+r2, +v2}}:
      +h => Shared.Bool.when_cases(
        Maybe<&2, Ledgers.Last>,
        m => {Safe.le(Some{Ledgers.Last{rz, vz}}, m) == True{}: Bool},
        Nat.is_lt(r1, r2),
        u => Some{Ledgers.Last{r2, v2}},
        u => Some{Ledgers.Last{r1, v1}},
        e => h,
        e => Shared.Nat.le_trans(rz, r2, r1)(h)(Shared.Nat.nlt_le(r1, r2)(e))
      )

# Safe.meet once the count of voters of from for v is known
def Safe.meet.at(
  ~mach: Machine(),
  ~d: Led(mach),
  +l: Led.L(mach, d),
  +w: Ledgers.Place,
  +os: List<&2, String>,
  +from: List<&2, String>,
  +v: Ledgers.Step,
  y: Nat,
  +ey: {Quorums.Quorum.yes(~Ledgers.Step, ~Ledgers.Step.is_eq, Ledgers.Kind.cells(~Machine.Q(mach), ~Led.kind(mach, d), l, w, from), v) == y: Nat}
) -> {Voters.sub(os, from) == True{}: Bool}
  -> {Voters.major(os, from) == True{}: Bool}
  -> {Quorums.Quorum.has(~Ledgers.Step, ~Ledgers.Step.is_eq, Ledgers.Kind.cells(~Machine.Q(mach), ~Led.kind(mach, d), l, w, os), v) == True{}: Bool}
  -> {Nat.is_lt(0n, Quorums.Quorum.yes(~Ledgers.Step, ~Ledgers.Step.is_eq, Ledgers.Kind.cells(~Machine.Q(mach), ~Led.kind(mach, d), l, w, from), v)) == True{}: Bool}:
  match y:
    case 0n:
      hs => hm => hh => Empty.absurd(
        {Nat.is_lt(0n, Quorums.Quorum.yes(~Ledgers.Step, ~Ledgers.Step.is_eq, Ledgers.Kind.cells(~Machine.Q(mach), ~Led.kind(mach, d), l, w, from), v)) == True{}: Bool},
        Shared.Nat.pigeon(
          List.length(&2, String, from),
          Quorums.Quorum.no(~Ledgers.Step, ~Ledgers.Step.is_eq, Ledgers.Kind.cells(~Machine.Q(mach), ~Led.kind(mach, d), l, w, os), v),
          Quorums.Quorum.yes(~Ledgers.Step, ~Ledgers.Step.is_eq, Ledgers.Kind.cells(~Machine.Q(mach), ~Led.kind(mach, d), l, w, os), v),
          List.length(&2, String, os)
        )(
          %Shared.Nat.add_zero(Quorums.Quorum.no(~Ledgers.Step, ~Ledgers.Step.is_eq, Ledgers.Kind.cells(~Machine.Q(mach), ~Led.kind(mach, d), l, w, os), v)): {
            Nat.is_le(List.length(&2, String, from), _) == True{}: Bool
          }
          %ey: {
            Nat.is_le(List.length(&2, String, from), Nat.add(Quorums.Quorum.no(~Ledgers.Step, ~Ledgers.Step.is_eq, Ledgers.Kind.cells(~Machine.Q(mach), ~Led.kind(mach, d), l, w, os), v), _)) == True{}: Bool
          }
          Safe.sub_count(~mach, ~d, l, w, os, from, v)(hs)
        )(hh)(
          %Equal.sym(
            Nat,
            Nat.add(Quorums.Quorum.yes(~Ledgers.Step, ~Ledgers.Step.is_eq, Ledgers.Kind.cells(~Machine.Q(mach), ~Led.kind(mach, d), l, w, os), v), Quorums.Quorum.no(~Ledgers.Step, ~Ledgers.Step.is_eq, Ledgers.Kind.cells(~Machine.Q(mach), ~Led.kind(mach, d), l, w, os), v)),
            List.length(&2, String, os),
            Safe.yes_no(~mach, ~d, l, w, os, v)
          ): {Nat.is_le(_, List.length(&2, String, os)) == True{}: Bool}
          Shared.Nat.le_refl(List.length(&2, String, os))
        )(hm)
      )
    case 1n+p:
      hs => hm => hh =>
        %Equal.sym(Nat, Quorums.Quorum.yes(~Ledgers.Step, ~Ledgers.Step.is_eq, Ledgers.Kind.cells(~Machine.Q(mach), ~Led.kind(mach, d), l, w, from), v), 1n+p, ey): {Nat.is_lt(0n, _) == True{}: Bool}
        {==}

# a majority of the voters that the rules count meets a majority that cast v:
# some of them cast v
def Safe.meet(
  ~mach: Machine(),
  ~d: Led(mach),
  +l: Led.L(mach, d),
  +w: Ledgers.Place,
  +os: List<&2, String>,
  +from: List<&2, String>,
  +v: Ledgers.Step
) -> {Voters.sub(os, from) == True{}: Bool}
  -> {Voters.major(os, from) == True{}: Bool}
  -> {Quorums.Quorum.has(~Ledgers.Step, ~Ledgers.Step.is_eq, Ledgers.Kind.cells(~Machine.Q(mach), ~Led.kind(mach, d), l, w, os), v) == True{}: Bool}
  -> {Nat.is_lt(0n, Quorums.Quorum.yes(~Ledgers.Step, ~Ledgers.Step.is_eq, Ledgers.Kind.cells(~Machine.Q(mach), ~Led.kind(mach, d), l, w, from), v)) == True{}: Bool}:
  Safe.meet.at(~mach, ~d, l, w, os, from, v, Quorums.Quorum.yes(~Ledgers.Step, ~Ledgers.Step.is_eq, Ledgers.Kind.cells(~Machine.Q(mach), ~Led.kind(mach, d), l, w, from), v), {==})

# a voter of from that cast v1 at w1, whose pass to w2 names y: a last vote
# at most the highest that the passes of from name
def Safe.Met0(
  -mach: Machine(),
  -d: Led(mach),
  -b: Led.L(mach, d),
  -w1: Ledgers.Place,
  -v1: Ledgers.Step,
  -w2: Ledgers.Place,
  -from: List<&2, String>
) -> Type:
  Exists(
    String,
    q => {Led.voted(~mach, ~d, b, w1, q) == Some{v1}: Maybe<&2, Ledgers.Step>}
      & Exists(
        Maybe<&2, Ledgers.Last>,
        y => {Led.passed(~mach, ~d, b, w2, q) == Some{y}: Maybe<&2, Maybe<&2, Ledgers.Last>>}
          & {Safe.le(y, Passes.last(~mach, ~d, b, w2, from)) == True{}: Bool}
      )
  )

# Met0 of a voter of the tail is one of the list
def Safe.pick0.ex(
  ~mach: Machine(),
  ~d: Led(mach),
  +b: Led.L(mach, d),
  +w1: Ledgers.Place,
  +v1: Ledgers.Step,
  +w2: Ledgers.Place,
  +o: String,
  +rest: List<&2, String>,
  -q: String,
  ex: Exists(
    Maybe<&2, Ledgers.Last>,
    y => {Led.passed(~mach, ~d, b, w2, q) == Some{y}: Maybe<&2, Maybe<&2, Ledgers.Last>>}
      & {Safe.le(y, Passes.last(~mach, ~d, b, w2, rest)) == True{}: Bool}
  )
) -> Exists(
    Maybe<&2, Ledgers.Last>,
    y => {Led.passed(~mach, ~d, b, w2, q) == Some{y}: Maybe<&2, Maybe<&2, Ledgers.Last>>}
      & {Safe.le(y, Passes.last(~mach, ~d, b, w2, o <> rest)) == True{}: Bool}
  ):
  match ex:
    case Tuple{+y, Tuple{hp, hl}}:
      Tuple{y, Tuple{hp, Safe.le_newer_right(y, Passed.last(Led.passed(~mach, ~d, b, w2, o)), Passes.last(~mach, ~d, b, w2, rest))(hl)}}

# Met0 of a voter of the tail is one of the list
def Safe.pick0.cons(
  ~mach: Machine(),
  ~d: Led(mach),
  +b: Led.L(mach, d),
  +w1: Ledgers.Place,
  +v1: Ledgers.Step,
  +w2: Ledgers.Place,
  +o: String,
  +rest: List<&2, String>,
  mt: Safe.Met0(mach, d, b, w1, v1, w2, rest)
) -> Safe.Met0(mach, d, b, w1, v1, w2, o <> rest):
  match mt:
    case Tuple{q, Tuple{hv, ex}}:
      Tuple{q, Tuple{hv, Safe.pick0.ex(~mach, ~d, b, w1, v1, w2, o, rest, q, ex)}}

# Met0 of the first voter, once its pass m is known
def Safe.pick0.here(
  ~mach: Machine(),
  ~d: Led(mach),
  +b: Led.L(mach, d),
  +w1: Ledgers.Place,
  +v1: Ledgers.Step,
  +w2: Ledgers.Place,
  +o: String,
  +rest: List<&2, String>,
  m: Maybe<&2, Maybe<&2, Ledgers.Last>>,
  +em: {Led.passed(~mach, ~d, b, w2, o) == m: Maybe<&2, Maybe<&2, Ledgers.Last>>},
  +hv: {Led.voted(~mach, ~d, b, w1, o) == Some{v1}: Maybe<&2, Ledgers.Step>},
  hp: {Passed.all(~mach, ~d, b, w2, o <> rest) == True{}: Bool}
) -> Safe.Met0(mach, d, b, w1, v1, w2, o <> rest):
  match m:
    case None{}:
      Empty.absurd(
        Safe.Met0(mach, d, b, w1, v1, w2, o <> rest),
        Shared.Bool.false_ne_true(
          %em: {Maybe.is_some(&2, Maybe<&2, Ledgers.Last>, _) == True{}: Bool}
          Shared.List.all.if_hit(
            Maybe.is_some(&2, Maybe<&2, Ledgers.Last>, Led.passed(~mach, ~d, b, w2, o)),
            u => Passed.all(~mach, ~d, b, w2, rest)
          )(hp)
        )
      )
    case Some{+y}:
      Tuple{o, Tuple{hv, Tuple{y, Tuple{em, 
        %Equal.sym(Maybe<&2, Maybe<&2, Ledgers.Last>>, Led.passed(~mach, ~d, b, w2, o), Some{y}, em): {
          Safe.le(y, Last.newer(Passed.last(_), Passes.last(~mach, ~d, b, w2, rest))) == True{}: Bool
        }
        Safe.le_newer_left(y, Passes.last(~mach, ~d, b, w2, rest))
      }}}}

# pick0 once it is known whether the first voter cast v1 (hb)
def Safe.pick0.at(
  ~mach: Machine(),
  ~d: Led(mach),
  +b: Led.L(mach, d),
  +w1: Ledgers.Place,
  +v1: Ledgers.Step,
  +w2: Ledgers.Place,
  +o: String,
  +rest: List<&2, String>,
  hb: Bool,
  +eb: {Quorums.Quorum.hit(~Ledgers.Step, ~Ledgers.Step.is_eq, Ledgers.Kind.cell(~Machine.Q(mach), ~Led.kind(mach, d), b, w1, o), v1) == hb: Bool},
  ih: {Nat.is_lt(0n, Quorums.Quorum.yes(~Ledgers.Step, ~Ledgers.Step.is_eq, Ledgers.Kind.cells(~Machine.Q(mach), ~Led.kind(mach, d), b, w1, rest), v1)) == True{}: Bool}
    -> {Passed.all(~mach, ~d, b, w2, rest) == True{}: Bool}
    -> Safe.Met0(mach, d, b, w1, v1, w2, rest)
) -> {Nat.is_lt(0n, Shared.Nat.add_if(hb, Quorums.Quorum.yes(~Ledgers.Step, ~Ledgers.Step.is_eq, Ledgers.Kind.cells(~Machine.Q(mach), ~Led.kind(mach, d), b, w1, rest), v1))) == True{}: Bool}
  -> {Passed.all(~mach, ~d, b, w2, o <> rest) == True{}: Bool}
  -> Safe.Met0(mach, d, b, w1, v1, w2, o <> rest):
  match hb:
    case True{}:
      h => hp => Safe.pick0.here(
        ~mach,
        ~d,
        b,
        w1,
        v1,
        w2,
        o,
        rest,
        Led.passed(~mach, ~d, b, w2, o),
        {==},
        Safe.hit_value(Ledgers.Kind.cell(~Machine.Q(mach), ~Led.kind(mach, d), b, w1, o), v1)(eb),
        hp
      )
    case False{}:
      h => hp => Safe.pick0.cons(
        ~mach,
        ~d,
        b,
        w1,
        v1,
        w2,
        o,
        rest,
        ih(h)(
          Shared.List.all.if_rest(
            Maybe.is_some(&2, Maybe<&2, Ledgers.Last>, Led.passed(~mach, ~d, b, w2, o)),
            u => Passed.all(~mach, ~d, b, w2, rest)
          )(hp)
        )
      )

# some voter of a majority whose passes the rules count cast v1
def Safe.pick0(
  ~mach: Machine(),
  ~d: Led(mach),
  +b: Led.L(mach, d),
  +w1: Ledgers.Place,
  +v1: Ledgers.Step,
  +w2: Ledgers.Place,
  from: List<&2, String>
) -> {Nat.is_lt(0n, Quorums.Quorum.yes(~Ledgers.Step, ~Ledgers.Step.is_eq, Ledgers.Kind.cells(~Machine.Q(mach), ~Led.kind(mach, d), b, w1, from), v1)) == True{}: Bool}
  -> {Passed.all(~mach, ~d, b, w2, from) == True{}: Bool}
  -> Safe.Met0(mach, d, b, w1, v1, w2, from):
  match from:
    case Nil{}:
      h => hp => Empty.absurd(Safe.Met0(mach, d, b, w1, v1, w2, []), Shared.Bool.false_ne_true(h))
    case Con{+o, +rest}:
      Safe.pick0.at(
        ~mach,
        ~d,
        b,
        w1,
        v1,
        w2,
        o,
        rest,
        Quorums.Quorum.hit(~Ledgers.Step, ~Ledgers.Step.is_eq, Ledgers.Kind.cell(~Machine.Q(mach), ~Led.kind(mach, d), b, w1, o), v1),
        {==},
        h => hp => Safe.pick0(~mach, ~d, b, w1, v1, w2, rest)(h)(hp)
      )

# a voter of from that cast v1 at w1, whose pass to w2 names y: a last vote
# that names no other step than v2 in the round t, and is at most the highest
# that the passes of from name
def Safe.Met(
  -mach: Machine(),
  -d: Led(mach),
  -b: Led.L(mach, d),
  -w1: Ledgers.Place,
  -v1: Ledgers.Step,
  -w2: Ledgers.Place,
  -from: List<&2, String>,
  -t: Nat,
  -v2: Ledgers.Step
) -> Type:
  Exists(
    String,
    q => {Led.voted(~mach, ~d, b, w1, q) == Some{v1}: Maybe<&2, Ledgers.Step>}
      & Exists(
        Maybe<&2, Ledgers.Last>,
        y => {Led.passed(~mach, ~d, b, w2, q) == Some{y}: Maybe<&2, Maybe<&2, Ledgers.Last>>}
          & ({Last.allows(y, t, v2) == True{}: Bool} & {Safe.le(y, Passes.last(~mach, ~d, b, w2, from)) == True{}: Bool})
      )
  )

# Met of a voter of the tail is one of the list
def Safe.pick.ex(
  ~mach: Machine(),
  ~d: Led(mach),
  +b: Led.L(mach, d),
  +w1: Ledgers.Place,
  +v1: Ledgers.Step,
  +w2: Ledgers.Place,
  +o: String,
  +rest: List<&2, String>, +t: Nat, +v2: Ledgers.Step,
  -q: String,
  ex: Exists(
    Maybe<&2, Ledgers.Last>,
    y => {Led.passed(~mach, ~d, b, w2, q) == Some{y}: Maybe<&2, Maybe<&2, Ledgers.Last>>}
      & ({Last.allows(y, t, v2) == True{}: Bool} & {Safe.le(y, Passes.last(~mach, ~d, b, w2, rest)) == True{}: Bool})
  )
) -> Exists(
    Maybe<&2, Ledgers.Last>,
    y => {Led.passed(~mach, ~d, b, w2, q) == Some{y}: Maybe<&2, Maybe<&2, Ledgers.Last>>}
      & ({Last.allows(y, t, v2) == True{}: Bool} & {Safe.le(y, Passes.last(~mach, ~d, b, w2, o <> rest)) == True{}: Bool})
  ):
  match ex:
    case Tuple{+y, Tuple{hp, Tuple{ha, hl}}}:
      Tuple{y, Tuple{hp, Tuple{ha, Safe.le_newer_right(y, Passed.last(Led.passed(~mach, ~d, b, w2, o)), Passes.last(~mach, ~d, b, w2, rest))(hl)}}}

# Met of a voter of the tail is one of the list
def Safe.pick.cons(
  ~mach: Machine(),
  ~d: Led(mach),
  +b: Led.L(mach, d),
  +w1: Ledgers.Place,
  +v1: Ledgers.Step,
  +w2: Ledgers.Place,
  +o: String,
  +rest: List<&2, String>, +t: Nat, +v2: Ledgers.Step,
  mt: Safe.Met(mach, d, b, w1, v1, w2, rest, t, v2)
) -> Safe.Met(mach, d, b, w1, v1, w2, o <> rest, t, v2):
  match mt:
    case Tuple{q, Tuple{hv, ex}}:
      Tuple{q, Tuple{hv, Safe.pick.ex(~mach, ~d, b, w1, v1, w2, o, rest, t, v2, q, ex)}}

# Met of the first voter, once its pass m is known
def Safe.pick.here(
  ~mach: Machine(),
  ~d: Led(mach),
  +b: Led.L(mach, d),
  +w1: Ledgers.Place,
  +v1: Ledgers.Step,
  +w2: Ledgers.Place,
  +o: String,
  +rest: List<&2, String>, +t: Nat, +v2: Ledgers.Step,
  m: Maybe<&2, Maybe<&2, Ledgers.Last>>,
  +em: {Led.passed(~mach, ~d, b, w2, o) == m: Maybe<&2, Maybe<&2, Ledgers.Last>>},
  +hv: {Led.voted(~mach, ~d, b, w1, o) == Some{v1}: Maybe<&2, Ledgers.Step>},
  hp: {Passed.all(~mach, ~d, b, w2, o <> rest) == True{}: Bool}, ha: {Passes.agree(~mach, ~d, b, w2, o <> rest, t, v2) == True{}: Bool}
) -> Safe.Met(mach, d, b, w1, v1, w2, o <> rest, t, v2):
  match m:
    case None{}:
      Empty.absurd(
        Safe.Met(mach, d, b, w1, v1, w2, o <> rest, t, v2),
        Shared.Bool.false_ne_true(
          %em: {Maybe.is_some(&2, Maybe<&2, Ledgers.Last>, _) == True{}: Bool}
          Shared.List.all.if_hit(
            Maybe.is_some(&2, Maybe<&2, Ledgers.Last>, Led.passed(~mach, ~d, b, w2, o)),
            u => Passed.all(~mach, ~d, b, w2, rest)
          )(hp)
        )
      )
    case Some{+y}:
      Tuple{o, Tuple{hv, Tuple{y, Tuple{em, Tuple{
          %em: {Last.allows(Passed.last(_), t, v2) == True{}: Bool}
          Shared.List.all.if_hit(
            Last.allows(Passed.last(Led.passed(~mach, ~d, b, w2, o)), t, v2),
            u => Passes.agree(~mach, ~d, b, w2, rest, t, v2)
          )(ha),
          %Equal.sym(Maybe<&2, Maybe<&2, Ledgers.Last>>, Led.passed(~mach, ~d, b, w2, o), Some{y}, em): {
            Safe.le(y, Last.newer(Passed.last(_), Passes.last(~mach, ~d, b, w2, rest))) == True{}: Bool
          }
          Safe.le_newer_left(y, Passes.last(~mach, ~d, b, w2, rest))
        }}}}}

# pick once it is known whether the first voter cast v1 (hb)
def Safe.pick.at(
  ~mach: Machine(),
  ~d: Led(mach),
  +b: Led.L(mach, d),
  +w1: Ledgers.Place,
  +v1: Ledgers.Step,
  +w2: Ledgers.Place,
  +o: String,
  +rest: List<&2, String>, +t: Nat, +v2: Ledgers.Step,
  hb: Bool,
  +eb: {Quorums.Quorum.hit(~Ledgers.Step, ~Ledgers.Step.is_eq, Ledgers.Kind.cell(~Machine.Q(mach), ~Led.kind(mach, d), b, w1, o), v1) == hb: Bool},
  ih: {Nat.is_lt(0n, Quorums.Quorum.yes(~Ledgers.Step, ~Ledgers.Step.is_eq, Ledgers.Kind.cells(~Machine.Q(mach), ~Led.kind(mach, d), b, w1, rest), v1)) == True{}: Bool}
    -> {Passed.all(~mach, ~d, b, w2, rest) == True{}: Bool}
    -> {Passes.agree(~mach, ~d, b, w2, rest, t, v2) == True{}: Bool}
    -> Safe.Met(mach, d, b, w1, v1, w2, rest, t, v2)
) -> {Nat.is_lt(0n, Shared.Nat.add_if(hb, Quorums.Quorum.yes(~Ledgers.Step, ~Ledgers.Step.is_eq, Ledgers.Kind.cells(~Machine.Q(mach), ~Led.kind(mach, d), b, w1, rest), v1))) == True{}: Bool}
  -> {Passed.all(~mach, ~d, b, w2, o <> rest) == True{}: Bool}
  -> {Passes.agree(~mach, ~d, b, w2, o <> rest, t, v2) == True{}: Bool}
  -> Safe.Met(mach, d, b, w1, v1, w2, o <> rest, t, v2):
  match hb:
    case True{}:
      h => hp => ha => Safe.pick.here(
        ~mach,
        ~d,
        b,
        w1,
        v1,
        w2,
        o,
        rest, t, v2,
        Led.passed(~mach, ~d, b, w2, o),
        {==},
        Safe.hit_value(Ledgers.Kind.cell(~Machine.Q(mach), ~Led.kind(mach, d), b, w1, o), v1)(eb),
        hp, ha
      )
    case False{}:
      h => hp => ha => Safe.pick.cons(
        ~mach,
        ~d,
        b,
        w1,
        v1,
        w2,
        o,
        rest, t, v2,
        ih(h)(
          Shared.List.all.if_rest(
            Maybe.is_some(&2, Maybe<&2, Ledgers.Last>, Led.passed(~mach, ~d, b, w2, o)),
            u => Passed.all(~mach, ~d, b, w2, rest)
          )(hp)
        )(
          Shared.List.all.if_rest(
            Last.allows(Passed.last(Led.passed(~mach, ~d, b, w2, o)), t, v2),
            u => Passes.agree(~mach, ~d, b, w2, rest, t, v2)
          )(ha)
        )
      )

# some voter of a majority whose passes the rules count cast v1
def Safe.pick(
  ~mach: Machine(),
  ~d: Led(mach),
  +b: Led.L(mach, d),
  +w1: Ledgers.Place,
  +v1: Ledgers.Step,
  +w2: Ledgers.Place,
  from: List<&2, String>, +t: Nat, +v2: Ledgers.Step
) -> {Nat.is_lt(0n, Quorums.Quorum.yes(~Ledgers.Step, ~Ledgers.Step.is_eq, Ledgers.Kind.cells(~Machine.Q(mach), ~Led.kind(mach, d), b, w1, from), v1)) == True{}: Bool}
  -> {Passed.all(~mach, ~d, b, w2, from) == True{}: Bool}
  -> {Passes.agree(~mach, ~d, b, w2, from, t, v2) == True{}: Bool}
  -> Safe.Met(mach, d, b, w1, v1, w2, from, t, v2):
  match from:
    case Nil{}:
      h => hp => ha => Empty.absurd(Safe.Met(mach, d, b, w1, v1, w2, [], t, v2), Shared.Bool.false_ne_true(h))
    case Con{+o, +rest}:
      Safe.pick.at(
        ~mach,
        ~d,
        b,
        w1,
        v1,
        w2,
        o,
        rest, t, v2,
        Quorums.Quorum.hit(~Ledgers.Step, ~Ledgers.Step.is_eq, Ledgers.Kind.cell(~Machine.Q(mach), ~Led.kind(mach, d), b, w1, o), v1),
        {==},
        h => hp => ha => Safe.pick(~mach, ~d, b, w1, v1, w2, rest, t, v2)(h)(hp)(ha)
      )

# a last vote of the round r1 or later is not none
def Safe.after_none(y: Maybe<&2, Ledgers.Last>, +r1: Nat, v1: Ledgers.Step) -> {Safe.after(y, r1, v1) == True{}: Bool}
  -> {Safe.le(y, None{}) == True{}: Bool}
  -> Empty:
  match y:
    case None{}:
      h1 => h2 => Shared.Bool.false_ne_true(h1)
    case Some{Ledgers.Last{t, w}}:
      h1 => h2 => Shared.Bool.false_ne_true(h2)

# the pass to the round 1 + p of a voter that cast v1 in the round r1 below it
# names a vote of r1 or later, and v1 when of r1
def Safe.round_safe.after(
  ~mach: Machine(),
  ~d: Led(mach),
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
  +r1: Nat,
  +v1: Ledgers.Step,
  +p: Nat,
  +q: String,
  +y: Maybe<&2, Ledgers.Last>,
  hp: {Led.passed(~mach, ~d, b, Ledgers.Place{c, h, 1n+p}, q) == Some{y}: Maybe<&2, Maybe<&2, Ledgers.Last>>},
  hv: {Led.voted(~mach, ~d, b, Ledgers.Place{c, h, r1}, q) == Some{v1}: Maybe<&2, Ledgers.Step>},
  hl: {Nat.is_lt(r1, 1n+p) == True{}: Bool}
) -> {Safe.after(y, r1, v1) == True{}: Bool}:
  %Equal.sym(
    Maybe<&2, Ledgers.Last>,
    y,
    Last.below(~mach, ~d, q, b, c, h, 1n+p),
    ll(a)(b)(c)(h)(later)(1n+p)(q)(y)(hp)
  ): {Safe.after(_, r1, v1) == True{}: Bool}
  Safe.mine(~mach, ~d, q, b, c, h, p, r1, v1)(hv)(Shared.Nat.lt_succ_le(r1, p)(hl))

# when the passes name no vote, the voter that two majorities share is a
# contradiction, once its pass is known
def Safe.round_safe.none2(
  ~mach: Machine(),
  ~d: Led(mach),
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
  +r1: Nat,
  +v1: Ledgers.Step,
  +p: Nat,
  +from: List<&2, String>,
  eM: {Passes.last(~mach, ~d, b, Ledgers.Place{c, h, 1n+p}, from) == None{}: Maybe<&2, Ledgers.Last>},
  hl: {Nat.is_lt(r1, 1n+p) == True{}: Bool},
  +q: String,
  hv: {Led.voted(~mach, ~d, b, Ledgers.Place{c, h, r1}, q) == Some{v1}: Maybe<&2, Ledgers.Step>},
  ex: Exists(
    Maybe<&2, Ledgers.Last>,
    y => {Led.passed(~mach, ~d, b, Ledgers.Place{c, h, 1n+p}, q) == Some{y}: Maybe<&2, Maybe<&2, Ledgers.Last>>}
      & {Safe.le(y, Passes.last(~mach, ~d, b, Ledgers.Place{c, h, 1n+p}, from)) == True{}: Bool}
  )
) -> Empty:
  match ex:
    case Tuple{+y, Tuple{hp, hle}}:
      Safe.after_none(y, r1, v1)(Safe.round_safe.after(~mach, ~d, ~ll, a, b, later, c, h, r1, v1, p, q, y, hp, hv, hl))(
        %eM: {Safe.le(y, _) == True{}: Bool}
        hle
      )

# when the passes name no vote, the voter that two majorities share is a
# contradiction
def Safe.round_safe.none(
  ~mach: Machine(),
  ~d: Led(mach),
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
  +r1: Nat,
  +v1: Ledgers.Step,
  +p: Nat,
  +from: List<&2, String>,
  eM: {Passes.last(~mach, ~d, b, Ledgers.Place{c, h, 1n+p}, from) == None{}: Maybe<&2, Ledgers.Last>},
  hl: {Nat.is_lt(r1, 1n+p) == True{}: Bool},
  mt: Safe.Met0(mach, d, b, Ledgers.Place{c, h, r1}, v1, Ledgers.Place{c, h, 1n+p}, from)
) -> Empty:
  match mt:
    case Tuple{+q, Tuple{hv, ex}}:
      Safe.round_safe.none2(~mach, ~d, ~ll, a, b, later, c, h, r1, v1, p, from, eM, hl, q, hv, ex)

# Safe.round_safe in the case of a later round t of the passes, once the act of
# the first voter whose pass names t is known
def Safe.round_safe.act(
  ~mach: Machine(),
  ~d: Led(mach),
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
  +r1: Nat,
  +v1: Ledgers.Step,
  +j: Nat,
  +p: Nat,
  +v2: Ledgers.Step,
  +from: List<&2, String>,
  +t: Nat,
  m: Maybe<&2, Ledgers.Cast>,
  cs: {Cast.casts(m, v2, +f => Step.allowed.in(~mach, ~d, b, c, h, os, v2, j, t, f)) == True{}: Bool},
  lt: {Nat.is_lt(r1, t) == True{}: Bool},
  ih: @t: Nat -> @f: List<&2, String> -> {Nat.is_lt(r1, t) == True{}: Bool}
    -> {Step.allowed.in(~mach, ~d, b, c, h, os, v2, j, t, f) == True{}: Bool}
    -> {v2 == v1: Ledgers.Step}
) -> {v2 == v1: Ledgers.Step}:
  match m:
    case Some{Ledgers.Cast.Vote{x, +f}}:
      ih(t)(f)(lt)(Shared.List.all.if_rest(Ledgers.Step.is_eq(x, v2), u => Step.allowed.in(~mach, ~d, b, c, h, os, v2, j, t, f))(cs))
    case Some{Ledgers.Cast.Pass{q}}:
      Empty.absurd({v2 == v1: Ledgers.Step}, Shared.Bool.false_ne_true(cs))
    case None{}:
      Empty.absurd({v2 == v1: Ledgers.Step}, Shared.Bool.false_ne_true(cs))

# Safe.round_safe once the last vote tq, xq of the shared voter is known, and
# whether the highest round t that the passes name is r1 (eb)
def Safe.round_safe.cmp(
  ~mach: Machine(),
  ~d: Led(mach),
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
  +r1: Nat,
  +v1: Ledgers.Step,
  +j: Nat,
  +p: Nat,
  +v2: Ledgers.Step,
  +from: List<&2, String>,
  +t: Nat,
  +tq: Nat,
  +xq: Ledgers.Step,
  eb: Bool,
  +ee: {Nat.is_eq(t, r1) == eb: Bool},
  +aft: {
    List.all.if(
      u => List.any.if(u2 => Ledgers.Step.is_eq(xq, v1), Bool.not(Nat.is_eq(tq, r1))),
      Nat.is_le(r1, tq)
    )
      == True{}: Bool
  },
  ha: {List.any.if(u => Ledgers.Step.is_eq(xq, v2), Bool.not(Nat.is_eq(tq, t))) == True{}: Bool},
  +hle: {Nat.is_le(tq, t) == True{}: Bool},
  cs: {Cast.casts(Passes.act(~mach, ~d, b, c, h, 1n+p, from, t), v2, +f => Step.allowed.in(~mach, ~d, b, c, h, os, v2, j, t, f)) == True{}: Bool},
  ih: @t: Nat -> @f: List<&2, String> -> {Nat.is_lt(r1, t) == True{}: Bool}
    -> {Step.allowed.in(~mach, ~d, b, c, h, os, v2, j, t, f) == True{}: Bool}
    -> {v2 == v1: Ledgers.Step}
) -> {v2 == v1: Ledgers.Step}:
  match eb:
    case True{}:
      +etr = Shared.Nat.is_eq_sound(t, r1)(ee)
      +hr1 = Shared.List.all.if_hit(
        Nat.is_le(r1, tq),
        u => List.any.if(u2 => Ledgers.Step.is_eq(xq, v1), Bool.not(Nat.is_eq(tq, r1)))
      )(aft)
      +eq1 = Equal.trans(
        Bool,
        Nat.is_eq(tq, r1),
        Bool.and(Nat.is_le(tq, r1), Nat.is_le(r1, tq)),
        True{},
        Equal.sym(Bool, Bool.and(Nat.is_le(tq, r1), Nat.is_le(r1, tq)), Nat.is_eq(tq, r1), Shared.Nat.le_both(tq, r1)),
        Shared.Bool.and_both(Nat.is_le(tq, r1), Nat.is_le(r1, tq))(
          %etr: {Nat.is_le(tq, _) == True{}: Bool}
          hle
        )(hr1)
      )
      Equal.trans(
        Ledgers.Step,
        v2,
        xq,
        v1,
        Equal.sym(
          Ledgers.Step,
          xq,
          v2,
          Ledgers.Step.is_eq_sound(
            xq,
            v2
          )(
            %eq1: {List.any.if(u => Ledgers.Step.is_eq(xq, v2), Bool.not(_)) == True{}: Bool}
            %etr: {List.any.if(u => Ledgers.Step.is_eq(xq, v2), Bool.not(Nat.is_eq(tq, _))) == True{}: Bool}
            ha
          )
        ),
        Ledgers.Step.is_eq_sound(
          xq,
          v1
        )(
          %eq1: {List.any.if(u2 => Ledgers.Step.is_eq(xq, v1), Bool.not(_)) == True{}: Bool}
          Shared.List.all.if_rest(
            Nat.is_le(r1, tq),
            u => List.any.if(u2 => Ledgers.Step.is_eq(xq, v1), Bool.not(Nat.is_eq(tq, r1)))
          )(aft)
        )
      )
    case False{}:
      Safe.round_safe.act(
        ~mach, ~d, ~ll, a, b, later, c, h, os, r1, v1, j, p, v2, from,
        t,
        Passes.act(~mach, ~d, b, c, h, 1n+p, from, t),
        cs,
        Safe.le_ne_lt(
          r1,
          t
        )(
          Shared.Nat.le_trans(r1, tq, t)(
            Shared.List.all.if_hit(
              Nat.is_le(r1, tq),
              u => List.any.if(u2 => Ledgers.Step.is_eq(xq, v1), Bool.not(Nat.is_eq(tq, r1)))
            )(aft)
          )(hle)
        )(Equal.trans(Bool, Nat.is_eq(r1, t), Nat.is_eq(t, r1), False{}, Shared.Nat.is_eq_comm(r1, t), ee)),
        ih
      )

# Safe.round_safe once the last vote y of the shared voter is known
def Safe.round_safe.y(
  ~mach: Machine(),
  ~d: Led(mach),
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
  +r1: Nat,
  +v1: Ledgers.Step,
  +j: Nat,
  +p: Nat,
  +v2: Ledgers.Step,
  +from: List<&2, String>,
  +t: Nat,
  -x: Ledgers.Step,
  y: Maybe<&2, Ledgers.Last>,
  aft: {Safe.after(y, r1, v1) == True{}: Bool},
  ha: {Last.allows(y, t, v2) == True{}: Bool},
  hle: {Safe.le(y, Some{Ledgers.Last{t, x}}) == True{}: Bool},
  cs: {Cast.casts(Passes.act(~mach, ~d, b, c, h, 1n+p, from, t), v2, +f => Step.allowed.in(~mach, ~d, b, c, h, os, v2, j, t, f)) == True{}: Bool},
  ih: @t: Nat -> @f: List<&2, String> -> {Nat.is_lt(r1, t) == True{}: Bool}
    -> {Step.allowed.in(~mach, ~d, b, c, h, os, v2, j, t, f) == True{}: Bool}
    -> {v2 == v1: Ledgers.Step}
) -> {v2 == v1: Ledgers.Step}:
  match y:
    case None{}:
      Empty.absurd({v2 == v1: Ledgers.Step}, Shared.Bool.false_ne_true(aft))
    case Some{Ledgers.Last{+tq, +xq}}:
      Safe.round_safe.cmp(~mach, ~d, ~ll, a, b, later, c, h, os, r1, v1, j, p, v2, from, t, tq, xq, Nat.is_eq(t, r1), {==}, aft, ha, hle, cs, ih)

# Safe.round_safe once the pass of the shared voter is known
def Safe.round_safe.some2(
  ~mach: Machine(),
  ~d: Led(mach),
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
  +r1: Nat,
  +v1: Ledgers.Step,
  +j: Nat,
  +p: Nat,
  +v2: Ledgers.Step,
  +from: List<&2, String>,
  +t: Nat,
  -x: Ledgers.Step,
  eM: {Passes.last(~mach, ~d, b, Ledgers.Place{c, h, 1n+p}, from) == Some{Ledgers.Last{t, x}}: Maybe<&2, Ledgers.Last>},
  hl: {Nat.is_lt(r1, 1n+p) == True{}: Bool},
  cs: {Cast.casts(Passes.act(~mach, ~d, b, c, h, 1n+p, from, t), v2, +f => Step.allowed.in(~mach, ~d, b, c, h, os, v2, j, t, f)) == True{}: Bool},
  ih: @t: Nat -> @f: List<&2, String> -> {Nat.is_lt(r1, t) == True{}: Bool}
    -> {Step.allowed.in(~mach, ~d, b, c, h, os, v2, j, t, f) == True{}: Bool}
    -> {v2 == v1: Ledgers.Step},
  +q: String,
  hv: {Led.voted(~mach, ~d, b, Ledgers.Place{c, h, r1}, q) == Some{v1}: Maybe<&2, Ledgers.Step>},
  ex: Exists(
    Maybe<&2, Ledgers.Last>,
    y => {Led.passed(~mach, ~d, b, Ledgers.Place{c, h, 1n+p}, q) == Some{y}: Maybe<&2, Maybe<&2, Ledgers.Last>>}
      & ({Last.allows(y, t, v2) == True{}: Bool} & {Safe.le(y, Passes.last(~mach, ~d, b, Ledgers.Place{c, h, 1n+p}, from)) == True{}: Bool})
  )
) -> {v2 == v1: Ledgers.Step}:
  match ex:
    case Tuple{+y, Tuple{hp, Tuple{ha, hle}}}:
      Safe.round_safe.y(
        ~mach, ~d, ~ll, a, b, later, c, h, os, r1, v1, j, p, v2, from,
        t,
        x,
        y,
        Safe.round_safe.after(~mach, ~d, ~ll, a, b, later, c, h, r1, v1, p, q, y, hp, hv, hl),
        ha,
        %eM: {Safe.le(y, _) == True{}: Bool}
        hle,
        cs,
        ih
      )

# Safe.round_safe once the voter that two majorities share is known
def Safe.round_safe.some(
  ~mach: Machine(),
  ~d: Led(mach),
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
  +r1: Nat,
  +v1: Ledgers.Step,
  +j: Nat,
  +p: Nat,
  +v2: Ledgers.Step,
  +from: List<&2, String>,
  +t: Nat,
  -x: Ledgers.Step,
  eM: {Passes.last(~mach, ~d, b, Ledgers.Place{c, h, 1n+p}, from) == Some{Ledgers.Last{t, x}}: Maybe<&2, Ledgers.Last>},
  hl: {Nat.is_lt(r1, 1n+p) == True{}: Bool},
  cs: {Cast.casts(Passes.act(~mach, ~d, b, c, h, 1n+p, from, t), v2, +f => Step.allowed.in(~mach, ~d, b, c, h, os, v2, j, t, f)) == True{}: Bool},
  ih: @t: Nat -> @f: List<&2, String> -> {Nat.is_lt(r1, t) == True{}: Bool}
    -> {Step.allowed.in(~mach, ~d, b, c, h, os, v2, j, t, f) == True{}: Bool}
    -> {v2 == v1: Ledgers.Step},
  mt: Safe.Met(mach, d, b, Ledgers.Place{c, h, r1}, v1, Ledgers.Place{c, h, 1n+p}, from, t, v2)
) -> {v2 == v1: Ledgers.Step}:
  match mt:
    case Tuple{+q, Tuple{hv, ex}}:
      Safe.round_safe.some2(~mach, ~d, ~ll, a, b, later, c, h, os, r1, v1, j, p, v2, from, t, x, eM, hl, cs, ih, q, hv, ex)

# Safe.round_safe once the highest last vote M that the passes name is known
def Safe.round_safe.at(
  ~mach: Machine(),
  ~d: Led(mach),
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
  +r1: Nat,
  +v1: Ledgers.Step,
  +j: Nat,
  +p: Nat,
  +v2: Ledgers.Step,
  +from: List<&2, String>,
  M: Maybe<&2, Ledgers.Last>,
  eM: {Passes.last(~mach, ~d, b, Ledgers.Place{c, h, 1n+p}, from) == M: Maybe<&2, Ledgers.Last>},
  lh: {Last.holds(M, +t => List.all.if(u2 => Cast.casts(Passes.act(~mach, ~d, b, c, h, 1n+p, from, t), v2, +f => Step.allowed.in(~mach, ~d, b, c, h, os, v2, j, t, f)), Passes.agree(~mach, ~d, b, Ledgers.Place{c, h, 1n+p}, from, t, v2))) == True{}: Bool},
  +pall: {Passed.all(~mach, ~d, b, Ledgers.Place{c, h, 1n+p}, from) == True{}: Bool},
  +meet: {
    Nat.is_lt(0n, Quorums.Quorum.yes(~Ledgers.Step, ~Ledgers.Step.is_eq, Ledgers.Kind.cells(~Machine.Q(mach), ~Led.kind(mach, d), b, Ledgers.Place{c, h, r1}, from), v1)) == True{}: Bool
  },
  hl: {Nat.is_lt(r1, 1n+p) == True{}: Bool},
  ih: @t: Nat -> @f: List<&2, String> -> {Nat.is_lt(r1, t) == True{}: Bool}
    -> {Step.allowed.in(~mach, ~d, b, c, h, os, v2, j, t, f) == True{}: Bool}
    -> {v2 == v1: Ledgers.Step}
) -> {v2 == v1: Ledgers.Step}:
  match M:
    case None{}:
      Empty.absurd(
        {v2 == v1: Ledgers.Step},
        Safe.round_safe.none(
          ~mach,
          ~d,
          ~ll,
          a,
          b,
          later,
          c,
          h,
          r1,
          v1,
          p,
          from,
          eM,
          hl,
          Safe.pick0(~mach, ~d, b, Ledgers.Place{c, h, r1}, v1, Ledgers.Place{c, h, 1n+p}, from)(meet)(pall)
        )
      )
    case Some{Ledgers.Last{+t, x}}:
      +lh2 = {lh : {List.all.if(u2 => Cast.casts(Passes.act(~mach, ~d, b, c, h, 1n+p, from, t), v2, +f => Step.allowed.in(~mach, ~d, b, c, h, os, v2, j, t, f)), Passes.agree(~mach, ~d, b, Ledgers.Place{c, h, 1n+p}, from, t, v2)) == True{}: Bool}}
      Safe.round_safe.some(
        ~mach, ~d, ~ll, a, b, later, c, h, os, r1, v1, j, p, v2, from,
        t,
        x,
        eM,
        hl,
        Shared.List.all.if_rest(Passes.agree(~mach, ~d, b, Ledgers.Place{c, h, 1n+p}, from, t, v2), u2 => Cast.casts(Passes.act(~mach, ~d, b, c, h, 1n+p, from, t), v2, +f => Step.allowed.in(~mach, ~d, b, c, h, os, v2, j, t, f)))(lh2),
        ih,
        Safe.pick(~mach, ~d, b, Ledgers.Place{c, h, r1}, v1, Ledgers.Place{c, h, 1n+p}, from, t, v2)(meet)(pall)(
          Shared.List.all.if_hit(Passes.agree(~mach, ~d, b, Ledgers.Place{c, h, 1n+p}, from, t, v2), u2 => Cast.casts(Passes.act(~mach, ~d, b, c, h, 1n+p, from, t), v2, +f => Step.allowed.in(~mach, ~d, b, c, h, os, v2, j, t, f)))(lh2)
        )
      )

# safety of rounds: when a majority cast v1 in the round r1, a later round
# allows no other step than v1. The passes of a majority meet that majority
# in a voter whose pass names a vote of r1 or later; the highest round t that
# the passes name is r1, where they name v1, or later, where v2 was allowed
# by the same argument
def Safe.round_safe(
  ~mach: Machine(),
  ~d: Led(mach),
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
  +r1: Nat,
  +v1: Ledgers.Step,
  k: Nat,
  r2: Nat,
  +v2: Ledgers.Step,
  +from: List<&2, String>
) -> {Quorums.Quorum.has(~Ledgers.Step, ~Ledgers.Step.is_eq, Ledgers.Kind.cells(~Machine.Q(mach), ~Led.kind(mach, d), b, Ledgers.Place{c, h, r1}, os), v1) == True{}: Bool}
  -> {Nat.is_lt(r1, r2) == True{}: Bool}
  -> {Step.allowed.in(~mach, ~d, b, c, h, os, v2, k, r2, from) == True{}: Bool}
  -> {v2 == v1: Ledgers.Step}:
  match k r2:
    case 0n 0n:
      hq => hl => e => Empty.absurd(
        {v2 == v1: Ledgers.Step},
        Shared.Bool.false_ne_true(
          Equal.trans(Bool, False{}, Nat.is_lt(r1, 0n), True{}, Equal.sym(Bool, Nat.is_lt(r1, 0n), False{}, Safe.lt_zero(r1)), hl)
        )
      )
    case 1n+j 0n:
      hq => hl => e => Empty.absurd(
        {v2 == v1: Ledgers.Step},
        Shared.Bool.false_ne_true(
          Equal.trans(Bool, False{}, Nat.is_lt(r1, 0n), True{}, Equal.sym(Bool, Nat.is_lt(r1, 0n), False{}, Safe.lt_zero(r1)), hl)
        )
      )
    case 0n 1n+p:
      hq => hl => e => Empty.absurd({v2 == v1: Ledgers.Step}, Shared.Bool.false_ne_true(e))
    case 1n+(+j) 1n+(+p):
      +hq => +hl => +e =>
        +pm = Shared.List.all.if_hit(
          Passed.major(~mach, ~d, b, Ledgers.Place{c, h, 1n+p}, os, from),
          u => Last.holds(Passes.last(~mach, ~d, b, Ledgers.Place{c, h, 1n+p}, from), +t => List.all.if(u2 => Cast.casts(Passes.act(~mach, ~d, b, c, h, 1n+p, from, t), v2, +f => Step.allowed.in(~mach, ~d, b, c, h, os, v2, j, t, f)), Passes.agree(~mach, ~d, b, Ledgers.Place{c, h, 1n+p}, from, t, v2)))
        )(e)
        +prs = Shared.List.all.if_rest(
          Passed.all(~mach, ~d, b, Ledgers.Place{c, h, 1n+p}, from),
          u => List.all.if(u2 => Voters.major(os, from), Voters.sub(os, from))
        )(pm)
        Safe.round_safe.at(
          ~mach, ~d, ~ll, a, b, later, c, h, os, r1, v1, j, p, v2, from,
          Passes.last(~mach, ~d, b, Ledgers.Place{c, h, 1n+p}, from),
          {==},
          Shared.List.all.if_rest(
            Passed.major(~mach, ~d, b, Ledgers.Place{c, h, 1n+p}, os, from),
            u => Last.holds(Passes.last(~mach, ~d, b, Ledgers.Place{c, h, 1n+p}, from), +t => List.all.if(u2 => Cast.casts(Passes.act(~mach, ~d, b, c, h, 1n+p, from, t), v2, +f => Step.allowed.in(~mach, ~d, b, c, h, os, v2, j, t, f)), Passes.agree(~mach, ~d, b, Ledgers.Place{c, h, 1n+p}, from, t, v2)))
          )(e),
          Shared.List.all.if_hit(
            Passed.all(~mach, ~d, b, Ledgers.Place{c, h, 1n+p}, from),
            u => List.all.if(u2 => Voters.major(os, from), Voters.sub(os, from))
          )(pm),
          Safe.meet(~mach, ~d, b, Ledgers.Place{c, h, r1}, os, from, v1)(
            Shared.List.all.if_hit(Voters.sub(os, from), u2 => Voters.major(os, from))(prs)
          )(Shared.List.all.if_rest(Voters.sub(os, from), u2 => Voters.major(os, from))(prs))(hq),
          hl,
          t => f => hlt => ha => Safe.round_safe(~mach, ~d, ~ll, a, b, later, c, h, os, r1, v1, j, t, v2, f)(hq)(hlt)(ha)
        )

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
  ?TODO

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
