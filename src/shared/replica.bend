import Base
import ./shared/ledger.bend as Ledgers
import ./shared/shared/depot.bend as Depots
import ./shared/shared/quorum.bend as Quorums
import ./shared/shared/shared/cell.bend as Cells
import ./shared/shared/shared/code.bend as Codes
import ./shared/shared/shared/hash.bend as Hashes
import ./shared/shared/shared/seal.bend as Seals
import ./shared/shared/shared/shared.bend as Shared
import ./shared/shared/text.bend as Texts
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
    a => b => Ledgers.Kind.grows(
      ~Machine.Q(mach),
      ~Machine.code(mach),
      ~Ledgers.Ledger.kind(Machine.Q(mach), Machine.code(mach), x),
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
        a => b => Ledgers.Kind.grows(
          ~Machine.Q(mach),
          ~Machine.code(mach),
          ~Ledgers.Ledger.kind(Machine.Q(mach), Machine.code(mach), x),
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
def Led.Grows(-mach: Machine(), -d: Led(mach), -a: Led.L(mach, d), -b: Led.L(mach, d)) -> Data:
  {Ledgers.Kind.grows(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), a, b) == True{}: Bool}

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

# the request taken x is i
def Taken.is_of(m: Maybe<&2, Taken>, +i: Ledgers.Id) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{Taken{j, r}}:
      Ledgers.Id.is_eq(j, i)

# the number that the outcome o of the request i names at the tip t, when the
# line took i there, below its count
def Out.number(~mach: Machine(), ~d: Led(mach), +l: Led.L(mach, d), +t: Tip, +i: Ledgers.Id, o: Out) -> Maybe<&2, U32>:
  match o:
    case Out.Stale{a}:
      None{}
    case Out.Taken{a, +m}:
      Shared.Maybe.when(
        U32,
        Bool.and(U32.is_lt(m, Tip.count(t)), Taken.is_of(Tip.taken(~mach, ~d, l, t, m), i)),
        u => Some{m}
      )

# the number of the request i at the tip t: the number that its outcome names,
# when the request taken there is i, below the count (none: else, or l lacks
# a node). The one reading of a log by ID and by number, so both agree
def Tip.number(~mach: Machine(), ~d: Led(mach), +l: Led.L(mach, d), +t: Tip, +i: Ledgers.Id) -> Maybe<&2, U32>:
  Maybe.bind(&2, Out, U32, Tip.out(~mach, ~d, l, t, i), o => Out.number(~mach, ~d, l, t, i, o))

# the root of the content of the version of the request i, at the tip t of
# its line (none: the line did not take it, or l lacks a node)
def Tip.version(
  ~mach: Machine(),
  ~d: Led(mach),
  +l: Led.L(mach, d),
  +t: Tip,
  +i: Ledgers.Id
) -> Maybe<&2, Maybe<&2, Hashes.Hash>>:
  Maybe.bind(
    &2,
    U32,
    Maybe<&2, Hashes.Hash>,
    Tip.number(~mach, ~d, l, t, i),
    m => Maybe.bind(&2, Taken, Maybe<&2, Hashes.Hash>, Tip.taken(~mach, ~d, l, t, m), x => Some{Taken.root(x)})
  )

# the IDs of the taken requests xs
def Taken.ids(xs: List<&2, Taken>) -> List<&2, Ledgers.Id>:
  match xs:
    case Nil{}:
      []
    case Con{Taken{i, r}, rest}:
      i <> Taken.ids(rest)

# the taken request that a known read m gives, before what rest gives (none:
# the read cannot tell, or the log lacks a request that its count names)
def Taken.con(
  m: Maybe<&2, Maybe<&2, Taken>>,
  rest: Unit -> Maybe<&2, List<&2, Taken>>
) -> Maybe<&2, List<&2, Taken>>:
  match m:
    case None{}:
      None{}
    case Some{None{}}:
      None{}
    case Some{Some{x}}:
      Maybe.map(&2, List<&2, Taken>, List<&2, Taken>, r => x <> r, rest(Unit{}))

# k versions from the number n, in order, at the tip t; fewer when the line
# took fewer than its count names (none: l lacks a node of the log, so a read
# cannot tell)
def Tip.versions(~mach: Machine(),
  ~d: Led(mach), k: Nat, +l: Led.L(mach, d), +t: Tip, +n: U32) -> Maybe<&2, List<&2, Taken>>:
  match k:
    case 0n:
      Some{[]}
    case 1n+p:
      Shared.Bool.when(
        Maybe<&2, List<&2, Taken>>,
        U32.is_lt(n, Tip.count(t)),
        u => Taken.con(
          Tip.known(~Taken, ~Taken.code, ~Taken.code.read, Tip.find(~mach, ~d, l, t, Log.taken(n))),
          u2 => Tip.versions(~mach, ~d, p, l, t, U32.inc(n))
        ),
        u => Some{[]}
      )

# the ID of the newest version at the tip t, or that there is none yet (none:
# l lacks a node of the log)
def Tip.newest(~mach: Machine(),
  ~d: Led(mach), l: Led.L(mach, d), +t: Tip) -> Maybe<&2, Maybe<&2, Ledgers.Id>>:
  Shared.Bool.when(
    Maybe<&2, Maybe<&2, Ledgers.Id>>,
    U32.is_eq(Tip.count(t), 0),
    u => Some{None{}},
    u => Maybe.bind(
      &2,
      Taken,
      Maybe<&2, Ledgers.Id>,
      Tip.taken(~mach, ~d, l, t, U32.sub(Tip.count(t), 1)),
      x => Some{Some{Taken.id(x)}}
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

# the time of the request of the entry e (none: it is not a request)
def Entry.time(-mach: Machine(), e: Ledgers.Entry<Machine.Q(mach)>) -> Maybe<&2, String>:
  match e:
    case Ledgers.Entry.Ask{i, time, q}:
      Some{time}
    case _:
      None{}

# the time of the request that the outcome o is of, in l (none: o is not of
# a taken request, or l lacks its entry)
def Out.time(~mach: Machine(),
  ~d: Led(mach), l: Led.L(mach, d), o: Out) -> Maybe<&2, String>:
  match o:
    case Out.Taken{a, n}:
      Maybe.bind(
        &2,
        Ledgers.Entry<Machine.Q(mach)>,
        String,
        Led.get(~mach, ~d, l, Ledgers.Name.Ask{a}),
        e => Entry.time(mach, e)
      )
    case _:
      None{}

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

# the ledger l holds each node that the act x adds, under its hash
def Act.held(~mach: Machine(), ~d: Led(mach), l: Led.L(mach, d), x: Act) -> Bool:
  match x:
    case Act.Taken{vs, h, ns}:
      Depots.Depot.holds(~Led.L(mach, d), ~(s => h2 => Led.fetch(~mach, ~d, s, h2)), l, ns)
    case Act.Opens{b, t, ns}:
      Depots.Depot.holds(~Led.L(mach, d), ~(s => h2 => Led.fetch(~mach, ~d, s, h2)), l, ns)
    case _:
      True{}

# that an act stays as the ledger grows: a kernel reads the ledger and the
# tip that it is given, waits for what it lacks, and does not answer on what
# it cannot read. So every replica that runs a request gets the same act, in
# a ledger that holds the nodes that the act adds (as a ledger where its step
# landed does: a node of another content under one of their hashes would
# change what reads them)
def Kernel.Stable(-mach: Machine(), -d: Led(mach), -f: Kernel.Change(mach, d)) -> Type:
  @t: Tip -> @c: Ledgers.Line -> @i: Ledgers.Id -> @q: Machine.Q(mach) -> @a: Led.L(mach, d) -> @b: Led.L(
    mach,
    d) -> @x: Act -> Led.Grows(mach, d, a, b) -> {f(a)(t)(c)(i)(q) == Some{x}: Maybe<&2, Act>} -> {
    Act.held(~mach, ~d, b, x) == True{}: Bool
  } -> {f(b)(t)(c)(i)(q) == Some{x}: Maybe<&2, Act>}

# a request, with its ID and its time
type Request<-Q: Data> is Data:
  Request{id: Ledgers.Id, time: String, ask: Q}

# the request, if any, that a replica asks by itself after a line moves (some
# none: none; none: the ledger lacks what the kernel reads, so it cannot tell
# yet)
def Kernel.Follow(-mach: Machine(), -d: Led(mach)) -> Type:
  Led.L(mach, d) -> Ledgers.Line -> Maybe<&2, Maybe<&2, Request<Machine.Q(mach)>>>

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
def Led.Later(~mach: Machine(), ~d: Led(mach), a: Led.L(mach, d), +b: Led.L(mach, d)) -> Data:
  {
    Bool.and(
      Ledgers.Kind.grows(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), a, b),
      Led.honest(~mach, ~d, b)
    )
      == True{}: Bool
  }

# the laws of the ledger d
def Led.laws(
  -mach: Machine(),
  d: Led(mach)
) -> Ledgers.Ledger.Laws(Machine.Q(mach), Machine.code(mach), Led.kind(mach, d)):
  match d:
    case Tuple{x, t}:
      Ledgers.Ledger.laws(Machine.Q(mach), Machine.code(mach), x)

# Led.later_grows, once the later ledger can be used often
def Led.later_grows.go(
  ~mach: Machine(),
  ~d: Led(mach),
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  h: Led.Later(~mach, ~d, a, b)
) -> Led.Grows(mach, d, a, b):
  Shared.Bool.and_true_left(
    Ledgers.Kind.grows(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), a, b),
    Led.honest(~mach, ~d, b)
  )(h)

# a later ledger holds each entry of the earlier one
law Led.later_grows:
  for ~mach: Machine()
  for ~d: Led(mach)
  for a: Led.L(mach, d)
  for b: Led.L(mach, d)
  Led.Later(~mach, ~d, a, b) -> Led.Grows(mach, d, a, b)

def Led.later_grows(mach, d, a, b):
  h => Led.later_grows.go(~mach, ~d, a, b, h)

# Cast.is_eq is True only for equal casts
def Cast.is_eq_sound(
  a: Ledgers.Cast,
  b: Ledgers.Cast
) -> {Ledgers.Cast.is_eq(a, b) == True{}: Bool} -> {a == b: Ledgers.Cast}:
  Shared.Eq.sound(
    ~Ledgers.Cast,
    ~Ledgers.Cast.is_eq,
    Codes.Code.eq_laws(~Ledgers.Cast, ~Ledgers.Cast.codec()),
    a,
    b
  )

# a check P of the first ballot b of a list holds of a member y of the list: b
# is y (s), or y is in the rest, whose check holds, and holds of its members
def Ballots.member.at(
  -P: Ledgers.Ballot -> Bool,
  s: Bool,
  +b: Ledgers.Ballot,
  +y: Ledgers.Ballot,
  -rest: Bool,
  -tail: Bool,
  es: {Ledgers.Ballot.is_eq(b, y) == s: Bool},
  hb: {P(b) == True{}: Bool},
  hr: {rest == True{}: Bool},
  kt: {List.any.if(u => tail, s) == True{}: Bool},
  ih: {rest == True{}: Bool} -> {tail == True{}: Bool} -> {P(y) == True{}: Bool}
) -> {P(y) == True{}: Bool}:
  match s:
    case True{}:
      %Ledgers.Ballot.is_eq_sound(b, y)(es): {P(_) == True{}: Bool}
      hb
    case False{}:
      ih(hr)(kt)

# a ballot that agrees with each ballot of bs agrees with each member of bs
def Ballots.agree_member(
  +a: Ledgers.Ballot,
  bs: List<&2, Ledgers.Ballot>,
  +y: Ledgers.Ballot
) -> {Ballots.agree_all(bs, a) == True{}: Bool} -> {
  List.contains(~Ledgers.Ballot, ~Ledgers.Ballot.is_eq, bs, y) == True{}: Bool
} -> {Ballots.agree(a, y) == True{}: Bool}:
  match bs:
    case Nil{}:
      h => k => Empty.absurd({Ballots.agree(a, y) == True{}: Bool}, Shared.Bool.false_ne_true(k))
    case Con{+b, +r}:
      +h => k =>
        Ballots.member.at(
          z => Ballots.agree(a, z),
          Ledgers.Ballot.is_eq(b, y),
          b,
          y,
          Ballots.agree_all(r, a),
          List.contains(~Ledgers.Ballot, ~Ledgers.Ballot.is_eq, r, y),
          {==},
          Shared.List.all.if_hit(Ballots.agree(a, b), u => Ballots.agree_all(r, a))(h),
          Shared.List.all.if_rest(Ballots.agree(a, b), u => Ballots.agree_all(r, a))(h),
          k,
          Ballots.agree_member(a, r, y)
        )

# each ballot of as agrees with each of bs, so each member of as does
def Ballots.single_member(
  as: List<&2, Ledgers.Ballot>,
  +bs: List<&2, Ledgers.Ballot>,
  +x: Ledgers.Ballot
) -> {Ballots.single(as, bs) == True{}: Bool} -> {
  List.contains(~Ledgers.Ballot, ~Ledgers.Ballot.is_eq, as, x) == True{}: Bool
} -> {Ballots.agree_all(bs, x) == True{}: Bool}:
  match as:
    case Nil{}:
      h => k => Empty.absurd({Ballots.agree_all(bs, x) == True{}: Bool}, Shared.Bool.false_ne_true(k))
    case Con{+a, +r}:
      +h => k =>
        Ballots.member.at(
          z => Ballots.agree_all(bs, z),
          Ledgers.Ballot.is_eq(a, x),
          a,
          x,
          Ballots.single(r, bs),
          List.contains(~Ledgers.Ballot, ~Ledgers.Ballot.is_eq, r, x),
          {==},
          Shared.List.all.if_hit(Ballots.agree_all(bs, a), u => Ballots.single(r, bs))(h),
          Shared.List.all.if_rest(Ballots.agree_all(bs, a), u => Ballots.single(r, bs))(h),
          k,
          Ballots.single_member(r, bs, x)
        )

# two ballots that agree, and are of one voter, at one place, and of one kind,
# cast the same
def Ballots.agree_cast(
  +a: Ledgers.Ballot,
  +b: Ledgers.Ballot,
  ha: {Ballots.agree(a, b) == True{}: Bool},
  hat: {Ledgers.Ballot.is_at(b, Ledgers.Ballot.at(a), Ledgers.Ballot.voter(a)) == True{}: Bool},
  hv: {Cast.is_vote(Ledgers.Ballot.cast(a)) == Cast.is_vote(Ledgers.Ballot.cast(b)): Bool}
) -> {Ledgers.Ballot.cast(a) == Ledgers.Ballot.cast(b): Ledgers.Cast}:
  Cast.is_eq_sound(Ledgers.Ballot.cast(a), Ledgers.Ballot.cast(b))(
    Equal.trans(
      Bool,
      Ledgers.Cast.is_eq(Ledgers.Ballot.cast(a), Ledgers.Ballot.cast(b)),
      Ballots.agree(a, b),
      True{},
      Equal.sym(
        Bool,
        Ballots.agree(a, b),
        Ledgers.Cast.is_eq(Ledgers.Ballot.cast(a), Ledgers.Ballot.cast(b)),
        Equal.cong(
          Bool,
          Bool,
          z => Bool.or(Bool.not(z), Ledgers.Cast.is_eq(Ledgers.Ballot.cast(a), Ledgers.Ballot.cast(b))),
          Bool.and(
            Ledgers.Ballot.is_at(b, Ledgers.Ballot.at(a), Ledgers.Ballot.voter(a)),
            Shared.Bool.is_eq(Cast.is_vote(Ledgers.Ballot.cast(a)), Cast.is_vote(Ledgers.Ballot.cast(b)))
          ),
          True{},
          Shared.Bool.and_both(
            Ledgers.Ballot.is_at(b, Ledgers.Ballot.at(a), Ledgers.Ballot.voter(a)),
            Shared.Bool.is_eq(Cast.is_vote(Ledgers.Ballot.cast(a)), Cast.is_vote(Ledgers.Ballot.cast(b)))
          )(hat)(
            %hv: {Shared.Bool.is_eq(Cast.is_vote(Ledgers.Ballot.cast(a)), _) == True{}: Bool}
            Shared.Bool.is_eq_refl(Cast.is_vote(Ledgers.Ballot.cast(a)))
          )
        )
      ),
      ha
    )
  )

# an "any" with the same hit is true when its rest is, if the rest of the other is (hit)
def Led.ballots.of_contains.at(
  hit: Bool,
  -p: Bool,
  -q: Bool
) -> {List.any.if(u => p, hit) == True{}: Bool} -> ({p == True{}: Bool} -> {q == True{}: Bool}) -> {
  List.any.if(u => q, hit) == True{}: Bool
}:
  match hit:
    case True{}:
      k => f => {==}
    case False{}:
      k => f => f(k)

# the ballots among the entries es include x, when es include its entry
def Led.ballots.of_contains(
  ~Q: Data,
  ~c: Codes.Codec(Q),
  es: List<&2, Ledgers.Entry<Q>>,
  +x: Ledgers.Ballot
) -> {
  List.contains(~Ledgers.Entry<Q>, ~Ledgers.Entry.same(~Q, ~c), es, Ledgers.Entry.Ballot{x}) == True{}: Bool
} -> {List.contains(~Ledgers.Ballot, ~Ledgers.Ballot.is_eq, Led.ballots.of(Q, es), x) == True{}: Bool}:
  match es:
    case Nil{}:
      h => h
    case Con{Ledgers.Entry.Ballot{+b}, +r}:
      h =>
        Led.ballots.of_contains.at(
          Ledgers.Ballot.is_eq(b, x),
          List.contains(~Ledgers.Entry<Q>, ~Ledgers.Entry.same(~Q, ~c), r, Ledgers.Entry.Ballot{x}),
          List.contains(~Ledgers.Ballot, ~Ledgers.Ballot.is_eq, Led.ballots.of(Q, r), x)
        )(h)(Led.ballots.of_contains(~Q, ~c, r, x))
    case Con{Ledgers.Entry.Ask{i, t, q}, +r}:
      h => Led.ballots.of_contains(~Q, ~c, r, x)(h)
    case Con{Ledgers.Entry.Data{ws}, +r}:
      h => Led.ballots.of_contains(~Q, ~c, r, x)(h)
    case Con{Ledgers.Entry.Lie{l}, +r}:
      h => Led.ballots.of_contains(~Q, ~c, r, x)(h)

# the ballots of a ledger include each ballot that it holds
def Led.ballots_have(
  ~mach: Machine(),
  ~d: Led(mach),
  +l: Led.L(mach, d),
  +x: Ledgers.Ballot,
  h: {Led.has(~mach, ~d, l, Ledgers.Entry.Ballot{x}) == True{}: Bool}
) -> {List.contains(~Ledgers.Ballot, ~Ledgers.Ballot.is_eq, Led.ballots(~mach, ~d, l), x) == True{}: Bool}:
  Led.ballots.of_contains(
    ~Machine.Q(mach),
    ~Machine.code(mach),
    Ledgers.Kind.entries(~Machine.Q(mach), ~Led.kind(mach, d), l),
    x
  )(
    Ledgers.Kind.entries_have(
      ~Machine.Q(mach),
      ~Machine.code(mach),
      ~Led.kind(mach, d),
      Ledgers.Laws.get_empty(Machine.Q(mach), Machine.code(mach), Led.kind(mach, d), Led.laws(mach, d)),
      Ledgers.Laws.missing(Machine.Q(mach), Machine.code(mach), Led.kind(mach, d), Led.laws(mach, d)),
      l,
      Ledgers.Entry.Ballot{x},
      h
    )
  )

# Led.later_single, once the later ledger can be used often
def Led.later_single.go(
  ~mach: Machine(),
  ~d: Led(mach),
  a: Led.L(mach, d),
  +b: Led.L(mach, d),
  h: Led.Later(~mach, ~d, a, b),
  +x: Ledgers.Ballot,
  +y: Ledgers.Ballot,
  hx: {Led.has(~mach, ~d, b, Ledgers.Entry.Ballot{x}) == True{}: Bool},
  hy: {Led.has(~mach, ~d, b, Ledgers.Entry.Ballot{y}) == True{}: Bool},
  hat: {Ledgers.Ballot.is_at(y, Ledgers.Ballot.at(x), Ledgers.Ballot.voter(x)) == True{}: Bool},
  hv: {Cast.is_vote(Ledgers.Ballot.cast(x)) == Cast.is_vote(Ledgers.Ballot.cast(y)): Bool}
) -> {Ledgers.Ballot.cast(x) == Ledgers.Ballot.cast(y): Ledgers.Cast}:
  Ballots.agree_cast(
    x,
    y,
    Ballots.agree_member(
      x,
      Led.ballots(~mach, ~d, b),
      y
    )(
      Ballots.single_member(
        Led.ballots(~mach, ~d, b),
        Led.ballots(~mach, ~d, b),
        x
      )(
        Shared.List.all.if_hit(
          Ballots.single(Led.ballots(~mach, ~d, b), Led.ballots(~mach, ~d, b)),
          u => Ballots.last(~mach, ~d, Led.ballots(~mach, ~d, b), b)
        )(
          Shared.Bool.and_true_right(
            Ledgers.Kind.grows(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), a, b),
            Led.honest(~mach, ~d, b)
          )(h)
        )
      )(Led.ballots_have(~mach, ~d, b, x, hx))
    )(Led.ballots_have(~mach, ~d, b, y, hy)),
    hat,
    hv
  )

# the ballots of a later ledger cast one vote at a place and one pass to it
law Led.later_single:
  for ~mach: Machine()
  for ~d: Led(mach)
  for a: Led.L(mach, d)
  for b: Led.L(mach, d)
  Led.Later(~mach, ~d, a, b) -> Led.Single(mach, d, b)

def Led.later_single(mach, d, a, b):
  h => x => y => hx => hy => hat => hv => Led.later_single.go(~mach, ~d, a, b, h, x, y, hx, hy, hat, hv)

# Sub.is_eq is True only for equal keys
def Sub.is_eq_sound(
  a: Maybe<&2, String>,
  b: Maybe<&2, String>
) -> {Ledgers.Sub.is_eq(a, b) == True{}: Bool} -> {a == b: Maybe<&2, String>}:
  Shared.Maybe.is_eq_sound(~String, ~String.eq, x => y => Texts.String.eq_sound(x, y), a, b)

# Line.is_eq is True only for equal lines
def Line.is_eq_sound(
  a: Ledgers.Line,
  b: Ledgers.Line
) -> {Ledgers.Line.is_eq(a, b) == True{}: Bool} -> {a == b: Ledgers.Line}:
  match a b:
    case Ledgers.Line{+i1, +k1} Ledgers.Line{+i2, +k2}:
      +h =>
        %Hashes.Hash.is_eq_sound(
          i1,
          i2
        )(
          Shared.List.all.if_hit(Hashes.Hash.is_eq(i1, i2), u => Ledgers.Sub.is_eq(k1, k2))(h)
        ): {Ledgers.Line{i1, k1} == Ledgers.Line{_, k2}: Ledgers.Line}
        %Sub.is_eq_sound(
          k1,
          k2
        )(
          Shared.List.all.if_rest(Hashes.Hash.is_eq(i1, i2), u => Ledgers.Sub.is_eq(k1, k2))(h)
        ): {Ledgers.Line{i1, k1} == Ledgers.Line{i1, _}: Ledgers.Line}
        {==}

# what holds of the parts of a place holds of the parts of a place that is the
# same
def Place.is_eq_move(
  -P: Ledgers.Line -> U32 -> Nat -> Type,
  +c1: Ledgers.Line,
  +h1: U32,
  +r1: Nat,
  +c2: Ledgers.Line,
  +h2: U32,
  +r2: Nat,
  +e: {Ledgers.Place.is_eq(Ledgers.Place{c1, h1, r1}, Ledgers.Place{c2, h2, r2}) == True{}: Bool},
  k: P(c1, h1, r1)
) -> P(c2, h2, r2):
  %Line.is_eq_sound(
    c1,
    c2
  )(
    Shared.List.all.if_hit(
      Ledgers.Line.is_eq(c1, c2),
      u => List.all.if(u2 => Nat.is_eq(r1, r2), U32.is_eq(h1, h2))
    )(e)
  ): P(_, h2, r2)
  %Shared.U32.is_eq_sound(
    h1,
    h2
  )(
    Shared.List.all.if_hit(
      U32.is_eq(h1, h2),
      u2 => Nat.is_eq(r1, r2)
    )(
      Shared.List.all.if_rest(
        Ledgers.Line.is_eq(c1, c2),
        u => List.all.if(u2 => Nat.is_eq(r1, r2), U32.is_eq(h1, h2))
      )(e)
    )
  ): P(c1, _, r2)
  %Shared.Nat.is_eq_sound(
    r1,
    r2
  )(
    Shared.List.all.if_rest(
      U32.is_eq(h1, h2),
      u2 => Nat.is_eq(r1, r2)
    )(
      Shared.List.all.if_rest(
        Ledgers.Line.is_eq(c1, c2),
        u => List.all.if(u2 => Nat.is_eq(r1, r2), U32.is_eq(h1, h2))
      )(e)
    )
  ): P(c1, h1, _)
  k

# a ballot that is at a place, by a voter, is by that voter
def Ballot.is_at_voter(
  b: Ledgers.Ballot,
  w: Ledgers.Place,
  +voter: String
) -> {Ledgers.Ballot.is_at(b, w, voter) == True{}: Bool} -> {Ledgers.Ballot.voter(b) == voter: String}:
  match b:
    case Ledgers.Ballot{Ledgers.Signed{+w2, +n, a}, l}:
      h =>
        Texts.String.eq_sound(
          n,
          voter
        )(Shared.List.all.if_rest(Ledgers.Place.is_eq(w2, w), u => String.eq(n, voter))(h))

# Last.is_eq is True only for equal last votes
def Last.is_eq_sound(
  a: Maybe<&2, Ledgers.Last>,
  b: Maybe<&2, Ledgers.Last>
) -> {Ledgers.Last.is_eq(a, b) == True{}: Bool} -> {a == b: Maybe<&2, Ledgers.Last>}:
  Shared.Maybe.is_eq_sound(
    ~Ledgers.Last,
    ~(x => y => Codes.Code.is_eq(~Ledgers.Last, ~Ledgers.Last.code, x, y)),
    x => y => Shared.Eq.sound(
      ~Ledgers.Last,
      ~(u => v => Codes.Code.is_eq(~Ledgers.Last, ~Ledgers.Last.code, u, v)),
      Codes.Code.eq_laws(~Ledgers.Last, ~Ledgers.Last.codec()),
      x,
      y
    ),
    a,
    b
  )

# the ballots bs of l, with a pass that names the last vote of its voter, when
# each does: so does each member of bs
def Ballots.last_member(
  ~mach: Machine(),
  ~d: Led(mach),
  bs: List<&2, Ledgers.Ballot>,
  +l: Led.L(mach, d),
  +y: Ledgers.Ballot
) -> {Ballots.last(~mach, ~d, bs, l) == True{}: Bool} -> {
  List.contains(~Ledgers.Ballot, ~Ledgers.Ballot.is_eq, bs, y) == True{}: Bool
} -> {Ballot.last(~mach, ~d, l, y) == True{}: Bool}:
  match bs:
    case Nil{}:
      h => k =>
        Empty.absurd({Ballot.last(~mach, ~d, l, y) == True{}: Bool}, Shared.Bool.false_ne_true(k))
    case Con{+b, +r}:
      +h => k =>
        Ballots.member.at(
          z => Ballot.last(~mach, ~d, l, z),
          Ledgers.Ballot.is_eq(b, y),
          b,
          y,
          Ballots.last(~mach, ~d, r, l),
          List.contains(~Ledgers.Ballot, ~Ledgers.Ballot.is_eq, r, y),
          {==},
          Shared.List.all.if_hit(Ballot.last(~mach, ~d, l, b), u => Ballots.last(~mach, ~d, r, l))(h),
          Shared.List.all.if_rest(Ballot.last(~mach, ~d, l, b), u => Ballots.last(~mach, ~d, r, l))(h),
          k,
          Ballots.last_member(~mach, ~d, r, l, y)
        )

# a pass that names the last vote of its voter, and is at a place by a voter,
# names the last vote that the voter cast below the round of the place
def Ballot.pass_last(
  ~mach: Machine(),
  ~d: Led(mach),
  +l: Led.L(mach, d),
  +p: Ledgers.Ballot,
  +c: Ledgers.Line,
  +h: U32,
  +r: Nat,
  +q: String,
  +z: Maybe<&2, Ledgers.Last>,
  +e: {Ledgers.Ballot.pass(p) == Some{z}: Maybe<&2, Maybe<&2, Ledgers.Last>>},
  hl: {Ballot.last(~mach, ~d, l, p) == True{}: Bool},
  +hat: {Ledgers.Ballot.is_at(p, Ledgers.Place{c, h, r}, q) == True{}: Bool}
) -> {z == Last.below(~mach, ~d, q, l, c, h, r): Maybe<&2, Ledgers.Last>}:
  match p:
    case Ledgers.Ballot{Ledgers.Signed{Ledgers.Place{c1, h1, r1}, n, Ledgers.Cast.Pass{y}}, lk}:
      %Ballot.is_at_voter(
        Ledgers.Ballot{Ledgers.Signed{Ledgers.Place{c1, h1, r1}, n, Ledgers.Cast.Pass{y}}, lk},
        Ledgers.Place{c, h, r},
        q
      )(hat): {z == Last.below(~mach, ~d, _, l, c, h, r): Maybe<&2, Ledgers.Last>}
      Place.is_eq_move(
        u => v => w => {z == Last.below(~mach, ~d, n, l, u, v, w): Maybe<&2, Ledgers.Last>},
        c1,
        h1,
        r1,
        c,
        h,
        r,
        Shared.List.all.if_hit(Ledgers.Place.is_eq(Ledgers.Place{c1, h1, r1}, Ledgers.Place{c, h, r}), u => String.eq(n, q))(hat),
        Equal.trans(
          Maybe<&2, Ledgers.Last>,
          z,
          y,
          Last.below(~mach, ~d, n, l, c1, h1, r1),
          Equal.sym(Maybe<&2, Ledgers.Last>, y, z, Shared.Maybe.some_inj(Maybe<&2, Ledgers.Last>, y, z, e)),
          Last.is_eq_sound(y, Last.below(~mach, ~d, n, l, c1, h1, r1))(hl)
        )
      )
    case Ledgers.Ballot{Ledgers.Signed{w2, n, Ledgers.Cast.Vote{v, from}}, lk}:
      Empty.absurd(
        {z == Last.below(~mach, ~d, q, l, c, h, r): Maybe<&2, Ledgers.Last>},
        Shared.Maybe.none_ne_some(Maybe<&2, Ledgers.Last>, z, e)
      )

# what the ballots hold of a part is t, at a ballot that put z there (z is t),
# when the part met the part of the rest (s)
def Ballots.cell_value.pick(
  -B: Data,
  s: Bool,
  +z: B,
  -t: B,
  -x: B,
  hz: {z == t: B},
  h: {
    Cells.Cell.value(B, Some{Bool.pick(Cells.Cell<B>, s, Cells.One{z}, Cells.Many{})}) == Some{x}: Maybe<
      &2,
      B>
  }
) -> {x == t: B}:
  match s:
    case True{}:
      Equal.trans(B, x, z, t, Equal.sym(B, z, x, Shared.Maybe.some_inj(B, z, x, h)), hz)
    case False{}:
      Empty.absurd({x == t: B}, Shared.Maybe.none_ne_some(B, x, h))

# what the ballots hold of a part is t, at a ballot whose part is o, and the
# cell c of the rest, when every part that a ballot puts there is t (hz) and
# the rest holds t (ih)
def Ballots.cell_value.at(
  ~B: Data,
  ~same: B -> B -> Bool,
  o: Maybe<&2, B>,
  c: Maybe<&2, Cells.Cell<B>>,
  -t: B,
  -x: B,
  hz: @z: B -> {o == Some{z}: Maybe<&2, B>} -> {z == t: B},
  ih: {Cells.Cell.value(B, c) == Some{x}: Maybe<&2, B>} -> {x == t: B}
) -> {
  Cells.Cell.value(
    B,
    Shared.Maybe.join(
      ~Cells.Cell<B>,
      ~Cells.Cell.join(~B, ~same),
      Maybe.bind(&2, B, Cells.Cell<B>, o, z => Some{Cells.One{z}}),
      c
    )
  )
    == Some{x}: Maybe<&2, B>
} -> {x == t: B}:
  match o c:
    case None{} y:
      h => ih(h)
    case Some{+z} None{}:
      h =>
        Equal.trans(
          B,
          x,
          z,
          t,
          Equal.sym(B, z, x, Shared.Maybe.some_inj(B, z, x, h)),
          hz(z)({==})
        )
    case Some{+z} Some{Cells.One{+w}}:
      h => Ballots.cell_value.pick(B, same(z, w), z, t, x, hz(z)({==}), h)
    case Some{z} Some{Cells.Many{}}:
      h => Empty.absurd({x == t: B}, Shared.Maybe.none_ne_some(B, x, h))

# a list that starts with a ballot holds it
def Ballots.contains_head(
  +p: Ledgers.Ballot,
  r: List<&2, Ledgers.Ballot>
) -> {List.contains(~Ledgers.Ballot, ~Ledgers.Ballot.is_eq, p <> r, p) == True{}: Bool}:
  %Equal.sym(
    Bool,
    Ledgers.Ballot.is_eq(p, p),
    True{},
    Ledgers.Ballot.is_eq_refl(p)
  ): {List.any.if(u => List.contains(~Ledgers.Ballot, ~Ledgers.Ballot.is_eq, r, p), _) == True{}: Bool}
  {==}

# a ballot of a list that is the ballots of a voter at a place of l, after pre,
# is one that l holds and that is at the place, by the voter
def Led.passed_last.member(
  ~mach: Machine(),
  ~d: Led(mach),
  +b: Led.L(mach, d),
  +c: Ledgers.Line,
  +h: U32,
  +r: Nat,
  +q: String,
  +p: Ledgers.Ballot,
  +pre: List<&2, Ledgers.Ballot>,
  +rest: List<&2, Ledgers.Ballot>,
  +e: {
    Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(b)(Ledgers.Place{c, h, r})(q)
      == List.append(&2, Ledgers.Ballot, pre, p <> rest): List<&2, Ledgers.Ballot>
  }
) -> {
  Bool.and(
    Led.has(~mach, ~d, b, Ledgers.Entry.Ballot{p}),
    Ledgers.Ballot.is_at(p, Ledgers.Place{c, h, r}, q)
  )
    == True{}: Bool
}:
  Equal.trans(
    Bool,
    Bool.and(
      Led.has(~mach, ~d, b, Ledgers.Entry.Ballot{p}),
      Ledgers.Ballot.is_at(p, Ledgers.Place{c, h, r}, q)
    ),
    List.contains(
      ~Ledgers.Ballot,
      ~Ledgers.Ballot.is_eq,
      Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(b)(Ledgers.Place{c, h, r})(q),
      p
    ),
    True{},
    Equal.sym(
      Bool,
      List.contains(
        ~Ledgers.Ballot,
        ~Ledgers.Ballot.is_eq,
        Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(b)(Ledgers.Place{c, h, r})(q),
        p
      ),
      Bool.and(
        Led.has(~mach, ~d, b, Ledgers.Entry.Ballot{p}),
        Ledgers.Ballot.is_at(p, Ledgers.Place{c, h, r}, q)
      ),
      Ledgers.Laws.ballots(
        Machine.Q(mach),
        Machine.code(mach),
        Led.kind(mach, d),
        Led.laws(mach, d)
      )(b)(Ledgers.Place{c, h, r})(q)(p)
    ),
    Equal.trans(
      Bool,
      List.contains(
        ~Ledgers.Ballot,
        ~Ledgers.Ballot.is_eq,
        Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(b)(Ledgers.Place{c, h, r})(q),
        p
      ),
      List.contains(
        ~Ledgers.Ballot,
        ~Ledgers.Ballot.is_eq,
        List.append(&2, Ledgers.Ballot, pre, p <> rest),
        p
      ),
      True{},
      Equal.cong(
        List<&2, Ledgers.Ballot>,
        Bool,
        z => List.contains(~Ledgers.Ballot, ~Ledgers.Ballot.is_eq, z, p),
        Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(b)(Ledgers.Place{c, h, r})(q),
        List.append(&2, Ledgers.Ballot, pre, p <> rest),
        e
      ),
      Shared.List.contains_right(
        ~Ledgers.Ballot,
        ~Ledgers.Ballot.is_eq,
        pre,
        p <> rest,
        p,
        Ballots.contains_head(p, rest)
      )
    )
  )

# the part that a cell of the passes of a voter at a place holds, when it
# holds one, is the last vote that the voter cast below the round of the place:
# the ballots bs follow pre in the ballots of the voter at the place
def Led.passed_last(
  ~mach: Machine(),
  ~d: Led(mach),
  +b: Led.L(mach, d),
  +c: Ledgers.Line,
  +h: U32,
  +r: Nat,
  +q: String,
  +hl: {Ballots.last(~mach, ~d, Led.ballots(~mach, ~d, b), b) == True{}: Bool},
  bs: List<&2, Ledgers.Ballot>,
  +pre: List<&2, Ledgers.Ballot>,
  +e: {
    Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(b)(Ledgers.Place{c, h, r})(q)
      == List.append(&2, Ledgers.Ballot, pre, bs): List<&2, Ledgers.Ballot>
  }
) -> @x: Maybe<&2, Ledgers.Last> -> {
  Cells.Cell.value(
    Maybe<&2, Ledgers.Last>,
    Ledgers.Ballots.cell(~Maybe<&2, Ledgers.Last>, ~Ledgers.Last.is_eq, ~Ledgers.Ballot.pass, bs)
  )
    == Some{x}: Maybe<&2, Maybe<&2, Ledgers.Last>>
} -> {x == Last.below(~mach, ~d, q, b, c, h, r): Maybe<&2, Ledgers.Last>}:
  match bs:
    case Nil{}:
      x => k =>
        Empty.absurd(
          {x == Last.below(~mach, ~d, q, b, c, h, r): Maybe<&2, Ledgers.Last>},
          Shared.Maybe.none_ne_some(Maybe<&2, Ledgers.Last>, x, k)
        )
    case Con{+p, +rest}:
      x => k =>
        Ballots.cell_value.at(
          ~Maybe<&2, Ledgers.Last>,
          ~Ledgers.Last.is_eq,
          Ledgers.Ballot.pass(p),
          Ledgers.Ballots.cell(~Maybe<&2, Ledgers.Last>, ~Ledgers.Last.is_eq, ~Ledgers.Ballot.pass, rest),
          Last.below(~mach, ~d, q, b, c, h, r),
          x,
          z => ep =>
            Ballot.pass_last(
              ~mach,
              ~d,
              b,
              p,
              c,
              h,
              r,
              q,
              z,
              ep,
              Ballots.last_member(~mach, ~d, Led.ballots(~mach, ~d, b), b, p)(hl)(
                Led.ballots_have(
                  ~mach,
                  ~d,
                  b,
                  p,
                  Shared.Bool.and_true_left(
                    Led.has(~mach, ~d, b, Ledgers.Entry.Ballot{p}),
                    Ledgers.Ballot.is_at(p, Ledgers.Place{c, h, r}, q)
                  )(Led.passed_last.member(~mach, ~d, b, c, h, r, q, p, pre, rest, e))
                )
              ),
              Shared.Bool.and_true_right(
                Led.has(~mach, ~d, b, Ledgers.Entry.Ballot{p}),
                Ledgers.Ballot.is_at(p, Ledgers.Place{c, h, r}, q)
              )(Led.passed_last.member(~mach, ~d, b, c, h, r, q, p, pre, rest, e))
            ),
          Led.passed_last(
            ~mach,
            ~d,
            b,
            c,
            h,
            r,
            q,
            hl,
            rest,
            List.append(&2, Ledgers.Ballot, pre, [p]),
            Equal.trans(
              List<&2, Ledgers.Ballot>,
              Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(b)(Ledgers.Place{c, h, r})(q),
              List.append(&2, Ledgers.Ballot, pre, p <> rest),
              List.append(&2, Ledgers.Ballot, List.append(&2, Ledgers.Ballot, pre, [p]), rest),
              e,
              Equal.sym(
                List<&2, Ledgers.Ballot>,
                List.append(&2, Ledgers.Ballot, List.append(&2, Ledgers.Ballot, pre, [p]), rest),
                List.append(&2, Ledgers.Ballot, pre, p <> rest),
                Shared.List.append_assoc(Ledgers.Ballot, pre, [p], rest)
              )
            )
          )(x)
        )(k)

# Led.later_last, once the later ledger can be used often
def Led.later_last.go(
  ~mach: Machine(),
  ~d: Led(mach),
  a: Led.L(mach, d),
  +b: Led.L(mach, d),
  h: Led.Later(~mach, ~d, a, b),
  +c: Ledgers.Line,
  +n: U32
) -> Rounds.Last(mach, d, b, c, n):
  +r => +q => +x => hp =>
    Led.passed_last(
      ~mach,
      ~d,
      b,
      c,
      n,
      r,
      q,
      Shared.List.all.if_rest(
        Ballots.single(Led.ballots(~mach, ~d, b), Led.ballots(~mach, ~d, b)),
        u => Ballots.last(~mach, ~d, Led.ballots(~mach, ~d, b), b)
      )(
        Shared.Bool.and_true_right(
          Ledgers.Kind.grows(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), a, b),
          Led.honest(~mach, ~d, b)
        )(h)
      ),
      Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(b)(Ledgers.Place{c, n, r})(q),
      [],
      {==}
    )(x)(hp)

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
  h2 => Led.later_last.go(~mach, ~d, a, b, h2, c, h)

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

# the newest tips of the lines cs are the same in the ledgers a and b
def Heads.same(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  cs: List<&2, Ledgers.Line>
) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{+c, rest}:
      Bool.and(
        Shared.Maybe.is_eq(
          ~Tip,
          ~(x => y => Codes.Code.is_eq(~Tip, ~Tip.code, x, y)),
          Line.head(~mach, ~d, ~kern, a, c),
          Line.head(~mach, ~d, ~kern, b, c)
        ),
        Heads.same(~mach, ~d, ~kern, a, b, rest)
      )

# the lines whose newest tips a kernel reads for each line
def Kernel.Deps(-mach: Machine(), -d: Led(mach)) -> Type:
  Led.L(mach, d) -> Ledgers.Line -> List<&2, Ledgers.Line>

# that what the kernel kern asks by itself for a line reads only the newest
# tips of the lines that deps names, and the data under them: in a later
# ledger where those tips are the same, a request that it could tell stays
def Kernel.Reads(
  -mach: Machine(),
  -d: Led(mach),
  -kern: Kernel(mach, d),
  -deps: Kernel.Deps(mach, d)
) -> Type:
  @a: Led.L(mach, d) -> @b: Led.L(mach, d) -> @c: Ledgers.Line -> @x: Maybe<&2, Request<Machine.Q(mach)>> -> Led.Later(
    ~mach,
    ~d,
    a,
    b
  ) -> {Kernel.follow(mach, d, kern)(a)(c) == Some{x}: Maybe<&2, Maybe<&2, Request<Machine.Q(mach)>>>} -> {
    Heads.same(~mach, ~d, ~kern, a, b, deps(a)(c)) == True{}: Bool
  } -> {Kernel.follow(mach, d, kern)(b)(c) == Some{x}: Maybe<&2, Maybe<&2, Request<Machine.Q(mach)>>>}

# that watch names each line that reads a line that moved: when deps says
# that the line c reads a line among moved, and watch can tell (some ws), ws
# names c. When it cannot tell, a replica asks again once the ledger holds
# more
def Kernel.Covers(
  -mach: Machine(),
  -d: Led(mach),
  -deps: Kernel.Deps(mach, d),
  -watch: Led.L(mach, d) -> List<&2, Ledgers.Line> -> Maybe<&2, List<&2, Ledgers.Line>>
) -> Type:
  @l: Led.L(mach, d) -> @moved: List<&2, Ledgers.Line> -> @ws: List<&2, Ledgers.Line> -> @c: Ledgers.Line -> @m: Ledgers.Line -> {
    watch(l)(moved) == Some{ws}: Maybe<&2, List<&2, Ledgers.Line>>
  } -> {List.contains(~Ledgers.Line, ~Ledgers.Line.is_eq, moved, m) == True{}: Bool} -> {
    List.contains(~Ledgers.Line, ~Ledgers.Line.is_eq, deps(l)(c), m) == True{}: Bool
  } -> {List.contains(~Ledgers.Line, ~Ledgers.Line.is_eq, ws, c) == True{}: Bool}

# that the kernel kern asks again only where watch says, when the lines moved
# move: Kernel.Reads and Kernel.Covers, for some deps
def Kernel.Watched(
  -mach: Machine(),
  -d: Led(mach),
  -kern: Kernel(mach, d),
  -watch: Led.L(mach, d) -> List<&2, Ledgers.Line> -> Maybe<&2, List<&2, Ledgers.Line>>
) -> Type:
  &deps: Kernel.Deps(mach, d) -> Kernel.Reads(mach, d, kern, deps) & Kernel.Covers(mach, d, deps, watch)

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
    } -> Ballot.Linked(mach, d, kern, l, b, Ledgers.Ballot.prev(b))
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
      == Some{Some{Request{i, time, q}}}: Maybe<&2, Maybe<&2, Request<Machine.Q(mach)>>>
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
    Ledgers.Line.root(c)
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
    Ledgers.Line.root(c)
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
    Ledgers.Line.root(c)
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

# what a ledger that grows from a gives under each name, by the check
def Hist.gets(
  ~mach: Machine(),
  ~d: Led(mach),
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  +g: Led.Grows(mach, d, a, b)
) -> Ledgers.Kind.Grows(Machine.Q(mach), Led.kind(mach, d), a, b):
  Ledgers.Kind.grows_get(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), ~Led.laws(mach, d), a, b)(g)

# a ledger grows from itself
def Hist.refl(~mach: Machine(), ~d: Led(mach), +l: Led.L(mach, d)) -> Led.Grows(mach, d, l, l):
  Ledgers.Kind.grows_refl(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), ~Led.laws(mach, d), l)

# growth is transitive
def Hist.trans(
  ~mach: Machine(),
  ~d: Led(mach),
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  +c: Led.L(mach, d),
  +g1: Led.Grows(mach, d, a, b),
  +g2: Led.Grows(mach, d, b, c)
) -> Led.Grows(mach, d, a, c):
  Ledgers.Kind.grows_trans(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), ~Led.laws(mach, d), a, b, c, g1, g2)

# a ledger grows by an entry
def Hist.add(~mach: Machine(), ~d: Led(mach), +l: Led.L(mach, d), +x: Entry(mach)) -> Led.Grows(
  mach,
  d,
  l,
  Led.add(~mach, ~d, l, x)
):
  Ledgers.Kind.grows_add(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), ~Led.laws(mach, d), l, x)

# a ledger grows by the data ns
def Hist.puts(~mach: Machine(), ~d: Led(mach), ns: List<&2, List<&2, U32>>, +l: Led.L(mach, d)) -> Led.Grows(
  mach,
  d,
  l,
  Led.puts(~mach, ~d, ns, l)
):
  match ns:
    case Nil{}:
      Hist.refl(~mach, ~d, l)
    case Con{+ws, +rest}:
      Hist.trans(~mach, ~d,
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
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  +h: Hashes.Hash,
  -w: List<&2, U32>,
  +g: Led.Grows(mach, d, a, b)
) -> {Led.fetch(~mach, ~d, a, h) == Some{w}: Maybe<&2, List<&2, U32>>}
  -> {Led.fetch(~mach, ~d, b, h) == Some{w}: Maybe<&2, List<&2, U32>>}:
  Hist.words(
    mach,
    Led.get(~mach, ~d, a, Ledgers.Name.Data{h}),
    Led.get(~mach, ~d, b, Ledgers.Name.Data{h}),
    w,
    e => Hist.gets(~mach, ~d, a, b, g)(Ledgers.Name.Data{h})(e)
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
  -grows: S -> S -> Bool,
  t: Trees.Tree(S, fetch, grows)
) -> Trees.Laws.Final(S, grows, Trees.Tree.ops(S, fetch, grows, t)):
  match t:
    case Tuple{o, Tuple{f, r}}:
      f

# the law that a write stays, of a tree t
def Hist.put_final.of(
  -S: Data,
  -fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  -grows: S -> S -> Bool,
  t: Trees.Tree(S, fetch, grows)
) -> Trees.Laws.PutFinal(S, grows, Trees.Tree.ops(S, fetch, grows, t)):
  match t:
    case Tuple{o, Tuple{f, Tuple{p, r}}}:
      p

# the law of a write, of a tree t
def Hist.write.of(
  -S: Data,
  -fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  -grows: S -> S -> Bool,
  t: Trees.Tree(S, fetch, grows)
) -> Trees.Laws.Write(S, fetch, grows, Trees.Tree.ops(S, fetch, grows, t)):
  match t:
    case Tuple{o, Tuple{f, Tuple{p, Tuple{w, r}}}}:
      w

# the law that a read stays, of the tree of the ledger d
def Hist.final(-mach: Machine(), d: Led(mach)) -> Trees.Laws.Final(
  Led.L(mach, d),
  a => b => Ledgers.Kind.grows(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), a, b),
  Led.tree(mach, d)
):
  match d:
    case Tuple{x, t}:
      Hist.final.of(
        Ledgers.Kind.L(Machine.Q(mach), Ledgers.Ledger.kind(Machine.Q(mach), Machine.code(mach), x)),
        Ledgers.Kind.data(Machine.Q(mach), Ledgers.Ledger.kind(Machine.Q(mach), Machine.code(mach), x)),
        a => b => Ledgers.Kind.grows(
          ~Machine.Q(mach),
          ~Machine.code(mach),
          ~Ledgers.Ledger.kind(Machine.Q(mach), Machine.code(mach), x),
          a,
          b
        ),
        t
      )

# the law that a write stays, of the tree of the ledger d
def Hist.put_final(-mach: Machine(), d: Led(mach)) -> Trees.Laws.PutFinal(
  Led.L(mach, d),
  a => b => Ledgers.Kind.grows(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), a, b),
  Led.tree(mach, d)
):
  match d:
    case Tuple{x, t}:
      Hist.put_final.of(
        Ledgers.Kind.L(Machine.Q(mach), Ledgers.Ledger.kind(Machine.Q(mach), Machine.code(mach), x)),
        Ledgers.Kind.data(Machine.Q(mach), Ledgers.Ledger.kind(Machine.Q(mach), Machine.code(mach), x)),
        a => b => Ledgers.Kind.grows(
          ~Machine.Q(mach),
          ~Machine.code(mach),
          ~Ledgers.Ledger.kind(Machine.Q(mach), Machine.code(mach), x),
          a,
          b
        ),
        t
      )

# the law of a write, of the tree of the ledger d
def Hist.write(-mach: Machine(), d: Led(mach)) -> Trees.Laws.Write(
  Led.L(mach, d),
  l => h => Led.fetch(~mach, ~d, l, h),
  a => b => Ledgers.Kind.grows(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), a, b),
  Led.tree(mach, d)
):
  match d:
    case Tuple{x, t}:
      Hist.write.of(
        Ledgers.Kind.L(Machine.Q(mach), Ledgers.Ledger.kind(Machine.Q(mach), Machine.code(mach), x)),
        Ledgers.Kind.data(Machine.Q(mach), Ledgers.Ledger.kind(Machine.Q(mach), Machine.code(mach), x)),
        a => b => Ledgers.Kind.grows(
          ~Machine.Q(mach),
          ~Machine.code(mach),
          ~Ledgers.Ledger.kind(Machine.Q(mach), Machine.code(mach), x),
          a,
          b
        ),
        t
      )

# the law that a listing stays, of a tree t
def Hist.range_final.of(
  -S: Data,
  -fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  -grows: S -> S -> Bool,
  t: Trees.Tree(S, fetch, grows)
) -> Trees.Laws.RangeFinal(S, grows, Trees.Tree.ops(S, fetch, grows, t)):
  match t:
    case Tuple{o, Tuple{f, Tuple{pf, Tuple{w, Tuple{cn, Tuple{rg, Tuple{df, Tuple{wh, Tuple{kp, Tuple{rf, dff}}}}}}}}}}:
      rf

# the law that a listing stays, of the tree of the ledger d
def Hist.range_final(-mach: Machine(), d: Led(mach)) -> Trees.Laws.RangeFinal(
  Led.L(mach, d),
  a => b => Ledgers.Kind.grows(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), a, b),
  Led.tree(mach, d)
):
  match d:
    case Tuple{x, t}:
      Hist.range_final.of(
        Ledgers.Kind.L(Machine.Q(mach), Ledgers.Ledger.kind(Machine.Q(mach), Machine.code(mach), x)),
        Ledgers.Kind.data(Machine.Q(mach), Ledgers.Ledger.kind(Machine.Q(mach), Machine.code(mach), x)),
        a => b => Ledgers.Kind.grows(
          ~Machine.Q(mach),
          ~Machine.code(mach),
          ~Ledgers.Ledger.kind(Machine.Q(mach), Machine.code(mach), x),
          a,
          b
        ),
        t
      )

# a listing of a tree stays as the ledger grows
def Hist.range(
  ~mach: Machine(),
  ~d: Led(mach),
  a: Led.L(mach, d),
  b: Led.L(mach, d),
  h: Maybe<&2, Hashes.Hash>,
  p: List<&2, U32>,
  bs: List<&2, Trees.Binding>,
  g: Led.Grows(mach, d, a, b)
) -> {Tree.range(~mach, ~d, a, h, p) == Some{bs}: Maybe<&2, List<&2, Trees.Binding>>}
  -> {Tree.range(~mach, ~d, b, h, p) == Some{bs}: Maybe<&2, List<&2, Trees.Binding>>}:
  e => Hist.range_final(mach, d)(a)(b)(h)(p)(bs)(e)(g)

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

# a ballot at the place w is at w
def Safe.at_of(e: Ledgers.Ballot, w: Ledgers.Place, +voter: String) -> {
  Ledgers.Ballot.is_at(e, w, voter) == True{}: Bool
} -> {Ledgers.Ballot.at(e) == w: Ledgers.Place}:
  match e w:
    case Ledgers.Ballot{Ledgers.Signed{Ledgers.Place{+c1, +h1, +r1}, +n, a}, l} Ledgers.Place{+c2, +h2, +r2}:
      h => Place.is_eq_move(
        c => x => r => {Ledgers.Place{c1, h1, r1} == Ledgers.Place{c, x, r}: Ledgers.Place},
        c1,
        h1,
        r1,
        c2,
        h2,
        r2,
        Shared.List.all.if_hit(
          Ledgers.Place.is_eq(Ledgers.Place{c1, h1, r1}, Ledgers.Place{c2, h2, r2}),
          u => String.eq(n, voter)
        )(h),
        {==}
      )

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
  Safe.laws.ballots(Machine.Q(mach), Machine.code(mach), Led.kind(mach, d), Led.laws(mach, d))

# the law of the bound of rounds, of the ledger d
def Safe.rounds_law(-mach: Machine(), d: Led(mach)) -> Ledgers.Laws.Rounds(
  Machine.Q(mach),
  Machine.code(mach),
  Led.kind(mach, d)
):
  Safe.laws.rounds(Machine.Q(mach), Machine.code(mach), Led.kind(mach, d), Led.laws(mach, d))

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
    x => Hist.gets(~mach, ~d, a, b, Led.later_grows(~mach, ~d, a, b)(later))(Entry.name(~mach, e))(x)
  )

# a ballot of a voter at a place in a ledger is one in a later ledger
def Safe.in_b(
  ~mach: Machine(),
  ~d: Led(mach),
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
      %Equal.sym(String, Ledgers.Ballot.voter(e0), voter, Ballot.is_at_voter(e0, w, voter)(i0)): {
        Ledgers.Ballot.is_at(e, w, _) == True{}: Bool
      }
      Shared.Bool.and_true_right(Led.has(~mach, ~d, b, Ledgers.Entry.Ballot{e}), Ledgers.Ballot.is_at(e, w, voter))(k1),
      Led.later_single(~mach, ~d, a, b)(later)
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
        Safe.of_in_b(~mach, ~d, ~B, ~same, ~sl, ~of, ~kd, ~ofc, ~ofk, a, b, later, w, voter, e0, x, e)(h0)(hx)(
          Shared.Bool.and_true_left(List.contains(~Ledgers.Ballot, ~Ledgers.Ballot.is_eq, Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(b)(w)(voter), e), Shared.List.within(~Ledgers.Ballot, ~Ledgers.Ballot.is_eq, r, Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(b)(w)(voter)))(h)
        )
      )(
        Safe.all_in_b(~mach, ~d, ~B, ~same, ~sl, ~of, ~kd, ~ofc, ~ofk, a, b, later, w, voter, e0, x, r)(h0)(hx)(
          Shared.Bool.and_true_right(List.contains(~Ledgers.Ballot, ~Ledgers.Ballot.is_eq, Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(b)(w)(voter), e), Shared.List.within(~Ledgers.Ballot, ~Ledgers.Ballot.is_eq, r, Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(b)(w)(voter)))(h)
        )
      )

# and so do those of the earlier ledger
def Safe.all_in_a(
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
        Safe.of_in_b(~mach, ~d, ~B, ~same, ~sl, ~of, ~kd, ~ofc, ~ofk, a, b, later, w, voter, e0, x, e)(h0)(hx)(
          Safe.in_b(~mach, ~d, a, b, later, w, voter, e)(
            Shared.Bool.and_true_left(List.contains(~Ledgers.Ballot, ~Ledgers.Ballot.is_eq, Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(a)(w)(voter), e), Shared.List.within(~Ledgers.Ballot, ~Ledgers.Ballot.is_eq, r, Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(a)(w)(voter)))(h)
          )
        )
      )(
        Safe.all_in_a(~mach, ~d, ~B, ~same, ~sl, ~of, ~kd, ~ofc, ~ofk, a, b, later, w, voter, e0, x, r)(h0)(hx)(
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
      +hcb = Safe.in_b(~mach, ~d, a, b, later, w, voter, e0)(hc)
      +caA = Safe.most_some(~B, ~same, ~sl, Ledgers.Ballots.cell(~B, ~same, ~of, Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(a)(w)(voter)), x)(
        Safe.cell_most(~B, ~same, ~sl, ~of, Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(a)(w)(voter), x)(
          Safe.all_in_a(~mach, ~d, ~B, ~same, ~sl, ~of, ~kd, ~ofc, ~ofk, a, b, later, w, voter, e0, x, Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(a)(w)(voter))(hcb)(hx)(
            Safe.within_refl(~Ledgers.Ballot, ~Ledgers.Ballot.is_eq, ~Ledgers.Ballot.laws(), Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(a)(w)(voter))
          )
        )
      )(Safe.some_of(Cells.Cell<B>, Ledgers.Ballots.cell(~B, ~same, ~of, Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(a)(w)(voter)), c, h))
      +cb = Safe.most_some(~B, ~same, ~sl, Ledgers.Ballots.cell(~B, ~same, ~of, Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(b)(w)(voter)), x)(
        Safe.cell_most(~B, ~same, ~sl, ~of, Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(b)(w)(voter), x)(
          Safe.all_in_b(~mach, ~d, ~B, ~same, ~sl, ~of, ~kd, ~ofc, ~ofk, a, b, later, w, voter, e0, x, Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(b)(w)(voter))(hcb)(hx)(
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
      Safe.cell_kept.of(~mach, ~d, ~B, ~same, ~sl, ~of, ~kd, ~ofc, ~ofk, a, b, later, w, voter, c, h, e0, hc, q)

# the cell of a voter at a place stays in a later ledger: an honest later
# ledger holds no ballot of the voter there that disagrees
def Safe.cell_kept(
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
  (a => Safe.last_refl(a), a => b => Last.is_eq_sound(a, b))

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
          c => Safe.cell_kept(~mach, ~d, ~Ledgers.Step, ~Ledgers.Step.is_eq, ~Ledgers.Step.laws(), ~Ledgers.Ballot.step, ~True{}, ~(x => y => Safe.step_cast(x, y)), ~(x => y => Safe.step_kind(x, y)), a, b, later, w, o, c)
        )
      )(Safe.cells_keep(~mach, ~d, a, b, later, w, r))

# the step that a majority cast at a place stays in a later ledger
def Safe.tally_kept(
  ~mach: Machine(),
  ~d: Led(mach),
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
  )(Ledgers.Kind.cells(~Machine.Q(mach), ~Led.kind(mach, d), b, w, os))(v)(Safe.cells_keep(~mach, ~d, a, b, later, w, os))(h)

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
          y => Safe.pass_kept(~mach, ~d, a, b, later, w, o, y)
        )(Shared.List.all.if_hit(Maybe.is_some(&2, Maybe<&2, Ledgers.Last>, Led.passed(~mach, ~d, a, w, o)), u => Passed.all(~mach, ~d, a, w, r))(e))
      )(
        Safe.passed_all_kept(~mach, ~d, a, b, later, w, r)(
          Shared.List.all.if_rest(Maybe.is_some(&2, Maybe<&2, Ledgers.Last>, Led.passed(~mach, ~d, a, w, o)), u => Passed.all(~mach, ~d, a, w, r))(e)
        )
      )

# a pass that a ledger holds is the same pass in a later ledger
def Safe.passed_eq(
  ~mach: Machine(),
  ~d: Led(mach),
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
    y => Safe.pass_kept(~mach, ~d, a, b, later, w, o, y)
  )

# the highest last vote that the passes of some voters name is the same in a
# later ledger, when the ledger holds each of the passes
def Safe.last_eq(
  ~mach: Machine(),
  ~d: Led(mach),
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
          Safe.passed_eq(~mach, ~d, a, b, later, w, o)(
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
          Safe.last_eq(~mach, ~d, a, b, later, w, r)(
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
          Safe.passed_eq(~mach, ~d, a, b, later, w, o)(
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
          Safe.agree_eq(~mach, ~d, a, b, later, w, r, t, v)(
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
      Safe.vote_kept(~mach, ~d, a, b, later, Ledgers.Place{c, h, k}, o, y)
    case False{}:
      ih

# the vote that the passes of some voters lead back to is the same in a later
# ledger, when the ledger holds each of the passes
def Safe.act_kept(
  ~mach: Machine(),
  ~d: Led(mach),
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
          Safe.passed_eq(~mach, ~d, a, b, later, Ledgers.Place{c, h, r}, o)(
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
          ~mach, ~d, a,
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
          Safe.act_kept(~mach, ~d, a, b, later, c, h, r, rest, k, y)(
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
          )(Safe.passed_all_kept(~mach, ~d, a, b, later, Ledgers.Place{c, h, 1n+p}, from)(pall))(
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
            Safe.last_eq(~mach, ~d, a, b, later, Ledgers.Place{c, h, 1n+p}, from)(pall)
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
                Safe.agree_eq(~mach, ~d, a, b, later, Ledgers.Place{c, h, 1n+p}, from, t, v)(pall)
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
                y => Safe.act_kept(~mach, ~d, a, b, later, c, h, 1n+p, from, t, y)(pall),
                f => Safe.allowed_kept(~mach, ~d, a, b, later, c, h, os, v, j, t, f)
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
      Safe.allowed_kept(~mach, ~d, a, b, later, c, h, os, v, r, r, from)

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
      y => Safe.vote_kept(~mach, ~d, a, b, later, w, p, y),
      f => Safe.allowed_at(~mach, ~d, a, b, later, w, os, v, f)
    )
  )

# the step that a round decides stays in a later ledger
def Safe.decide_kept(
  ~mach: Machine(),
  ~d: Led(mach),
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
    v => Safe.tally_kept(~mach, ~d, a, b, later, Ledgers.Place{c, h, r}, os, v),
    +v => Shared.Maybe.bind_kept(
      String,
      Ledgers.Step,
      Voters.turn(os, h, r),
      Voters.turn(os, h, r),
      p => Round.led(~mach, ~d, a, Ledgers.Place{c, h, r}, os, v, p),
      p => Round.led(~mach, ~d, b, Ledgers.Place{c, h, r}, os, v, p),
      x,
      p => e => e,
      p => Safe.led_kept(~mach, ~d, a, b, later, Ledgers.Place{c, h, r}, os, v, p, x)
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
    Led.later_last(~mach, ~d, a, b, c, h)(later)(1n+p)(q)(y)(hp)
  ): {Safe.after(_, r1, v1) == True{}: Bool}
  Safe.mine(~mach, ~d, q, b, c, h, p, r1, v1)(hv)(Shared.Nat.lt_succ_le(r1, p)(hl))

# when the passes name no vote, the voter that two majorities share is a
# contradiction, once its pass is known
def Safe.round_safe.none2(
  ~mach: Machine(),
  ~d: Led(mach),
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
      Safe.after_none(y, r1, v1)(Safe.round_safe.after(~mach, ~d, a, b, later, c, h, r1, v1, p, q, y, hp, hv, hl))(
        %eM: {Safe.le(y, _) == True{}: Bool}
        hle
      )

# when the passes name no vote, the voter that two majorities share is a
# contradiction
def Safe.round_safe.none(
  ~mach: Machine(),
  ~d: Led(mach),
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
      Safe.round_safe.none2(~mach, ~d, a, b, later, c, h, r1, v1, p, from, eM, hl, q, hv, ex)

# Safe.round_safe in the case of a later round t of the passes, once the act of
# the first voter whose pass names t is known
def Safe.round_safe.act(
  ~mach: Machine(),
  ~d: Led(mach),
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
        ~mach, ~d, a, b, later, c, h, os, r1, v1, j, p, v2, from,
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
      Safe.round_safe.cmp(~mach, ~d, a, b, later, c, h, os, r1, v1, j, p, v2, from, t, tq, xq, Nat.is_eq(t, r1), {==}, aft, ha, hle, cs, ih)

# Safe.round_safe once the pass of the shared voter is known
def Safe.round_safe.some2(
  ~mach: Machine(),
  ~d: Led(mach),
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
        ~mach, ~d, a, b, later, c, h, os, r1, v1, j, p, v2, from,
        t,
        x,
        y,
        Safe.round_safe.after(~mach, ~d, a, b, later, c, h, r1, v1, p, q, y, hp, hv, hl),
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
      Safe.round_safe.some2(~mach, ~d, a, b, later, c, h, os, r1, v1, j, p, v2, from, t, x, eM, hl, cs, ih, q, hv, ex)

# Safe.round_safe once the highest last vote M that the passes name is known
def Safe.round_safe.at(
  ~mach: Machine(),
  ~d: Led(mach),
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
        ~mach, ~d, a, b, later, c, h, os, r1, v1, j, p, v2, from,
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
          ~mach, ~d, a, b, later, c, h, os, r1, v1, j, p, v2, from,
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
          t => f => hlt => ha => Safe.round_safe(~mach, ~d, a, b, later, c, h, os, r1, v1, j, t, v2, f)(hq)(hlt)(ha)
        )

# a round decided x: its tally gave x, and the voter whose turn it was cast x
# with passes that allow it
def Safe.Dec(
  -mach: Machine(),
  -d: Led(mach),
  -l: Led.L(mach, d),
  -w: Ledgers.Place,
  -os: List<&2, String>,
  -x: Ledgers.Step
) -> Type:
  Exists(
    String,
    p => {Led.tally(~mach, ~d, l, w, os) == Some{x}: Maybe<&2, Ledgers.Step>}
      & {Cast.casts(Led.cast(~mach, ~d, l, w, p), x, f => Step.allowed(~mach, ~d, l, w, os, x, f)) == True{}: Bool}
  )

# the step that a round leads with is the step that it decides
def Safe.decided.led(cond: Bool, -v: Ledgers.Step, -x: Ledgers.Step) -> {
  Shared.Maybe.when(Ledgers.Step, cond, u => Some{v}) == Some{x}: Maybe<&2, Ledgers.Step>
} -> ({cond == True{}: Bool} & {v == x: Ledgers.Step}):
  match cond:
    case True{}:
      e => Tuple{{==}, Shared.Maybe.some_inj(Ledgers.Step, v, x, e)}
    case False{}:
      e => Empty.absurd(
        {False{} == True{}: Bool} & {v == x: Ledgers.Step},
        Shared.Maybe.none_ne_some(Ledgers.Step, x, e)
      )

# Safe.decided once the test of the voter p is known
def Safe.decided.pair(
  ~mach: Machine(),
  ~d: Led(mach),
  +l: Led.L(mach, d),
  +w: Ledgers.Place,
  +os: List<&2, String>,
  +p: String,
  +v: Ledgers.Step,
  -x: Ledgers.Step,
  em: {Led.tally(~mach, ~d, l, w, os) == Some{v}: Maybe<&2, Ledgers.Step>},
  pr: {Cast.casts(Led.cast(~mach, ~d, l, w, p), v, f => Step.allowed(~mach, ~d, l, w, os, v, f)) == True{}: Bool} & {v == x: Ledgers.Step}
) -> Safe.Dec(mach, d, l, w, os, x):
  match pr:
    case Tuple{hc, +hvx}:
      Tuple{
        p,
        Tuple{
          Equal.trans(
            Maybe<&2, Ledgers.Step>,
            Led.tally(~mach, ~d, l, w, os),
            Some{v},
            Some{x},
            em,
            Equal.cong(Ledgers.Step, Maybe<&2, Ledgers.Step>, z => Some{z}, v, x, hvx)
          ),
          %hvx: {Cast.casts(Led.cast(~mach, ~d, l, w, p), _, f => Step.allowed(~mach, ~d, l, w, os, _, f)) == True{}: Bool}
          hc
        }
      }

# Safe.decided once the voter whose turn it is is known
def Safe.decided.turn(
  ~mach: Machine(),
  ~d: Led(mach),
  t: Maybe<&2, String>,
  +l: Led.L(mach, d),
  +w: Ledgers.Place,
  +os: List<&2, String>,
  +v: Ledgers.Step,
  -x: Ledgers.Step,
  em: {Led.tally(~mach, ~d, l, w, os) == Some{v}: Maybe<&2, Ledgers.Step>}
) -> {
  Maybe.bind(&2, String, Ledgers.Step, t, p => Round.led(~mach, ~d, l, w, os, v, p)) == Some{x}: Maybe<&2, Ledgers.Step>
} -> Safe.Dec(mach, d, l, w, os, x):
  match t:
    case None{}:
      e => Empty.absurd(Safe.Dec(mach, d, l, w, os, x), Shared.Maybe.none_ne_some(Ledgers.Step, x, e))
    case Some{+p}:
      e => Safe.decided.pair(
        ~mach,
        ~d,
        l,
        w,
        os,
        p,
        v,
        x,
        em,
        Safe.decided.led(Cast.casts(Led.cast(~mach, ~d, l, w, p), v, f => Step.allowed(~mach, ~d, l, w, os, v, f)), v, x)(e)
      )

# Safe.decided once the tally m is known
def Safe.decided.at(
  ~mach: Machine(),
  ~d: Led(mach),
  m: Maybe<&2, Ledgers.Step>,
  +l: Led.L(mach, d),
  +c: Ledgers.Line,
  +h: U32,
  +os: List<&2, String>,
  +r: Nat,
  -x: Ledgers.Step,
  em: {Led.tally(~mach, ~d, l, Ledgers.Place{c, h, r}, os) == m: Maybe<&2, Ledgers.Step>}
) -> {
  Maybe.bind(
    &2,
    Ledgers.Step,
    Ledgers.Step,
    m,
    +v => Maybe.bind(&2, String, Ledgers.Step, Voters.turn(os, h, r), p => Round.led(~mach, ~d, l, Ledgers.Place{c, h, r}, os, v, p))
  )
    == Some{x}: Maybe<&2, Ledgers.Step>
} -> Safe.Dec(mach, d, l, Ledgers.Place{c, h, r}, os, x):
  match m:
    case None{}:
      e => Empty.absurd(Safe.Dec(mach, d, l, Ledgers.Place{c, h, r}, os, x), Shared.Maybe.none_ne_some(Ledgers.Step, x, e))
    case Some{+v}:
      Safe.decided.turn(~mach, ~d, Voters.turn(os, h, r), l, Ledgers.Place{c, h, r}, os, v, x, em)

# a round that decides x tallied x, and its leader cast x with passes that
# allow it
def Safe.decided(
  ~mach: Machine(),
  ~d: Led(mach),
  +l: Led.L(mach, d),
  +c: Ledgers.Line,
  +h: U32,
  +os: List<&2, String>,
  +r: Nat,
  -x: Ledgers.Step
) -> {Round.decide(~mach, ~d, l, c, h, os, r) == Some{x}: Maybe<&2, Ledgers.Step>} -> Safe.Dec(mach, d, l, Ledgers.Place{c, h, r}, os, x):
  Safe.decided.at(~mach, ~d, Led.tally(~mach, ~d, l, Ledgers.Place{c, h, r}, os), l, c, h, os, r, x, {==})

# Safe.one once the cast of the leader of the later round is known
def Safe.one.cast(
  ~mach: Machine(),
  ~d: Led(mach),
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
  +r2: Nat,
  +v1: Ledgers.Step,
  +v2: Ledgers.Step,
  m: Maybe<&2, Ledgers.Cast>,
  c2: {Cast.casts(m, v2, f => Step.allowed(~mach, ~d, b, Ledgers.Place{c, h, r2}, os, v2, f)) == True{}: Bool},
  hq: {Quorums.Quorum.has(~Ledgers.Step, ~Ledgers.Step.is_eq, Ledgers.Kind.cells(~Machine.Q(mach), ~Led.kind(mach, d), b, Ledgers.Place{c, h, r1}, os), v1) == True{}: Bool},
  hl: {Nat.is_lt(r1, r2) == True{}: Bool}
) -> {v2 == v1: Ledgers.Step}:
  match m:
    case Some{Ledgers.Cast.Vote{x, +f}}:
      Safe.round_safe(~mach, ~d, a, b, later, c, h, os, r1, v1, r2, r2, v2, f)(hq)(hl)(
        Shared.List.all.if_rest(
          Ledgers.Step.is_eq(x, v2),
          u => Step.allowed(~mach, ~d, b, Ledgers.Place{c, h, r2}, os, v2, f)
        )(c2)
      )
    case Some{Ledgers.Cast.Pass{q}}:
      Empty.absurd({v2 == v1: Ledgers.Step}, Shared.Bool.false_ne_true(c2))
    case None{}:
      Empty.absurd({v2 == v1: Ledgers.Step}, Shared.Bool.false_ne_true(c2))

# Safe.one once both decisions are split
def Safe.one.at(
  ~mach: Machine(),
  ~d: Led(mach),
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
  +r2: Nat,
  +v1: Ledgers.Step,
  +v2: Ledgers.Step,
  d1: Safe.Dec(mach, d, b, Ledgers.Place{c, h, r1}, os, v1),
  d2: Safe.Dec(mach, d, b, Ledgers.Place{c, h, r2}, os, v2),
  hl: {Nat.is_lt(r1, r2) == True{}: Bool}
) -> {v2 == v1: Ledgers.Step}:
  match d1 d2:
    case Tuple{p1, Tuple{t1, c1}} Tuple{+p2, Tuple{t2, c2}}:
      Safe.one.cast(
        ~mach,
        ~d,
        a,
        b,
        later,
        c,
        h,
        os,
        r1,
        r2,
        v1,
        v2,
        Led.cast(~mach, ~d, b, Ledgers.Place{c, h, r2}, p2),
        c2,
        Quorums.Quorum.major_has(~Ledgers.Step, ~Ledgers.Step.is_eq, ~Ledgers.Step.laws(), Ledgers.Kind.cells(~Machine.Q(mach), ~Led.kind(mach, d), b, Ledgers.Place{c, h, r1}, os), v1)(t1),
        hl
      )

# two rounds of a height, the first below the second, decide one step
def Safe.one(
  ~mach: Machine(),
  ~d: Led(mach),
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
  +r2: Nat,
  +v1: Ledgers.Step,
  +v2: Ledgers.Step
) -> {Round.decide(~mach, ~d, b, c, h, os, r1) == Some{v1}: Maybe<&2, Ledgers.Step>}
  -> {Round.decide(~mach, ~d, b, c, h, os, r2) == Some{v2}: Maybe<&2, Ledgers.Step>}
  -> {Nat.is_lt(r1, r2) == True{}: Bool}
  -> {v2 == v1: Ledgers.Step}:
  e1 => e2 => hl => Safe.one.at(
    ~mach,
    ~d,
    a,
    b,
    later,
    c,
    h,
    os,
    r1,
    r2,
    v1,
    v2,
    Safe.decided(~mach, ~d, b, c, h, os, r1, v1)(e1),
    Safe.decided(~mach, ~d, b, c, h, os, r2, v2)(e2),
    hl
  )

# Safe.same once it is known which round is lower
def Safe.same.at(
  ~mach: Machine(),
  ~d: Led(mach),
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
  +r2: Nat,
  +v: Ledgers.Step,
  +v2: Ledgers.Step,
  l1: Bool,
  +el1: {Nat.is_lt(r, r2) == l1: Bool},
  l2: Bool,
  +el2: {Nat.is_lt(r2, r) == l2: Bool}
) -> {Round.decide(~mach, ~d, b, c, h, os, r) == Some{v}: Maybe<&2, Ledgers.Step>}
  -> {Round.decide(~mach, ~d, b, c, h, os, r2) == Some{v2}: Maybe<&2, Ledgers.Step>}
  -> {v2 == v: Ledgers.Step}:
  match l1 l2:
    case True{} y:
      e1 => e2 => Safe.one(~mach, ~d, a, b, later, c, h, os, r, r2, v, v2)(e1)(e2)(el1)
    case False{} True{}:
      e1 => e2 => Equal.sym(
        Ledgers.Step,
        v,
        v2,
        Safe.one(~mach, ~d, a, b, later, c, h, os, r2, r, v2, v)(e2)(e1)(el2)
      )
    case False{} False{}:
      e1 => e2 => Shared.Maybe.some_inj(
        Ledgers.Step,
        v2,
        v,
        Equal.trans(
          Maybe<&2, Ledgers.Step>,
          Some{v2},
          Round.decide(~mach, ~d, b, c, h, os, r2),
          Some{v},
          Equal.sym(Maybe<&2, Ledgers.Step>, Round.decide(~mach, ~d, b, c, h, os, r2), Some{v2}, e2),
          %Shared.Nat.is_eq_sound(
            r,
            r2
          )(
            Equal.trans(
              Bool,
              Nat.is_eq(r, r2),
              Bool.and(Nat.is_le(r, r2), Nat.is_le(r2, r)),
              True{},
              Equal.sym(Bool, Bool.and(Nat.is_le(r, r2), Nat.is_le(r2, r)), Nat.is_eq(r, r2), Shared.Nat.le_both(r, r2)),
              Shared.Bool.and_both(Nat.is_le(r, r2), Nat.is_le(r2, r))(Shared.Nat.nlt_le(r2, r)(el2))(
                Shared.Nat.nlt_le(r, r2)(el1)
              )
            )
          ): {Round.decide(~mach, ~d, b, c, h, os, _) == Some{v}: Maybe<&2, Ledgers.Step>}
          e1
        )
      )

# any two rounds of a height decide one step, in an honest ledger
def Safe.same(
  ~mach: Machine(),
  ~d: Led(mach),
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
  +r2: Nat,
  +v: Ledgers.Step,
  +v2: Ledgers.Step
) -> {Round.decide(~mach, ~d, b, c, h, os, r) == Some{v}: Maybe<&2, Ledgers.Step>}
  -> {Round.decide(~mach, ~d, b, c, h, os, r2) == Some{v2}: Maybe<&2, Ledgers.Step>}
  -> {v2 == v: Ledgers.Step}:
  Safe.same.at(~mach, ~d, a, b, later, c, h, os, r, r2, v, v2, Nat.is_lt(r, r2), {==}, Nat.is_lt(r2, r), {==})

# a round up to k that decided x, of a height that decided x up to k
def Safe.Round(
  -mach: Machine(),
  -d: Led(mach),
  -l: Led.L(mach, d),
  -c: Ledgers.Line,
  -h: U32,
  -os: List<&2, String>,
  -k: Nat,
  -x: Ledgers.Step
) -> Type:
  Exists(
    Nat,
    r => {Nat.is_le(r, k) == True{}: Bool} & {Round.decide(~mach, ~d, l, c, h, os, r) == Some{x}: Maybe<&2, Ledgers.Step>}
  )

# a round up to p is a round up to 1 + p
def Safe.height_round.lift(
  ~mach: Machine(),
  ~d: Led(mach),
  -l: Led.L(mach, d),
  -c: Ledgers.Line,
  -h: U32,
  -os: List<&2, String>,
  +p: Nat,
  -x: Ledgers.Step,
  ex: Safe.Round(mach, d, l, c, h, os, p, x)
) -> Safe.Round(mach, d, l, c, h, os, 1n+p, x):
  match ex:
    case Tuple{+r, Tuple{hle, hd}}:
      Tuple{r, Tuple{Shared.Nat.le_succ(r, p)(hle), hd}}

# Safe.height_round once the round 1 + p is known
def Safe.height_round.at(
  ~mach: Machine(),
  ~d: Led(mach),
  -l: Led.L(mach, d),
  -c: Ledgers.Line,
  -h: U32,
  -os: List<&2, String>,
  +p: Nat,
  -x: Ledgers.Step,
  m: Maybe<&2, Ledgers.Step>,
  em: {Round.decide(~mach, ~d, l, c, h, os, 1n+p) == m: Maybe<&2, Ledgers.Step>},
  ih: {Height.decide(~mach, ~d, l, c, h, os, p) == Some{x}: Maybe<&2, Ledgers.Step>} -> Safe.Round(mach, d, l, c, h, os, p, x)
) -> {Step.first(m, u => Height.decide(~mach, ~d, l, c, h, os, p)) == Some{x}: Maybe<&2, Ledgers.Step>} -> Safe.Round(mach, d, l, c, h, os, 1n+p, x):
  match m:
    case Some{y}:
      e => Tuple{1n+p, Tuple{Shared.Nat.le_refl(1n+p), Equal.trans(Maybe<&2, Ledgers.Step>, Round.decide(~mach, ~d, l, c, h, os, 1n+p), Some{y}, Some{x}, em, e)}}
    case None{}:
      e => Safe.height_round.lift(~mach, ~d, l, c, h, os, p, x, ih(e))

# a height that decided x up to k did in some round up to k
def Safe.height_round(
  ~mach: Machine(),
  ~d: Led(mach),
  +l: Led.L(mach, d),
  +c: Ledgers.Line,
  +h: U32,
  +os: List<&2, String>,
  k: Nat,
  -x: Ledgers.Step
) -> {Height.decide(~mach, ~d, l, c, h, os, k) == Some{x}: Maybe<&2, Ledgers.Step>} -> Safe.Round(mach, d, l, c, h, os, k, x):
  match k:
    case 0n:
      e => Tuple{0n, Tuple{{==}, e}}
    case 1n+(+p):
      Safe.height_round.at(
        ~mach,
        ~d,
        l,
        c,
        h,
        os,
        p,
        x,
        Round.decide(~mach, ~d, l, c, h, os, 1n+p),
        {==},
        Safe.height_round(~mach, ~d, l, c, h, os, p, x)
      )

# Safe.height_of when the round 1 + p decided nothing, once it is known
# whether r is 1 + p
def Safe.height_of.none(
  ~mach: Machine(),
  ~d: Led(mach),
  +b: Led.L(mach, d),
  +c: Ledgers.Line,
  +h: U32,
  +os: List<&2, String>,
  +p: Nat,
  +r: Nat,
  -v: Ledgers.Step,
  eb: Bool,
  ee: {Nat.is_eq(r, 1n+p) == eb: Bool},
  em: {Round.decide(~mach, ~d, b, c, h, os, 1n+p) == None{}: Maybe<&2, Ledgers.Step>},
  hd: {Round.decide(~mach, ~d, b, c, h, os, r) == Some{v}: Maybe<&2, Ledgers.Step>},
  hle: {Nat.is_le(r, 1n+p) == True{}: Bool},
  ih: {Nat.is_le(r, p) == True{}: Bool} -> {Height.decide(~mach, ~d, b, c, h, os, p) == Some{v}: Maybe<&2, Ledgers.Step>}
) -> {Height.decide(~mach, ~d, b, c, h, os, p) == Some{v}: Maybe<&2, Ledgers.Step>}:
  match eb:
    case True{}:
      Empty.absurd(
        {Height.decide(~mach, ~d, b, c, h, os, p) == Some{v}: Maybe<&2, Ledgers.Step>},
        Shared.Maybe.none_ne_some(
          Ledgers.Step,
          v,
          Equal.trans(
            Maybe<&2, Ledgers.Step>,
            None{},
            Round.decide(~mach, ~d, b, c, h, os, 1n+p),
            Some{v},
            Equal.sym(Maybe<&2, Ledgers.Step>, Round.decide(~mach, ~d, b, c, h, os, 1n+p), None{}, em),
            %Shared.Nat.is_eq_sound(r, 1n+p)(ee): {Round.decide(~mach, ~d, b, c, h, os, _) == Some{v}: Maybe<&2, Ledgers.Step>}
            hd
          )
        )
      )
    case False{}:
      ih(Shared.Nat.le_step(r, p)(hle)(ee))

# Safe.height_of once the round 1 + p is known
def Safe.height_of.at(
  ~mach: Machine(),
  ~d: Led(mach),
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
  +p: Nat,
  +r: Nat,
  +v: Ledgers.Step,
  m: Maybe<&2, Ledgers.Step>,
  +em: {Round.decide(~mach, ~d, b, c, h, os, 1n+p) == m: Maybe<&2, Ledgers.Step>},
  +hd: {Round.decide(~mach, ~d, b, c, h, os, r) == Some{v}: Maybe<&2, Ledgers.Step>},
  +hle: {Nat.is_le(r, 1n+p) == True{}: Bool},
  ih: {Nat.is_le(r, p) == True{}: Bool} -> {Height.decide(~mach, ~d, b, c, h, os, p) == Some{v}: Maybe<&2, Ledgers.Step>}
) -> {Step.first(m, u => Height.decide(~mach, ~d, b, c, h, os, p)) == Some{v}: Maybe<&2, Ledgers.Step>}:
  match m:
    case Some{+y}:
      Equal.cong(
        Ledgers.Step,
        Maybe<&2, Ledgers.Step>,
        z => Some{z},
        y,
        v,
        Safe.same(~mach, ~d, a, b, later, c, h, os, r, 1n+p, v, y)(hd)(em)
      )
    case None{}:
      Safe.height_of.none(~mach, ~d, b, c, h, os, p, r, v, Nat.is_eq(r, 1n+p), {==}, em, hd, hle, ih)

# a height decides x up to k when a round up to k decided x, in an honest
# ledger
def Safe.height_of(
  ~mach: Machine(),
  ~d: Led(mach),
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
  k: Nat,
  +r: Nat,
  +v: Ledgers.Step
) -> {Round.decide(~mach, ~d, b, c, h, os, r) == Some{v}: Maybe<&2, Ledgers.Step>}
  -> {Nat.is_le(r, k) == True{}: Bool}
  -> {Height.decide(~mach, ~d, b, c, h, os, k) == Some{v}: Maybe<&2, Ledgers.Step>}:
  match k:
    case 0n:
      hd => hle =>
        %Safe.le_zero_eq(r)(hle): {Round.decide(~mach, ~d, b, c, h, os, _) == Some{v}: Maybe<&2, Ledgers.Step>}
        hd
    case 1n+(+p):
      +hd => +hle => Safe.height_of.at(
        ~mach,
        ~d,
        a,
        b,
        later,
        c,
        h,
        os,
        p,
        r,
        v,
        Round.decide(~mach, ~d, b, c, h, os, 1n+p),
        {==},
        hd,
        hle,
        hl2 => Safe.height_of(~mach, ~d, a, b, later, c, h, os, p, r, v)(hd)(hl2)
      )

# the law that no ballot is above the bound of rounds, of the laws rl
def Safe.laws.rounds_le(
  -Q: Data,
  -c: Codes.Codec(Q),
  -k: Ledgers.Ledger.Kind(Q),
  rl: Ledgers.Laws.Rounds(Q, c, k)
) -> @l: Ledgers.Kind.L(Q, k) -> @b: Ledgers.Ballot -> @line: Ledgers.Line -> @h: U32 -> @r: Nat -> @voter: String -> {
  Ledgers.Kind.has(~Q, ~c, ~k, l, Ledgers.Entry.Ballot{b}) == True{}: Bool
} -> {
  Ledgers.Ballot.is_at(b, Ledgers.Place{line, h, r}, voter) == True{}: Bool
} -> {Nat.is_le(r, Ledgers.Kind.rounds(Q, k)(l)(line)(h)) == True{}: Bool}:
  match rl:
    case Tuple{p1, p2}:
      p1

# the law that a bound of rounds is the round of a ballot, of the laws rl
def Safe.laws.rounds_has(
  -Q: Data,
  -c: Codes.Codec(Q),
  -k: Ledgers.Ledger.Kind(Q),
  rl: Ledgers.Laws.Rounds(Q, c, k)
) -> @l: Ledgers.Kind.L(Q, k) -> @line: Ledgers.Line -> @h: U32 -> {
  Nat.is_eq(Ledgers.Kind.rounds(Q, k)(l)(line)(h), 0n) == False{}: Bool
} -> Exists(
  Ledgers.Ballot,
  b => {Ledgers.Kind.has(~Q, ~c, ~k, l, Ledgers.Entry.Ballot{b}) == True{}: Bool}
    & {
      Ledgers.Ballot.is_at(b, Ledgers.Place{line, h, Ledgers.Kind.rounds(Q, k)(l)(line)(h)}, Ledgers.Ballot.voter(b)) == True{}: Bool
    }
):
  match rl:
    case Tuple{p1, p2}:
      p2

# Safe.rounds_mono from a ballot at the bound of rounds of a
def Safe.rounds_mono.ex(
  ~mach: Machine(),
  ~d: Led(mach),
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
  ex: Exists(
    Ledgers.Ballot,
    e => {Led.has(~mach, ~d, a, Ledgers.Entry.Ballot{e}) == True{}: Bool}
      & {Ledgers.Ballot.is_at(e, Ledgers.Place{c, h, Ledgers.Kind.rounds(Machine.Q(mach), Led.kind(mach, d))(a)(c)(h)}, Ledgers.Ballot.voter(e)) == True{}: Bool}
  )
) -> {Nat.is_le(Ledgers.Kind.rounds(Machine.Q(mach), Led.kind(mach, d))(a)(c)(h), Ledgers.Kind.rounds(Machine.Q(mach), Led.kind(mach, d))(b)(c)(h)) == True{}: Bool}:
  match ex:
    case Tuple{+e0, Tuple{hh, hat}}:
      Safe.laws.rounds_le(
        Machine.Q(mach),
        Machine.code(mach),
        Led.kind(mach, d),
        Safe.rounds_law(mach, d)
      )(b)(e0)(c)(h)(Ledgers.Kind.rounds(Machine.Q(mach), Led.kind(mach, d))(a)(c)(h))(Ledgers.Ballot.voter(e0))(
        Safe.has_grows(~mach, ~d, a, b, later, Ledgers.Entry.Ballot{e0})(hh)
      )(hat)

# Safe.rounds_mono once it is known whether the bound of a is 0
def Safe.rounds_mono.at(
  ~mach: Machine(),
  ~d: Led(mach),
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
  eb: Bool,
  ee: {Nat.is_eq(Ledgers.Kind.rounds(Machine.Q(mach), Led.kind(mach, d))(a)(c)(h), 0n) == eb: Bool}
) -> {Nat.is_le(Ledgers.Kind.rounds(Machine.Q(mach), Led.kind(mach, d))(a)(c)(h), Ledgers.Kind.rounds(Machine.Q(mach), Led.kind(mach, d))(b)(c)(h)) == True{}: Bool}:
  match eb:
    case True{}:
      %Equal.sym(Nat, Ledgers.Kind.rounds(Machine.Q(mach), Led.kind(mach, d))(a)(c)(h), 0n, Shared.Nat.is_eq_sound(Ledgers.Kind.rounds(Machine.Q(mach), Led.kind(mach, d))(a)(c)(h), 0n)(ee)): {
        Nat.is_le(_, Ledgers.Kind.rounds(Machine.Q(mach), Led.kind(mach, d))(b)(c)(h)) == True{}: Bool
      }
      Shared.Nat.le_zero(Ledgers.Kind.rounds(Machine.Q(mach), Led.kind(mach, d))(b)(c)(h))
    case False{}:
      Safe.rounds_mono.ex(
        ~mach,
        ~d,
        a,
        b,
        later,
        c,
        h,
        Safe.laws.rounds_has(Machine.Q(mach), Machine.code(mach), Led.kind(mach, d), Safe.rounds_law(mach, d))(a)(c)(h)(ee)
      )

# the bound of rounds of a height only grows in a later ledger
def Safe.rounds_mono(
  ~mach: Machine(),
  ~d: Led(mach),
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
  +h: U32
) -> {Nat.is_le(Ledgers.Kind.rounds(Machine.Q(mach), Led.kind(mach, d))(a)(c)(h), Ledgers.Kind.rounds(Machine.Q(mach), Led.kind(mach, d))(b)(c)(h)) == True{}: Bool}:
  Safe.rounds_mono.at(~mach, ~d, a, b, later, c, h, Nat.is_eq(Ledgers.Kind.rounds(Machine.Q(mach), Led.kind(mach, d))(a)(c)(h), 0n), {==})

# Safe.decide once a round of the earlier ledger that decided v is known
def Safe.decide.at(
  ~mach: Machine(),
  ~d: Led(mach),
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
  ex: Safe.Round(mach, d, a, c, h, os, Ledgers.Kind.rounds(Machine.Q(mach), Led.kind(mach, d))(a)(c)(h), v)
) -> {Height.decide(~mach, ~d, b, c, h, os, Ledgers.Kind.rounds(Machine.Q(mach), Led.kind(mach, d))(b)(c)(h)) == Some{v}: Maybe<&2, Ledgers.Step>}:
  match ex:
    case Tuple{+r, Tuple{hle, hdr}}:
      Safe.height_of(~mach, ~d, a, b, later, c, h, os, Ledgers.Kind.rounds(Machine.Q(mach), Led.kind(mach, d))(b)(c)(h), r, v)(
        Safe.decide_kept(~mach, ~d, a, b, later, c, h, os, r, v)(hdr)
      )(Shared.Nat.le_trans(r, Ledgers.Kind.rounds(Machine.Q(mach), Led.kind(mach, d))(a)(c)(h), Ledgers.Kind.rounds(Machine.Q(mach), Led.kind(mach, d))(b)(c)(h))(hle)(Safe.rounds_mono(~mach, ~d, a, b, later, c, h)))

# a height decides the same step in a later ledger
def Safe.decide(
  ~mach: Machine(),
  ~d: Led(mach),
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
  hd => Safe.decide.at(
    ~mach,
    ~d,
    a,
    b,
    later,
    c,
    h,
    os,
    v,
    Safe.height_round(
      ~mach,
      ~d,
      a,
      c,
      h,
      os,
      Ledgers.Kind.rounds(Machine.Q(mach), Led.kind(mach, d))(a)(c)(h),
      v
    )(hd)
  )

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
  +la: Led.L(mach, d),
  +lb: Led.L(mach, d),
  +w: List<&2, U32>,
  +n: Ledgers.Name,
  +e: Entry(mach),
  m: Maybe<&2, Entry(mach)>,
  em: {Led.get(~mach, ~d, la, n) == m: Maybe<&2, Entry(mach)>},
  +g: Led.Grows(mach, d, la, lb),
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
      Hist.gets(~mach, ~d, la, lb, g)(n)(e)(Equal.trans(Maybe<&2, Entry(mach)>, Led.get(~mach, ~d, la, n), Some{x}, Some{e}, em, h))
    case None{}:
      Ext.add_into.none(~mach, ~d, lb, w, n, e, hw, h)

# a ledger with data that lb holds gives what lb gives
def Ext.add_into.pi(
  ~mach: Machine(),
  ~d: Led(mach),
  +la: Led.L(mach, d),
  +lb: Led.L(mach, d),
  +w: List<&2, U32>,
  +g: Led.Grows(mach, d, la, lb),
  +hw: {Ext.has(~mach, ~d, lb, w) == True{}: Bool}
) -> Ledgers.Kind.Grows(Machine.Q(mach), Led.kind(mach, d), Led.add(~mach, ~d, la, Ledgers.Entry.Data{w}), lb):
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
        Ledgers.Laws.get_add(Machine.Q(mach), Machine.code(mach), Led.kind(mach, d), Led.laws(mach, d))(la)(Ledgers.Entry.Data{w})(n)
      ),
      h
    )
  )

# a ledger la that grows into lb, and data w that lb holds
def Ext.Into(-mach: Machine(), -d: Led(mach)) -> Data:
  +Sigma<Led.L(mach, d), la => +Sigma<Led.L(mach, d), lb => +Sigma<List<&2, U32>, w => +Sigma<
    Led.Grows(mach, d, la, lb),
    g => {Ext.has(~mach, ~d, lb, w) == True{}: Bool}>>>>

# la of x with the data w of x
def Ext.Into.from(~mach: Machine(), ~d: Led(mach), x: Ext.Into(mach, d)) -> Led.L(mach, d):
  match x:
    case Tuple{la, Tuple{lb, Tuple{w, r}}}:
      Led.add(~mach, ~d, la, Ledgers.Entry.Data{w})

# lb of x
def Ext.Into.to(-mach: Machine(), -d: Led(mach), x: Ext.Into(mach, d)) -> Led.L(mach, d):
  match x:
    case Tuple{la, Tuple{lb, r}}:
      lb

# what la of x with the data w of x holds, lb of x holds
def Ext.into.has(
  ~mach: Machine(),
  ~d: Led(mach),
  x: Ext.Into(mach, d),
  +e: Entry(mach)
) -> {Ledgers.Kind.has(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), Ext.Into.from(~mach, ~d, x), e) == True{}: Bool}
  -> {Ledgers.Kind.has(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), Ext.Into.to(mach, d, x), e) == True{}: Bool}:
  match x:
    case Tuple{+la, Tuple{+lb, Tuple{+w, Tuple{+g, +hw}}}}:
      h => Ledgers.Kind.has_of_get(
        ~Machine.Q(mach),
        ~Machine.code(mach),
        ~Led.kind(mach, d),
        Ledgers.Laws.get_named(Machine.Q(mach), Machine.code(mach), Led.kind(mach, d), Led.laws(mach, d)),
        lb,
        Entry.name(~mach, e),
        e,
        Ext.add_into.pi(~mach, ~d, la, lb, w, g, hw)(Entry.name(~mach, e))(e)(
          Ledgers.Kind.get_of_has(
            ~Machine.Q(mach),
            ~Machine.code(mach),
            ~Led.kind(mach, d),
            Led.add(~mach, ~d, la, Ledgers.Entry.Data{w}),
            Entry.name(~mach, e),
            e,
            {==},
            h
          )
        )
      )

# a ledger with data that lb holds still grows into lb
def Ext.add_into(
  ~mach: Machine(),
  ~d: Led(mach),
  +la: Led.L(mach, d),
  +lb: Led.L(mach, d),
  +w: List<&2, U32>,
  +g: Led.Grows(mach, d, la, lb),
  +hw: {Ext.has(~mach, ~d, lb, w) == True{}: Bool}
) -> Led.Grows(mach, d, Led.add(~mach, ~d, la, Ledgers.Entry.Data{w}), lb):
  Ledgers.Kind.grows_core(
    ~Machine.Q(mach),
    ~Machine.code(mach),
    ~Led.kind(mach, d),
    ~Led.laws(mach, d),
    ~Ext.Into(mach, d),
    ~(x => Ext.Into.from(~mach, ~d, x)),
    ~(x => Ext.Into.to(mach, d, x)),
    ~(x => e => h => Ext.into.has(~mach, ~d, x, e)(h)),
    Tuple{la, Tuple{lb, Tuple{w, Tuple{g, hw}}}}
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
        Hist.refl(~mach, ~d, base),
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

# that a ledger s reads the run r: the ledger of r and s are one ledger with
# data put (xs and ws), and s holds xs when it holds what r added
def Keep.Base(-mach: Machine(), -d: Led(mach), -s: Led.L(mach, d), -r: Run<Led.L(mach, d)>) -> Data:
  +Sigma<List<&2, List<&2, U32>>, xs => +Sigma<Led.L(mach, d), l0 => +Sigma<List<&2, List<&2, U32>>, ws => +Sigma<
    {Run.ledger(Led.L(mach, d), r) == Led.puts(~mach, ~d, xs, l0): Led.L(mach, d)},
    e1 => +Sigma<
      {s == Led.puts(~mach, ~d, ws, l0): Led.L(mach, d)},
      es => {Ext.holds(~mach, ~d, s, xs) == Ext.holds(~mach, ~d, s, Run.added(Led.L(mach, d), r)): Bool}>>>>>

# a run that follows a run that s reads is read by s
def Keep.base(
  ~mach: Machine(),
  ~d: Led(mach),
  +s: Led.L(mach, d),
  +r: Run<Led.L(mach, d)>,
  +r2: Run<Led.L(mach, d)>,
  bd: Keep.Base(mach, d, s, r),
  g: Ext.Gain(mach, d, s, r, r2)
) -> Keep.Base(mach, d, s, r2):
  match bd:
    case Tuple{+xs, Tuple{+l0, Tuple{+ws, Tuple{e1, Tuple{es, e2}}}}}:
      match g:
        case Tuple{+ys, Tuple{+zs, Tuple{a1, Tuple{l1, h1}}}}:
          Tuple{
            List.append(&2, List<&2, U32>, xs, zs),
            Tuple{
              l0,
              Tuple{
                ws,
                Tuple{
                  Equal.trans(
                    Led.L(mach, d),
                    Run.ledger(Led.L(mach, d), r2),
                    Led.puts(~mach, ~d, zs, Run.ledger(Led.L(mach, d), r)),
                    Led.puts(~mach, ~d, List.append(&2, List<&2, U32>, xs, zs), l0),
                    l1,
                    Equal.trans(
                      Led.L(mach, d),
                      Led.puts(~mach, ~d, zs, Run.ledger(Led.L(mach, d), r)),
                      Led.puts(~mach, ~d, zs, Led.puts(~mach, ~d, xs, l0)),
                      Led.puts(~mach, ~d, List.append(&2, List<&2, U32>, xs, zs), l0),
                      Equal.cong(
                        Led.L(mach, d),
                        Led.L(mach, d),
                        z => Led.puts(~mach, ~d, zs, z),
                        Run.ledger(Led.L(mach, d), r),
                        Led.puts(~mach, ~d, xs, l0),
                        e1
                      ),
                      Ext.puts_append(~mach, ~d, xs, zs, l0)
                    )
                  ),
                  Tuple{
                    es,
                    Ext.based.holds(
                      ~mach,
                      ~d,
                      s,
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
              }
            }
          }

# a ledger that is l0 with data put grows from l0
def Keep.base_from(
  ~mach: Machine(),
  ~d: Led(mach),
  +l0: Led.L(mach, d),
  -s: Led.L(mach, d),
  +ws: List<&2, List<&2, U32>>,
  es: {s == Led.puts(~mach, ~d, ws, l0): Led.L(mach, d)}
) -> Led.Grows(mach, d, l0, s):
  %Equal.sym(Led.L(mach, d), s, Led.puts(~mach, ~d, ws, l0), es): Led.Grows(mach, d, l0, _)
  Hist.puts(~mach, ~d, ws, l0)

# the ledger of a run that s reads grows into s, once s holds what it added
def Keep.base_grows(
  ~mach: Machine(),
  ~d: Led(mach),
  +s: Led.L(mach, d),
  r: Run<Led.L(mach, d)>,
  bd: Keep.Base(mach, d, s, r),
  h: {Ext.holds(~mach, ~d, s, Run.added(Led.L(mach, d), r)) == True{}: Bool}
) -> Led.Grows(mach, d, Run.ledger(Led.L(mach, d), r), s):
  match bd:
    case Tuple{+xs, Tuple{+l0, Tuple{+ws, Tuple{e1, Tuple{es, e2}}}}}:
      %Equal.sym(Led.L(mach, d), Run.ledger(Led.L(mach, d), r), Led.puts(~mach, ~d, xs, l0), e1): Led.Grows(
        mach,
        d,
        _,
        s
      )
      Ext.puts_into(
        ~mach,
        ~d,
        xs,
        l0,
        s,
        Keep.base_from(~mach, ~d, l0, s, ws, es),
        Equal.trans(
          Bool,
          Ext.holds(~mach, ~d, s, xs),
          Ext.holds(~mach, ~d, s, Run.added(Led.L(mach, d), r)),
          True{},
          e2,
          h
        )
      )

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
  +bd: Keep.Base(mach, d, l, Run{lr, t, a}),
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
                    Keep.base_grows(~mach, ~d, l, Run{lr, t, a}, bd, ha)
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
      @k2: List<&2, U32> -> @y: Maybe<&2, List<&2, U32>> -> {
        Shared.List.is_eq(~U32, ~U32.is_eq, k, k2) == False{}: Bool
      } -> {
        Trees.Look.known(Trees.Ops.look(Led.L(mach, d), Led.tree(mach, d))(l)(Tip.log(t))(k2))
          == Some{y}: Maybe<&2, Maybe<&2, List<&2, U32>>>
      } -> {
        Trees.Look.known(Trees.Ops.look(Led.L(mach, d), Led.tree(mach, d))(l)(Trees.Edit.root(e))(k2))
          == Some{y}: Maybe<&2, Maybe<&2, List<&2, U32>>>
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
      Keep.found_back(
        Trees.Ops.look(Led.L(mach, d), Led.tree(mach, d))(l)(Trees.Edit.root(e))(key),
        val,
        w2(key)(Some{val})(ne)(Keep.found(Trees.Ops.look(Led.L(mach, d), Led.tree(mach, d))(l)(Tip.log(t))(key), val, hg))
      )

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
  +bd: Keep.Base(mach, d, l, Run{lr, t, a}),
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
    Hist.write(mach, d)(lr)(l)(Tip.log(t))(k)(Some{x})(e)(ep)(Keep.base_grows(~mach, ~d, l, Run{lr, t, a}, bd, ha))(
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
  +bd: Keep.Base(mach, d, l, Run{lr, t, a}),
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
  bd: Keep.Base(mach, d, l, r),
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
  bd: Keep.Base(mach, d, l, r),
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
  bd: Keep.Base(mach, d, l, r),
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
  bd: Keep.Base(mach, d, l, r),
  hg: @r1: Run<Led.L(mach, d)> -> Keep.Base(mach, d, l, r1) -> Keep.Has(mach, d, l, key, val, r1)
    -> Keep.Out(mach, d, l, key, val, g(r1))
) -> Keep.Out(mach, d, l, key, val, Maybe.bind(&2, Run<Led.L(mach, d)>, Run<Led.L(mach, d)>, m, g)):
  match m:
    case None{}:
      Unit{}
    case Some{+r1}:
      hg(r1)(Keep.base(~mach, ~d, l, r, r1, bd, gm))(hm)

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
  +bd: Keep.Base(mach, d, l, r),
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
  bd: Keep.Base(mach, d, l, r),
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
  +bd: Keep.Base(mach, d, l, r),
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
  +bd: Keep.Base(mach, d, l, r),
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
  bd: Keep.Base(mach, d, l, r),
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
  +bd: Keep.Base(mach, d, l, r),
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
      Keep.base(
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
  +bd: Keep.Base(mach, d, l, r),
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
        Keep.base(~mach, ~d, l, r, Run.over(~mach, ~d, r, ns, h), bd, Ext.over(~mach, ~d, l, r, ns, h)),
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
  bd: Keep.Base(mach, d, l, r),
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
  bd: Keep.Base(mach, d, l, r),
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
  bd: Keep.Base(mach, d, l, r),
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
      Keep.Base(mach, d, l, r) & Keep.Has(mach, d, l, key, val, r)

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
  bd: Keep.Base(mach, d, l, r1)
) -> Keep.All(mach, d, l, key, val, m2):
  match m2:
    case None{}:
      Unit{}
    case Some{+r2}:
      Tuple{Keep.base(~mach, ~d, l, r1, r2, bd, gm), ko}

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
          Tuple{Tuple{[], Tuple{l, Tuple{[], Tuple{{==}, Tuple{{==}, {==}}}}}}, u => hg}
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
  Hist.trans(~mach, ~d,
    la,
    a,
    lb,
    Ext.based_grows(~mach, ~d, a, Run{la, ta, aa}, bda, ha),
    Hist.trans(~mach, ~d, a, b, lb, Led.later_grows(~mach, ~d, a, b)(later), Ext.based_from(~mach, ~d, b, Run{lb, ta, aa}, bdb))
  )

# what a ledger holds, a ledger that grows from it holds
def Hist.holds_grows(
  ~mach: Machine(),
  ~d: Led(mach),
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  +g: Led.Grows(mach, d, a, b),
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
            g
          )(Hist.has(~mach, ~d, a, w)(Shared.List.all.if_hit(Ext.has(~mach, ~d, a, w), u => Ext.holds(~mach, ~d, a, r))(h)))
        )
      )(
        Hist.holds_grows(
          ~mach,
          ~d,
          a,
          b,
          g,
          r,
          Shared.List.all.if_rest(Ext.has(~mach, ~d, a, w), u => Ext.holds(~mach, ~d, a, r))(h)
        )
      )

# what an act adds, a ledger that grows holds
def Hist.held_grows(
  ~mach: Machine(),
  ~d: Led(mach),
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  +g: Led.Grows(mach, d, a, b),
  act: Act
) -> {Act.held(~mach, ~d, a, act) == True{}: Bool} -> {Act.held(~mach, ~d, b, act) == True{}: Bool}:
  match act:
    case Act.Taken{vs, h, ns}:
      e => Hist.holds_grows(~mach, ~d, a, b, g, ns, e)
    case Act.Opens{x, t, ns}:
      e => Hist.holds_grows(~mach, ~d, a, b, g, ns, e)
    case Act.Stale{}:
      e => e
    case Act.Label{x}:
      e => e

# b holds what a holds
def Sim.holds_b(
  ~mach: Machine(),
  ~d: Led(mach),
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  +later: {
    Bool.and(
      Ledgers.Kind.grows(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), a, b),
      Led.honest(~mach, ~d, b)
    )
      == True{}: Bool
  },
  +ns: List<&2, List<&2, U32>>,
  +h: {Ext.holds(~mach, ~d, a, ns) == True{}: Bool}
) -> {Ext.holds(~mach, ~d, b, ns) == True{}: Bool}:
  Hist.holds_grows(~mach, ~d, a, b, Led.later_grows(~mach, ~d, a, b)(later), ns, h)

# the ledgers of two related runs grow, once a holds what the run in a added
def Sim.grow_of(
  ~mach: Machine(),
  ~d: Led(mach),
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
          Sim.grows(~mach, ~d, a, b, later, la, ta, aa, lb, bda, bdb, ha)

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

# Sim.cond, when the results in b are equal once a holds what the run in a
# added (heq)
def Sim.cond.held(
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
    -> @r2: Run<Led.L(mach, d)> -> {ma == Some{r2}: Maybe<&2, Run<Led.L(mach, d)>>}
    -> {Ext.holds(~mach, ~d, a, Run.added(Led.L(mach, d), r2)) == True{}: Bool} -> {mb2 == mb: Maybe<&2, Run<Led.L(mach, d)>>},
  inner: Sim.Has(mach, d, a, b, ra, rb) -> Sim.Out(mach, d, a, b, ma, mb2)
) -> Sim.Out(mach, d, a, b, ma, mb):
  match ma:
    case None{}:
      Unit{}
    case Some{+ra2}:
      +hh =>
        +hr = Ext.gain_holds(~mach, ~d, a, ra, ra2, gm, hh)
        +rel = sh(hr)
        %heq(rel)(hr)(ra2)({==})(hh): Sim.R2(mach, d, a, b, ra2, _)
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

# Sim.add once the write's nodes and the relation are known
def Sim.add.fin(
  ~mach: Machine(),
  ~d: Led(mach),
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
  +rb: Run<Led.L(mach, d)>,
  +k: List<&2, U32>,
  +x: List<&2, U32>,
  +e: Trees.Edit,
  ep: {Tree.put(~mach, ~d, la, Tip.log(ta), k, Some{x}) == Some{e}: Maybe<&2, Trees.Edit>},
  em: {Tip.find(~mach, ~d, la, ta, k) == Some{None{}}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
  rel: Sim.Rel(mach, d, a, b, Run{la, ta, aa}, rb),
  +ha: {Ext.holds(~mach, ~d, a, aa) == True{}: Bool}
) -> Sim.R2(
  mach,
  d,
  a,
  b,
  Run{
    Led.puts(~mach, ~d, Trees.Edit.nodes(e), la),
    Tip.logged(ta, Trees.Edit.root(e)),
    List.append(&2, List<&2, U32>, Trees.Edit.nodes(e), aa)
  },
  Run.add(~mach, ~d, rb, k, x)
):
  match rel:
    case Tuple{+lb, Tuple{erb, Tuple{+bda, +bdb}}}:
      %Equal.sym(Run<Led.L(mach, d)>, rb, Run{lb, ta, aa}, erb): Sim.R2(
        mach,
        d,
        a,
        b,
        Run{
          Led.puts(~mach, ~d, Trees.Edit.nodes(e), la),
          Tip.logged(ta, Trees.Edit.root(e)),
          List.append(&2, List<&2, U32>, Trees.Edit.nodes(e), aa)
        },
        Run.add(~mach, ~d, _, k, x)
      )
      %Equal.sym(
        Maybe<&2, Maybe<&2, List<&2, U32>>>,
        Tip.find(~mach, ~d, lb, ta, k),
        Some{None{}},
        Hist.find(~mach, ~d, la, lb, Tip.log(ta), k, None{}, Sim.grows(~mach, ~d, a, b, later, la, ta, aa, lb, bda, bdb, ha))(
          em
        )
      ): Sim.R2(
        mach,
        d,
        a,
        b,
        Run{
          Led.puts(~mach, ~d, Trees.Edit.nodes(e), la),
          Tip.logged(ta, Trees.Edit.root(e)),
          List.append(&2, List<&2, U32>, Trees.Edit.nodes(e), aa)
        },
        Run.add.at(~mach, ~d, Run{lb, ta, aa}, k, x, _)
      )
      %Equal.sym(
        Maybe<&2, Trees.Edit>,
        Tree.put(~mach, ~d, lb, Tip.log(ta), k, Some{x}),
        Some{e},
        Hist.put(
          ~mach,
          ~d,
          la,
          lb,
          Tip.log(ta),
          k,
          Some{x},
          e,
          Sim.grows(~mach, ~d, a, b, later, la, ta, aa, lb, bda, bdb, ha)
        )(ep)
      ): Sim.R2(
        mach,
        d,
        a,
        b,
        Run{
          Led.puts(~mach, ~d, Trees.Edit.nodes(e), la),
          Tip.logged(ta, Trees.Edit.root(e)),
          List.append(&2, List<&2, U32>, Trees.Edit.nodes(e), aa)
        },
        Run.logged(~mach, ~d, lb, ta, aa, _)
      )
      Tuple{
        Led.puts(~mach, ~d, Trees.Edit.nodes(e), lb),
        Tuple{
          {==},
          Tuple{
            Ext.based(
              ~mach,
              ~d,
              a,
              Run{la, ta, aa},
              Run{
                Led.puts(~mach, ~d, Trees.Edit.nodes(e), la),
                Tip.logged(ta, Trees.Edit.root(e)),
                List.append(&2, List<&2, U32>, Trees.Edit.nodes(e), aa)
              },
              bda,
              Ext.logged(~mach, ~d, a, la, ta, aa, Some{e})
            ),
            Ext.based(
              ~mach,
              ~d,
              b,
              Run{lb, ta, aa},
              Run{
                Led.puts(~mach, ~d, Trees.Edit.nodes(e), lb),
                Tip.logged(ta, Trees.Edit.root(e)),
                List.append(&2, List<&2, U32>, Trees.Edit.nodes(e), aa)
              },
              bdb,
              Ext.logged(~mach, ~d, b, lb, ta, aa, Some{e})
            )
          }
        }
      }

# Sim.add once the write in a is known (p)
def Sim.add.put(
  ~mach: Machine(),
  ~d: Led(mach),
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
  +rb: Run<Led.L(mach, d)>,
  +k: List<&2, U32>,
  +x: List<&2, U32>,
  p: Maybe<&2, Trees.Edit>,
  ep: {Tree.put(~mach, ~d, la, Tip.log(ta), k, Some{x}) == p: Maybe<&2, Trees.Edit>},
  em: {Tip.find(~mach, ~d, la, ta, k) == Some{None{}}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
  sh: Sim.Has(mach, d, a, b, Run{la, ta, aa}, rb)
) -> Sim.Out(mach, d, a, b, Run.logged(~mach, ~d, la, ta, aa, p), Run.add(~mach, ~d, rb, k, x)):
  match p:
    case None{}:
      Unit{}
    case Some{+e}:
      +hh => Sim.add.fin(
        ~mach,
        ~d,
        a,
        b,
        later,
        la,
        ta,
        aa,
        rb,
        k,
        x,
        e,
        ep,
        em,
        sh(Ext.holds_right(~mach, ~d, a, Trees.Edit.nodes(e), aa)(hh)),
        Ext.holds_right(~mach, ~d, a, Trees.Edit.nodes(e), aa)(hh)
      )

# Sim.add once the read of the key in a is known (m)
def Sim.add.find(
  ~mach: Machine(),
  ~d: Led(mach),
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
  +rb: Run<Led.L(mach, d)>,
  +k: List<&2, U32>,
  +x: List<&2, U32>,
  m: Maybe<&2, Maybe<&2, List<&2, U32>>>,
  em: {Tip.find(~mach, ~d, la, ta, k) == m: Maybe<&2, Maybe<&2, List<&2, U32>>>},
  sh: Sim.Has(mach, d, a, b, Run{la, ta, aa}, rb)
) -> Sim.Out(mach, d, a, b, Run.add.at(~mach, ~d, Run{la, ta, aa}, k, x, m), Run.add(~mach, ~d, rb, k, x)):
  match m:
    case None{}:
      Unit{}
    case Some{Some{o}}:
      Unit{}
    case Some{None{}}:
      Sim.add.put(
        ~mach,
        ~d,
        a,
        b,
        later,
        la,
        ta,
        aa,
        rb,
        k,
        x,
        Tree.put(~mach, ~d, la, Tip.log(ta), k, Some{x}),
        {==},
        em,
        sh
      )

# a write to the log, in a and in b, keeps two runs related
def Sim.add(
  ~mach: Machine(),
  ~d: Led(mach),
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
  +rb: Run<Led.L(mach, d)>,
  +k: List<&2, U32>,
  +x: List<&2, U32>,
  sh: Sim.Has(mach, d, a, b, ra, rb)
) -> Sim.Out(mach, d, a, b, Run.add(~mach, ~d, ra, k, x), Run.add(~mach, ~d, rb, k, x)):
  match ra:
    case Run{+la, +ta, +aa}:
      Sim.add.find(~mach, ~d, a, b, later, la, ta, aa, rb, k, x, Tip.find(~mach, ~d, la, ta, k), {==}, sh)

# a refusal, in a and in b, keeps two runs related
def Sim.stale(
  ~mach: Machine(),
  ~d: Led(mach),
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  +later: {
    Bool.and(
      Ledgers.Kind.grows(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), a, b),
      Led.honest(~mach, ~d, b)
    )
      == True{}: Bool
  },
  +ra: Run<Led.L(mach, d)>,
  +rb: Run<Led.L(mach, d)>,
  +i: Ledgers.Id,
  +q: Hashes.Hash,
  sh: Sim.Has(mach, d, a, b, ra, rb)
) -> Sim.Out(mach, d, a, b, Step.stale(~mach, ~d, ra, i, q), Step.stale(~mach, ~d, rb, i, q)):
  Sim.add(~mach, ~d, a, b, later, ra, rb, Log.out(i), Out.code(Out.Stale{q}, []), sh)

# Sim.step_next once the relation is known
def Sim.next.fin(
  ~mach: Machine(),
  ~d: Led(mach),
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  +la: Led.L(mach, d),
  +ta: Tip,
  +aa: List<&2, List<&2, U32>>,
  +rb: Run<Led.L(mach, d)>,
  +vs: Maybe<&2, List<&2, String>>,
  rel: Sim.Rel(mach, d, a, b, Run{la, ta, aa}, rb)
) -> Sim.Rel(mach, d, a, b, Run{la, Tip.next(ta, vs), aa}, Run.next(Led.L(mach, d), rb, vs)):
  match rel:
    case Tuple{+lb, Tuple{erb, Tuple{bda, bdb}}}:
      %Equal.sym(Run<Led.L(mach, d)>, rb, Run{lb, ta, aa}, erb): Sim.Rel(
        mach,
        d,
        a,
        b,
        Run{la, Tip.next(ta, vs), aa},
        Run.next(Led.L(mach, d), _, vs)
      )
      Tuple{
        lb,
        Tuple{
          {==},
          Tuple{
            Ext.based(
              ~mach,
              ~d,
              a,
              Run{la, ta, aa},
              Run{la, Tip.next(ta, vs), aa},
              bda,
              Ext.next(mach, d, a, Run{la, ta, aa}, vs)
            ),
            Ext.based(
              ~mach,
              ~d,
              b,
              Run{lb, ta, aa},
              Run{lb, Tip.next(ta, vs), aa},
              bdb,
              Ext.next(mach, d, b, Run{lb, ta, aa}, vs)
            )
          }
        }
      }

# one request on, in a and in b, keeps two runs related
def Sim.step_next(
  ~mach: Machine(),
  ~d: Led(mach),
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  ra: Run<Led.L(mach, d)>,
  +rb: Run<Led.L(mach, d)>,
  +vs: Maybe<&2, List<&2, String>>,
  sh: Sim.Has(mach, d, a, b, ra, rb)
) -> Sim.Has(mach, d, a, b, Run.next(Led.L(mach, d), ra, vs), Run.next(Led.L(mach, d), rb, vs)):
  match ra:
    case Run{+la, +ta, +aa}:
      hh => Sim.next.fin(~mach, ~d, a, b, la, ta, aa, rb, vs, sh(hh))

# Sim.over once the relation is known
def Sim.over.fin(
  ~mach: Machine(),
  ~d: Led(mach),
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  +la: Led.L(mach, d),
  +ta: Tip,
  +aa: List<&2, List<&2, U32>>,
  +rb: Run<Led.L(mach, d)>,
  +ns: List<&2, List<&2, U32>>,
  +hc: Maybe<&2, Hashes.Hash>,
  rel: Sim.Rel(mach, d, a, b, Run{la, ta, aa}, rb)
) -> Sim.Rel(
  mach,
  d,
  a,
  b,
  Run{Led.puts(~mach, ~d, ns, la), Tip.over(ta, hc), List.append(&2, List<&2, U32>, ns, aa)},
  Run.over(~mach, ~d, rb, ns, hc)
):
  match rel:
    case Tuple{+lb, Tuple{erb, Tuple{bda, bdb}}}:
      %Equal.sym(Run<Led.L(mach, d)>, rb, Run{lb, ta, aa}, erb): Sim.Rel(
        mach,
        d,
        a,
        b,
        Run{Led.puts(~mach, ~d, ns, la), Tip.over(ta, hc), List.append(&2, List<&2, U32>, ns, aa)},
        Run.over(~mach, ~d, _, ns, hc)
      )
      Tuple{
        Led.puts(~mach, ~d, ns, lb),
        Tuple{
          {==},
          Tuple{
            Ext.based(
              ~mach,
              ~d,
              a,
              Run{la, ta, aa},
              Run{Led.puts(~mach, ~d, ns, la), Tip.over(ta, hc), List.append(&2, List<&2, U32>, ns, aa)},
              bda,
              Ext.over(~mach, ~d, a, Run{la, ta, aa}, ns, hc)
            ),
            Ext.based(
              ~mach,
              ~d,
              b,
              Run{lb, ta, aa},
              Run{Led.puts(~mach, ~d, ns, lb), Tip.over(ta, hc), List.append(&2, List<&2, U32>, ns, aa)},
              bdb,
              Ext.over(~mach, ~d, b, Run{lb, ta, aa}, ns, hc)
            )
          }
        }
      }

# new content, in a and in b, keeps two runs related
def Sim.over(
  ~mach: Machine(),
  ~d: Led(mach),
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  ra: Run<Led.L(mach, d)>,
  +rb: Run<Led.L(mach, d)>,
  +ns: List<&2, List<&2, U32>>,
  +hc: Maybe<&2, Hashes.Hash>,
  sh: Sim.Has(mach, d, a, b, ra, rb)
) -> Sim.Has(mach, d, a, b, Run.over(~mach, ~d, ra, ns, hc), Run.over(~mach, ~d, rb, ns, hc)):
  match ra:
    case Run{+la, +ta, +aa}:
      hh => Sim.over.fin(~mach, ~d, a, b, la, ta, aa, rb, ns, hc, sh(Ext.holds_right(~mach, ~d, a, ns, aa)(hh)))

# a read of a log that tells, in the run in a, tells the same in the run in b
def Sim.find_eq(
  ~mach: Machine(),
  ~d: Led(mach),
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
  +k: List<&2, U32>,
  +y: Maybe<&2, List<&2, U32>>,
  rel: Sim.Rel(mach, d, a, b, ra, rb),
  ha: {Ext.holds(~mach, ~d, a, Run.added(Led.L(mach, d), ra)) == True{}: Bool},
  ef: {
    Tip.find(~mach, ~d, Run.ledger(Led.L(mach, d), ra), Run.tip(Led.L(mach, d), ra), k) == Some{y}: Maybe<&2, Maybe<&2, List<&2, U32>>>
  }
) -> {
  Tip.find(~mach, ~d, Run.ledger(Led.L(mach, d), rb), Run.tip(Led.L(mach, d), rb), k) == Some{y}: Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  match ra:
    case Run{+la, +ta, +aa}:
      match rel:
        case Tuple{+lb, Tuple{erb, Tuple{bda, bdb}}}:
          %Equal.sym(Run<Led.L(mach, d)>, rb, Run{lb, ta, aa}, erb): {
            Tip.find(~mach, ~d, Run.ledger(Led.L(mach, d), _), Run.tip(Led.L(mach, d), _), k) == Some{y}: Maybe<&2, Maybe<&2, List<&2, U32>>>
          }
          Hist.find(~mach, ~d, la, lb, Tip.log(ta), k, y, Sim.grows(~mach, ~d, a, b, later, la, ta, aa, lb, bda, bdb, ha))(
            ef
          )

# an entry of the ledger of the run in a is one of the run in b
def Sim.get_eq(
  ~mach: Machine(),
  ~d: Led(mach),
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  +later: {
    Bool.and(
      Ledgers.Kind.grows(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), a, b),
      Led.honest(~mach, ~d, b)
    )
      == True{}: Bool
  },
  +ra: Run<Led.L(mach, d)>,
  +rb: Run<Led.L(mach, d)>,
  +n: Ledgers.Name,
  +e: Entry(mach),
  rel: Sim.Rel(mach, d, a, b, ra, rb),
  ha: {Ext.holds(~mach, ~d, a, Run.added(Led.L(mach, d), ra)) == True{}: Bool},
  h: {Led.get(~mach, ~d, Run.ledger(Led.L(mach, d), ra), n) == Some{e}: Maybe<&2, Entry(mach)>}
) -> {Led.get(~mach, ~d, Run.ledger(Led.L(mach, d), rb), n) == Some{e}: Maybe<&2, Entry(mach)>}:
  Hist.gets(
    ~mach,
    ~d,
    Run.ledger(Led.L(mach, d), ra),
    Run.ledger(Led.L(mach, d), rb),
    Sim.grow_of(~mach, ~d, a, b, later, ra, rb, rel, ha)
  )(n)(e)(h)

# a gain of the run r0, once the result of the run after it is known (m)
def Ext.gain_of(
  -mach: Machine(),
  -d: Led(mach),
  -s: Led.L(mach, d),
  -r0: Run<Led.L(mach, d)>,
  m: Maybe<&2, Run<Led.L(mach, d)>>,
  -r2: Run<Led.L(mach, d)>,
  gm: Ext.GainM(mach, d, s, r0, m)
) -> {m == Some{r2}: Maybe<&2, Run<Led.L(mach, d)>>} -> Ext.Gain(mach, d, s, r0, r2):
  match m:
    case None{}:
      e => Empty.absurd(Ext.Gain(mach, d, s, r0, r2), Shared.Maybe.none_ne_some(Run<Led.L(mach, d)>, r2, e))
    case Some{r1}:
      e =>
        %Shared.Maybe.some_inj(Run<Led.L(mach, d)>, r1, r2, e): Ext.Gain(mach, d, s, r0, _)
        gm

# a ledger that holds what a run of the act x added holds what x adds
def Ext.act_held(
  ~mach: Machine(),
  ~d: Led(mach),
  +l: Led.L(mach, d),
  r: Run<Led.L(mach, d)>,
  +i: Ledgers.Id,
  +ah: Hashes.Hash,
  x: Act,
  +r2: Run<Led.L(mach, d)>
) -> {Act.run(~mach, ~d, r, i, ah, Some{x}) == Some{r2}: Maybe<&2, Run<Led.L(mach, d)>>}
  -> {Ext.holds(~mach, ~d, l, Run.added(Led.L(mach, d), r2)) == True{}: Bool}
  -> {Act.held(~mach, ~d, l, x) == True{}: Bool}:
  match r:
    case Run{+lr, +t, +aa}:
      match x:
        case Act.Stale{}:
          e => hh => {==}
        case Act.Label{m}:
          e => hh => {==}
        case Act.Taken{+vs, +h, +ns}:
          e => hh => Ext.holds_left(
            ~mach,
            ~d,
            l,
            ns,
            aa
          )(
            Ext.gain_holds(
              ~mach,
              ~d,
              l,
              Run.over(~mach, ~d, Run{lr, t, aa}, ns, h),
              r2,
              Ext.gain_of(
                mach,
                d,
                l,
                Run.over(~mach, ~d, Run{lr, t, aa}, ns, h),
                Step.taken(~mach, ~d, Run.over(~mach, ~d, Run{lr, t, aa}, ns, h), i, ah, vs),
                r2,
                Ext.taken(~mach, ~d, l, Run.over(~mach, ~d, Run{lr, t, aa}, ns, h), i, ah, vs)
              )(e),
              hh
            )
          )
        case Act.Opens{+b, +t2, +ns}:
          +r0 = Run.over(~mach, ~d, Run{lr, t, aa}, Tip.code(t2, []) <> ns, Tip.content(t))
          e => hh => Shared.List.all.if_rest(
            Ext.has(~mach, ~d, l, Tip.code(t2, [])),
            u => Ext.holds(~mach, ~d, l, ns)
          )(
            Ext.holds_left(
              ~mach,
              ~d,
              l,
              Tip.code(t2, []) <> ns,
              aa
            )(
              Ext.gain_holds(
                ~mach,
                ~d,
                l,
                r0,
                r2,
                Ext.gain_of(
                  mach,
                  d,
                  l,
                  r0,
                  Step.opens(~mach, ~d, Run{lr, t, aa}, i, ah, b, t2, ns),
                  r2,
                  Ext.bind(
                    ~mach,
                    ~d,
                    l,
                    r0,
                    Run.add(~mach, ~d, r0, Log.start(b), Hashes.Hash.code(Tip.hash(t2), [])),
                    r3 => Step.taken(~mach, ~d, r3, i, ah, None{}),
                    Ext.add(~mach, ~d, l, r0, Log.start(b), Hashes.Hash.code(Tip.hash(t2), [])),
                    r3 => Ext.taken(~mach, ~d, l, r3, i, ah, None{})
                  )
                )(e),
                hh
              )
            )
          )

# an act of the kernel in the run in a is its act in the run in b
def Sim.kern_eq(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
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
  +c: Ledgers.Line,
  +i: Ledgers.Id,
  +q: Machine.Q(mach),
  +act: Act,
  rel: Sim.Rel(mach, d, a, b, ra, rb),
  ha: {Ext.holds(~mach, ~d, a, Run.added(Led.L(mach, d), ra)) == True{}: Bool},
  h: {
    Kernel.change(mach, d, kern)(Run.ledger(Led.L(mach, d), ra))(Run.tip(Led.L(mach, d), ra))(c)(i)(q) == Some{act}: Maybe<&2, Act>
  },
  hd: {Act.held(~mach, ~d, a, act) == True{}: Bool}
) -> {
  Kernel.change(mach, d, kern)(Run.ledger(Led.L(mach, d), rb))(Run.tip(Led.L(mach, d), rb))(c)(i)(q) == Some{act}: Maybe<&2, Act>
}:
  match ra:
    case Run{+la, +ta, +aa}:
      match rel:
        case Tuple{+lb, Tuple{erb, Tuple{+bda, +bdb}}}:
          %Equal.sym(Run<Led.L(mach, d)>, rb, Run{lb, ta, aa}, erb): {
            Kernel.change(mach, d, kern)(Run.ledger(Led.L(mach, d), _))(Run.tip(Led.L(mach, d), _))(c)(i)(q) == Some{act}: Maybe<&2, Act>
          }
          Hist.kern(mach, d, kern)(ta)(c)(i)(q)(la)(lb)(act)(Sim.grows(~mach, ~d, a, b, later, la, ta, aa, lb, bda, bdb, ha))(h)(
            Hist.held_grows(
              ~mach,
              ~d,
              a,
              lb,
              Hist.trans(
                ~mach,
                ~d,
                a,
                b,
                lb,
                Led.later_grows(~mach, ~d, a, b)(later),
                Ext.based_from(~mach, ~d, b, Run{lb, ta, aa}, bdb)
              ),
              act
            )(hd)
          )

# Sim.taken_eq once the read of the log in a is known (m)
def Sim.taken_eq.at(
  ~mach: Machine(),
  ~d: Led(mach),
  +la: Led.L(mach, d),
  +lb: Led.L(mach, d),
  +t: Tip,
  +n: U32,
  -x: Taken,
  g: Led.Grows(mach, d, la, lb),
  m: Maybe<&2, List<&2, U32>>,
  em: {Tip.get(~mach, ~d, la, t, Log.taken(n)) == m: Maybe<&2, List<&2, U32>>},
  h: {
    Codes.Code.whole.of(~Taken, ~Taken.code, ~Taken.code.read, m) == Some{x}: Maybe<&2, Taken>
  }
) -> {Tip.taken(~mach, ~d, lb, t, n) == Some{x}: Maybe<&2, Taken>}:
  match m:
    case None{}:
      Empty.absurd({Tip.taken(~mach, ~d, lb, t, n) == Some{x}: Maybe<&2, Taken>}, Shared.Maybe.none_ne_some(Taken, x, h))
    case Some{+w}:
      %Equal.sym(
        Maybe<&2, List<&2, U32>>,
        Tip.get(~mach, ~d, lb, t, Log.taken(n)),
        Some{w},
        Keep.found_back(
          Trees.Ops.look(Led.L(mach, d), Led.tree(mach, d))(lb)(Tip.log(t))(Log.taken(n)),
          w,
          Hist.find(
            ~mach,
            ~d,
            la,
            lb,
            Tip.log(t),
            Log.taken(n),
            Some{w},
            g
          )(Keep.found(Trees.Ops.look(Led.L(mach, d), Led.tree(mach, d))(la)(Tip.log(t))(Log.taken(n)), w, em))
        )
      ): {Codes.Code.whole.of(~Taken, ~Taken.code, ~Taken.code.read, _) == Some{x}: Maybe<&2, Taken>}
      h

# a taken request that the log in a gives, the log in b gives
def Sim.taken_eq(
  ~mach: Machine(),
  ~d: Led(mach),
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  +later: {
    Bool.and(
      Ledgers.Kind.grows(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), a, b),
      Led.honest(~mach, ~d, b)
    )
      == True{}: Bool
  },
  +ra: Run<Led.L(mach, d)>,
  +rb: Run<Led.L(mach, d)>,
  +t: Tip,
  +n: U32,
  -x: Taken,
  +rel: Sim.Rel(mach, d, a, b, ra, rb),
  +ha: {Ext.holds(~mach, ~d, a, Run.added(Led.L(mach, d), ra)) == True{}: Bool},
  h: {Tip.taken(~mach, ~d, Run.ledger(Led.L(mach, d), ra), t, n) == Some{x}: Maybe<&2, Taken>}
) -> {Tip.taken(~mach, ~d, Run.ledger(Led.L(mach, d), rb), t, n) == Some{x}: Maybe<&2, Taken>}:
  Sim.taken_eq.at(
    ~mach,
    ~d,
    Run.ledger(Led.L(mach, d), ra),
    Run.ledger(Led.L(mach, d), rb),
    t,
    n,
    x,
    Sim.grow_of(~mach, ~d, a, b, later, ra, rb, rel, ha),
    Tip.get(~mach, ~d, Run.ledger(Led.L(mach, d), ra), t, Log.taken(n)),
    {==},
    h
  )

# taking a request, in a and in b, keeps two runs related
def Sim.taken.at(
  ~mach: Machine(),
  ~d: Led(mach),
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  +later: {
    Bool.and(
      Ledgers.Kind.grows(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), a, b),
      Led.honest(~mach, ~d, b)
    )
      == True{}: Bool
  },
  +ra: Run<Led.L(mach, d)>,
  +rb: Run<Led.L(mach, d)>,
  +i: Ledgers.Id,
  +ah: Hashes.Hash,
  +n: U32,
  +vs: Maybe<&2, List<&2, String>>,
  sh: Sim.Has(mach, d, a, b, ra, rb)
) -> Sim.Out(mach, d, a, b, Step.taken.at(~mach, ~d, ra, i, ah, n, vs), Step.taken.at(~mach, ~d, rb, i, ah, n, vs)):
  Sim.bind(
    ~mach,
    ~d,
    a,
    b,
    Run.add(~mach, ~d, ra, Log.out(i), Out.code(Out.Taken{ah, n}, [])),
    Run.add(~mach, ~d, rb, Log.out(i), Out.code(Out.Taken{ah, n}, [])),
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
    Sim.add(~mach, ~d, a, b, later, ra, rb, Log.out(i), Out.code(Out.Taken{ah, n}, []), sh),
    +r1 => Ext.bind(
      ~mach,
      ~d,
      a,
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
        a,
        r1,
        Log.taken(n),
        Taken.code(Taken{i, Tip.content(Run.tip(Led.L(mach, d), r1))}, [])
      ),
      r2 => Ext.next(mach, d, a, r2, vs)
    ),
    +r1 => +rb1 => sh1 => Sim.cond(
      ~mach,
      ~d,
      a,
      b,
      r1,
      rb1,
      Maybe.bind(
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
      Maybe.bind(
        &2,
        Run<Led.L(mach, d)>,
        Run<Led.L(mach, d)>,
        Run.add(
          ~mach,
          ~d,
          rb1,
          Log.taken(n),
          Taken.code(Taken{i, Tip.content(Run.tip(Led.L(mach, d), rb1))}, [])
        ),
        r2 => Some{Run.next(Led.L(mach, d), r2, vs)}
      ),
      Maybe.bind(
        &2,
        Run<Led.L(mach, d)>,
        Run<Led.L(mach, d)>,
        Run.add(
          ~mach,
          ~d,
          rb1,
          Log.taken(n),
          Taken.code(Taken{i, Tip.content(Run.tip(Led.L(mach, d), r1))}, [])
        ),
        r2 => Some{Run.next(Led.L(mach, d), r2, vs)}
      ),
      Ext.bind(
        ~mach,
        ~d,
        a,
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
          a,
          r1,
          Log.taken(n),
          Taken.code(Taken{i, Tip.content(Run.tip(Led.L(mach, d), r1))}, [])
        ),
        r2 => Ext.next(mach, d, a, r2, vs)
      ),
      sh1,
      rel => hr => Equal.cong(
        Tip,
        Maybe<&2, Run<Led.L(mach, d)>>,
        z => Maybe.bind(
          &2,
          Run<Led.L(mach, d)>,
          Run<Led.L(mach, d)>,
          Run.add(~mach, ~d, rb1, Log.taken(n), Taken.code(Taken{i, Tip.content(z)}, [])),
          r2 => Some{Run.next(Led.L(mach, d), r2, vs)}
        ),
        Run.tip(Led.L(mach, d), r1),
        Run.tip(Led.L(mach, d), rb1),
        Sim.tip_of(mach, d, a, b, r1, rb1, rel)
      ),
      sh2 => Sim.bind(
        ~mach,
        ~d,
        a,
        b,
        Run.add(
          ~mach,
          ~d,
          r1,
          Log.taken(n),
          Taken.code(Taken{i, Tip.content(Run.tip(Led.L(mach, d), r1))}, [])
        ),
        Run.add(
          ~mach,
          ~d,
          rb1,
          Log.taken(n),
          Taken.code(Taken{i, Tip.content(Run.tip(Led.L(mach, d), r1))}, [])
        ),
        r2 => Some{Run.next(Led.L(mach, d), r2, vs)},
        Sim.add(
          ~mach,
          ~d,
          a,
          b,
          later,
          r1,
          rb1,
          Log.taken(n),
          Taken.code(Taken{i, Tip.content(Run.tip(Led.L(mach, d), r1))}, []),
          sh2
        ),
        r2 => Ext.next(mach, d, a, r2, vs),
        r2 => rb2 => sh3 => Sim.step_next(~mach, ~d, a, b, r2, rb2, vs, sh3)
      )
    )
  )

# taking a request as the next number, in a and in b, keeps two runs related
def Sim.taken(
  ~mach: Machine(),
  ~d: Led(mach),
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  +later: {
    Bool.and(
      Ledgers.Kind.grows(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), a, b),
      Led.honest(~mach, ~d, b)
    )
      == True{}: Bool
  },
  +ra: Run<Led.L(mach, d)>,
  +rb: Run<Led.L(mach, d)>,
  +i: Ledgers.Id,
  +ah: Hashes.Hash,
  +vs: Maybe<&2, List<&2, String>>,
  sh: Sim.Has(mach, d, a, b, ra, rb)
) -> Sim.Out(mach, d, a, b, Step.taken(~mach, ~d, ra, i, ah, vs), Step.taken(~mach, ~d, rb, i, ah, vs)):
  Sim.cond(
    ~mach,
    ~d,
    a,
    b,
    ra,
    rb,
    Step.taken(~mach, ~d, ra, i, ah, vs),
    Step.taken(~mach, ~d, rb, i, ah, vs),
    Step.taken.at(~mach, ~d, rb, i, ah, Tip.count(Run.tip(Led.L(mach, d), ra)), vs),
    Ext.taken(~mach, ~d, a, ra, i, ah, vs),
    sh,
    rel => hr => Equal.cong(
      Tip,
      Maybe<&2, Run<Led.L(mach, d)>>,
      z => Step.taken.at(~mach, ~d, rb, i, ah, Tip.count(z), vs),
      Run.tip(Led.L(mach, d), ra),
      Run.tip(Led.L(mach, d), rb),
      Sim.tip_of(mach, d, a, b, ra, rb, rel)
    ),
    sh2 => Sim.taken.at(~mach, ~d, a, b, later, ra, rb, i, ah, Tip.count(Run.tip(Led.L(mach, d), ra)), vs, sh2)
  )

# a label on the same taken request, in a and in b, keeps two runs related
def Sim.labelled.some(
  ~mach: Machine(),
  ~d: Led(mach),
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  +later: {
    Bool.and(
      Ledgers.Kind.grows(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), a, b),
      Led.honest(~mach, ~d, b)
    )
      == True{}: Bool
  },
  +ra: Run<Led.L(mach, d)>,
  +rb: Run<Led.L(mach, d)>,
  +i: Ledgers.Id,
  +ah: Hashes.Hash,
  +m: String,
  +x: Taken,
  sh: Sim.Has(mach, d, a, b, ra, rb)
) -> Sim.Out(
  mach,
  d,
  a,
  b,
  Step.labelled(~mach, ~d, ra, i, ah, m, Some{x}),
  Step.labelled(~mach, ~d, rb, i, ah, m, Some{x})
):
  Sim.bind(
    ~mach,
    ~d,
    a,
    b,
    Run.add(~mach, ~d, ra, Log.label(m), Ledgers.Id.code(Taken.id(x), [])),
    Run.add(~mach, ~d, rb, Log.label(m), Ledgers.Id.code(Taken.id(x), [])),
    r2 => Step.taken(~mach, ~d, r2, i, ah, None{}),
    Sim.add(~mach, ~d, a, b, later, ra, rb, Log.label(m), Ledgers.Id.code(Taken.id(x), []), sh),
    r2 => Ext.taken(~mach, ~d, a, r2, i, ah, None{}),
    r2 => rb2 => sh2 => Sim.taken(~mach, ~d, a, b, later, r2, rb2, i, ah, None{}, sh2)
  )

# a label, in a and in b, once the taken request in a is known (va)
def Sim.labelled.read(
  ~mach: Machine(),
  ~d: Led(mach),
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  +later: {
    Bool.and(
      Ledgers.Kind.grows(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), a, b),
      Led.honest(~mach, ~d, b)
    )
      == True{}: Bool
  },
  +ra: Run<Led.L(mach, d)>,
  +rb: Run<Led.L(mach, d)>,
  +i: Ledgers.Id,
  +ah: Hashes.Hash,
  +m: String,
  +t: Tip,
  +n: U32,
  va: Maybe<&2, Taken>,
  +ev: {Tip.taken(~mach, ~d, Run.ledger(Led.L(mach, d), ra), t, n) == va: Maybe<&2, Taken>},
  sh: Sim.Has(mach, d, a, b, ra, rb)
) -> Sim.Out(
  mach,
  d,
  a,
  b,
  Step.labelled(~mach, ~d, ra, i, ah, m, va),
  Step.labelled(~mach, ~d, rb, i, ah, m, Tip.taken(~mach, ~d, Run.ledger(Led.L(mach, d), rb), t, n))
):
  match va:
    case None{}:
      Unit{}
    case Some{+x}:
      Sim.cond(
        ~mach,
        ~d,
        a,
        b,
        ra,
        rb,
        Step.labelled(~mach, ~d, ra, i, ah, m, Some{x}),
        Step.labelled(~mach, ~d, rb, i, ah, m, Tip.taken(~mach, ~d, Run.ledger(Led.L(mach, d), rb), t, n)),
        Step.labelled(~mach, ~d, rb, i, ah, m, Some{x}),
        Ext.labelled(~mach, ~d, a, ra, i, ah, m, Some{x}),
        sh,
        +rel => +hr => Equal.cong(
          Maybe<&2, Taken>,
          Maybe<&2, Run<Led.L(mach, d)>>,
          z => Step.labelled(~mach, ~d, rb, i, ah, m, z),
          Some{x},
          Tip.taken(~mach, ~d, Run.ledger(Led.L(mach, d), rb), t, n),
          Equal.sym(
            Maybe<&2, Taken>,
            Tip.taken(~mach, ~d, Run.ledger(Led.L(mach, d), rb), t, n),
            Some{x},
            Sim.taken_eq(~mach, ~d, a, b, later, ra, rb, t, n, x, rel, hr, ev)
          )
        ),
        sh2 => Sim.labelled.some(~mach, ~d, a, b, later, ra, rb, i, ah, m, x, sh2)
      )

# two runs related when a check is the same on both
def Sim.when(
  -mach: Machine(),
  -d: Led(mach),
  -a: Led.L(mach, d),
  -b: Led.L(mach, d),
  -ra: Run<Led.L(mach, d)>,
  -rb: Run<Led.L(mach, d)>,
  c0: Bool,
  -ka: Unit -> Maybe<&2, Run<Led.L(mach, d)>>,
  -ea: Unit -> Maybe<&2, Run<Led.L(mach, d)>>,
  -kb: Unit -> Maybe<&2, Run<Led.L(mach, d)>>,
  -eb: Unit -> Maybe<&2, Run<Led.L(mach, d)>>,
  sh: Sim.Has(mach, d, a, b, ra, rb),
  pk: {c0 == True{}: Bool} -> Sim.Has(mach, d, a, b, ra, rb) -> Sim.Out(mach, d, a, b, ka(Unit{}), kb(Unit{})),
  pe: {c0 == False{}: Bool} -> Sim.Has(mach, d, a, b, ra, rb) -> Sim.Out(mach, d, a, b, ea(Unit{}), eb(Unit{}))
) -> Sim.Out(
  mach,
  d,
  a,
  b,
  Shared.Bool.when(Maybe<&2, Run<Led.L(mach, d)>>, c0, ka, ea),
  Shared.Bool.when(Maybe<&2, Run<Led.L(mach, d)>>, c0, kb, eb)
):
  match c0:
    case True{}:
      pk({==})(sh)
    case False{}:
      pe({==})(sh)

# Step.label.at, in a and in b, keeps two runs related
def Sim.label.at(
  ~mach: Machine(),
  ~d: Led(mach),
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  +later: {
    Bool.and(
      Ledgers.Kind.grows(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), a, b),
      Led.honest(~mach, ~d, b)
    )
      == True{}: Bool
  },
  +ra: Run<Led.L(mach, d)>,
  +rb: Run<Led.L(mach, d)>,
  +i: Ledgers.Id,
  +ah: Hashes.Hash,
  +m: String,
  k: Maybe<&2, Maybe<&2, Ledgers.Id>>,
  sh: Sim.Has(mach, d, a, b, ra, rb)
) -> Sim.Out(mach, d, a, b, Step.label.at(~mach, ~d, ra, i, ah, m, k), Step.label.at(~mach, ~d, rb, i, ah, m, k)):
  match k:
    case None{}:
      Unit{}
    case Some{Some{x}}:
      Sim.stale(~mach, ~d, a, b, later, ra, rb, i, ah, sh)
    case Some{None{}}:
      Sim.cond(
        ~mach,
        ~d,
        a,
        b,
        ra,
        rb,
        Step.label.at(~mach, ~d, ra, i, ah, m, Some{None{}}),
        Step.label.at(~mach, ~d, rb, i, ah, m, Some{None{}}),
        Shared.Bool.when(
          Maybe<&2, Run<Led.L(mach, d)>>,
          U32.is_eq(Tip.count(Run.tip(Led.L(mach, d), ra)), 0),
          u => Step.stale(~mach, ~d, rb, i, ah),
          u => Step.labelled(
            ~mach,
            ~d,
            rb,
            i,
            ah,
            m,
            Tip.taken(
              ~mach,
              ~d,
              Run.ledger(Led.L(mach, d), rb),
              Run.tip(Led.L(mach, d), ra),
              U32.sub(Tip.count(Run.tip(Led.L(mach, d), ra)), 1)
            )
          )
        ),
        Ext.label.at(~mach, ~d, a, ra, i, ah, m, Some{None{}}),
        sh,
        rel => hr => Equal.cong(
          Tip,
          Maybe<&2, Run<Led.L(mach, d)>>,
          z => Shared.Bool.when(
            Maybe<&2, Run<Led.L(mach, d)>>,
            U32.is_eq(Tip.count(z), 0),
            u => Step.stale(~mach, ~d, rb, i, ah),
            u => Step.labelled(
              ~mach,
              ~d,
              rb,
              i,
              ah,
              m,
              Tip.taken(~mach, ~d, Run.ledger(Led.L(mach, d), rb), z, U32.sub(Tip.count(z), 1))
            )
          ),
          Run.tip(Led.L(mach, d), ra),
          Run.tip(Led.L(mach, d), rb),
          Sim.tip_of(mach, d, a, b, ra, rb, rel)
        ),
        sh2 => Sim.when(
          mach,
          d,
          a,
          b,
          ra,
          rb,
          U32.is_eq(Tip.count(Run.tip(Led.L(mach, d), ra)), 0),
          u => Step.stale(~mach, ~d, ra, i, ah),
          u => Step.labelled(
            ~mach,
            ~d,
            ra,
            i,
            ah,
            m,
            Tip.taken(
              ~mach,
              ~d,
              Run.ledger(Led.L(mach, d), ra),
              Run.tip(Led.L(mach, d), ra),
              U32.sub(Tip.count(Run.tip(Led.L(mach, d), ra)), 1)
            )
          ),
          u => Step.stale(~mach, ~d, rb, i, ah),
          u => Step.labelled(
            ~mach,
            ~d,
            rb,
            i,
            ah,
            m,
            Tip.taken(
              ~mach,
              ~d,
              Run.ledger(Led.L(mach, d), rb),
              Run.tip(Led.L(mach, d), ra),
              U32.sub(Tip.count(Run.tip(Led.L(mach, d), ra)), 1)
            )
          ),
          sh2,
          e => sh3 => Sim.stale(~mach, ~d, a, b, later, ra, rb, i, ah, sh3),
          e => sh3 => Sim.labelled.read(
            ~mach,
            ~d,
            a,
            b,
            later,
            ra,
            rb,
            i,
            ah,
            m,
            Run.tip(Led.L(mach, d), ra),
            U32.sub(Tip.count(Run.tip(Led.L(mach, d), ra)), 1),
            Tip.taken(
              ~mach,
              ~d,
              Run.ledger(Led.L(mach, d), ra),
              Run.tip(Led.L(mach, d), ra),
              U32.sub(Tip.count(Run.tip(Led.L(mach, d), ra)), 1)
            ),
            {==},
            sh3
          )
        )
      )

# a request for a label, in a and in b, once the read of the label in a is
# known (fa)
def Sim.label.read(
  ~mach: Machine(),
  ~d: Led(mach),
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  +later: {
    Bool.and(
      Ledgers.Kind.grows(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), a, b),
      Led.honest(~mach, ~d, b)
    )
      == True{}: Bool
  },
  +ra: Run<Led.L(mach, d)>,
  +rb: Run<Led.L(mach, d)>,
  +i: Ledgers.Id,
  +ah: Hashes.Hash,
  +m: String,
  fa: Maybe<&2, Maybe<&2, List<&2, U32>>>,
  +ef: {
    Tip.find(~mach, ~d, Run.ledger(Led.L(mach, d), ra), Run.tip(Led.L(mach, d), ra), Log.label(m)) == fa: Maybe<&2, Maybe<&2, List<&2, U32>>>
  },
  sh: Sim.Has(mach, d, a, b, ra, rb)
) -> Sim.Out(
  mach,
  d,
  a,
  b,
  Step.label.at(~mach, ~d, ra, i, ah, m, Tip.known(~Ledgers.Id, ~Ledgers.Id.code, ~Ledgers.Id.code.read, fa)),
  Step.label(~mach, ~d, rb, i, ah, m)
):
  match fa:
    case None{}:
      Unit{}
    case Some{+y}:
      Sim.cond(
        ~mach,
        ~d,
        a,
        b,
        ra,
        rb,
        Step.label.at(~mach, ~d, ra, i, ah, m, Tip.known(~Ledgers.Id, ~Ledgers.Id.code, ~Ledgers.Id.code.read, Some{y})),
        Step.label(~mach, ~d, rb, i, ah, m),
        Step.label.at(~mach, ~d, rb, i, ah, m, Tip.known(~Ledgers.Id, ~Ledgers.Id.code, ~Ledgers.Id.code.read, Some{y})),
        Ext.label.at(~mach, ~d, a, ra, i, ah, m, Tip.known(~Ledgers.Id, ~Ledgers.Id.code, ~Ledgers.Id.code.read, Some{y})),
        sh,
        +rel => +hr => Equal.cong(
          Maybe<&2, Maybe<&2, List<&2, U32>>>,
          Maybe<&2, Run<Led.L(mach, d)>>,
          z => Step.label.at(~mach, ~d, rb, i, ah, m, Tip.known(~Ledgers.Id, ~Ledgers.Id.code, ~Ledgers.Id.code.read, z)),
          Some{y},
          Tip.find(~mach, ~d, Run.ledger(Led.L(mach, d), rb), Run.tip(Led.L(mach, d), rb), Log.label(m)),
          Equal.sym(
            Maybe<&2, Maybe<&2, List<&2, U32>>>,
            Tip.find(~mach, ~d, Run.ledger(Led.L(mach, d), rb), Run.tip(Led.L(mach, d), rb), Log.label(m)),
            Some{y},
            Sim.find_eq(~mach, ~d, a, b, later, ra, rb, Log.label(m), y, rel, hr, ef)
          )
        ),
        sh2 => Sim.label.at(
          ~mach,
          ~d,
          a,
          b,
          later,
          ra,
          rb,
          i,
          ah,
          m,
          Tip.known(~Ledgers.Id, ~Ledgers.Id.code, ~Ledgers.Id.code.read, Some{y}),
          sh2
        )
      )

# a request for a label, in a and in b, keeps two runs related
def Sim.label(
  ~mach: Machine(),
  ~d: Led(mach),
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  +later: {
    Bool.and(
      Ledgers.Kind.grows(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), a, b),
      Led.honest(~mach, ~d, b)
    )
      == True{}: Bool
  },
  +ra: Run<Led.L(mach, d)>,
  +rb: Run<Led.L(mach, d)>,
  +i: Ledgers.Id,
  +ah: Hashes.Hash,
  +m: String,
  sh: Sim.Has(mach, d, a, b, ra, rb)
) -> Sim.Out(mach, d, a, b, Step.label(~mach, ~d, ra, i, ah, m), Step.label(~mach, ~d, rb, i, ah, m)):
  Sim.label.read(
    ~mach,
    ~d,
    a,
    b,
    later,
    ra,
    rb,
    i,
    ah,
    m,
    Tip.find(~mach, ~d, Run.ledger(Led.L(mach, d), ra), Run.tip(Led.L(mach, d), ra), Log.label(m)),
    {==},
    sh
  )

# opening a sub line, in a and in b, keeps two runs related
def Sim.opens(
  ~mach: Machine(),
  ~d: Led(mach),
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  +later: {
    Bool.and(
      Ledgers.Kind.grows(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), a, b),
      Led.honest(~mach, ~d, b)
    )
      == True{}: Bool
  },
  +ra: Run<Led.L(mach, d)>,
  +rb: Run<Led.L(mach, d)>,
  +i: Ledgers.Id,
  +ah: Hashes.Hash,
  +bn: String,
  +t: Tip,
  +ns: List<&2, List<&2, U32>>,
  sh: Sim.Has(mach, d, a, b, ra, rb)
) -> Sim.Out(mach, d, a, b, Step.opens(~mach, ~d, ra, i, ah, bn, t, ns), Step.opens(~mach, ~d, rb, i, ah, bn, t, ns)):
  Sim.cond(
    ~mach,
    ~d,
    a,
    b,
    ra,
    rb,
    Step.opens(~mach, ~d, ra, i, ah, bn, t, ns),
    Step.opens(~mach, ~d, rb, i, ah, bn, t, ns),
    Maybe.bind(
      &2,
      Run<Led.L(mach, d)>,
      Run<Led.L(mach, d)>,
      Run.add(
        ~mach,
        ~d,
        Run.over(~mach, ~d, rb, Tip.code(t, []) <> ns, Tip.content(Run.tip(Led.L(mach, d), ra))),
        Log.start(bn),
        Hashes.Hash.code(Tip.hash(t), [])
      ),
      r2 => Step.taken(~mach, ~d, r2, i, ah, None{})
    ),
    Ext.opens(~mach, ~d, a, ra, i, ah, bn, t, ns),
    sh,
    rel => hr => Equal.cong(
      Tip,
      Maybe<&2, Run<Led.L(mach, d)>>,
      z => Maybe.bind(
        &2,
        Run<Led.L(mach, d)>,
        Run<Led.L(mach, d)>,
        Run.add(
          ~mach,
          ~d,
          Run.over(~mach, ~d, rb, Tip.code(t, []) <> ns, Tip.content(z)),
          Log.start(bn),
          Hashes.Hash.code(Tip.hash(t), [])
        ),
        r2 => Step.taken(~mach, ~d, r2, i, ah, None{})
      ),
      Run.tip(Led.L(mach, d), ra),
      Run.tip(Led.L(mach, d), rb),
      Sim.tip_of(mach, d, a, b, ra, rb, rel)
    ),
    sh2 => Sim.bind(
      ~mach,
      ~d,
      a,
      b,
      Run.add(
        ~mach,
        ~d,
        Run.over(~mach, ~d, ra, Tip.code(t, []) <> ns, Tip.content(Run.tip(Led.L(mach, d), ra))),
        Log.start(bn),
        Hashes.Hash.code(Tip.hash(t), [])
      ),
      Run.add(
        ~mach,
        ~d,
        Run.over(~mach, ~d, rb, Tip.code(t, []) <> ns, Tip.content(Run.tip(Led.L(mach, d), ra))),
        Log.start(bn),
        Hashes.Hash.code(Tip.hash(t), [])
      ),
      r2 => Step.taken(~mach, ~d, r2, i, ah, None{}),
      Sim.add(
        ~mach,
        ~d,
        a,
        b,
        later,
        Run.over(~mach, ~d, ra, Tip.code(t, []) <> ns, Tip.content(Run.tip(Led.L(mach, d), ra))),
        Run.over(~mach, ~d, rb, Tip.code(t, []) <> ns, Tip.content(Run.tip(Led.L(mach, d), ra))),
        Log.start(bn),
        Hashes.Hash.code(Tip.hash(t), []),
        Sim.over(~mach, ~d, a, b, ra, rb, Tip.code(t, []) <> ns, Tip.content(Run.tip(Led.L(mach, d), ra)), sh2)
      ),
      r2 => Ext.taken(~mach, ~d, a, r2, i, ah, None{}),
      r2 => rb2 => sh3 => Sim.taken(~mach, ~d, a, b, later, r2, rb2, i, ah, None{}, sh3)
    )
  )

# an act of a kernel, in a and in b, keeps two runs related
def Sim.act(
  ~mach: Machine(),
  ~d: Led(mach),
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  +later: {
    Bool.and(
      Ledgers.Kind.grows(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), a, b),
      Led.honest(~mach, ~d, b)
    )
      == True{}: Bool
  },
  +ra: Run<Led.L(mach, d)>,
  +rb: Run<Led.L(mach, d)>,
  +i: Ledgers.Id,
  +ah: Hashes.Hash,
  m: Maybe<&2, Act>,
  sh: Sim.Has(mach, d, a, b, ra, rb)
) -> Sim.Out(mach, d, a, b, Act.run(~mach, ~d, ra, i, ah, m), Act.run(~mach, ~d, rb, i, ah, m)):
  match m:
    case None{}:
      Unit{}
    case Some{Act.Stale{}}:
      Sim.stale(~mach, ~d, a, b, later, ra, rb, i, ah, sh)
    case Some{Act.Label{x}}:
      Sim.label(~mach, ~d, a, b, later, ra, rb, i, ah, x, sh)
    case Some{Act.Taken{+vs, +h, +ns}}:
      Sim.taken(
        ~mach,
        ~d,
        a,
        b,
        later,
        Run.over(~mach, ~d, ra, ns, h),
        Run.over(~mach, ~d, rb, ns, h),
        i,
        ah,
        vs,
        Sim.over(~mach, ~d, a, b, ra, rb, ns, h, sh)
      )
    case Some{Act.Opens{bn, t, ns}}:
      Sim.opens(~mach, ~d, a, b, later, ra, rb, i, ah, bn, t, ns, sh)

# an act, in a and in b, once the act in a is known (ma)
def Sim.fresh.act(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  +later: {
    Bool.and(
      Ledgers.Kind.grows(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), a, b),
      Led.honest(~mach, ~d, b)
    )
      == True{}: Bool
  },
  +ra: Run<Led.L(mach, d)>,
  +rb: Run<Led.L(mach, d)>,
  +c: Ledgers.Line,
  +i: Ledgers.Id,
  +ah: Hashes.Hash,
  +q: Machine.Q(mach),
  ma: Maybe<&2, Act>,
  +em: {
    Kernel.change(mach, d, kern)(Run.ledger(Led.L(mach, d), ra))(Run.tip(Led.L(mach, d), ra))(c)(i)(q) == ma: Maybe<&2, Act>
  },
  sh: Sim.Has(mach, d, a, b, ra, rb)
) -> Sim.Out(
  mach,
  d,
  a,
  b,
  Act.run(~mach, ~d, ra, i, ah, ma),
  Act.run(
    ~mach,
    ~d,
    rb,
    i,
    ah,
    Kernel.change(mach, d, kern)(Run.ledger(Led.L(mach, d), rb))(Run.tip(Led.L(mach, d), rb))(c)(i)(q)
  )
):
  match ma:
    case None{}:
      Unit{}
    case Some{+act}:
      Sim.cond.held(
        ~mach,
        ~d,
        a,
        b,
        ra,
        rb,
        Act.run(~mach, ~d, ra, i, ah, Some{act}),
        Act.run(
          ~mach,
          ~d,
          rb,
          i,
          ah,
          Kernel.change(mach, d, kern)(Run.ledger(Led.L(mach, d), rb))(Run.tip(Led.L(mach, d), rb))(c)(i)(q)
        ),
        Act.run(~mach, ~d, rb, i, ah, Some{act}),
        Ext.act(~mach, ~d, a, ra, i, ah, Some{act}),
        sh,
        +rel => +hr => +r2 => e2 => hh2 => Equal.cong(
          Maybe<&2, Act>,
          Maybe<&2, Run<Led.L(mach, d)>>,
          z => Act.run(~mach, ~d, rb, i, ah, z),
          Some{act},
          Kernel.change(mach, d, kern)(Run.ledger(Led.L(mach, d), rb))(Run.tip(Led.L(mach, d), rb))(c)(i)(q),
          Equal.sym(
            Maybe<&2, Act>,
            Kernel.change(mach, d, kern)(Run.ledger(Led.L(mach, d), rb))(Run.tip(Led.L(mach, d), rb))(c)(i)(q),
            Some{act},
            Sim.kern_eq(~mach, ~d, ~kern, a, b, later, ra, rb, c, i, q, act, rel, hr, em, Ext.act_held(~mach, ~d, a, ra, i, ah, act, r2)(e2)(hh2))
          )
        ),
        sh2 => Sim.act(~mach, ~d, a, b, later, ra, rb, i, ah, Some{act}, sh2)
      )

# a request with the outcome o, in a and in b, keeps two runs related
def Sim.fresh(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  +later: {
    Bool.and(
      Ledgers.Kind.grows(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), a, b),
      Led.honest(~mach, ~d, b)
    )
      == True{}: Bool
  },
  +ra: Run<Led.L(mach, d)>,
  +rb: Run<Led.L(mach, d)>,
  +c: Ledgers.Line,
  +i: Ledgers.Id,
  +ah: Hashes.Hash,
  +q: Machine.Q(mach),
  o: Maybe<&2, Maybe<&2, Out>>,
  sh: Sim.Has(mach, d, a, b, ra, rb)
) -> Sim.Out(
  mach,
  d,
  a,
  b,
  Step.fresh(~mach, ~d, ~kern, ra, c, i, ah, q, o),
  Step.fresh(~mach, ~d, ~kern, rb, c, i, ah, q, o)
):
  match o:
    case None{}:
      Unit{}
    case Some{Some{x}}:
      sh
    case Some{None{}}:
      Sim.fresh.act(
        ~mach,
        ~d,
        ~kern,
        a,
        b,
        later,
        ra,
        rb,
        c,
        i,
        ah,
        q,
        Kernel.change(mach, d, kern)(Run.ledger(Led.L(mach, d), ra))(Run.tip(Led.L(mach, d), ra))(c)(i)(q),
        {==},
        sh
      )

# a request, in a and in b, once the read of its outcome in a is known (fa)
def Sim.asked.find(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  +later: {
    Bool.and(
      Ledgers.Kind.grows(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), a, b),
      Led.honest(~mach, ~d, b)
    )
      == True{}: Bool
  },
  +ra: Run<Led.L(mach, d)>,
  +rb: Run<Led.L(mach, d)>,
  +c: Ledgers.Line,
  +ah: Hashes.Hash,
  +i: Ledgers.Id,
  +q: Machine.Q(mach),
  fa: Maybe<&2, Maybe<&2, List<&2, U32>>>,
  +ef: {
    Tip.find(~mach, ~d, Run.ledger(Led.L(mach, d), ra), Run.tip(Led.L(mach, d), ra), Log.out(i)) == fa: Maybe<&2, Maybe<&2, List<&2, U32>>>
  },
  sh: Sim.Has(mach, d, a, b, ra, rb)
) -> Sim.Out(
  mach,
  d,
  a,
  b,
  Step.fresh(~mach, ~d, ~kern, ra, c, i, ah, q, Tip.known(~Out, ~Out.code, ~Out.code.read, fa)),
  Step.fresh(
    ~mach,
    ~d,
    ~kern,
    rb,
    c,
    i,
    ah,
    q,
    Tip.known(
      ~Out,
      ~Out.code,
      ~Out.code.read,
      Tip.find(~mach, ~d, Run.ledger(Led.L(mach, d), rb), Run.tip(Led.L(mach, d), rb), Log.out(i))
    )
  )
):
  match fa:
    case None{}:
      Unit{}
    case Some{+y}:
      Sim.cond(
        ~mach,
        ~d,
        a,
        b,
        ra,
        rb,
        Step.fresh(~mach, ~d, ~kern, ra, c, i, ah, q, Tip.known(~Out, ~Out.code, ~Out.code.read, Some{y})),
        Step.fresh(
          ~mach,
          ~d,
          ~kern,
          rb,
          c,
          i,
          ah,
          q,
          Tip.known(
            ~Out,
            ~Out.code,
            ~Out.code.read,
            Tip.find(~mach, ~d, Run.ledger(Led.L(mach, d), rb), Run.tip(Led.L(mach, d), rb), Log.out(i))
          )
        ),
        Step.fresh(~mach, ~d, ~kern, rb, c, i, ah, q, Tip.known(~Out, ~Out.code, ~Out.code.read, Some{y})),
        Ext.fresh(~mach, ~d, ~kern, a, ra, c, i, ah, q, Tip.known(~Out, ~Out.code, ~Out.code.read, Some{y})),
        sh,
        +rel => +hr => Equal.cong(
          Maybe<&2, Maybe<&2, List<&2, U32>>>,
          Maybe<&2, Run<Led.L(mach, d)>>,
          z => Step.fresh(~mach, ~d, ~kern, rb, c, i, ah, q, Tip.known(~Out, ~Out.code, ~Out.code.read, z)),
          Some{y},
          Tip.find(~mach, ~d, Run.ledger(Led.L(mach, d), rb), Run.tip(Led.L(mach, d), rb), Log.out(i)),
          Equal.sym(
            Maybe<&2, Maybe<&2, List<&2, U32>>>,
            Tip.find(~mach, ~d, Run.ledger(Led.L(mach, d), rb), Run.tip(Led.L(mach, d), rb), Log.out(i)),
            Some{y},
            Sim.find_eq(~mach, ~d, a, b, later, ra, rb, Log.out(i), y, rel, hr, ef)
          )
        ),
        sh2 => Sim.fresh(
          ~mach,
          ~d,
          ~kern,
          a,
          b,
          later,
          ra,
          rb,
          c,
          i,
          ah,
          q,
          Tip.known(~Out, ~Out.code, ~Out.code.read, Some{y}),
          sh2
        )
      )

# the entry m, in a and in b, keeps two runs related
def Sim.asked(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  +later: {
    Bool.and(
      Ledgers.Kind.grows(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), a, b),
      Led.honest(~mach, ~d, b)
    )
      == True{}: Bool
  },
  +ra: Run<Led.L(mach, d)>,
  +rb: Run<Led.L(mach, d)>,
  +c: Ledgers.Line,
  +ah: Hashes.Hash,
  m: Maybe<&2, Entry(mach)>,
  sh: Sim.Has(mach, d, a, b, ra, rb)
) -> Sim.Out(mach, d, a, b, Step.asked(~mach, ~d, ~kern, ra, c, ah, m), Step.asked(~mach, ~d, ~kern, rb, c, ah, m)):
  match m:
    case Some{Ledgers.Entry.Ask{+i, t, +q}}:
      Sim.asked.find(
        ~mach,
        ~d,
        ~kern,
        a,
        b,
        later,
        ra,
        rb,
        c,
        ah,
        i,
        q,
        Tip.find(~mach, ~d, Run.ledger(Led.L(mach, d), ra), Run.tip(Led.L(mach, d), ra), Log.out(i)),
        {==},
        sh
      )
    case None{}:
      Unit{}
    case Some{Ledgers.Entry.Ballot{x}}:
      Unit{}
    case Some{Ledgers.Entry.Data{x}}:
      Unit{}
    case Some{Ledgers.Entry.Lie{x}}:
      Unit{}

# one request, in a and in b, once its entry in a is known (me)
def Sim.one.get(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  +later: {
    Bool.and(
      Ledgers.Kind.grows(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), a, b),
      Led.honest(~mach, ~d, b)
    )
      == True{}: Bool
  },
  +ra: Run<Led.L(mach, d)>,
  +rb: Run<Led.L(mach, d)>,
  +c: Ledgers.Line,
  +ah: Hashes.Hash,
  me: Maybe<&2, Entry(mach)>,
  +eme: {Led.get(~mach, ~d, Run.ledger(Led.L(mach, d), ra), Ledgers.Name.Ask{ah}) == me: Maybe<&2, Entry(mach)>},
  sh: Sim.Has(mach, d, a, b, ra, rb)
) -> Sim.Out(
  mach,
  d,
  a,
  b,
  Step.asked(~mach, ~d, ~kern, ra, c, ah, me),
  Step.asked(~mach, ~d, ~kern, rb, c, ah, Led.get(~mach, ~d, Run.ledger(Led.L(mach, d), rb), Ledgers.Name.Ask{ah}))
):
  match me:
    case None{}:
      Unit{}
    case Some{+e}:
      Sim.cond(
        ~mach,
        ~d,
        a,
        b,
        ra,
        rb,
        Step.asked(~mach, ~d, ~kern, ra, c, ah, Some{e}),
        Step.asked(~mach, ~d, ~kern, rb, c, ah, Led.get(~mach, ~d, Run.ledger(Led.L(mach, d), rb), Ledgers.Name.Ask{ah})),
        Step.asked(~mach, ~d, ~kern, rb, c, ah, Some{e}),
        Ext.asked(~mach, ~d, ~kern, a, ra, c, ah, Some{e}),
        sh,
        +rel => +hr => Equal.cong(
          Maybe<&2, Entry(mach)>,
          Maybe<&2, Run<Led.L(mach, d)>>,
          z => Step.asked(~mach, ~d, ~kern, rb, c, ah, z),
          Some{e},
          Led.get(~mach, ~d, Run.ledger(Led.L(mach, d), rb), Ledgers.Name.Ask{ah}),
          Equal.sym(
            Maybe<&2, Entry(mach)>,
            Led.get(~mach, ~d, Run.ledger(Led.L(mach, d), rb), Ledgers.Name.Ask{ah}),
            Some{e},
            Sim.get_eq(~mach, ~d, a, b, later, ra, rb, Ledgers.Name.Ask{ah}, e, rel, hr, eme)
          )
        ),
        sh2 => Sim.asked(~mach, ~d, ~kern, a, b, later, ra, rb, c, ah, Some{e}, sh2)
      )

# one request, in a and in b, keeps two runs related
def Sim.one(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  +later: {
    Bool.and(
      Ledgers.Kind.grows(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), a, b),
      Led.honest(~mach, ~d, b)
    )
      == True{}: Bool
  },
  +ra: Run<Led.L(mach, d)>,
  +rb: Run<Led.L(mach, d)>,
  +c: Ledgers.Line,
  +ah: Hashes.Hash,
  sh: Sim.Has(mach, d, a, b, ra, rb)
) -> Sim.Out(mach, d, a, b, Step.one(~mach, ~d, ~kern, ra, c, ah), Step.one(~mach, ~d, ~kern, rb, c, ah)):
  Sim.one.get(
    ~mach,
    ~d,
    ~kern,
    a,
    b,
    later,
    ra,
    rb,
    c,
    ah,
    Led.get(~mach, ~d, Run.ledger(Led.L(mach, d), ra), Ledgers.Name.Ask{ah}),
    {==},
    sh
  )

# the requests qs, in a and in b, keep two runs related
def Sim.all(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
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
  qs: List<&2, Hashes.Hash>,
  +ma: Maybe<&2, Run<Led.L(mach, d)>>,
  +mb: Maybe<&2, Run<Led.L(mach, d)>>,
  hm: Sim.Out(mach, d, a, b, ma, mb)
) -> Sim.Out(mach, d, a, b, Step.all(~mach, ~d, ~kern, c, qs, ma), Step.all(~mach, ~d, ~kern, c, qs, mb)):
  match qs:
    case Nil{}:
      hm
    case Con{+q, rest}:
      Sim.all(
        ~mach,
        ~d,
        ~kern,
        a,
        b,
        later,
        c,
        rest,
        Maybe.bind(&2, Run<Led.L(mach, d)>, Run<Led.L(mach, d)>, ma, x => Step.one(~mach, ~d, ~kern, x, c, q)),
        Maybe.bind(&2, Run<Led.L(mach, d)>, Run<Led.L(mach, d)>, mb, x => Step.one(~mach, ~d, ~kern, x, c, q)),
        Sim.bind(
          ~mach,
          ~d,
          a,
          b,
          ma,
          mb,
          x => Step.one(~mach, ~d, ~kern, x, c, q),
          hm,
          x => Ext.one(~mach, ~d, ~kern, a, x, c, q),
          x => y => s => Sim.one(~mach, ~d, ~kern, a, b, later, x, y, c, q, s)
        )
      )

# the related run in b lands on the tip of the run in a
def Sim.landed.fin(
  ~mach: Machine(),
  ~d: Led(mach),
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
  +after: Maybe<&2, Hashes.Hash>,
  -x: Tip,
  rb: Run<Led.L(mach, d)>,
  rel: Sim.Rel(mach, d, a, b, Run{la, ta, aa}, rb),
  ha: {Ext.holds(~mach, ~d, a, aa) == True{}: Bool},
  es: {Tips.same(Some{Tip.hash(ta)}, after) == True{}: Bool},
  ex: {ta == x: Tip}
) -> {Line.landed(~mach, ~d, b, Some{rb}, after) == Some{x}: Maybe<&2, Tip>}:
  match rel:
    case Tuple{lb, Tuple{erb, y}}:
      %Equal.sym(Run<Led.L(mach, d)>, rb, Run{lb, ta, aa}, erb): {Line.landed(~mach, ~d, b, Some{_}, after) == Some{x}: Maybe<&2, Tip>}
      %Equal.sym(Bool, Tips.same(Some{Tip.hash(ta)}, after), True{}, es): {
        Shared.Maybe.when(Tip, Bool.and(_, Ext.holds(~mach, ~d, b, aa)), u => Some{ta}) == Some{x}: Maybe<&2, Tip>
      }
      %Equal.sym(Bool, Ext.holds(~mach, ~d, b, aa), True{}, Sim.holds_b(~mach, ~d, a, b, later, aa, ha)): {
        Shared.Maybe.when(Tip, Bool.and(True{}, _), u => Some{ta}) == Some{x}: Maybe<&2, Tip>
      }
      Equal.cong(Tip, Maybe<&2, Tip>, z => Some{z}, ta, x, ex)

# Sim.landed once what the run in b gave is known
def Sim.landed.mb(
  ~mach: Machine(),
  ~d: Led(mach),
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
  +after: Maybe<&2, Hashes.Hash>,
  -x: Tip,
  mb: Maybe<&2, Run<Led.L(mach, d)>>,
  r2: Sim.R2(mach, d, a, b, Run{la, ta, aa}, mb),
  ha: {Ext.holds(~mach, ~d, a, aa) == True{}: Bool},
  es: {Tips.same(Some{Tip.hash(ta)}, after) == True{}: Bool},
  ex: {ta == x: Tip}
) -> {Line.landed(~mach, ~d, b, mb, after) == Some{x}: Maybe<&2, Tip>}:
  match mb:
    case None{}:
      Empty.absurd({Line.landed(~mach, ~d, b, None{}, after) == Some{x}: Maybe<&2, Tip>}, r2)
    case Some{rb}:
      Sim.landed.fin(~mach, ~d, a, b, later, la, ta, aa, after, x, rb, r2, ha, es, ex)

# Sim.landed once the check of the run in a is known (bv)
def Sim.landed.at(
  ~mach: Machine(),
  ~d: Led(mach),
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
  +after: Maybe<&2, Hashes.Hash>,
  -x: Tip,
  mb: Maybe<&2, Run<Led.L(mach, d)>>,
  out: Sim.Out(mach, d, a, b, Some{Run{la, ta, aa}}, mb),
  bv: Bool,
  +eb: {Bool.and(Tips.same(Some{Tip.hash(ta)}, after), Ext.holds(~mach, ~d, a, aa)) == bv: Bool},
  e: {Shared.Maybe.when(Tip, bv, u => Some{ta}) == Some{x}: Maybe<&2, Tip>}
) -> {Line.landed(~mach, ~d, b, mb, after) == Some{x}: Maybe<&2, Tip>}:
  match bv:
    case True{}:
      +ha = Shared.Bool.and_true_right(Tips.same(Some{Tip.hash(ta)}, after), Ext.holds(~mach, ~d, a, aa))(eb)
      Sim.landed.mb(
        ~mach,
        ~d,
        a,
        b,
        later,
        la,
        ta,
        aa,
        after,
        x,
        mb,
        out(ha),
        ha,
        Shared.Bool.and_true_left(Tips.same(Some{Tip.hash(ta)}, after), Ext.holds(~mach, ~d, a, aa))(eb),
        Shared.Maybe.some_inj(Tip, ta, x, e)
      )
    case False{}:
      Empty.absurd(
        {Line.landed(~mach, ~d, b, mb, after) == Some{x}: Maybe<&2, Tip>},
        Shared.Maybe.none_ne_some(Tip, x, e)
      )

# a run in a that lands lands on the same tip in b
def Sim.landed(
  ~mach: Machine(),
  ~d: Led(mach),
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  +later: {
    Bool.and(
      Ledgers.Kind.grows(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), a, b),
      Led.honest(~mach, ~d, b)
    )
      == True{}: Bool
  },
  ma: Maybe<&2, Run<Led.L(mach, d)>>,
  mb: Maybe<&2, Run<Led.L(mach, d)>>,
  out: Sim.Out(mach, d, a, b, ma, mb),
  +after: Maybe<&2, Hashes.Hash>,
  -x: Tip,
  e: {Line.landed(~mach, ~d, a, ma, after) == Some{x}: Maybe<&2, Tip>}
) -> {Line.landed(~mach, ~d, b, mb, after) == Some{x}: Maybe<&2, Tip>}:
  match ma:
    case None{}:
      Empty.absurd({Line.landed(~mach, ~d, b, mb, after) == Some{x}: Maybe<&2, Tip>}, Shared.Maybe.none_ne_some(Tip, x, e))
    case Some{Run{+la, +ta, +aa}}:
      Sim.landed.at(
        ~mach,
        ~d,
        a,
        b,
        later,
        la,
        ta,
        aa,
        after,
        x,
        mb,
        out,
        Bool.and(Tips.same(Some{Tip.hash(ta)}, after), Ext.holds(~mach, ~d, a, aa)),
        {==},
        e
      )

# Sim.moved once whether the step names the tip is known (bv)
def Sim.moved.at(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
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
  +qs: List<&2, Hashes.Hash>,
  +after: Maybe<&2, Hashes.Hash>,
  -x: Tip,
  bv: Bool,
  e: {
    Shared.Maybe.when(Tip, bv, u => Line.landed(~mach, ~d, a, Step.run(~mach, ~d, ~kern, a, c, t, qs), after))
      == Some{x}: Maybe<&2, Tip>
  }
) -> {
  Shared.Maybe.when(Tip, bv, u => Line.landed(~mach, ~d, b, Step.run(~mach, ~d, ~kern, b, c, t, qs), after))
    == Some{x}: Maybe<&2, Tip>
}:
  match bv:
    case True{}:
      Sim.landed(
        ~mach,
        ~d,
        a,
        b,
        later,
        Step.run(~mach, ~d, ~kern, a, c, t, qs),
        Step.run(~mach, ~d, ~kern, b, c, t, qs),
        Sim.all(
          ~mach,
          ~d,
          ~kern,
          a,
          b,
          later,
          c,
          qs,
          Some{Run{a, t, []}},
          Some{Run{b, t, []}},
          hh => Tuple{b, Tuple{{==}, Tuple{Tuple{[], Tuple{{==}, {==}}}, Tuple{[], Tuple{{==}, {==}}}}}}
        ),
        after,
        x,
        e
      )
    case False{}:
      Empty.absurd(
        {Shared.Maybe.when(Tip, False{}, u => Line.landed(~mach, ~d, b, Step.run(~mach, ~d, ~kern, b, c, t, qs), after)) == Some{x}: Maybe<&2, Tip>},
        Shared.Maybe.none_ne_some(Tip, x, e)
      )

# a step lands on the same tip in a later ledger
def Sim.moved(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
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
  match v:
    case Ledgers.Step{before, +qs, +after}:
      e => Sim.moved.at(
        ~mach,
        ~d,
        ~kern,
        a,
        b,
        later,
        c,
        t,
        qs,
        after,
        x,
        Tips.same(before, Some{Tip.hash(t)}),
        e
      )

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

# the next tip of a line stays in a later ledger, once the decided step is
# known (m)
def Hist.next.at(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
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
  +t: Tip,
  +x: Tip,
  m: Maybe<&2, Ledgers.Step>
) -> {
  Height.decide(
    ~mach,
    ~d,
    a,
    c,
    h,
    Tip.voters(t),
    Ledgers.Kind.rounds(Machine.Q(mach), Led.kind(mach, d))(a)(c)(h)
  )
    == m: Maybe<&2, Ledgers.Step>
} -> {Line.moved(~mach, ~d, ~kern, a, c, t, m) == Some{x}: Maybe<&2, Tip>}
  -> {Line.next(~mach, ~d, ~kern, b, c, h, t) == Some{x}: Maybe<&2, Tip>}:
  match m:
    case None{}:
      em => e => Empty.absurd(
        {Line.next(~mach, ~d, ~kern, b, c, h, t) == Some{x}: Maybe<&2, Tip>},
        Shared.Maybe.none_ne_some(Tip, x, e)
      )
    case Some{+v}:
      em => e =>
        %Equal.sym(
          Maybe<&2, Ledgers.Step>,
          Height.decide(
            ~mach,
            ~d,
            b,
            c,
            h,
            Tip.voters(t),
            Ledgers.Kind.rounds(Machine.Q(mach), Led.kind(mach, d))(b)(c)(h)
          ),
          Some{v},
          Safe.decide(~mach, ~d, a, b, later, c, h, Tip.voters(t), v)(em)
        ): {Line.moved(~mach, ~d, ~kern, b, c, t, _) == Some{x}: Maybe<&2, Tip>}
        Sim.moved(~mach, ~d, ~kern, a, b, later, c, t, v, x)(e)

# the next tip of a line stays in a later ledger
def Hist.next(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
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
  +t: Tip,
  +x: Tip
) -> {Line.next(~mach, ~d, ~kern, a, c, h, t) == Some{x}: Maybe<&2, Tip>}
  -> {Line.next(~mach, ~d, ~kern, b, c, h, t) == Some{x}: Maybe<&2, Tip>}:
  e => Hist.next.at(
    ~mach,
    ~d,
    ~kern,
    a,
    b,
    later,
    c,
    h,
    t,
    x,
    Height.decide(
      ~mach,
      ~d,
      a,
      c,
      h,
      Tip.voters(t),
      Ledgers.Kind.rounds(Machine.Q(mach), Led.kind(mach, d))(a)(c)(h)
    )
  )({==})(e)

# a found read, once the read is known (la): what it finds in a ledger that
# grows (lb), it finds there too
def Hist.value.of(lb: Trees.Look, -v: List<&2, U32>) -> {
  Trees.Look.known(lb) == Some{Some{v}}: Maybe<&2, Maybe<&2, List<&2, U32>>>
} -> {Trees.Look.value(lb) == Some{v}: Maybe<&2, List<&2, U32>>}:
  match lb:
    case Trees.Look.Found{u}:
      e => Equal.cong(
        List<&2, U32>,
        Maybe<&2, List<&2, U32>>,
        y => Some{y},
        u,
        v,
        Shared.Maybe.some_inj(
          List<&2, U32>,
          u,
          v,
          Shared.Maybe.some_inj(Maybe<&2, List<&2, U32>>, Some{u}, Some{v}, e)
        )
      )
    case Trees.Look.Absent{}:
      e => Empty.absurd(
        {None{} == Some{v}: Maybe<&2, List<&2, U32>>},
        Shared.Maybe.none_ne_some(
          List<&2, U32>,
          v,
          Shared.Maybe.some_inj(Maybe<&2, List<&2, U32>>, None{}, Some{v}, e)
        )
      )
    case Trees.Look.Missing{y}:
      e => Empty.absurd(
        {None{} == Some{v}: Maybe<&2, List<&2, U32>>},
        Shared.Maybe.none_ne_some(Maybe<&2, List<&2, U32>>, Some{v}, e)
      )

# a read that found v in a finds v in each ledger whose reads keep what a's
# tell (hk)
def Hist.value(
  la: Trees.Look,
  lb: Trees.Look,
  -v: List<&2, U32>,
  hk: {Trees.Look.known(la) == Some{Some{v}}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
    -> {Trees.Look.known(lb) == Some{Some{v}}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
) -> {Trees.Look.value(la) == Some{v}: Maybe<&2, List<&2, U32>>}
  -> {Trees.Look.value(lb) == Some{v}: Maybe<&2, List<&2, U32>>}:
  match la:
    case Trees.Look.Found{u}:
      e => Hist.value.of(
        lb,
        v
      )(hk(Equal.cong(List<&2, U32>, Maybe<&2, Maybe<&2, List<&2, U32>>>, y => Some{Some{y}}, u, v, Shared.Maybe.some_inj(List<&2, U32>, u, v, e))))
    case Trees.Look.Absent{}:
      e => Empty.absurd(
        {Trees.Look.value(lb) == Some{v}: Maybe<&2, List<&2, U32>>},
        Shared.Maybe.none_ne_some(List<&2, U32>, v, e)
      )
    case Trees.Look.Missing{y}:
      e => Empty.absurd(
        {Trees.Look.value(lb) == Some{v}: Maybe<&2, List<&2, U32>>},
        Shared.Maybe.none_ne_some(List<&2, U32>, v, e)
      )

# what the log of a tip holds, it holds in a ledger that grows
def Hist.tip_get(
  ~mach: Machine(),
  ~d: Led(mach),
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  +t: Tip,
  +key: List<&2, U32>,
  v: List<&2, U32>,
  g: Led.Grows(mach, d, a, b)
) -> {Tip.get(~mach, ~d, a, t, key) == Some{v}: Maybe<&2, List<&2, U32>>}
  -> {Tip.get(~mach, ~d, b, t, key) == Some{v}: Maybe<&2, List<&2, U32>>}:
  e => Hist.value(
    Tree.look(~mach, ~d, a, Tip.log(t), key),
    Tree.look(~mach, ~d, b, Tip.log(t), key),
    v,
    Hist.find(~mach, ~d, a, b, Tip.log(t), key, Some{v}, g)
  )(e)

# the walk of a line in one ledger keeps each key that its log holds
def Hist.walk_keep(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  f: Nat,
  +b: Led.L(mach, d),
  +c: Ledgers.Line,
  +h: U32,
  +t: Tip,
  m: Maybe<&2, Tip>,
  +key: List<&2, U32>,
  +v: List<&2, U32>
) -> {Line.next(~mach, ~d, ~kern, b, c, h, t) == m: Maybe<&2, Tip>}
  -> {Tip.get(~mach, ~d, b, t, key) == Some{v}: Maybe<&2, List<&2, U32>>}
  -> {Tip.get(~mach, ~d, b, Line.walk(~mach, ~d, ~kern, f, b, c, h, t, m), key) == Some{v}: Maybe<&2, List<&2, U32>>}:
  match f m:
    case 0n y:
      em => ek => ek
    case 1n+g None{}:
      em => ek => ek
    case 1n+g Some{+t2}:
      em => ek => Hist.walk_keep(
        ~mach,
        ~d,
        ~kern,
        g,
        b,
        c,
        U32.inc(h),
        t2,
        Line.next(~mach, ~d, ~kern, b, c, U32.inc(h), t2),
        key,
        v
      )({==})(Keep.next(~mach, ~d, ~kern, b, c, h, t, t2, key, v)(em)(ek))

# the walks of a line in a ledger and in a later one: what the log of the
# first walk holds, the log of the second holds. The later walk follows the
# same tips (Hist.next), has at least as much fuel, and then keeps the keys
# (Hist.walk_keep)
def Hist.walk(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  fa: Nat,
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
  +t: Tip,
  ma: Maybe<&2, Tip>,
  fb: Nat,
  mb: Maybe<&2, Tip>,
  +key: List<&2, U32>,
  +v: List<&2, U32>
) -> {Nat.is_le(fa, fb) == True{}: Bool}
  -> {Line.next(~mach, ~d, ~kern, a, c, h, t) == ma: Maybe<&2, Tip>}
  -> {Line.next(~mach, ~d, ~kern, b, c, h, t) == mb: Maybe<&2, Tip>}
  -> {Tip.get(~mach, ~d, a, Line.walk(~mach, ~d, ~kern, fa, a, c, h, t, ma), key) == Some{v}: Maybe<&2, List<&2, U32>>}
  -> {Tip.get(~mach, ~d, b, Line.walk(~mach, ~d, ~kern, fb, b, c, h, t, mb), key) == Some{v}: Maybe<&2, List<&2, U32>>}:
  match fa ma:
    case 0n y:
      le => ea => eb => eg => Hist.walk_keep(
        ~mach,
        ~d,
        ~kern,
        fb,
        b,
        c,
        h,
        t,
        mb,
        key,
        v
      )(eb)(Hist.tip_get(~mach, ~d, a, b, t, key, v, Led.later_grows(~mach, ~d, a, b)(later))(eg))
    case 1n+f None{}:
      le => ea => eb => eg => Hist.walk_keep(
        ~mach,
        ~d,
        ~kern,
        fb,
        b,
        c,
        h,
        t,
        mb,
        key,
        v
      )(eb)(Hist.tip_get(~mach, ~d, a, b, t, key, v, Led.later_grows(~mach, ~d, a, b)(later))(eg))
    case 1n+(+f) Some{+t2}:
      match fb mb:
        case 0n y:
          le => Empty.absurd(
            {Line.next(~mach, ~d, ~kern, a, c, h, t) == Some{t2}: Maybe<&2, Tip>}
              -> {Line.next(~mach, ~d, ~kern, b, c, h, t) == y: Maybe<&2, Tip>}
              -> {Tip.get(~mach, ~d, a, Line.walk(~mach, ~d, ~kern, 1n+f, a, c, h, t, Some{t2}), key) == Some{v}: Maybe<&2, List<&2, U32>>}
              -> {Tip.get(~mach, ~d, b, Line.walk(~mach, ~d, ~kern, 0n, b, c, h, t, y), key) == Some{v}: Maybe<&2, List<&2, U32>>},
            Shared.Bool.false_ne_true(le)
          )
        case 1n+g None{}:
          le => ea => eb => Empty.absurd(
            {Tip.get(~mach, ~d, a, Line.walk(~mach, ~d, ~kern, 1n+f, a, c, h, t, Some{t2}), key) == Some{v}: Maybe<&2, List<&2, U32>>}
              -> {Tip.get(~mach, ~d, b, Line.walk(~mach, ~d, ~kern, 1n+g, b, c, h, t, None{}), key) == Some{v}: Maybe<&2, List<&2, U32>>},
            Shared.Maybe.none_ne_some(
              Tip,
              t2,
              Equal.trans(
                Maybe<&2, Tip>,
                None{},
                Line.next(~mach, ~d, ~kern, b, c, h, t),
                Some{t2},
                Equal.sym(Maybe<&2, Tip>, Line.next(~mach, ~d, ~kern, b, c, h, t), None{}, eb),
                Hist.next(~mach, ~d, ~kern, a, b, later, c, h, t, t2)(ea)
              )
            )
          )
        case 1n+(+g) Some{+t3}:
          le => ea => eb => eg =>
            %Shared.Maybe.some_inj(
              Tip,
              t2,
              t3,
              Equal.trans(
                Maybe<&2, Tip>,
                Some{t2},
                Line.next(~mach, ~d, ~kern, b, c, h, t),
                Some{t3},
                Equal.sym(
                  Maybe<&2, Tip>,
                  Line.next(~mach, ~d, ~kern, b, c, h, t),
                  Some{t2},
                  Hist.next(~mach, ~d, ~kern, a, b, later, c, h, t, t2)(ea)
                ),
                eb
              )
            ): {
              Tip.get(
                ~mach,
                ~d,
                b,
                Line.walk(~mach, ~d, ~kern, g, b, c, U32.inc(h), _, Line.next(~mach, ~d, ~kern, b, c, U32.inc(h), _)),
                key
              )
                == Some{v}: Maybe<&2, List<&2, U32>>
            }
            Hist.walk(
              ~mach,
              ~d,
              ~kern,
              f,
              a,
              b,
              later,
              c,
              U32.inc(h),
              t2,
              Line.next(~mach, ~d, ~kern, a, c, U32.inc(h), t2),
              g,
              Line.next(~mach, ~d, ~kern, b, c, U32.inc(h), t2),
              key,
              v
            )(le)({==})({==})(eg)

# that no ballot is above the height bound, of the laws ls
def Hist.laws.heights1(
  -Q: Data,
  -c: Codes.Codec(Q),
  -k: Ledgers.Ledger.Kind(Q),
  ls: Ledgers.Ledger.Laws(Q, c, k)
) -> @l: Ledgers.Kind.L(Q, k) -> @b: Ledgers.Ballot -> @line: Ledgers.Line -> @h: U32 -> @r: Nat -> @voter: String -> {
  Ledgers.Kind.has(~Q, ~c, ~k, l, Ledgers.Entry.Ballot{b}) == True{}: Bool
} -> {
  Ledgers.Ballot.is_at(b, Ledgers.Place{line, h, r}, voter) == True{}: Bool
} -> {Nat.is_le(U32.to_nat(h), Ledgers.Kind.heights(Q, k)(l)(line)) == True{}: Bool}:
  match ls:
    case Tuple{e0, Tuple{e1, Tuple{e2, Tuple{e3, Tuple{e4, Tuple{e5, Tuple{e6, Tuple{e7, Tuple{Tuple{p1, p2}, r}}}}}}}}}:
      p1

# that the height bound is the height of a ballot, or 0, of the laws ls
def Hist.laws.heights2(
  -Q: Data,
  -c: Codes.Codec(Q),
  -k: Ledgers.Ledger.Kind(Q),
  ls: Ledgers.Ledger.Laws(Q, c, k)
) -> @l: Ledgers.Kind.L(Q, k) -> @line: Ledgers.Line -> {
  Nat.is_eq(Ledgers.Kind.heights(Q, k)(l)(line), 0n) == False{}: Bool
} -> Exists(
  Ledgers.Ballot,
  b => {
    Ledgers.Kind.has(~Q, ~c, ~k, l, Ledgers.Entry.Ballot{b}) == True{}: Bool
  }
    & Exists(
      U32,
      h => Exists(
        Nat,
        r => {
          Ledgers.Ballot.is_at(b, Ledgers.Place{line, h, r}, Ledgers.Ballot.voter(b)) == True{}: Bool
        }
          & {U32.to_nat(h) == Ledgers.Kind.heights(Q, k)(l)(line): Nat}
      )
    )
):
  match ls:
    case Tuple{e0, Tuple{e1, Tuple{e2, Tuple{e3, Tuple{e4, Tuple{e5, Tuple{e6, Tuple{e7, Tuple{Tuple{p1, p2}, r}}}}}}}}}:
      p2

# a number that is one more than another is not zero
def Hist.ne_zero(-n: Nat, -p: Nat, e: {n == 1n+p: Nat}) -> {Nat.is_eq(n, 0n) == False{}: Bool}:
  %Equal.sym(Nat, n, 1n+p, e): {Nat.is_eq(_, 0n) == False{}: Bool}
  {==}

# what a ledger holds, a ledger that grows holds
def Hist.has_grows(
  ~mach: Machine(),
  ~d: Led(mach),
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  +e: Entry(mach),
  +g: Led.Grows(mach, d, a, b)
) -> {Ledgers.Kind.has(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), a, e) == True{}: Bool}
  -> {Ledgers.Kind.has(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), b, e) == True{}: Bool}:
  Ledgers.Kind.grows_has(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), ~Led.laws(mach, d), a, b, g, e)

# the height bound of a line grows with the ledger, once a ballot at it is
# known (ex)
def Hist.heights.of(
  ~mach: Machine(),
  ~d: Led(mach),
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
  ex: Exists(
    Ledgers.Ballot,
    bl => {
      Ledgers.Kind.has(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), a, Ledgers.Entry.Ballot{bl}) == True{}: Bool
    }
      & Exists(
        U32,
        h => Exists(
          Nat,
          r => {
            Ledgers.Ballot.is_at(bl, Ledgers.Place{c, h, r}, Ledgers.Ballot.voter(bl)) == True{}: Bool
          }
            & {U32.to_nat(h) == Ledgers.Kind.heights(Machine.Q(mach), Led.kind(mach, d))(a)(c): Nat}
        )
      )
  )
) -> {
  Nat.is_le(
    Ledgers.Kind.heights(Machine.Q(mach), Led.kind(mach, d))(a)(c),
    Ledgers.Kind.heights(Machine.Q(mach), Led.kind(mach, d))(b)(c)
  )
    == True{}: Bool
}:
  match ex:
    case Tuple{+bl, Tuple{hasa, Tuple{+h, Tuple{+r, Tuple{isat, eh}}}}}:
      %eh: {Nat.is_le(_, Ledgers.Kind.heights(Machine.Q(mach), Led.kind(mach, d))(b)(c)) == True{}: Bool}
      Hist.laws.heights1(
        Machine.Q(mach),
        Machine.code(mach),
        Led.kind(mach, d),
        Led.laws(mach, d)
      )(
        b
      )(
        bl
      )(
        c
      )(
        h
      )(
        r
      )(
        Ledgers.Ballot.voter(bl)
      )(Hist.has_grows(~mach, ~d, a, b, Ledgers.Entry.Ballot{bl}, Led.later_grows(~mach, ~d, a, b)(later))(hasa))(isat)

# the height bound of a line grows with the ledger, once it is known (n)
def Hist.heights.at(
  ~mach: Machine(),
  ~d: Led(mach),
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
  n: Nat
) -> {Ledgers.Kind.heights(Machine.Q(mach), Led.kind(mach, d))(a)(c) == n: Nat} -> {
  Nat.is_le(
    Ledgers.Kind.heights(Machine.Q(mach), Led.kind(mach, d))(a)(c),
    Ledgers.Kind.heights(Machine.Q(mach), Led.kind(mach, d))(b)(c)
  )
    == True{}: Bool
}:
  match n:
    case 0n:
      en =>
        %Equal.sym(Nat, Ledgers.Kind.heights(Machine.Q(mach), Led.kind(mach, d))(a)(c), 0n, en): {
          Nat.is_le(_, Ledgers.Kind.heights(Machine.Q(mach), Led.kind(mach, d))(b)(c)) == True{}: Bool
        }
        Shared.Nat.le_zero(Ledgers.Kind.heights(Machine.Q(mach), Led.kind(mach, d))(b)(c))
    case 1n+p:
      en => Hist.heights.of(
        ~mach,
        ~d,
        a,
        b,
        later,
        c,
        Hist.laws.heights2(
          Machine.Q(mach),
          Machine.code(mach),
          Led.kind(mach, d),
          Led.laws(mach, d)
        )(a)(c)(Hist.ne_zero(Ledgers.Kind.heights(Machine.Q(mach), Led.kind(mach, d))(a)(c), p, en))
      )

# the first tip of a root line stays, once the entry of its request is known
# (m)
def Hist.root_start.at(
  ~mach: Machine(),
  m: Maybe<&2, Entry(mach)>,
  -m2: Maybe<&2, Entry(mach)>,
  hm: @e: Entry(mach) -> {m == Some{e}: Maybe<&2, Entry(mach)>} -> {m2 == Some{e}: Maybe<&2, Entry(mach)>},
  -x: Tip
) -> {Root.start.of(~mach, m) == Some{x}: Maybe<&2, Tip>} -> {Root.start.of(~mach, m2) == Some{x}: Maybe<&2, Tip>}:
  match m:
    case None{}:
      e => Empty.absurd(
        {Root.start.of(~mach, m2) == Some{x}: Maybe<&2, Tip>},
        Shared.Maybe.none_ne_some(Tip, x, e)
      )
    case Some{y}:
      e =>
        %Equal.sym(Maybe<&2, Entry(mach)>, m2, Some{y}, hm(y)({==})): {
          Root.start.of(~mach, _) == Some{x}: Maybe<&2, Tip>
        }
        e

# the first tip of a root line stays in a later ledger
def Hist.root_start(
  ~mach: Machine(),
  ~d: Led(mach),
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  +later: {
    Bool.and(
      Ledgers.Kind.grows(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), a, b),
      Led.honest(~mach, ~d, b)
    )
      == True{}: Bool
  },
  +r: Hashes.Hash,
  -x: Tip
) -> {Root.start(~mach, ~d, a, r) == Some{x}: Maybe<&2, Tip>}
  -> {Root.start(~mach, ~d, b, r) == Some{x}: Maybe<&2, Tip>}:
  e => Hist.root_start.at(
    ~mach,
    Led.get(~mach, ~d, a, Ledgers.Name.Ask{r}),
    Led.get(~mach, ~d, b, Ledgers.Name.Ask{r}),
    y => Hist.gets(~mach, ~d, a, b, Led.later_grows(~mach, ~d, a, b)(later))(Ledgers.Name.Ask{r})(y),
    x
  )(e)

# a tip that some data is stays, once the data is known (m)
def Hist.whole(
  m: Maybe<&2, List<&2, U32>>,
  -m2: Maybe<&2, List<&2, U32>>,
  hm: @w: List<&2, U32> -> {m == Some{w}: Maybe<&2, List<&2, U32>>} -> {m2 == Some{w}: Maybe<&2, List<&2, U32>>},
  -x: Tip
) -> {Codes.Code.whole.of(~Tip, ~Tip.code, ~Tip.code.read, m) == Some{x}: Maybe<&2, Tip>}
  -> {Codes.Code.whole.of(~Tip, ~Tip.code, ~Tip.code.read, m2) == Some{x}: Maybe<&2, Tip>}:
  match m:
    case None{}:
      e => Empty.absurd(
        {Codes.Code.whole.of(~Tip, ~Tip.code, ~Tip.code.read, m2) == Some{x}: Maybe<&2, Tip>},
        Shared.Maybe.none_ne_some(Tip, x, e)
      )
    case Some{y}:
      e =>
        %Equal.sym(Maybe<&2, List<&2, U32>>, m2, Some{y}, hm(y)({==})): {
          Codes.Code.whole.of(~Tip, ~Tip.code, ~Tip.code.read, _) == Some{x}: Maybe<&2, Tip>
        }
        e

# the tip that some words name stays in a later ledger
def Hist.named(
  ~mach: Machine(),
  ~d: Led(mach),
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  +later: {
    Bool.and(
      Ledgers.Kind.grows(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), a, b),
      Led.honest(~mach, ~d, b)
    )
      == True{}: Bool
  },
  ws: List<&2, U32>,
  -x: Tip
) -> {Tip.named(~mach, ~d, a, ws) == Some{x}: Maybe<&2, Tip>}
  -> {Tip.named(~mach, ~d, b, ws) == Some{x}: Maybe<&2, Tip>}:
  e => Shared.Maybe.bind_kept(
    Hashes.Hash,
    Tip,
    Codes.Code.whole.read(~Hashes.Hash, ~Hashes.Hash.code, ~Hashes.Hash.code.read, ws),
    Codes.Code.whole.read(~Hashes.Hash, ~Hashes.Hash.code, ~Hashes.Hash.code.read, ws),
    h => Tip.at(~mach, ~d, a, h),
    h => Tip.at(~mach, ~d, b, h),
    x,
    h => eh => eh,
    +h => Hist.whole(
      Led.fetch(~mach, ~d, a, h),
      Led.fetch(~mach, ~d, b, h),
      w => Hist.fetch(~mach, ~d, a, b, h, w, Led.later_grows(~mach, ~d, a, b)(later)),
      x
    )
  )(e)

# a bind of a bind is a bind of a bind
def Hist.bind_assoc(
  -A: Data,
  -B: Data,
  -C: Data,
  m: Maybe<&2, A>,
  -f: A -> Maybe<&2, B>,
  -g: B -> Maybe<&2, C>
) -> {
  Maybe.bind(&2, A, C, m, x => Maybe.bind(&2, B, C, f(x), g))
    == Maybe.bind(&2, B, C, Maybe.bind(&2, A, B, m, f), g): Maybe<&2, C>
}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

# what the log of the newest tip of a line holds stays in a later ledger, when
# its first tip stays (hm)
def Hist.head_get(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
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
  ma: Maybe<&2, Tip>,
  -mb: Maybe<&2, Tip>,
  hm: @t: Tip -> {ma == Some{t}: Maybe<&2, Tip>} -> {mb == Some{t}: Maybe<&2, Tip>},
  +key: List<&2, U32>,
  +v: List<&2, U32>
) -> {
  Maybe.bind(&2, Tip, List<&2, U32>, Line.head.of(~mach, ~d, ~kern, a, c, ma), t => Tip.get(~mach, ~d, a, t, key))
    == Some{v}: Maybe<&2, List<&2, U32>>
} -> {
  Maybe.bind(&2, Tip, List<&2, U32>, Line.head.of(~mach, ~d, ~kern, b, c, mb), t => Tip.get(~mach, ~d, b, t, key))
    == Some{v}: Maybe<&2, List<&2, U32>>
}:
  match ma:
    case None{}:
      e => Empty.absurd(
        {
          Maybe.bind(&2, Tip, List<&2, U32>, Line.head.of(~mach, ~d, ~kern, b, c, mb), t => Tip.get(~mach, ~d, b, t, key))
            == Some{v}: Maybe<&2, List<&2, U32>>
        },
        Shared.Maybe.none_ne_some(List<&2, U32>, v, e)
      )
    case Some{+t}:
      e =>
        %Equal.sym(Maybe<&2, Tip>, mb, Some{t}, hm(t)({==})): {
          Maybe.bind(&2, Tip, List<&2, U32>, Line.head.of(~mach, ~d, ~kern, b, c, _), t => Tip.get(~mach, ~d, b, t, key))
            == Some{v}: Maybe<&2, List<&2, U32>>
        }
        Hist.walk(
          ~mach,
          ~d,
          ~kern,
          1n+Ledgers.Kind.heights(Machine.Q(mach), Led.kind(mach, d))(a)(c),
          a,
          b,
          later,
          c,
          0,
          t,
          Line.next(~mach, ~d, ~kern, a, c, 0, t),
          1n+Ledgers.Kind.heights(Machine.Q(mach), Led.kind(mach, d))(b)(c),
          Line.next(~mach, ~d, ~kern, b, c, 0, t),
          key,
          v
        )(
          Hist.heights.at(
            ~mach,
            ~d,
            a,
            b,
            later,
            c,
            Ledgers.Kind.heights(Machine.Q(mach), Led.kind(mach, d))(a)(c)
          )({==})
        )({==})({==})(e)

# the first tip of a sub line stays, once the newest tip of its root line in
# the earlier ledger is known (ma)
def Hist.sub_start(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  +later: {
    Bool.and(
      Ledgers.Kind.grows(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), a, b),
      Led.honest(~mach, ~d, b)
    )
      == True{}: Bool
  },
  +r: Hashes.Hash,
  +s: String,
  -x: Tip
) -> {Sub.start(~mach, ~d, a, s, Root.head(~mach, ~d, ~kern, a, r)) == Some{x}: Maybe<&2, Tip>}
  -> {Sub.start(~mach, ~d, b, s, Root.head(~mach, ~d, ~kern, b, r)) == Some{x}: Maybe<&2, Tip>}:
  e => Equal.trans(
    Maybe<&2, Tip>,
    Sub.start(~mach, ~d, b, s, Root.head(~mach, ~d, ~kern, b, r)),
    Maybe.bind(
      &2,
      List<&2, U32>,
      Tip,
      Maybe.bind(
        &2,
        Tip,
        List<&2, U32>,
        Root.head(~mach, ~d, ~kern, b, r),
        t => Tip.get(~mach, ~d, b, t, Log.start(s))
      ),
      ws => Tip.named(~mach, ~d, b, ws)
    ),
    Some{x},
    Hist.bind_assoc(
      Tip,
      List<&2, U32>,
      Tip,
      Root.head(~mach, ~d, ~kern, b, r),
      t => Tip.get(~mach, ~d, b, t, Log.start(s)),
      ws => Tip.named(~mach, ~d, b, ws)
    ),
    Shared.Maybe.bind_kept(
      List<&2, U32>,
      Tip,
      Maybe.bind(
        &2,
        Tip,
        List<&2, U32>,
        Root.head(~mach, ~d, ~kern, a, r),
        t => Tip.get(~mach, ~d, a, t, Log.start(s))
      ),
      Maybe.bind(
        &2,
        Tip,
        List<&2, U32>,
        Root.head(~mach, ~d, ~kern, b, r),
        t => Tip.get(~mach, ~d, b, t, Log.start(s))
      ),
      ws => Tip.named(~mach, ~d, a, ws),
      ws => Tip.named(~mach, ~d, b, ws),
      x,
      +ws => Hist.head_get(
        ~mach,
        ~d,
        ~kern,
        a,
        b,
        later,
        Ledgers.Line{r, None{}},
        Root.start(~mach, ~d, a, r),
        Root.start(~mach, ~d, b, r),
        t => Hist.root_start(~mach, ~d, a, b, later, r, t),
        Log.start(s),
        ws
      ),
      ws => Hist.named(~mach, ~d, a, b, later, ws, x)
    )(
      Equal.trans(
        Maybe<&2, Tip>,
        Maybe.bind(
          &2,
          List<&2, U32>,
          Tip,
          Maybe.bind(
            &2,
            Tip,
            List<&2, U32>,
            Root.head(~mach, ~d, ~kern, a, r),
            t => Tip.get(~mach, ~d, a, t, Log.start(s))
          ),
          ws => Tip.named(~mach, ~d, a, ws)
        ),
        Sub.start(~mach, ~d, a, s, Root.head(~mach, ~d, ~kern, a, r)),
        Some{x},
        Equal.sym(
          Maybe<&2, Tip>,
          Sub.start(~mach, ~d, a, s, Root.head(~mach, ~d, ~kern, a, r)),
          Maybe.bind(
            &2,
            List<&2, U32>,
            Tip,
            Maybe.bind(
              &2,
              Tip,
              List<&2, U32>,
              Root.head(~mach, ~d, ~kern, a, r),
              t => Tip.get(~mach, ~d, a, t, Log.start(s))
            ),
            ws => Tip.named(~mach, ~d, a, ws)
          ),
          Hist.bind_assoc(
            Tip,
            List<&2, U32>,
            Tip,
            Root.head(~mach, ~d, ~kern, a, r),
            t => Tip.get(~mach, ~d, a, t, Log.start(s)),
            ws => Tip.named(~mach, ~d, a, ws)
          )
        ),
        e
      )
    )
  )

# the first tip of a line stays in a later ledger
def Hist.start(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  +later: {
    Bool.and(
      Ledgers.Kind.grows(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), a, b),
      Led.honest(~mach, ~d, b)
    )
      == True{}: Bool
  },
  c: Ledgers.Line,
  -x: Tip
) -> {Line.start(~mach, ~d, ~kern, a, c) == Some{x}: Maybe<&2, Tip>}
  -> {Line.start(~mach, ~d, ~kern, b, c) == Some{x}: Maybe<&2, Tip>}:
  match c:
    case Ledgers.Line{+r, None{}}:
      Hist.root_start(~mach, ~d, a, b, later, r, x)
    case Ledgers.Line{+r, Some{+s}}:
      Hist.sub_start(~mach, ~d, ~kern, a, b, later, r, s, x)

# the tip of a line after k steps stays in a later ledger
def Hist.at(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  k: Nat,
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
  +x: Tip
) -> {Line.at(~mach, ~d, ~kern, k, a, c) == Some{x}: Maybe<&2, Tip>}
  -> {Line.at(~mach, ~d, ~kern, k, b, c) == Some{x}: Maybe<&2, Tip>}:
  match k:
    case 0n:
      Hist.start(~mach, ~d, ~kern, a, b, later, c, x)
    case 1n+(+p):
      e => Shared.Maybe.bind_kept(
        Tip,
        Tip,
        Line.at(~mach, ~d, ~kern, p, a, c),
        Line.at(~mach, ~d, ~kern, p, b, c),
        t => Line.next(~mach, ~d, ~kern, a, c, U32.from_nat(p), t),
        t => Line.next(~mach, ~d, ~kern, b, c, U32.from_nat(p), t),
        x,
        t => Hist.at(~mach, ~d, ~kern, p, a, b, later, c, t),
        +t => Hist.next(~mach, ~d, ~kern, a, b, later, c, U32.from_nat(p), t, x)
      )(e)

# what the log of a line holds stays in a later ledger
def Hist.get(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
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
  +key: List<&2, U32>,
  +v: List<&2, U32>
) -> {Line.get(~mach, ~d, ~kern, a, c, key) == Some{v}: Maybe<&2, List<&2, U32>>}
  -> {Line.get(~mach, ~d, ~kern, b, c, key) == Some{v}: Maybe<&2, List<&2, U32>>}:
  Hist.head_get(
    ~mach,
    ~d,
    ~kern,
    a,
    b,
    later,
    c,
    Line.start(~mach, ~d, ~kern, a, c),
    Line.start(~mach, ~d, ~kern, b, c),
    t => Hist.start(~mach, ~d, ~kern, a, b, later, c, t),
    key,
    v
  )

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

def Line.at_grows(mach, d, kern, k, c):
  +a => +b => +x => later => e => Hist.at(
    ~mach,
    ~d,
    ~kern,
    k,
    a,
    b,
    later,
    c,
    x
  )(e)

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

def Line.get_grows(mach, d, kern, c, key):
  +a => +b => +x => later => e => Hist.get(
    ~mach,
    ~d,
    ~kern,
    a,
    b,
    later,
    c,
    key,
    x
  )(e)

# Outcomes of a step
# ------------------
# A run whose ledger holds what it added gives each of its requests an
# outcome: the run writes it, or finds it, and then keeps it (Keep).

# the words v are the code of an outcome
def Outs.decodes(v: List<&2, U32>) -> Bool:
  Maybe.is_some(&2, Out, Codes.Code.whole.of(~Out, ~Out.code, ~Out.code.read, Some{v}))

# that the log of the run r reads, in s, the outcome of the request i, once s
# holds what r added
def Outs.Has(-mach: Machine(), -d: Led(mach), -s: Led.L(mach, d), -i: Ledgers.Id, -r: Run<Led.L(mach, d)>) -> Type:
  Exists(
    List<&2, U32>,
    v => {Outs.decodes(v) == True{}: Bool} & Keep.Has(mach, d, s, Log.out(i), v, r)
  )

# Outs.Has of the result m of a run, when there is one
def Outs.Res(
  -mach: Machine(),
  -d: Led(mach),
  -s: Led.L(mach, d),
  -i: Ledgers.Id,
  m: Maybe<&2, Run<Led.L(mach, d)>>
) -> Type:
  match m:
    case None{}:
      Unit
    case Some{r}:
      Outs.Has(mach, d, s, i, r)

# the code of an outcome is the code of an outcome
def Outs.code(+o: Out) -> {Outs.decodes(Out.code(o, [])) == True{}: Bool}:
  %Equal.sym(
    Maybe<&2, Out>,
    Codes.Code.whole.read(~Out, ~Out.code, ~Out.code.read, Out.code(o, [])),
    Some{o},
    Codes.Code.whole_read(~Out, ~Out.code, ~Out.code.read, ~(x => r => Out.code_read(x, r)), o)
  ): {Maybe.is_some(&2, Out, _) == True{}: Bool}
  {==}

# a kept outcome is an outcome
def Outs.of_keep(
  -mach: Machine(),
  -d: Led(mach),
  -s: Led.L(mach, d),
  -i: Ledgers.Id,
  v: List<&2, U32>,
  dv: {Outs.decodes(v) == True{}: Bool},
  m: Maybe<&2, Run<Led.L(mach, d)>>,
  ko: Keep.Out(mach, d, s, Log.out(i), v, m)
) -> Outs.Res(mach, d, s, i, m):
  match m:
    case None{}:
      Unit{}
    case Some{r}:
      Tuple{v, Tuple{dv, ko}}

# after a write that s holds, the log reads the key as written, in s (w: the
# law of the write)
def Outs.fin.of(
  ~mach: Machine(),
  ~d: Led(mach),
  +s: Led.L(mach, d),
  +t: Tip,
  +k: List<&2, U32>,
  +x: List<&2, U32>,
  +e: Trees.Edit,
  w: {
    Trees.Ops.look(Led.L(mach, d), Led.tree(mach, d))(s)(Trees.Edit.root(e))(k)
      == Trees.Look.of(Some{x}): Trees.Look
  }
    & (
      @k2: List<&2, U32> -> @y: Maybe<&2, List<&2, U32>> -> {
        Shared.List.is_eq(~U32, ~U32.is_eq, k, k2) == False{}: Bool
      } -> {
        Trees.Look.known(Trees.Ops.look(Led.L(mach, d), Led.tree(mach, d))(s)(Tip.log(t))(k2))
          == Some{y}: Maybe<&2, Maybe<&2, List<&2, U32>>>
      } -> {
        Trees.Look.known(Trees.Ops.look(Led.L(mach, d), Led.tree(mach, d))(s)(Trees.Edit.root(e))(k2))
          == Some{y}: Maybe<&2, Maybe<&2, List<&2, U32>>>
      }
    )
) -> {Tip.get(~mach, ~d, s, Tip.logged(t, Trees.Edit.root(e)), k) == Some{x}: Maybe<&2, List<&2, U32>>}:
  match w:
    case Tuple{w1, w2}:
      %Equal.sym(
        Maybe<&2, Hashes.Hash>,
        Tip.log(Tip.logged(t, Trees.Edit.root(e))),
        Trees.Edit.root(e),
        Keep.log_logged(t, Trees.Edit.root(e))
      ): {Tree.get(~mach, ~d, s, _, k) == Some{x}: Maybe<&2, List<&2, U32>>}
      %Equal.sym(
        Trees.Look,
        Trees.Ops.look(Led.L(mach, d), Led.tree(mach, d))(s)(Trees.Edit.root(e))(k),
        Trees.Look.of(Some{x}),
        w1
      ): {Trees.Look.value(_) == Some{x}: Maybe<&2, List<&2, U32>>}
      {==}

# a write whose nodes s holds reads, in s, as written
def Outs.fin(
  ~mach: Machine(),
  ~d: Led(mach),
  +s: Led.L(mach, d),
  +lr: Led.L(mach, d),
  +t: Tip,
  +a: List<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +x: List<&2, U32>,
  +e: Trees.Edit,
  ep: {Tree.put(~mach, ~d, lr, Tip.log(t), k, Some{x}) == Some{e}: Maybe<&2, Trees.Edit>},
  bd: Keep.Base(mach, d, s, Run{lr, t, a}),
  hn: {Ext.holds(~mach, ~d, s, Trees.Edit.nodes(e)) == True{}: Bool},
  ha: {Ext.holds(~mach, ~d, s, a) == True{}: Bool}
) -> {Tip.get(~mach, ~d, s, Tip.logged(t, Trees.Edit.root(e)), k) == Some{x}: Maybe<&2, List<&2, U32>>}:
  Outs.fin.of(
    ~mach,
    ~d,
    s,
    t,
    k,
    x,
    e,
    Hist.write(mach, d)(lr)(s)(Tip.log(t))(k)(Some{x})(e)(ep)(Keep.base_grows(~mach, ~d, s, Run{lr, t, a}, bd, ha))(
      Ext.held(~mach, ~d, s, e, hn)
    )
  )

# a write of a key reads as written
def Outs.logged(
  ~mach: Machine(),
  ~d: Led(mach),
  +s: Led.L(mach, d),
  +lr: Led.L(mach, d),
  +t: Tip,
  +a: List<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +x: List<&2, U32>,
  p: Maybe<&2, Trees.Edit>,
  ep: {Tree.put(~mach, ~d, lr, Tip.log(t), k, Some{x}) == p: Maybe<&2, Trees.Edit>},
  bd: Keep.Base(mach, d, s, Run{lr, t, a})
) -> Keep.Out(mach, d, s, k, x, Run.logged(~mach, ~d, lr, t, a, p)):
  match p:
    case None{}:
      Unit{}
    case Some{+e}:
      +hh => Outs.fin(
        ~mach,
        ~d,
        s,
        lr,
        t,
        a,
        k,
        x,
        e,
        ep,
        bd,
        Ext.holds_left(~mach, ~d, s, Trees.Edit.nodes(e), a)(hh),
        Ext.holds_right(~mach, ~d, s, Trees.Edit.nodes(e), a)(hh)
      )

# Run.add.at reads as written
def Outs.add.at(
  ~mach: Machine(),
  ~d: Led(mach),
  +s: Led.L(mach, d),
  r: Run<Led.L(mach, d)>,
  +k: List<&2, U32>,
  +x: List<&2, U32>,
  m: Maybe<&2, Maybe<&2, List<&2, U32>>>,
  bd: Keep.Base(mach, d, s, r)
) -> Keep.Out(mach, d, s, k, x, Run.add.at(~mach, ~d, r, k, x, m)):
  match r m:
    case Run{+lr, +t, +a} Some{None{}}:
      Outs.logged(~mach, ~d, s, lr, t, a, k, x, Tree.put(~mach, ~d, lr, Tip.log(t), k, Some{x}), {==}, bd)
    case y Some{Some{old}}:
      Unit{}
    case y None{}:
      Unit{}

# Run.add reads as written
def Outs.add(
  ~mach: Machine(),
  ~d: Led(mach),
  +s: Led.L(mach, d),
  +r: Run<Led.L(mach, d)>,
  +k: List<&2, U32>,
  +x: List<&2, U32>,
  bd: Keep.Base(mach, d, s, r)
) -> Keep.Out(mach, d, s, k, x, Run.add(~mach, ~d, r, k, x)):
  Outs.add.at(
    ~mach,
    ~d,
    s,
    r,
    k,
    x,
    Tip.find(~mach, ~d, Run.ledger(Led.L(mach, d), r), Run.tip(Led.L(mach, d), r), k),
    bd
  )

# a refusal gives an outcome
def Outs.stale(
  ~mach: Machine(),
  ~d: Led(mach),
  +s: Led.L(mach, d),
  +r: Run<Led.L(mach, d)>,
  +i: Ledgers.Id,
  +a: Hashes.Hash,
  bd: Keep.Base(mach, d, s, r)
) -> Outs.Res(mach, d, s, i, Step.stale(~mach, ~d, r, i, a)):
  Outs.of_keep(
    mach,
    d,
    s,
    i,
    Out.code(Out.Stale{a}, []),
    Outs.code(Out.Stale{a}),
    Step.stale(~mach, ~d, r, i, a),
    Outs.add(~mach, ~d, s, r, Log.out(i), Out.code(Out.Stale{a}, []), bd)
  )

# taking a request gives an outcome
def Outs.taken.at(
  ~mach: Machine(),
  ~d: Led(mach),
  +s: Led.L(mach, d),
  +r: Run<Led.L(mach, d)>,
  +i: Ledgers.Id,
  +a: Hashes.Hash,
  +n: U32,
  +vs: Maybe<&2, List<&2, String>>,
  +bd: Keep.Base(mach, d, s, r)
) -> Outs.Res(mach, d, s, i, Step.taken.at(~mach, ~d, r, i, a, n, vs)):
  Outs.of_keep(
    mach,
    d,
    s,
    i,
    Out.code(Out.Taken{a, n}, []),
    Outs.code(Out.Taken{a, n}),
    Step.taken.at(~mach, ~d, r, i, a, n, vs),
    Keep.bind(
      ~mach,
      ~d,
      s,
      Log.out(i),
      Out.code(Out.Taken{a, n}, []),
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
      Outs.add(~mach, ~d, s, r, Log.out(i), Out.code(Out.Taken{a, n}, []), bd),
      Ext.add(~mach, ~d, s, r, Log.out(i), Out.code(Out.Taken{a, n}, [])),
      bd,
      +r1 => +bd1 => kh1 => Keep.bind(
        ~mach,
        ~d,
        s,
        Log.out(i),
        Out.code(Out.Taken{a, n}, []),
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
          s,
          Log.out(i),
          Out.code(Out.Taken{a, n}, []),
          r1,
          Log.taken(n),
          Taken.code(Taken{i, Tip.content(Run.tip(Led.L(mach, d), r1))}, []),
          bd1,
          kh1
        ),
        Ext.add(
          ~mach,
          ~d,
          s,
          r1,
          Log.taken(n),
          Taken.code(Taken{i, Tip.content(Run.tip(Led.L(mach, d), r1))}, [])
        ),
        bd1,
        r2 => bd2 => kh2 => Keep.step_next(~mach, ~d, s, Log.out(i), Out.code(Out.Taken{a, n}, []), r2, vs, kh2)
      )
    )
  )

# taking a request as the next number gives an outcome
def Outs.taken(
  ~mach: Machine(),
  ~d: Led(mach),
  +s: Led.L(mach, d),
  +r: Run<Led.L(mach, d)>,
  +i: Ledgers.Id,
  +a: Hashes.Hash,
  +vs: Maybe<&2, List<&2, String>>,
  bd: Keep.Base(mach, d, s, r)
) -> Outs.Res(mach, d, s, i, Step.taken(~mach, ~d, r, i, a, vs)):
  Outs.taken.at(~mach, ~d, s, r, i, a, Tip.count(Run.tip(Led.L(mach, d), r)), vs, bd)

# a run then a step that gives an outcome gives an outcome
def Outs.bind(
  ~mach: Machine(),
  ~d: Led(mach),
  +s: Led.L(mach, d),
  -i: Ledgers.Id,
  +r: Run<Led.L(mach, d)>,
  m: Maybe<&2, Run<Led.L(mach, d)>>,
  -g: Run<Led.L(mach, d)> -> Maybe<&2, Run<Led.L(mach, d)>>,
  gm: Ext.GainM(mach, d, s, r, m),
  bd: Keep.Base(mach, d, s, r),
  hg: @r1: Run<Led.L(mach, d)> -> Keep.Base(mach, d, s, r1) -> Outs.Res(mach, d, s, i, g(r1))
) -> Outs.Res(mach, d, s, i, Maybe.bind(&2, Run<Led.L(mach, d)>, Run<Led.L(mach, d)>, m, g)):
  match m:
    case None{}:
      Unit{}
    case Some{+r1}:
      hg(r1)(Keep.base(~mach, ~d, s, r, r1, bd, gm))

# a label on a taken request gives an outcome
def Outs.labelled(
  ~mach: Machine(),
  ~d: Led(mach),
  +s: Led.L(mach, d),
  +r: Run<Led.L(mach, d)>,
  +i: Ledgers.Id,
  +a: Hashes.Hash,
  +m: String,
  v: Maybe<&2, Taken>,
  +bd: Keep.Base(mach, d, s, r)
) -> Outs.Res(mach, d, s, i, Step.labelled(~mach, ~d, r, i, a, m, v)):
  match v:
    case None{}:
      Unit{}
    case Some{+x}:
      Outs.bind(
        ~mach,
        ~d,
        s,
        i,
        r,
        Run.add(~mach, ~d, r, Log.label(m), Ledgers.Id.code(Taken.id(x), [])),
        r2 => Step.taken(~mach, ~d, r2, i, a, None{}),
        Ext.add(~mach, ~d, s, r, Log.label(m), Ledgers.Id.code(Taken.id(x), [])),
        bd,
        +r2 => bd2 => Outs.taken(~mach, ~d, s, r2, i, a, None{}, bd2)
      )

# Step.label.at gives an outcome
def Outs.label.at(
  ~mach: Machine(),
  ~d: Led(mach),
  +s: Led.L(mach, d),
  +r: Run<Led.L(mach, d)>,
  +i: Ledgers.Id,
  +a: Hashes.Hash,
  +m: String,
  k: Maybe<&2, Maybe<&2, Ledgers.Id>>,
  +bd: Keep.Base(mach, d, s, r)
) -> Outs.Res(mach, d, s, i, Step.label.at(~mach, ~d, r, i, a, m, k)):
  match k:
    case None{}:
      Unit{}
    case Some{Some{x}}:
      Outs.stale(~mach, ~d, s, r, i, a, bd)
    case Some{None{}}:
      Shared.Bool.when_cases(
        Maybe<&2, Run<Led.L(mach, d)>>,
        z => Outs.Res(mach, d, s, i, z),
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
        e => Outs.stale(~mach, ~d, s, r, i, a, bd),
        e => Outs.labelled(
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
          ),
          bd
        )
      )

# a request for a label gives an outcome
def Outs.label(
  ~mach: Machine(),
  ~d: Led(mach),
  +s: Led.L(mach, d),
  +r: Run<Led.L(mach, d)>,
  +i: Ledgers.Id,
  +a: Hashes.Hash,
  +m: String,
  bd: Keep.Base(mach, d, s, r)
) -> Outs.Res(mach, d, s, i, Step.label(~mach, ~d, r, i, a, m)):
  Outs.label.at(
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
    ),
    bd
  )

# opening a sub line gives an outcome
def Outs.opens(
  ~mach: Machine(),
  ~d: Led(mach),
  +s: Led.L(mach, d),
  +r: Run<Led.L(mach, d)>,
  +i: Ledgers.Id,
  +a: Hashes.Hash,
  +b: String,
  +t: Tip,
  +ns: List<&2, List<&2, U32>>,
  +bd: Keep.Base(mach, d, s, r)
) -> Outs.Res(mach, d, s, i, Step.opens(~mach, ~d, r, i, a, b, t, ns)):
  +r0 = Run.over(~mach, ~d, r, Tip.code(t, []) <> ns, Tip.content(Run.tip(Led.L(mach, d), r)))
  Outs.bind(
    ~mach,
    ~d,
    s,
    i,
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
    bd,
    +r2 => bd2 => Outs.taken(~mach, ~d, s, r2, i, a, None{}, bd2)
  )

# an act of a kernel gives an outcome
def Outs.act(
  ~mach: Machine(),
  ~d: Led(mach),
  +s: Led.L(mach, d),
  +r: Run<Led.L(mach, d)>,
  +i: Ledgers.Id,
  +a: Hashes.Hash,
  m: Maybe<&2, Act>,
  +bd: Keep.Base(mach, d, s, r)
) -> Outs.Res(mach, d, s, i, Act.run(~mach, ~d, r, i, a, m)):
  match m:
    case None{}:
      Unit{}
    case Some{Act.Stale{}}:
      Outs.stale(~mach, ~d, s, r, i, a, bd)
    case Some{Act.Label{x}}:
      Outs.label(~mach, ~d, s, r, i, a, x, bd)
    case Some{Act.Taken{+vs, +h, +ns}}:
      Outs.taken(
        ~mach,
        ~d,
        s,
        Run.over(~mach, ~d, r, ns, h),
        i,
        a,
        vs,
        Keep.base(~mach, ~d, s, r, Run.over(~mach, ~d, r, ns, h), bd, Ext.over(~mach, ~d, s, r, ns, h))
      )
    case Some{Act.Opens{b, t, ns}}:
      Outs.opens(~mach, ~d, s, r, i, a, b, t, ns, bd)

# a request whose outcome the log holds keeps it, once its code is read (dm)
def Outs.found(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  +s: Led.L(mach, d),
  +r: Run<Led.L(mach, d)>,
  +c: Ledgers.Line,
  +i: Ledgers.Id,
  +a: Hashes.Hash,
  +q: Machine.Q(mach),
  +w: List<&2, U32>,
  dm: Maybe<&2, Out>,
  edm: {Codes.Code.whole.of(~Out, ~Out.code, ~Out.code.read, Some{w}) == dm: Maybe<&2, Out>},
  +em: {
    Tip.find(~mach, ~d, Run.ledger(Led.L(mach, d), r), Run.tip(Led.L(mach, d), r), Log.out(i))
      == Some{Some{w}}: Maybe<&2, Maybe<&2, List<&2, U32>>>
  },
  +bd: Keep.Base(mach, d, s, r)
) -> Outs.Res(mach, d, s, i, Step.fresh(~mach, ~d, ~kern, r, c, i, a, q, Some{dm})):
  match dm:
    case Some{x}:
      Tuple{
        w,
        Tuple{
          %Equal.sym(
            Maybe<&2, Out>,
            Codes.Code.whole.of(~Out, ~Out.code, ~Out.code.read, Some{w}),
            Some{x},
            edm
          ): {Maybe.is_some(&2, Out, _) == True{}: Bool}
          {==},
          +hh => Keep.found_back(
            Trees.Ops.look(Led.L(mach, d), Led.tree(mach, d))(s)(Tip.log(Run.tip(Led.L(mach, d), r)))(Log.out(i)),
            w,
            Hist.find(
              ~mach,
              ~d,
              Run.ledger(Led.L(mach, d), r),
              s,
              Tip.log(Run.tip(Led.L(mach, d), r)),
              Log.out(i),
              Some{w},
              Keep.base_grows(~mach, ~d, s, r, bd, hh)
            )(em)
          )
        }
      }
    case None{}:
      Outs.act(
        ~mach,
        ~d,
        s,
        r,
        i,
        a,
        Kernel.change(mach, d, kern)(Run.ledger(Led.L(mach, d), r))(Run.tip(Led.L(mach, d), r))(c)(i)(q),
        bd
      )

# a request gives an outcome, once the read of its outcome is known (fm)
def Outs.fresh(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  +s: Led.L(mach, d),
  +r: Run<Led.L(mach, d)>,
  +c: Ledgers.Line,
  +i: Ledgers.Id,
  +a: Hashes.Hash,
  +q: Machine.Q(mach),
  fm: Maybe<&2, Maybe<&2, List<&2, U32>>>,
  em: {
    Tip.find(~mach, ~d, Run.ledger(Led.L(mach, d), r), Run.tip(Led.L(mach, d), r), Log.out(i))
      == fm: Maybe<&2, Maybe<&2, List<&2, U32>>>
  },
  +bd: Keep.Base(mach, d, s, r)
) -> Outs.Res(mach, d, s, i, Step.fresh(~mach, ~d, ~kern, r, c, i, a, q, Tip.known(~Out, ~Out.code, ~Out.code.read, fm))):
  match fm:
    case None{}:
      Unit{}
    case Some{None{}}:
      Outs.act(
        ~mach,
        ~d,
        s,
        r,
        i,
        a,
        Kernel.change(mach, d, kern)(Run.ledger(Led.L(mach, d), r))(Run.tip(Led.L(mach, d), r))(c)(i)(q),
        bd
      )
    case Some{Some{+w}}:
      Outs.found(
        ~mach,
        ~d,
        ~kern,
        s,
        r,
        c,
        i,
        a,
        q,
        w,
        Codes.Code.whole.of(~Out, ~Out.code, ~Out.code.read, Some{w}),
        {==},
        em,
        bd
      )

# the request whose entry is known gives an outcome
def Outs.one(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  +s: Led.L(mach, d),
  +r: Run<Led.L(mach, d)>,
  +c: Ledgers.Line,
  +a: Hashes.Hash,
  +i: Ledgers.Id,
  +time: String,
  +q: Machine.Q(mach),
  eg: {
    Led.get(~mach, ~d, Run.ledger(Led.L(mach, d), r), Ledgers.Name.Ask{a})
      == Some{Ledgers.Entry.Ask{i, time, q}}: Maybe<&2, Entry(mach)>
  },
  +bd: Keep.Base(mach, d, s, r)
) -> Outs.Res(mach, d, s, i, Step.one(~mach, ~d, ~kern, r, c, a)):
  %Equal.sym(
    Maybe<&2, Entry(mach)>,
    Led.get(~mach, ~d, Run.ledger(Led.L(mach, d), r), Ledgers.Name.Ask{a}),
    Some{Ledgers.Entry.Ask{i, time, q}},
    eg
  ): Outs.Res(mach, d, s, i, Step.asked(~mach, ~d, ~kern, r, c, a, _))
  Outs.fresh(
    ~mach,
    ~d,
    ~kern,
    s,
    r,
    c,
    i,
    a,
    q,
    Tip.find(~mach, ~d, Run.ledger(Led.L(mach, d), r), Run.tip(Led.L(mach, d), r), Log.out(i)),
    {==},
    bd
  )

# before the request a runs: s reads the run m, and its ledger holds the
# entry of a
def Outs.Pre(
  -mach: Machine(),
  -d: Led(mach),
  -s: Led.L(mach, d),
  -a: Hashes.Hash,
  -e: Entry(mach),
  m: Maybe<&2, Run<Led.L(mach, d)>>
) -> Data:
  match m:
    case None{}:
      Unit
    case Some{r}:
      +Sigma<
        Keep.Base(mach, d, s, r),
        x => {Led.get(~mach, ~d, Run.ledger(Led.L(mach, d), r), Ledgers.Name.Ask{a}) == Some{e}: Maybe<&2, Entry(mach)>}>

# after the request of the ID i ran: s reads the run m, and its outcome
def Outs.All(
  -mach: Machine(),
  -d: Led(mach),
  -s: Led.L(mach, d),
  -i: Ledgers.Id,
  m: Maybe<&2, Run<Led.L(mach, d)>>
) -> Type:
  match m:
    case None{}:
      Unit
    case Some{r}:
      Keep.Base(mach, d, s, r) & Outs.Has(mach, d, s, i, r)

# the entry that the ledger of a run holds, a run that follows it holds
def Outs.get_gain(
  ~mach: Machine(),
  ~d: Led(mach),
  -s: Led.L(mach, d),
  +a: Hashes.Hash,
  +e: Entry(mach),
  +r: Run<Led.L(mach, d)>,
  -r2: Run<Led.L(mach, d)>,
  g: Ext.Gain(mach, d, s, r, r2),
  eg: {Led.get(~mach, ~d, Run.ledger(Led.L(mach, d), r), Ledgers.Name.Ask{a}) == Some{e}: Maybe<&2, Entry(mach)>}
) -> {Led.get(~mach, ~d, Run.ledger(Led.L(mach, d), r2), Ledgers.Name.Ask{a}) == Some{e}: Maybe<&2, Entry(mach)>}:
  match g:
    case Tuple{ys, Tuple{+zs, Tuple{a1, Tuple{l1, h1}}}}:
      %Equal.sym(
        Led.L(mach, d),
        Run.ledger(Led.L(mach, d), r2),
        Led.puts(~mach, ~d, zs, Run.ledger(Led.L(mach, d), r)),
        l1
      ): {Led.get(~mach, ~d, _, Ledgers.Name.Ask{a}) == Some{e}: Maybe<&2, Entry(mach)>}
      Hist.gets(
        ~mach,
        ~d,
        Run.ledger(Led.L(mach, d), r),
        Led.puts(~mach, ~d, zs, Run.ledger(Led.L(mach, d), r)),
        Hist.puts(~mach, ~d, zs, Run.ledger(Led.L(mach, d), r))
      )(Ledgers.Name.Ask{a})(e)(eg)

# Outs.Pre of a run m2 that follows r
def Outs.pre_pair(
  ~mach: Machine(),
  ~d: Led(mach),
  +s: Led.L(mach, d),
  +a: Hashes.Hash,
  +e: Entry(mach),
  +r: Run<Led.L(mach, d)>,
  m2: Maybe<&2, Run<Led.L(mach, d)>>,
  +gm: Ext.GainM(mach, d, s, r, m2),
  +bd: Keep.Base(mach, d, s, r),
  +eg: {Led.get(~mach, ~d, Run.ledger(Led.L(mach, d), r), Ledgers.Name.Ask{a}) == Some{e}: Maybe<&2, Entry(mach)>}
) -> Outs.Pre(mach, d, s, a, e, m2):
  match m2:
    case None{}:
      Unit{}
    case Some{+r2}:
      Tuple{Keep.base(~mach, ~d, s, r, r2, bd, gm), Outs.get_gain(~mach, ~d, s, a, e, r, r2, gm, eg)}

# Outs.Pre after one more request
def Outs.pre_step(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  +s: Led.L(mach, d),
  +a: Hashes.Hash,
  +e: Entry(mach),
  +c: Ledgers.Line,
  +q: Hashes.Hash,
  m: Maybe<&2, Run<Led.L(mach, d)>>,
  st: Outs.Pre(mach, d, s, a, e, m)
) -> Outs.Pre(
  mach,
  d,
  s,
  a,
  e,
  Maybe.bind(&2, Run<Led.L(mach, d)>, Run<Led.L(mach, d)>, m, x => Step.one(~mach, ~d, ~kern, x, c, q))
):
  match m:
    case None{}:
      Unit{}
    case Some{+r}:
      match st:
        case Tuple{+bd, +eg}:
          Outs.pre_pair(
            ~mach,
            ~d,
            s,
            a,
            e,
            r,
            Step.one(~mach, ~d, ~kern, r, c, q),
            Ext.one(~mach, ~d, ~kern, s, r, c, q),
            bd,
            eg
          )

# Outs.All of a run m2 that follows r
def Outs.mid_pair(
  ~mach: Machine(),
  ~d: Led(mach),
  +s: Led.L(mach, d),
  -i: Ledgers.Id,
  +r: Run<Led.L(mach, d)>,
  m2: Maybe<&2, Run<Led.L(mach, d)>>,
  res: Outs.Res(mach, d, s, i, m2),
  gm: Ext.GainM(mach, d, s, r, m2),
  bd: Keep.Base(mach, d, s, r)
) -> Outs.All(mach, d, s, i, m2):
  match m2:
    case None{}:
      Unit{}
    case Some{+r2}:
      Tuple{Keep.base(~mach, ~d, s, r, r2, bd, gm), res}

# the request a gives its outcome
def Outs.mid(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  +s: Led.L(mach, d),
  +a: Hashes.Hash,
  +i: Ledgers.Id,
  +time: String,
  +q: Machine.Q(mach),
  +c: Ledgers.Line,
  m: Maybe<&2, Run<Led.L(mach, d)>>,
  st: Outs.Pre(mach, d, s, a, Ledgers.Entry.Ask{i, time, q}, m)
) -> Outs.All(
  mach,
  d,
  s,
  i,
  Maybe.bind(&2, Run<Led.L(mach, d)>, Run<Led.L(mach, d)>, m, x => Step.one(~mach, ~d, ~kern, x, c, a))
):
  match m:
    case None{}:
      Unit{}
    case Some{+r}:
      match st:
        case Tuple{+bd, eg}:
          Outs.mid_pair(
            ~mach,
            ~d,
            s,
            i,
            r,
            Step.one(~mach, ~d, ~kern, r, c, a),
            Outs.one(~mach, ~d, ~kern, s, r, c, a, i, time, q, eg, bd),
            Ext.one(~mach, ~d, ~kern, s, r, c, a),
            bd
          )

# the outcome stays through the rest of the requests
def Outs.post(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  +s: Led.L(mach, d),
  +i: Ledgers.Id,
  +a: Hashes.Hash,
  +c: Ledgers.Line,
  +rest: List<&2, Hashes.Hash>,
  m: Maybe<&2, Run<Led.L(mach, d)>>,
  st: Outs.All(mach, d, s, i, m)
) -> Outs.Res(mach, d, s, i, Step.all(~mach, ~d, ~kern, c, rest, m)):
  match m:
    case None{}:
      Outs.of_keep(
        mach,
        d,
        s,
        i,
        Out.code(Out.Stale{a}, []),
        Outs.code(Out.Stale{a}),
        Step.all(~mach, ~d, ~kern, c, rest, None{}),
        Keep.all(~mach, ~d, ~kern, s, Log.out(i), Out.code(Out.Stale{a}, []), c, rest, None{}, Unit{})
      )
    case Some{+r1}:
      match st:
        case Tuple{+bd, oh}:
          match oh:
            case Tuple{+v, Tuple{dv, kh}}:
              Outs.of_keep(
                mach,
                d,
                s,
                i,
                v,
                dv,
                Step.all(~mach, ~d, ~kern, c, rest, Some{r1}),
                Keep.all(~mach, ~d, ~kern, s, Log.out(i), v, c, rest, Some{r1}, Tuple{bd, kh})
              )

# a step whose requests include a gives a its outcome
def Outs.all(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  +s: Led.L(mach, d),
  +a: Hashes.Hash,
  +i: Ledgers.Id,
  +time: String,
  +q: Machine.Q(mach),
  +c: Ledgers.Line,
  qs: List<&2, Hashes.Hash>,
  +m: Maybe<&2, Run<Led.L(mach, d)>>,
  +st: Outs.Pre(mach, d, s, a, Ledgers.Entry.Ask{i, time, q}, m)
) -> {List.contains(~Hashes.Hash, ~Hashes.Hash.is_eq, qs, a) == True{}: Bool}
  -> Outs.Res(mach, d, s, i, Step.all(~mach, ~d, ~kern, c, qs, m)):
  match qs:
    case Nil{}:
      h => Empty.absurd(Outs.Res(mach, d, s, i, Step.all(~mach, ~d, ~kern, c, [], m)), Shared.Bool.false_ne_true(h))
    case Con{+x, +rest}:
      h => Ext.any_cases(
        Hashes.Hash.is_eq(x, a),
        u => List.contains(~Hashes.Hash, ~Hashes.Hash.is_eq, rest, a),
        Outs.Res(mach, d, s, i, Step.all(~mach, ~d, ~kern, c, x <> rest, m)),
        hx =>
          %Equal.sym(Hashes.Hash, x, a, Hashes.Hash.is_eq_sound(x, a)(hx)): Outs.Res(
            mach,
            d,
            s,
            i,
            Step.all(
              ~mach,
              ~d,
              ~kern,
              c,
              rest,
              Maybe.bind(&2, Run<Led.L(mach, d)>, Run<Led.L(mach, d)>, m, y => Step.one(~mach, ~d, ~kern, y, c, _))
            )
          )
          Outs.post(
            ~mach,
            ~d,
            ~kern,
            s,
            i,
            a,
            c,
            rest,
            Maybe.bind(&2, Run<Led.L(mach, d)>, Run<Led.L(mach, d)>, m, y => Step.one(~mach, ~d, ~kern, y, c, a)),
            Outs.mid(~mach, ~d, ~kern, s, a, i, time, q, c, m, st)
          ),
        hr => Outs.all(
          ~mach,
          ~d,
          ~kern,
          s,
          a,
          i,
          time,
          q,
          c,
          rest,
          Maybe.bind(&2, Run<Led.L(mach, d)>, Run<Led.L(mach, d)>, m, y => Step.one(~mach, ~d, ~kern, y, c, x)),
          Outs.pre_step(~mach, ~d, ~kern, s, a, Ledgers.Entry.Ask{i, time, q}, c, x, m, st)
        )(hr),
        h
      )

# the outcome that the log of a run reads, once s holds what it added
def Outs.final.has(
  ~mach: Machine(),
  ~d: Led(mach),
  +s: Led.L(mach, d),
  +i: Ledgers.Id,
  +r: Run<Led.L(mach, d)>,
  res: Outs.Has(mach, d, s, i, r)
) -> {Ext.holds(~mach, ~d, s, Run.added(Led.L(mach, d), r)) == True{}: Bool}
  -> {Maybe.is_some(&2, Out, Tip.out(~mach, ~d, s, Run.tip(Led.L(mach, d), r), i)) == True{}: Bool}:
  match res:
    case Tuple{+v, Tuple{dv, kh}}:
      hh =>
        %Equal.sym(
          Maybe<&2, List<&2, U32>>,
          Tip.get(~mach, ~d, s, Run.tip(Led.L(mach, d), r), Log.out(i)),
          Some{v},
          kh(hh)
        ): {Maybe.is_some(&2, Out, Codes.Code.whole.of(~Out, ~Out.code, ~Out.code.read, _)) == True{}: Bool}
        dv

# the outcome of the run that a step gave
def Outs.final(
  ~mach: Machine(),
  ~d: Led(mach),
  +s: Led.L(mach, d),
  +i: Ledgers.Id,
  m: Maybe<&2, Run<Led.L(mach, d)>>,
  +r: Run<Led.L(mach, d)>,
  res: Outs.Res(mach, d, s, i, m)
) -> {m == Some{r}: Maybe<&2, Run<Led.L(mach, d)>>}
  -> {Ext.holds(~mach, ~d, s, Run.added(Led.L(mach, d), r)) == True{}: Bool}
  -> {Maybe.is_some(&2, Out, Tip.out(~mach, ~d, s, Run.tip(Led.L(mach, d), r), i)) == True{}: Bool}:
  match m:
    case None{}:
      e => Empty.absurd(
        {Ext.holds(~mach, ~d, s, Run.added(Led.L(mach, d), r)) == True{}: Bool}
          -> {Maybe.is_some(&2, Out, Tip.out(~mach, ~d, s, Run.tip(Led.L(mach, d), r), i)) == True{}: Bool},
        Shared.Maybe.none_ne_some(Run<Led.L(mach, d)>, r, e)
      )
    case Some{+r2}:
      e =>
        %Shared.Maybe.some_inj(Run<Led.L(mach, d)>, r2, r, e): {
          Ext.holds(~mach, ~d, s, Run.added(Led.L(mach, d), _)) == True{}: Bool
        }
          -> {Maybe.is_some(&2, Out, Tip.out(~mach, ~d, s, Run.tip(Led.L(mach, d), _), i)) == True{}: Bool}
        Outs.final.has(~mach, ~d, s, i, r2, res)

# the start of a run that ends at r2, which the ledger of r reads, when r2 is r
def Outs.base0.of(
  -mach: Machine(),
  -d: Led(mach),
  +l: Led.L(mach, d),
  -t: Tip,
  r2: Run<Led.L(mach, d)>,
  -r: Run<Led.L(mach, d)>,
  g: Ext.Gain(mach, d, Run.ledger(Led.L(mach, d), r), Run{l, t, []}, r2),
  er: {r2 == r: Run<Led.L(mach, d)>}
) -> Keep.Base(mach, d, Run.ledger(Led.L(mach, d), r), Run{l, t, []}):
  match g:
    case Tuple{ys, Tuple{+zs, Tuple{a1, Tuple{l1, h1}}}}:
      Tuple{
        [],
        Tuple{
          l,
          Tuple{
            zs,
            Tuple{
              {==},
              Tuple{
                Equal.trans(
                  Led.L(mach, d),
                  Run.ledger(Led.L(mach, d), r),
                  Run.ledger(Led.L(mach, d), r2),
                  Led.puts(~mach, ~d, zs, l),
                  Equal.cong(
                    Run<Led.L(mach, d)>,
                    Led.L(mach, d),
                    z => Run.ledger(Led.L(mach, d), z),
                    r,
                    r2,
                    Equal.sym(Run<Led.L(mach, d)>, r2, r, er)
                  ),
                  l1
                ),
                {==}
              }
            }
          }
        }
      }

# the start of a run that ends at r, which the ledger of r reads, once the
# run is known (m)
def Outs.base0(
  -mach: Machine(),
  -d: Led(mach),
  +l: Led.L(mach, d),
  +t: Tip,
  m: Maybe<&2, Run<Led.L(mach, d)>>,
  -r: Run<Led.L(mach, d)>,
  gm: Ext.GainM(mach, d, Run.ledger(Led.L(mach, d), r), Run{l, t, []}, m)
) -> {m == Some{r}: Maybe<&2, Run<Led.L(mach, d)>>}
  -> Keep.Base(mach, d, Run.ledger(Led.L(mach, d), r), Run{l, t, []}):
  match m:
    case None{}:
      e => Empty.absurd(
        Keep.Base(mach, d, Run.ledger(Led.L(mach, d), r), Run{l, t, []}),
        Shared.Maybe.none_ne_some(Run<Led.L(mach, d)>, r, e)
      )
    case Some{+r2}:
      e => Outs.base0.of(mach, d, l, t, r2, r, gm, Shared.Maybe.some_inj(Run<Led.L(mach, d)>, r2, r, e))

# Step.run_outs, with its premises
def Outs.go(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  +l: Led.L(mach, d),
  +c: Ledgers.Line,
  +t: Tip,
  +qs: List<&2, Hashes.Hash>,
  +r: Run<Led.L(mach, d)>,
  +a: Hashes.Hash,
  +i: Ledgers.Id,
  +time: String,
  +q: Machine.Q(mach),
  +e: {Step.run(~mach, ~d, ~kern, l, c, t, qs) == Some{r}: Maybe<&2, Run<Led.L(mach, d)>>},
  hh: {Ext.holds(~mach, ~d, Run.ledger(Led.L(mach, d), r), Run.added(Led.L(mach, d), r)) == True{}: Bool},
  hc: {List.contains(~Hashes.Hash, ~Hashes.Hash.is_eq, qs, a) == True{}: Bool},
  eg: {Led.get(~mach, ~d, l, Ledgers.Name.Ask{a}) == Some{Ledgers.Entry.Ask{i, time, q}}: Maybe<&2, Entry(mach)>}
) -> {
  Maybe.is_some(&2, Out, Tip.out(~mach, ~d, Run.ledger(Led.L(mach, d), r), Run.tip(Led.L(mach, d), r), i)) == True{}: Bool
}:
  +s = Run.ledger(Led.L(mach, d), r)
  Outs.final(
    ~mach,
    ~d,
    s,
    i,
    Step.run(~mach, ~d, ~kern, l, c, t, qs),
    r,
    Outs.all(
      ~mach,
      ~d,
      ~kern,
      s,
      a,
      i,
      time,
      q,
      c,
      qs,
      Some{Run{l, t, []}},
      Tuple{
        Outs.base0(
          mach,
          d,
          l,
          t,
          Step.run(~mach, ~d, ~kern, l, c, t, qs),
          r,
          Ext.all(~mach, ~d, ~kern, s, Run{l, t, []}, c, qs, Some{Run{l, t, []}}, Ext.refl(mach, d, s, Run{l, t, []}))
        )(e),
        eg
      }
    )(hc)
  )(e)(hh)

# a step gives each of its requests an outcome: after a run whose ledger
# holds each node that it added (as a landed step's does), the log holds an
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
    -> {
      Depots.Depot.holds(
        ~Led.L(mach, d),
        ~(s => h => Led.fetch(~mach, ~d, s, h)),
        Run.ledger(Led.L(mach, d), r),
        Run.added(Led.L(mach, d), r)
      )
        == True{}: Bool
    }
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

def Step.run_outs(mach, d, kern, l, c, t, qs, r, a, i, time, q):
  e => hh => hc => eg => Outs.go(~mach, ~d, ~kern, l, c, t, qs, r, a, i, time, q, e, hh, hc, eg)

# A replica
# =========
# The replica that this module runs: a way to hold a ledger and act on it
# (Replica.Kind). It takes in an entry only when the entry checks (Entry.Checks,
# by a test), votes as the rules of rounds say, and keeps the count of its
# ballots before a ballot leaves it.

# Checks
# ------
# Each claim about an entry that a replica takes in is a test here, so the
# replica can make it, and a law says that the test proves the claim.

# the ballots of the voter at the place w, in l
def Led.ballots.at(~mach: Machine(), ~d: Led(mach), l: Led.L(mach, d), w: Ledgers.Place, voter: String) -> List<&2, Ledgers.Ballot>:
  Ledgers.Kind.ballots(Machine.Q(mach), Led.kind(mach, d))(l)(w)(voter)

# one of the ballots bs names the key k as the next of its chain, which seals b
def Ballots.link(bs: List<&2, Ledgers.Ballot>, +b: Ledgers.Ballot) -> Bool:
  match bs:
    case Nil{}:
      False{}
    case Con{b0, rest}:
      Bool.or(Ledgers.Ballot.sealed(Ballot.next(b0), b), Ballots.link(rest, b))

# the key m seals the ballot b
def Key.seals(m: Maybe<&2, Hashes.Hash>, b: Ledgers.Ballot) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{k}:
      Ledgers.Ballot.sealed(k, b)

# what go says of the tip m (False: none)
def Tip.on(m: Maybe<&2, Tip>, go: Tip -> Bool) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{t}:
      go(t)

# a tip of the root line c, from the tip t at the height h on, at most f steps
# on, gives the voter a key that seals b (Root.Gives, by a walk)
def Root.seals.go(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  f: Nat,
  +l: Led.L(mach, d),
  +c: Ledgers.Line,
  +h: U32,
  +t: Tip,
  +voter: String,
  +b: Ledgers.Ballot
) -> Bool:
  match f:
    case 0n:
      Key.seals(Tip.key(~mach, ~d, l, Some{t}, voter), b)
    case 1n+p:
      Bool.or(
        Key.seals(Tip.key(~mach, ~d, l, Some{t}, voter), b),
        Tip.on(Line.next(~mach, ~d, ~kern, l, c, h, t), t2 => Root.seals.go(~mach, ~d, ~kern, p, l, c, U32.inc(h), t2, voter, b))
      )

# the root line of the root r
def Root.line(r: Hashes.Hash) -> Ledgers.Line:
  Ledgers.Line{r, None{}}

# the first ballot b of its voter under its root is sealed by a first key that
# the root line gives the voter: the request that starts the line, or the
# content of a tip of the line (Root.Gives). The walk of the line costs its
# height, once for each first ballot of a voter
def Ballot.first_ok(~mach: Machine(), ~d: Led(mach), ~kern: Kernel(mach, d), +l: Led.L(mach, d), +b: Ledgers.Ballot) -> Bool:
  +r = Ledgers.Ballot.root(b)
  +c = Root.line(r)
  Bool.or(
    Key.seals(Root.key.at(~mach, Led.get(~mach, ~d, l, Ledgers.Name.Ask{r}), Ledgers.Ballot.voter(b)), b),
    Maybe.default(
      &2,
      Bool,
      Maybe.map(
        &2,
        Tip,
        Bool,
        t => Root.seals.go(
          ~mach,
          ~d,
          ~kern,
          Ledgers.Kind.heights(Machine.Q(mach), Led.kind(mach, d))(l)(c),
          l,
          c,
          0,
          t,
          Ledgers.Ballot.voter(b),
          b
        ),
        Line.start(~mach, ~d, ~kern, l, c)
      ),
      False{}
    )
  )

# the ballot b is linked in l (Ballot.Linked), when the ballot before it is at
# p: the ballot there, which l holds, names the key that seals it; or it is
# the first, and a first key of its voter seals it
def Ballot.linked.at(~mach: Machine(), ~d: Led(mach), ~kern: Kernel(mach, d), +l: Led.L(mach, d), +b: Ledgers.Ballot, p: Maybe<&2, Ledgers.Place>) -> Bool:
  match p:
    case None{}:
      Ballot.first_ok(~mach, ~d, ~kern, l, b)
    case Some{w}:
      Ballots.link(Led.ballots.at(~mach, ~d, l, w, Ledgers.Ballot.voter(b)), b)

# the ballot b is linked in l, by the place of the ballot before it
def Ballot.linked(~mach: Machine(), ~d: Led(mach), ~kern: Kernel(mach, d), +l: Led.L(mach, d), +b: Ledgers.Ballot) -> Bool:
  Ballot.linked.at(~mach, ~d, ~kern, l, b, Ledgers.Ballot.prev(b))

# the lie x is a proof (Lie.Proves): its key seals its two ballots, which are
# not the same
def Lie.proves(x: Ledgers.Lie) -> Bool:
  match x:
    case Ledgers.Lie{+k, +a, +b}:
      Bool.and(
        Bool.and(Ledgers.Ballot.sealed(k, a), Ledgers.Ballot.sealed(k, b)),
        Bool.not(Ledgers.Ballot.is_eq(a, b))
      )

# the entry e checks in l (Entry.Checks): a request and data do; a ballot does
# when l with it is honest and the ballot is linked; a proof of a lie does
# when it proves
def Entry.checks(~mach: Machine(), ~d: Led(mach), ~kern: Kernel(mach, d), +l: Led.L(mach, d), +e: Entry(mach)) -> Bool:
  match e:
    case Ledgers.Entry.Ask{i, t, q}:
      True{}
    case Ledgers.Entry.Data{ws}:
      True{}
    case Ledgers.Entry.Ballot{+b}:
      +l2 = Led.add(~mach, ~d, l, Ledgers.Entry.Ballot{b})
      Bool.and(Led.honest(~mach, ~d, l2), Ballot.linked(~mach, ~d, ~kern, l2, b))
    case Ledgers.Entry.Lie{x}:
      Lie.proves(x)

# Proofs of checks
# ----------------

# two ballots that Ballot.is_eq calls different are different
def Chk.ne(+a: Ledgers.Ballot, -b: Ledgers.Ballot, hf: {Ledgers.Ballot.is_eq(a, b) == False{}: Bool}) -> {a != b: Ledgers.Ballot}:
  e => Shared.Bool.true_ne_false(
    Equal.trans(
      Bool,
      True{},
      Ledgers.Ballot.is_eq(a, a),
      False{},
      Equal.sym(Bool, Ledgers.Ballot.is_eq(a, a), True{}, Ledgers.Ballot.is_eq_refl(a)),
      Equal.trans(
        Bool,
        Ledgers.Ballot.is_eq(a, a),
        Ledgers.Ballot.is_eq(a, b),
        False{},
        Equal.cong(Ledgers.Ballot, Bool, z => Ledgers.Ballot.is_eq(a, z), a, b, e),
        hf
      )
    )
  )

# Lie.proves_sound, by the parts of the lie
def Chk.lie(x: Ledgers.Lie) -> {Lie.proves(x) == True{}: Bool} -> Lie.Proves(x):
  match x:
    case Ledgers.Lie{+k, +a, +b}:
      +h =>
        +s = Shared.Bool.and_true_left(
          Bool.and(Ledgers.Ballot.sealed(k, a), Ledgers.Ballot.sealed(k, b)),
          Bool.not(Ledgers.Ballot.is_eq(a, b))
        )(h)
        Tuple{
          Shared.Bool.and_true_left(Ledgers.Ballot.sealed(k, a), Ledgers.Ballot.sealed(k, b))(s),
          Tuple{
            Shared.Bool.and_true_right(Ledgers.Ballot.sealed(k, a), Ledgers.Ballot.sealed(k, b))(s),
            Chk.ne(
              a,
              b,
              Shared.Bool.not_true(
                Ledgers.Ballot.is_eq(a, b)
              )(
                Shared.Bool.and_true_right(
                  Bool.and(Ledgers.Ballot.sealed(k, a), Ledgers.Ballot.sealed(k, b)),
                  Bool.not(Ledgers.Ballot.is_eq(a, b))
                )(h)
              )
            )
          }
        }

# the key of a request, once the entry is known (m): it stays as the ledger grows
def Chk.key_at(
  ~mach: Machine(),
  m: Maybe<&2, Entry(mach)>,
  -m2: Maybe<&2, Entry(mach)>,
  hm: @e: Entry(mach) -> {m == Some{e}: Maybe<&2, Entry(mach)>} -> {m2 == Some{e}: Maybe<&2, Entry(mach)>},
  voter: String,
  -k: Hashes.Hash
) -> {Root.key.at(~mach, m, voter) == Some{k}: Maybe<&2, Hashes.Hash>}
  -> {Root.key.at(~mach, m2, voter) == Some{k}: Maybe<&2, Hashes.Hash>}:
  match m:
    case None{}:
      e => Empty.absurd(
        {Root.key.at(~mach, m2, voter) == Some{k}: Maybe<&2, Hashes.Hash>},
        Shared.Maybe.none_ne_some(Hashes.Hash, k, e)
      )
    case Some{y}:
      e =>
        %Equal.sym(Maybe<&2, Entry(mach)>, m2, Some{y}, hm(y)({==})): {
          Root.key.at(~mach, _, voter) == Some{k}: Maybe<&2, Hashes.Hash>
        }
        e

# a key that some data is stays, once the data is known (m)
def Chk.whole(
  m: Maybe<&2, List<&2, U32>>,
  -m2: Maybe<&2, List<&2, U32>>,
  hm: @w: List<&2, U32> -> {m == Some{w}: Maybe<&2, List<&2, U32>>} -> {m2 == Some{w}: Maybe<&2, List<&2, U32>>},
  -k: Hashes.Hash
) -> {Codes.Code.whole.of(~Hashes.Hash, ~Hashes.Hash.code, ~Hashes.Hash.code.read, m) == Some{k}: Maybe<&2, Hashes.Hash>}
  -> {Codes.Code.whole.of(~Hashes.Hash, ~Hashes.Hash.code, ~Hashes.Hash.code.read, m2) == Some{k}: Maybe<&2, Hashes.Hash>}:
  match m:
    case None{}:
      e => Empty.absurd(
        {Codes.Code.whole.of(~Hashes.Hash, ~Hashes.Hash.code, ~Hashes.Hash.code.read, m2) == Some{k}: Maybe<&2, Hashes.Hash>},
        Shared.Maybe.none_ne_some(Hashes.Hash, k, e)
      )
    case Some{y}:
      e =>
        %Equal.sym(Maybe<&2, List<&2, U32>>, m2, Some{y}, hm(y)({==})): {
          Codes.Code.whole.of(~Hashes.Hash, ~Hashes.Hash.code, ~Hashes.Hash.code.read, _) == Some{k}: Maybe<&2, Hashes.Hash>
        }
        e

# the key that a tip gives a voter stays as the ledger grows, once the tip is
# known (m)
def Chk.tip_key(
  ~mach: Machine(),
  ~d: Led(mach),
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  +g: Led.Grows(mach, d, a, b),
  m: Maybe<&2, Tip>,
  -m2: Maybe<&2, Tip>,
  hm: @t: Tip -> {m == Some{t}: Maybe<&2, Tip>} -> {m2 == Some{t}: Maybe<&2, Tip>},
  +voter: String,
  -k: Hashes.Hash
) -> {Tip.key(~mach, ~d, a, m, voter) == Some{k}: Maybe<&2, Hashes.Hash>}
  -> {Tip.key(~mach, ~d, b, m2, voter) == Some{k}: Maybe<&2, Hashes.Hash>}:
  match m:
    case None{}:
      e => Empty.absurd(
        {Tip.key(~mach, ~d, b, m2, voter) == Some{k}: Maybe<&2, Hashes.Hash>},
        Shared.Maybe.none_ne_some(Hashes.Hash, k, e)
      )
    case Some{+t}:
      e =>
        %Equal.sym(Maybe<&2, Tip>, m2, Some{t}, hm(t)({==})): {
          Tip.key(~mach, ~d, b, _, voter) == Some{k}: Maybe<&2, Hashes.Hash>
        }
        Chk.whole(
          Tree.get(~mach, ~d, a, Tip.content(t), Machine.seal(mach)(voter)),
          Tree.get(~mach, ~d, b, Tip.content(t), Machine.seal(mach)(voter)),
          +w => ew => Hist.value(
            Tree.look(~mach, ~d, a, Tip.content(t), Machine.seal(mach)(voter)),
            Tree.look(~mach, ~d, b, Tip.content(t), Machine.seal(mach)(voter)),
            w,
            Hist.find(~mach, ~d, a, b, Tip.content(t), Machine.seal(mach)(voter), Some{w}, g)
          )(ew),
          k
        )(e)

# a first key that a root line gives stays in a later ledger
def Chk.gives(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  +later: Led.Later(~mach, ~d, a, b),
  +r: Hashes.Hash,
  +voter: String,
  -k: Hashes.Hash,
  gv: Root.Gives(mach, d, kern, a, r, voter, k)
) -> Root.Gives(mach, d, kern, b, r, voter, k):
  match gv:
    case Inl{e}:
      Inl{
        Chk.key_at(
          ~mach,
          Led.get(~mach, ~d, a, Ledgers.Name.Ask{r}),
          Led.get(~mach, ~d, b, Ledgers.Name.Ask{r}),
          y => Hist.gets(~mach, ~d, a, b, Led.later_grows(~mach, ~d, a, b)(later))(Ledgers.Name.Ask{r})(y),
          voter,
          k
        )(e)
      }
    case Inr{Tuple{+n, e}}:
      Inr{
        Tuple{
          n,
          Chk.tip_key(
            ~mach,
            ~d,
            a,
            b,
            Led.later_grows(~mach, ~d, a, b)(later),
            Line.at(~mach, ~d, ~kern, n, a, Ledgers.Line{r, None{}}),
            Line.at(~mach, ~d, ~kern, n, b, Ledgers.Line{r, None{}}),
            t => et => Line.at_grows(~mach, ~d, ~kern, n, Ledgers.Line{r, None{}})(a)(b)(t)(later)(et),
            voter,
            k
          )(e)
        }
      }

# a link of a ballot stays in a later ledger
def Chk.link_grows(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  +a: Led.L(mach, d),
  +b: Led.L(mach, d),
  +later: Led.Later(~mach, ~d, a, b),
  +x: Ledgers.Ballot,
  p: Maybe<&2, Ledgers.Place>,
  lk: Ballot.Linked(mach, d, kern, a, x, p)
) -> Ballot.Linked(mach, d, kern, b, x, p):
  match p:
    case None{}:
      match lk:
        case Tuple{+k, Tuple{sk, gv}}:
          Tuple{
            k,
            Tuple{sk, Chk.gives(~mach, ~d, ~kern, a, b, later, Ledgers.Ballot.root(x), Ledgers.Ballot.voter(x), k, gv)}
          }
    case Some{w}:
      match lk:
        case Tuple{+b0, Tuple{hb, rest}}:
          Tuple{
            b0,
            Tuple{
              Hist.has_grows(~mach, ~d, a, b, Ledgers.Entry.Ballot{b0}, Led.later_grows(~mach, ~d, a, b)(later))(hb),
              rest
            }
          }

# a key that seals a ballot, when there is one
def Chk.seals(m: Maybe<&2, Hashes.Hash>, +b: Ledgers.Ballot) -> {Key.seals(m, b) == True{}: Bool} -> Exists(
  Hashes.Hash,
  k => {m == Some{k}: Maybe<&2, Hashes.Hash>} & {Ledgers.Ballot.sealed(k, b) == True{}: Bool}
):
  match m:
    case None{}:
      h => Empty.absurd(
        Exists(Hashes.Hash, k => {None{} == Some{k}: Maybe<&2, Hashes.Hash>} & {Ledgers.Ballot.sealed(k, b) == True{}: Bool}),
        Shared.Bool.false_ne_true(h)
      )
    case Some{+k}:
      h => Tuple{k, Tuple{{==}, h}}

# a ballot is in a list that it starts
def Chk.contains_self(+b0: Ledgers.Ballot, rest: List<&2, Ledgers.Ballot>) -> {
  List.contains(~Ledgers.Ballot, ~Ledgers.Ballot.is_eq, b0 <> rest, b0) == True{}: Bool
}:
  %Equal.sym(Bool, Ledgers.Ballot.is_eq(b0, b0), True{}, Ledgers.Ballot.is_eq_refl(b0)): {
    List.any.if(u => List.contains(~Ledgers.Ballot, ~Ledgers.Ballot.is_eq, rest, b0), _) == True{}: Bool
  }
  {==}

# a ballot of rest that names the key that seals b is one of b0 <> rest
def Chk.link_cons(
  +b0: Ledgers.Ballot,
  +rest: List<&2, Ledgers.Ballot>,
  -b: Ledgers.Ballot,
  ex: Exists(
    Ledgers.Ballot,
    x => {
      List.contains(~Ledgers.Ballot, ~Ledgers.Ballot.is_eq, rest, x) == True{}: Bool
    }
      & {Ledgers.Ballot.sealed(Ballot.next(x), b) == True{}: Bool}
  )
) -> Exists(
  Ledgers.Ballot,
  x => {
    List.contains(~Ledgers.Ballot, ~Ledgers.Ballot.is_eq, b0 <> rest, x) == True{}: Bool
  }
    & {Ledgers.Ballot.sealed(Ballot.next(x), b) == True{}: Bool}
):
  match ex:
    case Tuple{+x, Tuple{hc, hs}}:
      Tuple{x, Tuple{Shared.List.contains_cons(~Ledgers.Ballot, ~Ledgers.Ballot.is_eq, b0, rest, x)(hc), hs}}

# Chk.link_find once whether the first ballot names the key is known (s)
def Chk.link_find.at(
  +b0: Ledgers.Ballot,
  +rest: List<&2, Ledgers.Ballot>,
  +b: Ledgers.Ballot,
  s: Bool,
  es: {Ledgers.Ballot.sealed(Ballot.next(b0), b) == s: Bool},
  h: {Bool.or(Ledgers.Ballot.sealed(Ballot.next(b0), b), Ballots.link(rest, b)) == True{}: Bool},
  ih: {Ballots.link(rest, b) == True{}: Bool} -> Exists(
    Ledgers.Ballot,
    x => {
      List.contains(~Ledgers.Ballot, ~Ledgers.Ballot.is_eq, rest, x) == True{}: Bool
    }
      & {Ledgers.Ballot.sealed(Ballot.next(x), b) == True{}: Bool}
  )
) -> Exists(
  Ledgers.Ballot,
  x => {
    List.contains(~Ledgers.Ballot, ~Ledgers.Ballot.is_eq, b0 <> rest, x) == True{}: Bool
  }
    & {Ledgers.Ballot.sealed(Ballot.next(x), b) == True{}: Bool}
):
  match s:
    case True{}:
      Tuple{b0, Tuple{Chk.contains_self(b0, rest), es}}
    case False{}:
      Chk.link_cons(
        b0,
        rest,
        b,
        ih(
          Equal.trans(
            Bool,
            Ballots.link(rest, b),
            Bool.or(Ledgers.Ballot.sealed(Ballot.next(b0), b), Ballots.link(rest, b)),
            True{},
            Equal.sym(
              Bool,
              Bool.or(Ledgers.Ballot.sealed(Ballot.next(b0), b), Ballots.link(rest, b)),
              Ballots.link(rest, b),
              Equal.cong(Bool, Bool, z => Bool.or(z, Ballots.link(rest, b)), Ledgers.Ballot.sealed(Ballot.next(b0), b), False{}, es)
            ),
            h
          )
        )
      )

# a ballot of the list that names the key that seals b
def Chk.link_find(xs: List<&2, Ledgers.Ballot>, +b: Ledgers.Ballot) -> {Ballots.link(xs, b) == True{}: Bool} -> Exists(
  Ledgers.Ballot,
  x => {
    List.contains(~Ledgers.Ballot, ~Ledgers.Ballot.is_eq, xs, x) == True{}: Bool
  }
    & {Ledgers.Ballot.sealed(Ballot.next(x), b) == True{}: Bool}
):
  match xs:
    case Nil{}:
      h => Empty.absurd(
        Exists(
          Ledgers.Ballot,
          x => {
            List.contains(~Ledgers.Ballot, ~Ledgers.Ballot.is_eq, [], x) == True{}: Bool
          }
            & {Ledgers.Ballot.sealed(Ballot.next(x), b) == True{}: Bool}
        ),
        Shared.Bool.false_ne_true(h)
      )
    case Con{+b0, +rest}:
      h => Chk.link_find.at(
        b0,
        rest,
        b,
        Ledgers.Ballot.sealed(Ballot.next(b0), b),
        {==},
        h,
        Chk.link_find(rest, b)
      )

# a ballot that a link names is a ballot of the ledger at the place before
def Chk.linked_some.of(
  ~mach: Machine(),
  ~d: Led(mach),
  -kern: Kernel(mach, d),
  +l: Led.L(mach, d),
  +b: Ledgers.Ballot,
  +w: Ledgers.Place,
  ex: Exists(
    Ledgers.Ballot,
    x => {
      List.contains(
        ~Ledgers.Ballot,
        ~Ledgers.Ballot.is_eq,
        Led.ballots.at(~mach, ~d, l, w, Ledgers.Ballot.voter(b)),
        x
      )
        == True{}: Bool
    }
      & {Ledgers.Ballot.sealed(Ballot.next(x), b) == True{}: Bool}
  )
) -> Ballot.Linked(mach, d, kern, l, b, Some{w}):
  match ex:
    case Tuple{+x, Tuple{hc, hs}}:
      +ha = Equal.trans(
        Bool,
        Bool.and(
          Ledgers.Kind.has(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), l, Ledgers.Entry.Ballot{x}),
          Ledgers.Ballot.is_at(x, w, Ledgers.Ballot.voter(b))
        ),
        List.contains(~Ledgers.Ballot, ~Ledgers.Ballot.is_eq, Led.ballots.at(~mach, ~d, l, w, Ledgers.Ballot.voter(b)), x),
        True{},
        Equal.sym(
          Bool,
          List.contains(~Ledgers.Ballot, ~Ledgers.Ballot.is_eq, Led.ballots.at(~mach, ~d, l, w, Ledgers.Ballot.voter(b)), x),
          Bool.and(
            Ledgers.Kind.has(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), l, Ledgers.Entry.Ballot{x}),
            Ledgers.Ballot.is_at(x, w, Ledgers.Ballot.voter(b))
          ),
          Ledgers.Laws.ballots(Machine.Q(mach), Machine.code(mach), Led.kind(mach, d), Led.laws(mach, d))(l)(w)(
            Ledgers.Ballot.voter(b)
          )(x)
        ),
        hc
      )
      Tuple{
        x,
        Tuple{
          Shared.Bool.and_true_left(
            Ledgers.Kind.has(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), l, Ledgers.Entry.Ballot{x}),
            Ledgers.Ballot.is_at(x, w, Ledgers.Ballot.voter(b))
          )(ha),
          Tuple{
            Shared.Bool.and_true_right(
              Ledgers.Kind.has(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), l, Ledgers.Entry.Ballot{x}),
              Ledgers.Ballot.is_at(x, w, Ledgers.Ballot.voter(b))
            )(ha),
            hs
          }
        }
      }

# what a test of a ballot that has a ballot before it says
def Chk.linked_some(
  ~mach: Machine(),
  ~d: Led(mach),
  -kern: Kernel(mach, d),
  +l: Led.L(mach, d),
  +b: Ledgers.Ballot,
  +w: Ledgers.Place
) -> {Ballots.link(Led.ballots.at(~mach, ~d, l, w, Ledgers.Ballot.voter(b)), b) == True{}: Bool}
  -> Ballot.Linked(mach, d, kern, l, b, Some{w}):
  h => Chk.linked_some.of(
    ~mach,
    ~d,
    kern,
    l,
    b,
    w,
    Chk.link_find(Led.ballots.at(~mach, ~d, l, w, Ledgers.Ballot.voter(b)), b)(h)
  )

# the key that a walk of the line found at the tip after j steps
def Chk.walk.hit.of(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  +l: Led.L(mach, d),
  +c: Ledgers.Line,
  +j: Nat,
  +t: Tip,
  +voter: String,
  -b: Ledgers.Ballot,
  et: {Line.at(~mach, ~d, ~kern, j, l, c) == Some{t}: Maybe<&2, Tip>},
  ex: Exists(
    Hashes.Hash,
    k => {Tip.key(~mach, ~d, l, Some{t}, voter) == Some{k}: Maybe<&2, Hashes.Hash>}
      & {Ledgers.Ballot.sealed(k, b) == True{}: Bool}
  )
) -> Exists(
  Hashes.Hash,
  k => {Ledgers.Ballot.sealed(k, b) == True{}: Bool}
    & Exists(Nat, n => {Tip.key(~mach, ~d, l, Line.at(~mach, ~d, ~kern, n, l, c), voter) == Some{k}: Maybe<&2, Hashes.Hash>})
):
  match ex:
    case Tuple{+k, Tuple{ek, sk}}:
      Tuple{
        k,
        Tuple{
          sk,
          Tuple{
            j,
            %Equal.sym(Maybe<&2, Tip>, Line.at(~mach, ~d, ~kern, j, l, c), Some{t}, et): {
              Tip.key(~mach, ~d, l, _, voter) == Some{k}: Maybe<&2, Hashes.Hash>
            }
            ek
          }
        }
      }

# Chk.walk once the next tip is known (m)
def Chk.walk.next(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  +p: Nat,
  +l: Led.L(mach, d),
  +c: Ledgers.Line,
  +j: Nat,
  +t: Tip,
  +voter: String,
  +b: Ledgers.Ballot,
  m: Maybe<&2, Tip>,
  em: {Line.next(~mach, ~d, ~kern, l, c, U32.from_nat(j), t) == m: Maybe<&2, Tip>},
  et: {Line.at(~mach, ~d, ~kern, j, l, c) == Some{t}: Maybe<&2, Tip>},
  h: {Tip.on(m, t2 => Root.seals.go(~mach, ~d, ~kern, p, l, c, U32.inc(U32.from_nat(j)), t2, voter, b)) == True{}: Bool},
  ih: @t2: Tip -> {Line.at(~mach, ~d, ~kern, 1n+j, l, c) == Some{t2}: Maybe<&2, Tip>}
    -> {Root.seals.go(~mach, ~d, ~kern, p, l, c, U32.from_nat(1n+j), t2, voter, b) == True{}: Bool}
    -> Exists(
      Hashes.Hash,
      k => {Ledgers.Ballot.sealed(k, b) == True{}: Bool}
        & Exists(Nat, n => {Tip.key(~mach, ~d, l, Line.at(~mach, ~d, ~kern, n, l, c), voter) == Some{k}: Maybe<&2, Hashes.Hash>})
    )
) -> Exists(
  Hashes.Hash,
  k => {Ledgers.Ballot.sealed(k, b) == True{}: Bool}
    & Exists(Nat, n => {Tip.key(~mach, ~d, l, Line.at(~mach, ~d, ~kern, n, l, c), voter) == Some{k}: Maybe<&2, Hashes.Hash>})
):
  match m:
    case None{}:
      Empty.absurd(
        Exists(
          Hashes.Hash,
          k => {Ledgers.Ballot.sealed(k, b) == True{}: Bool}
            & Exists(Nat, n => {Tip.key(~mach, ~d, l, Line.at(~mach, ~d, ~kern, n, l, c), voter) == Some{k}: Maybe<&2, Hashes.Hash>})
        ),
        Shared.Bool.false_ne_true(h)
      )
    case Some{+t2}:
      ih(
        t2
      )(
        %Equal.sym(Maybe<&2, Tip>, Line.at(~mach, ~d, ~kern, j, l, c), Some{t}, et): {
          Maybe.bind(&2, Tip, Tip, _, +x => Line.next(~mach, ~d, ~kern, l, c, U32.from_nat(j), x)) == Some{t2}: Maybe<&2, Tip>
        }
        em
      )(h)

# Chk.walk once whether the tip itself gives the key is known (s)
def Chk.walk.at(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  +p: Nat,
  +l: Led.L(mach, d),
  +c: Ledgers.Line,
  +j: Nat,
  +t: Tip,
  +voter: String,
  +b: Ledgers.Ballot,
  s: Bool,
  es: {Key.seals(Tip.key(~mach, ~d, l, Some{t}, voter), b) == s: Bool},
  h: {
    Bool.or(
      Key.seals(Tip.key(~mach, ~d, l, Some{t}, voter), b),
      Tip.on(
        Line.next(~mach, ~d, ~kern, l, c, U32.from_nat(j), t),
        t2 => Root.seals.go(~mach, ~d, ~kern, p, l, c, U32.inc(U32.from_nat(j)), t2, voter, b)
      )
    )
      == True{}: Bool
  },
  +et: {Line.at(~mach, ~d, ~kern, j, l, c) == Some{t}: Maybe<&2, Tip>},
  ih: @t2: Tip -> {Line.at(~mach, ~d, ~kern, 1n+j, l, c) == Some{t2}: Maybe<&2, Tip>}
    -> {Root.seals.go(~mach, ~d, ~kern, p, l, c, U32.from_nat(1n+j), t2, voter, b) == True{}: Bool}
    -> Exists(
      Hashes.Hash,
      k => {Ledgers.Ballot.sealed(k, b) == True{}: Bool}
        & Exists(Nat, n => {Tip.key(~mach, ~d, l, Line.at(~mach, ~d, ~kern, n, l, c), voter) == Some{k}: Maybe<&2, Hashes.Hash>})
    )
) -> Exists(
  Hashes.Hash,
  k => {Ledgers.Ballot.sealed(k, b) == True{}: Bool}
    & Exists(Nat, n => {Tip.key(~mach, ~d, l, Line.at(~mach, ~d, ~kern, n, l, c), voter) == Some{k}: Maybe<&2, Hashes.Hash>})
):
  match s:
    case True{}:
      Chk.walk.hit.of(~mach, ~d, ~kern, l, c, j, t, voter, b, et, Chk.seals(Tip.key(~mach, ~d, l, Some{t}, voter), b)(es))
    case False{}:
      Chk.walk.next(
        ~mach,
        ~d,
        ~kern,
        p,
        l,
        c,
        j,
        t,
        voter,
        b,
        Line.next(~mach, ~d, ~kern, l, c, U32.from_nat(j), t),
        {==},
        et,
        Equal.trans(
          Bool,
          Tip.on(
            Line.next(~mach, ~d, ~kern, l, c, U32.from_nat(j), t),
            t2 => Root.seals.go(~mach, ~d, ~kern, p, l, c, U32.inc(U32.from_nat(j)), t2, voter, b)
          ),
          Bool.or(
            Key.seals(Tip.key(~mach, ~d, l, Some{t}, voter), b),
            Tip.on(
              Line.next(~mach, ~d, ~kern, l, c, U32.from_nat(j), t),
              t2 => Root.seals.go(~mach, ~d, ~kern, p, l, c, U32.inc(U32.from_nat(j)), t2, voter, b)
            )
          ),
          True{},
          Equal.sym(
            Bool,
            Bool.or(
              Key.seals(Tip.key(~mach, ~d, l, Some{t}, voter), b),
              Tip.on(
                Line.next(~mach, ~d, ~kern, l, c, U32.from_nat(j), t),
                t2 => Root.seals.go(~mach, ~d, ~kern, p, l, c, U32.inc(U32.from_nat(j)), t2, voter, b)
              )
            ),
            Tip.on(
              Line.next(~mach, ~d, ~kern, l, c, U32.from_nat(j), t),
              t2 => Root.seals.go(~mach, ~d, ~kern, p, l, c, U32.inc(U32.from_nat(j)), t2, voter, b)
            ),
            Equal.cong(
              Bool,
              Bool,
              z => Bool.or(
                z,
                Tip.on(
                  Line.next(~mach, ~d, ~kern, l, c, U32.from_nat(j), t),
                  t2 => Root.seals.go(~mach, ~d, ~kern, p, l, c, U32.inc(U32.from_nat(j)), t2, voter, b)
                )
              ),
              Key.seals(Tip.key(~mach, ~d, l, Some{t}, voter), b),
              False{},
              es
            )
          ),
          h
        ),
        ih
      )

# a walk of a line from the tip after j steps that finds a key that seals b
# finds it at a tip after some steps
def Chk.walk(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  f: Nat,
  +l: Led.L(mach, d),
  +c: Ledgers.Line,
  +j: Nat,
  +t: Tip,
  +voter: String,
  +b: Ledgers.Ballot
) -> {Line.at(~mach, ~d, ~kern, j, l, c) == Some{t}: Maybe<&2, Tip>}
  -> {Root.seals.go(~mach, ~d, ~kern, f, l, c, U32.from_nat(j), t, voter, b) == True{}: Bool}
  -> Exists(
    Hashes.Hash,
    k => {Ledgers.Ballot.sealed(k, b) == True{}: Bool}
      & Exists(Nat, n => {Tip.key(~mach, ~d, l, Line.at(~mach, ~d, ~kern, n, l, c), voter) == Some{k}: Maybe<&2, Hashes.Hash>})
  ):
  match f:
    case 0n:
      et => h => Chk.walk.hit.of(~mach, ~d, ~kern, l, c, j, t, voter, b, et, Chk.seals(Tip.key(~mach, ~d, l, Some{t}, voter), b)(h))
    case 1n+(+p):
      +et => h => Chk.walk.at(
        ~mach,
        ~d,
        ~kern,
        p,
        l,
        c,
        j,
        t,
        voter,
        b,
        Key.seals(Tip.key(~mach, ~d, l, Some{t}, voter), b),
        {==},
        h,
        et,
        t2 => Chk.walk(~mach, ~d, ~kern, p, l, c, 1n+j, t2, voter, b)
      )

# the request that starts the root line gives the key that seals b
def Chk.first.key.of(
  ~mach: Machine(),
  ~d: Led(mach),
  -kern: Kernel(mach, d),
  -l: Led.L(mach, d),
  -b: Ledgers.Ballot,
  ex: Exists(
    Hashes.Hash,
    k => {
      Root.key.at(~mach, Led.get(~mach, ~d, l, Ledgers.Name.Ask{Ledgers.Ballot.root(b)}), Ledgers.Ballot.voter(b))
        == Some{k}: Maybe<&2, Hashes.Hash>
    }
      & {Ledgers.Ballot.sealed(k, b) == True{}: Bool}
  )
) -> Ballot.Linked(mach, d, kern, l, b, None{}):
  match ex:
    case Tuple{+k, Tuple{ek, sk}}:
      Tuple{k, Tuple{sk, Inl{ek}}}

# a tip of the root line gives the key that seals b
def Chk.first.walk.of(
  -mach: Machine(),
  -d: Led(mach),
  -kern: Kernel(mach, d),
  -l: Led.L(mach, d),
  -b: Ledgers.Ballot,
  ex: Exists(
    Hashes.Hash,
    k => {Ledgers.Ballot.sealed(k, b) == True{}: Bool}
      & Exists(
        Nat,
        n => {
          Tip.key(~mach, ~d, l, Line.at(~mach, ~d, ~kern, n, l, Root.line(Ledgers.Ballot.root(b))), Ledgers.Ballot.voter(b))
            == Some{k}: Maybe<&2, Hashes.Hash>
        }
      )
  )
) -> Ballot.Linked(mach, d, kern, l, b, None{}):
  match ex:
    case Tuple{+k, Tuple{sk, en}}:
      Tuple{k, Tuple{sk, Inr{en}}}

# the walk of the root line from its first tip, once the first tip is known
# (ms)
def Chk.first.start(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  +l: Led.L(mach, d),
  +b: Ledgers.Ballot,
  ms: Maybe<&2, Tip>,
  ems: {Line.start(~mach, ~d, ~kern, l, Root.line(Ledgers.Ballot.root(b))) == ms: Maybe<&2, Tip>},
  h: {
    Maybe.default(
      &2,
      Bool,
      Maybe.map(
        &2,
        Tip,
        Bool,
        t => Root.seals.go(
          ~mach,
          ~d,
          ~kern,
          Ledgers.Kind.heights(Machine.Q(mach), Led.kind(mach, d))(l)(Root.line(Ledgers.Ballot.root(b))),
          l,
          Root.line(Ledgers.Ballot.root(b)),
          0,
          t,
          Ledgers.Ballot.voter(b),
          b
        ),
        ms
      ),
      False{}
    )
      == True{}: Bool
  }
) -> Ballot.Linked(mach, d, kern, l, b, None{}):
  match ms:
    case None{}:
      Empty.absurd(Ballot.Linked(mach, d, kern, l, b, None{}), Shared.Bool.false_ne_true(h))
    case Some{+t0}:
      Chk.first.walk.of(
        mach,
        d,
        kern,
        l,
        b,
        Chk.walk(
          ~mach,
          ~d,
          ~kern,
          Ledgers.Kind.heights(Machine.Q(mach), Led.kind(mach, d))(l)(Root.line(Ledgers.Ballot.root(b))),
          l,
          Root.line(Ledgers.Ballot.root(b)),
          0n,
          t0,
          Ledgers.Ballot.voter(b),
          b
        )(ems)(h)
      )

# Chk.first once whether the start request gives the key is known (s)
def Chk.first.at(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  +l: Led.L(mach, d),
  +b: Ledgers.Ballot,
  s: Bool,
  es: {
    Key.seals(Root.key.at(~mach, Led.get(~mach, ~d, l, Ledgers.Name.Ask{Ledgers.Ballot.root(b)}), Ledgers.Ballot.voter(b)), b)
      == s: Bool
  },
  h: {Ballot.first_ok(~mach, ~d, ~kern, l, b) == True{}: Bool}
) -> Ballot.Linked(mach, d, kern, l, b, None{}):
  match s:
    case True{}:
      Chk.first.key.of(
        ~mach,
        ~d,
        kern,
        l,
        b,
        Chk.seals(
          Root.key.at(~mach, Led.get(~mach, ~d, l, Ledgers.Name.Ask{Ledgers.Ballot.root(b)}), Ledgers.Ballot.voter(b)),
          b
        )(es)
      )
    case False{}:
      Chk.first.start(
        ~mach,
        ~d,
        ~kern,
        l,
        b,
        Line.start(~mach, ~d, ~kern, l, Root.line(Ledgers.Ballot.root(b))),
        {==},
        Equal.trans(
          Bool,
          Maybe.default(
            &2,
            Bool,
            Maybe.map(
              &2,
              Tip,
              Bool,
              t => Root.seals.go(
                ~mach,
                ~d,
                ~kern,
                Ledgers.Kind.heights(Machine.Q(mach), Led.kind(mach, d))(l)(Root.line(Ledgers.Ballot.root(b))),
                l,
                Root.line(Ledgers.Ballot.root(b)),
                0,
                t,
                Ledgers.Ballot.voter(b),
                b
              ),
              Line.start(~mach, ~d, ~kern, l, Root.line(Ledgers.Ballot.root(b)))
            ),
            False{}
          ),
          Ballot.first_ok(~mach, ~d, ~kern, l, b),
          True{},
          Equal.sym(
            Bool,
            Ballot.first_ok(~mach, ~d, ~kern, l, b),
            Maybe.default(
              &2,
              Bool,
              Maybe.map(
                &2,
                Tip,
                Bool,
                t => Root.seals.go(
                  ~mach,
                  ~d,
                  ~kern,
                  Ledgers.Kind.heights(Machine.Q(mach), Led.kind(mach, d))(l)(Root.line(Ledgers.Ballot.root(b))),
                  l,
                  Root.line(Ledgers.Ballot.root(b)),
                  0,
                  t,
                  Ledgers.Ballot.voter(b),
                  b
                ),
                Line.start(~mach, ~d, ~kern, l, Root.line(Ledgers.Ballot.root(b)))
              ),
              False{}
            ),
            Equal.cong(
              Bool,
              Bool,
              z => Bool.or(
                z,
                Maybe.default(
                  &2,
                  Bool,
                  Maybe.map(
                    &2,
                    Tip,
                    Bool,
                    t => Root.seals.go(
                      ~mach,
                      ~d,
                      ~kern,
                      Ledgers.Kind.heights(Machine.Q(mach), Led.kind(mach, d))(l)(Root.line(Ledgers.Ballot.root(b))),
                      l,
                      Root.line(Ledgers.Ballot.root(b)),
                      0,
                      t,
                      Ledgers.Ballot.voter(b),
                      b
                    ),
                    Line.start(~mach, ~d, ~kern, l, Root.line(Ledgers.Ballot.root(b)))
                  ),
                  False{}
                )
              ),
              Key.seals(Root.key.at(~mach, Led.get(~mach, ~d, l, Ledgers.Name.Ask{Ledgers.Ballot.root(b)}), Ledgers.Ballot.voter(b)), b),
              False{},
              es
            )
          ),
          h
        )
      )

# a first ballot that the test passes is linked
def Chk.first(~mach: Machine(), ~d: Led(mach), ~kern: Kernel(mach, d), +l: Led.L(mach, d), +b: Ledgers.Ballot) -> {
  Ballot.first_ok(~mach, ~d, ~kern, l, b) == True{}: Bool
} -> Ballot.Linked(mach, d, kern, l, b, None{}):
  h => Chk.first.at(
    ~mach,
    ~d,
    ~kern,
    l,
    b,
    Key.seals(Root.key.at(~mach, Led.get(~mach, ~d, l, Ledgers.Name.Ask{Ledgers.Ballot.root(b)}), Ledgers.Ballot.voter(b)), b),
    {==},
    h
  )

# a ballot that the test passes is linked
def Chk.new_linked(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  +l: Led.L(mach, d),
  +b: Ledgers.Ballot,
  p: Maybe<&2, Ledgers.Place>
) -> {Ballot.linked.at(~mach, ~d, ~kern, l, b, p) == True{}: Bool} -> Ballot.Linked(mach, d, kern, l, b, p):
  match p:
    case None{}:
      Chk.first(~mach, ~d, ~kern, l, b)
    case Some{+w}:
      Chk.linked_some(~mach, ~d, kern, l, b, w)

# the ballot of an entry, or a default
def Chk.bal(-Q: Data, e: Ledgers.Entry<Q>, +x: Ledgers.Ballot) -> Ledgers.Ballot:
  match e:
    case Ledgers.Entry.Ballot{y}:
      y
    case _:
      x

# the new ballot b of l with b is linked, and so is the ballot b2 when the
# ledger holds it under the name of b (z: whether the names are one)
def Chk.new_case(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  +l2: Led.L(mach, d),
  +b: Ledgers.Ballot,
  +b2: Ledgers.Ballot,
  z: Bool,
  h: {
    Shared.Maybe.is_eq(
      ~Entry(mach),
      ~Ledgers.Entry.same(~Machine.Q(mach), ~Machine.code(mach)),
      Shared.Maybe.when(Entry(mach), z, u => Some{Ledgers.Entry.Ballot{b}}),
      Some{Ledgers.Entry.Ballot{b2}}
    )
      == True{}: Bool
  },
  ht: {Ballot.linked(~mach, ~d, ~kern, l2, b) == True{}: Bool}
) -> Ballot.Linked(mach, d, kern, l2, b2, Ledgers.Ballot.prev(b2)):
  match z:
    case True{}:
      %Equal.cong(
        Entry(mach),
        Ledgers.Ballot,
        y => Chk.bal(Machine.Q(mach), y, b),
        Ledgers.Entry.Ballot{b},
        Ledgers.Entry.Ballot{b2},
        Ledgers.Entry.same_sound(~Machine.Q(mach), ~Machine.code(mach), Ledgers.Entry.Ballot{b}, Ledgers.Entry.Ballot{b2})(h)
      ): Ballot.Linked(mach, d, kern, l2, _, Ledgers.Ballot.prev(_))
      Chk.new_linked(~mach, ~d, ~kern, l2, b, Ledgers.Ballot.prev(b))(ht)
    case False{}:
      Empty.absurd(Ballot.Linked(mach, d, kern, l2, b2, Ledgers.Ballot.prev(b2)), Shared.Bool.false_ne_true(h))

# a ballot of l with b is linked: an old one stays linked, the new one passed
# the test (m: what l holds under its name)
def Chk.old_or_new(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  +l: Led.L(mach, d),
  +b: Ledgers.Ballot,
  +b2: Ledgers.Ballot,
  s1: @x: Ledgers.Ballot -> {Led.has(~mach, ~d, l, Ledgers.Entry.Ballot{x}) == True{}: Bool}
    -> Ballot.Linked(mach, d, kern, l, x, Ledgers.Ballot.prev(x)),
  +later: Led.Later(~mach, ~d, l, Led.add(~mach, ~d, l, Ledgers.Entry.Ballot{b})),
  +ht: {Ballot.linked(~mach, ~d, ~kern, Led.add(~mach, ~d, l, Ledgers.Entry.Ballot{b}), b) == True{}: Bool},
  m: Maybe<&2, Entry(mach)>,
  em: {Led.get(~mach, ~d, l, Entry.name(~mach, Ledgers.Entry.Ballot{b2})) == m: Maybe<&2, Entry(mach)>}
) -> {
  Shared.Maybe.is_eq(
    ~Entry(mach),
    ~Ledgers.Entry.same(~Machine.Q(mach), ~Machine.code(mach)),
    Maybe.or(
      &2,
      Entry(mach),
      m,
      Shared.Maybe.when(
        Entry(mach),
        Ledgers.Name.is_eq(Entry.name(~mach, Ledgers.Entry.Ballot{b}), Entry.name(~mach, Ledgers.Entry.Ballot{b2})),
        u => Some{Ledgers.Entry.Ballot{b}}
      )
    ),
    Some{Ledgers.Entry.Ballot{b2}}
  )
    == True{}: Bool
} -> Ballot.Linked(mach, d, kern, Led.add(~mach, ~d, l, Ledgers.Entry.Ballot{b}), b2, Ledgers.Ballot.prev(b2)):
  match m:
    case Some{+y}:
      h => Chk.link_grows(
        ~mach,
        ~d,
        ~kern,
        l,
        Led.add(~mach, ~d, l, Ledgers.Entry.Ballot{b}),
        later,
        b2,
        Ledgers.Ballot.prev(b2),
        s1(
          b2
        )(
          Equal.trans(
            Bool,
            Shared.Maybe.is_eq(
              ~Entry(mach),
              ~Ledgers.Entry.same(~Machine.Q(mach), ~Machine.code(mach)),
              Led.get(~mach, ~d, l, Entry.name(~mach, Ledgers.Entry.Ballot{b2})),
              Some{Ledgers.Entry.Ballot{b2}}
            ),
            Shared.Maybe.is_eq(
              ~Entry(mach),
              ~Ledgers.Entry.same(~Machine.Q(mach), ~Machine.code(mach)),
              Some{y},
              Some{Ledgers.Entry.Ballot{b2}}
            ),
            True{},
            Equal.cong(
              Maybe<&2, Entry(mach)>,
              Bool,
              z => Shared.Maybe.is_eq(
                ~Entry(mach),
                ~Ledgers.Entry.same(~Machine.Q(mach), ~Machine.code(mach)),
                z,
                Some{Ledgers.Entry.Ballot{b2}}
              ),
              Led.get(~mach, ~d, l, Entry.name(~mach, Ledgers.Entry.Ballot{b2})),
              Some{y},
              em
            ),
            h
          )
        )
      )
    case None{}:
      h => Chk.new_case(
        ~mach,
        ~d,
        ~kern,
        Led.add(~mach, ~d, l, Ledgers.Entry.Ballot{b}),
        b,
        b2,
        Ledgers.Name.is_eq(Entry.name(~mach, Ledgers.Entry.Ballot{b}), Entry.name(~mach, Ledgers.Entry.Ballot{b2})),
        h,
        ht
      )

# a choice of m, else nothing, holds what m holds
def Chk.or_none(-mach: Machine(), m: Maybe<&2, Entry(mach)>, -e: Entry(mach)) -> {
  Shared.Maybe.is_eq(
    ~Entry(mach),
    ~Ledgers.Entry.same(~Machine.Q(mach), ~Machine.code(mach)),
    Maybe.or(&2, Entry(mach), m, None{}),
    Some{e}
  )
    == True{}: Bool
} -> {
  Shared.Maybe.is_eq(~Entry(mach), ~Ledgers.Entry.same(~Machine.Q(mach), ~Machine.code(mach)), m, Some{e}) == True{}: Bool
}:
  match m:
    case None{}:
      h => h
    case Some{y}:
      h => h

# a ledger with one more ballot holds the same proofs of lies
def Chk.lie_old(
  ~mach: Machine(),
  ~d: Led(mach),
  +l: Led.L(mach, d),
  +b: Ledgers.Ballot,
  +x: Ledgers.Lie
) -> {Led.has(~mach, ~d, Led.add(~mach, ~d, l, Ledgers.Entry.Ballot{b}), Ledgers.Entry.Lie{x}) == True{}: Bool}
  -> {Led.has(~mach, ~d, l, Ledgers.Entry.Lie{x}) == True{}: Bool}:
  hx => Chk.or_none(
    mach,
    Led.get(~mach, ~d, l, Entry.name(~mach, Ledgers.Entry.Lie{x})),
    Ledgers.Entry.Lie{x}
  )(
    Equal.trans(
      Bool,
      Shared.Maybe.is_eq(
        ~Entry(mach),
        ~Ledgers.Entry.same(~Machine.Q(mach), ~Machine.code(mach)),
        Maybe.or(
          &2,
          Entry(mach),
          Led.get(~mach, ~d, l, Entry.name(~mach, Ledgers.Entry.Lie{x})),
          Shared.Maybe.when(
            Entry(mach),
            Ledgers.Name.is_eq(Entry.name(~mach, Ledgers.Entry.Ballot{b}), Entry.name(~mach, Ledgers.Entry.Lie{x})),
            u => Some{Ledgers.Entry.Ballot{b}}
          )
        ),
        Some{Ledgers.Entry.Lie{x}}
      ),
      Shared.Maybe.is_eq(
        ~Entry(mach),
        ~Ledgers.Entry.same(~Machine.Q(mach), ~Machine.code(mach)),
        Led.get(~mach, ~d, Led.add(~mach, ~d, l, Ledgers.Entry.Ballot{b}), Entry.name(~mach, Ledgers.Entry.Lie{x})),
        Some{Ledgers.Entry.Lie{x}}
      ),
      True{},
      Equal.sym(
        Bool,
        Shared.Maybe.is_eq(
          ~Entry(mach),
          ~Ledgers.Entry.same(~Machine.Q(mach), ~Machine.code(mach)),
          Led.get(~mach, ~d, Led.add(~mach, ~d, l, Ledgers.Entry.Ballot{b}), Entry.name(~mach, Ledgers.Entry.Lie{x})),
          Some{Ledgers.Entry.Lie{x}}
        ),
        Shared.Maybe.is_eq(
          ~Entry(mach),
          ~Ledgers.Entry.same(~Machine.Q(mach), ~Machine.code(mach)),
          Maybe.or(
            &2,
            Entry(mach),
            Led.get(~mach, ~d, l, Entry.name(~mach, Ledgers.Entry.Lie{x})),
            Shared.Maybe.when(
              Entry(mach),
              Ledgers.Name.is_eq(Entry.name(~mach, Ledgers.Entry.Ballot{b}), Entry.name(~mach, Ledgers.Entry.Lie{x})),
              u => Some{Ledgers.Entry.Ballot{b}}
            )
          ),
          Some{Ledgers.Entry.Lie{x}}
        ),
        Equal.cong(
          Maybe<&2, Entry(mach)>,
          Bool,
          z => Shared.Maybe.is_eq(~Entry(mach), ~Ledgers.Entry.same(~Machine.Q(mach), ~Machine.code(mach)), z, Some{Ledgers.Entry.Lie{x}}),
          Led.get(~mach, ~d, Led.add(~mach, ~d, l, Ledgers.Entry.Ballot{b}), Entry.name(~mach, Ledgers.Entry.Lie{x})),
          Maybe.or(
            &2,
            Entry(mach),
            Led.get(~mach, ~d, l, Entry.name(~mach, Ledgers.Entry.Lie{x})),
            Shared.Maybe.when(
              Entry(mach),
              Ledgers.Name.is_eq(Entry.name(~mach, Ledgers.Entry.Ballot{b}), Entry.name(~mach, Ledgers.Entry.Lie{x})),
              u => Some{Ledgers.Entry.Ballot{b}}
            )
          ),
          Ledgers.Laws.get_add(Machine.Q(mach), Machine.code(mach), Led.kind(mach, d), Led.laws(mach, d))(l)(Ledgers.Entry.Ballot{b})(
            Entry.name(~mach, Ledgers.Entry.Lie{x})
          )
        )
      ),
      hx
    )
  )

# a ballot that the test passes checks, in a ledger that holds only what checks
def Chk.ballot(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  +l: Led.L(mach, d),
  +b: Ledgers.Ballot,
  so: Led.Sound(mach, d, kern, l),
  +h: {Entry.checks(~mach, ~d, ~kern, l, Ledgers.Entry.Ballot{b}) == True{}: Bool}
) -> Entry.Checks(mach, d, kern, l, Ledgers.Entry.Ballot{b}):
  match so:
    case Tuple{s1, s2}:
      +l2 = Led.add(~mach, ~d, l, Ledgers.Entry.Ballot{b})
      +hon = Shared.Bool.and_true_left(Led.honest(~mach, ~d, l2), Ballot.linked(~mach, ~d, ~kern, l2, b))(h)
      +ht = Shared.Bool.and_true_right(Led.honest(~mach, ~d, l2), Ballot.linked(~mach, ~d, ~kern, l2, b))(h)
      +later = Shared.Bool.and_both(
        Ledgers.Kind.grows(~Machine.Q(mach), ~Machine.code(mach), ~Led.kind(mach, d), l, l2),
        Led.honest(~mach, ~d, l2)
      )(Hist.add(~mach, ~d, l, Ledgers.Entry.Ballot{b}))(hon)
      Tuple{
        Tuple{Led.later_single(~mach, ~d, l, l2)(later), +c => +hh => Led.later_last(~mach, ~d, l, l2, c, hh)(later)},
        Tuple{
          +b2 => hb2 => Chk.old_or_new(
            ~mach,
            ~d,
            ~kern,
            l,
            b,
            b2,
            s1,
            later,
            ht,
            Led.get(~mach, ~d, l, Entry.name(~mach, Ledgers.Entry.Ballot{b2})),
            {==}
          )(
            Equal.trans(
              Bool,
              Shared.Maybe.is_eq(
                ~Entry(mach),
                ~Ledgers.Entry.same(~Machine.Q(mach), ~Machine.code(mach)),
                Maybe.or(
                  &2,
                  Entry(mach),
                  Led.get(~mach, ~d, l, Entry.name(~mach, Ledgers.Entry.Ballot{b2})),
                  Shared.Maybe.when(
                    Entry(mach),
                    Ledgers.Name.is_eq(Entry.name(~mach, Ledgers.Entry.Ballot{b}), Entry.name(~mach, Ledgers.Entry.Ballot{b2})),
                    u => Some{Ledgers.Entry.Ballot{b}}
                  )
                ),
                Some{Ledgers.Entry.Ballot{b2}}
              ),
              Shared.Maybe.is_eq(
                ~Entry(mach),
                ~Ledgers.Entry.same(~Machine.Q(mach), ~Machine.code(mach)),
                Led.get(~mach, ~d, l2, Entry.name(~mach, Ledgers.Entry.Ballot{b2})),
                Some{Ledgers.Entry.Ballot{b2}}
              ),
              True{},
              Equal.sym(
                Bool,
                Shared.Maybe.is_eq(
                  ~Entry(mach),
                  ~Ledgers.Entry.same(~Machine.Q(mach), ~Machine.code(mach)),
                  Led.get(~mach, ~d, l2, Entry.name(~mach, Ledgers.Entry.Ballot{b2})),
                  Some{Ledgers.Entry.Ballot{b2}}
                ),
                Shared.Maybe.is_eq(
                  ~Entry(mach),
                  ~Ledgers.Entry.same(~Machine.Q(mach), ~Machine.code(mach)),
                  Maybe.or(
                    &2,
                    Entry(mach),
                    Led.get(~mach, ~d, l, Entry.name(~mach, Ledgers.Entry.Ballot{b2})),
                    Shared.Maybe.when(
                      Entry(mach),
                      Ledgers.Name.is_eq(Entry.name(~mach, Ledgers.Entry.Ballot{b}), Entry.name(~mach, Ledgers.Entry.Ballot{b2})),
                      u => Some{Ledgers.Entry.Ballot{b}}
                    )
                  ),
                  Some{Ledgers.Entry.Ballot{b2}}
                ),
                Equal.cong(
                  Maybe<&2, Entry(mach)>,
                  Bool,
                  z => Shared.Maybe.is_eq(
                    ~Entry(mach),
                    ~Ledgers.Entry.same(~Machine.Q(mach), ~Machine.code(mach)),
                    z,
                    Some{Ledgers.Entry.Ballot{b2}}
                  ),
                  Led.get(~mach, ~d, l2, Entry.name(~mach, Ledgers.Entry.Ballot{b2})),
                  Maybe.or(
                    &2,
                    Entry(mach),
                    Led.get(~mach, ~d, l, Entry.name(~mach, Ledgers.Entry.Ballot{b2})),
                    Shared.Maybe.when(
                      Entry(mach),
                      Ledgers.Name.is_eq(Entry.name(~mach, Ledgers.Entry.Ballot{b}), Entry.name(~mach, Ledgers.Entry.Ballot{b2})),
                      u => Some{Ledgers.Entry.Ballot{b}}
                    )
                  ),
                  Ledgers.Laws.get_add(Machine.Q(mach), Machine.code(mach), Led.kind(mach, d), Led.laws(mach, d))(l)(
                    Ledgers.Entry.Ballot{b}
                  )(Entry.name(~mach, Ledgers.Entry.Ballot{b2}))
                )
              ),
              hb2
            )
          ),
          +x => hx => s2(x)(Chk.lie_old(~mach, ~d, l, b, x)(hx))
        }
      }

# Entry.checks_sound, by the kind of the entry
def Chk.go(
  ~mach: Machine(),
  ~d: Led(mach),
  ~kern: Kernel(mach, d),
  +l: Led.L(mach, d),
  e: Entry(mach),
  so: Led.Sound(mach, d, kern, l),
  h: {Entry.checks(~mach, ~d, ~kern, l, e) == True{}: Bool}
) -> Entry.Checks(mach, d, kern, l, e):
  match e:
    case Ledgers.Entry.Ask{i, t, q}:
      Unit{}
    case Ledgers.Entry.Data{ws}:
      Unit{}
    case Ledgers.Entry.Ballot{+b}:
      Chk.ballot(~mach, ~d, ~kern, l, b, so, h)
    case Ledgers.Entry.Lie{x}:
      Chk.lie(x)(h)

# Laws of checks

# a lie that the test passes proves
law Lie.proves_sound:
  for x: Ledgers.Lie
  {Lie.proves(x) == True{}: Bool} -> Lie.Proves(x)

def Lie.proves_sound(x):
  Chk.lie(x)

# an entry that the test passes checks, in a ledger that holds only what
# checks
law Entry.checks_sound:
  for ~mach: Machine()
  for ~d: Led(mach)
  for ~kern: Kernel(mach, d)
  for l: Led.L(mach, d)
  for e: Entry(mach)
  Led.Sound(mach, d, kern, l) -> {Entry.checks(~mach, ~d, ~kern, l, e) == True{}: Bool} -> Entry.Checks(mach, d, kern, l, e)

def Entry.checks_sound(mach, d, kern, l, e):
  so => h => Chk.go(~mach, ~d, ~kern, l, e, so, h)
