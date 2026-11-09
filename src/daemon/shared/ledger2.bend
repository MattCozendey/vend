import Base
import ../../shared.bend as Shared
import ./shared/cell.bend as Cells
import ./shared/quorum.bend as Quorums
import ./shared/shared/trie.bend as Tries

# Ledgers
# =======
# A ledger holds entries in slots: the requests that writers make, the votes
# of nodes, and facts that say where a decision is. Ledgers sync by joining
# what they hold, so every ledger that took in the same entries holds the
# same state, in any order and any number of times.
#
# A line (a store's root, or a line that its root made) is a list of epochs;
# the owners of an epoch are fixed. A step of an epoch is the decision of its
# owners' ballots in the bucket of its height (Quorum.decide). Heights and
# epochs are 32-bit, so a bucket is one key away: no read walks a line.
#
# Facts (where a request was decided, where an epoch began, where a line was
# made) are written by the nodes that see a decision, and checked against the
# bucket that they name whenever they are read, so a wrong fact is ignored,
# never believed.
#
# What a change Q means is the caller's. A ledger reads of a change only its
# View, compares changes with same, and asks judge for a verdict.

# Names
# -----

# a request: the writer that made it and the ID that the writer gave it. A
# version is the request that made it.
type Id is Data:
  Id{writer: String, request: String}

# a line: the request that started its store, and its key below the store's
# root line (none for the root). Keys below one root are prefix-free.
type Chain is Data:
  Chain{root: Id, sub: Maybe<&2, List<&2, Bool>>}

# what a ledger reads of a change: it starts a store with its first owners;
# or it changes the line on, gives it owners (if any: a new epoch) and, on a
# root, makes the line below it of that key (if any)
type View is Data:
  View.root{owners: List<&2, String>}
  View.on{chain: Chain, owners: Maybe<&2, List<&2, String>>, makes: Maybe<&2, List<&2, Bool>>}

# a vote for a request, whose change has the view: its owners take it, or
# refuse it as stale
type Vote is Data:
  Vote{id: Id, takes: Bool, view: View}

# a place on a line: an epoch and a height in it
type Where is Data:
  Where{chain: Chain, epoch: U32, height: U32}

# a request of a change, with its time; a vote of a node; or a fact
type Entry<-Q: Data> is Data:
  Entry.ask{id: Id, time: String, ask: Q}
  Entry.vote{vote: Vote}
  Entry.at{at: Where}

# Keys
# ----

# the key of i
def Id.key(i: Id) -> List<&2, Bool>:
  match i:
    case Id{w, r}:
      List.append(&2, Bool, Tries.Trie.text(w), Tries.Trie.text(r))

# the key of the line c
def Chain.key(c: Chain) -> List<&2, Bool>:
  match c:
    case Chain{i, None{}}:
      List.append(&2, Bool, Id.key(i), [False{}])
    case Chain{i, Some{k}}:
      List.append(&2, Bool, Id.key(i), True{} <> k)

# the key of an epoch or a height: its 32 bits, highest first, so keys are in
# the order of numbers
def Word.key(x: U32) -> List<&2, Bool>:
  Tries.Trie.word(32n, x)

# the number of a key of 32 bits, highest first, after acc
def Word.of_key(k: List<&2, Bool>, acc: U32) -> U32:
  match k:
    case Nil{}:
      acc
    case Con{False{}, r}:
      Word.of_key(r, U32.shl(acc))
    case Con{True{}, r}:
      Word.of_key(r, U32.or(U32.shl(acc), 1))

# the slot of the request i
def Slot.ask(i: Id) -> List<&2, Bool>:
  False{} <> False{} <> Id.key(i)

# the start of the slots of the votes of the epoch e of the line c
def Slot.votes(c: Chain, e: U32) -> List<&2, Bool>:
  False{} <> True{} <> List.append(&2, Bool, Chain.key(c), Word.key(e))

# the start of the slots of the bucket of the height h, in the epoch e of c
def Slot.bucket(c: Chain, e: U32, h: U32) -> List<&2, Bool>:
  List.append(&2, Bool, Slot.votes(c, e), Word.key(h))

# the slot of the node n's ballot in a bucket, below the bucket
def Slot.ballot(n: String) -> List<&2, Bool>:
  Tries.Trie.text(n)

# the slot of the node n's ballot at the place w
def Slot.vote(w: Where, n: String) -> List<&2, Bool>:
  match w:
    case Where{c, e, h}:
      List.append(&2, Bool, Slot.bucket(c, e, h), Slot.ballot(n))

# the slot of the fact where the request i was decided
def Slot.where(i: Id) -> List<&2, Bool>:
  True{} <> False{} <> Id.key(i)

# the start of the slots of the facts where the epochs of the line c began
def Slot.epochs(c: Chain) -> List<&2, Bool>:
  True{} <> True{} <> False{} <> Chain.key(c)

# the slot of the fact where the epoch e of the line c began
def Slot.epoch(c: Chain, e: U32) -> List<&2, Bool>:
  List.append(&2, Bool, Slot.epochs(c), Word.key(e))

# the slot of the fact where the line c was made
def Slot.made(c: Chain) -> List<&2, Bool>:
  True{} <> True{} <> True{} <> Chain.key(c)

# Equality
# --------

# a and b are the same request
def Id.is_eq(a: Id, b: Id) -> Bool:
  match a b:
    case Id{w1, r1} Id{w2, r2}:
      Bool.and(String.eq(w1, w2), String.eq(r1, r2))

# a and b are the same keys below a root
def Sub.is_eq(a: Maybe<&2, List<&2, Bool>>, b: Maybe<&2, List<&2, Bool>>) -> Bool:
  Shared.Maybe.is_eq(~List<&2, Bool>, ~Shared.List.is_eq(~Bool, ~Shared.Bool.is_eq), a, b)

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof's statement, or code that the laws split on, keeps each and/or as one value
# a and b are the same line
def Chain.is_eq(a: Chain, b: Chain) -> Bool:
  match a b:
    case Chain{i1, k1} Chain{i2, k2}:
      Bool.and(Id.is_eq(i1, i2), Sub.is_eq(k1, k2))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# a and b are the same owners
def Owners.is_eq(a: List<&2, String>, b: List<&2, String>) -> Bool:
  Shared.List.is_eq(~String, ~String.eq, a, b)

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof's statement, or code that the laws split on, keeps each and/or as one value
# a and b are the same views
def View.is_eq(a: View, b: View) -> Bool:
  match a b:
    case View.root{x} View.root{y}:
      Owners.is_eq(x, y)
    case View.on{c1, o1, m1} View.on{c2, o2, m2}:
      Bool.and(
        Chain.is_eq(c1, c2),
        Bool.and(Shared.Maybe.is_eq(~List<&2, String>, ~Owners.is_eq, o1, o2), Sub.is_eq(m1, m2))
      )
    case _ _:
      False{}
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof's statement, or code that the laws split on, keeps each and/or as one value
# a and b are the same vote
def Vote.is_eq(a: Vote, b: Vote) -> Bool:
  match a b:
    case Vote{i1, k1, v1} Vote{i2, k2, v2}:
      Bool.and(Id.is_eq(i1, i2), Bool.and(Shared.Bool.is_eq(k1, k2), View.is_eq(v1, v2)))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# a and b are the same place
def Where.is_eq(a: Where, b: Where) -> Bool:
  match a b:
    case Where{c1, e1, h1} Where{c2, e2, h2}:
      Bool.and(Chain.is_eq(c1, c2), Bool.and(U32.is_eq(e1, e2), U32.is_eq(h1, h2)))

# a and b are the same entry, when same compares changes
def Entry.is_eq(~Q: Data, ~same: Q -> Q -> Bool, a: Entry<Q>, b: Entry<Q>) -> Bool:
  match a b:
    case Entry.ask{i1, t1, q1} Entry.ask{i2, t2, q2}:
      Bool.and(Id.is_eq(i1, i2), Bool.and(String.eq(t1, t2), same(q1, q2)))
    case Entry.vote{v1} Entry.vote{v2}:
      Vote.is_eq(v1, v2)
    case Entry.at{w1} Entry.at{w2}:
      Where.is_eq(w1, w2)
    case _ _:
      False{}

# The state
# ---------

# what a ledger of changes Q holds: the cell of each slot
def State(-Q: Data) -> Data:
  Tries.Trie<Cells.Cell<Entry<Q>>>

# a ledger that holds nothing yet
def State.empty(~Q: Data) -> State(Q):
  Tries.Trie.new(Cells.Cell<Entry<Q>>)

# what a holder of a and of b holds: a sync
def State.join(~Q: Data, ~same: Q -> Q -> Bool, a: State(Q), b: State(Q)) -> State(Q):
  Tries.Trie.union(
    ~Cells.Cell<Entry<Q>>,
    ~Cells.Cell.join(~Entry<Q>, ~Entry.is_eq(~Q, ~same)),
    a,
    b
  )

# what a holder of r lacks of s: what a sync from s to r sends
def State.missing(~Q: Data, ~same: Q -> Q -> Bool, s: State(Q), r: State(Q)) -> State(Q):
  Tries.Trie.minus(
    ~Cells.Cell<Entry<Q>>,
    ~Cells.Cell.is_eq(~Entry<Q>, ~Entry.is_eq(~Q, ~same)),
    s,
    r
  )

# no entry of t contradicts one of s
def State.agrees(~Q: Data, ~same: Q -> Q -> Bool, s: State(Q), t: State(Q)) -> Bool:
  Cells.Cell.agrees(~Entry<Q>, ~Entry.is_eq(~Q, ~same), s, t)

# the cell of the slot k in s
def State.get(~Q: Data, s: State(Q), k: List<&2, Bool>) -> Maybe<&2, Cells.Cell<Entry<Q>>>:
  Tries.Trie.get(Cells.Cell<Entry<Q>>, s, k)

# the slots of s that start with k, under the rest of their keys
def State.under(~Q: Data, s: State(Q), k: List<&2, Bool>) -> State(Q):
  Tries.Trie.under(Cells.Cell<Entry<Q>>, s, k)

# a ledger that holds only the entry e, in the slot k
def State.one(~Q: Data, k: List<&2, Bool>, e: Entry<Q>) -> State(Q):
  Tries.Trie.one(Cells.Cell<Entry<Q>>, k, Cells.one{e})

# s with the entry e in the slot k
def State.put(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  s: State(Q),
  k: List<&2, Bool>,
  e: Entry<Q>
) -> State(Q):
  State.join(~Q, ~same, s, State.one(~Q, k, e))

# the value of a cell, when every holder agrees on it
def Cell.value(-V: Data, m: Maybe<&2, Cells.Cell<V>>) -> Maybe<&2, V>:
  match m:
    case Some{Cells.one{e}}:
      Some{e}
    case _:
      None{}

# the entry of the slot k of s, when every holder agrees on it
def State.entry(~Q: Data, s: State(Q), k: List<&2, Bool>) -> Maybe<&2, Entry<Q>>:
  Cell.value(Entry<Q>, State.get(~Q, s, k))

# a request that a ledger holds: its time and change
type Asked<-Q: Data> is Data:
  Asked{time: String, ask: Q}

# the request in the entry m
def Asked.of(~Q: Data, m: Maybe<&2, Entry<Q>>) -> Maybe<&2, Asked<Q>>:
  match m:
    case Some{Entry.ask{i, t, q}}:
      Some{Asked{t, q}}
    case _:
      None{}

# the request i, when s holds it
def State.asked(~Q: Data, s: State(Q), i: Id) -> Maybe<&2, Asked<Q>>:
  Asked.of(~Q, State.entry(~Q, s, Slot.ask(i)))

# the place in the entry m, when it is a fact
def Where.of(~Q: Data, m: Maybe<&2, Entry<Q>>) -> Maybe<&2, Where>:
  match m:
    case Some{Entry.at{w}}:
      Some{w}
    case _:
      None{}

# Buckets
# -------

# the ballot of a cell of a bucket: a vote, void when it holds anything else,
# none when it is empty
def Entry.ballot(~Q: Data, m: Maybe<&2, Cells.Cell<Entry<Q>>>) -> Quorums.Ballot(Vote):
  match m:
    case None{}:
      None{}
    case Some{Cells.one{Entry.vote{v}}}:
      Some{Some{v}}
    case Some{c}:
      Some{None{}}

# the ballots of the nodes ms in the bucket b, each read once
def Bucket.ballots(~Q: Data, +b: State(Q), ms: List<&2, String>) -> List<&2, Quorums.Ballot(Vote)>:
  match ms:
    case Nil{}:
      []
    case Con{m, r}:
      Entry.ballot(~Q, State.get(~Q, b, Slot.ballot(m))) <> Bucket.ballots(~Q, b, r)

# what the ballots of ms in the bucket b decide
def Bucket.decide(~Q: Data, b: State(Q), ms: List<&2, String>) -> Maybe<&2, Vote>:
  Quorums.Quorum.decide(~Vote, ~Vote.is_eq, Bucket.ballots(~Q, b, ms))

# the bucket b of owners ms is decided
def Bucket.decided(~Q: Data, ms: List<&2, String>, b: State(Q)) -> Bool:
  Maybe.is_some(&2, Vote, Bucket.decide(~Q, b, ms))

# the bucket of the place w in s
def State.bucket(~Q: Data, s: State(Q), w: Where) -> State(Q):
  match w:
    case Where{c, e, h}:
      State.under(~Q, s, Slot.bucket(c, e, h))

# what the owners ms decide at the place w of s
def State.decide(~Q: Data, s: State(Q), w: Where, ms: List<&2, String>) -> Maybe<&2, Vote>:
  Bucket.decide(~Q, State.bucket(~Q, s, w), ms)

# Epochs
# ------

# the owners of a view that starts a store
def Root.owners.view(v: View) -> Maybe<&2, List<&2, String>>:
  match v:
    case View.root{ms}:
      Some{ms}
    case _:
      None{}

# the owners in the view v of a request that starts a store
def Root.owners.of(
  ~Q: Data,
  ~view: Q -> View,
  m: Maybe<&2, Asked<Q>>
) -> Maybe<&2, List<&2, String>>:
  match m:
    case Some{Asked{t, q}}:
      Root.owners.view(view(q))
    case None{}:
      None{}

# the owners of the vote m, when it takes a request of the line c that gives
# it owners
def Owners.of_vote(c: Chain, m: Maybe<&2, Vote>) -> Maybe<&2, List<&2, String>>:
  match m:
    case Some{Vote{i, True{}, View.on{c2, Some{os}, mk}}}:
      Shared.Bool.when(Maybe<&2, List<&2, String>>, Chain.is_eq(c2, c), u => Some{os}, u => None{})
    case _:
      None{}

# the owners of the epoch after e of c, from the fact m where it began, whose
# owners are ms: the owners that the step there gives
def Epoch.next.of(
  ~Q: Data,
  s: State(Q),
  +c: Chain,
  +e: U32,
  ms: List<&2, String>,
  m: Maybe<&2, Where>
) -> Maybe<&2, List<&2, String>>:
  match m:
    case Some{Where{c2, e2, h}}:
      Shared.Bool.when(
        Maybe<&2, List<&2, String>>,
        Bool.and(Chain.is_eq(c2, c), U32.is_eq(e2, e)),
        u => Owners.of_vote(c, State.decide(~Q, s, Where{c, e, h}, ms)),
        u => None{}
      )
    case None{}:
      None{}

# the owners of the epoch after e of c, whose owners are ms
def Epoch.next(
  ~Q: Data,
  +s: State(Q),
  +c: Chain,
  +e: U32,
  ms: List<&2, String>
) -> Maybe<&2, List<&2, String>>:
  Epoch.next.of(~Q, s, c, e, ms, Where.of(~Q, State.entry(~Q, s, Slot.epoch(c, U32.inc(e)))))

# the owners of the epoch n after cur of c, whose owners are m
def Epoch.up(
  ~Q: Data,
  n: Nat,
  +s: State(Q),
  +c: Chain,
  +cur: U32,
  m: Maybe<&2, List<&2, String>>
) -> Maybe<&2, List<&2, String>>:
  match n m:
    case 0n w:
      w
    case 1n+p None{}:
      None{}
    case 1n+p Some{ms}:
      Epoch.up(~Q, p, s, c, U32.inc(cur), Epoch.next(~Q, s, c, cur, ms))

# the owners of the root line of r: those of the request that starts it
def Root.owners(~Q: Data, ~view: Q -> View, s: State(Q), r: Id) -> Maybe<&2, List<&2, String>>:
  Root.owners.of(~Q, ~view, State.asked(~Q, s, r))

# the owners of the epoch e of the root line of r
def Root.at(
  ~Q: Data,
  ~view: Q -> View,
  +s: State(Q),
  +r: Id,
  e: U32
) -> Maybe<&2, List<&2, String>>:
  Epoch.up(~Q, U32.to_nat(e), s, Chain{r, None{}}, 0, Root.owners(~Q, ~view, s, r))

# the vote m makes the line of the key k
def Vote.makes(k: List<&2, Bool>, m: Maybe<&2, Vote>) -> Bool:
  match m:
    case Some{Vote{i, True{}, View.on{c, o, Some{k2}}}}:
      Shared.List.is_eq(~Bool, ~Shared.Bool.is_eq, k2, k)
    case _:
      False{}

# the owners ms of the root's epoch at w, when the step there makes the line of k
def Made.check(
  ~Q: Data,
  s: State(Q),
  w: Where,
  k: List<&2, Bool>,
  m: Maybe<&2, List<&2, String>>
) -> Maybe<&2, List<&2, String>>:
  match m:
    case Some{+ms}:
      Shared.Bool.when(
        Maybe<&2, List<&2, String>>,
        Vote.makes(k, State.decide(~Q, s, w, ms)),
        u => Some{ms},
        u => None{}
      )
    case None{}:
      None{}

# the first owners of the line of the key k below the root of r, from the
# fact m where it was made: the owners of the root's epoch there
def Made.owners(
  ~Q: Data,
  ~view: Q -> View,
  +s: State(Q),
  +r: Id,
  k: List<&2, Bool>,
  m: Maybe<&2, Where>
) -> Maybe<&2, List<&2, String>>:
  match m:
    case Some{Where{+c2, +e, h}}:
      Shared.Bool.when(
        Maybe<&2, List<&2, String>>,
        Chain.is_eq(c2, Chain{r, None{}}),
        u => Made.check(~Q, s, Where{c2, e, h}, k, Root.at(~Q, ~view, s, r, e)),
        u => None{}
      )
    case None{}:
      None{}

# the owners of the first epoch of the line c
def Line.first(~Q: Data, ~view: Q -> View, +s: State(Q), +c: Chain) -> Maybe<&2, List<&2, String>>:
  match c:
    case Chain{r, None{}}:
      Root.owners(~Q, ~view, s, r)
    case Chain{+r, Some{+k}}:
      Made.owners(
        ~Q,
        ~view,
        s,
        r,
        k,
        Where.of(~Q, State.entry(~Q, s, Slot.made(Chain{r, Some{k}})))
      )

# the owners of the epoch e of the line c
def Line.owners(
  ~Q: Data,
  ~view: Q -> View,
  +s: State(Q),
  +c: Chain,
  e: U32
) -> Maybe<&2, List<&2, String>>:
  Epoch.up(~Q, U32.to_nat(e), s, c, 0, Line.first(~Q, ~view, s, c))

# the epoch of a line now, and its owners
type Now is Data:
  Now{epoch: U32, owners: List<&2, String>}

# the epoch of c now, from cur whose owners are ms and the owners m of the
# epoch after it; f epochs at most
def Epoch.last(
  ~Q: Data,
  f: Nat,
  +s: State(Q),
  +c: Chain,
  cur: U32,
  ms: List<&2, String>,
  m: Maybe<&2, List<&2, String>>
) -> Now:
  match f m:
    case 1n+p Some{+os}:
      +up = U32.inc(cur)
      Epoch.last(~Q, p, s, c, up, os, Epoch.next(~Q, s, c, up, os))
    case g w:
      Now{cur, ms}

# the epoch of the line c now, from the owners m of its first epoch
def Line.now.of(
  ~Q: Data,
  +s: State(Q),
  +c: Chain,
  m: Maybe<&2, List<&2, String>>
) -> Maybe<&2, Now>:
  match m:
    case Some{+ms}:
      Some{
        Epoch.last(
          ~Q,
          Tries.Trie.size(Cells.Cell<Entry<Q>>, State.under(~Q, s, Slot.epochs(c))),
          s,
          c,
          0,
          ms,
          Epoch.next(~Q, s, c, 0, ms)
        )
      }
    case None{}:
      None{}

# the epoch of the line c now, if the line exists: a step for each new epoch
def Line.now(~Q: Data, ~view: Q -> View, +s: State(Q), +c: Chain) -> Maybe<&2, Now>:
  Line.now.of(~Q, s, c, Line.first(~Q, ~view, s, c))

# Tips
# ----

# the end of a line: its epoch, its owners, the height that its owners vote
# at next, and the place of its last step in the epoch, if any
type Tip is Data:
  Tip{epoch: U32, owners: List<&2, String>, next: U32, last: Maybe<&2, Where>}

# the tip of the epoch e of c, whose owners are ms, from the highest key of a
# decided bucket m
def Tip.of(c: Chain, +e: U32, ms: List<&2, String>, m: Maybe<&2, List<&2, Bool>>) -> Tip:
  match m:
    case Some{k}:
      +h = Word.of_key(k, 0)
      Tip{e, ms, U32.inc(h), Some{Where{c, e, h}}}
    case None{}:
      Tip{e, ms, 0, None{}}

# the highest decided height of the epoch e of c, whose owners are ms
def Line.top(
  ~Q: Data,
  s: State(Q),
  c: Chain,
  e: U32,
  ms: List<&2, String>
) -> Maybe<&2, List<&2, Bool>>:
  Tries.Trie.top(
    ~Cells.Cell<Entry<Q>>,
    ~List<&2, String>,
    ~(os => b => Bucket.decided(~Q, os, b)),
    32n,
    State.under(~Q, s, Slot.votes(c, e)),
    ms
  )

# the tip of c, once the epoch now (m) is known
def Line.tip.of(~Q: Data, s: State(Q), +c: Chain, m: Maybe<&2, Now>) -> Maybe<&2, Tip>:
  match m:
    case Some{Now{+e, +ms}}:
      Some{Tip.of(c, e, ms, Line.top(~Q, s, c, e, ms))}
    case None{}:
      None{}

# the tip of the line c, if it exists: a descent of 32 heights, not a walk
def Line.tip(~Q: Data, ~view: Q -> View, +s: State(Q), +c: Chain) -> Maybe<&2, Tip>:
  Line.tip.of(~Q, s, c, Line.now(~Q, ~view, s, c))

# Status
# ------

# the vote m, when it is for the request i
def Vote.for(i: Id, m: Maybe<&2, Vote>) -> Maybe<&2, Vote>:
  match m:
    case Some{Vote{+j, k, v}}:
      Shared.Bool.when(Maybe<&2, Vote>, Id.is_eq(j, i), u => Some{Vote{j, k, v}}, u => None{})
    case None{}:
      None{}

# Where.check once the owners m of the epoch are known
def Where.check.of(
  ~Q: Data,
  s: State(Q),
  i: Id,
  w: Where,
  m: Maybe<&2, List<&2, String>>
) -> Maybe<&2, Vote>:
  match m:
    case Some{ms}:
      Vote.for(i, State.decide(~Q, s, w, ms))
    case None{}:
      None{}

# the vote that decided i at the place m, when the step there is for i
def Where.check(
  ~Q: Data,
  ~view: Q -> View,
  +s: State(Q),
  i: Id,
  m: Maybe<&2, Where>
) -> Maybe<&2, Vote>:
  match m:
    case Some{Where{+c, +e, h}}:
      Where.check.of(~Q, s, i, Where{c, e, h}, Line.owners(~Q, ~view, s, c, e))
    case None{}:
      None{}

# the vote that decided the request i, when s holds where and it checks
def State.decided(~Q: Data, ~view: Q -> View, +s: State(Q), +i: Id) -> Maybe<&2, Vote>:
  Where.check(~Q, ~view, s, i, Where.of(~Q, State.entry(~Q, s, Slot.where(i))))

# where a request is. Done: a step decided it, and took it or refused it as
# stale. Pending: no step decided it yet. Refused: it is contradicted. NotSeen:
# the ledger does not hold it.
type Status is Data:
  Status.done{takes: Bool}
  Status.pending{}
  Status.refused{}
  Status.not_seen{}

# the status of a request whose change has the view v, decided by the vote m
def Status.of.view(v: View, m: Maybe<&2, Vote>) -> Status:
  match v m:
    case View.root{ms} w:
      Status.done{True{}}
    case View.on{c, o, mk} Some{Vote{j, k, u}}:
      Status.done{k}
    case View.on{c, o, mk} None{}:
      Status.pending{}

# the status of the request i, whose cell is m
def Status.of(
  ~Q: Data,
  ~view: Q -> View,
  s: State(Q),
  i: Id,
  m: Maybe<&2, Cells.Cell<Entry<Q>>>
) -> Status:
  match m:
    case None{}:
      Status.not_seen{}
    case Some{Cells.many{}}:
      Status.refused{}
    case Some{Cells.one{Entry.ask{j, t, q}}}:
      Status.of.view(view(q), State.decided(~Q, ~view, s, i))
    case Some{Cells.one{e}}:
      Status.not_seen{}

# where the request i is
def State.status(~Q: Data, ~view: Q -> View, +s: State(Q), +i: Id) -> Status:
  Status.of(~Q, ~view, s, i, State.get(~Q, s, Slot.ask(i)))

# Changes
# -------

# the epoch of the place w
def Where.epoch(w: Where) -> U32:
  match w:
    case Where{c, e, h}:
      e

# Fact.put once the cell m of the slot is known
def Fact.put.of(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  s: State(Q),
  k: List<&2, Bool>,
  w: Where,
  m: Maybe<&2, Cells.Cell<Entry<Q>>>
) -> State(Q):
  match m:
    case None{}:
      State.put(~Q, ~same, s, k, Entry.at{w})
    case Some{x}:
      s

# s with the fact w in the slot k, unless the slot holds something already
def Fact.put(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  +s: State(Q),
  +k: List<&2, Bool>,
  w: Where
) -> State(Q):
  Fact.put.of(~Q, ~same, s, k, w, State.get(~Q, s, k))

# s with the facts of a step at w that takes (k) a request of the view v: where
# the epoch after it begins, when it gives owners; where the line that it
# makes was made
def Settle.view(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  s: State(Q),
  +w: Where,
  k: Bool,
  v: View
) -> State(Q):
  match k v:
    case True{} View.on{+c, Some{os}, mk}:
      Fact.put(~Q, ~same, s, Slot.epoch(c, U32.inc(Where.epoch(w))), w)
    case True{} View.on{Chain{r, b}, None{}, Some{key}}:
      Fact.put(~Q, ~same, s, Slot.made(Chain{r, Some{key}}), w)
    case x y:
      s

# s with the facts of the decision m at w
def Settle.of(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  s: State(Q),
  +w: Where,
  m: Maybe<&2, Vote>
) -> State(Q):
  match m:
    case Some{Vote{i, k, v}}:
      Settle.view(~Q, ~same, Fact.put(~Q, ~same, s, Slot.where(i), w), w, k, v)
    case None{}:
      s

# s with the facts of what the owners ms decide at w, if anything
def State.settle(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  +s: State(Q),
  +w: Where,
  ms: List<&2, String>
) -> State(Q):
  Settle.of(~Q, ~same, s, w, State.decide(~Q, s, w, ms))

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof's statement, or code that the laws split on, keeps each and/or as one value
# the node n may vote at w, whose owners are ms: it is one, and has not voted
def Vote.may(~Q: Data, +n: String, s: State(Q), w: Where, ms: List<&2, String>) -> Bool:
  Bool.and(
    List.contains(~String, ~String.eq, ms, n),
    Maybe.is_none(&2, Cells.Cell<Entry<Q>>, State.get(~Q, s, Slot.vote(w, n)))
  )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the verdict on the request q, whose view is v, after the step at last:
# refused when it makes a line that exists, else judge's (none: wait)
def Vote.verdict(
  ~Q: Data,
  ~view: Q -> View,
  ~judge: State(Q) -> Q -> Maybe<&2, Where> -> Maybe<&2, Bool>,
  +s: State(Q),
  q: Q,
  v: View,
  last: Maybe<&2, Where>
) -> Maybe<&2, Bool>:
  match v:
    case View.on{Chain{r, b}, o, Some{m}}:
      Shared.Bool.when(
        Maybe<&2, Bool>,
        Maybe.is_none(&2, List<&2, String>, Line.first(~Q, ~view, s, Chain{r, Some{m}})),
        u => judge(s, q, last),
        u => Some{False{}}
      )
    case w:
      judge(s, q, last)

# s with the vote for i of the view v (when held), with the verdict m (none:
# no vote)
def Vote.put(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  held: Bool,
  m: Maybe<&2, Bool>,
  s: State(Q),
  k: List<&2, Bool>,
  i: Id,
  v: View
) -> State(Q):
  match held m:
    case True{} Some{x}:
      State.put(~Q, ~same, s, k, Entry.vote{Vote{i, x, v}})
    case h w:
      s

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof's statement, or code that the laws split on, keeps each and/or as one value
# s after the node n votes for the request i of q, whose view v changes the
# line c, at the tip m of c, when it may; then the facts of what is decided
def Vote.cast(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~view: Q -> View,
  ~judge: State(Q) -> Q -> Maybe<&2, Where> -> Maybe<&2, Bool>,
  +n: String,
  +s: State(Q),
  c: Chain,
  +i: Id,
  q: Q,
  +v: View,
  m: Maybe<&2, Tip>
) -> State(Q):
  match m:
    case None{}:
      s
    case Some{Tip{e, +ms, h, last}}:
      +w = {Where{c, e, h}: Where}
      State.settle(
        ~Q,
        ~same,
        Vote.put(
          ~Q,
          ~same,
          Bool.and(
            Vote.may(~Q, n, s, w, ms),
            Maybe.is_none(&2, Vote, State.decided(~Q, ~view, s, i))
          ),
          Vote.verdict(~Q, ~view, ~judge, s, q, v, last),
          s,
          Slot.vote(w, n),
          i,
          v
        ),
        w,
        ms
      )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# s after the node n votes for the request i of q, whose view is v
def Vote.ask(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~view: Q -> View,
  ~judge: State(Q) -> Q -> Maybe<&2, Where> -> Maybe<&2, Bool>,
  n: String,
  +s: State(Q),
  i: Id,
  q: Q,
  v: View
) -> State(Q):
  match v:
    case View.root{ms}:
      s
    case View.on{+c, o, mk}:
      Vote.cast(
        ~Q,
        ~same,
        ~view,
        ~judge,
        n,
        s,
        c,
        i,
        q,
        View.on{c, o, mk},
        Line.tip(~Q, ~view, s, c)
      )

# s after the node n took in the request i of q at the time t, whose cell in s
# is m: a request that s holds already changes nothing
def State.ask.fresh(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~view: Q -> View,
  ~judge: State(Q) -> Q -> Maybe<&2, Where> -> Maybe<&2, Bool>,
  n: String,
  s: State(Q),
  +i: Id,
  t: String,
  +q: Q,
  m: Maybe<&2, Cells.Cell<Entry<Q>>>
) -> State(Q):
  match m:
    case Some{x}:
      s
    case None{}:
      Vote.ask(
        ~Q,
        ~same,
        ~view,
        ~judge,
        n,
        State.put(~Q, ~same, s, Slot.ask(i), Entry.ask{i, t, q}),
        i,
        q,
        view(q)
      )

# s, after the node n took in the request i of q at the time t: the request,
# and n's vote on it when n owns its line and judge gives a verdict
def State.ask(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~view: Q -> View,
  ~judge: State(Q) -> Q -> Maybe<&2, Where> -> Maybe<&2, Bool>,
  n: String,
  +s: State(Q),
  +i: Id,
  t: String,
  q: Q
) -> State(Q):
  State.ask.fresh(~Q, ~same, ~view, ~judge, n, s, i, t, q, State.get(~Q, s, Slot.ask(i)))
