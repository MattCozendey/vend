import Base
import ../node/shared/shared/resources.bend as Resources
import ./shared/ledger.bend as Ledgers
import ./shared/rope.bend as Ropes
import ./shared/shared/quorum.bend as Quorums
import ./shared/shared/shared/cell.bend as Cells
import ./shared/shared/shared/code.bend as Codes
import ./shared/shared/shared/hash.bend as Hashes
import ./shared/shared/shared/seal.bend as Seals
import ./shared/shared/shared/shared.bend as Shared
import ./shared/shared/shared/trie.bend as Tries
import ./shared/shared/store.bend as Stores
import ./shared/shared/text.bend as Texts
import ./shared/tree.bend as Trees

# Replicas
# --------
# A replica is a node of a replicated machine: it holds a ledger that only
# grows, a head of each line that it follows, the requests that wait, and its
# keys. It is generic over the machine: what a request is, and what a request
# does to a line. src/node gives the machine and the kernel of Vend.

# a machine: its requests; when two are the same, and that this is equality;
# how a request arrives at a node; whether it changes who decides; and the key
# of the first key of a node in the content of a store
def Machine() -> Type:
  &Q: Data -> &same: (
    Q -> Q -> Bool
  ) -> Shared.Eq.Laws(Q, same)
    & ((Q -> Arrival) & ((Q -> Bool) & (String -> List<&2, U32>)))

# the requests of the machine m
def Machine.Q(m: Machine()) -> Data:
  match m:
    case Tuple{q, r}:
      q

# two requests of the machine m are the same
def Machine.same(m: Machine()) -> Machine.Q(m) -> Machine.Q(m) -> Bool:
  match m:
    case Tuple{q, Tuple{s, r}}:
      s

# the sameness of the machine m is equality
def Machine.laws(m: Machine()) -> Shared.Eq.Laws(Machine.Q(m), Machine.same(m)):
  match m:
    case Tuple{q, Tuple{s, Tuple{l, r}}}:
      l

# how a request of the machine m arrives
def Machine.arrival(m: Machine()) -> Machine.Q(m) -> Arrival:
  match m:
    case Tuple{q, Tuple{s, Tuple{l, Tuple{a, r}}}}:
      a

# a request of the machine m changes who decides
def Machine.governs(m: Machine()) -> Machine.Q(m) -> Bool:
  match m:
    case Tuple{q, Tuple{s, Tuple{l, Tuple{a, Tuple{g, k}}}}}:
      g

# the key of the first key of a node, in the content of a store of the machine
# m
def Machine.seal(m: Machine()) -> String -> List<&2, U32>:
  match m:
    case Tuple{q, Tuple{s, Tuple{l, Tuple{a, Tuple{g, k}}}}}:
      k

# who asks for a change, and when
type Envelope is Data:
  Envelope{id: String, writer: String, time: String}

# the request of e
def Envelope.of(e: Envelope) -> Ledgers.Id:
  match e:
    case Envelope{r, w, t}:
      Ledgers.Id{w, r}

# the time of e
def Envelope.time(e: Envelope) -> String:
  match e:
    case Envelope{r, w, t}:
      t

# the key of the branch n below its store: prefix-free
def Line.key(n: String) -> List<&2, Bool>:
  Tries.Trie.text(n)

# the chain of the branch l of the store r (none: the store's own chain)
def Line.chain(r: Ledgers.Id, l: Maybe<&2, String>) -> Ledgers.Chain:
  match l:
    case None{}:
      Ledgers.Chain{r, None{}}
    case Some{x}:
      Ledgers.Chain{r, Some{Line.key(x)}}

# what a line holds: the root of its content, the root of its log, the count
# of its versions, and the owners of its next step. A read of the count or of
# the owners costs no node of a tree
type Tip is Data:
  Tip{
    content: Maybe<&2, Hashes.Hash>,
    log: Maybe<&2, Hashes.Hash>,
    count: U32,
    owners: List<&2, String>
  }

# a node's head of a line: the line, the height of its next step, and the hash
# of its tip (none: the node waits for the store's step that makes the line)
type Head is Data:
  Head{store: Ledgers.Id, branch: Maybe<&2, String>, next: U32, tip: Maybe<&2, Hashes.Hash>}

# the key chain of one node in one store, as a node knows it: how many of its
# ballots the node holds, the place of the last one, the key that signs the
# next one, and the first key of the chain (the one that the store gave it)
type Keychain is Data:
  Keychain{count: U32, last: Maybe<&2, Ledgers.Where>, key: Hashes.Hash, first: Hashes.Hash}

# what a node keeps to seal its ballots and to check those of other nodes: its
# secret seed; the key chain of each node in each store (its own too); the
# requests that a writer connected to it asked for (an owner casts for a
# change of who decides only when it was asked at the owner itself); and the
# highest round of which it holds a ballot, for each height that has a round
# after the first
type Keys is Data:
  Keys{
    seed: Hashes.Hash,
    chains: Tries.Trie<Keychain>,
    asked: Tries.Trie<Unit>,
    rounds: Tries.Trie<Nat>
  }

# what a node holds: its ledger, which nodes replicate; its head of each line
# that it follows; the requests of each line that wait for a step; and its
# keys. Heads, waiting requests and keys are the node's own: no other node
# sends them
type Node<-Q: Data> is Data:
  Node{
    ledger: Ledgers.State(Q),
    heads: Tries.Trie<Head>,
    waiting: Tries.Trie<List<&2, Ledgers.Id>>,
    keys: Keys
  }

# the ledger of s
def State.ledger(~mach: Machine(), s: Node<Machine.Q(mach)>) -> Ledgers.State(Machine.Q(mach)):
  match s:
    case Node{l, hs, ws, ks}:
      l

# the heads of s
def State.heads(~mach: Machine(), s: Node<Machine.Q(mach)>) -> Tries.Trie<Head>:
  match s:
    case Node{l, hs, ws, ks}:
      hs

# the requests of s that wait for a step, by line
def State.waiting(~mach: Machine(), s: Node<Machine.Q(mach)>) -> Tries.Trie<List<&2, Ledgers.Id>>:
  match s:
    case Node{l, hs, ws, ks}:
      ws

# the keys of s
def State.keys(~mach: Machine(), s: Node<Machine.Q(mach)>) -> Keys:
  match s:
    case Node{l, hs, ws, ks}:
      ks

# s with the ledger l
def State.led(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  l: Ledgers.State(Machine.Q(mach))
) -> Node<Machine.Q(mach)>:
  match s:
    case Node{old, hs, ws, ks}:
      Node{l, hs, ws, ks}

# s with the keys ks
def State.keyed(~mach: Machine(), s: Node<Machine.Q(mach)>, ks: Keys) -> Node<Machine.Q(mach)>:
  match s:
    case Node{l, hs, ws, old}:
      Node{l, hs, ws, ks}

# a node that holds nothing yet, with the secret seed
def Node.empty(~mach: Machine(), seed: Hashes.Hash) -> Node<Machine.Q(mach)>:
  Node{
    Ledgers.State.empty(~Machine.Q(mach)),
    Tries.Trie.new(Head),
    Tries.Trie.new(List<&2, Ledgers.Id>),
    Keys{seed, Tries.Trie.new(Keychain), Tries.Trie.new(Unit), Tries.Trie.new(Nat)}
  }

# the words that s holds under the hash h
def Store.fetch(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  h: Hashes.Hash
) -> Maybe<&2, List<&2, U32>>:
  Ledgers.State.data(~Machine.Q(mach), State.ledger(~mach, s), h)

# s with the words ds as data, each under its hash
def State.keep(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  ds: List<&2, List<&2, U32>>
) -> Node<Machine.Q(mach)>:
  State.led(
    ~mach,
    s,
    Ledgers.State.put_datas(~Machine.Q(mach), ~Machine.same(mach), ds, State.ledger(~mach, s))
  )

# the request i, when s holds it
def Node.asked(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  i: Ledgers.Id
) -> Maybe<&2, Ledgers.Asked<Machine.Q(mach)>>:
  Ledgers.State.asked(~Machine.Q(mach), State.ledger(~mach, s), i)

# what the tree whose root is h holds under the key k, in the store s
def Node.get(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  h: Maybe<&2, Hashes.Hash>,
  k: List<&2, U32>
) -> Maybe<&2, List<&2, U32>>:
  Trees.Tree.get(~Node<Machine.Q(mach)>, ~Store.fetch(~mach), s, h, k)

# the tree whose root is h with the key k set to x
def Node.set(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  h: Maybe<&2, Hashes.Hash>,
  k: List<&2, U32>,
  x: List<&2, U32>
) -> Maybe<&2, Trees.Put>:
  Trees.Tree.set(~Node<Machine.Q(mach)>, ~Store.fetch(~mach), s, h, k, x)

# what a read of the key k finds in the tree whose root is h
def Node.look(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  h: Maybe<&2, Hashes.Hash>,
  k: List<&2, U32>
) -> Trees.Look:
  Trees.Tree.look(~Node<Machine.Q(mach)>, ~Store.fetch(~mach), s, h, k)

# what a look knows: the value, or that there is none (none: it lacks a node,
# and cannot tell)
def Look.known(l: Trees.Look) -> Maybe<&2, Maybe<&2, List<&2, U32>>>:
  match l:
    case Trees.Look.Found{v}:
      Some{Some{v}}
    case Trees.Look.Absent{}:
      Some{None{}}
    case Trees.Look.Missing{x}:
      None{}

# what the tree whose root is h holds under the key k, or that it holds
# nothing there (none: the node lacks a node of the tree). A judge reads with
# this: it refuses only on what it knows, and waits for what it lacks
def Node.find(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  h: Maybe<&2, Hashes.Hash>,
  k: List<&2, U32>
) -> Maybe<&2, Maybe<&2, List<&2, U32>>>:
  Look.known(Node.look(~mach, s, h, k))

# the value of a read that is the whole of some words
def Read.whole(-A: Data, m: Maybe<&2, Codes.Read<A>>) -> Maybe<&2, A>:
  match m:
    case Some{Codes.Read{x, Nil{}}}:
      Some{x}
    case _:
      None{}

# the words of the tip t
def Tip.words(t: Tip) -> List<&2, U32>:
  match t:
    case Tip{c, l, n, os}:
      Codes.Code.maybe(
        ~Hashes.Hash,
        ~Hashes.Hash.code,
        c,
        Codes.Code.maybe(
          ~Hashes.Hash,
          ~Hashes.Hash.code,
          l,
          Codes.Code.token(n, Ledgers.Owners.code(os, []))
        )
      )

# the tip that some words are, when they are one
def Tip.read(ws: List<&2, U32>) -> Maybe<&2, Tip>:
  Read.whole(
    Tip,
    Codes.Code.four.read(
      ~Maybe<&2, Hashes.Hash>,
      ~Maybe<&2, Hashes.Hash>,
      ~U32,
      ~List<&2, String>,
      ~Tip,
      ~(m => Codes.Code.maybe.read(~Hashes.Hash, ~Hashes.Hash.code.read, m)),
      ~(m => Codes.Code.maybe.read(~Hashes.Hash, ~Hashes.Hash.code.read, m)),
      ~Codes.Code.token.read,
      ~Ledgers.Owners.code.read,
      c => l => n => os => Tip{c, l, n, os},
      ws
    )
  )

# the hash of the tip t: what a ballot names
def Tip.hash(t: Tip) -> Hashes.Hash:
  Hashes.Sha.hash(Tip.words(t))

# the tip that s holds under the hash h
def Tip.at(~mach: Machine(), s: Node<Machine.Q(mach)>, h: Hashes.Hash) -> Maybe<&2, Tip>:
  Maybe.bind(&2, List<&2, U32>, Tip, Store.fetch(~mach, s, h), ws => Tip.read(ws))

# the content of the tip t
def Tip.content(t: Tip) -> Maybe<&2, Hashes.Hash>:
  match t:
    case Tip{c, l, n, os}:
      c

# the log of the tip t
def Tip.log(t: Tip) -> Maybe<&2, Hashes.Hash>:
  match t:
    case Tip{c, l, n, os}:
      l

# the count of versions of a line at the tip t
def Tip.count(t: Tip) -> U32:
  match t:
    case Tip{c, l, n, os}:
      n

# the owners of the next step of a line at the tip t
def Tip.owners(t: Tip) -> List<&2, String>:
  match t:
    case Tip{c, l, n, os}:
      os

# the key of the outcome of the request i
def Log.out(i: Ledgers.Id) -> List<&2, U32>:
  2 <> Ledgers.Id.code(i, [])

# the key of the version of the number n
def Log.version(n: U32) -> List<&2, U32>:
  [3, n]

# the key of the mark m
def Log.mark(m: String) -> List<&2, U32>:
  4 <> Codes.Code.text(m, [])

# the key of the first tip of the branch b, in the log of its store
def Log.start(b: String) -> List<&2, U32>:
  5 <> Codes.Code.text(b, [])

# the outcome of a request: its owners refused it as stale, or took it as the
# version of a number
type Out is Data:
  Out.Stale{}
  Out.Taken{number: U32}

# the words of the outcome o
def Out.words(o: Out) -> List<&2, U32>:
  match o:
    case Out.Stale{}:
      [0]
    case Out.Taken{n}:
      [1, n]

# the outcome that some words are
def Out.read(ws: List<&2, U32>) -> Maybe<&2, Out>:
  match ws:
    case Con{0, Nil{}}:
      Some{Out.Stale{}}
    case Con{1, Con{n, Nil{}}}:
      Some{Out.Taken{n}}
    case _:
      None{}

# a version: the request that made it, and the root of the content after it
type Version is Data:
  Version{id: Ledgers.Id, root: Maybe<&2, Hashes.Hash>}

# the words of the version v
def Version.words(v: Version) -> List<&2, U32>:
  match v:
    case Version{i, r}:
      Ledgers.Id.code(i, Codes.Code.maybe(~Hashes.Hash, ~Hashes.Hash.code, r, []))

# the version that some words are
def Version.read(ws: List<&2, U32>) -> Maybe<&2, Version>:
  Read.whole(
    Version,
    Codes.Code.two.read(
      ~Ledgers.Id,
      ~Maybe<&2, Hashes.Hash>,
      ~Version,
      ~Ledgers.Id.code.read,
      ~(m => Codes.Code.maybe.read(~Hashes.Hash, ~Hashes.Hash.code.read, m)),
      i => r => Version{i, r},
      ws
    )
  )

# the request of the version v
def Version.id(v: Version) -> Ledgers.Id:
  match v:
    case Version{i, r}:
      i

# the root of the content of the version v
def Version.root(v: Version) -> Maybe<&2, Hashes.Hash>:
  match v:
    case Version{i, r}:
      r

# the outcome of the request i on a line at the tip t (none: no step decided
# it yet)
def Line.out(~mach: Machine(), s: Node<Machine.Q(mach)>, t: Tip, i: Ledgers.Id) -> Maybe<&2, Out>:
  Maybe.bind(&2, List<&2, U32>, Out, Node.get(~mach, s, Tip.log(t), Log.out(i)), ws => Out.read(ws))

# the version of the number n of a line at the tip t
def Line.version(~mach: Machine(), s: Node<Machine.Q(mach)>, t: Tip, n: U32) -> Maybe<&2, Version>:
  Maybe.bind(
    &2,
    List<&2, U32>,
    Version,
    Node.get(~mach, s, Tip.log(t), Log.version(n)),
    ws => Version.read(ws)
  )

# the version that the mark m names on a line at the tip t
def Line.mark(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  t: Tip,
  m: String
) -> Maybe<&2, Ledgers.Id>:
  Maybe.bind(
    &2,
    List<&2, U32>,
    Ledgers.Id,
    Node.get(~mach, s, Tip.log(t), Log.mark(m)),
    ws => Read.whole(Ledgers.Id, Ledgers.Id.code.read(ws))
  )

# the node's head of the line c, if it follows c
def Node.head_of(~mach: Machine(), s: Node<Machine.Q(mach)>, c: Ledgers.Chain) -> Maybe<&2, Head>:
  Tries.Trie.get(Head, State.heads(~mach, s), Ledgers.Chain.key(c))

# the tip of the head h, when s holds it
def Head.tip(~mach: Machine(), s: Node<Machine.Q(mach)>, h: Head) -> Maybe<&2, Tip>:
  match h:
    case Head{r, b, n, t}:
      Maybe.bind(&2, Hashes.Hash, Tip, t, x => Tip.at(~mach, s, x))

# what the line c holds now, as the node knows it
def Node.tip(~mach: Machine(), +s: Node<Machine.Q(mach)>, c: Ledgers.Chain) -> Maybe<&2, Tip>:
  Maybe.bind(&2, Head, Tip, Node.head_of(~mach, s, c), h => Head.tip(~mach, s, h))

# what the log of the head h holds under the key k
def Head.get(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  h: Head,
  k: List<&2, U32>
) -> Maybe<&2, List<&2, U32>>:
  Maybe.bind(&2, Tip, List<&2, U32>, Head.tip(~mach, s, h), t => Node.get(~mach, s, Tip.log(t), k))

# what the log of the line c holds under the key k, as the node knows it
def Line.get(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  k: List<&2, U32>
) -> Maybe<&2, List<&2, U32>>:
  Maybe.bind(&2, Head, List<&2, U32>, Node.head_of(~mach, s, c), h => Head.get(~mach, s, h, k))

# the change of the request a
def Asked.ask(~mach: Machine(), a: Ledgers.Asked<Machine.Q(mach)>) -> Machine.Q(mach):
  match a:
    case Ledgers.Asked{t, q}:
      q

# the outcome of the request i on the line c, as the node knows it
def Chain.out(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  i: Ledgers.Id
) -> Maybe<&2, Out>:
  Maybe.bind(&2, List<&2, U32>, Out, Line.get(~mach, s, c, Log.out(i)), ws => Out.read(ws))

# the version of the number n of the line c, as the node knows it
def Chain.version(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  n: U32
) -> Maybe<&2, Version>:
  Maybe.bind(
    &2,
    List<&2, U32>,
    Version,
    Line.get(~mach, s, c, Log.version(n)),
    ws => Version.read(ws)
  )

# the version that the mark m names on the line c, as the node knows it
def Chain.mark(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  m: String
) -> Maybe<&2, Ledgers.Id>:
  Maybe.bind(
    &2,
    List<&2, U32>,
    Ledgers.Id,
    Line.get(~mach, s, c, Log.mark(m)),
    ws => Read.whole(Ledgers.Id, Ledgers.Id.code.read(ws))
  )

# trees being written: the root, and the node that holds what was written
type Work<-Q: Data> is Data:
  Work{state: Node<Q>, root: Maybe<&2, Hashes.Hash>}

# what a judge says of one change: refuse it as stale, or take it, with the
# trees that it wrote
type Verdict<-Q: Data> is Data:
  Verdict.Stale{}
  Verdict.Taken{work: Work<Q>}

# s with the words ds as data, when it then holds each of them under its hash
# (none: a slot holds other words). A node reads back what it puts, so what a
# tree or a rope reads after a put never rests on what the store held before
def State.put(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  +ds: List<&2, List<&2, U32>>
) -> Maybe<&2, Node<Machine.Q(mach)>>:
  +s2 = State.keep(~mach, s, ds)
  Shared.Maybe.when(
    Node<Machine.Q(mach)>,
    Stores.Store.holds(~Node<Machine.Q(mach)>, ~Store.fetch(~mach), s2, ds),
    u => Some{s2}
  )

# the work at the root h on the state m
def Work.on(
  ~mach: Machine(),
  m: Maybe<&2, Node<Machine.Q(mach)>>,
  h: Maybe<&2, Hashes.Hash>
) -> Maybe<&2, Work<Machine.Q(mach)>>:
  match m:
    case None{}:
      None{}
    case Some{s2}:
      Some{Work{s2, h}}

# the work that the new subtree m gives on the state s
def Work.of(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  m: Maybe<&2, Trees.Put>
) -> Maybe<&2, Work<Machine.Q(mach)>>:
  match m:
    case None{}:
      None{}
    case Some{Trees.Put{h, ws}}:
      Work.on(~mach, State.put(~mach, s, ws), Some{h})

# w with the key k set to the value x (none: the store lacks a node)
def Work.set(
  ~mach: Machine(),
  w: Work<Machine.Q(mach)>,
  k: List<&2, U32>,
  x: List<&2, U32>
) -> Maybe<&2, Work<Machine.Q(mach)>>:
  match w:
    case Work{+s, h}:
      Work.of(~mach, s, Node.set(~mach, s, h, k, x))

# w with the words ns as data
def Work.keep(
  ~mach: Machine(),
  w: Work<Machine.Q(mach)>,
  ns: List<&2, List<&2, U32>>
) -> Maybe<&2, Work<Machine.Q(mach)>>:
  match w:
    case Work{s, h}:
      Work.on(~mach, State.put(~mach, s, ns), h)

# the root of w
def Work.root(~mach: Machine(), w: Work<Machine.Q(mach)>) -> Maybe<&2, Hashes.Hash>:
  match w:
    case Work{s, h}:
      h

# a verdict that takes the trees of m (none: wait)
def Work.take(
  ~mach: Machine(),
  m: Maybe<&2, Work<Machine.Q(mach)>>
) -> Maybe<&2, Verdict<Machine.Q(mach)>>:
  match m:
    case None{}:
      None{}
    case Some{w}:
      Some{Verdict.Taken{w}}

# the first tip of a new branch, and the node that holds it
type Made<-Q: Data> is Data:
  Made{tip: Tip, node: Node<Q>}

# the first tip t of a branch, once the trees of m hold it
def Made.put(
  ~mach: Machine(),
  t: Tip,
  m: Maybe<&2, Work<Machine.Q(mach)>>
) -> Maybe<&2, Made<Machine.Q(mach)>>:
  match m:
    case None{}:
      None{}
    case Some{Work{s, l}}:
      Some{Made{t, s}}

# a run: the node that holds what it wrote, and the tip so far
type Run<-Q: Data> is Data:
  Run{state: Node<Q>, tip: Tip}

# the state of the run r
def Run.state(~mach: Machine(), r: Run<Machine.Q(mach)>) -> Node<Machine.Q(mach)>:
  match r:
    case Run{s, t}:
      s

# the tip of the run r
def Run.tip(~mach: Machine(), r: Run<Machine.Q(mach)>) -> Tip:
  match r:
    case Run{s, t}:
      t

# the run of the state and the log of the work m, at the tip t
def Run.logged(
  ~mach: Machine(),
  t: Tip,
  m: Maybe<&2, Work<Machine.Q(mach)>>
) -> Maybe<&2, Run<Machine.Q(mach)>>:
  match t m:
    case x None{}:
      None{}
    case Tip{c, old, n, os} Some{Work{s, l}}:
      Some{Run{s, Tip{c, l, n, os}}}

# Run.add once the value m of the key in the log is known
def Run.add.at(
  ~mach: Machine(),
  r: Run<Machine.Q(mach)>,
  k: List<&2, U32>,
  x: List<&2, U32>,
  m: Maybe<&2, List<&2, U32>>
) -> Maybe<&2, Run<Machine.Q(mach)>>:
  match r m:
    case Run{s, +t} None{}:
      Run.logged(~mach, t, Work.set(~mach, Work{s, Tip.log(t)}, k, x))
    case y Some{old}:
      None{}

# the run r with the new key k of its log set to x (none: the log holds k, or
# the node lacks a node). A log only gains keys: no other def writes a log
def Run.add(
  ~mach: Machine(),
  +r: Run<Machine.Q(mach)>,
  +k: List<&2, U32>,
  x: List<&2, U32>
) -> Maybe<&2, Run<Machine.Q(mach)>>:
  Run.add.at(~mach, r, k, x, Node.get(~mach, Run.state(~mach, r), Tip.log(Run.tip(~mach, r)), k))

# the tip t with the content h
def Tip.over(t: Tip, h: Maybe<&2, Hashes.Hash>) -> Tip:
  match t:
    case Tip{c, l, n, os}:
      Tip{h, l, n, os}

# the run r on the node s2, which a judge grew from the node of r, with the
# content h
def Run.over(
  ~mach: Machine(),
  r: Run<Machine.Q(mach)>,
  s2: Node<Machine.Q(mach)>,
  h: Maybe<&2, Hashes.Hash>
) -> Run<Machine.Q(mach)>:
  Run{s2, Tip.over(Run.tip(~mach, r), h)}

# the tip t one version on, with the owners of the next step that the change
# gives, if it gives any
def Tip.next(t: Tip, own: Maybe<&2, List<&2, String>>) -> Tip:
  match t:
    case Tip{c, l, n, os}:
      Tip{c, l, U32.inc(n), Maybe.default(&2, List<&2, String>, own, os)}

# the run r one version on (Tip.next)
def Run.next(
  ~mach: Machine(),
  r: Run<Machine.Q(mach)>,
  own: Maybe<&2, List<&2, String>>
) -> Run<Machine.Q(mach)>:
  match r:
    case Run{s, t}:
      Run{s, Tip.next(t, own)}

# the run r, after it refused the request i as stale
def Step.stale(
  ~mach: Machine(),
  r: Run<Machine.Q(mach)>,
  i: Ledgers.Id
) -> Maybe<&2, Run<Machine.Q(mach)>>:
  Run.add(~mach, r, Log.out(i), Out.words(Out.Stale{}))

# the run r, after it took the request i as the version of the number n: its
# outcome, its version (the content of r), the count, and the owners that it
# gives
def Step.taken.at(
  ~mach: Machine(),
  r: Run<Machine.Q(mach)>,
  +i: Ledgers.Id,
  +n: U32,
  own: Maybe<&2, List<&2, String>>
) -> Maybe<&2, Run<Machine.Q(mach)>>:
  Maybe.bind(
    &2,
    Run<Machine.Q(mach)>,
    Run<Machine.Q(mach)>,
    Run.add(~mach, r, Log.out(i), Out.words(Out.Taken{n})),
    +r1 => Maybe.bind(
      &2,
      Run<Machine.Q(mach)>,
      Run<Machine.Q(mach)>,
      Run.add(
        ~mach,
        r1,
        Log.version(n),
        Version.words(Version{i, Tip.content(Run.tip(~mach, r1))})
      ),
      r2 => Some{Run.next(~mach, r2, own)}
    )
  )

# the run r, after it took the request i as its next version
def Step.taken(
  ~mach: Machine(),
  +r: Run<Machine.Q(mach)>,
  i: Ledgers.Id,
  own: Maybe<&2, List<&2, String>>
) -> Maybe<&2, Run<Machine.Q(mach)>>:
  Step.taken.at(~mach, r, i, Tip.count(Run.tip(~mach, r)), own)

# the run r, after the verdict m on the request i (none: wait)
def Step.judged(
  ~mach: Machine(),
  r: Run<Machine.Q(mach)>,
  i: Ledgers.Id,
  own: Maybe<&2, List<&2, String>>,
  m: Maybe<&2, Verdict<Machine.Q(mach)>>
) -> Maybe<&2, Run<Machine.Q(mach)>>:
  match m:
    case None{}:
      None{}
    case Some{Verdict.Stale{}}:
      Step.stale(~mach, r, i)
    case Some{Verdict.Taken{Work{s2, h}}}:
      Step.taken(~mach, Run.over(~mach, r, s2, h), i, own)

# the run r with the mark m on the version v, then the request i taken
def Step.marked(
  ~mach: Machine(),
  r: Run<Machine.Q(mach)>,
  i: Ledgers.Id,
  m: String,
  v: Maybe<&2, Version>
) -> Maybe<&2, Run<Machine.Q(mach)>>:
  match v:
    case None{}:
      None{}
    case Some{x}:
      Maybe.bind(
        &2,
        Run<Machine.Q(mach)>,
        Run<Machine.Q(mach)>,
        Run.add(~mach, r, Log.mark(m), Ledgers.Id.code(Version.id(x), [])),
        r2 => Step.taken(~mach, r2, i, None{})
      )

# the run r, after a request i for the mark m: it names the newest version,
# for good; a mark that the line has, or a line with no version, refuses it
def Step.mark(
  ~mach: Machine(),
  +r: Run<Machine.Q(mach)>,
  +i: Ledgers.Id,
  +m: String
) -> Maybe<&2, Run<Machine.Q(mach)>>:
  +s = Run.state(~mach, r)
  +t = Run.tip(~mach, r)
  +n = Tip.count(t)
  Shared.Bool.when(
    Maybe<&2, Run<Machine.Q(mach)>>,
    List.all.if(
      u => Maybe.is_none(&2, Ledgers.Id, Line.mark(~mach, s, t, m)),
      Bool.not(U32.is_eq(n, 0))
    ),
    u => Step.marked(~mach, r, i, m, Line.version(~mach, s, t, U32.sub(n, 1))),
    u => Step.stale(~mach, r, i)
  )

# the run r with the first tip m of the new branch b of its store in its log,
# then the request i taken (none: the node lacks a node)
def Branch.made(
  ~mach: Machine(),
  +r: Run<Machine.Q(mach)>,
  i: Ledgers.Id,
  b: String,
  m: Maybe<&2, Made<Machine.Q(mach)>>
) -> Maybe<&2, Run<Machine.Q(mach)>>:
  match m:
    case None{}:
      None{}
    case Some{Made{t, s2}}:
      Maybe.bind(
        &2,
        Run<Machine.Q(mach)>,
        Run<Machine.Q(mach)>,
        Run.add(
          ~mach,
          Run.over(~mach, r, s2, Tip.content(Run.tip(~mach, r))),
          Log.start(b),
          Hashes.Hash.code(Tip.hash(t), [])
        ),
        r2 => Step.taken(~mach, r2, i, None{})
      )

# the requests of a step that a node can run now, in order, and the run after
# them
type Picked<-Q: Data> is Data:
  Picked{run: Run<Q>, asks: List<&2, Ledgers.Id>}

# the run of p
def Picked.run(~mach: Machine(), p: Picked<Machine.Q(mach)>) -> Run<Machine.Q(mach)>:
  match p:
    case Picked{r, qs}:
      r

# the requests of p
def Picked.asks(~mach: Machine(), p: Picked<Machine.Q(mach)>) -> List<&2, Ledgers.Id>:
  match p:
    case Picked{r, qs}:
      qs

# p, with the request i before its requests when b holds
def Picked.add(
  ~mach: Machine(),
  b: Bool,
  i: Ledgers.Id,
  p: Picked<Machine.Q(mach)>
) -> Picked<Machine.Q(mach)>:
  match p:
    case Picked{r, qs}:
      Picked{r, List.filter.put(Ledgers.Id, i, qs, b)}

# a first owner of a store: a node, and the key that signs its first ballot in
# the store
type Owner is Data:
  Owner{name: String, key: Hashes.Hash}

# the first owner o, then r
def Owner.code(o: Owner, r: List<&2, U32>) -> List<&2, U32>:
  match o:
    case Owner{n, k}:
      Codes.Code.text(n, Hashes.Hash.code(k, r))

# a first owner
def Owner.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Owner>>:
  Codes.Code.two.read(
    ~String,
    ~Hashes.Hash,
    ~Owner,
    ~Codes.Code.text.read,
    ~Hashes.Hash.code.read,
    n => k => Owner{n, k},
    ts
  )

# the names of the first owners os
def Owner.names(os: List<&2, Owner>) -> List<&2, String>:
  match os:
    case Nil{}:
      []
    case Con{Owner{n, k}, r}:
      n <> Owner.names(r)

# how a request arrives at a node: it starts a store, with its first owners,
# or it waits on a line of a store
type Arrival is Data:
  Arrival.Starts{owners: List<&2, Owner>}
  Arrival.Waits{store: Ledgers.Id, line: Maybe<&2, String>}

# the line of the request i, which arrives as a: a store that starts is its
# own line
def Arrival.chain(i: Ledgers.Id, a: Arrival) -> Ledgers.Chain:
  match a:
    case Arrival.Starts{os}:
      Ledgers.Chain{i, None{}}
    case Arrival.Waits{r, l}:
      Line.chain(r, l)

# the kernel of a machine mach: what a request does to the run of a line; and
# the request, if any, that a node asks by itself after it works on a line of
# a store
def Kernel(mach: Machine()) -> Type:
  (
    Run<
      Machine.Q(
        mach
      )> -> Ledgers.Chain -> Ledgers.Id -> Machine.Q(mach) -> Maybe<&2, Run<Machine.Q(mach)>>
  )
    & (
      Node<
        Machine.Q(mach)> -> Ledgers.Id -> Maybe<&2, String> -> Maybe<&2, Request<Machine.Q(mach)>>
    )

# what a request does to the run of a line, by the kernel k
def Kernel.change(
  -mach: Machine(),
  k: Kernel(mach)
) -> Run<
  Machine.Q(
    mach
  )> -> Ledgers.Chain -> Ledgers.Id -> Machine.Q(mach) -> Maybe<&2, Run<Machine.Q(mach)>>:
  match k:
    case Tuple{c, f}:
      c

# the request that a node asks by itself after it works on a line of a
# store, by the kernel k
def Kernel.follow(
  -mach: Machine(),
  k: Kernel(mach)
) -> Node<
  Machine.Q(mach)> -> Ledgers.Id -> Maybe<&2, String> -> Maybe<&2, Request<Machine.Q(mach)>>:
  match k:
    case Tuple{c, f}:
      f

# the run r of the line c, after the request i, which the node holds as a
# (none: wait for the request)
def Step.asked(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  r: Run<Machine.Q(mach)>,
  c: Ledgers.Chain,
  i: Ledgers.Id,
  a: Maybe<&2, Ledgers.Asked<Machine.Q(mach)>>
) -> Maybe<&2, Run<Machine.Q(mach)>>:
  match a:
    case None{}:
      None{}
    case Some{Ledgers.Asked{t, q}}:
      Kernel.change(mach, kern)(r)(c)(i)(q)

# the run r of the line c, after the request i, whose outcome in the log is o:
# a request that has one is skipped
def Step.fresh(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +r: Run<Machine.Q(mach)>,
  c: Ledgers.Chain,
  +i: Ledgers.Id,
  o: Maybe<&2, Out>
) -> Maybe<&2, Run<Machine.Q(mach)>>:
  match o:
    case Some{x}:
      Some{r}
    case None{}:
      Step.asked(~mach, ~kern, r, c, i, Node.asked(~mach, Run.state(~mach, r), i))

# the run r of the line c, after the request i
def Step.one(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +r: Run<Machine.Q(mach)>,
  c: Ledgers.Chain,
  +i: Ledgers.Id
) -> Maybe<&2, Run<Machine.Q(mach)>>:
  Step.fresh(~mach, ~kern, r, c, i, Line.out(~mach, Run.state(~mach, r), Run.tip(~mach, r), i))

# the run m of the line c, after each request of is, in order
def Step.all(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +c: Ledgers.Chain,
  qs: List<&2, Ledgers.Id>,
  m: Maybe<&2, Run<Machine.Q(mach)>>
) -> Maybe<&2, Run<Machine.Q(mach)>>:
  match qs:
    case Nil{}:
      m
    case Con{i, rest}:
      Step.all(
        ~mach,
        ~kern,
        c,
        rest,
        Maybe.bind(
          &2,
          Run<Machine.Q(mach)>,
          Run<Machine.Q(mach)>,
          m,
          r => Step.one(~mach, ~kern, r, c, i)
        )
      )

# the requests of qs that can run now on the line c, from the run r, and the
# run after them. A request that must wait (for a version, a request or a
# node) is left out: it waits, and does not stop the others
def Step.some(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +c: Ledgers.Chain,
  qs: List<&2, Ledgers.Id>,
  +r: Run<Machine.Q(mach)>
) -> Picked<Machine.Q(mach)>:
  match qs:
    case Nil{}:
      Picked{r, []}
    case Con{+i, rest}:
      +m = Step.one(~mach, ~kern, r, c, i)
      Picked.add(
        ~mach,
        Maybe.is_some(&2, Run<Machine.Q(mach)>, m),
        i,
        Step.some(~mach, ~kern, c, rest, Maybe.default(&2, Run<Machine.Q(mach)>, m, r))
      )

# the step of the line c that runs the requests qs from the tip t (none: wait
# for a request, a version or a node)
def Step.run(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  t: Tip,
  qs: List<&2, Ledgers.Id>
) -> Maybe<&2, Run<Machine.Q(mach)>>:
  Step.all(~mach, ~kern, c, qs, Some{Run{s, t}})

# the place of the ballot b
def Ballot.at(b: Ledgers.Ballot) -> Ledgers.Where:
  match b:
    case Ledgers.Ballot{Ledgers.Signed{w, n, a}, l}:
      w

# the node of the ballot b
def Ballot.node(b: Ledgers.Ballot) -> String:
  match b:
    case Ledgers.Ballot{Ledgers.Signed{w, n, a}, l}:
      n

# the place of the ballot before b in its chain
def Ballot.prev(b: Ledgers.Ballot) -> Maybe<&2, Ledgers.Where>:
  match b:
    case Ledgers.Ballot{x, Ledgers.Link{p, k, z}}:
      p

# the key of the ballot after b in its chain
def Ballot.next(b: Ledgers.Ballot) -> Hashes.Hash:
  match b:
    case Ledgers.Ballot{x, Ledgers.Link{p, k, z}}:
      k

# the store of the place w
def Where.store(w: Ledgers.Where) -> Ledgers.Id:
  match w:
    case Ledgers.Where{Ledgers.Chain{r, k}, h, z}:
      r

# the line of the place w
def Where.line(w: Ledgers.Where) -> Ledgers.Chain:
  match w:
    case Ledgers.Where{c, h, z}:
      c

# the store of the ballot b
def Ballot.store(b: Ledgers.Ballot) -> Ledgers.Id:
  Where.store(Ballot.at(b))

# the key of the chain of the node n in the store r
def Seal.slot(r: Ledgers.Id, n: String) -> List<&2, Bool>:
  List.append(&2, Bool, Ledgers.Id.key(r), Tries.Trie.text(n))

# a and b are the same place, or both none
def Prev.same(a: Maybe<&2, Ledgers.Where>, b: Maybe<&2, Ledgers.Where>) -> Bool:
  match a b:
    case None{} None{}:
      True{}
    case Some{x} Some{y}:
      Codes.Code.is_eq(~Ledgers.Where, ~Ledgers.Where.code, x, y)
    case x y:
      False{}

# the key in the value m, if any
def Seal.read(m: Maybe<&2, List<&2, U32>>) -> Maybe<&2, Hashes.Hash>:
  Maybe.bind(
    &2,
    List<&2, U32>,
    Hashes.Hash,
    m,
    ws => Read.whole(Hashes.Hash, Hashes.Hash.code.read(ws))
  )

# the first key that the store r gave the node n, as s knows the store
def Seal.first(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +s: Node<Machine.Q(mach)>,
  r: Ledgers.Id,
  n: String
) -> Maybe<&2, Hashes.Hash>:
  Seal.read(
    Node.get(
      ~mach,
      s,
      Maybe.bind(
        &2,
        Tip,
        Hashes.Hash,
        Node.tip(~mach, s, Ledgers.Chain{r, None{}}),
        t => Tip.content(t)
      ),
      Machine.seal(mach)(n)
    )
  )

# the chain c, when it starts from the first key m; else a new chain from m
# (none: the store gave the node no key)
def Keychain.from(m: Maybe<&2, Hashes.Hash>, c: Maybe<&2, Keychain>) -> Maybe<&2, Keychain>:
  match m c:
    case None{} y:
      None{}
    case Some{k} None{}:
      Some{Keychain{0, None{}, k, k}}
    case Some{+k} Some{Keychain{n, l, x, +f}}:
      Some{
        Shared.Bool.when(
          Keychain,
          Hashes.Hash.is_eq(f, k),
          u => Keychain{n, l, x, f},
          u => Keychain{0, None{}, k, k}
        )
      }

# the chains of the keys ks
def Keys.chains(ks: Keys) -> Tries.Trie<Keychain>:
  match ks:
    case Keys{seed, cs, as, rs}:
      cs

# the secret seed of the keys ks
def Keys.seed(ks: Keys) -> Hashes.Hash:
  match ks:
    case Keys{seed, cs, as, rs}:
      seed

# ks, with the request i asked at this node
def Keys.mark(ks: Keys, i: Ledgers.Id) -> Keys:
  match ks:
    case Keys{seed, cs, as, rs}:
      Keys{seed, cs, Tries.Trie.set(Unit, as, Ledgers.Id.key(i), Unit{}), rs}

# the request i was asked at this node
def Keys.asked(ks: Keys, i: Ledgers.Id) -> Bool:
  match ks:
    case Keys{seed, cs, as, rs}:
      Tries.Trie.has(Unit, as, Ledgers.Id.key(i))

# ks with the chain c at the key k
def Keys.set(ks: Keys, k: List<&2, Bool>, c: Keychain) -> Keys:
  match ks:
    case Keys{seed, cs, as, rs}:
      Keys{seed, Tries.Trie.set(Keychain, cs, k, c), as, rs}

# the highest round, in the rounds rs, of the height h of the line c (0: the
# first round)
def Rounds.at(rs: Tries.Trie<Nat>, c: Ledgers.Chain, h: U32) -> Nat:
  Maybe.default(&2, Nat, Tries.Trie.get(Nat, rs, Ledgers.Slot.height(c, h)), 0n)

# the rounds of the keys ks
def Keys.rounds(ks: Keys) -> Tries.Trie<Nat>:
  match ks:
    case Keys{seed, cs, as, rs}:
      rs

# ks, which saw a ballot at the place w: the highest round of its height
def Keys.saw(ks: Keys, w: Ledgers.Where) -> Keys:
  match ks w:
    case Keys{seed, cs, as, +rs} Ledgers.Where{+c, +h, +r}:
      Keys{
        seed,
        cs,
        as,
        Shared.Bool.when(
          Tries.Trie<Nat>,
          Nat.is_lt(Rounds.at(rs, c, h), r),
          u => Tries.Trie.set(Nat, rs, Ledgers.Slot.height(c, h), r),
          u => rs
        )
      }

# the highest round of the height h of the line c of which s holds a ballot
def Round.seen(~mach: Machine(), s: Node<Machine.Q(mach)>, c: Ledgers.Chain, h: U32) -> Nat:
  Rounds.at(Keys.rounds(State.keys(~mach, s)), c, h)

# the chain of the node n in the store r, as s knows it
def Seal.chain(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +s: Node<Machine.Q(mach)>,
  +r: Ledgers.Id,
  +n: String
) -> Maybe<&2, Keychain>:
  Keychain.from(
    Seal.first(~mach, ~kern, s, r, n),
    Tries.Trie.get(Keychain, Keys.chains(State.keys(~mach, s)), Seal.slot(r, n))
  )

# the ballot b is the next of the chain c, and the key of c signs it
def Seal.fits(c: Keychain, +b: Ledgers.Ballot) -> Bool:
  match c:
    case Keychain{n, last, key, f}:
      List.all.if(u => Ledgers.Ballot.sealed(key, b), Prev.same(Ballot.prev(b), last))

# the chain c after its next ballot b
def Keychain.next(c: Keychain, +b: Ledgers.Ballot) -> Keychain:
  match c:
    case Keychain{n, last, key, f}:
      Keychain{U32.inc(n), Some{Ballot.at(b)}, Ballot.next(b), f}

# Seal.accept once the chain m of the ballot's node is known
def Seal.accept.at(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  +b: Ledgers.Ballot,
  m: Maybe<&2, Keychain>
) -> Maybe<&2, Node<Machine.Q(mach)>>:
  match m:
    case None{}:
      None{}
    case Some{+c}:
      Shared.Maybe.when(
        Node<Machine.Q(mach)>,
        Seal.fits(c, b),
        u => Some{
          State.keyed(
            ~mach,
            State.led(
              ~mach,
              s,
              Ledgers.State.keep(~Machine.Q(mach), ~Machine.same(mach), State.ledger(~mach, s), b)
            ),
            Keys.saw(
              Keys.set(
                State.keys(~mach, s),
                Seal.slot(Ballot.store(b), Ballot.node(b)),
                Keychain.next(c, b)
              ),
              Ballot.at(b)
            )
          )
        }
      )

# s with the ballot b, when it is the next of its node's chain in its store
# and the key of the chain signs it (none: not now)
def Seal.accept(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +s: Node<Machine.Q(mach)>,
  +b: Ledgers.Ballot
) -> Maybe<&2, Node<Machine.Q(mach)>>:
  Seal.accept.at(~mach, s, b, Seal.chain(~mach, ~kern, s, Ballot.store(b), Ballot.node(b)))

# the secret of the ballot of the number j of a node in the store r, from the
# node's seed
def Seal.secret(seed: Hashes.Hash, r: Ledgers.Id, j: U32) -> Hashes.Hash:
  Hashes.Sha.hash(Hashes.Hash.code(seed, Ledgers.Id.code(r, [j])))

# the key of the place m, if any
def Prev.key(m: Maybe<&2, Ledgers.Where>) -> List<&2, Bool>:
  match m:
    case None{}:
      [False{}]
    case Some{w}:
      True{} <> Ledgers.Slot.vote(w, "")

# the key of where the ballot after the one at last waits, for the node n in
# the store r
def Seal.link(r: Ledgers.Id, n: String, last: Maybe<&2, Ledgers.Where>) -> List<&2, Bool>:
  List.append(&2, Bool, Seal.slot(r, n), Prev.key(last))

# the ballots bs, each at the key of where it waits in its chain
def Pending.of(bs: List<&2, Ledgers.Ballot>) -> Tries.Trie<Ledgers.Ballot>:
  match bs:
    case Nil{}:
      Tries.Trie.new(Ledgers.Ballot)
    case Con{+b, r}:
      Tries.Trie.set(
        Ledgers.Ballot,
        Pending.of(r),
        Seal.link(Ballot.store(b), Ballot.node(b), Ballot.prev(b)),
        b
      )

# the last place of the chain c
def Keychain.last(c: Keychain) -> Maybe<&2, Ledgers.Where>:
  match c:
    case Keychain{n, last, key, f}:
      last

# the ballot of p that is the next of the chain of the node n in the store r
def Pending.next(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  s: Node<Machine.Q(mach)>,
  p: Tries.Trie<Ledgers.Ballot>,
  +r: Ledgers.Id,
  +n: String
) -> Maybe<&2, Ledgers.Ballot>:
  Maybe.bind(
    &2,
    Keychain,
    Ledgers.Ballot,
    Seal.chain(~mach, ~kern, s, r, n),
    c => Tries.Trie.get(Ledgers.Ballot, p, Seal.link(r, n, Keychain.last(c)))
  )

# s with each ballot of p that the chain of the node n in the store r leads
# to, from the ballot mb, f ballots at most
def Sealed.follow(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  f: Nat,
  +s: Node<Machine.Q(mach)>,
  +p: Tries.Trie<Ledgers.Ballot>,
  +r: Ledgers.Id,
  +n: String,
  mb: Maybe<&2, Ledgers.Ballot>
) -> Node<Machine.Q(mach)>:
  match f mb:
    case 1n+g Some{b}:
      Maybe.default(
        &2,
        Node<Machine.Q(mach)>,
        Maybe.bind(
          &2,
          Node<Machine.Q(mach)>,
          Node<Machine.Q(mach)>,
          Seal.accept(~mach, ~kern, s, b),
          +s2 => Some{
            Sealed.follow(~mach, ~kern, g, s2, p, r, n, Pending.next(~mach, ~kern, s2, p, r, n))
          }
        ),
        s
      )
    case x y:
      s

# s with the ballots of p that the chains of the ballots bs lead to
def Sealed.each(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +f: Nat,
  bs: List<&2, Ledgers.Ballot>,
  +p: Tries.Trie<Ledgers.Ballot>,
  +s: Node<Machine.Q(mach)>
) -> Node<Machine.Q(mach)>:
  match bs:
    case Nil{}:
      s
    case Con{+b, rest}:
      Sealed.each(
        ~mach,
        ~kern,
        f,
        rest,
        p,
        Sealed.follow(
          ~mach,
          ~kern,
          f,
          s,
          p,
          Ballot.store(b),
          Ballot.node(b),
          Pending.next(~mach, ~kern, s, p, Ballot.store(b), Ballot.node(b))
        )
      )

# s with each ballot of bs that its node's chain leads to and its key signs:
# the cost is about that of the ballots, in any order
def Sealed.take(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +bs: List<&2, Ledgers.Ballot>,
  s: Node<Machine.Q(mach)>
) -> Node<Machine.Q(mach)>:
  Sealed.each(~mach, ~kern, List.length(&2, Ledgers.Ballot, bs), bs, Pending.of(bs), s)

# the height of the next step of the head h
def Head.next(h: Head) -> U32:
  match h:
    case Head{r, b, n, t}:
      n

# s with the head h of the line c
def State.head(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  h: Head
) -> Node<Machine.Q(mach)>:
  match s:
    case Node{l, hs, ws, ks}:
      Node{l, Tries.Trie.set(Head, hs, Ledgers.Chain.key(c), h), ws, ks}

# the requests of the line c that wait for a step, the newest first
def Wait.of(~mach: Machine(), s: Node<Machine.Q(mach)>, c: Ledgers.Chain) -> List<&2, Ledgers.Id>:
  Maybe.default(
    &2,
    List<&2, Ledgers.Id>,
    Tries.Trie.get(List<&2, Ledgers.Id>, State.waiting(~mach, s), Ledgers.Chain.key(c)),
    []
  )

# the requests of the line c that wait for a step, as they came
def Wait.order(~mach: Machine(), s: Node<Machine.Q(mach)>, c: Ledgers.Chain) -> List<&2, Ledgers.Id>:
  List.reverse(&2, Ledgers.Id, Wait.of(~mach, s, c))

# ws with the requests qs waiting at the key k: a line with no waiting request
# has no entry, so the lines that wait are read without a walk of every line
def Wait.put(
  ws: Tries.Trie<List<&2, Ledgers.Id>>,
  k: List<&2, Bool>,
  qs: List<&2, Ledgers.Id>
) -> Tries.Trie<List<&2, Ledgers.Id>>:
  match qs:
    case Nil{}:
      Tries.Trie.drop(List<&2, Ledgers.Id>, ws, k)
    case Con{i, r}:
      Tries.Trie.set(List<&2, Ledgers.Id>, ws, k, Con{i, r})

# s with the requests qs waiting on the line c
def Wait.set(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  qs: List<&2, Ledgers.Id>
) -> Node<Machine.Q(mach)>:
  match s:
    case Node{l, hs, ws, ks}:
      Node{l, hs, Wait.put(ws, Ledgers.Chain.key(c), qs), ks}

# s with the request i waiting on the line c: the newest comes first, so a
# request waits in one step, however many wait (Wait.order gives them as
# they came)
def State.wait(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  i: Ledgers.Id
) -> Node<Machine.Q(mach)>:
  Wait.set(~mach, s, c, i <> Wait.of(~mach, s, c))

# the requests of qs whose keys done does not hold
def Wait.left(qs: List<&2, Ledgers.Id>, +done: Tries.Trie<Unit>) -> List<&2, Ledgers.Id>:
  match qs:
    case Nil{}:
      []
    case Con{+i, r}:
      List.filter.put(
        Ledgers.Id,
        i,
        Wait.left(r, done),
        Bool.not(Tries.Trie.has(Unit, done, Ledgers.Id.key(i)))
      )

# s at the head h of the line c, after a step that ran the requests qs: they
# wait no more
def State.moved(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  h: Head,
  qs: List<&2, Ledgers.Id>
) -> Node<Machine.Q(mach)>:
  State.head(
    ~mach,
    Wait.set(
      ~mach,
      s,
      c,
      Wait.left(
        Wait.of(~mach, s, c),
        Tries.Trie.put_keys(~Ledgers.Id, ~Ledgers.Id.key, qs, Tries.Trie.new(Unit))
      )
    ),
    c,
    h
  )

# State.first once the head m of the line is known
def First.at(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  h: Head,
  m: Maybe<&2, Head>
) -> Node<Machine.Q(mach)>:
  match m:
    case Some{Head{r, b, n, Some{t}}}:
      s
    case x:
      State.head(~mach, s, c, h)

# s with the first head h of the line c, when the line has no tip: a line
# that has a tip moves only by a step
def State.first(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  h: Head
) -> Node<Machine.Q(mach)>:
  First.at(~mach, s, c, h, Node.head_of(~mach, s, c))

# the state m with the first head h of the line c, else s
def Start.head(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  m: Maybe<&2, Node<Machine.Q(mach)>>,
  c: Ledgers.Chain,
  h: Head
) -> Node<Machine.Q(mach)>:
  match m:
    case None{}:
      s
    case Some{s2}:
      State.first(~mach, State.led(~mach, s, State.ledger(~mach, s2)), c, h)

# w with the first key of each first owner of os
def Seal.firsts(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  os: List<&2, Owner>,
  m: Maybe<&2, Work<Machine.Q(mach)>>
) -> Maybe<&2, Work<Machine.Q(mach)>>:
  match os:
    case Nil{}:
      m
    case Con{Owner{n, k}, r}:
      Seal.firsts(
        ~mach,
        ~kern,
        r,
        Maybe.bind(
          &2,
          Work<Machine.Q(mach)>,
          Work<Machine.Q(mach)>,
          m,
          w => Work.set(~mach, w, Machine.seal(mach)(n), Hashes.Hash.code(k, []))
        )
      )

# Node.start once the content m of the store is known: its first tip has no
# log and no version, and its owners are the first owners os
def Start.with(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  +i: Ledgers.Id,
  os: List<&2, String>,
  m: Maybe<&2, Work<Machine.Q(mach)>>
) -> Node<Machine.Q(mach)>:
  match m:
    case None{}:
      s
    case Some{Work{s2, c}}:
      +t = {Tip{c, None{}, 0, os}: Tip}
      Start.head(
        ~mach,
        s,
        State.put(~mach, s2, [Tip.words(t)]),
        Ledgers.Chain{i, None{}},
        Head{i, None{}, 0, Some{Tip.hash(t)}}
      )

# s, which follows the store that the request i starts with the first owners
# os: its content holds their first keys
def Node.start(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +s: Node<Machine.Q(mach)>,
  i: Ledgers.Id,
  +os: List<&2, Owner>
) -> Node<Machine.Q(mach)>:
  Start.with(~mach, s, i, Owner.names(os), Seal.firsts(~mach, ~kern, os, Some{Work{s, None{}}}))

# the first tip of the branch b of a store whose tip is m, if the store made
# b: the log of the store holds it, written once, so every node opens the
# branch at the same tip (Chain.start_final)
def Branch.first(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  b: String,
  m: Maybe<&2, Tip>
) -> Maybe<&2, Hashes.Hash>:
  match m:
    case None{}:
      None{}
    case Some{t}:
      Maybe.bind(
        &2,
        List<&2, U32>,
        Hashes.Hash,
        Node.get(~mach, s, Tip.log(t), Log.start(b)),
        ws => Read.whole(Hashes.Hash, Hashes.Hash.code.read(ws))
      )

# Node.open once the head m of the line is known
def Open.at(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  m: Maybe<&2, Head>
) -> Node<Machine.Q(mach)>:
  match m:
    case Some{Head{+r, Some{+b}, n, None{}}}:
      State.head(
        ~mach,
        s,
        c,
        Head{r, Some{b}, 0, Branch.first(~mach, s, b, Node.tip(~mach, s, Ledgers.Chain{r, None{}}))}
      )
    case x:
      s

# s, which follows the line c: a branch that the node waits for opens at its
# first tip, once the store that the node follows made it
def Node.open(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain
) -> Node<Machine.Q(mach)>:
  Open.at(~mach, s, c, Node.head_of(~mach, s, c))

# s, which follows the line l of the store r, when the head m says that it
# does not yet
def Follow.new(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  +r: Ledgers.Id,
  +l: Maybe<&2, String>,
  m: Maybe<&2, Head>
) -> Node<Machine.Q(mach)>:
  match m:
    case Some{h}:
      s
    case None{}:
      State.head(~mach, s, Line.chain(r, l), Head{r, l, 0, None{}})

# s, which follows the line l of the store r
def Node.follow(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  +r: Ledgers.Id,
  +l: Maybe<&2, String>
) -> Node<Machine.Q(mach)>:
  Follow.new(~mach, s, r, l, Node.head_of(~mach, s, Line.chain(r, l)))

# s, once it holds the new request i, which arrives as a: a store starts, or
# the request waits on its line
def Arrive.at(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  s: Node<Machine.Q(mach)>,
  i: Ledgers.Id,
  a: Arrival
) -> Node<Machine.Q(mach)>:
  match a:
    case Arrival.Starts{os}:
      Node.start(~mach, ~kern, s, i, os)
    case Arrival.Waits{+r, +l}:
      State.wait(~mach, Node.follow(~mach, s, r, l), Line.chain(r, l), i)

# s, once it holds the new request i of the change q
def Node.arrive(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  s: Node<Machine.Q(mach)>,
  i: Ledgers.Id,
  q: Machine.Q(mach)
) -> Node<Machine.Q(mach)>:
  Arrive.at(~mach, ~kern, s, i, Machine.arrival(mach)(q))

# a and b are the same root
def Root.same(a: Maybe<&2, Hashes.Hash>, b: Maybe<&2, Hashes.Hash>) -> Bool:
  Shared.Maybe.is_eq(~Hashes.Hash, ~Hashes.Hash.is_eq, a, b)

# the node n is free to cast a ballot at the place w of a line at the tip t:
# n is an owner, and n cast none there. A node reads this before it runs the
# requests that wait, so a node that cannot cast runs none
def Cast.free(~mach: Machine(), +n: String, s: Node<Machine.Q(mach)>, w: Ledgers.Where, t: Tip) -> Bool:
  List.all.if(
    v => Maybe.is_none(
      &2,
      Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>,
      Ledgers.State.get(~Machine.Q(mach), State.ledger(~mach, s), Ledgers.Slot.vote(w, n))
    ),
    List.contains(~String, ~String.eq, Tip.owners(t), n)
  )

# s with the node n's ballot for the act a at the place w, sealed as the next
# of the node's chain m (none: the store gave the node no key)
def Cast.seal(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +s: Node<Machine.Q(mach)>,
  +w: Ledgers.Where,
  n: String,
  a: Ledgers.Act,
  m: Maybe<&2, Keychain>
) -> Node<Machine.Q(mach)>:
  match m:
    case None{}:
      s
    case Some{Keychain{+j, last, key, f}}:
      +seed = Keys.seed(State.keys(~mach, s))
      +r = Where.store(w)
      Maybe.default(
        &2,
        Node<Machine.Q(mach)>,
        Seal.accept(
          ~mach,
          ~kern,
          s,
          Ledgers.Ballot.make(
            Seal.secret(seed, r, j),
            Ledgers.Signed{w, n, a},
            last,
            Seals.Seal.public(Seal.secret(seed, r, U32.inc(j)))
          )
        ),
        s
      )

# the state m with the node n's ballot for the act a at the place w, else s
def Cast.vote(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  s: Node<Machine.Q(mach)>,
  m: Maybe<&2, Node<Machine.Q(mach)>>,
  +w: Ledgers.Where,
  +n: String,
  a: Ledgers.Act
) -> Node<Machine.Q(mach)>:
  match m:
    case None{}:
      s
    case Some{s3}:
      +s4 = State.led(~mach, s, State.ledger(~mach, s3))
      Cast.seal(~mach, ~kern, s4, w, n, a, Seal.chain(~mach, ~kern, s4, Where.store(w), n))

# s with the node n's vote at the place w for the step that ran qs from the
# tip of the hash th, which the passes of the nodes from allow, when the run m
# is there: the run's nodes, its tip, and the ballot
def Cast.put(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  n: String,
  w: Ledgers.Where,
  th: Maybe<&2, Hashes.Hash>,
  qs: List<&2, Ledgers.Id>,
  from: List<&2, String>,
  m: Maybe<&2, Run<Machine.Q(mach)>>,
  s: Node<Machine.Q(mach)>
) -> Node<Machine.Q(mach)>:
  match m:
    case None{}:
      s
    case Some{Run{s2, +t2}}:
      Cast.vote(
        ~mach,
        ~kern,
        s,
        State.put(~mach, s2, [Tip.words(t2)]),
        w,
        n,
        Ledgers.Act.Vote{Ledgers.Vote{th, qs, Some{Tip.hash(t2)}}, from}
      )

# the node s may cast for the request i, which it holds as m: any request,
# but one of who decides only when it was asked at s
def Cast.mine.of(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  s: Node<Machine.Q(mach)>,
  i: Ledgers.Id,
  m: Maybe<&2, Ledgers.Asked<Machine.Q(mach)>>
) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{Ledgers.Asked{t, q}}:
      List.any.if(u => Keys.asked(State.keys(~mach, s), i), Bool.not(Machine.governs(mach)(q)))

# the requests of qs that the node s may cast for
def Cast.mine(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +s: Node<Machine.Q(mach)>,
  qs: List<&2, Ledgers.Id>
) -> List<&2, Ledgers.Id>:
  match qs:
    case Nil{}:
      []
    case Con{+i, r}:
      List.filter.put(
        Ledgers.Id,
        i,
        Cast.mine(~mach, ~kern, s, r),
        Cast.mine.of(~mach, ~kern, s, i, Node.asked(~mach, s, i))
      )

# the owner whose turn it is to propose the step at the height h, among the
# owners os: each in turn, by the height. One owner proposes a step and the
# others cast for the same step, so the owners do not split over what waits
# at each of them
def Owners.turn(+os: List<&2, String>, h: U32) -> Maybe<&2, String>:
  List.get(&2, String, os, U32.to_nat(U32.mod(h, U32.from_nat(List.length(&2, String, os)))))

# the step in the cell m of a ballot, if it holds one
def Cast.step(
  ~mach: Machine(),
  m: Maybe<&2, Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>>
) -> Maybe<&2, Ledgers.Vote>:
  match m:
    case Some{Cells.One{Ledgers.Entry.Vote{b}}}:
      Ledgers.Ballot.vote(b)
    case x:
      None{}

# the step that the node p cast at the place w, if s holds its ballot
def Cast.of(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  w: Ledgers.Where,
  p: String
) -> Maybe<&2, Ledgers.Vote>:
  Cast.step(
    ~mach,
    Ledgers.State.get(~Machine.Q(mach), State.ledger(~mach, s), Ledgers.Slot.vote(w, p))
  )

# what a node casts for: the requests of a step, its own run of them (none:
# it cannot run them now), and the nodes whose passes allow the step
type Plan<-Q: Data> is Data:
  Plan{asks: List<&2, Ledgers.Id>, run: Maybe<&2, Run<Q>>, from: List<&2, String>}

# the requests of the plan p
def Plan.asks(~mach: Machine(), p: Plan<Machine.Q(mach)>) -> List<&2, Ledgers.Id>:
  match p:
    case Plan{qs, m, from}:
      qs

# the run of the plan p
def Plan.run(~mach: Machine(), p: Plan<Machine.Q(mach)>) -> Maybe<&2, Run<Machine.Q(mach)>>:
  match p:
    case Plan{qs, m, from}:
      m

# the nodes whose passes allow the step of the plan p
def Plan.from(~mach: Machine(), p: Plan<Machine.Q(mach)>) -> List<&2, String>:
  match p:
    case Plan{qs, m, from}:
      from

# the plan of an owner that proposes freely, on the line c at the tip t: the
# requests that wait at it, that it may cast for and that can run now
def Plan.own(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  t: Tip,
  from: List<&2, String>
) -> Plan<Machine.Q(mach)>:
  +p = Step.some(~mach, ~kern, c, Cast.mine(~mach, ~kern, s, Wait.order(~mach, s, c)), Run{s, t})
  Plan{Picked.asks(~mach, p), Some{Picked.run(~mach, p)}, from}

# the node s may cast for each request of qs
def Cast.all_mine(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +s: Node<Machine.Q(mach)>,
  qs: List<&2, Ledgers.Id>
) -> Bool:
  match qs:
    case Nil{}:
      True{}
    case Con{+i, r}:
      List.all.if(
        u => Cast.all_mine(~mach, ~kern, s, r),
        Cast.mine.of(~mach, ~kern, s, i, Node.asked(~mach, s, i))
      )

# the run m, when it gives the tip of the hash after
def Plan.fit(
  ~mach: Machine(),
  after: Maybe<&2, Hashes.Hash>,
  m: Maybe<&2, Run<Machine.Q(mach)>>
) -> Maybe<&2, Run<Machine.Q(mach)>>:
  match m:
    case None{}:
      None{}
    case Some{Run{s2, +t2}}:
      Shared.Maybe.when(
        Run<Machine.Q(mach)>,
        Root.same(after, Some{Tip.hash(t2)}),
        u => Some{Run{s2, t2}}
      )

# the plan for a step m that another ballot names, on the line c at the tip t
# of the hash th: when the step starts from this tip, the node may cast for
# each of its requests, and the node's own run of them gives the same tip
def Plan.copy(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  t: Tip,
  th: Maybe<&2, Hashes.Hash>,
  m: Maybe<&2, Ledgers.Vote>,
  from: List<&2, String>
) -> Plan<Machine.Q(mach)>:
  match m:
    case None{}:
      Plan{[], None{}, []}
    case Some{Ledgers.Vote{before, +qs, after}}:
      Shared.Bool.when(
        Plan<Machine.Q(mach)>,
        List.all.if(u => Cast.all_mine(~mach, ~kern, s, qs), Root.same(before, th)),
        u => Plan{qs, Plan.fit(~mach, after, Step.run(~mach, ~kern, s, c, t, qs)), from},
        u => Plan{[], None{}, []}
      )

# the line of the request i, when s holds it
def Node.chain_of(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  +i: Ledgers.Id
) -> Maybe<&2, Ledgers.Chain>:
  Maybe.bind(
    &2,
    Ledgers.Asked<Machine.Q(mach)>,
    Ledgers.Chain,
    Node.asked(~mach, s, i),
    a => Some{Arrival.chain(i, Machine.arrival(mach)(Asked.ask(~mach, a)))}
  )

# the round of the place w
def Where.round(w: Ledgers.Where) -> Nat:
  match w:
    case Ledgers.Where{c, h, r}:
      r

# what the node p did at the place w, in the cell m of its vote
def Cast.act.of(
  ~mach: Machine(),
  m: Maybe<&2, Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>>
) -> Maybe<&2, Ledgers.Act>:
  match m:
    case Some{Cells.One{Ledgers.Entry.Vote{Ledgers.Ballot{Ledgers.Signed{w, n, a}, l}}}}:
      Some{a}
    case x:
      None{}

# the vote of the node p at the place w, with the nodes whose passes allow
# it, if s holds it
def Cast.act(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  w: Ledgers.Where,
  p: String
) -> Maybe<&2, Ledgers.Act>:
  Cast.act.of(
    ~mach,
    Ledgers.State.get(~Machine.Q(mach), State.ledger(~mach, s), Ledgers.Slot.vote(w, p))
  )

# the nodes that the vote m names, if m is a vote
def Act.from(m: Maybe<&2, Ledgers.Act>) -> List<&2, String>:
  match m:
    case Some{Ledgers.Act.Vote{v, from}}:
      from
    case x:
      []

# the nodes whose passes allow the vote of the node p at the place w, as the
# vote names them
def Cast.from(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  w: Ledgers.Where,
  p: String
) -> List<&2, String>:
  Act.from(Cast.act(~mach, s, w, p))

# the highest round, up to k, to which the node n passed at the height h of
# the line c (0: it passed to none)
def Round.mine(
  ~mach: Machine(),
  +n: String,
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  +h: U32,
  k: Nat
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
          Ledgers.State.passed(
            ~Machine.Q(mach),
            State.ledger(~mach, s),
            Ledgers.Where{c, h, 1n+p},
            n
          )
        ),
        u => 1n+p,
        u => Round.mine(~mach, n, s, c, h, p)
      )

# the vote m of the round r, as a last vote, else what rest gives
def Last.or(
  r: Nat,
  m: Maybe<&2, Ledgers.Vote>,
  rest: Unit -> Maybe<&2, Ledgers.Last>
) -> Maybe<&2, Ledgers.Last>:
  match m:
    case Some{v}:
      Some{Ledgers.Last{r, v}}
    case None{}:
      rest(Unit{})

# the last vote of the node n at the height h of the line c, in a round up to
# k, if it cast one
def Last.mine(
  ~mach: Machine(),
  +n: String,
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  +h: U32,
  k: Nat
) -> Maybe<&2, Ledgers.Last>:
  match k:
    case 0n:
      Last.or(0n, Cast.of(~mach, s, Ledgers.Where{c, h, 0n}, n), u => None{})
    case 1n+(+p):
      Last.or(
        1n+p,
        Cast.of(~mach, s, Ledgers.Where{c, h, 1n+p}, n),
        u => Last.mine(~mach, n, s, c, h, p)
      )

# the last vote of the node n at the height h of the line c, in a round below
# r, if it cast one
def Last.below(
  ~mach: Machine(),
  n: String,
  s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  h: U32,
  r: Nat
) -> Maybe<&2, Ledgers.Last>:
  match r:
    case 0n:
      None{}
    case 1n+p:
      Last.mine(~mach, n, s, c, h, p)

# the nodes of os whose pass to the place w the node s holds
def Passes.of(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  +w: Ledgers.Where,
  os: List<&2, String>
) -> List<&2, String>:
  match os:
    case Nil{}:
      []
    case Con{+o, r}:
      List.filter.put(
        String,
        o,
        Passes.of(~mach, s, w, r),
        Maybe.is_some(
          &2,
          Maybe<&2, Ledgers.Last>,
          Ledgers.State.passed(~Machine.Q(mach), State.ledger(~mach, s), w, o)
        )
      )

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

# the last vote of the highest round that the passes of the nodes from to the
# place w name, if any names one
def Passes.last(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  +w: Ledgers.Where,
  from: List<&2, String>
) -> Maybe<&2, Ledgers.Last>:
  match from:
    case Nil{}:
      None{}
    case Con{o, r}:
      Last.newer(
        Passed.last(Ledgers.State.passed(~Machine.Q(mach), State.ledger(~mach, s), w, o)),
        Passes.last(~mach, s, w, r)
      )

# the nodes from are a majority of the owners os
def Owners.major(os: List<&2, String>, +from: List<&2, String>) -> Bool:
  Nat.is_lt(
    List.length(&2, String, os),
    Nat.add(List.length(&2, String, from), List.length(&2, String, from))
  )

# the last vote m, if any, is for the step v
def Last.is(m: Maybe<&2, Ledgers.Last>, v: Ledgers.Vote) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{Ledgers.Last{r, x}}:
      Ledgers.Vote.is_eq(x, v)

# the node s holds the pass to the place w of each of the nodes from
def Passed.all(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  +w: Ledgers.Where,
  from: List<&2, String>
) -> Bool:
  match from:
    case Nil{}:
      True{}
    case Con{o, r}:
      List.all.if(
        u => Passed.all(~mach, s, w, r),
        Maybe.is_some(
          &2,
          Maybe<&2, Ledgers.Last>,
          Ledgers.State.passed(~Machine.Q(mach), State.ledger(~mach, s), w, o)
        )
      )

# the nodes from are some of the owners os, each once, in their order
def Owners.sub(os: List<&2, String>, from: List<&2, String>) -> Bool:
  match os from:
    case Nil{} Nil{}:
      True{}
    case Nil{} Con{f, fs}:
      False{}
    case Con{o, r} Nil{}:
      True{}
    case Con{o, +r} Con{+f, +fs}:
      Shared.Bool.when(Bool, String.eq(f, o), u => Owners.sub(r, fs), u => Owners.sub(r, f <> fs))

# the passes of the nodes from allow a vote for the step v at the place w of
# the owners os: in the first round, any step; later, the node holds the pass
# to w of each of them, they are owners and a majority, and v is the last vote
# of the highest round among them, if any
def Vote.allowed(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  +w: Ledgers.Where,
  +os: List<&2, String>,
  v: Ledgers.Vote,
  +from: List<&2, String>
) -> Bool:
  List.any.if(
    u => List.all.if(
      u2 => List.all.if(
        u3 => List.all.if(u4 => Last.is(Passes.last(~mach, s, w, from), v), Owners.major(os, from)),
        Owners.sub(os, from)
      ),
      Passed.all(~mach, s, w, from)
    ),
    Nat.is_eq(Where.round(w), 0n)
  )

# the plan of the proposer of a later round at the place w, once the nodes
# from that passed to it are known: none until they are a majority; then the
# last vote of the highest round among them, else what waits at the proposer
def Plan.later(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  t: Tip,
  th: Maybe<&2, Hashes.Hash>,
  os: List<&2, String>,
  +from: List<&2, String>,
  m: Maybe<&2, Ledgers.Last>
) -> Plan<Machine.Q(mach)>:
  match m:
    case None{}:
      Shared.Bool.when(
        Plan<Machine.Q(mach)>,
        Owners.major(os, from),
        u => Plan.own(~mach, ~kern, s, c, t, from),
        u => Plan{[], None{}, []}
      )
    case Some{Ledgers.Last{r, v}}:
      Shared.Bool.when(
        Plan<Machine.Q(mach)>,
        Owners.major(os, from),
        u => Plan.copy(~mach, ~kern, s, c, t, th, Some{v}, from),
        u => Plan{[], None{}, []}
      )

# the plan of the proposer at the place w
def Plan.lead(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  +w: Ledgers.Where,
  +t: Tip,
  th: Maybe<&2, Hashes.Hash>,
  +os: List<&2, String>
) -> Plan<Machine.Q(mach)>:
  +from = Passes.of(~mach, s, w, os)
  Shared.Bool.when(
    Plan<Machine.Q(mach)>,
    Nat.is_eq(Where.round(w), 0n),
    u => Plan.own(~mach, ~kern, s, c, t, []),
    u => Plan.later(~mach, ~kern, s, c, t, th, os, from, Passes.last(~mach, s, w, from))
  )

# the plan of another owner at the place w, once what the proposer did there
# is known (m): the proposer's step, when its passes allow it
def Plan.follow(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  w: Ledgers.Where,
  t: Tip,
  th: Maybe<&2, Hashes.Hash>,
  os: List<&2, String>,
  m: Maybe<&2, Ledgers.Act>
) -> Plan<Machine.Q(mach)>:
  match m:
    case Some{Ledgers.Act.Vote{+v, +from}}:
      Shared.Bool.when(
        Plan<Machine.Q(mach)>,
        Vote.allowed(~mach, s, w, os, v, from),
        u => Plan.copy(~mach, ~kern, s, c, t, th, Some{v}, from),
        u => Plan{[], None{}, []}
      )
    case x:
      Plan{[], None{}, []}

# what the node n casts for at the place w of the line c, at the tip t of the
# hash th, with the owners os, when it is turn's turn to propose
def Plan.of(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  n: String,
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  +w: Ledgers.Where,
  +t: Tip,
  +th: Maybe<&2, Hashes.Hash>,
  +os: List<&2, String>,
  turn: Maybe<&2, String>
) -> Plan<Machine.Q(mach)>:
  match turn:
    case None{}:
      Plan{[], None{}, []}
    case Some{+p}:
      Shared.Bool.when(
        Plan<Machine.Q(mach)>,
        String.eq(p, n),
        u => Plan.lead(~mach, ~kern, s, c, w, t, th, os),
        u => Plan.follow(~mach, ~kern, s, c, w, t, th, os, Cast.act(~mach, s, w, p))
      )

# s with the node n's pass to the place w, when n is one of the owners os and
# did not pass to w: it names its last vote at the height, in a round below
def Pass.to(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +n: String,
  +s: Node<Machine.Q(mach)>,
  +w: Ledgers.Where,
  os: List<&2, String>
) -> Node<Machine.Q(mach)>:
  match w:
    case Ledgers.Where{+c, +h, +r}:
      Shared.Bool.when(
        Node<Machine.Q(mach)>,
        List.all.if(
          u => Maybe.is_none(
            &2,
            Maybe<&2, Ledgers.Last>,
            Ledgers.State.passed(
              ~Machine.Q(mach),
              State.ledger(~mach, s),
              Ledgers.Where{c, h, r},
              n
            )
          ),
          List.contains(~String, ~String.eq, os, n)
        ),
        u => Cast.seal(
          ~mach,
          ~kern,
          s,
          Ledgers.Where{c, h, r},
          n,
          Ledgers.Act.Pass{Last.below(~mach, n, s, c, h, r)},
          Seal.chain(~mach, ~kern, s, Where.store(Ledgers.Where{c, h, r}), n)
        ),
        u => s
      )

# s, after the owner n joined the highest round of which it holds a ballot at
# the height h of the line c: a node casts in the round that the others reached
def Round.join(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +n: String,
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  +h: U32,
  os: List<&2, String>
) -> Node<Machine.Q(mach)>:
  +top = Round.seen(~mach, s, c, h)
  Shared.Bool.when(
    Node<Machine.Q(mach)>,
    Nat.is_lt(Round.mine(~mach, n, s, c, h, top), top),
    u => Pass.to(~mach, ~kern, n, s, Ledgers.Where{c, h, top}, os),
    u => s
  )

# s with the vote of the node n at the place w for the plan p, when the plan
# has a request
def Cast.plan(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  n: String,
  w: Ledgers.Where,
  th: Maybe<&2, Hashes.Hash>,
  +p: Plan<Machine.Q(mach)>,
  +s: Node<Machine.Q(mach)>
) -> Node<Machine.Q(mach)>:
  Shared.Bool.when(
    Node<Machine.Q(mach)>,
    Bool.not(List.is_empty(&2, Ledgers.Id, Plan.asks(~mach, p))),
    u => Cast.put(
      ~mach,
      ~kern,
      n,
      w,
      th,
      Plan.asks(~mach, p),
      Plan.from(~mach, p),
      Plan.run(~mach, p),
      s
    ),
    u => s
  )

# Node.cast in the round of the node n at the height next of the line c, at
# the tip t of the hash th
def Cast.round(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +n: String,
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  +next: U32,
  +th: Maybe<&2, Hashes.Hash>,
  +t: Tip
) -> Node<Machine.Q(mach)>:
  +os = Tip.owners(t)
  +r = Round.mine(~mach, n, s, c, next, Round.seen(~mach, s, c, next))
  +w = {Ledgers.Where{c, next, r}: Ledgers.Where}
  Shared.Bool.when(
    Node<Machine.Q(mach)>,
    Cast.free(~mach, n, s, w, t),
    u => Cast.plan(~mach, ~kern, n, w, th, Plan.of(~mach, ~kern, n, s, c, w, t, th, os, Owners.turn(os, U32.add(next, U32.from_nat(r)))), s),
    u => s
  )

# Node.cast at the head h of the line c, whose tip is m
def Cast.at(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +n: String,
  s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  h: Head,
  m: Maybe<&2, Tip>
) -> Node<Machine.Q(mach)>:
  match h m:
    case Head{r, b, +next, th} Some{+t}:
      Cast.round(
        ~mach,
        ~kern,
        n,
        Round.join(~mach, ~kern, n, s, c, next, Tip.owners(t)),
        c,
        next,
        th,
        t
      )
    case x y:
      s

# Node.pass at the head h of the line c, whose tip is m
def Pass.at(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +n: String,
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  h: Head,
  m: Maybe<&2, Tip>
) -> Node<Machine.Q(mach)>:
  match h m:
    case Head{r, b, +next, th} Some{t}:
      k = Round.seen(~mach, s, c, next)
      Pass.to(
        ~mach,
        ~kern,
        n,
        s,
        Ledgers.Where{c, next, 1n+Round.mine(~mach, n, s, c, next, k)},
        Tip.owners(t)
      )
    case x y:
      s

# Node.pass once the head m of the line c is known
def Pass.head(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  n: String,
  +s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  m: Maybe<&2, Head>
) -> Node<Machine.Q(mach)>:
  match m:
    case None{}:
      s
    case Some{+h}:
      Pass.at(~mach, ~kern, n, s, c, h, Head.tip(~mach, s, h))

# Node.cast once the head m of the line c is known
def Cast.head(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  n: String,
  +s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  m: Maybe<&2, Head>
) -> Node<Machine.Q(mach)>:
  match m:
    case None{}:
      s
    case Some{+h}:
      Cast.at(~mach, ~kern, n, s, c, h, Head.tip(~mach, s, h))

# s, after the node n cast its ballot for the next step of the line c, in its
# round (Rounds): when it is its turn, the step that the rules of the round
# give it; else the step that the owner whose turn it is cast, when the rules
# allow it and the node's own run of it gives the same tip
def Node.cast(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  n: String,
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain
) -> Node<Machine.Q(mach)>:
  Cast.head(~mach, ~kern, n, s, c, Node.head_of(~mach, s, c))

# the state m at the head h of the line c, after a step that ran qs, else s
def Advance.moved(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  m: Maybe<&2, Node<Machine.Q(mach)>>,
  c: Ledgers.Chain,
  h: Head,
  qs: List<&2, Ledgers.Id>
) -> Node<Machine.Q(mach)>:
  match m:
    case None{}:
      s
    case Some{s3}:
      State.moved(~mach, State.led(~mach, s, State.ledger(~mach, s3)), c, h, qs)

# s at the head of the next height of the line c, when the run m of the
# decided requests qs gives the tip that the ballots name (after): a node
# checks a step before it keeps it
def Advance.ran(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  r: Ledgers.Id,
  b: Maybe<&2, String>,
  next: U32,
  after: Maybe<&2, Hashes.Hash>,
  qs: List<&2, Ledgers.Id>,
  m: Maybe<&2, Run<Machine.Q(mach)>>
) -> Node<Machine.Q(mach)>:
  match m:
    case None{}:
      s
    case Some{Run{s2, +t2}}:
      Shared.Bool.when(
        Node<Machine.Q(mach)>,
        Root.same(after, Some{Tip.hash(t2)}),
        u => Advance.moved(
          ~mach,
          s,
          State.put(~mach, s2, [Tip.words(t2)]),
          c,
          Head{r, b, U32.inc(next), Some{Tip.hash(t2)}},
          qs
        ),
        u => s
      )

# Node.advance once the step m that the owners decided at the head is known
def Advance.step(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  h: Head,
  t: Tip,
  m: Maybe<&2, Ledgers.Vote>
) -> Node<Machine.Q(mach)>:
  match h m:
    case Head{r, b, next, th} Some{Ledgers.Vote{before, +qs, after}}:
      Shared.Bool.when(
        Node<Machine.Q(mach)>,
        Root.same(before, th),
        u => Advance.ran(~mach, s, c, r, b, next, after, qs, Step.run(~mach, ~kern, s, c, t, qs)),
        u => s
      )
    case x y:
      s

# the step m, if any, else the step that rest gives
def Vote.first(
  m: Maybe<&2, Ledgers.Vote>,
  rest: Unit -> Maybe<&2, Ledgers.Vote>
) -> Maybe<&2, Ledgers.Vote>:
  match m:
    case Some{v}:
      Some{v}
    case None{}:
      rest(Unit{})

# the step that the owners os decided at the height h of the line c, in a
# round up to k, the highest first, if they did. The rounds of a height decide
# one step (Height.One), so the order does not matter
def Height.decide(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  +h: U32,
  +os: List<&2, String>,
  k: Nat
) -> Maybe<&2, Ledgers.Vote>:
  match k:
    case 0n:
      Ledgers.State.decide(~Machine.Q(mach), State.ledger(~mach, s), Ledgers.Where{c, h, 0n}, os)
    case 1n+(+p):
      Vote.first(
        Ledgers.State.decide(
          ~Machine.Q(mach),
          State.ledger(~mach, s),
          Ledgers.Where{c, h, 1n+p},
          os
        ),
        u => Height.decide(~mach, s, c, h, os, p)
      )

# that the rounds of the height h of the line c decide one step in s, for the
# owners os: a law of rounds, and a premise of the laws of agreement
def Height.One(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  h: U32,
  os: List<&2, String>
) -> Type:
  @r1: Nat -> @r2: Nat -> @v1: Ledgers.Vote -> @v2: Ledgers.Vote -> {
    Ledgers.State.decide(
      ~Machine.Q(mach),
      State.ledger(~mach, s),
      Ledgers.Where{c, h, r1},
      os
    )
      == Some{v1}: Maybe<&2, Ledgers.Vote>
  } -> {
    Ledgers.State.decide(
      ~Machine.Q(mach),
      State.ledger(~mach, s),
      Ledgers.Where{c, h, r2},
      os
    )
      == Some{v2}: Maybe<&2, Ledgers.Vote>
  } -> {v1 == v2: Ledgers.Vote}

# that the passes that a vote names allow it (Vote.allowed), for the owners os
def Rounds.Allow(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  h: U32,
  os: List<&2, String>
) -> Type:
  @r: Nat -> @q: String -> @v: Ledgers.Vote -> {
    Cast.of(~mach, s, Ledgers.Where{c, h, r}, q) == Some{v}: Maybe<&2, Ledgers.Vote>
  } -> {
    Vote.allowed(
      ~mach,
      s,
      Ledgers.Where{c, h, r},
      os,
      v,
      Cast.from(~mach, s, Ledgers.Where{c, h, r}, q)
    )
      == True{}: Bool
  }

# that a pass names the last vote of its node below its round: a node that
# passed to a round casts no vote below it
def Rounds.Last(~mach: Machine(), s: Node<Machine.Q(mach)>, c: Ledgers.Chain, h: U32) -> Type:
  @r: Nat -> @q: String -> @l: Maybe<
    &2,
    Ledgers.Last> -> {
    Ledgers.State.passed(
      ~Machine.Q(mach),
      State.ledger(~mach, s),
      Ledgers.Where{c, h, r},
      q
    )
      == Some{l}: Maybe<&2, Maybe<&2, Ledgers.Last>>
  } -> {l == Last.below(~mach, q, s, c, h, r): Maybe<&2, Ledgers.Last>}

# that the votes of one round are for one step: one owner proposes, and the
# others copy
def Rounds.Same(~mach: Machine(), s: Node<Machine.Q(mach)>, c: Ledgers.Chain, h: U32) -> Type:
  @r: Nat -> @q1: String -> @q2: String -> @a: Ledgers.Vote -> @b: Ledgers.Vote -> {
    Cast.of(~mach, s, Ledgers.Where{c, h, r}, q1) == Some{a}: Maybe<&2, Ledgers.Vote>
  } -> {
    Cast.of(~mach, s, Ledgers.Where{c, h, r}, q2) == Some{b}: Maybe<&2, Ledgers.Vote>
  } -> {a == b: Ledgers.Vote}

# that the ballots that s holds on the line c follow the rules of rounds, at
# the next height of each head whose tip s holds, for the owners in that tip
def Rounds.Rules(~mach: Machine(), s: Node<Machine.Q(mach)>, c: Ledgers.Chain) -> Type:
  @x: Head -> @t: Tip -> {
    Head.tip(~mach, s, x) == Some{t}: Maybe<&2, Tip>
  } -> Rounds.Allow(
    ~mach,
    s,
    c,
    Head.next(x),
    Tip.owners(t)
  )
    & (Rounds.Last(~mach, s, c, Head.next(x)) & Rounds.Same(~mach, s, c, Head.next(x)))

# Node.advance at the head h of the line c, whose tip is m
def Advance.at(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  +h: Head,
  m: Maybe<&2, Tip>
) -> Node<Machine.Q(mach)>:
  match m:
    case None{}:
      s
    case Some{+t}:
      Advance.step(
        ~mach,
        ~kern,
        s,
        c,
        h,
        t,
        Height.decide(
          ~mach,
          s,
          c,
          Head.next(h),
          Tip.owners(t),
          Round.seen(~mach, s, c, Head.next(h))
        )
      )

# Node.advance once the head m of the line c is known
def Advance.head(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  m: Maybe<&2, Head>
) -> Node<Machine.Q(mach)>:
  match m:
    case None{}:
      s
    case Some{+h}:
      Advance.at(~mach, ~kern, s, c, h, Head.tip(~mach, s, h))

# s, with its head of the line c moved over the next step, when a majority of
# the owners in its tip cast it and the node's own run of it gives the same
# tip
def Node.advance(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain
) -> Node<Machine.Q(mach)>:
  Advance.head(~mach, ~kern, s, c, Node.head_of(~mach, s, c))

# the heads a and b are at the same height, or one is none
def Heads.level(a: Maybe<&2, Head>, b: Maybe<&2, Head>) -> Bool:
  match a b:
    case Some{x} Some{y}:
      U32.is_eq(Head.next(x), Head.next(y))
    case x y:
      True{}

# Node.advances once the head m of the line c is known
def Advances.at(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  f: Nat,
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  m: Maybe<&2, Head>
) -> Node<Machine.Q(mach)>:
  match f m:
    case 1n+p Some{+h}:
      +s1 = Advance.at(~mach, ~kern, s, c, h, Head.tip(~mach, s, h))
      +m1 = Node.head_of(~mach, s1, c)
      Shared.Bool.when(
        Node<Machine.Q(mach)>,
        Heads.level(Some{h}, m1),
        u => s1,
        u => Advances.at(~mach, ~kern, p, s1, c, m1)
      )
    case g x:
      s

# s, with its head of the line c moved over each step that is decided, f
# steps at most
def Node.advances(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  f: Nat,
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain
) -> Node<Machine.Q(mach)>:
  Advances.at(~mach, ~kern, f, s, c, Node.head_of(~mach, s, c))

# s, after the node n moved its head of the line c over each step that is
# decided, cast its ballot for the next step, and moved its head again
def Step.head(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  n: String,
  s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain
) -> Node<Machine.Q(mach)>:
  s1 = Node.advances(~mach, ~kern, 4294967295n, s, c)
  Node.advances(~mach, ~kern, 4294967295n, Node.cast(~mach, ~kern, n, s1, c), c)

# s, after the node n did what it can on the line c
def Node.step(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  n: String,
  s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain
) -> Node<Machine.Q(mach)>:
  Step.head(~mach, ~kern, n, Node.open(~mach, s, c), c)

# s, after the owner n passed to the next round of the next step of the line
# c, and did what it can there: the round took too long (the proposer may be
# away). Transport asks for this; the core has no clock
def Node.pass(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +n: String,
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain
) -> Node<Machine.Q(mach)>:
  Node.step(~mach, ~kern, n, Pass.head(~mach, ~kern, n, s, c, Node.head_of(~mach, s, c)), c)

# s, after the node n took in the new request q of e
def Node.ask.new(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  n: String,
  +s: Node<Machine.Q(mach)>,
  +e: Envelope,
  +q: Machine.Q(mach)
) -> Node<Machine.Q(mach)>:
  +i = Envelope.of(e)
  c = Arrival.chain(i, Machine.arrival(mach)(q))
  s1 = Node.arrive(
    ~mach,
    ~kern,
    State.led(
      ~mach,
      s,
      Ledgers.State.ask(
        ~Machine.Q(mach),
        ~Machine.same(mach),
        State.ledger(~mach, s),
        i,
        Envelope.time(e),
        q
      )
    ),
    i,
    q
  )
  Node.step(~mach, ~kern, n, s1, c)

# Node.ask once the cell m of the request's ID is known
def Node.ask.at(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  n: String,
  +s: Node<Machine.Q(mach)>,
  +e: Envelope,
  q: Machine.Q(mach),
  m: Maybe<&2, Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>>
) -> Node<Machine.Q(mach)>:
  match m:
    case Some{x}:
      s
    case None{}:
      Node.ask.new(
        ~mach,
        ~kern,
        n,
        State.keyed(~mach, s, Keys.mark(State.keys(~mach, s), Envelope.of(e))),
        e,
        q
      )

# s, after the node n took in the request q of e, cast its ballot when it owns
# its line, and moved its head when that decides the step. A request ID that s
# holds counts once: asked again, it changes nothing
def Node.ask(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  n: String,
  +s: Node<Machine.Q(mach)>,
  +e: Envelope,
  q: Machine.Q(mach)
) -> Node<Machine.Q(mach)>:
  Node.ask.at(
    ~mach,
    ~kern,
    n,
    s,
    e,
    q,
    Ledgers.State.get(~Machine.Q(mach), State.ledger(~mach, s), Ledgers.Slot.ask(Envelope.of(e)))
  )

# s, once it holds each request among the cells cs whose slot was empty in the
# ledger old: a request that the node held does not arrive again
def Take.asks(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  cs: List<&2, Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>>,
  +old: Ledgers.State(Machine.Q(mach)),
  +s: Node<Machine.Q(mach)>
) -> Node<Machine.Q(mach)>:
  match cs:
    case Nil{}:
      s
    case Con{Cells.One{Ledgers.Entry.Ask{+i, t, q}}, rest}:
      Take.asks(
        ~mach,
        ~kern,
        rest,
        old,
        Shared.Bool.when(
          Node<Machine.Q(mach)>,
          Maybe.is_none(
            &2,
            Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>,
            Ledgers.State.get(~Machine.Q(mach), old, Ledgers.Slot.ask(i))
          ),
          u => Node.arrive(~mach, ~kern, s, i, q),
          u => s
        )
      )
    case Con{c, rest}:
      Take.asks(~mach, ~kern, rest, old, s)

# l with the requests and the data among the cells cs, each in the slot that
# its own content names (a request by its ID, data by its hash). A ballot, a
# cell that is not one entry, and the slot that the sender gave are not kept:
# what another node sent is read, not believed
def Take.clean(
  ~mach: Machine(),
  cs: List<&2, Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>>,
  l: Ledgers.State(Machine.Q(mach))
) -> Ledgers.State(Machine.Q(mach)):
  match cs:
    case Nil{}:
      l
    case Con{Cells.One{Ledgers.Entry.Ask{i, t, q}}, rest}:
      Take.clean(~mach, rest, Ledgers.State.ask(~Machine.Q(mach), ~Machine.same(mach), l, i, t, q))
    case Con{Cells.One{Ledgers.Entry.Data{ws}}, rest}:
      Take.clean(~mach, rest, Ledgers.State.put_data(~Machine.Q(mach), ~Machine.same(mach), l, ws))
    case Con{c, rest}:
      Take.clean(~mach, rest, l)

# Node.consent once the line m of the request is known
def Consent.at(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  n: String,
  +s: Node<Machine.Q(mach)>,
  i: Ledgers.Id,
  m: Maybe<&2, Ledgers.Chain>
) -> Node<Machine.Q(mach)>:
  match m:
    case None{}:
      s
    case Some{c}:
      Node.step(~mach, ~kern, n, State.keyed(~mach, s, Keys.mark(State.keys(~mach, s), i)), c)

# s, after a writer connected to the node n asked for the request i, which s
# holds already (it came from another node): the request counts once, and the
# node now casts for it as one that was asked at it
def Node.consent(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  n: String,
  +s: Node<Machine.Q(mach)>,
  +i: Ledgers.Id
) -> Node<Machine.Q(mach)>:
  Consent.at(~mach, ~kern, n, s, i, Node.chain_of(~mach, s, i))

# the hash of the node that the look l lacks, if it lacks one
def Look.lack(l: Trees.Look) -> Maybe<&2, Hashes.Hash>:
  match l:
    case Trees.Look.Missing{x}:
      Some{x}
    case Trees.Look.Found{v}:
      None{}
    case Trees.Look.Absent{}:
      None{}

# the hash of the node that a read of the key k of the tree whose root is h
# lacks in s, if it lacks one: what the node asks another node for. A node
# keeps the part of a store that it uses, and fetches the rest on demand
def Node.lacks(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  h: Maybe<&2, Hashes.Hash>,
  k: List<&2, U32>
) -> Maybe<&2, Hashes.Hash>:
  Look.lack(Node.look(~mach, s, h, k))

# l with the data m, if any
def Serve.put(
  ~mach: Machine(),
  m: Maybe<&2, List<&2, U32>>,
  l: Ledgers.State(Machine.Q(mach))
) -> Ledgers.State(Machine.Q(mach)):
  match m:
    case None{}:
      l
    case Some{ws}:
      Ledgers.State.put_data(~Machine.Q(mach), ~Machine.same(mach), l, ws)

# the data that s holds under the hashes hs, as a ledger: what a node sends
# to a node that asks for them (Node.fetch)
def Node.serve(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  hs: List<&2, Hashes.Hash>
) -> Ledgers.State(Machine.Q(mach)):
  match hs:
    case Nil{}:
      Ledgers.State.empty(~Machine.Q(mach))
    case Con{h, r}:
      Serve.put(
        ~mach,
        Ledgers.State.data(~Machine.Q(mach), State.ledger(~mach, s), h),
        Node.serve(~mach, s, r)
      )

# what the ledger r lacks of s: what a sync from s to a holder of r sends
def Node.missing(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  r: Ledgers.State(Machine.Q(mach))
) -> Ledgers.State(Machine.Q(mach)):
  Ledgers.State.missing(~Machine.Q(mach), ~Machine.same(mach), State.ledger(~mach, s), r)

# what a node reads of the ledger t that another node sent: each request and
# each data, in the slot that its own content names (Take.clean)
def Node.reads(
  ~mach: Machine(),
  t: Ledgers.State(Machine.Q(mach))
) -> Ledgers.State(Machine.Q(mach)):
  Take.clean(
    ~mach,
    Tries.Trie.values(Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>, t),
    Ledgers.State.empty(~Machine.Q(mach))
  )

# the ballots among the cells cs
def Ballots.of(
  ~mach: Machine(),
  cs: List<&2, Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>>
) -> List<&2, Ledgers.Ballot>:
  match cs:
    case Nil{}:
      []
    case Con{Cells.One{Ledgers.Entry.Vote{b}}, rest}:
      b <> Ballots.of(~mach, rest)
    case Con{c, rest}:
      Ballots.of(~mach, rest)

# Node.take once the cells new that s lacks of t are known: a sync reads them
# once
def Take.of(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +s: Node<Machine.Q(mach)>,
  t: Ledgers.State(Machine.Q(mach)),
  new: List<&2, Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>>
) -> Node<Machine.Q(mach)>:
  +sent = Node.reads(~mach, t)
  Sealed.take(
    ~mach,
    ~kern,
    Ballots.of(~mach, new),
    Take.asks(
      ~mach,
      ~kern,
      Tries.Trie.values(Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>, sent),
      State.ledger(~mach, s),
      State.led(~mach, s, Ledgers.State.take(~Machine.Q(mach), State.ledger(~mach, s), sent))
    )
  )

# what a holder of s keeps of t, which another node sent. It checks everything
# before it keeps it: a request and data go to the slot that their own content
# names (Take.clean; data is read only under its hash), in the slots where s
# holds nothing; a ballot is kept when its node's chain leads to it and its
# key signs it (a ballot that it cannot check yet comes again with the next
# sync). Nothing that s holds is lost or changed. Each new request waits on
# its line: the cost is what t brings, not what s holds
def Node.take(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +s: Node<Machine.Q(mach)>,
  +t: Ledgers.State(Machine.Q(mach))
) -> Node<Machine.Q(mach)>:
  Take.of(
    ~mach,
    ~kern,
    s,
    t,
    Tries.Trie.values(
      Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>,
      Ledgers.State.missing(~Machine.Q(mach), ~Machine.same(mach), t, State.ledger(~mach, s))
    )
  )

# s, after the node n did what it can on each line of cs
def Node.steps(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +n: String,
  cs: List<&2, Ledgers.Chain>,
  s: Node<Machine.Q(mach)>
) -> Node<Machine.Q(mach)>:
  match cs:
    case Nil{}:
      s
    case Con{c, rest}:
      Node.steps(~mach, ~kern, n, rest, Node.step(~mach, ~kern, n, s, c))

# the line of the first of the waiting requests qs, then rest
def Lines.waiting(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  qs: List<&2, Ledgers.Id>,
  +rest: List<&2, Ledgers.Chain>
) -> List<&2, Ledgers.Chain>:
  match qs:
    case Nil{}:
      rest
    case Con{i, r}:
      Maybe.default(
        &2,
        List<&2, Ledgers.Chain>,
        Maybe.bind(
          &2,
          Ledgers.Chain,
          List<&2, Ledgers.Chain>,
          Node.chain_of(~mach, s, i),
          c => Some{c <> rest}
        ),
        rest
      )

# the lines of the lists of waiting requests qss
def Lines.waits(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  qss: List<&2, List<&2, Ledgers.Id>>
) -> List<&2, Ledgers.Chain>:
  match qss:
    case Nil{}:
      []
    case Con{qs, r}:
      Lines.waiting(~mach, s, qs, Lines.waits(~mach, s, r))

# the lines of the requests and the ballots among the cells cs, then rest
def Lines.new(
  ~mach: Machine(),
  cs: List<&2, Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>>,
  rest: List<&2, Ledgers.Chain>
) -> List<&2, Ledgers.Chain>:
  match cs:
    case Nil{}:
      rest
    case Con{Cells.One{Ledgers.Entry.Ask{i, t, q}}, r}:
      Arrival.chain(i, Machine.arrival(mach)(q)) <> Lines.new(~mach, r, rest)
    case Con{Cells.One{Ledgers.Entry.Vote{b}}, r}:
      Where.line(Ballot.at(b)) <> Lines.new(~mach, r, rest)
    case Con{c, r}:
      Lines.new(~mach, r, rest)

# Sync.lines once the cells new that s lacks of what was sent are known
def Lines.of(
  ~mach: Machine(),
  +s1: Node<Machine.Q(mach)>,
  new: List<&2, Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>>
) -> List<&2, Ledgers.Chain>:
  Tries.Trie.unique(
    ~Ledgers.Chain,
    ~Ledgers.Chain.key,
    Lines.new(
      ~mach,
      new,
      Lines.waits(~mach, s1, Tries.Trie.values(List<&2, Ledgers.Id>, State.waiting(~mach, s1)))
    ),
    Tries.Trie.new(Unit)
  )

# the lines that a sync of t into s may move, each once: those of the new
# requests and ballots of t, and those with waiting requests (new data can let
# them run). So a sync costs about what it brings, not every line of the node
def Sync.lines(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  s1: Node<Machine.Q(mach)>,
  t: Ledgers.State(Machine.Q(mach))
) -> List<&2, Ledgers.Chain>:
  Lines.of(
    ~mach,
    s1,
    Tries.Trie.values(
      Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>,
      Ledgers.State.missing(~Machine.Q(mach), ~Machine.same(mach), t, State.ledger(~mach, s))
    )
  )

# the node b holds every entry that the node a holds: its ledger only grew
def Node.grows(~mach: Machine(), a: Node<Machine.Q(mach)>, b: Node<Machine.Q(mach)>) -> Bool:
  Ledgers.State.grows(
    ~Machine.Q(mach),
    ~Machine.same(mach),
    State.ledger(~mach, a),
    State.ledger(~mach, b)
  )

# the tip that the step m names, if any
def Vote.tip(m: Maybe<&2, Ledgers.Vote>) -> Maybe<&2, Hashes.Hash>:
  match m:
    case Some{Ledgers.Vote{before, qs, after}}:
      after
    case None{}:
      None{}

# the head x one height up, at the tip y
def Head.up(x: Head, y: Hashes.Hash) -> Head:
  match x:
    case Head{r, b, n, th}:
      Head{r, b, U32.inc(n), Some{y}}

# the head x after the step m (none: no step, or one that names no tip)
def Head.moved(x: Head, m: Maybe<&2, Ledgers.Vote>) -> Maybe<&2, Head>:
  Maybe.bind(&2, Hashes.Hash, Head, Vote.tip(m), y => Some{Head.up(x, y)})

# the step that the owners in the tip of the head x decided next on the line
# c, in the round r, if they did
def Advance.in(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  +x: Head,
  r: Nat
) -> Maybe<&2, Ledgers.Vote>:
  Maybe.bind(
    &2,
    Tip,
    Ledgers.Vote,
    Head.tip(~mach, s, x),
    t => Ledgers.State.decide(
      ~Machine.Q(mach),
      State.ledger(~mach, s),
      Ledgers.Where{c, Head.next(x), r},
      Tip.owners(t)
    )
  )

# the head of the line c after one decided step for each round of rs, the
# last first, from the head h, by the ledger of s alone (none: a step is not
# decided in its round). A law's measure: no node runs it
def Line.at(
  ~mach: Machine(),
  rs: List<&2, Nat>,
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  h: Head
) -> Maybe<&2, Head>:
  match rs:
    case Nil{}:
      Some{h}
    case Con{r, rest}:
      Maybe.bind(
        &2,
        Head,
        Head,
        Line.at(~mach, rest, s, c, h),
        +x => Head.moved(x, Advance.in(~mach, s, c, x, r))
      )

# that b holds, in the log of each line, each key that a holds there
def Node.Keeps(~mach: Machine(), a: Node<Machine.Q(mach)>, b: Node<Machine.Q(mach)>) -> Type:
  @c: Ledgers.Chain -> @k: List<
    &2,
    U32> -> @v: List<
    &2,
    U32> -> {
    Line.get(~mach, a, c, k) == Some{v}: Maybe<&2, List<&2, U32>>
  } -> {Line.get(~mach, b, c, k) == Some{v}: Maybe<&2, List<&2, U32>>}

# the head m has a tip
def Head.held(m: Maybe<&2, Head>) -> Bool:
  match m:
    case Some{Head{r, b, n, Some{t}}}:
      True{}
    case x:
      False{}

# that the head of the line c in s is some decided steps from the head h0, by
# the ledger of s
def Line.Reach(~mach: Machine(), s: Node<Machine.Q(mach)>, c: Ledgers.Chain, h0: Head) -> Type:
  Exists(
    List<&2, Nat>,
    rs => Exists(
      Head,
      h => {
        Node.head_of(~mach, s, c) == Some{h}: Maybe<&2, Head>
      }
        & {Line.at(~mach, rs, s, c, h0) == Some{h}: Maybe<&2, Head>}
    )
  )

# that each head of a that is some decided steps from a head with a tip is,
# in b, some decided steps from it
def Node.On(~mach: Machine(), a: Node<Machine.Q(mach)>, b: Node<Machine.Q(mach)>) -> Type:
  @c: Ledgers.Chain -> @h0: Head -> {
    Head.held(Some{h0}) == True{}: Bool
  } -> Line.Reach(~mach, a, c, h0) -> Line.Reach(~mach, b, c, h0)

# the work m, if any, reads the key k as v
def Work.Reads(
  ~mach: Machine(),
  k: List<&2, U32>,
  v: List<&2, U32>,
  m: Maybe<&2, Work<Machine.Q(mach)>>
) -> Type:
  match m:
    case None{}:
      Unit
    case Some{Work{s2, h2}}:
      {Node.get(~mach, s2, h2, k) == Some{v}: Maybe<&2, List<&2, U32>>}

# the log of the run m, if any, holds an outcome of the request i
def Run.Outs(~mach: Machine(), m: Maybe<&2, Run<Machine.Q(mach)>>, i: Ledgers.Id) -> Type:
  match m:
    case None{}:
      Unit
    case Some{Run{s, t}}:
      {Maybe.is_some(&2, List<&2, U32>, Node.get(~mach, s, Tip.log(t), Log.out(i))) == True{}: Bool}

# the ledger of a node with a new ledger is that ledger
def Led.led(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  l: Ledgers.State(Machine.Q(mach))
) -> {State.ledger(~mach, State.led(~mach, s, l)) == l: Ledgers.State(Machine.Q(mach))}:
  match s:
    case Node{old, hs, ws, ks}:
      {==}

# a new head keeps the ledger
def Led.head(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  h: Head
) -> {
  State.ledger(
    ~mach,
    State.head(~mach, s, c, h)
  )
    == State.ledger(~mach, s): Ledgers.State(Machine.Q(mach))
}:
  match s:
    case Node{l, hs, ws, ks}:
      {==}

# a node grows to itself
def Grows.refl(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>
) -> {Node.grows(~mach, s, s) == True{}: Bool}:
  Ledgers.State.grows_refl(
    ~Machine.Q(mach),
    ~Machine.same(mach),
    ~Machine.laws(mach),
    State.ledger(~mach, s)
  )

# growth composes
def Grows.trans(
  ~mach: Machine(),
  a: Node<Machine.Q(mach)>,
  b: Node<Machine.Q(mach)>,
  c: Node<Machine.Q(mach)>
) -> {
  Node.grows(~mach, a, b) == True{}: Bool
} -> {Node.grows(~mach, b, c) == True{}: Bool} -> {Node.grows(~mach, a, c) == True{}: Bool}:
  Ledgers.State.grows_trans(
    ~Machine.Q(mach),
    ~Machine.same(mach),
    ~Machine.laws(mach),
    State.ledger(~mach, a),
    State.ledger(~mach, b),
    State.ledger(~mach, c)
  )

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in this proof a second use sits in a rewrite motive or an erased argument, and the checker accepts it
# a node with a new ledger grows when the ledger does
def Grows.led(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  l: Ledgers.State(Machine.Q(mach)),
  e: {
    Ledgers.State.grows(
      ~Machine.Q(mach),
      ~Machine.same(mach),
      State.ledger(~mach, s),
      l
    )
      == True{}: Bool
  }
) -> {Node.grows(~mach, s, State.led(~mach, s, l)) == True{}: Bool}:
  %Equal.sym(
    Ledgers.State(Machine.Q(mach)),
    State.ledger(~mach, State.led(~mach, s, l)),
    l,
    Led.led(~mach, s, l)
  ): {
    Ledgers.State.grows(
      ~Machine.Q(mach),
      ~Machine.same(mach),
      State.ledger(~mach, s),
      _
    )
      == True{}: Bool
  }
  e
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# data only grows a node
def Grows.keep(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  +ds: List<&2, List<&2, U32>>
) -> {Node.grows(~mach, s, State.keep(~mach, s, ds)) == True{}: Bool}:
  Grows.led(
    ~mach,
    s,
    Ledgers.State.put_datas(~Machine.Q(mach), ~Machine.same(mach), ds, State.ledger(~mach, s)),
    Ledgers.State.put_datas_grows(
      ~Machine.Q(mach),
      ~Machine.same(mach),
      ~Machine.laws(mach),
      ds,
      State.ledger(~mach, s)
    )
  )

# the work m, if any, is on a node that grew from s
def Work.after(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  m: Maybe<&2, Work<Machine.Q(mach)>>
) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{Work{s2, h}}:
      Node.grows(~mach, s, s2)

# the node m, if any, grew from s
def State.after(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  m: Maybe<&2, Node<Machine.Q(mach)>>
) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{s2}:
      Node.grows(~mach, s, s2)

# a node that is kept when b holds grew from s, when it did
def Put.grows.if(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  -s2: Node<Machine.Q(mach)>,
  b: Bool,
  g: {Node.grows(~mach, s, s2) == True{}: Bool}
) -> {
  State.after(~mach, s, Shared.Maybe.when(Node<Machine.Q(mach)>, b, u => Some{s2})) == True{}: Bool
}:
  match b:
    case True{}:
      g
    case False{}:
      {==}

# data that a node puts and reads back only grows it
def Put.grows(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  +ds: List<&2, List<&2, U32>>
) -> {State.after(~mach, s, State.put(~mach, s, ds)) == True{}: Bool}:
  Put.grows.if(
    ~mach,
    s,
    State.keep(~mach, s, ds),
    Stores.Store.holds(~Node<Machine.Q(mach)>, ~Store.fetch(~mach), State.keep(~mach, s, ds), ds),
    Grows.keep(~mach, s, ds)
  )

# a work on a node that grew
def Work.on.grows(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  m: Maybe<&2, Node<Machine.Q(mach)>>,
  h: Maybe<&2, Hashes.Hash>
) -> {
  State.after(~mach, s, m) == True{}: Bool
} -> {Work.after(~mach, s, Work.on(~mach, m, h)) == True{}: Bool}:
  match m:
    case None{}:
      e => {==}
    case Some{s2}:
      e => e

# a new subtree only grows a node
def Work.of.grows(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  m: Maybe<&2, Trees.Put>
) -> {Work.after(~mach, s, Work.of(~mach, s, m)) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{Trees.Put{h, +ws}}:
      Work.on.grows(~mach, s, State.put(~mach, s, ws), Some{h})(Put.grows(~mach, s, ws))

# a key set in a tree only grows a node
def Set.grows(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  h: Maybe<&2, Hashes.Hash>,
  k: List<&2, U32>,
  x: List<&2, U32>
) -> {Work.after(~mach, s, Work.set(~mach, Work{s, h}, k, x)) == True{}: Bool}:
  Work.of.grows(~mach, s, Node.set(~mach, s, h, k, x))

# the run m, if any, is on a node that grew from s
def Run.after(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  m: Maybe<&2, Run<Machine.Q(mach)>>
) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{Run{s2, t}}:
      Node.grows(~mach, s, s2)

# a run is on its own node
def After.self(
  ~mach: Machine(),
  r: Run<Machine.Q(mach)>
) -> {Run.after(~mach, Run.state(~mach, r), Some{r}) == True{}: Bool}:
  match r:
    case Run{s, t}:
      Grows.refl(~mach, s)

# a run on a node that grew from b is on one that grew from a, when b grew
# from a
def After.trans(
  ~mach: Machine(),
  a: Node<Machine.Q(mach)>,
  b: Node<Machine.Q(mach)>,
  +m: Maybe<&2, Run<Machine.Q(mach)>>,
  e1: {Node.grows(~mach, a, b) == True{}: Bool},
  e2: {Run.after(~mach, b, m) == True{}: Bool}
) -> {Run.after(~mach, a, m) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{Run{s2, t}}:
      Grows.trans(~mach, a, b, s2)(e1)(e2)

# a run, then a run from it, is on a node that grew
def After.bind(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  +m: Maybe<&2, Run<Machine.Q(mach)>>,
  f: Run<Machine.Q(mach)> -> Maybe<&2, Run<Machine.Q(mach)>>,
  hm: {Run.after(~mach, s, m) == True{}: Bool},
  hf: @r: Run<Machine.Q(mach)> -> {Run.after(~mach, Run.state(~mach, r), f(r)) == True{}: Bool}
) -> {
  Run.after(
    ~mach,
    s,
    Maybe.bind(&2, Run<Machine.Q(mach)>, Run<Machine.Q(mach)>, m, f)
  )
    == True{}: Bool
}:
  match m:
    case None{}:
      {==}
    case Some{Run{+s2, +t}}:
      After.trans(~mach, s, s2, f(Run{s2, t}), hm, hf(Run{s2, t}))

# a work on a node that grew from b is on one that grew from a, when b grew
# from a
def Work.after.trans(
  ~mach: Machine(),
  a: Node<Machine.Q(mach)>,
  b: Node<Machine.Q(mach)>,
  m: Maybe<&2, Work<Machine.Q(mach)>>,
  e1: {Node.grows(~mach, a, b) == True{}: Bool},
  e2: {Work.after(~mach, b, m) == True{}: Bool}
) -> {Work.after(~mach, a, m) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{Work{s3, h}}:
      Grows.trans(~mach, a, b, s3)(e1)(e2)

# a key set in a work on a node that grew from s is on a node that grew from s
def Work.set.after(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  m: Maybe<&2, Work<Machine.Q(mach)>>,
  +k: List<&2, U32>,
  +x: List<&2, U32>
) -> {
  Work.after(~mach, s, m) == True{}: Bool
} -> {
  Work.after(
    ~mach,
    s,
    Maybe.bind(&2, Work<Machine.Q(mach)>, Work<Machine.Q(mach)>, m, w => Work.set(~mach, w, k, x))
  )
    == True{}: Bool
}:
  match m:
    case None{}:
      e => {==}
    case Some{Work{+s2, +h}}:
      e => Work.after.trans(
        ~mach,
        s,
        s2,
        Work.set(~mach, Work{s2, h}, k, x),
        e,
        Set.grows(~mach, s2, h, k, x)
      )

# the run of picked requests, with one more request or not
def Add.run(
  ~mach: Machine(),
  b: Bool,
  i: Ledgers.Id,
  p: Picked<Machine.Q(mach)>
) -> {Picked.run(~mach, Picked.add(~mach, b, i, p)) == Picked.run(~mach, p): Run<Machine.Q(mach)>}:
  match p:
    case Picked{r, qs}:
      {==}

# the run m, if any, else r, is on a node that grew from that of r
def Default.run.grows(
  ~mach: Machine(),
  r: Run<Machine.Q(mach)>,
  m: Maybe<&2, Run<Machine.Q(mach)>>
) -> {
  Run.after(~mach, Run.state(~mach, r), m) == True{}: Bool
} -> {
  Node.grows(
    ~mach,
    Run.state(~mach, r),
    Run.state(~mach, Maybe.default(&2, Run<Machine.Q(mach)>, m, r))
  )
    == True{}: Bool
}:
  match m:
    case None{}:
      e => Grows.refl(~mach, Run.state(~mach, r))
    case Some{Run{s2, t}}:
      e => e

# a run that is kept when b holds is on a node that grew, when it is
def Fit.when.grows(
  ~mach: Machine(),
  -s: Node<Machine.Q(mach)>,
  b: Bool,
  -r: Run<Machine.Q(mach)>,
  e: {Run.after(~mach, s, Some{r}) == True{}: Bool}
) -> {
  Run.after(~mach, s, Shared.Maybe.when(Run<Machine.Q(mach)>, b, u => Some{r})) == True{}: Bool
}:
  match b:
    case True{}:
      e
    case False{}:
      {==}

# a run that fits a tip is on a node that grew, when the run is
def Plan.fit.grows(
  ~mach: Machine(),
  -s: Node<Machine.Q(mach)>,
  after: Maybe<&2, Hashes.Hash>,
  m: Maybe<&2, Run<Machine.Q(mach)>>
) -> {
  Run.after(~mach, s, m) == True{}: Bool
} -> {Run.after(~mach, s, Plan.fit(~mach, after, m)) == True{}: Bool}:
  match m:
    case None{}:
      e => {==}
    case Some{Run{s2, t2}}:
      e => Fit.when.grows(~mach, s, Root.same(after, Some{Tip.hash(t2)}), Run{s2, t2}, e)

# the run of one of two plans, each on a node that grew
def Plan.when.grows(
  ~mach: Machine(),
  -s: Node<Machine.Q(mach)>,
  b: Bool,
  -x: Plan<Machine.Q(mach)>,
  -y: Plan<Machine.Q(mach)>,
  hx: {Run.after(~mach, s, Plan.run(~mach, x)) == True{}: Bool},
  hy: {Run.after(~mach, s, Plan.run(~mach, y)) == True{}: Bool}
) -> {
  Run.after(
    ~mach,
    s,
    Plan.run(~mach, Shared.Bool.when(Plan<Machine.Q(mach)>, b, u => x, u => y))
  )
    == True{}: Bool
}:
  match b:
    case True{}:
      hx
    case False{}:
      hy

# a node with the ledger of a node that grew from a grew from a
def Grows.to(
  ~mach: Machine(),
  a: Node<Machine.Q(mach)>,
  b: Node<Machine.Q(mach)>,
  x: Node<Machine.Q(mach)>,
  e: {State.ledger(~mach, x) == State.ledger(~mach, b): Ledgers.State(Machine.Q(mach))},
  g: {Node.grows(~mach, a, b) == True{}: Bool}
) -> {Node.grows(~mach, a, x) == True{}: Bool}:
  %Equal.sym(
    Ledgers.State(Machine.Q(mach)),
    State.ledger(~mach, x),
    State.ledger(~mach, b),
    e
  ): {
    Ledgers.State.grows(
      ~Machine.Q(mach),
      ~Machine.same(mach),
      State.ledger(~mach, a),
      _
    )
      == True{}: Bool
  }
  g

# one of two nodes, each grown from s
def Grows.when(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  b: Bool,
  -x: Node<Machine.Q(mach)>,
  -y: Node<Machine.Q(mach)>,
  hx: {Node.grows(~mach, s, x) == True{}: Bool},
  hy: {Node.grows(~mach, s, y) == True{}: Bool}
) -> {
  Node.grows(~mach, s, Shared.Bool.when(Node<Machine.Q(mach)>, b, u => x, u => y)) == True{}: Bool
}:
  match b:
    case True{}:
      hx
    case False{}:
      hy

# a moved head keeps the ledger
def Led.moved(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  h: Head,
  qs: List<&2, Ledgers.Id>
) -> {
  State.ledger(
    ~mach,
    State.moved(~mach, s, c, h, qs)
  )
    == State.ledger(~mach, s): Ledgers.State(Machine.Q(mach))
}:
  match s:
    case Node{l, hs, ws, ks}:
      {==}

# a request that waits keeps the ledger
def Led.waits(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  i: Ledgers.Id
) -> {
  State.ledger(
    ~mach,
    State.wait(~mach, s, c, i)
  )
    == State.ledger(~mach, s): Ledgers.State(Machine.Q(mach))
}:
  match s:
    case Node{l, hs, ws, ks}:
      {==}

# a node with the ledger of a node that grew from it grew
def Grows.back(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  s3: Node<Machine.Q(mach)>,
  g: {Node.grows(~mach, s, s3) == True{}: Bool}
) -> {Node.grows(~mach, s, State.led(~mach, s, State.ledger(~mach, s3))) == True{}: Bool}:
  Grows.led(~mach, s, State.ledger(~mach, s3), g)

# new keys keep the ledger
def Led.keyed(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  ks: Keys
) -> {
  State.ledger(
    ~mach,
    State.keyed(~mach, s, ks)
  )
    == State.ledger(~mach, s): Ledgers.State(Machine.Q(mach))
}:
  match s:
    case Node{l, hs, ws, old}:
      {==}

# a ballot that a node accepts only grows it
def Accept.at.grows(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  +b: Ledgers.Ballot,
  m: Maybe<&2, Keychain>
) -> {State.after(~mach, s, Seal.accept.at(~mach, s, b, m)) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{+c}:
      Put.grows.if(
        ~mach,
        s,
        State.keyed(
          ~mach,
          State.led(
            ~mach,
            s,
            Ledgers.State.keep(~Machine.Q(mach), ~Machine.same(mach), State.ledger(~mach, s), b)
          ),
          Keys.saw(
            Keys.set(
              State.keys(~mach, s),
              Seal.slot(Ballot.store(b), Ballot.node(b)),
              Keychain.next(c, b)
            ),
            Ballot.at(b)
          )
        ),
        Seal.fits(c, b),
        Grows.to(
          ~mach,
          s,
          State.led(
            ~mach,
            s,
            Ledgers.State.keep(~Machine.Q(mach), ~Machine.same(mach), State.ledger(~mach, s), b)
          ),
          State.keyed(
            ~mach,
            State.led(
              ~mach,
              s,
              Ledgers.State.keep(~Machine.Q(mach), ~Machine.same(mach), State.ledger(~mach, s), b)
            ),
            Keys.saw(
              Keys.set(
                State.keys(~mach, s),
                Seal.slot(Ballot.store(b), Ballot.node(b)),
                Keychain.next(c, b)
              ),
              Ballot.at(b)
            )
          ),
          Led.keyed(
            ~mach,
            State.led(
              ~mach,
              s,
              Ledgers.State.keep(~Machine.Q(mach), ~Machine.same(mach), State.ledger(~mach, s), b)
            ),
            Keys.saw(
              Keys.set(
                State.keys(~mach, s),
                Seal.slot(Ballot.store(b), Ballot.node(b)),
                Keychain.next(c, b)
              ),
              Ballot.at(b)
            )
          ),
          Grows.led(
            ~mach,
            s,
            Ledgers.State.keep(~Machine.Q(mach), ~Machine.same(mach), State.ledger(~mach, s), b),
            Ledgers.State.add_grows(
              ~Machine.Q(mach),
              ~Machine.same(mach),
              ~Machine.laws(mach),
              State.ledger(~mach, s),
              Ledgers.Slot.of(b),
              Ledgers.Entry.Vote{b}
            )
          )
        )
      )

# the node m, if any, else s, grew from s when m did
def Default.grows(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  m: Maybe<&2, Node<Machine.Q(mach)>>
) -> {
  State.after(~mach, s, m) == True{}: Bool
} -> {Node.grows(~mach, s, Maybe.default(&2, Node<Machine.Q(mach)>, m, s)) == True{}: Bool}:
  match m:
    case None{}:
      e => Grows.refl(~mach, s)
    case Some{s2}:
      e => e

# a sealed ballot only grows a node
def Cast.seal.grows(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +s: Node<Machine.Q(mach)>,
  +w: Ledgers.Where,
  n: String,
  a0: Ledgers.Act,
  m: Maybe<&2, Keychain>
) -> {Node.grows(~mach, s, Cast.seal(~mach, ~kern, s, w, n, a0, m)) == True{}: Bool}:
  match m:
    case None{}:
      Grows.refl(~mach, s)
    case Some{Keychain{+j, last, key, f}}:
      +b = Ledgers.Ballot.make(
        Seal.secret(Keys.seed(State.keys(~mach, s)), Where.store(w), j),
        Ledgers.Signed{w, n, a0},
        last,
        Seals.Seal.public(Seal.secret(Keys.seed(State.keys(~mach, s)), Where.store(w), U32.inc(j)))
      )
      Default.grows(
        ~mach,
        s,
        Seal.accept(~mach, ~kern, s, b)
      )(Accept.at.grows(~mach, s, b, Seal.chain(~mach, ~kern, s, Ballot.store(b), Ballot.node(b))))

# a ballot on a node that grew from a, which grew from s, only grows s
def Cast.vote.grows(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +s: Node<Machine.Q(mach)>,
  a: Node<Machine.Q(mach)>,
  m: Maybe<&2, Node<Machine.Q(mach)>>,
  +w: Ledgers.Where,
  +n: String,
  +a0: Ledgers.Act,
  g: {Node.grows(~mach, s, a) == True{}: Bool}
) -> {
  State.after(~mach, a, m) == True{}: Bool
} -> {Node.grows(~mach, s, Cast.vote(~mach, ~kern, s, m, w, n, a0)) == True{}: Bool}:
  match m:
    case None{}:
      e => Grows.refl(~mach, s)
    case Some{+s3}:
      e =>
        +s4 = State.led(~mach, s, State.ledger(~mach, s3))
        Grows.trans(
          ~mach,
          s,
          s4,
          Cast.seal(~mach, ~kern, s4, w, n, a0, Seal.chain(~mach, ~kern, s4, Where.store(w), n))
        )(
          Grows.back(~mach, s, s3, Grows.trans(~mach, s, a, s3)(g)(e))
        )(
          Cast.seal.grows(
            ~mach,
            ~kern,
            s4,
            w,
            n,
            a0,
            Seal.chain(~mach, ~kern, s4, Where.store(w), n)
          )
        )

# a vote only grows a node
def Cast.put.grows(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  n: String,
  w: Ledgers.Where,
  th: Maybe<&2, Hashes.Hash>,
  qs: List<&2, Ledgers.Id>,
  from: List<&2, String>,
  m: Maybe<&2, Run<Machine.Q(mach)>>,
  s: Node<Machine.Q(mach)>
) -> {
  Run.after(~mach, s, m) == True{}: Bool
} -> {Node.grows(~mach, s, Cast.put(~mach, ~kern, n, w, th, qs, from, m, s)) == True{}: Bool}:
  match m:
    case None{}:
      e => Grows.refl(~mach, s)
    case Some{Run{+s2, +t2}}:
      e => Cast.vote.grows(
        ~mach,
        ~kern,
        s,
        s2,
        State.put(~mach, s2, [Tip.words(t2)]),
        w,
        n,
        Ledgers.Act.Vote{Ledgers.Vote{th, qs, Some{Tip.hash(t2)}}, from},
        e
      )(Put.grows(~mach, s2, [Tip.words(t2)]))

# a pass only grows a node
def Pass.to.grows(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +n: String,
  +s: Node<Machine.Q(mach)>,
  w: Ledgers.Where,
  os: List<&2, String>
) -> {Node.grows(~mach, s, Pass.to(~mach, ~kern, n, s, w, os)) == True{}: Bool}:
  match w:
    case Ledgers.Where{+c, +h, +r}:
      Grows.when(
        ~mach,
        s,
        List.all.if(
          u => Maybe.is_none(
            &2,
            Maybe<&2, Ledgers.Last>,
            Ledgers.State.passed(
              ~Machine.Q(mach),
              State.ledger(~mach, s),
              Ledgers.Where{c, h, r},
              n
            )
          ),
          List.contains(~String, ~String.eq, os, n)
        ),
        Cast.seal(
          ~mach,
          ~kern,
          s,
          Ledgers.Where{c, h, r},
          n,
          Ledgers.Act.Pass{Last.below(~mach, n, s, c, h, r)},
          Seal.chain(~mach, ~kern, s, Where.store(Ledgers.Where{c, h, r}), n)
        ),
        s,
        Cast.seal.grows(
          ~mach,
          ~kern,
          s,
          Ledgers.Where{c, h, r},
          n,
          Ledgers.Act.Pass{Last.below(~mach, n, s, c, h, r)},
          Seal.chain(~mach, ~kern, s, Where.store(Ledgers.Where{c, h, r}), n)
        ),
        Grows.refl(~mach, s)
      )

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in this proof a second use sits in a rewrite motive or an erased argument, and the checker accepts it
# a node that joins a round only grows a node
def Round.join.grows(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +n: String,
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  +h: U32,
  os: List<&2, String>
) -> {Node.grows(~mach, s, Round.join(~mach, ~kern, n, s, c, h, os)) == True{}: Bool}:
  +top = Round.seen(~mach, s, c, h)
  k = top
  Grows.when(
    ~mach,
    s,
    Nat.is_lt(Round.mine(~mach, n, s, c, h, k), top),
    Pass.to(~mach, ~kern, n, s, Ledgers.Where{c, h, top}, os),
    s,
    Pass.to.grows(~mach, ~kern, n, s, Ledgers.Where{c, h, top}, os),
    Grows.refl(~mach, s)
  )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# a head moved on a node that grew from a, which grew from s, only grows s
def Advance.moved.grows(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  a: Node<Machine.Q(mach)>,
  m: Maybe<&2, Node<Machine.Q(mach)>>,
  +c: Ledgers.Chain,
  +h: Head,
  +qs: List<&2, Ledgers.Id>,
  g: {Node.grows(~mach, s, a) == True{}: Bool}
) -> {
  State.after(~mach, a, m) == True{}: Bool
} -> {Node.grows(~mach, s, Advance.moved(~mach, s, m, c, h, qs)) == True{}: Bool}:
  match m:
    case None{}:
      e => Grows.refl(~mach, s)
    case Some{+s3}:
      e =>
        +x = State.led(~mach, s, State.ledger(~mach, s3))
        Grows.to(
          ~mach,
          s,
          x,
          State.moved(~mach, x, c, h, qs),
          Led.moved(~mach, x, c, h, qs),
          Grows.back(~mach, s, s3, Grows.trans(~mach, s, a, s3)(g)(e))
        )

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in this proof a second use sits in a rewrite motive or an erased argument, and the checker accepts it
# a checked step only grows a node
def Advance.ran.grows(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  r: Ledgers.Id,
  b: Maybe<&2, String>,
  next: U32,
  after: Maybe<&2, Hashes.Hash>,
  qs: List<&2, Ledgers.Id>,
  m: Maybe<&2, Run<Machine.Q(mach)>>
) -> {
  Run.after(~mach, s, m) == True{}: Bool
} -> {Node.grows(~mach, s, Advance.ran(~mach, s, c, r, b, next, after, qs, m)) == True{}: Bool}:
  match m:
    case None{}:
      e => Grows.refl(~mach, s)
    case Some{Run{+s2, +t2}}:
      e =>
        +hd = {Head{r, b, U32.inc(next), Some{Tip.hash(t2)}}: Head}
        Grows.when(
          ~mach,
          s,
          Root.same(after, Some{Tip.hash(t2)}),
          Advance.moved(~mach, s, State.put(~mach, s2, [Tip.words(t2)]), c, hd, qs),
          s,
          Advance.moved.grows(
            ~mach,
            s,
            s2,
            State.put(~mach, s2, [Tip.words(t2)]),
            c,
            hd,
            qs,
            e
          )(Put.grows(~mach, s2, [Tip.words(t2)])),
          Grows.refl(~mach, s)
        )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# a line that opens only grows a node, once its head m is known
def Open.at.grows(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  m: Maybe<&2, Head>
) -> {Node.grows(~mach, s, Open.at(~mach, s, c, m)) == True{}: Bool}:
  match m:
    case Some{Head{+r, Some{+b}, n, None{}}}:
      +hd = {
        Head{
          r,
          Some{b},
          0,
          Branch.first(~mach, s, b, Node.tip(~mach, s, Ledgers.Chain{r, None{}}))
        }: Head
      }
      Grows.to(
        ~mach,
        s,
        s,
        State.head(~mach, s, c, hd),
        Led.head(~mach, s, c, hd),
        Grows.refl(~mach, s)
      )
    case Some{Head{r, Some{b}, n, Some{t}}}:
      Grows.refl(~mach, s)
    case Some{Head{r, None{}, n, t}}:
      Grows.refl(~mach, s)
    case None{}:
      Grows.refl(~mach, s)

# a first head only grows a node, once the head m of its line is known
def First.at.grows(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  +h: Head,
  m: Maybe<&2, Head>
) -> {Node.grows(~mach, s, First.at(~mach, s, c, h, m)) == True{}: Bool}:
  match m:
    case Some{Head{r, b, n, Some{t}}}:
      Grows.refl(~mach, s)
    case Some{Head{r, b, n, None{}}}:
      Grows.to(
        ~mach,
        s,
        s,
        State.head(~mach, s, c, h),
        Led.head(~mach, s, c, h),
        Grows.refl(~mach, s)
      )
    case None{}:
      Grows.to(
        ~mach,
        s,
        s,
        State.head(~mach, s, c, h),
        Led.head(~mach, s, c, h),
        Grows.refl(~mach, s)
      )

# a first head on a node that grew from a, which grew from s, only grows s
def Start.head.grows(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  a: Node<Machine.Q(mach)>,
  m: Maybe<&2, Node<Machine.Q(mach)>>,
  +c: Ledgers.Chain,
  +h: Head,
  g: {Node.grows(~mach, s, a) == True{}: Bool}
) -> {
  State.after(~mach, a, m) == True{}: Bool
} -> {Node.grows(~mach, s, Start.head(~mach, s, m, c, h)) == True{}: Bool}:
  match m:
    case None{}:
      e => Grows.refl(~mach, s)
    case Some{+s3}:
      e =>
        +x = State.led(~mach, s, State.ledger(~mach, s3))
        Grows.trans(
          ~mach,
          s,
          x,
          State.first(~mach, x, c, h)
        )(
          Grows.back(~mach, s, s3, Grows.trans(~mach, s, a, s3)(g)(e))
        )(First.at.grows(~mach, x, c, h, Node.head_of(~mach, x, c)))

# Start.grows once the content m of the store is known
def Start.with.grows(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  +i: Ledgers.Id,
  os: List<&2, String>,
  m: Maybe<&2, Work<Machine.Q(mach)>>
) -> {
  Work.after(~mach, s, m) == True{}: Bool
} -> {Node.grows(~mach, s, Start.with(~mach, s, i, os, m)) == True{}: Bool}:
  match m:
    case None{}:
      e => Grows.refl(~mach, s)
    case Some{Work{+s2, c}}:
      e =>
        +t = {Tip{c, None{}, 0, os}: Tip}
        Start.head.grows(
          ~mach,
          s,
          s2,
          State.put(~mach, s2, [Tip.words(t)]),
          Ledgers.Chain{i, None{}},
          Head{i, None{}, 0, Some{Tip.hash(t)}},
          e
        )(Put.grows(~mach, s2, [Tip.words(t)]))

# a line that a node follows only grows it, once its head m is known
def Follow.new.grows(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  +r: Ledgers.Id,
  +l: Maybe<&2, String>,
  m: Maybe<&2, Head>
) -> {Node.grows(~mach, s, Follow.new(~mach, s, r, l, m)) == True{}: Bool}:
  match m:
    case Some{h}:
      Grows.refl(~mach, s)
    case None{}:
      Grows.to(
        ~mach,
        s,
        s,
        State.head(~mach, s, Line.chain(r, l), Head{r, l, 0, None{}}),
        Led.head(~mach, s, Line.chain(r, l), Head{r, l, 0, None{}}),
        Grows.refl(~mach, s)
      )

# the ballots that a chain leads to only grow a node, when each one more does
def Follow.step.grows(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  m: Maybe<&2, Node<Machine.Q(mach)>>,
  k: Node<Machine.Q(mach)> -> Node<Machine.Q(mach)>,
  ih: @s2: Node<Machine.Q(mach)> -> {Node.grows(~mach, s2, k(s2)) == True{}: Bool}
) -> {
  State.after(~mach, s, m) == True{}: Bool
} -> {
  Node.grows(
    ~mach,
    s,
    Maybe.default(
      &2,
      Node<Machine.Q(mach)>,
      Maybe.bind(&2, Node<Machine.Q(mach)>, Node<Machine.Q(mach)>, m, s2 => Some{k(s2)}),
      s
    )
  )
    == True{}: Bool
}:
  match m:
    case None{}:
      e => Grows.refl(~mach, s)
    case Some{+s2}:
      e => Grows.trans(~mach, s, s2, k(s2))(e)(ih(s2))

# the ballots that a chain leads to only grow a node
def Follow.grows(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  f: Nat,
  +s: Node<Machine.Q(mach)>,
  +p: Tries.Trie<Ledgers.Ballot>,
  +r: Ledgers.Id,
  +n: String,
  mb: Maybe<&2, Ledgers.Ballot>
) -> {Node.grows(~mach, s, Sealed.follow(~mach, ~kern, f, s, p, r, n, mb)) == True{}: Bool}:
  match f mb:
    case 0n x:
      Grows.refl(~mach, s)
    case 1n+g None{}:
      Grows.refl(~mach, s)
    case 1n+(+g) Some{+b}:
      Follow.step.grows(
        ~mach,
        s,
        Seal.accept(~mach, ~kern, s, b),
        +s2 => Sealed.follow(~mach, ~kern, g, s2, p, r, n, Pending.next(~mach, ~kern, s2, p, r, n)),
        +s2 => Follow.grows(~mach, ~kern, g, s2, p, r, n, Pending.next(~mach, ~kern, s2, p, r, n))
      )(Accept.at.grows(~mach, s, b, Seal.chain(~mach, ~kern, s, Ballot.store(b), Ballot.node(b))))

# the ballots that the chains of some ballots lead to only grow a node
def Each.grows(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +f: Nat,
  bs: List<&2, Ledgers.Ballot>,
  +p: Tries.Trie<Ledgers.Ballot>,
  +s: Node<Machine.Q(mach)>
) -> {Node.grows(~mach, s, Sealed.each(~mach, ~kern, f, bs, p, s)) == True{}: Bool}:
  match bs:
    case Nil{}:
      Grows.refl(~mach, s)
    case Con{+b, +rest}:
      +s1 = Sealed.follow(
        ~mach,
        ~kern,
        f,
        s,
        p,
        Ballot.store(b),
        Ballot.node(b),
        Pending.next(~mach, ~kern, s, p, Ballot.store(b), Ballot.node(b))
      )
      Grows.trans(
        ~mach,
        s,
        s1,
        Sealed.each(~mach, ~kern, f, rest, p, s1)
      )(
        Follow.grows(
          ~mach,
          ~kern,
          f,
          s,
          p,
          Ballot.store(b),
          Ballot.node(b),
          Pending.next(~mach, ~kern, s, p, Ballot.store(b), Ballot.node(b))
        )
      )(Each.grows(~mach, ~kern, f, rest, p, s1))

# that the log of the run m, if any, reads the key k2 as v
def Run.Keeps(
  ~mach: Machine(),
  k2: List<&2, U32>,
  v: List<&2, U32>,
  m: Maybe<&2, Run<Machine.Q(mach)>>
) -> Type:
  match m:
    case None{}:
      Unit
    case Some{Run{s2, t2}}:
      {Node.get(~mach, s2, Tip.log(t2), k2) == Some{v}: Maybe<&2, List<&2, U32>>}

# a request, and who asks for it
type Request<-Q: Data> is Data:
  Request{envelope: Envelope, ask: Q}

# s, after the node n took in the request m, if any
def Adopt.ask(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  n: String,
  s: Node<Machine.Q(mach)>,
  m: Maybe<&2, Request<Machine.Q(mach)>>
) -> Node<Machine.Q(mach)>:
  match m:
    case None{}:
      s
    case Some{Request{e, q}}:
      Node.ask(~mach, ~kern, n, s, e, q)

# s, after the node n asked for the adoption of the line l of the store r, if
# its owners are not the nodes inside its owner group
def Node.adopt(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  n: String,
  +s: Node<Machine.Q(mach)>,
  r: Ledgers.Id,
  l: Maybe<&2, String>
) -> Node<Machine.Q(mach)>:
  Adopt.ask(~mach, ~kern, n, s, Kernel.follow(mach, kern)(s)(r)(l))

# Adopt.at once the head m of the line is known
def Adopt.head(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  n: String,
  s: Node<Machine.Q(mach)>,
  m: Maybe<&2, Head>
) -> Node<Machine.Q(mach)>:
  match m:
    case None{}:
      s
    case Some{Head{r, b, next, t}}:
      Node.adopt(~mach, ~kern, n, s, r, b)

# s, after the node n asked for the adoption of the line c, if s follows c:
# a change of a group reaches each line that the group owns by a step of the
# line, which a node asks for by itself when it works on the line
def Adopt.at(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  n: String,
  +s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain
) -> Node<Machine.Q(mach)>:
  Adopt.head(~mach, ~kern, n, s, Node.head_of(~mach, s, c))

# Adopt.at for the line m, if any
def Adopt.maybe(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  n: String,
  s: Node<Machine.Q(mach)>,
  m: Maybe<&2, Ledgers.Chain>
) -> Node<Machine.Q(mach)>:
  match m:
    case None{}:
      s
    case Some{c}:
      Adopt.at(~mach, ~kern, n, s, c)

# s, after the node n asked for the adoption of each of the lines cs
def Node.adopts(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +n: String,
  cs: List<&2, Ledgers.Chain>,
  s: Node<Machine.Q(mach)>
) -> Node<Machine.Q(mach)>:
  match cs:
    case Nil{}:
      s
    case Con{c, rest}:
      Node.adopts(~mach, ~kern, n, rest, Adopt.at(~mach, ~kern, n, s, c))

# the heads of each of the lines cs are at the same height in a and in b
def Lines.level(
  ~mach: Machine(),
  cs: List<&2, Ledgers.Chain>,
  +a: Node<Machine.Q(mach)>,
  +b: Node<Machine.Q(mach)>
) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{+c, r}:
      List.all.if(
        u => Lines.level(~mach, r, a, b),
        Heads.level(Node.head_of(~mach, a, c), Node.head_of(~mach, b, c))
      )

# s, after it took the ballots bs (k of them, pd by where each waits) in again
# and did what it can on the lines cs, until no head moves, f times at most. A ballot whose key the store gives
# at a later height is kept once the node is there: one sync catches up over
# each change of a key
def Sync.more(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  f: Nat,
  +n: String,
  +cs: List<&2, Ledgers.Chain>,
  +k: Nat,
  +bs: List<&2, Ledgers.Ballot>,
  +pd: Tries.Trie<Ledgers.Ballot>,
  +s: Node<Machine.Q(mach)>
) -> Node<Machine.Q(mach)>:
  match f:
    case 0n:
      s
    case 1n+p:
      +s2 = Node.steps(~mach, ~kern, n, cs, Sealed.each(~mach, ~kern, k, bs, pd, s))
      Shared.Bool.when(
        Node<Machine.Q(mach)>,
        Lines.level(~mach, cs, s, s2),
        u => s2,
        u => Sync.more(~mach, ~kern, p, n, cs, k, bs, pd, s2)
      )

# s, after the node n took in t, which another node sent, did what it can on
# each line that this may move, and asked for the adoption of each: how a
# node that is behind catches up
def Node.sync(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +n: String,
  +s: Node<Machine.Q(mach)>,
  +t: Ledgers.State(Machine.Q(mach))
) -> Node<Machine.Q(mach)>:
  +new = Tries.Trie.values(
    Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>,
    Ledgers.State.missing(~Machine.Q(mach), ~Machine.same(mach), t, State.ledger(~mach, s))
  )
  +s1 = Take.of(~mach, ~kern, s, t, new)
  +cs = Lines.of(~mach, s1, new)
  +bs = Ballots.of(~mach, new)
  +k = List.length(&2, Ledgers.Ballot, bs)
  Node.adopts(
    ~mach,
    ~kern,
    n,
    cs,
    Sync.more(~mach, ~kern, k, n, cs, k, bs, Pending.of(bs), Node.steps(~mach, ~kern, n, cs, s1))
  )

# the bytes under the root m, if any, when s holds their rope
def Root.bytes(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  m: Maybe<&2, Ropes.Root>
) -> Maybe<&2, Texts.Bytes()>:
  Maybe.bind(
    &2,
    Ropes.Root,
    Texts.Bytes(),
    m,
    r => Ropes.Rope.read(~Node<Machine.Q(mach)>, ~Store.fetch(~mach), s, r)
  )

# x is the byte that ends a line
def Byte.is_end(x: U32) -> Bool:
  U32.is_eq(x, 10)

# the rope of the bytes b, cut after each line: content is stored once by
# hash, and two contents share every part that an edit did not touch
def Bytes.rope(b: Texts.Bytes()) -> Ropes.Put:
  Ropes.Rope.put(Ropes.Rope.cut(~U32, ~Byte.is_end, b))

# s with the bytes b: the nodes of their rope, each under its hash. A node
# keeps new bytes before it asks for a write of their content
def Node.keep(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  b: Texts.Bytes()
) -> Node<Machine.Q(mach)>:
  State.keep(~mach, s, Ropes.Put.nodes(Bytes.rope(b)))

# what a node does next: it takes in a request, or what another node sent,
# or it does a sync, or it keeps new bytes, or a writer connected to it asks
# for a request that it holds, or it passes to the next round on a line
type Deed<-Q: Data> is Data:
  Deed.Ask{envelope: Envelope, ask: Q}
  Deed.Take{sent: Ledgers.State(Q)}
  Deed.Sync{sent: Ledgers.State(Q)}
  Deed.Keep{bytes: Texts.Bytes()}
  Deed.Consent{id: Ledgers.Id}
  Deed.Pass{line: Ledgers.Chain}

# s, after the node n did ev
def Node.does(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +n: String,
  +s: Node<Machine.Q(mach)>,
  ev: Deed<Machine.Q(mach)>
) -> Node<Machine.Q(mach)>:
  match ev:
    case Deed.Ask{+e, +q}:
      Adopt.at(
        ~mach,
        ~kern,
        n,
        Node.ask(~mach, ~kern, n, s, e, q),
        Arrival.chain(Envelope.of(e), Machine.arrival(mach)(q))
      )
    case Deed.Take{t}:
      Node.take(~mach, ~kern, s, t)
    case Deed.Sync{t}:
      Node.sync(~mach, ~kern, n, s, t)
    case Deed.Keep{b}:
      Node.keep(~mach, s, b)
    case Deed.Consent{+i}:
      Adopt.maybe(~mach, ~kern, n, Node.consent(~mach, ~kern, n, s, i), Node.chain_of(~mach, s, i))
    case Deed.Pass{+c}:
      Adopt.at(~mach, ~kern, n, Node.pass(~mach, ~kern, n, s, c), c)

# s, after the node n did each of evs, in order: any later state of the node
def Node.after(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +n: String,
  evs: List<&2, Deed<Machine.Q(mach)>>,
  s: Node<Machine.Q(mach)>
) -> Node<Machine.Q(mach)>:
  match evs:
    case Nil{}:
      s
    case Con{ev, rest}:
      Node.after(~mach, ~kern, n, rest, Node.does(~mach, ~kern, n, s, ev))

# the outcome of the request i (none: no step that the node knows decided it)
def Node.out(~mach: Machine(), +s: Node<Machine.Q(mach)>, +i: Ledgers.Id) -> Maybe<&2, Out>:
  Maybe.bind(&2, Ledgers.Chain, Out, Node.chain_of(~mach, s, i), c => Chain.out(~mach, s, c, i))

# the version of the outcome o on the line c, when it took one
def Out.on(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  o: Out
) -> Maybe<&2, Version>:
  match o:
    case Out.Stale{}:
      None{}
    case Out.Taken{n}:
      Chain.version(~mach, s, c, n)

# the version that the request v made on the line c
def Chain.made(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  v: Ledgers.Id
) -> Maybe<&2, Version>:
  Maybe.bind(&2, Out, Version, Chain.out(~mach, s, c, v), o => Out.on(~mach, s, c, o))

# the version that the request v made (none: v is not a version that the node
# knows)
def Node.made(~mach: Machine(), +s: Node<Machine.Q(mach)>, +v: Ledgers.Id) -> Maybe<&2, Version>:
  Maybe.bind(
    &2,
    Ledgers.Chain,
    Version,
    Node.chain_of(~mach, s, v),
    +c => Chain.made(~mach, s, c, v)
  )

# the root of the content of the version v (none: v is not a version)
def Node.root(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  v: Ledgers.Id
) -> Maybe<&2, Maybe<&2, Hashes.Hash>>:
  Maybe.bind(
    &2,
    Version,
    Maybe<&2, Hashes.Hash>,
    Node.made(~mach, s, v),
    x => Some{Version.root(x)}
  )

# the root of the content of the version m, if any (none, or not a version:
# the empty tree)
def Node.root_of(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  m: Maybe<&2, Ledgers.Id>
) -> Maybe<&2, Hashes.Hash>:
  match m:
    case None{}:
      None{}
    case Some{v}:
      Maybe.bind(&2, Maybe<&2, Hashes.Hash>, Hashes.Hash, Node.root(~mach, s, v), h => h)

# a version's place: its line and its number
type Place is Data:
  Place{chain: Ledgers.Chain, number: U32}

# the place on the line c of the outcome o, when it took a version
def Out.place(c: Ledgers.Chain, o: Out) -> Maybe<&2, Place>:
  match o:
    case Out.Stale{}:
      None{}
    case Out.Taken{n}:
      Some{Place{c, n}}

# the place of the version v on the line c, at the tip t
def Place.at(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  v: Ledgers.Id,
  t: Tip
) -> Maybe<&2, Place>:
  Maybe.bind(&2, Out, Place, Line.out(~mach, s, t, v), o => Out.place(c, o))

# the place of the version v on the line c
def Place.on(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  v: Ledgers.Id
) -> Maybe<&2, Place>:
  Maybe.bind(&2, Tip, Place, Node.tip(~mach, s, c), t => Place.at(~mach, s, c, v, t))

# the place of the version v
def Node.place(~mach: Machine(), +s: Node<Machine.Q(mach)>, +v: Ledgers.Id) -> Maybe<&2, Place>:
  Maybe.bind(&2, Ledgers.Chain, Place, Node.chain_of(~mach, s, v), +c => Place.on(~mach, s, c, v))

# the place a is at or after the place b, of the same line
def Place.covers(a: Place, b: Place) -> Bool:
  match a b:
    case Place{c1, n1} Place{c2, n2}:
      U32.is_le(n2, n1)

# the line of the place p
def Place.chain(p: Place) -> Ledgers.Chain:
  match p:
    case Place{c, n}:
      c

# the place of the line c in the value of a version vector's entry
def Place.read(c: Ledgers.Chain, ws: List<&2, U32>) -> Maybe<&2, Place>:
  match ws:
    case Con{n, Nil{}}:
      Some{Place{c, n}}
    case _:
      None{}

# the value of a version vector's entry at the place p
def Place.code(p: Place) -> List<&2, U32>:
  match p:
    case Place{c, n}:
      [n]

# the place q, if any, covers the place p
def Place.covered(m: Maybe<&2, Place>, p: Place) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{q}:
      Place.covers(q, p)

# the first keys of a store are on a node that grew
def Firsts.after(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +s: Node<Machine.Q(mach)>,
  os: List<&2, Owner>,
  +m: Maybe<&2, Work<Machine.Q(mach)>>
) -> {
  Work.after(~mach, s, m) == True{}: Bool
} -> {Work.after(~mach, s, Seal.firsts(~mach, ~kern, os, m)) == True{}: Bool}:
  match os:
    case Nil{}:
      e => e
    case Con{Owner{+n, +k}, r}:
      e => Firsts.after(
        ~mach,
        ~kern,
        s,
        r,
        Maybe.bind(
          &2,
          Work<Machine.Q(mach)>,
          Work<Machine.Q(mach)>,
          m,
          w => Work.set(~mach, w, Machine.seal(mach)(n), Hashes.Hash.code(k, []))
        )
      )(Work.set.after(~mach, s, m, Machine.seal(mach)(n), Hashes.Hash.code(k, []))(e))

# a store that starts only grows a node
def Start.grows(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +s: Node<Machine.Q(mach)>,
  i: Ledgers.Id,
  +os: List<&2, Owner>
) -> {Node.grows(~mach, s, Node.start(~mach, ~kern, s, i, os)) == True{}: Bool}:
  Start.with.grows(
    ~mach,
    s,
    i,
    Owner.names(os),
    Seal.firsts(~mach, ~kern, os, Some{Work{s, None{}}})
  )(Firsts.after(~mach, ~kern, s, os, Some{Work{s, None{}}})(Grows.refl(~mach, s)))

# a new request only grows a node
def Arrive.grows(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +s: Node<Machine.Q(mach)>,
  +i: Ledgers.Id,
  a: Arrival
) -> {Node.grows(~mach, s, Arrive.at(~mach, ~kern, s, i, a)) == True{}: Bool}:
  match a:
    case Arrival.Starts{os}:
      Start.grows(~mach, ~kern, s, i, os)
    case Arrival.Waits{+r, +l}:
      +s1 = Node.follow(~mach, s, r, l)
      Grows.to(
        ~mach,
        s,
        s1,
        State.wait(~mach, s1, Line.chain(r, l), i),
        Led.waits(~mach, s1, Line.chain(r, l), i),
        Follow.new.grows(~mach, s, r, l, Node.head_of(~mach, s, Line.chain(r, l)))
      )

# the new requests among cells only grow a node
def Take.asks.grows(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  cs: List<&2, Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>>,
  +old: Ledgers.State(Machine.Q(mach)),
  +s: Node<Machine.Q(mach)>
) -> {Node.grows(~mach, s, Take.asks(~mach, ~kern, cs, old, s)) == True{}: Bool}:
  match cs:
    case Nil{}:
      Grows.refl(~mach, s)
    case Con{Cells.One{Ledgers.Entry.Ask{+i, t, +q}}, +rest}:
      +s1 = Shared.Bool.when(
        Node<Machine.Q(mach)>,
        Maybe.is_none(
          &2,
          Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>,
          Ledgers.State.get(~Machine.Q(mach), old, Ledgers.Slot.ask(i))
        ),
        u => Node.arrive(~mach, ~kern, s, i, q),
        u => s
      )
      Grows.trans(
        ~mach,
        s,
        s1,
        Take.asks(~mach, ~kern, rest, old, s1)
      )(
        Grows.when(
          ~mach,
          s,
          Maybe.is_none(
            &2,
            Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>,
            Ledgers.State.get(~Machine.Q(mach), old, Ledgers.Slot.ask(i))
          ),
          Node.arrive(~mach, ~kern, s, i, q),
          s,
          Arrive.grows(~mach, ~kern, s, i, Machine.arrival(mach)(q)),
          Grows.refl(~mach, s)
        )
      )(Take.asks.grows(~mach, ~kern, rest, old, s1))
    case Con{Cells.One{Ledgers.Entry.Vote{v}}, rest}:
      Take.asks.grows(~mach, ~kern, rest, old, s)
    case Con{Cells.One{Ledgers.Entry.Data{d}}, rest}:
      Take.asks.grows(~mach, ~kern, rest, old, s)
    case Con{Cells.Many{}, rest}:
      Take.asks.grows(~mach, ~kern, rest, old, s)

# a node that takes in what another node sent only grows
def Take.grows(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +s: Node<Machine.Q(mach)>,
  +t: Ledgers.State(Machine.Q(mach))
) -> {Node.grows(~mach, s, Node.take(~mach, ~kern, s, t)) == True{}: Bool}:
  +sent = Take.clean(
    ~mach,
    Tries.Trie.values(Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>, t),
    Ledgers.State.empty(~Machine.Q(mach))
  )
  +l1 = Ledgers.State.take(~Machine.Q(mach), State.ledger(~mach, s), sent)
  +s1 = State.led(~mach, s, l1)
  +cs = Tries.Trie.values(Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>, sent)
  +s2 = Take.asks(~mach, ~kern, cs, State.ledger(~mach, s), s1)
  +bs = Ballots.of(
    ~mach,
    Tries.Trie.values(
      Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>,
      Ledgers.State.missing(~Machine.Q(mach), ~Machine.same(mach), t, State.ledger(~mach, s))
    )
  )
  Grows.trans(
    ~mach,
    s,
    s1,
    Sealed.take(~mach, ~kern, bs, s2)
  )(
    Grows.led(
      ~mach,
      s,
      l1,
      Ledgers.State.take_grows(
        ~Machine.Q(mach),
        ~Machine.same(mach),
        ~Machine.laws(mach),
        State.ledger(~mach, s),
        sent
      )
    )
  )(
    Grows.trans(
      ~mach,
      s1,
      s2,
      Sealed.take(~mach, ~kern, bs, s2)
    )(
      Take.asks.grows(~mach, ~kern, cs, State.ledger(~mach, s), s1)
    )(Each.grows(~mach, ~kern, List.length(&2, Ledgers.Ballot, bs), bs, Pending.of(bs), s2))
  )

# that the change of the kernel kern only grows the node of a run
def Lawful.Grows(mach: Machine(), kern: Kernel(mach)) -> Type:
  @r: Run<
    Machine.Q(
      mach
    )> -> @c: Ledgers.Chain -> @i: Ledgers.Id -> @q: Machine.Q(
    mach
  ) -> {
    Run.after(~mach, Run.state(~mach, r), Kernel.change(mach, kern)(r)(c)(i)(q)) == True{}: Bool
  }

# that the change of the kernel kern keeps each key of the log of a run
def Lawful.Keeps(mach: Machine(), kern: Kernel(mach)) -> Type:
  @r: Run<
    Machine.Q(
      mach
    )> -> @c: Ledgers.Chain -> @i: Ledgers.Id -> @q: Machine.Q(
    mach
  ) -> @k2: List<
    &2,
    U32> -> @v: List<
    &2,
    U32> -> Run.Keeps(
    ~mach,
    k2,
    v,
    Some{r}
  ) -> Run.Keeps(~mach, k2, v, Kernel.change(mach, kern)(r)(c)(i)(q))

# that the change of the kernel kern gives its request an outcome
def Lawful.Outs(mach: Machine(), kern: Kernel(mach)) -> Type:
  @r: Run<
    Machine.Q(
      mach
    )> -> @c: Ledgers.Chain -> @i: Ledgers.Id -> @q: Machine.Q(
    mach
  ) -> Run.Outs(~mach, Kernel.change(mach, kern)(r)(c)(i)(q), i)

# a lawful kernel of the machine mach: a kernel, and the proofs that its change
# only grows the node, keeps the log, and gives an outcome
def Lawful(mach: Machine()) -> Type:
  &kern: Kernel(
    mach
  ) -> Lawful.Grows(mach, kern)
    & (Lawful.Keeps(mach, kern) & Lawful.Outs(mach, kern))

# the kernel of the lawful kernel l
def Lawful.kernel(-mach: Machine(), l: Lawful(mach)) -> Kernel(mach):
  match l:
    case Tuple{k, p}:
      k

# the change of the lawful kernel l only grows the node of a run
def Lawful.grows(-mach: Machine(), l: Lawful(mach)) -> Lawful.Grows(mach, Lawful.kernel(mach, l)):
  match l:
    case Tuple{k, Tuple{g, p}}:
      g

# the change of the lawful kernel l keeps each key of the log of a run
def Lawful.kept(-mach: Machine(), l: Lawful(mach)) -> Lawful.Keeps(mach, Lawful.kernel(mach, l)):
  match l:
    case Tuple{k, Tuple{g, Tuple{kp, o}}}:
      kp

# the change of the lawful kernel l gives its request an outcome
def Lawful.outs(-mach: Machine(), l: Lawful(mach)) -> Lawful.Outs(mach, Lawful.kernel(mach, l)):
  match l:
    case Tuple{k, Tuple{g, Tuple{kp, o}}}:
      o

# a request that the node holds or not only grows a run's node
def Asked.grows(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  r: Run<Machine.Q(mach)>,
  c: Ledgers.Chain,
  i: Ledgers.Id,
  +a: Maybe<&2, Ledgers.Asked<Machine.Q(mach)>>
) -> {
  Run.after(
    ~mach,
    Run.state(~mach, r),
    Step.asked(~mach, ~Lawful.kernel(mach, lawf), r, c, i, a)
  )
    == True{}: Bool
}:
  match a:
    case None{}:
      {==}
    case Some{Ledgers.Asked{t, q}}:
      Lawful.grows(mach, lawf)(r)(c)(i)(q)

# a request that the log holds or not only grows a run's node
def Fresh.grows(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  +r: Run<Machine.Q(mach)>,
  c: Ledgers.Chain,
  +i: Ledgers.Id,
  +o: Maybe<&2, Out>
) -> {
  Run.after(
    ~mach,
    Run.state(~mach, r),
    Step.fresh(~mach, ~Lawful.kernel(mach, lawf), r, c, i, o)
  )
    == True{}: Bool
}:
  match o:
    case Some{x}:
      After.self(~mach, r)
    case None{}:
      Asked.grows(~mach, ~lawf, r, c, i, Node.asked(~mach, Run.state(~mach, r), i))

# one request of a step only grows a run's node
def One.grows(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  +r: Run<Machine.Q(mach)>,
  c: Ledgers.Chain,
  +i: Ledgers.Id
) -> {
  Run.after(
    ~mach,
    Run.state(~mach, r),
    Step.one(~mach, ~Lawful.kernel(mach, lawf), r, c, i)
  )
    == True{}: Bool
}:
  Fresh.grows(~mach, ~lawf, r, c, i, Line.out(~mach, Run.state(~mach, r), Run.tip(~mach, r), i))

# the requests of a step only grow a run's node
def All.grows(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  +qs: List<&2, Ledgers.Id>,
  +m: Maybe<&2, Run<Machine.Q(mach)>>
) -> {
  Run.after(~mach, s, m) == True{}: Bool
} -> {Run.after(~mach, s, Step.all(~mach, ~Lawful.kernel(mach, lawf), c, qs, m)) == True{}: Bool}:
  match qs:
    case Nil{}:
      h => h
    case Con{+i, rest}:
      h => All.grows(
        ~mach,
        ~lawf,
        s,
        c,
        rest,
        Maybe.bind(
          &2,
          Run<Machine.Q(mach)>,
          Run<Machine.Q(mach)>,
          m,
          r => Step.one(~mach, ~Lawful.kernel(mach, lawf), r, c, i)
        )
      )(
        After.bind(
          ~mach,
          s,
          m,
          r => Step.one(~mach, ~Lawful.kernel(mach, lawf), r, c, i),
          h,
          r => One.grows(~mach, ~lawf, r, c, i)
        )
      )

# a step only grows a node: its run is on a node that keeps every entry
def Run.grows(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  +s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  t: Tip,
  qs: List<&2, Ledgers.Id>
) -> {
  Run.after(~mach, s, Step.run(~mach, ~Lawful.kernel(mach, lawf), s, c, t, qs)) == True{}: Bool
}:
  All.grows(~mach, ~lawf, s, c, qs, Some{Run{s, t}})(Grows.refl(~mach, s))

# the run of the requests that can run is on a node that grew
def Some.grows(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  +c: Ledgers.Chain,
  qs: List<&2, Ledgers.Id>,
  +r: Run<Machine.Q(mach)>
) -> {
  Run.after(
    ~mach,
    Run.state(~mach, r),
    Some{Picked.run(~mach, Step.some(~mach, ~Lawful.kernel(mach, lawf), c, qs, r))}
  )
    == True{}: Bool
}:
  match qs:
    case Nil{}:
      After.self(~mach, r)
    case Con{+i, +rest}:
      +m = Step.one(~mach, ~Lawful.kernel(mach, lawf), r, c, i)
      +r2 = Maybe.default(&2, Run<Machine.Q(mach)>, m, r)
      %Equal.sym(
        Run<Machine.Q(mach)>,
        Picked.run(
          ~mach,
          Picked.add(
            ~mach,
            Maybe.is_some(&2, Run<Machine.Q(mach)>, m),
            i,
            Step.some(~mach, ~Lawful.kernel(mach, lawf), c, rest, r2)
          )
        ),
        Picked.run(~mach, Step.some(~mach, ~Lawful.kernel(mach, lawf), c, rest, r2)),
        Add.run(
          ~mach,
          Maybe.is_some(&2, Run<Machine.Q(mach)>, m),
          i,
          Step.some(~mach, ~Lawful.kernel(mach, lawf), c, rest, r2)
        )
      ): {Run.after(~mach, Run.state(~mach, r), Some{_}) == True{}: Bool}
      After.trans(
        ~mach,
        Run.state(~mach, r),
        Run.state(~mach, r2),
        Some{Picked.run(~mach, Step.some(~mach, ~Lawful.kernel(mach, lawf), c, rest, r2))},
        Default.run.grows(~mach, r, m)(One.grows(~mach, ~lawf, r, c, i)),
        Some.grows(~mach, ~lawf, c, rest, r2)
      )

# the run of the plan of an owner that proposes freely is on a node that grew
def Plan.own.grows(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  t: Tip,
  -from: List<&2, String>
) -> {
  Run.after(
    ~mach,
    s,
    Plan.run(~mach, Plan.own(~mach, ~Lawful.kernel(mach, lawf), s, c, t, from))
  )
    == True{}: Bool
}:
  Some.grows(
    ~mach,
    ~lawf,
    c,
    Cast.mine(~mach, ~Lawful.kernel(mach, lawf), s, Wait.order(~mach, s, c)),
    Run{s, t}
  )

# the run of the plan for a step that another ballot names is on a node that
# grew
def Plan.copy.grows(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  +t: Tip,
  th: Maybe<&2, Hashes.Hash>,
  m: Maybe<&2, Ledgers.Vote>,
  -from: List<&2, String>
) -> {
  Run.after(
    ~mach,
    s,
    Plan.run(~mach, Plan.copy(~mach, ~Lawful.kernel(mach, lawf), s, c, t, th, m, from))
  )
    == True{}: Bool
}:
  match m:
    case None{}:
      {==}
    case Some{Ledgers.Vote{before, +qs, after}}:
      Plan.when.grows(
        ~mach,
        s,
        List.all.if(
          u => Cast.all_mine(~mach, ~Lawful.kernel(mach, lawf), s, qs),
          Root.same(before, th)
        ),
        Plan{
          qs,
          Plan.fit(~mach, after, Step.run(~mach, ~Lawful.kernel(mach, lawf), s, c, t, qs)),
          from
        },
        Plan{[], None{}, []},
        Plan.fit.grows(
          ~mach,
          s,
          after,
          Step.run(~mach, ~Lawful.kernel(mach, lawf), s, c, t, qs)
        )(Run.grows(~mach, ~lawf, s, c, t, qs)),
        {==}
      )

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in this proof a second use sits in a rewrite motive or an erased argument, and the checker accepts it
# the run of the plan of the proposer of a later round is on a node that grew
def Plan.later.grows(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  w: Ledgers.Where,
  t: Tip,
  th: Maybe<&2, Hashes.Hash>,
  os: List<&2, String>,
  from: List<&2, String>,
  m: Maybe<&2, Ledgers.Last>
) -> {
  Run.after(
    ~mach,
    s,
    Plan.run(~mach, Plan.later(~mach, ~Lawful.kernel(mach, lawf), s, c, t, th, os, from, m))
  )
    == True{}: Bool
}:
  match m:
    case None{}:
      Plan.when.grows(
        ~mach,
        s,
        Owners.major(os, from),
        Plan.own(~mach, ~Lawful.kernel(mach, lawf), s, c, t, from),
        Plan{[], None{}, []},
        Plan.own.grows(~mach, ~lawf, s, c, t, from),
        {==}
      )
    case Some{Ledgers.Last{r, v}}:
      Plan.when.grows(
        ~mach,
        s,
        Owners.major(os, from),
        Plan.copy(~mach, ~Lawful.kernel(mach, lawf), s, c, t, th, Some{v}, from),
        Plan{[], None{}, []},
        Plan.copy.grows(~mach, ~lawf, s, c, t, th, Some{v}, from),
        {==}
      )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in this proof a second use sits in a rewrite motive or an erased argument, and the checker accepts it
# the run of the plan of the proposer is on a node that grew
def Plan.lead.grows(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  +w: Ledgers.Where,
  +t: Tip,
  th: Maybe<&2, Hashes.Hash>,
  +os: List<&2, String>
) -> {
  Run.after(
    ~mach,
    s,
    Plan.run(~mach, Plan.lead(~mach, ~Lawful.kernel(mach, lawf), s, c, w, t, th, os))
  )
    == True{}: Bool
}:
  Plan.when.grows(
    ~mach,
    s,
    Nat.is_eq(Where.round(w), 0n),
    Plan.own(~mach, ~Lawful.kernel(mach, lawf), s, c, t, []),
    Plan.later(~mach, ~Lawful.kernel(mach, lawf), s, c, t, th, os, Passes.of(~mach, s, w, os), Passes.last(~mach, s, w, Passes.of(~mach, s, w, os))),
    Plan.own.grows(~mach, ~lawf, s, c, t, []),
    Plan.later.grows(
      ~mach,
      ~lawf,
      s,
      c,
      w,
      t,
      th,
      os,
      Passes.of(~mach, s, w, os),
      Passes.last(~mach, s, w, Passes.of(~mach, s, w, os))
    )
  )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in this proof a second use sits in a rewrite motive or an erased argument, and the checker accepts it
# the run of the plan of another owner is on a node that grew
def Plan.follow.grows(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  +s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  w: Ledgers.Where,
  t: Tip,
  th: Maybe<&2, Hashes.Hash>,
  os: List<&2, String>,
  m: Maybe<&2, Ledgers.Act>
) -> {
  Run.after(
    ~mach,
    s,
    Plan.run(~mach, Plan.follow(~mach, ~Lawful.kernel(mach, lawf), s, c, w, t, th, os, m))
  )
    == True{}: Bool
}:
  match m:
    case Some{Ledgers.Act.Vote{+v, from}}:
      Plan.when.grows(
        ~mach,
        s,
        Vote.allowed(~mach, s, w, os, v, from),
        Plan.copy(~mach, ~Lawful.kernel(mach, lawf), s, c, t, th, Some{v}, from),
        Plan{[], None{}, []},
        Plan.copy.grows(~mach, ~lawf, s, c, t, th, Some{v}, from),
        {==}
      )
    case Some{Ledgers.Act.Pass{l}}:
      {==}
    case None{}:
      {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# the run of what a node casts for is on a node that grew
def Plan.of.grows(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  n: String,
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  +w: Ledgers.Where,
  +t: Tip,
  +th: Maybe<&2, Hashes.Hash>,
  +os: List<&2, String>,
  turn: Maybe<&2, String>
) -> {
  Run.after(
    ~mach,
    s,
    Plan.run(~mach, Plan.of(~mach, ~Lawful.kernel(mach, lawf), n, s, c, w, t, th, os, turn))
  )
    == True{}: Bool
}:
  match turn:
    case None{}:
      {==}
    case Some{+p}:
      Plan.when.grows(
        ~mach,
        s,
        String.eq(p, n),
        Plan.lead(~mach, ~Lawful.kernel(mach, lawf), s, c, w, t, th, os),
        Plan.follow(
          ~mach,
          ~Lawful.kernel(mach, lawf),
          s,
          c,
          w,
          t,
          th,
          os,
          Cast.act(~mach, s, w, p)
        ),
        Plan.lead.grows(~mach, ~lawf, s, c, w, t, th, os),
        Plan.follow.grows(~mach, ~lawf, s, c, w, t, th, os, Cast.act(~mach, s, w, p))
      )

# a ballot in the node's round only grows a node
def Cast.round.grows(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  +n: String,
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  +next: U32,
  +th: Maybe<&2, Hashes.Hash>,
  +t: Tip
) -> {
  Node.grows(
    ~mach,
    s,
    Cast.round(~mach, ~Lawful.kernel(mach, lawf), n, s, c, next, th, t)
  )
    == True{}: Bool
}:
  +os = Tip.owners(t)
  +r = Round.mine(~mach, n, s, c, next, Round.seen(~mach, s, c, next))
  +w = {Ledgers.Where{c, next, r}: Ledgers.Where}
  +p = Plan.of(~mach, ~Lawful.kernel(mach, lawf), n, s, c, w, t, th, os, Owners.turn(os, U32.add(next, U32.from_nat(r))))
  Grows.when(
    ~mach,
    s,
    Cast.free(~mach, n, s, w, t),
    Cast.plan(~mach, ~Lawful.kernel(mach, lawf), n, w, th, p, s),
    s,
    Grows.when(
      ~mach,
      s,
      Bool.not(List.is_empty(&2, Ledgers.Id, Plan.asks(~mach, p))),
      Cast.put(
        ~mach,
        ~Lawful.kernel(mach, lawf),
        n,
        w,
        th,
        Plan.asks(~mach, p),
        Plan.from(~mach, p),
        Plan.run(~mach, p),
        s
      ),
      s,
      Cast.put.grows(
        ~mach,
        ~Lawful.kernel(mach, lawf),
        n,
        w,
        th,
        Plan.asks(~mach, p),
        Plan.from(~mach, p),
        Plan.run(~mach, p),
        s
      )(
        Plan.of.grows(
          ~mach,
          ~lawf,
          n,
          s,
          c,
          w,
          t,
          th,
          os,
          Owners.turn(os, U32.add(next, U32.from_nat(r)))
        )
      ),
      Grows.refl(~mach, s)
    ),
    Grows.refl(~mach, s)
  )

# Node.cast only grows a node, at the head h whose tip is m
def Cast.at.grows(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  +n: String,
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  h: Head,
  m: Maybe<&2, Tip>
) -> {
  Node.grows(~mach, s, Cast.at(~mach, ~Lawful.kernel(mach, lawf), n, s, c, h, m)) == True{}: Bool
}:
  match h m:
    case Head{r, b, +next, +th} Some{+t}:
      +s1 = Round.join(~mach, ~Lawful.kernel(mach, lawf), n, s, c, next, Tip.owners(t))
      Grows.trans(
        ~mach,
        s,
        s1,
        Cast.round(~mach, ~Lawful.kernel(mach, lawf), n, s1, c, next, th, t)
      )(
        Round.join.grows(~mach, ~Lawful.kernel(mach, lawf), n, s, c, next, Tip.owners(t))
      )(Cast.round.grows(~mach, ~lawf, n, s1, c, next, th, t))
    case Head{r, b, next, th} None{}:
      Grows.refl(~mach, s)

# Node.cast only grows a node, once the head m is known
def Cast.head.grows(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  n: String,
  +s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  m: Maybe<&2, Head>
) -> {
  Node.grows(~mach, s, Cast.head(~mach, ~Lawful.kernel(mach, lawf), n, s, c, m)) == True{}: Bool
}:
  match m:
    case None{}:
      Grows.refl(~mach, s)
    case Some{+h}:
      Cast.at.grows(~mach, ~lawf, n, s, c, h, Head.tip(~mach, s, h))

# a node's ballot only grows it
def Cast.grows(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  n: String,
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain
) -> {Node.grows(~mach, s, Node.cast(~mach, ~Lawful.kernel(mach, lawf), n, s, c)) == True{}: Bool}:
  Cast.head.grows(~mach, ~lawf, n, s, c, Node.head_of(~mach, s, c))

# Node.advance only grows a node, once the decided step m is known
def Advance.step.grows(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  h: Head,
  +t: Tip,
  m: Maybe<&2, Ledgers.Vote>
) -> {
  Node.grows(
    ~mach,
    s,
    Advance.step(~mach, ~Lawful.kernel(mach, lawf), s, c, h, t, m)
  )
    == True{}: Bool
}:
  match h m:
    case Head{r, b, next, th} Some{Ledgers.Vote{before, +qs, after}}:
      Grows.when(
        ~mach,
        s,
        Root.same(before, th),
        Advance.ran(
          ~mach,
          s,
          c,
          r,
          b,
          next,
          after,
          qs,
          Step.run(~mach, ~Lawful.kernel(mach, lawf), s, c, t, qs)
        ),
        s,
        Advance.ran.grows(
          ~mach,
          s,
          c,
          r,
          b,
          next,
          after,
          qs,
          Step.run(~mach, ~Lawful.kernel(mach, lawf), s, c, t, qs)
        )(Run.grows(~mach, ~lawf, s, c, t, qs)),
        Grows.refl(~mach, s)
      )
    case Head{r, b, next, th} None{}:
      Grows.refl(~mach, s)

# Node.advance only grows a node, at the head h whose tip is m
def Advance.at.grows(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  +h: Head,
  m: Maybe<&2, Tip>
) -> {
  Node.grows(~mach, s, Advance.at(~mach, ~Lawful.kernel(mach, lawf), s, c, h, m)) == True{}: Bool
}:
  match m:
    case None{}:
      Grows.refl(~mach, s)
    case Some{+t}:
      Advance.step.grows(
        ~mach,
        ~lawf,
        s,
        c,
        h,
        t,
        Height.decide(
          ~mach,
          s,
          c,
          Head.next(h),
          Tip.owners(t),
          Round.seen(~mach, s, c, Head.next(h))
        )
      )

# Advances.grows once the head m is known
def Advances.at.grows(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  f: Nat,
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  m: Maybe<&2, Head>
) -> {
  Node.grows(~mach, s, Advances.at(~mach, ~Lawful.kernel(mach, lawf), f, s, c, m)) == True{}: Bool
}:
  match f m:
    case 0n x:
      Grows.refl(~mach, s)
    case 1n+p None{}:
      Grows.refl(~mach, s)
    case 1n+(+p) Some{+h}:
      +s1 = Advance.at(~mach, ~Lawful.kernel(mach, lawf), s, c, h, Head.tip(~mach, s, h))
      +m1 = Node.head_of(~mach, s1, c)
      Grows.when(
        ~mach,
        s,
        Heads.level(Some{h}, m1),
        s1,
        Advances.at(~mach, ~Lawful.kernel(mach, lawf), p, s1, c, m1),
        Advance.at.grows(~mach, ~lawf, s, c, h, Head.tip(~mach, s, h)),
        Grows.trans(
          ~mach,
          s,
          s1,
          Advances.at(~mach, ~Lawful.kernel(mach, lawf), p, s1, c, m1)
        )(
          Advance.at.grows(~mach, ~lawf, s, c, h, Head.tip(~mach, s, h))
        )(Advances.at.grows(~mach, ~lawf, p, s1, c, m1))
      )

# a head that moves over each decided step only grows a node
def Advances.grows(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  f: Nat,
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain
) -> {
  Node.grows(~mach, s, Node.advances(~mach, ~Lawful.kernel(mach, lawf), f, s, c)) == True{}: Bool
}:
  Advances.at.grows(~mach, ~lawf, f, s, c, Node.head_of(~mach, s, c))

# what a node does at a head only grows it
def Step.head.grows(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  +n: String,
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain
) -> {Node.grows(~mach, s, Step.head(~mach, ~Lawful.kernel(mach, lawf), n, s, c)) == True{}: Bool}:
  +s1 = Node.advances(~mach, ~Lawful.kernel(mach, lawf), 4294967295n, s, c)
  +s2 = Node.cast(~mach, ~Lawful.kernel(mach, lawf), n, s1, c)
  +s3 = Node.advances(~mach, ~Lawful.kernel(mach, lawf), 4294967295n, s2, c)
  Grows.trans(
    ~mach,
    s,
    s1,
    s3
  )(
    Advances.grows(~mach, ~lawf, 4294967295n, s, c)
  )(
    Grows.trans(
      ~mach,
      s1,
      s2,
      s3
    )(Cast.grows(~mach, ~lawf, n, s1, c))(Advances.grows(~mach, ~lawf, 4294967295n, s2, c))
  )

# what a node does on a line only grows it
def Step.grows(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  +n: String,
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain
) -> {Node.grows(~mach, s, Node.step(~mach, ~Lawful.kernel(mach, lawf), n, s, c)) == True{}: Bool}:
  +s1 = Node.open(~mach, s, c)
  Grows.trans(
    ~mach,
    s,
    s1,
    Step.head(~mach, ~Lawful.kernel(mach, lawf), n, s1, c)
  )(Open.at.grows(~mach, s, c, Node.head_of(~mach, s, c)))(Step.head.grows(~mach, ~lawf, n, s1, c))

# a new request only grows a node
def Ask.new.grows(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  +n: String,
  +s: Node<Machine.Q(mach)>,
  +e: Envelope,
  +q: Machine.Q(mach)
) -> {
  Node.grows(~mach, s, Node.ask.new(~mach, ~Lawful.kernel(mach, lawf), n, s, e, q)) == True{}: Bool
}:
  +i = Envelope.of(e)
  +c = Arrival.chain(i, Machine.arrival(mach)(q))
  +l0 = Ledgers.State.ask(
    ~Machine.Q(mach),
    ~Machine.same(mach),
    State.ledger(~mach, s),
    i,
    Envelope.time(e),
    q
  )
  +s0 = State.led(~mach, s, l0)
  +s1 = Node.arrive(~mach, ~Lawful.kernel(mach, lawf), s0, i, q)
  Grows.trans(
    ~mach,
    s,
    s0,
    Node.step(~mach, ~Lawful.kernel(mach, lawf), n, s1, c)
  )(
    Grows.led(
      ~mach,
      s,
      l0,
      Ledgers.State.add_grows(
        ~Machine.Q(mach),
        ~Machine.same(mach),
        ~Machine.laws(mach),
        State.ledger(~mach, s),
        Ledgers.Slot.ask(i),
        Ledgers.Entry.Ask{i, Envelope.time(e), q}
      )
    )
  )(
    Grows.trans(
      ~mach,
      s0,
      s1,
      Node.step(~mach, ~Lawful.kernel(mach, lawf), n, s1, c)
    )(
      Arrive.grows(~mach, ~Lawful.kernel(mach, lawf), s0, i, Machine.arrival(mach)(q))
    )(Step.grows(~mach, ~lawf, n, s1, c))
  )

# Node.ask_grows once the cell m of the request's ID is known
def Ask.at.grows(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  +n: String,
  +s: Node<Machine.Q(mach)>,
  +e: Envelope,
  +q: Machine.Q(mach),
  m: Maybe<&2, Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>>
) -> {
  Node.grows(
    ~mach,
    s,
    Node.ask.at(~mach, ~Lawful.kernel(mach, lawf), n, s, e, q, m)
  )
    == True{}: Bool
}:
  match m:
    case Some{x}:
      Grows.refl(~mach, s)
    case None{}:
      Grows.trans(
        ~mach,
        s,
        State.keyed(~mach, s, Keys.mark(State.keys(~mach, s), Envelope.of(e))),
        Node.ask.new(
          ~mach,
          ~Lawful.kernel(mach, lawf),
          n,
          State.keyed(~mach, s, Keys.mark(State.keys(~mach, s), Envelope.of(e))),
          e,
          q
        )
      )(
        Grows.to(
          ~mach,
          s,
          s,
          State.keyed(~mach, s, Keys.mark(State.keys(~mach, s), Envelope.of(e))),
          Led.keyed(~mach, s, Keys.mark(State.keys(~mach, s), Envelope.of(e))),
          Grows.refl(~mach, s)
        )
      )(
        Ask.new.grows(
          ~mach,
          ~lawf,
          n,
          State.keyed(~mach, s, Keys.mark(State.keys(~mach, s), Envelope.of(e))),
          e,
          q
        )
      )

# a node that takes in a request only grows
def Ask.grows(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  n: String,
  +s: Node<Machine.Q(mach)>,
  +e: Envelope,
  q: Machine.Q(mach)
) -> {
  Node.grows(~mach, s, Node.ask(~mach, ~Lawful.kernel(mach, lawf), n, s, e, q)) == True{}: Bool
}:
  Ask.at.grows(
    ~mach,
    ~lawf,
    n,
    s,
    e,
    q,
    Ledgers.State.get(~Machine.Q(mach), State.ledger(~mach, s), Ledgers.Slot.ask(Envelope.of(e)))
  )

# what a node does on each of some lines only grows it
def Steps.grows(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  +n: String,
  cs: List<&2, Ledgers.Chain>,
  +s: Node<Machine.Q(mach)>
) -> {
  Node.grows(~mach, s, Node.steps(~mach, ~Lawful.kernel(mach, lawf), n, cs, s)) == True{}: Bool
}:
  match cs:
    case Nil{}:
      Grows.refl(~mach, s)
    case Con{+c, +rest}:
      +s1 = Node.step(~mach, ~Lawful.kernel(mach, lawf), n, s, c)
      Grows.trans(
        ~mach,
        s,
        s1,
        Node.steps(~mach, ~Lawful.kernel(mach, lawf), n, rest, s1)
      )(Step.grows(~mach, ~lawf, n, s, c))(Steps.grows(~mach, ~lawf, n, rest, s1))

# an adoption only grows a node, once the request m is known
def Adopt.ask.grows(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  n: String,
  s: Node<Machine.Q(mach)>,
  m: Maybe<&2, Request<Machine.Q(mach)>>
) -> {Node.grows(~mach, s, Adopt.ask(~mach, ~Lawful.kernel(mach, lawf), n, s, m)) == True{}: Bool}:
  match m:
    case None{}:
      Grows.refl(~mach, s)
    case Some{Request{e, q}}:
      Ask.grows(~mach, ~lawf, n, s, e, q)

# an adoption only grows a node, once the head m of the line is known
def Adopt.head.grows(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  n: String,
  +s: Node<Machine.Q(mach)>,
  m: Maybe<&2, Head>
) -> {Node.grows(~mach, s, Adopt.head(~mach, ~Lawful.kernel(mach, lawf), n, s, m)) == True{}: Bool}:
  match m:
    case None{}:
      Grows.refl(~mach, s)
    case Some{Head{r, b, next, t}}:
      Adopt.ask.grows(~mach, ~lawf, n, s, Kernel.follow(mach, Lawful.kernel(mach, lawf))(s)(r)(b))

# the adoption of a line only grows a node
def Adopt.at.grows(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  n: String,
  +s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain
) -> {Node.grows(~mach, s, Adopt.at(~mach, ~Lawful.kernel(mach, lawf), n, s, c)) == True{}: Bool}:
  Adopt.head.grows(~mach, ~lawf, n, s, Node.head_of(~mach, s, c))

# the adoption of each of some lines only grows a node
def Adopts.grows(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  +n: String,
  cs: List<&2, Ledgers.Chain>,
  +s: Node<Machine.Q(mach)>
) -> {
  Node.grows(~mach, s, Node.adopts(~mach, ~Lawful.kernel(mach, lawf), n, cs, s)) == True{}: Bool
}:
  match cs:
    case Nil{}:
      Grows.refl(~mach, s)
    case Con{+c, +rest}:
      Grows.trans(
        ~mach,
        s,
        Adopt.at(~mach, ~Lawful.kernel(mach, lawf), n, s, c),
        Node.adopts(
          ~mach,
          ~Lawful.kernel(mach, lawf),
          n,
          rest,
          Adopt.at(~mach, ~Lawful.kernel(mach, lawf), n, s, c)
        )
      )(
        Adopt.at.grows(~mach, ~lawf, n, s, c)
      )(Adopts.grows(~mach, ~lawf, n, rest, Adopt.at(~mach, ~Lawful.kernel(mach, lawf), n, s, c)))

# more rounds of a sync, grows
def More.grows(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  f: Nat,
  +n: String,
  +cs: List<&2, Ledgers.Chain>,
  +k: Nat,
  +bs: List<&2, Ledgers.Ballot>,
  +pd: Tries.Trie<Ledgers.Ballot>,
  +s: Node<Machine.Q(mach)>
) -> {
  Node.grows(
    ~mach,
    s,
    Sync.more(~mach, ~Lawful.kernel(mach, lawf), f, n, cs, k, bs, pd, s)
  )
    == True{}: Bool
}:
  match f:
    case 0n:
      Grows.refl(~mach, s)
    case 1n+(+p):
      Grows.when(
        ~mach,
        s,
        Lines.level(
          ~mach,
          cs,
          s,
          Node.steps(
            ~mach,
            ~Lawful.kernel(mach, lawf),
            n,
            cs,
            Sealed.each(~mach, ~Lawful.kernel(mach, lawf), k, bs, pd, s)
          )
        ),
        Node.steps(
          ~mach,
          ~Lawful.kernel(mach, lawf),
          n,
          cs,
          Sealed.each(~mach, ~Lawful.kernel(mach, lawf), k, bs, pd, s)
        ),
        Sync.more(
          ~mach,
          ~Lawful.kernel(mach, lawf),
          p,
          n,
          cs,
          k,
          bs,
          pd,
          Node.steps(
            ~mach,
            ~Lawful.kernel(mach, lawf),
            n,
            cs,
            Sealed.each(~mach, ~Lawful.kernel(mach, lawf), k, bs, pd, s)
          )
        ),
        Grows.trans(
          ~mach,
          s,
          Sealed.each(~mach, ~Lawful.kernel(mach, lawf), k, bs, pd, s),
          Node.steps(
            ~mach,
            ~Lawful.kernel(mach, lawf),
            n,
            cs,
            Sealed.each(~mach, ~Lawful.kernel(mach, lawf), k, bs, pd, s)
          )
        )(
          Each.grows(~mach, ~Lawful.kernel(mach, lawf), k, bs, pd, s)
        )(
          Steps.grows(
            ~mach,
            ~lawf,
            n,
            cs,
            Sealed.each(~mach, ~Lawful.kernel(mach, lawf), k, bs, pd, s)
          )
        ),
        Grows.trans(
          ~mach,
          s,
          Node.steps(
            ~mach,
            ~Lawful.kernel(mach, lawf),
            n,
            cs,
            Sealed.each(~mach, ~Lawful.kernel(mach, lawf), k, bs, pd, s)
          ),
          Sync.more(
            ~mach,
            ~Lawful.kernel(mach, lawf),
            p,
            n,
            cs,
            k,
            bs,
            pd,
            Node.steps(
              ~mach,
              ~Lawful.kernel(mach, lawf),
              n,
              cs,
              Sealed.each(~mach, ~Lawful.kernel(mach, lawf), k, bs, pd, s)
            )
          )
        )(
          Grows.trans(
            ~mach,
            s,
            Sealed.each(~mach, ~Lawful.kernel(mach, lawf), k, bs, pd, s),
            Node.steps(
              ~mach,
              ~Lawful.kernel(mach, lawf),
              n,
              cs,
              Sealed.each(~mach, ~Lawful.kernel(mach, lawf), k, bs, pd, s)
            )
          )(
            Each.grows(~mach, ~Lawful.kernel(mach, lawf), k, bs, pd, s)
          )(
            Steps.grows(
              ~mach,
              ~lawf,
              n,
              cs,
              Sealed.each(~mach, ~Lawful.kernel(mach, lawf), k, bs, pd, s)
            )
          )
        )(
          More.grows(
            ~mach,
            ~lawf,
            p,
            n,
            cs,
            k,
            bs,
            pd,
            Node.steps(
              ~mach,
              ~Lawful.kernel(mach, lawf),
              n,
              cs,
              Sealed.each(~mach, ~Lawful.kernel(mach, lawf), k, bs, pd, s)
            )
          )
        )
      )

# a sync only grows a node
def Sync.grows(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  +n: String,
  +s: Node<Machine.Q(mach)>,
  +t: Ledgers.State(Machine.Q(mach))
) -> {Node.grows(~mach, s, Node.sync(~mach, ~Lawful.kernel(mach, lawf), n, s, t)) == True{}: Bool}:
  +s1 = Node.take(~mach, ~Lawful.kernel(mach, lawf), s, t)
  +cs = Sync.lines(~mach, s, s1, t)
  +bs = Ballots.of(
    ~mach,
    Tries.Trie.values(
      Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>,
      Ledgers.State.missing(~Machine.Q(mach), ~Machine.same(mach), t, State.ledger(~mach, s))
    )
  )
  +s2 = Node.steps(~mach, ~Lawful.kernel(mach, lawf), n, cs, s1)
  +s3 = Sync.more(
    ~mach,
    ~Lawful.kernel(mach, lawf),
    List.length(&2, Ledgers.Ballot, bs),
    n,
    cs,
    List.length(&2, Ledgers.Ballot, bs),
    bs,
    Pending.of(bs),
    s2
  )
  Grows.trans(
    ~mach,
    s,
    s1,
    Node.adopts(~mach, ~Lawful.kernel(mach, lawf), n, cs, s3)
  )(
    Take.grows(~mach, ~Lawful.kernel(mach, lawf), s, t)
  )(
    Grows.trans(
      ~mach,
      s1,
      s2,
      Node.adopts(~mach, ~Lawful.kernel(mach, lawf), n, cs, s3)
    )(
      Steps.grows(~mach, ~lawf, n, cs, s1)
    )(
      Grows.trans(
        ~mach,
        s2,
        s3,
        Node.adopts(~mach, ~Lawful.kernel(mach, lawf), n, cs, s3)
      )(
        More.grows(
          ~mach,
          ~lawf,
          List.length(&2, Ledgers.Ballot, bs),
          n,
          cs,
          List.length(&2, Ledgers.Ballot, bs),
          bs,
          Pending.of(bs),
          s2
        )
      )(Adopts.grows(~mach, ~lawf, n, cs, s3))
    )
  )

# Proofs
# ------
# The laws of a replica, and the lemmas that prove them.

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in a proof a second use sits in a rewrite motive or an erased argument, and the checker accepts it
# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof does not run
# bend-lint: expect-begin bend-lint-rules/performance/missed_fork@hint -- a proof does not run
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- in a proof an unused binder is a premise of the proof's own type; a proof does not run
# a first owner reads back
def Owner.code_read(
  x: Owner,
  r: List<&2, U32>
) -> {Owner.code.read(Owner.code(x, r)) == Some{Codes.Read{x, r}}: Maybe<&2, Codes.Read<Owner>>}:
  match x:
    case Owner{n, k}:
      Codes.Code.two_read(
        ~String,
        ~Hashes.Hash,
        ~Owner,
        ~Codes.Code.text.codec(),
        ~Hashes.Hash.codec(),
        a => b => Owner{a, b},
        n,
        k,
        r
      )

# the code of first owners
def Owner.codec() -> Codes.Codec(Owner):
  (Owner.code, (Owner.code.read, x => r => Owner.code_read(x, r)))

# new waiting requests keep the ledger
def Led.wait(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  qs: List<&2, Ledgers.Id>
) -> {
  State.ledger(
    ~mach,
    Wait.set(~mach, s, c, qs)
  )
    == State.ledger(~mach, s): Ledgers.State(Machine.Q(mach))
}:
  match s:
    case Node{l, hs, ws, ks}:
      {==}

# one of two runs, each on a node that grew
def After.when(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  +b: Bool,
  -mx: Maybe<&2, Run<Machine.Q(mach)>>,
  -my: Maybe<&2, Run<Machine.Q(mach)>>,
  hx: {Run.after(~mach, s, mx) == True{}: Bool},
  hy: {Run.after(~mach, s, my) == True{}: Bool}
) -> {
  Run.after(
    ~mach,
    s,
    Shared.Bool.when(Maybe<&2, Run<Machine.Q(mach)>>, b, u => mx, u => my)
  )
    == True{}: Bool
}:
  match b:
    case True{}:
      hx
    case False{}:
      hy

# the node of the work w
def Work.state(~mach: Machine(), w: Work<Machine.Q(mach)>) -> Node<Machine.Q(mach)>:
  match w:
    case Work{s, h}:
      s

# a work is on its own node
def Grown.self(
  ~mach: Machine(),
  w: Work<Machine.Q(mach)>
) -> {Work.after(~mach, Work.state(~mach, w), Some{w}) == True{}: Bool}:
  match w:
    case Work{s, h}:
      Grows.refl(~mach, s)

# a work, then a work from it, is on a node that grew
def Grown.bind(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  +m: Maybe<&2, Work<Machine.Q(mach)>>,
  f: Work<Machine.Q(mach)> -> Maybe<&2, Work<Machine.Q(mach)>>,
  hm: {Work.after(~mach, s, m) == True{}: Bool},
  hf: @w: Work<Machine.Q(mach)> -> {Work.after(~mach, Work.state(~mach, w), f(w)) == True{}: Bool}
) -> {
  Work.after(
    ~mach,
    s,
    Maybe.bind(&2, Work<Machine.Q(mach)>, Work<Machine.Q(mach)>, m, f)
  )
    == True{}: Bool
}:
  match m:
    case None{}:
      {==}
    case Some{Work{+s2, +h}}:
      Work.after.trans(~mach, s, s2, f(Work{s2, h}), hm, hf(Work{s2, h}))

# a work from a value that the node reads is on a node that grew
def Grown.with(
  ~mach: Machine(),
  -A: Data,
  s: Node<Machine.Q(mach)>,
  +ma: Maybe<&2, A>,
  -k: A -> Maybe<&2, Work<Machine.Q(mach)>>,
  hk: @a: A -> {Work.after(~mach, s, k(a)) == True{}: Bool}
) -> {Work.after(~mach, s, Maybe.bind(&2, A, Work<Machine.Q(mach)>, ma, k)) == True{}: Bool}:
  match ma:
    case None{}:
      {==}
    case Some{a}:
      hk(a)

# one of two works, each on a node that grew
def Grown.when(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  +b: Bool,
  -mx: Maybe<&2, Work<Machine.Q(mach)>>,
  -my: Maybe<&2, Work<Machine.Q(mach)>>,
  hx: {Work.after(~mach, s, mx) == True{}: Bool},
  hy: {Work.after(~mach, s, my) == True{}: Bool}
) -> {
  Work.after(
    ~mach,
    s,
    Shared.Bool.when(Maybe<&2, Work<Machine.Q(mach)>>, b, u => mx, u => my)
  )
    == True{}: Bool
}:
  match b:
    case True{}:
      hx
    case False{}:
      hy

# a key set in a work only grows its node
def Grown.set(
  ~mach: Machine(),
  w: Work<Machine.Q(mach)>,
  k: List<&2, U32>,
  x: List<&2, U32>
) -> {Work.after(~mach, Work.state(~mach, w), Work.set(~mach, w, k, x)) == True{}: Bool}:
  match w:
    case Work{s, h}:
      Set.grows(~mach, s, h, k, x)

# words kept in a work only grow its node
def Grown.keep(
  ~mach: Machine(),
  w: Work<Machine.Q(mach)>,
  +ns: List<&2, List<&2, U32>>
) -> {Work.after(~mach, Work.state(~mach, w), Work.keep(~mach, w, ns)) == True{}: Bool}:
  match w:
    case Work{+s, h}:
      Work.on.grows(~mach, s, State.put(~mach, s, ns), h)(Put.grows(~mach, s, ns))

# the first tip m of a branch, if any, is on a node that grew from s
def Made.after(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  m: Maybe<&2, Made<Machine.Q(mach)>>
) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{Made{t, s2}}:
      Node.grows(~mach, s, s2)

# a first tip on a work is on a node that grew
def Grown.made.put(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  t: Tip,
  m: Maybe<&2, Work<Machine.Q(mach)>>
) -> {
  Work.after(~mach, s, m) == True{}: Bool
} -> {Made.after(~mach, s, Made.put(~mach, t, m)) == True{}: Bool}:
  match m:
    case None{}:
      e => {==}
    case Some{Work{s2, l}}:
      e => e

# the verdict m, if any, holds a node that grew from s
def Verdict.after(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  m: Maybe<&2, Verdict<Machine.Q(mach)>>
) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{Verdict.Stale{}}:
      True{}
    case Some{Verdict.Taken{Work{s2, h}}}:
      Node.grows(~mach, s, s2)

# a verdict that takes a work holds its node
def Verdict.take(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  m: Maybe<&2, Work<Machine.Q(mach)>>
) -> {
  Work.after(~mach, s, m) == True{}: Bool
} -> {Verdict.after(~mach, s, Work.take(~mach, m)) == True{}: Bool}:
  match m:
    case None{}:
      e => {==}
    case Some{Work{s2, h}}:
      e => e

# a verdict from a value that the node reads holds a node that grew
def Verdict.with(
  ~mach: Machine(),
  -A: Data,
  s: Node<Machine.Q(mach)>,
  +ma: Maybe<&2, A>,
  -k: A -> Maybe<&2, Verdict<Machine.Q(mach)>>,
  hk: @a: A -> {Verdict.after(~mach, s, k(a)) == True{}: Bool}
) -> {Verdict.after(~mach, s, Maybe.bind(&2, A, Verdict<Machine.Q(mach)>, ma, k)) == True{}: Bool}:
  match ma:
    case None{}:
      {==}
    case Some{a}:
      hk(a)

# the run of a new log is on a node that grew
def Run.logged.grows(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  t: Tip,
  +m: Maybe<&2, Work<Machine.Q(mach)>>,
  e: {Work.after(~mach, s, m) == True{}: Bool}
) -> {Run.after(~mach, s, Run.logged(~mach, t, m)) == True{}: Bool}:
  match t m:
    case x None{}:
      {==}
    case Tip{c, old, n, os} Some{Work{s2, l}}:
      e

# Add.grows once the value m of the key is known
def Add.at.grows(
  ~mach: Machine(),
  r: Run<Machine.Q(mach)>,
  +k: List<&2, U32>,
  +x: List<&2, U32>,
  m: Maybe<&2, List<&2, U32>>
) -> {Run.after(~mach, Run.state(~mach, r), Run.add.at(~mach, r, k, x, m)) == True{}: Bool}:
  match r m:
    case Run{+s, +t} None{}:
      Run.logged.grows(
        ~mach,
        s,
        t,
        Work.set(~mach, Work{s, Tip.log(t)}, k, x),
        Set.grows(~mach, s, Tip.log(t), k, x)
      )
    case y Some{old}:
      {==}

# a new key in a run's log only grows its node
def Add.grows(
  ~mach: Machine(),
  +r: Run<Machine.Q(mach)>,
  +k: List<&2, U32>,
  x: List<&2, U32>
) -> {Run.after(~mach, Run.state(~mach, r), Run.add(~mach, r, k, x)) == True{}: Bool}:
  Add.at.grows(~mach, r, k, x, Node.get(~mach, Run.state(~mach, r), Tip.log(Run.tip(~mach, r)), k))

# a run one version on is on its own node
def Next.grows(
  ~mach: Machine(),
  r: Run<Machine.Q(mach)>,
  own: Maybe<&2, List<&2, String>>
) -> {Run.after(~mach, Run.state(~mach, r), Some{Run.next(~mach, r, own)}) == True{}: Bool}:
  match r:
    case Run{s, t}:
      Grows.refl(~mach, s)

# a refused request only grows a run's node
def Stale.grows(
  ~mach: Machine(),
  r: Run<Machine.Q(mach)>,
  i: Ledgers.Id
) -> {Run.after(~mach, Run.state(~mach, r), Step.stale(~mach, r, i)) == True{}: Bool}:
  Add.grows(~mach, r, Log.out(i), Out.words(Out.Stale{}))

# a taken request only grows a run's node
def Taken.grows(
  ~mach: Machine(),
  +r: Run<Machine.Q(mach)>,
  +i: Ledgers.Id,
  +own: Maybe<&2, List<&2, String>>
) -> {Run.after(~mach, Run.state(~mach, r), Step.taken(~mach, r, i, own)) == True{}: Bool}:
  +n = Tip.count(Run.tip(~mach, r))
  After.bind(
    ~mach,
    Run.state(~mach, r),
    Run.add(~mach, r, Log.out(i), Out.words(Out.Taken{n})),
    +r1 => Maybe.bind(
      &2,
      Run<Machine.Q(mach)>,
      Run<Machine.Q(mach)>,
      Run.add(
        ~mach,
        r1,
        Log.version(n),
        Version.words(Version{i, Tip.content(Run.tip(~mach, r1))})
      ),
      r2 => Some{Run.next(~mach, r2, own)}
    ),
    Add.grows(~mach, r, Log.out(i), Out.words(Out.Taken{n})),
    +r1 => After.bind(
      ~mach,
      Run.state(~mach, r1),
      Run.add(
        ~mach,
        r1,
        Log.version(n),
        Version.words(Version{i, Tip.content(Run.tip(~mach, r1))})
      ),
      r2 => Some{Run.next(~mach, r2, own)},
      Add.grows(
        ~mach,
        r1,
        Log.version(n),
        Version.words(Version{i, Tip.content(Run.tip(~mach, r1))})
      ),
      r2 => Next.grows(~mach, r2, own)
    )
  )

# a judged request only grows a run's node
def Judged.grows(
  ~mach: Machine(),
  +r: Run<Machine.Q(mach)>,
  +i: Ledgers.Id,
  +own: Maybe<&2, List<&2, String>>,
  +m: Maybe<&2, Verdict<Machine.Q(mach)>>
) -> {
  Verdict.after(~mach, Run.state(~mach, r), m) == True{}: Bool
} -> {Run.after(~mach, Run.state(~mach, r), Step.judged(~mach, r, i, own, m)) == True{}: Bool}:
  match m:
    case None{}:
      g => {==}
    case Some{Verdict.Stale{}}:
      g => Stale.grows(~mach, r, i)
    case Some{Verdict.Taken{Work{+s2, +h}}}:
      g => After.trans(
        ~mach,
        Run.state(~mach, r),
        s2,
        Step.taken(~mach, Run.over(~mach, r, s2, h), i, own),
        g,
        Taken.grows(~mach, Run.over(~mach, r, s2, h), i, own)
      )

# a mark on a version only grows a run's node
def Marked.grows(
  ~mach: Machine(),
  +r: Run<Machine.Q(mach)>,
  +i: Ledgers.Id,
  +m: String,
  +v: Maybe<&2, Version>
) -> {Run.after(~mach, Run.state(~mach, r), Step.marked(~mach, r, i, m, v)) == True{}: Bool}:
  match v:
    case None{}:
      {==}
    case Some{+x}:
      After.bind(
        ~mach,
        Run.state(~mach, r),
        Run.add(~mach, r, Log.mark(m), Ledgers.Id.code(Version.id(x), [])),
        r2 => Step.taken(~mach, r2, i, None{}),
        Add.grows(~mach, r, Log.mark(m), Ledgers.Id.code(Version.id(x), [])),
        r2 => Taken.grows(~mach, r2, i, None{})
      )

# a request for a mark only grows a run's node
def Mark.grows(
  ~mach: Machine(),
  +r: Run<Machine.Q(mach)>,
  +i: Ledgers.Id,
  +m: String
) -> {Run.after(~mach, Run.state(~mach, r), Step.mark(~mach, r, i, m)) == True{}: Bool}:
  +s = Run.state(~mach, r)
  +t = Run.tip(~mach, r)
  +n = Tip.count(t)
  After.when(
    ~mach,
    s,
    List.all.if(
      u => Maybe.is_none(&2, Ledgers.Id, Line.mark(~mach, s, t, m)),
      Bool.not(U32.is_eq(n, 0))
    ),
    Step.marked(~mach, r, i, m, Line.version(~mach, s, t, U32.sub(n, 1))),
    Step.stale(~mach, r, i),
    Marked.grows(~mach, r, i, m, Line.version(~mach, s, t, U32.sub(n, 1))),
    Stale.grows(~mach, r, i)
  )

# the first tip of a new branch only grows a run's node
def Branch.made.grows(
  ~mach: Machine(),
  +r: Run<Machine.Q(mach)>,
  +i: Ledgers.Id,
  +b: String,
  m: Maybe<&2, Made<Machine.Q(mach)>>
) -> {
  Made.after(~mach, Run.state(~mach, r), m) == True{}: Bool
} -> {Run.after(~mach, Run.state(~mach, r), Branch.made(~mach, r, i, b, m)) == True{}: Bool}:
  match m:
    case None{}:
      g => {==}
    case Some{Made{+t, +s2}}:
      g =>
        +r1 = {Run.over(~mach, r, s2, Tip.content(Run.tip(~mach, r))): Run<Machine.Q(mach)>}
        After.trans(
          ~mach,
          Run.state(~mach, r),
          s2,
          Maybe.bind(
            &2,
            Run<Machine.Q(mach)>,
            Run<Machine.Q(mach)>,
            Run.add(~mach, r1, Log.start(b), Hashes.Hash.code(Tip.hash(t), [])),
            r2 => Step.taken(~mach, r2, i, None{})
          ),
          g,
          After.bind(
            ~mach,
            s2,
            Run.add(~mach, r1, Log.start(b), Hashes.Hash.code(Tip.hash(t), [])),
            r2 => Step.taken(~mach, r2, i, None{}),
            Add.grows(~mach, r1, Log.start(b), Hashes.Hash.code(Tip.hash(t), [])),
            r2 => Taken.grows(~mach, r2, i, None{})
          )
        )

# Node.pass only grows a node, at the head h whose tip is m
def Pass.at.grows(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +n: String,
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  h: Head,
  m: Maybe<&2, Tip>
) -> {Node.grows(~mach, s, Pass.at(~mach, ~kern, n, s, c, h, m)) == True{}: Bool}:
  match h m:
    case Head{r, b, +next, th} Some{t}:
      Pass.to.grows(
        ~mach,
        ~kern,
        n,
        s,
        Ledgers.Where{c, next, 1n+Round.mine(~mach, n, s, c, next, Round.seen(~mach, s, c, next))},
        Tip.owners(t)
      )
    case Head{r, b, next, th} None{}:
      Grows.refl(~mach, s)

# Node.pass only grows a node, once the head m is known
def Pass.head.grows(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  n: String,
  +s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  m: Maybe<&2, Head>
) -> {Node.grows(~mach, s, Pass.head(~mach, ~kern, n, s, c, m)) == True{}: Bool}:
  match m:
    case None{}:
      Grows.refl(~mach, s)
    case Some{+h}:
      Pass.at.grows(~mach, ~kern, n, s, c, h, Head.tip(~mach, s, h))

# a slot that holds a cell holds one in a node that grew
def Slot.held_kept(
  ~mach: Machine(),
  +a: Node<Machine.Q(mach)>,
  +b: Node<Machine.Q(mach)>,
  +k: List<&2, Bool>,
  g: {Node.grows(~mach, a, b) == True{}: Bool}
) -> {
  Maybe.is_some(
    &2,
    Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>,
    Ledgers.State.get(~Machine.Q(mach), State.ledger(~mach, a), k)
  )
    == True{}: Bool
} -> {
  Maybe.is_some(
    &2,
    Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>,
    Ledgers.State.get(~Machine.Q(mach), State.ledger(~mach, b), k)
  )
    == True{}: Bool
}:
  Cells.Cell.keeps_some(
    ~Ledgers.Entry<Machine.Q(mach)>,
    ~Ledgers.Entry.is_eq(~Machine.Q(mach), ~Machine.same(mach)),
    Ledgers.State.get(~Machine.Q(mach), State.ledger(~mach, a), k),
    Ledgers.State.get(~Machine.Q(mach), State.ledger(~mach, b), k)
  )(
    Tries.Trie.keeps_get(
      ~Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>,
      ~Cells.Cell.keeps(
        ~Ledgers.Entry<Machine.Q(mach)>,
        ~Ledgers.Entry.is_eq(~Machine.Q(mach), ~Machine.same(mach))
      ),
      ~Cells.Cell.none_kept(
        ~Ledgers.Entry<Machine.Q(mach)>,
        ~Ledgers.Entry.is_eq(~Machine.Q(mach), ~Machine.same(mach))
      ),
      State.ledger(~mach, a),
      State.ledger(~mach, b),
      k
    )(g)
  )

# a request whose slot holds a cell changes nothing
def Ask.once.at(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  m: String,
  s: Node<Machine.Q(mach)>,
  e: Envelope,
  q: Machine.Q(mach),
  c: Maybe<&2, Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>>
) -> {
  Maybe.is_some(&2, Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>, c) == True{}: Bool
} -> {Node.ask.at(~mach, ~kern, m, s, e, q, c) == s: Node<Machine.Q(mach)>}:
  match c:
    case Some{x}:
      h => {==}
    case None{}:
      h => Empty.absurd(
        {Node.ask.at(~mach, ~kern, m, s, e, q, None{}) == s: Node<Machine.Q(mach)>},
        Shared.Bool.false_ne_true(h)
      )

# a read of a tree stays in a node that grew
def Get.grows(
  ~mach: Machine(),
  +a: Node<Machine.Q(mach)>,
  +b: Node<Machine.Q(mach)>,
  +h: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  v: List<&2, U32>,
  g: {Node.grows(~mach, a, b) == True{}: Bool}
) -> {
  Node.get(~mach, a, h, k) == Some{v}: Maybe<&2, List<&2, U32>>
} -> {Node.get(~mach, b, h, k) == Some{v}: Maybe<&2, List<&2, U32>>}:
  e => Equal.trans(
    Maybe<&2, List<&2, U32>>,
    Node.get(~mach, b, h, k),
    Trees.Tree.get.plain(~Node<Machine.Q(mach)>, ~Store.fetch(~mach), b, h, k),
    Some{v},
    Trees.Tree.get_plain(~Node<Machine.Q(mach)>, ~Store.fetch(~mach), b, h, k),
    Trees.Tree.get_grows(
      ~Node<Machine.Q(mach)>,
      ~Store.fetch(~mach),
      ~Node.grows(~mach),
      ~(
        x => y => hh => w => Ledgers.State.data_grows(
          ~Machine.Q(mach),
          ~Machine.same(mach),
          ~Machine.laws(mach),
          State.ledger(~mach, x),
          State.ledger(~mach, y),
          hh,
          w
        )
      ),
      a,
      b,
      h,
      k,
      v
    )(
      g
    )(
      Equal.trans(
        Maybe<&2, List<&2, U32>>,
        Trees.Tree.get.plain(~Node<Machine.Q(mach)>, ~Store.fetch(~mach), a, h, k),
        Node.get(~mach, a, h, k),
        Some{v},
        Equal.sym(
          Maybe<&2, List<&2, U32>>,
          Node.get(~mach, a, h, k),
          Trees.Tree.get.plain(~Node<Machine.Q(mach)>, ~Store.fetch(~mach), a, h, k),
          Trees.Tree.get_plain(~Node<Machine.Q(mach)>, ~Store.fetch(~mach), a, h, k)
        ),
        e
      )
    )
  )

# Set.kept once whether the node holds the new nodes is known (b)
def Set.kept.if(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  +h: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  +x: List<&2, U32>,
  +k2: List<&2, U32>,
  v: List<&2, U32>,
  +hh: Hashes.Hash,
  +ws: List<&2, List<&2, U32>>,
  b: Bool,
  eb: {
    Stores.Store.holds(
      ~Node<Machine.Q(mach)>,
      ~Store.fetch(~mach),
      State.keep(~mach, s, ws),
      ws
    )
      == b: Bool
  },
  hne: {Shared.List.is_eq(~U32, ~U32.is_eq, k, k2) == False{}: Bool},
  hget: {Node.get(~mach, s, h, k2) == Some{v}: Maybe<&2, List<&2, U32>>},
  em: {Node.set(~mach, s, h, k, x) == Some{Trees.Put{hh, ws}}: Maybe<&2, Trees.Put>}
) -> Work.Reads(
  ~mach,
  k2,
  v,
  Work.on(
    ~mach,
    Shared.Maybe.when(Node<Machine.Q(mach)>, b, u => Some{State.keep(~mach, s, ws)}),
    Some{hh}
  )
):
  match b:
    case False{}:
      Unit{}
    case True{}:
      +sk = State.keep(~mach, s, ws)
      Equal.trans(
        Maybe<&2, List<&2, U32>>,
        Node.get(~mach, sk, Some{hh}, k2),
        Node.get(~mach, sk, h, k2),
        Some{v},
        Equal.trans(
          Maybe<&2, List<&2, U32>>,
          Node.get(~mach, sk, Some{hh}, k2),
          Trees.Tree.get.plain(~Node<Machine.Q(mach)>, ~Store.fetch(~mach), sk, Some{hh}, k2),
          Node.get(~mach, sk, h, k2),
          Trees.Tree.get_plain(~Node<Machine.Q(mach)>, ~Store.fetch(~mach), sk, Some{hh}, k2),
          Equal.trans(
            Maybe<&2, List<&2, U32>>,
            Trees.Tree.get.plain(~Node<Machine.Q(mach)>, ~Store.fetch(~mach), sk, Some{hh}, k2),
            Trees.Tree.get.plain(~Node<Machine.Q(mach)>, ~Store.fetch(~mach), sk, h, k2),
            Node.get(~mach, sk, h, k2),
            Trees.Tree.get_other(
              ~Node<Machine.Q(mach)>,
              ~Store.fetch(~mach),
              ~Node.grows(~mach),
              ~(
                p => q => g => w => Ledgers.State.data_grows(
                  ~Machine.Q(mach),
                  ~Machine.same(mach),
                  ~Machine.laws(mach),
                  State.ledger(~mach, p),
                  State.ledger(~mach, q),
                  g,
                  w
                )
              ),
              s,
              sk,
              h,
              k,
              x,
              Trees.Put{hh, ws},
              k2
            )(
              Grows.keep(~mach, s, ws)
            )(
              hne
            )(
              Equal.trans(
                Maybe<&2, Trees.Put>,
                Trees.Tree.set.plain(~Node<Machine.Q(mach)>, ~Store.fetch(~mach), s, h, k, x),
                Node.set(~mach, s, h, k, x),
                Some{Trees.Put{hh, ws}},
                Equal.sym(
                  Maybe<&2, Trees.Put>,
                  Node.set(~mach, s, h, k, x),
                  Trees.Tree.set.plain(~Node<Machine.Q(mach)>, ~Store.fetch(~mach), s, h, k, x),
                  Trees.Tree.set_plain(~Node<Machine.Q(mach)>, ~Store.fetch(~mach), s, h, k, x)
                ),
                em
              )
            )(eb),
            Equal.sym(
              Maybe<&2, List<&2, U32>>,
              Node.get(~mach, sk, h, k2),
              Trees.Tree.get.plain(~Node<Machine.Q(mach)>, ~Store.fetch(~mach), sk, h, k2),
              Trees.Tree.get_plain(~Node<Machine.Q(mach)>, ~Store.fetch(~mach), sk, h, k2)
            )
          )
        ),
        Get.grows(~mach, s, sk, h, k2, v, Grows.keep(~mach, s, ws))(hget)
      )

# Set.kept once the new subtree m is known
def Set.kept.of(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  h: Maybe<&2, Hashes.Hash>,
  k: List<&2, U32>,
  x: List<&2, U32>,
  k2: List<&2, U32>,
  v: List<&2, U32>,
  m: Maybe<&2, Trees.Put>,
  em: {Node.set(~mach, s, h, k, x) == m: Maybe<&2, Trees.Put>},
  hne: {Shared.List.is_eq(~U32, ~U32.is_eq, k, k2) == False{}: Bool},
  hget: {Node.get(~mach, s, h, k2) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> Work.Reads(~mach, k2, v, Work.of(~mach, s, m)):
  match m:
    case None{}:
      Unit{}
    case Some{Trees.Put{hh, +ws}}:
      Set.kept.if(
        ~mach,
        s,
        h,
        k,
        x,
        k2,
        v,
        hh,
        ws,
        Stores.Store.holds(
          ~Node<Machine.Q(mach)>,
          ~Store.fetch(~mach),
          State.keep(~mach, s, ws),
          ws
        ),
        {==},
        hne,
        hget,
        em
      )

# a key set in a tree keeps the value of each other key
def Set.kept(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  +h: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  +x: List<&2, U32>,
  k2: List<&2, U32>,
  v: List<&2, U32>,
  hne: {Shared.List.is_eq(~U32, ~U32.is_eq, k, k2) == False{}: Bool},
  hget: {Node.get(~mach, s, h, k2) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> Work.Reads(~mach, k2, v, Work.set(~mach, Work{s, h}, k, x)):
  Set.kept.of(~mach, s, h, k, x, k2, v, Node.set(~mach, s, h, k, x), {==}, hne, hget)

# the run of a new log that keeps a key keeps it
def Run.logged.keeps(
  ~mach: Machine(),
  -k2: List<&2, U32>,
  -v: List<&2, U32>,
  t: Tip,
  m: Maybe<&2, Work<Machine.Q(mach)>>
) -> Work.Reads(~mach, k2, v, m) -> Run.Keeps(~mach, k2, v, Run.logged(~mach, t, m)):
  match t m:
    case x None{}:
      w => Unit{}
    case Tip{c, old, n, os} Some{Work{s2, l}}:
      w => w

# a key that a tree does not hold is not a key that it holds, once whether
# they are the same is known (b)
def Keys.differ.if(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  h: Maybe<&2, Hashes.Hash>,
  k: List<&2, U32>,
  k2: List<&2, U32>,
  v: List<&2, U32>,
  b: Bool,
  eb: {Shared.List.is_eq(~U32, ~U32.is_eq, k, k2) == b: Bool},
  e1: {Node.get(~mach, s, h, k) == None{}: Maybe<&2, List<&2, U32>>},
  e2: {Node.get(~mach, s, h, k2) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> {b == False{}: Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Empty.absurd(
        {True{} == False{}: Bool},
        Shared.Maybe.none_ne_some(
          List<&2, U32>,
          v,
          Equal.trans(
            Maybe<&2, List<&2, U32>>,
            None{},
            Node.get(~mach, s, h, k),
            Some{v},
            Equal.sym(Maybe<&2, List<&2, U32>>, Node.get(~mach, s, h, k), None{}, e1),
            (
              %Equal.sym(List<&2, U32>, k, k2, Shared.List.is_eq_sound(~U32, ~U32.is_eq, ~Shared.U32.laws(), k, k2)(eb)): {Node.get(~mach, s, h, _) == Some{v}: Maybe<&2, List<&2, U32>>}
              e2)
          )
        )
      )

# Add.kept when the log does not hold the new key
def Add.new.kept(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  +t: Tip,
  +k: List<&2, U32>,
  +x: List<&2, U32>,
  +k2: List<&2, U32>,
  +v: List<&2, U32>,
  em: {Node.get(~mach, s, Tip.log(t), k) == None{}: Maybe<&2, List<&2, U32>>},
  +hr: {Node.get(~mach, s, Tip.log(t), k2) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> Run.Keeps(~mach, k2, v, Run.logged(~mach, t, Work.set(~mach, Work{s, Tip.log(t)}, k, x))):
  Run.logged.keeps(
    ~mach,
    k2,
    v,
    t,
    Work.set(~mach, Work{s, Tip.log(t)}, k, x)
  )(
    Set.kept(
      ~mach,
      s,
      Tip.log(t),
      k,
      x,
      k2,
      v,
      Keys.differ.if(
        ~mach,
        s,
        Tip.log(t),
        k,
        k2,
        v,
        Shared.List.is_eq(~U32, ~U32.is_eq, k, k2),
        {==},
        em,
        hr
      ),
      hr
    )
  )

# Add.kept once the value m of the new key is known
def Add.at.kept(
  ~mach: Machine(),
  r: Run<Machine.Q(mach)>,
  k: List<&2, U32>,
  x: List<&2, U32>,
  k2: List<&2, U32>,
  v: List<&2, U32>,
  m: Maybe<&2, List<&2, U32>>
) -> {
  Node.get(~mach, Run.state(~mach, r), Tip.log(Run.tip(~mach, r)), k) == m: Maybe<&2, List<&2, U32>>
} -> Run.Keeps(~mach, k2, v, Some{r}) -> Run.Keeps(~mach, k2, v, Run.add.at(~mach, r, k, x, m)):
  match r m:
    case Run{s, t} None{}:
      em => hr => Add.new.kept(~mach, s, t, k, x, k2, v, em, hr)
    case y Some{old}:
      em => hr => Unit{}

# a new key in a run's log keeps the value of each key that the log holds
def Add.kept(
  ~mach: Machine(),
  +r: Run<Machine.Q(mach)>,
  +k: List<&2, U32>,
  x: List<&2, U32>,
  k2: List<&2, U32>,
  v: List<&2, U32>
) -> Run.Keeps(~mach, k2, v, Some{r}) -> Run.Keeps(~mach, k2, v, Run.add(~mach, r, k, x)):
  Add.at.kept(
    ~mach,
    r,
    k,
    x,
    k2,
    v,
    Node.get(~mach, Run.state(~mach, r), Tip.log(Run.tip(~mach, r)), k)
  )({==})

# a run, then a run from it that keeps a key, keeps it
def Keeps.bind(
  ~mach: Machine(),
  -k2: List<&2, U32>,
  -v: List<&2, U32>,
  m: Maybe<&2, Run<Machine.Q(mach)>>,
  -f: Run<Machine.Q(mach)> -> Maybe<&2, Run<Machine.Q(mach)>>
) -> Run.Keeps(
  ~mach,
  k2,
  v,
  m
) -> (
  @r: Run<Machine.Q(mach)> -> Run.Keeps(~mach, k2, v, Some{r}) -> Run.Keeps(~mach, k2, v, f(r))
) -> Run.Keeps(~mach, k2, v, Maybe.bind(&2, Run<Machine.Q(mach)>, Run<Machine.Q(mach)>, m, f)):
  match m:
    case None{}:
      hm => hf => Unit{}
    case Some{r}:
      hm => hf => hf(r)(hm)

# one of two runs, each of which keeps a key that the run r keeps
def Keeps.when(
  ~mach: Machine(),
  -k2: List<&2, U32>,
  -v: List<&2, U32>,
  -r: Run<Machine.Q(mach)>,
  b: Bool,
  -mx: Maybe<&2, Run<Machine.Q(mach)>>,
  -my: Maybe<&2, Run<Machine.Q(mach)>>,
  hx: Run.Keeps(~mach, k2, v, Some{r}) -> Run.Keeps(~mach, k2, v, mx),
  hy: Run.Keeps(~mach, k2, v, Some{r}) -> Run.Keeps(~mach, k2, v, my)
) -> Run.Keeps(
  ~mach,
  k2,
  v,
  Some{r}
) -> Run.Keeps(
  ~mach,
  k2,
  v,
  Shared.Bool.when(Maybe<&2, Run<Machine.Q(mach)>>, b, u => mx, u => my)
):
  match b:
    case True{}:
      hx
    case False{}:
      hy

# a run one version on keeps each key of its log
def Next.kept(
  ~mach: Machine(),
  r: Run<Machine.Q(mach)>,
  -own: Maybe<&2, List<&2, String>>,
  -k2: List<&2, U32>,
  -v: List<&2, U32>
) -> Run.Keeps(~mach, k2, v, Some{r}) -> Run.Keeps(~mach, k2, v, Some{Run.next(~mach, r, own)}):
  match r:
    case Run{s, Tip{c, l, n, os}}:
      hr => hr

# a taken request keeps each key of a run's log
def Taken.kept(
  ~mach: Machine(),
  +r: Run<Machine.Q(mach)>,
  +i: Ledgers.Id,
  own: Maybe<&2, List<&2, String>>,
  +k2: List<&2, U32>,
  +v: List<&2, U32>
) -> Run.Keeps(~mach, k2, v, Some{r}) -> Run.Keeps(~mach, k2, v, Step.taken(~mach, r, i, own)):
  +n = Tip.count(Run.tip(~mach, r))
  hr => Keeps.bind(
    ~mach,
    k2,
    v,
    Run.add(~mach, r, Log.out(i), Out.words(Out.Taken{n})),
    +r1 => Maybe.bind(
      &2,
      Run<Machine.Q(mach)>,
      Run<Machine.Q(mach)>,
      Run.add(
        ~mach,
        r1,
        Log.version(n),
        Version.words(Version{i, Tip.content(Run.tip(~mach, r1))})
      ),
      r2 => Some{Run.next(~mach, r2, own)}
    )
  )(
    Add.kept(~mach, r, Log.out(i), Out.words(Out.Taken{n}), k2, v)(hr)
  )(
    +r1 => h1 => Keeps.bind(
      ~mach,
      k2,
      v,
      Run.add(
        ~mach,
        r1,
        Log.version(n),
        Version.words(Version{i, Tip.content(Run.tip(~mach, r1))})
      ),
      r2 => Some{Run.next(~mach, r2, own)}
    )(
      Add.kept(
        ~mach,
        r1,
        Log.version(n),
        Version.words(Version{i, Tip.content(Run.tip(~mach, r1))}),
        k2,
        v
      )(h1)
    )(r2 => h2 => Next.kept(~mach, r2, own, k2, v)(h2))
  )

# a run over a node that grew keeps each key of its log
def Over.kept(
  ~mach: Machine(),
  r: Run<Machine.Q(mach)>,
  s2: Node<Machine.Q(mach)>,
  -h: Maybe<&2, Hashes.Hash>,
  k2: List<&2, U32>,
  v: List<&2, U32>,
  g: {Node.grows(~mach, Run.state(~mach, r), s2) == True{}: Bool}
) -> Run.Keeps(~mach, k2, v, Some{r}) -> Run.Keeps(~mach, k2, v, Some{Run.over(~mach, r, s2, h)}):
  match r:
    case Run{s, Tip{c, l, n, os}}:
      hr => Get.grows(~mach, s, s2, l, k2, v, g)(hr)

# a judged request keeps each key of a run's log, other than the owners and
# the count
def Judged.kept(
  ~mach: Machine(),
  +r: Run<Machine.Q(mach)>,
  i: Ledgers.Id,
  own: Maybe<&2, List<&2, String>>,
  m: Maybe<&2, Verdict<Machine.Q(mach)>>,
  +k2: List<&2, U32>,
  +v: List<&2, U32>
) -> {
  Verdict.after(~mach, Run.state(~mach, r), m) == True{}: Bool
} -> Run.Keeps(~mach, k2, v, Some{r}) -> Run.Keeps(~mach, k2, v, Step.judged(~mach, r, i, own, m)):
  match m:
    case None{}:
      g => hr => Unit{}
    case Some{Verdict.Stale{}}:
      g => hr => Add.kept(~mach, r, Log.out(i), Out.words(Out.Stale{}), k2, v)(hr)
    case Some{Verdict.Taken{Work{+s2, h}}}:
      g => hr => Taken.kept(
        ~mach,
        Run.over(~mach, r, s2, h),
        i,
        own,
        k2,
        v
      )(Over.kept(~mach, r, s2, h, k2, v, g)(hr))

# a mark on a version keeps each key of a run's log, other than the owners
# and the count
def Marked.kept(
  ~mach: Machine(),
  +r: Run<Machine.Q(mach)>,
  i: Ledgers.Id,
  +m: String,
  x: Maybe<&2, Version>,
  +k2: List<&2, U32>,
  +v: List<&2, U32>
) -> Run.Keeps(~mach, k2, v, Some{r}) -> Run.Keeps(~mach, k2, v, Step.marked(~mach, r, i, m, x)):
  match x:
    case None{}:
      hr => Unit{}
    case Some{+y}:
      hr => Keeps.bind(
        ~mach,
        k2,
        v,
        Run.add(~mach, r, Log.mark(m), Ledgers.Id.code(Version.id(y), [])),
        r2 => Step.taken(~mach, r2, i, None{})
      )(
        Add.kept(~mach, r, Log.mark(m), Ledgers.Id.code(Version.id(y), []), k2, v)(hr)
      )(r2 => h2 => Taken.kept(~mach, r2, i, None{}, k2, v)(h2))

# a request for a mark keeps each key of a run's log, other than the owners
# and the count
def Mark.kept(
  ~mach: Machine(),
  +r: Run<Machine.Q(mach)>,
  +i: Ledgers.Id,
  +m: String,
  +k2: List<&2, U32>,
  +v: List<&2, U32>
) -> Run.Keeps(~mach, k2, v, Some{r}) -> Run.Keeps(~mach, k2, v, Step.mark(~mach, r, i, m)):
  +s = Run.state(~mach, r)
  +t = Run.tip(~mach, r)
  +n = Tip.count(t)
  Keeps.when(
    ~mach,
    k2,
    v,
    r,
    List.all.if(
      u => Maybe.is_none(&2, Ledgers.Id, Line.mark(~mach, s, t, m)),
      Bool.not(U32.is_eq(n, 0))
    ),
    Step.marked(~mach, r, i, m, Line.version(~mach, s, t, U32.sub(n, 1))),
    Step.stale(~mach, r, i),
    Marked.kept(~mach, r, i, m, Line.version(~mach, s, t, U32.sub(n, 1)), k2, v),
    Add.kept(~mach, r, Log.out(i), Out.words(Out.Stale{}), k2, v)
  )

# the first tip of a new branch keeps each key of a run's log, other than the
# owners and the count
def Branch.made.kept(
  ~mach: Machine(),
  +r: Run<Machine.Q(mach)>,
  i: Ledgers.Id,
  +b: String,
  m: Maybe<&2, Made<Machine.Q(mach)>>,
  +k2: List<&2, U32>,
  +v: List<&2, U32>
) -> {
  Made.after(~mach, Run.state(~mach, r), m) == True{}: Bool
} -> Run.Keeps(~mach, k2, v, Some{r}) -> Run.Keeps(~mach, k2, v, Branch.made(~mach, r, i, b, m)):
  match m:
    case None{}:
      g => hr => Unit{}
    case Some{Made{+t, +s2}}:
      g => hr =>
        +r1 = {Run.over(~mach, r, s2, Tip.content(Run.tip(~mach, r))): Run<Machine.Q(mach)>}
        Keeps.bind(
          ~mach,
          k2,
          v,
          Run.add(~mach, r1, Log.start(b), Hashes.Hash.code(Tip.hash(t), [])),
          r2 => Step.taken(~mach, r2, i, None{})
        )(
          Add.kept(
            ~mach,
            r1,
            Log.start(b),
            Hashes.Hash.code(Tip.hash(t), []),
            k2,
            v
          )(Over.kept(~mach, r, s2, Tip.content(Run.tip(~mach, r)), k2, v, g)(hr))
        )(r2 => h2 => Taken.kept(~mach, r2, i, None{}, k2, v)(h2))

# a tip that a node holds, a node that grew from it holds
def Tip.at.grows(
  ~mach: Machine(),
  +a: Node<Machine.Q(mach)>,
  b: Node<Machine.Q(mach)>,
  +x: Hashes.Hash,
  -t: Tip,
  g: {Node.grows(~mach, a, b) == True{}: Bool}
) -> {
  Tip.at(~mach, a, x) == Some{t}: Maybe<&2, Tip>
} -> {Tip.at(~mach, b, x) == Some{t}: Maybe<&2, Tip>}:
  Shared.Maybe.bind_kept(
    List<&2, U32>,
    Tip,
    Store.fetch(~mach, a, x),
    Store.fetch(~mach, b, x),
    ws => Tip.read(ws),
    ws => Tip.read(ws),
    t,
    w => Ledgers.State.data_grows(
      ~Machine.Q(mach),
      ~Machine.same(mach),
      ~Machine.laws(mach),
      State.ledger(~mach, a),
      State.ledger(~mach, b),
      x,
      w
    )(g),
    w => e => e
  )

# the tip of a head, in a node that grew
def Head.tip.grows(
  ~mach: Machine(),
  a: Node<Machine.Q(mach)>,
  b: Node<Machine.Q(mach)>,
  h: Head,
  -t: Tip,
  g: {Node.grows(~mach, a, b) == True{}: Bool}
) -> {
  Head.tip(~mach, a, h) == Some{t}: Maybe<&2, Tip>
} -> {Head.tip(~mach, b, h) == Some{t}: Maybe<&2, Tip>}:
  match h:
    case Head{r, br, n, th}:
      Shared.Maybe.bind_kept(
        Hashes.Hash,
        Tip,
        th,
        th,
        x => Tip.at(~mach, a, x),
        x => Tip.at(~mach, b, x),
        t,
        x => e => e,
        +x => Tip.at.grows(~mach, a, b, x, t, g)
      )

# what the log of a head holds, in a node that grew
def Head.get.grows(
  ~mach: Machine(),
  +a: Node<Machine.Q(mach)>,
  +b: Node<Machine.Q(mach)>,
  +h: Head,
  k: List<&2, U32>,
  v: List<&2, U32>,
  +g: {Node.grows(~mach, a, b) == True{}: Bool}
) -> {
  Head.get(~mach, a, h, k) == Some{v}: Maybe<&2, List<&2, U32>>
} -> {Head.get(~mach, b, h, k) == Some{v}: Maybe<&2, List<&2, U32>>}:
  Shared.Maybe.bind_kept(
    Tip,
    List<&2, U32>,
    Head.tip(~mach, a, h),
    Head.tip(~mach, b, h),
    t => Node.get(~mach, a, Tip.log(t), k),
    t => Node.get(~mach, b, Tip.log(t), k),
    v,
    t => Head.tip.grows(~mach, a, b, h, t, g),
    t => Get.grows(~mach, a, b, Tip.log(t), k, v, g)
  )

# a line whose head is the same in a node that grew holds what it held
def Line.same(
  ~mach: Machine(),
  +a: Node<Machine.Q(mach)>,
  b: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  k: List<&2, U32>,
  v: List<&2, U32>,
  g: {Node.grows(~mach, a, b) == True{}: Bool},
  eh: {Node.head_of(~mach, a, c) == Node.head_of(~mach, b, c): Maybe<&2, Head>}
) -> {
  Line.get(~mach, a, c, k) == Some{v}: Maybe<&2, List<&2, U32>>
} -> {Line.get(~mach, b, c, k) == Some{v}: Maybe<&2, List<&2, U32>>}:
  Shared.Maybe.bind_kept(
    Head,
    List<&2, U32>,
    Node.head_of(~mach, a, c),
    Node.head_of(~mach, b, c),
    h => Head.get(~mach, a, h, k),
    h => Head.get(~mach, b, h, k),
    v,
    h => e => Equal.trans(
      Maybe<&2, Head>,
      Node.head_of(~mach, b, c),
      Node.head_of(~mach, a, c),
      Some{h},
      Equal.sym(Maybe<&2, Head>, Node.head_of(~mach, a, c), Node.head_of(~mach, b, c), eh),
      e
    ),
    +h => Head.get.grows(~mach, a, b, h, k, v, g)
  )

# a node keeps its own logs
def Kept.refl(~mach: Machine(), -s: Node<Machine.Q(mach)>) -> Node.Keeps(~mach, s, s):
  c => k => v => e => e

# keeping composes
def Kept.trans(
  ~mach: Machine(),
  -a: Node<Machine.Q(mach)>,
  -b: Node<Machine.Q(mach)>,
  -d: Node<Machine.Q(mach)>,
  h1: Node.Keeps(~mach, a, b),
  h2: Node.Keeps(~mach, b, d)
) -> Node.Keeps(~mach, a, d):
  +c => +k => +v => e => h2(c)(k)(v)(h1(c)(k)(v)(e))

# one of two nodes, each of which keeps the logs of s
def Kept.when(
  ~mach: Machine(),
  b: Bool,
  -s: Node<Machine.Q(mach)>,
  -x: Node<Machine.Q(mach)>,
  -y: Node<Machine.Q(mach)>,
  hx: Node.Keeps(~mach, s, x),
  hy: Node.Keeps(~mach, s, y)
) -> Node.Keeps(~mach, s, Shared.Bool.when(Node<Machine.Q(mach)>, b, u => x, u => y)):
  match b:
    case True{}:
      hx
    case False{}:
      hy

# a node that grew, with the same heads, keeps the logs
def Kept.same(
  ~mach: Machine(),
  a: Node<Machine.Q(mach)>,
  b: Node<Machine.Q(mach)>,
  g: {Node.grows(~mach, a, b) == True{}: Bool},
  eh: {State.heads(~mach, a) == State.heads(~mach, b): Tries.Trie<Head>}
) -> Node.Keeps(~mach, a, b):
  +c => k => v => Line.same(
    ~mach,
    a,
    b,
    c,
    k,
    v,
    g,
    Equal.cong(
      Tries.Trie<Head>,
      Maybe<&2, Head>,
      hs => Tries.Trie.get(Head, hs, Ledgers.Chain.key(c)),
      State.heads(~mach, a),
      State.heads(~mach, b),
      eh
    )
  )

# a new ledger keeps the heads
def Heads.led(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  l: Ledgers.State(Machine.Q(mach))
) -> {State.heads(~mach, s) == State.heads(~mach, State.led(~mach, s, l)): Tries.Trie<Head>}:
  match s:
    case Node{old, hs, ws, ks}:
      {==}

# new waiting requests keep the heads
def Heads.wait(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  qs: List<&2, Ledgers.Id>
) -> {State.heads(~mach, s) == State.heads(~mach, Wait.set(~mach, s, c, qs)): Tries.Trie<Head>}:
  match s:
    case Node{l, hs, ws, ks}:
      {==}

# the head of a line, after the head of the line c is set
def Head.of_set(
  ~mach: Machine(),
  b0: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  hd: Head,
  c2: Ledgers.Chain
) -> {
  Node.head_of(
    ~mach,
    State.head(~mach, b0, c, hd),
    c2
  )
    == Bool.pick(
      Maybe<&2, Head>,
      Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
      Some{hd},
      Node.head_of(~mach, b0, c2)
    ): Maybe<&2, Head>
}:
  match b0:
    case Node{l, hs, ws, ks}:
      Tries.Trie.get_set(Head, hs, Ledgers.Chain.key(c), hd, Ledgers.Chain.key(c2))

# a pick, once what it picks by is known
def Pick.of(
  -A: Data,
  b: Bool,
  -p: Bool,
  -x: A,
  -y: A,
  eb: {p == b: Bool}
) -> {Bool.pick(A, p, x, y) == Bool.pick(A, b, x, y): A}:
  %eb: {Bool.pick(A, p, x, y) == Bool.pick(A, _, x, y): A}
  {==}

# what a line holds, once its head m is known
def Line.get.of(
  ~mach: Machine(),
  -a: Node<Machine.Q(mach)>,
  -c: Ledgers.Chain,
  -k: List<&2, U32>,
  -v: List<&2, U32>,
  -m: Maybe<&2, Head>,
  em: {Node.head_of(~mach, a, c) == m: Maybe<&2, Head>}
) -> {
  Line.get(~mach, a, c, k) == Some{v}: Maybe<&2, List<&2, U32>>
} -> {
  Maybe.bind(
    &2,
    Head,
    List<&2, U32>,
    m,
    h => Head.get(~mach, a, h, k)
  )
    == Some{v}: Maybe<&2, List<&2, U32>>
}:
  e =>
    %em: {
      Maybe.bind(
        &2,
        Head,
        List<&2, U32>,
        _,
        h => Head.get(~mach, a, h, k)
      )
        == Some{v}: Maybe<&2, List<&2, U32>>
    }
    e

# Head.put.kept once whether c2 is the line c is known (bs)
def Head.put.kept.if(
  ~mach: Machine(),
  +a: Node<Machine.Q(mach)>,
  +b0: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  +hd: Head,
  +c2: Ledgers.Chain,
  k: List<&2, U32>,
  v: List<&2, U32>,
  bs: Bool,
  +ebs: {Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)) == bs: Bool},
  g: {Node.grows(~mach, a, b0) == True{}: Bool},
  eh: {State.heads(~mach, a) == State.heads(~mach, b0): Tries.Trie<Head>},
  cov: {
    Line.get(~mach, a, c, k) == Some{v}: Maybe<&2, List<&2, U32>>
  } -> {Head.get(~mach, State.head(~mach, b0, c, hd), hd, k) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> {
  Line.get(~mach, a, c2, k) == Some{v}: Maybe<&2, List<&2, U32>>
} -> {Line.get(~mach, State.head(~mach, b0, c, hd), c2, k) == Some{v}: Maybe<&2, List<&2, U32>>}:
  match bs:
    case True{}:
      e =>
        %Equal.sym(
          Maybe<&2, Head>,
          Node.head_of(~mach, State.head(~mach, b0, c, hd), c2),
          Some{hd},
          Equal.trans(
            Maybe<&2, Head>,
            Node.head_of(~mach, State.head(~mach, b0, c, hd), c2),
            Bool.pick(
              Maybe<&2, Head>,
              Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
              Some{hd},
              Node.head_of(~mach, b0, c2)
            ),
            Some{hd},
            Head.of_set(~mach, b0, c, hd, c2),
            Pick.of(
              Maybe<&2, Head>,
              True{},
              Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
              Some{hd},
              Node.head_of(~mach, b0, c2),
              ebs
            )
          )
        ): {
          Maybe.bind(
            &2,
            Head,
            List<&2, U32>,
            _,
            h => Head.get(~mach, State.head(~mach, b0, c, hd), h, k)
          )
            == Some{v}: Maybe<&2, List<&2, U32>>
        }
        cov(
          Equal.trans(
            Maybe<&2, List<&2, U32>>,
            Line.get(~mach, a, c, k),
            Line.get(~mach, a, c2, k),
            Some{v},
            Equal.cong(
              List<&2, Bool>,
              Maybe<&2, List<&2, U32>>,
              kk => Maybe.bind(
                &2,
                Head,
                List<&2, U32>,
                Tries.Trie.get(Head, State.heads(~mach, a), kk),
                h => Head.get(~mach, a, h, k)
              ),
              Ledgers.Chain.key(c),
              Ledgers.Chain.key(c2),
              Equal.sym(
                List<&2, Bool>,
                Ledgers.Chain.key(c2),
                Ledgers.Chain.key(c),
                Shared.List.is_eq_sound(
                  ~Bool,
                  ~Shared.Bool.is_eq,
                  ~Shared.Bool.laws(),
                  Ledgers.Chain.key(c2),
                  Ledgers.Chain.key(c)
                )(ebs)
              )
            ),
            e
          )
        )
    case False{}:
      Line.same(
        ~mach,
        a,
        State.head(~mach, b0, c, hd),
        c2,
        k,
        v,
        Grows.to(~mach, a, b0, State.head(~mach, b0, c, hd), Led.head(~mach, b0, c, hd), g),
        Equal.trans(
          Maybe<&2, Head>,
          Node.head_of(~mach, a, c2),
          Node.head_of(~mach, b0, c2),
          Node.head_of(~mach, State.head(~mach, b0, c, hd), c2),
          Equal.cong(
            Tries.Trie<Head>,
            Maybe<&2, Head>,
            hs => Tries.Trie.get(Head, hs, Ledgers.Chain.key(c2)),
            State.heads(~mach, a),
            State.heads(~mach, b0),
            eh
          ),
          Equal.sym(
            Maybe<&2, Head>,
            Node.head_of(~mach, State.head(~mach, b0, c, hd), c2),
            Node.head_of(~mach, b0, c2),
            Equal.trans(
              Maybe<&2, Head>,
              Node.head_of(~mach, State.head(~mach, b0, c, hd), c2),
              Bool.pick(
                Maybe<&2, Head>,
                Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
                Some{hd},
                Node.head_of(~mach, b0, c2)
              ),
              Node.head_of(~mach, b0, c2),
              Head.of_set(~mach, b0, c, hd, c2),
              Pick.of(
                Maybe<&2, Head>,
                False{},
                Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
                Some{hd},
                Node.head_of(~mach, b0, c2),
                ebs
              )
            )
          )
        )
      )

# a node b0 with a new head hd of the line c keeps the logs of a, when b0 grew
# from a with the same heads, and hd holds what the line c holds in a
def Head.put.kept(
  ~mach: Machine(),
  a: Node<Machine.Q(mach)>,
  b0: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  hd: Head,
  g: {Node.grows(~mach, a, b0) == True{}: Bool},
  eh: {State.heads(~mach, a) == State.heads(~mach, b0): Tries.Trie<Head>},
  cover: @k: List<
    &2,
    U32> -> @v: List<
    &2,
    U32> -> {
    Line.get(~mach, a, c, k) == Some{v}: Maybe<&2, List<&2, U32>>
  } -> {Head.get(~mach, State.head(~mach, b0, c, hd), hd, k) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> Node.Keeps(~mach, a, State.head(~mach, b0, c, hd)):
  +c2 => +k => +v => Head.put.kept.if(
    ~mach,
    a,
    b0,
    c,
    hd,
    c2,
    k,
    v,
    Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
    {==},
    g,
    eh,
    cover(k)(v)
  )

# one of two nodes, each with the heads of s
def Heads.when(
  ~mach: Machine(),
  b: Bool,
  -s: Node<Machine.Q(mach)>,
  -x: Node<Machine.Q(mach)>,
  -y: Node<Machine.Q(mach)>,
  hx: {State.heads(~mach, s) == State.heads(~mach, x): Tries.Trie<Head>},
  hy: {State.heads(~mach, s) == State.heads(~mach, y): Tries.Trie<Head>}
) -> {
  State.heads(
    ~mach,
    s
  )
    == State.heads(
      ~mach,
      Shared.Bool.when(Node<Machine.Q(mach)>, b, u => x, u => y)
    ): Tries.Trie<Head>
}:
  match b:
    case True{}:
      hx
    case False{}:
      hy

# new keys keep the heads
def Heads.keyed(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  ks: Keys
) -> {State.heads(~mach, s) == State.heads(~mach, State.keyed(~mach, s, ks)): Tries.Trie<Head>}:
  match s:
    case Node{l, hs, ws, old}:
      {==}

# the heads of the node m, if any, else of s
def Heads.of(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  m: Maybe<&2, Node<Machine.Q(mach)>>
) -> Tries.Trie<Head>:
  match m:
    case None{}:
      State.heads(~mach, s)
    case Some{s2}:
      State.heads(~mach, s2)

# a node that is kept when b holds has the heads of s, when it has
def Heads.some.if(
  ~mach: Machine(),
  b: Bool,
  -s: Node<Machine.Q(mach)>,
  -x: Node<Machine.Q(mach)>,
  hx: {State.heads(~mach, s) == State.heads(~mach, x): Tries.Trie<Head>}
) -> {
  State.heads(
    ~mach,
    s
  )
    == Heads.of(
      ~mach,
      s,
      Shared.Maybe.when(Node<Machine.Q(mach)>, b, u => Some{x})
    ): Tries.Trie<Head>
}:
  match b:
    case True{}:
      hx
    case False{}:
      {==}

# a ballot that a node accepts keeps the heads
def Accept.at.heads(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  +b: Ledgers.Ballot,
  m: Maybe<&2, Keychain>
) -> {
  State.heads(~mach, s) == Heads.of(~mach, s, Seal.accept.at(~mach, s, b, m)): Tries.Trie<Head>
}:
  match m:
    case None{}:
      {==}
    case Some{+c}:
      Heads.some.if(
        ~mach,
        Seal.fits(c, b),
        s,
        State.keyed(
          ~mach,
          State.led(
            ~mach,
            s,
            Ledgers.State.keep(~Machine.Q(mach), ~Machine.same(mach), State.ledger(~mach, s), b)
          ),
          Keys.saw(
            Keys.set(
              State.keys(~mach, s),
              Seal.slot(Ballot.store(b), Ballot.node(b)),
              Keychain.next(c, b)
            ),
            Ballot.at(b)
          )
        ),
        Equal.trans(
          Tries.Trie<Head>,
          State.heads(~mach, s),
          State.heads(
            ~mach,
            State.led(
              ~mach,
              s,
              Ledgers.State.keep(~Machine.Q(mach), ~Machine.same(mach), State.ledger(~mach, s), b)
            )
          ),
          State.heads(
            ~mach,
            State.keyed(
              ~mach,
              State.led(
                ~mach,
                s,
                Ledgers.State.keep(~Machine.Q(mach), ~Machine.same(mach), State.ledger(~mach, s), b)
              ),
              Keys.saw(
                Keys.set(
                  State.keys(~mach, s),
                  Seal.slot(Ballot.store(b), Ballot.node(b)),
                  Keychain.next(c, b)
                ),
                Ballot.at(b)
              )
            )
          ),
          Heads.led(
            ~mach,
            s,
            Ledgers.State.keep(~Machine.Q(mach), ~Machine.same(mach), State.ledger(~mach, s), b)
          ),
          Heads.keyed(
            ~mach,
            State.led(
              ~mach,
              s,
              Ledgers.State.keep(~Machine.Q(mach), ~Machine.same(mach), State.ledger(~mach, s), b)
            ),
            Keys.saw(
              Keys.set(
                State.keys(~mach, s),
                Seal.slot(Ballot.store(b), Ballot.node(b)),
                Keychain.next(c, b)
              ),
              Ballot.at(b)
            )
          )
        )
      )

# the node m, if any, else s, has the heads of s when m has
def Default.heads(
  ~mach: Machine(),
  -s: Node<Machine.Q(mach)>,
  m: Maybe<&2, Node<Machine.Q(mach)>>
) -> {
  State.heads(~mach, s) == Heads.of(~mach, s, m): Tries.Trie<Head>
} -> {
  State.heads(
    ~mach,
    s
  )
    == State.heads(~mach, Maybe.default(&2, Node<Machine.Q(mach)>, m, s)): Tries.Trie<Head>
}:
  match m:
    case None{}:
      e => {==}
    case Some{s2}:
      e => e

# a sealed ballot keeps the heads
def Cast.seal.heads(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +s: Node<Machine.Q(mach)>,
  +w: Ledgers.Where,
  n: String,
  a0: Ledgers.Act,
  m: Maybe<&2, Keychain>
) -> {
  State.heads(
    ~mach,
    s
  )
    == State.heads(~mach, Cast.seal(~mach, ~kern, s, w, n, a0, m)): Tries.Trie<Head>
}:
  match m:
    case None{}:
      {==}
    case Some{Keychain{+j, last, key, f}}:
      +b = Ledgers.Ballot.make(
        Seal.secret(Keys.seed(State.keys(~mach, s)), Where.store(w), j),
        Ledgers.Signed{w, n, a0},
        last,
        Seals.Seal.public(Seal.secret(Keys.seed(State.keys(~mach, s)), Where.store(w), U32.inc(j)))
      )
      Default.heads(
        ~mach,
        s,
        Seal.accept(~mach, ~kern, s, b)
      )(Accept.at.heads(~mach, s, b, Seal.chain(~mach, ~kern, s, Ballot.store(b), Ballot.node(b))))

# a ballot keeps the heads
def Cast.vote.heads(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +s: Node<Machine.Q(mach)>,
  m: Maybe<&2, Node<Machine.Q(mach)>>,
  +w: Ledgers.Where,
  +n: String,
  a0: Ledgers.Act
) -> {
  State.heads(
    ~mach,
    s
  )
    == State.heads(~mach, Cast.vote(~mach, ~kern, s, m, w, n, a0)): Tries.Trie<Head>
}:
  match m:
    case None{}:
      {==}
    case Some{+s3}:
      +s4 = State.led(~mach, s, State.ledger(~mach, s3))
      Equal.trans(
        Tries.Trie<Head>,
        State.heads(~mach, s),
        State.heads(~mach, s4),
        State.heads(
          ~mach,
          Cast.seal(~mach, ~kern, s4, w, n, a0, Seal.chain(~mach, ~kern, s4, Where.store(w), n))
        ),
        Heads.led(~mach, s, State.ledger(~mach, s3)),
        Cast.seal.heads(~mach, ~kern, s4, w, n, a0, Seal.chain(~mach, ~kern, s4, Where.store(w), n))
      )

# the ballots that a chain leads to keep the heads, when each one more does
def Follow.step.heads(
  ~mach: Machine(),
  -s: Node<Machine.Q(mach)>,
  m: Maybe<&2, Node<Machine.Q(mach)>>,
  -k: Node<Machine.Q(mach)> -> Node<Machine.Q(mach)>,
  ih: @s2: Node<
    Machine.Q(mach)> -> {State.heads(~mach, s2) == State.heads(~mach, k(s2)): Tries.Trie<Head>}
) -> {
  State.heads(~mach, s) == Heads.of(~mach, s, m): Tries.Trie<Head>
} -> {
  State.heads(
    ~mach,
    s
  )
    == State.heads(
      ~mach,
      Maybe.default(
        &2,
        Node<Machine.Q(mach)>,
        Maybe.bind(&2, Node<Machine.Q(mach)>, Node<Machine.Q(mach)>, m, s2 => Some{k(s2)}),
        s
      )
    ): Tries.Trie<Head>
}:
  match m:
    case None{}:
      e => {==}
    case Some{s2}:
      e => Equal.trans(
        Tries.Trie<Head>,
        State.heads(~mach, s),
        State.heads(~mach, s2),
        State.heads(~mach, k(s2)),
        e,
        ih(s2)
      )

# the ballots that a chain leads to keep the heads
def Follow.heads(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  f: Nat,
  +s: Node<Machine.Q(mach)>,
  +p: Tries.Trie<Ledgers.Ballot>,
  +r: Ledgers.Id,
  +n: String,
  mb: Maybe<&2, Ledgers.Ballot>
) -> {
  State.heads(
    ~mach,
    s
  )
    == State.heads(~mach, Sealed.follow(~mach, ~kern, f, s, p, r, n, mb)): Tries.Trie<Head>
}:
  match f mb:
    case 0n x:
      {==}
    case 1n+g None{}:
      {==}
    case 1n+(+g) Some{+b}:
      Follow.step.heads(
        ~mach,
        s,
        Seal.accept(~mach, ~kern, s, b),
        +s2 => Sealed.follow(~mach, ~kern, g, s2, p, r, n, Pending.next(~mach, ~kern, s2, p, r, n)),
        +s2 => Follow.heads(~mach, ~kern, g, s2, p, r, n, Pending.next(~mach, ~kern, s2, p, r, n))
      )(Accept.at.heads(~mach, s, b, Seal.chain(~mach, ~kern, s, Ballot.store(b), Ballot.node(b))))

# the ballots that the chains of some ballots lead to keep the heads
def Each.heads(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +f: Nat,
  bs: List<&2, Ledgers.Ballot>,
  +p: Tries.Trie<Ledgers.Ballot>,
  +s: Node<Machine.Q(mach)>
) -> {
  State.heads(
    ~mach,
    s
  )
    == State.heads(~mach, Sealed.each(~mach, ~kern, f, bs, p, s)): Tries.Trie<Head>
}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, rest}:
      s1 = Sealed.follow(
        ~mach,
        ~kern,
        f,
        s,
        p,
        Ballot.store(b),
        Ballot.node(b),
        Pending.next(~mach, ~kern, s, p, Ballot.store(b), Ballot.node(b))
      )
      Equal.trans(
        Tries.Trie<Head>,
        State.heads(~mach, s),
        State.heads(~mach, s1),
        State.heads(~mach, Sealed.each(~mach, ~kern, f, rest, p, s1)),
        Follow.heads(
          ~mach,
          ~kern,
          f,
          s,
          p,
          Ballot.store(b),
          Ballot.node(b),
          Pending.next(~mach, ~kern, s, p, Ballot.store(b), Ballot.node(b))
        ),
        Each.heads(~mach, ~kern, f, rest, p, s1)
      )

# a vote keeps the heads
def Cast.put.heads(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  n: String,
  w: Ledgers.Where,
  th: Maybe<&2, Hashes.Hash>,
  qs: List<&2, Ledgers.Id>,
  from: List<&2, String>,
  m: Maybe<&2, Run<Machine.Q(mach)>>,
  s: Node<Machine.Q(mach)>
) -> {
  State.heads(
    ~mach,
    s
  )
    == State.heads(~mach, Cast.put(~mach, ~kern, n, w, th, qs, from, m, s)): Tries.Trie<Head>
}:
  match m:
    case None{}:
      {==}
    case Some{Run{s2, +t2}}:
      Cast.vote.heads(
        ~mach,
        ~kern,
        s,
        State.put(~mach, s2, [Tip.words(t2)]),
        w,
        n,
        Ledgers.Act.Vote{Ledgers.Vote{th, qs, Some{Tip.hash(t2)}}, from}
      )

# a pass keeps the heads
def Pass.to.heads(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +n: String,
  +s: Node<Machine.Q(mach)>,
  w: Ledgers.Where,
  os: List<&2, String>
) -> {
  State.heads(~mach, s) == State.heads(~mach, Pass.to(~mach, ~kern, n, s, w, os)): Tries.Trie<Head>
}:
  match w:
    case Ledgers.Where{+c, +h, +r}:
      Heads.when(
        ~mach,
        List.all.if(
          u => Maybe.is_none(
            &2,
            Maybe<&2, Ledgers.Last>,
            Ledgers.State.passed(
              ~Machine.Q(mach),
              State.ledger(~mach, s),
              Ledgers.Where{c, h, r},
              n
            )
          ),
          List.contains(~String, ~String.eq, os, n)
        ),
        s,
        Cast.seal(
          ~mach,
          ~kern,
          s,
          Ledgers.Where{c, h, r},
          n,
          Ledgers.Act.Pass{Last.below(~mach, n, s, c, h, r)},
          Seal.chain(~mach, ~kern, s, Where.store(Ledgers.Where{c, h, r}), n)
        ),
        s,
        Cast.seal.heads(
          ~mach,
          ~kern,
          s,
          Ledgers.Where{c, h, r},
          n,
          Ledgers.Act.Pass{Last.below(~mach, n, s, c, h, r)},
          Seal.chain(~mach, ~kern, s, Where.store(Ledgers.Where{c, h, r}), n)
        ),
        {==}
      )

# a node that joins a round keeps the heads
def Round.join.heads(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +n: String,
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  +h: U32,
  os: List<&2, String>
) -> {
  State.heads(
    ~mach,
    s
  )
    == State.heads(~mach, Round.join(~mach, ~kern, n, s, c, h, os)): Tries.Trie<Head>
}:
  +top = Round.seen(~mach, s, c, h)
  k = top
  Heads.when(
    ~mach,
    Nat.is_lt(Round.mine(~mach, n, s, c, h, k), top),
    s,
    Pass.to(~mach, ~kern, n, s, Ledgers.Where{c, h, top}, os),
    s,
    Pass.to.heads(~mach, ~kern, n, s, Ledgers.Where{c, h, top}, os),
    {==}
  )

# a ballot in the node's round keeps the heads
def Cast.round.heads(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +n: String,
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  +next: U32,
  +th: Maybe<&2, Hashes.Hash>,
  +t: Tip
) -> {
  State.heads(
    ~mach,
    s
  )
    == State.heads(~mach, Cast.round(~mach, ~kern, n, s, c, next, th, t)): Tries.Trie<Head>
}:
  +os = Tip.owners(t)
  +r = Round.mine(~mach, n, s, c, next, Round.seen(~mach, s, c, next))
  +w = {Ledgers.Where{c, next, r}: Ledgers.Where}
  +p = Plan.of(~mach, ~kern, n, s, c, w, t, th, os, Owners.turn(os, U32.add(next, U32.from_nat(r))))
  Heads.when(
    ~mach,
    Cast.free(~mach, n, s, w, t),
    s,
    Cast.plan(~mach, ~kern, n, w, th, p, s),
    s,
    Heads.when(
      ~mach,
      Bool.not(List.is_empty(&2, Ledgers.Id, Plan.asks(~mach, p))),
      s,
      Cast.put(
        ~mach,
        ~kern,
        n,
        w,
        th,
        Plan.asks(~mach, p),
        Plan.from(~mach, p),
        Plan.run(~mach, p),
        s
      ),
      s,
      Cast.put.heads(
        ~mach,
        ~kern,
        n,
        w,
        th,
        Plan.asks(~mach, p),
        Plan.from(~mach, p),
        Plan.run(~mach, p),
        s
      ),
      {==}
    ),
    {==}
  )

# Node.cast keeps the heads, at the head h whose tip is m
def Cast.at.heads(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +n: String,
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  h: Head,
  m: Maybe<&2, Tip>
) -> {
  State.heads(
    ~mach,
    s
  )
    == State.heads(~mach, Cast.at(~mach, ~kern, n, s, c, h, m)): Tries.Trie<Head>
}:
  match h m:
    case Head{r, b, +next, th} Some{+t}:
      s1 = Round.join(~mach, ~kern, n, s, c, next, Tip.owners(t))
      Equal.trans(
        Tries.Trie<Head>,
        State.heads(~mach, s),
        State.heads(~mach, s1),
        State.heads(~mach, Cast.round(~mach, ~kern, n, s1, c, next, th, t)),
        Round.join.heads(~mach, ~kern, n, s, c, next, Tip.owners(t)),
        Cast.round.heads(~mach, ~kern, n, s1, c, next, th, t)
      )
    case Head{r, b, next, th} None{}:
      {==}

# Node.pass keeps the heads, at the head h whose tip is m
def Pass.at.heads(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +n: String,
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  h: Head,
  m: Maybe<&2, Tip>
) -> {
  State.heads(
    ~mach,
    s
  )
    == State.heads(~mach, Pass.at(~mach, ~kern, n, s, c, h, m)): Tries.Trie<Head>
}:
  match h m:
    case Head{r, b, +next, th} Some{t}:
      Pass.to.heads(
        ~mach,
        ~kern,
        n,
        s,
        Ledgers.Where{c, next, 1n+Round.mine(~mach, n, s, c, next, Round.seen(~mach, s, c, next))},
        Tip.owners(t)
      )
    case Head{r, b, next, th} None{}:
      {==}

# Node.pass keeps the heads, once the head m is known
def Pass.head.heads(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  n: String,
  +s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  m: Maybe<&2, Head>
) -> {
  State.heads(~mach, s) == State.heads(~mach, Pass.head(~mach, ~kern, n, s, c, m)): Tries.Trie<Head>
}:
  match m:
    case None{}:
      {==}
    case Some{+h}:
      Pass.at.heads(~mach, ~kern, n, s, c, h, Head.tip(~mach, s, h))

# Node.cast keeps the heads, once the head m is known
def Cast.head.heads(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  n: String,
  +s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  m: Maybe<&2, Head>
) -> {
  State.heads(~mach, s) == State.heads(~mach, Cast.head(~mach, ~kern, n, s, c, m)): Tries.Trie<Head>
}:
  match m:
    case None{}:
      {==}
    case Some{+h}:
      Cast.at.heads(~mach, ~kern, n, s, c, h, Head.tip(~mach, s, h))

# the words of a tip read as the tip
def Tip.round(t: Tip) -> {Tip.read(Tip.words(t)) == Some{t}: Maybe<&2, Tip>}:
  match t:
    case Tip{c, l, n, os}:
      %Equal.sym(
        Maybe<&2, Codes.Read<Tip>>,
        Codes.Code.four.read(
          ~Maybe<&2, Hashes.Hash>,
          ~Maybe<&2, Hashes.Hash>,
          ~U32,
          ~List<&2, String>,
          ~Tip,
          ~Codes.Codec.dec(
            Maybe<&2, Hashes.Hash>,
            Codes.Code.maybe.codec(~Hashes.Hash, ~Hashes.Hash.codec())
          ),
          ~Codes.Codec.dec(
            Maybe<&2, Hashes.Hash>,
            Codes.Code.maybe.codec(~Hashes.Hash, ~Hashes.Hash.codec())
          ),
          ~Codes.Codec.dec(U32, Codes.Code.token.codec()),
          ~Codes.Codec.dec(
            List<&2, String>,
            Codes.Code.list.codec(~String, ~Codes.Code.text.codec())
          ),
          x => y => z => w => Tip{x, y, z, w},
          Codes.Codec.enc(
            Maybe<&2, Hashes.Hash>,
            Codes.Code.maybe.codec(~Hashes.Hash, ~Hashes.Hash.codec())
          )(
            c
          )(
            Codes.Codec.enc(
              Maybe<&2, Hashes.Hash>,
              Codes.Code.maybe.codec(~Hashes.Hash, ~Hashes.Hash.codec())
            )(
              l
            )(
              Codes.Codec.enc(
                U32,
                Codes.Code.token.codec()
              )(
                n
              )(
                Codes.Codec.enc(
                  List<&2, String>,
                  Codes.Code.list.codec(~String, ~Codes.Code.text.codec())
                )(os)([])
              )
            )
          )
        ),
        Some{Codes.Read{Tip{c, l, n, os}, []}},
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
          x => y => z => w => Tip{x, y, z, w},
          c,
          l,
          n,
          os,
          []
        )
      ): {Read.whole(Tip, _) == Some{Tip{c, l, n, os}}: Maybe<&2, Tip>}
      {==}

# Put.holds once whether the node holds the data is known (b)
def Put.holds.if(
  ~mach: Machine(),
  -s2: Node<Machine.Q(mach)>,
  -ds: List<&2, List<&2, U32>>,
  -s3: Node<Machine.Q(mach)>,
  b: Bool,
  eb: {
    Stores.Store.holds(
      ~Node<Machine.Q(mach)>,
      ~Store.fetch(~mach),
      State.keep(~mach, s2, ds),
      ds
    )
      == b: Bool
  }
) -> {
  Shared.Maybe.when(
    Node<Machine.Q(mach)>,
    b,
    u => Some{State.keep(~mach, s2, ds)}
  )
    == Some{s3}: Maybe<&2, Node<Machine.Q(mach)>>
} -> {Stores.Store.holds(~Node<Machine.Q(mach)>, ~Store.fetch(~mach), s3, ds) == True{}: Bool}:
  match b:
    case False{}:
      e => Empty.absurd(
        {Stores.Store.holds(~Node<Machine.Q(mach)>, ~Store.fetch(~mach), s3, ds) == True{}: Bool},
        Shared.Maybe.none_ne_some(Node<Machine.Q(mach)>, s3, e)
      )
    case True{}:
      e =>
        %Shared.Maybe.some_inj(
          Node<Machine.Q(mach)>,
          State.keep(~mach, s2, ds),
          s3,
          e
        ): {Stores.Store.holds(~Node<Machine.Q(mach)>, ~Store.fetch(~mach), _, ds) == True{}: Bool}
        eb

# a node that a put gives holds the data
def Put.holds(
  ~mach: Machine(),
  s2: Node<Machine.Q(mach)>,
  +ds: List<&2, List<&2, U32>>,
  -s3: Node<Machine.Q(mach)>
) -> {
  State.put(~mach, s2, ds) == Some{s3}: Maybe<&2, Node<Machine.Q(mach)>>
} -> {Stores.Store.holds(~Node<Machine.Q(mach)>, ~Store.fetch(~mach), s3, ds) == True{}: Bool}:
  Put.holds.if(
    ~mach,
    s2,
    ds,
    s3,
    Stores.Store.holds(~Node<Machine.Q(mach)>, ~Store.fetch(~mach), State.keep(~mach, s2, ds), ds),
    {==}
  )

# a node that a put gives grew
def Put.grew(
  ~mach: Machine(),
  s2: Node<Machine.Q(mach)>,
  ds: List<&2, List<&2, U32>>,
  -s3: Node<Machine.Q(mach)>,
  e: {State.put(~mach, s2, ds) == Some{s3}: Maybe<&2, Node<Machine.Q(mach)>>}
) -> {Node.grows(~mach, s2, s3) == True{}: Bool}:
  %e: {State.after(~mach, s2, _) == True{}: Bool}
  Put.grows(~mach, s2, ds)

# a node that the put of a tip gives holds the tip under its hash
def Tip.put.at(
  ~mach: Machine(),
  s2: Node<Machine.Q(mach)>,
  +t2: Tip,
  +s3: Node<Machine.Q(mach)>
) -> {
  State.put(~mach, s2, [Tip.words(t2)]) == Some{s3}: Maybe<&2, Node<Machine.Q(mach)>>
} -> {Tip.at(~mach, s3, Tip.hash(t2)) == Some{t2}: Maybe<&2, Tip>}:
  e =>
    %Equal.sym(
      Maybe<&2, List<&2, U32>>,
      Store.fetch(~mach, s3, Hashes.Sha.hash(Tip.words(t2))),
      Some{Tip.words(t2)},
      Shared.Maybe.is_eq_sound(
        ~List<&2, U32>,
        ~Shared.List.is_eq(~U32, ~U32.is_eq),
        x => y => Shared.List.is_eq_sound(~U32, ~U32.is_eq, ~Shared.U32.laws(), x, y),
        Store.fetch(~mach, s3, Hashes.Sha.hash(Tip.words(t2))),
        Some{Tip.words(t2)}
      )(
        Shared.List.all.if_hit(
          Stores.Store.has(~Node<Machine.Q(mach)>, ~Store.fetch(~mach), s3, Tip.words(t2)),
          u => Stores.Store.holds(~Node<Machine.Q(mach)>, ~Store.fetch(~mach), s3, [])
        )(Put.holds(~mach, s2, [Tip.words(t2)], s3)(e))
      )
    ): {Maybe.bind(&2, List<&2, U32>, Tip, _, ws => Tip.read(ws)) == Some{t2}: Maybe<&2, Tip>}
    Tip.round(t2)

# what a line holds is what the log of its tip holds
def Line.read.at(
  ~mach: Machine(),
  -s: Node<Machine.Q(mach)>,
  -c: Ledgers.Chain,
  -k: List<&2, U32>,
  -v: List<&2, U32>,
  -h: Head,
  -t: Tip,
  em: {Node.head_of(~mach, s, c) == Some{h}: Maybe<&2, Head>},
  et: {Head.tip(~mach, s, h) == Some{t}: Maybe<&2, Tip>}
) -> {
  Line.get(~mach, s, c, k) == Some{v}: Maybe<&2, List<&2, U32>>
} -> {Node.get(~mach, s, Tip.log(t), k) == Some{v}: Maybe<&2, List<&2, U32>>}:
  e =>
    %et: {
      Maybe.bind(
        &2,
        Tip,
        List<&2, U32>,
        _,
        t1 => Node.get(~mach, s, Tip.log(t1), k)
      )
        == Some{v}: Maybe<&2, List<&2, U32>>
    }
    Line.get.of(~mach, s, c, k, v, Some{h}, em)(e)

# a head at the tip t2 holds what the log of t2 holds, in a node that grew
# from one that holds the tip
def Moved.cover(
  ~mach: Machine(),
  +s3: Node<Machine.Q(mach)>,
  +b: Node<Machine.Q(mach)>,
  +t2: Tip,
  k: List<&2, U32>,
  v: List<&2, U32>,
  -r: Ledgers.Id,
  -br: Maybe<&2, String>,
  -nx: U32,
  +g: {Node.grows(~mach, s3, b) == True{}: Bool},
  e3: {Tip.at(~mach, s3, Tip.hash(t2)) == Some{t2}: Maybe<&2, Tip>},
  v3: {Node.get(~mach, s3, Tip.log(t2), k) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> {
  Head.get(~mach, b, Head{r, br, nx, Some{Tip.hash(t2)}}, k) == Some{v}: Maybe<&2, List<&2, U32>>
}:
  %Equal.sym(
    Maybe<&2, Tip>,
    Tip.at(~mach, b, Tip.hash(t2)),
    Some{t2},
    Tip.at.grows(~mach, s3, b, Tip.hash(t2), t2, g)(e3)
  ): {
    Maybe.bind(
      &2,
      Tip,
      List<&2, U32>,
      _,
      t1 => Node.get(~mach, b, Tip.log(t1), k)
    )
      == Some{v}: Maybe<&2, List<&2, U32>>
  }
  Get.grows(~mach, s3, b, Tip.log(t2), k, v, g)(v3)

# a head moved to the tip t2 keeps the logs, when the log of t2 holds what
# the log of the tip t of the head before holds
def Moved.kept(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  +s3: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  r: Ledgers.Id,
  br: Maybe<&2, String>,
  nx: U32,
  +t2: Tip,
  qs: List<&2, Ledgers.Id>,
  h: Head,
  t: Tip,
  g3: {Node.grows(~mach, s, s3) == True{}: Bool},
  em: {Node.head_of(~mach, s, c) == Some{h}: Maybe<&2, Head>},
  et: {Head.tip(~mach, s, h) == Some{t}: Maybe<&2, Tip>},
  e3: {Tip.at(~mach, s3, Tip.hash(t2)) == Some{t2}: Maybe<&2, Tip>},
  kk: @k: List<
    &2,
    U32> -> @v: List<
    &2,
    U32> -> {
    Node.get(~mach, s, Tip.log(t), k) == Some{v}: Maybe<&2, List<&2, U32>>
  } -> {Node.get(~mach, s3, Tip.log(t2), k) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> Node.Keeps(
  ~mach,
  s,
  State.moved(
    ~mach,
    State.led(~mach, s, State.ledger(~mach, s3)),
    c,
    Head{r, br, nx, Some{Tip.hash(t2)}},
    qs
  )
):
  +x = State.led(~mach, s, State.ledger(~mach, s3))
  +ws = Wait.left(
    Wait.of(~mach, x, c),
    Tries.Trie.put_keys(~Ledgers.Id, ~Ledgers.Id.key, qs, Tries.Trie.new(Unit))
  )
  +b0 = Wait.set(~mach, x, c, ws)
  +hd = {Head{r, br, nx, Some{Tip.hash(t2)}}: Head}
  Head.put.kept(
    ~mach,
    s,
    b0,
    c,
    hd,
    Grows.to(~mach, s, x, b0, Led.wait(~mach, x, c, ws), Grows.back(~mach, s, s3, g3)),
    Equal.trans(
      Tries.Trie<Head>,
      State.heads(~mach, s),
      State.heads(~mach, x),
      State.heads(~mach, b0),
      Heads.led(~mach, s, State.ledger(~mach, s3)),
      Heads.wait(~mach, x, c, ws)
    ),
    +k => +v => e => Moved.cover(
      ~mach,
      s3,
      State.head(~mach, b0, c, hd),
      t2,
      k,
      v,
      r,
      br,
      nx,
      Grows.to(
        ~mach,
        s3,
        s3,
        State.head(~mach, b0, c, hd),
        Equal.trans(
          Ledgers.State(Machine.Q(mach)),
          State.ledger(~mach, State.head(~mach, b0, c, hd)),
          State.ledger(~mach, b0),
          State.ledger(~mach, s3),
          Led.head(~mach, b0, c, hd),
          Equal.trans(
            Ledgers.State(Machine.Q(mach)),
            State.ledger(~mach, b0),
            State.ledger(~mach, x),
            State.ledger(~mach, s3),
            Led.wait(~mach, x, c, ws),
            Led.led(~mach, s, State.ledger(~mach, s3))
          )
        ),
        Grows.refl(~mach, s3)
      ),
      e3,
      kk(k)(v)(Line.read.at(~mach, s, c, k, v, h, t, em, et)(e))
    )
  )

# Advance.moved keeps the logs, once the node m that the put gives is known
def Advance.moved.kept(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  +s2: Node<Machine.Q(mach)>,
  m: Maybe<&2, Node<Machine.Q(mach)>>,
  c: Ledgers.Chain,
  r: Ledgers.Id,
  br: Maybe<&2, String>,
  nx: U32,
  +t2: Tip,
  qs: List<&2, Ledgers.Id>,
  h: Head,
  t: Tip,
  g2: {Node.grows(~mach, s, s2) == True{}: Bool},
  em: {Node.head_of(~mach, s, c) == Some{h}: Maybe<&2, Head>},
  et: {Head.tip(~mach, s, h) == Some{t}: Maybe<&2, Tip>},
  kk: @k: List<
    &2,
    U32> -> @v: List<
    &2,
    U32> -> {
    Node.get(~mach, s, Tip.log(t), k) == Some{v}: Maybe<&2, List<&2, U32>>
  } -> {Node.get(~mach, s2, Tip.log(t2), k) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> {
  State.put(~mach, s2, [Tip.words(t2)]) == m: Maybe<&2, Node<Machine.Q(mach)>>
} -> Node.Keeps(~mach, s, Advance.moved(~mach, s, m, c, Head{r, br, nx, Some{Tip.hash(t2)}}, qs)):
  match m:
    case None{}:
      e2 => Kept.refl(~mach, s)
    case Some{+s3}:
      +e2 => Moved.kept(
        ~mach,
        s,
        s3,
        c,
        r,
        br,
        nx,
        t2,
        qs,
        h,
        t,
        Grows.trans(~mach, s, s2, s3)(g2)(Put.grew(~mach, s2, [Tip.words(t2)], s3, e2)),
        em,
        et,
        Tip.put.at(~mach, s2, t2, s3)(e2),
        +k => +v => e => Get.grows(
          ~mach,
          s2,
          s3,
          Tip.log(t2),
          k,
          v,
          Put.grew(~mach, s2, [Tip.words(t2)], s3, e2)
        )(kk(k)(v)(e))
      )

# a checked step keeps the logs
def Advance.ran.kept(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  r: Ledgers.Id,
  br: Maybe<&2, String>,
  next: U32,
  after: Maybe<&2, Hashes.Hash>,
  qs: List<&2, Ledgers.Id>,
  m: Maybe<&2, Run<Machine.Q(mach)>>,
  h: Head,
  t: Tip,
  em: {Node.head_of(~mach, s, c) == Some{h}: Maybe<&2, Head>},
  et: {Head.tip(~mach, s, h) == Some{t}: Maybe<&2, Tip>}
) -> {
  Run.after(~mach, s, m) == True{}: Bool
} -> (
  @k: List<
    &2,
    U32> -> @v: List<
    &2,
    U32> -> {
    Node.get(~mach, s, Tip.log(t), k) == Some{v}: Maybe<&2, List<&2, U32>>
  } -> Run.Keeps(~mach, k, v, m)
) -> Node.Keeps(~mach, s, Advance.ran(~mach, s, c, r, br, next, after, qs, m)):
  match m:
    case None{}:
      ga => rk => Kept.refl(~mach, s)
    case Some{Run{+s2, +t2}}:
      ga => rk => Kept.when(
        ~mach,
        Root.same(after, Some{Tip.hash(t2)}),
        s,
        Advance.moved(
          ~mach,
          s,
          State.put(~mach, s2, [Tip.words(t2)]),
          c,
          Head{r, br, U32.inc(next), Some{Tip.hash(t2)}},
          qs
        ),
        s,
        Advance.moved.kept(
          ~mach,
          s,
          s2,
          State.put(~mach, s2, [Tip.words(t2)]),
          c,
          r,
          br,
          U32.inc(next),
          t2,
          qs,
          h,
          t,
          ga,
          em,
          et,
          rk
        )({==}),
        Kept.refl(~mach, s)
      )

# a line with no head holds nothing
def Cover.none(
  ~mach: Machine(),
  -a: Node<Machine.Q(mach)>,
  -c: Ledgers.Chain,
  -b: Node<Machine.Q(mach)>,
  -hd: Head,
  -k: List<&2, U32>,
  -v: List<&2, U32>,
  em: {Node.head_of(~mach, a, c) == None{}: Maybe<&2, Head>}
) -> {
  Line.get(~mach, a, c, k) == Some{v}: Maybe<&2, List<&2, U32>>
} -> {Head.get(~mach, b, hd, k) == Some{v}: Maybe<&2, List<&2, U32>>}:
  e => Empty.absurd(
    {Head.get(~mach, b, hd, k) == Some{v}: Maybe<&2, List<&2, U32>>},
    Shared.Maybe.none_ne_some(List<&2, U32>, v, Line.get.of(~mach, a, c, k, v, None{}, em)(e))
  )

# a line whose head has no tip holds nothing
def Cover.wait(
  ~mach: Machine(),
  -a: Node<Machine.Q(mach)>,
  -c: Ledgers.Chain,
  -b: Node<Machine.Q(mach)>,
  -hd: Head,
  -k: List<&2, U32>,
  -v: List<&2, U32>,
  -r: Ledgers.Id,
  -br: Maybe<&2, String>,
  -n: U32,
  em: {Node.head_of(~mach, a, c) == Some{Head{r, br, n, None{}}}: Maybe<&2, Head>}
) -> {
  Line.get(~mach, a, c, k) == Some{v}: Maybe<&2, List<&2, U32>>
} -> {Head.get(~mach, b, hd, k) == Some{v}: Maybe<&2, List<&2, U32>>}:
  e => Empty.absurd(
    {Head.get(~mach, b, hd, k) == Some{v}: Maybe<&2, List<&2, U32>>},
    Shared.Maybe.none_ne_some(
      List<&2, U32>,
      v,
      Line.get.of(~mach, a, c, k, v, Some{Head{r, br, n, None{}}}, em)(e)
    )
  )

# a line that opens keeps the logs, once its head m is known
def Open.at.kept(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  m: Maybe<&2, Head>
) -> {
  Node.head_of(~mach, s, c) == m: Maybe<&2, Head>
} -> Node.Keeps(~mach, s, Open.at(~mach, s, c, m)):
  match m:
    case Some{Head{+r, Some{+b}, n, None{}}}:
      +em =>
        +hd = {
          Head{
            r,
            Some{b},
            0,
            Branch.first(~mach, s, b, Node.tip(~mach, s, Ledgers.Chain{r, None{}}))
          }: Head
        }
        Head.put.kept(
          ~mach,
          s,
          s,
          c,
          hd,
          Grows.refl(~mach, s),
          {==},
          k => v => Cover.wait(
            ~mach,
            s,
            c,
            State.head(~mach, s, c, hd),
            hd,
            k,
            v,
            r,
            Some{b},
            n,
            em
          )
        )
    case Some{Head{r, Some{b}, n, Some{t}}}:
      em => Kept.refl(~mach, s)
    case Some{Head{r, None{}, n, t}}:
      em => Kept.refl(~mach, s)
    case None{}:
      em => Kept.refl(~mach, s)

# a first head keeps the logs, once the head m of its line is known
def First.at.kept(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  h: Head,
  m: Maybe<&2, Head>
) -> {
  Node.head_of(~mach, s, c) == m: Maybe<&2, Head>
} -> Node.Keeps(~mach, s, First.at(~mach, s, c, h, m)):
  match m:
    case Some{Head{r, b, n, Some{t}}}:
      em => Kept.refl(~mach, s)
    case Some{Head{r, b, n, None{}}}:
      +em => Head.put.kept(
        ~mach,
        s,
        s,
        c,
        h,
        Grows.refl(~mach, s),
        {==},
        k => v => Cover.wait(~mach, s, c, State.head(~mach, s, c, h), h, k, v, r, b, n, em)
      )
    case None{}:
      +em => Head.put.kept(
        ~mach,
        s,
        s,
        c,
        h,
        Grows.refl(~mach, s),
        {==},
        k => v => Cover.none(~mach, s, c, State.head(~mach, s, c, h), h, k, v, em)
      )

# a first head on a node that grew from a, which grew from s, keeps the logs
def Start.head.kept(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  a: Node<Machine.Q(mach)>,
  m: Maybe<&2, Node<Machine.Q(mach)>>,
  +c: Ledgers.Chain,
  h: Head,
  g: {Node.grows(~mach, s, a) == True{}: Bool}
) -> {
  State.after(~mach, a, m) == True{}: Bool
} -> Node.Keeps(~mach, s, Start.head(~mach, s, m, c, h)):
  match m:
    case None{}:
      e => Kept.refl(~mach, s)
    case Some{+s3}:
      e =>
        +x = State.led(~mach, s, State.ledger(~mach, s3))
        Kept.trans(
          ~mach,
          s,
          x,
          State.first(~mach, x, c, h),
          Kept.same(
            ~mach,
            s,
            x,
            Grows.back(~mach, s, s3, Grows.trans(~mach, s, a, s3)(g)(e)),
            Heads.led(~mach, s, State.ledger(~mach, s3))
          ),
          First.at.kept(~mach, x, c, h, Node.head_of(~mach, x, c))({==})
        )

# Start.kept once the content m of the store is known
def Start.with.kept(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  +i: Ledgers.Id,
  os: List<&2, String>,
  m: Maybe<&2, Work<Machine.Q(mach)>>
) -> {
  Work.after(~mach, s, m) == True{}: Bool
} -> Node.Keeps(~mach, s, Start.with(~mach, s, i, os, m)):
  match m:
    case None{}:
      e => Kept.refl(~mach, s)
    case Some{Work{+s2, c}}:
      e =>
        +t = {Tip{c, None{}, 0, os}: Tip}
        Start.head.kept(
          ~mach,
          s,
          s2,
          State.put(~mach, s2, [Tip.words(t)]),
          Ledgers.Chain{i, None{}},
          Head{i, None{}, 0, Some{Tip.hash(t)}},
          e
        )(Put.grows(~mach, s2, [Tip.words(t)]))

# a line that a node follows keeps the logs, once its head m is known
def Follow.new.kept(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  +r: Ledgers.Id,
  +l: Maybe<&2, String>,
  m: Maybe<&2, Head>
) -> {
  Node.head_of(~mach, s, Line.chain(r, l)) == m: Maybe<&2, Head>
} -> Node.Keeps(~mach, s, Follow.new(~mach, s, r, l, m)):
  match m:
    case Some{h}:
      em => Kept.refl(~mach, s)
    case None{}:
      +em => Head.put.kept(
        ~mach,
        s,
        s,
        Line.chain(r, l),
        Head{r, l, 0, None{}},
        Grows.refl(~mach, s),
        {==},
        k => v => Cover.none(
          ~mach,
          s,
          Line.chain(r, l),
          State.head(~mach, s, Line.chain(r, l), Head{r, l, 0, None{}}),
          Head{r, l, 0, None{}},
          k,
          v,
          em
        )
      )

# a request that waits keeps the heads
def Heads.waits(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  i: Ledgers.Id
) -> {State.heads(~mach, s) == State.heads(~mach, State.wait(~mach, s, c, i)): Tries.Trie<Head>}:
  match s:
    case Node{l, hs, ws, ks}:
      {==}

# a work that reads a key, after a step that keeps the read
def Reads.bind(
  ~mach: Machine(),
  -k: List<&2, U32>,
  -v: List<&2, U32>,
  m: Maybe<&2, Work<Machine.Q(mach)>>,
  -f: Work<Machine.Q(mach)> -> Maybe<&2, Work<Machine.Q(mach)>>
) -> Work.Reads(
  ~mach,
  k,
  v,
  m
) -> (
  @w: Work<Machine.Q(mach)> -> Work.Reads(~mach, k, v, Some{w}) -> Work.Reads(~mach, k, v, f(w))
) -> Work.Reads(~mach, k, v, Maybe.bind(&2, Work<Machine.Q(mach)>, Work<Machine.Q(mach)>, m, f)):
  match m:
    case None{}:
      hm => hf => Unit{}
    case Some{w}:
      hm => hf => hf(w)(hm)

# the words after the first one
def Words.rest(ws: List<&2, U32>) -> List<&2, U32>:
  match ws:
    case Nil{}:
      []
    case Con{w, r}:
      r

# the text that a read gave, "" without one
def Read.text(m: Maybe<&2, Codes.Read<String>>) -> String:
  match m:
    case Some{Codes.Read{t, r}}:
      t
    case None{}:
      ""

# texts with the same code are the same
def Text.same(
  t1: String,
  t2: String,
  e: {Codes.Code.text(t1, []) == Codes.Code.text(t2, []): List<&2, U32>}
) -> {t1 == t2: String}:
  Equal.trans(
    String,
    t1,
    Read.text(Codes.Code.text.read(Codes.Code.text(t1, []))),
    t2,
    Equal.sym(
      String,
      Read.text(Codes.Code.text.read(Codes.Code.text(t1, []))),
      t1,
      Equal.cong(
        Maybe<&2, Codes.Read<String>>,
        String,
        Read.text,
        Codes.Code.text.read(Codes.Code.text(t1, [])),
        Some{Codes.Read{t1, []}},
        Codes.Code.text_read(t1, [])
      )
    ),
    Equal.trans(
      String,
      Read.text(Codes.Code.text.read(Codes.Code.text(t1, []))),
      Read.text(Codes.Code.text.read(Codes.Code.text(t2, []))),
      t2,
      Equal.cong(
        List<&2, U32>,
        String,
        ws => Read.text(Codes.Code.text.read(ws)),
        Codes.Code.text(t1, []),
        Codes.Code.text(t2, []),
        e
      ),
      Equal.cong(
        Maybe<&2, Codes.Read<String>>,
        String,
        Read.text,
        Codes.Code.text.read(Codes.Code.text(t2, [])),
        Some{Codes.Read{t2, []}},
        Codes.Code.text_read(t2, [])
      )
    )
  )

# resources that are the same are equal
def Name.sound(
  +m: Resources.Name,
  +n: Resources.Name
) -> {Resources.Name.is_eq(m, n) == True{}: Bool} -> {m == n: Resources.Name}:
  match m n:
    case Resources.Name{t1} Resources.Name{t2}:
      e => Equal.cong(
        String,
        Resources.Name,
        z => Resources.Name{z},
        t1,
        t2,
        Texts.String.eq_sound(t1, t2)(e)
      )

# a work that reads a key, after a read that gives the next step
def Reads.with(
  ~mach: Machine(),
  -A: Data,
  -k: List<&2, U32>,
  -v: List<&2, U32>,
  +ma: Maybe<&2, A>,
  -f: A -> Maybe<&2, Work<Machine.Q(mach)>>
) -> (
  @a: A -> Work.Reads(~mach, k, v, f(a))
) -> Work.Reads(~mach, k, v, Maybe.bind(&2, A, Work<Machine.Q(mach)>, ma, f)):
  match ma:
    case None{}:
      hf => Unit{}
    case Some{a}:
      hf => hf(a)

# a set of another key keeps what a work reads
def Set.kept.work(
  ~mach: Machine(),
  +w: Work<Machine.Q(mach)>,
  k: List<&2, U32>,
  x: List<&2, U32>,
  k2: List<&2, U32>,
  v: List<&2, U32>,
  hne: {Shared.List.is_eq(~U32, ~U32.is_eq, k, k2) == False{}: Bool}
) -> Work.Reads(~mach, k2, v, Some{w}) -> Work.Reads(~mach, k2, v, Work.set(~mach, w, k, x)):
  match w:
    case Work{s, h}:
      hget => Set.kept(~mach, s, h, k, x, k2, v, hne, hget)

# Keep.reads once it is known whether the node holds the new data (b)
def Keep.reads.if(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  h: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>,
  k: List<&2, U32>,
  v: List<&2, U32>,
  +b: Bool,
  hget: {Node.get(~mach, s, h, k) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> Work.Reads(
  ~mach,
  k,
  v,
  Work.on(
    ~mach,
    Shared.Maybe.when(Node<Machine.Q(mach)>, b, u => Some{State.keep(~mach, s, ns)}),
    h
  )
):
  match b:
    case False{}:
      Unit{}
    case True{}:
      Get.grows(~mach, s, State.keep(~mach, s, ns), h, k, v, Grows.keep(~mach, s, ns))(hget)

# new data keeps what a work reads
def Keep.reads(
  ~mach: Machine(),
  +w: Work<Machine.Q(mach)>,
  +ns: List<&2, List<&2, U32>>,
  k: List<&2, U32>,
  v: List<&2, U32>
) -> Work.Reads(~mach, k, v, Some{w}) -> Work.Reads(~mach, k, v, Work.keep(~mach, w, ns)):
  match w:
    case Work{s, h}:
      hget => Keep.reads.if(
        ~mach,
        s,
        h,
        ns,
        k,
        v,
        Stores.Store.holds(
          ~Node<Machine.Q(mach)>,
          ~Store.fetch(~mach),
          State.keep(~mach, s, ns),
          ns
        ),
        hget
      )

# Set.read once it is known whether the node holds the new nodes (b)
def Set.read.if(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  +h: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  +x: List<&2, U32>,
  +hh: Hashes.Hash,
  +ws: List<&2, List<&2, U32>>,
  +b: Bool,
  eb: {
    Stores.Store.holds(
      ~Node<Machine.Q(mach)>,
      ~Store.fetch(~mach),
      State.keep(~mach, s, ws),
      ws
    )
      == b: Bool
  },
  em: {Node.set(~mach, s, h, k, x) == Some{Trees.Put{hh, ws}}: Maybe<&2, Trees.Put>}
) -> Work.Reads(
  ~mach,
  k,
  x,
  Work.on(
    ~mach,
    Shared.Maybe.when(Node<Machine.Q(mach)>, b, u => Some{State.keep(~mach, s, ws)}),
    Some{hh}
  )
):
  match b:
    case False{}:
      Unit{}
    case True{}:
      Equal.trans(
        Maybe<&2, List<&2, U32>>,
        Node.get(~mach, State.keep(~mach, s, ws), Some{hh}, k),
        Trees.Tree.get.plain(
          ~Node<Machine.Q(mach)>,
          ~Store.fetch(~mach),
          State.keep(~mach, s, ws),
          Some{hh},
          k
        ),
        Some{x},
        Trees.Tree.get_plain(
          ~Node<Machine.Q(mach)>,
          ~Store.fetch(~mach),
          State.keep(~mach, s, ws),
          Some{hh},
          k
        ),
        Trees.Tree.get_set(
          ~Node<Machine.Q(mach)>,
          ~Store.fetch(~mach),
          s,
          State.keep(~mach, s, ws),
          h,
          k,
          x,
          Trees.Put{hh, ws}
        )(
          Equal.trans(
            Maybe<&2, Trees.Put>,
            Trees.Tree.set.plain(~Node<Machine.Q(mach)>, ~Store.fetch(~mach), s, h, k, x),
            Node.set(~mach, s, h, k, x),
            Some{Trees.Put{hh, ws}},
            Equal.sym(
              Maybe<&2, Trees.Put>,
              Node.set(~mach, s, h, k, x),
              Trees.Tree.set.plain(~Node<Machine.Q(mach)>, ~Store.fetch(~mach), s, h, k, x),
              Trees.Tree.set_plain(~Node<Machine.Q(mach)>, ~Store.fetch(~mach), s, h, k, x)
            ),
            em
          )
        )(eb)
      )

# Set.read once the new subtree m is known
def Set.read.of(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  h: Maybe<&2, Hashes.Hash>,
  k: List<&2, U32>,
  x: List<&2, U32>,
  +m: Maybe<&2, Trees.Put>,
  em: {Node.set(~mach, s, h, k, x) == m: Maybe<&2, Trees.Put>}
) -> Work.Reads(~mach, k, x, Work.of(~mach, s, m)):
  match m:
    case None{}:
      Unit{}
    case Some{Trees.Put{hh, ws}}:
      Set.read.if(
        ~mach,
        s,
        h,
        k,
        x,
        hh,
        ws,
        Stores.Store.holds(
          ~Node<Machine.Q(mach)>,
          ~Store.fetch(~mach),
          State.keep(~mach, s, ws),
          ws
        ),
        {==},
        em
      )

# a key that a work sets, it reads
def Set.read(
  ~mach: Machine(),
  +w: Work<Machine.Q(mach)>,
  +k: List<&2, U32>,
  +x: List<&2, U32>
) -> Work.Reads(~mach, k, x, Work.set(~mach, w, k, x)):
  match w:
    case Work{s, h}:
      Set.read.of(~mach, s, h, k, x, Node.set(~mach, s, h, k, x), {==})

# the code of a count is not empty
def Count.full(
  n: Nat,
  r: List<&2, U32>
) -> {Shared.List.is_eq(~U32, ~U32.is_eq, [], Codes.Code.count(n, r)) == False{}: Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

# Add.reads once the value m of the key in the log is known
def Add.reads.at(
  ~mach: Machine(),
  r: Run<Machine.Q(mach)>,
  +k: List<&2, U32>,
  +x: List<&2, U32>,
  m: Maybe<&2, List<&2, U32>>
) -> Run.Keeps(~mach, k, x, Run.add.at(~mach, r, k, x, m)):
  match r m:
    case Run{+s, +t} None{}:
      Run.logged.keeps(
        ~mach,
        k,
        x,
        t,
        Work.set(~mach, Work{s, Tip.log(t)}, k, x)
      )(Set.read(~mach, Work{s, Tip.log(t)}, k, x))
    case y Some{old}:
      Unit{}

# a new key of the log of a run reads back
def Add.reads(
  ~mach: Machine(),
  +r: Run<Machine.Q(mach)>,
  +k: List<&2, U32>,
  x: List<&2, U32>
) -> Run.Keeps(~mach, k, x, Run.add(~mach, r, k, x)):
  Add.reads.at(~mach, r, k, x, Node.get(~mach, Run.state(~mach, r), Tip.log(Run.tip(~mach, r)), k))

# a log that reads the outcome key of i as v holds an outcome of i
def Outs.of(
  ~mach: Machine(),
  i: Ledgers.Id,
  v: List<&2, U32>,
  +m: Maybe<&2, Run<Machine.Q(mach)>>
) -> Run.Keeps(~mach, Log.out(i), v, m) -> Run.Outs(~mach, m, i):
  match m:
    case None{}:
      h => Unit{}
    case Some{Run{s, t}}:
      h =>
        %Equal.sym(
          Maybe<&2, List<&2, U32>>,
          Node.get(~mach, s, Tip.log(t), Log.out(i)),
          Some{v},
          h
        ): {Maybe.is_some(&2, List<&2, U32>, _) == True{}: Bool}
        {==}

# each run that f gives has an outcome of i: so has the run after a step
def Outs.all(
  ~mach: Machine(),
  +m: Maybe<&2, Run<Machine.Q(mach)>>,
  -f: Run<Machine.Q(mach)> -> Maybe<&2, Run<Machine.Q(mach)>>,
  -i: Ledgers.Id,
  hf: @r: Run<Machine.Q(mach)> -> Run.Outs(~mach, f(r), i)
) -> Run.Outs(~mach, Maybe.bind(&2, Run<Machine.Q(mach)>, Run<Machine.Q(mach)>, m, f), i):
  match m:
    case None{}:
      Unit{}
    case Some{r}:
      hf(r)

# one of two runs, each with an outcome of i
def Outs.when(
  ~mach: Machine(),
  +b: Bool,
  -mx: Maybe<&2, Run<Machine.Q(mach)>>,
  -my: Maybe<&2, Run<Machine.Q(mach)>>,
  -i: Ledgers.Id,
  hx: Run.Outs(~mach, mx, i),
  hy: Run.Outs(~mach, my, i)
) -> Run.Outs(~mach, Shared.Bool.when(Maybe<&2, Run<Machine.Q(mach)>>, b, u => mx, u => my), i):
  match b:
    case True{}:
      hx
    case False{}:
      hy

# a request that is refused as stale has an outcome
def Stale.outs(
  ~mach: Machine(),
  +r: Run<Machine.Q(mach)>,
  +i: Ledgers.Id
) -> Run.Outs(~mach, Step.stale(~mach, r, i), i):
  Outs.of(
    ~mach,
    i,
    Out.words(Out.Stale{}),
    Run.add(~mach, r, Log.out(i), Out.words(Out.Stale{}))
  )(Add.reads(~mach, r, Log.out(i), Out.words(Out.Stale{})))

# a request that is taken has an outcome
def Taken.outs(
  ~mach: Machine(),
  +r: Run<Machine.Q(mach)>,
  +i: Ledgers.Id,
  own: Maybe<&2, List<&2, String>>
) -> Run.Outs(~mach, Step.taken(~mach, r, i, own), i):
  +n = Tip.count(Run.tip(~mach, r))
  Outs.of(
    ~mach,
    i,
    Out.words(Out.Taken{n}),
    Step.taken(~mach, r, i, own)
  )(
    Keeps.bind(
      ~mach,
      Log.out(i),
      Out.words(Out.Taken{n}),
      Run.add(~mach, r, Log.out(i), Out.words(Out.Taken{n})),
      +r1 => Maybe.bind(
        &2,
        Run<Machine.Q(mach)>,
        Run<Machine.Q(mach)>,
        Run.add(
          ~mach,
          r1,
          Log.version(n),
          Version.words(Version{i, Tip.content(Run.tip(~mach, r1))})
        ),
        r2 => Some{Run.next(~mach, r2, own)}
      )
    )(
      Add.reads(~mach, r, Log.out(i), Out.words(Out.Taken{n}))
    )(
      +r1 => h1 => Keeps.bind(
        ~mach,
        Log.out(i),
        Out.words(Out.Taken{n}),
        Run.add(
          ~mach,
          r1,
          Log.version(n),
          Version.words(Version{i, Tip.content(Run.tip(~mach, r1))})
        ),
        r2 => Some{Run.next(~mach, r2, own)}
      )(
        Add.kept(
          ~mach,
          r1,
          Log.version(n),
          Version.words(Version{i, Tip.content(Run.tip(~mach, r1))}),
          Log.out(i),
          Out.words(Out.Taken{n})
        )(h1)
      )(r2 => h2 => Next.kept(~mach, r2, own, Log.out(i), Out.words(Out.Taken{n}))(h2))
    )
  )

# a judged request has an outcome
def Judged.outs(
  ~mach: Machine(),
  r: Run<Machine.Q(mach)>,
  i: Ledgers.Id,
  own: Maybe<&2, List<&2, String>>,
  +m: Maybe<&2, Verdict<Machine.Q(mach)>>
) -> Run.Outs(~mach, Step.judged(~mach, r, i, own, m), i):
  match m:
    case None{}:
      Unit{}
    case Some{Verdict.Stale{}}:
      Stale.outs(~mach, r, i)
    case Some{Verdict.Taken{Work{s2, h}}}:
      Taken.outs(~mach, Run.over(~mach, r, s2, h), i, own)

# a mark on a version has an outcome
def Marked.outs(
  ~mach: Machine(),
  r: Run<Machine.Q(mach)>,
  i: Ledgers.Id,
  m: String,
  +v: Maybe<&2, Version>
) -> Run.Outs(~mach, Step.marked(~mach, r, i, m, v), i):
  match v:
    case None{}:
      Unit{}
    case Some{x}:
      Outs.all(
        ~mach,
        Run.add(~mach, r, Log.mark(m), Ledgers.Id.code(Version.id(x), [])),
        r2 => Step.taken(~mach, r2, i, None{}),
        i,
        r2 => Taken.outs(~mach, r2, i, None{})
      )

# a request for a mark has an outcome
def Mark.outs(
  ~mach: Machine(),
  +r: Run<Machine.Q(mach)>,
  +i: Ledgers.Id,
  +m: String
) -> Run.Outs(~mach, Step.mark(~mach, r, i, m), i):
  +s = Run.state(~mach, r)
  +t = Run.tip(~mach, r)
  +n = Tip.count(t)
  Outs.when(
    ~mach,
    List.all.if(
      u => Maybe.is_none(&2, Ledgers.Id, Line.mark(~mach, s, t, m)),
      Bool.not(U32.is_eq(n, 0))
    ),
    Step.marked(~mach, r, i, m, Line.version(~mach, s, t, U32.sub(n, 1))),
    Step.stale(~mach, r, i),
    i,
    Marked.outs(~mach, r, i, m, Line.version(~mach, s, t, U32.sub(n, 1))),
    Stale.outs(~mach, r, i)
  )

# the first tip of a new branch has an outcome
def Branch.made.outs(
  ~mach: Machine(),
  +r: Run<Machine.Q(mach)>,
  i: Ledgers.Id,
  b: String,
  +m: Maybe<&2, Made<Machine.Q(mach)>>
) -> Run.Outs(~mach, Branch.made(~mach, r, i, b, m), i):
  match m:
    case None{}:
      Unit{}
    case Some{Made{t, s2}}:
      Outs.all(
        ~mach,
        Run.add(
          ~mach,
          Run.over(~mach, r, s2, Tip.content(Run.tip(~mach, r))),
          Log.start(b),
          Hashes.Hash.code(Tip.hash(t), [])
        ),
        r2 => Step.taken(~mach, r2, i, None{}),
        i,
        r2 => Taken.outs(~mach, r2, i, None{})
      )

# a run whose log reads the outcome key of i has an outcome of i
def Outs.self(
  ~mach: Machine(),
  +r: Run<Machine.Q(mach)>,
  i: Ledgers.Id,
  ws: List<&2, U32>
) -> {
  Node.get(
    ~mach,
    Run.state(~mach, r),
    Tip.log(Run.tip(~mach, r)),
    Log.out(i)
  )
    == Some{ws}: Maybe<&2, List<&2, U32>>
} -> Run.Outs(~mach, Some{r}, i):
  match r:
    case Run{s, t}:
      eg =>
        %Equal.sym(
          Maybe<&2, List<&2, U32>>,
          Node.get(~mach, s, Tip.log(t), Log.out(i)),
          Some{ws},
          eg
        ): {Maybe.is_some(&2, List<&2, U32>, _) == True{}: Bool}
        {==}

# no run gives no run
def All.none(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  c: Ledgers.Chain,
  +qs: List<&2, Ledgers.Id>
) -> {Step.all(~mach, ~kern, c, qs, None{}) == None{}: Maybe<&2, Run<Machine.Q(mach)>>}:
  match qs:
    case Nil{}:
      {==}
    case Con{i, rest}:
      All.none(~mach, ~kern, c, rest)

# a run reads what its log holds
def Keeps.self(
  ~mach: Machine(),
  +r: Run<Machine.Q(mach)>,
  k: List<&2, U32>,
  v: List<&2, U32>
) -> {
  Node.get(
    ~mach,
    Run.state(~mach, r),
    Tip.log(Run.tip(~mach, r)),
    k
  )
    == Some{v}: Maybe<&2, List<&2, U32>>
} -> Run.Keeps(~mach, k, v, Some{r}):
  match r:
    case Run{s, t}:
      e => e

# Wait.left_keeps at the first request j, once it is known whether it is i
# (same) and whether a step ran it (d)
def Left.keeps.at(
  j: Ledgers.Id,
  ks: List<&2, Ledgers.Id>,
  rs: List<&2, Ledgers.Id>,
  done: Tries.Trie<Unit>,
  i: Ledgers.Id,
  +same: Bool,
  +d: Bool,
  es: {Ledgers.Id.is_eq(j, i) == same: Bool},
  ed: {Tries.Trie.has(Unit, done, Ledgers.Id.key(j)) == d: Bool},
  hd: {Tries.Trie.has(Unit, done, Ledgers.Id.key(i)) == False{}: Bool},
  ih: {
    List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, rs, i) == True{}: Bool
  } -> {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, ks, i) == True{}: Bool}
) -> {
  List.any.if(u => List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, rs, i), same) == True{}: Bool
} -> {
  List.contains(
    ~Ledgers.Id,
    ~Ledgers.Id.is_eq,
    List.filter.put(Ledgers.Id, j, ks, Bool.not(d)),
    i
  )
    == True{}: Bool
}:
  match same d:
    case True{} False{}:
      e =>
        %Equal.sym(
          Bool,
          Ledgers.Id.is_eq(j, i),
          True{},
          es
        ): {
          List.any.if(u => List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, ks, i), _) == True{}: Bool
        }
        {==}
    case True{} True{}:
      e => Empty.absurd(
        {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, ks, i) == True{}: Bool},
        Shared.Bool.false_ne_true(
          Equal.trans(
            Bool,
            False{},
            Tries.Trie.has(Unit, done, Ledgers.Id.key(i)),
            True{},
            Equal.sym(Bool, Tries.Trie.has(Unit, done, Ledgers.Id.key(i)), False{}, hd),
            (
              %Ledgers.Id.is_eq_sound(j, i)(es): {Tries.Trie.has(Unit, done, Ledgers.Id.key(_)) == True{}: Bool}
              ed)
          )
        )
      )
    case False{} False{}:
      e => Shared.List.contains_cons(~Ledgers.Id, ~Ledgers.Id.is_eq, j, ks, i)(ih(e))
    case False{} True{}:
      e => ih(e)

# Plan.follow_allowed once it is known whether the rules allow the vote (b)
def Follow.allowed.at(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  t: Tip,
  th: Maybe<&2, Hashes.Hash>,
  v: Ledgers.Vote,
  from: List<&2, String>,
  b: Bool
) -> {
  Maybe.is_some(
    &2,
    Run<Machine.Q(mach)>,
    Plan.run(
      ~mach,
      Shared.Bool.when(
        Plan<Machine.Q(mach)>,
        b,
        u => Plan.copy(~mach, ~kern, s, c, t, th, Some{v}, from),
        u => Plan{[], None{}, []}
      )
    )
  )
    == True{}: Bool
} -> {b == True{}: Bool}:
  match b:
    case True{}:
      e => {==}
    case False{}:
      e => e

# a step that the owners decided at a place in a, they decided in a node that
# grew, with the owners that it reads
def Decide.up(
  ~mach: Machine(),
  a: Node<Machine.Q(mach)>,
  u: Node<Machine.Q(mach)>,
  t: Tip,
  w: Ledgers.Where,
  v: Ledgers.Vote,
  g: {Node.grows(~mach, a, u) == True{}: Bool}
) -> {
  Ledgers.State.decide(
    ~Machine.Q(mach),
    State.ledger(~mach, a),
    w,
    Tip.owners(t)
  )
    == Some{v}: Maybe<&2, Ledgers.Vote>
} -> {
  Ledgers.State.decide(
    ~Machine.Q(mach),
    State.ledger(~mach, u),
    w,
    Tip.owners(t)
  )
    == Some{v}: Maybe<&2, Ledgers.Vote>
}:
  e =>
    Ledgers.State.decide_grows(
      ~Machine.Q(mach),
      ~Machine.same(mach),
      ~Machine.laws(mach),
      State.ledger(~mach, a),
      State.ledger(~mach, u),
      w,
      Tip.owners(t),
      v
    )(g)(e)

# Scan.elim at a round, once what it decides is known (m)
def Scan.elim.at(
  ~mach: Machine(),
  -R: Type,
  -s: Node<Machine.Q(mach)>,
  -c: Ledgers.Chain,
  -n: U32,
  -os: List<&2, String>,
  -p: Nat,
  -v: Ledgers.Vote,
  r: Nat,
  m: Maybe<&2, Ledgers.Vote>,
  rec: {
    Height.decide(~mach, s, c, n, os, p) == Some{v}: Maybe<&2, Ledgers.Vote>
  } -> (
    @q: Nat -> {
      Ledgers.State.decide(
        ~Machine.Q(mach),
        State.ledger(~mach, s),
        Ledgers.Where{c, n, q},
        os
      )
        == Some{v}: Maybe<&2, Ledgers.Vote>
    } -> R
  ) -> R
) -> {
  Ledgers.State.decide(
    ~Machine.Q(mach),
    State.ledger(~mach, s),
    Ledgers.Where{c, n, r},
    os
  )
    == m: Maybe<&2, Ledgers.Vote>
} -> {
  Vote.first(m, u => Height.decide(~mach, s, c, n, os, p)) == Some{v}: Maybe<&2, Ledgers.Vote>
} -> (
  @q: Nat -> {
    Ledgers.State.decide(
      ~Machine.Q(mach),
      State.ledger(~mach, s),
      Ledgers.Where{c, n, q},
      os
    )
      == Some{v}: Maybe<&2, Ledgers.Vote>
  } -> R
) -> R:
  match m:
    case None{}:
      em => e => f => rec(e)(f)
    case Some{x}:
      em => e => f => f(
        r
      )(
        Equal.trans(
          Maybe<&2, Ledgers.Vote>,
          Ledgers.State.decide(
            ~Machine.Q(mach),
            State.ledger(~mach, s),
            Ledgers.Where{c, n, r},
            os
          ),
          Some{x},
          Some{v},
          em,
          e
        )
      )

# a step that a height decides in a round up to k is decided in some round
def Scan.elim(
  ~mach: Machine(),
  -R: Type,
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  +n: U32,
  +os: List<&2, String>,
  k: Nat,
  -v: Ledgers.Vote
) -> {
  Height.decide(~mach, s, c, n, os, k) == Some{v}: Maybe<&2, Ledgers.Vote>
} -> (
  @q: Nat -> {
    Ledgers.State.decide(
      ~Machine.Q(mach),
      State.ledger(~mach, s),
      Ledgers.Where{c, n, q},
      os
    )
      == Some{v}: Maybe<&2, Ledgers.Vote>
  } -> R
) -> R:
  match k:
    case 0n:
      e => f => f(0n)(e)
    case 1n+(+p):
      Scan.elim.at(
        ~mach,
        R,
        s,
        c,
        n,
        os,
        p,
        v,
        1n+p,
        Ledgers.State.decide(
          ~Machine.Q(mach),
          State.ledger(~mach, s),
          Ledgers.Where{c, n, 1n+p},
          os
        ),
        Scan.elim(~mach, R, s, c, n, os, p, v)
      )({==})

# a head is at its own height
def Level.refl(h: Head) -> {Heads.level(Some{h}, Some{h}) == True{}: Bool}:
  match h:
    case Head{r, b, n, t}:
      Shared.Eq.refl(~U32, ~U32.is_eq, Shared.U32.laws(), n)

# the step that the owners in the tip of the head h decided next on the line
# c, in a round up to k, if they did
def Advance.found(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  +h: Head,
  k: Nat
) -> Maybe<&2, Ledgers.Vote>:
  Maybe.bind(
    &2,
    Tip,
    Ledgers.Vote,
    Head.tip(~mach, s, h),
    t => Height.decide(~mach, s, c, Head.next(h), Tip.owners(t), k)
  )

# the step that the owners in the tip of the head h decided next on the line
# c, in a round of which the node holds a ballot, if they did
def Advance.vote(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  +h: Head
) -> Maybe<&2, Ledgers.Vote>:
  Advance.found(~mach, s, c, h, Round.seen(~mach, s, c, Head.next(h)))

# the head h after the step m: one height up, at the tip that the step names
# (no step, or one that names no tip: h)
def Head.step(h: Head, m: Maybe<&2, Ledgers.Vote>) -> Head:
  match h m:
    case Head{r, b, n, th} Some{Ledgers.Vote{before, qs, Some{x}}}:
      Head{r, b, U32.inc(n), Some{x}}
    case x y:
      x

# that the head of the line c in the node s2, when it is not at the height of
# h, is x
def Moves(~mach: Machine(), s2: Node<Machine.Q(mach)>, c: Ledgers.Chain, h: Head, x: Head) -> Type:
  {
    Heads.level(Some{h}, Node.head_of(~mach, s2, c)) == False{}: Bool
  } -> {Node.head_of(~mach, s2, c) == Some{x}: Maybe<&2, Head>}

# a node whose head is h did not move it
def Moves.stay(
  ~mach: Machine(),
  -s: Node<Machine.Q(mach)>,
  -c: Ledgers.Chain,
  h: Head,
  -x: Head,
  em: {Node.head_of(~mach, s, c) == Some{h}: Maybe<&2, Head>}
) -> Moves(~mach, s, c, h, x):
  hl => Empty.absurd(
    {Node.head_of(~mach, s, c) == Some{x}: Maybe<&2, Head>},
    Shared.Bool.false_ne_true(
      Equal.trans(
        Bool,
        False{},
        Heads.level(Some{h}, Some{h}),
        True{},
        Equal.trans(
          Bool,
          False{},
          Heads.level(Some{h}, Node.head_of(~mach, s, c)),
          Heads.level(Some{h}, Some{h}),
          Equal.sym(Bool, Heads.level(Some{h}, Node.head_of(~mach, s, c)), False{}, hl),
          Equal.cong(
            Maybe<&2, Head>,
            Bool,
            m => Heads.level(Some{h}, m),
            Node.head_of(~mach, s, c),
            Some{h},
            em
          )
        ),
        Level.refl(h)
      )
    )
  )

# one of two nodes, each with its head moved to x or not at all
def Moves.when(
  ~mach: Machine(),
  b: Bool,
  -sx: Node<Machine.Q(mach)>,
  -sy: Node<Machine.Q(mach)>,
  -c: Ledgers.Chain,
  -h: Head,
  -x: Head,
  hx: Moves(~mach, sx, c, h, x),
  hy: Moves(~mach, sy, c, h, x)
) -> Moves(~mach, Shared.Bool.when(Node<Machine.Q(mach)>, b, u => sx, u => sy), c, h, x):
  match b:
    case True{}:
      hx
    case False{}:
      hy

# the head of a line, after it is set
def Head.at_set(
  ~mach: Machine(),
  b0: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  hd: Head
) -> {Node.head_of(~mach, State.head(~mach, b0, c, hd), c) == Some{hd}: Maybe<&2, Head>}:
  Equal.trans(
    Maybe<&2, Head>,
    Node.head_of(~mach, State.head(~mach, b0, c, hd), c),
    Bool.pick(
      Maybe<&2, Head>,
      Tries.Trie.same_key(Ledgers.Chain.key(c), Ledgers.Chain.key(c)),
      Some{hd},
      Node.head_of(~mach, b0, c)
    ),
    Some{hd},
    Head.of_set(~mach, b0, c, hd, c),
    Pick.of(
      Maybe<&2, Head>,
      True{},
      Tries.Trie.same_key(Ledgers.Chain.key(c), Ledgers.Chain.key(c)),
      Some{hd},
      Node.head_of(~mach, b0, c),
      Shared.List.is_eq_refl(~Bool, ~Shared.Bool.is_eq, ~Shared.Bool.laws(), Ledgers.Chain.key(c))
    )
  )

# Advance.moved moves the head to hd, or not at all
def Advance.moved.moves(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  m: Maybe<&2, Node<Machine.Q(mach)>>,
  +c: Ledgers.Chain,
  hd: Head,
  qs: List<&2, Ledgers.Id>,
  h: Head,
  -x: Head,
  em: {Node.head_of(~mach, s, c) == Some{h}: Maybe<&2, Head>},
  ex: {hd == x: Head}
) -> Moves(~mach, Advance.moved(~mach, s, m, c, hd, qs), c, h, x):
  match m:
    case None{}:
      Moves.stay(~mach, s, c, h, x, em)
    case Some{+s3}:
      hl =>
        %ex: {
          Node.head_of(
            ~mach,
            State.moved(~mach, State.led(~mach, s, State.ledger(~mach, s3)), c, hd, qs),
            c
          )
            == Some{_}: Maybe<&2, Head>
        }
        Head.at_set(
          ~mach,
          Wait.set(
            ~mach,
            State.led(~mach, s, State.ledger(~mach, s3)),
            c,
            Wait.left(
              Wait.of(~mach, State.led(~mach, s, State.ledger(~mach, s3)), c),
              Tries.Trie.put_keys(~Ledgers.Id, ~Ledgers.Id.key, qs, Tries.Trie.new(Unit))
            )
          ),
          c,
          hd
        )

# Advance.ran.moves once whether the run gives the tip that the step names is
# known (bq)
def Advance.ran.moves.if(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  s2: Node<Machine.Q(mach)>,
  +t2: Tip,
  c: Ledgers.Chain,
  r: Ledgers.Id,
  br: Maybe<&2, String>,
  next: U32,
  after: Maybe<&2, Hashes.Hash>,
  qs: List<&2, Ledgers.Id>,
  h: Head,
  -x: Head,
  bq: Bool,
  ebq: {Root.same(after, Some{Tip.hash(t2)}) == bq: Bool},
  em: {Node.head_of(~mach, s, c) == Some{h}: Maybe<&2, Head>},
  ex: {
    Root.same(after, Some{Tip.hash(t2)}) == True{}: Bool
  } -> {Head{r, br, U32.inc(next), Some{Tip.hash(t2)}} == x: Head}
) -> Moves(
  ~mach,
  Shared.Bool.when(
    Node<Machine.Q(mach)>,
    bq,
    u => Advance.moved(
      ~mach,
      s,
      State.put(~mach, s2, [Tip.words(t2)]),
      c,
      Head{r, br, U32.inc(next), Some{Tip.hash(t2)}},
      qs
    ),
    u => s
  ),
  c,
  h,
  x
):
  match bq:
    case True{}:
      Advance.moved.moves(
        ~mach,
        s,
        State.put(~mach, s2, [Tip.words(t2)]),
        c,
        Head{r, br, U32.inc(next), Some{Tip.hash(t2)}},
        qs,
        h,
        x,
        em,
        ex(ebq)
      )
    case False{}:
      Moves.stay(~mach, s, c, h, x, em)

# a checked step moves the head to the tip that the step names, or not at all
def Advance.ran.moves(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  r: Ledgers.Id,
  br: Maybe<&2, String>,
  next: U32,
  +after: Maybe<&2, Hashes.Hash>,
  qs: List<&2, Ledgers.Id>,
  m: Maybe<&2, Run<Machine.Q(mach)>>,
  h: Head,
  -x: Head,
  em: {Node.head_of(~mach, s, c) == Some{h}: Maybe<&2, Head>},
  ex: @t2: Tip -> {
    Root.same(after, Some{Tip.hash(t2)}) == True{}: Bool
  } -> {Head{r, br, U32.inc(next), Some{Tip.hash(t2)}} == x: Head}
) -> Moves(~mach, Advance.ran(~mach, s, c, r, br, next, after, qs, m), c, h, x):
  match m:
    case None{}:
      Moves.stay(~mach, s, c, h, x, em)
    case Some{Run{s2, +t2}}:
      Advance.ran.moves.if(
        ~mach,
        s,
        s2,
        t2,
        c,
        r,
        br,
        next,
        after,
        qs,
        h,
        x,
        Root.same(after, Some{Tip.hash(t2)}),
        {==},
        em,
        ex(t2)
      )

# Node.advance moves the head by the decided step m, or not at all
def Advance.step.moves(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  h: Head,
  t: Tip,
  m: Maybe<&2, Ledgers.Vote>
) -> {
  Node.head_of(~mach, s, c) == Some{h}: Maybe<&2, Head>
} -> Moves(~mach, Advance.step(~mach, ~kern, s, c, h, t, m), c, h, Head.step(h, m)):
  match h m:
    case Head{+r, +br, +next, +th} Some{Ledgers.Vote{before, +qs, +after}}:
      +em => Moves.when(
        ~mach,
        Root.same(before, th),
        Advance.ran(~mach, s, c, r, br, next, after, qs, Step.run(~mach, ~kern, s, c, t, qs)),
        s,
        c,
        Head{r, br, next, th},
        Head.step(Head{r, br, next, th}, Some{Ledgers.Vote{before, qs, after}}),
        Advance.ran.moves(~mach,
          s,
          c,
          r,
          br,
          next,
          after,
          qs,
          Step.run(~mach, ~kern, s, c, t, qs),
          Head{r, br, next, th},
          Head.step(Head{r, br, next, th}, Some{Ledgers.Vote{before, qs, after}}),
          em,
          t2 => er =>
            %Equal.sym(Maybe<&2, Hashes.Hash>, after, Some{Tip.hash(t2)}, Shared.Maybe.is_eq_sound(~Hashes.Hash, ~Hashes.Hash.is_eq, x => y => Hashes.Hash.is_eq_sound(x, y), after, Some{Tip.hash(t2)})(er)): {Head{r, br, U32.inc(next), Some{Tip.hash(t2)}} == Head.step(Head{r, br, next, th}, Some{Ledgers.Vote{before, qs, _}}): Head}
            {==}),
        Moves.stay(
          ~mach,
          s,
          c,
          Head{r, br, next, th},
          Head.step(Head{r, br, next, th}, Some{Ledgers.Vote{before, qs, after}}),
          em
        )
      )
    case Head{+r, +br, +next, +th} None{}:
      em => Moves.stay(~mach, s, c, Head{r, br, next, th}, Head{r, br, next, th}, em)

# Node.advance moves the head by the step decided at the head h, whose tip is
# m, or not at all
def Advance.at.moves(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  +h: Head,
  m: Maybe<&2, Tip>
) -> {
  Node.head_of(~mach, s, c) == Some{h}: Maybe<&2, Head>
} -> {
  Head.tip(~mach, s, h) == m: Maybe<&2, Tip>
} -> Moves(
  ~mach,
  Advance.at(~mach, ~kern, s, c, h, m),
  c,
  h,
  Head.step(h, Advance.vote(~mach, s, c, h))
):
  match m:
    case None{}:
      em => et => Moves.stay(~mach, s, c, h, Head.step(h, Advance.vote(~mach, s, c, h)), em)
    case Some{+t}:
      em => et =>
        %Equal.sym(
          Maybe<&2, Ledgers.Vote>,
          Advance.vote(~mach, s, c, h),
          Height.decide(
            ~mach,
            s,
            c,
            Head.next(h),
            Tip.owners(t),
            Round.seen(~mach, s, c, Head.next(h))
          ),
          Equal.cong(
            Maybe<&2, Tip>,
            Maybe<&2, Ledgers.Vote>,
            mt => Maybe.bind(
              &2,
              Tip,
              Ledgers.Vote,
              mt,
              t1 => Height.decide(
                ~mach,
                s,
                c,
                Head.next(h),
                Tip.owners(t1),
                Round.seen(~mach, s, c, Head.next(h))
              )
            ),
            Head.tip(~mach, s, h),
            Some{t},
            et
          )
        ): Moves(
          ~mach,
          Advance.step(
            ~mach,
            ~kern,
            s,
            c,
            h,
            t,
            Height.decide(
              ~mach,
              s,
              c,
              Head.next(h),
              Tip.owners(t),
              Round.seen(~mach, s, c, Head.next(h))
            )
          ),
          c,
          h,
          Head.step(h, _)
        )
        Advance.step.moves(
          ~mach,
          ~kern,
          s,
          c,
          h,
          t,
          Height.decide(
            ~mach,
            s,
            c,
            Head.next(h),
            Tip.owners(t),
            Round.seen(~mach, s, c, Head.next(h))
          )
        )(em)

# a head moves only to the tip that the owners in its tip decided next
def Advance.decided(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  +h: Head
) -> {
  Node.head_of(~mach, s, c) == Some{h}: Maybe<&2, Head>
} -> {
  Heads.level(Some{h}, Node.head_of(~mach, Node.advance(~mach, ~kern, s, c), c)) == False{}: Bool
} -> {
  Node.head_of(
    ~mach,
    Node.advance(~mach, ~kern, s, c),
    c
  )
    == Some{Head.step(h, Advance.vote(~mach, s, c, h))}: Maybe<&2, Head>
}:
  +em =>
    %Equal.sym(
      Maybe<&2, Head>,
      Node.head_of(~mach, s, c),
      Some{h},
      em
    ): Moves(
      ~mach,
      Advance.head(~mach, ~kern, s, c, _),
      c,
      h,
      Head.step(h, Advance.vote(~mach, s, c, h))
    )
    Advance.at.moves(~mach, ~kern, s, c, h, Head.tip(~mach, s, h))(em)({==})

# Found.elim once the tip m of the head is known
def Found.elim.at(
  ~mach: Machine(),
  -R: Type,
  s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  h: Head,
  k: Nat,
  -v: Ledgers.Vote,
  m: Maybe<&2, Tip>
) -> {
  Head.tip(~mach, s, h) == m: Maybe<&2, Tip>
} -> {
  Maybe.bind(
    &2,
    Tip,
    Ledgers.Vote,
    m,
    t => Height.decide(~mach, s, c, Head.next(h), Tip.owners(t), k)
  )
    == Some{v}: Maybe<&2, Ledgers.Vote>
} -> (
  @t: Tip -> @q: Nat -> {
    Head.tip(~mach, s, h) == Some{t}: Maybe<&2, Tip>
  } -> {
    Ledgers.State.decide(
      ~Machine.Q(mach),
      State.ledger(~mach, s),
      Ledgers.Where{c, Head.next(h), q},
      Tip.owners(t)
    )
      == Some{v}: Maybe<&2, Ledgers.Vote>
  } -> R
) -> R:
  match m:
    case None{}:
      em => e => f => Empty.absurd(R, Shared.Maybe.none_ne_some(Ledgers.Vote, v, e))
    case Some{+t}:
      em => e => f => Scan.elim(
        ~mach,
        R,
        s,
        c,
        Head.next(h),
        Tip.owners(t),
        k,
        v
      )(e)(q => d => f(t)(q)(em)(d))

# a step that a node found at a head is decided at the head's tip, in some
# round
def Found.elim(
  ~mach: Machine(),
  -R: Type,
  +s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  +h: Head,
  k: Nat,
  -v: Ledgers.Vote
) -> {
  Advance.found(~mach, s, c, h, k) == Some{v}: Maybe<&2, Ledgers.Vote>
} -> (
  @t: Tip -> @q: Nat -> {
    Head.tip(~mach, s, h) == Some{t}: Maybe<&2, Tip>
  } -> {
    Ledgers.State.decide(
      ~Machine.Q(mach),
      State.ledger(~mach, s),
      Ledgers.Where{c, Head.next(h), q},
      Tip.owners(t)
    )
      == Some{v}: Maybe<&2, Ledgers.Vote>
  } -> R
) -> R:
  Found.elim.at(~mach, R, s, c, h, k, v, Head.tip(~mach, s, h))({==})

# the verdict m takes
def Verdict.took(~mach: Machine(), m: Maybe<&2, Verdict<Machine.Q(mach)>>) -> Bool:
  match m:
    case Some{Verdict.Taken{Work{s2, h}}}:
      True{}
    case x:
      False{}

# the tree of the verdict m
def Took.root(~mach: Machine(), m: Maybe<&2, Verdict<Machine.Q(mach)>>) -> Maybe<&2, Hashes.Hash>:
  match m:
    case Some{Verdict.Taken{Work{s2, h}}}:
      h
    case x:
      None{}

# the node of the verdict m, or d when it takes nothing
def Took.node(
  ~mach: Machine(),
  m: Maybe<&2, Verdict<Machine.Q(mach)>>,
  d: Node<Machine.Q(mach)>
) -> Node<Machine.Q(mach)>:
  match m:
    case Some{Verdict.Taken{Work{s2, h}}}:
      s2
    case x:
      d

# Set.reads once the node m2 that the put of the new subtree gives is known
def Set.reads.put(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  +h: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  +x: List<&2, U32>,
  +hh: Hashes.Hash,
  ws: List<&2, List<&2, U32>>,
  m2: Maybe<&2, Node<Machine.Q(mach)>>,
  -h2: Maybe<&2, Hashes.Hash>,
  s3: Node<Machine.Q(mach)>,
  hp: @y: Node<
    Machine.Q(
      mach
    )> -> {
    m2 == Some{y}: Maybe<&2, Node<Machine.Q(mach)>>
  } -> {Stores.Store.holds(~Node<Machine.Q(mach)>, ~Store.fetch(~mach), y, ws) == True{}: Bool}
) -> {
  Node.set(~mach, s, h, k, x) == Some{Trees.Put{hh, ws}}: Maybe<&2, Trees.Put>
} -> {
  Work.take(
    ~mach,
    Work.on(~mach, m2, Some{hh})
  )
    == Some{Verdict.Taken{Work{s3, h2}}}: Maybe<&2, Verdict<Machine.Q(mach)>>
} -> {Node.get(~mach, s3, h2, k) == Some{x}: Maybe<&2, List<&2, U32>>}:
  match m2:
    case None{}:
      es => e => Empty.absurd(
        {Node.get(~mach, s3, h2, k) == Some{x}: Maybe<&2, List<&2, U32>>},
        Shared.Maybe.none_ne_some(Verdict<Machine.Q(mach)>, Verdict.Taken{Work{s3, h2}}, e)
      )
    case Some{+sk}:
      es => +e =>
        %Equal.cong(
          Maybe<&2, Verdict<Machine.Q(mach)>>,
          Node<Machine.Q(mach)>,
          v => Took.node(~mach, v, s3),
          Some{Verdict.Taken{Work{sk, Some{hh}}}},
          Some{Verdict.Taken{Work{s3, h2}}},
          e
        ): {Node.get(~mach, _, h2, k) == Some{x}: Maybe<&2, List<&2, U32>>}
        %Equal.cong(
          Maybe<&2, Verdict<Machine.Q(mach)>>,
          Maybe<&2, Hashes.Hash>,
          v => Took.root(~mach, v),
          Some{Verdict.Taken{Work{sk, Some{hh}}}},
          Some{Verdict.Taken{Work{s3, h2}}},
          e
        ): {Node.get(~mach, sk, _, k) == Some{x}: Maybe<&2, List<&2, U32>>}
        Equal.trans(
          Maybe<&2, List<&2, U32>>,
          Node.get(~mach, sk, Some{hh}, k),
          Trees.Tree.get.plain(~Node<Machine.Q(mach)>, ~Store.fetch(~mach), sk, Some{hh}, k),
          Some{x},
          Trees.Tree.get_plain(~Node<Machine.Q(mach)>, ~Store.fetch(~mach), sk, Some{hh}, k),
          Trees.Tree.get_set(
            ~Node<Machine.Q(mach)>,
            ~Store.fetch(~mach),
            s,
            sk,
            h,
            k,
            x,
            Trees.Put{hh, ws}
          )(
            Equal.trans(
              Maybe<&2, Trees.Put>,
              Trees.Tree.set.plain(~Node<Machine.Q(mach)>, ~Store.fetch(~mach), s, h, k, x),
              Node.set(~mach, s, h, k, x),
              Some{Trees.Put{hh, ws}},
              Equal.sym(
                Maybe<&2, Trees.Put>,
                Node.set(~mach, s, h, k, x),
                Trees.Tree.set.plain(~Node<Machine.Q(mach)>, ~Store.fetch(~mach), s, h, k, x),
                Trees.Tree.set_plain(~Node<Machine.Q(mach)>, ~Store.fetch(~mach), s, h, k, x)
              ),
              es
            )
          )(hp(sk)({==}))
        )

# a key set in a tree, when the verdict takes the new tree, reads back in a
# node that holds the new nodes
def Set.reads(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  h: Maybe<&2, Hashes.Hash>,
  k: List<&2, U32>,
  x: List<&2, U32>,
  m: Maybe<&2, Trees.Put>,
  -h2: Maybe<&2, Hashes.Hash>,
  s3: Node<Machine.Q(mach)>
) -> {
  Node.set(~mach, s, h, k, x) == m: Maybe<&2, Trees.Put>
} -> {
  Work.take(
    ~mach,
    Work.of(~mach, s, m)
  )
    == Some{Verdict.Taken{Work{s3, h2}}}: Maybe<&2, Verdict<Machine.Q(mach)>>
} -> {Node.get(~mach, s3, h2, k) == Some{x}: Maybe<&2, List<&2, U32>>}:
  match m:
    case None{}:
      es => e => Empty.absurd(
        {Node.get(~mach, s3, h2, k) == Some{x}: Maybe<&2, List<&2, U32>>},
        Shared.Maybe.none_ne_some(Verdict<Machine.Q(mach)>, Verdict.Taken{Work{s3, h2}}, e)
      )
    case Some{Trees.Put{hh, +ws}}:
      Set.reads.put(
        ~mach,
        s,
        h,
        k,
        x,
        hh,
        ws,
        State.put(~mach, s, ws),
        h2,
        s3,
        y => ey => Put.holds(~mach, s, ws, y)(ey)
      )

# a verdict that takes, after a read, is the verdict of what comes next
def With.took(
  ~mach: Machine(),
  -A: Data,
  ma: Maybe<&2, A>,
  -k: A -> Maybe<&2, Verdict<Machine.Q(mach)>>,
  -kk: Maybe<&2, Verdict<Machine.Q(mach)>>,
  -h2: Maybe<&2, Hashes.Hash>,
  -s3: Node<Machine.Q(mach)>
) -> (
  @a: A -> {
    k(a) == Some{Verdict.Taken{Work{s3, h2}}}: Maybe<&2, Verdict<Machine.Q(mach)>>
  } -> {kk == Some{Verdict.Taken{Work{s3, h2}}}: Maybe<&2, Verdict<Machine.Q(mach)>>}
) -> {
  Maybe.bind(
    &2,
    A,
    Verdict<Machine.Q(mach)>,
    ma,
    k
  )
    == Some{Verdict.Taken{Work{s3, h2}}}: Maybe<&2, Verdict<Machine.Q(mach)>>
} -> {kk == Some{Verdict.Taken{Work{s3, h2}}}: Maybe<&2, Verdict<Machine.Q(mach)>>}:
  match ma:
    case None{}:
      hk => e => Empty.absurd(
        {kk == Some{Verdict.Taken{Work{s3, h2}}}: Maybe<&2, Verdict<Machine.Q(mach)>>},
        Shared.Maybe.none_ne_some(Verdict<Machine.Q(mach)>, Verdict.Taken{Work{s3, h2}}, e)
      )
    case Some{a}:
      hk => e => hk(a)(e)

# Seal.accept_fits once whether the ballot fits is known (f)
def Accept.fits.if(
  ~mach: Machine(),
  f: Bool,
  -x: Node<Machine.Q(mach)>,
  -s2: Node<Machine.Q(mach)>
) -> {
  Shared.Maybe.when(
    Node<Machine.Q(mach)>,
    f,
    u => Some{x}
  )
    == Some{s2}: Maybe<&2, Node<Machine.Q(mach)>>
} -> {f == True{}: Bool}:
  match f:
    case True{}:
      e => {==}
    case False{}:
      e => Empty.absurd(
        {False{} == True{}: Bool},
        Shared.Maybe.none_ne_some(Node<Machine.Q(mach)>, s2, e)
      )

# a place is the same as itself
def Prev.refl(m: Maybe<&2, Ledgers.Where>) -> {Prev.same(m, m) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{w}:
      Shared.List.is_eq_refl(~U32, ~U32.is_eq, ~Shared.U32.laws(), Ledgers.Where.code(w, []))

# a head that no step moves is at its own height
def Level.none(x: Head) -> {Heads.level(Some{x}, Some{Head.step(x, None{})}) == True{}: Bool}:
  match x:
    case Head{r, b, n, t}:
      Shared.Eq.refl(~U32, ~U32.is_eq, Shared.U32.laws(), n)

# that the rounds of each height of the line c decide one step in s
def Line.One(~mach: Machine(), s: Node<Machine.Q(mach)>, c: Ledgers.Chain) -> Type:
  @x: Head -> @t: Tip -> {
    Head.tip(~mach, s, x) == Some{t}: Maybe<&2, Tip>
  } -> Height.One(~mach, s, c, Head.next(x), Tip.owners(t))

# that the rounds of each of k heights of the line c decide one step in s (one
# witness for each step of a history: a proof uses each once)
def Line.Ones(~mach: Machine(), k: Nat, s: Node<Machine.Q(mach)>, c: Ledgers.Chain) -> Type:
  match k:
    case 0n:
      Unit
    case 1n+p:
      Line.Ones(~mach, p, s, c) & Line.One(~mach, s, c)

# In.grows once the tip m of the head in a is known
def In.grows.at(
  ~mach: Machine(),
  +a: Node<Machine.Q(mach)>,
  +u: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  +x: Head,
  r: Nat,
  v: Ledgers.Vote,
  m: Maybe<&2, Tip>,
  +g: {Node.grows(~mach, a, u) == True{}: Bool}
) -> {
  Head.tip(~mach, a, x) == m: Maybe<&2, Tip>
} -> {
  Maybe.bind(
    &2,
    Tip,
    Ledgers.Vote,
    m,
    t => Ledgers.State.decide(
      ~Machine.Q(mach),
      State.ledger(~mach, a),
      Ledgers.Where{c, Head.next(x), r},
      Tip.owners(t)
    )
  )
    == Some{v}: Maybe<&2, Ledgers.Vote>
} -> {Advance.in(~mach, u, c, x, r) == Some{v}: Maybe<&2, Ledgers.Vote>}:
  match m:
    case None{}:
      em => e => Empty.absurd(
        {Advance.in(~mach, u, c, x, r) == Some{v}: Maybe<&2, Ledgers.Vote>},
        Shared.Maybe.none_ne_some(Ledgers.Vote, v, e)
      )
    case Some{t}:
      em => e =>
        %Equal.sym(
          Maybe<&2, Tip>,
          Head.tip(~mach, u, x),
          Some{t},
          Head.tip.grows(~mach, a, u, x, t, g)(em)
        ): {
          Maybe.bind(
            &2,
            Tip,
            Ledgers.Vote,
            _,
            t1 => Ledgers.State.decide(
              ~Machine.Q(mach),
              State.ledger(~mach, u),
              Ledgers.Where{c, Head.next(x), r},
              Tip.owners(t1)
            )
          )
            == Some{v}: Maybe<&2, Ledgers.Vote>
        }
        Decide.up(~mach, a, u, t, Ledgers.Where{c, Head.next(x), r}, v, g)(e)

# a step that the owners decided at a head in a round, in a, they decided in
# a node that grew
def In.grows(
  ~mach: Machine(),
  +a: Node<Machine.Q(mach)>,
  u: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  +x: Head,
  r: Nat,
  v: Ledgers.Vote,
  g: {Node.grows(~mach, a, u) == True{}: Bool}
) -> {
  Advance.in(~mach, a, c, x, r) == Some{v}: Maybe<&2, Ledgers.Vote>
} -> {Advance.in(~mach, u, c, x, r) == Some{v}: Maybe<&2, Ledgers.Vote>}:
  In.grows.at(~mach, a, u, c, x, r, v, Head.tip(~mach, a, x), g)({==})

# Moved.grows once the step va that a holds at the head is known
def Moved.grows.at(
  ~mach: Machine(),
  a: Node<Machine.Q(mach)>,
  u: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  x: Head,
  -y: Head,
  r: Nat,
  va: Maybe<&2, Ledgers.Vote>,
  g: {Node.grows(~mach, a, u) == True{}: Bool}
) -> {
  Advance.in(~mach, a, c, x, r) == va: Maybe<&2, Ledgers.Vote>
} -> {
  Head.moved(x, va) == Some{y}: Maybe<&2, Head>
} -> {Head.moved(x, Advance.in(~mach, u, c, x, r)) == Some{y}: Maybe<&2, Head>}:
  match va:
    case None{}:
      ea => e => Empty.absurd(
        {Head.moved(x, Advance.in(~mach, u, c, x, r)) == Some{y}: Maybe<&2, Head>},
        Shared.Maybe.none_ne_some(Head, y, e)
      )
    case Some{v}:
      ea => e =>
        %Equal.sym(
          Maybe<&2, Ledgers.Vote>,
          Advance.in(~mach, u, c, x, r),
          Some{v},
          In.grows(~mach, a, u, c, x, r, v, g)(ea)
        ): {Head.moved(x, _) == Some{y}: Maybe<&2, Head>}
        e

# a head that a decided step moves in a, it moves the same in a node that grew
def Moved.grows(
  ~mach: Machine(),
  +a: Node<Machine.Q(mach)>,
  u: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  +x: Head,
  -y: Head,
  +r: Nat,
  g: {Node.grows(~mach, a, u) == True{}: Bool}
) -> {
  Head.moved(x, Advance.in(~mach, a, c, x, r)) == Some{y}: Maybe<&2, Head>
} -> {Head.moved(x, Advance.in(~mach, u, c, x, r)) == Some{y}: Maybe<&2, Head>}:
  Moved.grows.at(~mach, a, u, c, x, y, r, Advance.in(~mach, a, c, x, r), g)({==})

# Step.same once what the two rounds decide is known (w1, w2)
def Step.same.at(
  ~mach: Machine(),
  u: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  z: Head,
  r1: Nat,
  r2: Nat,
  t: Tip,
  -x: Head,
  -y: Head,
  w1: Maybe<&2, Ledgers.Vote>,
  w2: Maybe<&2, Ledgers.Vote>,
  one: Height.One(~mach, u, c, Head.next(z), Tip.owners(t))
) -> {
  Ledgers.State.decide(
    ~Machine.Q(mach),
    State.ledger(~mach, u),
    Ledgers.Where{c, Head.next(z), r1},
    Tip.owners(t)
  )
    == w1: Maybe<&2, Ledgers.Vote>
} -> {
  Ledgers.State.decide(
    ~Machine.Q(mach),
    State.ledger(~mach, u),
    Ledgers.Where{c, Head.next(z), r2},
    Tip.owners(t)
  )
    == w2: Maybe<&2, Ledgers.Vote>
} -> {
  Head.moved(z, w1) == Some{x}: Maybe<&2, Head>
} -> {Head.moved(z, w2) == Some{y}: Maybe<&2, Head>} -> {x == y: Head}:
  match w1 w2:
    case None{} b:
      e1 => e2 => k1 => k2 => Empty.absurd({x == y: Head}, Shared.Maybe.none_ne_some(Head, x, k1))
    case Some{v1} None{}:
      e1 => e2 => k1 => k2 => Empty.absurd({x == y: Head}, Shared.Maybe.none_ne_some(Head, y, k2))
    case Some{+v1} Some{v2}:
      e1 => e2 => k1 => k2 => Shared.Maybe.some_inj(
        Head,
        x,
        y,
        Equal.trans(
          Maybe<&2, Head>,
          Some{x},
          Head.moved(z, Some{v1}),
          Some{y},
          Equal.sym(Maybe<&2, Head>, Head.moved(z, Some{v1}), Some{x}, k1),
          Equal.trans(
            Maybe<&2, Head>,
            Head.moved(z, Some{v1}),
            Head.moved(z, Some{v2}),
            Some{y},
            Equal.cong(
              Ledgers.Vote,
              Maybe<&2, Head>,
              v => Head.moved(z, Some{v}),
              v1,
              v2,
              one(r1)(r2)(v1)(v2)(e1)(e2)
            ),
            k2
          )
        )
      )

# the steps of two rounds at one head move it the same, once the tip m of
# the head is known
def Step.same(
  ~mach: Machine(),
  +u: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  +z: Head,
  +r1: Nat,
  +r2: Nat,
  -x: Head,
  -y: Head,
  m: Maybe<&2, Tip>,
  one: Line.One(~mach, u, c)
) -> {
  Head.tip(~mach, u, z) == m: Maybe<&2, Tip>
} -> {
  Head.moved(
    z,
    Maybe.bind(
      &2,
      Tip,
      Ledgers.Vote,
      m,
      t => Ledgers.State.decide(
        ~Machine.Q(mach),
        State.ledger(~mach, u),
        Ledgers.Where{c, Head.next(z), r1},
        Tip.owners(t)
      )
    )
  )
    == Some{x}: Maybe<&2, Head>
} -> {
  Head.moved(
    z,
    Maybe.bind(
      &2,
      Tip,
      Ledgers.Vote,
      m,
      t => Ledgers.State.decide(
        ~Machine.Q(mach),
        State.ledger(~mach, u),
        Ledgers.Where{c, Head.next(z), r2},
        Tip.owners(t)
      )
    )
  )
    == Some{y}: Maybe<&2, Head>
} -> {x == y: Head}:
  match m:
    case None{}:
      em => k1 => k2 => Empty.absurd({x == y: Head}, Shared.Maybe.none_ne_some(Head, x, k1))
    case Some{+t}:
      em => k1 => k2 =>
        Step.same.at(
          ~mach,
          u,
          c,
          z,
          r1,
          r2,
          t,
          x,
          y,
          Ledgers.State.decide(
            ~Machine.Q(mach),
            State.ledger(~mach, u),
            Ledgers.Where{c, Head.next(z), r1},
            Tip.owners(t)
          ),
          Ledgers.State.decide(
            ~Machine.Q(mach),
            State.ledger(~mach, u),
            Ledgers.Where{c, Head.next(z), r2},
            Tip.owners(t)
          ),
          one(z)(t)(em)
        )({==})({==})(k1)(k2)

# At.same for one more step of each history, once the heads before are known
def At.same.step(
  ~mach: Machine(),
  +u: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  r1: Nat,
  r2: Nat,
  -x: Head,
  -y: Head,
  m1: Maybe<&2, Head>,
  m2: Maybe<&2, Head>,
  one: Line.One(~mach, u, c),
  ih: @z1: Head -> @z2: Head -> {
    m1 == Some{z1}: Maybe<&2, Head>
  } -> {m2 == Some{z2}: Maybe<&2, Head>} -> {z1 == z2: Head}
) -> {
  Maybe.bind(
    &2,
    Head,
    Head,
    m1,
    +z => Head.moved(z, Advance.in(~mach, u, c, z, r1))
  )
    == Some{x}: Maybe<&2, Head>
} -> {
  Maybe.bind(
    &2,
    Head,
    Head,
    m2,
    +z => Head.moved(z, Advance.in(~mach, u, c, z, r2))
  )
    == Some{y}: Maybe<&2, Head>
} -> {x == y: Head}:
  match m1 m2:
    case None{} b:
      k1 => k2 => Empty.absurd({x == y: Head}, Shared.Maybe.none_ne_some(Head, x, k1))
    case Some{z1} None{}:
      k1 => k2 => Empty.absurd({x == y: Head}, Shared.Maybe.none_ne_some(Head, y, k2))
    case Some{+z1} Some{z2}:
      k1 => k2 =>
        Step.same(
          ~mach,
          u,
          c,
          z1,
          r1,
          r2,
          x,
          y,
          Head.tip(~mach, u, z1),
          one
        )(
          {==}
        )(
          k1
        )(
          Equal.trans(
            Maybe<&2, Head>,
            Head.moved(z1, Advance.in(~mach, u, c, z1, r2)),
            Head.moved(z2, Advance.in(~mach, u, c, z2, r2)),
            Some{y},
            Equal.cong(
              Head,
              Maybe<&2, Head>,
              +z => Head.moved(z, Advance.in(~mach, u, c, z, r2)),
              z1,
              z2,
              ih(z1)(z2)({==})({==})
            ),
            k2
          )
        )

# At.same for one more step of each history, with the witness of each step
def At.same.con(
  ~mach: Machine(),
  +u: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  +h: Head,
  r1: Nat,
  r2: Nat,
  t1: List<&2, Nat>,
  t2: List<&2, Nat>,
  -x: Head,
  -y: Head,
  ones: Line.Ones(~mach, List.length(&2, Nat, t1), u, c) & Line.One(~mach, u, c),
  ih: @z1: Head -> @z2: Head -> Line.Ones(
    ~mach,
    List.length(&2, Nat, t1),
    u,
    c
  ) -> {
    Line.at(~mach, t1, u, c, h) == Some{z1}: Maybe<&2, Head>
  } -> {Line.at(~mach, t2, u, c, h) == Some{z2}: Maybe<&2, Head>} -> {z1 == z2: Head}
) -> {
  Line.at(~mach, r1 <> t1, u, c, h) == Some{x}: Maybe<&2, Head>
} -> {Line.at(~mach, r2 <> t2, u, c, h) == Some{y}: Maybe<&2, Head>} -> {x == y: Head}:
  match ones:
    case Tuple{rest, one}:
      At.same.step(
        ~mach,
        u,
        c,
        r1,
        r2,
        x,
        y,
        Line.at(~mach, t1, u, c, h),
        Line.at(~mach, t2, u, c, h),
        one,
        z1 => z2 => ih(z1)(z2)(rest)
      )

# in one node, the same number of decided steps from one head give one head,
# whatever the round of each step
def At.same(
  ~mach: Machine(),
  rs1: List<&2, Nat>,
  rs2: List<&2, Nat>,
  +u: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  +h: Head,
  x: Head,
  y: Head
) -> Line.Ones(~mach, List.length(&2, Nat, rs1), u, c)
  -> {List.length(&2, Nat, rs1) == List.length(&2, Nat, rs2): Nat}
  -> {Line.at(~mach, rs1, u, c, h) == Some{x}: Maybe<&2, Head>}
  -> {Line.at(~mach, rs2, u, c, h) == Some{y}: Maybe<&2, Head>}
  -> {x == y: Head}:
  match rs1 rs2:
    case Nil{} Nil{}:
      ones => el => e1 => e2 => Shared.Maybe.some_inj(
        Head,
        x,
        y,
        Equal.trans(
          Maybe<&2, Head>,
          Some{x},
          Some{h},
          Some{y},
          Equal.sym(Maybe<&2, Head>, Some{h}, Some{x}, e1),
          e2
        )
      )
    case Nil{} Con{r2, t2}:
      ones => el => e1 => e2 => Empty.absurd(
        {x == y: Head},
        Shared.Nat.zero_ne_succ(List.length(&2, Nat, t2), el)
      )
    case Con{r1, t1} Nil{}:
      ones => el => e1 => e2 => Empty.absurd(
        {x == y: Head},
        Shared.Nat.zero_ne_succ(
          List.length(&2, Nat, t1),
          Equal.sym(Nat, 1n+List.length(&2, Nat, t1), 0n, el)
        )
      )
    case Con{+r1, +t1} Con{r2, +t2}:
      ones => el =>
        At.same.con(
          ~mach,
          u,
          c,
          h,
          r1,
          r2,
          t1,
          t2,
          x,
          y,
          ones,
          z1 => z2 => rest => At.same(
            ~mach,
            t1,
            t2,
            u,
            c,
            h,
            z1,
            z2
          )(rest)(Shared.Nat.succ_inj(List.length(&2, Nat, t1), List.length(&2, Nat, t2), el))
        )

# a step that changes the height of a head moves it one height up
def Moved.step(
  h: Head,
  v: Ledgers.Vote
) -> {
  Heads.level(Some{h}, Some{Head.step(h, Some{v})}) == False{}: Bool
} -> {Head.moved(h, Some{v}) == Some{Head.step(h, Some{v})}: Maybe<&2, Head>}:
  match h v:
    case Head{r, b, n, th} Ledgers.Vote{before, qs, Some{y}}:
      e => {==}
    case Head{r, b, n, th} Ledgers.Vote{before, qs, None{}}:
      e => Empty.absurd(
        {None{} == Some{Head{r, b, n, th}}: Maybe<&2, Head>},
        Shared.Bool.false_ne_true(
          Equal.trans(
            Bool,
            False{},
            Heads.level(Some{Head{r, b, n, th}}, Some{Head{r, b, n, th}}),
            True{},
            Equal.sym(
              Bool,
              Heads.level(Some{Head{r, b, n, th}}, Some{Head{r, b, n, th}}),
              False{},
              e
            ),
            Level.refl(Head{r, b, n, th})
          )
        )
      )

# Node.advance_at once the step m that the node found at the head is known
def Advance.at.one(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  +h: Head,
  m: Maybe<&2, Ledgers.Vote>
) -> {
  Advance.vote(~mach, s, c, h) == m: Maybe<&2, Ledgers.Vote>
} -> {
  Heads.level(Some{h}, Some{Head.step(h, m)}) == False{}: Bool
} -> Exists(Nat, q => {Line.at(~mach, [q], s, c, h) == Some{Head.step(h, m)}: Maybe<&2, Head>}):
  match m:
    case None{}:
      em => hl => Empty.absurd(
        Exists(
          Nat,
          q => {Line.at(~mach, [q], s, c, h) == Some{Head.step(h, None{})}: Maybe<&2, Head>}
        ),
        Shared.Bool.false_ne_true(
          Equal.trans(
            Bool,
            False{},
            Heads.level(Some{h}, Some{Head.step(h, None{})}),
            True{},
            Equal.sym(Bool, Heads.level(Some{h}, Some{Head.step(h, None{})}), False{}, hl),
            Level.none(h)
          )
        )
      )
    case Some{v}:
      em => hl =>
        Found.elim(
          ~mach,
          Exists(
            Nat,
            q => {Line.at(~mach, [q], s, c, h) == Some{Head.step(h, Some{v})}: Maybe<&2, Head>}
          ),
          s,
          c,
          h,
          Round.seen(~mach, s, c, Head.next(h)),
          v
        )(em)(t => q => et => d => Tuple{q, (
              %Equal.sym(Maybe<&2, Tip>, Head.tip(~mach, s, h), Some{t}, et): {Head.moved(h, Maybe.bind(&2, Tip, Ledgers.Vote, _, t1 => Ledgers.State.decide(~Machine.Q(mach), State.ledger(~mach, s), Ledgers.Where{c, Head.next(h), q}, Tip.owners(t1)))) == Some{Head.step(h, Some{v})}: Maybe<&2, Head>}
              %Equal.sym(Maybe<&2, Ledgers.Vote>, Ledgers.State.decide(~Machine.Q(mach), State.ledger(~mach, s), Ledgers.Where{c, Head.next(h), q}, Tip.owners(t)), Some{v}, d): {Head.moved(h, _) == Some{Head.step(h, Some{v})}: Maybe<&2, Head>}
              Moved.step(h, v)(hl))})

# the ballots of the owners os in the round r of the height h of the line c
def Round.ballots(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  h: U32,
  r: Nat,
  os: List<&2, String>
) -> List<&2, Maybe<&2, Cells.Cell<Ledgers.Vote>>>:
  Ledgers.Bucket.ballots(
    ~Machine.Q(mach),
    Ledgers.State.under(~Machine.Q(mach), State.ledger(~mach, s), Ledgers.Slot.bucket(c, h, r)),
    os
  )

# the node o cast for the step v in the round r, as a count of ballots reads it
def Round.hit(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  h: U32,
  r: Nat,
  o: String,
  v: Ledgers.Vote
) -> Bool:
  Quorums.Quorum.hit(
    ~Ledgers.Vote,
    ~Ledgers.Vote.is_eq,
    Ledgers.Entry.ballot(
      ~Machine.Q(mach),
      Ledgers.State.get(
        ~Machine.Q(mach),
        Ledgers.State.under(~Machine.Q(mach), State.ledger(~mach, s), Ledgers.Slot.bucket(c, h, r)),
        Ledgers.Slot.ballot(o)
      )
    ),
    v
  )

# a cell that counts for the step v holds a vote for v
def Hit.step(
  ~mach: Machine(),
  m: Maybe<&2, Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>>,
  v: Ledgers.Vote
) -> {
  Quorums.Quorum.hit(
    ~Ledgers.Vote,
    ~Ledgers.Vote.is_eq,
    Ledgers.Entry.ballot(~Machine.Q(mach), m),
    v
  )
    == True{}: Bool
} -> {Cast.step(~mach, m) == Some{v}: Maybe<&2, Ledgers.Vote>}:
  match m:
    case None{}:
      e => Empty.absurd({None{} == Some{v}: Maybe<&2, Ledgers.Vote>}, Shared.Bool.false_ne_true(e))
    case Some{Cells.Many{}}:
      e => Empty.absurd({None{} == Some{v}: Maybe<&2, Ledgers.Vote>}, Shared.Bool.false_ne_true(e))
    case Some{Cells.One{Ledgers.Entry.Ask{i, t, q}}}:
      e => Empty.absurd({None{} == Some{v}: Maybe<&2, Ledgers.Vote>}, Shared.Bool.false_ne_true(e))
    case Some{Cells.One{Ledgers.Entry.Data{ws}}}:
      e => Empty.absurd({None{} == Some{v}: Maybe<&2, Ledgers.Vote>}, Shared.Bool.false_ne_true(e))
    case Some{
      Cells.One{Ledgers.Entry.Vote{Ledgers.Ballot{Ledgers.Signed{w, n, Ledgers.Act.Pass{p}}, l}}}
    }:
      e => Empty.absurd({None{} == Some{v}: Maybe<&2, Ledgers.Vote>}, Shared.Bool.false_ne_true(e))
    case Some{
      Cells.One{
        Ledgers.Entry.Vote{Ledgers.Ballot{Ledgers.Signed{w, n, Ledgers.Act.Vote{x, from}}, l}}
      }
    }:
      e => Equal.cong(
        Ledgers.Vote,
        Maybe<&2, Ledgers.Vote>,
        y => Some{y},
        x,
        v,
        Ledgers.Vote.is_eq_sound(x, v)(e)
      )

# a node that counts for the step v in a round cast v there
def Hit.cast(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  +h: U32,
  +r: Nat,
  +o: String,
  v: Ledgers.Vote
) -> {
  Round.hit(~mach, s, c, h, r, o, v) == True{}: Bool
} -> {Cast.of(~mach, s, Ledgers.Where{c, h, r}, o) == Some{v}: Maybe<&2, Ledgers.Vote>}:
  e =>
    %Tries.Trie.get_under(
      Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>,
      State.ledger(~mach, s),
      Ledgers.Slot.bucket(c, h, r),
      Ledgers.Slot.ballot(o)
    ): {Cast.step(~mach, _) == Some{v}: Maybe<&2, Ledgers.Vote>}
    Hit.step(
      ~mach,
      Ledgers.State.get(
        ~Machine.Q(mach),
        Ledgers.State.under(~Machine.Q(mach), State.ledger(~mach, s), Ledgers.Slot.bucket(c, h, r)),
        Ledgers.Slot.ballot(o)
      ),
      v
    )(e)

# a vote moved to an equal round
def Cast.moved(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  h: U32,
  q: String,
  a: Nat,
  b: Nat,
  v: Ledgers.Vote,
  e: {a == b: Nat}
) -> {
  Cast.of(~mach, s, Ledgers.Where{c, h, a}, q) == Some{v}: Maybe<&2, Ledgers.Vote>
} -> {Cast.of(~mach, s, Ledgers.Where{c, h, b}, q) == Some{v}: Maybe<&2, Ledgers.Vote>}:
  k =>
    %e: {Cast.of(~mach, s, Ledgers.Where{c, h, _}, q) == Some{v}: Maybe<&2, Ledgers.Vote>}
    k

# o when it is a hit, else rest
def Voter.if(+hit: Bool, o: String, rest: Maybe<&2, String>) -> Maybe<&2, String>:
  match hit:
    case True{}:
      Some{o}
    case False{}:
      rest

# the first node of os that cast for the step v in the round r, if any did
def Round.voter(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  +h: U32,
  +r: Nat,
  +os: List<&2, String>,
  +v: Ledgers.Vote
) -> Maybe<&2, String>:
  match os:
    case Nil{}:
      None{}
    case Con{+o, rest}:
      Voter.if(Round.hit(~mach, s, c, h, r, o, v), o, Round.voter(~mach, s, c, h, r, rest, v))

# no hit and no voter in the rest, when there is no voter
def Voter.if_hit(
  +hit: Bool,
  o: String,
  rest: Maybe<&2, String>
) -> {Voter.if(hit, o, rest) == None{}: Maybe<&2, String>} -> {hit == False{}: Bool}:
  match hit:
    case True{}:
      e => Empty.absurd(
        {True{} == False{}: Bool},
        Shared.Maybe.none_ne_some(String, o, Equal.sym(Maybe<&2, String>, Some{o}, None{}, e))
      )
    case False{}:
      e => {==}

def Voter.if_rest(
  +hit: Bool,
  o: String,
  rest: Maybe<&2, String>
) -> {Voter.if(hit, o, rest) == None{}: Maybe<&2, String>} -> {rest == None{}: Maybe<&2, String>}:
  match hit:
    case True{}:
      e => Empty.absurd(
        {rest == None{}: Maybe<&2, String>},
        Shared.Maybe.none_ne_some(String, o, Equal.sym(Maybe<&2, String>, Some{o}, None{}, e))
      )
    case False{}:
      e => e

# Voter.cast once the hit of the first node is known
def Voter.cast.at(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  h: U32,
  r: Nat,
  o: String,
  rest: Maybe<&2, String>,
  v: Ledgers.Vote,
  p: String,
  +hit: Bool,
  eh: {Round.hit(~mach, s, c, h, r, o, v) == hit: Bool},
  ih: {
    rest == Some{p}: Maybe<&2, String>
  } -> {Cast.of(~mach, s, Ledgers.Where{c, h, r}, p) == Some{v}: Maybe<&2, Ledgers.Vote>}
) -> {
  Voter.if(hit, o, rest) == Some{p}: Maybe<&2, String>
} -> {Cast.of(~mach, s, Ledgers.Where{c, h, r}, p) == Some{v}: Maybe<&2, Ledgers.Vote>}:
  match hit:
    case True{}:
      e =>
        %Shared.Maybe.some_inj(
          String,
          o,
          p,
          e
        ): {Cast.of(~mach, s, Ledgers.Where{c, h, r}, _) == Some{v}: Maybe<&2, Ledgers.Vote>}
        Hit.cast(~mach, s, c, h, r, o, v)(eh)
    case False{}:
      e => ih(e)

# the voter cast for the step
def Voter.cast(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  +h: U32,
  +r: Nat,
  +os: List<&2, String>,
  +v: Ledgers.Vote,
  +p: String
) -> {
  Round.voter(~mach, s, c, h, r, os, v) == Some{p}: Maybe<&2, String>
} -> {Cast.of(~mach, s, Ledgers.Where{c, h, r}, p) == Some{v}: Maybe<&2, Ledgers.Vote>}:
  match os:
    case Nil{}:
      e => Empty.absurd(
        {Cast.of(~mach, s, Ledgers.Where{c, h, r}, p) == Some{v}: Maybe<&2, Ledgers.Vote>},
        Shared.Maybe.none_ne_some(String, p, e)
      )
    case Con{+o, +rest}:
      Voter.cast.at(
        ~mach,
        s,
        c,
        h,
        r,
        o,
        Round.voter(~mach, s, c, h, r, rest, v),
        v,
        p,
        Round.hit(~mach, s, c, h, r, o, v),
        {==},
        Voter.cast(~mach, s, c, h, r, rest, v, p)
      )

# Voter.yes once the hit of the first node is known
def Voter.yes.at(
  +hit: Bool,
  o: String,
  rest: Maybe<&2, String>,
  y: Nat,
  ih: {rest == None{}: Maybe<&2, String>} -> {y == 0n: Nat}
) -> {
  Voter.if(hit, o, rest) == None{}: Maybe<&2, String>
} -> {Shared.Nat.add_if(hit, y) == 0n: Nat}:
  match hit:
    case True{}:
      e => Empty.absurd(
        {1n+y == 0n: Nat},
        Shared.Maybe.none_ne_some(String, o, Equal.sym(Maybe<&2, String>, Some{o}, None{}, e))
      )
    case False{}:
      e => ih(e)

# with no voter, no ballot is for the step
def Voter.yes(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  +h: U32,
  +r: Nat,
  +os: List<&2, String>,
  +v: Ledgers.Vote
) -> {
  Round.voter(~mach, s, c, h, r, os, v) == None{}: Maybe<&2, String>
} -> {
  Quorums.Quorum.yes(
    ~Ledgers.Vote,
    ~Ledgers.Vote.is_eq,
    Round.ballots(~mach, s, c, h, r, os),
    v
  )
    == 0n: Nat
}:
  match os:
    case Nil{}:
      e => {==}
    case Con{o, rest}:
      Voter.yes.at(
        Round.hit(~mach, s, c, h, r, o, v),
        o,
        Round.voter(~mach, s, c, h, r, rest, v),
        Quorums.Quorum.yes(
          ~Ledgers.Vote,
          ~Ledgers.Vote.is_eq,
          Round.ballots(~mach, s, c, h, r, rest),
          v
        ),
        Voter.yes(~mach, s, c, h, r, rest, v)
      )

# nothing is less than a number that is zero
def Lt.none(n: Nat, y: Nat, e: {y == 0n: Nat}) -> {Nat.is_lt(n, y) == True{}: Bool} -> Empty:
  k =>
    Shared.Nat.lt_zero(n)(
      %e: {Nat.is_lt(n, _) == True{}: Bool}
      k)

# a step with a majority has a voter
def Has.voter(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  +h: U32,
  +r: Nat,
  +os: List<&2, String>,
  +v: Ledgers.Vote
) -> {
  Quorums.Quorum.has(
    ~Ledgers.Vote,
    ~Ledgers.Vote.is_eq,
    Round.ballots(~mach, s, c, h, r, os),
    v
  )
    == True{}: Bool
} -> {Round.voter(~mach, s, c, h, r, os, v) == None{}: Maybe<&2, String>} -> Empty:
  hh => e =>
    Lt.none(
      Quorums.Quorum.no(
        ~Ledgers.Vote,
        ~Ledgers.Vote.is_eq,
        Round.ballots(~mach, s, c, h, r, os),
        v
      ),
      Quorums.Quorum.yes(
        ~Ledgers.Vote,
        ~Ledgers.Vote.is_eq,
        Round.ballots(~mach, s, c, h, r, os),
        v
      ),
      Voter.yes(~mach, s, c, h, r, os, v)(e)
    )(hh)

# Sub.count for a first owner o and a first node f, once it is known whether
# they are the same (b)
def Sub.count.at(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  +h: U32,
  +r: Nat,
  o: String,
  rest: List<&2, String>,
  +f: String,
  +fs: List<&2, String>,
  +v: Ledgers.Vote,
  b: Bool,
  eb: {String.eq(f, o) == b: Bool},
  ih1: {
    Owners.sub(rest, fs) == True{}: Bool
  } -> {
    Round.voter(~mach, s, c, h, r, fs, v) == None{}: Maybe<&2, String>
  } -> {
    Nat.is_le(
      List.length(&2, String, fs),
      Quorums.Quorum.no(
        ~Ledgers.Vote,
        ~Ledgers.Vote.is_eq,
        Round.ballots(~mach, s, c, h, r, rest),
        v
      )
    )
      == True{}: Bool
  },
  ih2: {
    Owners.sub(rest, f <> fs) == True{}: Bool
  } -> {
    Round.voter(~mach, s, c, h, r, f <> fs, v) == None{}: Maybe<&2, String>
  } -> {
    Nat.is_le(
      1n+List.length(&2, String, fs),
      Quorums.Quorum.no(
        ~Ledgers.Vote,
        ~Ledgers.Vote.is_eq,
        Round.ballots(~mach, s, c, h, r, rest),
        v
      )
    )
      == True{}: Bool
  }
) -> {
  Shared.Bool.when(
    Bool,
    b,
    u => Owners.sub(rest, fs),
    u => Owners.sub(rest, f <> fs)
  )
    == True{}: Bool
} -> {
  Round.voter(~mach, s, c, h, r, f <> fs, v) == None{}: Maybe<&2, String>
} -> {
  Nat.is_le(
    1n+List.length(&2, String, fs),
    Shared.Nat.add_if(
      Bool.not(Round.hit(~mach, s, c, h, r, o, v)),
      Quorums.Quorum.no(
        ~Ledgers.Vote,
        ~Ledgers.Vote.is_eq,
        Round.ballots(~mach, s, c, h, r, rest),
        v
      )
    )
  )
    == True{}: Bool
}:
  match b:
    case True{}:
      es => +ev =>
        %Texts.String.eq_sound(
          f,
          o
        )(
          eb
        ): {
          Nat.is_le(
            1n+List.length(&2, String, fs),
            Shared.Nat.add_if(
              Bool.not(Round.hit(~mach, s, c, h, r, _, v)),
              Quorums.Quorum.no(
                ~Ledgers.Vote,
                ~Ledgers.Vote.is_eq,
                Round.ballots(~mach, s, c, h, r, rest),
                v
              )
            )
          )
            == True{}: Bool
        }
        %Equal.sym(
          Bool,
          Round.hit(~mach, s, c, h, r, f, v),
          False{},
          Voter.if_hit(
            Round.hit(~mach, s, c, h, r, f, v),
            f,
            Round.voter(~mach, s, c, h, r, fs, v)
          )(ev)
        ): {
          Nat.is_le(
            1n+List.length(&2, String, fs),
            Shared.Nat.add_if(
              Bool.not(_),
              Quorums.Quorum.no(
                ~Ledgers.Vote,
                ~Ledgers.Vote.is_eq,
                Round.ballots(~mach, s, c, h, r, rest),
                v
              )
            )
          )
            == True{}: Bool
        }
        ih1(
          es
        )(
          Voter.if_rest(
            Round.hit(~mach, s, c, h, r, f, v),
            f,
            Round.voter(~mach, s, c, h, r, fs, v)
          )(ev)
        )
    case False{}:
      es => ev =>
        Shared.Nat.le_add_if(
          Bool.not(Round.hit(~mach, s, c, h, r, o, v)),
          1n+List.length(&2, String, fs),
          Quorums.Quorum.no(
            ~Ledgers.Vote,
            ~Ledgers.Vote.is_eq,
            Round.ballots(~mach, s, c, h, r, rest),
            v
          )
        )(ih2(es)(ev))

# nodes that are some of the owners, none of which cast for the step v, are
# at most the ballots that are not for v
def Sub.count(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  +h: U32,
  +r: Nat,
  os: List<&2, String>,
  from: List<&2, String>,
  +v: Ledgers.Vote
) -> {
  Owners.sub(os, from) == True{}: Bool
} -> {
  Round.voter(~mach, s, c, h, r, from, v) == None{}: Maybe<&2, String>
} -> {
  Nat.is_le(
    List.length(&2, String, from),
    Quorums.Quorum.no(~Ledgers.Vote, ~Ledgers.Vote.is_eq, Round.ballots(~mach, s, c, h, r, os), v)
  )
    == True{}: Bool
}:
  match os from:
    case Nil{} Nil{}:
      es => ev => {==}
    case Nil{} Con{f, fs}:
      es => ev => Empty.absurd({False{} == True{}: Bool}, Shared.Bool.false_ne_true(es))
    case Con{o, rest} Nil{}:
      es => ev => Shared.Nat.le_zero(
        Quorums.Quorum.no(
          ~Ledgers.Vote,
          ~Ledgers.Vote.is_eq,
          Round.ballots(~mach, s, c, h, r, o <> rest),
          v
        )
      )
    case Con{+o, +rest} Con{+f, +fs}:
      Sub.count.at(
        ~mach,
        s,
        c,
        h,
        r,
        o,
        rest,
        f,
        fs,
        v,
        String.eq(f, o),
        {==},
        Sub.count(~mach, s, c, h, r, rest, fs, v),
        Sub.count(~mach, s, c, h, r, rest, f <> fs, v)
      )

# Count.total once the hit of the first node is known
def Count.total.at(
  hit: Bool,
  y: Nat,
  n: Nat,
  l: Nat,
  ih: {Nat.add(y, n) == l: Nat}
) -> {Nat.add(Shared.Nat.add_if(hit, y), Shared.Nat.add_if(Bool.not(hit), n)) == 1n+l: Nat}:
  match hit:
    case True{}:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(y, n), l, ih)
    case False{}:
      Equal.trans(
        Nat,
        Nat.add(y, 1n+n),
        1n+Nat.add(y, n),
        1n+l,
        Shared.Nat.add_succ(y, n),
        Equal.cong(Nat, Nat, z => 1n+z, Nat.add(y, n), l, ih)
      )

# each owner's ballot is for the step v, or is not
def Count.total(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  +h: U32,
  +r: Nat,
  os: List<&2, String>,
  +v: Ledgers.Vote
) -> {
  Nat.add(
    Quorums.Quorum.yes(~Ledgers.Vote, ~Ledgers.Vote.is_eq, Round.ballots(~mach, s, c, h, r, os), v),
    Quorums.Quorum.no(~Ledgers.Vote, ~Ledgers.Vote.is_eq, Round.ballots(~mach, s, c, h, r, os), v)
  )
    == List.length(&2, String, os): Nat
}:
  match os:
    case Nil{}:
      {==}
    case Con{o, +rest}:
      Count.total.at(
        Round.hit(~mach, s, c, h, r, o, v),
        Quorums.Quorum.yes(
          ~Ledgers.Vote,
          ~Ledgers.Vote.is_eq,
          Round.ballots(~mach, s, c, h, r, rest),
          v
        ),
        Quorums.Quorum.no(
          ~Ledgers.Vote,
          ~Ledgers.Vote.is_eq,
          Round.ballots(~mach, s, c, h, r, rest),
          v
        ),
        List.length(&2, String, rest),
        Count.total(~mach, s, c, h, r, rest, v)
      )

# a number is at most a number equal to it
def Le.same(a: Nat, b: Nat, e: {a == b: Nat}) -> {Nat.is_le(a, b) == True{}: Bool}:
  %e: {Nat.is_le(a, _) == True{}: Bool}
  Shared.Nat.le_refl(a)

# two majorities share a node: nodes that are a majority of the owners, none
# of which cast for the step v, leave v no majority
def Major.meets(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  +h: U32,
  +r: Nat,
  +os: List<&2, String>,
  +from: List<&2, String>,
  +v: Ledgers.Vote
) -> {
  Quorums.Quorum.has(
    ~Ledgers.Vote,
    ~Ledgers.Vote.is_eq,
    Round.ballots(~mach, s, c, h, r, os),
    v
  )
    == True{}: Bool
} -> {Owners.sub(os, from) == True{}: Bool}
  -> {Owners.major(os, from) == True{}: Bool}
  -> {Round.voter(~mach, s, c, h, r, from, v) == None{}: Maybe<&2, String>}
  -> Empty:
  hh => es => em => ev =>
    Shared.Nat.pigeon(
      List.length(&2, String, from),
      Quorums.Quorum.no(
        ~Ledgers.Vote,
        ~Ledgers.Vote.is_eq,
        Round.ballots(~mach, s, c, h, r, os),
        v
      ),
      Quorums.Quorum.yes(
        ~Ledgers.Vote,
        ~Ledgers.Vote.is_eq,
        Round.ballots(~mach, s, c, h, r, os),
        v
      ),
      List.length(&2, String, os)
    )(
      Sub.count(~mach, s, c, h, r, os, from, v)(es)(ev)
    )(
      hh
    )(
      Le.same(
        Nat.add(
          Quorums.Quorum.yes(
            ~Ledgers.Vote,
            ~Ledgers.Vote.is_eq,
            Round.ballots(~mach, s, c, h, r, os),
            v
          ),
          Quorums.Quorum.no(
            ~Ledgers.Vote,
            ~Ledgers.Vote.is_eq,
            Round.ballots(~mach, s, c, h, r, os),
            v
          )
        ),
        List.length(&2, String, os),
        Count.total(~mach, s, c, h, r, os, v)
      )
    )(em)

# the round of a last vote, 0 without one
def Last.round(m: Maybe<&2, Ledgers.Last>) -> Nat:
  match m:
    case Some{Ledgers.Last{r, v}}:
      r
    case None{}:
      0n

# the step of a last vote, d without one
def Last.step(d: Ledgers.Vote, m: Maybe<&2, Ledgers.Last>) -> Ledgers.Vote:
  match m:
    case Some{Ledgers.Last{r, v}}:
      v
    case None{}:
      d

# the last vote m is of the round r1 or of a later one
def Last.from(m: Maybe<&2, Ledgers.Last>, r1: Nat) -> Bool:
  match m:
    case Some{Ledgers.Last{r, v}}:
      Nat.is_le(r1, r)
    case None{}:
      False{}

# Mine.le for one round
def Mine.le.or(
  k: Nat,
  m: Maybe<&2, Ledgers.Vote>,
  rest: Maybe<&2, Ledgers.Last>,
  r: Nat,
  x: Ledgers.Vote,
  ih: {
    rest == Some{Ledgers.Last{r, x}}: Maybe<&2, Ledgers.Last>
  } -> {Nat.is_le(r, k) == True{}: Bool}
) -> {
  Last.or(k, m, u => rest) == Some{Ledgers.Last{r, x}}: Maybe<&2, Ledgers.Last>
} -> {Nat.is_le(r, k) == True{}: Bool}:
  match m:
    case Some{y}:
      e =>
        %Equal.cong(
          Maybe<&2, Ledgers.Last>,
          Nat,
          Last.round,
          Some{Ledgers.Last{k, y}},
          Some{Ledgers.Last{r, x}},
          e
        ): {Nat.is_le(_, k) == True{}: Bool}
        Shared.Nat.le_refl(k)
    case None{}:
      e => ih(e)

# the last vote of a node up to the round p is of a round up to p
def Mine.le(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  +h: U32,
  +q: String,
  p: Nat,
  +r: Nat,
  +x: Ledgers.Vote
) -> {
  Last.mine(~mach, q, s, c, h, p) == Some{Ledgers.Last{r, x}}: Maybe<&2, Ledgers.Last>
} -> {Nat.is_le(r, p) == True{}: Bool}:
  match p:
    case 0n:
      Mine.le.or(
        0n,
        Cast.of(~mach, s, Ledgers.Where{c, h, 0n}, q),
        None{},
        r,
        x,
        e => Empty.absurd(
          {Nat.is_le(r, 0n) == True{}: Bool},
          Shared.Maybe.none_ne_some(Ledgers.Last, Ledgers.Last{r, x}, e)
        )
      )
    case 1n+(+j):
      Mine.le.or(
        1n+j,
        Cast.of(~mach, s, Ledgers.Where{c, h, 1n+j}, q),
        Last.mine(~mach, q, s, c, h, j),
        r,
        x,
        e => Shared.Nat.le_succ(r, j)(Mine.le(~mach, s, c, h, q, j, r, x)(e))
      )

# Mine.cast for one round
def Mine.cast.or(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  h: U32,
  q: String,
  k: Nat,
  m: Maybe<&2, Ledgers.Vote>,
  em: {Cast.of(~mach, s, Ledgers.Where{c, h, k}, q) == m: Maybe<&2, Ledgers.Vote>},
  rest: Maybe<&2, Ledgers.Last>,
  r: Nat,
  x: Ledgers.Vote,
  ih: {
    rest == Some{Ledgers.Last{r, x}}: Maybe<&2, Ledgers.Last>
  } -> {Cast.of(~mach, s, Ledgers.Where{c, h, r}, q) == Some{x}: Maybe<&2, Ledgers.Vote>}
) -> {
  Last.or(k, m, u => rest) == Some{Ledgers.Last{r, x}}: Maybe<&2, Ledgers.Last>
} -> {Cast.of(~mach, s, Ledgers.Where{c, h, r}, q) == Some{x}: Maybe<&2, Ledgers.Vote>}:
  match m:
    case Some{y}:
      +e =>
        %Equal.cong(
          Maybe<&2, Ledgers.Last>,
          Nat,
          Last.round,
          Some{Ledgers.Last{k, y}},
          Some{Ledgers.Last{r, x}},
          e
        ): {Cast.of(~mach, s, Ledgers.Where{c, h, _}, q) == Some{x}: Maybe<&2, Ledgers.Vote>}
        %Equal.cong(
          Maybe<&2, Ledgers.Last>,
          Ledgers.Vote,
          Last.step(y),
          Some{Ledgers.Last{k, y}},
          Some{Ledgers.Last{r, x}},
          e
        ): {Cast.of(~mach, s, Ledgers.Where{c, h, k}, q) == Some{_}: Maybe<&2, Ledgers.Vote>}
        em
    case None{}:
      e => ih(e)

# the last vote of a node is a vote that it cast
def Mine.cast(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  +h: U32,
  +q: String,
  p: Nat,
  +r: Nat,
  +x: Ledgers.Vote
) -> {
  Last.mine(~mach, q, s, c, h, p) == Some{Ledgers.Last{r, x}}: Maybe<&2, Ledgers.Last>
} -> {Cast.of(~mach, s, Ledgers.Where{c, h, r}, q) == Some{x}: Maybe<&2, Ledgers.Vote>}:
  match p:
    case 0n:
      Mine.cast.or(
        ~mach,
        s,
        c,
        h,
        q,
        0n,
        Cast.of(~mach, s, Ledgers.Where{c, h, 0n}, q),
        {==},
        None{},
        r,
        x,
        e => Empty.absurd(
          {Cast.of(~mach, s, Ledgers.Where{c, h, r}, q) == Some{x}: Maybe<&2, Ledgers.Vote>},
          Shared.Maybe.none_ne_some(Ledgers.Last, Ledgers.Last{r, x}, e)
        )
      )
    case 1n+(+j):
      Mine.cast.or(
        ~mach,
        s,
        c,
        h,
        q,
        1n+j,
        Cast.of(~mach, s, Ledgers.Where{c, h, 1n+j}, q),
        {==},
        Last.mine(~mach, q, s, c, h, j),
        r,
        x,
        Mine.cast(~mach, s, c, h, q, j, r, x)
      )

# Cast.apart once it is known whether the rounds are the same (b)
def Cast.apart.at(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  h: U32,
  q: String,
  +r1: Nat,
  +k: Nat,
  v1: Ledgers.Vote,
  b: Bool,
  eb: {Nat.is_eq(r1, k) == b: Bool}
) -> {
  Cast.of(~mach, s, Ledgers.Where{c, h, r1}, q) == Some{v1}: Maybe<&2, Ledgers.Vote>
} -> {
  Cast.of(~mach, s, Ledgers.Where{c, h, k}, q) == None{}: Maybe<&2, Ledgers.Vote>
} -> {b == False{}: Bool}:
  match b:
    case True{}:
      e1 => en => Empty.absurd(
        {True{} == False{}: Bool},
        Shared.Maybe.none_ne_some(
          Ledgers.Vote,
          v1,
          Equal.trans(
            Maybe<&2, Ledgers.Vote>,
            None{},
            Cast.of(~mach, s, Ledgers.Where{c, h, k}, q),
            Some{v1},
            Equal.sym(
              Maybe<&2, Ledgers.Vote>,
              Cast.of(~mach, s, Ledgers.Where{c, h, k}, q),
              None{},
              en
            ),
            Cast.moved(~mach, s, c, h, q, r1, k, v1, Shared.Nat.is_eq_sound(r1, k)(eb))(e1)
          )
        )
      )
    case False{}:
      e1 => en => {==}

# a round with a vote of a node is not a round without one
def Cast.apart(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  h: U32,
  q: String,
  +r1: Nat,
  +k: Nat,
  v1: Ledgers.Vote
) -> {
  Cast.of(~mach, s, Ledgers.Where{c, h, r1}, q) == Some{v1}: Maybe<&2, Ledgers.Vote>
} -> {
  Cast.of(~mach, s, Ledgers.Where{c, h, k}, q) == None{}: Maybe<&2, Ledgers.Vote>
} -> {Nat.is_eq(r1, k) == False{}: Bool}:
  e1 => en => Cast.apart.at(~mach, s, c, h, q, r1, k, v1, Nat.is_eq(r1, k), {==})(e1)(en)

# Mine.from for one round
def Mine.from.or(
  k: Nat,
  m: Maybe<&2, Ledgers.Vote>,
  rest: Maybe<&2, Ledgers.Last>,
  r1: Nat
) -> {
  Nat.is_le(r1, k) == True{}: Bool
} -> (
  {m == None{}: Maybe<&2, Ledgers.Vote>} -> {Last.from(rest, r1) == True{}: Bool}
) -> {Last.from(Last.or(k, m, u => rest), r1) == True{}: Bool}:
  match m:
    case Some{y}:
      hk => ih => hk
    case None{}:
      hk => ih => ih({==})

# a node that cast in the round r1 has a last vote of r1 or later, up to any
# round from r1 on
def Mine.from(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  +h: U32,
  +q: String,
  p: Nat,
  +r1: Nat,
  +v1: Ledgers.Vote
) -> {
  Cast.of(~mach, s, Ledgers.Where{c, h, r1}, q) == Some{v1}: Maybe<&2, Ledgers.Vote>
} -> {
  Nat.is_le(r1, p) == True{}: Bool
} -> {Last.from(Last.mine(~mach, q, s, c, h, p), r1) == True{}: Bool}:
  match p:
    case 0n:
      +e1 => +le =>
        Mine.from.or(
          0n,
          Cast.of(~mach, s, Ledgers.Where{c, h, 0n}, q),
          None{},
          r1
        )(
          le
        )(
          en => Empty.absurd(
            {False{} == True{}: Bool},
            Shared.Maybe.none_ne_some(
              Ledgers.Vote,
              v1,
              Equal.trans(
                Maybe<&2, Ledgers.Vote>,
                None{},
                Cast.of(~mach, s, Ledgers.Where{c, h, 0n}, q),
                Some{v1},
                Equal.sym(
                  Maybe<&2, Ledgers.Vote>,
                  Cast.of(~mach, s, Ledgers.Where{c, h, 0n}, q),
                  None{},
                  en
                ),
                Cast.moved(~mach, s, c, h, q, r1, 0n, v1, Shared.Nat.le_zero_eq(r1)(le))(e1)
              )
            )
          )
        )
    case 1n+(+j):
      +e1 => +le =>
        Mine.from.or(
          1n+j,
          Cast.of(~mach, s, Ledgers.Where{c, h, 1n+j}, q),
          Last.mine(~mach, q, s, c, h, j),
          r1
        )(
          le
        )(
          en => Mine.from(
            ~mach,
            s,
            c,
            h,
            q,
            j,
            r1,
            v1
          )(e1)(Shared.Nat.le_step(r1, j)(le)(Cast.apart(~mach, s, c, h, q, r1, 1n+j, v1)(e1)(en)))
        )

# Newer.left once it is known whether the round of a is less than that of b
def Newer.left.at(
  +ra: Nat,
  va: Ledgers.Vote,
  +rb: Nat,
  vb: Ledgers.Vote,
  r1: Nat,
  b: Bool,
  eb: {Nat.is_lt(ra, rb) == b: Bool}
) -> {
  Last.from(
    Shared.Bool.when(
      Maybe<&2, Ledgers.Last>,
      b,
      u => Some{Ledgers.Last{rb, vb}},
      u => Some{Ledgers.Last{ra, va}}
    ),
    r1
  )
    == False{}: Bool
} -> {Nat.is_le(r1, ra) == False{}: Bool}:
  match b:
    case True{}:
      e => Shared.Nat.nle_trans(r1, ra, rb)(e)(Shared.Nat.lt_weak(ra, rb)(eb))
    case False{}:
      e => e

# when the newer of two last votes is before the round r1, so is the first
def Newer.left(
  a: Maybe<&2, Ledgers.Last>,
  b: Maybe<&2, Ledgers.Last>,
  r1: Nat
) -> {Last.from(Last.newer(a, b), r1) == False{}: Bool} -> {Last.from(a, r1) == False{}: Bool}:
  match a b:
    case None{} y:
      e => {==}
    case Some{x} None{}:
      e => e
    case Some{Ledgers.Last{+ra, va}} Some{Ledgers.Last{+rb, vb}}:
      Newer.left.at(ra, va, rb, vb, r1, Nat.is_lt(ra, rb), {==})

# Newer.right once it is known whether the round of a is less than that of b
def Newer.right.at(
  +ra: Nat,
  va: Ledgers.Vote,
  +rb: Nat,
  vb: Ledgers.Vote,
  r1: Nat,
  b: Bool,
  eb: {Nat.is_lt(ra, rb) == b: Bool}
) -> {
  Last.from(
    Shared.Bool.when(
      Maybe<&2, Ledgers.Last>,
      b,
      u => Some{Ledgers.Last{rb, vb}},
      u => Some{Ledgers.Last{ra, va}}
    ),
    r1
  )
    == False{}: Bool
} -> {Nat.is_le(r1, rb) == False{}: Bool}:
  match b:
    case True{}:
      e => e
    case False{}:
      e => Shared.Nat.nle_trans(r1, rb, ra)(e)(Shared.Nat.nlt_le(ra, rb)(eb))

# when the newer of two last votes is before the round r1, so is the second
def Newer.right(
  a: Maybe<&2, Ledgers.Last>,
  b: Maybe<&2, Ledgers.Last>,
  r1: Nat
) -> {Last.from(Last.newer(a, b), r1) == False{}: Bool} -> {Last.from(b, r1) == False{}: Bool}:
  match a b:
    case None{} y:
      e => e
    case Some{x} None{}:
      e => {==}
    case Some{Ledgers.Last{+ra, va}} Some{Ledgers.Last{+rb, vb}}:
      Newer.right.at(ra, va, rb, vb, r1, Nat.is_lt(ra, rb), {==})

# the rule that the passes that a vote names allow it, at the head hd whose tip is tp
def Rules.allow(
  ~mach: Machine(),
  ~s: Node<Machine.Q(mach)>,
  ~c: Ledgers.Chain,
  ~rules: Rounds.Rules(~mach, s, c),
  hd: Head,
  tp: Tip,
  ok: {Head.tip(~mach, s, hd) == Some{tp}: Maybe<&2, Tip>}
) -> Rounds.Allow(~mach, s, c, Head.next(hd), Tip.owners(tp)):
  Shared.Pair.first(
    Rounds.Allow(~mach, s, c, Head.next(hd), Tip.owners(tp)),
    Rounds.Last(~mach, s, c, Head.next(hd)) & Rounds.Same(~mach, s, c, Head.next(hd)),
    rules(hd)(tp)(ok)
  )

# the rule that a pass names the last vote of its node below its round, at the head hd whose tip is tp
def Rules.last(
  ~mach: Machine(),
  ~s: Node<Machine.Q(mach)>,
  ~c: Ledgers.Chain,
  ~rules: Rounds.Rules(~mach, s, c),
  hd: Head,
  tp: Tip,
  ok: {Head.tip(~mach, s, hd) == Some{tp}: Maybe<&2, Tip>}
) -> Rounds.Last(~mach, s, c, Head.next(hd)):
  Shared.Pair.first(
    Rounds.Last(~mach, s, c, Head.next(hd)),
    Rounds.Same(~mach, s, c, Head.next(hd)),
    Shared.Pair.second(
      Rounds.Allow(~mach, s, c, Head.next(hd), Tip.owners(tp)),
      Rounds.Last(~mach, s, c, Head.next(hd)) & Rounds.Same(~mach, s, c, Head.next(hd)),
      rules(hd)(tp)(ok)
    )
  )

# the rule that the votes of one round are for one step, at the head hd whose tip is tp
def Rules.same(
  ~mach: Machine(),
  ~s: Node<Machine.Q(mach)>,
  ~c: Ledgers.Chain,
  ~rules: Rounds.Rules(~mach, s, c),
  hd: Head,
  tp: Tip,
  ok: {Head.tip(~mach, s, hd) == Some{tp}: Maybe<&2, Tip>}
) -> Rounds.Same(~mach, s, c, Head.next(hd)):
  Shared.Pair.second(
    Rounds.Last(~mach, s, c, Head.next(hd)),
    Rounds.Same(~mach, s, c, Head.next(hd)),
    Shared.Pair.second(
      Rounds.Allow(~mach, s, c, Head.next(hd), Tip.owners(tp)),
      Rounds.Last(~mach, s, c, Head.next(hd)) & Rounds.Same(~mach, s, c, Head.next(hd)),
      rules(hd)(tp)(ok)
    )
  )

# Pass.miss for a first node o, once its hit in the round r1 (hit) and its
# pass (m) are known
def Pass.miss.at(
  ~mach: Machine(),
  ~s: Node<Machine.Q(mach)>,
  ~c: Ledgers.Chain,
  ~rules: Rounds.Rules(~mach, s, c),
  +hd: Head,
  tp: Tip,
  ok: {Head.tip(~mach, s, hd) == Some{tp}: Maybe<&2, Tip>},
  +p: Nat,
  +r1: Nat,
  +v1: Ledgers.Vote,
  +o: String,
  rest: Maybe<&2, String>,
  hit: Bool,
  m: Maybe<&2, Maybe<&2, Ledgers.Last>>
) -> {Round.hit(~mach, s, c, Head.next(hd), r1, o, v1) == hit: Bool}
  -> {
    Ledgers.State.passed(
      ~Machine.Q(mach),
      State.ledger(~mach, s),
      Ledgers.Where{c, Head.next(hd), 1n+p},
      o
    )
      == m: Maybe<&2, Maybe<&2, Ledgers.Last>>
  }
  -> {Nat.is_le(r1, p) == True{}: Bool}
  -> {Maybe.is_some(&2, Maybe<&2, Ledgers.Last>, m) == True{}: Bool}
  -> {Last.from(Passed.last(m), r1) == False{}: Bool}
  -> {rest == None{}: Maybe<&2, String>}
  -> {Voter.if(hit, o, rest) == None{}: Maybe<&2, String>}:
  match hit m:
    case False{} y:
      eh => em => le => es => ef => ih => ih
    case True{} None{}:
      eh => em => le => es => ef => ih => Empty.absurd(
        {Some{o} == None{}: Maybe<&2, String>},
        Shared.Bool.false_ne_true(es)
      )
    case True{} Some{l}:
      eh => em => le => es => ef => ih => Empty.absurd(
        {Some{o} == None{}: Maybe<&2, String>},
        Shared.Bool.false_ne_true(Equal.trans(
            Bool,
            False{},
            Last.from(l, r1),
            True{},
            Equal.sym(Bool, Last.from(l, r1), False{}, ef),
            %Equal.sym(Maybe<&2, Ledgers.Last>, l, Last.mine(~mach, o, s, c, Head.next(hd), p), Rules.last(~mach, ~s, ~c, ~rules, hd, tp, ok)(1n+p)(o)(l)(em)): {Last.from(_, r1) == True{}: Bool}
            Mine.from(~mach, s, c, Head.next(hd), o, p, r1, v1)(Hit.cast(~mach, s, c, Head.next(hd), r1, o, v1)(eh))(le)))
      )

# when the passes of the nodes from to the round 1 + p name no vote of the
# round r1 or later, none of them cast in r1
def Pass.miss(
  ~mach: Machine(),
  ~s: Node<Machine.Q(mach)>,
  ~c: Ledgers.Chain,
  ~rules: Rounds.Rules(~mach, s, c),
  +hd: Head,
  +tp: Tip,
  +ok: {Head.tip(~mach, s, hd) == Some{tp}: Maybe<&2, Tip>},
  +p: Nat,
  +r1: Nat,
  +v1: Ledgers.Vote,
  from: List<&2, String>
) -> {Nat.is_le(r1, p) == True{}: Bool}
  -> {Passed.all(~mach, s, Ledgers.Where{c, Head.next(hd), 1n+p}, from) == True{}: Bool}
  -> {
    Last.from(
      Passes.last(~mach, s, Ledgers.Where{c, Head.next(hd), 1n+p}, from),
      r1
    )
      == False{}: Bool
  }
  -> {Round.voter(~mach, s, c, Head.next(hd), r1, from, v1) == None{}: Maybe<&2, String>}:
  match from:
    case Nil{}:
      le => ea => ef => {==}
    case Con{+o, +rest}:
      +le => +ea => +ef =>
        Pass.miss.at(
          ~mach,
          ~s,
          ~c,
          ~rules,
          hd,
          tp,
          ok,
          p,
          r1,
          v1,
          o,
          Round.voter(~mach, s, c, Head.next(hd), r1, rest, v1),
          Round.hit(~mach, s, c, Head.next(hd), r1, o, v1),
          Ledgers.State.passed(
            ~Machine.Q(mach),
            State.ledger(~mach, s),
            Ledgers.Where{c, Head.next(hd), 1n+p},
            o
          )
        )(
          {==}
        )(
          {==}
        )(
          le
        )(
          Shared.List.all.if_hit(
            Maybe.is_some(
              &2,
              Maybe<&2, Ledgers.Last>,
              Ledgers.State.passed(
                ~Machine.Q(mach),
                State.ledger(~mach, s),
                Ledgers.Where{c, Head.next(hd), 1n+p},
                o
              )
            ),
            u => Passed.all(~mach, s, Ledgers.Where{c, Head.next(hd), 1n+p}, rest)
          )(ea)
        )(
          Newer.left(
            Passed.last(
              Ledgers.State.passed(
                ~Machine.Q(mach),
                State.ledger(~mach, s),
                Ledgers.Where{c, Head.next(hd), 1n+p},
                o
              )
            ),
            Passes.last(~mach, s, Ledgers.Where{c, Head.next(hd), 1n+p}, rest),
            r1
          )(ef)
        )(
          Pass.miss(
            ~mach,
            ~s,
            ~c,
            ~rules,
            hd,
            tp,
            ok,
            p,
            r1,
            v1,
            rest
          )(
            le
          )(
            Shared.List.all.if_rest(
              Maybe.is_some(
                &2,
                Maybe<&2, Ledgers.Last>,
                Ledgers.State.passed(
                  ~Machine.Q(mach),
                  State.ledger(~mach, s),
                  Ledgers.Where{c, Head.next(hd), 1n+p},
                  o
                )
              ),
              u => Passed.all(~mach, s, Ledgers.Where{c, Head.next(hd), 1n+p}, rest)
            )(ea)
          )(
            Newer.right(
              Passed.last(
                Ledgers.State.passed(
                  ~Machine.Q(mach),
                  State.ledger(~mach, s),
                  Ledgers.Where{c, Head.next(hd), 1n+p},
                  o
                )
              ),
              Passes.last(~mach, s, Ledgers.Where{c, Head.next(hd), 1n+p}, rest),
              r1
            )(ef)
          )
        )

# the case of a choice by b
def When.elim(
  -R: Type,
  x: Bool,
  a: Maybe<&2, Ledgers.Last>,
  b: Maybe<&2, Ledgers.Last>,
  l: Ledgers.Last
) -> {
  Shared.Bool.when(Maybe<&2, Ledgers.Last>, x, u => b, u => a) == Some{l}: Maybe<&2, Ledgers.Last>
} -> (
  {b == Some{l}: Maybe<&2, Ledgers.Last>} -> R
) -> ({a == Some{l}: Maybe<&2, Ledgers.Last>} -> R) -> R:
  match x:
    case True{}:
      e => f => g => f(e)
    case False{}:
      e => f => g => g(e)

# that the pass of some node to the place w names the last vote l
def Named(
  ~mach: Machine(),
  -R: Type,
  s: Node<Machine.Q(mach)>,
  w: Ledgers.Where,
  l: Ledgers.Last
) -> Type:
  (
    @q: String -> {
      Passed.last(
        Ledgers.State.passed(~Machine.Q(mach), State.ledger(~mach, s), w, q)
      )
        == Some{l}: Maybe<&2, Ledgers.Last>
    } -> R
  ) -> R

# Last.elim for a first node o, once what it named (a) and what the rest
# named (b) are known
def Last.elim.at(
  ~mach: Machine(),
  -R: Type,
  s: Node<Machine.Q(mach)>,
  w: Ledgers.Where,
  o: String,
  l: Ledgers.Last,
  a: Maybe<&2, Ledgers.Last>,
  b: Maybe<&2, Ledgers.Last>
) -> {
  Passed.last(
    Ledgers.State.passed(~Machine.Q(mach), State.ledger(~mach, s), w, o)
  )
    == a: Maybe<&2, Ledgers.Last>
} -> (
  {b == Some{l}: Maybe<&2, Ledgers.Last>} -> Named(~mach, R, s, w, l)
) -> {Last.newer(a, b) == Some{l}: Maybe<&2, Ledgers.Last>} -> Named(~mach, R, s, w, l):
  match a b:
    case None{} y:
      ea => ih => e => ih(e)
    case Some{x} None{}:
      ea => ih => e => k => k(
        o
      )(
        Equal.trans(
          Maybe<&2, Ledgers.Last>,
          Passed.last(Ledgers.State.passed(~Machine.Q(mach), State.ledger(~mach, s), w, o)),
          Some{x},
          Some{l},
          ea,
          e
        )
      )
    case Some{Ledgers.Last{+ra, va}} Some{Ledgers.Last{+rb, vb}}:
      ea => ih => e =>
        When.elim(
          Named(~mach, R, s, w, l),
          Nat.is_lt(ra, rb),
          Some{Ledgers.Last{ra, va}},
          Some{Ledgers.Last{rb, vb}},
          l
        )(
          e
        )(
          ih
        )(
          e2 => k => k(
            o
          )(
            Equal.trans(
              Maybe<&2, Ledgers.Last>,
              Passed.last(Ledgers.State.passed(~Machine.Q(mach), State.ledger(~mach, s), w, o)),
              Some{Ledgers.Last{ra, va}},
              Some{l},
              ea,
              e2
            )
          )
        )

# the last vote of the highest round that passes name is named by one of them
def Last.elim(
  ~mach: Machine(),
  -R: Type,
  +s: Node<Machine.Q(mach)>,
  +w: Ledgers.Where,
  from: List<&2, String>,
  +l: Ledgers.Last
) -> {
  Passes.last(~mach, s, w, from) == Some{l}: Maybe<&2, Ledgers.Last>
} -> Named(~mach, R, s, w, l):
  match from:
    case Nil{}:
      e => k => Empty.absurd(R, Shared.Maybe.none_ne_some(Ledgers.Last, l, e))
    case Con{+o, +rest}:
      Last.elim.at(
        ~mach,
        R,
        s,
        w,
        o,
        l,
        Passed.last(Ledgers.State.passed(~Machine.Q(mach), State.ledger(~mach, s), w, o)),
        Passes.last(~mach, s, w, rest)
      )({==})(Last.elim(~mach, R, s, w, rest, l))

# a pass that names a last vote is held
def Passed.some(
  m: Maybe<&2, Maybe<&2, Ledgers.Last>>,
  l: Ledgers.Last
) -> {
  Passed.last(m) == Some{l}: Maybe<&2, Ledgers.Last>
} -> {m == Some{Some{l}}: Maybe<&2, Maybe<&2, Ledgers.Last>>}:
  match m:
    case None{}:
      e => Empty.absurd(
        {None{} == Some{Some{l}}: Maybe<&2, Maybe<&2, Ledgers.Last>>},
        Shared.Maybe.none_ne_some(Ledgers.Last, l, e)
      )
    case Some{x}:
      e => Equal.cong(
        Maybe<&2, Ledgers.Last>,
        Maybe<&2, Maybe<&2, Ledgers.Last>>,
        y => Some{y},
        x,
        Some{l},
        e
      )

# the parts of the rule of a later round
def Later.all(a: Bool, b: Bool, c: Bool, d: Bool) -> Bool:
  List.all.if(u2 => List.all.if(u3 => List.all.if(u4 => d, c), b), a)

def Later.all.a(
  a: Bool,
  b: Bool,
  c: Bool,
  d: Bool
) -> {Later.all(a, b, c, d) == True{}: Bool} -> {a == True{}: Bool}:
  match a:
    case True{}:
      e => {==}
    case False{}:
      e => e

def Later.all.b(
  a: Bool,
  b: Bool,
  c: Bool,
  d: Bool
) -> {Later.all(a, b, c, d) == True{}: Bool} -> {b == True{}: Bool}:
  match a b:
    case True{} True{}:
      e => {==}
    case True{} False{}:
      e => e
    case False{} y:
      e => Empty.absurd({y == True{}: Bool}, Shared.Bool.false_ne_true(e))

def Later.all.c(
  a: Bool,
  b: Bool,
  c: Bool,
  d: Bool
) -> {Later.all(a, b, c, d) == True{}: Bool} -> {c == True{}: Bool}:
  match a b c:
    case True{} True{} True{}:
      e => {==}
    case True{} True{} False{}:
      e => e
    case True{} False{} z:
      e => Empty.absurd({z == True{}: Bool}, Shared.Bool.false_ne_true(e))
    case False{} y z:
      e => Empty.absurd({z == True{}: Bool}, Shared.Bool.false_ne_true(e))

def Later.all.d(
  a: Bool,
  b: Bool,
  c: Bool,
  d: Bool
) -> {Later.all(a, b, c, d) == True{}: Bool} -> {d == True{}: Bool}:
  match a b c:
    case True{} True{} True{}:
      e => e
    case True{} True{} False{}:
      e => Empty.absurd({d == True{}: Bool}, Shared.Bool.false_ne_true(e))
    case True{} False{} z:
      e => Empty.absurd({d == True{}: Bool}, Shared.Bool.false_ne_true(e))
    case False{} y z:
      e => Empty.absurd({d == True{}: Bool}, Shared.Bool.false_ne_true(e))

# that each vote of a round from r1 on, below the round j, is for the step v1
def Rounds.Below(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  h: U32,
  r1: Nat,
  v1: Ledgers.Vote,
  j: Nat
) -> Type:
  @rm: Nat -> @qm: String -> @vm: Ledgers.Vote -> {
    Nat.is_lt(rm, j) == True{}: Bool
  } -> {
    Nat.is_le(r1, rm) == True{}: Bool
  } -> {
    Cast.of(~mach, s, Ledgers.Where{c, h, rm}, qm) == Some{vm}: Maybe<&2, Ledgers.Vote>
  } -> {vm == v1: Ledgers.Vote}

# Rounds.last once the node qw that named the last vote is known, with its
# last vote
def Rounds.named(
  ~mach: Machine(),
  ~s: Node<Machine.Q(mach)>,
  ~c: Ledgers.Chain,
  ~rules: Rounds.Rules(~mach, s, c),
  +hd: Head,
  tp: Tip,
  r1: Nat,
  v1: Ledgers.Vote,
  +p: Nat,
  j: Nat,
  +rm: Nat,
  +vm: Ledgers.Vote,
  +qw: String,
  +em: {
    Last.mine(
      ~mach,
      qw,
      s,
      c,
      Head.next(hd),
      p
    )
      == Some{Ledgers.Last{rm, vm}}: Maybe<&2, Ledgers.Last>
  },
  lt: {Nat.is_lt(p, j) == True{}: Bool},
  le: {Nat.is_le(r1, rm) == True{}: Bool},
  ih: Rounds.Below(~mach, s, c, Head.next(hd), r1, v1, j)
) -> {vm == v1: Ledgers.Vote}:
  ih(
    rm
  )(
    qw
  )(
    vm
  )(
    Shared.Nat.le_lt(rm, p, j)(Mine.le(~mach, s, c, Head.next(hd), qw, p, rm, vm)(em))(lt)
  )(le)(Mine.cast(~mach, s, c, Head.next(hd), qw, p, rm, vm)(em))

# Rounds.round once the last vote m that the passes name is known: it is of
# the round r1 or later, and the vote x is for its step
def Rounds.last(
  ~mach: Machine(),
  ~s: Node<Machine.Q(mach)>,
  ~c: Ledgers.Chain,
  ~rules: Rounds.Rules(~mach, s, c),
  +hd: Head,
  +tp: Tip,
  +ok: {Head.tip(~mach, s, hd) == Some{tp}: Maybe<&2, Tip>},
  r1: Nat,
  v1: Ledgers.Vote,
  +p: Nat,
  x: Ledgers.Vote,
  j: Nat,
  from: List<&2, String>,
  m: Maybe<&2, Ledgers.Last>
) -> {
  Passes.last(~mach, s, Ledgers.Where{c, Head.next(hd), 1n+p}, from) == m: Maybe<&2, Ledgers.Last>
}
  -> {Last.from(m, r1) == True{}: Bool}
  -> {Last.is(m, x) == True{}: Bool}
  -> {Nat.is_lt(p, j) == True{}: Bool}
  -> Rounds.Below(~mach, s, c, Head.next(hd), r1, v1, j)
  -> {x == v1: Ledgers.Vote}:
  match m:
    case None{}:
      em => ef => ei => lt => ih => Empty.absurd(
        {x == v1: Ledgers.Vote},
        Shared.Bool.false_ne_true(ef)
      )
    case Some{Ledgers.Last{+rm, +vm}}:
      em => ef => ei => lt => ih =>
        Last.elim(
          ~mach,
          {x == v1: Ledgers.Vote},
          s,
          Ledgers.Where{c, Head.next(hd), 1n+p},
          from,
          Ledgers.Last{rm, vm}
        )(em)(
          +qw => ew =>
            %Ledgers.Vote.is_eq_sound(vm, x)(ei): {_ == v1: Ledgers.Vote}
            Rounds.named(~mach, ~s, ~c, ~rules, hd, tp, r1, v1, p, j, rm, vm, qw, Equal.sym(Maybe<&2, Ledgers.Last>, Some{Ledgers.Last{rm, vm}}, Last.mine(~mach, qw, s, c, Head.next(hd), p), Rules.last(~mach, ~s, ~c, ~rules, hd, tp, ok)(1n+p)(qw)(Some{Ledgers.Last{rm, vm}})(Passed.some(Ledgers.State.passed(~Machine.Q(mach), State.ledger(~mach, s), Ledgers.Where{c, Head.next(hd), 1n+p}, qw), Ledgers.Last{rm, vm})(ew))), lt, ef, ih))

# Rounds.round once it is known whether the passes name a vote of the round
# r1 or later (f)
def Rounds.pick(
  ~mach: Machine(),
  ~s: Node<Machine.Q(mach)>,
  ~c: Ledgers.Chain,
  ~rules: Rounds.Rules(~mach, s, c),
  +hd: Head,
  +tp: Tip,
  ok: {Head.tip(~mach, s, hd) == Some{tp}: Maybe<&2, Tip>},
  +r1: Nat,
  +v1: Ledgers.Vote,
  +p: Nat,
  +x: Ledgers.Vote,
  j: Nat,
  +from: List<&2, String>,
  f: Bool
) -> {Last.from(Passes.last(~mach, s, Ledgers.Where{c, Head.next(hd), 1n+p}, from), r1) == f: Bool}
  -> {
    Quorums.Quorum.has(
      ~Ledgers.Vote,
      ~Ledgers.Vote.is_eq,
      Round.ballots(~mach, s, c, Head.next(hd), r1, Tip.owners(tp)),
      v1
    )
      == True{}: Bool
  }
  -> {Nat.is_lt(p, j) == True{}: Bool}
  -> {Nat.is_le(r1, p) == True{}: Bool}
  -> Rounds.Below(~mach, s, c, Head.next(hd), r1, v1, j)
  -> {
    Later.all(
      Passed.all(~mach, s, Ledgers.Where{c, Head.next(hd), 1n+p}, from),
      Owners.sub(Tip.owners(tp), from),
      Owners.major(Tip.owners(tp), from),
      Last.is(Passes.last(~mach, s, Ledgers.Where{c, Head.next(hd), 1n+p}, from), x)
    )
      == True{}: Bool
  }
  -> {x == v1: Ledgers.Vote}:
  match f:
    case False{}:
      ef => hh => lt => le => ih => +al =>
        Empty.absurd(
          {x == v1: Ledgers.Vote},
          Major.meets(
            ~mach,
            s,
            c,
            Head.next(hd),
            r1,
            Tip.owners(tp),
            from,
            v1
          )(
            hh
          )(
            Later.all.b(
              Passed.all(~mach, s, Ledgers.Where{c, Head.next(hd), 1n+p}, from),
              Owners.sub(Tip.owners(tp), from),
              Owners.major(Tip.owners(tp), from),
              Last.is(Passes.last(~mach, s, Ledgers.Where{c, Head.next(hd), 1n+p}, from), x)
            )(al)
          )(
            Later.all.c(
              Passed.all(~mach, s, Ledgers.Where{c, Head.next(hd), 1n+p}, from),
              Owners.sub(Tip.owners(tp), from),
              Owners.major(Tip.owners(tp), from),
              Last.is(Passes.last(~mach, s, Ledgers.Where{c, Head.next(hd), 1n+p}, from), x)
            )(al)
          )(
            Pass.miss(
              ~mach,
              ~s,
              ~c,
              ~rules,
              hd,
              tp,
              ok,
              p,
              r1,
              v1,
              from
            )(
              le
            )(
              Later.all.a(
                Passed.all(~mach, s, Ledgers.Where{c, Head.next(hd), 1n+p}, from),
                Owners.sub(Tip.owners(tp), from),
                Owners.major(Tip.owners(tp), from),
                Last.is(Passes.last(~mach, s, Ledgers.Where{c, Head.next(hd), 1n+p}, from), x)
              )(al)
            )(ef)
          )
        )
    case True{}:
      ef => hh => lt => le => ih => al =>
        Rounds.last(
          ~mach,
          ~s,
          ~c,
          ~rules,
          hd,
          tp,
          ok,
          r1,
          v1,
          p,
          x,
          j,
          from,
          Passes.last(~mach, s, Ledgers.Where{c, Head.next(hd), 1n+p}, from)
        )(
          {==}
        )(
          ef
        )(
          Later.all.d(
            Passed.all(~mach, s, Ledgers.Where{c, Head.next(hd), 1n+p}, from),
            Owners.sub(Tip.owners(tp), from),
            Owners.major(Tip.owners(tp), from),
            Last.is(Passes.last(~mach, s, Ledgers.Where{c, Head.next(hd), 1n+p}, from), x)
          )(al)
        )(lt)(ih)

# Rounds.same at the round r1 itself, once a voter m of the step v1 is known
def Rounds.base(
  ~mach: Machine(),
  ~s: Node<Machine.Q(mach)>,
  ~c: Ledgers.Chain,
  ~rules: Rounds.Rules(~mach, s, c),
  +hd: Head,
  +tp: Tip,
  ok: {Head.tip(~mach, s, hd) == Some{tp}: Maybe<&2, Tip>},
  +r1: Nat,
  +v1: Ledgers.Vote,
  q: String,
  x: Ledgers.Vote,
  m: Maybe<&2, String>
) -> {Round.voter(~mach, s, c, Head.next(hd), r1, Tip.owners(tp), v1) == m: Maybe<&2, String>}
  -> {
    Quorums.Quorum.has(
      ~Ledgers.Vote,
      ~Ledgers.Vote.is_eq,
      Round.ballots(~mach, s, c, Head.next(hd), r1, Tip.owners(tp)),
      v1
    )
      == True{}: Bool
  }
  -> {Cast.of(~mach, s, Ledgers.Where{c, Head.next(hd), r1}, q) == Some{x}: Maybe<&2, Ledgers.Vote>}
  -> {x == v1: Ledgers.Vote}:
  match m:
    case None{}:
      em => hh => e => Empty.absurd(
        {x == v1: Ledgers.Vote},
        Has.voter(~mach, s, c, Head.next(hd), r1, Tip.owners(tp), v1)(hh)(em)
      )
    case Some{+o}:
      em => hh => e => Rules.same(
        ~mach,
        ~s,
        ~c,
        ~rules,
        hd,
        tp,
        ok
      )(r1)(q)(o)(x)(v1)(e)(Voter.cast(~mach, s, c, Head.next(hd), r1, Tip.owners(tp), v1, o)(em))

# Rounds.same in a round after r1
def Rounds.step(
  ~mach: Machine(),
  ~s: Node<Machine.Q(mach)>,
  ~c: Ledgers.Chain,
  ~rules: Rounds.Rules(~mach, s, c),
  +hd: Head,
  +tp: Tip,
  +ok: {Head.tip(~mach, s, hd) == Some{tp}: Maybe<&2, Tip>},
  +r1: Nat,
  v1: Ledgers.Vote,
  r: Nat,
  +q: String,
  +x: Ledgers.Vote,
  j: Nat
) -> {Nat.is_eq(r1, r) == False{}: Bool}
  -> {
    Quorums.Quorum.has(
      ~Ledgers.Vote,
      ~Ledgers.Vote.is_eq,
      Round.ballots(~mach, s, c, Head.next(hd), r1, Tip.owners(tp)),
      v1
    )
      == True{}: Bool
  }
  -> {Nat.is_lt(r, 1n+j) == True{}: Bool}
  -> {Nat.is_le(r1, r) == True{}: Bool}
  -> {Cast.of(~mach, s, Ledgers.Where{c, Head.next(hd), r}, q) == Some{x}: Maybe<&2, Ledgers.Vote>}
  -> Rounds.Below(~mach, s, c, Head.next(hd), r1, v1, j)
  -> {x == v1: Ledgers.Vote}:
  match r:
    case 0n:
      ne => hh => lt => le => e => ih => Empty.absurd(
        {x == v1: Ledgers.Vote},
        Shared.Bool.false_ne_true(
          Equal.trans(
            Bool,
            False{},
            Nat.is_eq(r1, 0n),
            True{},
            Equal.sym(Bool, Nat.is_eq(r1, 0n), False{}, ne),
            Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), r1, 0n, Shared.Nat.le_zero_eq(r1)(le))
          )
        )
      )
    case 1n+(+p):
      ne => hh => lt => le => e => ih =>
        Rounds.pick(
          ~mach,
          ~s,
          ~c,
          ~rules,
          hd,
          tp,
          ok,
          r1,
          v1,
          p,
          x,
          j,
          Cast.from(~mach, s, Ledgers.Where{c, Head.next(hd), 1n+p}, q),
          Last.from(
            Passes.last(
              ~mach,
              s,
              Ledgers.Where{c, Head.next(hd), 1n+p},
              Cast.from(~mach, s, Ledgers.Where{c, Head.next(hd), 1n+p}, q)
            ),
            r1
          )
        )(
          {==}
        )(
          hh
        )(
          lt
        )(
          Shared.Nat.le_step(r1, p)(le)(ne)
        )(ih)(Rules.allow(~mach, ~s, ~c, ~rules, hd, tp, ok)(1n+p)(q)(x)(e))

# Rounds.same once it is known whether the round is r1 (b)
def Rounds.same.at(
  ~mach: Machine(),
  ~s: Node<Machine.Q(mach)>,
  ~c: Ledgers.Chain,
  ~rules: Rounds.Rules(~mach, s, c),
  +hd: Head,
  +tp: Tip,
  ok: {Head.tip(~mach, s, hd) == Some{tp}: Maybe<&2, Tip>},
  +r1: Nat,
  +v1: Ledgers.Vote,
  +r: Nat,
  +q: String,
  +x: Ledgers.Vote,
  j: Nat,
  b: Bool
) -> {Nat.is_eq(r1, r) == b: Bool}
  -> {
    Quorums.Quorum.has(
      ~Ledgers.Vote,
      ~Ledgers.Vote.is_eq,
      Round.ballots(~mach, s, c, Head.next(hd), r1, Tip.owners(tp)),
      v1
    )
      == True{}: Bool
  }
  -> {Nat.is_lt(r, 1n+j) == True{}: Bool}
  -> {Nat.is_le(r1, r) == True{}: Bool}
  -> {Cast.of(~mach, s, Ledgers.Where{c, Head.next(hd), r}, q) == Some{x}: Maybe<&2, Ledgers.Vote>}
  -> Rounds.Below(~mach, s, c, Head.next(hd), r1, v1, j)
  -> {x == v1: Ledgers.Vote}:
  match b:
    case True{}:
      eb => hh => lt => le => e => ih =>
        Rounds.base(
          ~mach,
          ~s,
          ~c,
          ~rules,
          hd,
          tp,
          ok,
          r1,
          v1,
          q,
          x,
          Round.voter(~mach, s, c, Head.next(hd), r1, Tip.owners(tp), v1)
        )(
          {==}
        )(
          hh
        )(
          Cast.moved(
            ~mach,
            s,
            c,
            Head.next(hd),
            q,
            r,
            r1,
            x,
            Equal.sym(Nat, r1, r, Shared.Nat.is_eq_sound(r1, r)(eb))
          )(e)
        )
    case False{}:
      eb => hh => lt => le => e => ih =>
        Rounds.step(~mach, ~s, ~c, ~rules, hd, tp, ok, r1, v1, r, q, x, j)(eb)(hh)(lt)(le)(e)(ih)

# each vote of a round from r1 on, below the round k, is for the step that a
# majority cast in r1
def Rounds.same(
  ~mach: Machine(),
  ~s: Node<Machine.Q(mach)>,
  ~c: Ledgers.Chain,
  ~rules: Rounds.Rules(~mach, s, c),
  +hd: Head,
  +tp: Tip,
  +ok: {Head.tip(~mach, s, hd) == Some{tp}: Maybe<&2, Tip>},
  k: Nat,
  +r1: Nat,
  +v1: Ledgers.Vote
) -> {
  Quorums.Quorum.has(
    ~Ledgers.Vote,
    ~Ledgers.Vote.is_eq,
    Round.ballots(~mach, s, c, Head.next(hd), r1, Tip.owners(tp)),
    v1
  )
    == True{}: Bool
} -> Rounds.Below(~mach, s, c, Head.next(hd), r1, v1, k):
  match k:
    case 0n:
      hh => rm => qm => vm => lt => le => e => Empty.absurd(
        {vm == v1: Ledgers.Vote},
        Shared.Nat.lt_zero(rm)(lt)
      )
    case 1n+(+j):
      +hh => +rm => qm => vm => lt => le => e =>
        Rounds.same.at(
          ~mach,
          ~s,
          ~c,
          ~rules,
          hd,
          tp,
          ok,
          r1,
          v1,
          rm,
          qm,
          vm,
          j,
          Nat.is_eq(r1, rm)
        )({==})(hh)(lt)(le)(e)(Rounds.same(~mach, ~s, ~c, ~rules, hd, tp, ok, j, r1, v1)(hh))

# Rounds.later once a voter m of the step v2 in the round r2 is known
def Rounds.later.at(
  ~mach: Machine(),
  ~s: Node<Machine.Q(mach)>,
  ~c: Ledgers.Chain,
  ~rules: Rounds.Rules(~mach, s, c),
  +hd: Head,
  +tp: Tip,
  ok: {Head.tip(~mach, s, hd) == Some{tp}: Maybe<&2, Tip>},
  r1: Nat,
  +r2: Nat,
  v1: Ledgers.Vote,
  +v2: Ledgers.Vote,
  m: Maybe<&2, String>
) -> {Round.voter(~mach, s, c, Head.next(hd), r2, Tip.owners(tp), v2) == m: Maybe<&2, String>}
  -> {Nat.is_le(r1, r2) == True{}: Bool}
  -> {
    Quorums.Quorum.has(
      ~Ledgers.Vote,
      ~Ledgers.Vote.is_eq,
      Round.ballots(~mach, s, c, Head.next(hd), r1, Tip.owners(tp)),
      v1
    )
      == True{}: Bool
  }
  -> {
    Quorums.Quorum.has(
      ~Ledgers.Vote,
      ~Ledgers.Vote.is_eq,
      Round.ballots(~mach, s, c, Head.next(hd), r2, Tip.owners(tp)),
      v2
    )
      == True{}: Bool
  }
  -> {v2 == v1: Ledgers.Vote}:
  match m:
    case None{}:
      em => le => h1 => h2 => Empty.absurd(
        {v2 == v1: Ledgers.Vote},
        Has.voter(~mach, s, c, Head.next(hd), r2, Tip.owners(tp), v2)(h2)(em)
      )
    case Some{+o}:
      em => le => h1 => h2 =>
        Rounds.same(
          ~mach,
          ~s,
          ~c,
          ~rules,
          hd,
          tp,
          ok,
          1n+r2,
          r1,
          v1
        )(
          h1
        )(
          r2
        )(
          o
        )(
          v2
        )(
          Shared.Nat.lt_succ(r2)
        )(le)(Voter.cast(~mach, s, c, Head.next(hd), r2, Tip.owners(tp), v2, o)(em))

# a round decides what an earlier round of its height decided
def Rounds.later(
  ~mach: Machine(),
  ~s: Node<Machine.Q(mach)>,
  ~c: Ledgers.Chain,
  ~rules: Rounds.Rules(~mach, s, c),
  +hd: Head,
  +tp: Tip,
  ok: {Head.tip(~mach, s, hd) == Some{tp}: Maybe<&2, Tip>},
  +r1: Nat,
  +r2: Nat,
  +v1: Ledgers.Vote,
  +v2: Ledgers.Vote
) -> {Nat.is_le(r1, r2) == True{}: Bool}
  -> {
    Ledgers.State.decide(
      ~Machine.Q(mach),
      State.ledger(~mach, s),
      Ledgers.Where{c, Head.next(hd), r1},
      Tip.owners(tp)
    )
      == Some{v1}: Maybe<&2, Ledgers.Vote>
  }
  -> {
    Ledgers.State.decide(
      ~Machine.Q(mach),
      State.ledger(~mach, s),
      Ledgers.Where{c, Head.next(hd), r2},
      Tip.owners(tp)
    )
      == Some{v2}: Maybe<&2, Ledgers.Vote>
  }
  -> {v2 == v1: Ledgers.Vote}:
  le => d1 => d2 =>
    Rounds.later.at(
      ~mach,
      ~s,
      ~c,
      ~rules,
      hd,
      tp,
      ok,
      r1,
      r2,
      v1,
      v2,
      Round.voter(~mach, s, c, Head.next(hd), r2, Tip.owners(tp), v2)
    )(
      {==}
    )(
      le
    )(
      Quorums.Quorum.major_has(
        ~Ledgers.Vote,
        ~Ledgers.Vote.is_eq,
        ~Ledgers.Vote.laws(),
        Round.ballots(~mach, s, c, Head.next(hd), r1, Tip.owners(tp)),
        v1
      )(d1)
    )(
      Quorums.Quorum.major_has(
        ~Ledgers.Vote,
        ~Ledgers.Vote.is_eq,
        ~Ledgers.Vote.laws(),
        Round.ballots(~mach, s, c, Head.next(hd), r2, Tip.owners(tp)),
        v2
      )(d2)
    )

# Rounds.one once it is known whether r1 is at most r2 (b)
def Rounds.one.at(
  ~mach: Machine(),
  ~s: Node<Machine.Q(mach)>,
  ~c: Ledgers.Chain,
  ~rules: Rounds.Rules(~mach, s, c),
  hd: Head,
  tp: Tip,
  ok: {Head.tip(~mach, s, hd) == Some{tp}: Maybe<&2, Tip>},
  +r1: Nat,
  +r2: Nat,
  v1: Ledgers.Vote,
  v2: Ledgers.Vote,
  b: Bool
) -> {Nat.is_le(r1, r2) == b: Bool}
  -> {
    Ledgers.State.decide(
      ~Machine.Q(mach),
      State.ledger(~mach, s),
      Ledgers.Where{c, Head.next(hd), r1},
      Tip.owners(tp)
    )
      == Some{v1}: Maybe<&2, Ledgers.Vote>
  }
  -> {
    Ledgers.State.decide(
      ~Machine.Q(mach),
      State.ledger(~mach, s),
      Ledgers.Where{c, Head.next(hd), r2},
      Tip.owners(tp)
    )
      == Some{v2}: Maybe<&2, Ledgers.Vote>
  }
  -> {v1 == v2: Ledgers.Vote}:
  match b:
    case True{}:
      eb => d1 => d2 => Equal.sym(
        Ledgers.Vote,
        v2,
        v1,
        Rounds.later(~mach, ~s, ~c, ~rules, hd, tp, ok, r1, r2, v1, v2)(eb)(d1)(d2)
      )
    case False{}:
      eb => d1 => d2 =>
        Rounds.later(
          ~mach,
          ~s,
          ~c,
          ~rules,
          hd,
          tp,
          ok,
          r2,
          r1,
          v2,
          v1
        )(Shared.Nat.nle_le(r1, r2)(eb))(d2)(d1)

# the rounds of a height decide one step, when the ballots follow the rules
# of rounds: a later round can only decide what an earlier round decided
def Rounds.one(
  ~mach: Machine(),
  ~s: Node<Machine.Q(mach)>,
  ~c: Ledgers.Chain,
  ~rules: Rounds.Rules(~mach, s, c)
) -> Line.One(~mach, s, c):
  +hd => +tp => +ok => +r1 => +r2 => v1 => v2 => d1 => d2 =>
    Rounds.one.at(
      ~mach,
      ~s,
      ~c,
      ~rules,
      hd,
      tp,
      ok,
      r1,
      r2,
      v1,
      v2,
      Nat.is_le(r1, r2)
    )({==})(d1)(d2)

# the rounds of each of k heights decide one step, when the ballots follow the
# rules of rounds
def Rounds.ones(
  ~mach: Machine(),
  ~s: Node<Machine.Q(mach)>,
  ~c: Ledgers.Chain,
  ~rules: Rounds.Rules(~mach, s, c),
  k: Nat
) -> Line.Ones(~mach, k, s, c):
  match k:
    case 0n:
      Unit{}
    case 1n+p:
      (Rounds.ones(~mach, ~s, ~c, ~rules, p), Rounds.one(~mach, ~s, ~c, ~rules))

# lines with the same key have the same key
def Key.same(
  c2: Ledgers.Chain,
  c: Ledgers.Chain
) -> {
  Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)) == True{}: Bool
} -> {Ledgers.Chain.key(c2) == Ledgers.Chain.key(c): List<&2, Bool>}:
  Shared.List.is_eq_sound(
    ~Bool,
    ~Shared.Bool.is_eq,
    ~Shared.Bool.laws(),
    Ledgers.Chain.key(c2),
    Ledgers.Chain.key(c)
  )

# an outcome that a line holds, it holds in a node that keeps its logs
def Chain.out.kept(
  ~mach: Machine(),
  a: Node<Machine.Q(mach)>,
  b: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  +i: Ledgers.Id,
  -o: Out,
  hk: Node.Keeps(~mach, a, b)
) -> {
  Chain.out(~mach, a, c, i) == Some{o}: Maybe<&2, Out>
} -> {Chain.out(~mach, b, c, i) == Some{o}: Maybe<&2, Out>}:
  Shared.Maybe.bind_kept(
    List<&2, U32>,
    Out,
    Line.get(~mach, a, c, Log.out(i)),
    Line.get(~mach, b, c, Log.out(i)),
    ws => Out.read(ws),
    ws => Out.read(ws),
    o,
    w => hk(c)(Log.out(i))(w),
    w => e => e
  )

# the version of a number that a line holds, it holds in a node that keeps
# its logs
def Chain.version.kept(
  ~mach: Machine(),
  a: Node<Machine.Q(mach)>,
  b: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  +n: U32,
  -x: Version,
  hk: Node.Keeps(~mach, a, b)
) -> {
  Chain.version(~mach, a, c, n) == Some{x}: Maybe<&2, Version>
} -> {Chain.version(~mach, b, c, n) == Some{x}: Maybe<&2, Version>}:
  Shared.Maybe.bind_kept(
    List<&2, U32>,
    Version,
    Line.get(~mach, a, c, Log.version(n)),
    Line.get(~mach, b, c, Log.version(n)),
    ws => Version.read(ws),
    ws => Version.read(ws),
    x,
    w => hk(c)(Log.version(n))(w),
    w => e => e
  )

# a mark that a line holds, it holds in a node that keeps its logs
def Chain.mark.kept(
  ~mach: Machine(),
  a: Node<Machine.Q(mach)>,
  b: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  +m: String,
  -v: Ledgers.Id,
  hk: Node.Keeps(~mach, a, b)
) -> {
  Chain.mark(~mach, a, c, m) == Some{v}: Maybe<&2, Ledgers.Id>
} -> {Chain.mark(~mach, b, c, m) == Some{v}: Maybe<&2, Ledgers.Id>}:
  Shared.Maybe.bind_kept(
    List<&2, U32>,
    Ledgers.Id,
    Line.get(~mach, a, c, Log.mark(m)),
    Line.get(~mach, b, c, Log.mark(m)),
    ws => Read.whole(Ledgers.Id, Ledgers.Id.code.read(ws)),
    ws => Read.whole(Ledgers.Id, Ledgers.Id.code.read(ws)),
    v,
    w => hk(c)(Log.mark(m))(w),
    w => e => e
  )

# a cell that is kept is the same cell
def Cell.kept.eq(
  ~mach: Machine(),
  c: Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>,
  mb: Maybe<&2, Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>>
) -> {
  Cells.Cell.keeps(
    ~Ledgers.Entry<Machine.Q(mach)>,
    ~Ledgers.Entry.is_eq(~Machine.Q(mach), ~Machine.same(mach)),
    Some{c},
    mb
  )
    == True{}: Bool
} -> {mb == Some{c}: Maybe<&2, Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>>}:
  match c mb:
    case Cells.One{x} y:
      Cells.Cell.keeps_value(
        ~Ledgers.Entry<Machine.Q(mach)>,
        ~Ledgers.Entry.is_eq(~Machine.Q(mach), ~Machine.same(mach)),
        ~Ledgers.Entry.laws(~Machine.Q(mach), ~Machine.same(mach), ~Machine.laws(mach)),
        x,
        y
      )
    case Cells.Many{} Some{Cells.Many{}}:
      h => {==}
    case Cells.Many{} Some{Cells.One{y}}:
      h => Empty.absurd(
        {
          Some{
            Cells.One{y}
          }
            == Some{Cells.Many{}}: Maybe<&2, Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>>
        },
        Shared.Bool.false_ne_true(h)
      )
    case Cells.Many{} None{}:
      h => Empty.absurd(
        {None{} == Some{Cells.Many{}}: Maybe<&2, Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>>},
        Shared.Bool.false_ne_true(h)
      )

# a head one height up has a tip
def Up.held(z: Head, y: Hashes.Hash) -> {Head.held(Some{Head.up(z, y)}) == True{}: Bool}:
  match z:
    case Head{r, b, n, th}:
      {==}

# Moved.held once the tip m that the step names is known
def Moved.held.at(
  z: Head,
  m: Maybe<&2, Hashes.Hash>,
  -h: Head
) -> {
  Maybe.bind(&2, Hashes.Hash, Head, m, y => Some{Head.up(z, y)}) == Some{h}: Maybe<&2, Head>
} -> {Head.held(Some{h}) == True{}: Bool}:
  match m:
    case None{}:
      e => Empty.absurd({Head.held(Some{h}) == True{}: Bool}, Shared.Maybe.none_ne_some(Head, h, e))
    case Some{y}:
      e =>
        %e: {Head.held(_) == True{}: Bool}
        Up.held(z, y)

# a head that a step moved has a tip
def Moved.held(
  z: Head,
  va: Maybe<&2, Ledgers.Vote>,
  -h: Head
) -> {Head.moved(z, va) == Some{h}: Maybe<&2, Head>} -> {Head.held(Some{h}) == True{}: Bool}:
  Moved.held.at(z, Vote.tip(va), h)

# Held.at for one more step, once the head m before it is known
def Held.at.step(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  r: Nat,
  -h: Head,
  m: Maybe<&2, Head>
) -> {
  Maybe.bind(
    &2,
    Head,
    Head,
    m,
    +x => Head.moved(x, Advance.in(~mach, s, c, x, r))
  )
    == Some{h}: Maybe<&2, Head>
} -> {Head.held(Some{h}) == True{}: Bool}:
  match m:
    case None{}:
      e => Empty.absurd({Head.held(Some{h}) == True{}: Bool}, Shared.Maybe.none_ne_some(Head, h, e))
    case Some{+z}:
      e => Moved.held(z, Advance.in(~mach, s, c, z, r), h)(e)

# a head that is some decided steps from a head with a tip has a tip
def Held.at(
  ~mach: Machine(),
  rs: List<&2, Nat>,
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  h0: Head,
  -h: Head
) -> {
  Head.held(Some{h0}) == True{}: Bool
} -> {
  Line.at(~mach, rs, s, c, h0) == Some{h}: Maybe<&2, Head>
} -> {Head.held(Some{h}) == True{}: Bool}:
  match rs:
    case Nil{}:
      t0 => e =>
        %e: {Head.held(_) == True{}: Bool}
        t0
    case Con{r, rest}:
      t0 => e => Held.at.step(~mach, s, c, r, h, Line.at(~mach, rest, s, c, h0))(e)

# a node is on its own paths
def Path.refl(~mach: Machine(), -s: Node<Machine.Q(mach)>) -> Node.On(~mach, s, s):
  c => h0 => t0 => ra => ra

# paths compose
def Path.trans(
  ~mach: Machine(),
  -a: Node<Machine.Q(mach)>,
  -b: Node<Machine.Q(mach)>,
  -d: Node<Machine.Q(mach)>,
  h1: Node.On(~mach, a, b),
  h2: Node.On(~mach, b, d)
) -> Node.On(~mach, a, d):
  +c => +h0 => +t0 => ra => h2(c)(h0)(t0)(h1(c)(h0)(t0)(ra))

# one of two nodes, each on the paths of s
def Path.when(
  ~mach: Machine(),
  b: Bool,
  -s: Node<Machine.Q(mach)>,
  -x: Node<Machine.Q(mach)>,
  -y: Node<Machine.Q(mach)>,
  hx: Node.On(~mach, s, x),
  hy: Node.On(~mach, s, y)
) -> Node.On(~mach, s, Shared.Bool.when(Node<Machine.Q(mach)>, b, u => x, u => y)):
  match b:
    case True{}:
      hx
    case False{}:
      hy

# the head of another line, after the head of the line c is set
def Head.other(
  ~mach: Machine(),
  a: Node<Machine.Q(mach)>,
  b0: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  hd: Head,
  c2: Ledgers.Chain,
  eh: {State.heads(~mach, a) == State.heads(~mach, b0): Tries.Trie<Head>},
  ebs: {Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)) == False{}: Bool}
) -> {
  Node.head_of(
    ~mach,
    a,
    c2
  )
    == Node.head_of(~mach, State.head(~mach, b0, c, hd), c2): Maybe<&2, Head>
}:
  Equal.trans(
    Maybe<&2, Head>,
    Node.head_of(~mach, a, c2),
    Node.head_of(~mach, b0, c2),
    Node.head_of(~mach, State.head(~mach, b0, c, hd), c2),
    Equal.cong(
      Tries.Trie<Head>,
      Maybe<&2, Head>,
      hs => Tries.Trie.get(Head, hs, Ledgers.Chain.key(c2)),
      State.heads(~mach, a),
      State.heads(~mach, b0),
      eh
    ),
    Equal.sym(
      Maybe<&2, Head>,
      Node.head_of(~mach, State.head(~mach, b0, c, hd), c2),
      Node.head_of(~mach, b0, c2),
      Equal.trans(
        Maybe<&2, Head>,
        Node.head_of(~mach, State.head(~mach, b0, c, hd), c2),
        Bool.pick(
          Maybe<&2, Head>,
          Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
          Some{hd},
          Node.head_of(~mach, b0, c2)
        ),
        Node.head_of(~mach, b0, c2),
        Head.of_set(~mach, b0, c, hd, c2),
        Pick.of(
          Maybe<&2, Head>,
          False{},
          Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
          Some{hd},
          Node.head_of(~mach, b0, c2),
          ebs
        )
      )
    )
  )

# the head of a line with the key of the line c, after the head of c is set
def Head.this(
  ~mach: Machine(),
  b0: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  hd: Head,
  c2: Ledgers.Chain,
  ebs: {Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)) == True{}: Bool}
) -> {Node.head_of(~mach, State.head(~mach, b0, c, hd), c2) == Some{hd}: Maybe<&2, Head>}:
  Equal.trans(
    Maybe<&2, Head>,
    Node.head_of(~mach, State.head(~mach, b0, c, hd), c2),
    Bool.pick(
      Maybe<&2, Head>,
      Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
      Some{hd},
      Node.head_of(~mach, b0, c2)
    ),
    Some{hd},
    Head.of_set(~mach, b0, c, hd, c2),
    Pick.of(
      Maybe<&2, Head>,
      True{},
      Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
      Some{hd},
      Node.head_of(~mach, b0, c2),
      ebs
    )
  )

# lines with the same key have the same head
def Head.keyed(
  ~mach: Machine(),
  a: Node<Machine.Q(mach)>,
  c2: Ledgers.Chain,
  c: Ledgers.Chain,
  ek: {Ledgers.Chain.key(c2) == Ledgers.Chain.key(c): List<&2, Bool>}
) -> {Node.head_of(~mach, a, c2) == Node.head_of(~mach, a, c): Maybe<&2, Head>}:
  Equal.cong(
    List<&2, Bool>,
    Maybe<&2, Head>,
    kk => Tries.Trie.get(Head, State.heads(~mach, a), kk),
    Ledgers.Chain.key(c2),
    Ledgers.Chain.key(c),
    ek
  )

# lines with the same key have the same decided steps
def In.key(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  c2: Ledgers.Chain,
  c: Ledgers.Chain,
  x: Head,
  r: Nat,
  ek: {Ledgers.Chain.key(c2) == Ledgers.Chain.key(c): List<&2, Bool>}
) -> {Advance.in(~mach, s, c2, x, r) == Advance.in(~mach, s, c, x, r): Maybe<&2, Ledgers.Vote>}:
  Equal.cong(
    List<&2, Bool>,
    Maybe<&2, Ledgers.Vote>,
    kk => Maybe.bind(
      &2,
      Tip,
      Ledgers.Vote,
      Head.tip(~mach, s, x),
      t => Ledgers.Bucket.decide(
        ~Machine.Q(mach),
        Ledgers.State.under(
          ~Machine.Q(mach),
          State.ledger(~mach, s),
          List.append(
            &2,
            Bool,
            List.append(&2, Bool, False{} <> True{} <> kk, Ledgers.Word.key(Head.next(x))),
            Ledgers.Round.key(r, [False{}])
          )
        ),
        Tip.owners(t)
      )
    ),
    Ledgers.Chain.key(c2),
    Ledgers.Chain.key(c),
    ek
  )

# no line with the key of c is some decided steps from a head with a tip, when
# the head of c has no tip
def Path.set.no(
  ~mach: Machine(),
  +a: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  +c2: Ledgers.Chain,
  h0: Head,
  ek: {Ledgers.Chain.key(c2) == Ledgers.Chain.key(c): List<&2, Bool>},
  nh: {Head.held(Node.head_of(~mach, a, c)) == False{}: Bool},
  t0: {Head.held(Some{h0}) == True{}: Bool},
  ra: Line.Reach(~mach, a, c2, h0)
) -> Empty:
  match ra:
    case Tuple{rs, Tuple{h, Tuple{e1, e2}}}:
      Shared.Bool.false_ne_true(
        Equal.trans(
          Bool,
          False{},
          Head.held(Node.head_of(~mach, a, c)),
          True{},
          Equal.sym(Bool, Head.held(Node.head_of(~mach, a, c)), False{}, nh),
          Equal.trans(
            Bool,
            Head.held(Node.head_of(~mach, a, c)),
            Head.held(Some{h}),
            True{},
            Equal.cong(
              Maybe<&2, Head>,
              Bool,
              Head.held,
              Node.head_of(~mach, a, c),
              Some{h},
              Equal.trans(
                Maybe<&2, Head>,
                Node.head_of(~mach, a, c),
                Node.head_of(~mach, a, c2),
                Some{h},
                Equal.sym(
                  Maybe<&2, Head>,
                  Node.head_of(~mach, a, c2),
                  Node.head_of(~mach, a, c),
                  Head.keyed(~mach, a, c2, c, ek)
                ),
                e1
              )
            ),
            Held.at(~mach, rs, a, c2, h0, h)(t0)(e2)
          )
        )
      )

# a head with no tip is not held
def Held.not(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  m: Maybe<&2, Head>,
  em: {Node.head_of(~mach, s, c) == m: Maybe<&2, Head>}
) -> {Head.held(Node.head_of(~mach, s, c)) == Head.held(m): Bool}:
  Equal.cong(Maybe<&2, Head>, Bool, Head.held, Node.head_of(~mach, s, c), m, em)

# a new ledger keeps the waiting requests
def Waiting.led(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  l: Ledgers.State(Machine.Q(mach))
) -> {
  State.waiting(
    ~mach,
    s
  )
    == State.waiting(~mach, State.led(~mach, s, l)): Tries.Trie<List<&2, Ledgers.Id>>
}:
  match s:
    case Node{old, hs, ws, ks}:
      {==}

# new keys keep the waiting requests
def Waiting.keyed(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  ks: Keys
) -> {
  State.waiting(
    ~mach,
    s
  )
    == State.waiting(~mach, State.keyed(~mach, s, ks)): Tries.Trie<List<&2, Ledgers.Id>>
}:
  match s:
    case Node{l, hs, ws, old}:
      {==}

# the waiting requests of the node m, if any, else of s
def Waiting.of(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  m: Maybe<&2, Node<Machine.Q(mach)>>
) -> Tries.Trie<List<&2, Ledgers.Id>>:
  match m:
    case None{}:
      State.waiting(~mach, s)
    case Some{s2}:
      State.waiting(~mach, s2)

# a node that is kept when b holds has the waiting requests of s, when it has
def Waiting.some.if(
  ~mach: Machine(),
  b: Bool,
  -s: Node<Machine.Q(mach)>,
  -x: Node<Machine.Q(mach)>,
  hx: {State.waiting(~mach, s) == State.waiting(~mach, x): Tries.Trie<List<&2, Ledgers.Id>>}
) -> {
  State.waiting(
    ~mach,
    s
  )
    == Waiting.of(
      ~mach,
      s,
      Shared.Maybe.when(Node<Machine.Q(mach)>, b, u => Some{x})
    ): Tries.Trie<List<&2, Ledgers.Id>>
}:
  match b:
    case True{}:
      hx
    case False{}:
      {==}

# a ballot that a node accepts keeps the waiting requests
def Accept.at.waiting(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  +b: Ledgers.Ballot,
  m: Maybe<&2, Keychain>
) -> {
  State.waiting(
    ~mach,
    s
  )
    == Waiting.of(~mach, s, Seal.accept.at(~mach, s, b, m)): Tries.Trie<List<&2, Ledgers.Id>>
}:
  match m:
    case None{}:
      {==}
    case Some{+c}:
      Waiting.some.if(
        ~mach,
        Seal.fits(c, b),
        s,
        State.keyed(
          ~mach,
          State.led(
            ~mach,
            s,
            Ledgers.State.keep(~Machine.Q(mach), ~Machine.same(mach), State.ledger(~mach, s), b)
          ),
          Keys.saw(
            Keys.set(
              State.keys(~mach, s),
              Seal.slot(Ballot.store(b), Ballot.node(b)),
              Keychain.next(c, b)
            ),
            Ballot.at(b)
          )
        ),
        Equal.trans(
          Tries.Trie<List<&2, Ledgers.Id>>,
          State.waiting(~mach, s),
          State.waiting(
            ~mach,
            State.led(
              ~mach,
              s,
              Ledgers.State.keep(~Machine.Q(mach), ~Machine.same(mach), State.ledger(~mach, s), b)
            )
          ),
          State.waiting(
            ~mach,
            State.keyed(
              ~mach,
              State.led(
                ~mach,
                s,
                Ledgers.State.keep(~Machine.Q(mach), ~Machine.same(mach), State.ledger(~mach, s), b)
              ),
              Keys.saw(
                Keys.set(
                  State.keys(~mach, s),
                  Seal.slot(Ballot.store(b), Ballot.node(b)),
                  Keychain.next(c, b)
                ),
                Ballot.at(b)
              )
            )
          ),
          Waiting.led(
            ~mach,
            s,
            Ledgers.State.keep(~Machine.Q(mach), ~Machine.same(mach), State.ledger(~mach, s), b)
          ),
          Waiting.keyed(
            ~mach,
            State.led(
              ~mach,
              s,
              Ledgers.State.keep(~Machine.Q(mach), ~Machine.same(mach), State.ledger(~mach, s), b)
            ),
            Keys.saw(
              Keys.set(
                State.keys(~mach, s),
                Seal.slot(Ballot.store(b), Ballot.node(b)),
                Keychain.next(c, b)
              ),
              Ballot.at(b)
            )
          )
        )
      )

# the ballots that a chain leads to keep the waiting requests, when each one more does
def Follow.step.waiting(
  ~mach: Machine(),
  -s: Node<Machine.Q(mach)>,
  m: Maybe<&2, Node<Machine.Q(mach)>>,
  -k: Node<Machine.Q(mach)> -> Node<Machine.Q(mach)>,
  ih: @s2: Node<
    Machine.Q(
      mach
    )> -> {
    State.waiting(~mach, s2) == State.waiting(~mach, k(s2)): Tries.Trie<List<&2, Ledgers.Id>>
  }
) -> {
  State.waiting(~mach, s) == Waiting.of(~mach, s, m): Tries.Trie<List<&2, Ledgers.Id>>
} -> {
  State.waiting(
    ~mach,
    s
  )
    == State.waiting(
      ~mach,
      Maybe.default(
        &2,
        Node<Machine.Q(mach)>,
        Maybe.bind(&2, Node<Machine.Q(mach)>, Node<Machine.Q(mach)>, m, s2 => Some{k(s2)}),
        s
      )
    ): Tries.Trie<List<&2, Ledgers.Id>>
}:
  match m:
    case None{}:
      e => {==}
    case Some{s2}:
      e => Equal.trans(
        Tries.Trie<List<&2, Ledgers.Id>>,
        State.waiting(~mach, s),
        State.waiting(~mach, s2),
        State.waiting(~mach, k(s2)),
        e,
        ih(s2)
      )

# the ballots that a chain leads to keep the waiting requests
def Follow.waiting(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  f: Nat,
  +s: Node<Machine.Q(mach)>,
  +p: Tries.Trie<Ledgers.Ballot>,
  +r: Ledgers.Id,
  +n: String,
  mb: Maybe<&2, Ledgers.Ballot>
) -> {
  State.waiting(
    ~mach,
    s
  )
    == State.waiting(
      ~mach,
      Sealed.follow(~mach, ~kern, f, s, p, r, n, mb)
    ): Tries.Trie<List<&2, Ledgers.Id>>
}:
  match f mb:
    case 0n x:
      {==}
    case 1n+g None{}:
      {==}
    case 1n+(+g) Some{+b}:
      Follow.step.waiting(
        ~mach,
        s,
        Seal.accept(~mach, ~kern, s, b),
        +s2 => Sealed.follow(~mach, ~kern, g, s2, p, r, n, Pending.next(~mach, ~kern, s2, p, r, n)),
        +s2 => Follow.waiting(~mach, ~kern, g, s2, p, r, n, Pending.next(~mach, ~kern, s2, p, r, n))
      )(
        Accept.at.waiting(~mach, s, b, Seal.chain(~mach, ~kern, s, Ballot.store(b), Ballot.node(b)))
      )

# the ballots that the chains of some ballots lead to keep the waiting requests
def Each.waiting(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +f: Nat,
  bs: List<&2, Ledgers.Ballot>,
  +p: Tries.Trie<Ledgers.Ballot>,
  +s: Node<Machine.Q(mach)>
) -> {
  State.waiting(
    ~mach,
    s
  )
    == State.waiting(
      ~mach,
      Sealed.each(~mach, ~kern, f, bs, p, s)
    ): Tries.Trie<List<&2, Ledgers.Id>>
}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, rest}:
      s1 = Sealed.follow(
        ~mach,
        ~kern,
        f,
        s,
        p,
        Ballot.store(b),
        Ballot.node(b),
        Pending.next(~mach, ~kern, s, p, Ballot.store(b), Ballot.node(b))
      )
      Equal.trans(
        Tries.Trie<List<&2, Ledgers.Id>>,
        State.waiting(~mach, s),
        State.waiting(~mach, s1),
        State.waiting(~mach, Sealed.each(~mach, ~kern, f, rest, p, s1)),
        Follow.waiting(
          ~mach,
          ~kern,
          f,
          s,
          p,
          Ballot.store(b),
          Ballot.node(b),
          Pending.next(~mach, ~kern, s, p, Ballot.store(b), Ballot.node(b))
        ),
        Each.waiting(~mach, ~kern, f, rest, p, s1)
      )

# a new head keeps the waiting requests
def Waiting.head(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  h: Head
) -> {
  State.waiting(
    ~mach,
    s
  )
    == State.waiting(~mach, State.head(~mach, s, c, h)): Tries.Trie<List<&2, Ledgers.Id>>
}:
  match s:
    case Node{l, hs, ws, ks}:
      {==}

# a first head keeps the waiting requests
def First.at.waiting(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  h: Head,
  +m: Maybe<&2, Head>
) -> {
  State.waiting(
    ~mach,
    s
  )
    == State.waiting(~mach, First.at(~mach, s, c, h, m)): Tries.Trie<List<&2, Ledgers.Id>>
}:
  match m:
    case Some{Head{r, b, n, Some{t}}}:
      {==}
    case Some{Head{r, b, n, None{}}}:
      Waiting.head(~mach, s, c, h)
    case None{}:
      Waiting.head(~mach, s, c, h)

# the first head of a store keeps the waiting requests
def Start.head.waiting(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  m: Maybe<&2, Node<Machine.Q(mach)>>,
  +c: Ledgers.Chain,
  h: Head
) -> {
  State.waiting(
    ~mach,
    s
  )
    == State.waiting(~mach, Start.head(~mach, s, m, c, h)): Tries.Trie<List<&2, Ledgers.Id>>
}:
  match m:
    case None{}:
      {==}
    case Some{+s2}:
      Equal.trans(
        Tries.Trie<List<&2, Ledgers.Id>>,
        State.waiting(~mach, s),
        State.waiting(~mach, State.led(~mach, s, State.ledger(~mach, s2))),
        State.waiting(
          ~mach,
          State.first(~mach, State.led(~mach, s, State.ledger(~mach, s2)), c, h)
        ),
        Waiting.led(~mach, s, State.ledger(~mach, s2)),
        First.at.waiting(
          ~mach,
          State.led(~mach, s, State.ledger(~mach, s2)),
          c,
          h,
          Node.head_of(~mach, State.led(~mach, s, State.ledger(~mach, s2)), c)
        )
      )

# a store that starts keeps the waiting requests, once its content m is known
def Start.with.waiting(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  +i: Ledgers.Id,
  +os: List<&2, String>,
  +m: Maybe<&2, Work<Machine.Q(mach)>>
) -> {
  State.waiting(
    ~mach,
    s
  )
    == State.waiting(~mach, Start.with(~mach, s, i, os, m)): Tries.Trie<List<&2, Ledgers.Id>>
}:
  match m:
    case None{}:
      {==}
    case Some{Work{s2, +c}}:
      Start.head.waiting(
        ~mach,
        s,
        State.put(~mach, s2, [Tip.words(Tip{c, None{}, 0, os})]),
        Ledgers.Chain{i, None{}},
        Head{i, None{}, 0, Some{Tip.hash(Tip{c, None{}, 0, os})}}
      )

# a line that a node starts to follow keeps the waiting requests
def Follow.new.waiting(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  +r: Ledgers.Id,
  +l: Maybe<&2, String>,
  +m: Maybe<&2, Head>
) -> {
  State.waiting(
    ~mach,
    s
  )
    == State.waiting(~mach, Follow.new(~mach, s, r, l, m)): Tries.Trie<List<&2, Ledgers.Id>>
}:
  match m:
    case Some{h}:
      {==}
    case None{}:
      Waiting.head(~mach, s, Line.chain(r, l), Head{r, l, 0, None{}})

# nodes with the same waiting requests have the same ones on each line
def Wait.same(
  ~mach: Machine(),
  a: Node<Machine.Q(mach)>,
  b: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  e: {State.waiting(~mach, a) == State.waiting(~mach, b): Tries.Trie<List<&2, Ledgers.Id>>}
) -> {Wait.of(~mach, a, c) == Wait.of(~mach, b, c): List<&2, Ledgers.Id>}:
  Equal.cong(
    Tries.Trie<List<&2, Ledgers.Id>>,
    List<&2, Ledgers.Id>,
    ws => Maybe.default(
      &2,
      List<&2, Ledgers.Id>,
      Tries.Trie.get(List<&2, Ledgers.Id>, ws, Ledgers.Chain.key(c)),
      []
    ),
    State.waiting(~mach, a),
    State.waiting(~mach, b),
    e
  )

# lines with the same key have the same waiting requests
def Wait.keyed(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  c2: Ledgers.Chain,
  c: Ledgers.Chain,
  ek: {Ledgers.Chain.key(c2) == Ledgers.Chain.key(c): List<&2, Bool>}
) -> {Wait.of(~mach, s, c2) == Wait.of(~mach, s, c): List<&2, Ledgers.Id>}:
  Equal.cong(
    List<&2, Bool>,
    List<&2, Ledgers.Id>,
    kk => Maybe.default(
      &2,
      List<&2, Ledgers.Id>,
      Tries.Trie.get(List<&2, Ledgers.Id>, State.waiting(~mach, s), kk),
      []
    ),
    Ledgers.Chain.key(c2),
    Ledgers.Chain.key(c),
    ek
  )

# the default of a pick is the pick of the defaults
def Wait.pick(
  +b: Bool,
  v: List<&2, Ledgers.Id>,
  m: Maybe<&2, List<&2, Ledgers.Id>>
) -> {
  Maybe.default(
    &2,
    List<&2, Ledgers.Id>,
    Bool.pick(Maybe<&2, List<&2, Ledgers.Id>>, b, Some{v}, m),
    []
  )
    == Bool.pick(
      List<&2, Ledgers.Id>,
      b,
      v,
      Maybe.default(&2, List<&2, Ledgers.Id>, m, [])
    ): List<&2, Ledgers.Id>
}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the requests that wait on a line, after some requests wait on the line c
def Wait.set.of(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  +x: Ledgers.Id,
  +r: List<&2, Ledgers.Id>,
  +c2: Ledgers.Chain
) -> {
  Wait.of(
    ~mach,
    Wait.set(~mach, s, c, x <> r),
    c2
  )
    == Bool.pick(
      List<&2, Ledgers.Id>,
      Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
      x <> r,
      Wait.of(~mach, s, c2)
    ): List<&2, Ledgers.Id>
}:
  match s:
    case Node{l, hs, +ws, ks}:
      %Equal.sym(
        Maybe<&2, List<&2, Ledgers.Id>>,
        Tries.Trie.get(
          List<&2, Ledgers.Id>,
          Tries.Trie.set(List<&2, Ledgers.Id>, ws, Ledgers.Chain.key(c), x <> r),
          Ledgers.Chain.key(c2)
        ),
        Bool.pick(
          Maybe<&2, List<&2, Ledgers.Id>>,
          Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
          Some{x <> r},
          Tries.Trie.get(List<&2, Ledgers.Id>, ws, Ledgers.Chain.key(c2))
        ),
        Tries.Trie.get_set(
          List<&2, Ledgers.Id>,
          ws,
          Ledgers.Chain.key(c),
          x <> r,
          Ledgers.Chain.key(c2)
        )
      ): {
        Maybe.default(
          &2,
          List<&2, Ledgers.Id>,
          _,
          []
        )
          == Bool.pick(
            List<&2, Ledgers.Id>,
            Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
            x <> r,
            Maybe.default(
              &2,
              List<&2, Ledgers.Id>,
              Tries.Trie.get(List<&2, Ledgers.Id>, ws, Ledgers.Chain.key(c2)),
              []
            )
          ): List<&2, Ledgers.Id>
      }
      Wait.pick(
        Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
        x <> r,
        Tries.Trie.get(List<&2, Ledgers.Id>, ws, Ledgers.Chain.key(c2))
      )

# the requests that wait on a line, after one more waits on the line c
def Wait.wait(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  j: Ledgers.Id,
  c2: Ledgers.Chain
) -> {
  Wait.of(
    ~mach,
    State.wait(~mach, s, c, j),
    c2
  )
    == Bool.pick(
      List<&2, Ledgers.Id>,
      Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
      j <> Wait.of(~mach, s, c),
      Wait.of(~mach, s, c2)
    ): List<&2, Ledgers.Id>
}:
  Wait.set.of(~mach, s, c, j, Wait.of(~mach, s, c), c2)

# Wait.keeps once it is known whether the line has the key of c (b)
def Wait.keeps.if(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  j: Ledgers.Id,
  +c2: Ledgers.Chain,
  i: Ledgers.Id,
  +b: Bool,
  eb: {Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)) == b: Bool},
  h: {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, Wait.of(~mach, s, c2), i) == True{}: Bool}
) -> {
  List.contains(
    ~Ledgers.Id,
    ~Ledgers.Id.is_eq,
    Bool.pick(
      List<&2, Ledgers.Id>,
      b,
      j <> Wait.of(~mach, s, c),
      Wait.of(~mach, s, c2)
    ),
    i
  )
    == True{}: Bool
}:
  match b:
    case True{}:
      Shared.List.contains_cons(~Ledgers.Id, ~Ledgers.Id.is_eq, j, Wait.of(~mach, s, c), i)((
          %Wait.keyed(~mach, s, c2, c, Key.same(c2, c)(eb)): {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, _, i) == True{}: Bool}
          h))
    case False{}:
      h

# a request that waits on a line waits there after one more waits on a line
def Wait.keeps(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  +j: Ledgers.Id,
  +c2: Ledgers.Chain,
  i: Ledgers.Id,
  h: {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, Wait.of(~mach, s, c2), i) == True{}: Bool}
) -> {
  List.contains(
    ~Ledgers.Id,
    ~Ledgers.Id.is_eq,
    Wait.of(~mach, State.wait(~mach, s, c, j), c2),
    i
  )
    == True{}: Bool
}:
  %Equal.sym(
    List<&2, Ledgers.Id>,
    Wait.of(~mach, State.wait(~mach, s, c, j), c2),
    Bool.pick(
      List<&2, Ledgers.Id>,
      Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
      j <> Wait.of(~mach, s, c),
      Wait.of(~mach, s, c2)
    ),
    Wait.wait(~mach, s, c, j, c2)
  ): {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, _, i) == True{}: Bool}
  Wait.keeps.if(
    ~mach,
    s,
    c,
    j,
    c2,
    i,
    Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
    {==},
    h
  )

# a request waits on its line once it waits there
def Wait.adds(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  +j: Ledgers.Id
) -> {
  List.contains(
    ~Ledgers.Id,
    ~Ledgers.Id.is_eq,
    Wait.of(~mach, State.wait(~mach, s, c, j), c),
    j
  )
    == True{}: Bool
}:
  %Equal.sym(
    List<&2, Ledgers.Id>,
    Wait.of(~mach, State.wait(~mach, s, c, j), c),
    Bool.pick(
      List<&2, Ledgers.Id>,
      Tries.Trie.same_key(Ledgers.Chain.key(c), Ledgers.Chain.key(c)),
      j <> Wait.of(~mach, s, c),
      Wait.of(~mach, s, c)
    ),
    Wait.wait(~mach, s, c, j, c)
  ): {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, _, j) == True{}: Bool}
  %Equal.sym(
    Bool,
    Tries.Trie.same_key(Ledgers.Chain.key(c), Ledgers.Chain.key(c)),
    True{},
    Shared.List.is_eq_refl(~Bool, ~Shared.Bool.is_eq, ~Shared.Bool.laws(), Ledgers.Chain.key(c))
  ): {
    List.contains(
      ~Ledgers.Id,
      ~Ledgers.Id.is_eq,
      Bool.pick(
        List<&2, Ledgers.Id>,
        _,
        j <> Wait.of(~mach, s, c),
        Wait.of(~mach, s, c)
      ),
      j
    )
      == True{}: Bool
  }
  %Equal.sym(
    Bool,
    Ledgers.Id.is_eq(j, j),
    True{},
    Ledgers.Id.is_eq_refl(j)
  ): {
    List.any.if(
      u => List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, Wait.of(~mach, s, c), j),
      _
    )
      == True{}: Bool
  }
  {==}

# one of two nodes, on each of which the request i waits on the line c2
def Contains.when(
  ~mach: Machine(),
  +b: Bool,
  -x: Node<Machine.Q(mach)>,
  -y: Node<Machine.Q(mach)>,
  -c2: Ledgers.Chain,
  -i: Ledgers.Id,
  hx: {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, Wait.of(~mach, x, c2), i) == True{}: Bool},
  hy: {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, Wait.of(~mach, y, c2), i) == True{}: Bool}
) -> {
  List.contains(
    ~Ledgers.Id,
    ~Ledgers.Id.is_eq,
    Wait.of(~mach, Shared.Bool.when(Node<Machine.Q(mach)>, b, u => x, u => y), c2),
    i
  )
    == True{}: Bool
}:
  match b:
    case True{}:
      hx
    case False{}:
      hy

# after its ledger took in what was sent, a node only grows as it takes the
# rest in
def Take.tail(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +s: Node<Machine.Q(mach)>,
  +t: Ledgers.State(Machine.Q(mach))
) -> {
  Node.grows(
    ~mach,
    State.led(
      ~mach,
      s,
      Ledgers.State.take(
        ~Machine.Q(mach),
        State.ledger(~mach, s),
        Take.clean(
          ~mach,
          Tries.Trie.values(Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>, t),
          Ledgers.State.empty(~Machine.Q(mach))
        )
      )
    ),
    Node.take(~mach, ~kern, s, t)
  )
    == True{}: Bool
}:
  +sent = Take.clean(
    ~mach,
    Tries.Trie.values(Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>, t),
    Ledgers.State.empty(~Machine.Q(mach))
  )
  l1 = Ledgers.State.take(~Machine.Q(mach), State.ledger(~mach, s), sent)
  +s1 = State.led(~mach, s, l1)
  +cs = Tries.Trie.values(Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>, sent)
  +s2 = Take.asks(~mach, ~kern, cs, State.ledger(~mach, s), s1)
  +bs = Ballots.of(
    ~mach,
    Tries.Trie.values(
      Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>,
      Ledgers.State.missing(~Machine.Q(mach), ~Machine.same(mach), t, State.ledger(~mach, s))
    )
  )
  Grows.trans(
    ~mach,
    s1,
    s2,
    Sealed.take(~mach, ~kern, bs, s2)
  )(
    Take.asks.grows(~mach, ~kern, cs, State.ledger(~mach, s), s1)
  )(Each.grows(~mach, ~kern, List.length(&2, Ledgers.Ballot, bs), bs, Pending.of(bs), s2))

# Node.fetch for the data ws itself
def Fetch.take(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +b: Node<Machine.Q(mach)>,
  +ws: List<&2, U32>
) -> {
  Ledgers.State.get(
    ~Machine.Q(mach),
    State.ledger(~mach, b),
    Ledgers.Slot.data(Hashes.Sha.hash(ws))
  )
    == None{}: Maybe<&2, Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>>
} -> {
  Ledgers.State.data(
    ~Machine.Q(mach),
    State.ledger(
      ~mach,
      Node.take(
        ~mach,
        ~kern,
        b,
        Ledgers.State.put_data(
          ~Machine.Q(mach),
          ~Machine.same(mach),
          Ledgers.State.empty(~Machine.Q(mach)),
          ws
        )
      )
    ),
    Hashes.Sha.hash(ws)
  )
    == Some{ws}: Maybe<&2, List<&2, U32>>
}:
  +t = Ledgers.State.put_data(
    ~Machine.Q(mach),
    ~Machine.same(mach),
    Ledgers.State.empty(~Machine.Q(mach)),
    ws
  )
  +l1 = Ledgers.State.take(~Machine.Q(mach), State.ledger(~mach, b), t)
  e =>
    Ledgers.State.data_grows(
      ~Machine.Q(mach),
      ~Machine.same(mach),
      ~Machine.laws(mach),
      State.ledger(~mach, State.led(~mach, b, l1)),
      State.ledger(~mach, Node.take(~mach, ~kern, b, t)),
      Hashes.Sha.hash(ws),
      ws
    )(Take.tail(~mach, ~kern, b, t))(
      %Equal.sym(Ledgers.State(Machine.Q(mach)), State.ledger(~mach, State.led(~mach, b, l1)), l1, Led.led(~mach, b, l1)): {Ledgers.State.data(~Machine.Q(mach), _, Hashes.Sha.hash(ws)) == Some{ws}: Maybe<&2, List<&2, U32>>}
      Ledgers.State.take_data(~Machine.Q(mach), ~Machine.same(mach), State.ledger(~mach, b), ws)(e))

# a store that starts keeps the logs
def Start.kept(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +s: Node<Machine.Q(mach)>,
  i: Ledgers.Id,
  +os: List<&2, Owner>
) -> Node.Keeps(~mach, s, Node.start(~mach, ~kern, s, i, os)):
  Start.with.kept(
    ~mach,
    s,
    i,
    Owner.names(os),
    Seal.firsts(~mach, ~kern, os, Some{Work{s, None{}}})
  )(Firsts.after(~mach, ~kern, s, os, Some{Work{s, None{}}})(Grows.refl(~mach, s)))

# a new request keeps the logs
def Arrive.kept(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +s: Node<Machine.Q(mach)>,
  +i: Ledgers.Id,
  a: Arrival
) -> Node.Keeps(~mach, s, Arrive.at(~mach, ~kern, s, i, a)):
  match a:
    case Arrival.Starts{os}:
      Start.kept(~mach, ~kern, s, i, os)
    case Arrival.Waits{+r, +l}:
      +s1 = Node.follow(~mach, s, r, l)
      Kept.trans(
        ~mach,
        s,
        s1,
        State.wait(~mach, s1, Line.chain(r, l), i),
        Follow.new.kept(~mach, s, r, l, Node.head_of(~mach, s, Line.chain(r, l)))({==}),
        Kept.same(
          ~mach,
          s1,
          State.wait(~mach, s1, Line.chain(r, l), i),
          Grows.to(
            ~mach,
            s1,
            s1,
            State.wait(~mach, s1, Line.chain(r, l), i),
            Led.waits(~mach, s1, Line.chain(r, l), i),
            Grows.refl(~mach, s1)
          ),
          Heads.waits(~mach, s1, Line.chain(r, l), i)
        )
      )

# the new requests among cells keep the logs
def Take.asks.kept(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  cs: List<&2, Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>>,
  +old: Ledgers.State(Machine.Q(mach)),
  +s: Node<Machine.Q(mach)>
) -> Node.Keeps(~mach, s, Take.asks(~mach, ~kern, cs, old, s)):
  match cs:
    case Nil{}:
      Kept.refl(~mach, s)
    case Con{Cells.One{Ledgers.Entry.Ask{+i, t, +q}}, rest}:
      s1 = Shared.Bool.when(
        Node<Machine.Q(mach)>,
        Maybe.is_none(
          &2,
          Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>,
          Ledgers.State.get(~Machine.Q(mach), old, Ledgers.Slot.ask(i))
        ),
        u => Node.arrive(~mach, ~kern, s, i, q),
        u => s
      )
      Kept.trans(
        ~mach,
        s,
        s1,
        Take.asks(~mach, ~kern, rest, old, s1),
        Kept.when(
          ~mach,
          Maybe.is_none(
            &2,
            Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>,
            Ledgers.State.get(~Machine.Q(mach), old, Ledgers.Slot.ask(i))
          ),
          s,
          Node.arrive(~mach, ~kern, s, i, q),
          s,
          Arrive.kept(~mach, ~kern, s, i, Machine.arrival(mach)(q)),
          Kept.refl(~mach, s)
        ),
        Take.asks.kept(~mach, ~kern, rest, old, s1)
      )
    case Con{Cells.One{Ledgers.Entry.Vote{v}}, rest}:
      Take.asks.kept(~mach, ~kern, rest, old, s)
    case Con{Cells.One{Ledgers.Entry.Data{d}}, rest}:
      Take.asks.kept(~mach, ~kern, rest, old, s)
    case Con{Cells.Many{}, rest}:
      Take.asks.kept(~mach, ~kern, rest, old, s)

# Node.take keeps the logs
def Take.kept(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +s: Node<Machine.Q(mach)>,
  +t: Ledgers.State(Machine.Q(mach))
) -> Node.Keeps(~mach, s, Node.take(~mach, ~kern, s, t)):
  +sent = Take.clean(
    ~mach,
    Tries.Trie.values(Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>, t),
    Ledgers.State.empty(~Machine.Q(mach))
  )
  +l1 = Ledgers.State.take(~Machine.Q(mach), State.ledger(~mach, s), sent)
  +s1 = State.led(~mach, s, l1)
  +cs = Tries.Trie.values(Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>, sent)
  +s2 = Take.asks(~mach, ~kern, cs, State.ledger(~mach, s), s1)
  +bs = Ballots.of(
    ~mach,
    Tries.Trie.values(
      Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>,
      Ledgers.State.missing(~Machine.Q(mach), ~Machine.same(mach), t, State.ledger(~mach, s))
    )
  )
  Kept.trans(
    ~mach,
    s,
    s1,
    Sealed.take(~mach, ~kern, bs, s2),
    Kept.same(
      ~mach,
      s,
      s1,
      Grows.led(
        ~mach,
        s,
        l1,
        Ledgers.State.take_grows(
          ~Machine.Q(mach),
          ~Machine.same(mach),
          ~Machine.laws(mach),
          State.ledger(~mach, s),
          sent
        )
      ),
      Heads.led(~mach, s, l1)
    ),
    Kept.trans(
      ~mach,
      s1,
      s2,
      Sealed.take(~mach, ~kern, bs, s2),
      Take.asks.kept(~mach, ~kern, cs, State.ledger(~mach, s), s1),
      Kept.same(
        ~mach,
        s2,
        Sealed.take(~mach, ~kern, bs, s2),
        Each.grows(~mach, ~kern, List.length(&2, Ledgers.Ballot, bs), bs, Pending.of(bs), s2),
        Each.heads(~mach, ~kern, List.length(&2, Ledgers.Ballot, bs), bs, Pending.of(bs), s2)
      )
    )
  )

# the line of a request that a node holds, a node that grew holds
def Chain.of.kept(
  ~mach: Machine(),
  +a: Node<Machine.Q(mach)>,
  b: Node<Machine.Q(mach)>,
  +i: Ledgers.Id,
  -c: Ledgers.Chain,
  g: {Node.grows(~mach, a, b) == True{}: Bool}
) -> {
  Node.chain_of(~mach, a, i) == Some{c}: Maybe<&2, Ledgers.Chain>
} -> {Node.chain_of(~mach, b, i) == Some{c}: Maybe<&2, Ledgers.Chain>}:
  Shared.Maybe.bind_kept(
    Ledgers.Asked<Machine.Q(mach)>,
    Ledgers.Chain,
    Node.asked(~mach, a, i),
    Node.asked(~mach, b, i),
    x => Some{Arrival.chain(i, Machine.arrival(mach)(Asked.ask(~mach, x)))},
    x => Some{Arrival.chain(i, Machine.arrival(mach)(Asked.ask(~mach, x)))},
    c,
    x => Ledgers.State.read_grows(
      ~Machine.Q(mach),
      ~Machine.same(mach),
      ~Machine.laws(mach),
      ~Ledgers.Asked<Machine.Q(mach)>,
      m => Ledgers.Asked.of(~Machine.Q(mach), m),
      {==},
      State.ledger(~mach, a),
      State.ledger(~mach, b),
      Ledgers.Slot.ask(i),
      x
    )(g),
    x => e => e
  )

# an outcome that a node knows, a node that grew and keeps its logs knows
def Out.kept(
  ~mach: Machine(),
  +a: Node<Machine.Q(mach)>,
  +b: Node<Machine.Q(mach)>,
  +i: Ledgers.Id,
  -o: Out,
  g: {Node.grows(~mach, a, b) == True{}: Bool},
  hk: Node.Keeps(~mach, a, b)
) -> {
  Node.out(~mach, a, i) == Some{o}: Maybe<&2, Out>
} -> {Node.out(~mach, b, i) == Some{o}: Maybe<&2, Out>}:
  Shared.Maybe.bind_kept(
    Ledgers.Chain,
    Out,
    Node.chain_of(~mach, a, i),
    Node.chain_of(~mach, b, i),
    c => Chain.out(~mach, a, c, i),
    c => Chain.out(~mach, b, c, i),
    o,
    c => Chain.of.kept(~mach, a, b, i, c, g),
    +c => Chain.out.kept(~mach, a, b, c, i, o, hk)
  )

# the version of an outcome, in a node that keeps the logs
def Out.on.kept(
  ~mach: Machine(),
  a: Node<Machine.Q(mach)>,
  b: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  o: Out,
  -x: Version,
  hk: Node.Keeps(~mach, a, b)
) -> {
  Out.on(~mach, a, c, o) == Some{x}: Maybe<&2, Version>
} -> {Out.on(~mach, b, c, o) == Some{x}: Maybe<&2, Version>}:
  match o:
    case Out.Stale{}:
      e => e
    case Out.Taken{n}:
      Chain.version.kept(~mach, a, b, c, n, x, hk)

# the version that a request made on a line, in a node that keeps the logs
def Chain.made.kept(
  ~mach: Machine(),
  +a: Node<Machine.Q(mach)>,
  +b: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  +v: Ledgers.Id,
  -x: Version,
  hk1: Node.Keeps(~mach, a, b),
  hk2: Node.Keeps(~mach, a, b)
) -> {
  Chain.made(~mach, a, c, v) == Some{x}: Maybe<&2, Version>
} -> {Chain.made(~mach, b, c, v) == Some{x}: Maybe<&2, Version>}:
  Shared.Maybe.bind_kept(
    Out,
    Version,
    Chain.out(~mach, a, c, v),
    Chain.out(~mach, b, c, v),
    o => Out.on(~mach, a, c, o),
    o => Out.on(~mach, b, c, o),
    x,
    o => Chain.out.kept(~mach, a, b, c, v, o, hk1),
    o => Out.on.kept(~mach, a, b, c, o, x, hk2)
  )

# the version that a request made, in a node that grew and keeps the logs
def Made.kept(
  ~mach: Machine(),
  +a: Node<Machine.Q(mach)>,
  +b: Node<Machine.Q(mach)>,
  +v: Ledgers.Id,
  -x: Version,
  g: {Node.grows(~mach, a, b) == True{}: Bool},
  hk1: Node.Keeps(~mach, a, b),
  hk2: Node.Keeps(~mach, a, b)
) -> {
  Node.made(~mach, a, v) == Some{x}: Maybe<&2, Version>
} -> {Node.made(~mach, b, v) == Some{x}: Maybe<&2, Version>}:
  Shared.Maybe.bind_kept(
    Ledgers.Chain,
    Version,
    Node.chain_of(~mach, a, v),
    Node.chain_of(~mach, b, v),
    +c => Chain.made(~mach, a, c, v),
    +c => Chain.made(~mach, b, c, v),
    x,
    c => Chain.of.kept(~mach, a, b, v, c, g),
    +c => Chain.made.kept(~mach, a, b, c, v, x, hk1, hk2)
  )

# a request that waits on a line waits there after a request arrives
def Arrive.waits(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +s: Node<Machine.Q(mach)>,
  +j: Ledgers.Id,
  +a: Arrival,
  +c2: Ledgers.Chain,
  i: Ledgers.Id,
  h: {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, Wait.of(~mach, s, c2), i) == True{}: Bool}
) -> {
  List.contains(
    ~Ledgers.Id,
    ~Ledgers.Id.is_eq,
    Wait.of(~mach, Arrive.at(~mach, ~kern, s, j, a), c2),
    i
  )
    == True{}: Bool
}:
  match a:
    case Arrival.Starts{os}:
      %Wait.same(
        ~mach,
        s,
        Node.start(~mach, ~kern, s, j, os),
        c2,
        Start.with.waiting(
          ~mach,
          s,
          j,
          Owner.names(os),
          Seal.firsts(~mach, ~kern, os, Some{Work{s, None{}}})
        )
      ): {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, _, i) == True{}: Bool}
      h
    case Arrival.Waits{r, l}:
      Wait.keeps(~mach, Node.follow(~mach, s, r, l), Line.chain(r, l), j, c2, i, (
          %Wait.same(~mach, s, Node.follow(~mach, s, r, l), c2, Follow.new.waiting(~mach, s, r, l, Node.head_of(~mach, s, Line.chain(r, l)))): {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, _, i) == True{}: Bool}
          h))

# a request that waits on a line waits there after more requests arrive
def Take.asks.waits(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +cs: List<&2, Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>>,
  +old: Ledgers.State(Machine.Q(mach)),
  +s: Node<Machine.Q(mach)>,
  +c2: Ledgers.Chain,
  +i: Ledgers.Id
) -> {
  List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, Wait.of(~mach, s, c2), i) == True{}: Bool
} -> {
  List.contains(
    ~Ledgers.Id,
    ~Ledgers.Id.is_eq,
    Wait.of(~mach, Take.asks(~mach, ~kern, cs, old, s), c2),
    i
  )
    == True{}: Bool
}:
  match cs:
    case Nil{}:
      h => h
    case Con{Cells.One{Ledgers.Entry.Ask{j, t, q}}, rest}:
      +h => Take.asks.waits(
        ~mach,
        ~kern,
        rest,
        old,
        Shared.Bool.when(
          Node<Machine.Q(mach)>,
          Maybe.is_none(
            &2,
            Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>,
            Ledgers.State.get(~Machine.Q(mach), old, Ledgers.Slot.ask(j))
          ),
          u => Node.arrive(~mach, ~kern, s, j, q),
          u => s
        ),
        c2,
        i
      )(
        Contains.when(
          ~mach,
          Maybe.is_none(
            &2,
            Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>,
            Ledgers.State.get(~Machine.Q(mach), old, Ledgers.Slot.ask(j))
          ),
          Node.arrive(~mach, ~kern, s, j, q),
          s,
          c2,
          i,
          Arrive.waits(~mach, ~kern, s, j, Machine.arrival(mach)(q), c2, i, h),
          h
        )
      )
    case Con{Cells.One{Ledgers.Entry.Vote{v}}, rest}:
      Take.asks.waits(~mach, ~kern, rest, old, s, c2, i)
    case Con{Cells.One{Ledgers.Entry.Data{d}}, rest}:
      Take.asks.waits(~mach, ~kern, rest, old, s, c2, i)
    case Con{Cells.Many{}, rest}:
      Take.asks.waits(~mach, ~kern, rest, old, s, c2, i)

# Node.advance only grows a node, once the head m is known
def Advance.head.grows(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  +s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  m: Maybe<&2, Head>
) -> {
  Node.grows(~mach, s, Advance.head(~mach, ~Lawful.kernel(mach, lawf), s, c, m)) == True{}: Bool
}:
  match m:
    case None{}:
      Grows.refl(~mach, s)
    case Some{+h}:
      Advance.at.grows(~mach, ~lawf, s, c, h, Head.tip(~mach, s, h))

# a pass to the next round only grows a node
def Pass.grows(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  +n: String,
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain
) -> {Node.grows(~mach, s, Node.pass(~mach, ~Lawful.kernel(mach, lawf), n, s, c)) == True{}: Bool}:
  +s1 = Pass.head(~mach, ~Lawful.kernel(mach, lawf), n, s, c, Node.head_of(~mach, s, c))
  Grows.trans(
    ~mach,
    s,
    s1,
    Node.step(~mach, ~Lawful.kernel(mach, lawf), n, s1, c)
  )(
    Pass.head.grows(~mach, ~Lawful.kernel(mach, lawf), n, s, c, Node.head_of(~mach, s, c))
  )(Step.grows(~mach, ~lawf, n, s1, c))

# the adoption of a line, if any, only grows a node
def Adopt.maybe.grows(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  n: String,
  s: Node<Machine.Q(mach)>,
  m: Maybe<&2, Ledgers.Chain>
) -> {
  Node.grows(~mach, s, Adopt.maybe(~mach, ~Lawful.kernel(mach, lawf), n, s, m)) == True{}: Bool
}:
  match m:
    case None{}:
      Grows.refl(~mach, s)
    case Some{c}:
      Adopt.at.grows(~mach, ~lawf, n, s, c)

# a node that took in a new request of e holds its slot
def Ask.held.new(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  +n: String,
  +s: Node<Machine.Q(mach)>,
  +e: Envelope,
  +q: Machine.Q(mach),
  +em: {
    Ledgers.State.get(
      ~Machine.Q(mach),
      State.ledger(~mach, s),
      Ledgers.Slot.ask(Envelope.of(e))
    )
      == None{}: Maybe<&2, Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>>
  }
) -> {
  Maybe.is_some(
    &2,
    Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>,
    Ledgers.State.get(
      ~Machine.Q(mach),
      State.ledger(~mach, Node.ask.new(~mach, ~Lawful.kernel(mach, lawf), n, s, e, q)),
      Ledgers.Slot.ask(Envelope.of(e))
    )
  )
    == True{}: Bool
}:
  +i = Envelope.of(e)
  +c = Arrival.chain(i, Machine.arrival(mach)(q))
  +k = Ledgers.Slot.ask(i)
  +en = {Ledgers.Entry.Ask{i, Envelope.time(e), q}: Ledgers.Entry<Machine.Q(mach)>}
  +l0 = Ledgers.State.put(~Machine.Q(mach), ~Machine.same(mach), State.ledger(~mach, s), k, en)
  +s0 = State.led(~mach, s, l0)
  +s1 = Node.arrive(~mach, ~Lawful.kernel(mach, lawf), s0, i, q)
  %Equal.sym(
    Maybe<&2, Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>>,
    Ledgers.State.get(~Machine.Q(mach), State.ledger(~mach, s), k),
    None{},
    em
  ): {
    Maybe.is_some(
      &2,
      Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>,
      Ledgers.State.get(
        ~Machine.Q(mach),
        State.ledger(
          ~mach,
          Node.step(
            ~mach,
            ~Lawful.kernel(mach, lawf),
            n,
            Node.arrive(
              ~mach,
              ~Lawful.kernel(mach, lawf),
              State.led(
                ~mach,
                s,
                Ledgers.State.add.of(
                  ~Machine.Q(mach),
                  ~Machine.same(mach),
                  State.ledger(~mach, s),
                  k,
                  en,
                  _
                )
              ),
              i,
              q
            ),
            c
          )
        ),
        k
      )
    )
      == True{}: Bool
  }
  Slot.held_kept(
    ~mach,
    s0,
    Node.step(~mach, ~Lawful.kernel(mach, lawf), n, s1, c),
    k,
    Grows.trans(
      ~mach,
      s0,
      s1,
      Node.step(~mach, ~Lawful.kernel(mach, lawf), n, s1, c)
    )(
      Arrive.grows(~mach, ~Lawful.kernel(mach, lawf), s0, i, Machine.arrival(mach)(q))
    )(Step.grows(~mach, ~lawf, n, s1, c))
  )(
    %Equal.sym(Ledgers.State(Machine.Q(mach)), State.ledger(~mach, s0), l0, Led.led(~mach, s, l0)): {Maybe.is_some(&2, Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>, Ledgers.State.get(~Machine.Q(mach), _, k)) == True{}: Bool}
    %Equal.sym(Maybe<&2, Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>>, Ledgers.State.get(~Machine.Q(mach), l0, k), Some{Cells.One{en}}, Ledgers.State.put_get(~Machine.Q(mach), ~Machine.same(mach), State.ledger(~mach, s), k, en)(em)): {Maybe.is_some(&2, Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>, _) == True{}: Bool}
    {==})

# a node that took in the request of e holds its slot, once the cell m of the
# slot before is known
def Ask.held.at(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  n: String,
  +s: Node<Machine.Q(mach)>,
  +e: Envelope,
  q: Machine.Q(mach),
  m: Maybe<&2, Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>>,
  em: {
    Ledgers.State.get(
      ~Machine.Q(mach),
      State.ledger(~mach, s),
      Ledgers.Slot.ask(Envelope.of(e))
    )
      == m: Maybe<&2, Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>>
  }
) -> {
  Maybe.is_some(
    &2,
    Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>,
    Ledgers.State.get(
      ~Machine.Q(mach),
      State.ledger(~mach, Node.ask.at(~mach, ~Lawful.kernel(mach, lawf), n, s, e, q, m)),
      Ledgers.Slot.ask(Envelope.of(e))
    )
  )
    == True{}: Bool
}:
  match m:
    case Some{x}:
      %Equal.sym(
        Maybe<&2, Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>>,
        Ledgers.State.get(
          ~Machine.Q(mach),
          State.ledger(~mach, s),
          Ledgers.Slot.ask(Envelope.of(e))
        ),
        Some{x},
        em
      ): {Maybe.is_some(&2, Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>, _) == True{}: Bool}
      {==}
    case None{}:
      Ask.held.new(
        ~mach,
        ~lawf,
        n,
        State.keyed(~mach, s, Keys.mark(State.keys(~mach, s), Envelope.of(e))),
        e,
        q,
        (
          %Equal.sym(Ledgers.State(Machine.Q(mach)), State.ledger(~mach, State.keyed(~mach, s, Keys.mark(State.keys(~mach, s), Envelope.of(e)))), State.ledger(~mach, s), Led.keyed(~mach, s, Keys.mark(State.keys(~mach, s), Envelope.of(e)))): {Ledgers.State.get(~Machine.Q(mach), _, Ledgers.Slot.ask(Envelope.of(e))) == None{}: Maybe<&2, Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>>}
          em)
      )

# a request that the node holds or not keeps each key of a run's log
def Asked.kept(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  r: Run<Machine.Q(mach)>,
  c: Ledgers.Chain,
  i: Ledgers.Id,
  a: Maybe<&2, Ledgers.Asked<Machine.Q(mach)>>,
  k2: List<&2, U32>,
  v: List<&2, U32>
) -> Run.Keeps(
  ~mach,
  k2,
  v,
  Some{r}
) -> Run.Keeps(~mach, k2, v, Step.asked(~mach, ~Lawful.kernel(mach, lawf), r, c, i, a)):
  match a:
    case None{}:
      hr => Unit{}
    case Some{Ledgers.Asked{t, q}}:
      Lawful.kept(mach, lawf)(r)(c)(i)(q)(k2)(v)

# a request that the log holds or not keeps each key of a run's log
def Fresh.kept(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  +r: Run<Machine.Q(mach)>,
  c: Ledgers.Chain,
  +i: Ledgers.Id,
  o: Maybe<&2, Out>,
  k2: List<&2, U32>,
  v: List<&2, U32>
) -> Run.Keeps(
  ~mach,
  k2,
  v,
  Some{r}
) -> Run.Keeps(~mach, k2, v, Step.fresh(~mach, ~Lawful.kernel(mach, lawf), r, c, i, o)):
  match o:
    case Some{x}:
      hr => hr
    case None{}:
      Asked.kept(~mach, ~lawf, r, c, i, Node.asked(~mach, Run.state(~mach, r), i), k2, v)

# the requests of a step keep each key of a run's log, other than the owners
# and the count
def All.kept(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  +c: Ledgers.Chain,
  qs: List<&2, Ledgers.Id>,
  +m: Maybe<&2, Run<Machine.Q(mach)>>,
  +k2: List<&2, U32>,
  +v: List<&2, U32>
) -> Run.Keeps(
  ~mach,
  k2,
  v,
  m
) -> Run.Keeps(~mach, k2, v, Step.all(~mach, ~Lawful.kernel(mach, lawf), c, qs, m)):
  match qs:
    case Nil{}:
      h => h
    case Con{+i, rest}:
      h => All.kept(
        ~mach,
        ~lawf,
        c,
        rest,
        Maybe.bind(
          &2,
          Run<Machine.Q(mach)>,
          Run<Machine.Q(mach)>,
          m,
          r => Step.one(~mach, ~Lawful.kernel(mach, lawf), r, c, i)
        ),
        k2,
        v
      )(
        Keeps.bind(
          ~mach,
          k2,
          v,
          m,
          r => Step.one(~mach, ~Lawful.kernel(mach, lawf), r, c, i)
        )(
          h
        )(
          +r => hr => Fresh.kept(
            ~mach,
            ~lawf,
            r,
            c,
            i,
            Line.out(~mach, Run.state(~mach, r), Run.tip(~mach, r), i),
            k2,
            v
          )(hr)
        )
      )

# a log only gains keys: a key that the log of a tip holds, other than the
# owners and the count, holds the same value after a step
def Run.kept(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  t: Tip,
  qs: List<&2, Ledgers.Id>,
  k2: List<&2, U32>,
  v: List<&2, U32>
) -> {
  Node.get(~mach, s, Tip.log(t), k2) == Some{v}: Maybe<&2, List<&2, U32>>
} -> Run.Keeps(~mach, k2, v, Step.run(~mach, ~Lawful.kernel(mach, lawf), s, c, t, qs)):
  match t:
    case Tip{c0, l, n, os}:
      h => All.kept(~mach, ~lawf, c, qs, Some{Run{s, Tip{c0, l, n, os}}}, k2, v)(h)

# a node's ballot keeps its logs
def Cast.kept(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  +n: String,
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain
) -> Node.Keeps(~mach, s, Node.cast(~mach, ~Lawful.kernel(mach, lawf), n, s, c)):
  Kept.same(
    ~mach,
    s,
    Node.cast(~mach, ~Lawful.kernel(mach, lawf), n, s, c),
    Cast.grows(~mach, ~lawf, n, s, c),
    Cast.head.heads(~mach, ~Lawful.kernel(mach, lawf), n, s, c, Node.head_of(~mach, s, c))
  )

# Node.advance keeps the logs, once the decided step m is known
def Advance.step.kept(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  h: Head,
  +t: Tip,
  m: Maybe<&2, Ledgers.Vote>
) -> {
  Node.head_of(~mach, s, c) == Some{h}: Maybe<&2, Head>
} -> {
  Head.tip(~mach, s, h) == Some{t}: Maybe<&2, Tip>
} -> Node.Keeps(~mach, s, Advance.step(~mach, ~Lawful.kernel(mach, lawf), s, c, h, t, m)):
  match h m:
    case Head{+r, +br, +next, +th} Some{Ledgers.Vote{before, +qs, after}}:
      +em => +et => Kept.when(
        ~mach,
        Root.same(before, th),
        s,
        Advance.ran(
          ~mach,
          s,
          c,
          r,
          br,
          next,
          after,
          qs,
          Step.run(~mach, ~Lawful.kernel(mach, lawf), s, c, t, qs)
        ),
        s,
        Advance.ran.kept(
          ~mach,
          s,
          c,
          r,
          br,
          next,
          after,
          qs,
          Step.run(~mach, ~Lawful.kernel(mach, lawf), s, c, t, qs),
          Head{r, br, next, th},
          t,
          em,
          et
        )(
          Run.grows(~mach, ~lawf, s, c, t, qs)
        )(+k => +v => Run.kept(~mach, ~lawf, s, c, t, qs, k, v)),
        Kept.refl(~mach, s)
      )
    case Head{r, br, next, th} None{}:
      em => et => Kept.refl(~mach, s)

# Node.advance keeps the logs, at the head h whose tip is m
def Advance.at.kept(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  +h: Head,
  m: Maybe<&2, Tip>
) -> {
  Node.head_of(~mach, s, c) == Some{h}: Maybe<&2, Head>
} -> {
  Head.tip(~mach, s, h) == m: Maybe<&2, Tip>
} -> Node.Keeps(~mach, s, Advance.at(~mach, ~Lawful.kernel(mach, lawf), s, c, h, m)):
  match m:
    case None{}:
      em => et => Kept.refl(~mach, s)
    case Some{+t}:
      em => et => Advance.step.kept(
        ~mach,
        ~lawf,
        s,
        c,
        h,
        t,
        Height.decide(
          ~mach,
          s,
          c,
          Head.next(h),
          Tip.owners(t),
          Round.seen(~mach, s, c, Head.next(h))
        )
      )(em)(et)

# Advances.kept once the head m is known
def Advances.at.kept(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  f: Nat,
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  m: Maybe<&2, Head>
) -> {
  Node.head_of(~mach, s, c) == m: Maybe<&2, Head>
} -> Node.Keeps(~mach, s, Advances.at(~mach, ~Lawful.kernel(mach, lawf), f, s, c, m)):
  match f m:
    case 0n x:
      em => Kept.refl(~mach, s)
    case 1n+p None{}:
      em => Kept.refl(~mach, s)
    case 1n+(+p) Some{+h}:
      +em =>
        +s1 = Advance.at(~mach, ~Lawful.kernel(mach, lawf), s, c, h, Head.tip(~mach, s, h))
        +m1 = Node.head_of(~mach, s1, c)
        Kept.when(
          ~mach,
          Heads.level(Some{h}, m1),
          s,
          s1,
          Advances.at(~mach, ~Lawful.kernel(mach, lawf), p, s1, c, m1),
          Advance.at.kept(~mach, ~lawf, s, c, h, Head.tip(~mach, s, h))(em)({==}),
          Kept.trans(
            ~mach,
            s,
            s1,
            Advances.at(~mach, ~Lawful.kernel(mach, lawf), p, s1, c, m1),
            Advance.at.kept(~mach, ~lawf, s, c, h, Head.tip(~mach, s, h))(em)({==}),
            Advances.at.kept(~mach, ~lawf, p, s1, c, m1)({==})
          )
        )

# a head that moves over each decided step keeps the logs
def Advances.kept(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  f: Nat,
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain
) -> Node.Keeps(~mach, s, Node.advances(~mach, ~Lawful.kernel(mach, lawf), f, s, c)):
  Advances.at.kept(~mach, ~lawf, f, s, c, Node.head_of(~mach, s, c))({==})

# what a node does at a head keeps the logs
def Step.head.kept(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  +n: String,
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain
) -> Node.Keeps(~mach, s, Step.head(~mach, ~Lawful.kernel(mach, lawf), n, s, c)):
  +s1 = Node.advances(~mach, ~Lawful.kernel(mach, lawf), 4294967295n, s, c)
  +s2 = Node.cast(~mach, ~Lawful.kernel(mach, lawf), n, s1, c)
  s3 = Node.advances(~mach, ~Lawful.kernel(mach, lawf), 4294967295n, s2, c)
  Kept.trans(
    ~mach,
    s,
    s1,
    s3,
    Advances.kept(~mach, ~lawf, 4294967295n, s, c),
    Kept.trans(
      ~mach,
      s1,
      s2,
      s3,
      Cast.kept(~mach, ~lawf, n, s1, c),
      Advances.kept(~mach, ~lawf, 4294967295n, s2, c)
    )
  )

# what a node does on a line keeps the logs
def Step.kept(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  n: String,
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain
) -> Node.Keeps(~mach, s, Node.step(~mach, ~Lawful.kernel(mach, lawf), n, s, c)):
  s1 = Node.open(~mach, s, c)
  Kept.trans(
    ~mach,
    s,
    s1,
    Step.head(~mach, ~Lawful.kernel(mach, lawf), n, s1, c),
    Open.at.kept(~mach, s, c, Node.head_of(~mach, s, c))({==}),
    Step.head.kept(~mach, ~lawf, n, s1, c)
  )

# a pass to the next round keeps the logs
def Pass.kept(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  +n: String,
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain
) -> Node.Keeps(~mach, s, Node.pass(~mach, ~Lawful.kernel(mach, lawf), n, s, c)):
  +s1 = Pass.head(~mach, ~Lawful.kernel(mach, lawf), n, s, c, Node.head_of(~mach, s, c))
  Kept.trans(
    ~mach,
    s,
    s1,
    Node.step(~mach, ~Lawful.kernel(mach, lawf), n, s1, c),
    Kept.same(
      ~mach,
      s,
      s1,
      Pass.head.grows(~mach, ~Lawful.kernel(mach, lawf), n, s, c, Node.head_of(~mach, s, c)),
      Pass.head.heads(~mach, ~Lawful.kernel(mach, lawf), n, s, c, Node.head_of(~mach, s, c))
    ),
    Step.kept(~mach, ~lawf, n, s1, c)
  )

# a new request keeps the logs
def Ask.new.kept(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  n: String,
  +s: Node<Machine.Q(mach)>,
  +e: Envelope,
  +q: Machine.Q(mach)
) -> Node.Keeps(~mach, s, Node.ask.new(~mach, ~Lawful.kernel(mach, lawf), n, s, e, q)):
  +i = Envelope.of(e)
  c = Arrival.chain(i, Machine.arrival(mach)(q))
  +l0 = Ledgers.State.ask(
    ~Machine.Q(mach),
    ~Machine.same(mach),
    State.ledger(~mach, s),
    i,
    Envelope.time(e),
    q
  )
  +s0 = State.led(~mach, s, l0)
  s1 = Node.arrive(~mach, ~Lawful.kernel(mach, lawf), s0, i, q)
  Kept.trans(
    ~mach,
    s,
    s0,
    Node.step(~mach, ~Lawful.kernel(mach, lawf), n, s1, c),
    Kept.same(
      ~mach,
      s,
      s0,
      Grows.led(
        ~mach,
        s,
        l0,
        Ledgers.State.add_grows(
          ~Machine.Q(mach),
          ~Machine.same(mach),
          ~Machine.laws(mach),
          State.ledger(~mach, s),
          Ledgers.Slot.ask(i),
          Ledgers.Entry.Ask{i, Envelope.time(e), q}
        )
      ),
      Heads.led(~mach, s, l0)
    ),
    Kept.trans(
      ~mach,
      s0,
      s1,
      Node.step(~mach, ~Lawful.kernel(mach, lawf), n, s1, c),
      Arrive.kept(~mach, ~Lawful.kernel(mach, lawf), s0, i, Machine.arrival(mach)(q)),
      Step.kept(~mach, ~lawf, n, s1, c)
    )
  )

# Node.ask_keeps once the cell m of the request's ID is known
def Ask.at.kept(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  n: String,
  +s: Node<Machine.Q(mach)>,
  +e: Envelope,
  q: Machine.Q(mach),
  m: Maybe<&2, Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>>
) -> Node.Keeps(~mach, s, Node.ask.at(~mach, ~Lawful.kernel(mach, lawf), n, s, e, q, m)):
  match m:
    case Some{x}:
      Kept.refl(~mach, s)
    case None{}:
      Kept.trans(
        ~mach,
        s,
        State.keyed(~mach, s, Keys.mark(State.keys(~mach, s), Envelope.of(e))),
        Node.ask.new(
          ~mach,
          ~Lawful.kernel(mach, lawf),
          n,
          State.keyed(~mach, s, Keys.mark(State.keys(~mach, s), Envelope.of(e))),
          e,
          q
        ),
        Kept.same(
          ~mach,
          s,
          State.keyed(~mach, s, Keys.mark(State.keys(~mach, s), Envelope.of(e))),
          Grows.to(
            ~mach,
            s,
            s,
            State.keyed(~mach, s, Keys.mark(State.keys(~mach, s), Envelope.of(e))),
            Led.keyed(~mach, s, Keys.mark(State.keys(~mach, s), Envelope.of(e))),
            Grows.refl(~mach, s)
          ),
          Heads.keyed(~mach, s, Keys.mark(State.keys(~mach, s), Envelope.of(e)))
        ),
        Ask.new.kept(
          ~mach,
          ~lawf,
          n,
          State.keyed(~mach, s, Keys.mark(State.keys(~mach, s), Envelope.of(e))),
          e,
          q
        )
      )

# Node.ask keeps the logs
def Ask.kept(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  n: String,
  +s: Node<Machine.Q(mach)>,
  +e: Envelope,
  q: Machine.Q(mach)
) -> Node.Keeps(~mach, s, Node.ask(~mach, ~Lawful.kernel(mach, lawf), n, s, e, q)):
  Ask.at.kept(
    ~mach,
    ~lawf,
    n,
    s,
    e,
    q,
    Ledgers.State.get(~Machine.Q(mach), State.ledger(~mach, s), Ledgers.Slot.ask(Envelope.of(e)))
  )

# what a node does on each of some lines keeps the logs
def Steps.kept(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  +n: String,
  cs: List<&2, Ledgers.Chain>,
  +s: Node<Machine.Q(mach)>
) -> Node.Keeps(~mach, s, Node.steps(~mach, ~Lawful.kernel(mach, lawf), n, cs, s)):
  match cs:
    case Nil{}:
      Kept.refl(~mach, s)
    case Con{+c, rest}:
      s1 = Node.step(~mach, ~Lawful.kernel(mach, lawf), n, s, c)
      Kept.trans(
        ~mach,
        s,
        s1,
        Node.steps(~mach, ~Lawful.kernel(mach, lawf), n, rest, s1),
        Step.kept(~mach, ~lawf, n, s, c),
        Steps.kept(~mach, ~lawf, n, rest, s1)
      )

# an adoption keeps the logs, once the request m is known
def Adopt.ask.kept(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  n: String,
  s: Node<Machine.Q(mach)>,
  m: Maybe<&2, Request<Machine.Q(mach)>>
) -> Node.Keeps(~mach, s, Adopt.ask(~mach, ~Lawful.kernel(mach, lawf), n, s, m)):
  match m:
    case None{}:
      Kept.refl(~mach, s)
    case Some{Request{e, q}}:
      Ask.kept(~mach, ~lawf, n, s, e, q)

# an adoption keeps the logs, once the head m of the line is known
def Adopt.head.kept(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  n: String,
  +s: Node<Machine.Q(mach)>,
  m: Maybe<&2, Head>
) -> Node.Keeps(~mach, s, Adopt.head(~mach, ~Lawful.kernel(mach, lawf), n, s, m)):
  match m:
    case None{}:
      Kept.refl(~mach, s)
    case Some{Head{r, b, next, t}}:
      Adopt.ask.kept(~mach, ~lawf, n, s, Kernel.follow(mach, Lawful.kernel(mach, lawf))(s)(r)(b))

# the adoption of a line keeps the logs
def Adopt.at.kept(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  n: String,
  +s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain
) -> Node.Keeps(~mach, s, Adopt.at(~mach, ~Lawful.kernel(mach, lawf), n, s, c)):
  Adopt.head.kept(~mach, ~lawf, n, s, Node.head_of(~mach, s, c))

# the adoption of a line, if any, keeps the logs
def Adopt.maybe.kept(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  n: String,
  s: Node<Machine.Q(mach)>,
  m: Maybe<&2, Ledgers.Chain>
) -> Node.Keeps(~mach, s, Adopt.maybe(~mach, ~Lawful.kernel(mach, lawf), n, s, m)):
  match m:
    case None{}:
      Kept.refl(~mach, s)
    case Some{c}:
      Adopt.at.kept(~mach, ~lawf, n, s, c)

# the adoption of each of some lines keeps the logs
def Adopts.kept(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  +n: String,
  cs: List<&2, Ledgers.Chain>,
  +s: Node<Machine.Q(mach)>
) -> Node.Keeps(~mach, s, Node.adopts(~mach, ~Lawful.kernel(mach, lawf), n, cs, s)):
  match cs:
    case Nil{}:
      Kept.refl(~mach, s)
    case Con{+c, rest}:
      Kept.trans(
        ~mach,
        s,
        Adopt.at(~mach, ~Lawful.kernel(mach, lawf), n, s, c),
        Node.adopts(
          ~mach,
          ~Lawful.kernel(mach, lawf),
          n,
          rest,
          Adopt.at(~mach, ~Lawful.kernel(mach, lawf), n, s, c)
        ),
        Adopt.at.kept(~mach, ~lawf, n, s, c),
        Adopts.kept(~mach, ~lawf, n, rest, Adopt.at(~mach, ~Lawful.kernel(mach, lawf), n, s, c))
      )

# more rounds of a sync, kept
def More.kept(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  f: Nat,
  +n: String,
  +cs: List<&2, Ledgers.Chain>,
  +k: Nat,
  +bs: List<&2, Ledgers.Ballot>,
  +pd: Tries.Trie<Ledgers.Ballot>,
  +s: Node<Machine.Q(mach)>
) -> Node.Keeps(~mach, s, Sync.more(~mach, ~Lawful.kernel(mach, lawf), f, n, cs, k, bs, pd, s)):
  match f:
    case 0n:
      Kept.refl(~mach, s)
    case 1n+(p):
      Kept.when(
        ~mach,
        Lines.level(
          ~mach,
          cs,
          s,
          Node.steps(
            ~mach,
            ~Lawful.kernel(mach, lawf),
            n,
            cs,
            Sealed.each(~mach, ~Lawful.kernel(mach, lawf), k, bs, pd, s)
          )
        ),
        s,
        Node.steps(
          ~mach,
          ~Lawful.kernel(mach, lawf),
          n,
          cs,
          Sealed.each(~mach, ~Lawful.kernel(mach, lawf), k, bs, pd, s)
        ),
        Sync.more(
          ~mach,
          ~Lawful.kernel(mach, lawf),
          p,
          n,
          cs,
          k,
          bs,
          pd,
          Node.steps(
            ~mach,
            ~Lawful.kernel(mach, lawf),
            n,
            cs,
            Sealed.each(~mach, ~Lawful.kernel(mach, lawf), k, bs, pd, s)
          )
        ),
        Kept.trans(
          ~mach,
          s,
          Sealed.each(~mach, ~Lawful.kernel(mach, lawf), k, bs, pd, s),
          Node.steps(
            ~mach,
            ~Lawful.kernel(mach, lawf),
            n,
            cs,
            Sealed.each(~mach, ~Lawful.kernel(mach, lawf), k, bs, pd, s)
          ),
          Kept.same(
            ~mach,
            s,
            Sealed.each(~mach, ~Lawful.kernel(mach, lawf), k, bs, pd, s),
            Each.grows(~mach, ~Lawful.kernel(mach, lawf), k, bs, pd, s),
            Each.heads(~mach, ~Lawful.kernel(mach, lawf), k, bs, pd, s)
          ),
          Steps.kept(
            ~mach,
            ~lawf,
            n,
            cs,
            Sealed.each(~mach, ~Lawful.kernel(mach, lawf), k, bs, pd, s)
          )
        ),
        Kept.trans(
          ~mach,
          s,
          Node.steps(
            ~mach,
            ~Lawful.kernel(mach, lawf),
            n,
            cs,
            Sealed.each(~mach, ~Lawful.kernel(mach, lawf), k, bs, pd, s)
          ),
          Sync.more(
            ~mach,
            ~Lawful.kernel(mach, lawf),
            p,
            n,
            cs,
            k,
            bs,
            pd,
            Node.steps(
              ~mach,
              ~Lawful.kernel(mach, lawf),
              n,
              cs,
              Sealed.each(~mach, ~Lawful.kernel(mach, lawf), k, bs, pd, s)
            )
          ),
          Kept.trans(
            ~mach,
            s,
            Sealed.each(~mach, ~Lawful.kernel(mach, lawf), k, bs, pd, s),
            Node.steps(
              ~mach,
              ~Lawful.kernel(mach, lawf),
              n,
              cs,
              Sealed.each(~mach, ~Lawful.kernel(mach, lawf), k, bs, pd, s)
            ),
            Kept.same(
              ~mach,
              s,
              Sealed.each(~mach, ~Lawful.kernel(mach, lawf), k, bs, pd, s),
              Each.grows(~mach, ~Lawful.kernel(mach, lawf), k, bs, pd, s),
              Each.heads(~mach, ~Lawful.kernel(mach, lawf), k, bs, pd, s)
            ),
            Steps.kept(
              ~mach,
              ~lawf,
              n,
              cs,
              Sealed.each(~mach, ~Lawful.kernel(mach, lawf), k, bs, pd, s)
            )
          ),
          More.kept(
            ~mach,
            ~lawf,
            p,
            n,
            cs,
            k,
            bs,
            pd,
            Node.steps(
              ~mach,
              ~Lawful.kernel(mach, lawf),
              n,
              cs,
              Sealed.each(~mach, ~Lawful.kernel(mach, lawf), k, bs, pd, s)
            )
          )
        )
      )

# a sync keeps the logs
def Sync.kept(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  +n: String,
  +s: Node<Machine.Q(mach)>,
  +t: Ledgers.State(Machine.Q(mach))
) -> Node.Keeps(~mach, s, Node.sync(~mach, ~Lawful.kernel(mach, lawf), n, s, t)):
  +s1 = Node.take(~mach, ~Lawful.kernel(mach, lawf), s, t)
  +cs = Sync.lines(~mach, s, s1, t)
  +bs = Ballots.of(
    ~mach,
    Tries.Trie.values(
      Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>,
      Ledgers.State.missing(~Machine.Q(mach), ~Machine.same(mach), t, State.ledger(~mach, s))
    )
  )
  +s2 = Node.steps(~mach, ~Lawful.kernel(mach, lawf), n, cs, s1)
  s3 = Sync.more(
    ~mach,
    ~Lawful.kernel(mach, lawf),
    List.length(&2, Ledgers.Ballot, bs),
    n,
    cs,
    List.length(&2, Ledgers.Ballot, bs),
    bs,
    Pending.of(bs),
    s2
  )
  Kept.trans(
    ~mach,
    s,
    s1,
    Node.adopts(~mach, ~Lawful.kernel(mach, lawf), n, cs, s3),
    Take.kept(~mach, ~Lawful.kernel(mach, lawf), s, t),
    Kept.trans(
      ~mach,
      s1,
      s2,
      Node.adopts(~mach, ~Lawful.kernel(mach, lawf), n, cs, s3),
      Steps.kept(~mach, ~lawf, n, cs, s1),
      Kept.trans(
        ~mach,
        s2,
        s3,
        Node.adopts(~mach, ~Lawful.kernel(mach, lawf), n, cs, s3),
        More.kept(
          ~mach,
          ~lawf,
          List.length(&2, Ledgers.Ballot, bs),
          n,
          cs,
          List.length(&2, Ledgers.Ballot, bs),
          bs,
          Pending.of(bs),
          s2
        ),
        Adopts.kept(~mach, ~lawf, n, cs, s3)
      )
    )
  )

# a request that a writer asks again at a node only grows it
def Consent.grows(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  +n: String,
  +s: Node<Machine.Q(mach)>,
  +i: Ledgers.Id,
  m: Maybe<&2, Ledgers.Chain>
) -> {
  Node.grows(~mach, s, Consent.at(~mach, ~Lawful.kernel(mach, lawf), n, s, i, m)) == True{}: Bool
}:
  match m:
    case None{}:
      Grows.refl(~mach, s)
    case Some{+c}:
      Grows.trans(
        ~mach,
        s,
        State.keyed(~mach, s, Keys.mark(State.keys(~mach, s), i)),
        Node.step(
          ~mach,
          ~Lawful.kernel(mach, lawf),
          n,
          State.keyed(~mach, s, Keys.mark(State.keys(~mach, s), i)),
          c
        )
      )(
        Grows.to(
          ~mach,
          s,
          s,
          State.keyed(~mach, s, Keys.mark(State.keys(~mach, s), i)),
          Led.keyed(~mach, s, Keys.mark(State.keys(~mach, s), i)),
          Grows.refl(~mach, s)
        )
      )(Step.grows(~mach, ~lawf, n, State.keyed(~mach, s, Keys.mark(State.keys(~mach, s), i)), c))

# a request that a writer asks again at a node keeps the logs
def Consent.kept(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  n: String,
  +s: Node<Machine.Q(mach)>,
  +i: Ledgers.Id,
  m: Maybe<&2, Ledgers.Chain>
) -> Node.Keeps(~mach, s, Consent.at(~mach, ~Lawful.kernel(mach, lawf), n, s, i, m)):
  match m:
    case None{}:
      Kept.refl(~mach, s)
    case Some{c}:
      Kept.trans(
        ~mach,
        s,
        State.keyed(~mach, s, Keys.mark(State.keys(~mach, s), i)),
        Node.step(
          ~mach,
          ~Lawful.kernel(mach, lawf),
          n,
          State.keyed(~mach, s, Keys.mark(State.keys(~mach, s), i)),
          c
        ),
        Kept.same(
          ~mach,
          s,
          State.keyed(~mach, s, Keys.mark(State.keys(~mach, s), i)),
          Grows.to(
            ~mach,
            s,
            s,
            State.keyed(~mach, s, Keys.mark(State.keys(~mach, s), i)),
            Led.keyed(~mach, s, Keys.mark(State.keys(~mach, s), i)),
            Grows.refl(~mach, s)
          ),
          Heads.keyed(~mach, s, Keys.mark(State.keys(~mach, s), i))
        ),
        Step.kept(~mach, ~lawf, n, State.keyed(~mach, s, Keys.mark(State.keys(~mach, s), i)), c)
      )

# what a node does only grows it
def Does.grows(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  +n: String,
  +s: Node<Machine.Q(mach)>,
  ev: Deed<Machine.Q(mach)>
) -> {Node.grows(~mach, s, Node.does(~mach, ~Lawful.kernel(mach, lawf), n, s, ev)) == True{}: Bool}:
  match ev:
    case Deed.Ask{+e, +q}:
      Grows.trans(
        ~mach,
        s,
        Node.ask(~mach, ~Lawful.kernel(mach, lawf), n, s, e, q),
        Adopt.at(
          ~mach,
          ~Lawful.kernel(mach, lawf),
          n,
          Node.ask(~mach, ~Lawful.kernel(mach, lawf), n, s, e, q),
          Arrival.chain(Envelope.of(e), Machine.arrival(mach)(q))
        )
      )(
        Ask.grows(~mach, ~lawf, n, s, e, q)
      )(
        Adopt.at.grows(
          ~mach,
          ~lawf,
          n,
          Node.ask(~mach, ~Lawful.kernel(mach, lawf), n, s, e, q),
          Arrival.chain(Envelope.of(e), Machine.arrival(mach)(q))
        )
      )
    case Deed.Take{t}:
      Take.grows(~mach, ~Lawful.kernel(mach, lawf), s, t)
    case Deed.Sync{t}:
      Sync.grows(~mach, ~lawf, n, s, t)
    case Deed.Keep{b}:
      Grows.keep(~mach, s, Ropes.Put.nodes(Bytes.rope(b)))
    case Deed.Consent{+i}:
      Grows.trans(
        ~mach,
        s,
        Node.consent(~mach, ~Lawful.kernel(mach, lawf), n, s, i),
        Adopt.maybe(
          ~mach,
          ~Lawful.kernel(mach, lawf),
          n,
          Node.consent(~mach, ~Lawful.kernel(mach, lawf), n, s, i),
          Node.chain_of(~mach, s, i)
        )
      )(
        Consent.grows(~mach, ~lawf, n, s, i, Node.chain_of(~mach, s, i))
      )(
        Adopt.maybe.grows(
          ~mach,
          ~lawf,
          n,
          Node.consent(~mach, ~Lawful.kernel(mach, lawf), n, s, i),
          Node.chain_of(~mach, s, i)
        )
      )
    case Deed.Pass{+c}:
      Grows.trans(
        ~mach,
        s,
        Node.pass(~mach, ~Lawful.kernel(mach, lawf), n, s, c),
        Adopt.at(
          ~mach,
          ~Lawful.kernel(mach, lawf),
          n,
          Node.pass(~mach, ~Lawful.kernel(mach, lawf), n, s, c),
          c
        )
      )(
        Pass.grows(~mach, ~lawf, n, s, c)
      )(Adopt.at.grows(~mach, ~lawf, n, Node.pass(~mach, ~Lawful.kernel(mach, lawf), n, s, c), c))

# what a node does keeps the logs
def Does.kept(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  +n: String,
  +s: Node<Machine.Q(mach)>,
  ev: Deed<Machine.Q(mach)>
) -> Node.Keeps(~mach, s, Node.does(~mach, ~Lawful.kernel(mach, lawf), n, s, ev)):
  match ev:
    case Deed.Ask{+e, +q}:
      Kept.trans(
        ~mach,
        s,
        Node.ask(~mach, ~Lawful.kernel(mach, lawf), n, s, e, q),
        Adopt.at(
          ~mach,
          ~Lawful.kernel(mach, lawf),
          n,
          Node.ask(~mach, ~Lawful.kernel(mach, lawf), n, s, e, q),
          Arrival.chain(Envelope.of(e), Machine.arrival(mach)(q))
        ),
        Ask.kept(~mach, ~lawf, n, s, e, q),
        Adopt.at.kept(
          ~mach,
          ~lawf,
          n,
          Node.ask(~mach, ~Lawful.kernel(mach, lawf), n, s, e, q),
          Arrival.chain(Envelope.of(e), Machine.arrival(mach)(q))
        )
      )
    case Deed.Take{t}:
      Take.kept(~mach, ~Lawful.kernel(mach, lawf), s, t)
    case Deed.Sync{t}:
      Sync.kept(~mach, ~lawf, n, s, t)
    case Deed.Keep{+b}:
      Kept.same(
        ~mach,
        s,
        Node.keep(~mach, s, b),
        Grows.keep(~mach, s, Ropes.Put.nodes(Bytes.rope(b))),
        Heads.led(
          ~mach,
          s,
          Ledgers.State.put_datas(
            ~Machine.Q(mach),
            ~Machine.same(mach),
            Ropes.Put.nodes(Bytes.rope(b)),
            State.ledger(~mach, s)
          )
        )
      )
    case Deed.Consent{+i}:
      Kept.trans(
        ~mach,
        s,
        Node.consent(~mach, ~Lawful.kernel(mach, lawf), n, s, i),
        Adopt.maybe(
          ~mach,
          ~Lawful.kernel(mach, lawf),
          n,
          Node.consent(~mach, ~Lawful.kernel(mach, lawf), n, s, i),
          Node.chain_of(~mach, s, i)
        ),
        Consent.kept(~mach, ~lawf, n, s, i, Node.chain_of(~mach, s, i)),
        Adopt.maybe.kept(
          ~mach,
          ~lawf,
          n,
          Node.consent(~mach, ~Lawful.kernel(mach, lawf), n, s, i),
          Node.chain_of(~mach, s, i)
        )
      )
    case Deed.Pass{+c}:
      Kept.trans(
        ~mach,
        s,
        Node.pass(~mach, ~Lawful.kernel(mach, lawf), n, s, c),
        Adopt.at(
          ~mach,
          ~Lawful.kernel(mach, lawf),
          n,
          Node.pass(~mach, ~Lawful.kernel(mach, lawf), n, s, c),
          c
        ),
        Pass.kept(~mach, ~lawf, n, s, c),
        Adopt.at.kept(~mach, ~lawf, n, Node.pass(~mach, ~Lawful.kernel(mach, lawf), n, s, c), c)
      )
    case Deed.Pass{c}:
      Pass.kept(~mach, ~lawf, n, s, c)

# a request that the node holds or not, of a run, has an outcome
def Asked.outs(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  r: Run<Machine.Q(mach)>,
  c: Ledgers.Chain,
  i: Ledgers.Id,
  +a: Maybe<&2, Ledgers.Asked<Machine.Q(mach)>>
) -> Run.Outs(~mach, Step.asked(~mach, ~Lawful.kernel(mach, lawf), r, c, i, a), i):
  match a:
    case None{}:
      Unit{}
    case Some{Ledgers.Asked{t, q}}:
      Lawful.outs(mach, lawf)(r)(c)(i)(q)

# One.outs once the outcome o that the words ws read as is known
def One.outs.read(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  +r: Run<Machine.Q(mach)>,
  c: Ledgers.Chain,
  +i: Ledgers.Id,
  ws: List<&2, U32>,
  +o: Maybe<&2, Out>,
  eg: {
    Node.get(
      ~mach,
      Run.state(~mach, r),
      Tip.log(Run.tip(~mach, r)),
      Log.out(i)
    )
      == Some{ws}: Maybe<&2, List<&2, U32>>
  }
) -> Run.Outs(~mach, Step.fresh(~mach, ~Lawful.kernel(mach, lawf), r, c, i, o), i):
  match o:
    case Some{x}:
      Outs.self(~mach, r, i, ws)(eg)
    case None{}:
      Asked.outs(~mach, ~lawf, r, c, i, Node.asked(~mach, Run.state(~mach, r), i))

# One.outs once what the log holds for the request is known (g)
def One.outs.at(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  +r: Run<Machine.Q(mach)>,
  c: Ledgers.Chain,
  +i: Ledgers.Id,
  g: Maybe<&2, List<&2, U32>>,
  eg: {
    Node.get(
      ~mach,
      Run.state(~mach, r),
      Tip.log(Run.tip(~mach, r)),
      Log.out(i)
    )
      == g: Maybe<&2, List<&2, U32>>
  }
) -> Run.Outs(
  ~mach,
  Step.fresh(
    ~mach,
    ~Lawful.kernel(mach, lawf),
    r,
    c,
    i,
    Maybe.bind(&2, List<&2, U32>, Out, g, ws => Out.read(ws))
  ),
  i
):
  match g:
    case None{}:
      Asked.outs(~mach, ~lawf, r, c, i, Node.asked(~mach, Run.state(~mach, r), i))
    case Some{+ws}:
      One.outs.read(~mach, ~lawf, r, c, i, ws, Out.read(ws), eg)

# a request has an outcome after its step
def One.outs(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  +r: Run<Machine.Q(mach)>,
  c: Ledgers.Chain,
  +i: Ledgers.Id
) -> Run.Outs(~mach, Step.one(~mach, ~Lawful.kernel(mach, lawf), r, c, i), i):
  One.outs.at(
    ~mach,
    ~lawf,
    r,
    c,
    i,
    Node.get(~mach, Run.state(~mach, r), Tip.log(Run.tip(~mach, r)), Log.out(i)),
    {==}
  )

# Outs.kept once what the log of the run holds for the request is known (g)
def Outs.kept.at(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  +c: Ledgers.Chain,
  +qs: List<&2, Ledgers.Id>,
  +r: Run<Machine.Q(mach)>,
  +i: Ledgers.Id,
  g: Maybe<&2, List<&2, U32>>,
  eg: {
    Node.get(
      ~mach,
      Run.state(~mach, r),
      Tip.log(Run.tip(~mach, r)),
      Log.out(i)
    )
      == g: Maybe<&2, List<&2, U32>>
  }
) -> {
  Maybe.is_some(&2, List<&2, U32>, g) == True{}: Bool
} -> Run.Outs(~mach, Step.all(~mach, ~Lawful.kernel(mach, lawf), c, qs, Some{r}), i):
  match g:
    case None{}:
      h => Empty.absurd(
        Run.Outs(~mach, Step.all(~mach, ~Lawful.kernel(mach, lawf), c, qs, Some{r}), i),
        Shared.Bool.false_ne_true(h)
      )
    case Some{+v}:
      h => Outs.of(
        ~mach,
        i,
        v,
        Step.all(~mach, ~Lawful.kernel(mach, lawf), c, qs, Some{r})
      )(
        All.kept(
          ~mach,
          ~lawf,
          c,
          qs,
          Some{r},
          Log.out(i),
          v
        )(Keeps.self(~mach, r, Log.out(i), v)(eg))
      )

# an outcome that a run has, it has after more requests
def Outs.kept(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  c: Ledgers.Chain,
  qs: List<&2, Ledgers.Id>,
  +m: Maybe<&2, Run<Machine.Q(mach)>>,
  +i: Ledgers.Id
) -> Run.Outs(
  ~mach,
  m,
  i
) -> Run.Outs(~mach, Step.all(~mach, ~Lawful.kernel(mach, lawf), c, qs, m), i):
  match m:
    case None{}:
      h =>
        %Equal.sym(
          Maybe<&2, Run<Machine.Q(mach)>>,
          Step.all(~mach, ~Lawful.kernel(mach, lawf), c, qs, None{}),
          None{},
          All.none(~mach, ~Lawful.kernel(mach, lawf), c, qs)
        ): Run.Outs(~mach, _, i)
        Unit{}
    case Some{Run{s, t}}:
      h => Outs.kept.at(
        ~mach,
        ~lawf,
        c,
        qs,
        Run{s, t},
        i,
        Node.get(~mach, s, Tip.log(t), Log.out(i)),
        {==}
      )(h)

# All.outs at the first request j, once it is known whether it is i
def All.outs.at(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  +c: Ledgers.Chain,
  +j: Ledgers.Id,
  rest: List<&2, Ledgers.Id>,
  +m: Maybe<&2, Run<Machine.Q(mach)>>,
  +i: Ledgers.Id,
  +same: Bool,
  es: {Ledgers.Id.is_eq(j, i) == same: Bool},
  ih: {
    List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, rest, i) == True{}: Bool
  } -> Run.Outs(
    ~mach,
    Step.all(
      ~mach,
      ~Lawful.kernel(mach, lawf),
      c,
      rest,
      Maybe.bind(
        &2,
        Run<Machine.Q(mach)>,
        Run<Machine.Q(mach)>,
        m,
        r => Step.one(~mach, ~Lawful.kernel(mach, lawf), r, c, j)
      )
    ),
    i
  )
) -> {
  List.any.if(u => List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, rest, i), same) == True{}: Bool
} -> Run.Outs(
  ~mach,
  Step.all(
    ~mach,
    ~Lawful.kernel(mach, lawf),
    c,
    rest,
    Maybe.bind(
      &2,
      Run<Machine.Q(mach)>,
      Run<Machine.Q(mach)>,
      m,
      r => Step.one(~mach, ~Lawful.kernel(mach, lawf), r, c, j)
    )
  ),
  i
):
  match same:
    case True{}:
      e => Outs.kept(
        ~mach,
        ~lawf,
        c,
        rest,
        Maybe.bind(
          &2,
          Run<Machine.Q(mach)>,
          Run<Machine.Q(mach)>,
          m,
          r => Step.one(~mach, ~Lawful.kernel(mach, lawf), r, c, j)
        ),
        i
      )(
        %Equal.sym(Ledgers.Id, j, i, Ledgers.Id.is_eq_sound(j, i)(es)): Run.Outs(~mach, Maybe.bind(&2, Run<Machine.Q(mach)>, Run<Machine.Q(mach)>, m, r => Step.one(~mach, ~Lawful.kernel(mach, lawf), r, c, _)), i)
        Outs.all(~mach, m, r => Step.one(~mach, ~Lawful.kernel(mach, lawf), r, c, i), i, r => One.outs(~mach, ~lawf, r, c, i)))
    case False{}:
      e => ih(e)

# each request of a step has an outcome after it
def All.outs(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  +c: Ledgers.Chain,
  +qs: List<&2, Ledgers.Id>,
  +m: Maybe<&2, Run<Machine.Q(mach)>>,
  +i: Ledgers.Id
) -> {
  List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, qs, i) == True{}: Bool
} -> Run.Outs(~mach, Step.all(~mach, ~Lawful.kernel(mach, lawf), c, qs, m), i):
  match qs:
    case Nil{}:
      e => Empty.absurd(Run.Outs(~mach, m, i), Shared.Bool.false_ne_true(e))
    case Con{j, rest}:
      All.outs.at(
        ~mach,
        ~lawf,
        c,
        j,
        rest,
        m,
        i,
        Ledgers.Id.is_eq(j, i),
        {==},
        All.outs(
          ~mach,
          ~lawf,
          c,
          rest,
          Maybe.bind(
            &2,
            Run<Machine.Q(mach)>,
            Run<Machine.Q(mach)>,
            m,
            r => Step.one(~mach, ~Lawful.kernel(mach, lawf), r, c, j)
          ),
          i
        )
      )

# a node fetches on demand: a node b that lacks the data of the hash h holds
# it after it takes in what a node a that holds it serves
law Node.fetch:
  for ~mach: Machine()
  for ~kern: Kernel(mach)
  for +a: Node<Machine.Q(mach)>
  for b: Node<Machine.Q(mach)>
  for +h: Hashes.Hash
  for ws: List<&2, U32>
  {
    Ledgers.State.data(
      ~Machine.Q(mach),
      State.ledger(~mach, a),
      h
    )
      == Some{ws}: Maybe<&2, List<&2, U32>>
  }
    -> {
      Ledgers.State.get(
        ~Machine.Q(mach),
        State.ledger(~mach, b),
        Ledgers.Slot.data(h)
      )
        == None{}: Maybe<&2, Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>>
    }
    -> {
      Ledgers.State.data(
        ~Machine.Q(mach),
        State.ledger(~mach, Node.take(~mach, ~kern, b, Node.serve(~mach, a, [h]))),
        h
      )
        == Some{ws}: Maybe<&2, List<&2, U32>>
    }

def Node.fetch(mach, kern, a, b, h, ws):
  +ea => eb =>
    %Equal.sym(
      Maybe<&2, List<&2, U32>>,
      Ledgers.State.data(~Machine.Q(mach), State.ledger(~mach, a), h),
      Some{ws},
      ea
    ): {
      Ledgers.State.data(
        ~Machine.Q(mach),
        State.ledger(
          ~mach,
          Node.take(~mach, ~kern, b, Serve.put(~mach, _, Ledgers.State.empty(~Machine.Q(mach))))
        ),
        h
      )
        == Some{ws}: Maybe<&2, List<&2, U32>>
    }
    %Ledgers.State.data_hash(
      ~Machine.Q(mach),
      State.ledger(~mach, a),
      h,
      ws
    )(
      ea
    ): {
      Ledgers.State.data(
        ~Machine.Q(mach),
        State.ledger(
          ~mach,
          Node.take(
            ~mach,
            ~kern,
            b,
            Ledgers.State.put_data(
              ~Machine.Q(mach),
              ~Machine.same(mach),
              Ledgers.State.empty(~Machine.Q(mach)),
              ws
            )
          )
        ),
        _
      )
        == Some{ws}: Maybe<&2, List<&2, U32>>
    }
    Fetch.take(~mach, ~kern, b, ws)(
      %Equal.sym(Hashes.Hash, Hashes.Sha.hash(ws), h, Ledgers.State.data_hash(~Machine.Q(mach), State.ledger(~mach, a), h, ws)(ea)): {Ledgers.State.get(~Machine.Q(mach), State.ledger(~mach, b), Ledgers.Slot.data(_)) == None{}: Maybe<&2, Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>>}
      eb)

# a change counts once on a node, however often it is asked: a node that took
# a request in changes nothing when its ID is asked again (across nodes: a
# node takes a request that it holds no second time, Node.take, and a step
# skips a request that its log holds, Step.fresh)
law Node.ask_once:
  for ~mach: Machine()
  for ~lawf: Lawful(mach)
  for +n: String
  for m: String
  for +s: Node<Machine.Q(mach)>
  for +e: Envelope
  for +q: Machine.Q(mach)
  for +e2: Envelope
  for q2: Machine.Q(mach)
  {Envelope.of(e2) == Envelope.of(e): Ledgers.Id}
    -> {
      Node.ask(
        ~mach,
        ~Lawful.kernel(mach, lawf),
        m,
        Node.ask(~mach, ~Lawful.kernel(mach, lawf), n, s, e, q),
        e2,
        q2
      )
        == Node.ask(~mach, ~Lawful.kernel(mach, lawf), n, s, e, q): Node<Machine.Q(mach)>
    }

def Node.ask_once(mach, lawf, n, m, s, e, q, e2, q2):
  h =>
    +a = Node.ask(~mach, ~Lawful.kernel(mach, lawf), n, s, e, q)
    Ask.once.at(
      ~mach,
      ~Lawful.kernel(mach, lawf),
      m,
      a,
      e2,
      q2,
      Ledgers.State.get(~Machine.Q(mach), State.ledger(~mach, a), Ledgers.Slot.ask(Envelope.of(e2)))
    )(
      %Equal.sym(Ledgers.Id, Envelope.of(e2), Envelope.of(e), h): {Maybe.is_some(&2, Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>, Ledgers.State.get(~Machine.Q(mach), State.ledger(~mach, a), Ledgers.Slot.ask(_))) == True{}: Bool}
      Ask.held.at(~mach, ~lawf, n, s, e, q, Ledgers.State.get(~Machine.Q(mach), State.ledger(~mach, s), Ledgers.Slot.ask(Envelope.of(e))), {==}))

# a node only grows, whatever it does
law Node.after_grows:
  for ~mach: Machine()
  for ~lawf: Lawful(mach)
  for +n: String
  for +evs: List<&2, Deed<Machine.Q(mach)>>
  for +s: Node<Machine.Q(mach)>
  {Node.grows(~mach, s, Node.after(~mach, ~Lawful.kernel(mach, lawf), n, evs, s)) == True{}: Bool}

def Node.after_grows(mach, lawf, n, evs, s):
  match evs:
    case Nil{}:
      Grows.refl(~mach, s)
    case Con{+ev, +rest}:
      +s1 = Node.does(~mach, ~Lawful.kernel(mach, lawf), n, s, ev)
      Grows.trans(
        ~mach,
        s,
        s1,
        Node.after(~mach, ~Lawful.kernel(mach, lawf), n, rest, s1)
      )(Does.grows(~mach, ~lawf, n, s, ev))(Node.after_grows(~mach, ~lawf, n, rest, s1))

# a log only gains keys: what the log of a line holds, it holds for good,
# whatever the node does next
law Node.after_keeps:
  for ~mach: Machine()
  for ~lawf: Lawful(mach)
  for +n: String
  for +evs: List<&2, Deed<Machine.Q(mach)>>
  for +s: Node<Machine.Q(mach)>
  Node.Keeps(~mach, s, Node.after(~mach, ~Lawful.kernel(mach, lawf), n, evs, s))

def Node.after_keeps(mach, lawf, n, evs, s):
  match evs:
    case Nil{}:
      Kept.refl(~mach, s)
    case Con{+ev, rest}:
      s1 = Node.does(~mach, ~Lawful.kernel(mach, lawf), n, s, ev)
      Kept.trans(
        ~mach,
        s,
        s1,
        Node.after(~mach, ~Lawful.kernel(mach, lawf), n, rest, s1),
        Does.kept(~mach, ~lawf, n, s, ev),
        Node.after_keeps(~mach, ~lawf, n, rest, s1)
      )

# a request waits until its line gives it an outcome. A step gives each of
# its requests an outcome
law Step.run_outs:
  for ~mach: Machine()
  for ~lawf: Lawful(mach)
  for s: Node<Machine.Q(mach)>
  for c: Ledgers.Chain
  for t: Tip
  for qs: List<&2, Ledgers.Id>
  for i: Ledgers.Id
  {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, qs, i) == True{}: Bool}
    -> Run.Outs(~mach, Step.run(~mach, ~Lawful.kernel(mach, lawf), s, c, t, qs), i)

def Step.run_outs(mach, lawf, s, c, t, qs, i):
  All.outs(~mach, ~lawf, c, qs, Some{Run{s, t}}, i)

# and a head that moves over a step takes only the requests of the step off
# the requests that wait (State.moved, the one place that takes any off)
law Wait.left_keeps:
  for +ws: List<&2, Ledgers.Id>
  for +done: Tries.Trie<Unit>
  for +i: Ledgers.Id
  {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, ws, i) == True{}: Bool}
    -> {Tries.Trie.has(Unit, done, Ledgers.Id.key(i)) == False{}: Bool}
    -> {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, Wait.left(ws, done), i) == True{}: Bool}

def Wait.left_keeps(ws, done, i):
  match ws:
    case Nil{}:
      e => hd => e
    case Con{j, rs}:
      e => +hd => Left.keeps.at(
        j,
        Wait.left(rs, done),
        rs,
        done,
        i,
        Ledgers.Id.is_eq(j, i),
        Tries.Trie.has(Unit, done, Ledgers.Id.key(j)),
        {==},
        {==},
        hd,
        e2 => Wait.left_keeps(rs, done, i)(e2)(hd)
      )(e)

# a node copies only a vote that the rules of rounds allow: when it plans to
# cast for the vote of the proposer, the passes that the vote names allow it
law Plan.follow_allowed:
  for ~mach: Machine()
  for ~kern: Kernel(mach)
  for +s: Node<Machine.Q(mach)>
  for c: Ledgers.Chain
  for w: Ledgers.Where
  for t: Tip
  for th: Maybe<&2, Hashes.Hash>
  for os: List<&2, String>
  for +v: Ledgers.Vote
  for +from: List<&2, String>
  {
    Maybe.is_some(
      &2,
      Run<Machine.Q(mach)>,
      Plan.run(
        ~mach,
        Plan.follow(~mach, ~kern, s, c, w, t, th, os, Some{Ledgers.Act.Vote{v, from}})
      )
    )
      == True{}: Bool
  }
    -> {Vote.allowed(~mach, s, w, os, v, from) == True{}: Bool}

def Plan.follow_allowed(mach, kern, s, c, w, t, th, os, v, from):
  Follow.allowed.at(~mach, ~kern, s, c, t, th, v, from, Vote.allowed(~mach, s, w, os, v, from))

# Seals
# -----
# a node keeps only ballots that it checked: a ballot that it accepts is the
# next of its node's chain in its store, and the key of that chain signs it
law Seal.accept_fits:
  for ~mach: Machine()
  for ~kern: Kernel(mach)
  for s: Node<Machine.Q(mach)>
  for b: Ledgers.Ballot
  for c: Keychain
  for s2: Node<Machine.Q(mach)>
  {Seal.chain(~mach, ~kern, s, Ballot.store(b), Ballot.node(b)) == Some{c}: Maybe<&2, Keychain>}
    -> {Seal.accept(~mach, ~kern, s, b) == Some{s2}: Maybe<&2, Node<Machine.Q(mach)>>}
    -> {Seal.fits(c, b) == True{}: Bool}

def Seal.accept_fits(mach, kern, s, b, c, s2):
  ec => ea => Accept.fits.if(
    ~mach,
    Seal.fits(c, b),
    State.keyed(
      ~mach,
      State.led(
        ~mach,
        s,
        Ledgers.State.keep(~Machine.Q(mach), ~Machine.same(mach), State.ledger(~mach, s), b)
      ),
      Keys.saw(
        Keys.set(
          State.keys(~mach, s),
          Seal.slot(Ballot.store(b), Ballot.node(b)),
          Keychain.next(c, b)
        ),
        Ballot.at(b)
      )
    ),
    s2
  )(
    %ec: {Seal.accept.at(~mach, s, b, _) == Some{s2}: Maybe<&2, Node<Machine.Q(mach)>>}
    ea)

# a ballot that a node seals with the secret of its chain's key fits the chain.
# (That no other node can make one is the assumption of Seals: a hash has no
# known second input.)
law Seal.fits_own:
  for +seed: Hashes.Hash
  for +x: Ledgers.Signed
  for +last: Maybe<&2, Ledgers.Where>
  for +k: Hashes.Hash
  for n: U32
  for f: Hashes.Hash
  {
    Seal.fits(
      Keychain{n, last, Seals.Seal.public(seed), f},
      Ledgers.Ballot.make(seed, x, last, k)
    )
      == True{}: Bool
  }

def Seal.fits_own(seed, x, last, k, n, f):
  Shared.List.all.if_both(
    Prev.same(last, last),
    u => Ledgers.Ballot.sealed(Seals.Seal.public(seed), Ledgers.Ballot.make(seed, x, last, k))
  )(Prev.refl(last))(Ledgers.Ballot.sealed_make(seed, x, last, k))

# Histories
# ---------
# the decided steps of a line stay as a node grows: a head that is some
# decided steps from a head h is so in any node that keeps every cell
law Line.at_grows:
  for ~mach: Machine()
  for +rs: List<&2, Nat>
  for +a: Node<Machine.Q(mach)>
  for +u: Node<Machine.Q(mach)>
  for +c: Ledgers.Chain
  for +h: Head
  for x: Head
  {Node.grows(~mach, a, u) == True{}: Bool}
    -> {Line.at(~mach, rs, a, c, h) == Some{x}: Maybe<&2, Head>}
    -> {Line.at(~mach, rs, u, c, h) == Some{x}: Maybe<&2, Head>}

def Line.at_grows(mach, rs, a, u, c, h, x):
  match rs:
    case Nil{}:
      g => e => e
    case Con{r, +rest}:
      +g => Shared.Maybe.bind_kept(
        Head,
        Head,
        Line.at(~mach, rest, a, c, h),
        Line.at(~mach, rest, u, c, h),
        +z => Head.moved(z, Advance.in(~mach, a, c, z, r)),
        +z => Head.moved(z, Advance.in(~mach, u, c, z, r)),
        x,
        +z => Line.at_grows(~mach, rest, a, u, c, h, z)(g),
        +z => Moved.grows(~mach, a, u, c, z, x, r, g)
      )

# a majority decides, in sequence: a head moves only over a step that the
# owners in its tip decided next, in some round
law Node.advance_at:
  for ~mach: Machine()
  for ~kern: Kernel(mach)
  for +s: Node<Machine.Q(mach)>
  for +c: Ledgers.Chain
  for +h: Head
  {Node.head_of(~mach, s, c) == Some{h}: Maybe<&2, Head>}
    -> {
      Heads.level(
        Some{h},
        Node.head_of(~mach, Node.advance(~mach, ~kern, s, c), c)
      )
        == False{}: Bool
    }
    -> Exists(
      Nat,
      q => {
        Line.at(
          ~mach,
          [q],
          s,
          c,
          h
        )
          == Node.head_of(~mach, Node.advance(~mach, ~kern, s, c), c): Maybe<&2, Head>
      }
    )

def Node.advance_at(mach, kern, s, c, h):
  +eh => +hl =>
    %Equal.sym(
      Maybe<&2, Head>,
      Node.head_of(~mach, Node.advance(~mach, ~kern, s, c), c),
      Some{Head.step(h, Advance.vote(~mach, s, c, h))},
      Advance.decided(~mach, ~kern, s, c, h)(eh)(hl)
    ): Exists(Nat, q => {Line.at(~mach, [q], s, c, h) == _: Maybe<&2, Head>})
    Advance.at.one(~mach, s, c, h, Advance.vote(~mach, s, c, h))({==})(
      %Advance.decided(~mach, ~kern, s, c, h)(eh)(hl): {Heads.level(Some{h}, _) == False{}: Bool}
      hl)

# Rounds
# ------
# Two rounds of one height decide the same step (Rounds.one). A majority
# cast the step v1 in the round r1. A vote of a later round names a majority
# that passed to it; one of them cast v1 in r1 (two majorities share a node),
# and its pass names a vote of r1 or later. So the vote is the last vote of a
# round from r1 on, which is v1 by the same argument, by induction on the
# round.
# one history: two nodes whose ledgers do not clash (one node u keeps every
# cell of both, and the ballots that u holds on the line follow the rules of
# rounds), the same number of decided steps from the same head of a line, are
# at the same head, whatever the round of each step
law Line.at_agrees:
  for ~mach: Machine()
  for ~u: Node<Machine.Q(mach)>
  for ~c: Ledgers.Chain
  for ~rules: Rounds.Rules(~mach, u, c)
  for +rs1: List<&2, Nat>
  for +rs2: List<&2, Nat>
  for a: Node<Machine.Q(mach)>
  for b: Node<Machine.Q(mach)>
  for +h: Head
  for +x: Head
  for +y: Head
  {Node.grows(~mach, a, u) == True{}: Bool}
    -> {Node.grows(~mach, b, u) == True{}: Bool}
    -> {List.length(&2, Nat, rs1) == List.length(&2, Nat, rs2): Nat}
    -> {Line.at(~mach, rs1, a, c, h) == Some{x}: Maybe<&2, Head>}
    -> {Line.at(~mach, rs2, b, c, h) == Some{y}: Maybe<&2, Head>}
    -> {x == y: Head}

def Line.at_agrees(mach, u, c, rules, rs1, rs2, a, b, h, x, y):
  ga => gb => el => ea => eb =>
    At.same(
      ~mach,
      rs1,
      rs2,
      u,
      c,
      h,
      x,
      y
    )(
      Rounds.ones(~mach, ~u, ~c, ~rules, List.length(&2, Nat, rs1))
    )(
      el
    )(
      Line.at_grows(~mach, rs1, a, u, c, h, x)(ga)(ea)
    )(Line.at_grows(~mach, rs2, b, u, c, h, y)(gb)(eb))

# every part is kept by enough nodes: a node that casts for a step keeps each
# new part of the step (what its own run of the step put: the node of the run
# is s2), so a majority of the owners holds each part of a decided step; and a
# node only grows (Node.after_grows)
law Cast.put_keeps:
  for ~mach: Machine()
  for ~kern: Kernel(mach)
  for +n: String
  for +w: Ledgers.Where
  for th: Maybe<&2, Hashes.Hash>
  for qs: List<&2, Ledgers.Id>
  for from: List<&2, String>
  for +s2: Node<Machine.Q(mach)>
  for +t2: Tip
  for +s: Node<Machine.Q(mach)>
  for +s3: Node<Machine.Q(mach)>
  {State.put(~mach, s2, [Tip.words(t2)]) == Some{s3}: Maybe<&2, Node<Machine.Q(mach)>>}
    -> {
      Node.grows(
        ~mach,
        s2,
        Cast.put(~mach, ~kern, n, w, th, qs, from, Some{Run{s2, t2}}, s)
      )
        == True{}: Bool
    }

def Cast.put_keeps(mach, kern, n, w, th, qs, from, s2, t2, s, s3):
  +s4 = State.led(~mach, s, State.ledger(~mach, s3))
  +a0 = {Ledgers.Act.Vote{Ledgers.Vote{th, qs, Some{Tip.hash(t2)}}, from}: Ledgers.Act}
  +e =>
    %Equal.sym(
      Maybe<&2, Node<Machine.Q(mach)>>,
      State.put(~mach, s2, [Tip.words(t2)]),
      Some{s3},
      e
    ): {Node.grows(~mach, s2, Cast.vote(~mach, ~kern, s, _, w, n, a0)) == True{}: Bool}
    Grows.trans(
      ~mach,
      s2,
      s4,
      Cast.seal(~mach, ~kern, s4, w, n, a0, Seal.chain(~mach, ~kern, s4, Where.store(w), n))
    )(
      Grows.to(
        ~mach,
        s2,
        s3,
        s4,
        Led.led(~mach, s, State.ledger(~mach, s3)),
        Put.grew(~mach, s2, [Tip.words(t2)], s3, e)
      )
    )(Cast.seal.grows(~mach, ~kern, s4, w, n, a0, Seal.chain(~mach, ~kern, s4, Where.store(w), n)))

# and it holds the tip that it casts for
law Cast.put_tip:
  for ~mach: Machine()
  for ~kern: Kernel(mach)
  for +n: String
  for +w: Ledgers.Where
  for th: Maybe<&2, Hashes.Hash>
  for qs: List<&2, Ledgers.Id>
  for from: List<&2, String>
  for s2: Node<Machine.Q(mach)>
  for +t2: Tip
  for +s: Node<Machine.Q(mach)>
  for +s3: Node<Machine.Q(mach)>
  {State.put(~mach, s2, [Tip.words(t2)]) == Some{s3}: Maybe<&2, Node<Machine.Q(mach)>>}
    -> {
      Tip.at(
        ~mach,
        Cast.put(~mach, ~kern, n, w, th, qs, from, Some{Run{s2, t2}}, s),
        Tip.hash(t2)
      )
        == Some{t2}: Maybe<&2, Tip>
    }

def Cast.put_tip(mach, kern, n, w, th, qs, from, s2, t2, s, s3):
  +s4 = State.led(~mach, s, State.ledger(~mach, s3))
  +a0 = {Ledgers.Act.Vote{Ledgers.Vote{th, qs, Some{Tip.hash(t2)}}, from}: Ledgers.Act}
  +e =>
    %Equal.sym(
      Maybe<&2, Node<Machine.Q(mach)>>,
      State.put(~mach, s2, [Tip.words(t2)]),
      Some{s3},
      e
    ): {
      Tip.at(
        ~mach,
        Cast.vote(~mach, ~kern, s, _, w, n, a0),
        Tip.hash(t2)
      )
        == Some{t2}: Maybe<&2, Tip>
    }
    Tip.at.grows(
      ~mach,
      s3,
      Cast.seal(~mach, ~kern, s4, w, n, a0, Seal.chain(~mach, ~kern, s4, Where.store(w), n)),
      Tip.hash(t2),
      t2,
      Grows.trans(
        ~mach,
        s3,
        s4,
        Cast.seal(~mach, ~kern, s4, w, n, a0, Seal.chain(~mach, ~kern, s4, Where.store(w), n))
      )(
        Grows.to(
          ~mach,
          s3,
          s3,
          s4,
          Led.led(~mach, s, State.ledger(~mach, s3)),
          Grows.refl(~mach, s3)
        )
      )(
        Cast.seal.grows(~mach, ~kern, s4, w, n, a0, Seal.chain(~mach, ~kern, s4, Where.store(w), n))
      )
    )(Tip.put.at(~mach, s2, t2, s3)(e))

# Finality
# --------
# What a node knows of a line stays, whatever the node does next.
# an outcome is final: a request that a step took stays taken, as the same
# version number, and one that its owners refused stays refused
law Node.out_final:
  for ~mach: Machine()
  for ~lawf: Lawful(mach)
  for +n: String
  for +evs: List<&2, Deed<Machine.Q(mach)>>
  for +s: Node<Machine.Q(mach)>
  for i: Ledgers.Id
  for o: Out
  {Node.out(~mach, s, i) == Some{o}: Maybe<&2, Out>}
    -> {
      Node.out(
        ~mach,
        Node.after(~mach, ~Lawful.kernel(mach, lawf), n, evs, s),
        i
      )
        == Some{o}: Maybe<&2, Out>
    }

def Node.out_final(mach, lawf, n, evs, s, i, o):
  Out.kept(
    ~mach,
    s,
    Node.after(~mach, ~Lawful.kernel(mach, lawf), n, evs, s),
    i,
    o,
    Node.after_grows(~mach, ~lawf, n, evs, s),
    Node.after_keeps(~mach, ~lawf, n, evs, s)
  )

# a version never changes: the request that made it and the root of its
# content stay
law Node.made_final:
  for ~mach: Machine()
  for ~lawf: Lawful(mach)
  for +n: String
  for +evs: List<&2, Deed<Machine.Q(mach)>>
  for +s: Node<Machine.Q(mach)>
  for v: Ledgers.Id
  for x: Version
  {Node.made(~mach, s, v) == Some{x}: Maybe<&2, Version>}
    -> {
      Node.made(
        ~mach,
        Node.after(~mach, ~Lawful.kernel(mach, lawf), n, evs, s),
        v
      )
        == Some{x}: Maybe<&2, Version>
    }

def Node.made_final(mach, lawf, n, evs, s, v, x):
  Made.kept(
    ~mach,
    s,
    Node.after(~mach, ~Lawful.kernel(mach, lawf), n, evs, s),
    v,
    x,
    Node.after_grows(~mach, ~lawf, n, evs, s),
    Node.after_keeps(~mach, ~lawf, n, evs, s),
    Node.after_keeps(~mach, ~lawf, n, evs, s)
  )

# the history of a line only grows at its end: the version of a number stays
law Chain.version_final:
  for ~mach: Machine()
  for ~lawf: Lawful(mach)
  for +n: String
  for +evs: List<&2, Deed<Machine.Q(mach)>>
  for +s: Node<Machine.Q(mach)>
  for c: Ledgers.Chain
  for k: U32
  for x: Version
  {Chain.version(~mach, s, c, k) == Some{x}: Maybe<&2, Version>}
    -> {
      Chain.version(
        ~mach,
        Node.after(~mach, ~Lawful.kernel(mach, lawf), n, evs, s),
        c,
        k
      )
        == Some{x}: Maybe<&2, Version>
    }

def Chain.version_final(mach, lawf, n, evs, s, c, k, x):
  Chain.version.kept(
    ~mach,
    s,
    Node.after(~mach, ~Lawful.kernel(mach, lawf), n, evs, s),
    c,
    k,
    x,
    Node.after_keeps(~mach, ~lawf, n, evs, s)
  )

# a mark names its version for good
law Chain.mark_final:
  for ~mach: Machine()
  for ~lawf: Lawful(mach)
  for +n: String
  for +evs: List<&2, Deed<Machine.Q(mach)>>
  for +s: Node<Machine.Q(mach)>
  for c: Ledgers.Chain
  for m: String
  for v: Ledgers.Id
  {Chain.mark(~mach, s, c, m) == Some{v}: Maybe<&2, Ledgers.Id>}
    -> {
      Chain.mark(
        ~mach,
        Node.after(~mach, ~Lawful.kernel(mach, lawf), n, evs, s),
        c,
        m
      )
        == Some{v}: Maybe<&2, Ledgers.Id>
    }

def Chain.mark_final(mach, lawf, n, evs, s, c, m, v):
  Chain.mark.kept(
    ~mach,
    s,
    Node.after(~mach, ~Lawful.kernel(mach, lawf), n, evs, s),
    c,
    m,
    v,
    Node.after_keeps(~mach, ~lawf, n, evs, s)
  )

# the first tip of a branch is for good: what the log of a store holds for a
# branch, it holds whatever the node does next, so a node that opens the
# branch later opens it at the same tip
law Chain.start_final:
  for ~mach: Machine()
  for ~lawf: Lawful(mach)
  for n: String
  for evs: List<&2, Deed<Machine.Q(mach)>>
  for s: Node<Machine.Q(mach)>
  for r: Ledgers.Id
  for b: String
  for v: List<&2, U32>
  {Line.get(~mach, s, Ledgers.Chain{r, None{}}, Log.start(b)) == Some{v}: Maybe<&2, List<&2, U32>>}
    -> {
      Line.get(
        ~mach,
        Node.after(~mach, ~Lawful.kernel(mach, lawf), n, evs, s),
        Ledgers.Chain{r, None{}},
        Log.start(b)
      )
        == Some{v}: Maybe<&2, List<&2, U32>>
    }

def Chain.start_final(mach, lawf, n, evs, s, r, b, v):
  Node.after_keeps(~mach, ~lawf, n, evs, s)(Ledgers.Chain{r, None{}})(Log.start(b))(v)

# a line whose head is the same in a node that grew is where it was
def Reach.same(
  ~mach: Machine(),
  a: Node<Machine.Q(mach)>,
  b: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  h0: Head,
  g: {Node.grows(~mach, a, b) == True{}: Bool},
  eh: {Node.head_of(~mach, a, c) == Node.head_of(~mach, b, c): Maybe<&2, Head>},
  ra: Line.Reach(~mach, a, c, h0)
) -> Line.Reach(~mach, b, c, h0):
  match ra:
    case Tuple{+rs, Tuple{+h, Tuple{e1, e2}}}:
      Tuple{
        rs,
        Tuple{
          h,
          Tuple{
            Equal.trans(
              Maybe<&2, Head>,
              Node.head_of(~mach, b, c),
              Node.head_of(~mach, a, c),
              Some{h},
              Equal.sym(Maybe<&2, Head>, Node.head_of(~mach, a, c), Node.head_of(~mach, b, c), eh),
              e1
            ),
            Line.at_grows(~mach, rs, a, b, c, h0, h)(g)(e2)
          }
        }
      }

# a node that grew, with the same heads, is on the paths
def Path.same(
  ~mach: Machine(),
  a: Node<Machine.Q(mach)>,
  b: Node<Machine.Q(mach)>,
  g: {Node.grows(~mach, a, b) == True{}: Bool},
  eh: {State.heads(~mach, a) == State.heads(~mach, b): Tries.Trie<Head>}
) -> Node.On(~mach, a, b):
  +c => +h0 => t0 => ra => Reach.same(
    ~mach,
    a,
    b,
    c,
    h0,
    g,
    Equal.cong(
      Tries.Trie<Head>,
      Maybe<&2, Head>,
      hs => Tries.Trie.get(Head, hs, Ledgers.Chain.key(c)),
      State.heads(~mach, a),
      State.heads(~mach, b),
      eh
    ),
    ra
  )

# Path.set for the line c2, once it is known whether it has the key of c (bs)
def Path.set.if(
  ~mach: Machine(),
  +a: Node<Machine.Q(mach)>,
  +b0: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  +hd: Head,
  +c2: Ledgers.Chain,
  h0: Head,
  bs: Bool,
  ebs: {Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)) == bs: Bool},
  g: {Node.grows(~mach, a, b0) == True{}: Bool},
  eh: {State.heads(~mach, a) == State.heads(~mach, b0): Tries.Trie<Head>},
  nh: {Head.held(Node.head_of(~mach, a, c)) == False{}: Bool},
  t0: {Head.held(Some{h0}) == True{}: Bool},
  ra: Line.Reach(~mach, a, c2, h0)
) -> Line.Reach(~mach, State.head(~mach, b0, c, hd), c2, h0):
  match bs:
    case True{}:
      Empty.absurd(
        Line.Reach(~mach, State.head(~mach, b0, c, hd), c2, h0),
        Path.set.no(~mach, a, c, c2, h0, Key.same(c2, c)(ebs), nh, t0, ra)
      )
    case False{}:
      Reach.same(
        ~mach,
        a,
        State.head(~mach, b0, c, hd),
        c2,
        h0,
        Grows.to(~mach, a, b0, State.head(~mach, b0, c, hd), Led.head(~mach, b0, c, hd), g),
        Head.other(~mach, a, b0, c, hd, c2, eh, ebs),
        ra
      )

# a node b0 with a new head hd of the line c is on the paths of a, when b0
# grew from a with the same heads, and the head of c in a has no tip
def Path.set(
  ~mach: Machine(),
  a: Node<Machine.Q(mach)>,
  b0: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  hd: Head,
  g: {Node.grows(~mach, a, b0) == True{}: Bool},
  eh: {State.heads(~mach, a) == State.heads(~mach, b0): Tries.Trie<Head>},
  nh: {Head.held(Node.head_of(~mach, a, c)) == False{}: Bool}
) -> Node.On(~mach, a, State.head(~mach, b0, c, hd)):
  +c2 => +h0 => t0 => ra => Path.set.if(
    ~mach,
    a,
    b0,
    c,
    hd,
    c2,
    h0,
    Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
    {==},
    g,
    eh,
    nh,
    t0,
    ra
  )

# Path.moved for a line with the key of c: one more decided step
def Path.moved.yes(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  +n: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  +h: Head,
  hd: Head,
  +q: Nat,
  v: Ledgers.Vote,
  +c2: Ledgers.Chain,
  h0: Head,
  +ek: {Ledgers.Chain.key(c2) == Ledgers.Chain.key(c): List<&2, Bool>},
  +gn: {Node.grows(~mach, s, n) == True{}: Bool},
  en: {Node.head_of(~mach, n, c2) == Some{hd}: Maybe<&2, Head>},
  em: {Node.head_of(~mach, s, c) == Some{h}: Maybe<&2, Head>},
  ein: {Advance.in(~mach, s, c, h, q) == Some{v}: Maybe<&2, Ledgers.Vote>},
  emv: {Head.moved(h, Some{v}) == Some{hd}: Maybe<&2, Head>},
  ra: Line.Reach(~mach, s, c2, h0)
) -> Line.Reach(~mach, n, c2, h0):
  match ra:
    case Tuple{+rs, Tuple{h2, Tuple{e1, e2}}}:
      Tuple{
        q <> rs,
        Tuple{
          hd,
          Tuple{
            en,
            Equal.trans(
              Maybe<&2, Head>,
              Line.at(~mach, q <> rs, n, c2, h0),
              Head.moved(h2, Advance.in(~mach, n, c2, h2, q)),
              Some{hd},
              Equal.cong(
                Maybe<&2, Head>,
                Maybe<&2, Head>,
                m => Maybe.bind(
                  &2,
                  Head,
                  Head,
                  m,
                  +z => Head.moved(z, Advance.in(~mach, n, c2, z, q))
                ),
                Line.at(~mach, rs, n, c2, h0),
                Some{h2},
                Line.at_grows(~mach, rs, s, n, c2, h0, h2)(gn)(e2)
              ),
              Equal.trans(
                Maybe<&2, Head>,
                Head.moved(h2, Advance.in(~mach, n, c2, h2, q)),
                Head.moved(h, Advance.in(~mach, n, c2, h, q)),
                Some{hd},
                Equal.cong(
                  Head,
                  Maybe<&2, Head>,
                  +z => Head.moved(z, Advance.in(~mach, n, c2, z, q)),
                  h2,
                  h,
                  Shared.Maybe.some_inj(
                    Head,
                    h2,
                    h,
                    Equal.trans(
                      Maybe<&2, Head>,
                      Some{h2},
                      Node.head_of(~mach, s, c2),
                      Some{h},
                      Equal.sym(Maybe<&2, Head>, Node.head_of(~mach, s, c2), Some{h2}, e1),
                      Equal.trans(
                        Maybe<&2, Head>,
                        Node.head_of(~mach, s, c2),
                        Node.head_of(~mach, s, c),
                        Some{h},
                        Head.keyed(~mach, s, c2, c, ek),
                        em
                      )
                    )
                  )
                ),
                Equal.trans(
                  Maybe<&2, Head>,
                  Head.moved(h, Advance.in(~mach, n, c2, h, q)),
                  Head.moved(h, Some{v}),
                  Some{hd},
                  Equal.cong(
                    Maybe<&2, Ledgers.Vote>,
                    Maybe<&2, Head>,
                    w => Head.moved(h, w),
                    Advance.in(~mach, n, c2, h, q),
                    Some{v},
                    Equal.trans(
                      Maybe<&2, Ledgers.Vote>,
                      Advance.in(~mach, n, c2, h, q),
                      Advance.in(~mach, n, c, h, q),
                      Some{v},
                      In.key(~mach, n, c2, c, h, q, ek),
                      In.grows(~mach, s, n, c, h, q, v, gn)(ein)
                    )
                  ),
                  emv
                )
              )
            )
          }
        }
      }

# Path.moved for the line c2, once it is known whether it has the key of c
def Path.moved.if(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  +b0: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  h: Head,
  +hd: Head,
  q: Nat,
  v: Ledgers.Vote,
  +c2: Ledgers.Chain,
  h0: Head,
  bs: Bool,
  +ebs: {Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)) == bs: Bool},
  g: {Node.grows(~mach, s, b0) == True{}: Bool},
  eh: {State.heads(~mach, s) == State.heads(~mach, b0): Tries.Trie<Head>},
  em: {Node.head_of(~mach, s, c) == Some{h}: Maybe<&2, Head>},
  ein: {Advance.in(~mach, s, c, h, q) == Some{v}: Maybe<&2, Ledgers.Vote>},
  emv: {Head.moved(h, Some{v}) == Some{hd}: Maybe<&2, Head>},
  ra: Line.Reach(~mach, s, c2, h0)
) -> Line.Reach(~mach, State.head(~mach, b0, c, hd), c2, h0):
  match bs:
    case True{}:
      Path.moved.yes(
        ~mach,
        s,
        State.head(~mach, b0, c, hd),
        c,
        h,
        hd,
        q,
        v,
        c2,
        h0,
        Key.same(c2, c)(ebs),
        Grows.to(~mach, s, b0, State.head(~mach, b0, c, hd), Led.head(~mach, b0, c, hd), g),
        Head.this(~mach, b0, c, hd, c2, ebs),
        em,
        ein,
        emv,
        ra
      )
    case False{}:
      Reach.same(
        ~mach,
        s,
        State.head(~mach, b0, c, hd),
        c2,
        h0,
        Grows.to(~mach, s, b0, State.head(~mach, b0, c, hd), Led.head(~mach, b0, c, hd), g),
        Head.other(~mach, s, b0, c, hd, c2, eh, ebs),
        ra
      )

# a head moved over the step v that the owners decided at it, in the round
# q, is one more decided step on its path
def Path.moved(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  +s3: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  h: Head,
  hd: Head,
  qs: List<&2, Ledgers.Id>,
  q: Nat,
  v: Ledgers.Vote,
  g3: {Node.grows(~mach, s, s3) == True{}: Bool},
  em: {Node.head_of(~mach, s, c) == Some{h}: Maybe<&2, Head>},
  ein: {Advance.in(~mach, s, c, h, q) == Some{v}: Maybe<&2, Ledgers.Vote>},
  emv: {Head.moved(h, Some{v}) == Some{hd}: Maybe<&2, Head>}
) -> Node.On(~mach, s, State.moved(~mach, State.led(~mach, s, State.ledger(~mach, s3)), c, hd, qs)):
  +x = State.led(~mach, s, State.ledger(~mach, s3))
  +ws = Wait.left(
    Wait.of(~mach, x, c),
    Tries.Trie.put_keys(~Ledgers.Id, ~Ledgers.Id.key, qs, Tries.Trie.new(Unit))
  )
  +b0 = Wait.set(~mach, x, c, ws)
  +c2 => +h0 => t0 => ra => Path.moved.if(
    ~mach,
    s,
    b0,
    c,
    h,
    hd,
    q,
    v,
    c2,
    h0,
    Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
    {==},
    Grows.to(~mach, s, x, b0, Led.wait(~mach, x, c, ws), Grows.back(~mach, s, s3, g3)),
    Equal.trans(
      Tries.Trie<Head>,
      State.heads(~mach, s),
      State.heads(~mach, x),
      State.heads(~mach, b0),
      Heads.led(~mach, s, State.ledger(~mach, s3)),
      Heads.wait(~mach, x, c, ws)
    ),
    em,
    ein,
    emv,
    ra
  )

# Advance.moved is on the paths, once the node m that the put gives is known
def Advance.moved.path(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  +s2: Node<Machine.Q(mach)>,
  m: Maybe<&2, Node<Machine.Q(mach)>>,
  c: Ledgers.Chain,
  h: Head,
  hd: Head,
  t2: Tip,
  qs: List<&2, Ledgers.Id>,
  q: Nat,
  v: Ledgers.Vote,
  g2: {Node.grows(~mach, s, s2) == True{}: Bool},
  em: {Node.head_of(~mach, s, c) == Some{h}: Maybe<&2, Head>},
  ein: {Advance.in(~mach, s, c, h, q) == Some{v}: Maybe<&2, Ledgers.Vote>},
  emv: {Head.moved(h, Some{v}) == Some{hd}: Maybe<&2, Head>}
) -> {
  State.put(~mach, s2, [Tip.words(t2)]) == m: Maybe<&2, Node<Machine.Q(mach)>>
} -> Node.On(~mach, s, Advance.moved(~mach, s, m, c, hd, qs)):
  match m:
    case None{}:
      e2 => Path.refl(~mach, s)
    case Some{+s3}:
      e2 => Path.moved(
        ~mach,
        s,
        s3,
        c,
        h,
        hd,
        qs,
        q,
        v,
        Grows.trans(~mach, s, s2, s3)(g2)(Put.grew(~mach, s2, [Tip.words(t2)], s3, e2)),
        em,
        ein,
        emv
      )

# Advance.ran is on the paths, once it is known whether the run gives the tip
# that the step names (bq)
def Advance.ran.path.if(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  +s2: Node<Machine.Q(mach)>,
  +t2: Tip,
  c: Ledgers.Chain,
  +r: Ledgers.Id,
  +br: Maybe<&2, String>,
  +next: U32,
  th: Maybe<&2, Hashes.Hash>,
  before: Maybe<&2, Hashes.Hash>,
  +after: Maybe<&2, Hashes.Hash>,
  +qs: List<&2, Ledgers.Id>,
  q: Nat,
  bq: Bool,
  ebq: {Root.same(after, Some{Tip.hash(t2)}) == bq: Bool},
  g2: {Node.grows(~mach, s, s2) == True{}: Bool},
  em: {Node.head_of(~mach, s, c) == Some{Head{r, br, next, th}}: Maybe<&2, Head>},
  ein: {
    Advance.in(
      ~mach,
      s,
      c,
      Head{r, br, next, th},
      q
    )
      == Some{Ledgers.Vote{before, qs, after}}: Maybe<&2, Ledgers.Vote>
  }
) -> Node.On(
  ~mach,
  s,
  Shared.Bool.when(
    Node<Machine.Q(mach)>,
    bq,
    u => Advance.moved(
      ~mach,
      s,
      State.put(~mach, s2, [Tip.words(t2)]),
      c,
      Head{r, br, U32.inc(next), Some{Tip.hash(t2)}},
      qs
    ),
    u => s
  )
):
  match bq:
    case True{}:
      Advance.moved.path(
        ~mach,
        s,
        s2,
        State.put(~mach, s2, [Tip.words(t2)]),
        c,
        Head{r, br, next, th},
        Head{r, br, U32.inc(next), Some{Tip.hash(t2)}},
        t2,
        qs,
        q,
        Ledgers.Vote{before, qs, after},
        g2,
        em,
        ein,
        Equal.cong(
          Maybe<&2, Hashes.Hash>,
          Maybe<&2, Head>,
          a => Maybe.bind(&2, Hashes.Hash, Head, a, y => Some{Head.up(Head{r, br, next, th}, y)}),
          after,
          Some{Tip.hash(t2)},
          Shared.Maybe.is_eq_sound(
            ~Hashes.Hash,
            ~Hashes.Hash.is_eq,
            Hashes.Hash.is_eq_sound,
            after,
            Some{Tip.hash(t2)}
          )(ebq)
        )
      )({==})
    case False{}:
      Path.refl(~mach, s)

# a checked step is on the paths
def Advance.ran.path(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain,
  r: Ledgers.Id,
  br: Maybe<&2, String>,
  next: U32,
  th: Maybe<&2, Hashes.Hash>,
  before: Maybe<&2, Hashes.Hash>,
  +after: Maybe<&2, Hashes.Hash>,
  qs: List<&2, Ledgers.Id>,
  m: Maybe<&2, Run<Machine.Q(mach)>>,
  q: Nat,
  em: {Node.head_of(~mach, s, c) == Some{Head{r, br, next, th}}: Maybe<&2, Head>},
  ein: {
    Advance.in(
      ~mach,
      s,
      c,
      Head{r, br, next, th},
      q
    )
      == Some{Ledgers.Vote{before, qs, after}}: Maybe<&2, Ledgers.Vote>
  }
) -> {
  Run.after(~mach, s, m) == True{}: Bool
} -> Node.On(~mach, s, Advance.ran(~mach, s, c, r, br, next, after, qs, m)):
  match m:
    case None{}:
      ga => Path.refl(~mach, s)
    case Some{Run{s2, +t2}}:
      ga => Advance.ran.path.if(
        ~mach,
        s,
        s2,
        t2,
        c,
        r,
        br,
        next,
        th,
        before,
        after,
        qs,
        q,
        Root.same(after, Some{Tip.hash(t2)}),
        {==},
        ga,
        em,
        ein
      )

# Node.advance is on the paths, once the decided step m is known
def Advance.step.path(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  h: Head,
  +t: Tip,
  m: Maybe<&2, Ledgers.Vote>
) -> {Node.head_of(~mach, s, c) == Some{h}: Maybe<&2, Head>}
  -> {Head.tip(~mach, s, h) == Some{t}: Maybe<&2, Tip>}
  -> {
    Height.decide(
      ~mach,
      s,
      c,
      Head.next(h),
      Tip.owners(t),
      Round.seen(~mach, s, c, Head.next(h))
    )
      == m: Maybe<&2, Ledgers.Vote>
  }
  -> Node.On(~mach, s, Advance.step(~mach, ~Lawful.kernel(mach, lawf), s, c, h, t, m)):
  match h m:
    case Head{r, br, +next, +th} Some{Ledgers.Vote{+before, +qs, after}}:
      em => et => ed => Path.when(
        ~mach,
        Root.same(before, th),
        s,
        Advance.ran(
          ~mach,
          s,
          c,
          r,
          br,
          next,
          after,
          qs,
          Step.run(~mach, ~Lawful.kernel(mach, lawf), s, c, t, qs)
        ),
        s,
        Scan.elim(
          ~mach,
          Node.On(
            ~mach,
            s,
            Advance.ran(
              ~mach,
              s,
              c,
              r,
              br,
              next,
              after,
              qs,
              Step.run(~mach, ~Lawful.kernel(mach, lawf), s, c, t, qs)
            )
          ),
          s,
          c,
          next,
          Tip.owners(t),
          Round.seen(~mach, s, c, next),
          Ledgers.Vote{before, qs, after}
        )(
          ed
        )(
          q => d => Advance.ran.path(
            ~mach,
            s,
            c,
            r,
            br,
            next,
            th,
            before,
            after,
            qs,
            Step.run(~mach, ~Lawful.kernel(mach, lawf), s, c, t, qs),
            q,
            em,
            (
              %Equal.sym(Maybe<&2, Tip>, Head.tip(~mach, s, Head{r, br, next, th}), Some{t}, et): {Maybe.bind(&2, Tip, Ledgers.Vote, _, t1 => Ledgers.State.decide(~Machine.Q(mach), State.ledger(~mach, s), Ledgers.Where{c, next, q}, Tip.owners(t1))) == Some{Ledgers.Vote{before, qs, after}}: Maybe<&2, Ledgers.Vote>}
              d)
          )(Run.grows(~mach, ~lawf, s, c, t, qs))
        ),
        Path.refl(~mach, s)
      )
    case Head{r, br, next, th} None{}:
      em => et => ed => Path.refl(~mach, s)

# Node.advance is on the paths, at the head h whose tip is m
def Advance.at.path(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  +h: Head,
  m: Maybe<&2, Tip>
) -> {
  Node.head_of(~mach, s, c) == Some{h}: Maybe<&2, Head>
} -> {
  Head.tip(~mach, s, h) == m: Maybe<&2, Tip>
} -> Node.On(~mach, s, Advance.at(~mach, ~Lawful.kernel(mach, lawf), s, c, h, m)):
  match m:
    case None{}:
      em => et => Path.refl(~mach, s)
    case Some{+t}:
      em => et => Advance.step.path(
        ~mach,
        ~lawf,
        s,
        c,
        h,
        t,
        Height.decide(
          ~mach,
          s,
          c,
          Head.next(h),
          Tip.owners(t),
          Round.seen(~mach, s, c, Head.next(h))
        )
      )(em)(et)({==})

# a node's ballot keeps its logs
def Cast.path(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  +n: String,
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain
) -> Node.On(~mach, s, Node.cast(~mach, ~Lawful.kernel(mach, lawf), n, s, c)):
  Path.same(
    ~mach,
    s,
    Node.cast(~mach, ~Lawful.kernel(mach, lawf), n, s, c),
    Cast.grows(~mach, ~lawf, n, s, c),
    Cast.head.heads(~mach, ~Lawful.kernel(mach, lawf), n, s, c, Node.head_of(~mach, s, c))
  )

# Advances.kept once the head m is known
def Advances.at.path(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  f: Nat,
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  m: Maybe<&2, Head>
) -> {
  Node.head_of(~mach, s, c) == m: Maybe<&2, Head>
} -> Node.On(~mach, s, Advances.at(~mach, ~Lawful.kernel(mach, lawf), f, s, c, m)):
  match f m:
    case 0n x:
      em => Path.refl(~mach, s)
    case 1n+p None{}:
      em => Path.refl(~mach, s)
    case 1n+(+p) Some{+h}:
      +em =>
        +s1 = Advance.at(~mach, ~Lawful.kernel(mach, lawf), s, c, h, Head.tip(~mach, s, h))
        +m1 = Node.head_of(~mach, s1, c)
        Path.when(
          ~mach,
          Heads.level(Some{h}, m1),
          s,
          s1,
          Advances.at(~mach, ~Lawful.kernel(mach, lawf), p, s1, c, m1),
          Advance.at.path(~mach, ~lawf, s, c, h, Head.tip(~mach, s, h))(em)({==}),
          Path.trans(
            ~mach,
            s,
            s1,
            Advances.at(~mach, ~Lawful.kernel(mach, lawf), p, s1, c, m1),
            Advance.at.path(~mach, ~lawf, s, c, h, Head.tip(~mach, s, h))(em)({==}),
            Advances.at.path(~mach, ~lawf, p, s1, c, m1)({==})
          )
        )

# a head that moves over each decided step is on the paths
def Advances.path(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  f: Nat,
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain
) -> Node.On(~mach, s, Node.advances(~mach, ~Lawful.kernel(mach, lawf), f, s, c)):
  Advances.at.path(~mach, ~lawf, f, s, c, Node.head_of(~mach, s, c))({==})

# what a node does at a head is on the paths
def Step.head.path(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  +n: String,
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain
) -> Node.On(~mach, s, Step.head(~mach, ~Lawful.kernel(mach, lawf), n, s, c)):
  +s1 = Node.advances(~mach, ~Lawful.kernel(mach, lawf), 4294967295n, s, c)
  +s2 = Node.cast(~mach, ~Lawful.kernel(mach, lawf), n, s1, c)
  s3 = Node.advances(~mach, ~Lawful.kernel(mach, lawf), 4294967295n, s2, c)
  Path.trans(
    ~mach,
    s,
    s1,
    s3,
    Advances.path(~mach, ~lawf, 4294967295n, s, c),
    Path.trans(
      ~mach,
      s1,
      s2,
      s3,
      Cast.path(~mach, ~lawf, n, s1, c),
      Advances.path(~mach, ~lawf, 4294967295n, s2, c)
    )
  )

# a branch that opens is on the paths, once the head m of the line is known
def Open.at.path(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  m: Maybe<&2, Head>
) -> {
  Node.head_of(~mach, s, c) == m: Maybe<&2, Head>
} -> Node.On(~mach, s, Open.at(~mach, s, c, m)):
  match m:
    case Some{Head{+r, Some{+b}, n, None{}}}:
      em => Path.set(
        ~mach,
        s,
        s,
        c,
        Head{
          r,
          Some{b},
          0,
          Branch.first(~mach, s, b, Node.tip(~mach, s, Ledgers.Chain{r, None{}}))
        },
        Grows.refl(~mach, s),
        {==},
        Held.not(~mach, s, c, Some{Head{r, Some{b}, n, None{}}}, em)
      )
    case Some{Head{r, Some{b}, n, Some{t}}}:
      em => Path.refl(~mach, s)
    case Some{Head{r, None{}, n, t}}:
      em => Path.refl(~mach, s)
    case None{}:
      em => Path.refl(~mach, s)

# what a node does on a line is on the paths
def Step.path(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  n: String,
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain
) -> Node.On(~mach, s, Node.step(~mach, ~Lawful.kernel(mach, lawf), n, s, c)):
  s1 = Node.open(~mach, s, c)
  Path.trans(
    ~mach,
    s,
    s1,
    Step.head(~mach, ~Lawful.kernel(mach, lawf), n, s1, c),
    Open.at.path(~mach, s, c, Node.head_of(~mach, s, c))({==}),
    Step.head.path(~mach, ~lawf, n, s1, c)
  )

# a pass to the next round is on the paths
def Pass.path(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  +n: String,
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain
) -> Node.On(~mach, s, Node.pass(~mach, ~Lawful.kernel(mach, lawf), n, s, c)):
  +s1 = Pass.head(~mach, ~Lawful.kernel(mach, lawf), n, s, c, Node.head_of(~mach, s, c))
  Path.trans(
    ~mach,
    s,
    s1,
    Node.step(~mach, ~Lawful.kernel(mach, lawf), n, s1, c),
    Path.same(
      ~mach,
      s,
      s1,
      Pass.head.grows(~mach, ~Lawful.kernel(mach, lawf), n, s, c, Node.head_of(~mach, s, c)),
      Pass.head.heads(~mach, ~Lawful.kernel(mach, lawf), n, s, c, Node.head_of(~mach, s, c))
    ),
    Step.path(~mach, ~lawf, n, s1, c)
  )

# a first head is on the paths, once the head m of the line is known
def First.at.path(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  +c: Ledgers.Chain,
  h: Head,
  m: Maybe<&2, Head>
) -> {
  Node.head_of(~mach, s, c) == m: Maybe<&2, Head>
} -> Node.On(~mach, s, First.at(~mach, s, c, h, m)):
  match m:
    case Some{Head{r, b, n, Some{t}}}:
      em => Path.refl(~mach, s)
    case Some{Head{+r, +b, +n, None{}}}:
      em => Path.set(
        ~mach,
        s,
        s,
        c,
        h,
        Grows.refl(~mach, s),
        {==},
        Held.not(~mach, s, c, Some{Head{r, b, n, None{}}}, em)
      )
    case None{}:
      em => Path.set(
        ~mach,
        s,
        s,
        c,
        h,
        Grows.refl(~mach, s),
        {==},
        Held.not(~mach, s, c, None{}, em)
      )

# a first head on a node that grew from a, which grew from s, is on the paths
def Start.head.path(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  a: Node<Machine.Q(mach)>,
  m: Maybe<&2, Node<Machine.Q(mach)>>,
  +c: Ledgers.Chain,
  h: Head,
  g: {Node.grows(~mach, s, a) == True{}: Bool}
) -> {State.after(~mach, a, m) == True{}: Bool} -> Node.On(~mach, s, Start.head(~mach, s, m, c, h)):
  match m:
    case None{}:
      e => Path.refl(~mach, s)
    case Some{+s3}:
      e =>
        +x = State.led(~mach, s, State.ledger(~mach, s3))
        Path.trans(
          ~mach,
          s,
          x,
          State.first(~mach, x, c, h),
          Path.same(
            ~mach,
            s,
            x,
            Grows.back(~mach, s, s3, Grows.trans(~mach, s, a, s3)(g)(e)),
            Heads.led(~mach, s, State.ledger(~mach, s3))
          ),
          First.at.path(~mach, x, c, h, Node.head_of(~mach, x, c))({==})
        )

# Start.path once the content m of the store is known
def Start.with.path(
  ~mach: Machine(),
  s: Node<Machine.Q(mach)>,
  +i: Ledgers.Id,
  os: List<&2, String>,
  m: Maybe<&2, Work<Machine.Q(mach)>>
) -> {Work.after(~mach, s, m) == True{}: Bool} -> Node.On(~mach, s, Start.with(~mach, s, i, os, m)):
  match m:
    case None{}:
      e => Path.refl(~mach, s)
    case Some{Work{+s2, c}}:
      e =>
        +t = {Tip{c, None{}, 0, os}: Tip}
        Start.head.path(
          ~mach,
          s,
          s2,
          State.put(~mach, s2, [Tip.words(t)]),
          Ledgers.Chain{i, None{}},
          Head{i, None{}, 0, Some{Tip.hash(t)}},
          e
        )(Put.grows(~mach, s2, [Tip.words(t)]))

# a store that starts is on the paths
def Start.path(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +s: Node<Machine.Q(mach)>,
  i: Ledgers.Id,
  +os: List<&2, Owner>
) -> Node.On(~mach, s, Node.start(~mach, ~kern, s, i, os)):
  Start.with.path(
    ~mach,
    s,
    i,
    Owner.names(os),
    Seal.firsts(~mach, ~kern, os, Some{Work{s, None{}}})
  )(Firsts.after(~mach, ~kern, s, os, Some{Work{s, None{}}})(Grows.refl(~mach, s)))

# a line that a node starts to follow is on the paths
def Follow.new.path(
  ~mach: Machine(),
  +s: Node<Machine.Q(mach)>,
  +r: Ledgers.Id,
  +l: Maybe<&2, String>,
  m: Maybe<&2, Head>
) -> {
  Node.head_of(~mach, s, Line.chain(r, l)) == m: Maybe<&2, Head>
} -> Node.On(~mach, s, Follow.new(~mach, s, r, l, m)):
  match m:
    case Some{h}:
      em => Path.refl(~mach, s)
    case None{}:
      em => Path.set(
        ~mach,
        s,
        s,
        Line.chain(r, l),
        Head{r, l, 0, None{}},
        Grows.refl(~mach, s),
        {==},
        Held.not(~mach, s, Line.chain(r, l), None{}, em)
      )

# a new request is on the paths
def Arrive.path(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +s: Node<Machine.Q(mach)>,
  +i: Ledgers.Id,
  a: Arrival
) -> Node.On(~mach, s, Arrive.at(~mach, ~kern, s, i, a)):
  match a:
    case Arrival.Starts{os}:
      Start.path(~mach, ~kern, s, i, os)
    case Arrival.Waits{+r, +l}:
      +s1 = Node.follow(~mach, s, r, l)
      Path.trans(
        ~mach,
        s,
        s1,
        State.wait(~mach, s1, Line.chain(r, l), i),
        Follow.new.path(~mach, s, r, l, Node.head_of(~mach, s, Line.chain(r, l)))({==}),
        Path.same(
          ~mach,
          s1,
          State.wait(~mach, s1, Line.chain(r, l), i),
          Grows.to(
            ~mach,
            s1,
            s1,
            State.wait(~mach, s1, Line.chain(r, l), i),
            Led.waits(~mach, s1, Line.chain(r, l), i),
            Grows.refl(~mach, s1)
          ),
          Heads.waits(~mach, s1, Line.chain(r, l), i)
        )
      )

# a new request is on the paths
def Ask.new.path(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  n: String,
  +s: Node<Machine.Q(mach)>,
  +e: Envelope,
  +q: Machine.Q(mach)
) -> Node.On(~mach, s, Node.ask.new(~mach, ~Lawful.kernel(mach, lawf), n, s, e, q)):
  +i = Envelope.of(e)
  c = Arrival.chain(i, Machine.arrival(mach)(q))
  +l0 = Ledgers.State.ask(
    ~Machine.Q(mach),
    ~Machine.same(mach),
    State.ledger(~mach, s),
    i,
    Envelope.time(e),
    q
  )
  +s0 = State.led(~mach, s, l0)
  s1 = Node.arrive(~mach, ~Lawful.kernel(mach, lawf), s0, i, q)
  Path.trans(
    ~mach,
    s,
    s0,
    Node.step(~mach, ~Lawful.kernel(mach, lawf), n, s1, c),
    Path.same(
      ~mach,
      s,
      s0,
      Grows.led(
        ~mach,
        s,
        l0,
        Ledgers.State.add_grows(
          ~Machine.Q(mach),
          ~Machine.same(mach),
          ~Machine.laws(mach),
          State.ledger(~mach, s),
          Ledgers.Slot.ask(i),
          Ledgers.Entry.Ask{i, Envelope.time(e), q}
        )
      ),
      Heads.led(~mach, s, l0)
    ),
    Path.trans(
      ~mach,
      s0,
      s1,
      Node.step(~mach, ~Lawful.kernel(mach, lawf), n, s1, c),
      Arrive.path(~mach, ~Lawful.kernel(mach, lawf), s0, i, Machine.arrival(mach)(q)),
      Step.path(~mach, ~lawf, n, s1, c)
    )
  )

# Node.ask_keeps once the cell m of the request's ID is known
def Ask.at.path(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  n: String,
  +s: Node<Machine.Q(mach)>,
  +e: Envelope,
  q: Machine.Q(mach),
  m: Maybe<&2, Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>>
) -> Node.On(~mach, s, Node.ask.at(~mach, ~Lawful.kernel(mach, lawf), n, s, e, q, m)):
  match m:
    case Some{x}:
      Path.refl(~mach, s)
    case None{}:
      Path.trans(
        ~mach,
        s,
        State.keyed(~mach, s, Keys.mark(State.keys(~mach, s), Envelope.of(e))),
        Node.ask.new(
          ~mach,
          ~Lawful.kernel(mach, lawf),
          n,
          State.keyed(~mach, s, Keys.mark(State.keys(~mach, s), Envelope.of(e))),
          e,
          q
        ),
        Path.same(
          ~mach,
          s,
          State.keyed(~mach, s, Keys.mark(State.keys(~mach, s), Envelope.of(e))),
          Grows.to(
            ~mach,
            s,
            s,
            State.keyed(~mach, s, Keys.mark(State.keys(~mach, s), Envelope.of(e))),
            Led.keyed(~mach, s, Keys.mark(State.keys(~mach, s), Envelope.of(e))),
            Grows.refl(~mach, s)
          ),
          Heads.keyed(~mach, s, Keys.mark(State.keys(~mach, s), Envelope.of(e)))
        ),
        Ask.new.path(
          ~mach,
          ~lawf,
          n,
          State.keyed(~mach, s, Keys.mark(State.keys(~mach, s), Envelope.of(e))),
          e,
          q
        )
      )

# Node.ask is on the paths
def Ask.path(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  n: String,
  +s: Node<Machine.Q(mach)>,
  +e: Envelope,
  q: Machine.Q(mach)
) -> Node.On(~mach, s, Node.ask(~mach, ~Lawful.kernel(mach, lawf), n, s, e, q)):
  Ask.at.path(
    ~mach,
    ~lawf,
    n,
    s,
    e,
    q,
    Ledgers.State.get(~Machine.Q(mach), State.ledger(~mach, s), Ledgers.Slot.ask(Envelope.of(e)))
  )

# the new requests among cells are on the paths
def Take.asks.path(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  cs: List<&2, Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>>,
  +old: Ledgers.State(Machine.Q(mach)),
  +s: Node<Machine.Q(mach)>
) -> Node.On(~mach, s, Take.asks(~mach, ~kern, cs, old, s)):
  match cs:
    case Nil{}:
      Path.refl(~mach, s)
    case Con{Cells.One{Ledgers.Entry.Ask{+i, t, +q}}, rest}:
      s1 = Shared.Bool.when(
        Node<Machine.Q(mach)>,
        Maybe.is_none(
          &2,
          Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>,
          Ledgers.State.get(~Machine.Q(mach), old, Ledgers.Slot.ask(i))
        ),
        u => Node.arrive(~mach, ~kern, s, i, q),
        u => s
      )
      Path.trans(
        ~mach,
        s,
        s1,
        Take.asks(~mach, ~kern, rest, old, s1),
        Path.when(
          ~mach,
          Maybe.is_none(
            &2,
            Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>,
            Ledgers.State.get(~Machine.Q(mach), old, Ledgers.Slot.ask(i))
          ),
          s,
          Node.arrive(~mach, ~kern, s, i, q),
          s,
          Arrive.path(~mach, ~kern, s, i, Machine.arrival(mach)(q)),
          Path.refl(~mach, s)
        ),
        Take.asks.path(~mach, ~kern, rest, old, s1)
      )
    case Con{Cells.One{Ledgers.Entry.Vote{v}}, rest}:
      Take.asks.path(~mach, ~kern, rest, old, s)
    case Con{Cells.One{Ledgers.Entry.Data{d}}, rest}:
      Take.asks.path(~mach, ~kern, rest, old, s)
    case Con{Cells.Many{}, rest}:
      Take.asks.path(~mach, ~kern, rest, old, s)

# Node.take is on the paths
def Take.path(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +s: Node<Machine.Q(mach)>,
  +t: Ledgers.State(Machine.Q(mach))
) -> Node.On(~mach, s, Node.take(~mach, ~kern, s, t)):
  +sent = Take.clean(
    ~mach,
    Tries.Trie.values(Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>, t),
    Ledgers.State.empty(~Machine.Q(mach))
  )
  +l1 = Ledgers.State.take(~Machine.Q(mach), State.ledger(~mach, s), sent)
  +s1 = State.led(~mach, s, l1)
  +cs = Tries.Trie.values(Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>, sent)
  +s2 = Take.asks(~mach, ~kern, cs, State.ledger(~mach, s), s1)
  +bs = Ballots.of(
    ~mach,
    Tries.Trie.values(
      Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>,
      Ledgers.State.missing(~Machine.Q(mach), ~Machine.same(mach), t, State.ledger(~mach, s))
    )
  )
  Path.trans(
    ~mach,
    s,
    s1,
    Sealed.take(~mach, ~kern, bs, s2),
    Path.same(
      ~mach,
      s,
      s1,
      Grows.led(
        ~mach,
        s,
        l1,
        Ledgers.State.take_grows(
          ~Machine.Q(mach),
          ~Machine.same(mach),
          ~Machine.laws(mach),
          State.ledger(~mach, s),
          sent
        )
      ),
      Heads.led(~mach, s, l1)
    ),
    Path.trans(
      ~mach,
      s1,
      s2,
      Sealed.take(~mach, ~kern, bs, s2),
      Take.asks.path(~mach, ~kern, cs, State.ledger(~mach, s), s1),
      Path.same(
        ~mach,
        s2,
        Sealed.take(~mach, ~kern, bs, s2),
        Each.grows(~mach, ~kern, List.length(&2, Ledgers.Ballot, bs), bs, Pending.of(bs), s2),
        Each.heads(~mach, ~kern, List.length(&2, Ledgers.Ballot, bs), bs, Pending.of(bs), s2)
      )
    )
  )

# what a node does on each of some lines is on the paths
def Steps.path(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  +n: String,
  cs: List<&2, Ledgers.Chain>,
  +s: Node<Machine.Q(mach)>
) -> Node.On(~mach, s, Node.steps(~mach, ~Lawful.kernel(mach, lawf), n, cs, s)):
  match cs:
    case Nil{}:
      Path.refl(~mach, s)
    case Con{+c, rest}:
      s1 = Node.step(~mach, ~Lawful.kernel(mach, lawf), n, s, c)
      Path.trans(
        ~mach,
        s,
        s1,
        Node.steps(~mach, ~Lawful.kernel(mach, lawf), n, rest, s1),
        Step.path(~mach, ~lawf, n, s, c),
        Steps.path(~mach, ~lawf, n, rest, s1)
      )

# an adoption is on the paths, once the request m is known
def Adopt.ask.path(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  n: String,
  s: Node<Machine.Q(mach)>,
  m: Maybe<&2, Request<Machine.Q(mach)>>
) -> Node.On(~mach, s, Adopt.ask(~mach, ~Lawful.kernel(mach, lawf), n, s, m)):
  match m:
    case None{}:
      Path.refl(~mach, s)
    case Some{Request{e, q}}:
      Ask.path(~mach, ~lawf, n, s, e, q)

# an adoption is on the paths, once the head m of the line is known
def Adopt.head.path(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  n: String,
  +s: Node<Machine.Q(mach)>,
  m: Maybe<&2, Head>
) -> Node.On(~mach, s, Adopt.head(~mach, ~Lawful.kernel(mach, lawf), n, s, m)):
  match m:
    case None{}:
      Path.refl(~mach, s)
    case Some{Head{r, b, next, t}}:
      Adopt.ask.path(~mach, ~lawf, n, s, Kernel.follow(mach, Lawful.kernel(mach, lawf))(s)(r)(b))

# the adoption of a line is on the paths
def Adopt.at.path(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  n: String,
  +s: Node<Machine.Q(mach)>,
  c: Ledgers.Chain
) -> Node.On(~mach, s, Adopt.at(~mach, ~Lawful.kernel(mach, lawf), n, s, c)):
  Adopt.head.path(~mach, ~lawf, n, s, Node.head_of(~mach, s, c))

# the adoption of a line, if any, is on the paths
def Adopt.maybe.path(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  n: String,
  s: Node<Machine.Q(mach)>,
  m: Maybe<&2, Ledgers.Chain>
) -> Node.On(~mach, s, Adopt.maybe(~mach, ~Lawful.kernel(mach, lawf), n, s, m)):
  match m:
    case None{}:
      Path.refl(~mach, s)
    case Some{c}:
      Adopt.at.path(~mach, ~lawf, n, s, c)

# the adoption of each of some lines is on the paths
def Adopts.path(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  +n: String,
  cs: List<&2, Ledgers.Chain>,
  +s: Node<Machine.Q(mach)>
) -> Node.On(~mach, s, Node.adopts(~mach, ~Lawful.kernel(mach, lawf), n, cs, s)):
  match cs:
    case Nil{}:
      Path.refl(~mach, s)
    case Con{+c, rest}:
      Path.trans(
        ~mach,
        s,
        Adopt.at(~mach, ~Lawful.kernel(mach, lawf), n, s, c),
        Node.adopts(
          ~mach,
          ~Lawful.kernel(mach, lawf),
          n,
          rest,
          Adopt.at(~mach, ~Lawful.kernel(mach, lawf), n, s, c)
        ),
        Adopt.at.path(~mach, ~lawf, n, s, c),
        Adopts.path(~mach, ~lawf, n, rest, Adopt.at(~mach, ~Lawful.kernel(mach, lawf), n, s, c))
      )

# more rounds of a sync, path
def More.path(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  f: Nat,
  +n: String,
  +cs: List<&2, Ledgers.Chain>,
  +k: Nat,
  +bs: List<&2, Ledgers.Ballot>,
  +pd: Tries.Trie<Ledgers.Ballot>,
  +s: Node<Machine.Q(mach)>
) -> Node.On(~mach, s, Sync.more(~mach, ~Lawful.kernel(mach, lawf), f, n, cs, k, bs, pd, s)):
  match f:
    case 0n:
      Path.refl(~mach, s)
    case 1n+(p):
      Path.when(
        ~mach,
        Lines.level(
          ~mach,
          cs,
          s,
          Node.steps(
            ~mach,
            ~Lawful.kernel(mach, lawf),
            n,
            cs,
            Sealed.each(~mach, ~Lawful.kernel(mach, lawf), k, bs, pd, s)
          )
        ),
        s,
        Node.steps(
          ~mach,
          ~Lawful.kernel(mach, lawf),
          n,
          cs,
          Sealed.each(~mach, ~Lawful.kernel(mach, lawf), k, bs, pd, s)
        ),
        Sync.more(
          ~mach,
          ~Lawful.kernel(mach, lawf),
          p,
          n,
          cs,
          k,
          bs,
          pd,
          Node.steps(
            ~mach,
            ~Lawful.kernel(mach, lawf),
            n,
            cs,
            Sealed.each(~mach, ~Lawful.kernel(mach, lawf), k, bs, pd, s)
          )
        ),
        Path.trans(
          ~mach,
          s,
          Sealed.each(~mach, ~Lawful.kernel(mach, lawf), k, bs, pd, s),
          Node.steps(
            ~mach,
            ~Lawful.kernel(mach, lawf),
            n,
            cs,
            Sealed.each(~mach, ~Lawful.kernel(mach, lawf), k, bs, pd, s)
          ),
          Path.same(
            ~mach,
            s,
            Sealed.each(~mach, ~Lawful.kernel(mach, lawf), k, bs, pd, s),
            Each.grows(~mach, ~Lawful.kernel(mach, lawf), k, bs, pd, s),
            Each.heads(~mach, ~Lawful.kernel(mach, lawf), k, bs, pd, s)
          ),
          Steps.path(
            ~mach,
            ~lawf,
            n,
            cs,
            Sealed.each(~mach, ~Lawful.kernel(mach, lawf), k, bs, pd, s)
          )
        ),
        Path.trans(
          ~mach,
          s,
          Node.steps(
            ~mach,
            ~Lawful.kernel(mach, lawf),
            n,
            cs,
            Sealed.each(~mach, ~Lawful.kernel(mach, lawf), k, bs, pd, s)
          ),
          Sync.more(
            ~mach,
            ~Lawful.kernel(mach, lawf),
            p,
            n,
            cs,
            k,
            bs,
            pd,
            Node.steps(
              ~mach,
              ~Lawful.kernel(mach, lawf),
              n,
              cs,
              Sealed.each(~mach, ~Lawful.kernel(mach, lawf), k, bs, pd, s)
            )
          ),
          Path.trans(
            ~mach,
            s,
            Sealed.each(~mach, ~Lawful.kernel(mach, lawf), k, bs, pd, s),
            Node.steps(
              ~mach,
              ~Lawful.kernel(mach, lawf),
              n,
              cs,
              Sealed.each(~mach, ~Lawful.kernel(mach, lawf), k, bs, pd, s)
            ),
            Path.same(
              ~mach,
              s,
              Sealed.each(~mach, ~Lawful.kernel(mach, lawf), k, bs, pd, s),
              Each.grows(~mach, ~Lawful.kernel(mach, lawf), k, bs, pd, s),
              Each.heads(~mach, ~Lawful.kernel(mach, lawf), k, bs, pd, s)
            ),
            Steps.path(
              ~mach,
              ~lawf,
              n,
              cs,
              Sealed.each(~mach, ~Lawful.kernel(mach, lawf), k, bs, pd, s)
            )
          ),
          More.path(
            ~mach,
            ~lawf,
            p,
            n,
            cs,
            k,
            bs,
            pd,
            Node.steps(
              ~mach,
              ~Lawful.kernel(mach, lawf),
              n,
              cs,
              Sealed.each(~mach, ~Lawful.kernel(mach, lawf), k, bs, pd, s)
            )
          )
        )
      )

# a sync is on the paths
def Sync.path(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  +n: String,
  +s: Node<Machine.Q(mach)>,
  +t: Ledgers.State(Machine.Q(mach))
) -> Node.On(~mach, s, Node.sync(~mach, ~Lawful.kernel(mach, lawf), n, s, t)):
  +s1 = Node.take(~mach, ~Lawful.kernel(mach, lawf), s, t)
  +cs = Sync.lines(~mach, s, s1, t)
  +bs = Ballots.of(
    ~mach,
    Tries.Trie.values(
      Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>,
      Ledgers.State.missing(~Machine.Q(mach), ~Machine.same(mach), t, State.ledger(~mach, s))
    )
  )
  +s2 = Node.steps(~mach, ~Lawful.kernel(mach, lawf), n, cs, s1)
  s3 = Sync.more(
    ~mach,
    ~Lawful.kernel(mach, lawf),
    List.length(&2, Ledgers.Ballot, bs),
    n,
    cs,
    List.length(&2, Ledgers.Ballot, bs),
    bs,
    Pending.of(bs),
    s2
  )
  Path.trans(
    ~mach,
    s,
    s1,
    Node.adopts(~mach, ~Lawful.kernel(mach, lawf), n, cs, s3),
    Take.path(~mach, ~Lawful.kernel(mach, lawf), s, t),
    Path.trans(
      ~mach,
      s1,
      s2,
      Node.adopts(~mach, ~Lawful.kernel(mach, lawf), n, cs, s3),
      Steps.path(~mach, ~lawf, n, cs, s1),
      Path.trans(
        ~mach,
        s2,
        s3,
        Node.adopts(~mach, ~Lawful.kernel(mach, lawf), n, cs, s3),
        More.path(
          ~mach,
          ~lawf,
          List.length(&2, Ledgers.Ballot, bs),
          n,
          cs,
          List.length(&2, Ledgers.Ballot, bs),
          bs,
          Pending.of(bs),
          s2
        ),
        Adopts.path(~mach, ~lawf, n, cs, s3)
      )
    )
  )

# a request that a writer asks again at a node is on the paths
def Consent.path(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  n: String,
  +s: Node<Machine.Q(mach)>,
  +i: Ledgers.Id,
  m: Maybe<&2, Ledgers.Chain>
) -> Node.On(~mach, s, Consent.at(~mach, ~Lawful.kernel(mach, lawf), n, s, i, m)):
  match m:
    case None{}:
      Path.refl(~mach, s)
    case Some{c}:
      Path.trans(
        ~mach,
        s,
        State.keyed(~mach, s, Keys.mark(State.keys(~mach, s), i)),
        Node.step(
          ~mach,
          ~Lawful.kernel(mach, lawf),
          n,
          State.keyed(~mach, s, Keys.mark(State.keys(~mach, s), i)),
          c
        ),
        Path.same(
          ~mach,
          s,
          State.keyed(~mach, s, Keys.mark(State.keys(~mach, s), i)),
          Grows.to(
            ~mach,
            s,
            s,
            State.keyed(~mach, s, Keys.mark(State.keys(~mach, s), i)),
            Led.keyed(~mach, s, Keys.mark(State.keys(~mach, s), i)),
            Grows.refl(~mach, s)
          ),
          Heads.keyed(~mach, s, Keys.mark(State.keys(~mach, s), i))
        ),
        Step.path(~mach, ~lawf, n, State.keyed(~mach, s, Keys.mark(State.keys(~mach, s), i)), c)
      )

# what a node does is on the paths
def Does.path(
  ~mach: Machine(),
  ~lawf: Lawful(mach),
  +n: String,
  +s: Node<Machine.Q(mach)>,
  ev: Deed<Machine.Q(mach)>
) -> Node.On(~mach, s, Node.does(~mach, ~Lawful.kernel(mach, lawf), n, s, ev)):
  match ev:
    case Deed.Ask{+e, +q}:
      Path.trans(
        ~mach,
        s,
        Node.ask(~mach, ~Lawful.kernel(mach, lawf), n, s, e, q),
        Adopt.at(
          ~mach,
          ~Lawful.kernel(mach, lawf),
          n,
          Node.ask(~mach, ~Lawful.kernel(mach, lawf), n, s, e, q),
          Arrival.chain(Envelope.of(e), Machine.arrival(mach)(q))
        ),
        Ask.path(~mach, ~lawf, n, s, e, q),
        Adopt.at.path(
          ~mach,
          ~lawf,
          n,
          Node.ask(~mach, ~Lawful.kernel(mach, lawf), n, s, e, q),
          Arrival.chain(Envelope.of(e), Machine.arrival(mach)(q))
        )
      )
    case Deed.Take{t}:
      Take.path(~mach, ~Lawful.kernel(mach, lawf), s, t)
    case Deed.Sync{t}:
      Sync.path(~mach, ~lawf, n, s, t)
    case Deed.Keep{+b}:
      Path.same(
        ~mach,
        s,
        Node.keep(~mach, s, b),
        Grows.keep(~mach, s, Ropes.Put.nodes(Bytes.rope(b))),
        Heads.led(
          ~mach,
          s,
          Ledgers.State.put_datas(
            ~Machine.Q(mach),
            ~Machine.same(mach),
            Ropes.Put.nodes(Bytes.rope(b)),
            State.ledger(~mach, s)
          )
        )
      )
    case Deed.Consent{+i}:
      Path.trans(
        ~mach,
        s,
        Node.consent(~mach, ~Lawful.kernel(mach, lawf), n, s, i),
        Adopt.maybe(
          ~mach,
          ~Lawful.kernel(mach, lawf),
          n,
          Node.consent(~mach, ~Lawful.kernel(mach, lawf), n, s, i),
          Node.chain_of(~mach, s, i)
        ),
        Consent.path(~mach, ~lawf, n, s, i, Node.chain_of(~mach, s, i)),
        Adopt.maybe.path(
          ~mach,
          ~lawf,
          n,
          Node.consent(~mach, ~Lawful.kernel(mach, lawf), n, s, i),
          Node.chain_of(~mach, s, i)
        )
      )
    case Deed.Pass{+c}:
      Path.trans(
        ~mach,
        s,
        Node.pass(~mach, ~Lawful.kernel(mach, lawf), n, s, c),
        Adopt.at(
          ~mach,
          ~Lawful.kernel(mach, lawf),
          n,
          Node.pass(~mach, ~Lawful.kernel(mach, lawf), n, s, c),
          c
        ),
        Pass.path(~mach, ~lawf, n, s, c),
        Adopt.at.path(~mach, ~lawf, n, Node.pass(~mach, ~Lawful.kernel(mach, lawf), n, s, c), c)
      )
    case Deed.Pass{c}:
      Pass.path(~mach, ~lawf, n, s, c)

# every head is on the decided chain: a head that has a tip moves only over
# decided steps, whatever the node does next
law Node.after_on:
  for ~mach: Machine()
  for ~lawf: Lawful(mach)
  for +n: String
  for +evs: List<&2, Deed<Machine.Q(mach)>>
  for +s: Node<Machine.Q(mach)>
  Node.On(~mach, s, Node.after(~mach, ~Lawful.kernel(mach, lawf), n, evs, s))

def Node.after_on(mach, lawf, n, evs, s):
  match evs:
    case Nil{}:
      Path.refl(~mach, s)
    case Con{+ev, rest}:
      s1 = Node.does(~mach, ~Lawful.kernel(mach, lawf), n, s, ev)
      Path.trans(
        ~mach,
        s,
        s1,
        Node.after(~mach, ~Lawful.kernel(mach, lawf), n, rest, s1),
        Does.path(~mach, ~lawf, n, s, ev),
        Node.after_on(~mach, ~lawf, n, rest, s1)
      )

# a node holds what it takes in: an entry that it reads of what was sent, in
# a slot that it lacks, it then holds
law Node.take_holds:
  for ~mach: Machine()
  for ~kern: Kernel(mach)
  for +s: Node<Machine.Q(mach)>
  for +t: Ledgers.State(Machine.Q(mach))
  for +k: List<&2, Bool>
  for e: Ledgers.Entry<Machine.Q(mach)>
  {
    Ledgers.State.get(
      ~Machine.Q(mach),
      Node.reads(~mach, t),
      k
    )
      == Some{Cells.One{e}}: Maybe<&2, Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>>
  }
    -> {
      Ledgers.State.get(
        ~Machine.Q(mach),
        State.ledger(~mach, s),
        k
      )
        == None{}: Maybe<&2, Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>>
    }
    -> {
      Ledgers.State.get(
        ~Machine.Q(mach),
        State.ledger(~mach, Node.take(~mach, ~kern, s, t)),
        k
      )
        == Some{Cells.One{e}}: Maybe<&2, Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>>
    }

def Node.take_holds(mach, kern, s, t, k, e):
  +sent = Node.reads(~mach, t)
  +l1 = Ledgers.State.take(~Machine.Q(mach), State.ledger(~mach, s), sent)
  es => eb =>
    Ledgers.State.one_grows(
      ~Machine.Q(mach),
      ~Machine.same(mach),
      ~Machine.laws(mach),
      State.ledger(~mach, State.led(~mach, s, l1)),
      State.ledger(~mach, Node.take(~mach, ~kern, s, t)),
      k,
      e
    )(Take.tail(~mach, ~kern, s, t))(
      %Equal.sym(Ledgers.State(Machine.Q(mach)), State.ledger(~mach, State.led(~mach, s, l1)), l1, Led.led(~mach, s, l1)): {Ledgers.State.get(~Machine.Q(mach), _, k) == Some{Cells.One{e}}: Maybe<&2, Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>>}
      Equal.trans(Maybe<&2, Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>>, Ledgers.State.get(~Machine.Q(mach), l1, k), Ledgers.State.get(~Machine.Q(mach), sent, k), Some{Cells.One{e}}, Ledgers.State.take_get(~Machine.Q(mach), State.ledger(~mach, s), sent, k)(eb), es))

# Paths
# -----
# Every head is on the decided chain. A node sets a head in four places: a
# step that it checked (Advance.moved), and three that set only a head with no
# tip (Open.at, First.at, Follow.new). So a head that is some decided steps
# from a head with a tip stays so, one more step at a time, whatever the node
# does (Node.after_on).

# Waits
# -----
# A request that a node takes in waits on its line: a pending write goes with
# its writer to another node (Node.take_waits).

# a new request among the cells that a node takes in waits on its line
def Take.asks.adds(
  ~mach: Machine(),
  ~kern: Kernel(mach),
  +pre: List<&2, Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>>,
  post: List<&2, Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>>,
  +old: Ledgers.State(Machine.Q(mach)),
  +s: Node<Machine.Q(mach)>,
  +i: Ledgers.Id,
  time: String,
  +r: Ledgers.Id,
  +l: Maybe<&2, String>,
  +ask: Machine.Q(mach),
  ea: {Machine.arrival(mach)(ask) == Arrival.Waits{r, l}: Arrival}
) -> {
  Ledgers.State.get(
    ~Machine.Q(mach),
    old,
    Ledgers.Slot.ask(i)
  )
    == None{}: Maybe<&2, Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>>
} -> {
  List.contains(
    ~Ledgers.Id,
    ~Ledgers.Id.is_eq,
    Wait.of(
      ~mach,
      Take.asks(
        ~mach,
        ~kern,
        List.append(
          &2,
          Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>,
          pre,
          Cells.One{Ledgers.Entry.Ask{i, time, ask}} <> post
        ),
        old,
        s
      ),
      Line.chain(r, l)
    ),
    i
  )
    == True{}: Bool
}:
  match pre:
    case Nil{}:
      e =>
        %Equal.sym(Arrival, Machine.arrival(mach)(ask), Arrival.Waits{r, l}, ea): {
          List.contains(
            ~Ledgers.Id,
            ~Ledgers.Id.is_eq,
            Wait.of(
              ~mach,
              Take.asks(
                ~mach,
                ~kern,
                post,
                old,
                Shared.Bool.when(
                  Node<Machine.Q(mach)>,
                  Maybe.is_none(
                    &2,
                    Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>,
                    Ledgers.State.get(~Machine.Q(mach), old, Ledgers.Slot.ask(i))
                  ),
                  u => Arrive.at(~mach, ~kern, s, i, _),
                  u => s
                )
              ),
              Line.chain(r, l)
            ),
            i
          )
            == True{}: Bool
        }
        Take.asks.waits(
        ~mach,
        ~kern,
        post,
        old,
        Shared.Bool.when(
          Node<Machine.Q(mach)>,
          Maybe.is_none(
            &2,
            Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>,
            Ledgers.State.get(~Machine.Q(mach), old, Ledgers.Slot.ask(i))
          ),
          u => Arrive.at(~mach, ~kern, s, i, Arrival.Waits{r, l}),
          u => s
        ),
        Line.chain(r, l),
        i
      )(
        %Equal.sym(Maybe<&2, Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>>, Ledgers.State.get(~Machine.Q(mach), old, Ledgers.Slot.ask(i)), None{}, e): {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, Wait.of(~mach, Shared.Bool.when(Node<Machine.Q(mach)>, Maybe.is_none(&2, Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>, _), u => Arrive.at(~mach, ~kern, s, i, Arrival.Waits{r, l}), u => s), Line.chain(r, l)), i) == True{}: Bool}
        Wait.adds(~mach, Node.follow(~mach, s, r, l), Line.chain(r, l), i))
    case Con{Cells.One{Ledgers.Entry.Ask{j, t, q}}, rest}:
      e => Take.asks.adds(
        ~mach,
        ~kern,
        rest,
        post,
        old,
        Shared.Bool.when(
          Node<Machine.Q(mach)>,
          Maybe.is_none(
            &2,
            Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>,
            Ledgers.State.get(~Machine.Q(mach), old, Ledgers.Slot.ask(j))
          ),
          u => Node.arrive(~mach, ~kern, s, j, q),
          u => s
        ),
        i,
        time,
        r,
        l,
        ask,
        ea
      )(e)
    case Con{Cells.One{Ledgers.Entry.Vote{v}}, rest}:
      Take.asks.adds(~mach, ~kern, rest, post, old, s, i, time, r, l, ask, ea)
    case Con{Cells.One{Ledgers.Entry.Data{d}}, rest}:
      Take.asks.adds(~mach, ~kern, rest, post, old, s, i, time, r, l, ask, ea)
    case Con{Cells.Many{}, rest}:
      Take.asks.adds(~mach, ~kern, rest, post, old, s, i, time, r, l, ask, ea)

# a pending request goes with its writer to another node: a request that a
# node takes in, and that waits on a line (its arrival), waits on that line
# there
law Node.take_waits:
  for ~mach: Machine()
  for ~kern: Kernel(mach)
  for +s: Node<Machine.Q(mach)>
  for +t: Ledgers.State(Machine.Q(mach))
  for +i: Ledgers.Id
  for +time: String
  for +ask: Machine.Q(mach)
  for +r: Ledgers.Id
  for +l: Maybe<&2, String>
  {Machine.arrival(mach)(ask) == Arrival.Waits{r, l}: Arrival}
    -> {
      Ledgers.State.get(
        ~Machine.Q(mach),
        Node.reads(~mach, t),
        Ledgers.Slot.ask(i)
      )
        == Some{Cells.One{Ledgers.Entry.Ask{i, time, ask}}}: Maybe<&2, Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>>
    }
    -> {
      Ledgers.State.get(
        ~Machine.Q(mach),
        State.ledger(~mach, s),
        Ledgers.Slot.ask(i)
      )
        == None{}: Maybe<&2, Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>>
    }
    -> {
      List.contains(
        ~Ledgers.Id,
        ~Ledgers.Id.is_eq,
        Wait.of(~mach, Node.take(~mach, ~kern, s, t), Line.chain(r, l)),
        i
      )
        == True{}: Bool
    }

def Node.take_waits(mach, kern, s, t, i, time, ask, r, l):
  +sent = Node.reads(~mach, t)
  l1 = Ledgers.State.take(~Machine.Q(mach), State.ledger(~mach, s), sent)
  +s1 = State.led(~mach, s, l1)
  cs = Tries.Trie.values(Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>, sent)
  +s2 = Take.asks(
    ~mach,
    ~kern,
    cs,
    State.ledger(~mach, s),
    s1
  )
  +bs = Ballots.of(
    ~mach,
    Tries.Trie.values(
      Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>,
      Ledgers.State.missing(
        ~Machine.Q(mach),
        ~Machine.same(mach),
        t,
        State.ledger(~mach, s)
      )
    )
  )
  cell = {
    Cells.One{
      Ledgers.Entry.Ask{i, time, ask}
    }: Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>
  }
  ea => es => eb =>
    %Wait.same(
      ~mach,
      s2,
      Sealed.take(~mach, ~kern, bs, s2),
      Line.chain(r, l),
      Each.waiting(
        ~mach,
        ~kern,
        List.length(&2, Ledgers.Ballot, bs),
        bs,
        Pending.of(bs),
        s2
      )
    ): {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, _, i) == True{}: Bool}
    %Equal.sym(
      List<&2, Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>>,
      cs,
      List.append(
        &2,
        Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>,
        Tries.Trie.before(Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>, sent, Ledgers.Slot.ask(i)),
        cell <> Tries.Trie.after(Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>, sent, Ledgers.Slot.ask(i))
      ),
      Tries.Trie.values_around(
        Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>,
        sent,
        Ledgers.Slot.ask(i),
        cell
      )(es)
    ): {
      List.contains(
        ~Ledgers.Id,
        ~Ledgers.Id.is_eq,
        Wait.of(
          ~mach,
          Take.asks(
            ~mach,
            ~kern,
            _,
            State.ledger(~mach, s),
            s1
          ),
          Line.chain(r, l)
        ),
        i
      )
        == True{}: Bool
    }
    Take.asks.adds(
      ~mach,
      ~kern,
      Tries.Trie.before(Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>, sent, Ledgers.Slot.ask(i)),
      Tries.Trie.after(Cells.Cell<Ledgers.Entry<Machine.Q(mach)>>, sent, Ledgers.Slot.ask(i)),
      State.ledger(~mach, s),
      s1,
      i,
      time,
      r,
      l,
      ask,
      ea
    )(eb)
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information
# bend-lint: expect-end bend-lint-rules/performance/missed_fork@hint
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information
