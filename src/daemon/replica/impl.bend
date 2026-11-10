import Base
import ../../shared.bend as Shared
import ../shared/ledger.bend as Ledgers
import ../shared/resources.bend as Resources
import ../shared/rope.bend as Ropes
import ../shared/shared/quorum.bend as Quorums
import ../shared/shared/shared/cell.bend as Cells
import ../shared/shared/shared/code.bend as Codes
import ../shared/shared/shared/hash.bend as Hashes
import ../shared/shared/shared/seal.bend as Seals
import ../shared/shared/shared/trie.bend as Tries
import ../shared/shared/store.bend as Stores
import ../shared/shared/text.bend as Texts
import ../shared/tree.bend as Trees

# Replicas
# --------
# A replica is a node of a replicated machine: it holds a ledger that only
# grows, a head of each line that it follows, the requests that wait, and its
# keys. It is generic over the machine: what a request is, and what a request
# does to a line. src/daemon/core gives the machine of Vend.

# a machine: its requests; when two are the same, and that this is equality;
# how a request arrives at a node; whether it changes who decides; and the key
# of the first key of a node in the content of a store
def Machine() -> Type:
  &Q: Data -> &same: (Q -> Q -> Bool) -> Shared.Eq.Laws(
    Q,
    same
  ) & ((Q -> Arrival) & ((Q -> Bool) & (String -> List<&2, U32>)))

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
def State.ledger(~M: Machine(), s: Node<Machine.Q(M)>) -> Ledgers.State(Machine.Q(M)):
  match s:
    case Node{l, hs, ws, ks}:
      l

# the heads of s
def State.heads(~M: Machine(), s: Node<Machine.Q(M)>) -> Tries.Trie<Head>:
  match s:
    case Node{l, hs, ws, ks}:
      hs

# the requests of s that wait for a step, by line
def State.waiting(~M: Machine(), s: Node<Machine.Q(M)>) -> Tries.Trie<List<&2, Ledgers.Id>>:
  match s:
    case Node{l, hs, ws, ks}:
      ws

# the keys of s
def State.keys(~M: Machine(), s: Node<Machine.Q(M)>) -> Keys:
  match s:
    case Node{l, hs, ws, ks}:
      ks

# s with the ledger l
def State.led(~M: Machine(), s: Node<Machine.Q(M)>, l: Ledgers.State(Machine.Q(M))) -> Node<Machine.Q(M)>:
  match s:
    case Node{old, hs, ws, ks}:
      Node{l, hs, ws, ks}

# s with the keys ks
def State.keyed(~M: Machine(), s: Node<Machine.Q(M)>, ks: Keys) -> Node<Machine.Q(M)>:
  match s:
    case Node{l, hs, ws, old}:
      Node{l, hs, ws, ks}

# a node that holds nothing yet, with the secret seed
def Node.empty(~M: Machine(), seed: Hashes.Hash) -> Node<Machine.Q(M)>:
  Node{
    Ledgers.State.empty(~Machine.Q(M)),
    Tries.Trie.new(Head),
    Tries.Trie.new(List<&2, Ledgers.Id>),
    Keys{seed, Tries.Trie.new(Keychain), Tries.Trie.new(Unit), Tries.Trie.new(Nat)}
  }

# the words that s holds under the hash h
def Store.fetch(~M: Machine(), s: Node<Machine.Q(M)>, h: Hashes.Hash) -> Maybe<&2, List<&2, U32>>:
  Ledgers.State.data(~Machine.Q(M), State.ledger(~M, s), h)

# s with the words ds as data, each under its hash
def State.keep(~M: Machine(), +s: Node<Machine.Q(M)>, ds: List<&2, List<&2, U32>>) -> Node<Machine.Q(M)>:
  State.led(~M, s, Ledgers.State.put_datas(~Machine.Q(M), ~Machine.same(M), ds, State.ledger(~M, s)))

# the request i, when s holds it
def Node.asked(~M: Machine(), s: Node<Machine.Q(M)>, i: Ledgers.Id) -> Maybe<&2, Ledgers.Asked<Machine.Q(M)>>:
  Ledgers.State.asked(~Machine.Q(M), State.ledger(~M, s), i)

# what the tree whose root is h holds under the key k, in the store s
def Node.get(~M: Machine(), +s: Node<Machine.Q(M)>, h: Maybe<&2, Hashes.Hash>, k: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  Trees.Tree.get(~Node<Machine.Q(M)>, ~Store.fetch(~M), s, h, k)

# the tree whose root is h with the key k set to x
def Node.set(
  ~M: Machine(),
  +s: Node<Machine.Q(M)>,
  +h: Maybe<&2, Hashes.Hash>,
  k: List<&2, U32>,
  x: List<&2, U32>
) -> Maybe<&2, Trees.Put>:
  Trees.Tree.set(~Node<Machine.Q(M)>, ~Store.fetch(~M), s, h, k, x)

# what a read of the key k finds in the tree whose root is h
def Node.look(~M: Machine(), +s: Node<Machine.Q(M)>, +h: Maybe<&2, Hashes.Hash>, k: List<&2, U32>) -> Trees.Look:
  Trees.Tree.look(~Node<Machine.Q(M)>, ~Store.fetch(~M), s, h, k)

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
  ~M: Machine(),
  s: Node<Machine.Q(M)>,
  h: Maybe<&2, Hashes.Hash>,
  k: List<&2, U32>
) -> Maybe<&2, Maybe<&2, List<&2, U32>>>:
  Look.known(Node.look(~M, s, h, k))

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
def Tip.at(~M: Machine(), s: Node<Machine.Q(M)>, h: Hashes.Hash) -> Maybe<&2, Tip>:
  Maybe.bind(&2, List<&2, U32>, Tip, Store.fetch(~M, s, h), ws => Tip.read(ws))

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

# bend-lint: expect-begin bend-lint-rules/layout/case@warning -- a constructor is PascalCase, as in Base (Some, Con): the rule reads a constructor as a law
# the outcome of a request: its owners refused it as stale, or took it as the
# version of a number
type Out is Data:
  Out.Stale{}
  Out.Taken{number: U32}
# bend-lint: expect-end bend-lint-rules/layout/case@warning

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
def Line.out(~M: Machine(), s: Node<Machine.Q(M)>, t: Tip, i: Ledgers.Id) -> Maybe<&2, Out>:
  Maybe.bind(&2, List<&2, U32>, Out, Node.get(~M, s, Tip.log(t), Log.out(i)), ws => Out.read(ws))

# the version of the number n of a line at the tip t
def Line.version(~M: Machine(), s: Node<Machine.Q(M)>, t: Tip, n: U32) -> Maybe<&2, Version>:
  Maybe.bind(
    &2,
    List<&2, U32>,
    Version,
    Node.get(~M, s, Tip.log(t), Log.version(n)),
    ws => Version.read(ws)
  )

# the version that the mark m names on a line at the tip t
def Line.mark(~M: Machine(), s: Node<Machine.Q(M)>, t: Tip, m: String) -> Maybe<&2, Ledgers.Id>:
  Maybe.bind(
    &2,
    List<&2, U32>,
    Ledgers.Id,
    Node.get(~M, s, Tip.log(t), Log.mark(m)),
    ws => Read.whole(Ledgers.Id, Ledgers.Id.code.read(ws))
  )

# the node's head of the line c, if it follows c
def Node.head_of(~M: Machine(), s: Node<Machine.Q(M)>, c: Ledgers.Chain) -> Maybe<&2, Head>:
  Tries.Trie.get(Head, State.heads(~M, s), Ledgers.Chain.key(c))

# the tip of the head h, when s holds it
def Head.tip(~M: Machine(), s: Node<Machine.Q(M)>, h: Head) -> Maybe<&2, Tip>:
  match h:
    case Head{r, b, n, t}:
      Maybe.bind(&2, Hashes.Hash, Tip, t, x => Tip.at(~M, s, x))

# what the line c holds now, as the node knows it
def Node.tip(~M: Machine(), +s: Node<Machine.Q(M)>, c: Ledgers.Chain) -> Maybe<&2, Tip>:
  Maybe.bind(&2, Head, Tip, Node.head_of(~M, s, c), h => Head.tip(~M, s, h))

# what the log of the head h holds under the key k
def Head.get(~M: Machine(), +s: Node<Machine.Q(M)>, h: Head, k: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  Maybe.bind(&2, Tip, List<&2, U32>, Head.tip(~M, s, h), t => Node.get(~M, s, Tip.log(t), k))

# what the log of the line c holds under the key k, as the node knows it
def Line.get(~M: Machine(), +s: Node<Machine.Q(M)>, c: Ledgers.Chain, k: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  Maybe.bind(&2, Head, List<&2, U32>, Node.head_of(~M, s, c), h => Head.get(~M, s, h, k))

# the change of the request a
def Asked.ask(~M: Machine(), a: Ledgers.Asked<Machine.Q(M)>) -> Machine.Q(M):
  match a:
    case Ledgers.Asked{t, q}:
      q

# the outcome of the request i on the line c, as the node knows it
def Chain.out(~M: Machine(), s: Node<Machine.Q(M)>, c: Ledgers.Chain, i: Ledgers.Id) -> Maybe<&2, Out>:
  Maybe.bind(&2, List<&2, U32>, Out, Line.get(~M, s, c, Log.out(i)), ws => Out.read(ws))

# the version of the number n of the line c, as the node knows it
def Chain.version(~M: Machine(), s: Node<Machine.Q(M)>, c: Ledgers.Chain, n: U32) -> Maybe<&2, Version>:
  Maybe.bind(&2, List<&2, U32>, Version, Line.get(~M, s, c, Log.version(n)), ws => Version.read(ws))

# the version that the mark m names on the line c, as the node knows it
def Chain.mark(~M: Machine(), s: Node<Machine.Q(M)>, c: Ledgers.Chain, m: String) -> Maybe<&2, Ledgers.Id>:
  Maybe.bind(
    &2,
    List<&2, U32>,
    Ledgers.Id,
    Line.get(~M, s, c, Log.mark(m)),
    ws => Read.whole(Ledgers.Id, Ledgers.Id.code.read(ws))
  )

# trees being written: the root, and the node that holds what was written
type Work<-Q: Data> is Data:
  Work{state: Node<Q>, root: Maybe<&2, Hashes.Hash>}

# bend-lint: expect-begin bend-lint-rules/layout/case@warning -- a constructor is PascalCase, as in Base (Some, Con): the rule reads a constructor as a law
# what a judge says of one change: refuse it as stale, or take it, with the
# trees that it wrote
type Verdict<-Q: Data> is Data:
  Verdict.Stale{}
  Verdict.Taken{work: Work<Q>}
# bend-lint: expect-end bend-lint-rules/layout/case@warning

# s with the words ds as data, when it then holds each of them under its hash
# (none: a slot holds other words). A node reads back what it puts, so what a
# tree or a rope reads after a put never rests on what the store held before
def State.put(~M: Machine(), s: Node<Machine.Q(M)>, +ds: List<&2, List<&2, U32>>) -> Maybe<&2, Node<Machine.Q(M)>>:
  +s2 = State.keep(~M, s, ds)
  Shared.Maybe.when(
    Node<Machine.Q(M)>,
    Stores.Store.holds(~Node<Machine.Q(M)>, ~Store.fetch(~M), s2, ds),
    u => Some{s2}
  )

# the work at the root h on the state m
def Work.on(~M: Machine(), m: Maybe<&2, Node<Machine.Q(M)>>, h: Maybe<&2, Hashes.Hash>) -> Maybe<&2, Work<Machine.Q(M)>>:
  match m:
    case None{}:
      None{}
    case Some{s2}:
      Some{Work{s2, h}}

# the work that the new subtree m gives on the state s
def Work.of(~M: Machine(), s: Node<Machine.Q(M)>, m: Maybe<&2, Trees.Put>) -> Maybe<&2, Work<Machine.Q(M)>>:
  match m:
    case None{}:
      None{}
    case Some{Trees.Put{h, ws}}:
      Work.on(~M, State.put(~M, s, ws), Some{h})

# w with the key k set to the value x (none: the store lacks a node)
def Work.set(~M: Machine(), w: Work<Machine.Q(M)>, k: List<&2, U32>, x: List<&2, U32>) -> Maybe<&2, Work<Machine.Q(M)>>:
  match w:
    case Work{+s, h}:
      Work.of(~M, s, Node.set(~M, s, h, k, x))

# w with the words ns as data
def Work.keep(~M: Machine(), w: Work<Machine.Q(M)>, ns: List<&2, List<&2, U32>>) -> Maybe<&2, Work<Machine.Q(M)>>:
  match w:
    case Work{s, h}:
      Work.on(~M, State.put(~M, s, ns), h)

# the root of w
def Work.root(~M: Machine(), w: Work<Machine.Q(M)>) -> Maybe<&2, Hashes.Hash>:
  match w:
    case Work{s, h}:
      h

# a verdict that takes the trees of m (none: wait)
def Work.take(~M: Machine(), m: Maybe<&2, Work<Machine.Q(M)>>) -> Maybe<&2, Verdict<Machine.Q(M)>>:
  match m:
    case None{}:
      None{}
    case Some{w}:
      Some{Verdict.Taken{w}}

# the first tip of a new branch, and the node that holds it
type Made<-Q: Data> is Data:
  Made{tip: Tip, node: Node<Q>}

# the first tip t of a branch, once the trees of m hold it
def Made.put(~M: Machine(), t: Tip, m: Maybe<&2, Work<Machine.Q(M)>>) -> Maybe<&2, Made<Machine.Q(M)>>:
  match m:
    case None{}:
      None{}
    case Some{Work{s, l}}:
      Some{Made{t, s}}

# a run: the node that holds what it wrote, and the tip so far
type Run<-Q: Data> is Data:
  Run{state: Node<Q>, tip: Tip}

# the state of the run r
def Run.state(~M: Machine(), r: Run<Machine.Q(M)>) -> Node<Machine.Q(M)>:
  match r:
    case Run{s, t}:
      s

# the tip of the run r
def Run.tip(~M: Machine(), r: Run<Machine.Q(M)>) -> Tip:
  match r:
    case Run{s, t}:
      t

# the run of the state and the log of the work m, at the tip t
def Run.logged(~M: Machine(), t: Tip, m: Maybe<&2, Work<Machine.Q(M)>>) -> Maybe<&2, Run<Machine.Q(M)>>:
  match t m:
    case x None{}:
      None{}
    case Tip{c, old, n, os} Some{Work{s, l}}:
      Some{Run{s, Tip{c, l, n, os}}}

# Run.add once the value m of the key in the log is known
def Run.add.at(
  ~M: Machine(),
  r: Run<Machine.Q(M)>,
  k: List<&2, U32>,
  x: List<&2, U32>,
  m: Maybe<&2, List<&2, U32>>
) -> Maybe<&2, Run<Machine.Q(M)>>:
  match r m:
    case Run{s, +t} None{}:
      Run.logged(~M, t, Work.set(~M, Work{s, Tip.log(t)}, k, x))
    case y Some{old}:
      None{}

# the run r with the new key k of its log set to x (none: the log holds k, or
# the node lacks a node). A log only gains keys: no other def writes a log
def Run.add(~M: Machine(), +r: Run<Machine.Q(M)>, +k: List<&2, U32>, x: List<&2, U32>) -> Maybe<&2, Run<Machine.Q(M)>>:
  Run.add.at(~M, r, k, x, Node.get(~M, Run.state(~M, r), Tip.log(Run.tip(~M, r)), k))

# the tip t with the content h
def Tip.over(t: Tip, h: Maybe<&2, Hashes.Hash>) -> Tip:
  match t:
    case Tip{c, l, n, os}:
      Tip{h, l, n, os}

# the run r on the node s2, which a judge grew from the node of r, with the
# content h
def Run.over(~M: Machine(), r: Run<Machine.Q(M)>, s2: Node<Machine.Q(M)>, h: Maybe<&2, Hashes.Hash>) -> Run<Machine.Q(M)>:
  Run{s2, Tip.over(Run.tip(~M, r), h)}

# the tip t one version on, with the owners of the next step that the change
# gives, if it gives any
def Tip.next(t: Tip, own: Maybe<&2, List<&2, String>>) -> Tip:
  match t:
    case Tip{c, l, n, os}:
      Tip{c, l, U32.inc(n), Maybe.default(&2, List<&2, String>, own, os)}

# the run r one version on (Tip.next)
def Run.next(~M: Machine(), r: Run<Machine.Q(M)>, own: Maybe<&2, List<&2, String>>) -> Run<Machine.Q(M)>:
  match r:
    case Run{s, t}:
      Run{s, Tip.next(t, own)}

# the run r, after it refused the request i as stale
def Step.stale(~M: Machine(), r: Run<Machine.Q(M)>, i: Ledgers.Id) -> Maybe<&2, Run<Machine.Q(M)>>:
  Run.add(~M, r, Log.out(i), Out.words(Out.Stale{}))

# the run r, after it took the request i as the version of the number n: its
# outcome, its version (the content of r), the count, and the owners that it
# gives
def Step.taken.at(
  ~M: Machine(),
  r: Run<Machine.Q(M)>,
  +i: Ledgers.Id,
  +n: U32,
  own: Maybe<&2, List<&2, String>>
) -> Maybe<&2, Run<Machine.Q(M)>>:
  Maybe.bind(
    &2,
    Run<Machine.Q(M)>,
    Run<Machine.Q(M)>,
    Run.add(~M, r, Log.out(i), Out.words(Out.Taken{n})),
    +r1 => Maybe.bind(
      &2,
      Run<Machine.Q(M)>,
      Run<Machine.Q(M)>,
      Run.add(~M, 
        r1,
        Log.version(n),
        Version.words(Version{i, Tip.content(Run.tip(~M, r1))})
      ),
      r2 => Some{Run.next(~M, r2, own)}
    )
  )

# the run r, after it took the request i as its next version
def Step.taken(~M: Machine(), +r: Run<Machine.Q(M)>, i: Ledgers.Id, own: Maybe<&2, List<&2, String>>) -> Maybe<&2, Run<Machine.Q(M)>>:
  Step.taken.at(~M, r, i, Tip.count(Run.tip(~M, r)), own)

# the run r, after the verdict m on the request i (none: wait)
def Step.judged(
  ~M: Machine(),
  r: Run<Machine.Q(M)>,
  i: Ledgers.Id,
  own: Maybe<&2, List<&2, String>>,
  m: Maybe<&2, Verdict<Machine.Q(M)>>
) -> Maybe<&2, Run<Machine.Q(M)>>:
  match m:
    case None{}:
      None{}
    case Some{Verdict.Stale{}}:
      Step.stale(~M, r, i)
    case Some{Verdict.Taken{Work{s2, h}}}:
      Step.taken(~M, Run.over(~M, r, s2, h), i, own)

# the run r with the mark m on the version v, then the request i taken
def Step.marked(~M: Machine(), r: Run<Machine.Q(M)>, i: Ledgers.Id, m: String, v: Maybe<&2, Version>) -> Maybe<&2, Run<Machine.Q(M)>>:
  match v:
    case None{}:
      None{}
    case Some{x}:
      Maybe.bind(
        &2,
        Run<Machine.Q(M)>,
        Run<Machine.Q(M)>,
        Run.add(~M, r, Log.mark(m), Ledgers.Id.code(Version.id(x), [])),
        r2 => Step.taken(~M, r2, i, None{})
      )

# the run r, after a request i for the mark m: it names the newest version,
# for good; a mark that the line has, or a line with no version, refuses it
def Step.mark(~M: Machine(), +r: Run<Machine.Q(M)>, +i: Ledgers.Id, +m: String) -> Maybe<&2, Run<Machine.Q(M)>>:
  +s = Run.state(~M, r)
  +t = Run.tip(~M, r)
  +n = Tip.count(t)
  Shared.Bool.when(
    Maybe<&2, Run<Machine.Q(M)>>,
    List.all.if(
      u => Maybe.is_none(&2, Ledgers.Id, Line.mark(~M, s, t, m)),
      Bool.not(U32.is_eq(n, 0))
    ),
    u => Step.marked(~M, r, i, m, Line.version(~M, s, t, U32.sub(n, 1))),
    u => Step.stale(~M, r, i)
  )

# the run r with the first tip m of the new branch b of its store in its log,
# then the request i taken (none: the node lacks a node)
def Branch.made(~M: Machine(), +r: Run<Machine.Q(M)>, i: Ledgers.Id, b: String, m: Maybe<&2, Made<Machine.Q(M)>>) -> Maybe<&2, Run<Machine.Q(M)>>:
  match m:
    case None{}:
      None{}
    case Some{Made{t, s2}}:
      Maybe.bind(
        &2,
        Run<Machine.Q(M)>,
        Run<Machine.Q(M)>,
        Run.add(~M, 
          Run.over(~M, r, s2, Tip.content(Run.tip(~M, r))),
          Log.start(b),
          Hashes.Hash.code(Tip.hash(t), [])
        ),
        r2 => Step.taken(~M, r2, i, None{})
      )

# the requests of a step that a node can run now, in order, and the run after
# them
type Picked<-Q: Data> is Data:
  Picked{run: Run<Q>, asks: List<&2, Ledgers.Id>}

# the run of p
def Picked.run(~M: Machine(), p: Picked<Machine.Q(M)>) -> Run<Machine.Q(M)>:
  match p:
    case Picked{r, qs}:
      r

# the requests of p
def Picked.asks(~M: Machine(), p: Picked<Machine.Q(M)>) -> List<&2, Ledgers.Id>:
  match p:
    case Picked{r, qs}:
      qs

# p, with the request i before its requests when b holds
def Picked.add(~M: Machine(), b: Bool, i: Ledgers.Id, p: Picked<Machine.Q(M)>) -> Picked<Machine.Q(M)>:
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

# a first owner reads back
def Owner.code_read(
  x: Owner,
  r: List<&2, U32>
) -> {
  Owner.code.read(
    Owner.code(x, r)
  )
    == Some{Codes.Read{x, r}}: Maybe<&2, Codes.Read<Owner>>
}:
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

# Kernels
# -------
# A kernel is a machine and what one of its requests does to a run.

# bend-lint: expect-begin bend-lint-rules/layout/case@warning -- a constructor is PascalCase, as in Base (Some, Con): the rule reads a constructor as a law
# how a request arrives at a node: it starts a store, with its first owners,
# or it waits on a line of a store
type Arrival is Data:
  Arrival.Starts{owners: List<&2, Owner>}
  Arrival.Waits{store: Ledgers.Id, line: Maybe<&2, String>}
# bend-lint: expect-end bend-lint-rules/layout/case@warning

# the line of the request i, which arrives as a: a store that starts is its
# own line
def Arrival.chain(i: Ledgers.Id, a: Arrival) -> Ledgers.Chain:
  match a:
    case Arrival.Starts{os}:
      Ledgers.Chain{i, None{}}
    case Arrival.Waits{r, l}:
      Line.chain(r, l)

# a kernel: a machine; what a request does to the run of a line; and the
# request, if any, that a node asks by itself after it works on a line of a
# store
def Kernel() -> Type:
  &M: Machine() -> (
    Run<Machine.Q(M)> -> Ledgers.Chain -> Ledgers.Id -> Machine.Q(M) -> Maybe<&2, Run<Machine.Q(M)>>
  ) & (Node<Machine.Q(M)> -> Ledgers.Id -> Maybe<&2, String> -> Maybe<&2, Request<Machine.Q(M)>>)

# the machine of the kernel k
def Kernel.machine(k: Kernel()) -> Machine():
  match k:
    case Tuple{m, h}:
      m

# what a request of the kernel k does to the run of a line
def Kernel.change(
  k: Kernel()
) -> Run<Machine.Q(Kernel.machine(k))> -> Ledgers.Chain -> Ledgers.Id -> Machine.Q(Kernel.machine(k)) -> Maybe<&2, Run<Machine.Q(Kernel.machine(k))>>:
  match k:
    case Tuple{m, Tuple{c, f}}:
      c

# the request that a node of the kernel k asks by itself after it works on a
# line of a store
def Kernel.follow(
  k: Kernel()
) -> Node<Machine.Q(Kernel.machine(k))> -> Ledgers.Id -> Maybe<&2, String> -> Maybe<&2, Request<Machine.Q(Kernel.machine(k))>>:
  match k:
    case Tuple{m, Tuple{c, f}}:
      f

# the run r of the line c, after the request i, which the node holds as a
# (none: wait for the request)
def Step.asked(
  ~K: Kernel(),
  r: Run<Machine.Q(Kernel.machine(K))>,
  c: Ledgers.Chain,
  i: Ledgers.Id,
  a: Maybe<&2, Ledgers.Asked<Machine.Q(Kernel.machine(K))>>
) -> Maybe<&2, Run<Machine.Q(Kernel.machine(K))>>:
  match a:
    case None{}:
      None{}
    case Some{Ledgers.Asked{t, q}}:
      Kernel.change(K)(r)(c)(i)(q)

# the run r of the line c, after the request i, whose outcome in the log is o:
# a request that has one is skipped
def Step.fresh(
  ~K: Kernel(),
  +r: Run<Machine.Q(Kernel.machine(K))>,
  c: Ledgers.Chain,
  +i: Ledgers.Id,
  o: Maybe<&2, Out>
) -> Maybe<&2, Run<Machine.Q(Kernel.machine(K))>>:
  match o:
    case Some{x}:
      Some{r}
    case None{}:
      Step.asked(~K, r, c, i, Node.asked(~Kernel.machine(K), Run.state(~Kernel.machine(K), r), i))

# the run r of the line c, after the request i
def Step.one(~K: Kernel(), +r: Run<Machine.Q(Kernel.machine(K))>, c: Ledgers.Chain, +i: Ledgers.Id) -> Maybe<&2, Run<Machine.Q(Kernel.machine(K))>>:
  Step.fresh(~K, r, c, i, Line.out(~Kernel.machine(K), Run.state(~Kernel.machine(K), r), Run.tip(~Kernel.machine(K), r), i))

# the run m of the line c, after each request of is, in order
def Step.all(~K: Kernel(), +c: Ledgers.Chain, qs: List<&2, Ledgers.Id>, m: Maybe<&2, Run<Machine.Q(Kernel.machine(K))>>) -> Maybe<&2, Run<Machine.Q(Kernel.machine(K))>>:
  match qs:
    case Nil{}:
      m
    case Con{i, rest}:
      Step.all(~K, c, rest, Maybe.bind(&2, Run<Machine.Q(Kernel.machine(K))>, Run<Machine.Q(Kernel.machine(K))>, m, r => Step.one(~K, r, c, i)))

# the requests of qs that can run now on the line c, from the run r, and the
# run after them. A request that must wait (for a version, a request or a
# node) is left out: it waits, and does not stop the others
def Step.some(~K: Kernel(), +c: Ledgers.Chain, qs: List<&2, Ledgers.Id>, +r: Run<Machine.Q(Kernel.machine(K))>) -> Picked<Machine.Q(Kernel.machine(K))>:
  match qs:
    case Nil{}:
      Picked{r, []}
    case Con{+i, rest}:
      +m = Step.one(~K, r, c, i)
      Picked.add(~Kernel.machine(K), Maybe.is_some(&2, Run<Machine.Q(Kernel.machine(K))>, m), i, Step.some(~K, c, rest, Maybe.default(&2, Run<Machine.Q(Kernel.machine(K))>, m, r)))

# the step of the line c that runs the requests qs from the tip t (none: wait
# for a request, a version or a node)
def Step.run(
  ~K: Kernel(),
  s: Node<Machine.Q(Kernel.machine(K))>,
  c: Ledgers.Chain,
  t: Tip,
  qs: List<&2, Ledgers.Id>
) -> Maybe<&2, Run<Machine.Q(Kernel.machine(K))>>:
  Step.all(~K, c, qs, Some{Run{s, t}})

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
def Seal.first(~K: Kernel(), +s: Node<Machine.Q(Kernel.machine(K))>, r: Ledgers.Id, n: String) -> Maybe<&2, Hashes.Hash>:
  Seal.read(
    Node.get(~Kernel.machine(K), 
      s,
      Maybe.bind(
        &2,
        Tip,
        Hashes.Hash,
        Node.tip(~Kernel.machine(K), s, Ledgers.Chain{r, None{}}),
        t => Tip.content(t)
      ),
      Machine.seal(Kernel.machine(K))(n)
    )
  )

# the chain c, when it starts from the first key m; else a new chain from m
# (none: the store gave the node no key)
def Keychain.from(
  m: Maybe<&2, Hashes.Hash>,
  c: Maybe<&2, Keychain>
) -> Maybe<&2, Keychain>:
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
def Round.seen(~M: Machine(), s: Node<Machine.Q(M)>, c: Ledgers.Chain, h: U32) -> Nat:
  Rounds.at(Keys.rounds(State.keys(~M, s)), c, h)

# the chain of the node n in the store r, as s knows it
def Seal.chain(~K: Kernel(), +s: Node<Machine.Q(Kernel.machine(K))>, +r: Ledgers.Id, +n: String) -> Maybe<&2, Keychain>:
  Keychain.from(
    Seal.first(~K, s, r, n),
    Tries.Trie.get(Keychain, Keys.chains(State.keys(~Kernel.machine(K), s)), Seal.slot(r, n))
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
  ~M: Machine(),
  +s: Node<Machine.Q(M)>,
  +b: Ledgers.Ballot,
  m: Maybe<&2, Keychain>
) -> Maybe<&2, Node<Machine.Q(M)>>:
  match m:
    case None{}:
      None{}
    case Some{+c}:
      Shared.Maybe.when(
        Node<Machine.Q(M)>,
        Seal.fits(c, b),
        u => Some{
          State.keyed(~M, 
            State.led(~M, 
              s,
              Ledgers.State.keep(~Machine.Q(M), ~Machine.same(M), State.ledger(~M, s), b)
            ),
            Keys.saw(
              Keys.set(
                State.keys(~M, s),
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
def Seal.accept(~K: Kernel(), +s: Node<Machine.Q(Kernel.machine(K))>, +b: Ledgers.Ballot) -> Maybe<&2, Node<Machine.Q(Kernel.machine(K))>>:
  Seal.accept.at(~Kernel.machine(K), s, b, Seal.chain(~K, s, Ballot.store(b), Ballot.node(b)))

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
  ~K: Kernel(),
  s: Node<Machine.Q(Kernel.machine(K))>,
  p: Tries.Trie<Ledgers.Ballot>,
  +r: Ledgers.Id,
  +n: String
) -> Maybe<&2, Ledgers.Ballot>:
  Maybe.bind(
    &2,
    Keychain,
    Ledgers.Ballot,
    Seal.chain(~K, s, r, n),
    c => Tries.Trie.get(Ledgers.Ballot, p, Seal.link(r, n, Keychain.last(c)))
  )

# s with each ballot of p that the chain of the node n in the store r leads
# to, from the ballot mb, f ballots at most
def Sealed.follow(
  ~K: Kernel(),
  f: Nat,
  +s: Node<Machine.Q(Kernel.machine(K))>,
  +p: Tries.Trie<Ledgers.Ballot>,
  +r: Ledgers.Id,
  +n: String,
  mb: Maybe<&2, Ledgers.Ballot>
) -> Node<Machine.Q(Kernel.machine(K))>:
  match f mb:
    case 1n+g Some{b}:
      Maybe.default(
        &2,
        Node<Machine.Q(Kernel.machine(K))>,
        Maybe.bind(
          &2,
          Node<Machine.Q(Kernel.machine(K))>,
          Node<Machine.Q(Kernel.machine(K))>,
          Seal.accept(~K, s, b),
          +s2 => Some{Sealed.follow(~K, g, s2, p, r, n, Pending.next(~K, s2, p, r, n))}
        ),
        s
      )
    case x y:
      s

# s with the ballots of p that the chains of the ballots bs lead to
def Sealed.each(
  ~K: Kernel(),
  +f: Nat,
  bs: List<&2, Ledgers.Ballot>,
  +p: Tries.Trie<Ledgers.Ballot>,
  +s: Node<Machine.Q(Kernel.machine(K))>
) -> Node<Machine.Q(Kernel.machine(K))>:
  match bs:
    case Nil{}:
      s
    case Con{+b, rest}:
      Sealed.each(~K, 
        f,
        rest,
        p,
        Sealed.follow(~K, 
          f,
          s,
          p,
          Ballot.store(b),
          Ballot.node(b),
          Pending.next(~K, s, p, Ballot.store(b), Ballot.node(b))
        )
      )

# s with each ballot of bs that its node's chain leads to and its key signs:
# the cost is about that of the ballots, in any order
def Sealed.take(~K: Kernel(), +bs: List<&2, Ledgers.Ballot>, s: Node<Machine.Q(Kernel.machine(K))>) -> Node<Machine.Q(Kernel.machine(K))>:
  Sealed.each(~K, List.length(&2, Ledgers.Ballot, bs), bs, Pending.of(bs), s)

# the height of the next step of the head h
def Head.next(h: Head) -> U32:
  match h:
    case Head{r, b, n, t}:
      n

# s with the head h of the line c
def State.head(~M: Machine(), s: Node<Machine.Q(M)>, c: Ledgers.Chain, h: Head) -> Node<Machine.Q(M)>:
  match s:
    case Node{l, hs, ws, ks}:
      Node{l, Tries.Trie.set(Head, hs, Ledgers.Chain.key(c), h), ws, ks}

# the requests of the line c that wait for a step, in the order that the node
# took them in
def Wait.of(~M: Machine(), s: Node<Machine.Q(M)>, c: Ledgers.Chain) -> List<&2, Ledgers.Id>:
  Maybe.default(
    &2,
    List<&2, Ledgers.Id>,
    Tries.Trie.get(List<&2, Ledgers.Id>, State.waiting(~M, s), Ledgers.Chain.key(c)),
    []
  )

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
def Wait.set(~M: Machine(), s: Node<Machine.Q(M)>, c: Ledgers.Chain, qs: List<&2, Ledgers.Id>) -> Node<Machine.Q(M)>:
  match s:
    case Node{l, hs, ws, ks}:
      Node{l, hs, Wait.put(ws, Ledgers.Chain.key(c), qs), ks}

# s with the request i waiting on the line c, after those that wait
def State.wait(~M: Machine(), +s: Node<Machine.Q(M)>, +c: Ledgers.Chain, i: Ledgers.Id) -> Node<Machine.Q(M)>:
  Wait.set(~M, s, c, List.append(&2, Ledgers.Id, Wait.of(~M, s, c), [i]))

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
  ~M: Machine(),
  +s: Node<Machine.Q(M)>,
  +c: Ledgers.Chain,
  h: Head,
  qs: List<&2, Ledgers.Id>
) -> Node<Machine.Q(M)>:
  State.head(~M, 
    Wait.set(~M, 
      s,
      c,
      Wait.left(
        Wait.of(~M, s, c),
        Tries.Trie.put_keys(~Ledgers.Id, ~Ledgers.Id.key, qs, Tries.Trie.new(Unit))
      )
    ),
    c,
    h
  )

# State.first once the head m of the line is known
def First.at(
  ~M: Machine(),
  s: Node<Machine.Q(M)>,
  c: Ledgers.Chain,
  h: Head,
  m: Maybe<&2, Head>
) -> Node<Machine.Q(M)>:
  match m:
    case Some{Head{r, b, n, Some{t}}}:
      s
    case x:
      State.head(~M, s, c, h)

# s with the first head h of the line c, when the line has no tip: a line
# that has a tip moves only by a step
def State.first(~M: Machine(), +s: Node<Machine.Q(M)>, +c: Ledgers.Chain, h: Head) -> Node<Machine.Q(M)>:
  First.at(~M, s, c, h, Node.head_of(~M, s, c))

# the state m with the first head h of the line c, else s
def Start.head(
  ~M: Machine(),
  s: Node<Machine.Q(M)>,
  m: Maybe<&2, Node<Machine.Q(M)>>,
  c: Ledgers.Chain,
  h: Head
) -> Node<Machine.Q(M)>:
  match m:
    case None{}:
      s
    case Some{s2}:
      State.first(~M, State.led(~M, s, State.ledger(~M, s2)), c, h)

# w with the first key of each first owner of os
def Seal.firsts(~K: Kernel(), os: List<&2, Owner>, m: Maybe<&2, Work<Machine.Q(Kernel.machine(K))>>) -> Maybe<&2, Work<Machine.Q(Kernel.machine(K))>>:
  match os:
    case Nil{}:
      m
    case Con{Owner{n, k}, r}:
      Seal.firsts(~K, 
        r,
        Maybe.bind(
          &2,
          Work<Machine.Q(Kernel.machine(K))>,
          Work<Machine.Q(Kernel.machine(K))>,
          m,
          w => Work.set(~Kernel.machine(K), w, Machine.seal(Kernel.machine(K))(n), Hashes.Hash.code(k, []))
        )
      )

# Node.start once the content m of the store is known: its first tip has no
# log and no version, and its owners are the first owners os
def Start.with(
  ~M: Machine(),
  s: Node<Machine.Q(M)>,
  +i: Ledgers.Id,
  os: List<&2, String>,
  m: Maybe<&2, Work<Machine.Q(M)>>
) -> Node<Machine.Q(M)>:
  match m:
    case None{}:
      s
    case Some{Work{s2, c}}:
      +t = {Tip{c, None{}, 0, os}: Tip}
      Start.head(~M, 
        s,
        State.put(~M, s2, [Tip.words(t)]),
        Ledgers.Chain{i, None{}},
        Head{i, None{}, 0, Some{Tip.hash(t)}}
      )

# s, which follows the store that the request i starts with the first owners
# os: its content holds their first keys
def Node.start(~K: Kernel(), +s: Node<Machine.Q(Kernel.machine(K))>, i: Ledgers.Id, +os: List<&2, Owner>) -> Node<Machine.Q(Kernel.machine(K))>:
  Start.with(~Kernel.machine(K), s, i, Owner.names(os), Seal.firsts(~K, os, Some{Work{s, None{}}}))

# the first tip of the branch b of a store whose tip is m, if the store made
# b: the log of the store holds it, written once, so every node opens the
# branch at the same tip (Chain.start_final)
def Branch.first(~M: Machine(), s: Node<Machine.Q(M)>, b: String, m: Maybe<&2, Tip>) -> Maybe<&2, Hashes.Hash>:
  match m:
    case None{}:
      None{}
    case Some{t}:
      Maybe.bind(
        &2,
        List<&2, U32>,
        Hashes.Hash,
        Node.get(~M, s, Tip.log(t), Log.start(b)),
        ws => Read.whole(Hashes.Hash, Hashes.Hash.code.read(ws))
      )

# Node.open once the head m of the line is known
def Open.at(~M: Machine(), +s: Node<Machine.Q(M)>, c: Ledgers.Chain, m: Maybe<&2, Head>) -> Node<Machine.Q(M)>:
  match m:
    case Some{Head{+r, Some{+b}, n, None{}}}:
      State.head(~M, 
        s,
        c,
        Head{r, Some{b}, 0, Branch.first(~M, s, b, Node.tip(~M, s, Ledgers.Chain{r, None{}}))}
      )
    case x:
      s

# s, which follows the line c: a branch that the node waits for opens at its
# first tip, once the store that the node follows made it
def Node.open(~M: Machine(), +s: Node<Machine.Q(M)>, +c: Ledgers.Chain) -> Node<Machine.Q(M)>:
  Open.at(~M, s, c, Node.head_of(~M, s, c))

# s, which follows the line l of the store r, when the head m says that it
# does not yet
def Follow.new(
  ~M: Machine(),
  s: Node<Machine.Q(M)>,
  +r: Ledgers.Id,
  +l: Maybe<&2, String>,
  m: Maybe<&2, Head>
) -> Node<Machine.Q(M)>:
  match m:
    case Some{h}:
      s
    case None{}:
      State.head(~M, s, Line.chain(r, l), Head{r, l, 0, None{}})

# s, which follows the line l of the store r
def Node.follow(~M: Machine(), +s: Node<Machine.Q(M)>, +r: Ledgers.Id, +l: Maybe<&2, String>) -> Node<Machine.Q(M)>:
  Follow.new(~M, s, r, l, Node.head_of(~M, s, Line.chain(r, l)))

# s, once it holds the new request i, which arrives as a: a store starts, or
# the request waits on its line
def Arrive.at(~K: Kernel(), s: Node<Machine.Q(Kernel.machine(K))>, i: Ledgers.Id, a: Arrival) -> Node<Machine.Q(Kernel.machine(K))>:
  match a:
    case Arrival.Starts{os}:
      Node.start(~K, s, i, os)
    case Arrival.Waits{+r, +l}:
      State.wait(~Kernel.machine(K), Node.follow(~Kernel.machine(K), s, r, l), Line.chain(r, l), i)

# s, once it holds the new request i of the change q
def Node.arrive(~K: Kernel(), s: Node<Machine.Q(Kernel.machine(K))>, i: Ledgers.Id, q: Machine.Q(Kernel.machine(K))) -> Node<Machine.Q(Kernel.machine(K))>:
  Arrive.at(~K, s, i, Machine.arrival(Kernel.machine(K))(q))

# a and b are the same root
def Root.same(a: Maybe<&2, Hashes.Hash>, b: Maybe<&2, Hashes.Hash>) -> Bool:
  Shared.Maybe.is_eq(~Hashes.Hash, ~Hashes.Hash.is_eq, a, b)

# the node n may cast a ballot at the place w of a line at the tip t, for the
# requests qs: there is a request, n is an owner, and n cast none there
def Cast.may(
  ~M: Machine(),
  +n: String,
  +s: Node<Machine.Q(M)>,
  w: Ledgers.Where,
  t: Tip,
  qs: List<&2, Ledgers.Id>
) -> Bool:
  List.all.if(
    u => List.all.if(
      v => Maybe.is_none(
        &2,
        Cells.Cell<Ledgers.Entry<Machine.Q(M)>>,
        Ledgers.State.get(~Machine.Q(M), State.ledger(~M, s), Ledgers.Slot.vote(w, n))
      ),
      List.contains(~String, ~String.eq, Tip.owners(t), n)
    ),
    Bool.not(List.is_empty(&2, Ledgers.Id, qs))
  )

# s with the node n's ballot for the act a at the place w, sealed as the next
# of the node's chain m (none: the store gave the node no key)
def Cast.seal(
  ~K: Kernel(),
  +s: Node<Machine.Q(Kernel.machine(K))>,
  +w: Ledgers.Where,
  n: String,
  a: Ledgers.Act,
  m: Maybe<&2, Keychain>
) -> Node<Machine.Q(Kernel.machine(K))>:
  match m:
    case None{}:
      s
    case Some{Keychain{+j, last, key, f}}:
      +seed = Keys.seed(State.keys(~Kernel.machine(K), s))
      +r = Where.store(w)
      Maybe.default(
        &2,
        Node<Machine.Q(Kernel.machine(K))>,
        Seal.accept(~K, 
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
  ~K: Kernel(),
  s: Node<Machine.Q(Kernel.machine(K))>,
  m: Maybe<&2, Node<Machine.Q(Kernel.machine(K))>>,
  +w: Ledgers.Where,
  +n: String,
  a: Ledgers.Act
) -> Node<Machine.Q(Kernel.machine(K))>:
  match m:
    case None{}:
      s
    case Some{s3}:
      +s4 = State.led(~Kernel.machine(K), s, State.ledger(~Kernel.machine(K), s3))
      Cast.seal(~K, s4, w, n, a, Seal.chain(~K, s4, Where.store(w), n))

# s with the node n's vote at the place w for the step that ran qs from the
# tip of the hash th, which the passes of the nodes from allow, when the run m
# is there: the run's nodes, its tip, and the ballot
def Cast.put(
  ~K: Kernel(),
  n: String,
  w: Ledgers.Where,
  th: Maybe<&2, Hashes.Hash>,
  qs: List<&2, Ledgers.Id>,
  from: List<&2, String>,
  m: Maybe<&2, Run<Machine.Q(Kernel.machine(K))>>,
  s: Node<Machine.Q(Kernel.machine(K))>
) -> Node<Machine.Q(Kernel.machine(K))>:
  match m:
    case None{}:
      s
    case Some{Run{s2, +t2}}:
      Cast.vote(~K, 
        s,
        State.put(~Kernel.machine(K), s2, [Tip.words(t2)]),
        w,
        n,
        Ledgers.Act.Vote{Ledgers.Vote{th, qs, Some{Tip.hash(t2)}}, from}
      )

# the node s may cast for the request i, which it holds as m: any request,
# but one of who decides only when it was asked at s
def Cast.mine.of(~K: Kernel(), s: Node<Machine.Q(Kernel.machine(K))>, i: Ledgers.Id, m: Maybe<&2, Ledgers.Asked<Machine.Q(Kernel.machine(K))>>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{Ledgers.Asked{t, q}}:
      List.any.if(u => Keys.asked(State.keys(~Kernel.machine(K), s), i), Bool.not(Machine.governs(Kernel.machine(K))(q)))

# the requests of qs that the node s may cast for
def Cast.mine(~K: Kernel(), +s: Node<Machine.Q(Kernel.machine(K))>, qs: List<&2, Ledgers.Id>) -> List<&2, Ledgers.Id>:
  match qs:
    case Nil{}:
      []
    case Con{+i, r}:
      List.filter.put(Ledgers.Id, i, Cast.mine(~K, s, r), Cast.mine.of(~K, s, i, Node.asked(~Kernel.machine(K), s, i)))

# the owner whose turn it is to propose the step at the height h, among the
# owners os: each in turn, by the height. One owner proposes a step and the
# others cast for the same step, so the owners do not split over what waits
# at each of them
def Owners.turn(+os: List<&2, String>, h: U32) -> Maybe<&2, String>:
  List.get(&2, String, os, U32.to_nat(U32.mod(h, U32.from_nat(List.length(&2, String, os)))))

# the step in the cell m of a ballot, if it holds one
def Cast.step(~M: Machine(), m: Maybe<&2, Cells.Cell<Ledgers.Entry<Machine.Q(M)>>>) -> Maybe<&2, Ledgers.Vote>:
  match m:
    case Some{Cells.One{Ledgers.Entry.Vote{b}}}:
      Ledgers.Ballot.vote(b)
    case x:
      None{}

# the step that the node p cast at the place w, if s holds its ballot
def Cast.of(~M: Machine(), s: Node<Machine.Q(M)>, w: Ledgers.Where, p: String) -> Maybe<&2, Ledgers.Vote>:
  Cast.step(~M, Ledgers.State.get(~Machine.Q(M), State.ledger(~M, s), Ledgers.Slot.vote(w, p)))

# what a node casts for: the requests of a step, its own run of them (none:
# it cannot run them now), and the nodes whose passes allow the step
type Plan<-Q: Data> is Data:
  Plan{asks: List<&2, Ledgers.Id>, run: Maybe<&2, Run<Q>>, from: List<&2, String>}

# the requests of the plan p
def Plan.asks(~M: Machine(), p: Plan<Machine.Q(M)>) -> List<&2, Ledgers.Id>:
  match p:
    case Plan{qs, m, from}:
      qs

# the run of the plan p
def Plan.run(~M: Machine(), p: Plan<Machine.Q(M)>) -> Maybe<&2, Run<Machine.Q(M)>>:
  match p:
    case Plan{qs, m, from}:
      m

# the nodes whose passes allow the step of the plan p
def Plan.from(~M: Machine(), p: Plan<Machine.Q(M)>) -> List<&2, String>:
  match p:
    case Plan{qs, m, from}:
      from

# the plan of an owner that proposes freely, on the line c at the tip t: the
# requests that wait at it, that it may cast for and that can run now
def Plan.own(~K: Kernel(), +s: Node<Machine.Q(Kernel.machine(K))>, +c: Ledgers.Chain, t: Tip, from: List<&2, String>) -> Plan<Machine.Q(Kernel.machine(K))>:
  +p = Step.some(~K, c, Cast.mine(~K, s, Wait.of(~Kernel.machine(K), s, c)), Run{s, t})
  Plan{Picked.asks(~Kernel.machine(K), p), Some{Picked.run(~Kernel.machine(K), p)}, from}

# the node s may cast for each request of qs
def Cast.all_mine(~K: Kernel(), +s: Node<Machine.Q(Kernel.machine(K))>, qs: List<&2, Ledgers.Id>) -> Bool:
  match qs:
    case Nil{}:
      True{}
    case Con{+i, r}:
      List.all.if(u => Cast.all_mine(~K, s, r), Cast.mine.of(~K, s, i, Node.asked(~Kernel.machine(K), s, i)))

# the run m, when it gives the tip of the hash after
def Plan.fit(~M: Machine(), after: Maybe<&2, Hashes.Hash>, m: Maybe<&2, Run<Machine.Q(M)>>) -> Maybe<&2, Run<Machine.Q(M)>>:
  match m:
    case None{}:
      None{}
    case Some{Run{s2, +t2}}:
      Shared.Maybe.when(
        Run<Machine.Q(M)>,
        Root.same(after, Some{Tip.hash(t2)}),
        u => Some{Run{s2, t2}}
      )

# the plan for a step m that another ballot names, on the line c at the tip t
# of the hash th: when the step starts from this tip, the node may cast for
# each of its requests, and the node's own run of them gives the same tip
def Plan.copy(
  ~K: Kernel(),
  +s: Node<Machine.Q(Kernel.machine(K))>,
  c: Ledgers.Chain,
  t: Tip,
  th: Maybe<&2, Hashes.Hash>,
  m: Maybe<&2, Ledgers.Vote>,
  from: List<&2, String>
) -> Plan<Machine.Q(Kernel.machine(K))>:
  match m:
    case None{}:
      Plan{[], None{}, []}
    case Some{Ledgers.Vote{before, +qs, after}}:
      Shared.Bool.when(
        Plan<Machine.Q(Kernel.machine(K))>,
        List.all.if(u => Cast.all_mine(~K, s, qs), Root.same(before, th)),
        u => Plan{qs, Plan.fit(~Kernel.machine(K), after, Step.run(~K, s, c, t, qs)), from},
        u => Plan{[], None{}, []}
      )

# the line of the request i, when s holds it
def Node.chain_of(~M: Machine(), s: Node<Machine.Q(M)>, +i: Ledgers.Id) -> Maybe<&2, Ledgers.Chain>:
  Maybe.bind(
    &2,
    Ledgers.Asked<Machine.Q(M)>,
    Ledgers.Chain,
    Node.asked(~M, s, i),
    a => Some{Arrival.chain(i, Machine.arrival(M)(Asked.ask(~M, a)))}
  )

# the round of the place w
def Where.round(w: Ledgers.Where) -> Nat:
  match w:
    case Ledgers.Where{c, h, r}:
      r

# what the node p did at the place w, in the cell m of its vote
def Cast.act.of(~M: Machine(), m: Maybe<&2, Cells.Cell<Ledgers.Entry<Machine.Q(M)>>>) -> Maybe<&2, Ledgers.Act>:
  match m:
    case Some{Cells.One{Ledgers.Entry.Vote{Ledgers.Ballot{Ledgers.Signed{w, n, a}, l}}}}:
      Some{a}
    case x:
      None{}

# the vote of the node p at the place w, with the nodes whose passes allow
# it, if s holds it
def Cast.act(~M: Machine(), s: Node<Machine.Q(M)>, w: Ledgers.Where, p: String) -> Maybe<&2, Ledgers.Act>:
  Cast.act.of(~M, Ledgers.State.get(~Machine.Q(M), State.ledger(~M, s), Ledgers.Slot.vote(w, p)))

# the nodes that the vote m names, if m is a vote
def Act.from(m: Maybe<&2, Ledgers.Act>) -> List<&2, String>:
  match m:
    case Some{Ledgers.Act.Vote{v, from}}:
      from
    case x:
      []

# the nodes whose passes allow the vote of the node p at the place w, as the
# vote names them
def Cast.from(~M: Machine(), s: Node<Machine.Q(M)>, w: Ledgers.Where, p: String) -> List<&2, String>:
  Act.from(Cast.act(~M, s, w, p))

# the highest round, up to k, to which the node n passed at the height h of
# the line c (0: it passed to none)
def Round.mine(~M: Machine(), +n: String, +s: Node<Machine.Q(M)>, +c: Ledgers.Chain, +h: U32, k: Nat) -> Nat:
  match k:
    case 0n:
      0n
    case 1n+(+p):
      Shared.Bool.when(
        Nat,
        Maybe.is_some(
          &2,
          Maybe<&2, Ledgers.Last>,
          Ledgers.State.passed(~Machine.Q(M), State.ledger(~M, s), Ledgers.Where{c, h, 1n+p}, n)
        ),
        u => 1n+p,
        u => Round.mine(~M, n, s, c, h, p)
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
  ~M: Machine(),
  +n: String,
  +s: Node<Machine.Q(M)>,
  +c: Ledgers.Chain,
  +h: U32,
  k: Nat
) -> Maybe<&2, Ledgers.Last>:
  match k:
    case 0n:
      Last.or(0n, Cast.of(~M, s, Ledgers.Where{c, h, 0n}, n), u => None{})
    case 1n+(+p):
      Last.or(1n+p, Cast.of(~M, s, Ledgers.Where{c, h, 1n+p}, n), u => Last.mine(~M, n, s, c, h, p))

# the last vote of the node n at the height h of the line c, in a round below
# r, if it cast one
def Last.below(
  ~M: Machine(),
  n: String,
  s: Node<Machine.Q(M)>,
  c: Ledgers.Chain,
  h: U32,
  r: Nat
) -> Maybe<&2, Ledgers.Last>:
  match r:
    case 0n:
      None{}
    case 1n+p:
      Last.mine(~M, n, s, c, h, p)

# the nodes of os whose pass to the place w the node s holds
def Passes.of(~M: Machine(), +s: Node<Machine.Q(M)>, +w: Ledgers.Where, os: List<&2, String>) -> List<&2, String>:
  match os:
    case Nil{}:
      []
    case Con{+o, r}:
      List.filter.put(
        String,
        o,
        Passes.of(~M, s, w, r),
        Maybe.is_some(
          &2,
          Maybe<&2, Ledgers.Last>,
          Ledgers.State.passed(~Machine.Q(M), State.ledger(~M, s), w, o)
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
  ~M: Machine(),
  +s: Node<Machine.Q(M)>,
  +w: Ledgers.Where,
  from: List<&2, String>
) -> Maybe<&2, Ledgers.Last>:
  match from:
    case Nil{}:
      None{}
    case Con{o, r}:
      Last.newer(
        Passed.last(Ledgers.State.passed(~Machine.Q(M), State.ledger(~M, s), w, o)),
        Passes.last(~M, s, w, r)
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
def Passed.all(~M: Machine(), +s: Node<Machine.Q(M)>, +w: Ledgers.Where, from: List<&2, String>) -> Bool:
  match from:
    case Nil{}:
      True{}
    case Con{o, r}:
      List.all.if(
        u => Passed.all(~M, s, w, r),
        Maybe.is_some(
          &2,
          Maybe<&2, Ledgers.Last>,
          Ledgers.State.passed(~Machine.Q(M), State.ledger(~M, s), w, o)
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
  ~M: Machine(),
  +s: Node<Machine.Q(M)>,
  +w: Ledgers.Where,
  +os: List<&2, String>,
  v: Ledgers.Vote,
  +from: List<&2, String>
) -> Bool:
  List.any.if(
    u => List.all.if(
      u2 => List.all.if(
        u3 => List.all.if(u4 => Last.is(Passes.last(~M, s, w, from), v), Owners.major(os, from)),
        Owners.sub(os, from)
      ),
      Passed.all(~M, s, w, from)
    ),
    Nat.is_eq(Where.round(w), 0n)
  )

# the plan of the proposer of a later round at the place w, once the nodes
# from that passed to it are known: none until they are a majority; then the
# last vote of the highest round among them, else what waits at the proposer
def Plan.later(
  ~K: Kernel(),
  s: Node<Machine.Q(Kernel.machine(K))>,
  c: Ledgers.Chain,
  w: Ledgers.Where,
  t: Tip,
  th: Maybe<&2, Hashes.Hash>,
  os: List<&2, String>,
  +from: List<&2, String>,
  m: Maybe<&2, Ledgers.Last>
) -> Plan<Machine.Q(Kernel.machine(K))>:
  match m:
    case None{}:
      Shared.Bool.when(
        Plan<Machine.Q(Kernel.machine(K))>,
        Owners.major(os, from),
        u => Plan.own(~K, s, c, t, from),
        u => Plan{[], None{}, []}
      )
    case Some{Ledgers.Last{r, v}}:
      Shared.Bool.when(
        Plan<Machine.Q(Kernel.machine(K))>,
        Owners.major(os, from),
        u => Plan.copy(~K, s, c, t, th, Some{v}, from),
        u => Plan{[], None{}, []}
      )

# the plan of the proposer at the place w
def Plan.lead(
  ~K: Kernel(),
  +s: Node<Machine.Q(Kernel.machine(K))>,
  +c: Ledgers.Chain,
  +w: Ledgers.Where,
  +t: Tip,
  th: Maybe<&2, Hashes.Hash>,
  +os: List<&2, String>
) -> Plan<Machine.Q(Kernel.machine(K))>:
  +from = Passes.of(~Kernel.machine(K), s, w, os)
  Shared.Bool.when(
    Plan<Machine.Q(Kernel.machine(K))>,
    Nat.is_eq(Where.round(w), 0n),
    u => Plan.own(~K, s, c, t, []),
    u => Plan.later(~K, s, c, w, t, th, os, from, Passes.last(~Kernel.machine(K), s, w, from))
  )

# the plan of another owner at the place w, once what the proposer did there
# is known (m): the proposer's step, when its passes allow it
def Plan.follow(
  ~K: Kernel(),
  +s: Node<Machine.Q(Kernel.machine(K))>,
  c: Ledgers.Chain,
  w: Ledgers.Where,
  t: Tip,
  th: Maybe<&2, Hashes.Hash>,
  os: List<&2, String>,
  m: Maybe<&2, Ledgers.Act>
) -> Plan<Machine.Q(Kernel.machine(K))>:
  match m:
    case Some{Ledgers.Act.Vote{+v, +from}}:
      Shared.Bool.when(
        Plan<Machine.Q(Kernel.machine(K))>,
        Vote.allowed(~Kernel.machine(K), s, w, os, v, from),
        u => Plan.copy(~K, s, c, t, th, Some{v}, from),
        u => Plan{[], None{}, []}
      )
    case x:
      Plan{[], None{}, []}

# what the node n casts for at the place w of the line c, at the tip t of the
# hash th, with the owners os, when it is turn's turn to propose
def Plan.of(
  ~K: Kernel(),
  n: String,
  +s: Node<Machine.Q(Kernel.machine(K))>,
  +c: Ledgers.Chain,
  +w: Ledgers.Where,
  +t: Tip,
  +th: Maybe<&2, Hashes.Hash>,
  +os: List<&2, String>,
  turn: Maybe<&2, String>
) -> Plan<Machine.Q(Kernel.machine(K))>:
  match turn:
    case None{}:
      Plan{[], None{}, []}
    case Some{+p}:
      Shared.Bool.when(
        Plan<Machine.Q(Kernel.machine(K))>,
        String.eq(p, n),
        u => Plan.lead(~K, s, c, w, t, th, os),
        u => Plan.follow(~K, s, c, w, t, th, os, Cast.act(~Kernel.machine(K), s, w, p))
      )

# s with the node n's pass to the place w, when n is one of the owners os and
# did not pass to w: it names its last vote at the height, in a round below
def Pass.to(~K: Kernel(), +n: String, +s: Node<Machine.Q(Kernel.machine(K))>, +w: Ledgers.Where, os: List<&2, String>) -> Node<Machine.Q(Kernel.machine(K))>:
  match w:
    case Ledgers.Where{+c, +h, +r}:
      Shared.Bool.when(
        Node<Machine.Q(Kernel.machine(K))>,
        List.all.if(
          u => Maybe.is_none(
            &2,
            Maybe<&2, Ledgers.Last>,
            Ledgers.State.passed(~Machine.Q(Kernel.machine(K)), State.ledger(~Kernel.machine(K), s), Ledgers.Where{c, h, r}, n)
          ),
          List.contains(~String, ~String.eq, os, n)
        ),
        u => Cast.seal(~K, 
          s,
          Ledgers.Where{c, h, r},
          n,
          Ledgers.Act.Pass{Last.below(~Kernel.machine(K), n, s, c, h, r)},
          Seal.chain(~K, s, Where.store(Ledgers.Where{c, h, r}), n)
        ),
        u => s
      )

# s, after the owner n joined the highest round of which it holds a ballot at
# the height h of the line c: a node casts in the round that the others reached
def Round.join(
  ~K: Kernel(),
  +n: String,
  +s: Node<Machine.Q(Kernel.machine(K))>,
  +c: Ledgers.Chain,
  +h: U32,
  os: List<&2, String>
) -> Node<Machine.Q(Kernel.machine(K))>:
  +top = Round.seen(~Kernel.machine(K), s, c, h)
  Shared.Bool.when(
    Node<Machine.Q(Kernel.machine(K))>,
    Nat.is_lt(Round.mine(~Kernel.machine(K), n, s, c, h, top), top),
    u => Pass.to(~K, n, s, Ledgers.Where{c, h, top}, os),
    u => s
  )

# Node.cast in the round of the node n at the height next of the line c, at
# the tip t of the hash th
def Cast.round(
  ~K: Kernel(),
  +n: String,
  +s: Node<Machine.Q(Kernel.machine(K))>,
  +c: Ledgers.Chain,
  +next: U32,
  +th: Maybe<&2, Hashes.Hash>,
  +t: Tip
) -> Node<Machine.Q(Kernel.machine(K))>:
  +os = Tip.owners(t)
  +r = Round.mine(~Kernel.machine(K), n, s, c, next, Round.seen(~Kernel.machine(K), s, c, next))
  +w = {Ledgers.Where{c, next, r}: Ledgers.Where}
  +p = Plan.of(~K, n, s, c, w, t, th, os, Owners.turn(os, U32.add(next, U32.from_nat(r))))
  Shared.Bool.when(
    Node<Machine.Q(Kernel.machine(K))>,
    Cast.may(~Kernel.machine(K), n, s, w, t, Plan.asks(~Kernel.machine(K), p)),
    u => Cast.put(~K, 
      n,
      w,
      th,
      Plan.asks(~Kernel.machine(K), p),
      Plan.from(~Kernel.machine(K), p),
      Plan.run(~Kernel.machine(K), p),
      s
    ),
    u => s
  )

# Node.cast at the head h of the line c, whose tip is m
def Cast.at(
  ~K: Kernel(),
  +n: String,
  +s: Node<Machine.Q(Kernel.machine(K))>,
  +c: Ledgers.Chain,
  h: Head,
  m: Maybe<&2, Tip>
) -> Node<Machine.Q(Kernel.machine(K))>:
  match h m:
    case Head{r, b, +next, th} Some{+t}:
      Cast.round(~K, n, Round.join(~K, n, s, c, next, Tip.owners(t)), c, next, th, t)
    case x y:
      s

# Node.pass at the head h of the line c, whose tip is m
def Pass.at(
  ~K: Kernel(),
  +n: String,
  +s: Node<Machine.Q(Kernel.machine(K))>,
  +c: Ledgers.Chain,
  h: Head,
  m: Maybe<&2, Tip>
) -> Node<Machine.Q(Kernel.machine(K))>:
  match h m:
    case Head{r, b, +next, th} Some{t}:
      k = Round.seen(~Kernel.machine(K), s, c, next)
      Pass.to(~K, 
        n,
        s,
        Ledgers.Where{c, next, 1n+Round.mine(~Kernel.machine(K), n, s, c, next, k)},
        Tip.owners(t)
      )
    case x y:
      s

# Node.pass once the head m of the line c is known
def Pass.head(
  ~K: Kernel(),
  n: String,
  +s: Node<Machine.Q(Kernel.machine(K))>,
  c: Ledgers.Chain,
  m: Maybe<&2, Head>
) -> Node<Machine.Q(Kernel.machine(K))>:
  match m:
    case None{}:
      s
    case Some{+h}:
      Pass.at(~K, n, s, c, h, Head.tip(~Kernel.machine(K), s, h))

# Node.cast once the head m of the line c is known
def Cast.head(
  ~K: Kernel(),
  n: String,
  +s: Node<Machine.Q(Kernel.machine(K))>,
  c: Ledgers.Chain,
  m: Maybe<&2, Head>
) -> Node<Machine.Q(Kernel.machine(K))>:
  match m:
    case None{}:
      s
    case Some{+h}:
      Cast.at(~K, n, s, c, h, Head.tip(~Kernel.machine(K), s, h))

# s, after the node n cast its ballot for the next step of the line c, in its
# round (Rounds): when it is its turn, the step that the rules of the round
# give it; else the step that the owner whose turn it is cast, when the rules
# allow it and the node's own run of it gives the same tip
def Node.cast(~K: Kernel(), n: String, +s: Node<Machine.Q(Kernel.machine(K))>, +c: Ledgers.Chain) -> Node<Machine.Q(Kernel.machine(K))>:
  Cast.head(~K, n, s, c, Node.head_of(~Kernel.machine(K), s, c))

# the state m at the head h of the line c, after a step that ran qs, else s
def Advance.moved(
  ~M: Machine(),
  s: Node<Machine.Q(M)>,
  m: Maybe<&2, Node<Machine.Q(M)>>,
  c: Ledgers.Chain,
  h: Head,
  qs: List<&2, Ledgers.Id>
) -> Node<Machine.Q(M)>:
  match m:
    case None{}:
      s
    case Some{s3}:
      State.moved(~M, State.led(~M, s, State.ledger(~M, s3)), c, h, qs)

# s at the head of the next height of the line c, when the run m of the
# decided requests qs gives the tip that the ballots name (after): a node
# checks a step before it keeps it
def Advance.ran(
  ~M: Machine(),
  +s: Node<Machine.Q(M)>,
  c: Ledgers.Chain,
  r: Ledgers.Id,
  b: Maybe<&2, String>,
  next: U32,
  after: Maybe<&2, Hashes.Hash>,
  qs: List<&2, Ledgers.Id>,
  m: Maybe<&2, Run<Machine.Q(M)>>
) -> Node<Machine.Q(M)>:
  match m:
    case None{}:
      s
    case Some{Run{s2, +t2}}:
      Shared.Bool.when(
        Node<Machine.Q(M)>,
        Root.same(after, Some{Tip.hash(t2)}),
        u => Advance.moved(~M, 
          s,
          State.put(~M, s2, [Tip.words(t2)]),
          c,
          Head{r, b, U32.inc(next), Some{Tip.hash(t2)}},
          qs
        ),
        u => s
      )

# Node.advance once the step m that the owners decided at the head is known
def Advance.step(
  ~K: Kernel(),
  +s: Node<Machine.Q(Kernel.machine(K))>,
  +c: Ledgers.Chain,
  h: Head,
  t: Tip,
  m: Maybe<&2, Ledgers.Vote>
) -> Node<Machine.Q(Kernel.machine(K))>:
  match h m:
    case Head{r, b, next, th} Some{Ledgers.Vote{before, +qs, after}}:
      Shared.Bool.when(
        Node<Machine.Q(Kernel.machine(K))>,
        Root.same(before, th),
        u => Advance.ran(~Kernel.machine(K), s, c, r, b, next, after, qs, Step.run(~K, s, c, t, qs)),
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
  ~M: Machine(),
  +s: Node<Machine.Q(M)>,
  +c: Ledgers.Chain,
  +h: U32,
  +os: List<&2, String>,
  k: Nat
) -> Maybe<&2, Ledgers.Vote>:
  match k:
    case 0n:
      Ledgers.State.decide(~Machine.Q(M), State.ledger(~M, s), Ledgers.Where{c, h, 0n}, os)
    case 1n+(+p):
      Vote.first(
        Ledgers.State.decide(~Machine.Q(M), State.ledger(~M, s), Ledgers.Where{c, h, 1n+p}, os),
        u => Height.decide(~M, s, c, h, os, p)
      )

# that the rounds of the height h of the line c decide one step in s, for the
# owners os: a law of rounds, and a premise of the laws of agreement
def Height.One(~M: Machine(), s: Node<Machine.Q(M)>, c: Ledgers.Chain, h: U32, os: List<&2, String>) -> Type:
  @r1: Nat -> @r2: Nat -> @v1: Ledgers.Vote -> @v2: Ledgers.Vote -> {
    Ledgers.State.decide(
      ~Machine.Q(M),
      State.ledger(~M, s),
      Ledgers.Where{c, h, r1},
      os
    )
      == Some{v1}: Maybe<&2, Ledgers.Vote>
  } -> {
    Ledgers.State.decide(
      ~Machine.Q(M),
      State.ledger(~M, s),
      Ledgers.Where{c, h, r2},
      os
    )
      == Some{v2}: Maybe<&2, Ledgers.Vote>
  } -> {v1 == v2: Ledgers.Vote}

# that the passes that a vote names allow it (Vote.allowed), for the owners os
def Rounds.Allow(~M: Machine(), s: Node<Machine.Q(M)>, c: Ledgers.Chain, h: U32, os: List<&2, String>) -> Type:
  @r: Nat -> @q: String -> @v: Ledgers.Vote -> {
    Cast.of(~M, s, Ledgers.Where{c, h, r}, q) == Some{v}: Maybe<&2, Ledgers.Vote>
  } -> {
    Vote.allowed(~M, 
      s,
      Ledgers.Where{c, h, r},
      os,
      v,
      Cast.from(~M, s, Ledgers.Where{c, h, r}, q)
    )
      == True{}: Bool
  }

# that a pass names the last vote of its node below its round: a node that
# passed to a round casts no vote below it
def Rounds.Last(~M: Machine(), s: Node<Machine.Q(M)>, c: Ledgers.Chain, h: U32) -> Type:
  @r: Nat -> @q: String -> @l: Maybe<
    &2,
    Ledgers.Last> -> {
    Ledgers.State.passed(
      ~Machine.Q(M),
      State.ledger(~M, s),
      Ledgers.Where{c, h, r},
      q
    )
      == Some{l}: Maybe<&2, Maybe<&2, Ledgers.Last>>
  } -> {l == Last.below(~M, q, s, c, h, r): Maybe<&2, Ledgers.Last>}

# that the votes of one round are for one step: one owner proposes, and the
# others copy
def Rounds.Same(~M: Machine(), s: Node<Machine.Q(M)>, c: Ledgers.Chain, h: U32) -> Type:
  @r: Nat -> @q1: String -> @q2: String -> @a: Ledgers.Vote -> @b: Ledgers.Vote -> {
    Cast.of(~M, s, Ledgers.Where{c, h, r}, q1) == Some{a}: Maybe<&2, Ledgers.Vote>
  } -> {
    Cast.of(~M, s, Ledgers.Where{c, h, r}, q2) == Some{b}: Maybe<&2, Ledgers.Vote>
  } -> {a == b: Ledgers.Vote}

# that the ballots that s holds on the line c follow the rules of rounds, at
# the next height of each head whose tip s holds, for the owners in that tip
def Rounds.Rules(~M: Machine(), s: Node<Machine.Q(M)>, c: Ledgers.Chain) -> Type:
  @x: Head -> @t: Tip -> {
    Head.tip(~M, s, x) == Some{t}: Maybe<&2, Tip>
  } -> Rounds.Allow(~M, 
    s,
    c,
    Head.next(x),
    Tip.owners(t)
  )
    & (Rounds.Last(~M, s, c, Head.next(x)) & Rounds.Same(~M, s, c, Head.next(x)))

# Node.advance at the head h of the line c, whose tip is m
def Advance.at(
  ~K: Kernel(),
  +s: Node<Machine.Q(Kernel.machine(K))>,
  +c: Ledgers.Chain,
  +h: Head,
  m: Maybe<&2, Tip>
) -> Node<Machine.Q(Kernel.machine(K))>:
  match m:
    case None{}:
      s
    case Some{+t}:
      Advance.step(~K, 
        s,
        c,
        h,
        t,
        Height.decide(~Kernel.machine(K), 
          s,
          c,
          Head.next(h),
          Tip.owners(t),
          Round.seen(~Kernel.machine(K), s, c, Head.next(h))
        )
      )

# Node.advance once the head m of the line c is known
def Advance.head(~K: Kernel(), +s: Node<Machine.Q(Kernel.machine(K))>, c: Ledgers.Chain, m: Maybe<&2, Head>) -> Node<Machine.Q(Kernel.machine(K))>:
  match m:
    case None{}:
      s
    case Some{+h}:
      Advance.at(~K, s, c, h, Head.tip(~Kernel.machine(K), s, h))

# s, with its head of the line c moved over the next step, when a majority of
# the owners in its tip cast it and the node's own run of it gives the same
# tip
def Node.advance(~K: Kernel(), +s: Node<Machine.Q(Kernel.machine(K))>, +c: Ledgers.Chain) -> Node<Machine.Q(Kernel.machine(K))>:
  Advance.head(~K, s, c, Node.head_of(~Kernel.machine(K), s, c))

# the heads a and b are at the same height, or one is none
def Heads.level(a: Maybe<&2, Head>, b: Maybe<&2, Head>) -> Bool:
  match a b:
    case Some{x} Some{y}:
      U32.is_eq(Head.next(x), Head.next(y))
    case x y:
      True{}

# Node.advances once the head m of the line c is known
def Advances.at(
  ~K: Kernel(),
  f: Nat,
  +s: Node<Machine.Q(Kernel.machine(K))>,
  +c: Ledgers.Chain,
  m: Maybe<&2, Head>
) -> Node<Machine.Q(Kernel.machine(K))>:
  match f m:
    case 1n+p Some{+h}:
      +s1 = Advance.at(~K, s, c, h, Head.tip(~Kernel.machine(K), s, h))
      +m1 = Node.head_of(~Kernel.machine(K), s1, c)
      Shared.Bool.when(
        Node<Machine.Q(Kernel.machine(K))>,
        Heads.level(Some{h}, m1),
        u => s1,
        u => Advances.at(~K, p, s1, c, m1)
      )
    case g x:
      s

# s, with its head of the line c moved over each step that is decided, f
# steps at most
def Node.advances(~K: Kernel(), f: Nat, +s: Node<Machine.Q(Kernel.machine(K))>, +c: Ledgers.Chain) -> Node<Machine.Q(Kernel.machine(K))>:
  Advances.at(~K, f, s, c, Node.head_of(~Kernel.machine(K), s, c))

# s, after the node n moved its head of the line c over each step that is
# decided, cast its ballot for the next step, and moved its head again
def Step.head(~K: Kernel(), n: String, s: Node<Machine.Q(Kernel.machine(K))>, +c: Ledgers.Chain) -> Node<Machine.Q(Kernel.machine(K))>:
  s1 = Node.advances(~K, 4294967295n, s, c)
  Node.advances(~K, 4294967295n, Node.cast(~K, n, s1, c), c)

# s, after the node n did what it can on the line c
def Node.step(~K: Kernel(), n: String, s: Node<Machine.Q(Kernel.machine(K))>, +c: Ledgers.Chain) -> Node<Machine.Q(Kernel.machine(K))>:
  Step.head(~K, n, Node.open(~Kernel.machine(K), s, c), c)

# s, after the owner n passed to the next round of the next step of the line
# c, and did what it can there: the round took too long (the proposer may be
# away). Transport asks for this; the core has no clock
def Node.pass(~K: Kernel(), +n: String, +s: Node<Machine.Q(Kernel.machine(K))>, +c: Ledgers.Chain) -> Node<Machine.Q(Kernel.machine(K))>:
  Node.step(~K, n, Pass.head(~K, n, s, c, Node.head_of(~Kernel.machine(K), s, c)), c)

# s, after the node n took in the new request q of e
def Node.ask.new(~K: Kernel(), n: String, +s: Node<Machine.Q(Kernel.machine(K))>, +e: Envelope, +q: Machine.Q(Kernel.machine(K))) -> Node<Machine.Q(Kernel.machine(K))>:
  +i = Envelope.of(e)
  c = Arrival.chain(i, Machine.arrival(Kernel.machine(K))(q))
  s1 = Node.arrive(~K, 
    State.led(~Kernel.machine(K), 
      s,
      Ledgers.State.ask(
        ~Machine.Q(Kernel.machine(K)),
        ~Machine.same(Kernel.machine(K)),
        State.ledger(~Kernel.machine(K), s),
        i,
        Envelope.time(e),
        q
      )
    ),
    i,
    q
  )
  Node.step(~K, n, s1, c)

# Node.ask once the cell m of the request's ID is known
def Node.ask.at(
  ~K: Kernel(),
  n: String,
  +s: Node<Machine.Q(Kernel.machine(K))>,
  +e: Envelope,
  q: Machine.Q(Kernel.machine(K)),
  m: Maybe<&2, Cells.Cell<Ledgers.Entry<Machine.Q(Kernel.machine(K))>>>
) -> Node<Machine.Q(Kernel.machine(K))>:
  match m:
    case Some{x}:
      s
    case None{}:
      Node.ask.new(~K, 
        n,
        State.keyed(~Kernel.machine(K), s, Keys.mark(State.keys(~Kernel.machine(K), s), Envelope.of(e))),
        e,
        q
      )

# s, after the node n took in the request q of e, cast its ballot when it owns
# its line, and moved its head when that decides the step. A request ID that s
# holds counts once: asked again, it changes nothing
def Node.ask(~K: Kernel(), n: String, +s: Node<Machine.Q(Kernel.machine(K))>, +e: Envelope, q: Machine.Q(Kernel.machine(K))) -> Node<Machine.Q(Kernel.machine(K))>:
  Node.ask.at(~K, 
    n,
    s,
    e,
    q,
    Ledgers.State.get(~Machine.Q(Kernel.machine(K)), State.ledger(~Kernel.machine(K), s), Ledgers.Slot.ask(Envelope.of(e)))
  )

# s, once it holds each request among the cells cs whose slot was empty in the
# ledger old: a request that the node held does not arrive again
def Take.asks(
  ~K: Kernel(),
  cs: List<&2, Cells.Cell<Ledgers.Entry<Machine.Q(Kernel.machine(K))>>>,
  +old: Ledgers.State(Machine.Q(Kernel.machine(K))),
  +s: Node<Machine.Q(Kernel.machine(K))>
) -> Node<Machine.Q(Kernel.machine(K))>:
  match cs:
    case Nil{}:
      s
    case Con{Cells.One{Ledgers.Entry.Ask{+i, t, q}}, rest}:
      Take.asks(~K, 
        rest,
        old,
        Shared.Bool.when(
          Node<Machine.Q(Kernel.machine(K))>,
          Maybe.is_none(
            &2,
            Cells.Cell<Ledgers.Entry<Machine.Q(Kernel.machine(K))>>,
            Ledgers.State.get(~Machine.Q(Kernel.machine(K)), old, Ledgers.Slot.ask(i))
          ),
          u => Node.arrive(~K, s, i, q),
          u => s
        )
      )
    case Con{c, rest}:
      Take.asks(~K, rest, old, s)

# l with the requests and the data among the cells cs, each in the slot that
# its own content names (a request by its ID, data by its hash). A ballot, a
# cell that is not one entry, and the slot that the sender gave are not kept:
# what another node sent is read, not believed
def Take.clean(
  ~M: Machine(),
  cs: List<&2, Cells.Cell<Ledgers.Entry<Machine.Q(M)>>>,
  l: Ledgers.State(Machine.Q(M))
) -> Ledgers.State(Machine.Q(M)):
  match cs:
    case Nil{}:
      l
    case Con{Cells.One{Ledgers.Entry.Ask{i, t, q}}, rest}:
      Take.clean(~M, rest, Ledgers.State.ask(~Machine.Q(M), ~Machine.same(M), l, i, t, q))
    case Con{Cells.One{Ledgers.Entry.Data{ws}}, rest}:
      Take.clean(~M, rest, Ledgers.State.put_data(~Machine.Q(M), ~Machine.same(M), l, ws))
    case Con{c, rest}:
      Take.clean(~M, rest, l)

# Node.consent once the line m of the request is known
def Consent.at(
  ~K: Kernel(),
  n: String,
  +s: Node<Machine.Q(Kernel.machine(K))>,
  i: Ledgers.Id,
  m: Maybe<&2, Ledgers.Chain>
) -> Node<Machine.Q(Kernel.machine(K))>:
  match m:
    case None{}:
      s
    case Some{c}:
      Node.step(~K, n, State.keyed(~Kernel.machine(K), s, Keys.mark(State.keys(~Kernel.machine(K), s), i)), c)

# s, after a writer connected to the node n asked for the request i, which s
# holds already (it came from another node): the request counts once, and the
# node now casts for it as one that was asked at it
def Node.consent(~K: Kernel(), n: String, +s: Node<Machine.Q(Kernel.machine(K))>, +i: Ledgers.Id) -> Node<Machine.Q(Kernel.machine(K))>:
  Consent.at(~K, n, s, i, Node.chain_of(~Kernel.machine(K), s, i))

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
  ~M: Machine(),
  s: Node<Machine.Q(M)>,
  h: Maybe<&2, Hashes.Hash>,
  k: List<&2, U32>
) -> Maybe<&2, Hashes.Hash>:
  Look.lack(Node.look(~M, s, h, k))

# l with the data m, if any
def Serve.put(
  ~M: Machine(),
  m: Maybe<&2, List<&2, U32>>,
  l: Ledgers.State(Machine.Q(M))
) -> Ledgers.State(Machine.Q(M)):
  match m:
    case None{}:
      l
    case Some{ws}:
      Ledgers.State.put_data(~Machine.Q(M), ~Machine.same(M), l, ws)

# the data that s holds under the hashes hs, as a ledger: what a node sends
# to a node that asks for them (Node.fetch)
def Node.serve(~M: Machine(), +s: Node<Machine.Q(M)>, hs: List<&2, Hashes.Hash>) -> Ledgers.State(Machine.Q(M)):
  match hs:
    case Nil{}:
      Ledgers.State.empty(~Machine.Q(M))
    case Con{h, r}:
      Serve.put(~M, Ledgers.State.data(~Machine.Q(M), State.ledger(~M, s), h), Node.serve(~M, s, r))

# what the ledger r lacks of s: what a sync from s to a holder of r sends
def Node.missing(~M: Machine(), s: Node<Machine.Q(M)>, r: Ledgers.State(Machine.Q(M))) -> Ledgers.State(Machine.Q(M)):
  Ledgers.State.missing(~Machine.Q(M), ~Machine.same(M), State.ledger(~M, s), r)

# what a node reads of the ledger t that another node sent: each request and
# each data, in the slot that its own content names (Take.clean)
def Node.reads(~M: Machine(), t: Ledgers.State(Machine.Q(M))) -> Ledgers.State(Machine.Q(M)):
  Take.clean(~M, 
    Tries.Trie.values(Cells.Cell<Ledgers.Entry<Machine.Q(M)>>, t),
    Ledgers.State.empty(~Machine.Q(M))
  )

# the ballots among the cells cs
def Ballots.of(~M: Machine(), cs: List<&2, Cells.Cell<Ledgers.Entry<Machine.Q(M)>>>) -> List<&2, Ledgers.Ballot>:
  match cs:
    case Nil{}:
      []
    case Con{Cells.One{Ledgers.Entry.Vote{b}}, rest}:
      b <> Ballots.of(~M, rest)
    case Con{c, rest}:
      Ballots.of(~M, rest)

# what a holder of s keeps of t, which another node sent. It checks everything
# before it keeps it: a request and data go to the slot that their own content
# names (Take.clean; data is read only under its hash), in the slots where s
# holds nothing; a ballot is kept when its node's chain leads to it and its
# key signs it (a ballot that it cannot check yet comes again with the next
# sync). Nothing that s holds is lost or changed. Each new request waits on
# its line: the cost is what t brings, not what s holds
def Node.take(~K: Kernel(), +s: Node<Machine.Q(Kernel.machine(K))>, +t: Ledgers.State(Machine.Q(Kernel.machine(K)))) -> Node<Machine.Q(Kernel.machine(K))>:
  +sent = Node.reads(~Kernel.machine(K), t)
  Sealed.take(~K, 
    Ballots.of(~Kernel.machine(K), 
      Tries.Trie.values(
        Cells.Cell<Ledgers.Entry<Machine.Q(Kernel.machine(K))>>,
        Ledgers.State.missing(~Machine.Q(Kernel.machine(K)), ~Machine.same(Kernel.machine(K)), t, State.ledger(~Kernel.machine(K), s))
      )
    ),
    Take.asks(~K, 
      Tries.Trie.values(Cells.Cell<Ledgers.Entry<Machine.Q(Kernel.machine(K))>>, sent),
      State.ledger(~Kernel.machine(K), s),
      State.led(~Kernel.machine(K), s, Ledgers.State.take(~Machine.Q(Kernel.machine(K)), State.ledger(~Kernel.machine(K), s), sent))
    )
  )

# s, after the node n did what it can on each line of cs
def Node.steps(~K: Kernel(), +n: String, cs: List<&2, Ledgers.Chain>, s: Node<Machine.Q(Kernel.machine(K))>) -> Node<Machine.Q(Kernel.machine(K))>:
  match cs:
    case Nil{}:
      s
    case Con{c, rest}:
      Node.steps(~K, n, rest, Node.step(~K, n, s, c))

# the line of the first of the waiting requests qs, then rest
def Lines.waiting(
  ~M: Machine(),
  s: Node<Machine.Q(M)>,
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
          Node.chain_of(~M, s, i),
          c => Some{c <> rest}
        ),
        rest
      )

# the lines of the lists of waiting requests qss
def Lines.waits(~M: Machine(), +s: Node<Machine.Q(M)>, qss: List<&2, List<&2, Ledgers.Id>>) -> List<&2, Ledgers.Chain>:
  match qss:
    case Nil{}:
      []
    case Con{qs, r}:
      Lines.waiting(~M, s, qs, Lines.waits(~M, s, r))

# the lines of the requests and the ballots among the cells cs, then rest
def Lines.new(
  ~M: Machine(),
  cs: List<&2, Cells.Cell<Ledgers.Entry<Machine.Q(M)>>>,
  rest: List<&2, Ledgers.Chain>
) -> List<&2, Ledgers.Chain>:
  match cs:
    case Nil{}:
      rest
    case Con{Cells.One{Ledgers.Entry.Ask{i, t, q}}, r}:
      Arrival.chain(i, Machine.arrival(M)(q)) <> Lines.new(~M, r, rest)
    case Con{Cells.One{Ledgers.Entry.Vote{b}}, r}:
      Where.line(Ballot.at(b)) <> Lines.new(~M, r, rest)
    case Con{c, r}:
      Lines.new(~M, r, rest)

# the lines that a sync of t into s may move, each once: those of the new
# requests and ballots of t, and those with waiting requests (new data can let
# them run). So a sync costs about what it brings, not every line of the node
def Sync.lines(
  ~M: Machine(),
  s: Node<Machine.Q(M)>,
  +s1: Node<Machine.Q(M)>,
  t: Ledgers.State(Machine.Q(M))
) -> List<&2, Ledgers.Chain>:
  Tries.Trie.unique(
    ~Ledgers.Chain,
    ~Ledgers.Chain.key,
    Lines.new(~M, 
      Tries.Trie.values(
        Cells.Cell<Ledgers.Entry<Machine.Q(M)>>,
        Ledgers.State.missing(~Machine.Q(M), ~Machine.same(M), t, State.ledger(~M, s))
      ),
      Lines.waits(~M, s1, Tries.Trie.values(List<&2, Ledgers.Id>, State.waiting(~M, s1)))
    ),
    Tries.Trie.new(Unit)
  )

# the node b holds every entry that the node a holds: its ledger only grew
def Node.grows(~M: Machine(), a: Node<Machine.Q(M)>, b: Node<Machine.Q(M)>) -> Bool:
  Ledgers.State.grows(
    ~Machine.Q(M),
    ~Machine.same(M),
    State.ledger(~M, a),
    State.ledger(~M, b)
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
  ~M: Machine(),
  +s: Node<Machine.Q(M)>,
  c: Ledgers.Chain,
  +x: Head,
  r: Nat
) -> Maybe<&2, Ledgers.Vote>:
  Maybe.bind(
    &2,
    Tip,
    Ledgers.Vote,
    Head.tip(~M, s, x),
    t => Ledgers.State.decide(
      ~Machine.Q(M),
      State.ledger(~M, s),
      Ledgers.Where{c, Head.next(x), r},
      Tip.owners(t)
    )
  )

# the head of the line c after one decided step for each round of rs, the
# last first, from the head h, by the ledger of s alone (none: a step is not
# decided in its round). A law's measure: no node runs it
def Line.at(
  ~M: Machine(),
  rs: List<&2, Nat>,
  +s: Node<Machine.Q(M)>,
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
        Line.at(~M, rest, s, c, h),
        +x => Head.moved(x, Advance.in(~M, s, c, x, r))
      )

# that b holds, in the log of each line, each key that a holds there
def Node.Keeps(~M: Machine(), a: Node<Machine.Q(M)>, b: Node<Machine.Q(M)>) -> Type:
  @c: Ledgers.Chain -> @k: List<
    &2,
    U32> -> @v: List<
    &2,
    U32> -> {
    Line.get(~M, a, c, k) == Some{v}: Maybe<&2, List<&2, U32>>
  } -> {Line.get(~M, b, c, k) == Some{v}: Maybe<&2, List<&2, U32>>}

# the head m has a tip
def Head.held(m: Maybe<&2, Head>) -> Bool:
  match m:
    case Some{Head{r, b, n, Some{t}}}:
      True{}
    case x:
      False{}

# that the head of the line c in s is some decided steps from the head h0, by
# the ledger of s
def Line.Reach(~M: Machine(), s: Node<Machine.Q(M)>, c: Ledgers.Chain, h0: Head) -> Type:
  Exists(
    List<&2, Nat>,
    rs => Exists(
      Head,
      h => {
        Node.head_of(~M, s, c) == Some{h}: Maybe<&2, Head>
      }
        & {Line.at(~M, rs, s, c, h0) == Some{h}: Maybe<&2, Head>}
    )
  )

# that each head of a that is some decided steps from a head with a tip is,
# in b, some decided steps from it
def Node.On(~M: Machine(), a: Node<Machine.Q(M)>, b: Node<Machine.Q(M)>) -> Type:
  @c: Ledgers.Chain -> @h0: Head -> {
    Head.held(Some{h0}) == True{}: Bool
  } -> Line.Reach(~M, a, c, h0) -> Line.Reach(~M, b, c, h0)

# the work m, if any, reads the key k as v
def Work.Reads(~M: Machine(), k: List<&2, U32>, v: List<&2, U32>, m: Maybe<&2, Work<Machine.Q(M)>>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{Work{s2, h2}}:
      {Node.get(~M, s2, h2, k) == Some{v}: Maybe<&2, List<&2, U32>>}

# the log of the run m, if any, holds an outcome of the request i
def Run.Outs(~M: Machine(), m: Maybe<&2, Run<Machine.Q(M)>>, i: Ledgers.Id) -> Type:
  match m:
    case None{}:
      Unit
    case Some{Run{s, t}}:
      {
        Maybe.is_some(
          &2,
          List<&2, U32>,
          Node.get(~M, s, Tip.log(t), Log.out(i))
        )
          == True{}: Bool
      }

# the ledger of a node with a new ledger is that ledger
def Led.led(
  ~M: Machine(),
  s: Node<Machine.Q(M)>,
  l: Ledgers.State(Machine.Q(M))
) -> {State.ledger(~M, State.led(~M, s, l)) == l: Ledgers.State(Machine.Q(M))}:
  match s:
    case Node{old, hs, ws, ks}:
      {==}

# a new head keeps the ledger
def Led.head(
  ~M: Machine(),
  s: Node<Machine.Q(M)>,
  c: Ledgers.Chain,
  h: Head
) -> {
  State.ledger(~M, 
    State.head(~M, s, c, h)
  )
    == State.ledger(~M, s): Ledgers.State(Machine.Q(M))
}:
  match s:
    case Node{l, hs, ws, ks}:
      {==}

# new waiting requests keep the ledger
def Led.wait(
  ~M: Machine(),
  s: Node<Machine.Q(M)>,
  c: Ledgers.Chain,
  qs: List<&2, Ledgers.Id>
) -> {
  State.ledger(~M, 
    Wait.set(~M, s, c, qs)
  )
    == State.ledger(~M, s): Ledgers.State(Machine.Q(M))
}:
  match s:
    case Node{l, hs, ws, ks}:
      {==}

# a node grows to itself
def Grows.refl(~M: Machine(), s: Node<Machine.Q(M)>) -> {Node.grows(~M, s, s) == True{}: Bool}:
  Ledgers.State.grows_refl(~Machine.Q(M), ~Machine.same(M), ~Machine.laws(M), State.ledger(~M, s))

# growth composes
def Grows.trans(
  ~M: Machine(),
  a: Node<Machine.Q(M)>,
  b: Node<Machine.Q(M)>,
  c: Node<Machine.Q(M)>
) -> {
  Node.grows(~M, a, b) == True{}: Bool
} -> {Node.grows(~M, b, c) == True{}: Bool} -> {Node.grows(~M, a, c) == True{}: Bool}:
  Ledgers.State.grows_trans(
    ~Machine.Q(M),
    ~Machine.same(M),
    ~Machine.laws(M),
    State.ledger(~M, a),
    State.ledger(~M, b),
    State.ledger(~M, c)
  )

# a node with a new ledger grows when the ledger does
def Grows.led(
  ~M: Machine(),
  s: Node<Machine.Q(M)>,
  l: Ledgers.State(Machine.Q(M)),
  e: {
    Ledgers.State.grows(~Machine.Q(M), ~Machine.same(M), State.ledger(~M, s), l) == True{}: Bool
  }
) -> {Node.grows(~M, s, State.led(~M, s, l)) == True{}: Bool}:
  %Equal.sym(
    Ledgers.State(Machine.Q(M)),
    State.ledger(~M, State.led(~M, s, l)),
    l,
    Led.led(~M, s, l)
  ): {
    Ledgers.State.grows(~Machine.Q(M), ~Machine.same(M), State.ledger(~M, s), _) == True{}: Bool
  }
  e

# data only grows a node
def Grows.keep(
  ~M: Machine(),
  +s: Node<Machine.Q(M)>,
  +ds: List<&2, List<&2, U32>>
) -> {Node.grows(~M, s, State.keep(~M, s, ds)) == True{}: Bool}:
  Grows.led(~M, 
    s,
    Ledgers.State.put_datas(~Machine.Q(M), ~Machine.same(M), ds, State.ledger(~M, s)),
    Ledgers.State.put_datas_grows(
      ~Machine.Q(M),
      ~Machine.same(M),
      ~Machine.laws(M),
      ds,
      State.ledger(~M, s)
    )
  )

# the work m, if any, is on a node that grew from s
def Work.after(~M: Machine(), s: Node<Machine.Q(M)>, m: Maybe<&2, Work<Machine.Q(M)>>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{Work{s2, h}}:
      Node.grows(~M, s, s2)

# the node m, if any, grew from s
def State.after(~M: Machine(), s: Node<Machine.Q(M)>, m: Maybe<&2, Node<Machine.Q(M)>>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{s2}:
      Node.grows(~M, s, s2)

# a node that is kept when b holds grew from s, when it did
def Put.grows.if(
  ~M: Machine(),
  s: Node<Machine.Q(M)>,
  -s2: Node<Machine.Q(M)>,
  b: Bool,
  g: {Node.grows(~M, s, s2) == True{}: Bool}
) -> {State.after(~M, s, Shared.Maybe.when(Node<Machine.Q(M)>, b, u => Some{s2})) == True{}: Bool}:
  match b:
    case True{}:
      g
    case False{}:
      {==}

# data that a node puts and reads back only grows it
def Put.grows(
  ~M: Machine(),
  +s: Node<Machine.Q(M)>,
  +ds: List<&2, List<&2, U32>>
) -> {State.after(~M, s, State.put(~M, s, ds)) == True{}: Bool}:
  Put.grows.if(~M, 
    s,
    State.keep(~M, s, ds),
    Stores.Store.holds(~Node<Machine.Q(M)>, ~Store.fetch(~M), State.keep(~M, s, ds), ds),
    Grows.keep(~M, s, ds)
  )

# a work on a node that grew
def Work.on.grows(
  ~M: Machine(),
  s: Node<Machine.Q(M)>,
  m: Maybe<&2, Node<Machine.Q(M)>>,
  h: Maybe<&2, Hashes.Hash>
) -> {
  State.after(~M, s, m) == True{}: Bool
} -> {Work.after(~M, s, Work.on(~M, m, h)) == True{}: Bool}:
  match m:
    case None{}:
      e => {==}
    case Some{s2}:
      e => e

# a new subtree only grows a node
def Work.of.grows(
  ~M: Machine(),
  +s: Node<Machine.Q(M)>,
  m: Maybe<&2, Trees.Put>
) -> {Work.after(~M, s, Work.of(~M, s, m)) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{Trees.Put{h, +ws}}:
      Work.on.grows(~M, s, State.put(~M, s, ws), Some{h})(Put.grows(~M, s, ws))

# a key set in a tree only grows a node
def Set.grows(
  ~M: Machine(),
  +s: Node<Machine.Q(M)>,
  h: Maybe<&2, Hashes.Hash>,
  k: List<&2, U32>,
  x: List<&2, U32>
) -> {Work.after(~M, s, Work.set(~M, Work{s, h}, k, x)) == True{}: Bool}:
  Work.of.grows(~M, s, Node.set(~M, s, h, k, x))

# the run m, if any, is on a node that grew from s
def Run.after(~M: Machine(), s: Node<Machine.Q(M)>, m: Maybe<&2, Run<Machine.Q(M)>>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{Run{s2, t}}:
      Node.grows(~M, s, s2)

# a run is on its own node
def After.self(~M: Machine(), r: Run<Machine.Q(M)>) -> {Run.after(~M, Run.state(~M, r), Some{r}) == True{}: Bool}:
  match r:
    case Run{s, t}:
      Grows.refl(~M, s)

# a run on a node that grew from b is on one that grew from a, when b grew
# from a
def After.trans(
  ~M: Machine(),
  a: Node<Machine.Q(M)>,
  b: Node<Machine.Q(M)>,
  +m: Maybe<&2, Run<Machine.Q(M)>>,
  e1: {Node.grows(~M, a, b) == True{}: Bool},
  e2: {Run.after(~M, b, m) == True{}: Bool}
) -> {Run.after(~M, a, m) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{Run{s2, t}}:
      Grows.trans(~M, a, b, s2)(e1)(e2)

# a run, then a run from it, is on a node that grew
def After.bind(
  ~M: Machine(),
  s: Node<Machine.Q(M)>,
  +m: Maybe<&2, Run<Machine.Q(M)>>,
  f: Run<Machine.Q(M)> -> Maybe<&2, Run<Machine.Q(M)>>,
  hm: {Run.after(~M, s, m) == True{}: Bool},
  hf: @r: Run<Machine.Q(M)> -> {Run.after(~M, Run.state(~M, r), f(r)) == True{}: Bool}
) -> {Run.after(~M, s, Maybe.bind(&2, Run<Machine.Q(M)>, Run<Machine.Q(M)>, m, f)) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{Run{+s2, +t}}:
      After.trans(~M, s, s2, f(Run{s2, t}), hm, hf(Run{s2, t}))

# one of two runs, each on a node that grew
def After.when(
  ~M: Machine(),
  s: Node<Machine.Q(M)>,
  +b: Bool,
  -mx: Maybe<&2, Run<Machine.Q(M)>>,
  -my: Maybe<&2, Run<Machine.Q(M)>>,
  hx: {Run.after(~M, s, mx) == True{}: Bool},
  hy: {Run.after(~M, s, my) == True{}: Bool}
) -> {Run.after(~M, s, Shared.Bool.when(Maybe<&2, Run<Machine.Q(M)>>, b, u => mx, u => my)) == True{}: Bool}:
  match b:
    case True{}:
      hx
    case False{}:
      hy

# a work on a node that grew from b is on one that grew from a, when b grew
# from a
def Work.after.trans(
  ~M: Machine(),
  a: Node<Machine.Q(M)>,
  b: Node<Machine.Q(M)>,
  m: Maybe<&2, Work<Machine.Q(M)>>,
  e1: {Node.grows(~M, a, b) == True{}: Bool},
  e2: {Work.after(~M, b, m) == True{}: Bool}
) -> {Work.after(~M, a, m) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{Work{s3, h}}:
      Grows.trans(~M, a, b, s3)(e1)(e2)

# a key set in a work on a node that grew from s is on a node that grew from s
def Work.set.after(
  ~M: Machine(),
  s: Node<Machine.Q(M)>,
  m: Maybe<&2, Work<Machine.Q(M)>>,
  +k: List<&2, U32>,
  +x: List<&2, U32>
) -> {
  Work.after(~M, s, m) == True{}: Bool
} -> {
  Work.after(~M, 
    s,
    Maybe.bind(&2, Work<Machine.Q(M)>, Work<Machine.Q(M)>, m, w => Work.set(~M, w, k, x))
  )
    == True{}: Bool
}:
  match m:
    case None{}:
      e => {==}
    case Some{Work{+s2, +h}}:
      e => Work.after.trans(~M, 
        s,
        s2,
        Work.set(~M, Work{s2, h}, k, x),
        e,
        Set.grows(~M, s2, h, k, x)
      )

# the node of the work w
def Work.state(~M: Machine(), w: Work<Machine.Q(M)>) -> Node<Machine.Q(M)>:
  match w:
    case Work{s, h}:
      s

# a work is on its own node
def Grown.self(~M: Machine(), w: Work<Machine.Q(M)>) -> {Work.after(~M, Work.state(~M, w), Some{w}) == True{}: Bool}:
  match w:
    case Work{s, h}:
      Grows.refl(~M, s)

# a work, then a work from it, is on a node that grew
def Grown.bind(
  ~M: Machine(),
  s: Node<Machine.Q(M)>,
  +m: Maybe<&2, Work<Machine.Q(M)>>,
  f: Work<Machine.Q(M)> -> Maybe<&2, Work<Machine.Q(M)>>,
  hm: {Work.after(~M, s, m) == True{}: Bool},
  hf: @w: Work<Machine.Q(M)> -> {Work.after(~M, Work.state(~M, w), f(w)) == True{}: Bool}
) -> {Work.after(~M, s, Maybe.bind(&2, Work<Machine.Q(M)>, Work<Machine.Q(M)>, m, f)) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{Work{+s2, +h}}:
      Work.after.trans(~M, s, s2, f(Work{s2, h}), hm, hf(Work{s2, h}))

# a work from a value that the node reads is on a node that grew
def Grown.with(
  ~M: Machine(),
  -A: Data,
  s: Node<Machine.Q(M)>,
  +ma: Maybe<&2, A>,
  -k: A -> Maybe<&2, Work<Machine.Q(M)>>,
  hk: @a: A -> {Work.after(~M, s, k(a)) == True{}: Bool}
) -> {Work.after(~M, s, Maybe.bind(&2, A, Work<Machine.Q(M)>, ma, k)) == True{}: Bool}:
  match ma:
    case None{}:
      {==}
    case Some{a}:
      hk(a)

# one of two works, each on a node that grew
def Grown.when(
  ~M: Machine(),
  s: Node<Machine.Q(M)>,
  +b: Bool,
  -mx: Maybe<&2, Work<Machine.Q(M)>>,
  -my: Maybe<&2, Work<Machine.Q(M)>>,
  hx: {Work.after(~M, s, mx) == True{}: Bool},
  hy: {Work.after(~M, s, my) == True{}: Bool}
) -> {
  Work.after(~M, s, Shared.Bool.when(Maybe<&2, Work<Machine.Q(M)>>, b, u => mx, u => my)) == True{}: Bool
}:
  match b:
    case True{}:
      hx
    case False{}:
      hy

# a key set in a work only grows its node
def Grown.set(
  ~M: Machine(),
  w: Work<Machine.Q(M)>,
  k: List<&2, U32>,
  x: List<&2, U32>
) -> {Work.after(~M, Work.state(~M, w), Work.set(~M, w, k, x)) == True{}: Bool}:
  match w:
    case Work{s, h}:
      Set.grows(~M, s, h, k, x)

# words kept in a work only grow its node
def Grown.keep(
  ~M: Machine(),
  w: Work<Machine.Q(M)>,
  +ns: List<&2, List<&2, U32>>
) -> {Work.after(~M, Work.state(~M, w), Work.keep(~M, w, ns)) == True{}: Bool}:
  match w:
    case Work{+s, h}:
      Work.on.grows(~M, s, State.put(~M, s, ns), h)(Put.grows(~M, s, ns))

# the first tip m of a branch, if any, is on a node that grew from s
def Made.after(~M: Machine(), s: Node<Machine.Q(M)>, m: Maybe<&2, Made<Machine.Q(M)>>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{Made{t, s2}}:
      Node.grows(~M, s, s2)

# a first tip on a work is on a node that grew
def Grown.made.put(
  ~M: Machine(),
  s: Node<Machine.Q(M)>,
  t: Tip,
  m: Maybe<&2, Work<Machine.Q(M)>>
) -> {Work.after(~M, s, m) == True{}: Bool} -> {Made.after(~M, s, Made.put(~M, t, m)) == True{}: Bool}:
  match m:
    case None{}:
      e => {==}
    case Some{Work{s2, l}}:
      e => e

# the verdict m, if any, holds a node that grew from s
def Verdict.after(~M: Machine(), s: Node<Machine.Q(M)>, m: Maybe<&2, Verdict<Machine.Q(M)>>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{Verdict.Stale{}}:
      True{}
    case Some{Verdict.Taken{Work{s2, h}}}:
      Node.grows(~M, s, s2)

# a verdict that takes a work holds its node
def Verdict.take(
  ~M: Machine(),
  s: Node<Machine.Q(M)>,
  m: Maybe<&2, Work<Machine.Q(M)>>
) -> {Work.after(~M, s, m) == True{}: Bool} -> {Verdict.after(~M, s, Work.take(~M, m)) == True{}: Bool}:
  match m:
    case None{}:
      e => {==}
    case Some{Work{s2, h}}:
      e => e

# a verdict from a value that the node reads holds a node that grew
def Verdict.with(
  ~M: Machine(),
  -A: Data,
  s: Node<Machine.Q(M)>,
  +ma: Maybe<&2, A>,
  -k: A -> Maybe<&2, Verdict<Machine.Q(M)>>,
  hk: @a: A -> {Verdict.after(~M, s, k(a)) == True{}: Bool}
) -> {Verdict.after(~M, s, Maybe.bind(&2, A, Verdict<Machine.Q(M)>, ma, k)) == True{}: Bool}:
  match ma:
    case None{}:
      {==}
    case Some{a}:
      hk(a)

# the run of a new log is on a node that grew
def Run.logged.grows(
  ~M: Machine(),
  s: Node<Machine.Q(M)>,
  t: Tip,
  +m: Maybe<&2, Work<Machine.Q(M)>>,
  e: {Work.after(~M, s, m) == True{}: Bool}
) -> {Run.after(~M, s, Run.logged(~M, t, m)) == True{}: Bool}:
  match t m:
    case x None{}:
      {==}
    case Tip{c, old, n, os} Some{Work{s2, l}}:
      e

# Add.grows once the value m of the key is known
def Add.at.grows(
  ~M: Machine(),
  r: Run<Machine.Q(M)>,
  +k: List<&2, U32>,
  +x: List<&2, U32>,
  m: Maybe<&2, List<&2, U32>>
) -> {Run.after(~M, Run.state(~M, r), Run.add.at(~M, r, k, x, m)) == True{}: Bool}:
  match r m:
    case Run{+s, +t} None{}:
      Run.logged.grows(~M, 
        s,
        t,
        Work.set(~M, Work{s, Tip.log(t)}, k, x),
        Set.grows(~M, s, Tip.log(t), k, x)
      )
    case y Some{old}:
      {==}

# a new key in a run's log only grows its node
def Add.grows(
  ~M: Machine(),
  +r: Run<Machine.Q(M)>,
  +k: List<&2, U32>,
  x: List<&2, U32>
) -> {Run.after(~M, Run.state(~M, r), Run.add(~M, r, k, x)) == True{}: Bool}:
  Add.at.grows(~M, 
    r,
    k,
    x,
    Node.get(~M, Run.state(~M, r), Tip.log(Run.tip(~M, r)), k)
  )

# a run one version on is on its own node
def Next.grows(
  ~M: Machine(),
  r: Run<Machine.Q(M)>,
  own: Maybe<&2, List<&2, String>>
) -> {Run.after(~M, Run.state(~M, r), Some{Run.next(~M, r, own)}) == True{}: Bool}:
  match r:
    case Run{s, t}:
      Grows.refl(~M, s)

# a refused request only grows a run's node
def Stale.grows(
  ~M: Machine(),
  r: Run<Machine.Q(M)>,
  i: Ledgers.Id
) -> {Run.after(~M, Run.state(~M, r), Step.stale(~M, r, i)) == True{}: Bool}:
  Add.grows(~M, r, Log.out(i), Out.words(Out.Stale{}))

# a taken request only grows a run's node
def Taken.grows(
  ~M: Machine(),
  +r: Run<Machine.Q(M)>,
  +i: Ledgers.Id,
  +own: Maybe<&2, List<&2, String>>
) -> {Run.after(~M, Run.state(~M, r), Step.taken(~M, r, i, own)) == True{}: Bool}:
  +n = Tip.count(Run.tip(~M, r))
  After.bind(~M, 
    Run.state(~M, r),
    Run.add(~M, r, Log.out(i), Out.words(Out.Taken{n})),
    +r1 => Maybe.bind(
      &2,
      Run<Machine.Q(M)>,
      Run<Machine.Q(M)>,
      Run.add(~M, 
        r1,
        Log.version(n),
        Version.words(Version{i, Tip.content(Run.tip(~M, r1))})
      ),
      r2 => Some{Run.next(~M, r2, own)}
    ),
    Add.grows(~M, r, Log.out(i), Out.words(Out.Taken{n})),
    +r1 => After.bind(~M, 
      Run.state(~M, r1),
      Run.add(~M, 
        r1,
        Log.version(n),
        Version.words(Version{i, Tip.content(Run.tip(~M, r1))})
      ),
      r2 => Some{Run.next(~M, r2, own)},
      Add.grows(~M, 
        r1,
        Log.version(n),
        Version.words(Version{i, Tip.content(Run.tip(~M, r1))})
      ),
      r2 => Next.grows(~M, r2, own)
    )
  )

# a judged request only grows a run's node
def Judged.grows(
  ~M: Machine(),
  +r: Run<Machine.Q(M)>,
  +i: Ledgers.Id,
  +own: Maybe<&2, List<&2, String>>,
  +m: Maybe<&2, Verdict<Machine.Q(M)>>
) -> {
  Verdict.after(~M, Run.state(~M, r), m) == True{}: Bool
} -> {Run.after(~M, Run.state(~M, r), Step.judged(~M, r, i, own, m)) == True{}: Bool}:
  match m:
    case None{}:
      g => {==}
    case Some{Verdict.Stale{}}:
      g => Stale.grows(~M, r, i)
    case Some{Verdict.Taken{Work{+s2, +h}}}:
      g => After.trans(~M, 
        Run.state(~M, r),
        s2,
        Step.taken(~M, Run.over(~M, r, s2, h), i, own),
        g,
        Taken.grows(~M, Run.over(~M, r, s2, h), i, own)
      )

# a mark on a version only grows a run's node
def Marked.grows(
  ~M: Machine(),
  +r: Run<Machine.Q(M)>,
  +i: Ledgers.Id,
  +m: String,
  +v: Maybe<&2, Version>
) -> {Run.after(~M, Run.state(~M, r), Step.marked(~M, r, i, m, v)) == True{}: Bool}:
  match v:
    case None{}:
      {==}
    case Some{+x}:
      After.bind(~M, 
        Run.state(~M, r),
        Run.add(~M, r, Log.mark(m), Ledgers.Id.code(Version.id(x), [])),
        r2 => Step.taken(~M, r2, i, None{}),
        Add.grows(~M, r, Log.mark(m), Ledgers.Id.code(Version.id(x), [])),
        r2 => Taken.grows(~M, r2, i, None{})
      )

# a request for a mark only grows a run's node
def Mark.grows(
  ~M: Machine(),
  +r: Run<Machine.Q(M)>,
  +i: Ledgers.Id,
  +m: String
) -> {Run.after(~M, Run.state(~M, r), Step.mark(~M, r, i, m)) == True{}: Bool}:
  +s = Run.state(~M, r)
  +t = Run.tip(~M, r)
  +n = Tip.count(t)
  After.when(~M, 
    s,
    List.all.if(
      u => Maybe.is_none(&2, Ledgers.Id, Line.mark(~M, s, t, m)),
      Bool.not(U32.is_eq(n, 0))
    ),
    Step.marked(~M, r, i, m, Line.version(~M, s, t, U32.sub(n, 1))),
    Step.stale(~M, r, i),
    Marked.grows(~M, r, i, m, Line.version(~M, s, t, U32.sub(n, 1))),
    Stale.grows(~M, r, i)
  )

# the first tip of a new branch only grows a run's node
def Branch.made.grows(
  ~M: Machine(),
  +r: Run<Machine.Q(M)>,
  +i: Ledgers.Id,
  +b: String,
  m: Maybe<&2, Made<Machine.Q(M)>>
) -> {
  Made.after(~M, Run.state(~M, r), m) == True{}: Bool
} -> {Run.after(~M, Run.state(~M, r), Branch.made(~M, r, i, b, m)) == True{}: Bool}:
  match m:
    case None{}:
      g => {==}
    case Some{Made{+t, +s2}}:
      g =>
        +r1 = {Run.over(~M, r, s2, Tip.content(Run.tip(~M, r))): Run<Machine.Q(M)>}
        After.trans(~M, 
          Run.state(~M, r),
          s2,
          Maybe.bind(
            &2,
            Run<Machine.Q(M)>,
            Run<Machine.Q(M)>,
            Run.add(~M, r1, Log.start(b), Hashes.Hash.code(Tip.hash(t), [])),
            r2 => Step.taken(~M, r2, i, None{})
          ),
          g,
          After.bind(~M, 
            s2,
            Run.add(~M, r1, Log.start(b), Hashes.Hash.code(Tip.hash(t), [])),
            r2 => Step.taken(~M, r2, i, None{}),
            Add.grows(~M, r1, Log.start(b), Hashes.Hash.code(Tip.hash(t), [])),
            r2 => Taken.grows(~M, r2, i, None{})
          )
        )

# the run of picked requests, with one more request or not
def Add.run(
  ~M: Machine(),
  b: Bool,
  i: Ledgers.Id,
  p: Picked<Machine.Q(M)>
) -> {Picked.run(~M, Picked.add(~M, b, i, p)) == Picked.run(~M, p): Run<Machine.Q(M)>}:
  match p:
    case Picked{r, qs}:
      {==}

# the run m, if any, else r, is on a node that grew from that of r
def Default.run.grows(
  ~M: Machine(),
  r: Run<Machine.Q(M)>,
  m: Maybe<&2, Run<Machine.Q(M)>>
) -> {
  Run.after(~M, Run.state(~M, r), m) == True{}: Bool
} -> {
  Node.grows(~M, 
    Run.state(~M, r),
    Run.state(~M, Maybe.default(&2, Run<Machine.Q(M)>, m, r))
  )
    == True{}: Bool
}:
  match m:
    case None{}:
      e => Grows.refl(~M, Run.state(~M, r))
    case Some{Run{s2, t}}:
      e => e

# a run that is kept when b holds is on a node that grew, when it is
def Fit.when.grows(
  ~M: Machine(),
  -s: Node<Machine.Q(M)>,
  b: Bool,
  -r: Run<Machine.Q(M)>,
  e: {Run.after(~M, s, Some{r}) == True{}: Bool}
) -> {Run.after(~M, s, Shared.Maybe.when(Run<Machine.Q(M)>, b, u => Some{r})) == True{}: Bool}:
  match b:
    case True{}:
      e
    case False{}:
      {==}

# a run that fits a tip is on a node that grew, when the run is
def Plan.fit.grows(
  ~M: Machine(),
  -s: Node<Machine.Q(M)>,
  after: Maybe<&2, Hashes.Hash>,
  m: Maybe<&2, Run<Machine.Q(M)>>
) -> {
  Run.after(~M, s, m) == True{}: Bool
} -> {Run.after(~M, s, Plan.fit(~M, after, m)) == True{}: Bool}:
  match m:
    case None{}:
      e => {==}
    case Some{Run{s2, t2}}:
      e => Fit.when.grows(~M, 
        s,
        Root.same(after, Some{Tip.hash(t2)}),
        Run{s2, t2},
        e
      )

# the run of one of two plans, each on a node that grew
def Plan.when.grows(
  ~M: Machine(),
  -s: Node<Machine.Q(M)>,
  b: Bool,
  -x: Plan<Machine.Q(M)>,
  -y: Plan<Machine.Q(M)>,
  hx: {Run.after(~M, s, Plan.run(~M, x)) == True{}: Bool},
  hy: {Run.after(~M, s, Plan.run(~M, y)) == True{}: Bool}
) -> {
  Run.after(~M, s, Plan.run(~M, Shared.Bool.when(Plan<Machine.Q(M)>, b, u => x, u => y))) == True{}: Bool
}:
  match b:
    case True{}:
      hx
    case False{}:
      hy

# a node with the ledger of a node that grew from a grew from a
def Grows.to(
  ~M: Machine(),
  a: Node<Machine.Q(M)>,
  b: Node<Machine.Q(M)>,
  x: Node<Machine.Q(M)>,
  e: {State.ledger(~M, x) == State.ledger(~M, b): Ledgers.State(Machine.Q(M))},
  g: {Node.grows(~M, a, b) == True{}: Bool}
) -> {Node.grows(~M, a, x) == True{}: Bool}:
  %Equal.sym(
    Ledgers.State(Machine.Q(M)),
    State.ledger(~M, x),
    State.ledger(~M, b),
    e
  ): {
    Ledgers.State.grows(~Machine.Q(M), ~Machine.same(M), State.ledger(~M, a), _) == True{}: Bool
  }
  g

# one of two nodes, each grown from s
def Grows.when(
  ~M: Machine(),
  s: Node<Machine.Q(M)>,
  b: Bool,
  -x: Node<Machine.Q(M)>,
  -y: Node<Machine.Q(M)>,
  hx: {Node.grows(~M, s, x) == True{}: Bool},
  hy: {Node.grows(~M, s, y) == True{}: Bool}
) -> {Node.grows(~M, s, Shared.Bool.when(Node<Machine.Q(M)>, b, u => x, u => y)) == True{}: Bool}:
  match b:
    case True{}:
      hx
    case False{}:
      hy

# a moved head keeps the ledger
def Led.moved(
  ~M: Machine(),
  s: Node<Machine.Q(M)>,
  c: Ledgers.Chain,
  h: Head,
  qs: List<&2, Ledgers.Id>
) -> {
  State.ledger(~M, 
    State.moved(~M, s, c, h, qs)
  )
    == State.ledger(~M, s): Ledgers.State(Machine.Q(M))
}:
  match s:
    case Node{l, hs, ws, ks}:
      {==}

# a request that waits keeps the ledger
def Led.waits(
  ~M: Machine(),
  s: Node<Machine.Q(M)>,
  c: Ledgers.Chain,
  i: Ledgers.Id
) -> {
  State.ledger(~M, 
    State.wait(~M, s, c, i)
  )
    == State.ledger(~M, s): Ledgers.State(Machine.Q(M))
}:
  match s:
    case Node{l, hs, ws, ks}:
      {==}

# a node with the ledger of a node that grew from it grew
def Grows.back(
  ~M: Machine(),
  s: Node<Machine.Q(M)>,
  s3: Node<Machine.Q(M)>,
  g: {Node.grows(~M, s, s3) == True{}: Bool}
) -> {Node.grows(~M, s, State.led(~M, s, State.ledger(~M, s3))) == True{}: Bool}:
  Grows.led(~M, s, State.ledger(~M, s3), g)

# new keys keep the ledger
def Led.keyed(
  ~M: Machine(),
  s: Node<Machine.Q(M)>,
  ks: Keys
) -> {
  State.ledger(~M, 
    State.keyed(~M, s, ks)
  )
    == State.ledger(~M, s): Ledgers.State(Machine.Q(M))
}:
  match s:
    case Node{l, hs, ws, old}:
      {==}

# a ballot that a node accepts only grows it
def Accept.at.grows(
  ~M: Machine(),
  +s: Node<Machine.Q(M)>,
  +b: Ledgers.Ballot,
  m: Maybe<&2, Keychain>
) -> {State.after(~M, s, Seal.accept.at(~M, s, b, m)) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{+c}:
      Put.grows.if(~M, 
        s,
        State.keyed(~M, 
          State.led(~M, 
            s,
            Ledgers.State.keep(~Machine.Q(M), ~Machine.same(M), State.ledger(~M, s), b)
          ),
          Keys.saw(
            Keys.set(
              State.keys(~M, s),
              Seal.slot(Ballot.store(b), Ballot.node(b)),
              Keychain.next(c, b)
            ),
            Ballot.at(b)
          )
        ),
        Seal.fits(c, b),
        Grows.to(~M, 
          s,
          State.led(~M, 
            s,
            Ledgers.State.keep(~Machine.Q(M), ~Machine.same(M), State.ledger(~M, s), b)
          ),
          State.keyed(~M, 
            State.led(~M, 
              s,
              Ledgers.State.keep(~Machine.Q(M), ~Machine.same(M), State.ledger(~M, s), b)
            ),
            Keys.saw(
              Keys.set(
                State.keys(~M, s),
                Seal.slot(Ballot.store(b), Ballot.node(b)),
                Keychain.next(c, b)
              ),
              Ballot.at(b)
            )
          ),
          Led.keyed(~M, 
            State.led(~M, 
              s,
              Ledgers.State.keep(~Machine.Q(M), ~Machine.same(M), State.ledger(~M, s), b)
            ),
            Keys.saw(
              Keys.set(
                State.keys(~M, s),
                Seal.slot(Ballot.store(b), Ballot.node(b)),
                Keychain.next(c, b)
              ),
              Ballot.at(b)
            )
          ),
          Grows.led(~M, 
            s,
            Ledgers.State.keep(~Machine.Q(M), ~Machine.same(M), State.ledger(~M, s), b),
            Ledgers.State.add_grows(
              ~Machine.Q(M),
              ~Machine.same(M),
              ~Machine.laws(M),
              State.ledger(~M, s),
              Ledgers.Slot.of(b),
              Ledgers.Entry.Vote{b}
            )
          )
        )
      )

# the node m, if any, else s, grew from s when m did
def Default.grows(
  ~M: Machine(),
  s: Node<Machine.Q(M)>,
  m: Maybe<&2, Node<Machine.Q(M)>>
) -> {
  State.after(~M, s, m) == True{}: Bool
} -> {Node.grows(~M, s, Maybe.default(&2, Node<Machine.Q(M)>, m, s)) == True{}: Bool}:
  match m:
    case None{}:
      e => Grows.refl(~M, s)
    case Some{s2}:
      e => e

# a sealed ballot only grows a node
def Cast.seal.grows(
  ~K: Kernel(),
  +s: Node<Machine.Q(Kernel.machine(K))>,
  +w: Ledgers.Where,
  n: String,
  a0: Ledgers.Act,
  m: Maybe<&2, Keychain>
) -> {Node.grows(~Kernel.machine(K), s, Cast.seal(~K, s, w, n, a0, m)) == True{}: Bool}:
  match m:
    case None{}:
      Grows.refl(~Kernel.machine(K), s)
    case Some{Keychain{+j, last, key, f}}:
      +b = Ledgers.Ballot.make(
        Seal.secret(Keys.seed(State.keys(~Kernel.machine(K), s)), Where.store(w), j),
        Ledgers.Signed{w, n, a0},
        last,
        Seals.Seal.public(
          Seal.secret(
            Keys.seed(State.keys(~Kernel.machine(K), s)),
            Where.store(w),
            U32.inc(j)
          )
        )
      )
      Default.grows(~Kernel.machine(K), 
        s,
        Seal.accept(~K, s, b)
      )(
        Accept.at.grows(~Kernel.machine(K), 
          s,
          b,
          Seal.chain(~K, s, Ballot.store(b), Ballot.node(b))
        )
      )

# a ballot on a node that grew from a, which grew from s, only grows s
def Cast.vote.grows(
  ~K: Kernel(),
  +s: Node<Machine.Q(Kernel.machine(K))>,
  a: Node<Machine.Q(Kernel.machine(K))>,
  m: Maybe<&2, Node<Machine.Q(Kernel.machine(K))>>,
  +w: Ledgers.Where,
  +n: String,
  +a0: Ledgers.Act,
  g: {Node.grows(~Kernel.machine(K), s, a) == True{}: Bool}
) -> {
  State.after(~Kernel.machine(K), a, m) == True{}: Bool
} -> {Node.grows(~Kernel.machine(K), s, Cast.vote(~K, s, m, w, n, a0)) == True{}: Bool}:
  match m:
    case None{}:
      e => Grows.refl(~Kernel.machine(K), s)
    case Some{+s3}:
      e =>
        +s4 = State.led(~Kernel.machine(K), s, State.ledger(~Kernel.machine(K), s3))
        Grows.trans(~Kernel.machine(K), 
          s,
          s4,
          Cast.seal(~K, s4, w, n, a0, Seal.chain(~K, s4, Where.store(w), n))
        )(
          Grows.back(~Kernel.machine(K), s, s3, Grows.trans(~Kernel.machine(K), s, a, s3)(g)(e))
        )(Cast.seal.grows(~K, s4, w, n, a0, Seal.chain(~K, s4, Where.store(w), n)))

# a vote only grows a node
def Cast.put.grows(
  ~K: Kernel(),
  n: String,
  w: Ledgers.Where,
  th: Maybe<&2, Hashes.Hash>,
  qs: List<&2, Ledgers.Id>,
  from: List<&2, String>,
  m: Maybe<&2, Run<Machine.Q(Kernel.machine(K))>>,
  s: Node<Machine.Q(Kernel.machine(K))>
) -> {
  Run.after(~Kernel.machine(K), s, m) == True{}: Bool
} -> {Node.grows(~Kernel.machine(K), s, Cast.put(~K, n, w, th, qs, from, m, s)) == True{}: Bool}:
  match m:
    case None{}:
      e => Grows.refl(~Kernel.machine(K), s)
    case Some{Run{+s2, +t2}}:
      e => Cast.vote.grows(~K, 
        s,
        s2,
        State.put(~Kernel.machine(K), s2, [Tip.words(t2)]),
        w,
        n,
        Ledgers.Act.Vote{Ledgers.Vote{th, qs, Some{Tip.hash(t2)}}, from},
        e
      )(Put.grows(~Kernel.machine(K), s2, [Tip.words(t2)]))

# a pass only grows a node
def Pass.to.grows(
  ~K: Kernel(),
  +n: String,
  +s: Node<Machine.Q(Kernel.machine(K))>,
  w: Ledgers.Where,
  os: List<&2, String>
) -> {Node.grows(~Kernel.machine(K), s, Pass.to(~K, n, s, w, os)) == True{}: Bool}:
  match w:
    case Ledgers.Where{+c, +h, +r}:
      Grows.when(~Kernel.machine(K), 
        s,
        List.all.if(
          u => Maybe.is_none(
            &2,
            Maybe<&2, Ledgers.Last>,
            Ledgers.State.passed(~Machine.Q(Kernel.machine(K)), State.ledger(~Kernel.machine(K), s), Ledgers.Where{c, h, r}, n)
          ),
          List.contains(~String, ~String.eq, os, n)
        ),
        Cast.seal(~K, 
          s,
          Ledgers.Where{c, h, r},
          n,
          Ledgers.Act.Pass{Last.below(~Kernel.machine(K), n, s, c, h, r)},
          Seal.chain(~K, s, Where.store(Ledgers.Where{c, h, r}), n)
        ),
        s,
        Cast.seal.grows(~K, 
          s,
          Ledgers.Where{c, h, r},
          n,
          Ledgers.Act.Pass{Last.below(~Kernel.machine(K), n, s, c, h, r)},
          Seal.chain(~K, s, Where.store(Ledgers.Where{c, h, r}), n)
        ),
        Grows.refl(~Kernel.machine(K), s)
      )

# a node that joins a round only grows a node
def Round.join.grows(
  ~K: Kernel(),
  +n: String,
  +s: Node<Machine.Q(Kernel.machine(K))>,
  +c: Ledgers.Chain,
  +h: U32,
  os: List<&2, String>
) -> {Node.grows(~Kernel.machine(K), s, Round.join(~K, n, s, c, h, os)) == True{}: Bool}:
  +top = Round.seen(~Kernel.machine(K), s, c, h)
  k = top
  Grows.when(~Kernel.machine(K), 
    s,
    Nat.is_lt(Round.mine(~Kernel.machine(K), n, s, c, h, k), top),
    Pass.to(~K, n, s, Ledgers.Where{c, h, top}, os),
    s,
    Pass.to.grows(~K, n, s, Ledgers.Where{c, h, top}, os),
    Grows.refl(~Kernel.machine(K), s)
  )

# Node.pass only grows a node, at the head h whose tip is m
def Pass.at.grows(
  ~K: Kernel(),
  +n: String,
  +s: Node<Machine.Q(Kernel.machine(K))>,
  +c: Ledgers.Chain,
  h: Head,
  m: Maybe<&2, Tip>
) -> {Node.grows(~Kernel.machine(K), s, Pass.at(~K, n, s, c, h, m)) == True{}: Bool}:
  match h m:
    case Head{r, b, +next, th} Some{t}:
      Pass.to.grows(~K, 
        n,
        s,
        Ledgers.Where{c, next, 1n+Round.mine(~Kernel.machine(K), n, s, c, next, Round.seen(~Kernel.machine(K), s, c, next))},
        Tip.owners(t)
      )
    case Head{r, b, next, th} None{}:
      Grows.refl(~Kernel.machine(K), s)

# Node.pass only grows a node, once the head m is known
def Pass.head.grows(
  ~K: Kernel(),
  n: String,
  +s: Node<Machine.Q(Kernel.machine(K))>,
  c: Ledgers.Chain,
  m: Maybe<&2, Head>
) -> {Node.grows(~Kernel.machine(K), s, Pass.head(~K, n, s, c, m)) == True{}: Bool}:
  match m:
    case None{}:
      Grows.refl(~Kernel.machine(K), s)
    case Some{+h}:
      Pass.at.grows(~K, n, s, c, h, Head.tip(~Kernel.machine(K), s, h))

# a head moved on a node that grew from a, which grew from s, only grows s
def Advance.moved.grows(
  ~M: Machine(),
  +s: Node<Machine.Q(M)>,
  a: Node<Machine.Q(M)>,
  m: Maybe<&2, Node<Machine.Q(M)>>,
  +c: Ledgers.Chain,
  +h: Head,
  +qs: List<&2, Ledgers.Id>,
  g: {Node.grows(~M, s, a) == True{}: Bool}
) -> {
  State.after(~M, a, m) == True{}: Bool
} -> {Node.grows(~M, s, Advance.moved(~M, s, m, c, h, qs)) == True{}: Bool}:
  match m:
    case None{}:
      e => Grows.refl(~M, s)
    case Some{+s3}:
      e =>
        +x = State.led(~M, s, State.ledger(~M, s3))
        Grows.to(~M, 
          s,
          x,
          State.moved(~M, x, c, h, qs),
          Led.moved(~M, x, c, h, qs),
          Grows.back(~M, s, s3, Grows.trans(~M, s, a, s3)(g)(e))
        )

# a checked step only grows a node
def Advance.ran.grows(
  ~M: Machine(),
  +s: Node<Machine.Q(M)>,
  c: Ledgers.Chain,
  r: Ledgers.Id,
  b: Maybe<&2, String>,
  next: U32,
  after: Maybe<&2, Hashes.Hash>,
  qs: List<&2, Ledgers.Id>,
  m: Maybe<&2, Run<Machine.Q(M)>>
) -> {
  Run.after(~M, s, m) == True{}: Bool
} -> {Node.grows(~M, s, Advance.ran(~M, s, c, r, b, next, after, qs, m)) == True{}: Bool}:
  match m:
    case None{}:
      e => Grows.refl(~M, s)
    case Some{Run{+s2, +t2}}:
      e =>
        +hd = {Head{r, b, U32.inc(next), Some{Tip.hash(t2)}}: Head}
        Grows.when(~M, 
          s,
          Root.same(after, Some{Tip.hash(t2)}),
          Advance.moved(~M, s, State.put(~M, s2, [Tip.words(t2)]), c, hd, qs),
          s,
          Advance.moved.grows(~M, 
            s,
            s2,
            State.put(~M, s2, [Tip.words(t2)]),
            c,
            hd,
            qs,
            e
          )(Put.grows(~M, s2, [Tip.words(t2)])),
          Grows.refl(~M, s)
        )

# a line that opens only grows a node, once its head m is known
def Open.at.grows(
  ~M: Machine(),
  +s: Node<Machine.Q(M)>,
  +c: Ledgers.Chain,
  m: Maybe<&2, Head>
) -> {Node.grows(~M, s, Open.at(~M, s, c, m)) == True{}: Bool}:
  match m:
    case Some{Head{+r, Some{+b}, n, None{}}}:
      +hd = {
        Head{
          r,
          Some{b},
          0,
          Branch.first(~M, s, b, Node.tip(~M, s, Ledgers.Chain{r, None{}}))
        }: Head
      }
      Grows.to(~M, s, s, State.head(~M, s, c, hd), Led.head(~M, s, c, hd), Grows.refl(~M, s))
    case Some{Head{r, Some{b}, n, Some{t}}}:
      Grows.refl(~M, s)
    case Some{Head{r, None{}, n, t}}:
      Grows.refl(~M, s)
    case None{}:
      Grows.refl(~M, s)

# a first head only grows a node, once the head m of its line is known
def First.at.grows(
  ~M: Machine(),
  +s: Node<Machine.Q(M)>,
  +c: Ledgers.Chain,
  +h: Head,
  m: Maybe<&2, Head>
) -> {Node.grows(~M, s, First.at(~M, s, c, h, m)) == True{}: Bool}:
  match m:
    case Some{Head{r, b, n, Some{t}}}:
      Grows.refl(~M, s)
    case Some{Head{r, b, n, None{}}}:
      Grows.to(~M, s, s, State.head(~M, s, c, h), Led.head(~M, s, c, h), Grows.refl(~M, s))
    case None{}:
      Grows.to(~M, s, s, State.head(~M, s, c, h), Led.head(~M, s, c, h), Grows.refl(~M, s))

# a first head on a node that grew from a, which grew from s, only grows s
def Start.head.grows(
  ~M: Machine(),
  +s: Node<Machine.Q(M)>,
  a: Node<Machine.Q(M)>,
  m: Maybe<&2, Node<Machine.Q(M)>>,
  +c: Ledgers.Chain,
  +h: Head,
  g: {Node.grows(~M, s, a) == True{}: Bool}
) -> {
  State.after(~M, a, m) == True{}: Bool
} -> {Node.grows(~M, s, Start.head(~M, s, m, c, h)) == True{}: Bool}:
  match m:
    case None{}:
      e => Grows.refl(~M, s)
    case Some{+s3}:
      e =>
        +x = State.led(~M, s, State.ledger(~M, s3))
        Grows.trans(~M, 
          s,
          x,
          State.first(~M, x, c, h)
        )(
          Grows.back(~M, s, s3, Grows.trans(~M, s, a, s3)(g)(e))
        )(First.at.grows(~M, x, c, h, Node.head_of(~M, x, c)))

# Start.grows once the content m of the store is known
def Start.with.grows(
  ~M: Machine(),
  +s: Node<Machine.Q(M)>,
  +i: Ledgers.Id,
  +os: List<&2, String>,
  m: Maybe<&2, Work<Machine.Q(M)>>
) -> {
  Work.after(~M, s, m) == True{}: Bool
} -> {Node.grows(~M, s, Start.with(~M, s, i, os, m)) == True{}: Bool}:
  match m:
    case None{}:
      e => Grows.refl(~M, s)
    case Some{Work{+s2, +c}}:
      e =>
        +t = {Tip{c, None{}, 0, os}: Tip}
        Start.head.grows(~M, 
          s,
          s2,
          State.put(~M, s2, [Tip.words(t)]),
          Ledgers.Chain{i, None{}},
          Head{i, None{}, 0, Some{Tip.hash(t)}},
          e
        )(Put.grows(~M, s2, [Tip.words(t)]))

# a line that a node follows only grows it, once its head m is known
def Follow.new.grows(
  ~M: Machine(),
  +s: Node<Machine.Q(M)>,
  +r: Ledgers.Id,
  +l: Maybe<&2, String>,
  m: Maybe<&2, Head>
) -> {Node.grows(~M, s, Follow.new(~M, s, r, l, m)) == True{}: Bool}:
  match m:
    case Some{h}:
      Grows.refl(~M, s)
    case None{}:
      Grows.to(~M, 
        s,
        s,
        State.head(~M, s, Line.chain(r, l), Head{r, l, 0, None{}}),
        Led.head(~M, s, Line.chain(r, l), Head{r, l, 0, None{}}),
        Grows.refl(~M, s)
      )

# the ballots that a chain leads to only grow a node, when each one more does
def Follow.step.grows(
  ~M: Machine(),
  s: Node<Machine.Q(M)>,
  m: Maybe<&2, Node<Machine.Q(M)>>,
  k: Node<Machine.Q(M)> -> Node<Machine.Q(M)>,
  ih: @s2: Node<Machine.Q(M)> -> {Node.grows(~M, s2, k(s2)) == True{}: Bool}
) -> {
  State.after(~M, s, m) == True{}: Bool
} -> {
  Node.grows(~M, 
    s,
    Maybe.default(
      &2,
      Node<Machine.Q(M)>,
      Maybe.bind(&2, Node<Machine.Q(M)>, Node<Machine.Q(M)>, m, s2 => Some{k(s2)}),
      s
    )
  )
    == True{}: Bool
}:
  match m:
    case None{}:
      e => Grows.refl(~M, s)
    case Some{+s2}:
      e => Grows.trans(~M, s, s2, k(s2))(e)(ih(s2))

# the ballots that a chain leads to only grow a node
def Follow.grows(
  ~K: Kernel(),
  f: Nat,
  +s: Node<Machine.Q(Kernel.machine(K))>,
  +p: Tries.Trie<Ledgers.Ballot>,
  +r: Ledgers.Id,
  +n: String,
  mb: Maybe<&2, Ledgers.Ballot>
) -> {Node.grows(~Kernel.machine(K), s, Sealed.follow(~K, f, s, p, r, n, mb)) == True{}: Bool}:
  match f mb:
    case 0n x:
      Grows.refl(~Kernel.machine(K), s)
    case 1n+g None{}:
      Grows.refl(~Kernel.machine(K), s)
    case 1n+(+g) Some{+b}:
      Follow.step.grows(~Kernel.machine(K), 
        s,
        Seal.accept(~K, s, b),
        +s2 => Sealed.follow(~K, g, s2, p, r, n, Pending.next(~K, s2, p, r, n)),
        +s2 => Follow.grows(~K, g, s2, p, r, n, Pending.next(~K, s2, p, r, n))
      )(
        Accept.at.grows(~Kernel.machine(K), 
          s,
          b,
          Seal.chain(~K, s, Ballot.store(b), Ballot.node(b))
        )
      )

# the ballots that the chains of some ballots lead to only grow a node
def Each.grows(
  ~K: Kernel(),
  +f: Nat,
  bs: List<&2, Ledgers.Ballot>,
  +p: Tries.Trie<Ledgers.Ballot>,
  +s: Node<Machine.Q(Kernel.machine(K))>
) -> {Node.grows(~Kernel.machine(K), s, Sealed.each(~K, f, bs, p, s)) == True{}: Bool}:
  match bs:
    case Nil{}:
      Grows.refl(~Kernel.machine(K), s)
    case Con{+b, +rest}:
      +s1 = Sealed.follow(~K, 
        f,
        s,
        p,
        Ballot.store(b),
        Ballot.node(b),
        Pending.next(~K, s, p, Ballot.store(b), Ballot.node(b))
      )
      Grows.trans(~Kernel.machine(K), 
        s,
        s1,
        Sealed.each(~K, f, rest, p, s1)
      )(
        Follow.grows(~K, 
          f,
          s,
          p,
          Ballot.store(b),
          Ballot.node(b),
          Pending.next(~K, s, p, Ballot.store(b), Ballot.node(b))
        )
      )(Each.grows(~K, f, rest, p, s1))

# a slot that holds a cell holds one in a node that grew
def Slot.held_kept(
  ~M: Machine(),
  +a: Node<Machine.Q(M)>,
  +b: Node<Machine.Q(M)>,
  +k: List<&2, Bool>,
  g: {Node.grows(~M, a, b) == True{}: Bool}
) -> {
  Maybe.is_some(
    &2,
    Cells.Cell<Ledgers.Entry<Machine.Q(M)>>,
    Ledgers.State.get(~Machine.Q(M), State.ledger(~M, a), k)
  )
    == True{}: Bool
} -> {
  Maybe.is_some(
    &2,
    Cells.Cell<Ledgers.Entry<Machine.Q(M)>>,
    Ledgers.State.get(~Machine.Q(M), State.ledger(~M, b), k)
  )
    == True{}: Bool
}:
  Cells.Cell.keeps_some(
    ~Ledgers.Entry<Machine.Q(M)>,
    ~Ledgers.Entry.is_eq(~Machine.Q(M), ~Machine.same(M)),
    Ledgers.State.get(~Machine.Q(M), State.ledger(~M, a), k),
    Ledgers.State.get(~Machine.Q(M), State.ledger(~M, b), k)
  )(
    Tries.Trie.keeps_get(
      ~Cells.Cell<Ledgers.Entry<Machine.Q(M)>>,
      ~Cells.Cell.keeps(
        ~Ledgers.Entry<Machine.Q(M)>,
        ~Ledgers.Entry.is_eq(~Machine.Q(M), ~Machine.same(M))
      ),
      ~Cells.Cell.none_kept(
        ~Ledgers.Entry<Machine.Q(M)>,
        ~Ledgers.Entry.is_eq(~Machine.Q(M), ~Machine.same(M))
      ),
      State.ledger(~M, a),
      State.ledger(~M, b),
      k
    )(g)
  )

# a request whose slot holds a cell changes nothing
def Ask.once.at(
  ~K: Kernel(),
  m: String,
  s: Node<Machine.Q(Kernel.machine(K))>,
  e: Envelope,
  q: Machine.Q(Kernel.machine(K)),
  c: Maybe<&2, Cells.Cell<Ledgers.Entry<Machine.Q(Kernel.machine(K))>>>
) -> {
  Maybe.is_some(&2, Cells.Cell<Ledgers.Entry<Machine.Q(Kernel.machine(K))>>, c) == True{}: Bool
} -> {Node.ask.at(~K, m, s, e, q, c) == s: Node<Machine.Q(Kernel.machine(K))>}:
  match c:
    case Some{x}:
      h => {==}
    case None{}:
      h => Empty.absurd(
        {Node.ask.at(~K, m, s, e, q, None{}) == s: Node<Machine.Q(Kernel.machine(K))>},
        Shared.Bool.false_ne_true(h)
      )

# a read of a tree stays in a node that grew
def Get.grows(
  ~M: Machine(),
  +a: Node<Machine.Q(M)>,
  +b: Node<Machine.Q(M)>,
  +h: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  v: List<&2, U32>,
  g: {Node.grows(~M, a, b) == True{}: Bool}
) -> {
  Node.get(~M, a, h, k) == Some{v}: Maybe<&2, List<&2, U32>>
} -> {Node.get(~M, b, h, k) == Some{v}: Maybe<&2, List<&2, U32>>}:
  e => Equal.trans(
    Maybe<&2, List<&2, U32>>,
    Node.get(~M, b, h, k),
    Trees.Tree.get.plain(~Node<Machine.Q(M)>, ~Store.fetch(~M), b, h, k),
    Some{v},
    Trees.Tree.get_plain(~Node<Machine.Q(M)>, ~Store.fetch(~M), b, h, k),
    Trees.Tree.get_grows(
      ~Node<Machine.Q(M)>,
      ~Store.fetch(~M),
      ~Node.grows(~M),
      ~(
        x => y => hh => w => Ledgers.State.data_grows(
          ~Machine.Q(M),
          ~Machine.same(M),
          ~Machine.laws(M),
          State.ledger(~M, x),
          State.ledger(~M, y),
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
        Trees.Tree.get.plain(~Node<Machine.Q(M)>, ~Store.fetch(~M), a, h, k),
        Node.get(~M, a, h, k),
        Some{v},
        Equal.sym(
          Maybe<&2, List<&2, U32>>,
          Node.get(~M, a, h, k),
          Trees.Tree.get.plain(~Node<Machine.Q(M)>, ~Store.fetch(~M), a, h, k),
          Trees.Tree.get_plain(~Node<Machine.Q(M)>, ~Store.fetch(~M), a, h, k)
        ),
        e
      )
    )
  )

# Set.kept once whether the node holds the new nodes is known (b)
def Set.kept.if(
  ~M: Machine(),
  +s: Node<Machine.Q(M)>,
  +h: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  +x: List<&2, U32>,
  +k2: List<&2, U32>,
  v: List<&2, U32>,
  +hh: Hashes.Hash,
  +ws: List<&2, List<&2, U32>>,
  b: Bool,
  eb: {
    Stores.Store.holds(~Node<Machine.Q(M)>, ~Store.fetch(~M), State.keep(~M, s, ws), ws) == b: Bool
  },
  hne: {Shared.List.is_eq(~U32, ~U32.is_eq, k, k2) == False{}: Bool},
  hget: {Node.get(~M, s, h, k2) == Some{v}: Maybe<&2, List<&2, U32>>},
  em: {Node.set(~M, s, h, k, x) == Some{Trees.Put{hh, ws}}: Maybe<&2, Trees.Put>}
) -> Work.Reads(~M, 
  k2,
  v,
  Work.on(~M, Shared.Maybe.when(Node<Machine.Q(M)>, b, u => Some{State.keep(~M, s, ws)}), Some{hh})
):
  match b:
    case False{}:
      Unit{}
    case True{}:
      +sk = State.keep(~M, s, ws)
      Equal.trans(
        Maybe<&2, List<&2, U32>>,
        Node.get(~M, sk, Some{hh}, k2),
        Node.get(~M, sk, h, k2),
        Some{v},
        Equal.trans(
          Maybe<&2, List<&2, U32>>,
          Node.get(~M, sk, Some{hh}, k2),
          Trees.Tree.get.plain(~Node<Machine.Q(M)>, ~Store.fetch(~M), sk, Some{hh}, k2),
          Node.get(~M, sk, h, k2),
          Trees.Tree.get_plain(~Node<Machine.Q(M)>, ~Store.fetch(~M), sk, Some{hh}, k2),
          Equal.trans(
            Maybe<&2, List<&2, U32>>,
            Trees.Tree.get.plain(~Node<Machine.Q(M)>, ~Store.fetch(~M), sk, Some{hh}, k2),
            Trees.Tree.get.plain(~Node<Machine.Q(M)>, ~Store.fetch(~M), sk, h, k2),
            Node.get(~M, sk, h, k2),
            Trees.Tree.get_other(
              ~Node<Machine.Q(M)>,
              ~Store.fetch(~M),
              ~Node.grows(~M),
              ~(
                p => q => g => w => Ledgers.State.data_grows(
                  ~Machine.Q(M),
                  ~Machine.same(M),
                  ~Machine.laws(M),
                  State.ledger(~M, p),
                  State.ledger(~M, q),
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
              Grows.keep(~M, s, ws)
            )(
              hne
            )(
              Equal.trans(
                Maybe<&2, Trees.Put>,
                Trees.Tree.set.plain(~Node<Machine.Q(M)>, ~Store.fetch(~M), s, h, k, x),
                Node.set(~M, s, h, k, x),
                Some{Trees.Put{hh, ws}},
                Equal.sym(
                  Maybe<&2, Trees.Put>,
                  Node.set(~M, s, h, k, x),
                  Trees.Tree.set.plain(~Node<Machine.Q(M)>, ~Store.fetch(~M), s, h, k, x),
                  Trees.Tree.set_plain(~Node<Machine.Q(M)>, ~Store.fetch(~M), s, h, k, x)
                ),
                em
              )
            )(eb),
            Equal.sym(
              Maybe<&2, List<&2, U32>>,
              Node.get(~M, sk, h, k2),
              Trees.Tree.get.plain(~Node<Machine.Q(M)>, ~Store.fetch(~M), sk, h, k2),
              Trees.Tree.get_plain(~Node<Machine.Q(M)>, ~Store.fetch(~M), sk, h, k2)
            )
          )
        ),
        Get.grows(~M, s, sk, h, k2, v, Grows.keep(~M, s, ws))(hget)
      )

# Set.kept once the new subtree m is known
def Set.kept.of(
  ~M: Machine(),
  +s: Node<Machine.Q(M)>,
  h: Maybe<&2, Hashes.Hash>,
  k: List<&2, U32>,
  x: List<&2, U32>,
  k2: List<&2, U32>,
  v: List<&2, U32>,
  m: Maybe<&2, Trees.Put>,
  em: {Node.set(~M, s, h, k, x) == m: Maybe<&2, Trees.Put>},
  hne: {Shared.List.is_eq(~U32, ~U32.is_eq, k, k2) == False{}: Bool},
  hget: {Node.get(~M, s, h, k2) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> Work.Reads(~M, k2, v, Work.of(~M, s, m)):
  match m:
    case None{}:
      Unit{}
    case Some{Trees.Put{hh, +ws}}:
      Set.kept.if(~M, 
        s,
        h,
        k,
        x,
        k2,
        v,
        hh,
        ws,
        Stores.Store.holds(~Node<Machine.Q(M)>, ~Store.fetch(~M), State.keep(~M, s, ws), ws),
        {==},
        hne,
        hget,
        em
      )

# a key set in a tree keeps the value of each other key
def Set.kept(
  ~M: Machine(),
  +s: Node<Machine.Q(M)>,
  +h: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  +x: List<&2, U32>,
  k2: List<&2, U32>,
  v: List<&2, U32>,
  hne: {Shared.List.is_eq(~U32, ~U32.is_eq, k, k2) == False{}: Bool},
  hget: {Node.get(~M, s, h, k2) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> Work.Reads(~M, k2, v, Work.set(~M, Work{s, h}, k, x)):
  Set.kept.of(~M, s, h, k, x, k2, v, Node.set(~M, s, h, k, x), {==}, hne, hget)

# that the log of the run m, if any, reads the key k2 as v
def Run.Keeps(~M: Machine(), k2: List<&2, U32>, v: List<&2, U32>, m: Maybe<&2, Run<Machine.Q(M)>>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{Run{s2, t2}}:
      {Node.get(~M, s2, Tip.log(t2), k2) == Some{v}: Maybe<&2, List<&2, U32>>}

# the run of a new log that keeps a key keeps it
def Run.logged.keeps(
  ~M: Machine(),
  -k2: List<&2, U32>,
  -v: List<&2, U32>,
  t: Tip,
  m: Maybe<&2, Work<Machine.Q(M)>>
) -> Work.Reads(~M, k2, v, m) -> Run.Keeps(~M, k2, v, Run.logged(~M, t, m)):
  match t m:
    case x None{}:
      w => Unit{}
    case Tip{c, old, n, os} Some{Work{s2, l}}:
      w => w

# a key that a tree does not hold is not a key that it holds, once whether
# they are the same is known (b)
def Keys.differ.if(
  ~M: Machine(),
  s: Node<Machine.Q(M)>,
  h: Maybe<&2, Hashes.Hash>,
  k: List<&2, U32>,
  k2: List<&2, U32>,
  v: List<&2, U32>,
  b: Bool,
  eb: {Shared.List.is_eq(~U32, ~U32.is_eq, k, k2) == b: Bool},
  e1: {Node.get(~M, s, h, k) == None{}: Maybe<&2, List<&2, U32>>},
  e2: {Node.get(~M, s, h, k2) == Some{v}: Maybe<&2, List<&2, U32>>}
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
            Node.get(~M, s, h, k),
            Some{v},
            Equal.sym(Maybe<&2, List<&2, U32>>, Node.get(~M, s, h, k), None{}, e1),
            (
              %Equal.sym(List<&2, U32>, k, k2, Shared.List.is_eq_sound(~U32, ~U32.is_eq, ~Shared.U32.laws(), k, k2)(eb)): {Node.get(~M, s, h, _) == Some{v}: Maybe<&2, List<&2, U32>>}
              e2)
          )
        )
      )

# Add.kept when the log does not hold the new key
def Add.new.kept(
  ~M: Machine(),
  +s: Node<Machine.Q(M)>,
  +t: Tip,
  +k: List<&2, U32>,
  +x: List<&2, U32>,
  +k2: List<&2, U32>,
  +v: List<&2, U32>,
  em: {Node.get(~M, s, Tip.log(t), k) == None{}: Maybe<&2, List<&2, U32>>},
  +hr: {Node.get(~M, s, Tip.log(t), k2) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> Run.Keeps(~M, 
  k2,
  v,
  Run.logged(~M, t, Work.set(~M, Work{s, Tip.log(t)}, k, x))
):
  Run.logged.keeps(~M, 
    k2,
    v,
    t,
    Work.set(~M, Work{s, Tip.log(t)}, k, x)
  )(
    Set.kept(~M, 
      s,
      Tip.log(t),
      k,
      x,
      k2,
      v,
      Keys.differ.if(~M, 
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
  ~M: Machine(),
  r: Run<Machine.Q(M)>,
  +k: List<&2, U32>,
  +x: List<&2, U32>,
  +k2: List<&2, U32>,
  +v: List<&2, U32>,
  m: Maybe<&2, List<&2, U32>>
) -> {
  Node.get(~M, 
    Run.state(~M, r),
    Tip.log(Run.tip(~M, r)),
    k
  )
    == m: Maybe<&2, List<&2, U32>>
} -> Run.Keeps(~M, k2, v, Some{r}) -> Run.Keeps(~M, k2, v, Run.add.at(~M, r, k, x, m)):
  match r m:
    case Run{+s, +t} None{}:
      em => hr => Add.new.kept(~M, s, t, k, x, k2, v, em, hr)
    case y Some{old}:
      em => hr => Unit{}

# a new key in a run's log keeps the value of each key that the log holds
def Add.kept(
  ~M: Machine(),
  +r: Run<Machine.Q(M)>,
  +k: List<&2, U32>,
  x: List<&2, U32>,
  k2: List<&2, U32>,
  v: List<&2, U32>
) -> Run.Keeps(~M, k2, v, Some{r}) -> Run.Keeps(~M, k2, v, Run.add(~M, r, k, x)):
  Add.at.kept(~M, 
    r,
    k,
    x,
    k2,
    v,
    Node.get(~M, Run.state(~M, r), Tip.log(Run.tip(~M, r)), k)
  )({==})

# a run, then a run from it that keeps a key, keeps it
def Keeps.bind(
  ~M: Machine(),
  -k2: List<&2, U32>,
  -v: List<&2, U32>,
  m: Maybe<&2, Run<Machine.Q(M)>>,
  -f: Run<Machine.Q(M)> -> Maybe<&2, Run<Machine.Q(M)>>
) -> Run.Keeps(~M, 
  k2,
  v,
  m
) -> (
  @r: Run<Machine.Q(M)> -> Run.Keeps(~M, k2, v, Some{r}) -> Run.Keeps(~M, k2, v, f(r))
) -> Run.Keeps(~M, k2, v, Maybe.bind(&2, Run<Machine.Q(M)>, Run<Machine.Q(M)>, m, f)):
  match m:
    case None{}:
      hm => hf => Unit{}
    case Some{r}:
      hm => hf => hf(r)(hm)

# one of two runs, each of which keeps a key that the run r keeps
def Keeps.when(
  ~M: Machine(),
  -k2: List<&2, U32>,
  -v: List<&2, U32>,
  -r: Run<Machine.Q(M)>,
  b: Bool,
  -mx: Maybe<&2, Run<Machine.Q(M)>>,
  -my: Maybe<&2, Run<Machine.Q(M)>>,
  hx: Run.Keeps(~M, k2, v, Some{r}) -> Run.Keeps(~M, k2, v, mx),
  hy: Run.Keeps(~M, k2, v, Some{r}) -> Run.Keeps(~M, k2, v, my)
) -> Run.Keeps(~M, 
  k2,
  v,
  Some{r}
) -> Run.Keeps(~M, k2, v, Shared.Bool.when(Maybe<&2, Run<Machine.Q(M)>>, b, u => mx, u => my)):
  match b:
    case True{}:
      hx
    case False{}:
      hy

# a run one version on keeps each key of its log
def Next.kept(
  ~M: Machine(),
  r: Run<Machine.Q(M)>,
  -own: Maybe<&2, List<&2, String>>,
  -k2: List<&2, U32>,
  -v: List<&2, U32>
) -> Run.Keeps(~M, k2, v, Some{r}) -> Run.Keeps(~M, k2, v, Some{Run.next(~M, r, own)}):
  match r:
    case Run{s, Tip{c, l, n, os}}:
      hr => hr

# a taken request keeps each key of a run's log
def Taken.kept(
  ~M: Machine(),
  +r: Run<Machine.Q(M)>,
  +i: Ledgers.Id,
  own: Maybe<&2, List<&2, String>>,
  +k2: List<&2, U32>,
  +v: List<&2, U32>
) -> Run.Keeps(~M, k2, v, Some{r}) -> Run.Keeps(~M, k2, v, Step.taken(~M, r, i, own)):
  +n = Tip.count(Run.tip(~M, r))
  hr => Keeps.bind(~M, 
    k2,
    v,
    Run.add(~M, r, Log.out(i), Out.words(Out.Taken{n})),
    +r1 => Maybe.bind(
      &2,
      Run<Machine.Q(M)>,
      Run<Machine.Q(M)>,
      Run.add(~M, 
        r1,
        Log.version(n),
        Version.words(Version{i, Tip.content(Run.tip(~M, r1))})
      ),
      r2 => Some{Run.next(~M, r2, own)}
    )
  )(
    Add.kept(~M, r, Log.out(i), Out.words(Out.Taken{n}), k2, v)(hr)
  )(
    +r1 => h1 => Keeps.bind(~M, 
      k2,
      v,
      Run.add(~M, 
        r1,
        Log.version(n),
        Version.words(Version{i, Tip.content(Run.tip(~M, r1))})
      ),
      r2 => Some{Run.next(~M, r2, own)}
    )(
      Add.kept(~M, 
        r1,
        Log.version(n),
        Version.words(Version{i, Tip.content(Run.tip(~M, r1))}),
        k2,
        v
      )(h1)
    )(r2 => h2 => Next.kept(~M, r2, own, k2, v)(h2))
  )

# a run over a node that grew keeps each key of its log
def Over.kept(
  ~M: Machine(),
  r: Run<Machine.Q(M)>,
  s2: Node<Machine.Q(M)>,
  -h: Maybe<&2, Hashes.Hash>,
  k2: List<&2, U32>,
  v: List<&2, U32>,
  g: {Node.grows(~M, Run.state(~M, r), s2) == True{}: Bool}
) -> Run.Keeps(~M, k2, v, Some{r}) -> Run.Keeps(~M, k2, v, Some{Run.over(~M, r, s2, h)}):
  match r:
    case Run{s, Tip{c, l, n, os}}:
      hr => Get.grows(~M, s, s2, l, k2, v, g)(hr)

# a judged request keeps each key of a run's log, other than the owners and
# the count
def Judged.kept(
  ~M: Machine(),
  +r: Run<Machine.Q(M)>,
  i: Ledgers.Id,
  own: Maybe<&2, List<&2, String>>,
  m: Maybe<&2, Verdict<Machine.Q(M)>>,
  +k2: List<&2, U32>,
  +v: List<&2, U32>
) -> {
  Verdict.after(~M, Run.state(~M, r), m) == True{}: Bool
} -> Run.Keeps(~M, k2, v, Some{r}) -> Run.Keeps(~M, k2, v, Step.judged(~M, r, i, own, m)):
  match m:
    case None{}:
      g => hr => Unit{}
    case Some{Verdict.Stale{}}:
      g => hr => Add.kept(~M, r, Log.out(i), Out.words(Out.Stale{}), k2, v)(hr)
    case Some{Verdict.Taken{Work{+s2, h}}}:
      g => hr => Taken.kept(~M, 
        Run.over(~M, r, s2, h),
        i,
        own,
        k2,
        v
      )(Over.kept(~M, r, s2, h, k2, v, g)(hr))

# a mark on a version keeps each key of a run's log, other than the owners
# and the count
def Marked.kept(
  ~M: Machine(),
  +r: Run<Machine.Q(M)>,
  i: Ledgers.Id,
  +m: String,
  x: Maybe<&2, Version>,
  +k2: List<&2, U32>,
  +v: List<&2, U32>
) -> Run.Keeps(~M, k2, v, Some{r}) -> Run.Keeps(~M, k2, v, Step.marked(~M, r, i, m, x)):
  match x:
    case None{}:
      hr => Unit{}
    case Some{+y}:
      hr => Keeps.bind(~M, 
        k2,
        v,
        Run.add(~M, r, Log.mark(m), Ledgers.Id.code(Version.id(y), [])),
        r2 => Step.taken(~M, r2, i, None{})
      )(
        Add.kept(~M, r, Log.mark(m), Ledgers.Id.code(Version.id(y), []), k2, v)(hr)
      )(r2 => h2 => Taken.kept(~M, r2, i, None{}, k2, v)(h2))

# a request for a mark keeps each key of a run's log, other than the owners
# and the count
def Mark.kept(
  ~M: Machine(),
  +r: Run<Machine.Q(M)>,
  +i: Ledgers.Id,
  +m: String,
  +k2: List<&2, U32>,
  +v: List<&2, U32>
) -> Run.Keeps(~M, k2, v, Some{r}) -> Run.Keeps(~M, k2, v, Step.mark(~M, r, i, m)):
  +s = Run.state(~M, r)
  +t = Run.tip(~M, r)
  +n = Tip.count(t)
  Keeps.when(~M, 
    k2,
    v,
    r,
    List.all.if(
      u => Maybe.is_none(&2, Ledgers.Id, Line.mark(~M, s, t, m)),
      Bool.not(U32.is_eq(n, 0))
    ),
    Step.marked(~M, r, i, m, Line.version(~M, s, t, U32.sub(n, 1))),
    Step.stale(~M, r, i),
    Marked.kept(~M, r, i, m, Line.version(~M, s, t, U32.sub(n, 1)), k2, v),
    Add.kept(~M, r, Log.out(i), Out.words(Out.Stale{}), k2, v)
  )

# the first tip of a new branch keeps each key of a run's log, other than the
# owners and the count
def Branch.made.kept(
  ~M: Machine(),
  +r: Run<Machine.Q(M)>,
  i: Ledgers.Id,
  +b: String,
  m: Maybe<&2, Made<Machine.Q(M)>>,
  +k2: List<&2, U32>,
  +v: List<&2, U32>
) -> {
  Made.after(~M, Run.state(~M, r), m) == True{}: Bool
} -> Run.Keeps(~M, k2, v, Some{r}) -> Run.Keeps(~M, k2, v, Branch.made(~M, r, i, b, m)):
  match m:
    case None{}:
      g => hr => Unit{}
    case Some{Made{+t, +s2}}:
      g => hr =>
        +r1 = {Run.over(~M, r, s2, Tip.content(Run.tip(~M, r))): Run<Machine.Q(M)>}
        Keeps.bind(~M, 
          k2,
          v,
          Run.add(~M, r1, Log.start(b), Hashes.Hash.code(Tip.hash(t), [])),
          r2 => Step.taken(~M, r2, i, None{})
        )(
          Add.kept(~M, 
            r1,
            Log.start(b),
            Hashes.Hash.code(Tip.hash(t), []),
            k2,
            v
          )(Over.kept(~M, r, s2, Tip.content(Run.tip(~M, r)), k2, v, g)(hr))
        )(r2 => h2 => Taken.kept(~M, r2, i, None{}, k2, v)(h2))

# a tip that a node holds, a node that grew from it holds
def Tip.at.grows(
  ~M: Machine(),
  +a: Node<Machine.Q(M)>,
  b: Node<Machine.Q(M)>,
  +x: Hashes.Hash,
  -t: Tip,
  g: {Node.grows(~M, a, b) == True{}: Bool}
) -> {
  Tip.at(~M, a, x) == Some{t}: Maybe<&2, Tip>
} -> {Tip.at(~M, b, x) == Some{t}: Maybe<&2, Tip>}:
  Shared.Maybe.bind_kept(
    List<&2, U32>,
    Tip,
    Store.fetch(~M, a, x),
    Store.fetch(~M, b, x),
    ws => Tip.read(ws),
    ws => Tip.read(ws),
    t,
    w => Ledgers.State.data_grows(
      ~Machine.Q(M),
      ~Machine.same(M),
      ~Machine.laws(M),
      State.ledger(~M, a),
      State.ledger(~M, b),
      x,
      w
    )(g),
    w => e => e
  )

# the tip of a head, in a node that grew
def Head.tip.grows(
  ~M: Machine(),
  a: Node<Machine.Q(M)>,
  b: Node<Machine.Q(M)>,
  h: Head,
  -t: Tip,
  g: {Node.grows(~M, a, b) == True{}: Bool}
) -> {
  Head.tip(~M, a, h) == Some{t}: Maybe<&2, Tip>
} -> {Head.tip(~M, b, h) == Some{t}: Maybe<&2, Tip>}:
  match h:
    case Head{r, br, n, th}:
      Shared.Maybe.bind_kept(
        Hashes.Hash,
        Tip,
        th,
        th,
        x => Tip.at(~M, a, x),
        x => Tip.at(~M, b, x),
        t,
        x => e => e,
        +x => Tip.at.grows(~M, a, b, x, t, g)
      )

# what the log of a head holds, in a node that grew
def Head.get.grows(
  ~M: Machine(),
  +a: Node<Machine.Q(M)>,
  +b: Node<Machine.Q(M)>,
  +h: Head,
  k: List<&2, U32>,
  v: List<&2, U32>,
  +g: {Node.grows(~M, a, b) == True{}: Bool}
) -> {
  Head.get(~M, a, h, k) == Some{v}: Maybe<&2, List<&2, U32>>
} -> {Head.get(~M, b, h, k) == Some{v}: Maybe<&2, List<&2, U32>>}:
  Shared.Maybe.bind_kept(
    Tip,
    List<&2, U32>,
    Head.tip(~M, a, h),
    Head.tip(~M, b, h),
    t => Node.get(~M, a, Tip.log(t), k),
    t => Node.get(~M, b, Tip.log(t), k),
    v,
    t => Head.tip.grows(~M, a, b, h, t, g),
    t => Get.grows(~M, a, b, Tip.log(t), k, v, g)
  )

# a line whose head is the same in a node that grew holds what it held
def Line.same(
  ~M: Machine(),
  +a: Node<Machine.Q(M)>,
  b: Node<Machine.Q(M)>,
  c: Ledgers.Chain,
  k: List<&2, U32>,
  v: List<&2, U32>,
  g: {Node.grows(~M, a, b) == True{}: Bool},
  eh: {Node.head_of(~M, a, c) == Node.head_of(~M, b, c): Maybe<&2, Head>}
) -> {
  Line.get(~M, a, c, k) == Some{v}: Maybe<&2, List<&2, U32>>
} -> {Line.get(~M, b, c, k) == Some{v}: Maybe<&2, List<&2, U32>>}:
  Shared.Maybe.bind_kept(
    Head,
    List<&2, U32>,
    Node.head_of(~M, a, c),
    Node.head_of(~M, b, c),
    h => Head.get(~M, a, h, k),
    h => Head.get(~M, b, h, k),
    v,
    h => e => Equal.trans(
      Maybe<&2, Head>,
      Node.head_of(~M, b, c),
      Node.head_of(~M, a, c),
      Some{h},
      Equal.sym(Maybe<&2, Head>, Node.head_of(~M, a, c), Node.head_of(~M, b, c), eh),
      e
    ),
    +h => Head.get.grows(~M, a, b, h, k, v, g)
  )

# a node keeps its own logs
def Kept.refl(~M: Machine(), -s: Node<Machine.Q(M)>) -> Node.Keeps(~M, s, s):
  c => k => v => e => e

# keeping composes
def Kept.trans(
  ~M: Machine(),
  -a: Node<Machine.Q(M)>,
  -b: Node<Machine.Q(M)>,
  -d: Node<Machine.Q(M)>,
  h1: Node.Keeps(~M, a, b),
  h2: Node.Keeps(~M, b, d)
) -> Node.Keeps(~M, a, d):
  +c => +k => +v => e => h2(c)(k)(v)(h1(c)(k)(v)(e))

# one of two nodes, each of which keeps the logs of s
def Kept.when(
  ~M: Machine(),
  b: Bool,
  -s: Node<Machine.Q(M)>,
  -x: Node<Machine.Q(M)>,
  -y: Node<Machine.Q(M)>,
  hx: Node.Keeps(~M, s, x),
  hy: Node.Keeps(~M, s, y)
) -> Node.Keeps(~M, s, Shared.Bool.when(Node<Machine.Q(M)>, b, u => x, u => y)):
  match b:
    case True{}:
      hx
    case False{}:
      hy

# a node that grew, with the same heads, keeps the logs
def Kept.same(
  ~M: Machine(),
  a: Node<Machine.Q(M)>,
  b: Node<Machine.Q(M)>,
  g: {Node.grows(~M, a, b) == True{}: Bool},
  eh: {State.heads(~M, a) == State.heads(~M, b): Tries.Trie<Head>}
) -> Node.Keeps(~M, a, b):
  +c => k => v => Line.same(~M, 
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
      State.heads(~M, a),
      State.heads(~M, b),
      eh
    )
  )

# a new ledger keeps the heads
def Heads.led(
  ~M: Machine(),
  s: Node<Machine.Q(M)>,
  l: Ledgers.State(Machine.Q(M))
) -> {State.heads(~M, s) == State.heads(~M, State.led(~M, s, l)): Tries.Trie<Head>}:
  match s:
    case Node{old, hs, ws, ks}:
      {==}

# new waiting requests keep the heads
def Heads.wait(
  ~M: Machine(),
  s: Node<Machine.Q(M)>,
  c: Ledgers.Chain,
  qs: List<&2, Ledgers.Id>
) -> {
  State.heads(~M, s) == State.heads(~M, Wait.set(~M, s, c, qs)): Tries.Trie<Head>
}:
  match s:
    case Node{l, hs, ws, ks}:
      {==}

# the head of a line, after the head of the line c is set
def Head.of_set(
  ~M: Machine(),
  b0: Node<Machine.Q(M)>,
  c: Ledgers.Chain,
  hd: Head,
  c2: Ledgers.Chain
) -> {
  Node.head_of(~M, 
    State.head(~M, b0, c, hd),
    c2
  )
    == Bool.pick(
      Maybe<&2, Head>,
      Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
      Some{hd},
      Node.head_of(~M, b0, c2)
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
  ~M: Machine(),
  -a: Node<Machine.Q(M)>,
  -c: Ledgers.Chain,
  -k: List<&2, U32>,
  -v: List<&2, U32>,
  -m: Maybe<&2, Head>,
  em: {Node.head_of(~M, a, c) == m: Maybe<&2, Head>}
) -> {
  Line.get(~M, a, c, k) == Some{v}: Maybe<&2, List<&2, U32>>
} -> {
  Maybe.bind(
    &2,
    Head,
    List<&2, U32>,
    m,
    h => Head.get(~M, a, h, k)
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
        h => Head.get(~M, a, h, k)
      )
        == Some{v}: Maybe<&2, List<&2, U32>>
    }
    e

# Head.put.kept once whether c2 is the line c is known (bs)
def Head.put.kept.if(
  ~M: Machine(),
  +a: Node<Machine.Q(M)>,
  +b0: Node<Machine.Q(M)>,
  +c: Ledgers.Chain,
  +hd: Head,
  +c2: Ledgers.Chain,
  k: List<&2, U32>,
  v: List<&2, U32>,
  bs: Bool,
  +ebs: {Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)) == bs: Bool},
  g: {Node.grows(~M, a, b0) == True{}: Bool},
  eh: {State.heads(~M, a) == State.heads(~M, b0): Tries.Trie<Head>},
  cov: {
    Line.get(~M, a, c, k) == Some{v}: Maybe<&2, List<&2, U32>>
  } -> {Head.get(~M, State.head(~M, b0, c, hd), hd, k) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> {
  Line.get(~M, a, c2, k) == Some{v}: Maybe<&2, List<&2, U32>>
} -> {Line.get(~M, State.head(~M, b0, c, hd), c2, k) == Some{v}: Maybe<&2, List<&2, U32>>}:
  match bs:
    case True{}:
      e =>
        %Equal.sym(
          Maybe<&2, Head>,
          Node.head_of(~M, State.head(~M, b0, c, hd), c2),
          Some{hd},
          Equal.trans(
            Maybe<&2, Head>,
            Node.head_of(~M, State.head(~M, b0, c, hd), c2),
            Bool.pick(
              Maybe<&2, Head>,
              Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
              Some{hd},
              Node.head_of(~M, b0, c2)
            ),
            Some{hd},
            Head.of_set(~M, b0, c, hd, c2),
            Pick.of(
              Maybe<&2, Head>,
              True{},
              Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
              Some{hd},
              Node.head_of(~M, b0, c2),
              ebs
            )
          )
        ): {
          Maybe.bind(
            &2,
            Head,
            List<&2, U32>,
            _,
            h => Head.get(~M, State.head(~M, b0, c, hd), h, k)
          )
            == Some{v}: Maybe<&2, List<&2, U32>>
        }
        cov(
          Equal.trans(
            Maybe<&2, List<&2, U32>>,
            Line.get(~M, a, c, k),
            Line.get(~M, a, c2, k),
            Some{v},
            Equal.cong(
              List<&2, Bool>,
              Maybe<&2, List<&2, U32>>,
              kk => Maybe.bind(
                &2,
                Head,
                List<&2, U32>,
                Tries.Trie.get(Head, State.heads(~M, a), kk),
                h => Head.get(~M, a, h, k)
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
      Line.same(~M, 
        a,
        State.head(~M, b0, c, hd),
        c2,
        k,
        v,
        Grows.to(~M, 
          a,
          b0,
          State.head(~M, b0, c, hd),
          Led.head(~M, b0, c, hd),
          g
        ),
        Equal.trans(
          Maybe<&2, Head>,
          Node.head_of(~M, a, c2),
          Node.head_of(~M, b0, c2),
          Node.head_of(~M, State.head(~M, b0, c, hd), c2),
          Equal.cong(
            Tries.Trie<Head>,
            Maybe<&2, Head>,
            hs => Tries.Trie.get(Head, hs, Ledgers.Chain.key(c2)),
            State.heads(~M, a),
            State.heads(~M, b0),
            eh
          ),
          Equal.sym(
            Maybe<&2, Head>,
            Node.head_of(~M, State.head(~M, b0, c, hd), c2),
            Node.head_of(~M, b0, c2),
            Equal.trans(
              Maybe<&2, Head>,
              Node.head_of(~M, State.head(~M, b0, c, hd), c2),
              Bool.pick(
                Maybe<&2, Head>,
                Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
                Some{hd},
                Node.head_of(~M, b0, c2)
              ),
              Node.head_of(~M, b0, c2),
              Head.of_set(~M, b0, c, hd, c2),
              Pick.of(
                Maybe<&2, Head>,
                False{},
                Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
                Some{hd},
                Node.head_of(~M, b0, c2),
                ebs
              )
            )
          )
        )
      )

# a node b0 with a new head hd of the line c keeps the logs of a, when b0 grew
# from a with the same heads, and hd holds what the line c holds in a
def Head.put.kept(
  ~M: Machine(),
  a: Node<Machine.Q(M)>,
  b0: Node<Machine.Q(M)>,
  +c: Ledgers.Chain,
  hd: Head,
  g: {Node.grows(~M, a, b0) == True{}: Bool},
  eh: {State.heads(~M, a) == State.heads(~M, b0): Tries.Trie<Head>},
  cover: @k: List<
    &2,
    U32> -> @v: List<
    &2,
    U32> -> {
    Line.get(~M, a, c, k) == Some{v}: Maybe<&2, List<&2, U32>>
  } -> {Head.get(~M, State.head(~M, b0, c, hd), hd, k) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> Node.Keeps(~M, a, State.head(~M, b0, c, hd)):
  +c2 => +k => +v => Head.put.kept.if(~M, 
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
  ~M: Machine(),
  b: Bool,
  -s: Node<Machine.Q(M)>,
  -x: Node<Machine.Q(M)>,
  -y: Node<Machine.Q(M)>,
  hx: {State.heads(~M, s) == State.heads(~M, x): Tries.Trie<Head>},
  hy: {State.heads(~M, s) == State.heads(~M, y): Tries.Trie<Head>}
) -> {
  State.heads(~M, 
    s
  )
    == State.heads(~M, Shared.Bool.when(Node<Machine.Q(M)>, b, u => x, u => y)): Tries.Trie<Head>
}:
  match b:
    case True{}:
      hx
    case False{}:
      hy

# new keys keep the heads
def Heads.keyed(
  ~M: Machine(),
  s: Node<Machine.Q(M)>,
  ks: Keys
) -> {
  State.heads(~M, s) == State.heads(~M, State.keyed(~M, s, ks)): Tries.Trie<Head>
}:
  match s:
    case Node{l, hs, ws, old}:
      {==}

# the heads of the node m, if any, else of s
def Heads.of(~M: Machine(), s: Node<Machine.Q(M)>, m: Maybe<&2, Node<Machine.Q(M)>>) -> Tries.Trie<Head>:
  match m:
    case None{}:
      State.heads(~M, s)
    case Some{s2}:
      State.heads(~M, s2)

# a node that is kept when b holds has the heads of s, when it has
def Heads.some.if(
  ~M: Machine(),
  b: Bool,
  -s: Node<Machine.Q(M)>,
  -x: Node<Machine.Q(M)>,
  hx: {State.heads(~M, s) == State.heads(~M, x): Tries.Trie<Head>}
) -> {
  State.heads(~M, 
    s
  )
    == Heads.of(~M, s, Shared.Maybe.when(Node<Machine.Q(M)>, b, u => Some{x})): Tries.Trie<Head>
}:
  match b:
    case True{}:
      hx
    case False{}:
      {==}

# a ballot that a node accepts keeps the heads
def Accept.at.heads(
  ~M: Machine(),
  +s: Node<Machine.Q(M)>,
  +b: Ledgers.Ballot,
  m: Maybe<&2, Keychain>
) -> {
  State.heads(~M, s) == Heads.of(~M, s, Seal.accept.at(~M, s, b, m)): Tries.Trie<Head>
}:
  match m:
    case None{}:
      {==}
    case Some{+c}:
      Heads.some.if(~M, 
        Seal.fits(c, b),
        s,
        State.keyed(~M, 
          State.led(~M, 
            s,
            Ledgers.State.keep(~Machine.Q(M), ~Machine.same(M), State.ledger(~M, s), b)
          ),
          Keys.saw(
            Keys.set(
              State.keys(~M, s),
              Seal.slot(Ballot.store(b), Ballot.node(b)),
              Keychain.next(c, b)
            ),
            Ballot.at(b)
          )
        ),
        Equal.trans(
          Tries.Trie<Head>,
          State.heads(~M, s),
          State.heads(~M, 
            State.led(~M, 
              s,
              Ledgers.State.keep(~Machine.Q(M), ~Machine.same(M), State.ledger(~M, s), b)
            )
          ),
          State.heads(~M, 
            State.keyed(~M, 
              State.led(~M, 
                s,
                Ledgers.State.keep(~Machine.Q(M), ~Machine.same(M), State.ledger(~M, s), b)
              ),
              Keys.saw(
                Keys.set(
                  State.keys(~M, s),
                  Seal.slot(Ballot.store(b), Ballot.node(b)),
                  Keychain.next(c, b)
                ),
                Ballot.at(b)
              )
            )
          ),
          Heads.led(~M, 
            s,
            Ledgers.State.keep(~Machine.Q(M), ~Machine.same(M), State.ledger(~M, s), b)
          ),
          Heads.keyed(~M, 
            State.led(~M, 
              s,
              Ledgers.State.keep(~Machine.Q(M), ~Machine.same(M), State.ledger(~M, s), b)
            ),
            Keys.saw(
              Keys.set(
                State.keys(~M, s),
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
  ~M: Machine(),
  -s: Node<Machine.Q(M)>,
  m: Maybe<&2, Node<Machine.Q(M)>>
) -> {
  State.heads(~M, s) == Heads.of(~M, s, m): Tries.Trie<Head>
} -> {
  State.heads(~M, 
    s
  )
    == State.heads(~M, Maybe.default(&2, Node<Machine.Q(M)>, m, s)): Tries.Trie<Head>
}:
  match m:
    case None{}:
      e => {==}
    case Some{s2}:
      e => e

# a sealed ballot keeps the heads
def Cast.seal.heads(
  ~K: Kernel(),
  +s: Node<Machine.Q(Kernel.machine(K))>,
  +w: Ledgers.Where,
  n: String,
  a0: Ledgers.Act,
  m: Maybe<&2, Keychain>
) -> {
  State.heads(~Kernel.machine(K), 
    s
  )
    == State.heads(~Kernel.machine(K), Cast.seal(~K, s, w, n, a0, m)): Tries.Trie<Head>
}:
  match m:
    case None{}:
      {==}
    case Some{Keychain{+j, last, key, f}}:
      +b = Ledgers.Ballot.make(
        Seal.secret(Keys.seed(State.keys(~Kernel.machine(K), s)), Where.store(w), j),
        Ledgers.Signed{w, n, a0},
        last,
        Seals.Seal.public(
          Seal.secret(
            Keys.seed(State.keys(~Kernel.machine(K), s)),
            Where.store(w),
            U32.inc(j)
          )
        )
      )
      Default.heads(~Kernel.machine(K), 
        s,
        Seal.accept(~K, s, b)
      )(
        Accept.at.heads(~Kernel.machine(K), 
          s,
          b,
          Seal.chain(~K, s, Ballot.store(b), Ballot.node(b))
        )
      )

# a ballot keeps the heads
def Cast.vote.heads(
  ~K: Kernel(),
  +s: Node<Machine.Q(Kernel.machine(K))>,
  m: Maybe<&2, Node<Machine.Q(Kernel.machine(K))>>,
  +w: Ledgers.Where,
  +n: String,
  a0: Ledgers.Act
) -> {
  State.heads(~Kernel.machine(K), 
    s
  )
    == State.heads(~Kernel.machine(K), Cast.vote(~K, s, m, w, n, a0)): Tries.Trie<Head>
}:
  match m:
    case None{}:
      {==}
    case Some{+s3}:
      +s4 = State.led(~Kernel.machine(K), s, State.ledger(~Kernel.machine(K), s3))
      Equal.trans(
        Tries.Trie<Head>,
        State.heads(~Kernel.machine(K), s),
        State.heads(~Kernel.machine(K), s4),
        State.heads(~Kernel.machine(K), 
          Cast.seal(~K, s4, w, n, a0, Seal.chain(~K, s4, Where.store(w), n))
        ),
        Heads.led(~Kernel.machine(K), s, State.ledger(~Kernel.machine(K), s3)),
        Cast.seal.heads(~K, s4, w, n, a0, Seal.chain(~K, s4, Where.store(w), n))
      )

# the ballots that a chain leads to keep the heads, when each one more does
def Follow.step.heads(
  ~M: Machine(),
  -s: Node<Machine.Q(M)>,
  m: Maybe<&2, Node<Machine.Q(M)>>,
  -k: Node<Machine.Q(M)> -> Node<Machine.Q(M)>,
  ih: @s2: Node<Machine.Q(M)> -> {
    State.heads(~M, s2) == State.heads(~M, k(s2)): Tries.Trie<Head>
  }
) -> {
  State.heads(~M, s) == Heads.of(~M, s, m): Tries.Trie<Head>
} -> {
  State.heads(~M, 
    s
  )
    == State.heads(~M, 
      Maybe.default(
        &2,
        Node<Machine.Q(M)>,
        Maybe.bind(&2, Node<Machine.Q(M)>, Node<Machine.Q(M)>, m, s2 => Some{k(s2)}),
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
        State.heads(~M, s),
        State.heads(~M, s2),
        State.heads(~M, k(s2)),
        e,
        ih(s2)
      )

# the ballots that a chain leads to keep the heads
def Follow.heads(
  ~K: Kernel(),
  f: Nat,
  +s: Node<Machine.Q(Kernel.machine(K))>,
  +p: Tries.Trie<Ledgers.Ballot>,
  +r: Ledgers.Id,
  +n: String,
  mb: Maybe<&2, Ledgers.Ballot>
) -> {
  State.heads(~Kernel.machine(K), 
    s
  )
    == State.heads(~Kernel.machine(K), Sealed.follow(~K, f, s, p, r, n, mb)): Tries.Trie<Head>
}:
  match f mb:
    case 0n x:
      {==}
    case 1n+g None{}:
      {==}
    case 1n+(+g) Some{+b}:
      Follow.step.heads(~Kernel.machine(K), 
        s,
        Seal.accept(~K, s, b),
        +s2 => Sealed.follow(~K, g, s2, p, r, n, Pending.next(~K, s2, p, r, n)),
        +s2 => Follow.heads(~K, g, s2, p, r, n, Pending.next(~K, s2, p, r, n))
      )(
        Accept.at.heads(~Kernel.machine(K), 
          s,
          b,
          Seal.chain(~K, s, Ballot.store(b), Ballot.node(b))
        )
      )

# the ballots that the chains of some ballots lead to keep the heads
def Each.heads(
  ~K: Kernel(),
  +f: Nat,
  bs: List<&2, Ledgers.Ballot>,
  +p: Tries.Trie<Ledgers.Ballot>,
  +s: Node<Machine.Q(Kernel.machine(K))>
) -> {
  State.heads(~Kernel.machine(K), 
    s
  )
    == State.heads(~Kernel.machine(K), Sealed.each(~K, f, bs, p, s)): Tries.Trie<Head>
}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, rest}:
      s1 = Sealed.follow(~K, 
        f,
        s,
        p,
        Ballot.store(b),
        Ballot.node(b),
        Pending.next(~K, s, p, Ballot.store(b), Ballot.node(b))
      )
      Equal.trans(
        Tries.Trie<Head>,
        State.heads(~Kernel.machine(K), s),
        State.heads(~Kernel.machine(K), s1),
        State.heads(~Kernel.machine(K), Sealed.each(~K, f, rest, p, s1)),
        Follow.heads(~K, 
          f,
          s,
          p,
          Ballot.store(b),
          Ballot.node(b),
          Pending.next(~K, s, p, Ballot.store(b), Ballot.node(b))
        ),
        Each.heads(~K, f, rest, p, s1)
      )

# a vote keeps the heads
def Cast.put.heads(
  ~K: Kernel(),
  n: String,
  w: Ledgers.Where,
  th: Maybe<&2, Hashes.Hash>,
  qs: List<&2, Ledgers.Id>,
  from: List<&2, String>,
  m: Maybe<&2, Run<Machine.Q(Kernel.machine(K))>>,
  s: Node<Machine.Q(Kernel.machine(K))>
) -> {
  State.heads(~Kernel.machine(K), 
    s
  )
    == State.heads(~Kernel.machine(K), Cast.put(~K, n, w, th, qs, from, m, s)): Tries.Trie<Head>
}:
  match m:
    case None{}:
      {==}
    case Some{Run{s2, +t2}}:
      Cast.vote.heads(~K, 
        s,
        State.put(~Kernel.machine(K), s2, [Tip.words(t2)]),
        w,
        n,
        Ledgers.Act.Vote{Ledgers.Vote{th, qs, Some{Tip.hash(t2)}}, from}
      )

# a pass keeps the heads
def Pass.to.heads(
  ~K: Kernel(),
  +n: String,
  +s: Node<Machine.Q(Kernel.machine(K))>,
  w: Ledgers.Where,
  os: List<&2, String>
) -> {
  State.heads(~Kernel.machine(K), s) == State.heads(~Kernel.machine(K), Pass.to(~K, n, s, w, os)): Tries.Trie<Head>
}:
  match w:
    case Ledgers.Where{+c, +h, +r}:
      Heads.when(~Kernel.machine(K), 
        List.all.if(
          u => Maybe.is_none(
            &2,
            Maybe<&2, Ledgers.Last>,
            Ledgers.State.passed(~Machine.Q(Kernel.machine(K)), State.ledger(~Kernel.machine(K), s), Ledgers.Where{c, h, r}, n)
          ),
          List.contains(~String, ~String.eq, os, n)
        ),
        s,
        Cast.seal(~K, 
          s,
          Ledgers.Where{c, h, r},
          n,
          Ledgers.Act.Pass{Last.below(~Kernel.machine(K), n, s, c, h, r)},
          Seal.chain(~K, s, Where.store(Ledgers.Where{c, h, r}), n)
        ),
        s,
        Cast.seal.heads(~K, 
          s,
          Ledgers.Where{c, h, r},
          n,
          Ledgers.Act.Pass{Last.below(~Kernel.machine(K), n, s, c, h, r)},
          Seal.chain(~K, s, Where.store(Ledgers.Where{c, h, r}), n)
        ),
        {==}
      )

# a node that joins a round keeps the heads
def Round.join.heads(
  ~K: Kernel(),
  +n: String,
  +s: Node<Machine.Q(Kernel.machine(K))>,
  +c: Ledgers.Chain,
  +h: U32,
  os: List<&2, String>
) -> {
  State.heads(~Kernel.machine(K), 
    s
  )
    == State.heads(~Kernel.machine(K), Round.join(~K, n, s, c, h, os)): Tries.Trie<Head>
}:
  +top = Round.seen(~Kernel.machine(K), s, c, h)
  k = top
  Heads.when(~Kernel.machine(K), 
    Nat.is_lt(Round.mine(~Kernel.machine(K), n, s, c, h, k), top),
    s,
    Pass.to(~K, n, s, Ledgers.Where{c, h, top}, os),
    s,
    Pass.to.heads(~K, n, s, Ledgers.Where{c, h, top}, os),
    {==}
  )

# a ballot in the node's round keeps the heads
def Cast.round.heads(
  ~K: Kernel(),
  +n: String,
  +s: Node<Machine.Q(Kernel.machine(K))>,
  +c: Ledgers.Chain,
  +next: U32,
  +th: Maybe<&2, Hashes.Hash>,
  +t: Tip
) -> {
  State.heads(~Kernel.machine(K), 
    s
  )
    == State.heads(~Kernel.machine(K), Cast.round(~K, n, s, c, next, th, t)): Tries.Trie<Head>
}:
  +os = Tip.owners(t)
  +r = Round.mine(~Kernel.machine(K), n, s, c, next, Round.seen(~Kernel.machine(K), s, c, next))
  +w = {Ledgers.Where{c, next, r}: Ledgers.Where}
  +p = Plan.of(~K, 
    n,
    s,
    c,
    w,
    t,
    th,
    os,
    Owners.turn(os, U32.add(next, U32.from_nat(r)))
  )
  Heads.when(~Kernel.machine(K), 
    Cast.may(~Kernel.machine(K), n, s, w, t, Plan.asks(~Kernel.machine(K), p)),
    s,
    Cast.put(~K, n, w, th, Plan.asks(~Kernel.machine(K), p), Plan.from(~Kernel.machine(K), p), Plan.run(~Kernel.machine(K), p), s),
    s,
    Cast.put.heads(~K, n, w, th, Plan.asks(~Kernel.machine(K), p), Plan.from(~Kernel.machine(K), p), Plan.run(~Kernel.machine(K), p), s),
    {==}
  )

# Node.cast keeps the heads, at the head h whose tip is m
def Cast.at.heads(
  ~K: Kernel(),
  +n: String,
  +s: Node<Machine.Q(Kernel.machine(K))>,
  +c: Ledgers.Chain,
  h: Head,
  m: Maybe<&2, Tip>
) -> {
  State.heads(~Kernel.machine(K), 
    s
  )
    == State.heads(~Kernel.machine(K), Cast.at(~K, n, s, c, h, m)): Tries.Trie<Head>
}:
  match h m:
    case Head{r, b, +next, th} Some{+t}:
      s1 = Round.join(~K, n, s, c, next, Tip.owners(t))
      Equal.trans(
        Tries.Trie<Head>,
        State.heads(~Kernel.machine(K), s),
        State.heads(~Kernel.machine(K), s1),
        State.heads(~Kernel.machine(K), Cast.round(~K, n, s1, c, next, th, t)),
        Round.join.heads(~K, n, s, c, next, Tip.owners(t)),
        Cast.round.heads(~K, n, s1, c, next, th, t)
      )
    case Head{r, b, next, th} None{}:
      {==}

# Node.pass keeps the heads, at the head h whose tip is m
def Pass.at.heads(
  ~K: Kernel(),
  +n: String,
  +s: Node<Machine.Q(Kernel.machine(K))>,
  +c: Ledgers.Chain,
  h: Head,
  m: Maybe<&2, Tip>
) -> {
  State.heads(~Kernel.machine(K), 
    s
  )
    == State.heads(~Kernel.machine(K), Pass.at(~K, n, s, c, h, m)): Tries.Trie<Head>
}:
  match h m:
    case Head{r, b, +next, th} Some{t}:
      Pass.to.heads(~K, 
        n,
        s,
        Ledgers.Where{c, next, 1n+Round.mine(~Kernel.machine(K), n, s, c, next, Round.seen(~Kernel.machine(K), s, c, next))},
        Tip.owners(t)
      )
    case Head{r, b, next, th} None{}:
      {==}

# Node.pass keeps the heads, once the head m is known
def Pass.head.heads(
  ~K: Kernel(),
  n: String,
  +s: Node<Machine.Q(Kernel.machine(K))>,
  c: Ledgers.Chain,
  m: Maybe<&2, Head>
) -> {
  State.heads(~Kernel.machine(K), s) == State.heads(~Kernel.machine(K), Pass.head(~K, n, s, c, m)): Tries.Trie<Head>
}:
  match m:
    case None{}:
      {==}
    case Some{+h}:
      Pass.at.heads(~K, n, s, c, h, Head.tip(~Kernel.machine(K), s, h))

# Node.cast keeps the heads, once the head m is known
def Cast.head.heads(
  ~K: Kernel(),
  n: String,
  +s: Node<Machine.Q(Kernel.machine(K))>,
  c: Ledgers.Chain,
  m: Maybe<&2, Head>
) -> {
  State.heads(~Kernel.machine(K), s) == State.heads(~Kernel.machine(K), Cast.head(~K, n, s, c, m)): Tries.Trie<Head>
}:
  match m:
    case None{}:
      {==}
    case Some{+h}:
      Cast.at.heads(~K, n, s, c, h, Head.tip(~Kernel.machine(K), s, h))

# the words of a tip read as the tip
def Tip.round(
  t: Tip
) -> {Tip.read(Tip.words(t)) == Some{t}: Maybe<&2, Tip>}:
  match t:
    case Tip{+c, +l, +n, +os}:
      %Equal.sym(
        Maybe<&2, Codes.Read<Tip>>,
        Codes.Code.four.read(
          ~Maybe<&2, Hashes.Hash>,
          ~Maybe<&2, Hashes.Hash>,
          ~U32,
          ~List<&2, String>,
          ~Tip,
          ~Codes.Codec.dec(Maybe<&2, Hashes.Hash>, Codes.Code.maybe.codec(~Hashes.Hash, ~Hashes.Hash.codec())),
          ~Codes.Codec.dec(Maybe<&2, Hashes.Hash>, Codes.Code.maybe.codec(~Hashes.Hash, ~Hashes.Hash.codec())),
          ~Codes.Codec.dec(U32, Codes.Code.token.codec()),
          ~Codes.Codec.dec(List<&2, String>, Codes.Code.list.codec(~String, ~Codes.Code.text.codec())),
          x => y => z => w => Tip{x, y, z, w},
          Codes.Codec.enc(Maybe<&2, Hashes.Hash>, Codes.Code.maybe.codec(~Hashes.Hash, ~Hashes.Hash.codec()))(c)(
            Codes.Codec.enc(Maybe<&2, Hashes.Hash>, Codes.Code.maybe.codec(~Hashes.Hash, ~Hashes.Hash.codec()))(l)(
              Codes.Codec.enc(U32, Codes.Code.token.codec())(n)(Codes.Codec.enc(List<&2, String>, Codes.Code.list.codec(~String, ~Codes.Code.text.codec()))(os)([]))
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
  ~M: Machine(),
  -s2: Node<Machine.Q(M)>,
  -ds: List<&2, List<&2, U32>>,
  -s3: Node<Machine.Q(M)>,
  b: Bool,
  eb: {
    Stores.Store.holds(~Node<Machine.Q(M)>, ~Store.fetch(~M), State.keep(~M, s2, ds), ds) == b: Bool
  }
) -> {
  Shared.Maybe.when(
    Node<Machine.Q(M)>,
    b,
    u => Some{State.keep(~M, s2, ds)}
  )
    == Some{s3}: Maybe<&2, Node<Machine.Q(M)>>
} -> {Stores.Store.holds(~Node<Machine.Q(M)>, ~Store.fetch(~M), s3, ds) == True{}: Bool}:
  match b:
    case False{}:
      e => Empty.absurd(
        {Stores.Store.holds(~Node<Machine.Q(M)>, ~Store.fetch(~M), s3, ds) == True{}: Bool},
        Shared.Maybe.none_ne_some(Node<Machine.Q(M)>, s3, e)
      )
    case True{}:
      e =>
        %Shared.Maybe.some_inj(
          Node<Machine.Q(M)>,
          State.keep(~M, s2, ds),
          s3,
          e
        ): {Stores.Store.holds(~Node<Machine.Q(M)>, ~Store.fetch(~M), _, ds) == True{}: Bool}
        eb

# a node that a put gives holds the data
def Put.holds(
  ~M: Machine(),
  s2: Node<Machine.Q(M)>,
  +ds: List<&2, List<&2, U32>>,
  -s3: Node<Machine.Q(M)>
) -> {
  State.put(~M, s2, ds) == Some{s3}: Maybe<&2, Node<Machine.Q(M)>>
} -> {Stores.Store.holds(~Node<Machine.Q(M)>, ~Store.fetch(~M), s3, ds) == True{}: Bool}:
  Put.holds.if(~M, 
    s2,
    ds,
    s3,
    Stores.Store.holds(~Node<Machine.Q(M)>, ~Store.fetch(~M), State.keep(~M, s2, ds), ds),
    {==}
  )

# a node that a put gives grew
def Put.grew(
  ~M: Machine(),
  s2: Node<Machine.Q(M)>,
  ds: List<&2, List<&2, U32>>,
  -s3: Node<Machine.Q(M)>,
  e: {State.put(~M, s2, ds) == Some{s3}: Maybe<&2, Node<Machine.Q(M)>>}
) -> {Node.grows(~M, s2, s3) == True{}: Bool}:
  %e: {State.after(~M, s2, _) == True{}: Bool}
  Put.grows(~M, s2, ds)

# a node that the put of a tip gives holds the tip under its hash
def Tip.put.at(
  ~M: Machine(),
  s2: Node<Machine.Q(M)>,
  +t2: Tip,
  +s3: Node<Machine.Q(M)>
) -> {
  State.put(~M, s2, [Tip.words(t2)]) == Some{s3}: Maybe<&2, Node<Machine.Q(M)>>
} -> {Tip.at(~M, s3, Tip.hash(t2)) == Some{t2}: Maybe<&2, Tip>}:
  e =>
    %Equal.sym(
      Maybe<&2, List<&2, U32>>,
      Store.fetch(~M, s3, Hashes.Sha.hash(Tip.words(t2))),
      Some{Tip.words(t2)},
      Shared.Maybe.is_eq_sound(
        ~List<&2, U32>,
        ~Shared.List.is_eq(~U32, ~U32.is_eq),
        x => y => Shared.List.is_eq_sound(~U32, ~U32.is_eq, ~Shared.U32.laws(), x, y),
        Store.fetch(~M, s3, Hashes.Sha.hash(Tip.words(t2))),
        Some{Tip.words(t2)}
      )(
        Shared.List.all.if_hit(
          Stores.Store.has(~Node<Machine.Q(M)>, ~Store.fetch(~M), s3, Tip.words(t2)),
          u => Stores.Store.holds(~Node<Machine.Q(M)>, ~Store.fetch(~M), s3, [])
        )(Put.holds(~M, s2, [Tip.words(t2)], s3)(e))
      )
    ): {
      Maybe.bind(
        &2,
        List<&2, U32>,
        Tip,
        _,
        ws => Tip.read(ws)
      )
        == Some{t2}: Maybe<&2, Tip>
    }
    Tip.round(t2)

# what a line holds is what the log of its tip holds
def Line.read.at(
  ~M: Machine(),
  -s: Node<Machine.Q(M)>,
  -c: Ledgers.Chain,
  -k: List<&2, U32>,
  -v: List<&2, U32>,
  -h: Head,
  -t: Tip,
  em: {Node.head_of(~M, s, c) == Some{h}: Maybe<&2, Head>},
  et: {Head.tip(~M, s, h) == Some{t}: Maybe<&2, Tip>}
) -> {
  Line.get(~M, s, c, k) == Some{v}: Maybe<&2, List<&2, U32>>
} -> {Node.get(~M, s, Tip.log(t), k) == Some{v}: Maybe<&2, List<&2, U32>>}:
  e =>
    %et: {
      Maybe.bind(
        &2,
        Tip,
        List<&2, U32>,
        _,
        t1 => Node.get(~M, s, Tip.log(t1), k)
      )
        == Some{v}: Maybe<&2, List<&2, U32>>
    }
    Line.get.of(~M, s, c, k, v, Some{h}, em)(e)

# a head at the tip t2 holds what the log of t2 holds, in a node that grew
# from one that holds the tip
def Moved.cover(
  ~M: Machine(),
  +s3: Node<Machine.Q(M)>,
  +b: Node<Machine.Q(M)>,
  +t2: Tip,
  k: List<&2, U32>,
  v: List<&2, U32>,
  -r: Ledgers.Id,
  -br: Maybe<&2, String>,
  -nx: U32,
  +g: {Node.grows(~M, s3, b) == True{}: Bool},
  e3: {Tip.at(~M, s3, Tip.hash(t2)) == Some{t2}: Maybe<&2, Tip>},
  v3: {Node.get(~M, s3, Tip.log(t2), k) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> {
  Head.get(~M, 
    b,
    Head{r, br, nx, Some{Tip.hash(t2)}},
    k
  )
    == Some{v}: Maybe<&2, List<&2, U32>>
}:
  %Equal.sym(
    Maybe<&2, Tip>,
    Tip.at(~M, b, Tip.hash(t2)),
    Some{t2},
    Tip.at.grows(~M, s3, b, Tip.hash(t2), t2, g)(e3)
  ): {
    Maybe.bind(
      &2,
      Tip,
      List<&2, U32>,
      _,
      t1 => Node.get(~M, b, Tip.log(t1), k)
    )
      == Some{v}: Maybe<&2, List<&2, U32>>
  }
  Get.grows(~M, s3, b, Tip.log(t2), k, v, g)(v3)

# a head moved to the tip t2 keeps the logs, when the log of t2 holds what
# the log of the tip t of the head before holds
def Moved.kept(
  ~M: Machine(),
  +s: Node<Machine.Q(M)>,
  +s3: Node<Machine.Q(M)>,
  +c: Ledgers.Chain,
  r: Ledgers.Id,
  br: Maybe<&2, String>,
  nx: U32,
  +t2: Tip,
  qs: List<&2, Ledgers.Id>,
  h: Head,
  t: Tip,
  g3: {Node.grows(~M, s, s3) == True{}: Bool},
  em: {Node.head_of(~M, s, c) == Some{h}: Maybe<&2, Head>},
  et: {Head.tip(~M, s, h) == Some{t}: Maybe<&2, Tip>},
  e3: {Tip.at(~M, s3, Tip.hash(t2)) == Some{t2}: Maybe<&2, Tip>},
  kk: @k: List<
    &2,
    U32> -> @v: List<
    &2,
    U32> -> {
    Node.get(~M, s, Tip.log(t), k) == Some{v}: Maybe<&2, List<&2, U32>>
  } -> {Node.get(~M, s3, Tip.log(t2), k) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> Node.Keeps(~M, 
  s,
  State.moved(~M, 
    State.led(~M, s, State.ledger(~M, s3)),
    c,
    Head{r, br, nx, Some{Tip.hash(t2)}},
    qs
  )
):
  +x = State.led(~M, s, State.ledger(~M, s3))
  +ws = Wait.left(
    Wait.of(~M, x, c),
    Tries.Trie.put_keys(~Ledgers.Id, ~Ledgers.Id.key, qs, Tries.Trie.new(Unit))
  )
  +b0 = Wait.set(~M, x, c, ws)
  +hd = {Head{r, br, nx, Some{Tip.hash(t2)}}: Head}
  Head.put.kept(~M, 
    s,
    b0,
    c,
    hd,
    Grows.to(~M, s, x, b0, Led.wait(~M, x, c, ws), Grows.back(~M, s, s3, g3)),
    Equal.trans(
      Tries.Trie<Head>,
      State.heads(~M, s),
      State.heads(~M, x),
      State.heads(~M, b0),
      Heads.led(~M, s, State.ledger(~M, s3)),
      Heads.wait(~M, x, c, ws)
    ),
    +k => +v => e => Moved.cover(~M, 
      s3,
      State.head(~M, b0, c, hd),
      t2,
      k,
      v,
      r,
      br,
      nx,
      Grows.to(~M, 
        s3,
        s3,
        State.head(~M, b0, c, hd),
        Equal.trans(
          Ledgers.State(Machine.Q(M)),
          State.ledger(~M, State.head(~M, b0, c, hd)),
          State.ledger(~M, b0),
          State.ledger(~M, s3),
          Led.head(~M, b0, c, hd),
          Equal.trans(
            Ledgers.State(Machine.Q(M)),
            State.ledger(~M, b0),
            State.ledger(~M, x),
            State.ledger(~M, s3),
            Led.wait(~M, x, c, ws),
            Led.led(~M, s, State.ledger(~M, s3))
          )
        ),
        Grows.refl(~M, s3)
      ),
      e3,
      kk(k)(v)(Line.read.at(~M, s, c, k, v, h, t, em, et)(e))
    )
  )

# Advance.moved keeps the logs, once the node m that the put gives is known
def Advance.moved.kept(
  ~M: Machine(),
  +s: Node<Machine.Q(M)>,
  +s2: Node<Machine.Q(M)>,
  m: Maybe<&2, Node<Machine.Q(M)>>,
  c: Ledgers.Chain,
  r: Ledgers.Id,
  br: Maybe<&2, String>,
  nx: U32,
  +t2: Tip,
  qs: List<&2, Ledgers.Id>,
  h: Head,
  t: Tip,
  g2: {Node.grows(~M, s, s2) == True{}: Bool},
  em: {Node.head_of(~M, s, c) == Some{h}: Maybe<&2, Head>},
  et: {Head.tip(~M, s, h) == Some{t}: Maybe<&2, Tip>},
  kk: @k: List<
    &2,
    U32> -> @v: List<
    &2,
    U32> -> {
    Node.get(~M, s, Tip.log(t), k) == Some{v}: Maybe<&2, List<&2, U32>>
  } -> {Node.get(~M, s2, Tip.log(t2), k) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> {
  State.put(~M, s2, [Tip.words(t2)]) == m: Maybe<&2, Node<Machine.Q(M)>>
} -> Node.Keeps(~M, 
  s,
  Advance.moved(~M, s, m, c, Head{r, br, nx, Some{Tip.hash(t2)}}, qs)
):
  match m:
    case None{}:
      e2 => Kept.refl(~M, s)
    case Some{+s3}:
      +e2 => Moved.kept(~M, 
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
        Grows.trans(~M, s, s2, s3)(g2)(Put.grew(~M, s2, [Tip.words(t2)], s3, e2)),
        em,
        et,
        Tip.put.at(~M, s2, t2, s3)(e2),
        +k => +v => e => Get.grows(~M, 
          s2,
          s3,
          Tip.log(t2),
          k,
          v,
          Put.grew(~M, s2, [Tip.words(t2)], s3, e2)
        )(kk(k)(v)(e))
      )

# a checked step keeps the logs
def Advance.ran.kept(
  ~M: Machine(),
  s: Node<Machine.Q(M)>,
  c: Ledgers.Chain,
  r: Ledgers.Id,
  br: Maybe<&2, String>,
  next: U32,
  after: Maybe<&2, Hashes.Hash>,
  qs: List<&2, Ledgers.Id>,
  m: Maybe<&2, Run<Machine.Q(M)>>,
  h: Head,
  t: Tip,
  em: {Node.head_of(~M, s, c) == Some{h}: Maybe<&2, Head>},
  et: {Head.tip(~M, s, h) == Some{t}: Maybe<&2, Tip>}
) -> {
  Run.after(~M, s, m) == True{}: Bool
} -> (
  @k: List<
    &2,
    U32> -> @v: List<
    &2,
    U32> -> {
    Node.get(~M, s, Tip.log(t), k) == Some{v}: Maybe<&2, List<&2, U32>>
  } -> Run.Keeps(~M, k, v, m)
) -> Node.Keeps(~M, s, Advance.ran(~M, s, c, r, br, next, after, qs, m)):
  match m:
    case None{}:
      ga => rk => Kept.refl(~M, s)
    case Some{Run{+s2, +t2}}:
      ga => rk => Kept.when(~M, 
        Root.same(after, Some{Tip.hash(t2)}),
        s,
        Advance.moved(~M, 
          s,
          State.put(~M, s2, [Tip.words(t2)]),
          c,
          Head{r, br, U32.inc(next), Some{Tip.hash(t2)}},
          qs
        ),
        s,
        Advance.moved.kept(~M, 
          s,
          s2,
          State.put(~M, s2, [Tip.words(t2)]),
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
        Kept.refl(~M, s)
      )

# a line with no head holds nothing
def Cover.none(
  ~M: Machine(),
  -a: Node<Machine.Q(M)>,
  -c: Ledgers.Chain,
  -b: Node<Machine.Q(M)>,
  -hd: Head,
  -k: List<&2, U32>,
  -v: List<&2, U32>,
  em: {Node.head_of(~M, a, c) == None{}: Maybe<&2, Head>}
) -> {
  Line.get(~M, a, c, k) == Some{v}: Maybe<&2, List<&2, U32>>
} -> {Head.get(~M, b, hd, k) == Some{v}: Maybe<&2, List<&2, U32>>}:
  e => Empty.absurd(
    {Head.get(~M, b, hd, k) == Some{v}: Maybe<&2, List<&2, U32>>},
    Shared.Maybe.none_ne_some(List<&2, U32>, v, Line.get.of(~M, a, c, k, v, None{}, em)(e))
  )

# a line whose head has no tip holds nothing
def Cover.wait(
  ~M: Machine(),
  -a: Node<Machine.Q(M)>,
  -c: Ledgers.Chain,
  -b: Node<Machine.Q(M)>,
  -hd: Head,
  -k: List<&2, U32>,
  -v: List<&2, U32>,
  -r: Ledgers.Id,
  -br: Maybe<&2, String>,
  -n: U32,
  em: {Node.head_of(~M, a, c) == Some{Head{r, br, n, None{}}}: Maybe<&2, Head>}
) -> {
  Line.get(~M, a, c, k) == Some{v}: Maybe<&2, List<&2, U32>>
} -> {Head.get(~M, b, hd, k) == Some{v}: Maybe<&2, List<&2, U32>>}:
  e => Empty.absurd(
    {Head.get(~M, b, hd, k) == Some{v}: Maybe<&2, List<&2, U32>>},
    Shared.Maybe.none_ne_some(
      List<&2, U32>,
      v,
      Line.get.of(~M, a, c, k, v, Some{Head{r, br, n, None{}}}, em)(e)
    )
  )

# a line that opens keeps the logs, once its head m is known
def Open.at.kept(
  ~M: Machine(),
  +s: Node<Machine.Q(M)>,
  c: Ledgers.Chain,
  m: Maybe<&2, Head>
) -> {
  Node.head_of(~M, s, c) == m: Maybe<&2, Head>
} -> Node.Keeps(~M, s, Open.at(~M, s, c, m)):
  match m:
    case Some{Head{+r, Some{+b}, n, None{}}}:
      +em =>
        +hd = {
          Head{
            r,
            Some{b},
            0,
            Branch.first(~M, s, b, Node.tip(~M, s, Ledgers.Chain{r, None{}}))
          }: Head
        }
        Head.put.kept(~M, 
          s,
          s,
          c,
          hd,
          Grows.refl(~M, s),
          {==},
          k => v => Cover.wait(~M, 
            s,
            c,
            State.head(~M, s, c, hd),
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
      em => Kept.refl(~M, s)
    case Some{Head{r, None{}, n, t}}:
      em => Kept.refl(~M, s)
    case None{}:
      em => Kept.refl(~M, s)

# a first head keeps the logs, once the head m of its line is known
def First.at.kept(
  ~M: Machine(),
  +s: Node<Machine.Q(M)>,
  c: Ledgers.Chain,
  h: Head,
  m: Maybe<&2, Head>
) -> {
  Node.head_of(~M, s, c) == m: Maybe<&2, Head>
} -> Node.Keeps(~M, s, First.at(~M, s, c, h, m)):
  match m:
    case Some{Head{r, b, n, Some{t}}}:
      em => Kept.refl(~M, s)
    case Some{Head{r, b, n, None{}}}:
      +em => Head.put.kept(~M, 
        s,
        s,
        c,
        h,
        Grows.refl(~M, s),
        {==},
        k => v => Cover.wait(~M, s, c, State.head(~M, s, c, h), h, k, v, r, b, n, em)
      )
    case None{}:
      +em => Head.put.kept(~M, 
        s,
        s,
        c,
        h,
        Grows.refl(~M, s),
        {==},
        k => v => Cover.none(~M, s, c, State.head(~M, s, c, h), h, k, v, em)
      )

# a first head on a node that grew from a, which grew from s, keeps the logs
def Start.head.kept(
  ~M: Machine(),
  +s: Node<Machine.Q(M)>,
  a: Node<Machine.Q(M)>,
  m: Maybe<&2, Node<Machine.Q(M)>>,
  +c: Ledgers.Chain,
  h: Head,
  g: {Node.grows(~M, s, a) == True{}: Bool}
) -> {
  State.after(~M, a, m) == True{}: Bool
} -> Node.Keeps(~M, s, Start.head(~M, s, m, c, h)):
  match m:
    case None{}:
      e => Kept.refl(~M, s)
    case Some{+s3}:
      e =>
        +x = State.led(~M, s, State.ledger(~M, s3))
        Kept.trans(~M, 
          s,
          x,
          State.first(~M, x, c, h),
          Kept.same(~M, 
            s,
            x,
            Grows.back(~M, s, s3, Grows.trans(~M, s, a, s3)(g)(e)),
            Heads.led(~M, s, State.ledger(~M, s3))
          ),
          First.at.kept(~M, x, c, h, Node.head_of(~M, x, c))({==})
        )

# Start.kept once the content m of the store is known
def Start.with.kept(
  ~M: Machine(),
  +s: Node<Machine.Q(M)>,
  +i: Ledgers.Id,
  +os: List<&2, String>,
  m: Maybe<&2, Work<Machine.Q(M)>>
) -> {
  Work.after(~M, s, m) == True{}: Bool
} -> Node.Keeps(~M, s, Start.with(~M, s, i, os, m)):
  match m:
    case None{}:
      e => Kept.refl(~M, s)
    case Some{Work{+s2, +c}}:
      e =>
        +t = {Tip{c, None{}, 0, os}: Tip}
        Start.head.kept(~M, 
          s,
          s2,
          State.put(~M, s2, [Tip.words(t)]),
          Ledgers.Chain{i, None{}},
          Head{i, None{}, 0, Some{Tip.hash(t)}},
          e
        )(Put.grows(~M, s2, [Tip.words(t)]))

# a line that a node follows keeps the logs, once its head m is known
def Follow.new.kept(
  ~M: Machine(),
  +s: Node<Machine.Q(M)>,
  +r: Ledgers.Id,
  +l: Maybe<&2, String>,
  m: Maybe<&2, Head>
) -> {
  Node.head_of(~M, s, Line.chain(r, l)) == m: Maybe<&2, Head>
} -> Node.Keeps(~M, s, Follow.new(~M, s, r, l, m)):
  match m:
    case Some{h}:
      em => Kept.refl(~M, s)
    case None{}:
      +em => Head.put.kept(~M, 
        s,
        s,
        Line.chain(r, l),
        Head{r, l, 0, None{}},
        Grows.refl(~M, s),
        {==},
        k => v => Cover.none(~M, 
          s,
          Line.chain(r, l),
          State.head(~M, s, Line.chain(r, l), Head{r, l, 0, None{}}),
          Head{r, l, 0, None{}},
          k,
          v,
          em
        )
      )

# a request that waits keeps the heads
def Heads.waits(
  ~M: Machine(),
  s: Node<Machine.Q(M)>,
  c: Ledgers.Chain,
  i: Ledgers.Id
) -> {
  State.heads(~M, s) == State.heads(~M, State.wait(~M, s, c, i)): Tries.Trie<Head>
}:
  match s:
    case Node{l, hs, ws, ks}:
      {==}

# a work that reads a key, after a step that keeps the read
def Reads.bind(
  ~M: Machine(),
  -k: List<&2, U32>,
  -v: List<&2, U32>,
  m: Maybe<&2, Work<Machine.Q(M)>>,
  -f: Work<Machine.Q(M)> -> Maybe<&2, Work<Machine.Q(M)>>
) -> Work.Reads(~M, 
  k,
  v,
  m
) -> (
  @w: Work<Machine.Q(M)> -> Work.Reads(~M, k, v, Some{w}) -> Work.Reads(~M, k, v, f(w))
) -> Work.Reads(~M, k, v, Maybe.bind(&2, Work<Machine.Q(M)>, Work<Machine.Q(M)>, m, f)):
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
  ~M: Machine(),
  -A: Data,
  -k: List<&2, U32>,
  -v: List<&2, U32>,
  +ma: Maybe<&2, A>,
  -f: A -> Maybe<&2, Work<Machine.Q(M)>>
) -> (
  @a: A -> Work.Reads(~M, k, v, f(a))
) -> Work.Reads(~M, k, v, Maybe.bind(&2, A, Work<Machine.Q(M)>, ma, f)):
  match ma:
    case None{}:
      hf => Unit{}
    case Some{a}:
      hf => hf(a)

# a set of another key keeps what a work reads
def Set.kept.work(
  ~M: Machine(),
  +w: Work<Machine.Q(M)>,
  k: List<&2, U32>,
  x: List<&2, U32>,
  k2: List<&2, U32>,
  v: List<&2, U32>,
  hne: {Shared.List.is_eq(~U32, ~U32.is_eq, k, k2) == False{}: Bool}
) -> Work.Reads(~M, k2, v, Some{w}) -> Work.Reads(~M, k2, v, Work.set(~M, w, k, x)):
  match w:
    case Work{s, h}:
      hget => Set.kept(~M, s, h, k, x, k2, v, hne, hget)

# Keep.reads once it is known whether the node holds the new data (b)
def Keep.reads.if(
  ~M: Machine(),
  +s: Node<Machine.Q(M)>,
  h: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>,
  k: List<&2, U32>,
  v: List<&2, U32>,
  +b: Bool,
  hget: {Node.get(~M, s, h, k) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> Work.Reads(~M, 
  k,
  v,
  Work.on(~M, Shared.Maybe.when(Node<Machine.Q(M)>, b, u => Some{State.keep(~M, s, ns)}), h)
):
  match b:
    case False{}:
      Unit{}
    case True{}:
      Get.grows(~M, s, State.keep(~M, s, ns), h, k, v, Grows.keep(~M, s, ns))(hget)

# new data keeps what a work reads
def Keep.reads(
  ~M: Machine(),
  +w: Work<Machine.Q(M)>,
  +ns: List<&2, List<&2, U32>>,
  k: List<&2, U32>,
  v: List<&2, U32>
) -> Work.Reads(~M, k, v, Some{w}) -> Work.Reads(~M, k, v, Work.keep(~M, w, ns)):
  match w:
    case Work{s, h}:
      hget => Keep.reads.if(~M, s, h, ns, k, v, Stores.Store.holds(~Node<Machine.Q(M)>, ~Store.fetch(~M), State.keep(~M, s, ns), ns), hget)

# Set.read once it is known whether the node holds the new nodes (b)
def Set.read.if(
  ~M: Machine(),
  +s: Node<Machine.Q(M)>,
  +h: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  +x: List<&2, U32>,
  +hh: Hashes.Hash,
  +ws: List<&2, List<&2, U32>>,
  +b: Bool,
  eb: {
    Stores.Store.holds(~Node<Machine.Q(M)>, ~Store.fetch(~M), State.keep(~M, s, ws), ws) == b: Bool
  },
  em: {Node.set(~M, s, h, k, x) == Some{Trees.Put{hh, ws}}: Maybe<&2, Trees.Put>}
) -> Work.Reads(~M, 
  k,
  x,
  Work.on(~M, Shared.Maybe.when(Node<Machine.Q(M)>, b, u => Some{State.keep(~M, s, ws)}), Some{hh})
):
  match b:
    case False{}:
      Unit{}
    case True{}:
      Equal.trans(
        Maybe<&2, List<&2, U32>>,
        Node.get(~M, State.keep(~M, s, ws), Some{hh}, k),
        Trees.Tree.get.plain(~Node<Machine.Q(M)>, ~Store.fetch(~M), State.keep(~M, s, ws), Some{hh}, k),
        Some{x},
        Trees.Tree.get_plain(~Node<Machine.Q(M)>, ~Store.fetch(~M), State.keep(~M, s, ws), Some{hh}, k),
        Trees.Tree.get_set(
          ~Node<Machine.Q(M)>,
          ~Store.fetch(~M),
          s,
          State.keep(~M, s, ws),
          h,
          k,
          x,
          Trees.Put{hh, ws}
        )(
          Equal.trans(
            Maybe<&2, Trees.Put>,
            Trees.Tree.set.plain(~Node<Machine.Q(M)>, ~Store.fetch(~M), s, h, k, x),
            Node.set(~M, s, h, k, x),
            Some{Trees.Put{hh, ws}},
            Equal.sym(
              Maybe<&2, Trees.Put>,
              Node.set(~M, s, h, k, x),
              Trees.Tree.set.plain(~Node<Machine.Q(M)>, ~Store.fetch(~M), s, h, k, x),
              Trees.Tree.set_plain(~Node<Machine.Q(M)>, ~Store.fetch(~M), s, h, k, x)
            ),
            em
          )
        )(eb)
      )

# Set.read once the new subtree m is known
def Set.read.of(
  ~M: Machine(),
  +s: Node<Machine.Q(M)>,
  h: Maybe<&2, Hashes.Hash>,
  k: List<&2, U32>,
  x: List<&2, U32>,
  +m: Maybe<&2, Trees.Put>,
  em: {Node.set(~M, s, h, k, x) == m: Maybe<&2, Trees.Put>}
) -> Work.Reads(~M, k, x, Work.of(~M, s, m)):
  match m:
    case None{}:
      Unit{}
    case Some{Trees.Put{hh, ws}}:
      Set.read.if(~M, 
        s,
        h,
        k,
        x,
        hh,
        ws,
        Stores.Store.holds(~Node<Machine.Q(M)>, ~Store.fetch(~M), State.keep(~M, s, ws), ws),
        {==},
        em
      )

# a key that a work sets, it reads
def Set.read(
  ~M: Machine(),
  +w: Work<Machine.Q(M)>,
  +k: List<&2, U32>,
  +x: List<&2, U32>
) -> Work.Reads(~M, k, x, Work.set(~M, w, k, x)):
  match w:
    case Work{s, h}:
      Set.read.of(~M, s, h, k, x, Node.set(~M, s, h, k, x), {==})

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
  ~M: Machine(),
  r: Run<Machine.Q(M)>,
  +k: List<&2, U32>,
  +x: List<&2, U32>,
  m: Maybe<&2, List<&2, U32>>
) -> Run.Keeps(~M, k, x, Run.add.at(~M, r, k, x, m)):
  match r m:
    case Run{+s, +t} None{}:
      Run.logged.keeps(~M, 
        k,
        x,
        t,
        Work.set(~M, Work{s, Tip.log(t)}, k, x)
      )(Set.read(~M, Work{s, Tip.log(t)}, k, x))
    case y Some{old}:
      Unit{}

# a new key of the log of a run reads back
def Add.reads(
  ~M: Machine(),
  +r: Run<Machine.Q(M)>,
  +k: List<&2, U32>,
  x: List<&2, U32>
) -> Run.Keeps(~M, k, x, Run.add(~M, r, k, x)):
  Add.reads.at(~M, 
    r,
    k,
    x,
    Node.get(~M, Run.state(~M, r), Tip.log(Run.tip(~M, r)), k)
  )

# a log that reads the outcome key of i as v holds an outcome of i
def Outs.of(
  ~M: Machine(),
  i: Ledgers.Id,
  v: List<&2, U32>,
  +m: Maybe<&2, Run<Machine.Q(M)>>
) -> Run.Keeps(~M, Log.out(i), v, m) -> Run.Outs(~M, m, i):
  match m:
    case None{}:
      h => Unit{}
    case Some{Run{s, t}}:
      h =>
        %Equal.sym(
          Maybe<&2, List<&2, U32>>,
          Node.get(~M, s, Tip.log(t), Log.out(i)),
          Some{v},
          h
        ): {Maybe.is_some(&2, List<&2, U32>, _) == True{}: Bool}
        {==}

# each run that f gives has an outcome of i: so has the run after a step
def Outs.all(
  ~M: Machine(),
  +m: Maybe<&2, Run<Machine.Q(M)>>,
  -f: Run<Machine.Q(M)> -> Maybe<&2, Run<Machine.Q(M)>>,
  -i: Ledgers.Id,
  hf: @r: Run<Machine.Q(M)> -> Run.Outs(~M, f(r), i)
) -> Run.Outs(~M, Maybe.bind(&2, Run<Machine.Q(M)>, Run<Machine.Q(M)>, m, f), i):
  match m:
    case None{}:
      Unit{}
    case Some{r}:
      hf(r)

# one of two runs, each with an outcome of i
def Outs.when(
  ~M: Machine(),
  +b: Bool,
  -mx: Maybe<&2, Run<Machine.Q(M)>>,
  -my: Maybe<&2, Run<Machine.Q(M)>>,
  -i: Ledgers.Id,
  hx: Run.Outs(~M, mx, i),
  hy: Run.Outs(~M, my, i)
) -> Run.Outs(~M, Shared.Bool.when(Maybe<&2, Run<Machine.Q(M)>>, b, u => mx, u => my), i):
  match b:
    case True{}:
      hx
    case False{}:
      hy

# a request that is refused as stale has an outcome
def Stale.outs(~M: Machine(), +r: Run<Machine.Q(M)>, +i: Ledgers.Id) -> Run.Outs(~M, Step.stale(~M, r, i), i):
  Outs.of(~M, 
    i,
    Out.words(Out.Stale{}),
    Run.add(~M, r, Log.out(i), Out.words(Out.Stale{}))
  )(Add.reads(~M, r, Log.out(i), Out.words(Out.Stale{})))

# a request that is taken has an outcome
def Taken.outs(
  ~M: Machine(),
  +r: Run<Machine.Q(M)>,
  +i: Ledgers.Id,
  +own: Maybe<&2, List<&2, String>>
) -> Run.Outs(~M, Step.taken(~M, r, i, own), i):
  +n = Tip.count(Run.tip(~M, r))
  Outs.of(~M, 
    i,
    Out.words(Out.Taken{n}),
    Step.taken(~M, r, i, own)
  )(
    Keeps.bind(~M, 
      Log.out(i),
      Out.words(Out.Taken{n}),
      Run.add(~M, r, Log.out(i), Out.words(Out.Taken{n})),
      +r1 => Maybe.bind(
        &2,
        Run<Machine.Q(M)>,
        Run<Machine.Q(M)>,
        Run.add(~M, 
          r1,
          Log.version(n),
          Version.words(Version{i, Tip.content(Run.tip(~M, r1))})
        ),
        r2 => Some{Run.next(~M, r2, own)}
      )
    )(
      Add.reads(~M, r, Log.out(i), Out.words(Out.Taken{n}))
    )(
      +r1 => h1 => Keeps.bind(~M, 
        Log.out(i),
        Out.words(Out.Taken{n}),
        Run.add(~M, 
          r1,
          Log.version(n),
          Version.words(Version{i, Tip.content(Run.tip(~M, r1))})
        ),
        r2 => Some{Run.next(~M, r2, own)}
      )(
        Add.kept(~M, 
          r1,
          Log.version(n),
          Version.words(Version{i, Tip.content(Run.tip(~M, r1))}),
          Log.out(i),
          Out.words(Out.Taken{n})
        )(h1)
      )(
        r2 => h2 => Next.kept(~M, 
          r2,
          own,
          Log.out(i),
          Out.words(Out.Taken{n})
        )(h2)
      )
    )
  )

# a judged request has an outcome
def Judged.outs(
  ~M: Machine(),
  r: Run<Machine.Q(M)>,
  i: Ledgers.Id,
  own: Maybe<&2, List<&2, String>>,
  +m: Maybe<&2, Verdict<Machine.Q(M)>>
) -> Run.Outs(~M, Step.judged(~M, r, i, own, m), i):
  match m:
    case None{}:
      Unit{}
    case Some{Verdict.Stale{}}:
      Stale.outs(~M, r, i)
    case Some{Verdict.Taken{Work{s2, h}}}:
      Taken.outs(~M, Run.over(~M, r, s2, h), i, own)

# a mark on a version has an outcome
def Marked.outs(
  ~M: Machine(),
  r: Run<Machine.Q(M)>,
  i: Ledgers.Id,
  m: String,
  +v: Maybe<&2, Version>
) -> Run.Outs(~M, Step.marked(~M, r, i, m, v), i):
  match v:
    case None{}:
      Unit{}
    case Some{x}:
      Outs.all(~M, 
        Run.add(~M, r, Log.mark(m), Ledgers.Id.code(Version.id(x), [])),
        r2 => Step.taken(~M, r2, i, None{}),
        i,
        r2 => Taken.outs(~M, r2, i, None{})
      )

# a request for a mark has an outcome
def Mark.outs(
  ~M: Machine(),
  +r: Run<Machine.Q(M)>,
  +i: Ledgers.Id,
  +m: String
) -> Run.Outs(~M, Step.mark(~M, r, i, m), i):
  +s = Run.state(~M, r)
  +t = Run.tip(~M, r)
  +n = Tip.count(t)
  Outs.when(~M, 
    List.all.if(
      u => Maybe.is_none(&2, Ledgers.Id, Line.mark(~M, s, t, m)),
      Bool.not(U32.is_eq(n, 0))
    ),
    Step.marked(~M, r, i, m, Line.version(~M, s, t, U32.sub(n, 1))),
    Step.stale(~M, r, i),
    i,
    Marked.outs(~M, r, i, m, Line.version(~M, s, t, U32.sub(n, 1))),
    Stale.outs(~M, r, i)
  )

# the first tip of a new branch has an outcome
def Branch.made.outs(
  ~M: Machine(),
  +r: Run<Machine.Q(M)>,
  i: Ledgers.Id,
  b: String,
  +m: Maybe<&2, Made<Machine.Q(M)>>
) -> Run.Outs(~M, Branch.made(~M, r, i, b, m), i):
  match m:
    case None{}:
      Unit{}
    case Some{Made{t, s2}}:
      Outs.all(~M, 
        Run.add(~M, 
          Run.over(~M, r, s2, Tip.content(Run.tip(~M, r))),
          Log.start(b),
          Hashes.Hash.code(Tip.hash(t), [])
        ),
        r2 => Step.taken(~M, r2, i, None{}),
        i,
        r2 => Taken.outs(~M, r2, i, None{})
      )

# a run whose log reads the outcome key of i has an outcome of i
def Outs.self(
  ~M: Machine(),
  +r: Run<Machine.Q(M)>,
  i: Ledgers.Id,
  ws: List<&2, U32>
) -> {
  Node.get(~M, 
    Run.state(~M, r),
    Tip.log(Run.tip(~M, r)),
    Log.out(i)
  )
    == Some{ws}: Maybe<&2, List<&2, U32>>
} -> Run.Outs(~M, Some{r}, i):
  match r:
    case Run{s, t}:
      eg =>
        %Equal.sym(
          Maybe<&2, List<&2, U32>>,
          Node.get(~M, s, Tip.log(t), Log.out(i)),
          Some{ws},
          eg
        ): {Maybe.is_some(&2, List<&2, U32>, _) == True{}: Bool}
        {==}

# no run gives no run
def All.none(
  ~K: Kernel(),
  c: Ledgers.Chain,
  +qs: List<&2, Ledgers.Id>
) -> {Step.all(~K, c, qs, None{}) == None{}: Maybe<&2, Run<Machine.Q(Kernel.machine(K))>>}:
  match qs:
    case Nil{}:
      {==}
    case Con{i, rest}:
      All.none(~K, c, rest)

# a run reads what its log holds
def Keeps.self(
  ~M: Machine(),
  +r: Run<Machine.Q(M)>,
  k: List<&2, U32>,
  v: List<&2, U32>
) -> {
  Node.get(~M, 
    Run.state(~M, r),
    Tip.log(Run.tip(~M, r)),
    k
  )
    == Some{v}: Maybe<&2, List<&2, U32>>
} -> Run.Keeps(~M, k, v, Some{r}):
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
  ~K: Kernel(),
  s: Node<Machine.Q(Kernel.machine(K))>,
  c: Ledgers.Chain,
  t: Tip,
  th: Maybe<&2, Hashes.Hash>,
  v: Ledgers.Vote,
  from: List<&2, String>,
  b: Bool
) -> {
  Maybe.is_some(
    &2,
    Run<Machine.Q(Kernel.machine(K))>,
    Plan.run(~Kernel.machine(K), 
      Shared.Bool.when(
        Plan<Machine.Q(Kernel.machine(K))>,
        b,
        u => Plan.copy(~K, s, c, t, th, Some{v}, from),
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
  ~M: Machine(),
  +a: Node<Machine.Q(M)>,
  +u: Node<Machine.Q(M)>,
  +t: Tip,
  +w: Ledgers.Where,
  v: Ledgers.Vote,
  +g: {Node.grows(~M, a, u) == True{}: Bool}
) -> {
  Ledgers.State.decide(
    ~Machine.Q(M),
    State.ledger(~M, a),
    w,
    Tip.owners(t)
  )
    == Some{v}: Maybe<&2, Ledgers.Vote>
} -> {
  Ledgers.State.decide(
    ~Machine.Q(M),
    State.ledger(~M, u),
    w,
    Tip.owners(t)
  )
    == Some{v}: Maybe<&2, Ledgers.Vote>
}:
  e =>
    Ledgers.State.decide_grows(
      ~Machine.Q(M),
      ~Machine.same(M),
      ~Machine.laws(M),
      State.ledger(~M, a),
      State.ledger(~M, u),
      w,
      Tip.owners(t),
      v
    )(g)(e)

# Scan.elim at a round, once what it decides is known (m)
def Scan.elim.at(
  ~M: Machine(),
  -R: Type,
  -s: Node<Machine.Q(M)>,
  -c: Ledgers.Chain,
  -n: U32,
  -os: List<&2, String>,
  -p: Nat,
  -v: Ledgers.Vote,
  r: Nat,
  m: Maybe<&2, Ledgers.Vote>,
  rec: {
    Height.decide(~M, s, c, n, os, p) == Some{v}: Maybe<&2, Ledgers.Vote>
  } -> (
    @q: Nat -> {
      Ledgers.State.decide(
        ~Machine.Q(M),
        State.ledger(~M, s),
        Ledgers.Where{c, n, q},
        os
      )
        == Some{v}: Maybe<&2, Ledgers.Vote>
    } -> R
  ) -> R
) -> {
  Ledgers.State.decide(
    ~Machine.Q(M),
    State.ledger(~M, s),
    Ledgers.Where{c, n, r},
    os
  )
    == m: Maybe<&2, Ledgers.Vote>
} -> {
  Vote.first(
    m,
    u => Height.decide(~M, s, c, n, os, p)
  )
    == Some{v}: Maybe<&2, Ledgers.Vote>
} -> (
  @q: Nat -> {
    Ledgers.State.decide(
      ~Machine.Q(M),
      State.ledger(~M, s),
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
          Ledgers.State.decide(~Machine.Q(M), State.ledger(~M, s), Ledgers.Where{c, n, r}, os),
          Some{x},
          Some{v},
          em,
          e
        )
      )

# a step that a height decides in a round up to k is decided in some round
def Scan.elim(
  ~M: Machine(),
  -R: Type,
  +s: Node<Machine.Q(M)>,
  +c: Ledgers.Chain,
  +n: U32,
  +os: List<&2, String>,
  k: Nat,
  -v: Ledgers.Vote
) -> {
  Height.decide(~M, s, c, n, os, k) == Some{v}: Maybe<&2, Ledgers.Vote>
} -> (
  @q: Nat -> {
    Ledgers.State.decide(
      ~Machine.Q(M),
      State.ledger(~M, s),
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
      Scan.elim.at(~M, 
        R,
        s,
        c,
        n,
        os,
        p,
        v,
        1n+p,
        Ledgers.State.decide(~Machine.Q(M), State.ledger(~M, s), Ledgers.Where{c, n, 1n+p}, os),
        Scan.elim(~M, R, s, c, n, os, p, v)
      )({==})

# a head is at its own height
def Level.refl(h: Head) -> {Heads.level(Some{h}, Some{h}) == True{}: Bool}:
  match h:
    case Head{r, b, n, t}:
      Shared.Eq.refl(~U32, ~U32.is_eq, Shared.U32.laws(), n)

# the step that the owners in the tip of the head h decided next on the line
# c, in a round up to k, if they did
def Advance.found(
  ~M: Machine(),
  +s: Node<Machine.Q(M)>,
  c: Ledgers.Chain,
  +h: Head,
  k: Nat
) -> Maybe<&2, Ledgers.Vote>:
  Maybe.bind(
    &2,
    Tip,
    Ledgers.Vote,
    Head.tip(~M, s, h),
    t => Height.decide(~M, s, c, Head.next(h), Tip.owners(t), k)
  )

# the step that the owners in the tip of the head h decided next on the line
# c, in a round of which the node holds a ballot, if they did
def Advance.vote(~M: Machine(), +s: Node<Machine.Q(M)>, +c: Ledgers.Chain, +h: Head) -> Maybe<&2, Ledgers.Vote>:
  Advance.found(~M, s, c, h, Round.seen(~M, s, c, Head.next(h)))

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
def Moves(~M: Machine(), s2: Node<Machine.Q(M)>, c: Ledgers.Chain, h: Head, x: Head) -> Type:
  {
    Heads.level(Some{h}, Node.head_of(~M, s2, c)) == False{}: Bool
  } -> {Node.head_of(~M, s2, c) == Some{x}: Maybe<&2, Head>}

# a node whose head is h did not move it
def Moves.stay(
  ~M: Machine(),
  -s: Node<Machine.Q(M)>,
  -c: Ledgers.Chain,
  h: Head,
  -x: Head,
  em: {Node.head_of(~M, s, c) == Some{h}: Maybe<&2, Head>}
) -> Moves(~M, s, c, h, x):
  hl => Empty.absurd(
    {Node.head_of(~M, s, c) == Some{x}: Maybe<&2, Head>},
    Shared.Bool.false_ne_true(
      Equal.trans(
        Bool,
        False{},
        Heads.level(Some{h}, Some{h}),
        True{},
        Equal.trans(
          Bool,
          False{},
          Heads.level(Some{h}, Node.head_of(~M, s, c)),
          Heads.level(Some{h}, Some{h}),
          Equal.sym(Bool, Heads.level(Some{h}, Node.head_of(~M, s, c)), False{}, hl),
          Equal.cong(
            Maybe<&2, Head>,
            Bool,
            m => Heads.level(Some{h}, m),
            Node.head_of(~M, s, c),
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
  ~M: Machine(),
  b: Bool,
  -sx: Node<Machine.Q(M)>,
  -sy: Node<Machine.Q(M)>,
  -c: Ledgers.Chain,
  -h: Head,
  -x: Head,
  hx: Moves(~M, sx, c, h, x),
  hy: Moves(~M, sy, c, h, x)
) -> Moves(~M, Shared.Bool.when(Node<Machine.Q(M)>, b, u => sx, u => sy), c, h, x):
  match b:
    case True{}:
      hx
    case False{}:
      hy

# the head of a line, after it is set
def Head.at_set(
  ~M: Machine(),
  b0: Node<Machine.Q(M)>,
  +c: Ledgers.Chain,
  hd: Head
) -> {Node.head_of(~M, State.head(~M, b0, c, hd), c) == Some{hd}: Maybe<&2, Head>}:
  Equal.trans(
    Maybe<&2, Head>,
    Node.head_of(~M, State.head(~M, b0, c, hd), c),
    Bool.pick(
      Maybe<&2, Head>,
      Tries.Trie.same_key(Ledgers.Chain.key(c), Ledgers.Chain.key(c)),
      Some{hd},
      Node.head_of(~M, b0, c)
    ),
    Some{hd},
    Head.of_set(~M, b0, c, hd, c),
    Pick.of(
      Maybe<&2, Head>,
      True{},
      Tries.Trie.same_key(Ledgers.Chain.key(c), Ledgers.Chain.key(c)),
      Some{hd},
      Node.head_of(~M, b0, c),
      Shared.List.is_eq_refl(~Bool, ~Shared.Bool.is_eq, ~Shared.Bool.laws(), Ledgers.Chain.key(c))
    )
  )

# Advance.moved moves the head to hd, or not at all
def Advance.moved.moves(
  ~M: Machine(),
  +s: Node<Machine.Q(M)>,
  m: Maybe<&2, Node<Machine.Q(M)>>,
  +c: Ledgers.Chain,
  hd: Head,
  qs: List<&2, Ledgers.Id>,
  h: Head,
  -x: Head,
  em: {Node.head_of(~M, s, c) == Some{h}: Maybe<&2, Head>},
  ex: {hd == x: Head}
) -> Moves(~M, Advance.moved(~M, s, m, c, hd, qs), c, h, x):
  match m:
    case None{}:
      Moves.stay(~M, s, c, h, x, em)
    case Some{+s3}:
      hl =>
        %ex: {
          Node.head_of(~M, 
            State.moved(~M, State.led(~M, s, State.ledger(~M, s3)), c, hd, qs),
            c
          )
            == Some{_}: Maybe<&2, Head>
        }
        Head.at_set(~M, 
          Wait.set(~M, 
            State.led(~M, s, State.ledger(~M, s3)),
            c,
            Wait.left(
              Wait.of(~M, State.led(~M, s, State.ledger(~M, s3)), c),
              Tries.Trie.put_keys(~Ledgers.Id, ~Ledgers.Id.key, qs, Tries.Trie.new(Unit))
            )
          ),
          c,
          hd
        )

# Advance.ran.moves once whether the run gives the tip that the step names is
# known (bq)
def Advance.ran.moves.if(
  ~M: Machine(),
  s: Node<Machine.Q(M)>,
  s2: Node<Machine.Q(M)>,
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
  em: {Node.head_of(~M, s, c) == Some{h}: Maybe<&2, Head>},
  ex: {
    Root.same(after, Some{Tip.hash(t2)}) == True{}: Bool
  } -> {Head{r, br, U32.inc(next), Some{Tip.hash(t2)}} == x: Head}
) -> Moves(~M, 
  Shared.Bool.when(
    Node<Machine.Q(M)>,
    bq,
    u => Advance.moved(~M, 
      s,
      State.put(~M, s2, [Tip.words(t2)]),
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
      Advance.moved.moves(~M, 
        s,
        State.put(~M, s2, [Tip.words(t2)]),
        c,
        Head{r, br, U32.inc(next), Some{Tip.hash(t2)}},
        qs,
        h,
        x,
        em,
        ex(ebq)
      )
    case False{}:
      Moves.stay(~M, s, c, h, x, em)

# a checked step moves the head to the tip that the step names, or not at all
def Advance.ran.moves(
  ~M: Machine(),
  s: Node<Machine.Q(M)>,
  c: Ledgers.Chain,
  r: Ledgers.Id,
  br: Maybe<&2, String>,
  next: U32,
  +after: Maybe<&2, Hashes.Hash>,
  qs: List<&2, Ledgers.Id>,
  m: Maybe<&2, Run<Machine.Q(M)>>,
  h: Head,
  -x: Head,
  em: {Node.head_of(~M, s, c) == Some{h}: Maybe<&2, Head>},
  ex: @t2: Tip -> {
    Root.same(after, Some{Tip.hash(t2)}) == True{}: Bool
  } -> {Head{r, br, U32.inc(next), Some{Tip.hash(t2)}} == x: Head}
) -> Moves(~M, Advance.ran(~M, s, c, r, br, next, after, qs, m), c, h, x):
  match m:
    case None{}:
      Moves.stay(~M, s, c, h, x, em)
    case Some{Run{s2, +t2}}:
      Advance.ran.moves.if(~M, 
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
  ~K: Kernel(),
  +s: Node<Machine.Q(Kernel.machine(K))>,
  +c: Ledgers.Chain,
  h: Head,
  t: Tip,
  m: Maybe<&2, Ledgers.Vote>
) -> {
  Node.head_of(~Kernel.machine(K), s, c) == Some{h}: Maybe<&2, Head>
} -> Moves(~Kernel.machine(K), Advance.step(~K, s, c, h, t, m), c, h, Head.step(h, m)):
  match h m:
    case Head{+r, +br, +next, +th} Some{Ledgers.Vote{before, +qs, +after}}:
      +em => Moves.when(~Kernel.machine(K), 
        Root.same(before, th),
        Advance.ran(~Kernel.machine(K), s, c, r, br, next, after, qs, Step.run(~K, s, c, t, qs)),
        s,
        c,
        Head{r, br, next, th},
        Head.step(Head{r, br, next, th}, Some{Ledgers.Vote{before, qs, after}}),
        Advance.ran.moves(~Kernel.machine(K), 
          s,
          c,
          r,
          br,
          next,
          after,
          qs,
          Step.run(~K, s, c, t, qs),
          Head{r, br, next, th},
          Head.step(Head{r, br, next, th}, Some{Ledgers.Vote{before, qs, after}}),
          em,
          t2 => er =>
            %Equal.sym(Maybe<&2, Hashes.Hash>, after, Some{Tip.hash(t2)}, Shared.Maybe.is_eq_sound(~Hashes.Hash, ~Hashes.Hash.is_eq, x => y => Hashes.Hash.is_eq_sound(x, y), after, Some{Tip.hash(t2)})(er)): {Head{r, br, U32.inc(next), Some{Tip.hash(t2)}} == Head.step(Head{r, br, next, th}, Some{Ledgers.Vote{before, qs, _}}): Head}
            {==}),
        Moves.stay(~Kernel.machine(K), 
          s,
          c,
          Head{r, br, next, th},
          Head.step(Head{r, br, next, th}, Some{Ledgers.Vote{before, qs, after}}),
          em
        )
      )
    case Head{+r, +br, +next, +th} None{}:
      em => Moves.stay(~Kernel.machine(K), s, c, Head{r, br, next, th}, Head{r, br, next, th}, em)

# Node.advance moves the head by the step decided at the head h, whose tip is
# m, or not at all
def Advance.at.moves(
  ~K: Kernel(),
  +s: Node<Machine.Q(Kernel.machine(K))>,
  +c: Ledgers.Chain,
  +h: Head,
  m: Maybe<&2, Tip>
) -> {
  Node.head_of(~Kernel.machine(K), s, c) == Some{h}: Maybe<&2, Head>
} -> {
  Head.tip(~Kernel.machine(K), s, h) == m: Maybe<&2, Tip>
} -> Moves(~Kernel.machine(K), Advance.at(~K, s, c, h, m), c, h, Head.step(h, Advance.vote(~Kernel.machine(K), s, c, h))):
  match m:
    case None{}:
      em => et => Moves.stay(~Kernel.machine(K), s, c, h, Head.step(h, Advance.vote(~Kernel.machine(K), s, c, h)), em)
    case Some{+t}:
      em => et =>
        %Equal.sym(
          Maybe<&2, Ledgers.Vote>,
          Advance.vote(~Kernel.machine(K), s, c, h),
          Height.decide(~Kernel.machine(K), 
            s,
            c,
            Head.next(h),
            Tip.owners(t),
            Round.seen(~Kernel.machine(K), s, c, Head.next(h))
          ),
          Equal.cong(
            Maybe<&2, Tip>,
            Maybe<&2, Ledgers.Vote>,
            mt => Maybe.bind(
              &2,
              Tip,
              Ledgers.Vote,
              mt,
              t1 => Height.decide(~Kernel.machine(K), 
                s,
                c,
                Head.next(h),
                Tip.owners(t1),
                Round.seen(~Kernel.machine(K), s, c, Head.next(h))
              )
            ),
            Head.tip(~Kernel.machine(K), s, h),
            Some{t},
            et
          )
        ): Moves(~Kernel.machine(K), 
          Advance.step(~K, 
            s,
            c,
            h,
            t,
            Height.decide(~Kernel.machine(K), 
              s,
              c,
              Head.next(h),
              Tip.owners(t),
              Round.seen(~Kernel.machine(K), s, c, Head.next(h))
            )
          ),
          c,
          h,
          Head.step(h, _)
        )
        Advance.step.moves(~K, 
          s,
          c,
          h,
          t,
          Height.decide(~Kernel.machine(K), 
            s,
            c,
            Head.next(h),
            Tip.owners(t),
            Round.seen(~Kernel.machine(K), s, c, Head.next(h))
          )
        )(em)

# a head moves only to the tip that the owners in its tip decided next
def Advance.decided(
  ~K: Kernel(),
  +s: Node<Machine.Q(Kernel.machine(K))>,
  c: Ledgers.Chain,
  +h: Head
) -> {
  Node.head_of(~Kernel.machine(K), s, c) == Some{h}: Maybe<&2, Head>
} -> {
  Heads.level(Some{h}, Node.head_of(~Kernel.machine(K), Node.advance(~K, s, c), c)) == False{}: Bool
} -> {
  Node.head_of(~Kernel.machine(K), 
    Node.advance(~K, s, c),
    c
  )
    == Some{Head.step(h, Advance.vote(~Kernel.machine(K), s, c, h))}: Maybe<&2, Head>
}:
  +em =>
    %Equal.sym(
      Maybe<&2, Head>,
      Node.head_of(~Kernel.machine(K), s, c),
      Some{h},
      em
    ): Moves(~Kernel.machine(K), Advance.head(~K, s, c, _), c, h, Head.step(h, Advance.vote(~Kernel.machine(K), s, c, h)))
    Advance.at.moves(~K, s, c, h, Head.tip(~Kernel.machine(K), s, h))(em)({==})

# Found.elim once the tip m of the head is known
def Found.elim.at(
  ~M: Machine(),
  -R: Type,
  +s: Node<Machine.Q(M)>,
  c: Ledgers.Chain,
  h: Head,
  k: Nat,
  -v: Ledgers.Vote,
  m: Maybe<&2, Tip>
) -> {
  Head.tip(~M, s, h) == m: Maybe<&2, Tip>
} -> {
  Maybe.bind(
    &2,
    Tip,
    Ledgers.Vote,
    m,
    t => Height.decide(~M, s, c, Head.next(h), Tip.owners(t), k)
  )
    == Some{v}: Maybe<&2, Ledgers.Vote>
} -> (
  @t: Tip -> @q: Nat -> {
    Head.tip(~M, s, h) == Some{t}: Maybe<&2, Tip>
  } -> {
    Ledgers.State.decide(
      ~Machine.Q(M),
      State.ledger(~M, s),
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
      em => e => f => Scan.elim(~M, 
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
  ~M: Machine(),
  -R: Type,
  +s: Node<Machine.Q(M)>,
  c: Ledgers.Chain,
  +h: Head,
  k: Nat,
  -v: Ledgers.Vote
) -> {
  Advance.found(~M, s, c, h, k) == Some{v}: Maybe<&2, Ledgers.Vote>
} -> (
  @t: Tip -> @q: Nat -> {
    Head.tip(~M, s, h) == Some{t}: Maybe<&2, Tip>
  } -> {
    Ledgers.State.decide(
      ~Machine.Q(M),
      State.ledger(~M, s),
      Ledgers.Where{c, Head.next(h), q},
      Tip.owners(t)
    )
      == Some{v}: Maybe<&2, Ledgers.Vote>
  } -> R
) -> R:
  Found.elim.at(~M, R, s, c, h, k, v, Head.tip(~M, s, h))({==})

# the verdict m takes
def Verdict.took(~M: Machine(), m: Maybe<&2, Verdict<Machine.Q(M)>>) -> Bool:
  match m:
    case Some{Verdict.Taken{Work{s2, h}}}:
      True{}
    case x:
      False{}

# the tree of the verdict m
def Took.root(~M: Machine(), m: Maybe<&2, Verdict<Machine.Q(M)>>) -> Maybe<&2, Hashes.Hash>:
  match m:
    case Some{Verdict.Taken{Work{s2, h}}}:
      h
    case x:
      None{}

# the node of the verdict m, or d when it takes nothing
def Took.node(~M: Machine(), m: Maybe<&2, Verdict<Machine.Q(M)>>, d: Node<Machine.Q(M)>) -> Node<Machine.Q(M)>:
  match m:
    case Some{Verdict.Taken{Work{s2, h}}}:
      s2
    case x:
      d

# Set.reads once the node m2 that the put of the new subtree gives is known
def Set.reads.put(
  ~M: Machine(),
  +s: Node<Machine.Q(M)>,
  +h: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  +x: List<&2, U32>,
  +hh: Hashes.Hash,
  ws: List<&2, List<&2, U32>>,
  m2: Maybe<&2, Node<Machine.Q(M)>>,
  -h2: Maybe<&2, Hashes.Hash>,
  s3: Node<Machine.Q(M)>,
  hp: @y: Node<Machine.Q(M)> -> {
    m2 == Some{y}: Maybe<&2, Node<Machine.Q(M)>>
  } -> {Stores.Store.holds(~Node<Machine.Q(M)>, ~Store.fetch(~M), y, ws) == True{}: Bool}
) -> {
  Node.set(~M, s, h, k, x) == Some{Trees.Put{hh, ws}}: Maybe<&2, Trees.Put>
} -> {
  Work.take(~M, 
    Work.on(~M, m2, Some{hh})
  )
    == Some{Verdict.Taken{Work{s3, h2}}}: Maybe<&2, Verdict<Machine.Q(M)>>
} -> {Node.get(~M, s3, h2, k) == Some{x}: Maybe<&2, List<&2, U32>>}:
  match m2:
    case None{}:
      es => e => Empty.absurd(
        {Node.get(~M, s3, h2, k) == Some{x}: Maybe<&2, List<&2, U32>>},
        Shared.Maybe.none_ne_some(Verdict<Machine.Q(M)>, Verdict.Taken{Work{s3, h2}}, e)
      )
    case Some{+sk}:
      es => +e =>
        %Equal.cong(
          Maybe<&2, Verdict<Machine.Q(M)>>,
          Node<Machine.Q(M)>,
          v => Took.node(~M, v, s3),
          Some{Verdict.Taken{Work{sk, Some{hh}}}},
          Some{Verdict.Taken{Work{s3, h2}}},
          e
        ): {Node.get(~M, _, h2, k) == Some{x}: Maybe<&2, List<&2, U32>>}
        %Equal.cong(
          Maybe<&2, Verdict<Machine.Q(M)>>,
          Maybe<&2, Hashes.Hash>,
          v => Took.root(~M, v),
          Some{Verdict.Taken{Work{sk, Some{hh}}}},
          Some{Verdict.Taken{Work{s3, h2}}},
          e
        ): {Node.get(~M, sk, _, k) == Some{x}: Maybe<&2, List<&2, U32>>}
        Equal.trans(
          Maybe<&2, List<&2, U32>>,
          Node.get(~M, sk, Some{hh}, k),
          Trees.Tree.get.plain(~Node<Machine.Q(M)>, ~Store.fetch(~M), sk, Some{hh}, k),
          Some{x},
          Trees.Tree.get_plain(~Node<Machine.Q(M)>, ~Store.fetch(~M), sk, Some{hh}, k),
          Trees.Tree.get_set(
            ~Node<Machine.Q(M)>,
            ~Store.fetch(~M),
            s,
            sk,
            h,
            k,
            x,
            Trees.Put{hh, ws}
          )(
            Equal.trans(
              Maybe<&2, Trees.Put>,
              Trees.Tree.set.plain(~Node<Machine.Q(M)>, ~Store.fetch(~M), s, h, k, x),
              Node.set(~M, s, h, k, x),
              Some{Trees.Put{hh, ws}},
              Equal.sym(
                Maybe<&2, Trees.Put>,
                Node.set(~M, s, h, k, x),
                Trees.Tree.set.plain(~Node<Machine.Q(M)>, ~Store.fetch(~M), s, h, k, x),
                Trees.Tree.set_plain(~Node<Machine.Q(M)>, ~Store.fetch(~M), s, h, k, x)
              ),
              es
            )
          )(hp(sk)({==}))
        )

# a key set in a tree, when the verdict takes the new tree, reads back in a
# node that holds the new nodes
def Set.reads(
  ~M: Machine(),
  +s: Node<Machine.Q(M)>,
  h: Maybe<&2, Hashes.Hash>,
  k: List<&2, U32>,
  x: List<&2, U32>,
  m: Maybe<&2, Trees.Put>,
  -h2: Maybe<&2, Hashes.Hash>,
  s3: Node<Machine.Q(M)>
) -> {
  Node.set(~M, s, h, k, x) == m: Maybe<&2, Trees.Put>
} -> {
  Work.take(~M, 
    Work.of(~M, s, m)
  )
    == Some{Verdict.Taken{Work{s3, h2}}}: Maybe<&2, Verdict<Machine.Q(M)>>
} -> {Node.get(~M, s3, h2, k) == Some{x}: Maybe<&2, List<&2, U32>>}:
  match m:
    case None{}:
      es => e => Empty.absurd(
        {Node.get(~M, s3, h2, k) == Some{x}: Maybe<&2, List<&2, U32>>},
        Shared.Maybe.none_ne_some(Verdict<Machine.Q(M)>, Verdict.Taken{Work{s3, h2}}, e)
      )
    case Some{Trees.Put{hh, +ws}}:
      Set.reads.put(~M, 
        s,
        h,
        k,
        x,
        hh,
        ws,
        State.put(~M, s, ws),
        h2,
        s3,
        y => ey => Put.holds(~M, s, ws, y)(ey)
      )

# a verdict that takes, after a read, is the verdict of what comes next
def With.took(
  ~M: Machine(),
  -A: Data,
  ma: Maybe<&2, A>,
  -k: A -> Maybe<&2, Verdict<Machine.Q(M)>>,
  -kk: Maybe<&2, Verdict<Machine.Q(M)>>,
  -h2: Maybe<&2, Hashes.Hash>,
  -s3: Node<Machine.Q(M)>
) -> (
  @a: A -> {
    k(a) == Some{Verdict.Taken{Work{s3, h2}}}: Maybe<&2, Verdict<Machine.Q(M)>>
  } -> {kk == Some{Verdict.Taken{Work{s3, h2}}}: Maybe<&2, Verdict<Machine.Q(M)>>}
) -> {
  Maybe.bind(
    &2,
    A,
    Verdict<Machine.Q(M)>,
    ma,
    k
  )
    == Some{Verdict.Taken{Work{s3, h2}}}: Maybe<&2, Verdict<Machine.Q(M)>>
} -> {kk == Some{Verdict.Taken{Work{s3, h2}}}: Maybe<&2, Verdict<Machine.Q(M)>>}:
  match ma:
    case None{}:
      hk => e => Empty.absurd(
        {kk == Some{Verdict.Taken{Work{s3, h2}}}: Maybe<&2, Verdict<Machine.Q(M)>>},
        Shared.Maybe.none_ne_some(Verdict<Machine.Q(M)>, Verdict.Taken{Work{s3, h2}}, e)
      )
    case Some{a}:
      hk => e => hk(a)(e)

# Seal.accept_fits once whether the ballot fits is known (f)
def Accept.fits.if(
  ~M: Machine(),
  f: Bool,
  -x: Node<Machine.Q(M)>,
  -s2: Node<Machine.Q(M)>
) -> {
  Shared.Maybe.when(Node<Machine.Q(M)>, f, u => Some{x}) == Some{s2}: Maybe<&2, Node<Machine.Q(M)>>
} -> {f == True{}: Bool}:
  match f:
    case True{}:
      e => {==}
    case False{}:
      e => Empty.absurd({False{} == True{}: Bool}, Shared.Maybe.none_ne_some(Node<Machine.Q(M)>, s2, e))

# a place is the same as itself
def Prev.refl(m: Maybe<&2, Ledgers.Where>) -> {Prev.same(m, m) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{w}:
      Shared.List.is_eq_refl(~U32, ~U32.is_eq, ~Shared.U32.laws(), Ledgers.Where.code(w, []))

# a head that no step moves is at its own height
def Level.none(
  x: Head
) -> {Heads.level(Some{x}, Some{Head.step(x, None{})}) == True{}: Bool}:
  match x:
    case Head{r, b, n, t}:
      Shared.Eq.refl(~U32, ~U32.is_eq, Shared.U32.laws(), n)

# that the rounds of each height of the line c decide one step in s
def Line.One(~M: Machine(), s: Node<Machine.Q(M)>, c: Ledgers.Chain) -> Type:
  @x: Head -> @t: Tip -> {
    Head.tip(~M, s, x) == Some{t}: Maybe<&2, Tip>
  } -> Height.One(~M, s, c, Head.next(x), Tip.owners(t))

# that the rounds of each of k heights of the line c decide one step in s (one
# witness for each step of a history: a proof uses each once)
def Line.Ones(~M: Machine(), k: Nat, s: Node<Machine.Q(M)>, c: Ledgers.Chain) -> Type:
  match k:
    case 0n:
      Unit
    case 1n+p:
      Line.Ones(~M, p, s, c) & Line.One(~M, s, c)

# In.grows once the tip m of the head in a is known
def In.grows.at(
  ~M: Machine(),
  +a: Node<Machine.Q(M)>,
  +u: Node<Machine.Q(M)>,
  c: Ledgers.Chain,
  +x: Head,
  r: Nat,
  v: Ledgers.Vote,
  m: Maybe<&2, Tip>,
  +g: {Node.grows(~M, a, u) == True{}: Bool}
) -> {
  Head.tip(~M, a, x) == m: Maybe<&2, Tip>
} -> {
  Maybe.bind(
    &2,
    Tip,
    Ledgers.Vote,
    m,
    t => Ledgers.State.decide(
      ~Machine.Q(M),
      State.ledger(~M, a),
      Ledgers.Where{c, Head.next(x), r},
      Tip.owners(t)
    )
  )
    == Some{v}: Maybe<&2, Ledgers.Vote>
} -> {Advance.in(~M, u, c, x, r) == Some{v}: Maybe<&2, Ledgers.Vote>}:
  match m:
    case None{}:
      em => e => Empty.absurd(
        {Advance.in(~M, u, c, x, r) == Some{v}: Maybe<&2, Ledgers.Vote>},
        Shared.Maybe.none_ne_some(Ledgers.Vote, v, e)
      )
    case Some{t}:
      em => e =>
        %Equal.sym(
          Maybe<&2, Tip>,
          Head.tip(~M, u, x),
          Some{t},
          Head.tip.grows(~M, a, u, x, t, g)(em)
        ): {
          Maybe.bind(
            &2,
            Tip,
            Ledgers.Vote,
            _,
            t1 => Ledgers.State.decide(
              ~Machine.Q(M),
              State.ledger(~M, u),
              Ledgers.Where{c, Head.next(x), r},
              Tip.owners(t1)
            )
          )
            == Some{v}: Maybe<&2, Ledgers.Vote>
        }
        Decide.up(~M, a, u, t, Ledgers.Where{c, Head.next(x), r}, v, g)(e)

# a step that the owners decided at a head in a round, in a, they decided in
# a node that grew
def In.grows(
  ~M: Machine(),
  +a: Node<Machine.Q(M)>,
  u: Node<Machine.Q(M)>,
  c: Ledgers.Chain,
  +x: Head,
  r: Nat,
  v: Ledgers.Vote,
  g: {Node.grows(~M, a, u) == True{}: Bool}
) -> {
  Advance.in(~M, a, c, x, r) == Some{v}: Maybe<&2, Ledgers.Vote>
} -> {Advance.in(~M, u, c, x, r) == Some{v}: Maybe<&2, Ledgers.Vote>}:
  In.grows.at(~M, a, u, c, x, r, v, Head.tip(~M, a, x), g)({==})

# Moved.grows once the step va that a holds at the head is known
def Moved.grows.at(
  ~M: Machine(),
  a: Node<Machine.Q(M)>,
  u: Node<Machine.Q(M)>,
  c: Ledgers.Chain,
  x: Head,
  -y: Head,
  r: Nat,
  va: Maybe<&2, Ledgers.Vote>,
  g: {Node.grows(~M, a, u) == True{}: Bool}
) -> {
  Advance.in(~M, a, c, x, r) == va: Maybe<&2, Ledgers.Vote>
} -> {
  Head.moved(x, va) == Some{y}: Maybe<&2, Head>
} -> {Head.moved(x, Advance.in(~M, u, c, x, r)) == Some{y}: Maybe<&2, Head>}:
  match va:
    case None{}:
      ea => e => Empty.absurd(
        {Head.moved(x, Advance.in(~M, u, c, x, r)) == Some{y}: Maybe<&2, Head>},
        Shared.Maybe.none_ne_some(Head, y, e)
      )
    case Some{v}:
      ea => e =>
        %Equal.sym(
          Maybe<&2, Ledgers.Vote>,
          Advance.in(~M, u, c, x, r),
          Some{v},
          In.grows(~M, a, u, c, x, r, v, g)(ea)
        ): {Head.moved(x, _) == Some{y}: Maybe<&2, Head>}
        e

# a head that a decided step moves in a, it moves the same in a node that grew
def Moved.grows(
  ~M: Machine(),
  +a: Node<Machine.Q(M)>,
  u: Node<Machine.Q(M)>,
  +c: Ledgers.Chain,
  +x: Head,
  -y: Head,
  +r: Nat,
  g: {Node.grows(~M, a, u) == True{}: Bool}
) -> {
  Head.moved(x, Advance.in(~M, a, c, x, r)) == Some{y}: Maybe<&2, Head>
} -> {Head.moved(x, Advance.in(~M, u, c, x, r)) == Some{y}: Maybe<&2, Head>}:
  Moved.grows.at(~M, a, u, c, x, y, r, Advance.in(~M, a, c, x, r), g)({==})

# Step.same once what the two rounds decide is known (w1, w2)
def Step.same.at(
  ~M: Machine(),
  u: Node<Machine.Q(M)>,
  c: Ledgers.Chain,
  z: Head,
  r1: Nat,
  r2: Nat,
  t: Tip,
  -x: Head,
  -y: Head,
  w1: Maybe<&2, Ledgers.Vote>,
  w2: Maybe<&2, Ledgers.Vote>,
  one: Height.One(~M, u, c, Head.next(z), Tip.owners(t))
) -> {
  Ledgers.State.decide(
    ~Machine.Q(M),
    State.ledger(~M, u),
    Ledgers.Where{c, Head.next(z), r1},
    Tip.owners(t)
  )
    == w1: Maybe<&2, Ledgers.Vote>
} -> {
  Ledgers.State.decide(
    ~Machine.Q(M),
    State.ledger(~M, u),
    Ledgers.Where{c, Head.next(z), r2},
    Tip.owners(t)
  )
    == w2: Maybe<&2, Ledgers.Vote>
} -> {
  Head.moved(z, w1) == Some{x}: Maybe<&2, Head>
} -> {Head.moved(z, w2) == Some{y}: Maybe<&2, Head>} -> {x == y: Head}:
  match w1 w2:
    case None{} b:
      e1 => e2 => k1 => k2 => Empty.absurd(
        {x == y: Head},
        Shared.Maybe.none_ne_some(Head, x, k1)
      )
    case Some{v1} None{}:
      e1 => e2 => k1 => k2 => Empty.absurd(
        {x == y: Head},
        Shared.Maybe.none_ne_some(Head, y, k2)
      )
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
  ~M: Machine(),
  +u: Node<Machine.Q(M)>,
  +c: Ledgers.Chain,
  +z: Head,
  +r1: Nat,
  +r2: Nat,
  -x: Head,
  -y: Head,
  m: Maybe<&2, Tip>,
  one: Line.One(~M, u, c)
) -> {
  Head.tip(~M, u, z) == m: Maybe<&2, Tip>
} -> {
  Head.moved(
    z,
    Maybe.bind(
      &2,
      Tip,
      Ledgers.Vote,
      m,
      t => Ledgers.State.decide(
        ~Machine.Q(M),
        State.ledger(~M, u),
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
        ~Machine.Q(M),
        State.ledger(~M, u),
        Ledgers.Where{c, Head.next(z), r2},
        Tip.owners(t)
      )
    )
  )
    == Some{y}: Maybe<&2, Head>
} -> {x == y: Head}:
  match m:
    case None{}:
      em => k1 => k2 => Empty.absurd(
        {x == y: Head},
        Shared.Maybe.none_ne_some(Head, x, k1)
      )
    case Some{+t}:
      em => k1 => k2 =>
        Step.same.at(~M, 
          u,
          c,
          z,
          r1,
          r2,
          t,
          x,
          y,
          Ledgers.State.decide(
            ~Machine.Q(M),
            State.ledger(~M, u),
            Ledgers.Where{c, Head.next(z), r1},
            Tip.owners(t)
          ),
          Ledgers.State.decide(
            ~Machine.Q(M),
            State.ledger(~M, u),
            Ledgers.Where{c, Head.next(z), r2},
            Tip.owners(t)
          ),
          one(z)(t)(em)
        )({==})({==})(k1)(k2)

# At.same for one more step of each history, once the heads before are known
def At.same.step(
  ~M: Machine(),
  +u: Node<Machine.Q(M)>,
  c: Ledgers.Chain,
  r1: Nat,
  r2: Nat,
  -x: Head,
  -y: Head,
  m1: Maybe<&2, Head>,
  m2: Maybe<&2, Head>,
  one: Line.One(~M, u, c),
  ih: @z1: Head -> @z2: Head -> {
    m1 == Some{z1}: Maybe<&2, Head>
  } -> {m2 == Some{z2}: Maybe<&2, Head>} -> {z1 == z2: Head}
) -> {
  Maybe.bind(
    &2,
    Head,
    Head,
    m1,
    +z => Head.moved(z, Advance.in(~M, u, c, z, r1))
  )
    == Some{x}: Maybe<&2, Head>
} -> {
  Maybe.bind(
    &2,
    Head,
    Head,
    m2,
    +z => Head.moved(z, Advance.in(~M, u, c, z, r2))
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
        Step.same(~M, 
          u,
          c,
          z1,
          r1,
          r2,
          x,
          y,
          Head.tip(~M, u, z1),
          one
        )(
          {==}
        )(
          k1
        )(
          Equal.trans(
            Maybe<&2, Head>,
            Head.moved(z1, Advance.in(~M, u, c, z1, r2)),
            Head.moved(z2, Advance.in(~M, u, c, z2, r2)),
            Some{y},
            Equal.cong(
              Head,
              Maybe<&2, Head>,
              +z => Head.moved(z, Advance.in(~M, u, c, z, r2)),
              z1,
              z2,
              ih(z1)(z2)({==})({==})
            ),
            k2
          )
        )

# At.same for one more step of each history, with the witness of each step
def At.same.con(
  ~M: Machine(),
  +u: Node<Machine.Q(M)>,
  +c: Ledgers.Chain,
  +h: Head,
  r1: Nat,
  r2: Nat,
  t1: List<&2, Nat>,
  t2: List<&2, Nat>,
  -x: Head,
  -y: Head,
  ones: Line.Ones(~M, List.length(&2, Nat, t1), u, c) & Line.One(~M, u, c),
  ih: @z1: Head -> @z2: Head -> Line.Ones(~M, 
    List.length(&2, Nat, t1),
    u,
    c
  ) -> {
    Line.at(~M, t1, u, c, h) == Some{z1}: Maybe<&2, Head>
  } -> {Line.at(~M, t2, u, c, h) == Some{z2}: Maybe<&2, Head>} -> {z1 == z2: Head}
) -> {
  Line.at(~M, r1 <> t1, u, c, h) == Some{x}: Maybe<&2, Head>
} -> {Line.at(~M, r2 <> t2, u, c, h) == Some{y}: Maybe<&2, Head>} -> {x == y: Head}:
  match ones:
    case Tuple{rest, one}:
      At.same.step(~M, 
        u,
        c,
        r1,
        r2,
        x,
        y,
        Line.at(~M, t1, u, c, h),
        Line.at(~M, t2, u, c, h),
        one,
        z1 => z2 => ih(z1)(z2)(rest)
      )

# in one node, the same number of decided steps from one head give one head,
# whatever the round of each step
def At.same(
  ~M: Machine(),
  rs1: List<&2, Nat>,
  rs2: List<&2, Nat>,
  +u: Node<Machine.Q(M)>,
  +c: Ledgers.Chain,
  +h: Head,
  x: Head,
  y: Head
) -> Line.Ones(~M, List.length(&2, Nat, rs1), u, c)
  -> {List.length(&2, Nat, rs1) == List.length(&2, Nat, rs2): Nat}
  -> {Line.at(~M, rs1, u, c, h) == Some{x}: Maybe<&2, Head>}
  -> {Line.at(~M, rs2, u, c, h) == Some{y}: Maybe<&2, Head>}
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
        At.same.con(~M, 
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
          z1 => z2 => rest => At.same(~M, 
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
} -> {
  Head.moved(h, Some{v}) == Some{Head.step(h, Some{v})}: Maybe<&2, Head>
}:
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
  ~M: Machine(),
  +s: Node<Machine.Q(M)>,
  +c: Ledgers.Chain,
  +h: Head,
  m: Maybe<&2, Ledgers.Vote>
) -> {
  Advance.vote(~M, s, c, h) == m: Maybe<&2, Ledgers.Vote>
} -> {
  Heads.level(Some{h}, Some{Head.step(h, m)}) == False{}: Bool
} -> Exists(
  Nat,
  q => {Line.at(~M, [q], s, c, h) == Some{Head.step(h, m)}: Maybe<&2, Head>}
):
  match m:
    case None{}:
      em => hl => Empty.absurd(
        Exists(
          Nat,
          q => {
            Line.at(~M, 
              [q],
              s,
              c,
              h
            )
              == Some{Head.step(h, None{})}: Maybe<&2, Head>
          }
        ),
        Shared.Bool.false_ne_true(
          Equal.trans(
            Bool,
            False{},
            Heads.level(Some{h}, Some{Head.step(h, None{})}),
            True{},
            Equal.sym(
              Bool,
              Heads.level(Some{h}, Some{Head.step(h, None{})}),
              False{},
              hl
            ),
            Level.none(h)
          )
        )
      )
    case Some{v}:
      em => hl =>
        Found.elim(~M, 
          Exists(
            Nat,
            q => {
              Line.at(~M, 
                [q],
                s,
                c,
                h
              )
                == Some{Head.step(h, Some{v})}: Maybe<&2, Head>
            }
          ),
          s,
          c,
          h,
          Round.seen(~M, s, c, Head.next(h)),
          v
        )(em)(t => q => et => d => Tuple{q, (
              %Equal.sym(Maybe<&2, Tip>, Head.tip(~M, s, h), Some{t}, et): {Head.moved(h, Maybe.bind(&2, Tip, Ledgers.Vote, _, t1 => Ledgers.State.decide(~Machine.Q(M), State.ledger(~M, s), Ledgers.Where{c, Head.next(h), q}, Tip.owners(t1)))) == Some{Head.step(h, Some{v})}: Maybe<&2, Head>}
              %Equal.sym(Maybe<&2, Ledgers.Vote>, Ledgers.State.decide(~Machine.Q(M), State.ledger(~M, s), Ledgers.Where{c, Head.next(h), q}, Tip.owners(t)), Some{v}, d): {Head.moved(h, _) == Some{Head.step(h, Some{v})}: Maybe<&2, Head>}
              Moved.step(h, v)(hl))})

# the ballots of the owners os in the round r of the height h of the line c
def Round.ballots(
  ~M: Machine(),
  s: Node<Machine.Q(M)>,
  c: Ledgers.Chain,
  h: U32,
  r: Nat,
  os: List<&2, String>
) -> List<&2, Maybe<&2, Cells.Cell<Ledgers.Vote>>>:
  Ledgers.Bucket.ballots(
    ~Machine.Q(M),
    Ledgers.State.under(~Machine.Q(M), State.ledger(~M, s), Ledgers.Slot.bucket(c, h, r)),
    os
  )

# the node o cast for the step v in the round r, as a count of ballots reads it
def Round.hit(~M: Machine(), s: Node<Machine.Q(M)>, c: Ledgers.Chain, h: U32, r: Nat, o: String, v: Ledgers.Vote) -> Bool:
  Quorums.Quorum.hit(
    ~Ledgers.Vote,
    ~Ledgers.Vote.is_eq,
    Ledgers.Entry.ballot(
      ~Machine.Q(M),
      Ledgers.State.get(
        ~Machine.Q(M),
        Ledgers.State.under(~Machine.Q(M), State.ledger(~M, s), Ledgers.Slot.bucket(c, h, r)),
        Ledgers.Slot.ballot(o)
      )
    ),
    v
  )

# a cell that counts for the step v holds a vote for v
def Hit.step(
  ~M: Machine(),
  m: Maybe<&2, Cells.Cell<Ledgers.Entry<Machine.Q(M)>>>,
  v: Ledgers.Vote
) -> {
  Quorums.Quorum.hit(
    ~Ledgers.Vote,
    ~Ledgers.Vote.is_eq,
    Ledgers.Entry.ballot(~Machine.Q(M), m),
    v
  )
    == True{}: Bool
} -> {Cast.step(~M, m) == Some{v}: Maybe<&2, Ledgers.Vote>}:
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
  ~M: Machine(),
  +s: Node<Machine.Q(M)>,
  +c: Ledgers.Chain,
  +h: U32,
  +r: Nat,
  +o: String,
  v: Ledgers.Vote
) -> {
  Round.hit(~M, s, c, h, r, o, v) == True{}: Bool
} -> {Cast.of(~M, s, Ledgers.Where{c, h, r}, o) == Some{v}: Maybe<&2, Ledgers.Vote>}:
  e =>
    %Tries.Trie.get_under(
      Cells.Cell<Ledgers.Entry<Machine.Q(M)>>,
      State.ledger(~M, s),
      Ledgers.Slot.bucket(c, h, r),
      Ledgers.Slot.ballot(o)
    ): {Cast.step(~M, _) == Some{v}: Maybe<&2, Ledgers.Vote>}
    Hit.step(~M, 
      Ledgers.State.get(
        ~Machine.Q(M),
        Ledgers.State.under(~Machine.Q(M), State.ledger(~M, s), Ledgers.Slot.bucket(c, h, r)),
        Ledgers.Slot.ballot(o)
      ),
      v
    )(e)

# a vote moved to an equal round
def Cast.moved(
  ~M: Machine(),
  s: Node<Machine.Q(M)>,
  c: Ledgers.Chain,
  h: U32,
  q: String,
  a: Nat,
  b: Nat,
  v: Ledgers.Vote,
  e: {a == b: Nat}
) -> {
  Cast.of(~M, s, Ledgers.Where{c, h, a}, q) == Some{v}: Maybe<&2, Ledgers.Vote>
} -> {Cast.of(~M, s, Ledgers.Where{c, h, b}, q) == Some{v}: Maybe<&2, Ledgers.Vote>}:
  k =>
    %e: {Cast.of(~M, s, Ledgers.Where{c, h, _}, q) == Some{v}: Maybe<&2, Ledgers.Vote>}
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
  ~M: Machine(),
  +s: Node<Machine.Q(M)>,
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
      Voter.if(Round.hit(~M, s, c, h, r, o, v), o, Round.voter(~M, s, c, h, r, rest, v))

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
  ~M: Machine(),
  s: Node<Machine.Q(M)>,
  c: Ledgers.Chain,
  h: U32,
  r: Nat,
  o: String,
  rest: Maybe<&2, String>,
  v: Ledgers.Vote,
  p: String,
  +hit: Bool,
  eh: {Round.hit(~M, s, c, h, r, o, v) == hit: Bool},
  ih: {
    rest == Some{p}: Maybe<&2, String>
  } -> {Cast.of(~M, s, Ledgers.Where{c, h, r}, p) == Some{v}: Maybe<&2, Ledgers.Vote>}
) -> {
  Voter.if(hit, o, rest) == Some{p}: Maybe<&2, String>
} -> {Cast.of(~M, s, Ledgers.Where{c, h, r}, p) == Some{v}: Maybe<&2, Ledgers.Vote>}:
  match hit:
    case True{}:
      e =>
        %Shared.Maybe.some_inj(
          String,
          o,
          p,
          e
        ): {Cast.of(~M, s, Ledgers.Where{c, h, r}, _) == Some{v}: Maybe<&2, Ledgers.Vote>}
        Hit.cast(~M, s, c, h, r, o, v)(eh)
    case False{}:
      e => ih(e)

# the voter cast for the step
def Voter.cast(
  ~M: Machine(),
  +s: Node<Machine.Q(M)>,
  +c: Ledgers.Chain,
  +h: U32,
  +r: Nat,
  +os: List<&2, String>,
  +v: Ledgers.Vote,
  +p: String
) -> {
  Round.voter(~M, s, c, h, r, os, v) == Some{p}: Maybe<&2, String>
} -> {Cast.of(~M, s, Ledgers.Where{c, h, r}, p) == Some{v}: Maybe<&2, Ledgers.Vote>}:
  match os:
    case Nil{}:
      e => Empty.absurd(
        {Cast.of(~M, s, Ledgers.Where{c, h, r}, p) == Some{v}: Maybe<&2, Ledgers.Vote>},
        Shared.Maybe.none_ne_some(String, p, e)
      )
    case Con{+o, +rest}:
      Voter.cast.at(~M, 
        s,
        c,
        h,
        r,
        o,
        Round.voter(~M, s, c, h, r, rest, v),
        v,
        p,
        Round.hit(~M, s, c, h, r, o, v),
        {==},
        Voter.cast(~M, s, c, h, r, rest, v, p)
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
  ~M: Machine(),
  +s: Node<Machine.Q(M)>,
  +c: Ledgers.Chain,
  +h: U32,
  +r: Nat,
  +os: List<&2, String>,
  +v: Ledgers.Vote
) -> {
  Round.voter(~M, s, c, h, r, os, v) == None{}: Maybe<&2, String>
} -> {
  Quorums.Quorum.yes(
    ~Ledgers.Vote,
    ~Ledgers.Vote.is_eq,
    Round.ballots(~M, s, c, h, r, os),
    v
  )
    == 0n: Nat
}:
  match os:
    case Nil{}:
      e => {==}
    case Con{o, rest}:
      Voter.yes.at(
        Round.hit(~M, s, c, h, r, o, v),
        o,
        Round.voter(~M, s, c, h, r, rest, v),
        Quorums.Quorum.yes(~Ledgers.Vote, ~Ledgers.Vote.is_eq, Round.ballots(~M, s, c, h, r, rest), v),
        Voter.yes(~M, s, c, h, r, rest, v)
      )

# nothing is less than a number that is zero
def Lt.none(n: Nat, y: Nat, e: {y == 0n: Nat}) -> {Nat.is_lt(n, y) == True{}: Bool} -> Empty:
  k =>
    Shared.Nat.lt_zero(n)(
      %e: {Nat.is_lt(n, _) == True{}: Bool}
      k)

# a step with a majority has a voter
def Has.voter(
  ~M: Machine(),
  +s: Node<Machine.Q(M)>,
  +c: Ledgers.Chain,
  +h: U32,
  +r: Nat,
  +os: List<&2, String>,
  +v: Ledgers.Vote
) -> {
  Quorums.Quorum.has(
    ~Ledgers.Vote,
    ~Ledgers.Vote.is_eq,
    Round.ballots(~M, s, c, h, r, os),
    v
  )
    == True{}: Bool
} -> {Round.voter(~M, s, c, h, r, os, v) == None{}: Maybe<&2, String>} -> Empty:
  hh => e =>
    Lt.none(
      Quorums.Quorum.no(~Ledgers.Vote, ~Ledgers.Vote.is_eq, Round.ballots(~M, s, c, h, r, os), v),
      Quorums.Quorum.yes(~Ledgers.Vote, ~Ledgers.Vote.is_eq, Round.ballots(~M, s, c, h, r, os), v),
      Voter.yes(~M, s, c, h, r, os, v)(e)
    )(hh)

# Sub.count for a first owner o and a first node f, once it is known whether
# they are the same (b)
def Sub.count.at(
  ~M: Machine(),
  +s: Node<Machine.Q(M)>,
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
    Round.voter(~M, s, c, h, r, fs, v) == None{}: Maybe<&2, String>
  } -> {
    Nat.is_le(
      List.length(&2, String, fs),
      Quorums.Quorum.no(~Ledgers.Vote, ~Ledgers.Vote.is_eq, Round.ballots(~M, s, c, h, r, rest), v)
    )
      == True{}: Bool
  },
  ih2: {
    Owners.sub(rest, f <> fs) == True{}: Bool
  } -> {
    Round.voter(~M, s, c, h, r, f <> fs, v) == None{}: Maybe<&2, String>
  } -> {
    Nat.is_le(
      1n+List.length(&2, String, fs),
      Quorums.Quorum.no(~Ledgers.Vote, ~Ledgers.Vote.is_eq, Round.ballots(~M, s, c, h, r, rest), v)
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
  Round.voter(~M, s, c, h, r, f <> fs, v) == None{}: Maybe<&2, String>
} -> {
  Nat.is_le(
    1n+List.length(&2, String, fs),
    Shared.Nat.add_if(
      Bool.not(Round.hit(~M, s, c, h, r, o, v)),
      Quorums.Quorum.no(~Ledgers.Vote, ~Ledgers.Vote.is_eq, Round.ballots(~M, s, c, h, r, rest), v)
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
              Bool.not(Round.hit(~M, s, c, h, r, _, v)),
              Quorums.Quorum.no(
                ~Ledgers.Vote,
                ~Ledgers.Vote.is_eq,
                Round.ballots(~M, s, c, h, r, rest),
                v
              )
            )
          )
            == True{}: Bool
        }
        %Equal.sym(
          Bool,
          Round.hit(~M, s, c, h, r, f, v),
          False{},
          Voter.if_hit(Round.hit(~M, s, c, h, r, f, v), f, Round.voter(~M, s, c, h, r, fs, v))(ev)
        ): {
          Nat.is_le(
            1n+List.length(&2, String, fs),
            Shared.Nat.add_if(
              Bool.not(_),
              Quorums.Quorum.no(
                ~Ledgers.Vote,
                ~Ledgers.Vote.is_eq,
                Round.ballots(~M, s, c, h, r, rest),
                v
              )
            )
          )
            == True{}: Bool
        }
        ih1(es)(Voter.if_rest(Round.hit(~M, s, c, h, r, f, v), f, Round.voter(~M, s, c, h, r, fs, v))(ev))
    case False{}:
      es => ev =>
        Shared.Nat.le_add_if(
          Bool.not(Round.hit(~M, s, c, h, r, o, v)),
          1n+List.length(&2, String, fs),
          Quorums.Quorum.no(~Ledgers.Vote, ~Ledgers.Vote.is_eq, Round.ballots(~M, s, c, h, r, rest), v)
        )(ih2(es)(ev))

# nodes that are some of the owners, none of which cast for the step v, are
# at most the ballots that are not for v
def Sub.count(
  ~M: Machine(),
  +s: Node<Machine.Q(M)>,
  +c: Ledgers.Chain,
  +h: U32,
  +r: Nat,
  os: List<&2, String>,
  from: List<&2, String>,
  +v: Ledgers.Vote
) -> {
  Owners.sub(os, from) == True{}: Bool
} -> {
  Round.voter(~M, s, c, h, r, from, v) == None{}: Maybe<&2, String>
} -> {
  Nat.is_le(
    List.length(&2, String, from),
    Quorums.Quorum.no(~Ledgers.Vote, ~Ledgers.Vote.is_eq, Round.ballots(~M, s, c, h, r, os), v)
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
          Round.ballots(~M, s, c, h, r, o <> rest),
          v
        )
      )
    case Con{+o, +rest} Con{+f, +fs}:
      Sub.count.at(~M, 
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
        Sub.count(~M, s, c, h, r, rest, fs, v),
        Sub.count(~M, s, c, h, r, rest, f <> fs, v)
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
  ~M: Machine(),
  +s: Node<Machine.Q(M)>,
  +c: Ledgers.Chain,
  +h: U32,
  +r: Nat,
  os: List<&2, String>,
  +v: Ledgers.Vote
) -> {
  Nat.add(
    Quorums.Quorum.yes(~Ledgers.Vote, ~Ledgers.Vote.is_eq, Round.ballots(~M, s, c, h, r, os), v),
    Quorums.Quorum.no(~Ledgers.Vote, ~Ledgers.Vote.is_eq, Round.ballots(~M, s, c, h, r, os), v)
  )
    == List.length(&2, String, os): Nat
}:
  match os:
    case Nil{}:
      {==}
    case Con{o, +rest}:
      Count.total.at(
        Round.hit(~M, s, c, h, r, o, v),
        Quorums.Quorum.yes(~Ledgers.Vote, ~Ledgers.Vote.is_eq, Round.ballots(~M, s, c, h, r, rest), v),
        Quorums.Quorum.no(~Ledgers.Vote, ~Ledgers.Vote.is_eq, Round.ballots(~M, s, c, h, r, rest), v),
        List.length(&2, String, rest),
        Count.total(~M, s, c, h, r, rest, v)
      )

# a number is at most a number equal to it
def Le.same(a: Nat, b: Nat, e: {a == b: Nat}) -> {Nat.is_le(a, b) == True{}: Bool}:
  %e: {Nat.is_le(a, _) == True{}: Bool}
  Shared.Nat.le_refl(a)

# two majorities share a node: nodes that are a majority of the owners, none
# of which cast for the step v, leave v no majority
def Major.meets(
  ~M: Machine(),
  +s: Node<Machine.Q(M)>,
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
    Round.ballots(~M, s, c, h, r, os),
    v
  )
    == True{}: Bool
} -> {Owners.sub(os, from) == True{}: Bool}
  -> {Owners.major(os, from) == True{}: Bool}
  -> {Round.voter(~M, s, c, h, r, from, v) == None{}: Maybe<&2, String>}
  -> Empty:
  hh => es => em => ev =>
    Shared.Nat.pigeon(
      List.length(&2, String, from),
      Quorums.Quorum.no(~Ledgers.Vote, ~Ledgers.Vote.is_eq, Round.ballots(~M, s, c, h, r, os), v),
      Quorums.Quorum.yes(~Ledgers.Vote, ~Ledgers.Vote.is_eq, Round.ballots(~M, s, c, h, r, os), v),
      List.length(&2, String, os)
    )(
      Sub.count(~M, s, c, h, r, os, from, v)(es)(ev)
    )(
      hh
    )(
      Le.same(
        Nat.add(
          Quorums.Quorum.yes(~Ledgers.Vote, ~Ledgers.Vote.is_eq, Round.ballots(~M, s, c, h, r, os), v),
          Quorums.Quorum.no(~Ledgers.Vote, ~Ledgers.Vote.is_eq, Round.ballots(~M, s, c, h, r, os), v)
        ),
        List.length(&2, String, os),
        Count.total(~M, s, c, h, r, os, v)
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
  ~M: Machine(),
  +s: Node<Machine.Q(M)>,
  +c: Ledgers.Chain,
  +h: U32,
  +q: String,
  p: Nat,
  +r: Nat,
  +x: Ledgers.Vote
) -> {
  Last.mine(~M, q, s, c, h, p) == Some{Ledgers.Last{r, x}}: Maybe<&2, Ledgers.Last>
} -> {Nat.is_le(r, p) == True{}: Bool}:
  match p:
    case 0n:
      Mine.le.or(
        0n,
        Cast.of(~M, s, Ledgers.Where{c, h, 0n}, q),
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
        Cast.of(~M, s, Ledgers.Where{c, h, 1n+j}, q),
        Last.mine(~M, q, s, c, h, j),
        r,
        x,
        e => Shared.Nat.le_succ(r, j)(Mine.le(~M, s, c, h, q, j, r, x)(e))
      )

# Mine.cast for one round
def Mine.cast.or(
  ~M: Machine(),
  s: Node<Machine.Q(M)>,
  c: Ledgers.Chain,
  h: U32,
  q: String,
  k: Nat,
  m: Maybe<&2, Ledgers.Vote>,
  em: {Cast.of(~M, s, Ledgers.Where{c, h, k}, q) == m: Maybe<&2, Ledgers.Vote>},
  rest: Maybe<&2, Ledgers.Last>,
  r: Nat,
  x: Ledgers.Vote,
  ih: {
    rest == Some{Ledgers.Last{r, x}}: Maybe<&2, Ledgers.Last>
  } -> {Cast.of(~M, s, Ledgers.Where{c, h, r}, q) == Some{x}: Maybe<&2, Ledgers.Vote>}
) -> {
  Last.or(k, m, u => rest) == Some{Ledgers.Last{r, x}}: Maybe<&2, Ledgers.Last>
} -> {Cast.of(~M, s, Ledgers.Where{c, h, r}, q) == Some{x}: Maybe<&2, Ledgers.Vote>}:
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
        ): {Cast.of(~M, s, Ledgers.Where{c, h, _}, q) == Some{x}: Maybe<&2, Ledgers.Vote>}
        %Equal.cong(
          Maybe<&2, Ledgers.Last>,
          Ledgers.Vote,
          Last.step(y),
          Some{Ledgers.Last{k, y}},
          Some{Ledgers.Last{r, x}},
          e
        ): {Cast.of(~M, s, Ledgers.Where{c, h, k}, q) == Some{_}: Maybe<&2, Ledgers.Vote>}
        em
    case None{}:
      e => ih(e)

# the last vote of a node is a vote that it cast
def Mine.cast(
  ~M: Machine(),
  +s: Node<Machine.Q(M)>,
  +c: Ledgers.Chain,
  +h: U32,
  +q: String,
  p: Nat,
  +r: Nat,
  +x: Ledgers.Vote
) -> {
  Last.mine(~M, q, s, c, h, p) == Some{Ledgers.Last{r, x}}: Maybe<&2, Ledgers.Last>
} -> {Cast.of(~M, s, Ledgers.Where{c, h, r}, q) == Some{x}: Maybe<&2, Ledgers.Vote>}:
  match p:
    case 0n:
      Mine.cast.or(~M, 
        s,
        c,
        h,
        q,
        0n,
        Cast.of(~M, s, Ledgers.Where{c, h, 0n}, q),
        {==},
        None{},
        r,
        x,
        e => Empty.absurd(
          {Cast.of(~M, s, Ledgers.Where{c, h, r}, q) == Some{x}: Maybe<&2, Ledgers.Vote>},
          Shared.Maybe.none_ne_some(Ledgers.Last, Ledgers.Last{r, x}, e)
        )
      )
    case 1n+(+j):
      Mine.cast.or(~M, 
        s,
        c,
        h,
        q,
        1n+j,
        Cast.of(~M, s, Ledgers.Where{c, h, 1n+j}, q),
        {==},
        Last.mine(~M, q, s, c, h, j),
        r,
        x,
        Mine.cast(~M, s, c, h, q, j, r, x)
      )

# Cast.apart once it is known whether the rounds are the same (b)
def Cast.apart.at(
  ~M: Machine(),
  s: Node<Machine.Q(M)>,
  c: Ledgers.Chain,
  h: U32,
  q: String,
  +r1: Nat,
  +k: Nat,
  v1: Ledgers.Vote,
  b: Bool,
  eb: {Nat.is_eq(r1, k) == b: Bool}
) -> {
  Cast.of(~M, s, Ledgers.Where{c, h, r1}, q) == Some{v1}: Maybe<&2, Ledgers.Vote>
} -> {
  Cast.of(~M, s, Ledgers.Where{c, h, k}, q) == None{}: Maybe<&2, Ledgers.Vote>
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
            Cast.of(~M, s, Ledgers.Where{c, h, k}, q),
            Some{v1},
            Equal.sym(
              Maybe<&2, Ledgers.Vote>,
              Cast.of(~M, s, Ledgers.Where{c, h, k}, q),
              None{},
              en
            ),
            Cast.moved(~M, s, c, h, q, r1, k, v1, Shared.Nat.is_eq_sound(r1, k)(eb))(e1)
          )
        )
      )
    case False{}:
      e1 => en => {==}

# a round with a vote of a node is not a round without one
def Cast.apart(
  ~M: Machine(),
  s: Node<Machine.Q(M)>,
  c: Ledgers.Chain,
  h: U32,
  q: String,
  +r1: Nat,
  +k: Nat,
  v1: Ledgers.Vote
) -> {
  Cast.of(~M, s, Ledgers.Where{c, h, r1}, q) == Some{v1}: Maybe<&2, Ledgers.Vote>
} -> {
  Cast.of(~M, s, Ledgers.Where{c, h, k}, q) == None{}: Maybe<&2, Ledgers.Vote>
} -> {Nat.is_eq(r1, k) == False{}: Bool}:
  e1 => en => Cast.apart.at(~M, s, c, h, q, r1, k, v1, Nat.is_eq(r1, k), {==})(e1)(en)

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
  ~M: Machine(),
  +s: Node<Machine.Q(M)>,
  +c: Ledgers.Chain,
  +h: U32,
  +q: String,
  p: Nat,
  +r1: Nat,
  +v1: Ledgers.Vote
) -> {
  Cast.of(~M, s, Ledgers.Where{c, h, r1}, q) == Some{v1}: Maybe<&2, Ledgers.Vote>
} -> {
  Nat.is_le(r1, p) == True{}: Bool
} -> {Last.from(Last.mine(~M, q, s, c, h, p), r1) == True{}: Bool}:
  match p:
    case 0n:
      +e1 => +le =>
        Mine.from.or(
          0n,
          Cast.of(~M, s, Ledgers.Where{c, h, 0n}, q),
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
                Cast.of(~M, s, Ledgers.Where{c, h, 0n}, q),
                Some{v1},
                Equal.sym(
                  Maybe<&2, Ledgers.Vote>,
                  Cast.of(~M, s, Ledgers.Where{c, h, 0n}, q),
                  None{},
                  en
                ),
                Cast.moved(~M, s, c, h, q, r1, 0n, v1, Shared.Nat.le_zero_eq(r1)(le))(e1)
              )
            )
          )
        )
    case 1n+(+j):
      +e1 => +le =>
        Mine.from.or(
          1n+j,
          Cast.of(~M, s, Ledgers.Where{c, h, 1n+j}, q),
          Last.mine(~M, q, s, c, h, j),
          r1
        )(
          le
        )(
          en => Mine.from(~M, 
            s,
            c,
            h,
            q,
            j,
            r1,
            v1
          )(e1)(Shared.Nat.le_step(r1, j)(le)(Cast.apart(~M, s, c, h, q, r1, 1n+j, v1)(e1)(en)))
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
) -> {
  Last.from(Last.newer(a, b), r1) == False{}: Bool
} -> {Last.from(a, r1) == False{}: Bool}:
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
) -> {
  Last.from(Last.newer(a, b), r1) == False{}: Bool
} -> {Last.from(b, r1) == False{}: Bool}:
  match a b:
    case None{} y:
      e => e
    case Some{x} None{}:
      e => {==}
    case Some{Ledgers.Last{+ra, va}} Some{Ledgers.Last{+rb, vb}}:
      Newer.right.at(ra, va, rb, vb, r1, Nat.is_lt(ra, rb), {==})

# the rule that the passes that a vote names allow it, at the head hd whose tip is tp
def Rules.allow(
  ~M: Machine(),
  ~s: Node<Machine.Q(M)>,
  ~c: Ledgers.Chain,
  ~rules: Rounds.Rules(~M, s, c),
  hd: Head,
  tp: Tip,
  ok: {Head.tip(~M, s, hd) == Some{tp}: Maybe<&2, Tip>}
) -> Rounds.Allow(~M, s, c, Head.next(hd), Tip.owners(tp)):
  Shared.Pair.first(
    Rounds.Allow(~M, s, c, Head.next(hd), Tip.owners(tp)),
    Rounds.Last(~M, 
      s,
      c,
      Head.next(hd)
    )
      & Rounds.Same(~M, s, c, Head.next(hd)),
    rules(hd)(tp)(ok)
  )

# the rule that a pass names the last vote of its node below its round, at the head hd whose tip is tp
def Rules.last(
  ~M: Machine(),
  ~s: Node<Machine.Q(M)>,
  ~c: Ledgers.Chain,
  ~rules: Rounds.Rules(~M, s, c),
  hd: Head,
  tp: Tip,
  ok: {Head.tip(~M, s, hd) == Some{tp}: Maybe<&2, Tip>}
) -> Rounds.Last(~M, s, c, Head.next(hd)):
  Shared.Pair.first(
    Rounds.Last(~M, s, c, Head.next(hd)),
    Rounds.Same(~M, s, c, Head.next(hd)),
    Shared.Pair.second(
      Rounds.Allow(~M, s, c, Head.next(hd), Tip.owners(tp)),
      Rounds.Last(~M, 
        s,
        c,
        Head.next(hd)
      )
        & Rounds.Same(~M, s, c, Head.next(hd)),
      rules(hd)(tp)(ok)
    )
  )

# the rule that the votes of one round are for one step, at the head hd whose tip is tp
def Rules.same(
  ~M: Machine(),
  ~s: Node<Machine.Q(M)>,
  ~c: Ledgers.Chain,
  ~rules: Rounds.Rules(~M, s, c),
  hd: Head,
  tp: Tip,
  ok: {Head.tip(~M, s, hd) == Some{tp}: Maybe<&2, Tip>}
) -> Rounds.Same(~M, s, c, Head.next(hd)):
  Shared.Pair.second(
    Rounds.Last(~M, s, c, Head.next(hd)),
    Rounds.Same(~M, s, c, Head.next(hd)),
    Shared.Pair.second(
      Rounds.Allow(~M, s, c, Head.next(hd), Tip.owners(tp)),
      Rounds.Last(~M, 
        s,
        c,
        Head.next(hd)
      )
        & Rounds.Same(~M, s, c, Head.next(hd)),
      rules(hd)(tp)(ok)
    )
  )

# Pass.miss for a first node o, once its hit in the round r1 (hit) and its
# pass (m) are known
def Pass.miss.at(
  ~M: Machine(),
  ~s: Node<Machine.Q(M)>,
  ~c: Ledgers.Chain,
  ~rules: Rounds.Rules(~M, s, c),
  +hd: Head,
  tp: Tip,
  ok: {Head.tip(~M, s, hd) == Some{tp}: Maybe<&2, Tip>},
  +p: Nat,
  +r1: Nat,
  +v1: Ledgers.Vote,
  +o: String,
  rest: Maybe<&2, String>,
  hit: Bool,
  m: Maybe<&2, Maybe<&2, Ledgers.Last>>
) -> {Round.hit(~M, s, c, Head.next(hd), r1, o, v1) == hit: Bool}
  -> {
    Ledgers.State.passed(
      ~Machine.Q(M),
      State.ledger(~M, s),
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
            %Equal.sym(Maybe<&2, Ledgers.Last>, l, Last.mine(~M, o, s, c, Head.next(hd), p), Rules.last(~M, ~s, ~c, ~rules, hd, tp, ok)(1n+p)(o)(l)(em)): {Last.from(_, r1) == True{}: Bool}
            Mine.from(~M, s, c, Head.next(hd), o, p, r1, v1)(Hit.cast(~M, s, c, Head.next(hd), r1, o, v1)(eh))(le)))
      )

# when the passes of the nodes from to the round 1 + p name no vote of the
# round r1 or later, none of them cast in r1
def Pass.miss(
  ~M: Machine(),
  ~s: Node<Machine.Q(M)>,
  ~c: Ledgers.Chain,
  ~rules: Rounds.Rules(~M, s, c),
  +hd: Head,
  +tp: Tip,
  +ok: {Head.tip(~M, s, hd) == Some{tp}: Maybe<&2, Tip>},
  +p: Nat,
  +r1: Nat,
  +v1: Ledgers.Vote,
  from: List<&2, String>
) -> {Nat.is_le(r1, p) == True{}: Bool}
  -> {Passed.all(~M, s, Ledgers.Where{c, Head.next(hd), 1n+p}, from) == True{}: Bool}
  -> {
    Last.from(
      Passes.last(~M, s, Ledgers.Where{c, Head.next(hd), 1n+p}, from),
      r1
    )
      == False{}: Bool
  }
  -> {Round.voter(~M, s, c, Head.next(hd), r1, from, v1) == None{}: Maybe<&2, String>}:
  match from:
    case Nil{}:
      le => ea => ef => {==}
    case Con{+o, +rest}:
      +le => +ea => +ef =>
        Pass.miss.at(~M, 
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
          Round.voter(~M, s, c, Head.next(hd), r1, rest, v1),
          Round.hit(~M, s, c, Head.next(hd), r1, o, v1),
          Ledgers.State.passed(
            ~Machine.Q(M),
            State.ledger(~M, s),
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
                ~Machine.Q(M),
                State.ledger(~M, s),
                Ledgers.Where{c, Head.next(hd), 1n+p},
                o
              )
            ),
            u => Passed.all(~M, s, Ledgers.Where{c, Head.next(hd), 1n+p}, rest)
          )(ea)
        )(
          Newer.left(
            Passed.last(
              Ledgers.State.passed(
                ~Machine.Q(M),
                State.ledger(~M, s),
                Ledgers.Where{c, Head.next(hd), 1n+p},
                o
              )
            ),
            Passes.last(~M, s, Ledgers.Where{c, Head.next(hd), 1n+p}, rest),
            r1
          )(ef)
        )(
          Pass.miss(~M, 
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
                  ~Machine.Q(M),
                  State.ledger(~M, s),
                  Ledgers.Where{c, Head.next(hd), 1n+p},
                  o
                )
              ),
              u => Passed.all(~M, s, Ledgers.Where{c, Head.next(hd), 1n+p}, rest)
            )(ea)
          )(
            Newer.right(
              Passed.last(
                Ledgers.State.passed(
                  ~Machine.Q(M),
                  State.ledger(~M, s),
                  Ledgers.Where{c, Head.next(hd), 1n+p},
                  o
                )
              ),
              Passes.last(~M, s, Ledgers.Where{c, Head.next(hd), 1n+p}, rest),
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
def Named(~M: Machine(), -R: Type, s: Node<Machine.Q(M)>, w: Ledgers.Where, l: Ledgers.Last) -> Type:
  (
    @q: String -> {
      Passed.last(
        Ledgers.State.passed(~Machine.Q(M), State.ledger(~M, s), w, q)
      )
        == Some{l}: Maybe<&2, Ledgers.Last>
    } -> R
  ) -> R

# Last.elim for a first node o, once what it named (a) and what the rest
# named (b) are known
def Last.elim.at(
  ~M: Machine(),
  -R: Type,
  s: Node<Machine.Q(M)>,
  w: Ledgers.Where,
  o: String,
  l: Ledgers.Last,
  a: Maybe<&2, Ledgers.Last>,
  b: Maybe<&2, Ledgers.Last>
) -> {
  Passed.last(
    Ledgers.State.passed(~Machine.Q(M), State.ledger(~M, s), w, o)
  )
    == a: Maybe<&2, Ledgers.Last>
} -> (
  {b == Some{l}: Maybe<&2, Ledgers.Last>} -> Named(~M, R, s, w, l)
) -> {Last.newer(a, b) == Some{l}: Maybe<&2, Ledgers.Last>} -> Named(~M, R, s, w, l):
  match a b:
    case None{} y:
      ea => ih => e => ih(e)
    case Some{x} None{}:
      ea => ih => e => k => k(
        o
      )(
        Equal.trans(
          Maybe<&2, Ledgers.Last>,
          Passed.last(Ledgers.State.passed(~Machine.Q(M), State.ledger(~M, s), w, o)),
          Some{x},
          Some{l},
          ea,
          e
        )
      )
    case Some{Ledgers.Last{+ra, va}} Some{Ledgers.Last{+rb, vb}}:
      ea => ih => e =>
        When.elim(
          Named(~M, R, s, w, l),
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
              Passed.last(Ledgers.State.passed(~Machine.Q(M), State.ledger(~M, s), w, o)),
              Some{Ledgers.Last{ra, va}},
              Some{l},
              ea,
              e2
            )
          )
        )

# the last vote of the highest round that passes name is named by one of them
def Last.elim(
  ~M: Machine(),
  -R: Type,
  +s: Node<Machine.Q(M)>,
  +w: Ledgers.Where,
  from: List<&2, String>,
  +l: Ledgers.Last
) -> {Passes.last(~M, s, w, from) == Some{l}: Maybe<&2, Ledgers.Last>} -> Named(~M, R, s, w, l):
  match from:
    case Nil{}:
      e => k => Empty.absurd(R, Shared.Maybe.none_ne_some(Ledgers.Last, l, e))
    case Con{+o, +rest}:
      Last.elim.at(~M, 
        R,
        s,
        w,
        o,
        l,
        Passed.last(Ledgers.State.passed(~Machine.Q(M), State.ledger(~M, s), w, o)),
        Passes.last(~M, s, w, rest)
      )({==})(Last.elim(~M, R, s, w, rest, l))

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
  ~M: Machine(),
  s: Node<Machine.Q(M)>,
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
    Cast.of(~M, s, Ledgers.Where{c, h, rm}, qm) == Some{vm}: Maybe<&2, Ledgers.Vote>
  } -> {vm == v1: Ledgers.Vote}

# Rounds.last once the node qw that named the last vote is known, with its
# last vote
def Rounds.named(
  ~M: Machine(),
  ~s: Node<Machine.Q(M)>,
  ~c: Ledgers.Chain,
  ~rules: Rounds.Rules(~M, s, c),
  +hd: Head,
  tp: Tip,
  ok: {Head.tip(~M, s, hd) == Some{tp}: Maybe<&2, Tip>},
  r1: Nat,
  v1: Ledgers.Vote,
  +p: Nat,
  j: Nat,
  +rm: Nat,
  +vm: Ledgers.Vote,
  +qw: String,
  +em: {
    Last.mine(~M, 
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
  ih: Rounds.Below(~M, s, c, Head.next(hd), r1, v1, j)
) -> {vm == v1: Ledgers.Vote}:
  ih(
    rm
  )(
    qw
  )(
    vm
  )(
    Shared.Nat.le_lt(rm, p, j)(Mine.le(~M, s, c, Head.next(hd), qw, p, rm, vm)(em))(lt)
  )(le)(Mine.cast(~M, s, c, Head.next(hd), qw, p, rm, vm)(em))

# Rounds.round once the last vote m that the passes name is known: it is of
# the round r1 or later, and the vote x is for its step
def Rounds.last(
  ~M: Machine(),
  ~s: Node<Machine.Q(M)>,
  ~c: Ledgers.Chain,
  ~rules: Rounds.Rules(~M, s, c),
  +hd: Head,
  +tp: Tip,
  +ok: {Head.tip(~M, s, hd) == Some{tp}: Maybe<&2, Tip>},
  r1: Nat,
  v1: Ledgers.Vote,
  +p: Nat,
  x: Ledgers.Vote,
  j: Nat,
  from: List<&2, String>,
  m: Maybe<&2, Ledgers.Last>
) -> {
  Passes.last(~M, 
    s,
    Ledgers.Where{c, Head.next(hd), 1n+p},
    from
  )
    == m: Maybe<&2, Ledgers.Last>
}
  -> {Last.from(m, r1) == True{}: Bool}
  -> {Last.is(m, x) == True{}: Bool}
  -> {Nat.is_lt(p, j) == True{}: Bool}
  -> Rounds.Below(~M, s, c, Head.next(hd), r1, v1, j)
  -> {x == v1: Ledgers.Vote}:
  match m:
    case None{}:
      em => ef => ei => lt => ih => Empty.absurd(
        {x == v1: Ledgers.Vote},
        Shared.Bool.false_ne_true(ef)
      )
    case Some{Ledgers.Last{+rm, +vm}}:
      em => ef => ei => lt => ih =>
        Last.elim(~M, 
          {x == v1: Ledgers.Vote},
          s,
          Ledgers.Where{c, Head.next(hd), 1n+p},
          from,
          Ledgers.Last{rm, vm}
        )(em)(
          +qw => ew =>
            %Ledgers.Vote.is_eq_sound(vm, x)(ei): {_ == v1: Ledgers.Vote}
            Rounds.named(~M, ~s, ~c, ~rules, hd, tp, ok, r1, v1, p, j, rm, vm, qw, Equal.sym(Maybe<&2, Ledgers.Last>, Some{Ledgers.Last{rm, vm}}, Last.mine(~M, qw, s, c, Head.next(hd), p), Rules.last(~M, ~s, ~c, ~rules, hd, tp, ok)(1n+p)(qw)(Some{Ledgers.Last{rm, vm}})(Passed.some(Ledgers.State.passed(~Machine.Q(M), State.ledger(~M, s), Ledgers.Where{c, Head.next(hd), 1n+p}, qw), Ledgers.Last{rm, vm})(ew))), lt, ef, ih))

# Rounds.round once it is known whether the passes name a vote of the round
# r1 or later (f)
def Rounds.pick(
  ~M: Machine(),
  ~s: Node<Machine.Q(M)>,
  ~c: Ledgers.Chain,
  ~rules: Rounds.Rules(~M, s, c),
  +hd: Head,
  +tp: Tip,
  ok: {Head.tip(~M, s, hd) == Some{tp}: Maybe<&2, Tip>},
  +r1: Nat,
  +v1: Ledgers.Vote,
  +p: Nat,
  +x: Ledgers.Vote,
  j: Nat,
  +from: List<&2, String>,
  f: Bool
) -> {
  Last.from(
    Passes.last(~M, s, Ledgers.Where{c, Head.next(hd), 1n+p}, from),
    r1
  )
    == f: Bool
}
  -> {
    Quorums.Quorum.has(
      ~Ledgers.Vote,
      ~Ledgers.Vote.is_eq,
      Round.ballots(~M, s, c, Head.next(hd), r1, Tip.owners(tp)),
      v1
    )
      == True{}: Bool
  }
  -> {Nat.is_lt(p, j) == True{}: Bool}
  -> {Nat.is_le(r1, p) == True{}: Bool}
  -> Rounds.Below(~M, s, c, Head.next(hd), r1, v1, j)
  -> {
    Later.all(
      Passed.all(~M, s, Ledgers.Where{c, Head.next(hd), 1n+p}, from),
      Owners.sub(Tip.owners(tp), from),
      Owners.major(Tip.owners(tp), from),
      Last.is(Passes.last(~M, s, Ledgers.Where{c, Head.next(hd), 1n+p}, from), x)
    )
      == True{}: Bool
  }
  -> {x == v1: Ledgers.Vote}:
  match f:
    case False{}:
      ef => hh => lt => le => ih => +al =>
        Empty.absurd(
          {x == v1: Ledgers.Vote},
          Major.meets(~M, 
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
              Passed.all(~M, s, Ledgers.Where{c, Head.next(hd), 1n+p}, from),
              Owners.sub(Tip.owners(tp), from),
              Owners.major(Tip.owners(tp), from),
              Last.is(
                Passes.last(~M, s, Ledgers.Where{c, Head.next(hd), 1n+p}, from),
                x
              )
            )(al)
          )(
            Later.all.c(
              Passed.all(~M, s, Ledgers.Where{c, Head.next(hd), 1n+p}, from),
              Owners.sub(Tip.owners(tp), from),
              Owners.major(Tip.owners(tp), from),
              Last.is(
                Passes.last(~M, s, Ledgers.Where{c, Head.next(hd), 1n+p}, from),
                x
              )
            )(al)
          )(
            Pass.miss(~M, 
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
                Passed.all(~M, s, Ledgers.Where{c, Head.next(hd), 1n+p}, from),
                Owners.sub(Tip.owners(tp), from),
                Owners.major(Tip.owners(tp), from),
                Last.is(
                  Passes.last(~M, s, Ledgers.Where{c, Head.next(hd), 1n+p}, from),
                  x
                )
              )(al)
            )(ef)
          )
        )
    case True{}:
      ef => hh => lt => le => ih => al =>
        Rounds.last(~M, 
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
          Passes.last(~M, s, Ledgers.Where{c, Head.next(hd), 1n+p}, from)
        )(
          {==}
        )(
          ef
        )(
          Later.all.d(
            Passed.all(~M, s, Ledgers.Where{c, Head.next(hd), 1n+p}, from),
            Owners.sub(Tip.owners(tp), from),
            Owners.major(Tip.owners(tp), from),
            Last.is(
              Passes.last(~M, s, Ledgers.Where{c, Head.next(hd), 1n+p}, from),
              x
            )
          )(al)
        )(lt)(ih)

# Rounds.same at the round r1 itself, once a voter m of the step v1 is known
def Rounds.base(
  ~M: Machine(),
  ~s: Node<Machine.Q(M)>,
  ~c: Ledgers.Chain,
  ~rules: Rounds.Rules(~M, s, c),
  +hd: Head,
  +tp: Tip,
  ok: {Head.tip(~M, s, hd) == Some{tp}: Maybe<&2, Tip>},
  +r1: Nat,
  +v1: Ledgers.Vote,
  q: String,
  x: Ledgers.Vote,
  m: Maybe<&2, String>
) -> {
  Round.voter(~M, 
    s,
    c,
    Head.next(hd),
    r1,
    Tip.owners(tp),
    v1
  )
    == m: Maybe<&2, String>
}
  -> {
    Quorums.Quorum.has(
      ~Ledgers.Vote,
      ~Ledgers.Vote.is_eq,
      Round.ballots(~M, s, c, Head.next(hd), r1, Tip.owners(tp)),
      v1
    )
      == True{}: Bool
  }
  -> {
    Cast.of(~M, 
      s,
      Ledgers.Where{c, Head.next(hd), r1},
      q
    )
      == Some{x}: Maybe<&2, Ledgers.Vote>
  }
  -> {x == v1: Ledgers.Vote}:
  match m:
    case None{}:
      em => hh => e => Empty.absurd(
        {x == v1: Ledgers.Vote},
        Has.voter(~M, s, c, Head.next(hd), r1, Tip.owners(tp), v1)(hh)(em)
      )
    case Some{+o}:
      em => hh => e => Rules.same(~M, 
        ~s,
        ~c,
        ~rules,
        hd,
        tp,
        ok
      )(
        r1
      )(
        q
      )(
        o
      )(x)(v1)(e)(Voter.cast(~M, s, c, Head.next(hd), r1, Tip.owners(tp), v1, o)(em))

# Rounds.same in a round after r1
def Rounds.step(
  ~M: Machine(),
  ~s: Node<Machine.Q(M)>,
  ~c: Ledgers.Chain,
  ~rules: Rounds.Rules(~M, s, c),
  +hd: Head,
  +tp: Tip,
  +ok: {Head.tip(~M, s, hd) == Some{tp}: Maybe<&2, Tip>},
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
      Round.ballots(~M, s, c, Head.next(hd), r1, Tip.owners(tp)),
      v1
    )
      == True{}: Bool
  }
  -> {Nat.is_lt(r, 1n+j) == True{}: Bool}
  -> {Nat.is_le(r1, r) == True{}: Bool}
  -> {
    Cast.of(~M, 
      s,
      Ledgers.Where{c, Head.next(hd), r},
      q
    )
      == Some{x}: Maybe<&2, Ledgers.Vote>
  }
  -> Rounds.Below(~M, s, c, Head.next(hd), r1, v1, j)
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
        Rounds.pick(~M, 
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
          Cast.from(~M, s, Ledgers.Where{c, Head.next(hd), 1n+p}, q),
          Last.from(
            Passes.last(~M, 
              s,
              Ledgers.Where{c, Head.next(hd), 1n+p},
              Cast.from(~M, s, Ledgers.Where{c, Head.next(hd), 1n+p}, q)
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
        )(ih)(Rules.allow(~M, ~s, ~c, ~rules, hd, tp, ok)(1n+p)(q)(x)(e))

# Rounds.same once it is known whether the round is r1 (b)
def Rounds.same.at(
  ~M: Machine(),
  ~s: Node<Machine.Q(M)>,
  ~c: Ledgers.Chain,
  ~rules: Rounds.Rules(~M, s, c),
  +hd: Head,
  +tp: Tip,
  ok: {Head.tip(~M, s, hd) == Some{tp}: Maybe<&2, Tip>},
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
      Round.ballots(~M, s, c, Head.next(hd), r1, Tip.owners(tp)),
      v1
    )
      == True{}: Bool
  }
  -> {Nat.is_lt(r, 1n+j) == True{}: Bool}
  -> {Nat.is_le(r1, r) == True{}: Bool}
  -> {
    Cast.of(~M, 
      s,
      Ledgers.Where{c, Head.next(hd), r},
      q
    )
      == Some{x}: Maybe<&2, Ledgers.Vote>
  }
  -> Rounds.Below(~M, s, c, Head.next(hd), r1, v1, j)
  -> {x == v1: Ledgers.Vote}:
  match b:
    case True{}:
      eb => hh => lt => le => e => ih =>
        Rounds.base(~M, 
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
          Round.voter(~M, s, c, Head.next(hd), r1, Tip.owners(tp), v1)
        )(
          {==}
        )(
          hh
        )(
          Cast.moved(~M, 
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
        Rounds.step(~M, ~s, ~c, ~rules, hd, tp, ok, r1, v1, r, q, x, j)(eb)(hh)(lt)(le)(e)(ih)

# each vote of a round from r1 on, below the round k, is for the step that a
# majority cast in r1
def Rounds.same(
  ~M: Machine(),
  ~s: Node<Machine.Q(M)>,
  ~c: Ledgers.Chain,
  ~rules: Rounds.Rules(~M, s, c),
  +hd: Head,
  +tp: Tip,
  +ok: {Head.tip(~M, s, hd) == Some{tp}: Maybe<&2, Tip>},
  k: Nat,
  +r1: Nat,
  +v1: Ledgers.Vote
) -> {
  Quorums.Quorum.has(
    ~Ledgers.Vote,
    ~Ledgers.Vote.is_eq,
    Round.ballots(~M, s, c, Head.next(hd), r1, Tip.owners(tp)),
    v1
  )
    == True{}: Bool
} -> Rounds.Below(~M, s, c, Head.next(hd), r1, v1, k):
  match k:
    case 0n:
      hh => rm => qm => vm => lt => le => e => Empty.absurd(
        {vm == v1: Ledgers.Vote},
        Shared.Nat.lt_zero(rm)(lt)
      )
    case 1n+(+j):
      +hh => +rm => qm => vm => lt => le => e =>
        Rounds.same.at(~M, 
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
        )({==})(hh)(lt)(le)(e)(Rounds.same(~M, ~s, ~c, ~rules, hd, tp, ok, j, r1, v1)(hh))

# Rounds.later once a voter m of the step v2 in the round r2 is known
def Rounds.later.at(
  ~M: Machine(),
  ~s: Node<Machine.Q(M)>,
  ~c: Ledgers.Chain,
  ~rules: Rounds.Rules(~M, s, c),
  +hd: Head,
  +tp: Tip,
  ok: {Head.tip(~M, s, hd) == Some{tp}: Maybe<&2, Tip>},
  r1: Nat,
  +r2: Nat,
  v1: Ledgers.Vote,
  +v2: Ledgers.Vote,
  m: Maybe<&2, String>
) -> {
  Round.voter(~M, 
    s,
    c,
    Head.next(hd),
    r2,
    Tip.owners(tp),
    v2
  )
    == m: Maybe<&2, String>
}
  -> {Nat.is_le(r1, r2) == True{}: Bool}
  -> {
    Quorums.Quorum.has(
      ~Ledgers.Vote,
      ~Ledgers.Vote.is_eq,
      Round.ballots(~M, s, c, Head.next(hd), r1, Tip.owners(tp)),
      v1
    )
      == True{}: Bool
  }
  -> {
    Quorums.Quorum.has(
      ~Ledgers.Vote,
      ~Ledgers.Vote.is_eq,
      Round.ballots(~M, s, c, Head.next(hd), r2, Tip.owners(tp)),
      v2
    )
      == True{}: Bool
  }
  -> {v2 == v1: Ledgers.Vote}:
  match m:
    case None{}:
      em => le => h1 => h2 => Empty.absurd(
        {v2 == v1: Ledgers.Vote},
        Has.voter(~M, s, c, Head.next(hd), r2, Tip.owners(tp), v2)(h2)(em)
      )
    case Some{+o}:
      em => le => h1 => h2 =>
        Rounds.same(~M, 
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
        )(le)(Voter.cast(~M, s, c, Head.next(hd), r2, Tip.owners(tp), v2, o)(em))

# a round decides what an earlier round of its height decided
def Rounds.later(
  ~M: Machine(),
  ~s: Node<Machine.Q(M)>,
  ~c: Ledgers.Chain,
  ~rules: Rounds.Rules(~M, s, c),
  +hd: Head,
  +tp: Tip,
  ok: {Head.tip(~M, s, hd) == Some{tp}: Maybe<&2, Tip>},
  +r1: Nat,
  +r2: Nat,
  +v1: Ledgers.Vote,
  +v2: Ledgers.Vote
) -> {Nat.is_le(r1, r2) == True{}: Bool}
  -> {
    Ledgers.State.decide(
      ~Machine.Q(M),
      State.ledger(~M, s),
      Ledgers.Where{c, Head.next(hd), r1},
      Tip.owners(tp)
    )
      == Some{v1}: Maybe<&2, Ledgers.Vote>
  }
  -> {
    Ledgers.State.decide(
      ~Machine.Q(M),
      State.ledger(~M, s),
      Ledgers.Where{c, Head.next(hd), r2},
      Tip.owners(tp)
    )
      == Some{v2}: Maybe<&2, Ledgers.Vote>
  }
  -> {v2 == v1: Ledgers.Vote}:
  le => d1 => d2 =>
    Rounds.later.at(~M, 
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
      Round.voter(~M, s, c, Head.next(hd), r2, Tip.owners(tp), v2)
    )(
      {==}
    )(
      le
    )(
      Quorums.Quorum.major_has(
        ~Ledgers.Vote,
        ~Ledgers.Vote.is_eq,
        ~Ledgers.Vote.laws(),
        Round.ballots(~M, s, c, Head.next(hd), r1, Tip.owners(tp)),
        v1
      )(d1)
    )(
      Quorums.Quorum.major_has(
        ~Ledgers.Vote,
        ~Ledgers.Vote.is_eq,
        ~Ledgers.Vote.laws(),
        Round.ballots(~M, s, c, Head.next(hd), r2, Tip.owners(tp)),
        v2
      )(d2)
    )

# Rounds.one once it is known whether r1 is at most r2 (b)
def Rounds.one.at(
  ~M: Machine(),
  ~s: Node<Machine.Q(M)>,
  ~c: Ledgers.Chain,
  ~rules: Rounds.Rules(~M, s, c),
  hd: Head,
  tp: Tip,
  ok: {Head.tip(~M, s, hd) == Some{tp}: Maybe<&2, Tip>},
  +r1: Nat,
  +r2: Nat,
  v1: Ledgers.Vote,
  v2: Ledgers.Vote,
  b: Bool
) -> {Nat.is_le(r1, r2) == b: Bool}
  -> {
    Ledgers.State.decide(
      ~Machine.Q(M),
      State.ledger(~M, s),
      Ledgers.Where{c, Head.next(hd), r1},
      Tip.owners(tp)
    )
      == Some{v1}: Maybe<&2, Ledgers.Vote>
  }
  -> {
    Ledgers.State.decide(
      ~Machine.Q(M),
      State.ledger(~M, s),
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
        Rounds.later(~M, ~s, ~c, ~rules, hd, tp, ok, r1, r2, v1, v2)(eb)(d1)(d2)
      )
    case False{}:
      eb => d1 => d2 =>
        Rounds.later(~M, 
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
  ~M: Machine(),
  ~s: Node<Machine.Q(M)>,
  ~c: Ledgers.Chain,
  ~rules: Rounds.Rules(~M, s, c)
) -> Line.One(~M, s, c):
  +hd => +tp => +ok => +r1 => +r2 => v1 => v2 => d1 => d2 =>
    Rounds.one.at(~M, ~s, ~c, ~rules, hd, tp, ok, r1, r2, v1, v2, Nat.is_le(r1, r2))({==})(d1)(d2)

# the rounds of each of k heights decide one step, when the ballots follow the
# rules of rounds
def Rounds.ones(
  ~M: Machine(),
  ~s: Node<Machine.Q(M)>,
  ~c: Ledgers.Chain,
  ~rules: Rounds.Rules(~M, s, c),
  k: Nat
) -> Line.Ones(~M, k, s, c):
  match k:
    case 0n:
      Unit{}
    case 1n+p:
      (Rounds.ones(~M, ~s, ~c, ~rules, p), Rounds.one(~M, ~s, ~c, ~rules))

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
  ~M: Machine(),
  a: Node<Machine.Q(M)>,
  b: Node<Machine.Q(M)>,
  +c: Ledgers.Chain,
  +i: Ledgers.Id,
  -o: Out,
  hk: Node.Keeps(~M, a, b)
) -> {
  Chain.out(~M, a, c, i) == Some{o}: Maybe<&2, Out>
} -> {Chain.out(~M, b, c, i) == Some{o}: Maybe<&2, Out>}:
  Shared.Maybe.bind_kept(
    List<&2, U32>,
    Out,
    Line.get(~M, a, c, Log.out(i)),
    Line.get(~M, b, c, Log.out(i)),
    ws => Out.read(ws),
    ws => Out.read(ws),
    o,
    w => hk(c)(Log.out(i))(w),
    w => e => e
  )

# the version of a number that a line holds, it holds in a node that keeps
# its logs
def Chain.version.kept(
  ~M: Machine(),
  a: Node<Machine.Q(M)>,
  b: Node<Machine.Q(M)>,
  +c: Ledgers.Chain,
  +n: U32,
  -x: Version,
  hk: Node.Keeps(~M, a, b)
) -> {
  Chain.version(~M, a, c, n) == Some{x}: Maybe<&2, Version>
} -> {Chain.version(~M, b, c, n) == Some{x}: Maybe<&2, Version>}:
  Shared.Maybe.bind_kept(
    List<&2, U32>,
    Version,
    Line.get(~M, a, c, Log.version(n)),
    Line.get(~M, b, c, Log.version(n)),
    ws => Version.read(ws),
    ws => Version.read(ws),
    x,
    w => hk(c)(Log.version(n))(w),
    w => e => e
  )

# a mark that a line holds, it holds in a node that keeps its logs
def Chain.mark.kept(
  ~M: Machine(),
  a: Node<Machine.Q(M)>,
  b: Node<Machine.Q(M)>,
  +c: Ledgers.Chain,
  +m: String,
  -v: Ledgers.Id,
  hk: Node.Keeps(~M, a, b)
) -> {
  Chain.mark(~M, a, c, m) == Some{v}: Maybe<&2, Ledgers.Id>
} -> {Chain.mark(~M, b, c, m) == Some{v}: Maybe<&2, Ledgers.Id>}:
  Shared.Maybe.bind_kept(
    List<&2, U32>,
    Ledgers.Id,
    Line.get(~M, a, c, Log.mark(m)),
    Line.get(~M, b, c, Log.mark(m)),
    ws => Read.whole(Ledgers.Id, Ledgers.Id.code.read(ws)),
    ws => Read.whole(Ledgers.Id, Ledgers.Id.code.read(ws)),
    v,
    w => hk(c)(Log.mark(m))(w),
    w => e => e
  )

# a cell that is kept is the same cell
def Cell.kept.eq(
  ~M: Machine(),
  c: Cells.Cell<Ledgers.Entry<Machine.Q(M)>>,
  mb: Maybe<&2, Cells.Cell<Ledgers.Entry<Machine.Q(M)>>>
) -> {
  Cells.Cell.keeps(
    ~Ledgers.Entry<Machine.Q(M)>,
    ~Ledgers.Entry.is_eq(~Machine.Q(M), ~Machine.same(M)),
    Some{c},
    mb
  )
    == True{}: Bool
} -> {mb == Some{c}: Maybe<&2, Cells.Cell<Ledgers.Entry<Machine.Q(M)>>>}:
  match c mb:
    case Cells.One{x} y:
      Cells.Cell.keeps_value(
        ~Ledgers.Entry<Machine.Q(M)>,
        ~Ledgers.Entry.is_eq(~Machine.Q(M), ~Machine.same(M)),
        ~Ledgers.Entry.laws(~Machine.Q(M), ~Machine.same(M), ~Machine.laws(M)),
        x,
        y
      )
    case Cells.Many{} Some{Cells.Many{}}:
      h => {==}
    case Cells.Many{} Some{Cells.One{y}}:
      h => Empty.absurd(
        {
          Some{Cells.One{y}} == Some{Cells.Many{}}: Maybe<&2, Cells.Cell<Ledgers.Entry<Machine.Q(M)>>>
        },
        Shared.Bool.false_ne_true(h)
      )
    case Cells.Many{} None{}:
      h => Empty.absurd(
        {None{} == Some{Cells.Many{}}: Maybe<&2, Cells.Cell<Ledgers.Entry<Machine.Q(M)>>>},
        Shared.Bool.false_ne_true(h)
      )

# a head one height up has a tip
def Up.held(
  z: Head,
  y: Hashes.Hash
) -> {Head.held(Some{Head.up(z, y)}) == True{}: Bool}:
  match z:
    case Head{r, b, n, th}:
      {==}

# Moved.held once the tip m that the step names is known
def Moved.held.at(
  z: Head,
  m: Maybe<&2, Hashes.Hash>,
  -h: Head
) -> {
  Maybe.bind(
    &2,
    Hashes.Hash,
    Head,
    m,
    y => Some{Head.up(z, y)}
  )
    == Some{h}: Maybe<&2, Head>
} -> {Head.held(Some{h}) == True{}: Bool}:
  match m:
    case None{}:
      e => Empty.absurd(
        {Head.held(Some{h}) == True{}: Bool},
        Shared.Maybe.none_ne_some(Head, h, e)
      )
    case Some{y}:
      e =>
        %e: {Head.held(_) == True{}: Bool}
        Up.held(z, y)

# a head that a step moved has a tip
def Moved.held(
  z: Head,
  va: Maybe<&2, Ledgers.Vote>,
  -h: Head
) -> {
  Head.moved(z, va) == Some{h}: Maybe<&2, Head>
} -> {Head.held(Some{h}) == True{}: Bool}:
  Moved.held.at(z, Vote.tip(va), h)

# Held.at for one more step, once the head m before it is known
def Held.at.step(
  ~M: Machine(),
  s: Node<Machine.Q(M)>,
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
    +x => Head.moved(x, Advance.in(~M, s, c, x, r))
  )
    == Some{h}: Maybe<&2, Head>
} -> {Head.held(Some{h}) == True{}: Bool}:
  match m:
    case None{}:
      e => Empty.absurd(
        {Head.held(Some{h}) == True{}: Bool},
        Shared.Maybe.none_ne_some(Head, h, e)
      )
    case Some{+z}:
      e => Moved.held(z, Advance.in(~M, s, c, z, r), h)(e)

# a head that is some decided steps from a head with a tip has a tip
def Held.at(
  ~M: Machine(),
  rs: List<&2, Nat>,
  +s: Node<Machine.Q(M)>,
  +c: Ledgers.Chain,
  h0: Head,
  -h: Head
) -> {
  Head.held(Some{h0}) == True{}: Bool
} -> {
  Line.at(~M, rs, s, c, h0) == Some{h}: Maybe<&2, Head>
} -> {Head.held(Some{h}) == True{}: Bool}:
  match rs:
    case Nil{}:
      t0 => e =>
        %e: {Head.held(_) == True{}: Bool}
        t0
    case Con{r, rest}:
      t0 => e => Held.at.step(~M, s, c, r, h, Line.at(~M, rest, s, c, h0))(e)

# a node is on its own paths
def Path.refl(~M: Machine(), -s: Node<Machine.Q(M)>) -> Node.On(~M, s, s):
  c => h0 => t0 => ra => ra

# paths compose
def Path.trans(
  ~M: Machine(),
  -a: Node<Machine.Q(M)>,
  -b: Node<Machine.Q(M)>,
  -d: Node<Machine.Q(M)>,
  h1: Node.On(~M, a, b),
  h2: Node.On(~M, b, d)
) -> Node.On(~M, a, d):
  +c => +h0 => +t0 => ra => h2(c)(h0)(t0)(h1(c)(h0)(t0)(ra))

# one of two nodes, each on the paths of s
def Path.when(
  ~M: Machine(),
  b: Bool,
  -s: Node<Machine.Q(M)>,
  -x: Node<Machine.Q(M)>,
  -y: Node<Machine.Q(M)>,
  hx: Node.On(~M, s, x),
  hy: Node.On(~M, s, y)
) -> Node.On(~M, s, Shared.Bool.when(Node<Machine.Q(M)>, b, u => x, u => y)):
  match b:
    case True{}:
      hx
    case False{}:
      hy

# the head of another line, after the head of the line c is set
def Head.other(
  ~M: Machine(),
  a: Node<Machine.Q(M)>,
  b0: Node<Machine.Q(M)>,
  c: Ledgers.Chain,
  hd: Head,
  c2: Ledgers.Chain,
  eh: {State.heads(~M, a) == State.heads(~M, b0): Tries.Trie<Head>},
  ebs: {Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)) == False{}: Bool}
) -> {
  Node.head_of(~M, 
    a,
    c2
  )
    == Node.head_of(~M, State.head(~M, b0, c, hd), c2): Maybe<&2, Head>
}:
  Equal.trans(
    Maybe<&2, Head>,
    Node.head_of(~M, a, c2),
    Node.head_of(~M, b0, c2),
    Node.head_of(~M, State.head(~M, b0, c, hd), c2),
    Equal.cong(
      Tries.Trie<Head>,
      Maybe<&2, Head>,
      hs => Tries.Trie.get(Head, hs, Ledgers.Chain.key(c2)),
      State.heads(~M, a),
      State.heads(~M, b0),
      eh
    ),
    Equal.sym(
      Maybe<&2, Head>,
      Node.head_of(~M, State.head(~M, b0, c, hd), c2),
      Node.head_of(~M, b0, c2),
      Equal.trans(
        Maybe<&2, Head>,
        Node.head_of(~M, State.head(~M, b0, c, hd), c2),
        Bool.pick(
          Maybe<&2, Head>,
          Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
          Some{hd},
          Node.head_of(~M, b0, c2)
        ),
        Node.head_of(~M, b0, c2),
        Head.of_set(~M, b0, c, hd, c2),
        Pick.of(
          Maybe<&2, Head>,
          False{},
          Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
          Some{hd},
          Node.head_of(~M, b0, c2),
          ebs
        )
      )
    )
  )

# the head of a line with the key of the line c, after the head of c is set
def Head.this(
  ~M: Machine(),
  b0: Node<Machine.Q(M)>,
  c: Ledgers.Chain,
  hd: Head,
  c2: Ledgers.Chain,
  ebs: {Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)) == True{}: Bool}
) -> {Node.head_of(~M, State.head(~M, b0, c, hd), c2) == Some{hd}: Maybe<&2, Head>}:
  Equal.trans(
    Maybe<&2, Head>,
    Node.head_of(~M, State.head(~M, b0, c, hd), c2),
    Bool.pick(
      Maybe<&2, Head>,
      Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
      Some{hd},
      Node.head_of(~M, b0, c2)
    ),
    Some{hd},
    Head.of_set(~M, b0, c, hd, c2),
    Pick.of(
      Maybe<&2, Head>,
      True{},
      Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
      Some{hd},
      Node.head_of(~M, b0, c2),
      ebs
    )
  )

# lines with the same key have the same head
def Head.keyed(
  ~M: Machine(),
  a: Node<Machine.Q(M)>,
  c2: Ledgers.Chain,
  c: Ledgers.Chain,
  ek: {Ledgers.Chain.key(c2) == Ledgers.Chain.key(c): List<&2, Bool>}
) -> {Node.head_of(~M, a, c2) == Node.head_of(~M, a, c): Maybe<&2, Head>}:
  Equal.cong(
    List<&2, Bool>,
    Maybe<&2, Head>,
    kk => Tries.Trie.get(Head, State.heads(~M, a), kk),
    Ledgers.Chain.key(c2),
    Ledgers.Chain.key(c),
    ek
  )

# lines with the same key have the same decided steps
def In.key(
  ~M: Machine(),
  s: Node<Machine.Q(M)>,
  c2: Ledgers.Chain,
  c: Ledgers.Chain,
  x: Head,
  r: Nat,
  ek: {Ledgers.Chain.key(c2) == Ledgers.Chain.key(c): List<&2, Bool>}
) -> {Advance.in(~M, s, c2, x, r) == Advance.in(~M, s, c, x, r): Maybe<&2, Ledgers.Vote>}:
  Equal.cong(
    List<&2, Bool>,
    Maybe<&2, Ledgers.Vote>,
    kk => Maybe.bind(
      &2,
      Tip,
      Ledgers.Vote,
      Head.tip(~M, s, x),
      t => Ledgers.Bucket.decide(
        ~Machine.Q(M),
        Ledgers.State.under(
          ~Machine.Q(M),
          State.ledger(~M, s),
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
  ~M: Machine(),
  +a: Node<Machine.Q(M)>,
  c: Ledgers.Chain,
  +c2: Ledgers.Chain,
  h0: Head,
  ek: {Ledgers.Chain.key(c2) == Ledgers.Chain.key(c): List<&2, Bool>},
  nh: {Head.held(Node.head_of(~M, a, c)) == False{}: Bool},
  t0: {Head.held(Some{h0}) == True{}: Bool},
  ra: Line.Reach(~M, a, c2, h0)
) -> Empty:
  match ra:
    case Tuple{rs, Tuple{h, Tuple{e1, e2}}}:
      Shared.Bool.false_ne_true(
        Equal.trans(
          Bool,
          False{},
          Head.held(Node.head_of(~M, a, c)),
          True{},
          Equal.sym(Bool, Head.held(Node.head_of(~M, a, c)), False{}, nh),
          Equal.trans(
            Bool,
            Head.held(Node.head_of(~M, a, c)),
            Head.held(Some{h}),
            True{},
            Equal.cong(
              Maybe<&2, Head>,
              Bool,
              Head.held,
              Node.head_of(~M, a, c),
              Some{h},
              Equal.trans(
                Maybe<&2, Head>,
                Node.head_of(~M, a, c),
                Node.head_of(~M, a, c2),
                Some{h},
                Equal.sym(
                  Maybe<&2, Head>,
                  Node.head_of(~M, a, c2),
                  Node.head_of(~M, a, c),
                  Head.keyed(~M, a, c2, c, ek)
                ),
                e1
              )
            ),
            Held.at(~M, rs, a, c2, h0, h)(t0)(e2)
          )
        )
      )

# a head with no tip is not held
def Held.not(
  ~M: Machine(),
  s: Node<Machine.Q(M)>,
  c: Ledgers.Chain,
  m: Maybe<&2, Head>,
  em: {Node.head_of(~M, s, c) == m: Maybe<&2, Head>}
) -> {Head.held(Node.head_of(~M, s, c)) == Head.held(m): Bool}:
  Equal.cong(Maybe<&2, Head>, Bool, Head.held, Node.head_of(~M, s, c), m, em)

# a new ledger keeps the waiting requests
def Waiting.led(
  ~M: Machine(),
  s: Node<Machine.Q(M)>,
  l: Ledgers.State(Machine.Q(M))
) -> {
  State.waiting(~M, 
    s
  )
    == State.waiting(~M, State.led(~M, s, l)): Tries.Trie<List<&2, Ledgers.Id>>
}:
  match s:
    case Node{old, hs, ws, ks}:
      {==}

# new keys keep the waiting requests
def Waiting.keyed(
  ~M: Machine(),
  s: Node<Machine.Q(M)>,
  ks: Keys
) -> {
  State.waiting(~M, 
    s
  )
    == State.waiting(~M, State.keyed(~M, s, ks)): Tries.Trie<List<&2, Ledgers.Id>>
}:
  match s:
    case Node{l, hs, ws, old}:
      {==}

# the waiting requests of the node m, if any, else of s
def Waiting.of(~M: Machine(), s: Node<Machine.Q(M)>, m: Maybe<&2, Node<Machine.Q(M)>>) -> Tries.Trie<List<&2, Ledgers.Id>>:
  match m:
    case None{}:
      State.waiting(~M, s)
    case Some{s2}:
      State.waiting(~M, s2)

# a node that is kept when b holds has the waiting requests of s, when it has
def Waiting.some.if(
  ~M: Machine(),
  b: Bool,
  -s: Node<Machine.Q(M)>,
  -x: Node<Machine.Q(M)>,
  hx: {State.waiting(~M, s) == State.waiting(~M, x): Tries.Trie<List<&2, Ledgers.Id>>}
) -> {
  State.waiting(~M, 
    s
  )
    == Waiting.of(~M, 
      s,
      Shared.Maybe.when(Node<Machine.Q(M)>, b, u => Some{x})
    ): Tries.Trie<List<&2, Ledgers.Id>>
}:
  match b:
    case True{}:
      hx
    case False{}:
      {==}

# a ballot that a node accepts keeps the waiting requests
def Accept.at.waiting(
  ~M: Machine(),
  +s: Node<Machine.Q(M)>,
  +b: Ledgers.Ballot,
  m: Maybe<&2, Keychain>
) -> {
  State.waiting(~M, 
    s
  )
    == Waiting.of(~M, s, Seal.accept.at(~M, s, b, m)): Tries.Trie<List<&2, Ledgers.Id>>
}:
  match m:
    case None{}:
      {==}
    case Some{+c}:
      Waiting.some.if(~M, 
        Seal.fits(c, b),
        s,
        State.keyed(~M, 
          State.led(~M, 
            s,
            Ledgers.State.keep(~Machine.Q(M), ~Machine.same(M), State.ledger(~M, s), b)
          ),
          Keys.saw(
            Keys.set(
              State.keys(~M, s),
              Seal.slot(Ballot.store(b), Ballot.node(b)),
              Keychain.next(c, b)
            ),
            Ballot.at(b)
          )
        ),
        Equal.trans(
          Tries.Trie<List<&2, Ledgers.Id>>,
          State.waiting(~M, s),
          State.waiting(~M, 
            State.led(~M, 
              s,
              Ledgers.State.keep(~Machine.Q(M), ~Machine.same(M), State.ledger(~M, s), b)
            )
          ),
          State.waiting(~M, 
            State.keyed(~M, 
              State.led(~M, 
                s,
                Ledgers.State.keep(~Machine.Q(M), ~Machine.same(M), State.ledger(~M, s), b)
              ),
              Keys.saw(
                Keys.set(
                  State.keys(~M, s),
                  Seal.slot(Ballot.store(b), Ballot.node(b)),
                  Keychain.next(c, b)
                ),
                Ballot.at(b)
              )
            )
          ),
          Waiting.led(~M, 
            s,
            Ledgers.State.keep(~Machine.Q(M), ~Machine.same(M), State.ledger(~M, s), b)
          ),
          Waiting.keyed(~M, 
            State.led(~M, 
              s,
              Ledgers.State.keep(~Machine.Q(M), ~Machine.same(M), State.ledger(~M, s), b)
            ),
            Keys.saw(
              Keys.set(
                State.keys(~M, s),
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
  ~M: Machine(),
  -s: Node<Machine.Q(M)>,
  m: Maybe<&2, Node<Machine.Q(M)>>,
  -k: Node<Machine.Q(M)> -> Node<Machine.Q(M)>,
  ih: @s2: Node<Machine.Q(M)> -> {
    State.waiting(~M, s2) == State.waiting(~M, k(s2)): Tries.Trie<List<&2, Ledgers.Id>>
  }
) -> {
  State.waiting(~M, s) == Waiting.of(~M, s, m): Tries.Trie<List<&2, Ledgers.Id>>
} -> {
  State.waiting(~M, 
    s
  )
    == State.waiting(~M, 
      Maybe.default(
        &2,
        Node<Machine.Q(M)>,
        Maybe.bind(&2, Node<Machine.Q(M)>, Node<Machine.Q(M)>, m, s2 => Some{k(s2)}),
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
        State.waiting(~M, s),
        State.waiting(~M, s2),
        State.waiting(~M, k(s2)),
        e,
        ih(s2)
      )

# the ballots that a chain leads to keep the waiting requests
def Follow.waiting(
  ~K: Kernel(),
  f: Nat,
  +s: Node<Machine.Q(Kernel.machine(K))>,
  +p: Tries.Trie<Ledgers.Ballot>,
  +r: Ledgers.Id,
  +n: String,
  mb: Maybe<&2, Ledgers.Ballot>
) -> {
  State.waiting(~Kernel.machine(K), 
    s
  )
    == State.waiting(~Kernel.machine(K), 
      Sealed.follow(~K, f, s, p, r, n, mb)
    ): Tries.Trie<List<&2, Ledgers.Id>>
}:
  match f mb:
    case 0n x:
      {==}
    case 1n+g None{}:
      {==}
    case 1n+(+g) Some{+b}:
      Follow.step.waiting(~Kernel.machine(K), 
        s,
        Seal.accept(~K, s, b),
        +s2 => Sealed.follow(~K, g, s2, p, r, n, Pending.next(~K, s2, p, r, n)),
        +s2 => Follow.waiting(~K, g, s2, p, r, n, Pending.next(~K, s2, p, r, n))
      )(
        Accept.at.waiting(~Kernel.machine(K), 
          s,
          b,
          Seal.chain(~K, s, Ballot.store(b), Ballot.node(b))
        )
      )

# the ballots that the chains of some ballots lead to keep the waiting requests
def Each.waiting(
  ~K: Kernel(),
  +f: Nat,
  bs: List<&2, Ledgers.Ballot>,
  +p: Tries.Trie<Ledgers.Ballot>,
  +s: Node<Machine.Q(Kernel.machine(K))>
) -> {
  State.waiting(~Kernel.machine(K), 
    s
  )
    == State.waiting(~Kernel.machine(K), Sealed.each(~K, f, bs, p, s)): Tries.Trie<List<&2, Ledgers.Id>>
}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, rest}:
      s1 = Sealed.follow(~K, 
        f,
        s,
        p,
        Ballot.store(b),
        Ballot.node(b),
        Pending.next(~K, s, p, Ballot.store(b), Ballot.node(b))
      )
      Equal.trans(
        Tries.Trie<List<&2, Ledgers.Id>>,
        State.waiting(~Kernel.machine(K), s),
        State.waiting(~Kernel.machine(K), s1),
        State.waiting(~Kernel.machine(K), Sealed.each(~K, f, rest, p, s1)),
        Follow.waiting(~K, 
          f,
          s,
          p,
          Ballot.store(b),
          Ballot.node(b),
          Pending.next(~K, s, p, Ballot.store(b), Ballot.node(b))
        ),
        Each.waiting(~K, f, rest, p, s1)
      )

# a new head keeps the waiting requests
def Waiting.head(
  ~M: Machine(),
  +s: Node<Machine.Q(M)>,
  c: Ledgers.Chain,
  h: Head
) -> {
  State.waiting(~M, 
    s
  )
    == State.waiting(~M, State.head(~M, s, c, h)): Tries.Trie<List<&2, Ledgers.Id>>
}:
  match s:
    case Node{l, hs, ws, ks}:
      {==}

# a first head keeps the waiting requests
def First.at.waiting(
  ~M: Machine(),
  s: Node<Machine.Q(M)>,
  c: Ledgers.Chain,
  h: Head,
  +m: Maybe<&2, Head>
) -> {
  State.waiting(~M, 
    s
  )
    == State.waiting(~M, First.at(~M, s, c, h, m)): Tries.Trie<List<&2, Ledgers.Id>>
}:
  match m:
    case Some{Head{r, b, n, Some{t}}}:
      {==}
    case Some{Head{r, b, n, None{}}}:
      Waiting.head(~M, s, c, h)
    case None{}:
      Waiting.head(~M, s, c, h)

# the first head of a store keeps the waiting requests
def Start.head.waiting(
  ~M: Machine(),
  +s: Node<Machine.Q(M)>,
  m: Maybe<&2, Node<Machine.Q(M)>>,
  +c: Ledgers.Chain,
  h: Head
) -> {
  State.waiting(~M, 
    s
  )
    == State.waiting(~M, Start.head(~M, s, m, c, h)): Tries.Trie<List<&2, Ledgers.Id>>
}:
  match m:
    case None{}:
      {==}
    case Some{+s2}:
      Equal.trans(
        Tries.Trie<List<&2, Ledgers.Id>>,
        State.waiting(~M, s),
        State.waiting(~M, State.led(~M, s, State.ledger(~M, s2))),
        State.waiting(~M, 
          State.first(~M, State.led(~M, s, State.ledger(~M, s2)), c, h)
        ),
        Waiting.led(~M, s, State.ledger(~M, s2)),
        First.at.waiting(~M, 
          State.led(~M, s, State.ledger(~M, s2)),
          c,
          h,
          Node.head_of(~M, State.led(~M, s, State.ledger(~M, s2)), c)
        )
      )

# a store that starts keeps the waiting requests, once its content m is known
def Start.with.waiting(
  ~M: Machine(),
  s: Node<Machine.Q(M)>,
  +i: Ledgers.Id,
  +os: List<&2, String>,
  +m: Maybe<&2, Work<Machine.Q(M)>>
) -> {
  State.waiting(~M, 
    s
  )
    == State.waiting(~M, Start.with(~M, s, i, os, m)): Tries.Trie<List<&2, Ledgers.Id>>
}:
  match m:
    case None{}:
      {==}
    case Some{Work{s2, +c}}:
      Start.head.waiting(~M, 
        s,
        State.put(~M, s2, [Tip.words(Tip{c, None{}, 0, os})]),
        Ledgers.Chain{i, None{}},
        Head{i, None{}, 0, Some{Tip.hash(Tip{c, None{}, 0, os})}}
      )

# a line that a node starts to follow keeps the waiting requests
def Follow.new.waiting(
  ~M: Machine(),
  s: Node<Machine.Q(M)>,
  +r: Ledgers.Id,
  +l: Maybe<&2, String>,
  +m: Maybe<&2, Head>
) -> {
  State.waiting(~M, 
    s
  )
    == State.waiting(~M, Follow.new(~M, s, r, l, m)): Tries.Trie<List<&2, Ledgers.Id>>
}:
  match m:
    case Some{h}:
      {==}
    case None{}:
      Waiting.head(~M, s, Line.chain(r, l), Head{r, l, 0, None{}})

# nodes with the same waiting requests have the same ones on each line
def Wait.same(
  ~M: Machine(),
  a: Node<Machine.Q(M)>,
  b: Node<Machine.Q(M)>,
  c: Ledgers.Chain,
  e: {State.waiting(~M, a) == State.waiting(~M, b): Tries.Trie<List<&2, Ledgers.Id>>}
) -> {Wait.of(~M, a, c) == Wait.of(~M, b, c): List<&2, Ledgers.Id>}:
  Equal.cong(
    Tries.Trie<List<&2, Ledgers.Id>>,
    List<&2, Ledgers.Id>,
    ws => Maybe.default(
      &2,
      List<&2, Ledgers.Id>,
      Tries.Trie.get(List<&2, Ledgers.Id>, ws, Ledgers.Chain.key(c)),
      []
    ),
    State.waiting(~M, a),
    State.waiting(~M, b),
    e
  )

# lines with the same key have the same waiting requests
def Wait.keyed(
  ~M: Machine(),
  s: Node<Machine.Q(M)>,
  c2: Ledgers.Chain,
  c: Ledgers.Chain,
  ek: {Ledgers.Chain.key(c2) == Ledgers.Chain.key(c): List<&2, Bool>}
) -> {Wait.of(~M, s, c2) == Wait.of(~M, s, c): List<&2, Ledgers.Id>}:
  Equal.cong(
    List<&2, Bool>,
    List<&2, Ledgers.Id>,
    kk => Maybe.default(
      &2,
      List<&2, Ledgers.Id>,
      Tries.Trie.get(List<&2, Ledgers.Id>, State.waiting(~M, s), kk),
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
  ~M: Machine(),
  +s: Node<Machine.Q(M)>,
  +c: Ledgers.Chain,
  +x: Ledgers.Id,
  +r: List<&2, Ledgers.Id>,
  +c2: Ledgers.Chain
) -> {
  Wait.of(~M, 
    Wait.set(~M, s, c, x <> r),
    c2
  )
    == Bool.pick(
      List<&2, Ledgers.Id>,
      Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
      x <> r,
      Wait.of(~M, s, c2)
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

# Wait.wait for any requests ys that waited on the line c
def Wait.wait.at(
  ~M: Machine(),
  s: Node<Machine.Q(M)>,
  c: Ledgers.Chain,
  j: Ledgers.Id,
  c2: Ledgers.Chain,
  +ys: List<&2, Ledgers.Id>
) -> {
  Wait.of(~M, 
    Wait.set(~M, s, c, List.append(&2, Ledgers.Id, ys, [j])),
    c2
  )
    == Bool.pick(
      List<&2, Ledgers.Id>,
      Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
      List.append(&2, Ledgers.Id, ys, [j]),
      Wait.of(~M, s, c2)
    ): List<&2, Ledgers.Id>
}:
  match ys:
    case Nil{}:
      Wait.set.of(~M, s, c, j, [], c2)
    case Con{x, r}:
      Wait.set.of(~M, s, c, x, List.append(&2, Ledgers.Id, r, [j]), c2)

# the requests that wait on a line, after one more waits on the line c
def Wait.wait(
  ~M: Machine(),
  +s: Node<Machine.Q(M)>,
  +c: Ledgers.Chain,
  j: Ledgers.Id,
  c2: Ledgers.Chain
) -> {
  Wait.of(~M, 
    State.wait(~M, s, c, j),
    c2
  )
    == Bool.pick(
      List<&2, Ledgers.Id>,
      Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
      List.append(&2, Ledgers.Id, Wait.of(~M, s, c), [j]),
      Wait.of(~M, s, c2)
    ): List<&2, Ledgers.Id>
}:
  Wait.wait.at(~M, s, c, j, c2, Wait.of(~M, s, c))

# Wait.keeps once it is known whether the line has the key of c (b)
def Wait.keeps.if(
  ~M: Machine(),
  +s: Node<Machine.Q(M)>,
  +c: Ledgers.Chain,
  j: Ledgers.Id,
  +c2: Ledgers.Chain,
  i: Ledgers.Id,
  +b: Bool,
  eb: {Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)) == b: Bool},
  h: {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, Wait.of(~M, s, c2), i) == True{}: Bool}
) -> {
  List.contains(
    ~Ledgers.Id,
    ~Ledgers.Id.is_eq,
    Bool.pick(
      List<&2, Ledgers.Id>,
      b,
      List.append(&2, Ledgers.Id, Wait.of(~M, s, c), [j]),
      Wait.of(~M, s, c2)
    ),
    i
  )
    == True{}: Bool
}:
  match b:
    case True{}:
      Shared.List.contains_left(~Ledgers.Id, ~Ledgers.Id.is_eq, Wait.of(~M, s, c), [j], i, (
          %Wait.keyed(~M, s, c2, c, Key.same(c2, c)(eb)): {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, _, i) == True{}: Bool}
          h))
    case False{}:
      h

# a request that waits on a line waits there after one more waits on a line
def Wait.keeps(
  ~M: Machine(),
  +s: Node<Machine.Q(M)>,
  +c: Ledgers.Chain,
  +j: Ledgers.Id,
  +c2: Ledgers.Chain,
  i: Ledgers.Id,
  h: {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, Wait.of(~M, s, c2), i) == True{}: Bool}
) -> {
  List.contains(
    ~Ledgers.Id,
    ~Ledgers.Id.is_eq,
    Wait.of(~M, State.wait(~M, s, c, j), c2),
    i
  )
    == True{}: Bool
}:
  %Equal.sym(
    List<&2, Ledgers.Id>,
    Wait.of(~M, State.wait(~M, s, c, j), c2),
    Bool.pick(
      List<&2, Ledgers.Id>,
      Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
      List.append(&2, Ledgers.Id, Wait.of(~M, s, c), [j]),
      Wait.of(~M, s, c2)
    ),
    Wait.wait(~M, s, c, j, c2)
  ): {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, _, i) == True{}: Bool}
  Wait.keeps.if(~M, 
    s,
    c,
    j,
    c2,
    i,
    Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
    {==},
    h
  )

# a list of one is a member of itself
def Contains.one(
  j: Ledgers.Id
) -> {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, [j], j) == True{}: Bool}:
  %Equal.sym(
    Bool,
    Ledgers.Id.is_eq(j, j),
    True{},
    Ledgers.Id.is_eq_refl(j)
  ): {List.any.if(u => List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, [], j), _) == True{}: Bool}
  {==}

# a request waits on its line once it waits there
def Wait.adds(
  ~M: Machine(),
  +s: Node<Machine.Q(M)>,
  +c: Ledgers.Chain,
  +j: Ledgers.Id
) -> {
  List.contains(
    ~Ledgers.Id,
    ~Ledgers.Id.is_eq,
    Wait.of(~M, State.wait(~M, s, c, j), c),
    j
  )
    == True{}: Bool
}:
  %Equal.sym(
    List<&2, Ledgers.Id>,
    Wait.of(~M, State.wait(~M, s, c, j), c),
    Bool.pick(
      List<&2, Ledgers.Id>,
      Tries.Trie.same_key(Ledgers.Chain.key(c), Ledgers.Chain.key(c)),
      List.append(&2, Ledgers.Id, Wait.of(~M, s, c), [j]),
      Wait.of(~M, s, c)
    ),
    Wait.wait(~M, s, c, j, c)
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
        List.append(&2, Ledgers.Id, Wait.of(~M, s, c), [j]),
        Wait.of(~M, s, c)
      ),
      j
    )
      == True{}: Bool
  }
  Shared.List.contains_right(
    ~Ledgers.Id,
    ~Ledgers.Id.is_eq,
    Wait.of(~M, s, c),
    [j],
    j,
    Contains.one(j)
  )

# one of two nodes, on each of which the request i waits on the line c2
def Contains.when(
  ~M: Machine(),
  +b: Bool,
  -x: Node<Machine.Q(M)>,
  -y: Node<Machine.Q(M)>,
  -c2: Ledgers.Chain,
  -i: Ledgers.Id,
  hx: {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, Wait.of(~M, x, c2), i) == True{}: Bool},
  hy: {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, Wait.of(~M, y, c2), i) == True{}: Bool}
) -> {
  List.contains(
    ~Ledgers.Id,
    ~Ledgers.Id.is_eq,
    Wait.of(~M, Shared.Bool.when(Node<Machine.Q(M)>, b, u => x, u => y), c2),
    i
  )
    == True{}: Bool
}:
  match b:
    case True{}:
      hx
    case False{}:
      hy

# a request, and who asks for it
type Request<-Q: Data> is Data:
  Request{envelope: Envelope, ask: Q}

# s, after the node n took in the request m, if any
def Adopt.ask(~K: Kernel(), n: String, s: Node<Machine.Q(Kernel.machine(K))>, m: Maybe<&2, Request<Machine.Q(Kernel.machine(K))>>) -> Node<Machine.Q(Kernel.machine(K))>:
  match m:
    case None{}:
      s
    case Some{Request{e, q}}:
      Node.ask(~K, n, s, e, q)

# s, after the node n asked for the adoption of the line l of the store r, if
# its owners are not the nodes inside its owner group
def Node.adopt(~K: Kernel(), n: String, +s: Node<Machine.Q(Kernel.machine(K))>, r: Ledgers.Id, l: Maybe<&2, String>) -> Node<Machine.Q(Kernel.machine(K))>:
  Adopt.ask(~K, n, s, Kernel.follow(K)(s)(r)(l))

# Adopt.at once the head m of the line is known
def Adopt.head(~K: Kernel(), n: String, s: Node<Machine.Q(Kernel.machine(K))>, m: Maybe<&2, Head>) -> Node<Machine.Q(Kernel.machine(K))>:
  match m:
    case None{}:
      s
    case Some{Head{r, b, next, t}}:
      Node.adopt(~K, n, s, r, b)

# s, after the node n asked for the adoption of the line c, if s follows c:
# a change of a group reaches each line that the group owns by a step of the
# line, which a node asks for by itself when it works on the line
def Adopt.at(~K: Kernel(), n: String, +s: Node<Machine.Q(Kernel.machine(K))>, c: Ledgers.Chain) -> Node<Machine.Q(Kernel.machine(K))>:
  Adopt.head(~K, n, s, Node.head_of(~Kernel.machine(K), s, c))

# Adopt.at for the line m, if any
def Adopt.maybe(~K: Kernel(), n: String, s: Node<Machine.Q(Kernel.machine(K))>, m: Maybe<&2, Ledgers.Chain>) -> Node<Machine.Q(Kernel.machine(K))>:
  match m:
    case None{}:
      s
    case Some{c}:
      Adopt.at(~K, n, s, c)

# s, after the node n asked for the adoption of each of the lines cs
def Node.adopts(~K: Kernel(), +n: String, cs: List<&2, Ledgers.Chain>, s: Node<Machine.Q(Kernel.machine(K))>) -> Node<Machine.Q(Kernel.machine(K))>:
  match cs:
    case Nil{}:
      s
    case Con{c, rest}:
      Node.adopts(~K, n, rest, Adopt.at(~K, n, s, c))

# the heads of each of the lines cs are at the same height in a and in b
def Lines.level(~M: Machine(), cs: List<&2, Ledgers.Chain>, +a: Node<Machine.Q(M)>, +b: Node<Machine.Q(M)>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{+c, r}:
      List.all.if(
        u => Lines.level(~M, r, a, b),
        Heads.level(Node.head_of(~M, a, c), Node.head_of(~M, b, c))
      )

# s, after it took the ballots bs (k of them, pd by where each waits) in again
# and did what it can on the lines cs, until no head moves, f times at most. A ballot whose key the store gives
# at a later height is kept once the node is there: one sync catches up over
# each change of a key
def Sync.more(
  ~K: Kernel(),
  f: Nat,
  +n: String,
  +cs: List<&2, Ledgers.Chain>,
  +k: Nat,
  +bs: List<&2, Ledgers.Ballot>,
  +pd: Tries.Trie<Ledgers.Ballot>,
  +s: Node<Machine.Q(Kernel.machine(K))>
) -> Node<Machine.Q(Kernel.machine(K))>:
  match f:
    case 0n:
      s
    case 1n+p:
      +s2 = Node.steps(~K, n, cs, Sealed.each(~K, k, bs, pd, s))
      Shared.Bool.when(
        Node<Machine.Q(Kernel.machine(K))>,
        Lines.level(~Kernel.machine(K), cs, s, s2),
        u => s2,
        u => Sync.more(~K, p, n, cs, k, bs, pd, s2)
      )

# s, after the node n took in t, which another node sent, did what it can on
# each line that this may move, and asked for the adoption of each: how a
# node that is behind catches up
def Node.sync(~K: Kernel(), +n: String, +s: Node<Machine.Q(Kernel.machine(K))>, +t: Ledgers.State(Machine.Q(Kernel.machine(K)))) -> Node<Machine.Q(Kernel.machine(K))>:
  +s1 = Node.take(~K, s, t)
  +cs = Sync.lines(~Kernel.machine(K), s, s1, t)
  +bs = Ballots.of(~Kernel.machine(K), 
    Tries.Trie.values(
      Cells.Cell<Ledgers.Entry<Machine.Q(Kernel.machine(K))>>,
      Ledgers.State.missing(~Machine.Q(Kernel.machine(K)), ~Machine.same(Kernel.machine(K)), t, State.ledger(~Kernel.machine(K), s))
    )
  )
  +k = List.length(&2, Ledgers.Ballot, bs)
  Node.adopts(~K, 
    n,
    cs,
    Sync.more(~K, k, n, cs, k, bs, Pending.of(bs), Node.steps(~K, n, cs, s1))
  )

# the bytes under the root m, if any, when s holds their rope
def Root.bytes(~M: Machine(), s: Node<Machine.Q(M)>, m: Maybe<&2, Ropes.Root>) -> Maybe<&2, Texts.Bytes()>:
  Maybe.bind(&2, Ropes.Root, Texts.Bytes(), m, r => Ropes.Rope.read(~Node<Machine.Q(M)>, ~Store.fetch(~M), s, r))

# x is the byte that ends a line
def Byte.is_end(x: U32) -> Bool:
  U32.is_eq(x, 10)

# the rope of the bytes b, cut after each line: content is stored once by
# hash, and two contents share every part that an edit did not touch
def Bytes.rope(b: Texts.Bytes()) -> Ropes.Put:
  Ropes.Rope.put(Ropes.Rope.cut(~U32, ~Byte.is_end, b))

# s with the bytes b: the nodes of their rope, each under its hash. A node
# keeps new bytes before it asks for a write of their content
def Node.keep(~M: Machine(), s: Node<Machine.Q(M)>, b: Texts.Bytes()) -> Node<Machine.Q(M)>:
  State.keep(~M, s, Ropes.Put.nodes(Bytes.rope(b)))

# bend-lint: expect-begin bend-lint-rules/layout/case@warning -- a constructor is PascalCase, as in Base (Some, Con): the rule reads a constructor as a law
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
# bend-lint: expect-end bend-lint-rules/layout/case@warning

# s, after the node n did ev
def Node.does(~K: Kernel(), +n: String, +s: Node<Machine.Q(Kernel.machine(K))>, ev: Deed<Machine.Q(Kernel.machine(K))>) -> Node<Machine.Q(Kernel.machine(K))>:
  match ev:
    case Deed.Ask{+e, +q}:
      Adopt.at(~K, n, Node.ask(~K, n, s, e, q), Arrival.chain(Envelope.of(e), Machine.arrival(Kernel.machine(K))(q)))
    case Deed.Take{t}:
      Node.take(~K, s, t)
    case Deed.Sync{t}:
      Node.sync(~K, n, s, t)
    case Deed.Keep{b}:
      Node.keep(~Kernel.machine(K), s, b)
    case Deed.Consent{+i}:
      Adopt.maybe(~K, n, Node.consent(~K, n, s, i), Node.chain_of(~Kernel.machine(K), s, i))
    case Deed.Pass{+c}:
      Adopt.at(~K, n, Node.pass(~K, n, s, c), c)

# s, after the node n did each of evs, in order: any later state of the node
def Node.after(~K: Kernel(), +n: String, evs: List<&2, Deed<Machine.Q(Kernel.machine(K))>>, s: Node<Machine.Q(Kernel.machine(K))>) -> Node<Machine.Q(Kernel.machine(K))>:
  match evs:
    case Nil{}:
      s
    case Con{ev, rest}:
      Node.after(~K, n, rest, Node.does(~K, n, s, ev))

# the outcome of the request i (none: no step that the node knows decided it)
def Node.out(~M: Machine(), +s: Node<Machine.Q(M)>, +i: Ledgers.Id) -> Maybe<&2, Out>:
  Maybe.bind(&2, Ledgers.Chain, Out, Node.chain_of(~M, s, i), c => Chain.out(~M, s, c, i))

# the version of the outcome o on the line c, when it took one
def Out.on(~M: Machine(), s: Node<Machine.Q(M)>, c: Ledgers.Chain, o: Out) -> Maybe<&2, Version>:
  match o:
    case Out.Stale{}:
      None{}
    case Out.Taken{n}:
      Chain.version(~M, s, c, n)

# the version that the request v made on the line c
def Chain.made(~M: Machine(), +s: Node<Machine.Q(M)>, +c: Ledgers.Chain, v: Ledgers.Id) -> Maybe<&2, Version>:
  Maybe.bind(&2, Out, Version, Chain.out(~M, s, c, v), o => Out.on(~M, s, c, o))

# the version that the request v made (none: v is not a version that the node
# knows)
def Node.made(~M: Machine(), +s: Node<Machine.Q(M)>, +v: Ledgers.Id) -> Maybe<&2, Version>:
  Maybe.bind(&2, Ledgers.Chain, Version, Node.chain_of(~M, s, v), +c => Chain.made(~M, s, c, v))

# the root of the content of the version v (none: v is not a version)
def Node.root(~M: Machine(), s: Node<Machine.Q(M)>, v: Ledgers.Id) -> Maybe<&2, Maybe<&2, Hashes.Hash>>:
  Maybe.bind(&2, Version, Maybe<&2, Hashes.Hash>, Node.made(~M, s, v), x => Some{Version.root(x)})

# the root of the content of the version m, if any (none, or not a version:
# the empty tree)
def Node.root_of(~M: Machine(), s: Node<Machine.Q(M)>, m: Maybe<&2, Ledgers.Id>) -> Maybe<&2, Hashes.Hash>:
  match m:
    case None{}:
      None{}
    case Some{v}:
      Maybe.bind(&2, Maybe<&2, Hashes.Hash>, Hashes.Hash, Node.root(~M, s, v), h => h)

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
def Place.at(~M: Machine(), s: Node<Machine.Q(M)>, c: Ledgers.Chain, v: Ledgers.Id, t: Tip) -> Maybe<&2, Place>:
  Maybe.bind(&2, Out, Place, Line.out(~M, s, t, v), o => Out.place(c, o))

# the place of the version v on the line c
def Place.on(~M: Machine(), +s: Node<Machine.Q(M)>, +c: Ledgers.Chain, v: Ledgers.Id) -> Maybe<&2, Place>:
  Maybe.bind(&2, Tip, Place, Node.tip(~M, s, c), t => Place.at(~M, s, c, v, t))

# the place of the version v
def Node.place(~M: Machine(), +s: Node<Machine.Q(M)>, +v: Ledgers.Id) -> Maybe<&2, Place>:
  Maybe.bind(&2, Ledgers.Chain, Place, Node.chain_of(~M, s, v), +c => Place.on(~M, s, c, v))

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
  ~K: Kernel(),
  +s: Node<Machine.Q(Kernel.machine(K))>,
  os: List<&2, Owner>,
  +m: Maybe<&2, Work<Machine.Q(Kernel.machine(K))>>
) -> {
  Work.after(~Kernel.machine(K), s, m) == True{}: Bool
} -> {Work.after(~Kernel.machine(K), s, Seal.firsts(~K, os, m)) == True{}: Bool}:
  match os:
    case Nil{}:
      e => e
    case Con{Owner{+n, +k}, r}:
      e => Firsts.after(~K, 
        s,
        r,
        Maybe.bind(
          &2,
          Work<Machine.Q(Kernel.machine(K))>,
          Work<Machine.Q(Kernel.machine(K))>,
          m,
          w => Work.set(~Kernel.machine(K), w, Machine.seal(Kernel.machine(K))(n), Hashes.Hash.code(k, []))
        )
      )(Work.set.after(~Kernel.machine(K), s, m, Machine.seal(Kernel.machine(K))(n), Hashes.Hash.code(k, []))(e))

# a store that starts only grows a node
def Start.grows(
  ~K: Kernel(),
  +s: Node<Machine.Q(Kernel.machine(K))>,
  i: Ledgers.Id,
  +os: List<&2, Owner>
) -> {Node.grows(~Kernel.machine(K), s, Node.start(~K, s, i, os)) == True{}: Bool}:
  Start.with.grows(~Kernel.machine(K), 
    s,
    i,
    Owner.names(os),
    Seal.firsts(~K, os, Some{Work{s, None{}}})
  )(Firsts.after(~K, s, os, Some{Work{s, None{}}})(Grows.refl(~Kernel.machine(K), s)))

# a new request only grows a node
def Arrive.grows(
  ~K: Kernel(),
  +s: Node<Machine.Q(Kernel.machine(K))>,
  +i: Ledgers.Id,
  a: Arrival,
) -> {Node.grows(~Kernel.machine(K), s, Arrive.at(~K, s, i, a)) == True{}: Bool}:
  match a:
    case Arrival.Starts{os}:
      Start.grows(~K, s, i, os)
    case Arrival.Waits{+r, +l}:
      +s1 = Node.follow(~Kernel.machine(K), s, r, l)
      Grows.to(~Kernel.machine(K), 
        s,
        s1,
        State.wait(~Kernel.machine(K), s1, Line.chain(r, l), i),
        Led.waits(~Kernel.machine(K), s1, Line.chain(r, l), i),
        Follow.new.grows(~Kernel.machine(K), s, r, l, Node.head_of(~Kernel.machine(K), s, Line.chain(r, l)))
      )

# the new requests among cells only grow a node
def Take.asks.grows(
  ~K: Kernel(),
  cs: List<&2, Cells.Cell<Ledgers.Entry<Machine.Q(Kernel.machine(K))>>>,
  +old: Ledgers.State(Machine.Q(Kernel.machine(K))),
  +s: Node<Machine.Q(Kernel.machine(K))>
) -> {Node.grows(~Kernel.machine(K), s, Take.asks(~K, cs, old, s)) == True{}: Bool}:
  match cs:
    case Nil{}:
      Grows.refl(~Kernel.machine(K), s)
    case Con{Cells.One{Ledgers.Entry.Ask{+i, t, +q}}, +rest}:
      +s1 = Shared.Bool.when(
        Node<Machine.Q(Kernel.machine(K))>,
        Maybe.is_none(
          &2,
          Cells.Cell<Ledgers.Entry<Machine.Q(Kernel.machine(K))>>,
          Ledgers.State.get(~Machine.Q(Kernel.machine(K)), old, Ledgers.Slot.ask(i))
        ),
        u => Node.arrive(~K, s, i, q),
        u => s
      )
      Grows.trans(~Kernel.machine(K), 
        s,
        s1,
        Take.asks(~K, rest, old, s1)
      )(
        Grows.when(~Kernel.machine(K), 
          s,
          Maybe.is_none(
            &2,
            Cells.Cell<Ledgers.Entry<Machine.Q(Kernel.machine(K))>>,
            Ledgers.State.get(~Machine.Q(Kernel.machine(K)), old, Ledgers.Slot.ask(i))
          ),
          Node.arrive(~K, s, i, q),
          s,
          Arrive.grows(~K, s, i, Machine.arrival(Kernel.machine(K))(q)),
          Grows.refl(~Kernel.machine(K), s)
        )
      )(Take.asks.grows(~K, rest, old, s1))
    case Con{Cells.One{Ledgers.Entry.Vote{v}}, rest}:
      Take.asks.grows(~K, rest, old, s)
    case Con{Cells.One{Ledgers.Entry.Data{d}}, rest}:
      Take.asks.grows(~K, rest, old, s)
    case Con{Cells.Many{}, rest}:
      Take.asks.grows(~K, rest, old, s)

# a node that takes in what another node sent only grows
def Take.grows(
  ~K: Kernel(),
  +s: Node<Machine.Q(Kernel.machine(K))>,
  +t: Ledgers.State(Machine.Q(Kernel.machine(K)))
) -> {Node.grows(~Kernel.machine(K), s, Node.take(~K, s, t)) == True{}: Bool}:
  +sent = Take.clean(~Kernel.machine(K), 
    Tries.Trie.values(Cells.Cell<Ledgers.Entry<Machine.Q(Kernel.machine(K))>>, t),
    Ledgers.State.empty(~Machine.Q(Kernel.machine(K)))
  )
  +l1 = Ledgers.State.take(~Machine.Q(Kernel.machine(K)), State.ledger(~Kernel.machine(K), s), sent)
  +s1 = State.led(~Kernel.machine(K), s, l1)
  +cs = Tries.Trie.values(Cells.Cell<Ledgers.Entry<Machine.Q(Kernel.machine(K))>>, sent)
  +s2 = Take.asks(~K, cs, State.ledger(~Kernel.machine(K), s), s1)
  +bs = Ballots.of(~Kernel.machine(K), 
    Tries.Trie.values(
      Cells.Cell<Ledgers.Entry<Machine.Q(Kernel.machine(K))>>,
      Ledgers.State.missing(~Machine.Q(Kernel.machine(K)), ~Machine.same(Kernel.machine(K)), t, State.ledger(~Kernel.machine(K), s))
    )
  )
  Grows.trans(~Kernel.machine(K), 
    s,
    s1,
    Sealed.take(~K, bs, s2)
  )(
    Grows.led(~Kernel.machine(K), 
      s,
      l1,
      Ledgers.State.take_grows(
        ~Machine.Q(Kernel.machine(K)),
        ~Machine.same(Kernel.machine(K)),
        ~Machine.laws(Kernel.machine(K)),
        State.ledger(~Kernel.machine(K), s),
        sent
      )
    )
  )(
    Grows.trans(~Kernel.machine(K), 
      s1,
      s2,
      Sealed.take(~K, bs, s2)
    )(
      Take.asks.grows(~K, cs, State.ledger(~Kernel.machine(K), s), s1)
    )(Each.grows(~K, List.length(&2, Ledgers.Ballot, bs), bs, Pending.of(bs), s2))
  )

# after its ledger took in what was sent, a node only grows as it takes the
# rest in
def Take.tail(
  ~K: Kernel(),
  +s: Node<Machine.Q(Kernel.machine(K))>,
  +t: Ledgers.State(Machine.Q(Kernel.machine(K)))
) -> {
  Node.grows(~Kernel.machine(K), 
    State.led(~Kernel.machine(K), 
      s,
      Ledgers.State.take(
        ~Machine.Q(Kernel.machine(K)),
        State.ledger(~Kernel.machine(K), s),
        Take.clean(~Kernel.machine(K), 
          Tries.Trie.values(Cells.Cell<Ledgers.Entry<Machine.Q(Kernel.machine(K))>>, t),
          Ledgers.State.empty(~Machine.Q(Kernel.machine(K)))
        )
      )
    ),
    Node.take(~K, s, t)
  )
    == True{}: Bool
}:
  +sent = Take.clean(~Kernel.machine(K), 
    Tries.Trie.values(Cells.Cell<Ledgers.Entry<Machine.Q(Kernel.machine(K))>>, t),
    Ledgers.State.empty(~Machine.Q(Kernel.machine(K)))
  )
  l1 = Ledgers.State.take(~Machine.Q(Kernel.machine(K)), State.ledger(~Kernel.machine(K), s), sent)
  +s1 = State.led(~Kernel.machine(K), s, l1)
  +cs = Tries.Trie.values(Cells.Cell<Ledgers.Entry<Machine.Q(Kernel.machine(K))>>, sent)
  +s2 = Take.asks(~K, cs, State.ledger(~Kernel.machine(K), s), s1)
  +bs = Ballots.of(~Kernel.machine(K), 
    Tries.Trie.values(
      Cells.Cell<Ledgers.Entry<Machine.Q(Kernel.machine(K))>>,
      Ledgers.State.missing(~Machine.Q(Kernel.machine(K)), ~Machine.same(Kernel.machine(K)), t, State.ledger(~Kernel.machine(K), s))
    )
  )
  Grows.trans(~Kernel.machine(K), 
    s1,
    s2,
    Sealed.take(~K, bs, s2)
  )(
    Take.asks.grows(~K, cs, State.ledger(~Kernel.machine(K), s), s1)
  )(Each.grows(~K, List.length(&2, Ledgers.Ballot, bs), bs, Pending.of(bs), s2))

# Node.fetch for the data ws itself
def Fetch.take(
  ~K: Kernel(),
  +b: Node<Machine.Q(Kernel.machine(K))>,
  +ws: List<&2, U32>
) -> {
  Ledgers.State.get(
    ~Machine.Q(Kernel.machine(K)),
    State.ledger(~Kernel.machine(K), b),
    Ledgers.Slot.data(Hashes.Sha.hash(ws))
  )
    == None{}: Maybe<&2, Cells.Cell<Ledgers.Entry<Machine.Q(Kernel.machine(K))>>>
} -> {
  Ledgers.State.data(
    ~Machine.Q(Kernel.machine(K)),
    State.ledger(~Kernel.machine(K), 
      Node.take(~K, 
        b,
        Ledgers.State.put_data(~Machine.Q(Kernel.machine(K)), ~Machine.same(Kernel.machine(K)), Ledgers.State.empty(~Machine.Q(Kernel.machine(K))), ws)
      )
    ),
    Hashes.Sha.hash(ws)
  )
    == Some{ws}: Maybe<&2, List<&2, U32>>
}:
  +t = Ledgers.State.put_data(~Machine.Q(Kernel.machine(K)), ~Machine.same(Kernel.machine(K)), Ledgers.State.empty(~Machine.Q(Kernel.machine(K))), ws)
  +l1 = Ledgers.State.take(~Machine.Q(Kernel.machine(K)), State.ledger(~Kernel.machine(K), b), t)
  e =>
    Ledgers.State.data_grows(
      ~Machine.Q(Kernel.machine(K)),
      ~Machine.same(Kernel.machine(K)),
      ~Machine.laws(Kernel.machine(K)),
      State.ledger(~Kernel.machine(K), State.led(~Kernel.machine(K), b, l1)),
      State.ledger(~Kernel.machine(K), Node.take(~K, b, t)),
      Hashes.Sha.hash(ws),
      ws
    )(Take.tail(~K, b, t))(
      %Equal.sym(Ledgers.State(Machine.Q(Kernel.machine(K))), State.ledger(~Kernel.machine(K), State.led(~Kernel.machine(K), b, l1)), l1, Led.led(~Kernel.machine(K), b, l1)): {Ledgers.State.data(~Machine.Q(Kernel.machine(K)), _, Hashes.Sha.hash(ws)) == Some{ws}: Maybe<&2, List<&2, U32>>}
      Ledgers.State.take_data(~Machine.Q(Kernel.machine(K)), ~Machine.same(Kernel.machine(K)), State.ledger(~Kernel.machine(K), b), ws)(e))

# a store that starts keeps the logs
def Start.kept(
  ~K: Kernel(),
  +s: Node<Machine.Q(Kernel.machine(K))>,
  i: Ledgers.Id,
  +os: List<&2, Owner>
) -> Node.Keeps(~Kernel.machine(K), s, Node.start(~K, s, i, os)):
  Start.with.kept(~Kernel.machine(K), 
    s,
    i,
    Owner.names(os),
    Seal.firsts(~K, os, Some{Work{s, None{}}})
  )(Firsts.after(~K, s, os, Some{Work{s, None{}}})(Grows.refl(~Kernel.machine(K), s)))

# a new request keeps the logs
def Arrive.kept(
  ~K: Kernel(),
  +s: Node<Machine.Q(Kernel.machine(K))>,
  +i: Ledgers.Id,
  a: Arrival,
) -> Node.Keeps(~Kernel.machine(K), s, Arrive.at(~K, s, i, a)):
  match a:
    case Arrival.Starts{os}:
      Start.kept(~K, s, i, os)
    case Arrival.Waits{+r, +l}:
      +s1 = Node.follow(~Kernel.machine(K), s, r, l)
      Kept.trans(~Kernel.machine(K), 
        s,
        s1,
        State.wait(~Kernel.machine(K), s1, Line.chain(r, l), i),
        Follow.new.kept(~Kernel.machine(K), s, r, l, Node.head_of(~Kernel.machine(K), s, Line.chain(r, l)))({==}),
        Kept.same(~Kernel.machine(K), 
          s1,
          State.wait(~Kernel.machine(K), s1, Line.chain(r, l), i),
          Grows.to(~Kernel.machine(K), 
            s1,
            s1,
            State.wait(~Kernel.machine(K), s1, Line.chain(r, l), i),
            Led.waits(~Kernel.machine(K), s1, Line.chain(r, l), i),
            Grows.refl(~Kernel.machine(K), s1)
          ),
          Heads.waits(~Kernel.machine(K), s1, Line.chain(r, l), i)
        )
      )

# the new requests among cells keep the logs
def Take.asks.kept(
  ~K: Kernel(),
  cs: List<&2, Cells.Cell<Ledgers.Entry<Machine.Q(Kernel.machine(K))>>>,
  +old: Ledgers.State(Machine.Q(Kernel.machine(K))),
  +s: Node<Machine.Q(Kernel.machine(K))>
) -> Node.Keeps(~Kernel.machine(K), s, Take.asks(~K, cs, old, s)):
  match cs:
    case Nil{}:
      Kept.refl(~Kernel.machine(K), s)
    case Con{Cells.One{Ledgers.Entry.Ask{+i, t, +q}}, rest}:
      s1 = Shared.Bool.when(
        Node<Machine.Q(Kernel.machine(K))>,
        Maybe.is_none(
          &2,
          Cells.Cell<Ledgers.Entry<Machine.Q(Kernel.machine(K))>>,
          Ledgers.State.get(~Machine.Q(Kernel.machine(K)), old, Ledgers.Slot.ask(i))
        ),
        u => Node.arrive(~K, s, i, q),
        u => s
      )
      Kept.trans(~Kernel.machine(K), 
        s,
        s1,
        Take.asks(~K, rest, old, s1),
        Kept.when(~Kernel.machine(K), 
          Maybe.is_none(
            &2,
            Cells.Cell<Ledgers.Entry<Machine.Q(Kernel.machine(K))>>,
            Ledgers.State.get(~Machine.Q(Kernel.machine(K)), old, Ledgers.Slot.ask(i))
          ),
          s,
          Node.arrive(~K, s, i, q),
          s,
          Arrive.kept(~K, s, i, Machine.arrival(Kernel.machine(K))(q)),
          Kept.refl(~Kernel.machine(K), s)
        ),
        Take.asks.kept(~K, rest, old, s1)
      )
    case Con{Cells.One{Ledgers.Entry.Vote{v}}, rest}:
      Take.asks.kept(~K, rest, old, s)
    case Con{Cells.One{Ledgers.Entry.Data{d}}, rest}:
      Take.asks.kept(~K, rest, old, s)
    case Con{Cells.Many{}, rest}:
      Take.asks.kept(~K, rest, old, s)

# Node.take keeps the logs
def Take.kept(
  ~K: Kernel(),
  +s: Node<Machine.Q(Kernel.machine(K))>,
  +t: Ledgers.State(Machine.Q(Kernel.machine(K)))
) -> Node.Keeps(~Kernel.machine(K), s, Node.take(~K, s, t)):
  +sent = Take.clean(~Kernel.machine(K), 
    Tries.Trie.values(Cells.Cell<Ledgers.Entry<Machine.Q(Kernel.machine(K))>>, t),
    Ledgers.State.empty(~Machine.Q(Kernel.machine(K)))
  )
  +l1 = Ledgers.State.take(~Machine.Q(Kernel.machine(K)), State.ledger(~Kernel.machine(K), s), sent)
  +s1 = State.led(~Kernel.machine(K), s, l1)
  +cs = Tries.Trie.values(Cells.Cell<Ledgers.Entry<Machine.Q(Kernel.machine(K))>>, sent)
  +s2 = Take.asks(~K, cs, State.ledger(~Kernel.machine(K), s), s1)
  +bs = Ballots.of(~Kernel.machine(K), 
    Tries.Trie.values(
      Cells.Cell<Ledgers.Entry<Machine.Q(Kernel.machine(K))>>,
      Ledgers.State.missing(~Machine.Q(Kernel.machine(K)), ~Machine.same(Kernel.machine(K)), t, State.ledger(~Kernel.machine(K), s))
    )
  )
  Kept.trans(~Kernel.machine(K), 
    s,
    s1,
    Sealed.take(~K, bs, s2),
    Kept.same(~Kernel.machine(K), 
      s,
      s1,
      Grows.led(~Kernel.machine(K), 
        s,
        l1,
        Ledgers.State.take_grows(
          ~Machine.Q(Kernel.machine(K)),
          ~Machine.same(Kernel.machine(K)),
          ~Machine.laws(Kernel.machine(K)),
          State.ledger(~Kernel.machine(K), s),
          sent
        )
      ),
      Heads.led(~Kernel.machine(K), s, l1)
    ),
    Kept.trans(~Kernel.machine(K), 
      s1,
      s2,
      Sealed.take(~K, bs, s2),
      Take.asks.kept(~K, cs, State.ledger(~Kernel.machine(K), s), s1),
      Kept.same(~Kernel.machine(K), 
        s2,
        Sealed.take(~K, bs, s2),
        Each.grows(~K, List.length(&2, Ledgers.Ballot, bs), bs, Pending.of(bs), s2),
        Each.heads(~K, List.length(&2, Ledgers.Ballot, bs), bs, Pending.of(bs), s2)
      )
    )
  )

# the line of a request that a node holds, a node that grew holds
def Chain.of.kept(
  ~M: Machine(),
  +a: Node<Machine.Q(M)>,
  b: Node<Machine.Q(M)>,
  +i: Ledgers.Id,
  -c: Ledgers.Chain,
  g: {Node.grows(~M, a, b) == True{}: Bool}
) -> {
  Node.chain_of(~M, a, i) == Some{c}: Maybe<&2, Ledgers.Chain>
} -> {Node.chain_of(~M, b, i) == Some{c}: Maybe<&2, Ledgers.Chain>}:
  Shared.Maybe.bind_kept(
    Ledgers.Asked<Machine.Q(M)>,
    Ledgers.Chain,
    Node.asked(~M, a, i),
    Node.asked(~M, b, i),
    x => Some{Arrival.chain(i, Machine.arrival(M)(Asked.ask(~M, x)))},
    x => Some{Arrival.chain(i, Machine.arrival(M)(Asked.ask(~M, x)))},
    c,
    x => Ledgers.State.read_grows(
      ~Machine.Q(M),
      ~Machine.same(M),
      ~Machine.laws(M),
      ~Ledgers.Asked<Machine.Q(M)>,
      m => Ledgers.Asked.of(~Machine.Q(M), m),
      {==},
      State.ledger(~M, a),
      State.ledger(~M, b),
      Ledgers.Slot.ask(i),
      x
    )(g),
    x => e => e
  )

# an outcome that a node knows, a node that grew and keeps its logs knows
def Out.kept(
  ~M: Machine(),
  +a: Node<Machine.Q(M)>,
  +b: Node<Machine.Q(M)>,
  +i: Ledgers.Id,
  -o: Out,
  g: {Node.grows(~M, a, b) == True{}: Bool},
  hk: Node.Keeps(~M, a, b)
) -> {
  Node.out(~M, a, i) == Some{o}: Maybe<&2, Out>
} -> {Node.out(~M, b, i) == Some{o}: Maybe<&2, Out>}:
  Shared.Maybe.bind_kept(
    Ledgers.Chain,
    Out,
    Node.chain_of(~M, a, i),
    Node.chain_of(~M, b, i),
    c => Chain.out(~M, a, c, i),
    c => Chain.out(~M, b, c, i),
    o,
    c => Chain.of.kept(~M, a, b, i, c, g),
    +c => Chain.out.kept(~M, a, b, c, i, o, hk)
  )

# the version of an outcome, in a node that keeps the logs
def Out.on.kept(
  ~M: Machine(),
  a: Node<Machine.Q(M)>,
  b: Node<Machine.Q(M)>,
  c: Ledgers.Chain,
  o: Out,
  -x: Version,
  hk: Node.Keeps(~M, a, b)
) -> {
  Out.on(~M, a, c, o) == Some{x}: Maybe<&2, Version>
} -> {Out.on(~M, b, c, o) == Some{x}: Maybe<&2, Version>}:
  match o:
    case Out.Stale{}:
      e => e
    case Out.Taken{n}:
      Chain.version.kept(~M, a, b, c, n, x, hk)

# the version that a request made on a line, in a node that keeps the logs
def Chain.made.kept(
  ~M: Machine(),
  +a: Node<Machine.Q(M)>,
  +b: Node<Machine.Q(M)>,
  +c: Ledgers.Chain,
  +v: Ledgers.Id,
  -x: Version,
  hk1: Node.Keeps(~M, a, b),
  hk2: Node.Keeps(~M, a, b)
) -> {
  Chain.made(~M, a, c, v) == Some{x}: Maybe<&2, Version>
} -> {Chain.made(~M, b, c, v) == Some{x}: Maybe<&2, Version>}:
  Shared.Maybe.bind_kept(
    Out,
    Version,
    Chain.out(~M, a, c, v),
    Chain.out(~M, b, c, v),
    o => Out.on(~M, a, c, o),
    o => Out.on(~M, b, c, o),
    x,
    o => Chain.out.kept(~M, a, b, c, v, o, hk1),
    o => Out.on.kept(~M, a, b, c, o, x, hk2)
  )

# the version that a request made, in a node that grew and keeps the logs
def Made.kept(
  ~M: Machine(),
  +a: Node<Machine.Q(M)>,
  +b: Node<Machine.Q(M)>,
  +v: Ledgers.Id,
  -x: Version,
  g: {Node.grows(~M, a, b) == True{}: Bool},
  hk1: Node.Keeps(~M, a, b),
  hk2: Node.Keeps(~M, a, b)
) -> {
  Node.made(~M, a, v) == Some{x}: Maybe<&2, Version>
} -> {Node.made(~M, b, v) == Some{x}: Maybe<&2, Version>}:
  Shared.Maybe.bind_kept(
    Ledgers.Chain,
    Version,
    Node.chain_of(~M, a, v),
    Node.chain_of(~M, b, v),
    +c => Chain.made(~M, a, c, v),
    +c => Chain.made(~M, b, c, v),
    x,
    c => Chain.of.kept(~M, a, b, v, c, g),
    +c => Chain.made.kept(~M, a, b, c, v, x, hk1, hk2)
  )

# a request that waits on a line waits there after a request arrives
def Arrive.waits(
  ~K: Kernel(),
  +s: Node<Machine.Q(Kernel.machine(K))>,
  +j: Ledgers.Id,
  +a: Arrival,
  +c2: Ledgers.Chain,
  i: Ledgers.Id,
  h: {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, Wait.of(~Kernel.machine(K), s, c2), i) == True{}: Bool}
) -> {
  List.contains(
    ~Ledgers.Id,
    ~Ledgers.Id.is_eq,
    Wait.of(~Kernel.machine(K), Arrive.at(~K, s, j, a), c2),
    i
  )
    == True{}: Bool
}:
  match a:
    case Arrival.Starts{os}:
      %Wait.same(~Kernel.machine(K), 
        s,
        Node.start(~K, s, j, os),
        c2,
        Start.with.waiting(~Kernel.machine(K), 
          s,
          j,
          Owner.names(os),
          Seal.firsts(~K, os, Some{Work{s, None{}}})
        )
      ): {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, _, i) == True{}: Bool}
      h
    case Arrival.Waits{r, l}:
      Wait.keeps(~Kernel.machine(K), Node.follow(~Kernel.machine(K), s, r, l), Line.chain(r, l), j, c2, i, (
          %Wait.same(~Kernel.machine(K), s, Node.follow(~Kernel.machine(K), s, r, l), c2, Follow.new.waiting(~Kernel.machine(K), s, r, l, Node.head_of(~Kernel.machine(K), s, Line.chain(r, l)))): {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, _, i) == True{}: Bool}
          h))

# a request that waits on a line waits there after more requests arrive
def Take.asks.waits(
  ~K: Kernel(),
  +cs: List<&2, Cells.Cell<Ledgers.Entry<Machine.Q(Kernel.machine(K))>>>,
  +old: Ledgers.State(Machine.Q(Kernel.machine(K))),
  +s: Node<Machine.Q(Kernel.machine(K))>,
  +c2: Ledgers.Chain,
  +i: Ledgers.Id
) -> {
  List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, Wait.of(~Kernel.machine(K), s, c2), i) == True{}: Bool
} -> {
  List.contains(
    ~Ledgers.Id,
    ~Ledgers.Id.is_eq,
    Wait.of(~Kernel.machine(K), Take.asks(~K, cs, old, s), c2),
    i
  )
    == True{}: Bool
}:
  match cs:
    case Nil{}:
      h => h
    case Con{Cells.One{Ledgers.Entry.Ask{j, t, q}}, rest}:
      +h => Take.asks.waits(~K, 
        rest,
        old,
        Shared.Bool.when(
          Node<Machine.Q(Kernel.machine(K))>,
          Maybe.is_none(
            &2,
            Cells.Cell<Ledgers.Entry<Machine.Q(Kernel.machine(K))>>,
            Ledgers.State.get(~Machine.Q(Kernel.machine(K)), old, Ledgers.Slot.ask(j))
          ),
          u => Node.arrive(~K, s, j, q),
          u => s
        ),
        c2,
        i
      )(
        Contains.when(~Kernel.machine(K), 
          Maybe.is_none(
            &2,
            Cells.Cell<Ledgers.Entry<Machine.Q(Kernel.machine(K))>>,
            Ledgers.State.get(~Machine.Q(Kernel.machine(K)), old, Ledgers.Slot.ask(j))
          ),
          Node.arrive(~K, s, j, q),
          s,
          c2,
          i,
          Arrive.waits(~K, s, j, Machine.arrival(Kernel.machine(K))(q), c2, i, h),
          h
        )
      )
    case Con{Cells.One{Ledgers.Entry.Vote{v}}, rest}:
      Take.asks.waits(~K, rest, old, s, c2, i)
    case Con{Cells.One{Ledgers.Entry.Data{d}}, rest}:
      Take.asks.waits(~K, rest, old, s, c2, i)
    case Con{Cells.Many{}, rest}:
      Take.asks.waits(~K, rest, old, s, c2, i)
