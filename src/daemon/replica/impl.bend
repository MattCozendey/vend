import Base
import ../../shared.bend as Shared
import ../shared/ledger.bend as Ledgers
import ../shared/shared/shared/cell.bend as Cells
import ../shared/shared/shared/code.bend as Codes
import ../shared/shared/shared/hash.bend as Hashes
import ../shared/shared/shared/seal.bend as Seals
import ../shared/shared/shared/trie.bend as Tries
import ../shared/shared/store.bend as Stores
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

# a kernel: a machine, and what a request does to the run of a line
def Kernel() -> Type:
  &M: Machine() -> Run<
    Machine.Q(M)> -> Ledgers.Chain -> Ledgers.Id -> Machine.Q(M) -> Maybe<&2, Run<Machine.Q(M)>>

# the machine of the kernel k
def Kernel.machine(k: Kernel()) -> Machine():
  match k:
    case Tuple{m, c}:
      m

# what a request of the kernel k does to the run of a line
def Kernel.change(
  k: Kernel()
) -> Run<
  Machine.Q(Kernel.machine(k))> -> Ledgers.Chain -> Ledgers.Id -> Machine.Q(Kernel.machine(k)) -> Maybe<
  &2,
  Run<Machine.Q(Kernel.machine(k))>>:
  match k:
    case Tuple{m, c}:
      c

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
