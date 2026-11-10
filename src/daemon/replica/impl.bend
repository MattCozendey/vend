import Base
import ../../shared.bend as Shared
import ../shared/ledger.bend as Ledgers
import ../shared/shared/shared/code.bend as Codes
import ../shared/shared/shared/hash.bend as Hashes
import ../shared/shared/shared/trie.bend as Tries
import ../shared/shared/store.bend as Stores
import ../shared/tree.bend as Trees

# Replicas
# --------
# A replica is a node of a replicated machine: it holds a ledger that only
# grows, a head of each line that it follows, the requests that wait, and its
# keys. It is generic over the machine: what a request is, and what a request
# does to a line. src/daemon/core gives the machine of Vend.

# a machine: its requests, when two are the same, and that this is equality
def Machine() -> Type:
  &Q: Data -> &same: (Q -> Q -> Bool) -> Shared.Eq.Laws(Q, same)

# the requests of the machine m
def Machine.Q(m: Machine()) -> Data:
  match m:
    case Tuple{q, r}:
      q

# two requests of the machine m are the same
def Machine.same(m: Machine()) -> Machine.Q(m) -> Machine.Q(m) -> Bool:
  match m:
    case Tuple{q, Tuple{s, l}}:
      s

# the sameness of the machine m is equality
def Machine.laws(m: Machine()) -> Shared.Eq.Laws(Machine.Q(m), Machine.same(m)):
  match m:
    case Tuple{q, Tuple{s, l}}:
      l

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
# A kernel is a machine and what a replica asks of its requests.

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

# what a kernel says of the requests of the machine M: how one arrives,
# whether it changes who decides, the key of the first key of a node in the
# content of a store, and what one does to the run of a line
def Kernel.Hooks(M: Machine()) -> Type:
  (Machine.Q(M) -> Arrival) & (
    (Machine.Q(M) -> Bool) & (
      (String -> List<&2, U32>) & (
        Run<Machine.Q(M)> -> Ledgers.Chain -> Ledgers.Id -> Machine.Q(M) -> Maybe<&2, Run<Machine.Q(M)>>
      )
    )
  )

# a kernel: a machine, and its hooks
def Kernel() -> Type:
  &M: Machine() -> Kernel.Hooks(M)

# the machine of the kernel k
def Kernel.machine(k: Kernel()) -> Machine():
  match k:
    case Tuple{m, h}:
      m

# how a request of the kernel k arrives
def Kernel.arrival(k: Kernel()) -> Machine.Q(Kernel.machine(k)) -> Arrival:
  match k:
    case Tuple{m, Tuple{a, h}}:
      a

# a request of the kernel k changes who decides
def Kernel.governs(k: Kernel()) -> Machine.Q(Kernel.machine(k)) -> Bool:
  match k:
    case Tuple{m, Tuple{a, Tuple{g, h}}}:
      g

# the key of the first key of a node, in the content of a store of the kernel
# k
def Kernel.seal(k: Kernel()) -> String -> List<&2, U32>:
  match k:
    case Tuple{m, Tuple{a, Tuple{g, Tuple{s, c}}}}:
      s

# what a request of the kernel k does to the run of a line
def Kernel.change(
  k: Kernel()
) -> Run<
  Machine.Q(Kernel.machine(k))> -> Ledgers.Chain -> Ledgers.Id -> Machine.Q(Kernel.machine(k)) -> Maybe<
  &2,
  Run<Machine.Q(Kernel.machine(k))>>:
  match k:
    case Tuple{m, Tuple{a, Tuple{g, Tuple{s, c}}}}:
      c
