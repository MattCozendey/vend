import Base
import ../shared/shared/ledger.bend as Ledgers
import ./spec.bend as Spec
import ../shared/shared/shared/shared/hash.bend as Hashes
import ./run/facts.bend as Facts
import ./node.bend as Nodes
import ./run/fast.bend as Fasts
import ./types.bend as Types
import ./impl.bend as Impl

# Driver: L live nodes of N owners; random interleavings of Ask / Work / Sync
# with repeated Works; then settle, and check that each request is decided
# and that the live nodes agree. args: N L seed steps asks

def status(m: Maybe<&2, Spec.Reply>) -> String:
  match m:
    case None{}:
      "Pending"
    case Some{Spec.Reply.Status{Spec.Status.Written{}}}:
      "Written"
    case Some{Spec.Reply.Status{Spec.Status.Conflicted{i}}}:
      "Conflicted"
    case Some{Spec.Reply.Status{Spec.Status.Stale{}}}:
      "Stale"
    case Some{Spec.Reply.Status{Spec.Status.Refused{}}}:
      "Refused"
    case Some{r}:
      "Other"

def names(n: Nat) -> List<&2, String>:
  match n:
    case 0n:
      []
    case 1n:
      ["a"]
    case 2n:
      ["a", "b"]
    case 3n+m:
      ["a", "b", "c"]

def start(+n: Nat) -> Spec.Request:
  Spec.Request.Start{names(n)}

def hash(+n: Nat) -> Hashes.Hash:
  Facts.Start.root(Ledgers.Id{"wa", "s1"}, start(n))

def line(+n: Nat, b: String) -> Ledgers.Line:
  Ledgers.Line{hash(n), Some{b}}

def root(+n: Nat) -> Ledgers.Line:
  Ledgers.Line{hash(n), None{}}

def node(name: String) -> Fasts.Fast:
  +name = name
  Fasts.Fast.does(Fasts.Fast.new(name), Nodes.Act.Connect{String.append("w", name)})

def nodes(ns: List<&2, String>) -> List<&2, Fasts.Fast>:
  match ns:
    case Nil{}:
      []
    case Con{x, r}:
      node(x) <> nodes(r)

def nth(xs: List<&2, Fasts.Fast>, i: Nat) -> Fasts.Fast:
  match xs i:
    case Nil{} j:
      Fasts.Fast.new("?")
    case Con{x, r} 0n:
      x
    case Con{x, r} 1n+j:
      nth(r, j)

def put(xs: List<&2, Fasts.Fast>, i: Nat, y: Fasts.Fast) -> List<&2, Fasts.Fast>:
  match xs i:
    case Nil{} j:
      []
    case Con{x, r} 0n:
      y <> r
    case Con{x, r} 1n+j:
      x <> put(r, j, y)

def works(n: Nat, r: Fasts.Fast) -> Fasts.Fast:
  match n:
    case 0n:
      r
    case 1n+p:
      works(p, Fasts.Fast.does(r, Nodes.Act.Work{}))

def sync(to: Fasts.Fast, from: Fasts.Fast) -> Fasts.Fast:
  Fasts.Fast.does(to, Nodes.Act.Sync{Fasts.Fast.raw(from)})

# node i takes in what node j holds
def syncs(+xs: List<&2, Fasts.Fast>, +i: Nat, j: Nat) -> List<&2, Fasts.Fast>:
  put(xs, i, sync(nth(xs, i), nth(xs, j)))

def workn(+xs: List<&2, Fasts.Fast>, +i: Nat, k: Nat) -> List<&2, Fasts.Fast>:
  put(xs, i, works(k, nth(xs, i)))

def ask(+xs: List<&2, Fasts.Fast>, +i: Nat, id: Ledgers.Id, q: Spec.Request) -> List<&2, Fasts.Fast>:
  put(xs, i, Fasts.Fast.does(nth(xs, i), Nodes.Act.Ask{id, q}))

# each node j takes in what node i holds, for j below m
def spread(m: Nat, +xs: List<&2, Fasts.Fast>, +i: Nat) -> List<&2, Fasts.Fast>:
  match m:
    case 0n:
      xs
    case 1n++j:
      spread(j, syncs(xs, j, i), i)

# each node works twice, then every node takes in what it holds
def turn(m: Nat, +l: Nat, +xs: List<&2, Fasts.Fast>) -> List<&2, Fasts.Fast>:
  match m:
    case 0n:
      xs
    case 1n++j:
      turn(j, l, spread(l, workn(xs, j, 2n), j))

def settle(k: Nat, +l: Nat, xs: List<&2, Fasts.Fast>) -> List<&2, Fasts.Fast>:
  match k:
    case 0n:
      xs
    case 1n+p:
      settle(p, l, turn(l, l, xs))

def idn(i: Nat, c: Nat) -> Ledgers.Id:
  match i:
    case 0n:
      Ledgers.Id{"wa", String.append("x", Nat.show(c))}
    case 1n:
      Ledgers.Id{"wb", String.append("x", Nat.show(c))}
    case 2n+m:
      Ledgers.Id{"wc", String.append("x", Nat.show(c))}

def words.of(c: Nat) -> Maybe<&2, List<&2, U32>>:
  match c:
    case 0n:
      Some{[104, 105, 106]}
    case 1n:
      Some{[104, 105, 107]}
    case 2n+m:
      Some{[104]}

def words(c: Nat) -> Maybe<&2, List<&2, U32>>:
  words.of(Nat.mod(c, 3n))

def setup(+n: Nat, +l: Nat) -> List<&2, Fasts.Fast>:
  +x0 = settle(6n, l, ask(nodes(names(l)), 0n, Ledgers.Id{"wa", "s1"}, start(n)))
  +x1 = settle(6n, l, ask(x0, 0n, Ledgers.Id{"wa", "g1"}, Spec.Request.Group{hash(n), "core", names(n)}))
  +x2 = settle(6n, l, ask(x1, 0n, Ledgers.Id{"wa", "o1"}, Spec.Request.Own{root(n), "core"}))
  +x3 = settle(6n, l, ask(x2, 0n, Ledgers.Id{"wa", "o2"}, Spec.Request.Own{line(n, "sh"), "core"}))
  +x4 = settle(6n, l, ask(x3, 0n, Ledgers.Id{"wa", "o3"}, Spec.Request.Own{line(n, "b0"), "core"}))
  +x5 = settle(6n, l, ask(x4, 0n, Ledgers.Id{"wa", "o4"}, Spec.Request.Own{line(n, "b1"), "core"}))
  settle(6n, l, ask(x5, 0n, Ledgers.Id{"wa", "o5"}, Spec.Request.Own{line(n, "b2"), "core"}))

def rnd(x: Nat) -> Nat:
  Nat.mod(Nat.mul(x, 48271n), 2147483647n)

# the branch of the write number c of the node i: its own, or the shared one
def branch(i: Nat, sh: Bool) -> String:
  match sh:
    case True{}:
      "sh"
    case False{}:
      String.append("b", Nat.show(i))

# a request that was asked: its line and id
type Asked is Data:
  Asked{line: Ledgers.Line, id: Ledgers.Id}

type Sim is Data:
  Sim{nodes: List<&2, Fasts.Fast>, asked: List<&2, Asked>, left: Nat}

def step(op: Nat, +i: Nat, j: Nat, +x: Nat, +n: Nat, m: Sim) -> Sim:
  match op m:
    case 0n Sim{xs, as, 0n}:
      Sim{xs, as, 0n}
    case 0n Sim{xs, as, 1n++c}:
      +b = line(n, branch(i, Nat.is_eq(Nat.mod(Nat.div(x, 1024n), 2n), 0n)))
      Sim{ask(xs, i, idn(i, c), Spec.Request.Write{b, String.append("f", Nat.show(Nat.mod(c, 5n))), words(c)}), Asked{b, idn(i, c)} <> as, c}
    case 1n Sim{xs, as, c}:
      Sim{workn(xs, i, 1n), as, c}
    case 2n Sim{xs, as, c}:
      Sim{workn(xs, i, 2n), as, c}
    case 3n Sim{xs, as, c}:
      Sim{workn(xs, i, 3n), as, c}
    case 4n+o Sim{xs, as, c}:
      Sim{syncs(xs, i, j), as, c}

def run(k: Nat, +x: Nat, +n: Nat, +l: Nat, m: Sim) -> Sim:
  match k:
    case 0n:
      m
    case 1n+p:
      run(p, rnd(x), n, l, step(Nat.mod(Nat.div(x, 65536n), 7n), Nat.mod(Nat.div(x, 8n), l), Nat.mod(Nat.div(x, 128n), l), x, n, m))

def stats(xs: List<&2, Fasts.Fast>, +a: Asked) -> List<&2, String>:
  match xs a:
    case Nil{} b:
      []
    case Con{x, r} Asked{c, i}:
      status(Fasts.Fast.answer(x, Spec.Question.Status{c, i})) <> stats(r, a)

def same(xs: List<&2, String>, +y: String) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, r}:
      Bool.and(String.eq(x, y), same(r, y))

def good(xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, r}:
      Bool.and(Bool.not(String.eq(x, "Pending")), same(r, x))

def join(xs: List<&2, String>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, r}:
      String.append(x, String.append(" ", join(r)))

def idshow(a: Asked) -> String:
  match a:
    case Asked{c, Ledgers.Id{w, i}}:
      String.append(w, String.append("/", i))

def report(ok: Bool, +a: Asked, st: List<&2, String>) -> IO(Unit):
  match ok:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      IO.print(String.append("BAD ", String.append(idshow(a), String.append(": ", join(st)))))

def bump(ok: Bool, bad: Nat) -> Nat:
  match ok:
    case True{}:
      bad
    case False{}:
      1n+bad

def check(as: List<&2, Asked>, +xs: List<&2, Fasts.Fast>, bad: Nat, n: Nat) -> IO(Unit):
  match as:
    case Nil{}:
      IO.print(String.append(String.append("requests=", Nat.show(n)), String.append(" bad=", Nat.show(bad))))
    case Con{+a, r}:
      +st = stats(xs, a)
      +ok = good(st)
      do IO<Unit>:
        report(ok, a, st)
        check(r, xs, bump(ok, bad), 1n+n)

def count(m: Maybe<&2, Spec.Reply>) -> String:
  match m:
    case Some{Spec.Reply.Number{n}}:
      Nat.show(n)
    case _:
      "?"

def counts(xs: List<&2, Fasts.Fast>, +c: Ledgers.Line) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, r}:
      String.append(count(Fasts.Fast.answer(x, Spec.Question.Count{c})), String.append(" ", counts(r, c)))

def facts(xs: List<&2, Fasts.Fast>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, r}:
      String.append(Nat.show(Facts.Facts.fuel(Nodes.Raw.facts(Fasts.Fast.raw(x)))), String.append(" ", facts(r)))

# each node below m works three more times
def idle(m: Nat, +xs: List<&2, Fasts.Fast>) -> List<&2, Fasts.Fast>:
  match m:
    case 0n:
      xs
    case 1n++j:
      idle(j, workn(xs, j, 3n))

def fin(+n: Nat, +l: Nat, m: Sim) -> IO(Unit):
  match m:
    case Sim{xs, +as, c}:
      +ys = settle(Nat.add(12n, List.length(&2, Asked, as)), l, xs)
      do IO<Unit>:
        IO.print(String.append("counts store=", String.append(counts(ys, root(n)), String.append(" sh=", String.append(counts(ys, line(n, "sh")), String.append(" b0=", String.append(counts(ys, line(n, "b0")), String.append(" b1=", String.append(counts(ys, line(n, "b1")), String.append(" facts=", facts(ys)))))))))))
        IO.print(String.append("facts after 3 more works of each node=", facts(idle(l, ys))))
        check(as, ys, 0n, 0n)

def nat(t: String) -> Nat:
  Maybe.default(&2, Nat, Nat.read(t), 0n)

def copy(xs: List<&1, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      []
    case Con{x, r}:
      x <> copy(r)

def go(xs: List<&2, String>) -> IO(Unit):
  match xs:
    case Con{a, Con{n, Con{l, Con{seed, Con{steps, Con{asks, rest}}}}}}:
      +n = nat(n)
      +l = nat(l)
      fin(n, l, run(nat(steps), nat(seed), n, l, Sim{setup(n, l), [], nat(asks)}))
    case _:
      IO.print("usage: N L seed steps asks")

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<&1, String> <- IO.args()
    go(copy(xs))
