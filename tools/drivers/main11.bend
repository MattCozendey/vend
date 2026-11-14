import Base
import ../shared/shared/ledger.bend as Ledgers
import ./spec.bend as Spec
import ../shared/shared/shared/shared/hash.bend as Hashes
import ./run/facts.bend as Facts
import ./node.bend as Nodes
import ./run/fast.bend as Fasts
import ./impl.bend as Impl
import ./run/work.bend as Works
import ./run/known.bend as Known
import ./run/lines.bend as Lines
import ./run/rounds.bend as Rounds
import ./types.bend as Types
import ./run/parts.bend as Parts
import ./run/content.bend as Contents

def id(n: String) -> Ledgers.Id:
  Ledgers.Id{"w", n}

def show(m: Maybe<&2, Spec.Reply>) -> String:
  match m:
    case None{}:
      "Unknown"
    case Some{Spec.Reply.Status{Spec.Status.Written{}}}:
      "Written"
    case Some{Spec.Reply.Status{s}}:
      "OtherStatus"
    case Some{Spec.Reply.Number{n}}:
      Nat.show(n)
    case Some{r}:
      "Some"

def words(m: Maybe<&2, Maybe<&2, List<&2, U32>>>) -> String:
  match m:
    case None{}:
      "Unknown"
    case Some{None{}}:
      "NoResource"
    case Some{Some{ws}}:
      String.append("words:", Nat.show(List.length(&2, U32, ws)))

def start() -> Spec.Request:
  Spec.Request.Start{["a"]}

def root() -> Ledgers.Line:
  Ledgers.Line{Facts.Start.root(id("s1"), start()), None{}}

def branch() -> Ledgers.Line:
  Ledgers.Line{Facts.Start.root(id("s1"), start()), Some{"main"}}

def step(r: Fasts.Fast, i: String, q: Spec.Request) -> Fasts.Fast:
  Fasts.Fast.does(Fasts.Fast.does(r, Nodes.Act.Ask{id(i), q}), Nodes.Act.Work{})

def final() -> Fasts.Fast:
  n1 = Fasts.Fast.does(Fasts.Fast.new("a"), Nodes.Act.Connect{"w"})
  n2 = Fasts.Fast.does(n1, Nodes.Act.Ask{id("s1"), start()})
  n3 = step(n2, "g1", Spec.Request.Group{Facts.Start.root(id("s1"), start()), "core", ["a"]})
  n4 = step(n3, "o1", Spec.Request.Own{root(), "core"})
  n5 = step(n4, "o2", Spec.Request.Own{branch(), "core"})
  step(n5, "w1", Spec.Request.Write{branch(), "a.txt", Some{[104, 105]}})

# the branch number k of the store
def line(k: Nat) -> Ledgers.Line:
  Ledgers.Line{Facts.Start.root(id("s1"), start()), Some{String.append("b", Nat.show(k))}}

# the node with b more branches owned
def owned(b: Nat, r: Fasts.Fast) -> Fasts.Fast:
  match b:
    case 0n:
      r
    case 1n+p:
      +p = p
      owned(p, step(r, String.append("ob", Nat.show(p)), Spec.Request.Own{line(p), "core"}))

# the id number p of the writer w
def wid(w: String, p: Nat) -> Ledgers.Id:
  Ledgers.Id{w, String.append("x", Nat.show(p))}

# the writer of the write number p: one of two
def writer.of(m: Nat) -> String:
  match m:
    case 0n:
      "w"
    case 1n+q:
      "v"

def writer(p: Nat) -> String:
  writer.of(Nat.mod(p, 2n))

def step2(r: Fasts.Fast, i: Ledgers.Id, q: Spec.Request) -> Fasts.Fast:
  Fasts.Fast.does(Fasts.Fast.does(r, Nodes.Act.Ask{i, q}), Nodes.Act.Work{})

# n writes, spread over 50 branches, by two writers
def writes(n: Nat, r: Fasts.Fast) -> Fasts.Fast:
  match n:
    case 0n:
      r
    case 1n+p:
      +p = p
      writes(p, step2(r, wid(writer(p), p), Spec.Request.Write{line(Nat.mod(p, 50n)), String.append("f", Nat.show(Nat.mod(p, 7n))), Some{[104, 105, 106]}}))

def nat(t: String) -> Nat:
  Maybe.default(&2, Nat, Nat.read(t), 0n)

def build(+n: Nat) -> Fasts.Fast:
  writes(n, owned(50n, Fasts.Fast.does(final(), Nodes.Act.Connect{"v"})))

def pending(r: Fasts.Fast) -> Fasts.Fast:
  Fasts.Fast.does(r, Nodes.Act.Ask{id("last"), Spec.Request.Write{line(7n), "zz", Some{[104, 105, 106]}}})

def blen(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      2n

def ksize(kn: Known.Known()) -> Nat:
  match kn:
    case Known.Table{l, sh, h, q}:
      1n

def size(r: Fasts.Fast) -> Nat:
  match r:
    case Fasts.Fast{Nodes.Raw{name, ws, ms, st, fs, ps}, kn}:
      Nat.add(ksize(kn), blen(st))

# whole deeds, on the node r (idle) and q (one ask waits)
def deed(mode: Nat, +r: Fasts.Fast, +q: Fasts.Fast) -> Nat:
  match mode:
    case 0n:
      size(pending(r))
    case 1n:
      size(Fasts.Fast.does(q, Nodes.Act.Work{}))
    case 2n:
      size(Fasts.Fast.does(r, Nodes.Act.Work{}))
    case 3n:
      String.length(words(Fasts.Fast.view(r, "v", line(7n), "f1")))
    case 4n:
      String.length(show(Fasts.Fast.answer(r, Spec.Question.Count{line(7n)})))
    case 5n:
      String.length(words(Fasts.Fast.read(r, line(7n), 1n, "f1")))
    case 6n+x:
      String.length(show(Fasts.Fast.answer(r, Spec.Question.Status{line(7n), wid("v", 107n)})))

def deeds(n: Nat, +mode: Nat, +r: Fasts.Fast, +q: Fasts.Fast, acc: Nat) -> Nat:
  match n:
    case 0n:
      acc
    case 1n+p:
      deeds(p, mode, r, q, Nat.add(acc, deed(mode, r, q)))

def loop(ms: List<&2, String>, +r: Fasts.Fast, +q: Fasts.Fast, +k: Nat) -> IO(Unit):
  match ms:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{+m, rest}:
      do IO<Unit>:
        t0 : Nat <- IO.now()
        IO.write(String.append(String.append("mode ", m), String.append(" r=", Nat.show(deeds(k, Nat.sub(nat(m), 100n), r, q, 0n)))))
        t1 : Nat <- IO.now()
        IO.print(String.append(" ms=", Nat.show(Nat.sub(t1, t0))))
        loop(rest, r, q, k)

def copy(xs: List<&1, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      []
    case Con{x, r}:
      x <> copy(r)

def start4(+r: Fasts.Fast, +q: Fasts.Fast, +k: Nat, rest: List<&2, String>) -> IO(Unit):
  do IO<Unit>:
    IO.print(String.append("pending size=", Nat.show(size(q))))
    IO.print(String.append("count b7=", show(Fasts.Fast.answer(r, Spec.Question.Count{line(7n)}))))
    IO.print(String.append("status w106=", show(Fasts.Fast.answer(r, Spec.Question.Status{line(7n), wid("v", 107n)}))))
    IO.print(String.append("view=", words(Fasts.Fast.view(r, "v", line(7n), "f1"))))
    loop(rest, r, q, k)

def start3(+r: Fasts.Fast, +k: Nat, rest: List<&2, String>, t0: Nat) -> IO(Unit):
  do IO<Unit>:
    IO.write(String.append("build size=", Nat.show(size(r))))
    t1 : Nat <- IO.now()
    IO.print(String.append(" ms=", Nat.show(Nat.sub(t1, t0))))
    start4(r, pending(r), k, rest)

def start2(xs: List<&2, String>) -> IO(Unit):
  match xs:
    case Con{a, Con{b, Con{c, rest}}}:
      do IO<Unit>:
        t0 : Nat <- IO.now()
        start3(build(nat(b)), nat(c), rest, t0)
    case _:
      IO.print("usage: n reps modes...")

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<&1, String> <- IO.args()
    start2(copy(xs))
