import Base
import ../shared/shared/ledger.bend as Ledgers
import ./spec.bend as Spec
import ../shared/shared/shared/shared/hash.bend as Hashes
import ./run/facts.bend as Facts
import ./node.bend as Nodes
import ./run/fast.bend as Fasts
import ./impl.bend as Impl
import ./run/known.bend as Known

# Scenario 4: two nodes a and b own one store; each writes on its own branch;
# a ballot reaches the other node by a Sync. Every 50 writes a node asks for a
# group and for a new branch (requests of the store line).

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

def start() -> Spec.Request:
  Spec.Request.Start{["a", "b"]}

def hash() -> Hashes.Hash:
  Facts.Start.root(Ledgers.Id{"w", "s1"}, start())

def root() -> Ledgers.Line:
  Ledgers.Line{hash(), None{}}

def line(b: String) -> Ledgers.Line:
  Ledgers.Line{hash(), Some{b}}

# two nodes
type Two is Data:
  Two{a: Fasts.Fast, b: Fasts.Fast}

def works(n: Nat, r: Fasts.Fast) -> Fasts.Fast:
  match n:
    case 0n:
      r
    case 1n+p:
      works(p, Fasts.Fast.does(r, Nodes.Act.Work{}))

def sync(to: Fasts.Fast, from: Fasts.Fast) -> Fasts.Fast:
  Fasts.Fast.does(to, Nodes.Act.Sync{Fasts.Fast.raw(from)})

# a round: a works, b takes in what a holds and works, a takes in what b holds
def round(t: Two) -> Two:
  match t:
    case Two{a, b}:
      +a2 = works(1n, a)
      +b2 = works(1n, sync(b, a2))
      Two{sync(a2, b2), b2}

def settle(k: Nat, t: Two) -> Two:
  match k:
    case 0n:
      t
    case 1n+p:
      settle(p, round(t))

def aska(t: Two, i: String, q: Spec.Request) -> Two:
  match t:
    case Two{a, b}:
      Two{Fasts.Fast.does(a, Nodes.Act.Ask{Ledgers.Id{"w", i}, q}), b}

def askb(t: Two, i: String, q: Spec.Request) -> Two:
  match t:
    case Two{a, b}:
      Two{a, Fasts.Fast.does(b, Nodes.Act.Ask{Ledgers.Id{"v", i}, q})}

def words() -> Maybe<&2, List<&2, U32>>:
  Some{[104, 105, 106]}

def zero() -> Two:
  Two{Fasts.Fast.does(Fasts.Fast.new("a"), Nodes.Act.Connect{"w"}), Fasts.Fast.does(Fasts.Fast.new("b"), Nodes.Act.Connect{"v"})}

def first() -> Two:
  settle(3n, aska(settle(3n, aska(settle(3n, aska(settle(3n, aska(settle(2n, aska(zero(), "s1", start())), "g1", Spec.Request.Group{hash(), "core", ["a", "b"]})), "o1", Spec.Request.Own{root(), "core"})), "o2", Spec.Request.Own{line("ba"), "core"})), "o3", Spec.Request.Own{line("bb"), "core"}))

# a write of each node on its branch, then the rounds that decide both
def pair(t: Two, +p: Nat) -> Two:
  settle(4n, askb(aska(t, String.append("x", Nat.show(p)), Spec.Request.Write{line("ba"), String.append("f", Nat.show(Nat.mod(p, 7n))), words()}), String.append("y", Nat.show(p)), Spec.Request.Write{line("bb"), String.append("g", Nat.show(Nat.mod(p, 7n))), words()}))

# a group and a new branch, asked of a: requests of the store line
def store.if(go: Bool, t: Two, +p: Nat) -> Two:
  match go:
    case False{}:
      t
    case True{}:
      settle(3n, aska(settle(3n, aska(t, String.append("g", Nat.show(p)), Spec.Request.Group{hash(), String.append("team", Nat.show(p)), ["a", "b"]})), String.append("n", Nat.show(p)), Spec.Request.Own{line(String.append("n", Nat.show(p))), "core"}))

def writes(n: Nat, t: Two) -> Two:
  match n:
    case 0n:
      t
    case 1n+p:
      +p = p
      writes(p, store.if(Nat.is_eq(Nat.mod(p, 50n), 49n), pair(t, p), p))

def nat(t: String) -> Nat:
  Maybe.default(&2, Nat, Nat.read(t), 0n)

def blen(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      2n

def size(r: Fasts.Fast) -> Nat:
  match r:
    case Fasts.Fast{Nodes.Raw{name, ws, ms, st, fs, ps}, Known.Table{l, sh, h, q}}:
      blen(st)

def size2(t: Two) -> Nat:
  match t:
    case Two{a, b}:
      Nat.add(size(a), size(b))

def fa(t: Two) -> Fasts.Fast:
  match t:
    case Two{a, b}:
      a

def fb(t: Two) -> Fasts.Fast:
  match t:
    case Two{a, b}:
      b

def pend(t: Two) -> Two:
  aska(t, "last", Spec.Request.Write{line("ba"), "zz", words()})

# whole deeds on the two nodes t
def deed(mode: Nat, +t: Two) -> Nat:
  match mode:
    case 0n:
      size2(pend(t))
    case 1n:
      size(Fasts.Fast.does(fa(pend(t)), Nodes.Act.Work{}))
    case 2n:
      size(Fasts.Fast.does(fa(t), Nodes.Act.Work{}))
    case 3n:
      size2(pair(t, 100000n))
    case 4n:
      size(sync(fa(t), fb(t)))
    case 5n:
      size(works(1n, sync(fb(t), fa(pend(t)))))
    case 6n:
      size2(store.if(True{}, t, 100000n))
    case 7n+x:
      String.length(show(Fasts.Fast.answer(fa(t), Spec.Question.Status{line("ba"), Ledgers.Id{"w", "x1"}})))

def deeds(n: Nat, +mode: Nat, +t: Two, acc: Nat) -> Nat:
  match n:
    case 0n:
      acc
    case 1n+p:
      deeds(p, mode, t, Nat.add(acc, deed(mode, t)))

def loop(ms: List<&2, String>, +t: Two, +k: Nat) -> IO(Unit):
  match ms:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{+m, rest}:
      do IO<Unit>:
        t0 : Nat <- IO.now()
        IO.write(String.append(String.append("mode ", m), String.append(" r=", Nat.show(deeds(k, Nat.sub(nat(m), 100n), t, 0n)))))
        t1 : Nat <- IO.now()
        IO.print(String.append(" ms=", Nat.show(Nat.sub(t1, t0))))
        loop(rest, t, k)

def copy(xs: List<&1, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      []
    case Con{x, r}:
      x <> copy(r)

def start3(+t: Two, +k: Nat, rest: List<&2, String>, t0: Nat) -> IO(Unit):
  do IO<Unit>:
    IO.write(String.append("build size=", Nat.show(size2(t))))
    t1 : Nat <- IO.now()
    IO.print(String.append(" ms=", Nat.show(Nat.sub(t1, t0))))
    IO.print(String.append("count ba at a=", show(Fasts.Fast.answer(fa(t), Spec.Question.Count{line("ba")}))))
    IO.print(String.append("count bb at a=", show(Fasts.Fast.answer(fa(t), Spec.Question.Count{line("bb")}))))
    IO.print(String.append("count bb at b=", show(Fasts.Fast.answer(fb(t), Spec.Question.Count{line("bb")}))))
    IO.print(String.append("count store at b=", show(Fasts.Fast.answer(fb(t), Spec.Question.Count{root()}))))
    loop(rest, t, k)

def start2(xs: List<&2, String>) -> IO(Unit):
  match xs:
    case Con{a, Con{b, Con{c, rest}}}:
      do IO<Unit>:
        t0 : Nat <- IO.now()
        start3(writes(nat(b), first()), nat(c), rest, t0)
    case _:
      IO.print("usage: n reps modes...")

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<&1, String> <- IO.args()
    start2(copy(xs))
