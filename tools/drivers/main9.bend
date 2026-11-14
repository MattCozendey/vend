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
import ./run/files.bend as Files
import ../shared/shared/shared/shared/crit.bend as Crits
import ./codes.bend as Coded

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

def writes(n: Nat, r: Fasts.Fast) -> Fasts.Fast:
  match n:
    case 0n:
      r
    case 1n+p:
      +p = p
      writes(p, step(r, String.append("x", Nat.show(p)), Spec.Request.Write{branch(), String.append("f", Nat.show(p)), Some{[104, 105, 106]}}))

def arg(xs: List<&1, String>) -> Nat:
  match xs:
    case Con{a, Con{b, r}}:
      Maybe.default(&2, Nat, Nat.read(b), 0n)
    case _:
      0n

def asks(n: Nat, r: Fasts.Fast) -> Fasts.Fast:
  match n:
    case 0n:
      r
    case 1n+p:
      +p = p
      asks(p, Fasts.Fast.does(r, Nodes.Act.Ask{id(String.append("y", Nat.show(p))), Spec.Request.Write{branch(), "g", None{}}}))

def works(n: Nat, r: Fasts.Fast) -> Fasts.Fast:
  match n:
    case 0n:
      r
    case 1n+p:
      works(p, Fasts.Fast.does(r, Nodes.Act.Work{}))

def counts(n: Nat, +r: Fasts.Fast, acc: Nat) -> Nat:
  match n:
    case 0n:
      acc
    case 1n+p:
      counts(p, r, Nat.add(acc, String.length(show(Fasts.Fast.answer(r, Spec.Question.Count{branch()})))))

def reads(n: Nat, +r: Fasts.Fast, +k: Nat, acc: Nat) -> Nat:
  match n:
    case 0n:
      acc
    case 1n+p:
      reads(p, r, k, Nat.add(acc, String.length(words(Fasts.Fast.read(r, branch(), k, "f1")))))

def count(m: Maybe<&2, Spec.Reply>) -> Nat:
  match m:
    case Some{Spec.Reply.Number{n}}:
      n
    case _:
      0n

def pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def views(n: Nat, +r: Fasts.Fast, acc: Nat) -> Nat:
  match n:
    case 0n:
      acc
    case 1n+p:
      views(p, r, Nat.add(acc, String.length(words(Fasts.Fast.view(r, "w", branch(), "f1")))))

def arg2(xs: List<&1, String>) -> Nat:
  match xs:
    case Con{a, Con{b, Con{c, r}}}:
      Maybe.default(&2, Nat, Nat.read(c), 0n)
    case _:
      0n

def plen(m: Maybe<&2, Works.Plan>) -> Nat:
  match m:
    case None{}:
      1n
    case Some{x}:
      2n

def olen(m: Maybe<&2, Works.Open>) -> Nat:
  match m:
    case None{}:
      1n
    case Some{x}:
      2n

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

def klen(kn: Known.Known()) -> Nat:
  ksize(kn)

def voted(+kn: Known.Known(), +fs: Facts.Plain(), m: Maybe<&2, Works.Plan>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{Works.Plan{+st, +x}}:
      klen(Fasts.Table.voted(kn, Facts.Facts.add(fs, Types.Fact.Vote{"a", st, x}), st, Types.Fact.Vote{"a", st, x}))

def casted(+kn: Known.Known(), +fs: Facts.Plain(), m: Maybe<&2, Works.Plan>) -> Nat:
  match m:
    case Some{Works.Plan{Types.Step.At{+c, +k, +t}, +x}}:
      klen(Known.Known.cast(kn, Facts.Facts.add(fs, Types.Fact.Vote{"a", Types.Step.At{c, k, t}, x}), c, k, Known.Known.walk(kn, Types.Fact.Vote{"a", Types.Step.At{c, k, t}, x})))
    case _:
      0n

def olen2(m: Maybe<&2, Lines.State>) -> Nat:
  match m:
    case None{}:
      1n
    case Some{x}:
      2n

def nexted(+kn: Known.Known(), +fs: Facts.Plain(), m: Maybe<&2, Works.Plan>) -> Nat:
  match m:
    case Some{Works.Plan{Types.Step.At{+c, +k, +t}, +x}}:
      olen2(Known.Known.next.of(Known.Known.walk(kn, Types.Fact.Vote{"a", Types.Step.At{c, k, t}, x}), Facts.Facts.add(fs, Types.Fact.Vote{"a", Types.Step.At{c, k, t}, x}), c, k, Known.Known.find(kn, c), Known.Known.over(c, Known.Known.find(kn, Known.Known.root(c)))))
    case _:
      0n

def seated(+kn: Known.Known(), +fs: Facts.Plain(), m: Maybe<&2, Works.Plan>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{Works.Plan{+st, x}}:
      blen(Fasts.Seat.cast(kn, fs, "a", st))

def rlen(m: Maybe<&2, Lines.Rule>) -> Nat:
  match m:
    case None{}:
      1n
    case Some{x}:
      2n

def rlen2(m: Maybe<&2, Nat>) -> Nat:
  match m:
    case None{}:
      1n
    case Some{x}:
      2n

def wlen(m: Maybe<&2, List<&2, U32>>) -> Nat:
  match m:
    case None{}:
      1n
    case Some{x}:
      2n

def fsize(f: Files.Files()) -> Nat:
  match f:
    case Files.Files{d}:
      3n

def fset(m: Maybe<&2, Files.Files()>, mode: Nat) -> Nat:
  match m:
    case None{}:
      0n
    case Some{x}:
      match mode:
        case 0n:
          fsize(Files.Files.set(x, "f1", Some{[1, 2, 3]}))
        case 1n:
          wlen(Files.Files.get(x, "f1"))
        case 2n:
          fsize(Files.Files.set(x, "newpath", Some{[1, 2, 3]}))
        case 3n+q:
          5n

def csize(f: Facts.Plain()) -> Nat:
  match f:
    case Crits.Crit.Tip{}:
      0n
    case Crits.Crit.Leaf{k, v}:
      1n
    case Crits.Crit.Fork{r, p, e, z, o}:
      2n

def csize2(f: Crits.Crit<Types.Ask>) -> Nat:
  match f:
    case Crits.Crit.Tip{}:
      0n
    case Crits.Crit.Leaf{k, v}:
      1n
    case Crits.Crit.Fork{r, p, e, z, o}:
      2n

def tops(m: Maybe<&2, Crits.Crit<Types.Ask>>) -> Crits.Crit<Types.Ask>:
  match m:
    case None{}:
      Crits.Crit.new(Types.Ask)
    case Some{x}:
      x

def vlen(m: Maybe<&2, Lines.State>) -> List<&2, Types.Entry>:
  match m:
    case None{}:
      []
    case Some{Lines.State{vs, k}}:
      vs

def state(m: Maybe<&2, Lines.State>) -> Lines.State:
  match m:
    case None{}:
      Lines.State{[], 0n}
    case Some{st}:
      st

def pk() -> Types.Pick:
  Types.Pick{Types.Ask{id("nope"), 3n, Spec.Request.Write{branch(), "g", None{}}}, Lines.Pins.plain(0n)}

def grown(+kn: Known.Known(), +fs: Facts.Plain(), m: Maybe<&2, Works.Plan>) -> Nat:
  match m:
    case Some{Works.Plan{Types.Step.At{+c, +k, +t}, +x}}:
      klen(Contents.Known.grow(kn, Known.Known.cast(kn, Facts.Facts.add(fs, Types.Fact.Vote{"a", Types.Step.At{c, k, t}, x}), c, k, Known.Known.walk(kn, Types.Fact.Vote{"a", Types.Step.At{c, k, t}, x})), Facts.Facts.add(fs, Types.Fact.Vote{"a", Types.Step.At{c, k, t}, x}), c))
    case _:
      0n

def plen2(m: Maybe<&2, Types.Pick>) -> Nat:
  match m:
    case None{}:
      1n
    case Some{x}:
      2n

def slotof(m: Maybe<&2, Works.Plan>) -> Nat:
  match m:
    case Some{Works.Plan{Types.Step.At{c, k, t}, x}}:
      k
    case _:
      0n

def wfs(kn: Known.Known(), m: Maybe<&2, Works.Plan>) -> List<&2, Types.Fact>:
  match m:
    case Some{Works.Plan{st, x}}:
      Maybe.default(&2, List<&2, Types.Fact>, Known.Known.walk(kn, Types.Fact.Vote{"a", st, x}), [])
    case _:
      []

def one(mode: Nat, +b: Ledgers.Line, +kn: Known.Known(), +fs: Facts.Plain(), +m: Maybe<&2, Works.Plan>) -> Nat:
  match mode:
    case 0n:
      1n
    case 1n:
      plen(Works.Work.plan(kn, fs, "a"))
    case 2n:
      plen(Works.Work.propose(kn, fs, "a"))
    case 3n:
      voted(kn, fs, m)
    case 4n:
      casted(kn, fs, m)
    case 5n:
      nexted(kn, fs, m)
    case 6n:
      seated(kn, fs, m)
    case 7n:
      klen(Known.Known.learn(kn, fs, b))
    case 8n:
      klen(Fasts.Learn.asked(kn, fs, Spec.Request.Write{b, "g", None{}}))
    case 9n:
      List.length(&2, Types.Fact, Facts.Facts.list(Fasts.Asked.take("a", fs, Facts.Facts.asked(fs, id("q"), Spec.Request.Write{b, "g", None{}}))))
    case 10n:
      plen(Works.Work.follow(kn, fs, "a", Facts.Facts.list(fs)))
    case 11n:
      plen(Works.Work.pass.all(Facts.Facts.list(fs), kn, fs, "a"))
    case 12n:
      klen(Fasts.Learn.work(kn, fs))
    case 13n:
      rlen(Known.Known.rule.next(kn, fs, b, Known.Known.find(kn, b)))
    case 14n:
      Lines.Line.bound(Facts.Facts.list(fs), b)
    case 15n:
      List.length(&2, Rounds.Ballot, Works.Work.ballots(kn, fs, b, 5n))
    case 16n:
      klen(Known.Known.voted(kn, b, True{}))
    case 17n:
      klen(Known.Known.contents(kn))
    case 18n:
      olen2(Lines.Line.step(fs, Some{[]}, b, Lines.State{[], 3n}))
    case 19n:
      Lines.Line.era(b, vlen(Known.Known.find(kn, b)))
    case 20n:
      blen(Known.Known.made(kn, b, [], id("x100")))
    case 21n:
      List.length(&2, U32, Known.Id.key(id("x100")))
    case 22n:
      olen(Works.Work.open(kn, fs, "a", b))
    case 23n:
      plen(Works.Work.offer(kn, fs, [], "a", Types.Ask{id("x100"), 50n, Spec.Request.Write{b, "g", None{}}}))
    case 24n:
      List.length(&2, Types.Ask, Works.Work.ready(Facts.Facts.list(fs), kn, fs, Facts.Facts.list(fs), "a"))
    case 25n:
      List.length(&2, Types.Fact, Facts.Facts.list(fs))
    case 26n:
      Facts.Seq.peak(Facts.Facts.list(fs))
    case 27n:
      Facts.Facts.fuel(Facts.Facts.add(fs, Types.Fact.Vote{"zz", Types.Step.Broken{}, Types.Cast.Pass{0n}}))
    case 28n:
      grown(kn, fs, m)
    case 29n:
      rlen(Lines.Line.rule(Some{vlen(Known.Known.find(kn, root()))}, b, vlen(Known.Known.find(kn, b))))
    case 30n:
      olen2(Lines.Line.step(fs, Some{vlen(Known.Known.find(kn, root()))}, b, state(Known.Known.find(kn, b))))
    case 31n:
      List.length(&2, Types.Entry, Lines.State.versions(Lines.State.put(vlen(Known.Known.find(kn, b)), 7n, pk())))
    case 32n:
      klen(Known.Known.joined(kn, fs, Types.Fact.Ask{Types.Ask{id("q"), 5n, Spec.Request.Write{b, "g", None{}}}}))
    case 33n:
      List.length(&2, Types.Fact, Known.Known.facts(kn, fs))
    case 34n:
      List.length(&2, Types.Fact, Known.Open.put(Known.Known.facts(kn, fs), Types.Fact.Vote{"a", Types.Step.At{b, 7n, 0n}, Types.Cast.Pass{0n}}))
    case 35n:
      olen2(Lines.Line.step.in(Known.Known.facts(kn, fs), Some{vlen(Known.Known.find(kn, root()))}, b, state(Known.Known.find(kn, b))))
    case 36n:
      Lines.Line.bound(Known.Known.facts(kn, fs), b)
    case 37n:
      klen(Known.Known.learn(kn, fs, b))
    case 38n:
      klen(Known.Known.moved(kn, fs, Some{Known.Known.facts(kn, fs)}, 0n, Known.Shelf.tops(Known.Known.shelf(kn)), Known.Shelf.merges(Known.Known.shelf(kn))))
    case 39n:
      rlen(Known.Known.rule.next(kn, fs, b, Known.Known.find(kn, b)))
    case 40n:
      klen(Known.Known.voted(kn, b, True{}))
    case 41n:
      plen2(Rounds.Slot.decided(Rounds.Slot.ballots(wfs(kn, m), b, slotof(m)), ["a"], slotof(m)))
    case 42n:
      olen2(Lines.Line.step.in(wfs(kn, m), Some{vlen(Known.Known.find(kn, root()))}, b, state(Known.Known.find(kn, b))))
    case 43n:
      List.length(&2, Types.Entry, Lines.State.versions(Known.Known.go.in(wfs(kn, m), b, state(Known.Known.find(kn, b)), Some{vlen(Known.Known.find(kn, root()))})))
    case 44n:
      String.length(Rounds.Turn.of(["a", "b", "c"], slotof(m)))
    case 45n:
      List.length(&2, Types.Fact, wfs(kn, m))
    case 46n:
      List.length(&2, Rounds.Ballot, Rounds.Slot.ballots(wfs(kn, m), b, slotof(m)))
    case 47n:
      klen(Known.Known.hold(kn, Known.Held{b, 99999n, 5n, Files.Files.new(), []}))
    case 48n:
      rlen2(Known.Known.depth(kn, b, 100n))
    case 49n:
      klen(Contents.Known.fill.new(kn, fs, b, 100n))
    case 50n:
      List.length(&2, U32, Known.Held.key(b, 100n))
    case 51n:
      klen(Known.Known.deeper(Known.Known.contents(kn)))
    case 52n:
      klen(Known.Known.spared(True{}, kn))
    case 54n:
      fset(Contents.Content.of(kn, fs, b, 100n), 0n)
    case 55n:
      fset(Contents.Content.of(kn, fs, b, 100n), 1n)
    case 56n:
      fset(Contents.Content.of(kn, fs, b, 100n), 2n)
    case 57n:
      fset(Contents.Content.of(kn, fs, b, 100n), 3n)
    case 60n:
      csize(Facts.Facts.add(fs, Types.Fact.Ask{Types.Ask{id("x77777"), 99999n, Spec.Request.Write{b, "g", Some{[1, 2, 3]}}}}))
    case 61n:
      csize2(Known.Tops.set(tops(Known.Shelf.tops(Known.Known.shelf(kn))), Types.Ask{id("x77777"), 99999n, Spec.Request.Write{b, "f1", Some{[1, 2, 3]}}}, Some{Known.Place{"w", b, "f1"}}))
    case 62n:
      List.length(&2, Types.Fact, Known.Open.put(Known.Known.facts(kn, fs), Types.Fact.Ask{Types.Ask{id("x77777"), 99999n, Spec.Request.Write{b, "g", Some{[1, 2, 3]}}}}))
    case 63n:
      klen(Fasts.Learn.asked(kn, fs, Spec.Request.Write{b, "g", None{}}))
    case 64n:
      List.length(&2, U32, Known.Place.key(Known.Place{"w", b, "f1"}))
    case 65n:
      blen(Known.Fact.waits(Known.Scene{kn, fs}, Types.Fact.Ask{Types.Ask{id("x77777"), 99999n, Spec.Request.Write{b, "g", Some{[1, 2, 3]}}}}))
    case 66n:
      List.length(&2, U32, Coded.Fact.words(Types.Fact.Ask{Types.Ask{id("x77777"), 99999n, Spec.Request.Write{b, "g", Some{[1, 2, 3]}}}}))
    case 67n:
      csize(Facts.Facts.add(fs, Types.Fact.Vote{"a", Types.Step.At{b, 99999n, 0n}, Types.Cast.Pass{0n}}))
    case 68n:
      blen(Fasts.Seat.cast(kn, fs, "a", Types.Step.At{b, 99999n, 0n}))
    case 70n:
      List.length(&2, Types.Entry, vlen(Known.Known.find(kn, b)))
    case 71n:
      klen(Contents.Known.fill.new(kn, fs, b, Nat.sub(List.length(&2, Types.Entry, vlen(Known.Known.find(kn, b))), 1n)))
    case 72n:
      rlen2(Known.Known.depth(kn, b, Nat.sub(List.length(&2, Types.Entry, vlen(Known.Known.find(kn, b))), 1n)))
    case 73n:
      klen(Known.Known.learn(kn, fs, b))
    case 74n:
      List.length(&2, Types.Fact, Known.Open.of(Known.Known.facts(kn, fs), Known.Scene{kn, fs}))
    case 53n+q:
      klen(Known.Known.join(Known.Known.voted(kn, b, True{}), Known.Known.spared(True{}, kn)))


def prof(n: Nat, +mode: Nat, +b: Ledgers.Line, +kn: Known.Known(), +fs: Facts.Plain(), +m: Maybe<&2, Works.Plan>, acc: Nat) -> Nat:
  match n:
    case 0n:
      acc
    case 1n+p:
      prof(p, mode, b, kn, fs, m, Nat.add(acc, one(mode, b, kn, fs, m)))


def nat(t: String) -> Nat:
  Maybe.default(&2, Nat, Nat.read(t), 0n)

def build(+n: Nat) -> Fasts.Fast:
  writes(n, final())

def pending(r: Fasts.Fast, +b: Ledgers.Line) -> Fasts.Fast:
  Fasts.Fast.does(r, Nodes.Act.Ask{id("last"), Spec.Request.Write{b, "zz", Some{[104, 105, 106]}}})

def size(r: Fasts.Fast) -> Nat:
  match r:
    case Fasts.Fast{Nodes.Raw{name, ws, ms, st, fs, ps}, kn}:
      Nat.add(klen(kn), blen(st))

# whole deeds, on the node r (idle) and q (one ask waits)
def deed(mode: Nat, +b: Ledgers.Line, +r: Fasts.Fast, +q: Fasts.Fast) -> Nat:
  match mode:
    case 0n:
      size(pending(r, b))
    case 1n:
      size(Fasts.Fast.does(q, Nodes.Act.Work{}))
    case 2n:
      size(Fasts.Fast.does(r, Nodes.Act.Work{}))
    case 3n:
      String.length(words(Fasts.Fast.view(r, "w", b, "f1")))
    case 4n:
      String.length(show(Fasts.Fast.answer(r, Spec.Question.Count{b})))
    case 5n:
      String.length(words(Fasts.Fast.read(r, b, 3n, "f1")))
    case 6n+x:
      String.length(show(Fasts.Fast.answer(r, Spec.Question.Status{b, id("x5")})))

def deeds(n: Nat, +mode: Nat, +b: Ledgers.Line, +r: Fasts.Fast, +q: Fasts.Fast, acc: Nat) -> Nat:
  match n:
    case 0n:
      acc
    case 1n+p:
      deeds(p, mode, b, r, q, Nat.add(acc, deed(mode, b, r, q)))

def parts(mode: Nat, +b: Ledgers.Line, q: Fasts.Fast, +k: Nat) -> Nat:
  match q:
    case Fasts.Fast{Nodes.Raw{name, ws, ms, st, fs, ps}, kn}:
      +fs = fs
      +kn = kn
      prof(k, mode, b, kn, fs, Works.Work.plan(kn, fs, "a"), 0n)

def pick.if(lt: Bool, +mode: Nat, +b: Ledgers.Line, +r: Fasts.Fast, +q: Fasts.Fast, +k: Nat) -> Nat:
  match lt:
    case True{}:
      parts(mode, b, q, k)
    case False{}:
      deeds(k, Nat.sub(mode, 100n), b, r, q, 0n)

def pick(+mode: Nat, +b: Ledgers.Line, +r: Fasts.Fast, +q: Fasts.Fast, +k: Nat) -> Nat:
  pick.if(Nat.is_lt(mode, 100n), mode, b, r, q, k)

def loop(ms: List<&2, String>, +b: Ledgers.Line, +r: Fasts.Fast, +q: Fasts.Fast, +k: Nat) -> IO(Unit):
  match ms:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{+m, rest}:
      do IO<Unit>:
        t0 : Nat <- IO.now()
        IO.write(String.append(String.append("mode ", m), String.append(" r=", Nat.show(pick(nat(m), b, r, q, k)))))
        t1 : Nat <- IO.now()
        IO.print(String.append(" ms=", Nat.show(Nat.sub(t1, t0))))
        loop(rest, b, r, q, k)

def copy(xs: List<&1, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      []
    case Con{x, r}:
      x <> copy(r)

def start4(+b: Ledgers.Line, +r: Fasts.Fast, +q: Fasts.Fast, +k: Nat, rest: List<&2, String>) -> IO(Unit):
  do IO<Unit>:
    IO.print(String.append("pending size=", Nat.show(size(q))))
    loop(rest, b, r, q, k)

def start5(+b: Ledgers.Line, +r: Fasts.Fast, +k: Nat, rest: List<&2, String>) -> IO(Unit):
  start4(b, r, pending(r, b), k, rest)

def start3(+r: Fasts.Fast, +k: Nat, rest: List<&2, String>, t0: Nat) -> IO(Unit):
  do IO<Unit>:
    IO.write(String.append("build size=", Nat.show(size(r))))
    t1 : Nat <- IO.now()
    IO.print(String.append(" ms=", Nat.show(Nat.sub(t1, t0))))
    start5(branch(), r, k, rest)

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
