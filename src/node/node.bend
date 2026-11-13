import Base
import ../branch/merges.bend as Merges
import ../group/owners.bend as Owners
import ../resource/formats.bend as Formats
import ../resource/resources.bend as Resources
import ../shared/replica.bend as Replicas
import ../shared/shared/ledger.bend as Ledgers
import ../shared/shared/rope.bend as Ropes
import ../shared/shared/shared/depot.bend as Depots
import ../shared/shared/shared/pack.bend as Packs
import ../shared/shared/shared/shared/code.bend as Codes
import ../shared/shared/shared/shared/crit.bend as Crits
import ../shared/shared/shared/shared/hash.bend as Hashes
import ../shared/shared/shared/shared/shared.bend as Shared
import ../shared/shared/shared/shared/side.bend as Sides
import ../shared/shared/shared/text.bend as Texts
import ../shared/shared/tree.bend as Trees
import ../shared/vend.bend as Vend
import ../store/kept.bend as Store
import ../writer/reads.bend as Reads
import ../writer/requests.bend as Requests

# The pure core of a Vend Node (README): what it answers, and the rules of
# Vend's kernel. A Vend Node is a replica (Replicas) of the machine of Vend
# (Requests.Ask.machine): a store is a root line, a branch is a sub line, the
# owners of a line are its voters, a version is a taken request, and a mark
# is a label. So every answer here is a read of a ledger, and what Replicas
# proves of every machine holds of Vend: a node only grows, a history is one,
# and what a line knows is final.
#
# A def here takes the ledger d as a template, and the kernel kern where it
# reads a history. transport/spec.bend carries the core over IO.

# The kernel of Vend
# ------------------

# that the kernel kern obeys the rules of Vend: what it does with a request
# is what Ask.act says, and what it asks by itself is what Own.due says
def Kernel.Rules(-d: Vend.Led(), -kern: Vend.Kern(d)) -> Type:
  (
    @l: Vend.L(
      d
    ) -> @t: Replicas.Tip -> @c: Ledgers.Line -> @i: Ledgers.Id -> @q: Requests.Ask -> {
      Replicas.Kernel.change(Requests.Ask.machine(), d, kern)(l)(t)(c)(i)(q)
        == Owners.Ask.act(~d, l, t, c, i, q): Maybe<&2, Replicas.Act>
    }
  )
    & (
      @hs: Replicas.Tops() -> @l: Vend.L(
        d
      ) -> @c: Ledgers.Line -> {
        Replicas.Kernel.follow(Requests.Ask.machine(), d, kern)(hs)(l)(c)
          == Owners.Own.due(~d, hs, l, c): Maybe<&2, Maybe<&2, Replicas.Request<Requests.Ask>>>
      }
    )

# the kernel of Vend: a kernel, and the proof that it obeys the rules
def Kernel(-d: Vend.Led()) -> Type:
  &kern: Vend.Kern(d) -> Kernel.Rules(d, kern)

# Proofs of the reads of Own.due
# ------------------------------

# a line is the same line as itself
def Cov.line_refl(c: Ledgers.Line) -> {Ledgers.Line.is_eq(c, c) == True{}: Bool}:
  match c:
    case Ledgers.Line{+r, None{}}:
      %Equal.sym(Bool, Hashes.Hash.is_eq(r, r), True{}, Hashes.Hash.is_eq_refl(r)): {
        List.all.if(u => Ledgers.Sub.is_eq(None{}, None{}), _) == True{}: Bool
      }
      {==}
    case Ledgers.Line{+r, Some{+b}}:
      %Equal.sym(Bool, Hashes.Hash.is_eq(r, r), True{}, Hashes.Hash.is_eq_refl(r)): {
        List.all.if(u => Ledgers.Sub.is_eq(Some{b}, Some{b}), _) == True{}: Bool
      }
      Texts.String.eq_refl(b)

# an "any" whose rest holds holds
def Cov.any_rest(s: Bool, -rest: Unit -> Bool) -> {rest(Unit{}) == True{}: Bool} -> {List.any.if(rest, s) == True{}: Bool}:
  match s:
    case True{}:
      h => {==}
    case False{}:
      h => h

# a list of lines that starts with c holds c
def Cov.head(+c: Ledgers.Line, rest: List<&2, Ledgers.Line>) -> {
  List.contains(~Ledgers.Line, ~Ledgers.Line.is_eq, c <> rest, c) == True{}: Bool
}:
  %Equal.sym(Bool, Ledgers.Line.is_eq(c, c), True{}, Cov.line_refl(c)): {
    List.any.if(u => List.contains(~Ledgers.Line, ~Ledgers.Line.is_eq, rest, c), _) == True{}: Bool
  }
  {==}

# what Vend asks by itself is Own.due, by the rules
def Rd.rule(-d: Vend.Led(), -kern: Vend.Kern(d), rules: Kernel.Rules(d, kern)) -> @hs: Replicas.Tops() -> @l: Vend.L(d) -> @c: Ledgers.Line -> {
  Replicas.Kernel.follow(Requests.Ask.machine(), d, kern)(hs)(l)(c)
    == Owners.Own.due(~d, hs, l, c): Maybe<&2, Maybe<&2, Replicas.Request<Requests.Ask>>>
}:
  match rules:
    case Tuple{fst, snd}:
      snd

# two heads that Heads.same calls the same are the same
def Rd.heq(m1: Maybe<&2, Replicas.Tip>, m2: Maybe<&2, Replicas.Tip>) -> {
  Shared.Maybe.is_eq(~Replicas.Tip, ~(x => y => Codes.Code.is_eq(~Replicas.Tip, ~Replicas.Tip.code, x, y)), m1, m2) == True{}: Bool
} -> {m1 == m2: Maybe<&2, Replicas.Tip>}:
  Shared.Maybe.is_eq_sound(
    ~Replicas.Tip,
    ~(x => y => Codes.Code.is_eq(~Replicas.Tip, ~Replicas.Tip.code, x, y)),
    x => y => Shared.Eq.sound(
      ~Replicas.Tip,
      ~(u => v => Codes.Code.is_eq(~Replicas.Tip, ~Replicas.Tip.code, u, v)),
      Codes.Code.eq_laws(~Replicas.Tip, ~(Replicas.Tip.code, (Replicas.Tip.code.read, t => r => Replicas.Tip.code_read(t, r)))),
      x,
      y
    ),
    m1,
    m2
  )

# a value that some data is stays, once the data is known (m)
def Rd.whole(
  ~A: Data,
  ~enc: A -> List<&2, U32> -> List<&2, U32>,
  ~dec: List<&2, U32> -> Maybe<&2, Codes.Read<A>>,
  m: Maybe<&2, List<&2, U32>>,
  -m2: Maybe<&2, List<&2, U32>>,
  hm: @w: List<&2, U32> -> {m == Some{w}: Maybe<&2, List<&2, U32>>} -> {m2 == Some{w}: Maybe<&2, List<&2, U32>>},
  -x: A
) -> {Codes.Code.whole.of(~A, ~enc, ~dec, m) == Some{x}: Maybe<&2, A>}
  -> {Codes.Code.whole.of(~A, ~enc, ~dec, m2) == Some{x}: Maybe<&2, A>}:
  match m:
    case None{}:
      e => Empty.absurd(
        {Codes.Code.whole.of(~A, ~enc, ~dec, m2) == Some{x}: Maybe<&2, A>},
        Shared.Maybe.none_ne_some(A, x, e)
      )
    case Some{y}:
      e =>
        %Equal.sym(Maybe<&2, List<&2, U32>>, m2, Some{y}, hm(y)({==})): {
          Codes.Code.whole.of(~A, ~enc, ~dec, _) == Some{x}: Maybe<&2, A>
        }
        e

# a known read stays, once the read is known (m)
def Rd.known(
  ~A: Data,
  ~enc: A -> List<&2, U32> -> List<&2, U32>,
  ~dec: List<&2, U32> -> Maybe<&2, Codes.Read<A>>,
  m: Maybe<&2, Maybe<&2, List<&2, U32>>>,
  -m2: Maybe<&2, Maybe<&2, List<&2, U32>>>,
  hm: @w: Maybe<&2, List<&2, U32>> -> {m == Some{w}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
    -> {m2 == Some{w}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
  -x: Maybe<&2, A>
) -> {Replicas.Tip.known(~A, ~enc, ~dec, m) == Some{x}: Maybe<&2, Maybe<&2, A>>}
  -> {Replicas.Tip.known(~A, ~enc, ~dec, m2) == Some{x}: Maybe<&2, Maybe<&2, A>>}:
  match m:
    case None{}:
      e => Empty.absurd(
        {Replicas.Tip.known(~A, ~enc, ~dec, m2) == Some{x}: Maybe<&2, Maybe<&2, A>>},
        Shared.Maybe.none_ne_some(Maybe<&2, A>, x, e)
      )
    case Some{y}:
      e =>
        %Equal.sym(Maybe<&2, Maybe<&2, List<&2, U32>>>, m2, Some{y}, hm(y)({==})): {
          Replicas.Tip.known(~A, ~enc, ~dec, _) == Some{x}: Maybe<&2, Maybe<&2, A>>
        }
        e

# a map of a value that stays stays
def Rd.map(
  -A: Data,
  -B: Data,
  m: Maybe<&2, A>,
  -m2: Maybe<&2, A>,
  hm: @y: A -> {m == Some{y}: Maybe<&2, A>} -> {m2 == Some{y}: Maybe<&2, A>},
  -f: A -> B,
  -x: B
) -> {Maybe.map(&2, A, B, f, m) == Some{x}: Maybe<&2, B>} -> {Maybe.map(&2, A, B, f, m2) == Some{x}: Maybe<&2, B>}:
  match m:
    case None{}:
      e => Empty.absurd({Maybe.map(&2, A, B, f, m2) == Some{x}: Maybe<&2, B>}, Shared.Maybe.none_ne_some(B, x, e))
    case Some{y}:
      e =>
        %Equal.sym(Maybe<&2, A>, m2, Some{y}, hm(y)({==})): {Maybe.map(&2, A, B, f, _) == Some{x}: Maybe<&2, B>}
        e

# what Due.then gives stays, when each step stays
def Rd.then(
  -A: Data,
  m: Maybe<&2, A>,
  -k1: A -> Maybe<&2, Maybe<&2, Replicas.Request<Requests.Ask>>>,
  -k2: A -> Maybe<&2, Maybe<&2, Replicas.Request<Requests.Ask>>>,
  -x: Maybe<&2, Replicas.Request<Requests.Ask>>,
  hk: @v: A -> {k1(v) == Some{x}: Maybe<&2, Maybe<&2, Replicas.Request<Requests.Ask>>>}
    -> {k2(v) == Some{x}: Maybe<&2, Maybe<&2, Replicas.Request<Requests.Ask>>>}
) -> {Owners.Due.then(~A, m, k1) == Some{x}: Maybe<&2, Maybe<&2, Replicas.Request<Requests.Ask>>>}
  -> {Owners.Due.then(~A, m, k2) == Some{x}: Maybe<&2, Maybe<&2, Replicas.Request<Requests.Ask>>>}:
  match m:
    case None{}:
      x1 => x1
    case Some{value}:
      x1 => hk(value)(x1)

# the nodes of a group stay as the ledger grows
def Rd.nodes(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b),
  +h: Maybe<&2, Hashes.Hash>,
  +gn: String,
  -ns: List<&2, String>
) -> {Owners.Group.nodes(~d, a, h, gn) == Some{ns}: Maybe<&2, List<&2, String>>}
  -> {Owners.Group.nodes(~d, b, h, gn) == Some{ns}: Maybe<&2, List<&2, String>>}:
  Rd.map(
    List<&2, Owners.Group>,
    List<&2, String>,
    Owners.Groups.in(~d, a, h),
    Owners.Groups.in(~d, b, h),
    gs => ge => Rd.map(
      List<&2, Trees.Binding>,
      List<&2, Owners.Group>,
      Vend.Tree.range(~d, a, h, [2]),
      Vend.Tree.range(~d, b, h, [2]),
      bs => eb => Replicas.Hist.range(~Requests.Ask.machine(), ~d, a, b, h, [2], bs, g)(eb),
      Owners.Groups.of,
      gs
    )(ge),
    gs => Owners.Group.nodes.of(gs, gn),
    ns
  )

# a taken request stays as the ledger grows
def Rd.taken(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b),
  +t: Replicas.Tip,
  +n: U32,
  -y: Replicas.Taken
) -> {Replicas.Tip.taken(~Requests.Ask.machine(), ~d, a, t, n) == Some{y}: Maybe<&2, Replicas.Taken>}
  -> {Replicas.Tip.taken(~Requests.Ask.machine(), ~d, b, t, n) == Some{y}: Maybe<&2, Replicas.Taken>}:
  x => Replicas.Sim.taken_eq.at(~Requests.Ask.machine(), ~d, a, b, t, n, y, g, Trees.Look.value(Trees.Ops.look(Ledgers.Kind.L(Requests.Ask, Replicas.Led.kind((Requests.Ask, (Requests.Ask.code, Requests.Ask.code.read, x => r => Requests.Ask.code_read(x, r)), Requests.Ask.arrival, Requests.Ask.governs, Requests.Key.seal), d)), Replicas.Led.tree((Requests.Ask, (Requests.Ask.code, Requests.Ask.code.read, x => r => Requests.Ask.code_read(x, r)), Requests.Ask.arrival, Requests.Ask.governs, Requests.Key.seal), d), a, Replicas.Tip.log(t), [3, n])), {==}, x)

# the newest version stays as the ledger grows, once whether there is none
# is known (z)
def Rd.newest.at(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b),
  +ts: Replicas.Tip,
  z: Bool,
  -y: Maybe<&2, Ledgers.Id>
) -> {
  Shared.Bool.when(
    Maybe<&2, Maybe<&2, Ledgers.Id>>,
    z,
    u => Some{None{}},
    u => Maybe.bind(
      &2,
      Replicas.Taken,
      Maybe<&2, Ledgers.Id>,
      Replicas.Tip.taken(~Requests.Ask.machine(), ~d, a, ts, U32.sub(Replicas.Tip.count(ts), 1)),
      x => Some{Some{Replicas.Taken.id(x)}}
    )
  )
    == Some{y}: Maybe<&2, Maybe<&2, Ledgers.Id>>
} -> {
  Shared.Bool.when(
    Maybe<&2, Maybe<&2, Ledgers.Id>>,
    z,
    u => Some{None{}},
    u => Maybe.bind(
      &2,
      Replicas.Taken,
      Maybe<&2, Ledgers.Id>,
      Replicas.Tip.taken(~Requests.Ask.machine(), ~d, b, ts, U32.sub(Replicas.Tip.count(ts), 1)),
      x => Some{Some{Replicas.Taken.id(x)}}
    )
  )
    == Some{y}: Maybe<&2, Maybe<&2, Ledgers.Id>>
}:
  match z:
    case False{}:
      x => (%Equal.sym(Maybe<&2, Maybe<&2, Ledgers.Id>>, Maybe.bind(&2, Replicas.Taken, Maybe<&2, Ledgers.Id>, Codes.Code.whole.of(Replicas.Taken, Replicas.Taken.code, Replicas.Taken.code.read, Trees.Look.value(Trees.Ops.look(Ledgers.Kind.L(Requests.Ask, Replicas.Led.kind((Requests.Ask, (Requests.Ask.code, Requests.Ask.code.read, x => r => Requests.Ask.code_read(x, r)), Requests.Ask.arrival, Requests.Ask.governs, Requests.Key.seal), d)), Replicas.Led.tree((Requests.Ask, (Requests.Ask.code, Requests.Ask.code.read, x => r => Requests.Ask.code_read(x, r)), Requests.Ask.arrival, Requests.Ask.governs, Requests.Key.seal), d), b, Replicas.Tip.log(ts), [3, U32.sub(Replicas.Tip.count(ts), 1)]))), x => Some{Some{Replicas.Taken.id(x)}}), Some{y}, Shared.Maybe.bind_kept(Replicas.Taken, Maybe<&2, Ledgers.Id>, Codes.Code.whole.of(Replicas.Taken, Replicas.Taken.code, Replicas.Taken.code.read, Trees.Look.value(Trees.Ops.look(Ledgers.Kind.L(Requests.Ask, Replicas.Led.kind((Requests.Ask, (Requests.Ask.code, Requests.Ask.code.read, x => r => Requests.Ask.code_read(x, r)), Requests.Ask.arrival, Requests.Ask.governs, Requests.Key.seal), d)), Replicas.Led.tree((Requests.Ask, (Requests.Ask.code, Requests.Ask.code.read, x => r => Requests.Ask.code_read(x, r)), Requests.Ask.arrival, Requests.Ask.governs, Requests.Key.seal), d), a, Replicas.Tip.log(ts), [3, U32.sub(Replicas.Tip.count(ts), 1)]))), Codes.Code.whole.of(Replicas.Taken, Replicas.Taken.code, Replicas.Taken.code.read, Trees.Look.value(Trees.Ops.look(Ledgers.Kind.L(Requests.Ask, Replicas.Led.kind((Requests.Ask, (Requests.Ask.code, Requests.Ask.code.read, x => r => Requests.Ask.code_read(x, r)), Requests.Ask.arrival, Requests.Ask.governs, Requests.Key.seal), d)), Replicas.Led.tree((Requests.Ask, (Requests.Ask.code, Requests.Ask.code.read, x => r => Requests.Ask.code_read(x, r)), Requests.Ask.arrival, Requests.Ask.governs, Requests.Key.seal), d), b, Replicas.Tip.log(ts), [3, U32.sub(Replicas.Tip.count(ts), 1)]))), x => Some{Some{Replicas.Taken.id(x)}}, x => Some{Some{Replicas.Taken.id(x)}}, y, a1 => x1 => Rd.taken(~d, a, b, g, ts, U32.sub(Replicas.Tip.count(ts), 1), a1)(x1), a1 => x1 => x1)(x)) : {_ == Some{y} : Maybe<&2, Maybe<&2, Ledgers.Id>>}; {==})
    case True{}:
      x => x

# the newest version stays as the ledger grows
def Rd.newest(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b),
  +ts: Replicas.Tip,
  -y: Maybe<&2, Ledgers.Id>
) -> {Replicas.Tip.newest(~Requests.Ask.machine(), ~d, a, ts) == Some{y}: Maybe<&2, Maybe<&2, Ledgers.Id>>}
  -> {Replicas.Tip.newest(~Requests.Ask.machine(), ~d, b, ts) == Some{y}: Maybe<&2, Maybe<&2, Ledgers.Id>>}:
  x => (%Equal.sym(Cmp, U32.cmp(Replicas.Tip.count(ts), 0), Trees.Cmp.flip(U32.cmp(0, Replicas.Tip.count(ts))), Trees.U32.cmp_flip(0, Replicas.Tip.count(ts))) : {Shared.Bool.when(Maybe<&2, Maybe<&2, Ledgers.Id>>, Cmp.is_eq(_), u => Some{None{}}, u => Maybe.bind(&2, Replicas.Taken, Maybe<&2, Ledgers.Id>, Replicas.Tip.taken(Requests.Ask.machine(), d, b, ts, U32.sub(Replicas.Tip.count(ts), 1)), x => Some{Some{Replicas.Taken.id(x)}})) == Some{y} : Maybe<&2, Maybe<&2, Ledgers.Id>>}; Rd.newest.at(~d, a, b, g, ts, Cmp.is_eq(Trees.Cmp.flip(U32.cmp(0, Replicas.Tip.count(ts)))), y)((%Trees.U32.cmp_flip(0, Replicas.Tip.count(ts)) : {Shared.Bool.when(Maybe<&2, Maybe<&2, Ledgers.Id>>, Cmp.is_eq(_), u => Some{None{}}, u => Maybe.bind(&2, Replicas.Taken, Maybe<&2, Ledgers.Id>, Replicas.Tip.taken(Requests.Ask.machine(), d, a, ts, U32.sub(Replicas.Tip.count(ts), 1)), x => Some{Some{Replicas.Taken.id(x)}})) == Some{y} : Maybe<&2, Maybe<&2, Ledgers.Id>>}; x)))

# the owner group of a line stays as the ledger grows
def Rd.group(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b),
  +t: Replicas.Tip,
  -y: Maybe<&2, String>
) -> {Owners.Tip.group(~d, a, t) == Some{y}: Maybe<&2, Maybe<&2, String>>}
  -> {Owners.Tip.group(~d, b, t) == Some{y}: Maybe<&2, Maybe<&2, String>>}:
  Rd.known(
    ~String,
    ~Codes.Code.text,
    ~Codes.Code.text.read,
    Replicas.Tree.find(~Requests.Ask.machine(), ~d, a, Replicas.Tip.content(t), Owners.Key.owner()),
    Replicas.Tree.find(~Requests.Ask.machine(), ~d, b, Replicas.Tip.content(t), Owners.Key.owner()),
    w => ew => Replicas.Hist.find(~Requests.Ask.machine(), ~d, a, b, Replicas.Tip.content(t), Owners.Key.owner(), w, g)(ew),
    y
  )

# Own.due.at once the owner group gn is known: it stays as the ledger grows
def Rd.at.group(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b),
  +c: Ledgers.Line,
  +t: Replicas.Tip,
  +ts: Replicas.Tip,
  +gn: String,
  -x: Maybe<&2, Replicas.Request<Requests.Ask>>
) -> {
  Maybe.bind(
    &2,
    Maybe<&2, Ledgers.Id>,
    Maybe<&2, Replicas.Request<Requests.Ask>>,
    Replicas.Tip.newest(~Requests.Ask.machine(), ~d, a, ts),
    mv => Owners.Due.then(
      ~Ledgers.Id,
      mv,
      v => Maybe.map(
        &2,
        List<&2, String>,
        Maybe<&2, Replicas.Request<Requests.Ask>>,
        ns => Owners.Own.due.of(c, t, ts, gn, ns, v),
        Owners.Group.nodes(~d, a, Replicas.Tip.content(ts), gn)
      )
    )
  )
    == Some{x}: Maybe<&2, Maybe<&2, Replicas.Request<Requests.Ask>>>
} -> {
  Maybe.bind(
    &2,
    Maybe<&2, Ledgers.Id>,
    Maybe<&2, Replicas.Request<Requests.Ask>>,
    Replicas.Tip.newest(~Requests.Ask.machine(), ~d, b, ts),
    mv => Owners.Due.then(
      ~Ledgers.Id,
      mv,
      v => Maybe.map(
        &2,
        List<&2, String>,
        Maybe<&2, Replicas.Request<Requests.Ask>>,
        ns => Owners.Own.due.of(c, t, ts, gn, ns, v),
        Owners.Group.nodes(~d, b, Replicas.Tip.content(ts), gn)
      )
    )
  )
    == Some{x}: Maybe<&2, Maybe<&2, Replicas.Request<Requests.Ask>>>
}:
  Shared.Maybe.bind_kept(
    Maybe<&2, Ledgers.Id>,
    Maybe<&2, Replicas.Request<Requests.Ask>>,
    Replicas.Tip.newest(~Requests.Ask.machine(), ~d, a, ts),
    Replicas.Tip.newest(~Requests.Ask.machine(), ~d, b, ts),
    mv => Owners.Due.then(
      ~Ledgers.Id,
      mv,
      v => Maybe.map(
        &2,
        List<&2, String>,
        Maybe<&2, Replicas.Request<Requests.Ask>>,
        ns => Owners.Own.due.of(c, t, ts, gn, ns, v),
        Owners.Group.nodes(~d, a, Replicas.Tip.content(ts), gn)
      )
    ),
    mv => Owners.Due.then(
      ~Ledgers.Id,
      mv,
      v => Maybe.map(
        &2,
        List<&2, String>,
        Maybe<&2, Replicas.Request<Requests.Ask>>,
        ns => Owners.Own.due.of(c, t, ts, gn, ns, v),
        Owners.Group.nodes(~d, b, Replicas.Tip.content(ts), gn)
      )
    ),
    x,
    mv => ev => Rd.newest(~d, a, b, g, ts, mv)(ev),
    mv => Rd.then(
      Ledgers.Id,
      mv,
      v => Maybe.map(
        &2,
        List<&2, String>,
        Maybe<&2, Replicas.Request<Requests.Ask>>,
        ns => Owners.Own.due.of(c, t, ts, gn, ns, v),
        Owners.Group.nodes(~d, a, Replicas.Tip.content(ts), gn)
      ),
      v => Maybe.map(
        &2,
        List<&2, String>,
        Maybe<&2, Replicas.Request<Requests.Ask>>,
        ns => Owners.Own.due.of(c, t, ts, gn, ns, v),
        Owners.Group.nodes(~d, b, Replicas.Tip.content(ts), gn)
      ),
      x,
      +v => Rd.map(
        List<&2, String>,
        Maybe<&2, Replicas.Request<Requests.Ask>>,
        Owners.Group.nodes(~d, a, Replicas.Tip.content(ts), gn),
        Owners.Group.nodes(~d, b, Replicas.Tip.content(ts), gn),
        ns => en => Rd.nodes(~d, a, b, g, Replicas.Tip.content(ts), gn, ns)(en),
        ns => Owners.Own.due.of(c, t, ts, gn, ns, v),
        x
      )
    )
  )

# Own.due.at stays as the ledger grows
def Rd.at(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b),
  +c: Ledgers.Line,
  +t: Replicas.Tip,
  +ts: Replicas.Tip,
  -x: Maybe<&2, Replicas.Request<Requests.Ask>>
) -> {Owners.Own.due.at(~d, a, c, t, ts) == Some{x}: Maybe<&2, Maybe<&2, Replicas.Request<Requests.Ask>>>}
  -> {Owners.Own.due.at(~d, b, c, t, ts) == Some{x}: Maybe<&2, Maybe<&2, Replicas.Request<Requests.Ask>>>}:
  x1 => (%Equal.sym(Maybe<&2, Maybe<&2, Replicas.Request<Requests.Ask>>>, Maybe.bind(&2, Maybe<&2, String>, Maybe<&2, Replicas.Request<Requests.Ask>>, Replicas.Tip.known(String, Codes.Code.text, Codes.Code.text.read, Trees.Look.known(Trees.Ops.look(Ledgers.Kind.L(Requests.Ask, Replicas.Led.kind((Requests.Ask, (Requests.Ask.code, Requests.Ask.code.read, x => r => Requests.Ask.code_read(x, r)), Requests.Ask.arrival, Requests.Ask.governs, Requests.Key.seal), d)), Replicas.Led.tree((Requests.Ask, (Requests.Ask.code, Requests.Ask.code.read, x => r => Requests.Ask.code_read(x, r)), Requests.Ask.arrival, Requests.Ask.governs, Requests.Key.seal), d), b, Replicas.Tip.content(t), [6]))), mg => Owners.Due.then(String, mg, +g => Maybe.bind(&2, Maybe<&2, Ledgers.Id>, Maybe<&2, Replicas.Request<Requests.Ask>>, Replicas.Tip.newest(Requests.Ask.machine(), d, b, ts), mv => Owners.Due.then(Ledgers.Id, mv, v => Maybe.map(&2, List<&2, String>, Maybe<&2, Replicas.Request<Requests.Ask>>, ns => Owners.Own.due.of(c, t, ts, g, ns, v), Owners.Group.nodes(d, b, Replicas.Tip.content(ts), g)))))), Some{x}, Shared.Maybe.bind_kept(Maybe<&2, String>, Maybe<&2, Replicas.Request<Requests.Ask>>, Replicas.Tip.known(String, Codes.Code.text, Codes.Code.text.read, Trees.Look.known(Trees.Ops.look(Ledgers.Kind.L(Requests.Ask, Replicas.Led.kind((Requests.Ask, (Requests.Ask.code, Requests.Ask.code.read, x => r => Requests.Ask.code_read(x, r)), Requests.Ask.arrival, Requests.Ask.governs, Requests.Key.seal), d)), Replicas.Led.tree((Requests.Ask, (Requests.Ask.code, Requests.Ask.code.read, x => r => Requests.Ask.code_read(x, r)), Requests.Ask.arrival, Requests.Ask.governs, Requests.Key.seal), d), a, Replicas.Tip.content(t), [6]))), Replicas.Tip.known(String, Codes.Code.text, Codes.Code.text.read, Trees.Look.known(Trees.Ops.look(Ledgers.Kind.L(Requests.Ask, Replicas.Led.kind((Requests.Ask, (Requests.Ask.code, Requests.Ask.code.read, x => r => Requests.Ask.code_read(x, r)), Requests.Ask.arrival, Requests.Ask.governs, Requests.Key.seal), d)), Replicas.Led.tree((Requests.Ask, (Requests.Ask.code, Requests.Ask.code.read, x => r => Requests.Ask.code_read(x, r)), Requests.Ask.arrival, Requests.Ask.governs, Requests.Key.seal), d), b, Replicas.Tip.content(t), [6]))), mg => Owners.Due.then(String, mg, +g => Maybe.bind(&2, Maybe<&2, Ledgers.Id>, Maybe<&2, Replicas.Request<Requests.Ask>>, Replicas.Tip.newest(Requests.Ask.machine(), d, a, ts), mv => Owners.Due.then(Ledgers.Id, mv, v => Maybe.map(&2, List<&2, String>, Maybe<&2, Replicas.Request<Requests.Ask>>, ns => Owners.Own.due.of(c, t, ts, g, ns, v), Owners.Group.nodes(d, a, Replicas.Tip.content(ts), g))))), mg => Owners.Due.then(String, mg, +g => Maybe.bind(&2, Maybe<&2, Ledgers.Id>, Maybe<&2, Replicas.Request<Requests.Ask>>, Replicas.Tip.newest(Requests.Ask.machine(), d, b, ts), mv => Owners.Due.then(Ledgers.Id, mv, v => Maybe.map(&2, List<&2, String>, Maybe<&2, Replicas.Request<Requests.Ask>>, ns => Owners.Own.due.of(c, t, ts, g, ns, v), Owners.Group.nodes(d, b, Replicas.Tip.content(ts), g))))), x, a1 => x2 => Rd.group(~d, a, b, g, t, a1)(x2), a1 => x2 => Rd.then(String, a1, +g => Maybe.bind(&2, Maybe<&2, Ledgers.Id>, Maybe<&2, Replicas.Request<Requests.Ask>>, Replicas.Tip.newest(Requests.Ask.machine(), d, a, ts), mv => Owners.Due.then(Ledgers.Id, mv, v => Maybe.map(&2, List<&2, String>, Maybe<&2, Replicas.Request<Requests.Ask>>, ns => Owners.Own.due.of(c, t, ts, g, ns, v), Owners.Group.nodes(d, a, Replicas.Tip.content(ts), g)))), +g => Maybe.bind(&2, Maybe<&2, Ledgers.Id>, Maybe<&2, Replicas.Request<Requests.Ask>>, Replicas.Tip.newest(Requests.Ask.machine(), d, b, ts), mv => Owners.Due.then(Ledgers.Id, mv, v => Maybe.map(&2, List<&2, String>, Maybe<&2, Replicas.Request<Requests.Ask>>, ns => Owners.Own.due.of(c, t, ts, g, ns, v), Owners.Group.nodes(d, b, Replicas.Tip.content(ts), g)))), x, v => x3 => Rd.at.group(~d, a, b, g, c, t, ts, v, x)(x3))(x2))(x1)) : {_ == Some{x} : Maybe<&2, Maybe<&2, Replicas.Request<Requests.Ask>>>}; {==})

# what Vend asks by itself for a line reads only the tips that Own.deps names
law Own.reads:
  for ~d: Vend.Led()
  for ~kern: Vend.Kern(d)
  for ~rules: Kernel.Rules(d, kern)
  Replicas.Kernel.Reads(Requests.Ask.machine(), d, kern, hs => l => c => Owners.Own.deps(hs, c))

def Own.reads(d, kern, rules):
  ?TODO

# Own.watch names each line that reads a line that moved
law Own.covers:
  for ~d: Vend.Led()
  Replicas.Kernel.Covers(
    Requests.Ask.machine(),
    d,
    hs => l => c => Owners.Own.deps(hs, c),
    hs => l => ms => Some{Owners.Own.watch(hs, ms)}
  )

def Own.covers(d):
  ?TODO

# the acts of the rules of Vend stay as the ledger grows: each rule reads the
# ledger and the tip of its line, and waits for what it lacks
law Ask.act_stable:
  for ~d: Vend.Led()
  Replicas.Kernel.Stable(Requests.Ask.machine(), d, l => t => c => i => q => Owners.Ask.act(~d, l, t, c, i, q))

# Laws
# ----

# Answer.merged follows itself: a clash that is open or shut after the merge k
# gives Conflicted or Written, and both may follow each other
def Answer.merged_follows.at(
  p: Bool,
  p2: Bool,
  +k: Ledgers.Id
) -> {
  Vend.Answer.follows(
    Shared.Bool.when(Vend.Answer, p, u => Vend.Answer.Conflicted{k}, u => Vend.Answer.Written{}),
    Some{Shared.Bool.when(Vend.Answer, p2, u => Vend.Answer.Conflicted{k}, u => Vend.Answer.Written{})}
  )
    == True{}: Bool
}:
  match p p2:
    case True{} True{}:
      Ledgers.Id.is_eq_refl(k)
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# Answer.merged follows itself once the reads of the clashes (m, m2) are
# known: a read that told, tells in the next
def Answer.merged_follows.of(
  m: Maybe<&2, Bool>,
  m2: Maybe<&2, Bool>,
  +k: Ledgers.Id,
  kn: {Maybe.is_some(&2, Bool, m) == True{}: Bool} -> {Maybe.is_some(&2, Bool, m2) == True{}: Bool}
) -> {Vend.Answer.follows(Vend.Answer.merged.of(m, k), Some{Vend.Answer.merged.of(m2, k)}) == True{}: Bool}:
  match m m2:
    case None{} y:
      {==}
    case Some{p} None{}:
      Empty.absurd(
        {Vend.Answer.follows(Vend.Answer.merged.of(Some{p}, k), Some{Vend.Answer.merged.of(None{}, k)}) == True{}: Bool},
        Shared.Bool.false_ne_true(kn({==}))
      )
    case Some{+p} Some{+p2}:
      Answer.merged_follows.at(p, p2, k)

# Answer.merged follows itself at another ledger and tree
def Answer.merged_follows(
  ~d: Vend.Led(),
  l: Vend.L(d),
  l2: Vend.L(d),
  h: Maybe<&2, Hashes.Hash>,
  h2: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  kn: Vend.Answer.Known(~d, l, h, l2, h2)
) -> {Vend.Answer.follows(Vend.Answer.merged(~d, l, h, k), Some{Vend.Answer.merged(~d, l2, h2, k)}) == True{}: Bool}:
  Answer.merged_follows.of(Vend.Clash.left(~d, l, h, k), Vend.Clash.left(~d, l2, h2, k), k, kn(k))

# Answer.taken follows itself at another ledger and tree: the merge that a
# change names is its own
def Answer.taken_follows(
  ~d: Vend.Led(),
  l: Vend.L(d),
  l2: Vend.L(d),
  h: Maybe<&2, Hashes.Hash>,
  h2: Maybe<&2, Hashes.Hash>,
  +i: Ledgers.Id,
  +q: Requests.Ask,
  kn: Vend.Answer.Known(~d, l, h, l2, h2)
) -> {Vend.Answer.follows(Vend.Answer.taken(~d, l, h, i, q), Some{Vend.Answer.taken(~d, l2, h2, i, q)}) == True{}: Bool}:
  match q:
    case Requests.Ask.Start{os}:
      {==}
    case Requests.Ask.On{st, b, Requests.Change.Branch{n, at}}:
      {==}
    case Requests.Ask.On{st, b, Requests.Change.Group{n, ms}}:
      {==}
    case Requests.Ask.On{st, b, Requests.Change.Own{g, at, os}}:
      {==}
    case Requests.Ask.On{st, b, Requests.Change.Write{n, base, x}}:
      {==}
    case Requests.Ask.On{st, b, Requests.Change.Resolve{k, n, x}}:
      Answer.merged_follows(~d, l, l2, h, h2, k, kn)
    case Requests.Ask.On{st, b, Requests.Change.Merge{v, base}}:
      Answer.merged_follows(~d, l, l2, h, h2, i, kn)
    case Requests.Ask.On{st, b, Requests.Change.Move{v}}:
      {==}
    case Requests.Ask.On{st, b, Requests.Change.Mark{m, text}}:
      {==}
    case Requests.Ask.On{st, b, Requests.Change.Key{n, k}}:
      {==}

# Answer.out follows itself once it is known whether the entry of the outcome
# is the request (p): Stale and Refused are final
def Answer.out_follows.stale(
  +p: Bool
) -> {
  Vend.Answer.follows(
    Shared.Bool.when(Vend.Answer, p, u => Vend.Answer.Stale{}, u => Vend.Answer.Refused{}),
    Some{Shared.Bool.when(Vend.Answer, p, u => Vend.Answer.Stale{}, u => Vend.Answer.Refused{})}
  )
    == True{}: Bool
}:
  match p:
    case True{}:
      {==}
    case False{}:
      {==}

# Answer.out follows itself for a taken outcome once it is known whether the
# entry of the outcome is the request (p)
def Answer.out_follows.taken(
  ~d: Vend.Led(),
  l: Vend.L(d),
  l2: Vend.L(d),
  h: Maybe<&2, Hashes.Hash>,
  h2: Maybe<&2, Hashes.Hash>,
  +i: Ledgers.Id,
  +q: Requests.Ask,
  +p: Bool,
  kn: Vend.Answer.Known(~d, l, h, l2, h2)
) -> {
  Vend.Answer.follows(
    Shared.Bool.when(Vend.Answer, p, u => Vend.Answer.taken(~d, l, h, i, q), u => Vend.Answer.Refused{}),
    Some{Shared.Bool.when(Vend.Answer, p, u => Vend.Answer.taken(~d, l2, h2, i, q), u => Vend.Answer.Refused{})}
  )
    == True{}: Bool
}:
  match p:
    case True{}:
      Answer.taken_follows(~d, l, l2, h, h2, i, q, kn)
    case False{}:
      {==}

# Answer.out follows itself for one outcome, at another ledger and tip: a
# request that has an outcome keeps its answer, but for the clash of a merge
def Answer.out_follows(
  ~d: Vend.Led(),
  l: Vend.L(d),
  l2: Vend.L(d),
  t: Replicas.Tip,
  t2: Replicas.Tip,
  +i: Ledgers.Id,
  +q: Requests.Ask,
  +a: Hashes.Hash,
  o: Maybe<&2, Replicas.Out>,
  kn: Vend.Answer.Known(~d, l, Replicas.Tip.content(t), l2, Replicas.Tip.content(t2))
) -> {
  Vend.Answer.follows(Vend.Answer.out(~d, l, t, i, q, a, o), Some{Vend.Answer.out(~d, l2, t2, i, q, a, o)}) == True{}: Bool
}:
  match o:
    case None{}:
      {==}
    case Some{Replicas.Out.Stale{x}}:
      Answer.out_follows.stale(Hashes.Hash.is_eq(x, a))
    case Some{Replicas.Out.Taken{x, n}}:
      Answer.out_follows.taken(
        ~d,
        l,
        l2,
        Replicas.Tip.content(t),
        Replicas.Tip.content(t2),
        i,
        q,
        Hashes.Hash.is_eq(x, a),
        kn
      )

# Answer.at follows itself once the outcome is read from two words (g1 at the
# first tip, g2 at the second) and g2 holds what g1 does
def Answer.at_follows.words(
  ~d: Vend.Led(),
  l: Vend.L(d),
  l2: Vend.L(d),
  t: Replicas.Tip,
  t2: Replicas.Tip,
  +i: Ledgers.Id,
  +q: Requests.Ask,
  +a: Hashes.Hash,
  g1: Maybe<&2, List<&2, U32>>,
  g2: Maybe<&2, List<&2, U32>>,
  keep: @ws: List<&2, U32> -> {g1 == Some{ws}: Maybe<&2, List<&2, U32>>} -> {g2 == Some{ws}: Maybe<&2, List<&2, U32>>},
  kn: Vend.Answer.Known(~d, l, Replicas.Tip.content(t), l2, Replicas.Tip.content(t2))
) -> {
  Vend.Answer.follows(
    Vend.Answer.out(~d, l, t, i, q, a, Codes.Code.whole.of(~Replicas.Out, ~Replicas.Out.code, ~Replicas.Out.code.read, g1)),
    Some{
      Vend.Answer.out(~d, l2, t2, i, q, a, Codes.Code.whole.of(~Replicas.Out, ~Replicas.Out.code, ~Replicas.Out.code.read, g2))
    }
  )
    == True{}: Bool
}:
  match g1:
    case None{}:
      {==}
    case Some{+ws}:
      %Equal.sym(Maybe<&2, List<&2, U32>>, g2, Some{ws}, keep(ws)({==})): {
        Vend.Answer.follows(
          Vend.Answer.out(~d, l, t, i, q, a, Codes.Code.whole.of(~Replicas.Out, ~Replicas.Out.code, ~Replicas.Out.code.read, Some{ws})),
          Some{
            Vend.Answer.out(~d, l2, t2, i, q, a, Codes.Code.whole.of(~Replicas.Out, ~Replicas.Out.code, ~Replicas.Out.code.read, _))
          }
        )
          == True{}: Bool
      }
      Answer.out_follows(~d, l, l2, t, t2, i, q, a, Codes.Code.whole.of(~Replicas.Out, ~Replicas.Out.code, ~Replicas.Out.code.read, Some{ws}), kn)

# Answer.at follows Pending: no outcome words are read at the first tip
def Answer.at_follows.pending(
  ~d: Vend.Led(),
  l: Vend.L(d),
  t: Replicas.Tip,
  +i: Ledgers.Id,
  +q: Requests.Ask,
  +a: Hashes.Hash,
  g1: Maybe<&2, List<&2, U32>>,
  none: @ws: List<&2, U32> -> {g1 == Some{ws}: Maybe<&2, List<&2, U32>>} -> Empty
) -> {
  Vend.Answer.follows(
    Vend.Answer.out(~d, l, t, i, q, a, Codes.Code.whole.of(~Replicas.Out, ~Replicas.Out.code, ~Replicas.Out.code.read, g1)),
    Some{Vend.Answer.Pending{}}
  )
    == True{}: Bool
}:
  match g1:
    case None{}:
      {==}
    case Some{ws}:
      Empty.absurd(
        {
          Vend.Answer.follows(
            Vend.Answer.out(~d, l, t, i, q, a, Codes.Code.whole.of(~Replicas.Out, ~Replicas.Out.code, ~Replicas.Out.code.read, Some{ws})),
            Some{Vend.Answer.Pending{}}
          )
            == True{}: Bool
        },
        none(ws)({==})
      )

# Answer.at follows itself from a tip t of the first ledger, once the words
# that t holds for the outcome of i are held by the tip m2 of the second
def Answer.at_follows.tip(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +t: Replicas.Tip,
  +m2: Maybe<&2, Replicas.Tip>,
  +i: Ledgers.Id,
  +q: Requests.Ask,
  +h: Hashes.Hash,
  keep: @ws: List<&2, U32> -> {
    Replicas.Tip.get(~Requests.Ask.machine(), ~d, a, t, Replicas.Log.out(i)) == Some{ws}: Maybe<&2, List<&2, U32>>
  } -> {
    Maybe.bind(
      &2,
      Replicas.Tip,
      List<&2, U32>,
      m2,
      t2 => Replicas.Tip.get(~Requests.Ask.machine(), ~d, b, t2, Replicas.Log.out(i))
    )
      == Some{ws}: Maybe<&2, List<&2, U32>>
  },
  kn: @t2: Replicas.Tip -> {m2 == Some{t2}: Maybe<&2, Replicas.Tip>} -> Vend.Answer.Known(
    ~d,
    a,
    Replicas.Tip.content(t),
    b,
    Replicas.Tip.content(t2)
  )
) -> {Vend.Answer.follows(Vend.Answer.at(~d, a, i, q, h, Some{t}), Some{Vend.Answer.at(~d, b, i, q, h, m2)}) == True{}: Bool}:
  match m2:
    case None{}:
      Answer.at_follows.pending(
        ~d,
        a,
        t,
        i,
        q,
        h,
        Replicas.Tip.get(~Requests.Ask.machine(), ~d, a, t, Replicas.Log.out(i)),
        ws => e => Shared.Maybe.none_ne_some(List<&2, U32>, ws, keep(ws)(e))
      )
    case Some{+t2}:
      Answer.at_follows.words(
        ~d,
        a,
        b,
        t,
        t2,
        i,
        q,
        h,
        Replicas.Tip.get(~Requests.Ask.machine(), ~d, a, t, Replicas.Log.out(i)),
        Replicas.Tip.get(~Requests.Ask.machine(), ~d, b, t2, Replicas.Log.out(i)),
        keep,
        kn(t2)({==})
      )

# the log of the head of the line c holds, at a later ledger, what it holds
# under the key of the outcome of i (Answer.Stays)
def Answer.at_follows.keep(
  ~d: Vend.Led(),
  ~kern: Vend.Kern(d),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +c: Ledgers.Line,
  +i: Ledgers.Id,
  +t: Replicas.Tip,
  +m2: Maybe<&2, Replicas.Tip>,
  g: Replicas.Led.Later(~Requests.Ask.machine(), ~d, a, b),
  stays: Vend.Answer.Stays(~d, ~kern),
  e1: {Replicas.Line.head(~Requests.Ask.machine(), ~d, ~kern, a, c) == Some{t}: Maybe<&2, Replicas.Tip>},
  e2: {Replicas.Line.head(~Requests.Ask.machine(), ~d, ~kern, b, c) == m2: Maybe<&2, Replicas.Tip>},
  +ws: List<&2, U32>,
  hw: {Replicas.Tip.get(~Requests.Ask.machine(), ~d, a, t, Replicas.Log.out(i)) == Some{ws}: Maybe<&2, List<&2, U32>>}
) -> {
  Maybe.bind(
    &2,
    Replicas.Tip,
    List<&2, U32>,
    m2,
    t2 => Replicas.Tip.get(~Requests.Ask.machine(), ~d, b, t2, Replicas.Log.out(i))
  )
    == Some{ws}: Maybe<&2, List<&2, U32>>
}:
  %e2: {
    Maybe.bind(
      &2,
      Replicas.Tip,
      List<&2, U32>,
      _,
      t2 => Replicas.Tip.get(~Requests.Ask.machine(), ~d, b, t2, Replicas.Log.out(i))
    )
      == Some{ws}: Maybe<&2, List<&2, U32>>
  }
  stays(c)(Replicas.Log.out(i))(a)(b)(ws)(g)(
    %Equal.sym(
      Maybe<&2, Replicas.Tip>,
      Replicas.Line.head(~Requests.Ask.machine(), ~d, ~kern, a, c),
      Some{t},
      e1
    ): {
      Maybe.bind(
        &2,
        Replicas.Tip,
        List<&2, U32>,
        _,
        t2 => Replicas.Tip.get(~Requests.Ask.machine(), ~d, a, t2, Replicas.Log.out(i))
      )
        == Some{ws}: Maybe<&2, List<&2, U32>>
    }
    hw
  )

# Answer.at follows itself at the heads m1 and m2 of the line c, in two
# ledgers where the second is a later state of the first
def Answer.at_follows.head(
  ~d: Vend.Led(),
  ~kern: Vend.Kern(d),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +c: Ledgers.Line,
  +i: Ledgers.Id,
  +q: Requests.Ask,
  +h: Hashes.Hash,
  g: Replicas.Led.Later(~Requests.Ask.machine(), ~d, a, b),
  stays: Vend.Answer.Stays(~d, ~kern),
  m1: Maybe<&2, Replicas.Tip>,
  +m2: Maybe<&2, Replicas.Tip>,
  +e1: {Replicas.Line.head(~Requests.Ask.machine(), ~d, ~kern, a, c) == m1: Maybe<&2, Replicas.Tip>},
  +e2: {Replicas.Line.head(~Requests.Ask.machine(), ~d, ~kern, b, c) == m2: Maybe<&2, Replicas.Tip>},
  kn: @t: Replicas.Tip -> @t2: Replicas.Tip -> {m1 == Some{t}: Maybe<&2, Replicas.Tip>} -> {
    m2 == Some{t2}: Maybe<&2, Replicas.Tip>
  } -> Vend.Answer.Known(~d, a, Replicas.Tip.content(t), b, Replicas.Tip.content(t2))
) -> {Vend.Answer.follows(Vend.Answer.at(~d, a, i, q, h, m1), Some{Vend.Answer.at(~d, b, i, q, h, m2)}) == True{}: Bool}:
  match m1:
    case None{}:
      {==}
    case Some{+t}:
      Answer.at_follows.tip(
        ~d,
        a,
        b,
        t,
        m2,
        i,
        q,
        h,
        ws => hw => Answer.at_follows.keep(~d, ~kern, a, b, c, i, t, m2, g, stays, e1, e2, ws, hw),
        t2 => e2x => kn(t)(t2)({==})(e2x)
      )

# Answer.of follows itself in a later state of the ledger
def Answer.of_follows(
  ~d: Vend.Led(),
  ~kern: Vend.Kern(d),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +i: Ledgers.Id,
  +q: Requests.Ask,
  +h: Hashes.Hash,
  g: Replicas.Led.Later(~Requests.Ask.machine(), ~d, a, b),
  stays: Vend.Answer.Stays(~d, ~kern),
  w: Replicas.Arrival,
  kn: @c: Ledgers.Line -> @t: Replicas.Tip -> @t2: Replicas.Tip -> {
    Replicas.Line.head(~Requests.Ask.machine(), ~d, ~kern, a, c) == Some{t}: Maybe<&2, Replicas.Tip>
  } -> {
    Replicas.Line.head(~Requests.Ask.machine(), ~d, ~kern, b, c) == Some{t2}: Maybe<&2, Replicas.Tip>
  } -> Vend.Answer.Known(~d, a, Replicas.Tip.content(t), b, Replicas.Tip.content(t2))
) -> {Vend.Answer.follows(Vend.Answer.of(~d, ~kern, a, i, q, h, w), Some{Vend.Answer.of(~d, ~kern, b, i, q, h, w)}) == True{}: Bool}:
  match w:
    case Replicas.Arrival.Starts{vs}:
      {==}
    case Replicas.Arrival.Waits{+c}:
      Answer.at_follows.head(
        ~d,
        ~kern,
        a,
        b,
        c,
        i,
        q,
        h,
        g,
        stays,
        Replicas.Line.head(~Requests.Ask.machine(), ~d, ~kern, a, c),
        Replicas.Line.head(~Requests.Ask.machine(), ~d, ~kern, b, c),
        {==},
        {==},
        t => t2 => e1 => e2 => kn(c)(t)(t2)(e1)(e2)
      )

# Node.answer follows itself once it is known whether each ledger holds the
# request (pa, pb), and the answers that they give (A1, A2) follow
def Node.answer_follows.when(
  +pa: Bool,
  +pb: Bool,
  +A1: Vend.Answer,
  +A2: Vend.Answer,
  +x: Vend.Answer,
  keep: {pa == True{}: Bool} -> {pb == True{}: Bool},
  step: {Vend.Answer.follows(A1, Some{A2}) == True{}: Bool},
  e: {Shared.Maybe.when(Vend.Answer, pa, u => Some{A1}) == Some{x}: Maybe<&2, Vend.Answer>}
) -> {Vend.Answer.follows(x, Shared.Maybe.when(Vend.Answer, pb, u => Some{A2})) == True{}: Bool}:
  match pa pb:
    case True{} True{}:
      %Shared.Maybe.some_inj(Vend.Answer, A1, x, e): {Vend.Answer.follows(_, Some{A2}) == True{}: Bool}
      step
    case True{} False{}:
      Empty.absurd({Vend.Answer.follows(x, None{}) == True{}: Bool}, Shared.Bool.false_ne_true(keep({==})))
    case False{} y:
      Empty.absurd(
        {Vend.Answer.follows(x, Shared.Maybe.when(Vend.Answer, y, u => Some{A2})) == True{}: Bool},
        Shared.Maybe.none_ne_some(Vend.Answer, x, e)
      )

# Node.answer_follows for the ledgers a and b, once Line.get_grows is known
def Node.answer_follows.go(
  ~d: Vend.Led(),
  ~kern: Vend.Kern(d),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +i: Ledgers.Id,
  +time: String,
  +q: Requests.Ask,
  +x: Vend.Answer,
  +g: Replicas.Led.Later(~Requests.Ask.machine(), ~d, a, b),
  stays: Vend.Answer.Stays(~d, ~kern),
  e: {Vend.Node.answer(~d, ~kern, a, i, time, q) == Some{x}: Maybe<&2, Vend.Answer>},
  kn: @c: Ledgers.Line -> @t: Replicas.Tip -> @t2: Replicas.Tip -> {
    Replicas.Line.head(~Requests.Ask.machine(), ~d, ~kern, a, c) == Some{t}: Maybe<&2, Replicas.Tip>
  } -> {
    Replicas.Line.head(~Requests.Ask.machine(), ~d, ~kern, b, c) == Some{t2}: Maybe<&2, Replicas.Tip>
  } -> Vend.Answer.Known(~d, a, Replicas.Tip.content(t), b, Replicas.Tip.content(t2))
) -> {Vend.Answer.follows(x, Vend.Node.answer(~d, ~kern, b, i, time, q)) == True{}: Bool}:
  Node.answer_follows.when(
    Replicas.Led.has(~Requests.Ask.machine(), ~d, a, Ledgers.Entry.Ask{i, time, q}),
    Replicas.Led.has(~Requests.Ask.machine(), ~d, b, Ledgers.Entry.Ask{i, time, q}),
    Vend.Answer.of(~d, ~kern, a, i, q, Ledgers.Name.hash(Replicas.Entry.name(~Requests.Ask.machine(), Ledgers.Entry.Ask{i, time, q})), Requests.Ask.arrival(q)),
    Vend.Answer.of(~d, ~kern, b, i, q, Ledgers.Name.hash(Replicas.Entry.name(~Requests.Ask.machine(), Ledgers.Entry.Ask{i, time, q})), Requests.Ask.arrival(q)),
    x,
    Replicas.Hist.has_grows(~Requests.Ask.machine(), ~d, a, b, Ledgers.Entry.Ask{i, time, q}, Replicas.Led.later_grows(~Requests.Ask.machine(), ~d, a, b)(g)),
    Answer.of_follows(
      ~d,
      ~kern,
      a,
      b,
      i,
      q,
      Ledgers.Name.hash(Replicas.Entry.name(~Requests.Ask.machine(), Ledgers.Entry.Ask{i, time, q})),
      g,
      stays,
      Requests.Ask.arrival(q),
      kn
    ),
    e
  )

# Node.answer_follows, once Line.get_grows (stays) and Node.head_kept (hk) are
# known
def Node.answer_follows.of(
  ~d: Vend.Led(),
  ~kern: Vend.Kern(d),
  +i: Ledgers.Id,
  +time: String,
  +q: Requests.Ask,
  stays: Vend.Answer.Stays(~d, ~kern),
  hk: Merges.Node.HeadKept(~d, ~kern)
) -> Shared.Read.Forward(
  Vend.L(d),
  a => b => Replicas.Led.Later(~Requests.Ask.machine(), ~d, a, b),
  Vend.Answer,
  x => m => {Vend.Answer.follows(x, m) == True{}: Bool},
  l => Vend.Node.answer(~d, ~kern, l, i, time, q)
):
  +a => +b => +x => g => e => Node.answer_follows.go(
    ~d,
    ~kern,
    a,
    b,
    i,
    time,
    q,
    x,
    g,
    stays,
    e,
    c => +t => +t2 => e1 => e2 => Merges.Answer.kn_of_kept(~d, a, Replicas.Tip.content(t), b, Replicas.Tip.content(t2), hk(b)(c)(t2)(e2))
  )

# the owners of a line keep each part of what they decide: the ledger holds
# the whole of the content of the newest tip of each line, its nodes and the
# format and the bytes of each of its resources
law Node.head_kept:
  for ~d: Vend.Led()
  for ~kern: Vend.Kern(d)
  for ~rules: Kernel.Rules(d, kern)
  for l: Vend.L(d)
  for c: Ledgers.Line
  for t: Replicas.Tip
  {Replicas.Line.head(~Requests.Ask.machine(), ~d, ~kern, l, c) == Some{t}: Maybe<&2, Replicas.Tip>}
    -> {Vend.Tree.kept(~d, l, Replicas.Tip.content(t)) == True{}: Bool}

# answers only move forward: as the ledger grows, and while its ballots are
# honest, a request that a node answers stays answered; Stale and Refused are
# final; a taken change stays taken (Answer.follows)
law Node.answer_follows:
  for ~d: Vend.Led()
  for ~kern: Vend.Kern(d)
  for rules: Kernel.Rules(d, kern)
  for i: Ledgers.Id
  for time: String
  for q: Requests.Ask
  Shared.Read.Forward(
    Vend.L(d),
    a => b => Replicas.Led.Later(~Requests.Ask.machine(), ~d, a, b),
    Vend.Answer,
    x => m => {Vend.Answer.follows(x, m) == True{}: Bool},
    l => Vend.Node.answer(~d, ~kern, l, i, time, q)
  )


# Tips that are good
# ------------------
# A tip is good in a ledger when the ledger holds the whole of its content, the
# whole of its log, and a log whose first tips of sub lines are tips of kept
# trees without a log.

# the log whose root is h names, for each sub line, a first tip that the ledger
# holds with a kept tree and no log
def Kp.StartsAt(-d: Vend.Led(), l: Vend.L(d), h: Maybe<&2, Hashes.Hash>) -> Type:
  @b: String -> @ws: List<&2, U32> -> @tb: Replicas.Tip -> {
    Replicas.Tree.get(~Requests.Ask.machine(), ~d, l, h, Replicas.Log.start(b)) == Some{ws}: Maybe<&2, List<&2, U32>>
  } -> {Replicas.Tip.named(~Requests.Ask.machine(), ~d, l, ws) == Some{tb}: Maybe<&2, Replicas.Tip>} -> Merges.Merge.And(
    {Vend.Tree.kept(~d, l, Replicas.Tip.content(tb)) == True{}: Bool},
    {Replicas.Tip.log(tb) == None{}: Maybe<&2, Hashes.Hash>}
  )

# a log that a write gives for the key k the value v: when k is the key of the
# first tip of a sub line, v names a tip that the ledger holds with a kept tree
# and no log
def Kp.Wrote(-d: Vend.Led(), l: Vend.L(d), k: List<&2, U32>, v: List<&2, U32>) -> Type:
  @b: String -> {Shared.List.is_eq(~U32, ~U32.is_eq, k, Replicas.Log.start(b)) == True{}: Bool} -> @tb: Replicas.Tip -> {
    Replicas.Tip.named(~Requests.Ask.machine(), ~d, l, v) == Some{tb}: Maybe<&2, Replicas.Tip>
  } -> Merges.Merge.And({Vend.Tree.kept(~d, l, Replicas.Tip.content(tb)) == True{}: Bool}, {Replicas.Tip.log(tb) == None{}: Maybe<&2, Hashes.Hash>})

# a tip that its ledger holds whole, with a log whose first tips of sub lines
# are good
def Kp.Good(-d: Vend.Led(), l: Vend.L(d), t: Replicas.Tip) -> Type:
  {Vend.Tree.kept(~d, l, Replicas.Tip.content(t)) == True{}: Bool}
    & (
      {Maybe.is_some(&2, List<&2, Trees.Binding>, Vend.Tree.range(~d, l, Replicas.Tip.log(t), [])) == True{}: Bool}
        & Kp.StartsAt(d, l, Replicas.Tip.log(t))
    )

# that the tip of the run r is good in l, once l holds what r added
def Kp.Has(-d: Vend.Led(), l: Vend.L(d), r: Replicas.Run<Vend.L(d)>) -> Type:
  {Replicas.Ext.holds(~Requests.Ask.machine(), ~d, l, Replicas.Run.added(Vend.L(d), r)) == True{}: Bool} -> Kp.Good(d, l, Replicas.Run.tip(Vend.L(d), r))

# Kp.Has of the run that a run gives, when it gives one
def Kp.Out(-d: Vend.Led(), l: Vend.L(d), m: Maybe<&2, Replicas.Run<Vend.L(d)>>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{r}:
      Kp.Has(d, l, r)

# that l reads the run in m as a run on l with some data put, and its tip is
# good once l holds what it added
def Kp.All(-d: Vend.Led(), l: Vend.L(d), m: Maybe<&2, Replicas.Run<Vend.L(d)>>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{r}:
      Replicas.Ext.Based(Requests.Ask.machine(), d, l, r) & Kp.Has(d, l, r)

# a log that a write gives for the key k the value v, once the ledger holds the
# nodes a of the run before the write and the content c of its tip is kept
def Kp.WroteIf(
  -d: Vend.Led(),
  l: Vend.L(d),
  k: List<&2, U32>,
  v: List<&2, U32>,
  a: List<&2, List<&2, U32>>,
  c: Maybe<&2, Hashes.Hash>
) -> Type:
  {Replicas.Ext.holds(~Requests.Ask.machine(), ~d, l, a) == True{}: Bool}
    -> {Vend.Tree.kept(~d, l, c) == True{}: Bool} -> Kp.Wrote(d, l, k, v)

# what a kernel gives for the run r, in a ledger that holds what it added: if
# the act that it gives is held, and the content of the tip of r is kept, the
# content that the act gives is kept
def Kp.ActOk(-d: Vend.Led(), l: Vend.L(d), r: Replicas.Run<Vend.L(d)>, m: Maybe<&2, Replicas.Act>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{act}:
      {Replicas.Act.held(~Requests.Ask.machine(), ~d, l, act) == True{}: Bool}
        -> {Replicas.Ext.holds(~Requests.Ask.machine(), ~d, l, Replicas.Run.added(Vend.L(d), r)) == True{}: Bool}
        -> {Vend.Tree.kept(~d, l, Replicas.Tip.content(Replicas.Run.tip(Vend.L(d), r))) == True{}: Bool}
        -> Store.Acts.Kept(~d, l, act)

# a write to a log whose tree is listed gives a listed tree, once the tree is
# known to be listed (sb)
def Kp.put_whole.at(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  +m: Maybe<&2, List<&2, U32>>,
  +e: Trees.Edit,
  +ep: {Replicas.Tree.put(~Requests.Ask.machine(), ~d, l, h, k, m) == Some{e}: Maybe<&2, Trees.Edit>},
  +hh: Merges.Merge.Held(~d, l, Trees.Edit.nodes(e)),
  sb: Store.Kept.Some(List<&2, Trees.Binding>, Vend.Tree.range(~d, l, h, []))
) -> {Maybe.is_some(&2, List<&2, Trees.Binding>, Vend.Tree.range(~d, l, Trees.Edit.root(e), [])) == True{}: Bool}:
  (+bs, e1) = sb
  Store.Kept.laws_kept(d)(l)(l)(h)(bs)(k)(m)(e)(e1)(ep)(Replicas.Hist.refl(~Requests.Ask.machine(), ~d, l))(
    Replicas.Ext.held(~Requests.Ask.machine(), ~d, l, e, hh)
  )

# a write to a log whose tree is listed gives a listed tree
def Kp.put_whole(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  +m: Maybe<&2, List<&2, U32>>,
  +e: Trees.Edit,
  hl: {Maybe.is_some(&2, List<&2, Trees.Binding>, Vend.Tree.range(~d, l, h, [])) == True{}: Bool},
  +ep: {Replicas.Tree.put(~Requests.Ask.machine(), ~d, l, h, k, m) == Some{e}: Maybe<&2, Trees.Edit>},
  +hh: Merges.Merge.Held(~d, l, Trees.Edit.nodes(e))
) -> {Maybe.is_some(&2, List<&2, Trees.Binding>, Vend.Tree.range(~d, l, Trees.Edit.root(e), [])) == True{}: Bool}:
  Kp.put_whole.at(~d, l, h, k, m, e, ep, hh, Store.Kept.some_of(List<&2, Trees.Binding>, Vend.Tree.range(~d, l, h, []), hl))


# the first tips that a log names, after a write to it of a key that is not the
# key of a first tip, are those that it named, once the read of the key in the log
# before the write is known (sx)
def Kp.starts_put.miss(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +h1: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  +b: String,
  +ws: List<&2, U32>,
  +tb: Replicas.Tip,
  +ep: {Shared.List.is_eq(~U32, ~U32.is_eq, k, Replicas.Log.start(b)) == False{}: Bool},
  wr: Merges.Merge.Writes(~d, l, h1, h, k, Some{v}),
  st: Kp.StartsAt(d, l, h),
  +hg: {Replicas.Tree.get(~Requests.Ask.machine(), ~d, l, h1, Replicas.Log.start(b)) == Some{ws}: Maybe<&2, List<&2, U32>>},
  hn: {Replicas.Tip.named(~Requests.Ask.machine(), ~d, l, ws) == Some{tb}: Maybe<&2, Replicas.Tip>},
  sx: Store.Kept.Some(Maybe<&2, List<&2, U32>>, Replicas.Tree.find(~Requests.Ask.machine(), ~d, l, h, Replicas.Log.start(b)))
) -> Merges.Merge.And({Vend.Tree.kept(~d, l, Replicas.Tip.content(tb)) == True{}: Bool}, {Replicas.Tip.log(tb) == None{}: Maybe<&2, Hashes.Hash>}):
  (+x, +ex) = sx
  st(b)(ws)(tb)(
    Merges.Merge.value_known(
      Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, h, Replicas.Log.start(b)),
      Some{ws},
      %Equal.sym(
        Maybe<&2, List<&2, U32>>,
        Some{ws},
        x,
        Shared.Maybe.some_inj(
          Maybe<&2, List<&2, U32>>,
          Some{ws},
          x,
          %Store.Kept.look_found(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, h1, Replicas.Log.start(b)), ws, hg): {
            Trees.Look.known(_) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
          }
          Merges.Merge.writes_frame(~d, l, h1, h, k, Some{v}, wr, Replicas.Log.start(b), x, ep, ex)
        )
      ): {Trees.Look.known(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, h, Replicas.Log.start(b))) == Some{_}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
      ex
    )
  )(hn)

# the first tips that a log names, after a write to it, the written key being the
# key of a first tip, or not (p)
def Kp.starts_put.at(
  ~d: Vend.Led(),
  p: Bool,
  +l: Vend.L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +h1: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  +bs: List<&2, Trees.Binding>,
  +b: String,
  +ws: List<&2, U32>,
  +tb: Replicas.Tip,
  +ep: {Shared.List.is_eq(~U32, ~U32.is_eq, k, Replicas.Log.start(b)) == p: Bool},
  +e1: {Vend.Tree.range(~d, l, h, []) == Some{bs}: Maybe<&2, List<&2, Trees.Binding>>},
  wr: Merges.Merge.Writes(~d, l, h1, h, k, Some{v}),
  st: Kp.StartsAt(d, l, h),
  wk: Kp.Wrote(d, l, k, v),
  +hg: {Replicas.Tree.get(~Requests.Ask.machine(), ~d, l, h1, Replicas.Log.start(b)) == Some{ws}: Maybe<&2, List<&2, U32>>},
  +hn: {Replicas.Tip.named(~Requests.Ask.machine(), ~d, l, ws) == Some{tb}: Maybe<&2, Replicas.Tip>}
) -> Merges.Merge.And({Vend.Tree.kept(~d, l, Replicas.Tip.content(tb)) == True{}: Bool}, {Replicas.Tip.log(tb) == None{}: Maybe<&2, Hashes.Hash>}):
  match p:
    case True{}:
      wk(b)(ep)(tb)(
        %Equal.sym(
          List<&2, U32>,
          v,
          ws,
          Shared.Maybe.some_inj(
            List<&2, U32>,
            v,
            ws,
            %Merges.Merge.writes_hit(~d, l, h1, h, k, Some{v}, wr): {Trees.Look.value(_) == Some{ws}: Maybe<&2, List<&2, U32>>}
            %Equal.sym(
              List<&2, U32>,
              k,
              Replicas.Log.start(b),
              Shared.List.is_eq_sound(~U32, ~U32.is_eq, ~Shared.U32.laws(), k, Replicas.Log.start(b))(ep)
            ): {Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, h1, _)) == Some{ws}: Maybe<&2, List<&2, U32>>}
            hg
          )
        ): {Replicas.Tip.named(~Requests.Ask.machine(), ~d, l, _) == Some{tb}: Maybe<&2, Replicas.Tip>}
        hn
      )
    case False{}:
      Kp.starts_put.miss(
        ~d,
        l,
        h,
        h1,
        k,
        v,
        b,
        ws,
        tb,
        ep,
        wr,
        st,
        hg,
        hn,
        Store.Kept.some_of(
          Maybe<&2, List<&2, U32>>,
          Replicas.Tree.find(~Requests.Ask.machine(), ~d, l, h, Replicas.Log.start(b)),
          Merges.Merge.final_look(
            Vend.L(d),
            Replicas.Led.tree(Requests.Ask.machine(), d),
            Merges.Merge.laws_whole(d),
            l,
            h,
            bs,
            e1,
            Replicas.Log.start(b)
          )
        )
      )

# the first tips that a log names, after a write to it, are good, when the one
# written is
def Kp.starts_put(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +h1: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  +bs: List<&2, Trees.Binding>,
  +e1: {Vend.Tree.range(~d, l, h, []) == Some{bs}: Maybe<&2, List<&2, Trees.Binding>>},
  wr: Merges.Merge.Writes(~d, l, h1, h, k, Some{v}),
  st: Kp.StartsAt(d, l, h),
  wk: Kp.Wrote(d, l, k, v)
) -> Kp.StartsAt(d, l, h1):
  +b => +ws => +tb => hg => hn => Kp.starts_put.at(
    ~d,
    Shared.List.is_eq(~U32, ~U32.is_eq, k, Replicas.Log.start(b)),
    l,
    h,
    h1,
    k,
    v,
    bs,
    b,
    ws,
    tb,
    {==},
    e1,
    wr,
    st,
    wk,
    hg,
    hn
  )

# the tip of a run after a write to its log is good, once the tip before it is
# good (gd), the listing of its log is known (sb) and the ledger holds the nodes
# of the write
def Kp.logged.good3(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +lr: Vend.L(d),
  +c: Maybe<&2, Hashes.Hash>,
  +lg: Maybe<&2, Hashes.Hash>,
  +n: U32,
  +vs: List<&2, String>,
  +x: Trees.Edit,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  +ep: {Replicas.Tree.put(~Requests.Ask.machine(), ~d, lr, lg, k, Some{v}) == Some{x}: Maybe<&2, Trees.Edit>},
  +gr: Replicas.Led.Grows(Requests.Ask.machine(), d, lr, l),
  +hx: Merges.Merge.Held(~d, l, Trees.Edit.nodes(x)),
  wk: Kp.Wrote(d, l, k, v),
  g1: {Vend.Tree.kept(~d, l, c) == True{}: Bool},
  +w1: {Maybe.is_some(&2, List<&2, Trees.Binding>, Vend.Tree.range(~d, l, lg, [])) == True{}: Bool},
  st1: Kp.StartsAt(d, l, lg),
  sb: Store.Kept.Some(List<&2, Trees.Binding>, Vend.Tree.range(~d, l, lg, []))
) -> Kp.Good(d, l, Replicas.Tip{c, Trees.Edit.root(x), n, vs}):
  (+bs, +e1) = sb
  (
    g1,
    (
      Kp.put_whole(
        ~d,
        l,
        lg,
        k,
        Some{v},
        x,
        w1,
        Replicas.Hist.put(~Requests.Ask.machine(), ~d, lr, l, lg, k, Some{v}, x, gr)(ep),
        hx
      ),
      Kp.starts_put(
        ~d,
        l,
        lg,
        Trees.Edit.root(x),
        k,
        v,
        bs,
        e1,
        Replicas.Hist.write(Requests.Ask.machine(), d)(l)(l)(lg)(k)(Some{v})(x)(
          Replicas.Hist.put(~Requests.Ask.machine(), ~d, lr, l, lg, k, Some{v}, x, gr)(ep)
        )(Replicas.Hist.refl(~Requests.Ask.machine(), ~d, l))(Replicas.Ext.held(~Requests.Ask.machine(), ~d, l, x, hx)),
        st1,
        wk
      )
    )
  )

# the tip of a run after a write to its log is good, once the tip before it is
# good (gd)
def Kp.logged.good2(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +lr: Vend.L(d),
  +c: Maybe<&2, Hashes.Hash>,
  +lg: Maybe<&2, Hashes.Hash>,
  +n: U32,
  +vs: List<&2, String>,
  +x: Trees.Edit,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  +ep: {Replicas.Tree.put(~Requests.Ask.machine(), ~d, lr, lg, k, Some{v}) == Some{x}: Maybe<&2, Trees.Edit>},
  +gr: Replicas.Led.Grows(Requests.Ask.machine(), d, lr, l),
  +hx: Merges.Merge.Held(~d, l, Trees.Edit.nodes(x)),
  wk: {Vend.Tree.kept(~d, l, c) == True{}: Bool} -> Kp.Wrote(d, l, k, v),
  gd: Kp.Good(d, l, Replicas.Tip{c, lg, n, vs})
) -> Kp.Good(d, l, Replicas.Tip{c, Trees.Edit.root(x), n, vs}):
  (+g1, r1) = gd
  (+w1, st1) = r1
  Kp.logged.good3(
    ~d,
    l,
    lr,
    c,
    lg,
    n,
    vs,
    x,
    k,
    v,
    ep,
    gr,
    hx,
    wk(g1),
    g1,
    w1,
    st1,
    Store.Kept.some_of(List<&2, Trees.Binding>, Vend.Tree.range(~d, l, lg, []), w1)
  )

# the tip of a run after a write to its log is good in the ledger that holds
# what the run added
def Kp.logged.good(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +lr: Vend.L(d),
  +c: Maybe<&2, Hashes.Hash>,
  +lg: Maybe<&2, Hashes.Hash>,
  +n: U32,
  +vs: List<&2, String>,
  +a: List<&2, List<&2, U32>>,
  +x: Trees.Edit,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  +ep: {Replicas.Tree.put(~Requests.Ask.machine(), ~d, lr, lg, k, Some{v}) == Some{x}: Maybe<&2, Trees.Edit>},
  bd: Replicas.Ext.Based(Requests.Ask.machine(), d, l, Replicas.Run{lr, Replicas.Tip{c, lg, n, vs}, a}),
  hr: Kp.Has(d, l, Replicas.Run{lr, Replicas.Tip{c, lg, n, vs}, a}),
  wk: Kp.WroteIf(d, l, k, v, a, c),
  +hh: {Replicas.Ext.holds(~Requests.Ask.machine(), ~d, l, List.append(&2, List<&2, U32>, Trees.Edit.nodes(x), a)) == True{}: Bool}
) -> Kp.Good(d, l, Replicas.Tip{c, Trees.Edit.root(x), n, vs}):
  Kp.logged.good2(
    ~d,
    l,
    lr,
    c,
    lg,
    n,
    vs,
    x,
    k,
    v,
    ep,
    Replicas.Ext.based_grows(
      ~Requests.Ask.machine(),
      ~d,
      l,
      Replicas.Run{lr, Replicas.Tip{c, lg, n, vs}, a},
      bd,
      Replicas.Ext.holds_right(~Requests.Ask.machine(), ~d, l, Trees.Edit.nodes(x), a)(hh)
    ),
    Replicas.Ext.holds_left(~Requests.Ask.machine(), ~d, l, Trees.Edit.nodes(x), a)(hh),
    wk(Replicas.Ext.holds_right(~Requests.Ask.machine(), ~d, l, Trees.Edit.nodes(x), a)(hh)),
    hr(Replicas.Ext.holds_right(~Requests.Ask.machine(), ~d, l, Trees.Edit.nodes(x), a)(hh))
  )

# a run that writes to its log, once the write of the tree is known (p), has a
# good tip
def Kp.logged(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +lr: Vend.L(d),
  t: Replicas.Tip,
  +a: List<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  p: Maybe<&2, Trees.Edit>,
  ep: {Replicas.Tree.put(~Requests.Ask.machine(), ~d, lr, Replicas.Tip.log(t), k, Some{v}) == p: Maybe<&2, Trees.Edit>},
  bd: Replicas.Ext.Based(Requests.Ask.machine(), d, l, Replicas.Run{lr, t, a}),
  hr: Kp.Has(d, l, Replicas.Run{lr, t, a}),
  wk: Kp.WroteIf(d, l, k, v, a, Replicas.Tip.content(t))
) -> Kp.Out(d, l, Replicas.Run.logged(~Requests.Ask.machine(), ~d, lr, t, a, p)):
  match t p:
    case Replicas.Tip{+c, +lg, +n, +vs} None{}:
      Unit{}
    case Replicas.Tip{+c, +lg, +n, +vs} Some{+x}:
      hh => Kp.logged.good(~d, l, lr, c, lg, n, vs, a, x, k, v, ep, bd, hr, wk, hh)

# a run that writes a new key to its log has a good tip, once the read of the key
# is known (m)
def Kp.add.at(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  r: Replicas.Run<Vend.L(d)>,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  m: Maybe<&2, Maybe<&2, List<&2, U32>>>,
  bd: Replicas.Ext.Based(Requests.Ask.machine(), d, l, r),
  hr: Kp.Has(d, l, r),
  wk: Kp.WroteIf(d, l, k, v, Replicas.Run.added(Vend.L(d), r), Replicas.Tip.content(Replicas.Run.tip(Vend.L(d), r)))
) -> Kp.Out(d, l, Replicas.Run.add.at(~Requests.Ask.machine(), ~d, r, k, v, m)):
  match r m:
    case Replicas.Run{+lr, +t, +a} Some{None{}}:
      Kp.logged(~d, l, lr, t, a, k, v, Replicas.Tree.put(~Requests.Ask.machine(), ~d, lr, Replicas.Tip.log(t), k, Some{v}), {==}, bd, hr, wk)
    case Replicas.Run{+lr, +t, +a} Some{Some{old}}:
      Unit{}
    case Replicas.Run{+lr, +t, +a} None{}:
      Unit{}

# a run that writes a new key to its log has a good tip
def Kp.add(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +r: Replicas.Run<Vend.L(d)>,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  bd: Replicas.Ext.Based(Requests.Ask.machine(), d, l, r),
  hr: Kp.Has(d, l, r),
  wk: Kp.WroteIf(d, l, k, v, Replicas.Run.added(Vend.L(d), r), Replicas.Tip.content(Replicas.Run.tip(Vend.L(d), r)))
) -> Kp.Out(d, l, Replicas.Run.add(~Requests.Ask.machine(), ~d, r, k, v)):
  Kp.add.at(
    ~d,
    l,
    r,
    k,
    v,
    Replicas.Tip.find(~Requests.Ask.machine(), ~d, Replicas.Run.ledger(Vend.L(d), r), Replicas.Run.tip(Vend.L(d), r), k),
    bd,
    hr,
    wk
  )

# the key of the outcome of a request is not the key of a first tip
def Kp.wrote_out(~d: Vend.Led(), +l: Vend.L(d), +i: Ledgers.Id, +v: List<&2, U32>) -> Kp.Wrote(d, l, Replicas.Log.out(i), v):
  +b => he => +tb => hn => Empty.absurd(
    Merges.Merge.And({Vend.Tree.kept(~d, l, Replicas.Tip.content(tb)) == True{}: Bool}, {Replicas.Tip.log(tb) == None{}: Maybe<&2, Hashes.Hash>}),
    Shared.Bool.false_ne_true(he)
  )

# the key of a taken request is not the key of a first tip
def Kp.wrote_taken(~d: Vend.Led(), +l: Vend.L(d), +n: U32, +v: List<&2, U32>) -> Kp.Wrote(d, l, Replicas.Log.taken(n), v):
  +b => he => +tb => hn => Empty.absurd(
    Merges.Merge.And({Vend.Tree.kept(~d, l, Replicas.Tip.content(tb)) == True{}: Bool}, {Replicas.Tip.log(tb) == None{}: Maybe<&2, Hashes.Hash>}),
    Shared.Bool.false_ne_true(he)
  )

# the key of a label is not the key of a first tip
def Kp.wrote_label(~d: Vend.Led(), +l: Vend.L(d), +m: String, +v: List<&2, U32>) -> Kp.Wrote(d, l, Replicas.Log.label(m), v):
  +b => he => +tb => hn => Empty.absurd(
    Merges.Merge.And({Vend.Tree.kept(~d, l, Replicas.Tip.content(tb)) == True{}: Bool}, {Replicas.Tip.log(tb) == None{}: Maybe<&2, Hashes.Hash>}),
    Shared.Bool.false_ne_true(he)
  )

# a run that follows a run whose tip is good, and whose tip is good once it is
# known to
def Kp.bind(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +r: Replicas.Run<Vend.L(d)>,
  m: Maybe<&2, Replicas.Run<Vend.L(d)>>,
  g: Replicas.Run<Vend.L(d)> -> Maybe<&2, Replicas.Run<Vend.L(d)>>,
  hm: Kp.Out(d, l, m),
  gm: Replicas.Ext.GainM(Requests.Ask.machine(), d, l, r, m),
  +bd: Replicas.Ext.Based(Requests.Ask.machine(), d, l, r),
  hg: @r1: Replicas.Run<Vend.L(d)> -> Replicas.Ext.Based(Requests.Ask.machine(), d, l, r1) -> Kp.Has(d, l, r1) -> Kp.Out(d, l, g(r1))
) -> Kp.Out(d, l, Maybe.bind(&2, Replicas.Run<Vend.L(d)>, Replicas.Run<Vend.L(d)>, m, g)):
  match m:
    case None{}:
      Unit{}
    case Some{+r1}:
      hg(r1)(Replicas.Ext.based(~Requests.Ask.machine(), ~d, l, r, r1, bd, gm))(hm)

# a run one request on has a good tip, when the run has
def Kp.next(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  r2: Replicas.Run<Vend.L(d)>,
  +vs: Maybe<&2, List<&2, String>>,
  kh: Kp.Has(d, l, r2)
) -> Kp.Has(d, l, Replicas.Run.next(Vend.L(d), r2, vs)):
  match r2:
    case Replicas.Run{+lr, +t, +a}:
      match t:
        case Replicas.Tip{+c, +lg, +n, +old}:
          kh

# the run after a request that its line refused as stale has a good tip
def Kp.stale(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +r: Replicas.Run<Vend.L(d)>,
  +i: Ledgers.Id,
  +a: Hashes.Hash,
  +bd: Replicas.Ext.Based(Requests.Ask.machine(), d, l, r),
  hr: Kp.Has(d, l, r)
) -> Kp.Out(d, l, Replicas.Step.stale(~Requests.Ask.machine(), ~d, r, i, a)):
  Kp.add(
    ~d,
    l,
    r,
    Replicas.Log.out(i),
    Replicas.Out.code(Replicas.Out.Stale{a}, []),
    bd,
    hr,
    hh0 => g0 => Kp.wrote_out(~d, l, i, Replicas.Out.code(Replicas.Out.Stale{a}, []))
  )

# the run after a request that its line took as the number n has a good tip
def Kp.taken.at(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +r: Replicas.Run<Vend.L(d)>,
  +i: Ledgers.Id,
  +a: Hashes.Hash,
  +n: U32,
  +vs: Maybe<&2, List<&2, String>>,
  +bd: Replicas.Ext.Based(Requests.Ask.machine(), d, l, r),
  hr: Kp.Has(d, l, r)
) -> Kp.Out(d, l, Replicas.Step.taken.at(~Requests.Ask.machine(), ~d, r, i, a, n, vs)):
  Kp.bind(
    ~d,
    l,
    r,
    Replicas.Run.add(~Requests.Ask.machine(), ~d, r, Replicas.Log.out(i), Replicas.Out.code(Replicas.Out.Taken{a, n}, [])),
    +r1 => Maybe.bind(
      &2,
      Replicas.Run<Vend.L(d)>,
      Replicas.Run<Vend.L(d)>,
      Replicas.Run.add(
        ~Requests.Ask.machine(),
        ~d,
        r1,
        Replicas.Log.taken(n),
        Replicas.Taken.code(Replicas.Taken{i, Replicas.Tip.content(Replicas.Run.tip(Vend.L(d), r1))}, [])
      ),
      r2 => Some{Replicas.Run.next(Vend.L(d), r2, vs)}
    ),
    Kp.add(
      ~d,
      l,
      r,
      Replicas.Log.out(i),
      Replicas.Out.code(Replicas.Out.Taken{a, n}, []),
      bd,
      hr,
      hh0 => g0 => Kp.wrote_out(~d, l, i, Replicas.Out.code(Replicas.Out.Taken{a, n}, []))
    ),
    Replicas.Ext.add(~Requests.Ask.machine(), ~d, l, r, Replicas.Log.out(i), Replicas.Out.code(Replicas.Out.Taken{a, n}, [])),
    bd,
    +r1 => +bd1 => hr1 => Kp.bind(
      ~d,
      l,
      r1,
      Replicas.Run.add(
        ~Requests.Ask.machine(),
        ~d,
        r1,
        Replicas.Log.taken(n),
        Replicas.Taken.code(Replicas.Taken{i, Replicas.Tip.content(Replicas.Run.tip(Vend.L(d), r1))}, [])
      ),
      r2 => Some{Replicas.Run.next(Vend.L(d), r2, vs)},
      Kp.add(
        ~d,
        l,
        r1,
        Replicas.Log.taken(n),
        Replicas.Taken.code(Replicas.Taken{i, Replicas.Tip.content(Replicas.Run.tip(Vend.L(d), r1))}, []),
        bd1,
        hr1,
        hh0 => g0 => Kp.wrote_taken(~d, l, n, Replicas.Taken.code(Replicas.Taken{i, Replicas.Tip.content(Replicas.Run.tip(Vend.L(d), r1))}, []))
      ),
      Replicas.Ext.add(
        ~Requests.Ask.machine(),
        ~d,
        l,
        r1,
        Replicas.Log.taken(n),
        Replicas.Taken.code(Replicas.Taken{i, Replicas.Tip.content(Replicas.Run.tip(Vend.L(d), r1))}, [])
      ),
      bd1,
      r2 => bd2 => hr2 => Kp.next(~d, l, r2, vs, hr2)
    )
  )

# the run after a request that its line took as its next number has a good tip
def Kp.taken(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +r: Replicas.Run<Vend.L(d)>,
  +i: Ledgers.Id,
  +a: Hashes.Hash,
  +vs: Maybe<&2, List<&2, String>>,
  +bd: Replicas.Ext.Based(Requests.Ask.machine(), d, l, r),
  hr: Kp.Has(d, l, r)
) -> Kp.Out(d, l, Replicas.Step.taken(~Requests.Ask.machine(), ~d, r, i, a, vs)):
  Kp.taken.at(~d, l, r, i, a, Replicas.Tip.count(Replicas.Run.tip(Vend.L(d), r)), vs, bd, hr)

# the run after a label, once the taken request that it names is known (v), has a
# good tip
def Kp.labelled(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +r: Replicas.Run<Vend.L(d)>,
  +i: Ledgers.Id,
  +a: Hashes.Hash,
  +m: String,
  v: Maybe<&2, Replicas.Taken>,
  +bd: Replicas.Ext.Based(Requests.Ask.machine(), d, l, r),
  hr: Kp.Has(d, l, r)
) -> Kp.Out(d, l, Replicas.Step.labelled(~Requests.Ask.machine(), ~d, r, i, a, m, v)):
  match v:
    case None{}:
      Unit{}
    case Some{+x}:
      Kp.bind(
        ~d,
        l,
        r,
        Replicas.Run.add(~Requests.Ask.machine(), ~d, r, Replicas.Log.label(m), Ledgers.Id.code(Replicas.Taken.id(x), [])),
        r2 => Replicas.Step.taken(~Requests.Ask.machine(), ~d, r2, i, a, None{}),
        Kp.add(
          ~d,
          l,
          r,
          Replicas.Log.label(m),
          Ledgers.Id.code(Replicas.Taken.id(x), []),
          bd,
          hr,
          hh0 => g0 => Kp.wrote_label(~d, l, m, Ledgers.Id.code(Replicas.Taken.id(x), []))
        ),
        Replicas.Ext.add(~Requests.Ask.machine(), ~d, l, r, Replicas.Log.label(m), Ledgers.Id.code(Replicas.Taken.id(x), [])),
        bd,
        r2 => bd2 => hr2 => Kp.taken(~d, l, r2, i, a, None{}, bd2, hr2)
      )

# the run after a request for a label, once the read of the label is known (k),
# has a good tip
def Kp.label.at(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +r: Replicas.Run<Vend.L(d)>,
  +i: Ledgers.Id,
  +a: Hashes.Hash,
  +m: String,
  k: Maybe<&2, Maybe<&2, Ledgers.Id>>,
  +bd: Replicas.Ext.Based(Requests.Ask.machine(), d, l, r),
  hr: Kp.Has(d, l, r)
) -> Kp.Out(d, l, Replicas.Step.label.at(~Requests.Ask.machine(), ~d, r, i, a, m, k)):
  match k:
    case None{}:
      Unit{}
    case Some{Some{+x}}:
      Kp.stale(~d, l, r, i, a, bd, hr)
    case Some{None{}}:
      Shared.Bool.when_cases(
        Maybe<&2, Replicas.Run<Vend.L(d)>>,
        z => Kp.Has(d, l, r) -> Kp.Out(d, l, z),
        U32.is_eq(Replicas.Tip.count(Replicas.Run.tip(Vend.L(d), r)), 0),
        u => Replicas.Step.stale(~Requests.Ask.machine(), ~d, r, i, a),
        u => Replicas.Step.labelled(
          ~Requests.Ask.machine(),
          ~d,
          r,
          i,
          a,
          m,
          Replicas.Tip.taken(
            ~Requests.Ask.machine(),
            ~d,
            Replicas.Run.ledger(Vend.L(d), r),
            Replicas.Run.tip(Vend.L(d), r),
            U32.sub(Replicas.Tip.count(Replicas.Run.tip(Vend.L(d), r)), 1)
          )
        ),
        e => hr1 => Kp.stale(~d, l, r, i, a, bd, hr1),
        e => hr1 => Kp.labelled(
          ~d,
          l,
          r,
          i,
          a,
          m,
          Replicas.Tip.taken(
            ~Requests.Ask.machine(),
            ~d,
            Replicas.Run.ledger(Vend.L(d), r),
            Replicas.Run.tip(Vend.L(d), r),
            U32.sub(Replicas.Tip.count(Replicas.Run.tip(Vend.L(d), r)), 1)
          ),
          bd,
          hr1
        )
      )(hr)

# the run after a request for a label has a good tip
def Kp.label(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +r: Replicas.Run<Vend.L(d)>,
  +i: Ledgers.Id,
  +a: Hashes.Hash,
  +m: String,
  +bd: Replicas.Ext.Based(Requests.Ask.machine(), d, l, r),
  hr: Kp.Has(d, l, r)
) -> Kp.Out(d, l, Replicas.Step.label(~Requests.Ask.machine(), ~d, r, i, a, m)):
  Kp.label.at(
    ~d,
    l,
    r,
    i,
    a,
    m,
    Replicas.Tip.known(
      ~Ledgers.Id,
      ~Ledgers.Id.code,
      ~Ledgers.Id.code.read,
      Replicas.Tip.find(~Requests.Ask.machine(), ~d, Replicas.Run.ledger(Vend.L(d), r), Replicas.Run.tip(Vend.L(d), r), Replicas.Log.label(m))
    ),
    bd,
    hr
  )

# an owner act gives a kept tree
def Own.act_kept(
  ~d: Vend.Led(),
  +lf: Vend.L(d),
  +t: Replicas.Tip,
  +g: String,
  +at: Maybe<&2, Requests.Source>,
  +os: List<&2, String>,
  +a: Replicas.Act,
  hk: {Vend.Tree.kept(~d, lf, Replicas.Tip.content(t)) == True{}: Bool},
  ec: {Owners.Own.act(~d, lf, t, g, at, os) == Some{a}: Maybe<&2, Replicas.Act>},
  hh: {Replicas.Act.held(~Requests.Ask.machine(), ~d, lf, a) == True{}: Bool}
) -> Store.Acts.Kept(~d, lf, a):
  Store.Kept.when(
    ~d,
    lf,
    Vend.Tree.whole(~d, lf, Owners.Own.tree(t, at)),
    u => Maybe.bind(
      &2,
      List<&2, String>,
      Replicas.Act,
      Owners.Group.nodes(~d, lf, Owners.Own.tree(t, at), g),
      +ns => Shared.Bool.when(
        Maybe<&2, Replicas.Act>,
        List.all.if(
          v => Shared.List.same_set(~String, ~String.eq, os, ns),
          Bool.not(List.is_empty(&2, String, os))
        ),
        v => Vend.Act.put(
          Some{os},
          [],
          Replicas.Tree.put(
            ~Requests.Ask.machine(),
            ~d,
            lf,
            Replicas.Tip.content(t),
            Owners.Key.owner(),
            Some{Codes.Code.text(g, [])}
          )
        ),
        v => Some{Replicas.Act.Stale{}}
      )
    ),
    u => None{},
    a,
    e1 => Store.Kept.bind(
      ~d,
      lf,
      List<&2, String>,
      Owners.Group.nodes(~d, lf, Owners.Own.tree(t, at), g),
      +ns => Shared.Bool.when(
        Maybe<&2, Replicas.Act>,
        List.all.if(
          v => Shared.List.same_set(~String, ~String.eq, os, ns),
          Bool.not(List.is_empty(&2, String, os))
        ),
        v => Vend.Act.put(
          Some{os},
          [],
          Replicas.Tree.put(
            ~Requests.Ask.machine(),
            ~d,
            lf,
            Replicas.Tip.content(t),
            Owners.Key.owner(),
            Some{Codes.Code.text(g, [])}
          )
        ),
        v => Some{Replicas.Act.Stale{}}
      ),
      a,
      ns => e2 => Store.Kept.when(
        ~d,
        lf,
        List.all.if(
          v => Shared.List.same_set(~String, ~String.eq, os, ns),
          Bool.not(List.is_empty(&2, String, os))
        ),
        v => Vend.Act.put(
          Some{os},
          [],
          Replicas.Tree.put(
            ~Requests.Ask.machine(),
            ~d,
            lf,
            Replicas.Tip.content(t),
            Owners.Key.owner(),
            Some{Codes.Code.text(g, [])}
          )
        ),
        v => Some{Replicas.Act.Stale{}},
        a,
        e3 => Store.Act.put_kept(
          ~d,
          lf,
          Replicas.Tip.content(t),
          Owners.Key.owner(),
          Some{Codes.Code.text(g, [])},
          Some{os},
          [],
          a,
          hk,
          e3,
          hh,
          v => e => {==}
        ),
        e3 => (%Shared.Maybe.some_inj(Replicas.Act, Replicas.Act.Stale{}, a, e3) : Store.Acts.Kept(~d, lf, _); Unit{}),
        e2
      ),
      e1
    ),
    e1 => Empty.absurd(Store.Acts.Kept(~d, lf, a), Shared.Maybe.none_ne_some(Replicas.Act, a, e1)),
    ec
  )

# a group act, once the groups of the tree are known (gs), gives a kept tree
def Group.act.of_kept(
  ~d: Vend.Led(),
  +lf: Vend.L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +g: String,
  +ms: List<&2, Requests.Member>,
  gs: List<&2, Owners.Group>,
  +a: Replicas.Act,
  hk: {Vend.Tree.kept(~d, lf, h) == True{}: Bool},
  ec: {Owners.Group.act.of(~d, lf, h, g, ms, gs) == Some{a}: Maybe<&2, Replicas.Act>},
  hh: {Replicas.Act.held(~Requests.Ask.machine(), ~d, lf, a) == True{}: Bool}
) -> Store.Acts.Kept(~d, lf, a):
  Store.Kept.when(
    ~d,
    lf,
    Crits.Dict.has(Unit, Owners.Group.reach(Owners.Groups.set(gs, g, ms), g), Owners.Group.key(g)),
    u => Some{Replicas.Act.Stale{}},
    u => Vend.Act.put(
      None{},
      [],
      Replicas.Tree.put(~Requests.Ask.machine(), ~d, lf, h, Owners.Key.group(g), Some{Requests.Members.code(ms, [])})
    ),
    a,
    e3 => (%Shared.Maybe.some_inj(Replicas.Act, Replicas.Act.Stale{}, a, e3) : Store.Acts.Kept(~d, lf, _); Unit{}),
    e3 => Store.Act.put_kept(
      ~d,
      lf,
      h,
      Owners.Key.group(g),
      Some{Requests.Members.code(ms, [])},
      None{},
      [],
      a,
      hk,
      e3,
      hh,
      v => e => {==}
    ),
    ec
  )

# a group act gives a kept tree
def Group.act_kept(
  ~d: Vend.Led(),
  +lf: Vend.L(d),
  +t: Replicas.Tip,
  +g: String,
  +ms: List<&2, Requests.Member>,
  +a: Replicas.Act,
  hk: {Vend.Tree.kept(~d, lf, Replicas.Tip.content(t)) == True{}: Bool},
  ec: {Owners.Group.act(~d, lf, t, g, ms) == Some{a}: Maybe<&2, Replicas.Act>},
  hh: {Replicas.Act.held(~Requests.Ask.machine(), ~d, lf, a) == True{}: Bool}
) -> Store.Acts.Kept(~d, lf, a):
  Store.Kept.when(
    ~d,
    lf,
    Vend.Tree.whole(~d, lf, Replicas.Tip.content(t)),
    u => Maybe.bind(
      &2,
      List<&2, Owners.Group>,
      Replicas.Act,
      Owners.Groups.in(~d, lf, Replicas.Tip.content(t)),
      gs => Owners.Group.act.of(~d, lf, Replicas.Tip.content(t), g, ms, gs)
    ),
    u => None{},
    a,
    e1 => Store.Kept.bind(
      ~d,
      lf,
      List<&2, Owners.Group>,
      Owners.Groups.in(~d, lf, Replicas.Tip.content(t)),
      gs => Owners.Group.act.of(~d, lf, Replicas.Tip.content(t), g, ms, gs),
      a,
      gs => e2 => Group.act.of_kept(~d, lf, Replicas.Tip.content(t), g, ms, gs, a, hk, e2, hh),
      e1
    ),
    e1 => Empty.absurd(Store.Acts.Kept(~d, lf, a), Shared.Maybe.none_ne_some(Replicas.Act, a, e1)),
    ec
  )

# a change gives a kept tree
def Change.act_kept(
  ~d: Vend.Led(),
  +lf: Vend.L(d),
  +t: Replicas.Tip,
  b: Maybe<&2, String>,
  +i: Ledgers.Id,
  ch: Requests.Change,
  +a: Replicas.Act,
  hk: {Vend.Tree.kept(~d, lf, Replicas.Tip.content(t)) == True{}: Bool},
  ec: {Owners.Change.act(~d, lf, t, b, i, ch) == Some{a}: Maybe<&2, Replicas.Act>},
  hh: {Replicas.Act.held(~Requests.Ask.machine(), ~d, lf, a) == True{}: Bool}
) -> Store.Acts.Kept(~d, lf, a):
  match b ch:
    case Some{x} Requests.Change.Write{n, base, c}:
      Store.Write.act_kept(~d, lf, t, n, base, c, a, hk, ec, hh)
    case Some{x} Requests.Change.Resolve{k, n, c}:
      Store.Resolve.act_kept(~d, lf, t, k, n, c, a, hk, ec, hh)
    case Some{x} Requests.Change.Merge{from, base}:
      Store.Merge.act_kept_a(~d, lf, t, i, from, base, a, ec, hh)
    case Some{x} Requests.Change.Move{to}:
      Store.Move.act_kept(~d, lf, to, a, ec)
    case Some{x} Requests.Change.Mark{m, text}:
      %Shared.Maybe.some_inj(Replicas.Act, Replicas.Act.Label{m}, a, ec): Store.Acts.Kept(~d, lf, _)
      Unit{}
    case None{} Requests.Change.Branch{n, at}:
      Store.Branch.act_kept(~d, lf, t, n, at, a, ec)
    case None{} Requests.Change.Group{g, ms}:
      Group.act_kept(~d, lf, t, g, ms, a, hk, ec, hh)
    case None{} Requests.Change.Key{n, k}:
      Store.Key.act_kept(~d, lf, t, n, k, a, hk, ec, hh)
    case y Requests.Change.Own{g, at, os}:
      Own.act_kept(~d, lf, t, g, at, os, a, hk, ec, hh)
    case Some{x} Requests.Change.Branch{n, at}:
      %Shared.Maybe.some_inj(Replicas.Act, Replicas.Act.Stale{}, a, ec): Store.Acts.Kept(~d, lf, _)
      Unit{}
    case Some{x} Requests.Change.Group{n, ms}:
      %Shared.Maybe.some_inj(Replicas.Act, Replicas.Act.Stale{}, a, ec): Store.Acts.Kept(~d, lf, _)
      Unit{}
    case Some{x} Requests.Change.Key{n, k}:
      %Shared.Maybe.some_inj(Replicas.Act, Replicas.Act.Stale{}, a, ec): Store.Acts.Kept(~d, lf, _)
      Unit{}
    case None{} Requests.Change.Write{n, base, c}:
      %Shared.Maybe.some_inj(Replicas.Act, Replicas.Act.Stale{}, a, ec): Store.Acts.Kept(~d, lf, _)
      Unit{}
    case None{} Requests.Change.Resolve{k, n, c}:
      %Shared.Maybe.some_inj(Replicas.Act, Replicas.Act.Stale{}, a, ec): Store.Acts.Kept(~d, lf, _)
      Unit{}
    case None{} Requests.Change.Merge{from, base}:
      %Shared.Maybe.some_inj(Replicas.Act, Replicas.Act.Stale{}, a, ec): Store.Acts.Kept(~d, lf, _)
      Unit{}
    case None{} Requests.Change.Move{to}:
      %Shared.Maybe.some_inj(Replicas.Act, Replicas.Act.Stale{}, a, ec): Store.Acts.Kept(~d, lf, _)
      Unit{}
    case None{} Requests.Change.Mark{m, text}:
      %Shared.Maybe.some_inj(Replicas.Act, Replicas.Act.Stale{}, a, ec): Store.Acts.Kept(~d, lf, _)
      Unit{}

# a request gives a kept tree
def Ask.act_kept(
  ~d: Vend.Led(),
  +lf: Vend.L(d),
  +t: Replicas.Tip,
  +c: Ledgers.Line,
  +i: Ledgers.Id,
  q: Requests.Ask,
  +a: Replicas.Act,
  hk: {Vend.Tree.kept(~d, lf, Replicas.Tip.content(t)) == True{}: Bool},
  ec: {Owners.Ask.act(~d, lf, t, c, i, q) == Some{a}: Maybe<&2, Replicas.Act>},
  hh: {Replicas.Act.held(~Requests.Ask.machine(), ~d, lf, a) == True{}: Bool}
) -> Store.Acts.Kept(~d, lf, a):
  match q:
    case Requests.Ask.Start{vs}:
      %Shared.Maybe.some_inj(Replicas.Act, Replicas.Act.Stale{}, a, ec): Store.Acts.Kept(~d, lf, _)
      Unit{}
    case Requests.Ask.On{+st, +b, +ch}:
      Store.Kept.when(
        ~d,
        lf,
        Ledgers.Line.is_eq(Ledgers.Line{st, b}, c),
        u => Owners.Change.act(~d, lf, t, b, i, ch),
        u => Some{Replicas.Act.Stale{}},
        a,
        e1 => Change.act_kept(~d, lf, t, b, i, ch, a, hk, e1, hh),
        e1 => (%Shared.Maybe.some_inj(Replicas.Act, Replicas.Act.Stale{}, a, e1) : Store.Acts.Kept(~d, lf, _); Unit{}),
        ec
      )

# a node that is the first of a list is in it
def Kp.contains_head(
  +w: List<&2, U32>,
  r: List<&2, List<&2, U32>>
) -> {List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), w <> r, w) == True{}: Bool}:
  %Equal.sym(Bool, Shared.List.is_eq(~U32, ~U32.is_eq, w, w), True{}, Shared.List.is_eq_refl(~U32, ~U32.is_eq, ~Shared.U32.laws(), w)): {
    List.any.if(u => List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), r, w), _) == True{}: Bool
  }
  {==}

# a tip whose node the ledger holds is the tip that its hash names, in a code
def Kp.tip_named(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +t: Replicas.Tip,
  +ns: List<&2, List<&2, U32>>,
  hh: {Replicas.Ext.holds(~Requests.Ask.machine(), ~d, l, Replicas.Tip.code(t, []) <> ns) == True{}: Bool}
) -> {Replicas.Tip.named(~Requests.Ask.machine(), ~d, l, Hashes.Hash.code(Replicas.Tip.hash(t), [])) == Some{t}: Maybe<&2, Replicas.Tip>}:
  %Equal.sym(
    Maybe<&2, Hashes.Hash>,
    Codes.Code.whole.read(~Hashes.Hash, ~Hashes.Hash.code, ~Hashes.Hash.code.read, Hashes.Hash.code(Replicas.Tip.hash(t), [])),
    Some{Replicas.Tip.hash(t)},
    Codes.Code.whole_read(~Hashes.Hash, ~Hashes.Hash.code, ~Hashes.Hash.code.read, ~(x => r => Hashes.Hash.code_read(x, r)), Replicas.Tip.hash(t))
  ): {Replicas.Tip.of(~Requests.Ask.machine(), ~d, l, _) == Some{t}: Maybe<&2, Replicas.Tip>}
  %Equal.sym(
    Maybe<&2, List<&2, U32>>,
    Replicas.Led.fetch(~Requests.Ask.machine(), ~d)(l)(Replicas.Tip.hash(t)),
    Some{Replicas.Tip.code(t, [])},
    Replicas.Ext.held.of(
      ~Requests.Ask.machine(),
      ~d,
      l,
      Replicas.Tip.code(t, []) <> ns,
      Replicas.Tip.code(t, []),
      hh,
      Kp.contains_head(Replicas.Tip.code(t, []), ns)
    )
  ): {Codes.Code.whole.of(~Replicas.Tip, ~Replicas.Tip.code, ~Replicas.Tip.code.read, _) == Some{t}: Maybe<&2, Replicas.Tip>}
  Codes.Code.whole_read(~Replicas.Tip, ~Replicas.Tip.code, ~Replicas.Tip.code.read, ~(x => r => Replicas.Tip.code_read(x, r)), t)

# the first tip of a sub line that a log names is good, once the ledger holds the
# node of the tip and the tip is
def Kp.wrote_start(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +b: String,
  +t: Replicas.Tip,
  +ns: List<&2, List<&2, U32>>,
  hh: {Replicas.Ext.holds(~Requests.Ask.machine(), ~d, l, Replicas.Tip.code(t, []) <> ns) == True{}: Bool},
  ak: Merges.Merge.And({Vend.Tree.kept(~d, l, Replicas.Tip.content(t)) == True{}: Bool}, {Replicas.Tip.log(t) == None{}: Maybe<&2, Hashes.Hash>})
) -> Kp.Wrote(d, l, Replicas.Log.start(b), Hashes.Hash.code(Replicas.Tip.hash(t), [])):
  +b2 => he => +tb => hn =>
    %Shared.Maybe.some_inj(
      Replicas.Tip,
      t,
      tb,
      %Kp.tip_named(~d, l, t, ns, hh): {_ == Some{tb}: Maybe<&2, Replicas.Tip>}
      hn
    ): Merges.Merge.And({Vend.Tree.kept(~d, l, Replicas.Tip.content(_)) == True{}: Bool}, {Replicas.Tip.log(_) == None{}: Maybe<&2, Hashes.Hash>})
    ak

# a tip with new content that is kept is good, when the tip before it is
def Kp.over.pair(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +c: Maybe<&2, Hashes.Hash>,
  +lg: Maybe<&2, Hashes.Hash>,
  +n: U32,
  +vs: List<&2, String>,
  hk: {Vend.Tree.kept(~d, l, c) == True{}: Bool} -> {Vend.Tree.kept(~d, l, h) == True{}: Bool},
  g: Kp.Good(d, l, Replicas.Tip{c, lg, n, vs})
) -> Kp.Good(d, l, Replicas.Tip{h, lg, n, vs}):
  (+g1, g2) = g
  (hk(g1), g2)

# new content that is kept gives a tip that is good, when the tip before it is,
# once the ledger holds the nodes that come with the content
def Kp.over(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  r: Replicas.Run<Vend.L(d)>,
  +ns: List<&2, List<&2, U32>>,
  +h: Maybe<&2, Hashes.Hash>,
  hk: {Replicas.Ext.holds(~Requests.Ask.machine(), ~d, l, List.append(&2, List<&2, U32>, ns, Replicas.Run.added(Vend.L(d), r))) == True{}: Bool}
    -> {Vend.Tree.kept(~d, l, Replicas.Tip.content(Replicas.Run.tip(Vend.L(d), r))) == True{}: Bool} -> {Vend.Tree.kept(~d, l, h) == True{}: Bool},
  hr: Kp.Has(d, l, r)
) -> Kp.Has(d, l, Replicas.Run.over(~Requests.Ask.machine(), ~d, r, ns, h)):
  match r:
    case Replicas.Run{+lr, +t, +a}:
      match t:
        case Replicas.Tip{+c, +lg, +n, +vs}:
          +hh => Kp.over.pair(~d, l, h, c, lg, n, vs, +g1 => hk(hh)(g1), hr(Replicas.Ext.holds_right(~Requests.Ask.machine(), ~d, l, ns, a)(hh)))

# the same content, with more nodes, gives a tip that is good, when the tip
# before it is
def Kp.over.same(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  r: Replicas.Run<Vend.L(d)>,
  +ns: List<&2, List<&2, U32>>,
  hr: Kp.Has(d, l, r)
) -> Kp.Has(d, l, Replicas.Run.over(~Requests.Ask.machine(), ~d, r, ns, Replicas.Tip.content(Replicas.Run.tip(Vend.L(d), r)))):
  match r:
    case Replicas.Run{+lr, +t, +a}:
      match t:
        case Replicas.Tip{+c, +lg, +n, +vs}:
          +hh => hr(Replicas.Ext.holds_right(~Requests.Ask.machine(), ~d, l, ns, a)(hh))

# the first tip of a sub line that a run opens gives a run whose tip is good
def Kp.opens(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  r: Replicas.Run<Vend.L(d)>,
  +i: Ledgers.Id,
  +a: Hashes.Hash,
  +b: String,
  +t: Replicas.Tip,
  +ns: List<&2, List<&2, U32>>,
  +bd: Replicas.Ext.Based(Requests.Ask.machine(), d, l, r),
  hr: Kp.Has(d, l, r),
  ak: {Replicas.Ext.holds(~Requests.Ask.machine(), ~d, l, ns) == True{}: Bool}
    -> {Replicas.Ext.holds(~Requests.Ask.machine(), ~d, l, Replicas.Run.added(Vend.L(d), r)) == True{}: Bool}
    -> {Vend.Tree.kept(~d, l, Replicas.Tip.content(Replicas.Run.tip(Vend.L(d), r))) == True{}: Bool}
    -> Merges.Merge.And({Vend.Tree.kept(~d, l, Replicas.Tip.content(t)) == True{}: Bool}, {Replicas.Tip.log(t) == None{}: Maybe<&2, Hashes.Hash>})
) -> Kp.Out(d, l, Replicas.Step.opens(~Requests.Ask.machine(), ~d, r, i, a, b, t, ns)):
  match r:
    case Replicas.Run{+lr, +tr, +a0}:
      match tr:
        case Replicas.Tip{+c, +lg, +n, +vs}:
          +r0 = Replicas.Run.over(
            ~Requests.Ask.machine(),
            ~d,
            Replicas.Run{lr, Replicas.Tip{c, lg, n, vs}, a0},
            Replicas.Tip.code(t, []) <> ns,
            Replicas.Tip.content(Replicas.Run.tip(Vend.L(d), Replicas.Run{lr, Replicas.Tip{c, lg, n, vs}, a0}))
          )
          Kp.bind(
            ~d,
            l,
            Replicas.Run{lr, Replicas.Tip{c, lg, n, vs}, a0},
            Replicas.Run.add(~Requests.Ask.machine(), ~d, r0, Replicas.Log.start(b), Hashes.Hash.code(Replicas.Tip.hash(t), [])),
            r2 => Replicas.Step.taken(~Requests.Ask.machine(), ~d, r2, i, a, None{}),
            Kp.add(
              ~d,
              l,
              r0,
              Replicas.Log.start(b),
              Hashes.Hash.code(Replicas.Tip.hash(t), []),
              Replicas.Ext.based(
                ~Requests.Ask.machine(),
                ~d,
                l,
                Replicas.Run{lr, Replicas.Tip{c, lg, n, vs}, a0},
                r0,
                bd,
                Replicas.Ext.over(
                  ~Requests.Ask.machine(),
                  ~d,
                  l,
                  Replicas.Run{lr, Replicas.Tip{c, lg, n, vs}, a0},
                  Replicas.Tip.code(t, []) <> ns,
                  Replicas.Tip.content(Replicas.Run.tip(Vend.L(d), Replicas.Run{lr, Replicas.Tip{c, lg, n, vs}, a0}))
                )
              ),
              Kp.over.same(
                ~d,
                l,
                Replicas.Run{lr, Replicas.Tip{c, lg, n, vs}, a0},
                Replicas.Tip.code(t, []) <> ns,
                hr
              ),
              +hh0 => +g0 => Kp.wrote_start(
                ~d,
                l,
                b,
                t,
                ns,
                Replicas.Ext.holds_left(~Requests.Ask.machine(), ~d, l, Replicas.Tip.code(t, []) <> ns, a0)(hh0),
                ak(
                  Shared.List.all.if_rest(
                    Replicas.Ext.has(~Requests.Ask.machine(), ~d, l, Replicas.Tip.code(t, [])),
                    u => Replicas.Ext.holds(~Requests.Ask.machine(), ~d, l, ns)
                  )(Replicas.Ext.holds_left(~Requests.Ask.machine(), ~d, l, Replicas.Tip.code(t, []) <> ns, a0)(hh0))
                )(Replicas.Ext.holds_right(~Requests.Ask.machine(), ~d, l, Replicas.Tip.code(t, []) <> ns, a0)(hh0))(g0)
              )
            ),
            Replicas.Ext.transM(
              ~Requests.Ask.machine(),
              ~d,
              l,
              Replicas.Run{lr, Replicas.Tip{c, lg, n, vs}, a0},
              r0,
              Replicas.Run.add(~Requests.Ask.machine(), ~d, r0, Replicas.Log.start(b), Hashes.Hash.code(Replicas.Tip.hash(t), [])),
              Replicas.Ext.over(
                ~Requests.Ask.machine(),
                ~d,
                l,
                Replicas.Run{lr, Replicas.Tip{c, lg, n, vs}, a0},
                Replicas.Tip.code(t, []) <> ns,
                Replicas.Tip.content(Replicas.Run.tip(Vend.L(d), Replicas.Run{lr, Replicas.Tip{c, lg, n, vs}, a0}))
              ),
              Replicas.Ext.add(~Requests.Ask.machine(), ~d, l, r0, Replicas.Log.start(b), Hashes.Hash.code(Replicas.Tip.hash(t), []))
            ),
            bd,
            r2 => bd2 => hr2 => Kp.taken(~d, l, r2, i, a, None{}, bd2, hr2)
          )

# the first part of a good tip: its content is kept
def Kp.kept_of(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +t: Replicas.Tip,
  g: Kp.Good(d, l, t)
) -> {Vend.Tree.kept(~d, l, Replicas.Tip.content(t)) == True{}: Bool}:
  (+g1, g2) = g
  g1

# what the kernel of Vend does with a request is what Ask.act says
def Kp.rules_change(
  ~d: Vend.Led(),
  ~kern: Vend.Kern(d),
  rules: Kernel.Rules(d, kern),
  +l: Vend.L(d),
  +t: Replicas.Tip,
  +c: Ledgers.Line,
  +i: Ledgers.Id,
  +q: Requests.Ask
) -> {
  Replicas.Kernel.change(Requests.Ask.machine(), d, kern)(l)(t)(c)(i)(q) == Owners.Ask.act(~d, l, t, c, i, q): Maybe<&2, Replicas.Act>
}:
  (r1, r2) = rules
  r1(l)(t)(c)(i)(q)

# what the kernel gives for a run, once its tip is good, is an act that the
# ledger holds and whose content is kept, once the ledger holds what the run
# added
def Kp.act_ok.at(
  ~d: Vend.Led(),
  ~kern: Vend.Kern(d),
  ~rules: Kernel.Rules(d, kern),
  +l: Vend.L(d),
  +r: Replicas.Run<Vend.L(d)>,
  +c: Ledgers.Line,
  +i: Ledgers.Id,
  +q: Requests.Ask,
  m: Maybe<&2, Replicas.Act>,
  e: {Replicas.Kernel.change(Requests.Ask.machine(), d, kern)(Replicas.Run.ledger(Vend.L(d), r))(Replicas.Run.tip(Vend.L(d), r))(c)(i)(q) == m: Maybe<&2, Replicas.Act>},
  bd: Replicas.Ext.Based(Requests.Ask.machine(), d, l, r)
) -> Kp.ActOk(d, l, r, m):
  match m:
    case None{}:
      Unit{}
    case Some{+act}:
      +hh => +hr0 => +g1 =>
        Ask.act_kept(
          ~d,
          l,
          Replicas.Run.tip(Vend.L(d), r),
          c,
          i,
          q,
          act,
          g1,
          Equal.trans(
            Maybe<&2, Replicas.Act>,
            Owners.Ask.act(~d, l, Replicas.Run.tip(Vend.L(d), r), c, i, q),
            Replicas.Kernel.change(Requests.Ask.machine(), d, kern)(l)(Replicas.Run.tip(Vend.L(d), r))(c)(i)(q),
            Some{act},
            Equal.sym(
              Maybe<&2, Replicas.Act>,
              Replicas.Kernel.change(Requests.Ask.machine(), d, kern)(l)(Replicas.Run.tip(Vend.L(d), r))(c)(i)(q),
              Owners.Ask.act(~d, l, Replicas.Run.tip(Vend.L(d), r), c, i, q),
              Kp.rules_change(~d, ~kern, rules, l, Replicas.Run.tip(Vend.L(d), r), c, i, q)
            ),
            Replicas.Hist.kern(Requests.Ask.machine(), d, kern)(Replicas.Run.tip(Vend.L(d), r))(c)(i)(q)(Replicas.Run.ledger(Vend.L(d), r))(l)(act)(
              Replicas.Ext.based_grows(~Requests.Ask.machine(), ~d, l, r, bd, hr0)
            )(e)(hh)
          ),
          hh
        )

# what the kernel gives for a run is an act that the ledger holds and whose
# content is kept
def Kp.act_ok(
  ~d: Vend.Led(),
  ~kern: Vend.Kern(d),
  ~rules: Kernel.Rules(d, kern),
  +l: Vend.L(d),
  +r: Replicas.Run<Vend.L(d)>,
  +c: Ledgers.Line,
  +i: Ledgers.Id,
  +q: Requests.Ask,
  bd: Replicas.Ext.Based(Requests.Ask.machine(), d, l, r)
) -> Kp.ActOk(
  d,
  l,
  r,
  Replicas.Kernel.change(Requests.Ask.machine(), d, kern)(Replicas.Run.ledger(Vend.L(d), r))(Replicas.Run.tip(Vend.L(d), r))(c)(i)(q)
):
  Kp.act_ok.at(
    ~d,
    ~kern,
    ~rules,
    l,
    r,
    c,
    i,
    q,
    Replicas.Kernel.change(Requests.Ask.machine(), d, kern)(Replicas.Run.ledger(Vend.L(d), r))(Replicas.Run.tip(Vend.L(d), r))(c)(i)(q),
    {==},
    bd
  )

# the run after an act of a kernel has a good tip
def Kp.act(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +r: Replicas.Run<Vend.L(d)>,
  +i: Ledgers.Id,
  +a: Hashes.Hash,
  m: Maybe<&2, Replicas.Act>,
  +bd: Replicas.Ext.Based(Requests.Ask.machine(), d, l, r),
  hr: Kp.Has(d, l, r),
  ok: Kp.ActOk(d, l, r, m)
) -> Kp.Out(d, l, Replicas.Act.run(~Requests.Ask.machine(), ~d, r, i, a, m)):
  match m:
    case None{}:
      Unit{}
    case Some{Replicas.Act.Stale{}}:
      Kp.stale(~d, l, r, i, a, bd, hr)
    case Some{Replicas.Act.Label{+x}}:
      Kp.label(~d, l, r, i, a, x, bd, hr)
    case Some{Replicas.Act.Taken{+vs, +h, +ns}}:
      Kp.taken(
        ~d,
        l,
        Replicas.Run.over(~Requests.Ask.machine(), ~d, r, ns, h),
        i,
        a,
        vs,
        Replicas.Ext.based(
          ~Requests.Ask.machine(),
          ~d,
          l,
          r,
          Replicas.Run.over(~Requests.Ask.machine(), ~d, r, ns, h),
          bd,
          Replicas.Ext.over(~Requests.Ask.machine(), ~d, l, r, ns, h)
        ),
        Kp.over(
          ~d,
          l,
          r,
          ns,
          h,
          +hh => +g1 => ok(Replicas.Ext.holds_left(~Requests.Ask.machine(), ~d, l, ns, Replicas.Run.added(Vend.L(d), r))(hh))(
            Replicas.Ext.holds_right(~Requests.Ask.machine(), ~d, l, ns, Replicas.Run.added(Vend.L(d), r))(hh)
          )(g1),
          hr
        )
      )
    case Some{Replicas.Act.Opens{+b, +t, +ns}}:
      Kp.opens(~d, l, r, i, a, b, t, ns, bd, hr, ok)

# the run after a request with the outcome o has a good tip
def Kp.fresh(
  ~d: Vend.Led(),
  ~kern: Vend.Kern(d),
  ~rules: Kernel.Rules(d, kern),
  +l: Vend.L(d),
  +r: Replicas.Run<Vend.L(d)>,
  +c: Ledgers.Line,
  +i: Ledgers.Id,
  +a: Hashes.Hash,
  +q: Requests.Ask,
  o: Maybe<&2, Maybe<&2, Replicas.Out>>,
  +bd: Replicas.Ext.Based(Requests.Ask.machine(), d, l, r),
  hr: Kp.Has(d, l, r)
) -> Kp.Out(d, l, Replicas.Step.fresh(~Requests.Ask.machine(), ~d, ~kern, r, c, i, a, q, o)):
  match o:
    case None{}:
      Unit{}
    case Some{Some{x}}:
      hr
    case Some{None{}}:
      Kp.act(
        ~d,
        l,
        r,
        i,
        a,
        Replicas.Kernel.change(Requests.Ask.machine(), d, kern)(Replicas.Run.ledger(Vend.L(d), r))(Replicas.Run.tip(Vend.L(d), r))(c)(i)(q),
        bd,
        hr,
        Kp.act_ok(~d, ~kern, ~rules, l, r, c, i, q, bd)
      )

# the run after the entry m has a good tip
def Kp.asked(
  ~d: Vend.Led(),
  ~kern: Vend.Kern(d),
  ~rules: Kernel.Rules(d, kern),
  +l: Vend.L(d),
  +r: Replicas.Run<Vend.L(d)>,
  +c: Ledgers.Line,
  +a: Hashes.Hash,
  m: Maybe<&2, Ledgers.Entry<Requests.Ask>>,
  +bd: Replicas.Ext.Based(Requests.Ask.machine(), d, l, r),
  hr: Kp.Has(d, l, r)
) -> Kp.Out(d, l, Replicas.Step.asked(~Requests.Ask.machine(), ~d, ~kern, r, c, a, m)):
  match m:
    case Some{Ledgers.Entry.Ask{+i, t, q}}:
      Kp.fresh(
        ~d,
        ~kern,
        ~rules,
        l,
        r,
        c,
        i,
        a,
        q,
        Replicas.Tip.known(
          ~Replicas.Out,
          ~Replicas.Out.code,
          ~Replicas.Out.code.read,
          Replicas.Tip.find(~Requests.Ask.machine(), ~d, Replicas.Run.ledger(Vend.L(d), r), Replicas.Run.tip(Vend.L(d), r), Replicas.Log.out(i))
        ),
        bd,
        hr
      )
    case None{}:
      Unit{}
    case Some{Ledgers.Entry.Ballot{x}}:
      Unit{}
    case Some{Ledgers.Entry.Data{x}}:
      Unit{}
    case Some{Ledgers.Entry.Lie{x}}:
      Unit{}

# the run after one request has a good tip
def Kp.one(
  ~d: Vend.Led(),
  ~kern: Vend.Kern(d),
  ~rules: Kernel.Rules(d, kern),
  +l: Vend.L(d),
  +r: Replicas.Run<Vend.L(d)>,
  +c: Ledgers.Line,
  +a: Hashes.Hash,
  +bd: Replicas.Ext.Based(Requests.Ask.machine(), d, l, r),
  hr: Kp.Has(d, l, r)
) -> Kp.Out(d, l, Replicas.Step.one(~Requests.Ask.machine(), ~d, ~kern, r, c, a)):
  Kp.asked(
    ~d,
    ~kern,
    ~rules,
    l,
    r,
    c,
    a,
    Replicas.Led.get(~Requests.Ask.machine(), ~d, Replicas.Run.ledger(Vend.L(d), r), Ledgers.Name.Ask{a}),
    bd,
    hr
  )

# Kp.All of a run m2 that follows r1
def Kp.all_pair(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +r1: Replicas.Run<Vend.L(d)>,
  m2: Maybe<&2, Replicas.Run<Vend.L(d)>>,
  ko: Kp.Out(d, l, m2),
  gm: Replicas.Ext.GainM(Requests.Ask.machine(), d, l, r1, m2),
  bd: Replicas.Ext.Based(Requests.Ask.machine(), d, l, r1)
) -> Kp.All(d, l, m2):
  match m2:
    case None{}:
      Unit{}
    case Some{+r2}:
      Tuple{Replicas.Ext.based(~Requests.Ask.machine(), ~d, l, r1, r2, bd, gm), ko}

# Kp.All after one more request
def Kp.all_step(
  ~d: Vend.Led(),
  ~kern: Vend.Kern(d),
  ~rules: Kernel.Rules(d, kern),
  +l: Vend.L(d),
  +c: Ledgers.Line,
  +q: Hashes.Hash,
  m: Maybe<&2, Replicas.Run<Vend.L(d)>>,
  hm: Kp.All(d, l, m)
) -> Kp.All(
  d,
  l,
  Maybe.bind(&2, Replicas.Run<Vend.L(d)>, Replicas.Run<Vend.L(d)>, m, x => Replicas.Step.one(~Requests.Ask.machine(), ~d, ~kern, x, c, q))
):
  match m:
    case None{}:
      Unit{}
    case Some{+r1}:
      match hm:
        case Tuple{+bd, hr}:
          Kp.all_pair(
            ~d,
            l,
            r1,
            Replicas.Step.one(~Requests.Ask.machine(), ~d, ~kern, r1, c, q),
            Kp.one(~d, ~kern, ~rules, l, r1, c, q, bd, hr),
            Replicas.Ext.one(~Requests.Ask.machine(), ~d, ~kern, l, r1, c, q),
            bd
          )

# Kp.All gives Kp.Out
def Kp.all_out(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  m: Maybe<&2, Replicas.Run<Vend.L(d)>>,
  hm: Kp.All(d, l, m)
) -> Kp.Out(d, l, m):
  match m:
    case None{}:
      Unit{}
    case Some{r}:
      match hm:
        case Tuple{bd, hr}:
          hr

# the run after each of the requests qs has a good tip
def Kp.all(
  ~d: Vend.Led(),
  ~kern: Vend.Kern(d),
  ~rules: Kernel.Rules(d, kern),
  +l: Vend.L(d),
  +c: Ledgers.Line,
  qs: List<&2, Hashes.Hash>,
  +m: Maybe<&2, Replicas.Run<Vend.L(d)>>,
  hm: Kp.All(d, l, m)
) -> Kp.Out(d, l, Replicas.Step.all(~Requests.Ask.machine(), ~d, ~kern, c, qs, m)):
  match qs:
    case Nil{}:
      Kp.all_out(~d, l, m, hm)
    case Con{+q, rest}:
      Kp.all(
        ~d,
        ~kern,
        ~rules,
        l,
        c,
        rest,
        Maybe.bind(&2, Replicas.Run<Vend.L(d)>, Replicas.Run<Vend.L(d)>, m, x => Replicas.Step.one(~Requests.Ask.machine(), ~d, ~kern, x, c, q)),
        Kp.all_step(~d, ~kern, ~rules, l, c, q, m, hm)
      )

# a line that lands has a good tip, once the check of its run is known (b)
def Kp.landed.at(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +tr: Replicas.Tip,
  +a: List<&2, List<&2, U32>>,
  after: Maybe<&2, Hashes.Hash>,
  +x: Replicas.Tip,
  b: Bool,
  eb: {
    Bool.and(Replicas.Tips.same(Some{Replicas.Tip.hash(tr)}, after), Replicas.Ext.holds(~Requests.Ask.machine(), ~d, l, a)) == b: Bool
  },
  ko: {Replicas.Ext.holds(~Requests.Ask.machine(), ~d, l, a) == True{}: Bool} -> Kp.Good(d, l, tr),
  e: {Shared.Maybe.when(Replicas.Tip, b, u => Some{tr}) == Some{x}: Maybe<&2, Replicas.Tip>}
) -> Kp.Good(d, l, x):
  match b:
    case True{}:
      %Shared.Maybe.some_inj(Replicas.Tip, tr, x, e): Kp.Good(d, l, _)
      ko(
        Shared.Bool.and_true_right(
          Replicas.Tips.same(Some{Replicas.Tip.hash(tr)}, after),
          Replicas.Ext.holds(~Requests.Ask.machine(), ~d, l, a)
        )(eb)
      )
    case False{}:
      Empty.absurd(Kp.Good(d, l, x), Shared.Maybe.none_ne_some(Replicas.Tip, x, e))

# a run that lands has a good tip
def Kp.landed(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  ma: Maybe<&2, Replicas.Run<Vend.L(d)>>,
  +after: Maybe<&2, Hashes.Hash>,
  +x: Replicas.Tip,
  ko: Kp.Out(d, l, ma),
  e: {Replicas.Line.landed(~Requests.Ask.machine(), ~d, l, ma, after) == Some{x}: Maybe<&2, Replicas.Tip>}
) -> Kp.Good(d, l, x):
  match ma:
    case None{}:
      Empty.absurd(Kp.Good(d, l, x), Shared.Maybe.none_ne_some(Replicas.Tip, x, e))
    case Some{Replicas.Run{lr, +tr, +a}}:
      Kp.landed.at(
        ~d,
        l,
        tr,
        a,
        after,
        x,
        Bool.and(Replicas.Tips.same(Some{Replicas.Tip.hash(tr)}, after), Replicas.Ext.holds(~Requests.Ask.machine(), ~d, l, a)),
        {==},
        ko,
        e
      )

# a step that moves a line has a good tip, once whether the step names the tip
# is known (b)
def Kp.moved.at(
  ~d: Vend.Led(),
  ~kern: Vend.Kern(d),
  ~rules: Kernel.Rules(d, kern),
  +l: Vend.L(d),
  +c: Ledgers.Line,
  +t: Replicas.Tip,
  +qs: List<&2, Hashes.Hash>,
  +after: Maybe<&2, Hashes.Hash>,
  +x: Replicas.Tip,
  b: Bool,
  e: {
    Shared.Maybe.when(
      Replicas.Tip,
      b,
      u => Replicas.Line.landed(~Requests.Ask.machine(), ~d, l, Replicas.Step.run(~Requests.Ask.machine(), ~d, ~kern, l, c, t, qs), after)
    )
      == Some{x}: Maybe<&2, Replicas.Tip>
  },
  gt: Kp.Good(d, l, t)
) -> Kp.Good(d, l, x):
  match b:
    case True{}:
      Kp.landed(
        ~d,
        l,
        Replicas.Step.run(~Requests.Ask.machine(), ~d, ~kern, l, c, t, qs),
        after,
        x,
        Kp.all(
          ~d,
          ~kern,
          ~rules,
          l,
          c,
          qs,
          Some{Replicas.Run{l, t, []}},
          Tuple{Tuple{[], Tuple{{==}, {==}}}, u => gt}
        ),
        e
      )
    case False{}:
      Empty.absurd(Kp.Good(d, l, x), Shared.Maybe.none_ne_some(Replicas.Tip, x, e))

# a step that moves a line has a good tip
def Kp.moved(
  ~d: Vend.Led(),
  ~kern: Vend.Kern(d),
  ~rules: Kernel.Rules(d, kern),
  +l: Vend.L(d),
  +c: Ledgers.Line,
  +t: Replicas.Tip,
  m: Maybe<&2, Ledgers.Step>,
  +x: Replicas.Tip,
  e: {Replicas.Line.moved(~Requests.Ask.machine(), ~d, ~kern, l, c, t, m) == Some{x}: Maybe<&2, Replicas.Tip>},
  gt: Kp.Good(d, l, t)
) -> Kp.Good(d, l, x):
  match m:
    case None{}:
      Empty.absurd(Kp.Good(d, l, x), Shared.Maybe.none_ne_some(Replicas.Tip, x, e))
    case Some{Ledgers.Step{before, qs, after}}:
      Kp.moved.at(~d, ~kern, ~rules, l, c, t, qs, after, x, Replicas.Tips.same(before, Some{Replicas.Tip.hash(t)}), e, gt)

# a step of a line has a good tip
def Kp.step(
  ~d: Vend.Led(),
  ~kern: Vend.Kern(d),
  ~rules: Kernel.Rules(d, kern),
  +l: Vend.L(d),
  +c: Ledgers.Line,
  +h: U32,
  +t: Replicas.Tip,
  +x: Replicas.Tip,
  e: {Replicas.Line.next(~Requests.Ask.machine(), ~d, ~kern, l, c, h, t) == Some{x}: Maybe<&2, Replicas.Tip>},
  gt: Kp.Good(d, l, t)
) -> Kp.Good(d, l, x):
  Kp.moved(
    ~d,
    ~kern,
    ~rules,
    l,
    c,
    t,
    Replicas.Height.decide(
      ~Requests.Ask.machine(),
      ~d,
      l,
      c,
      h,
      Replicas.Tip.voters(t),
      Ledgers.Kind.rounds(Replicas.Machine.Q(Requests.Ask.machine()), Replicas.Led.kind(Requests.Ask.machine(), d))(l)(c)(h)
    ),
    x,
    e,
    gt
  )

# the walk of a line has a good tip
def Kp.walk(
  ~d: Vend.Led(),
  ~kern: Vend.Kern(d),
  ~rules: Kernel.Rules(d, kern),
  f: Nat,
  +l: Vend.L(d),
  +c: Ledgers.Line,
  +h: U32,
  +t: Replicas.Tip,
  m: Maybe<&2, Replicas.Tip>,
  em: {Replicas.Line.next(~Requests.Ask.machine(), ~d, ~kern, l, c, h, t) == m: Maybe<&2, Replicas.Tip>},
  gt: Kp.Good(d, l, t)
) -> Kp.Good(d, l, Replicas.Line.walk(~Requests.Ask.machine(), ~d, ~kern, f, l, c, h, t, m)):
  match f m:
    case 0n y:
      gt
    case 1n+g None{}:
      gt
    case 1n+g Some{+t2}:
      Kp.walk(
        ~d,
        ~kern,
        ~rules,
        g,
        l,
        c,
        U32.inc(h),
        t2,
        Replicas.Line.next(~Requests.Ask.machine(), ~d, ~kern, l, c, U32.inc(h), t2),
        {==},
        Kp.step(~d, ~kern, ~rules, l, c, h, t, t2, em, gt)
      )

# that the tip in m, when there is one, is good
def Kp.GoodM(-d: Vend.Led(), l: Vend.L(d), m: Maybe<&2, Replicas.Tip>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{t}:
      Kp.Good(d, l, t)

# the empty tree is listed
def Kp.empty_whole(
  ~d: Vend.Led(),
  +l: Vend.L(d)
) -> {Maybe.is_some(&2, List<&2, Trees.Binding>, Vend.Tree.range(~d, l, None{}, [])) == True{}: Bool}:
  %Equal.sym(
    Maybe<&2, List<&2, Trees.Binding>>,
    Vend.Tree.range(~d, l, None{}, []),
    Some{[]},
    Store.Kept.empty_range(Vend.L(d), Replicas.Led.tree(Requests.Ask.machine(), d), Merges.Merge.laws_whole(d), l)
  ): {Maybe.is_some(&2, List<&2, Trees.Binding>, _) == True{}: Bool}
  {==}

# the empty tree names no first tip of a sub line
def Kp.starts_none(~d: Vend.Led(), +l: Vend.L(d)) -> Kp.StartsAt(d, l, None{}):
  +b => +ws => +tb => hg => hn =>
    Empty.absurd(
      Merges.Merge.And({Vend.Tree.kept(~d, l, Replicas.Tip.content(tb)) == True{}: Bool}, {Replicas.Tip.log(tb) == None{}: Maybe<&2, Hashes.Hash>}),
      Shared.Bool.false_ne_true(
        Store.Kept.of_range(
          ~d,
          l,
          None{},
          [],
          Store.Kept.empty_range(Vend.L(d), Replicas.Led.tree(Requests.Ask.machine(), d), Merges.Merge.laws_whole(d), l),
          Replicas.Log.start(b),
          ws,
          hg
        )
      )
    )

# a tip with no log is good, when its content is kept (the log of a tip is the
# empty log: its listing is known, and it names no first tip of a sub line)
def Kp.nolog.whole(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +x: Replicas.Tip,
  elog: {Replicas.Tip.log(x) == None{}: Maybe<&2, Hashes.Hash>}
) -> {Maybe.is_some(&2, List<&2, Trees.Binding>, Vend.Tree.range(~d, l, Replicas.Tip.log(x), [])) == True{}: Bool}:
  %Equal.sym(Maybe<&2, Hashes.Hash>, Replicas.Tip.log(x), None{}, elog): {
    Maybe.is_some(&2, List<&2, Trees.Binding>, Vend.Tree.range(~d, l, _, [])) == True{}: Bool
  }
  Kp.empty_whole(~d, l)

# a tip with no log is good, when its content is kept
def Kp.nolog.starts(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +x: Replicas.Tip,
  elog: {Replicas.Tip.log(x) == None{}: Maybe<&2, Hashes.Hash>}
) -> Kp.StartsAt(d, l, Replicas.Tip.log(x)):
  %Equal.sym(Maybe<&2, Hashes.Hash>, Replicas.Tip.log(x), None{}, elog): Kp.StartsAt(d, l, _)
  Kp.starts_none(~d, l)

# a tip with no log is good, when its content is kept
def Kp.nolog(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +x: Replicas.Tip,
  hk: {Vend.Tree.kept(~d, l, Replicas.Tip.content(x)) == True{}: Bool},
  +elog: {Replicas.Tip.log(x) == None{}: Maybe<&2, Hashes.Hash>}
) -> Kp.Good(d, l, x):
  (hk, (Kp.nolog.whole(~d, l, x, elog), Kp.nolog.starts(~d, l, x, elog)))

# the first tip of a root line is good
def Kp.root_first(~d: Vend.Led(), +l: Vend.L(d), a: Replicas.Arrival) -> Kp.GoodM(d, l, Replicas.Root.first(a)):
  match a:
    case Replicas.Arrival.Starts{+vs}:
      Kp.nolog(~d, l, Replicas.Tip{None{}, None{}, 0, Replicas.Voter.names(vs)}, Store.Kept.empty(~d, l), {==})
    case Replicas.Arrival.Waits{c}:
      Unit{}

# the first tip of the root line that the entry m starts is good
def Kp.root_start.of(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  m: Maybe<&2, Ledgers.Entry<Requests.Ask>>
) -> Kp.GoodM(d, l, Replicas.Root.start.of(~Requests.Ask.machine(), m)):
  match m:
    case Some{Ledgers.Entry.Ask{i, t, q}}:
      Kp.root_first(~d, l, Requests.Ask.arrival(q))
    case None{}:
      Unit{}
    case Some{Ledgers.Entry.Ballot{x}}:
      Unit{}
    case Some{Ledgers.Entry.Data{x}}:
      Unit{}
    case Some{Ledgers.Entry.Lie{x}}:
      Unit{}

# the first tip of a root line is good
def Kp.root_start(~d: Vend.Led(), +l: Vend.L(d), r: Hashes.Hash) -> Kp.GoodM(d, l, Replicas.Root.start(~Requests.Ask.machine(), ~d, l, r)):
  Kp.root_start.of(~d, l, Replicas.Led.get(~Requests.Ask.machine(), ~d, l, Ledgers.Name.Ask{r}))

# the tip that a log names for a sub line is good, once the tip that is read is
# known (mt)
def Kp.sub_named.at(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +b: String,
  +t: Replicas.Tip,
  +ws: List<&2, U32>,
  st: Kp.StartsAt(d, l, Replicas.Tip.log(t)),
  mt: Maybe<&2, Replicas.Tip>,
  hg: {Replicas.Tree.get(~Requests.Ask.machine(), ~d, l, Replicas.Tip.log(t), Replicas.Log.start(b)) == Some{ws}: Maybe<&2, List<&2, U32>>},
  en: {Replicas.Tip.named(~Requests.Ask.machine(), ~d, l, ws) == mt: Maybe<&2, Replicas.Tip>}
) -> Kp.GoodM(d, l, mt):
  match mt:
    case None{}:
      Unit{}
    case Some{+x}:
      +ak = st(b)(ws)(x)(hg)(en)
      Kp.nolog(
        ~d,
        l,
        x,
        Merges.Merge.And.left({Vend.Tree.kept(~d, l, Replicas.Tip.content(x)) == True{}: Bool}, {Replicas.Tip.log(x) == None{}: Maybe<&2, Hashes.Hash>}, ak),
        Merges.Merge.And.right({Vend.Tree.kept(~d, l, Replicas.Tip.content(x)) == True{}: Bool}, {Replicas.Tip.log(x) == None{}: Maybe<&2, Hashes.Hash>}, ak)
      )

# the tip that a log names for a sub line is good, once the tip that is read is
# known (mt)
def Kp.sub_named(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +b: String,
  +t: Replicas.Tip,
  +ws: List<&2, U32>,
  g: Kp.Good(d, l, t),
  mt: Maybe<&2, Replicas.Tip>,
  hg: {Replicas.Tree.get(~Requests.Ask.machine(), ~d, l, Replicas.Tip.log(t), Replicas.Log.start(b)) == Some{ws}: Maybe<&2, List<&2, U32>>},
  en: {Replicas.Tip.named(~Requests.Ask.machine(), ~d, l, ws) == mt: Maybe<&2, Replicas.Tip>}
) -> Kp.GoodM(d, l, mt):
  (+g1, r1) = g
  (+w1, st) = r1
  Kp.sub_named.at(~d, l, b, t, ws, st, mt, hg, en)

# the tip that a log names for a sub line is good, once the read of it is known (mw)
def Kp.sub_get(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +b: String,
  +t: Replicas.Tip,
  g: Kp.Good(d, l, t),
  mw: Maybe<&2, List<&2, U32>>,
  ew: {Replicas.Tip.get(~Requests.Ask.machine(), ~d, l, t, Replicas.Log.start(b)) == mw: Maybe<&2, List<&2, U32>>}
) -> Kp.GoodM(
  d,
  l,
  Maybe.bind(&2, List<&2, U32>, Replicas.Tip, mw, ws => Replicas.Tip.named(~Requests.Ask.machine(), ~d, l, ws))
):
  match mw:
    case None{}:
      Unit{}
    case Some{+ws}:
      Kp.sub_named(~d, l, b, t, ws, g, Replicas.Tip.named(~Requests.Ask.machine(), ~d, l, ws), ew, {==})

# the first tip of a sub line is good, when the tip of its root line is
def Kp.sub_start(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +b: String,
  m: Maybe<&2, Replicas.Tip>,
  gm: Kp.GoodM(d, l, m)
) -> Kp.GoodM(d, l, Replicas.Sub.start(~Requests.Ask.machine(), ~d, l, b, m)):
  match m:
    case None{}:
      Unit{}
    case Some{+t}:
      Kp.sub_get(~d, l, b, t, gm, Replicas.Tip.get(~Requests.Ask.machine(), ~d, l, t, Replicas.Log.start(b)), {==})

# the newest tip of a line is good, when its first tip is
def Kp.head.of(
  ~d: Vend.Led(),
  ~kern: Vend.Kern(d),
  ~rules: Kernel.Rules(d, kern),
  +l: Vend.L(d),
  +c: Ledgers.Line,
  m: Maybe<&2, Replicas.Tip>,
  gm: Kp.GoodM(d, l, m)
) -> Kp.GoodM(d, l, Replicas.Line.head.of(~Requests.Ask.machine(), ~d, ~kern, l, c, m)):
  match m:
    case None{}:
      Unit{}
    case Some{+t}:
      Kp.walk(
        ~d,
        ~kern,
        ~rules,
        1n+Ledgers.Kind.heights(Replicas.Machine.Q(Requests.Ask.machine()), Replicas.Led.kind(Requests.Ask.machine(), d))(l)(c),
        l,
        c,
        0,
        t,
        Replicas.Line.next(~Requests.Ask.machine(), ~d, ~kern, l, c, 0, t),
        {==},
        gm
      )

# the newest tip of a root line is good
def Kp.root_head(
  ~d: Vend.Led(),
  ~kern: Vend.Kern(d),
  ~rules: Kernel.Rules(d, kern),
  +l: Vend.L(d),
  +r: Hashes.Hash
) -> Kp.GoodM(d, l, Replicas.Root.head(~Requests.Ask.machine(), ~d, ~kern, l, r)):
  Kp.head.of(~d, ~kern, ~rules, l, Ledgers.Line{r, None{}}, Replicas.Root.start(~Requests.Ask.machine(), ~d, l, r), Kp.root_start(~d, l, r))

# the first tip of a line is good
def Kp.start(
  ~d: Vend.Led(),
  ~kern: Vend.Kern(d),
  ~rules: Kernel.Rules(d, kern),
  +l: Vend.L(d),
  c: Ledgers.Line
) -> Kp.GoodM(d, l, Replicas.Line.start(~Requests.Ask.machine(), ~d, ~kern, l, c)):
  match c:
    case Ledgers.Line{+r, None{}}:
      Kp.root_start(~d, l, r)
    case Ledgers.Line{+r, Some{+b}}:
      Kp.sub_start(
        ~d,
        l,
        b,
        Replicas.Root.head(~Requests.Ask.machine(), ~d, ~kern, l, r),
        Kp.root_head(~d, ~kern, ~rules, l, r)
      )

# the newest tip of a line is good
def Kp.head(
  ~d: Vend.Led(),
  ~kern: Vend.Kern(d),
  ~rules: Kernel.Rules(d, kern),
  +l: Vend.L(d),
  +c: Ledgers.Line
) -> Kp.GoodM(d, l, Replicas.Line.head(~Requests.Ask.machine(), ~d, ~kern, l, c)):
  Kp.head.of(~d, ~kern, ~rules, l, c, Replicas.Line.start(~Requests.Ask.machine(), ~d, ~kern, l, c), Kp.start(~d, ~kern, ~rules, l, c))

# a tip that a line reads, once the line reads one (e), is good
def Kp.some_of(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  mt: Maybe<&2, Replicas.Tip>,
  +t: Replicas.Tip,
  gm: Kp.GoodM(d, l, mt),
  e: {mt == Some{t}: Maybe<&2, Replicas.Tip>}
) -> Kp.Good(d, l, t):
  match mt:
    case None{}:
      Empty.absurd(Kp.Good(d, l, t), Shared.Maybe.none_ne_some(Replicas.Tip, t, e))
    case Some{+x}:
      %Shared.Maybe.some_inj(Replicas.Tip, x, t, e): Kp.Good(d, l, _)
      gm

# the content of the newest tip of a line is kept
def Kp.head_kept(
  ~d: Vend.Led(),
  ~kern: Vend.Kern(d),
  ~rules: Kernel.Rules(d, kern),
  +l: Vend.L(d),
  +c: Ledgers.Line,
  +t: Replicas.Tip,
  e: {Replicas.Line.head(~Requests.Ask.machine(), ~d, ~kern, l, c) == Some{t}: Maybe<&2, Replicas.Tip>}
) -> {Vend.Tree.kept(~d, l, Replicas.Tip.content(t)) == True{}: Bool}:
  Kp.kept_of(
    ~d,
    l,
    t,
    Kp.some_of(~d, l, Replicas.Line.head(~Requests.Ask.machine(), ~d, ~kern, l, c), t, Kp.head(~d, ~kern, ~rules, l, c), e)
  )

def Node.head_kept(d, kern, rules, l, c, t):
  e => Kp.head_kept(~d, ~kern, ~rules, l, c, t, e)


def Node.answer_follows(d, kern, rules, i, time, q):
  Node.answer_follows.of(
    ~d,
    ~kern,
    i,
    time,
    q,
    c => key => Replicas.Line.get_grows(Requests.Ask.machine(), d, kern, c, key),
    l => c => t => e => Node.head_kept(d, kern, rules, l, c, t)(e)
  )

# Stability, proven
# -----------------
# The helpers of Ask.act_stable: each read of a rule that tells, tells the
# same in a ledger that grows.

# the law that a listing stays, of a tree t
def Stable.range_of(
  -S: Data,
  -fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  -grows: S -> S -> Bool,
  t: Trees.Tree(S, fetch, grows)
) -> Trees.Laws.RangeFinal(S, grows, Trees.Tree.ops(S, fetch, grows, t)):
  match t:
    case Tuple{o, Tuple{f, Tuple{p, Tuple{w, Tuple{c, Tuple{r, Tuple{df, Tuple{wh, Tuple{kp, Tuple{rf, dff}}}}}}}}}}:
      rf

# the law that a difference stays, of a tree t
def Stable.diff_of(
  -S: Data,
  -fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  -grows: S -> S -> Bool,
  t: Trees.Tree(S, fetch, grows)
) -> Trees.Laws.DiffFinal(S, grows, Trees.Tree.ops(S, fetch, grows, t)):
  match t:
    case Tuple{o, Tuple{f, Tuple{p, Tuple{w, Tuple{c, Tuple{r, Tuple{df, Tuple{wh, Tuple{kp, Tuple{rf, dff}}}}}}}}}}:
      dff

# the law that a listing stays, of the tree of the ledger d
def Stable.range(d: Vend.Led()) -> Trees.Laws.RangeFinal(
  Vend.L(d),
  a => b => Ledgers.Kind.grows(
    ~Replicas.Machine.Q(Requests.Ask.machine()),
    ~Replicas.Machine.code(Requests.Ask.machine()),
    ~Replicas.Led.kind(Requests.Ask.machine(), d),
    a,
    b
  ),
  Replicas.Led.tree(Requests.Ask.machine(), d)
):
  match d:
    case Tuple{x, t}:
      Stable.range_of(
        Ledgers.Kind.L(
          Replicas.Machine.Q(Requests.Ask.machine()),
          Ledgers.Ledger.kind(Replicas.Machine.Q(Requests.Ask.machine()), Replicas.Machine.code(Requests.Ask.machine()), x)
        ),
        Ledgers.Kind.data(
          Replicas.Machine.Q(Requests.Ask.machine()),
          Ledgers.Ledger.kind(Replicas.Machine.Q(Requests.Ask.machine()), Replicas.Machine.code(Requests.Ask.machine()), x)
        ),
        a => b => Ledgers.Kind.grows(
          ~Replicas.Machine.Q(Requests.Ask.machine()),
          ~Replicas.Machine.code(Requests.Ask.machine()),
          ~Ledgers.Ledger.kind(Replicas.Machine.Q(Requests.Ask.machine()), Replicas.Machine.code(Requests.Ask.machine()), x),
          a,
          b
        ),
        t
      )

# the law that a difference stays, of the tree of the ledger d
def Stable.diff(d: Vend.Led()) -> Trees.Laws.DiffFinal(
  Vend.L(d),
  a => b => Ledgers.Kind.grows(
    ~Replicas.Machine.Q(Requests.Ask.machine()),
    ~Replicas.Machine.code(Requests.Ask.machine()),
    ~Replicas.Led.kind(Requests.Ask.machine(), d),
    a,
    b
  ),
  Replicas.Led.tree(Requests.Ask.machine(), d)
):
  match d:
    case Tuple{x, t}:
      Stable.diff_of(
        Ledgers.Kind.L(
          Replicas.Machine.Q(Requests.Ask.machine()),
          Ledgers.Ledger.kind(Replicas.Machine.Q(Requests.Ask.machine()), Replicas.Machine.code(Requests.Ask.machine()), x)
        ),
        Ledgers.Kind.data(
          Replicas.Machine.Q(Requests.Ask.machine()),
          Ledgers.Ledger.kind(Replicas.Machine.Q(Requests.Ask.machine()), Replicas.Machine.code(Requests.Ask.machine()), x)
        ),
        a => b => Ledgers.Kind.grows(
          ~Replicas.Machine.Q(Requests.Ask.machine()),
          ~Replicas.Machine.code(Requests.Ask.machine()),
          ~Ledgers.Ledger.kind(Replicas.Machine.Q(Requests.Ask.machine()), Replicas.Machine.code(Requests.Ask.machine()), x),
          a,
          b
        ),
        t
      )

# a listing stays as the ledger grows
def Stable.range_grows(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +p: List<&2, U32>,
  +bs: List<&2, Trees.Binding>,
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b)
) -> {Vend.Tree.range(~d, a, h, p) == Some{bs}: Maybe<&2, List<&2, Trees.Binding>>}
  -> {Vend.Tree.range(~d, b, h, p) == Some{bs}: Maybe<&2, List<&2, Trees.Binding>>}:
  e => Stable.range(d)(a)(b)(h)(p)(bs)(e)(g)

# a difference stays as the ledger grows
def Stable.diff_grows(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +h1: Maybe<&2, Hashes.Hash>,
  +h2: Maybe<&2, Hashes.Hash>,
  +ks: List<&2, List<&2, U32>>,
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b)
) -> {Replicas.Tree.diff(~Requests.Ask.machine(), ~d, a, h1, h2) == Some{ks}: Maybe<&2, List<&2, List<&2, U32>>>}
  -> {Replicas.Tree.diff(~Requests.Ask.machine(), ~d, b, h1, h2) == Some{ks}: Maybe<&2, List<&2, List<&2, U32>>>}:
  e => Stable.diff(d)(a)(b)(h1)(h2)(ks)(e)(g)

# a map that gives y gives y of a read that gives what the first gave
def Stable.map_kept(
  -A: Data,
  -B: Data,
  -f: A -> B,
  m: Maybe<&2, A>,
  -m2: Maybe<&2, A>,
  -y: B,
  hm: @v: A -> {m == Some{v}: Maybe<&2, A>} -> {m2 == Some{v}: Maybe<&2, A>}
) -> {Maybe.map(&2, A, B, f, m) == Some{y}: Maybe<&2, B>} -> {Maybe.map(&2, A, B, f, m2) == Some{y}: Maybe<&2, B>}:
  match m:
    case None{}:
      e => Empty.absurd({Maybe.map(&2, A, B, f, m2) == Some{y}: Maybe<&2, B>}, Shared.Maybe.none_ne_some(B, y, e))
    case Some{+v}:
      e =>
        %Equal.sym(Maybe<&2, A>, m2, Some{v}, hm(v)({==})): {Maybe.map(&2, A, B, f, _) == Some{y}: Maybe<&2, B>}
        e

# a choice by the test c gives y with each choice kept
def Stable.when_same(
  -R: Type,
  c: Bool,
  -k: Unit -> R,
  -e: Unit -> R,
  -k2: Unit -> R,
  -e2: Unit -> R,
  -y: R,
  hk: {c == True{}: Bool} -> {k(Unit{}) == y: R} -> {k2(Unit{}) == y: R},
  he: {c == False{}: Bool} -> {e(Unit{}) == y: R} -> {e2(Unit{}) == y: R}
) -> {Shared.Bool.when(R, c, k, e) == y: R} -> {Shared.Bool.when(R, c, k2, e2) == y: R}:
  match c:
    case True{}:
      h => hk({==})(h)
    case False{}:
      h => he({==})(h)

# a choice by a test that holds, and holds after, gives y when its choice is
# kept; its other choice gives no y
def Stable.when_test(
  -R: Type,
  c: Bool,
  -c2: Bool,
  -k: Unit -> R,
  -e: Unit -> R,
  -k2: Unit -> R,
  -e2: Unit -> R,
  -y: R,
  hc: {c == True{}: Bool} -> {c2 == True{}: Bool},
  hk: {k(Unit{}) == y: R} -> {k2(Unit{}) == y: R},
  he: {e(Unit{}) == y: R} -> Empty
) -> {Shared.Bool.when(R, c, k, e) == y: R} -> {Shared.Bool.when(R, c2, k2, e2) == y: R}:
  match c:
    case True{}:
      h =>
        %Equal.sym(Bool, c2, True{}, hc({==})): {Shared.Bool.when(R, _, k2, e2) == y: R}
        hk(h)
    case False{}:
      h => Empty.absurd({Shared.Bool.when(R, c2, k2, e2) == y: R}, he(h))

# Maybe.when by a test that holds, and holds after
def Stable.mwhen_test(
  -B: Data,
  c: Bool,
  -c2: Bool,
  -k: Unit -> Maybe<&2, B>,
  -k2: Unit -> Maybe<&2, B>,
  -y: B,
  hc: {c == True{}: Bool} -> {c2 == True{}: Bool},
  hk: {k(Unit{}) == Some{y}: Maybe<&2, B>} -> {k2(Unit{}) == Some{y}: Maybe<&2, B>}
) -> {Shared.Maybe.when(B, c, k) == Some{y}: Maybe<&2, B>} -> {Shared.Maybe.when(B, c2, k2) == Some{y}: Maybe<&2, B>}:
  match c:
    case True{}:
      h =>
        %Equal.sym(Bool, c2, True{}, hc({==})): {Shared.Maybe.when(B, _, k2) == Some{y}: Maybe<&2, B>}
        hk(h)
    case False{}:
      h => Empty.absurd({Shared.Maybe.when(B, c2, k2) == Some{y}: Maybe<&2, B>}, Shared.Maybe.none_ne_some(B, y, h))

# a value read whole from words that stay stays
def Stable.whole_of_kept(
  ~A: Data,
  ~enc: A -> List<&2, U32> -> List<&2, U32>,
  ~dec: List<&2, U32> -> Maybe<&2, Codes.Read<A>>,
  m: Maybe<&2, List<&2, U32>>,
  -m2: Maybe<&2, List<&2, U32>>,
  -y: A,
  hm: @v: List<&2, U32> -> {m == Some{v}: Maybe<&2, List<&2, U32>>} -> {m2 == Some{v}: Maybe<&2, List<&2, U32>>}
) -> {Codes.Code.whole.of(~A, ~enc, ~dec, m) == Some{y}: Maybe<&2, A>}
  -> {Codes.Code.whole.of(~A, ~enc, ~dec, m2) == Some{y}: Maybe<&2, A>}:
  match m:
    case None{}:
      e => Empty.absurd({Codes.Code.whole.of(~A, ~enc, ~dec, m2) == Some{y}: Maybe<&2, A>}, Shared.Maybe.none_ne_some(A, y, e))
    case Some{+v}:
      e =>
        %Equal.sym(Maybe<&2, List<&2, U32>>, m2, Some{v}, hm(v)({==})): {Codes.Code.whole.of(~A, ~enc, ~dec, _) == Some{y}: Maybe<&2, A>}
        e

# a known read of a value whose words stay stays
def Stable.known_kept(
  ~A: Data,
  ~enc: A -> List<&2, U32> -> List<&2, U32>,
  ~dec: List<&2, U32> -> Maybe<&2, Codes.Read<A>>,
  m: Maybe<&2, Maybe<&2, List<&2, U32>>>,
  -m2: Maybe<&2, Maybe<&2, List<&2, U32>>>,
  -y: Maybe<&2, A>,
  hm: @v: Maybe<&2, List<&2, U32>> -> {m == Some{v}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
    -> {m2 == Some{v}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
) -> {Replicas.Tip.known(~A, ~enc, ~dec, m) == Some{y}: Maybe<&2, Maybe<&2, A>>}
  -> {Replicas.Tip.known(~A, ~enc, ~dec, m2) == Some{y}: Maybe<&2, Maybe<&2, A>>}:
  match m:
    case None{}:
      e => Empty.absurd(
        {Replicas.Tip.known(~A, ~enc, ~dec, m2) == Some{y}: Maybe<&2, Maybe<&2, A>>},
        Shared.Maybe.none_ne_some(Maybe<&2, A>, y, e)
      )
    case Some{+v}:
      e =>
        %Equal.sym(Maybe<&2, Maybe<&2, List<&2, U32>>>, m2, Some{v}, hm(v)({==})): {
          Replicas.Tip.known(~A, ~enc, ~dec, _) == Some{y}: Maybe<&2, Maybe<&2, A>>
        }
        e

# a read that tells stays telling
def Stable.is_some_kept(
  -A: Data,
  m: Maybe<&2, A>,
  -m2: Maybe<&2, A>,
  hm: @v: A -> {m == Some{v}: Maybe<&2, A>} -> {m2 == Some{v}: Maybe<&2, A>}
) -> {Maybe.is_some(&2, A, m) == True{}: Bool} -> {Maybe.is_some(&2, A, m2) == True{}: Bool}:
  match m:
    case None{}:
      e => Empty.absurd({Maybe.is_some(&2, A, m2) == True{}: Bool}, Shared.Bool.false_ne_true(e))
    case Some{+v}:
      e =>
        %Equal.sym(Maybe<&2, A>, m2, Some{v}, hm(v)({==})): {Maybe.is_some(&2, A, _) == True{}: Bool}
        {==}

# the act that takes a tree that a write gives stays when the write does
def Stable.act_put_kept(
  vs: Maybe<&2, List<&2, String>>,
  ns: List<&2, List<&2, U32>>,
  p: Maybe<&2, Trees.Edit>,
  -p2: Maybe<&2, Trees.Edit>,
  -x: Replicas.Act,
  hm: @v: Trees.Edit -> {p == Some{v}: Maybe<&2, Trees.Edit>} -> {p2 == Some{v}: Maybe<&2, Trees.Edit>}
) -> {Vend.Act.put(vs, ns, p) == Some{x}: Maybe<&2, Replicas.Act>} -> {Vend.Act.put(vs, ns, p2) == Some{x}: Maybe<&2, Replicas.Act>}:
  match p:
    case None{}:
      e => Empty.absurd({Vend.Act.put(vs, ns, p2) == Some{x}: Maybe<&2, Replicas.Act>}, Shared.Maybe.none_ne_some(Replicas.Act, x, e))
    case Some{+v}:
      e =>
        %Equal.sym(Maybe<&2, Trees.Edit>, p2, Some{v}, hm(v)({==})): {Vend.Act.put(vs, ns, _) == Some{x}: Maybe<&2, Replicas.Act>}
        e

# what a tree reads under a key stays as the ledger grows
def Stable.get(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b)
) -> {Replicas.Tree.get(~Requests.Ask.machine(), ~d, a, h, k) == Some{v}: Maybe<&2, List<&2, U32>>}
  -> {Replicas.Tree.get(~Requests.Ask.machine(), ~d, b, h, k) == Some{v}: Maybe<&2, List<&2, U32>>}:
  e => Reads.Affects.known_value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, b, h, k), Some{v})(
    Replicas.Hist.find(~Requests.Ask.machine(), ~d, a, b, h, k, Some{v}, g)(
      Reads.Affects.value_known(Replicas.Tree.look(~Requests.Ask.machine(), ~d, a, h, k), v)(e)
    )
  )

# the resource that a tree holds under a name stays as the ledger grows
def Stable.res_find(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +n: Resources.Name,
  +r: Maybe<&2, Requests.Res>,
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b)
) -> {Vend.Res.find(~d, a, h, n) == Some{r}: Maybe<&2, Maybe<&2, Requests.Res>>}
  -> {Vend.Res.find(~d, b, h, n) == Some{r}: Maybe<&2, Maybe<&2, Requests.Res>>}:
  Shared.Maybe.bind_kept(
    Maybe<&2, List<&2, U32>>,
    Maybe<&2, Requests.Res>,
    Replicas.Tree.find(~Requests.Ask.machine(), ~d, a, h, Vend.Key.res(n)),
    Replicas.Tree.find(~Requests.Ask.machine(), ~d, b, h, Vend.Key.res(n)),
    m => Some{Vend.Res.found(m)},
    m => Some{Vend.Res.found(m)},
    r,
    m0 => e => Replicas.Hist.find(~Requests.Ask.machine(), ~d, a, b, h, Vend.Key.res(n), m0, g)(e),
    m0 => e => e
  )

# what the log of a tip holds under a key stays as the ledger grows
def Stable.tip_get(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +t: Replicas.Tip,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b)
) -> {Replicas.Tip.get(~Requests.Ask.machine(), ~d, a, t, k) == Some{v}: Maybe<&2, List<&2, U32>>}
  -> {Replicas.Tip.get(~Requests.Ask.machine(), ~d, b, t, k) == Some{v}: Maybe<&2, List<&2, U32>>}:
  Stable.get(~d, a, b, Replicas.Tip.log(t), k, v, g)

# the request that a line took as a number stays as the ledger grows
def Stable.taken(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +t: Replicas.Tip,
  +n: U32,
  +x: Replicas.Taken,
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b)
) -> {Replicas.Tip.taken(~Requests.Ask.machine(), ~d, a, t, n) == Some{x}: Maybe<&2, Replicas.Taken>}
  -> {Replicas.Tip.taken(~Requests.Ask.machine(), ~d, b, t, n) == Some{x}: Maybe<&2, Replicas.Taken>}:
  Stable.whole_of_kept(
    ~Replicas.Taken,
    ~Replicas.Taken.code,
    ~Replicas.Taken.code.read,
    Replicas.Tip.get(~Requests.Ask.machine(), ~d, a, t, Replicas.Log.taken(n)),
    Replicas.Tip.get(~Requests.Ask.machine(), ~d, b, t, Replicas.Log.taken(n)),
    x,
    +ws => e => Stable.tip_get(~d, a, b, t, Replicas.Log.taken(n), ws, g)(e)
  )

# the outcome of a request stays as the ledger grows
def Stable.out(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +t: Replicas.Tip,
  +i: Ledgers.Id,
  +o: Replicas.Out,
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b)
) -> {Replicas.Tip.out(~Requests.Ask.machine(), ~d, a, t, i) == Some{o}: Maybe<&2, Replicas.Out>}
  -> {Replicas.Tip.out(~Requests.Ask.machine(), ~d, b, t, i) == Some{o}: Maybe<&2, Replicas.Out>}:
  Stable.whole_of_kept(
    ~Replicas.Out,
    ~Replicas.Out.code,
    ~Replicas.Out.code.read,
    Replicas.Tip.get(~Requests.Ask.machine(), ~d, a, t, Replicas.Log.out(i)),
    Replicas.Tip.get(~Requests.Ask.machine(), ~d, b, t, Replicas.Log.out(i)),
    o,
    +ws => e => Stable.tip_get(~d, a, b, t, Replicas.Log.out(i), ws, g)(e)
  )

# the request taken is i, and stays so
def Stable.is_of(
  m: Maybe<&2, Replicas.Taken>,
  -m2: Maybe<&2, Replicas.Taken>,
  +i: Ledgers.Id,
  hm: @v: Replicas.Taken -> {m == Some{v}: Maybe<&2, Replicas.Taken>} -> {m2 == Some{v}: Maybe<&2, Replicas.Taken>}
) -> {Replicas.Taken.is_of(m, i) == True{}: Bool} -> {Replicas.Taken.is_of(m2, i) == True{}: Bool}:
  match m:
    case None{}:
      e => Empty.absurd({Replicas.Taken.is_of(m2, i) == True{}: Bool}, Shared.Bool.false_ne_true(e))
    case Some{+v}:
      e =>
        %Equal.sym(Maybe<&2, Replicas.Taken>, m2, Some{v}, hm(v)({==})): {Replicas.Taken.is_of(_, i) == True{}: Bool}
        e

# the number that an outcome names stays as the ledger grows
def Stable.out_number(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +t: Replicas.Tip,
  +i: Ledgers.Id,
  o: Replicas.Out,
  +m: U32,
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b)
) -> {Replicas.Out.number(~Requests.Ask.machine(), ~d, a, t, i, o) == Some{m}: Maybe<&2, U32>}
  -> {Replicas.Out.number(~Requests.Ask.machine(), ~d, b, t, i, o) == Some{m}: Maybe<&2, U32>}:
  match o:
    case Replicas.Out.Stale{oa}:
      e => Empty.absurd(
        {Replicas.Out.number(~Requests.Ask.machine(), ~d, b, t, i, Replicas.Out.Stale{oa}) == Some{m}: Maybe<&2, U32>},
        Shared.Maybe.none_ne_some(U32, m, e)
      )
    case Replicas.Out.Taken{oa, +m1}:
      +p = U32.is_lt(m1, Replicas.Tip.count(t))
      +qa = Replicas.Taken.is_of(Replicas.Tip.taken(~Requests.Ask.machine(), ~d, a, t, m1), i)
      +qb = Replicas.Taken.is_of(Replicas.Tip.taken(~Requests.Ask.machine(), ~d, b, t, m1), i)
      Stable.mwhen_test(
        U32,
        Bool.and(p, qa),
        Bool.and(p, qb),
        u => Some{m1},
        u => Some{m1},
        m,
        +h => Shared.Bool.and_both(p, qb)(Shared.Bool.and_true_left(p, qa)(h))(
          Stable.is_of(
            Replicas.Tip.taken(~Requests.Ask.machine(), ~d, a, t, m1),
            Replicas.Tip.taken(~Requests.Ask.machine(), ~d, b, t, m1),
            i,
            +v => ev => Stable.taken(~d, a, b, t, m1, v, g)(ev)
          )(Shared.Bool.and_true_right(p, qa)(h))
        ),
        e => e
      )

# the number of a request stays as the ledger grows
def Stable.number(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +t: Replicas.Tip,
  +i: Ledgers.Id,
  +m: U32,
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b)
) -> {Replicas.Tip.number(~Requests.Ask.machine(), ~d, a, t, i) == Some{m}: Maybe<&2, U32>}
  -> {Replicas.Tip.number(~Requests.Ask.machine(), ~d, b, t, i) == Some{m}: Maybe<&2, U32>}:
  Shared.Maybe.bind_kept(
    Replicas.Out,
    U32,
    Replicas.Tip.out(~Requests.Ask.machine(), ~d, a, t, i),
    Replicas.Tip.out(~Requests.Ask.machine(), ~d, b, t, i),
    o => Replicas.Out.number(~Requests.Ask.machine(), ~d, a, t, i, o),
    o => Replicas.Out.number(~Requests.Ask.machine(), ~d, b, t, i, o),
    m,
    +o => e => Stable.out(~d, a, b, t, i, o, g)(e),
    +o => e => Stable.out_number(~d, a, b, t, i, o, m, g)(e)
  )

# the tree of a version stays as the ledger grows
def Stable.version(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +t: Replicas.Tip,
  +i: Ledgers.Id,
  +h: Maybe<&2, Hashes.Hash>,
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b)
) -> {Replicas.Tip.version(~Requests.Ask.machine(), ~d, a, t, i) == Some{h}: Maybe<&2, Maybe<&2, Hashes.Hash>>}
  -> {Replicas.Tip.version(~Requests.Ask.machine(), ~d, b, t, i) == Some{h}: Maybe<&2, Maybe<&2, Hashes.Hash>>}:
  Shared.Maybe.bind_kept(
    U32,
    Maybe<&2, Hashes.Hash>,
    Replicas.Tip.number(~Requests.Ask.machine(), ~d, a, t, i),
    Replicas.Tip.number(~Requests.Ask.machine(), ~d, b, t, i),
    m => Maybe.bind(&2, Replicas.Taken, Maybe<&2, Hashes.Hash>, Replicas.Tip.taken(~Requests.Ask.machine(), ~d, a, t, m), x => Some{Replicas.Taken.root(x)}),
    m => Maybe.bind(&2, Replicas.Taken, Maybe<&2, Hashes.Hash>, Replicas.Tip.taken(~Requests.Ask.machine(), ~d, b, t, m), x => Some{Replicas.Taken.root(x)}),
    h,
    +m => e => Stable.number(~d, a, b, t, i, m, g)(e),
    +m => e => Shared.Maybe.bind_kept(
      Replicas.Taken,
      Maybe<&2, Hashes.Hash>,
      Replicas.Tip.taken(~Requests.Ask.machine(), ~d, a, t, m),
      Replicas.Tip.taken(~Requests.Ask.machine(), ~d, b, t, m),
      x => Some{Replicas.Taken.root(x)},
      x => Some{Replicas.Taken.root(x)},
      h,
      +x => e2 => Stable.taken(~d, a, b, t, m, x, g)(e2),
      x => e2 => e2
    )(e)
  )

# the bytes of a rope stay as the ledger grows
def Stable.bytes(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +r: Ropes.Root,
  +x: Texts.Bytes(),
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b)
) -> {Vend.Root.bytes(~d, a, r) == Some{x}: Maybe<&2, Texts.Bytes()>} -> {Vend.Root.bytes(~d, b, r) == Some{x}: Maybe<&2, Texts.Bytes()>}:
  Shared.Maybe.bind_kept(
    List<&2, U32>,
    List<&2, U32>,
    Ropes.Rope.read(~Vend.L(d), ~Replicas.Led.fetch(~Requests.Ask.machine(), ~d), a, r),
    Ropes.Rope.read(~Vend.L(d), ~Replicas.Led.fetch(~Requests.Ask.machine(), ~d), b, r),
    ws => Some{Packs.Pack.read(ws, Packs.At.Length{0n})},
    ws => Some{Packs.Pack.read(ws, Packs.At.Length{0n})},
    x,
    +ws => e => Ropes.Rope.read_grows(
      ~Vend.L(d),
      ~Replicas.Led.fetch(~Requests.Ask.machine(), ~d),
      ~(a2 => b2 => Ledgers.Kind.grows(
        ~Replicas.Machine.Q(Requests.Ask.machine()),
        ~Replicas.Machine.code(Requests.Ask.machine()),
        ~Replicas.Led.kind(Requests.Ask.machine(), d),
        a2,
        b2
      )),
      ~(a2 => b2 => h2 => w2 => g2 => e2 => Replicas.Hist.fetch(~Requests.Ask.machine(), ~d, a2, b2, h2, w2, g2)(e2)),
      a,
      b,
      r,
      ws
    )(g)(e),
    ws => e => e
  )

# a format that the ledger holds stays as it grows
def Stable.format_at(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +h: Hashes.Hash,
  +f: Formats.Format,
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b)
) -> {Vend.Format.at(~d, a, h) == Some{f}: Maybe<&2, Formats.Format>} -> {Vend.Format.at(~d, b, h) == Some{f}: Maybe<&2, Formats.Format>}:
  Stable.whole_of_kept(
    ~Formats.Format,
    ~Formats.Format.code,
    ~Formats.Format.code.read,
    Replicas.Led.fetch(~Requests.Ask.machine(), ~d)(a)(h),
    Replicas.Led.fetch(~Requests.Ask.machine(), ~d)(b)(h),
    f,
    +ws => e => Replicas.Hist.fetch(~Requests.Ask.machine(), ~d, a, b, h, ws, g)(e)
  )

# a ledger that holds a resource holds it as it grows
def Stable.res_kept(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  m: Maybe<&2, Requests.Res>,
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b)
) -> {Vend.Res.kept(~d, a, m) == True{}: Bool} -> {Vend.Res.kept(~d, b, m) == True{}: Bool}:
  match m:
    case None{}:
      e => e
    case Some{+x}:
      +e => Shared.List.all.if_both(
        Maybe.is_some(&2, Formats.Format, Vend.Res.format(~d, b, x)),
        u => Maybe.is_some(&2, Texts.Bytes(), Vend.Root.bytes(~d, b, Vend.Res.root(x)))
      )(
        Stable.is_some_kept(
          Formats.Format,
          Vend.Res.format(~d, a, x),
          Vend.Res.format(~d, b, x),
          +f => ef => Stable.format_at(~d, a, b, Vend.Res.format.hash(x), f, g)(ef)
        )(
          Shared.List.all.if_hit(
            Maybe.is_some(&2, Formats.Format, Vend.Res.format(~d, a, x)),
            u => Maybe.is_some(&2, Texts.Bytes(), Vend.Root.bytes(~d, a, Vend.Res.root(x)))
          )(e)
        )
      )(
        Stable.is_some_kept(
          Texts.Bytes(),
          Vend.Root.bytes(~d, a, Vend.Res.root(x)),
          Vend.Root.bytes(~d, b, Vend.Res.root(x)),
          +y => ey => Stable.bytes(~d, a, b, Vend.Res.root(x), y, g)(ey)
        )(
          Shared.List.all.if_rest(
            Maybe.is_some(&2, Formats.Format, Vend.Res.format(~d, a, x)),
            u => Maybe.is_some(&2, Texts.Bytes(), Vend.Root.bytes(~d, a, Vend.Res.root(x)))
          )(e)
        )
      )

# a ledger that holds each node of some words holds them as it grows
def Stable.holds(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  ns: List<&2, List<&2, U32>>,
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b)
) -> {
  Depots.Depot.holds(~Vend.L(d), ~(s => x => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, x)), a, ns) == True{}: Bool
} -> {Depots.Depot.holds(~Vend.L(d), ~(s => x => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, x)), b, ns) == True{}: Bool}:
  match ns:
    case Nil{}:
      e => e
    case Con{+ws, +r}:
      +e => Shared.List.all.if_both(
        Depots.Depot.has(~Vend.L(d), ~(s => x => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, x)), b, ws),
        u => Depots.Depot.holds(~Vend.L(d), ~(s => x => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, x)), b, r)
      )(
        Replicas.Hist.has.of(~Requests.Ask.machine(), ~d, b, ws)(
          Replicas.Hist.fetch(~Requests.Ask.machine(), ~d, a, b, Hashes.Sha.hash(ws), ws, g)(
            Replicas.Hist.has(~Requests.Ask.machine(), ~d, a, ws)(
              Shared.List.all.if_hit(
                Depots.Depot.has(~Vend.L(d), ~(s => x => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, x)), a, ws),
                u => Depots.Depot.holds(~Vend.L(d), ~(s => x => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, x)), a, r)
              )(e)
            )
          )
        )
      )(
        Stable.holds(~d, a, b, r, g)(
          Shared.List.all.if_rest(
            Depots.Depot.has(~Vend.L(d), ~(s => x => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, x)), a, ws),
            u => Depots.Depot.holds(~Vend.L(d), ~(s => x => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, x)), a, r)
          )(e)
        )
      )

# a ledger that holds the resource of a binding holds it as it grows
def Stable.res_held(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  x: Trees.Binding,
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b)
) -> {Vend.Res.held(~d, a, x) == True{}: Bool} -> {Vend.Res.held(~d, b, x) == True{}: Bool}:
  match x:
    case Trees.Binding{Nil{}, v}:
      e => e
    case Trees.Binding{Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, r}, +v}:
      Stable.res_kept(
        ~d,
        a,
        b,
        Codes.Code.whole.read(~Requests.Res, ~Requests.Res.code, ~Requests.Res.code.read, v),
        g
      )
    case Trees.Binding{Con{U32{WCon{True{}, t}}, r}, v}:
      e => e
    case Trees.Binding{Con{U32{WCon{False{}, WCon{True{}, t}}}, r}, v}:
      e => e
    case Trees.Binding{Con{U32{WCon{False{}, WCon{False{}, WCon{True{}, t}}}}, r}, v}:
      e => e
    case Trees.Binding{Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}, r}, v}:
      e => e
    case Trees.Binding{Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}, r}, v}:
      e => e
    case Trees.Binding{Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}, r}, v}:
      e => e
    case Trees.Binding{Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}, r}, v}:
      e => e
    case Trees.Binding{Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}, r}, v}:
      e => e
    case Trees.Binding{Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}, r}, v}:
      e => e
    case Trees.Binding{Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}, r}, v}:
      e => e
    case Trees.Binding{Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}, r}, v}:
      e => e
    case Trees.Binding{Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}, r}, v}:
      e => e
    case Trees.Binding{Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}, r}, v}:
      e => e
    case Trees.Binding{Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}, r}, v}:
      e => e
    case Trees.Binding{Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}, r}, v}:
      e => e
    case Trees.Binding{Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}, r}, v}:
      e => e
    case Trees.Binding{Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}, r}, v}:
      e => e
    case Trees.Binding{Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}, r}, v}:
      e => e
    case Trees.Binding{Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}, r}, v}:
      e => e
    case Trees.Binding{Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}, r}, v}:
      e => e
    case Trees.Binding{Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}}, r}, v}:
      e => e
    case Trees.Binding{Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}}}, r}, v}:
      e => e
    case Trees.Binding{Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}}}}, r}, v}:
      e => e
    case Trees.Binding{Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}}}}}, r}, v}:
      e => e
    case Trees.Binding{Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}}}}}}, r}, v}:
      e => e
    case Trees.Binding{Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}}}}}}}, r}, v}:
      e => e
    case Trees.Binding{Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}}}}}}}}, r}, v}:
      e => e
    case Trees.Binding{Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, r}, v}:
      e => e
    case Trees.Binding{Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, r}, v}:
      e => e
    case Trees.Binding{Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, r}, v}:
      e => e
    case Trees.Binding{Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, r}, v}:
      e => e
    case Trees.Binding{Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, r}, v}:
      e => e

# a ledger that holds the resources of some bindings holds them as it grows
def Stable.all_held(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  xs: List<&2, Trees.Binding>,
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b)
) -> {Vend.Res.all_held(~d, a, xs) == True{}: Bool} -> {Vend.Res.all_held(~d, b, xs) == True{}: Bool}:
  match xs:
    case Nil{}:
      e => e
    case Con{+x, +rest}:
      +e => Shared.List.all.if_both(Vend.Res.held(~d, b, x), u => Vend.Res.all_held(~d, b, rest))(
        Stable.res_held(~d, a, b, x, g)(Shared.List.all.if_hit(Vend.Res.held(~d, a, x), u => Vend.Res.all_held(~d, a, rest))(e))
      )(Stable.all_held(~d, a, b, rest, g)(Shared.List.all.if_rest(Vend.Res.held(~d, a, x), u => Vend.Res.all_held(~d, a, rest))(e)))

# Stable.tree_kept, once the listing m is known
def Stable.kept_of(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  m: Maybe<&2, List<&2, Trees.Binding>>,
  -m2: Maybe<&2, List<&2, Trees.Binding>>,
  hm: @v: List<&2, Trees.Binding> -> {m == Some{v}: Maybe<&2, List<&2, Trees.Binding>>}
    -> {m2 == Some{v}: Maybe<&2, List<&2, Trees.Binding>>},
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b)
) -> {
  Maybe.default(&2, Bool, Maybe.bind(&2, List<&2, Trees.Binding>, Bool, m, bs => Some{Vend.Res.all_held(~d, a, bs)}), False{}) == True{}: Bool
} -> {
  Maybe.default(&2, Bool, Maybe.bind(&2, List<&2, Trees.Binding>, Bool, m2, bs => Some{Vend.Res.all_held(~d, b, bs)}), False{}) == True{}: Bool
}:
  match m:
    case None{}:
      e => Empty.absurd(
        {
          Maybe.default(&2, Bool, Maybe.bind(&2, List<&2, Trees.Binding>, Bool, m2, bs => Some{Vend.Res.all_held(~d, b, bs)}), False{})
            == True{}: Bool
        },
        Shared.Bool.false_ne_true(e)
      )
    case Some{+v}:
      e =>
        %Equal.sym(Maybe<&2, List<&2, Trees.Binding>>, m2, Some{v}, hm(v)({==})): {
          Maybe.default(&2, Bool, Maybe.bind(&2, List<&2, Trees.Binding>, Bool, _, bs => Some{Vend.Res.all_held(~d, b, bs)}), False{})
            == True{}: Bool
        }
        Stable.all_held(~d, a, b, v, g)(e)

# a ledger that holds a whole tree holds it as it grows
def Stable.tree_kept(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b)
) -> {Vend.Tree.kept(~d, a, h) == True{}: Bool} -> {Vend.Tree.kept(~d, b, h) == True{}: Bool}:
  Stable.kept_of(
    ~d,
    a,
    b,
    Vend.Tree.range(~d, a, h, []),
    Vend.Tree.range(~d, b, h, []),
    +v => e => Stable.range_grows(~d, a, b, h, [], v, g)(e),
    g
  )

# a ledger that holds each node of a tree holds them as it grows
def Stable.tree_whole(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b)
) -> {Vend.Tree.whole(~d, a, h) == True{}: Bool} -> {Vend.Tree.whole(~d, b, h) == True{}: Bool}:
  Stable.is_some_kept(
    List<&2, Trees.Binding>,
    Vend.Tree.range(~d, a, h, []),
    Vend.Tree.range(~d, b, h, []),
    +v => e => Stable.range_grows(~d, a, b, h, [], v, g)(e)
  )

# the groups of a tree stay as the ledger grows
def Stable.groups_in(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +gs: List<&2, Owners.Group>,
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b)
) -> {Owners.Groups.in(~d, a, h) == Some{gs}: Maybe<&2, List<&2, Owners.Group>>} -> {Owners.Groups.in(~d, b, h) == Some{gs}: Maybe<&2, List<&2, Owners.Group>>}:
  Stable.map_kept(
    List<&2, Trees.Binding>,
    List<&2, Owners.Group>,
    Owners.Groups.of,
    Vend.Tree.range(~d, a, h, [2]),
    Vend.Tree.range(~d, b, h, [2]),
    gs,
    +v => e => Stable.range_grows(~d, a, b, h, [2], v, g)(e)
  )

# the nodes of a group stay as the ledger grows
def Stable.group_nodes(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +gn: String,
  +ns: List<&2, String>,
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b)
) -> {Owners.Group.nodes(~d, a, h, gn) == Some{ns}: Maybe<&2, List<&2, String>>}
  -> {Owners.Group.nodes(~d, b, h, gn) == Some{ns}: Maybe<&2, List<&2, String>>}:
  Stable.map_kept(
    List<&2, Owners.Group>,
    List<&2, String>,
    gs => Owners.Group.nodes.of(gs, gn),
    Owners.Groups.in(~d, a, h),
    Owners.Groups.in(~d, b, h),
    ns,
    +v => e => Stable.groups_in(~d, a, b, h, v, g)(e)
  )

# the clashes that are open after a merge stay as the ledger grows
def Stable.clash_names(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +ns: List<&2, Resources.Name>,
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b)
) -> {Vend.Clash.names(~d, a, h, k) == Some{ns}: Maybe<&2, List<&2, Resources.Name>>}
  -> {Vend.Clash.names(~d, b, h, k) == Some{ns}: Maybe<&2, List<&2, Resources.Name>>}:
  Stable.map_kept(
    Maybe<&2, List<&2, Resources.Name>>,
    List<&2, Resources.Name>,
    m => Maybe.default(&2, List<&2, Resources.Name>, m, []),
    Replicas.Tip.known(
      ~List<&2, Resources.Name>,
      ~(ns2 => r => Codes.Code.list(~Resources.Name, ~Resources.Name.code, ns2, r)),
      ~(ws => Codes.Code.list.read(~Resources.Name, ~Resources.Name.code.read, ws)),
      Replicas.Tree.find(~Requests.Ask.machine(), ~d, a, h, Vend.Key.clashes(k))
    ),
    Replicas.Tip.known(
      ~List<&2, Resources.Name>,
      ~(ns2 => r => Codes.Code.list(~Resources.Name, ~Resources.Name.code, ns2, r)),
      ~(ws => Codes.Code.list.read(~Resources.Name, ~Resources.Name.code.read, ws)),
      Replicas.Tree.find(~Requests.Ask.machine(), ~d, b, h, Vend.Key.clashes(k))
    ),
    ns,
    +v => e => Stable.known_kept(
      ~List<&2, Resources.Name>,
      ~(ns2 => r => Codes.Code.list(~Resources.Name, ~Resources.Name.code, ns2, r)),
      ~(ws => Codes.Code.list.read(~Resources.Name, ~Resources.Name.code.read, ws)),
      Replicas.Tree.find(~Requests.Ask.machine(), ~d, a, h, Vend.Key.clashes(k)),
      Replicas.Tree.find(~Requests.Ask.machine(), ~d, b, h, Vend.Key.clashes(k)),
      v,
      +w => ew => Replicas.Hist.find(~Requests.Ask.machine(), ~d, a, b, h, Vend.Key.clashes(k), w, g)(ew)
    )(e)
  )

# the resource that a content gives stays as the ledger grows
def Stable.content(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +t: Replicas.Tip,
  +n: Resources.Name,
  +x: Requests.Content,
  +r: Maybe<&2, Requests.Res>,
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b)
) -> {Vend.Content.find(~d, a, t, n, x) == Some{r}: Maybe<&2, Maybe<&2, Requests.Res>>}
  -> {Vend.Content.find(~d, b, t, n, x) == Some{r}: Maybe<&2, Maybe<&2, Requests.Res>>}:
  match x:
    case Requests.Content.New{y}:
      e => e
    case Requests.Content.Of{+i}:
      Shared.Maybe.bind_kept(
        Maybe<&2, Hashes.Hash>,
        Maybe<&2, Requests.Res>,
        Replicas.Tip.version(~Requests.Ask.machine(), ~d, a, t, i),
        Replicas.Tip.version(~Requests.Ask.machine(), ~d, b, t, i),
        h => Vend.Res.find(~d, a, h, n),
        h => Vend.Res.find(~d, b, h, n),
        r,
        +h => e => Stable.version(~d, a, b, t, i, h, g)(e),
        +h => e => Stable.res_find(~d, a, b, h, n, r, g)(e)
      )

# the tree of the base of a write stays as the ledger grows
def Stable.base_root(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +t: Replicas.Tip,
  +m: Maybe<&2, Ledgers.Id>,
  +h: Maybe<&2, Hashes.Hash>,
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b)
) -> {Vend.Base.root(~d, a, t, m) == Some{h}: Maybe<&2, Maybe<&2, Hashes.Hash>>}
  -> {Vend.Base.root(~d, b, t, m) == Some{h}: Maybe<&2, Maybe<&2, Hashes.Hash>>}:
  match m:
    case None{}:
      e => e
    case Some{+i}:
      Stable.version(~d, a, b, t, i, h, g)

# what Res.set does stays as the ledger grows
def Stable.res_set(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +t: Replicas.Tip,
  +n: Resources.Name,
  +new: Maybe<&2, Requests.Res>,
  +x: Replicas.Act,
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b)
) -> {Vend.Res.set(~d, a, t, n, new) == Some{x}: Maybe<&2, Replicas.Act>} -> {Vend.Res.set(~d, b, t, n, new) == Some{x}: Maybe<&2, Replicas.Act>}:
  Stable.when_test(
    Maybe<&2, Replicas.Act>,
    Vend.Res.kept(~d, a, new),
    Vend.Res.kept(~d, b, new),
    u => Vend.Act.put(
      None{},
      [],
      Replicas.Tree.put(~Requests.Ask.machine(), ~d, a, Replicas.Tip.content(t), Vend.Key.res(n), Vend.Res.value(new))
    ),
    u => None{},
    u => Vend.Act.put(
      None{},
      [],
      Replicas.Tree.put(~Requests.Ask.machine(), ~d, b, Replicas.Tip.content(t), Vend.Key.res(n), Vend.Res.value(new))
    ),
    u => None{},
    Some{x},
    hc => Stable.res_kept(~d, a, b, new, g)(hc),
    Stable.act_put_kept(
      None{},
      [],
      Replicas.Tree.put(~Requests.Ask.machine(), ~d, a, Replicas.Tip.content(t), Vend.Key.res(n), Vend.Res.value(new)),
      Replicas.Tree.put(~Requests.Ask.machine(), ~d, b, Replicas.Tip.content(t), Vend.Key.res(n), Vend.Res.value(new)),
      x,
      +v => e => Replicas.Hist.put(~Requests.Ask.machine(), ~d, a, b, Replicas.Tip.content(t), Vend.Key.res(n), Vend.Res.value(new), v, g)(e)
    ),
    e => Shared.Maybe.none_ne_some(Replicas.Act, x, e)
  )

# what a write does stays as the ledger grows
def Stable.write(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +t: Replicas.Tip,
  +n: Resources.Name,
  +base: Maybe<&2, Ledgers.Id>,
  +c: Requests.Content,
  +x: Replicas.Act,
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b)
) -> {Vend.Write.act(~d, a, t, n, base, c) == Some{x}: Maybe<&2, Replicas.Act>}
  -> {Vend.Write.act(~d, b, t, n, base, c) == Some{x}: Maybe<&2, Replicas.Act>}:
  Shared.Maybe.bind_kept(
    Maybe<&2, Requests.Res>,
    Replicas.Act,
    Vend.Res.find(~d, a, Replicas.Tip.content(t), n),
    Vend.Res.find(~d, b, Replicas.Tip.content(t), n),
    ours => Maybe.bind(
      &2,
      Maybe<&2, Hashes.Hash>,
      Replicas.Act,
      Vend.Base.root(~d, a, t, base),
      h => Maybe.bind(
        &2,
        Maybe<&2, Requests.Res>,
        Replicas.Act,
        Vend.Res.find(~d, a, h, n),
        held => Maybe.bind(
          &2,
          Maybe<&2, Requests.Res>,
          Replicas.Act,
          Vend.Content.find(~d, a, t, n, c),
          new => Vend.Write.act.of(~d, a, t, n, ours, held, new)
        )
      )
    ),
    ours => Maybe.bind(
      &2,
      Maybe<&2, Hashes.Hash>,
      Replicas.Act,
      Vend.Base.root(~d, b, t, base),
      h => Maybe.bind(
        &2,
        Maybe<&2, Requests.Res>,
        Replicas.Act,
        Vend.Res.find(~d, b, h, n),
        held => Maybe.bind(
          &2,
          Maybe<&2, Requests.Res>,
          Replicas.Act,
          Vend.Content.find(~d, b, t, n, c),
          new => Vend.Write.act.of(~d, b, t, n, ours, held, new)
        )
      )
    ),
    x,
    +ours => e => Stable.res_find(~d, a, b, Replicas.Tip.content(t), n, ours, g)(e),
    +ours => Shared.Maybe.bind_kept(
      Maybe<&2, Hashes.Hash>,
      Replicas.Act,
      Vend.Base.root(~d, a, t, base),
      Vend.Base.root(~d, b, t, base),
      h => Maybe.bind(
        &2,
        Maybe<&2, Requests.Res>,
        Replicas.Act,
        Vend.Res.find(~d, a, h, n),
        held => Maybe.bind(
          &2,
          Maybe<&2, Requests.Res>,
          Replicas.Act,
          Vend.Content.find(~d, a, t, n, c),
          new => Vend.Write.act.of(~d, a, t, n, ours, held, new)
        )
      ),
      h => Maybe.bind(
        &2,
        Maybe<&2, Requests.Res>,
        Replicas.Act,
        Vend.Res.find(~d, b, h, n),
        held => Maybe.bind(
          &2,
          Maybe<&2, Requests.Res>,
          Replicas.Act,
          Vend.Content.find(~d, b, t, n, c),
          new => Vend.Write.act.of(~d, b, t, n, ours, held, new)
        )
      ),
      x,
      +h => e => Stable.base_root(~d, a, b, t, base, h, g)(e),
      +h => Shared.Maybe.bind_kept(
        Maybe<&2, Requests.Res>,
        Replicas.Act,
        Vend.Res.find(~d, a, h, n),
        Vend.Res.find(~d, b, h, n),
        held => Maybe.bind(
          &2,
          Maybe<&2, Requests.Res>,
          Replicas.Act,
          Vend.Content.find(~d, a, t, n, c),
          new => Vend.Write.act.of(~d, a, t, n, ours, held, new)
        ),
        held => Maybe.bind(
          &2,
          Maybe<&2, Requests.Res>,
          Replicas.Act,
          Vend.Content.find(~d, b, t, n, c),
          new => Vend.Write.act.of(~d, b, t, n, ours, held, new)
        ),
        x,
        +held => e => Stable.res_find(~d, a, b, h, n, held, g)(e),
        +held => Shared.Maybe.bind_kept(
          Maybe<&2, Requests.Res>,
          Replicas.Act,
          Vend.Content.find(~d, a, t, n, c),
          Vend.Content.find(~d, b, t, n, c),
          new => Vend.Write.act.of(~d, a, t, n, ours, held, new),
          new => Vend.Write.act.of(~d, b, t, n, ours, held, new),
          x,
          +new => e => Stable.content(~d, a, b, t, n, c, new, g)(e),
          +new => Stable.when_same(
            Maybe<&2, Replicas.Act>,
            Vend.Res.same(ours, held),
            u => Vend.Res.set(~d, a, t, n, new),
            u => Some{Replicas.Act.Stale{}},
            u => Vend.Res.set(~d, b, t, n, new),
            u => Some{Replicas.Act.Stale{}},
            Some{x},
            c1 => e => Stable.res_set(~d, a, b, t, n, new, x, g)(e),
            c1 => e => e
          )
        )
      )
    )
  )

# what a move does stays as the ledger grows
def Stable.move(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +s: Requests.Source,
  +x: Replicas.Act,
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b)
) -> {Vend.Move.act(~d, a, s) == Some{x}: Maybe<&2, Replicas.Act>} -> {Vend.Move.act(~d, b, s) == Some{x}: Maybe<&2, Replicas.Act>}:
  match s:
    case Requests.Source{v, +h}:
      Stable.when_test(
        Maybe<&2, Replicas.Act>,
        Vend.Tree.kept(~d, a, h),
        Vend.Tree.kept(~d, b, h),
        u => Some{Replicas.Act.Taken{None{}, h, []}},
        u => None{},
        u => Some{Replicas.Act.Taken{None{}, h, []}},
        u => None{},
        Some{x},
        hc => Stable.tree_kept(~d, a, b, h, g)(hc),
        e => e,
        e => Shared.Maybe.none_ne_some(Replicas.Act, x, e)
      )

# what a new branch does stays as the ledger grows
def Stable.branch(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +t: Replicas.Tip,
  +n: String,
  +m: Maybe<&2, Requests.Source>,
  +x: Replicas.Act,
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b)
) -> {Vend.Branch.act(~d, a, t, n, m) == Some{x}: Maybe<&2, Replicas.Act>} -> {Vend.Branch.act(~d, b, t, n, m) == Some{x}: Maybe<&2, Replicas.Act>}:
  match m:
    case None{}:
      e => e
    case Some{Requests.Source{v, +h}}:
      Stable.when_test(
        Maybe<&2, Replicas.Act>,
        Vend.Tree.kept(~d, a, h),
        Vend.Tree.kept(~d, b, h),
        u => Some{Replicas.Act.Opens{n, Vend.Branch.tip(t, h), []}},
        u => None{},
        u => Some{Replicas.Act.Opens{n, Vend.Branch.tip(t, h), []}},
        u => None{},
        Some{x},
        hc => Stable.tree_kept(~d, a, b, h, g)(hc),
        e => e,
        e => Shared.Maybe.none_ne_some(Replicas.Act, x, e)
      )

# what a first key does stays as the ledger grows
def Stable.key(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +t: Replicas.Tip,
  +n: String,
  +k: Hashes.Hash,
  +x: Replicas.Act,
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b)
) -> {Vend.Key.act(~d, a, t, n, k) == Some{x}: Maybe<&2, Replicas.Act>} -> {Vend.Key.act(~d, b, t, n, k) == Some{x}: Maybe<&2, Replicas.Act>}:
  Stable.act_put_kept(
    None{},
    [],
    Replicas.Tree.put(~Requests.Ask.machine(), ~d, a, Replicas.Tip.content(t), Requests.Key.seal(n), Some{Hashes.Hash.code(k, [])}),
    Replicas.Tree.put(~Requests.Ask.machine(), ~d, b, Replicas.Tip.content(t), Requests.Key.seal(n), Some{Hashes.Hash.code(k, [])}),
    x,
    +v => e => Replicas.Hist.put(
      ~Requests.Ask.machine(),
      ~d,
      a,
      b,
      Replicas.Tip.content(t),
      Requests.Key.seal(n),
      Some{Hashes.Hash.code(k, [])},
      v,
      g
    )(e)
  )

# what Group.act.of does stays as the ledger grows
def Stable.group_of(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +gn: String,
  +ms: List<&2, Requests.Member>,
  +gs: List<&2, Owners.Group>,
  +x: Replicas.Act,
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b)
) -> {Owners.Group.act.of(~d, a, h, gn, ms, gs) == Some{x}: Maybe<&2, Replicas.Act>}
  -> {Owners.Group.act.of(~d, b, h, gn, ms, gs) == Some{x}: Maybe<&2, Replicas.Act>}:
  Stable.when_same(
    Maybe<&2, Replicas.Act>,
    Crits.Dict.has(Unit, Owners.Group.reach(Owners.Groups.set(gs, gn, ms), gn), Owners.Group.key(gn)),
    u => Some{Replicas.Act.Stale{}},
    u => Vend.Act.put(None{}, [], Replicas.Tree.put(~Requests.Ask.machine(), ~d, a, h, Owners.Key.group(gn), Some{Requests.Members.code(ms, [])})),
    u => Some{Replicas.Act.Stale{}},
    u => Vend.Act.put(None{}, [], Replicas.Tree.put(~Requests.Ask.machine(), ~d, b, h, Owners.Key.group(gn), Some{Requests.Members.code(ms, [])})),
    Some{x},
    c => e => e,
    c => Stable.act_put_kept(
      None{},
      [],
      Replicas.Tree.put(~Requests.Ask.machine(), ~d, a, h, Owners.Key.group(gn), Some{Requests.Members.code(ms, [])}),
      Replicas.Tree.put(~Requests.Ask.machine(), ~d, b, h, Owners.Key.group(gn), Some{Requests.Members.code(ms, [])}),
      x,
      +v => e => Replicas.Hist.put(
        ~Requests.Ask.machine(),
        ~d,
        a,
        b,
        h,
        Owners.Key.group(gn),
        Some{Requests.Members.code(ms, [])},
        v,
        g
      )(e)
    )
  )

# what a group does stays as the ledger grows
def Stable.group(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +t: Replicas.Tip,
  +gn: String,
  +ms: List<&2, Requests.Member>,
  +x: Replicas.Act,
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b)
) -> {Owners.Group.act(~d, a, t, gn, ms) == Some{x}: Maybe<&2, Replicas.Act>} -> {Owners.Group.act(~d, b, t, gn, ms) == Some{x}: Maybe<&2, Replicas.Act>}:
  +h = Replicas.Tip.content(t)
  Stable.when_test(
    Maybe<&2, Replicas.Act>,
    Vend.Tree.whole(~d, a, h),
    Vend.Tree.whole(~d, b, h),
    u => Maybe.bind(&2, List<&2, Owners.Group>, Replicas.Act, Owners.Groups.in(~d, a, h), gs => Owners.Group.act.of(~d, a, h, gn, ms, gs)),
    u => None{},
    u => Maybe.bind(&2, List<&2, Owners.Group>, Replicas.Act, Owners.Groups.in(~d, b, h), gs => Owners.Group.act.of(~d, b, h, gn, ms, gs)),
    u => None{},
    Some{x},
    hc => Stable.tree_whole(~d, a, b, h, g)(hc),
    Shared.Maybe.bind_kept(
      List<&2, Owners.Group>,
      Replicas.Act,
      Owners.Groups.in(~d, a, h),
      Owners.Groups.in(~d, b, h),
      gs => Owners.Group.act.of(~d, a, h, gn, ms, gs),
      gs => Owners.Group.act.of(~d, b, h, gn, ms, gs),
      x,
      +gs => e => Stable.groups_in(~d, a, b, h, gs, g)(e),
      +gs => e => Stable.group_of(~d, a, b, h, gn, ms, gs, x, g)(e)
    ),
    e => Shared.Maybe.none_ne_some(Replicas.Act, x, e)
  )

# what an Own does stays as the ledger grows
def Stable.own(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +t: Replicas.Tip,
  +gn: String,
  +at: Maybe<&2, Requests.Source>,
  +os: List<&2, String>,
  +x: Replicas.Act,
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b)
) -> {Owners.Own.act(~d, a, t, gn, at, os) == Some{x}: Maybe<&2, Replicas.Act>}
  -> {Owners.Own.act(~d, b, t, gn, at, os) == Some{x}: Maybe<&2, Replicas.Act>}:
  +h = Owners.Own.tree(t, at)
  Stable.when_test(
    Maybe<&2, Replicas.Act>,
    Vend.Tree.whole(~d, a, h),
    Vend.Tree.whole(~d, b, h),
    u => Maybe.bind(
      &2,
      List<&2, String>,
      Replicas.Act,
      Owners.Group.nodes(~d, a, h, gn),
      +ns => Shared.Bool.when(
        Maybe<&2, Replicas.Act>,
        List.all.if(v => Shared.List.same_set(~String, ~String.eq, os, ns), Bool.not(List.is_empty(&2, String, os))),
        v => Vend.Act.put(
          Some{os},
          [],
          Replicas.Tree.put(~Requests.Ask.machine(), ~d, a, Replicas.Tip.content(t), Owners.Key.owner(), Some{Codes.Code.text(gn, [])})
        ),
        v => Some{Replicas.Act.Stale{}}
      )
    ),
    u => None{},
    u => Maybe.bind(
      &2,
      List<&2, String>,
      Replicas.Act,
      Owners.Group.nodes(~d, b, h, gn),
      +ns => Shared.Bool.when(
        Maybe<&2, Replicas.Act>,
        List.all.if(v => Shared.List.same_set(~String, ~String.eq, os, ns), Bool.not(List.is_empty(&2, String, os))),
        v => Vend.Act.put(
          Some{os},
          [],
          Replicas.Tree.put(~Requests.Ask.machine(), ~d, b, Replicas.Tip.content(t), Owners.Key.owner(), Some{Codes.Code.text(gn, [])})
        ),
        v => Some{Replicas.Act.Stale{}}
      )
    ),
    u => None{},
    Some{x},
    hc => Stable.tree_whole(~d, a, b, h, g)(hc),
    Shared.Maybe.bind_kept(
      List<&2, String>,
      Replicas.Act,
      Owners.Group.nodes(~d, a, h, gn),
      Owners.Group.nodes(~d, b, h, gn),
      +ns => Shared.Bool.when(
        Maybe<&2, Replicas.Act>,
        List.all.if(v => Shared.List.same_set(~String, ~String.eq, os, ns), Bool.not(List.is_empty(&2, String, os))),
        v => Vend.Act.put(
          Some{os},
          [],
          Replicas.Tree.put(~Requests.Ask.machine(), ~d, a, Replicas.Tip.content(t), Owners.Key.owner(), Some{Codes.Code.text(gn, [])})
        ),
        v => Some{Replicas.Act.Stale{}}
      ),
      +ns => Shared.Bool.when(
        Maybe<&2, Replicas.Act>,
        List.all.if(v => Shared.List.same_set(~String, ~String.eq, os, ns), Bool.not(List.is_empty(&2, String, os))),
        v => Vend.Act.put(
          Some{os},
          [],
          Replicas.Tree.put(~Requests.Ask.machine(), ~d, b, Replicas.Tip.content(t), Owners.Key.owner(), Some{Codes.Code.text(gn, [])})
        ),
        v => Some{Replicas.Act.Stale{}}
      ),
      x,
      +ns => e => Stable.group_nodes(~d, a, b, h, gn, ns, g)(e),
      +ns => Stable.when_same(
        Maybe<&2, Replicas.Act>,
        List.all.if(v => Shared.List.same_set(~String, ~String.eq, os, ns), Bool.not(List.is_empty(&2, String, os))),
        v => Vend.Act.put(
          Some{os},
          [],
          Replicas.Tree.put(~Requests.Ask.machine(), ~d, a, Replicas.Tip.content(t), Owners.Key.owner(), Some{Codes.Code.text(gn, [])})
        ),
        v => Some{Replicas.Act.Stale{}},
        v => Vend.Act.put(
          Some{os},
          [],
          Replicas.Tree.put(~Requests.Ask.machine(), ~d, b, Replicas.Tip.content(t), Owners.Key.owner(), Some{Codes.Code.text(gn, [])})
        ),
        v => Some{Replicas.Act.Stale{}},
        Some{x},
        c => Stable.act_put_kept(
          Some{os},
          [],
          Replicas.Tree.put(~Requests.Ask.machine(), ~d, a, Replicas.Tip.content(t), Owners.Key.owner(), Some{Codes.Code.text(gn, [])}),
          Replicas.Tree.put(~Requests.Ask.machine(), ~d, b, Replicas.Tip.content(t), Owners.Key.owner(), Some{Codes.Code.text(gn, [])}),
          x,
          +v => e => Replicas.Hist.put(
            ~Requests.Ask.machine(),
            ~d,
            a,
            b,
            Replicas.Tip.content(t),
            Owners.Key.owner(),
            Some{Codes.Code.text(gn, [])},
            v,
            g
          )(e)
        ),
        c => e => e
      )
    ),
    e => Shared.Maybe.none_ne_some(Replicas.Act, x, e)
  )

# the ledger a, the ledger b that grows from it, and the words w that b holds
def Stable.Plus(~d: Vend.Led()) -> Data:
  Sigma<&2, &2, Vend.L(d), a => Sigma<&2, &2, Vend.L(d), b => Sigma<&2, &2, List<&2, U32>, w => Merges.Merge.And(
    Replicas.Led.Grows(Requests.Ask.machine(), d, a, b),
    {Replicas.Led.fetch(~Requests.Ask.machine(), ~d, b, Hashes.Sha.hash(w)) == Some{w}: Maybe<&2, List<&2, U32>>}
  )>>>

# the ledger a of p with the words w
def Stable.Plus.added(~d: Vend.Led(), p: Stable.Plus(~d)) -> Vend.L(d):
  match p:
    case Tuple{a, Tuple{b, Tuple{w, r}}}:
      Replicas.Led.add(~Requests.Ask.machine(), ~d, a, Ledgers.Entry.Data{w})

# the ledger b of p
def Stable.Plus.top(~d: Vend.Led(), p: Stable.Plus(~d)) -> Vend.L(d):
  match p:
    case Tuple{a, Tuple{b, Tuple{w, r}}}:
      b

# a ledger that gives the words w under their hash holds them as an entry
def Stable.word_has(
  ~d: Vend.Led(),
  +b: Vend.L(d),
  +w: List<&2, U32>,
  r: Maybe<&2, Ledgers.Entry<Requests.Ask>>,
  +er: {Ledgers.Kind.get(Replicas.Machine.Q(Requests.Ask.machine()), Replicas.Led.kind(Requests.Ask.machine(), d))(b)(Ledgers.Name.Data{Hashes.Sha.hash(w)}) == r: Maybe<&2, Ledgers.Entry<Requests.Ask>>},
  hf: {Ledgers.Entry.words(Requests.Ask, r) == Some{w}: Maybe<&2, List<&2, U32>>}
) -> {Ledgers.Kind.has(~Replicas.Machine.Q(Requests.Ask.machine()), ~Replicas.Machine.code(Requests.Ask.machine()), ~Replicas.Led.kind(Requests.Ask.machine(), d), b, Ledgers.Entry.Data{w}) == True{}: Bool}:
  match r:
    case None{}:
      Empty.absurd({Ledgers.Kind.has(~Replicas.Machine.Q(Requests.Ask.machine()), ~Replicas.Machine.code(Requests.Ask.machine()), ~Replicas.Led.kind(Requests.Ask.machine(), d), b, Ledgers.Entry.Data{w}) == True{}: Bool}, Shared.Maybe.none_ne_some(List<&2, U32>, w, hf))
    case Some{Ledgers.Entry.Ask{i, t, q}}:
      Empty.absurd({Ledgers.Kind.has(~Replicas.Machine.Q(Requests.Ask.machine()), ~Replicas.Machine.code(Requests.Ask.machine()), ~Replicas.Led.kind(Requests.Ask.machine(), d), b, Ledgers.Entry.Data{w}) == True{}: Bool}, Shared.Maybe.none_ne_some(List<&2, U32>, w, hf))
    case Some{Ledgers.Entry.Ballot{x}}:
      Empty.absurd({Ledgers.Kind.has(~Replicas.Machine.Q(Requests.Ask.machine()), ~Replicas.Machine.code(Requests.Ask.machine()), ~Replicas.Led.kind(Requests.Ask.machine(), d), b, Ledgers.Entry.Data{w}) == True{}: Bool}, Shared.Maybe.none_ne_some(List<&2, U32>, w, hf))
    case Some{Ledgers.Entry.Lie{x}}:
      Empty.absurd({Ledgers.Kind.has(~Replicas.Machine.Q(Requests.Ask.machine()), ~Replicas.Machine.code(Requests.Ask.machine()), ~Replicas.Led.kind(Requests.Ask.machine(), d), b, Ledgers.Entry.Data{w}) == True{}: Bool}, Shared.Maybe.none_ne_some(List<&2, U32>, w, hf))
    case Some{Ledgers.Entry.Data{+ws}}:
      %Equal.sym(Maybe<&2, Ledgers.Entry<Requests.Ask>>, Ledgers.Kind.get(Replicas.Machine.Q(Requests.Ask.machine()), Replicas.Led.kind(Requests.Ask.machine(), d))(b)(Ledgers.Name.Data{Hashes.Sha.hash(w)}), Some{Ledgers.Entry.Data{ws}}, er): {
        Shared.Maybe.is_eq(~Ledgers.Entry<Requests.Ask>, ~Ledgers.Entry.same(~Requests.Ask, ~Replicas.Machine.code(Requests.Ask.machine())), _, Some{Ledgers.Entry.Data{w}}) == True{}: Bool
      }
      %Equal.sym(List<&2, U32>, ws, w, Shared.Maybe.some_inj(List<&2, U32>, ws, w, hf)): {
        Shared.Maybe.is_eq(~Ledgers.Entry<Requests.Ask>, ~Ledgers.Entry.same(~Requests.Ask, ~Replicas.Machine.code(Requests.Ask.machine())), Some{Ledgers.Entry.Data{_}}, Some{Ledgers.Entry.Data{w}}) == True{}: Bool
      }
      Ledgers.Entry.same_refl(~Requests.Ask, ~Replicas.Machine.code(Requests.Ask.machine()), Ledgers.Entry.Data{w})

# Stable.add_has when a lacks the name of e, once it is known whether it is
# the name of the words w (q)
def Stable.add_has.none(
  ~d: Vend.Led(),
  +b: Vend.L(d),
  +w: List<&2, U32>,
  +e: Ledgers.Entry<Requests.Ask>,
  q: Bool,
  +hf: {Replicas.Led.fetch(~Requests.Ask.machine(), ~d, b, Hashes.Sha.hash(w)) == Some{w}: Maybe<&2, List<&2, U32>>}
) -> {
  Shared.Maybe.is_eq(~Ledgers.Entry<Requests.Ask>, ~Ledgers.Entry.same(~Requests.Ask, ~Replicas.Machine.code(Requests.Ask.machine())), Shared.Maybe.when(Ledgers.Entry<Requests.Ask>, q, u => Some{Ledgers.Entry.Data{w}}), Some{e}) == True{}: Bool
} -> {Ledgers.Kind.has(~Replicas.Machine.Q(Requests.Ask.machine()), ~Replicas.Machine.code(Requests.Ask.machine()), ~Replicas.Led.kind(Requests.Ask.machine(), d), b, e) == True{}: Bool}:
  match q:
    case True{}:
      h => Reads.Affects.cast(
        Ledgers.Entry<Requests.Ask>,
        z => {Ledgers.Kind.has(~Replicas.Machine.Q(Requests.Ask.machine()), ~Replicas.Machine.code(Requests.Ask.machine()), ~Replicas.Led.kind(Requests.Ask.machine(), d), b, z) == True{}: Bool},
        Ledgers.Entry.Data{w},
        e,
        Ledgers.Entry.same_sound(~Requests.Ask, ~Replicas.Machine.code(Requests.Ask.machine()), Ledgers.Entry.Data{w}, e)(h),
        Stable.word_has(~d, b, w, Ledgers.Kind.get(Replicas.Machine.Q(Requests.Ask.machine()), Replicas.Led.kind(Requests.Ask.machine(), d))(b)(Ledgers.Name.Data{Hashes.Sha.hash(w)}), {==}, hf)
      )
    case False{}:
      h => Empty.absurd({Ledgers.Kind.has(~Replicas.Machine.Q(Requests.Ask.machine()), ~Replicas.Machine.code(Requests.Ask.machine()), ~Replicas.Led.kind(Requests.Ask.machine(), d), b, e) == True{}: Bool}, Shared.Bool.false_ne_true(h))

# Stable.add_has once the entry m that a gives under the name of e is known
def Stable.add_has.at(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +w: List<&2, U32>,
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b),
  +hf: {Replicas.Led.fetch(~Requests.Ask.machine(), ~d, b, Hashes.Sha.hash(w)) == Some{w}: Maybe<&2, List<&2, U32>>},
  +e: Ledgers.Entry<Requests.Ask>,
  m: Maybe<&2, Ledgers.Entry<Requests.Ask>>,
  +em: {Ledgers.Kind.get(Replicas.Machine.Q(Requests.Ask.machine()), Replicas.Led.kind(Requests.Ask.machine(), d))(a)(Ledgers.Entry.name(~Requests.Ask, ~Replicas.Machine.code(Requests.Ask.machine()), e)) == m: Maybe<&2, Ledgers.Entry<Requests.Ask>>}
) -> {
  Shared.Maybe.is_eq(~Ledgers.Entry<Requests.Ask>, ~Ledgers.Entry.same(~Requests.Ask, ~Replicas.Machine.code(Requests.Ask.machine())), Maybe.or(
      &2,
      Ledgers.Entry<Requests.Ask>,
      m,
      Shared.Maybe.when(Ledgers.Entry<Requests.Ask>, Ledgers.Name.is_eq(Ledgers.Entry.name(~Requests.Ask, ~Replicas.Machine.code(Requests.Ask.machine()), Ledgers.Entry.Data{w}), Ledgers.Entry.name(~Requests.Ask, ~Replicas.Machine.code(Requests.Ask.machine()), e)), u => Some{Ledgers.Entry.Data{w}})
    ), Some{e})
    == True{}: Bool
} -> {Ledgers.Kind.has(~Replicas.Machine.Q(Requests.Ask.machine()), ~Replicas.Machine.code(Requests.Ask.machine()), ~Replicas.Led.kind(Requests.Ask.machine(), d), b, e) == True{}: Bool}:
  match m:
    case Some{+y}:
      h => Ledgers.Kind.grows_has(~Replicas.Machine.Q(Requests.Ask.machine()), ~Replicas.Machine.code(Requests.Ask.machine()), ~Replicas.Led.kind(Requests.Ask.machine(), d), ~Replicas.Led.laws(Requests.Ask.machine(), d), a, b, g, e)(
        Reads.Affects.cast(
          Maybe<&2, Ledgers.Entry<Requests.Ask>>,
          z => {Shared.Maybe.is_eq(~Ledgers.Entry<Requests.Ask>, ~Ledgers.Entry.same(~Requests.Ask, ~Replicas.Machine.code(Requests.Ask.machine())), z, Some{e}) == True{}: Bool},
          Some{y},
          Ledgers.Kind.get(Replicas.Machine.Q(Requests.Ask.machine()), Replicas.Led.kind(Requests.Ask.machine(), d))(a)(Ledgers.Entry.name(~Requests.Ask, ~Replicas.Machine.code(Requests.Ask.machine()), e)),
          Equal.sym(Maybe<&2, Ledgers.Entry<Requests.Ask>>, Ledgers.Kind.get(Replicas.Machine.Q(Requests.Ask.machine()), Replicas.Led.kind(Requests.Ask.machine(), d))(a)(Ledgers.Entry.name(~Requests.Ask, ~Replicas.Machine.code(Requests.Ask.machine()), e)), Some{y}, em),
          h
        )
      )
    case None{}:
      h => Stable.add_has.none(~d, b, w, e, Ledgers.Name.is_eq(Ledgers.Entry.name(~Requests.Ask, ~Replicas.Machine.code(Requests.Ask.machine()), Ledgers.Entry.Data{w}), Ledgers.Entry.name(~Requests.Ask, ~Replicas.Machine.code(Requests.Ask.machine()), e)), hf)(h)

# each entry of a with the words w is an entry of b, which holds them
def Stable.add_has(~d: Vend.Led(), p: Stable.Plus(~d), +e: Ledgers.Entry<Requests.Ask>) -> {Ledgers.Kind.has(~Replicas.Machine.Q(Requests.Ask.machine()), ~Replicas.Machine.code(Requests.Ask.machine()), ~Replicas.Led.kind(Requests.Ask.machine(), d), Stable.Plus.added(~d, p), e) == True{}: Bool}
  -> {Ledgers.Kind.has(~Replicas.Machine.Q(Requests.Ask.machine()), ~Replicas.Machine.code(Requests.Ask.machine()), ~Replicas.Led.kind(Requests.Ask.machine(), d), Stable.Plus.top(~d, p), e) == True{}: Bool}:
  match p:
    case Tuple{+a, Tuple{+b, Tuple{+w, Tuple{+g, +hf}}}}:
      h => Stable.add_has.at(~d, a, b, w, g, hf, e, Ledgers.Kind.get(Replicas.Machine.Q(Requests.Ask.machine()), Replicas.Led.kind(Requests.Ask.machine(), d))(a)(Ledgers.Entry.name(~Requests.Ask, ~Replicas.Machine.code(Requests.Ask.machine()), e)), {==})(
        Reads.Affects.cast(
          Maybe<&2, Ledgers.Entry<Requests.Ask>>,
          z => {Shared.Maybe.is_eq(~Ledgers.Entry<Requests.Ask>, ~Ledgers.Entry.same(~Requests.Ask, ~Replicas.Machine.code(Requests.Ask.machine())), z, Some{e}) == True{}: Bool},
          Ledgers.Kind.get(Replicas.Machine.Q(Requests.Ask.machine()), Replicas.Led.kind(Requests.Ask.machine(), d))(Replicas.Led.add(~Requests.Ask.machine(), ~d, a, Ledgers.Entry.Data{w}))(Ledgers.Entry.name(~Requests.Ask, ~Replicas.Machine.code(Requests.Ask.machine()), e)),
          Maybe.or(
            &2,
            Ledgers.Entry<Requests.Ask>,
            Ledgers.Kind.get(Replicas.Machine.Q(Requests.Ask.machine()), Replicas.Led.kind(Requests.Ask.machine(), d))(a)(Ledgers.Entry.name(~Requests.Ask, ~Replicas.Machine.code(Requests.Ask.machine()), e)),
            Shared.Maybe.when(Ledgers.Entry<Requests.Ask>, Ledgers.Name.is_eq(Ledgers.Entry.name(~Requests.Ask, ~Replicas.Machine.code(Requests.Ask.machine()), Ledgers.Entry.Data{w}), Ledgers.Entry.name(~Requests.Ask, ~Replicas.Machine.code(Requests.Ask.machine()), e)), u => Some{Ledgers.Entry.Data{w}})
          ),
          Merges.Merge.get_add(~d)(a)(Ledgers.Entry.Data{w})(Ledgers.Entry.name(~Requests.Ask, ~Replicas.Machine.code(Requests.Ask.machine()), e)),
          h
        )
      )

# a ledger with some words grows into a ledger that holds them, when the ledger
# without them does
def Stable.grows_add(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +w: List<&2, U32>,
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b),
  +hf: {Replicas.Led.fetch(~Requests.Ask.machine(), ~d, b, Hashes.Sha.hash(w)) == Some{w}: Maybe<&2, List<&2, U32>>}
) -> Replicas.Led.Grows(Requests.Ask.machine(), d, Replicas.Led.add(~Requests.Ask.machine(), ~d, a, Ledgers.Entry.Data{w}), b):
  Ledgers.Kind.grows_core(
    ~Replicas.Machine.Q(Requests.Ask.machine()), ~Replicas.Machine.code(Requests.Ask.machine()), ~Replicas.Led.kind(Requests.Ask.machine(), d),
    ~Replicas.Led.laws(Requests.Ask.machine(), d),
    ~Stable.Plus(~d),
    ~(p => Stable.Plus.added(~d, p)),
    ~(p => Stable.Plus.top(~d, p)),
    ~(p => e => h => Stable.add_has(~d, p, e)(h)),
    Tuple{a, Tuple{b, Tuple{w, Tuple{g, hf}}}}
  )

# a ledger with the nodes N grows into a ledger that holds them, when the
# ledger without them does
def Stable.puts_grows(
  ~d: Vend.Led(),
  N: List<&2, List<&2, U32>>,
  +a: Vend.L(d),
  +b: Vend.L(d),
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b),
  +hn: {Depots.Depot.holds(~Vend.L(d), ~(s => x => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, x)), b, N) == True{}: Bool}
) -> Replicas.Led.Grows(Requests.Ask.machine(), d, Replicas.Led.puts(~Requests.Ask.machine(), ~d, N, a), b):
  match N:
    case Nil{}:
      g
    case Con{+w, +r}:
      Stable.puts_grows(
        ~d,
        r,
        Replicas.Led.add(~Requests.Ask.machine(), ~d, a, Ledgers.Entry.Data{w}),
        b,
        Stable.grows_add(
          ~d,
          a,
          b,
          w,
          g,
          Replicas.Hist.has(~Requests.Ask.machine(), ~d, b, w)(
            Shared.List.all.if_hit(
              Depots.Depot.has(~Vend.L(d), ~(s => x => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, x)), b, w),
              u => Depots.Depot.holds(~Vend.L(d), ~(s => x => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, x)), b, r)
            )(hn)
          )
        ),
        Shared.List.all.if_rest(
          Depots.Depot.has(~Vend.L(d), ~(s => x => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, x)), b, w),
          u => Depots.Depot.holds(~Vend.L(d), ~(s => x => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, x)), b, r)
        )(hn)
      )

# two ledgers that get the same nodes grow, when the larger holds them
def Stable.puts_mono(
  ~d: Vend.Led(),
  +N: List<&2, List<&2, U32>>,
  +a: Vend.L(d),
  +b: Vend.L(d),
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b),
  +hn: {Depots.Depot.holds(~Vend.L(d), ~(s => x => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, x)), b, N) == True{}: Bool}
) -> Replicas.Led.Grows(Requests.Ask.machine(), d, Replicas.Led.puts(~Requests.Ask.machine(), ~d, N, a), Replicas.Led.puts(~Requests.Ask.machine(), ~d, N, b)):
  Replicas.Hist.trans(
    ~Requests.Ask.machine(),
    ~d,
    Replicas.Led.puts(~Requests.Ask.machine(), ~d, N, a),
    b,
    Replicas.Led.puts(~Requests.Ask.machine(), ~d, N, b),
    Stable.puts_grows(~d, N, a, b, g, hn),
    Replicas.Hist.puts(~Requests.Ask.machine(), ~d, N, b)
  )

# a ledger that holds the nodes A and then B holds A
def Stable.holds_left(~d: Vend.Led(), +l: Vend.L(d), A: List<&2, List<&2, U32>>, +B: List<&2, List<&2, U32>>) -> {Depots.Depot.holds(~Vend.L(d), ~(s => x => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, x)), l, List.append(&2, List<&2, U32>, A, B)) == True{}: Bool} -> {Depots.Depot.holds(~Vend.L(d), ~(s => x => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, x)), l, A) == True{}: Bool}:
  match A:
    case Nil{}:
      e => {==}
    case Con{+w, +r}:
      +e => Shared.List.all.if_both(
        Depots.Depot.has(~Vend.L(d), ~(s => x => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, x)), l, w),
        u => Depots.Depot.holds(~Vend.L(d), ~(s => x => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, x)), l, r)
      )(
        Shared.List.all.if_hit(
          Depots.Depot.has(~Vend.L(d), ~(s => x => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, x)), l, w),
          u => Depots.Depot.holds(~Vend.L(d), ~(s => x => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, x)), l, List.append(&2, List<&2, U32>, r, B))
        )(e)
      )(
        Stable.holds_left(~d, l, r, B)(
          Shared.List.all.if_rest(
            Depots.Depot.has(~Vend.L(d), ~(s => x => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, x)), l, w),
            u => Depots.Depot.holds(~Vend.L(d), ~(s => x => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, x)), l, List.append(&2, List<&2, U32>, r, B))
          )(e)
        )
      )

# a ledger that holds some nodes holds the nodes before them
def Stable.holds_prefix(~d: Vend.Led(), +l: Vend.L(d), +P: List<&2, List<&2, U32>>, +N: List<&2, List<&2, U32>>, nd: Merges.Merge.Nodes(P, N), +hn: {Depots.Depot.holds(~Vend.L(d), ~(s => x => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, x)), l, N) == True{}: Bool}) -> {Depots.Depot.holds(~Vend.L(d), ~(s => x => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, x)), l, P) == True{}: Bool}:
  match nd:
    case Tuple{+ex, pe}:
      Stable.holds_left(~d, l, P, ex)(
        Reads.Affects.cast(List<&2, List<&2, U32>>, z => {Depots.Depot.holds(~Vend.L(d), ~(s => x => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, x)), l, z) == True{}: Bool}, N, List.append(&2, List<&2, U32>, P, ex), pe, hn)
      )

# the nodes after the nodes of a pair of facts
def Stable.nodes_of(-A: Data, -P: List<&2, List<&2, U32>>, -N: List<&2, List<&2, U32>>, p: Merges.Merge.And(A, Merges.Merge.Nodes(P, N))) -> Merges.Merge.Nodes(P, N):
  match p:
    case Tuple{x, y}:
      y

# the ledger of a pair of facts
def Stable.puts_of(-A: Data, -B: Data, p: Merges.Merge.And(A, B)) -> A:
  match p:
    case Tuple{x, y}:
      x

# the work w as a ledger b that grows from its own would hold it: b with the
# nodes of w
def Stable.over(~d: Vend.Led(), +b: Vend.L(d), w: Merges.Work<Vend.L(d)>) -> Merges.Work<Vend.L(d)>:
  match w:
    case Merges.Work{l, h, +ns}:
      Merges.Work{Replicas.Led.puts(~Requests.Ask.machine(), ~d, ns, b), h, ns}

# a bind that gives x gives y of a read that gives what the first gave, when
# each rest that gives x gives y
def Stable.bind_to(
  -A: Data,
  -B: Data,
  m: Maybe<&2, A>,
  -m2: Maybe<&2, A>,
  -k: A -> Maybe<&2, B>,
  -k2: A -> Maybe<&2, B>,
  -x: B,
  -y: B,
  hm: @v: A -> {m == Some{v}: Maybe<&2, A>} -> {m2 == Some{v}: Maybe<&2, A>},
  hk: @v: A -> {k(v) == Some{x}: Maybe<&2, B>} -> {k2(v) == Some{y}: Maybe<&2, B>}
) -> {Maybe.bind(&2, A, B, m, k) == Some{x}: Maybe<&2, B>} -> {Maybe.bind(&2, A, B, m2, k2) == Some{y}: Maybe<&2, B>}:
  match m:
    case None{}:
      e => Empty.absurd({Maybe.bind(&2, A, B, m2, k2) == Some{y}: Maybe<&2, B>}, Shared.Maybe.none_ne_some(B, x, e))
    case Some{+v}:
      e =>
        %Equal.sym(Maybe<&2, A>, m2, Some{v}, hm(v)({==})): {Maybe.bind(&2, A, B, _, k2) == Some{y}: Maybe<&2, B>}
        hk(v)(e)

# Stable.set once the write pr of the work is known
def Stable.set.at(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +la: Vend.L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +km: List<&2, U32>,
  +m: Maybe<&2, List<&2, U32>>,
  pr: Maybe<&2, Trees.Edit>,
  +epr: {Replicas.Tree.put(~Requests.Ask.machine(), ~d, la, h, km, m) == pr: Maybe<&2, Trees.Edit>},
  +W1: Merges.Work<Vend.L(d)>,
  +wa: Merges.Merge.Puts(~d, a, la, P),
  +hold1: {Depots.Depot.holds(~Vend.L(d), ~(s => x => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, x)), b, Merges.Merge.nodes(~d, W1)) == True{}: Bool},
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b)
) -> {Merges.Work.put(~d, la, P, pr) == Some{W1}: Maybe<&2, Merges.Work<Vend.L(d)>>}
  -> {Merges.Work.set(~d, Merges.Work{Replicas.Led.puts(~Requests.Ask.machine(), ~d, P, b), h, P}, km, m) == Some{Stable.over(~d, b, W1)}: Maybe<&2, Merges.Work<Vend.L(d)>>}:
  match pr:
    case None{}:
      e => Empty.absurd(
        {Merges.Work.set(~d, Merges.Work{Replicas.Led.puts(~Requests.Ask.machine(), ~d, P, b), h, P}, km, m) == Some{Stable.over(~d, b, W1)}: Maybe<&2, Merges.Work<Vend.L(d)>>},
        Shared.Maybe.none_ne_some(Merges.Work<Vend.L(d)>, W1, e)
      )
    case Some{+ed}:
      +e =>
        +ew = Merges.Merge.put_work(~d, la, P, ed, W1, e)
        +hN = Reads.Affects.cast(
          Merges.Work<Vend.L(d)>,
          z => {Depots.Depot.holds(~Vend.L(d), ~(s => x => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, x)), b, Merges.Merge.nodes(~d, z)) == True{}: Bool},
          W1,
          Merges.Work{Replicas.Led.puts(~Requests.Ask.machine(), ~d, Trees.Edit.nodes(ed), la), Trees.Edit.root(ed), List.append(&2, List<&2, U32>, P, Trees.Edit.nodes(ed))},
          Equal.sym(Merges.Work<Vend.L(d)>, Merges.Work{Replicas.Led.puts(~Requests.Ask.machine(), ~d, Trees.Edit.nodes(ed), la), Trees.Edit.root(ed), List.append(&2, List<&2, U32>, P, Trees.Edit.nodes(ed))}, W1, ew),
          hold1
        )
        +gla = Reads.Affects.cast(
          Vend.L(d),
          z => Replicas.Led.Grows(Requests.Ask.machine(), d, z, Replicas.Led.puts(~Requests.Ask.machine(), ~d, P, b)),
          Replicas.Led.puts(~Requests.Ask.machine(), ~d, P, a),
          la,
          Equal.sym(Vend.L(d), la, Replicas.Led.puts(~Requests.Ask.machine(), ~d, P, a), wa),
          Stable.puts_mono(~d, P, a, b, g, Stable.holds_left(~d, b, P, Trees.Edit.nodes(ed))(hN))
        )
        %ew: {Merges.Work.set(~d, Merges.Work{Replicas.Led.puts(~Requests.Ask.machine(), ~d, P, b), h, P}, km, m) == Some{Stable.over(~d, b, _)}: Maybe<&2, Merges.Work<Vend.L(d)>>}
        %Equal.sym(
          Vend.L(d),
          Replicas.Led.puts(~Requests.Ask.machine(), ~d, List.append(&2, List<&2, U32>, P, Trees.Edit.nodes(ed)), b),
          Replicas.Led.puts(~Requests.Ask.machine(), ~d, Trees.Edit.nodes(ed), Replicas.Led.puts(~Requests.Ask.machine(), ~d, P, b)),
          Merges.Merge.puts_append(~d, P, Trees.Edit.nodes(ed), b)
        ): {
          Merges.Work.set(~d, Merges.Work{Replicas.Led.puts(~Requests.Ask.machine(), ~d, P, b), h, P}, km, m) == Some{Merges.Work{_, Trees.Edit.root(ed), List.append(&2, List<&2, U32>, P, Trees.Edit.nodes(ed))}}: Maybe<&2, Merges.Work<Vend.L(d)>>
        }
        %Equal.sym(
          Maybe<&2, Trees.Edit>,
          Replicas.Tree.put(~Requests.Ask.machine(), ~d, Replicas.Led.puts(~Requests.Ask.machine(), ~d, P, b), h, km, m),
          Some{ed},
          Replicas.Hist.put(~Requests.Ask.machine(), ~d, la, Replicas.Led.puts(~Requests.Ask.machine(), ~d, P, b), h, km, m, ed, gla)(epr)
        ): {
          Merges.Work.put(~d, Replicas.Led.puts(~Requests.Ask.machine(), ~d, P, b), P, _)
            == Some{Merges.Work{Replicas.Led.puts(~Requests.Ask.machine(), ~d, Trees.Edit.nodes(ed), Replicas.Led.puts(~Requests.Ask.machine(), ~d, P, b)), Trees.Edit.root(ed), List.append(&2, List<&2, U32>, P, Trees.Edit.nodes(ed))}}: Maybe<&2, Merges.Work<Vend.L(d)>>
        }
        {==}

# a write to a work stays, in a ledger that grows and holds its nodes
def Stable.set(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  w: Merges.Work<Vend.L(d)>,
  +km: List<&2, U32>,
  +m: Maybe<&2, List<&2, U32>>,
  +W1: Merges.Work<Vend.L(d)>,
  +wa: Merges.Merge.Puts(~d, a, Merges.Merge.ledger(~d, w), Merges.Merge.nodes(~d, w)),
  +hold1: {Depots.Depot.holds(~Vend.L(d), ~(s => x => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, x)), b, Merges.Merge.nodes(~d, W1)) == True{}: Bool},
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b)
) -> {Merges.Work.set(~d, w, km, m) == Some{W1}: Maybe<&2, Merges.Work<Vend.L(d)>>} -> {Merges.Work.set(~d, Stable.over(~d, b, w), km, m) == Some{Stable.over(~d, b, W1)}: Maybe<&2, Merges.Work<Vend.L(d)>>}:
  match w:
    case Merges.Work{+la, +h, +P}:
      e => Stable.set.at(~d, a, b, la, h, P, km, m, Replicas.Tree.put(~Requests.Ask.machine(), ~d, la, h, km, m), {==}, W1, wa, hold1, g)(e)

# the bytes of a resource, or none, stay as the ledger grows
def Stable.text(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  m: Maybe<&2, Requests.Res>,
  +y: Texts.Bytes(),
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b)
) -> {Merges.Res.text(~d, a, m) == Some{y}: Maybe<&2, Texts.Bytes()>} -> {Merges.Res.text(~d, b, m) == Some{y}: Maybe<&2, Texts.Bytes()>}:
  match m:
    case None{}:
      e => e
    case Some{+x}:
      Stable.bytes(~d, a, b, Vend.Res.root(x), y, g)

# Stable.pick_format for a format that merges bytes
def Stable.pick_format.bytes(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +h: Hashes.Hash,
  +f: Formats.Format,
  +bm: Maybe<&2, Requests.Res>,
  +ob: Texts.Bytes(),
  +tb: Texts.Bytes(),
  +p: Merges.Pick,
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b)
) -> {
  Maybe.bind(&2, Texts.Bytes(), Merges.Pick, Merges.Res.text(~d, a, bm), bb => Some{Merges.Pick.of(h, Formats.Format.merge(f, bb, ob, tb))}) == Some{p}: Maybe<&2, Merges.Pick>
} -> {
  Maybe.bind(&2, Texts.Bytes(), Merges.Pick, Merges.Res.text(~d, b, bm), bb => Some{Merges.Pick.of(h, Formats.Format.merge(f, bb, ob, tb))}) == Some{p}: Maybe<&2, Merges.Pick>
}:
  Shared.Maybe.bind_kept(
    Texts.Bytes(),
    Merges.Pick,
    Merges.Res.text(~d, a, bm),
    Merges.Res.text(~d, b, bm),
    bb => Some{Merges.Pick.of(h, Formats.Format.merge(f, bb, ob, tb))},
    bb => Some{Merges.Pick.of(h, Formats.Format.merge(f, bb, ob, tb))},
    p,
    +y => e => Stable.text(~d, a, b, bm, y, g)(e),
    y => e => e
  )

# the pick of a merge in a format stays as the ledger grows
def Stable.pick_format(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +h: Hashes.Hash,
  +f: Formats.Format,
  +bm: Maybe<&2, Requests.Res>,
  +ob: Texts.Bytes(),
  +tb: Texts.Bytes(),
  +p: Merges.Pick,
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b)
) -> {Merges.Pick.format(~d, a, h, f, bm, ob, tb) == Some{p}: Maybe<&2, Merges.Pick>} -> {Merges.Pick.format(~d, b, h, f, bm, ob, tb) == Some{p}: Maybe<&2, Merges.Pick>}:
  match f:
    case Formats.Format.Leaf{Formats.Leaf.Module{}}:
      e => e
    case Formats.Format.Leaf{Formats.Leaf.Lines{}}:
      Stable.pick_format.bytes(~d, a, b, h, Formats.Format.Leaf{Formats.Leaf.Lines{}}, bm, ob, tb, p, g)
    case Formats.Format.Leaf{Formats.Leaf.Whole{}}:
      Stable.pick_format.bytes(~d, a, b, h, Formats.Format.Leaf{Formats.Leaf.Whole{}}, bm, ob, tb, p, g)
    case Formats.Format.Embed{+o1, +op, +cl, +i1}:
      Stable.pick_format.bytes(~d, a, b, h, Formats.Format.Embed{o1, op, cl, i1}, bm, ob, tb, p, g)
    case Formats.Format.Code{+bs, +ru, +im}:
      Stable.pick_format.bytes(~d, a, b, h, Formats.Format.Code{bs, ru, im}, bm, ob, tb, p, g)

# the pick of a merge of both changes, in a format, stays as the ledger grows
def Stable.pick_in(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +h: Hashes.Hash,
  +f: Formats.Format,
  +bm: Maybe<&2, Requests.Res>,
  +o: Maybe<&2, Requests.Res>,
  +t: Maybe<&2, Requests.Res>,
  +p: Merges.Pick,
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b)
) -> {Merges.Pick.in(~d, a, h, f, bm, o, t) == Some{p}: Maybe<&2, Merges.Pick>} -> {Merges.Pick.in(~d, b, h, f, bm, o, t) == Some{p}: Maybe<&2, Merges.Pick>}:
  Shared.Maybe.bind_kept(
    Texts.Bytes(),
    Merges.Pick,
    Merges.Res.text(~d, a, o),
    Merges.Res.text(~d, b, o),
    ob => Maybe.bind(&2, Texts.Bytes(), Merges.Pick, Merges.Res.text(~d, a, t), tb => Merges.Pick.format(~d, a, h, f, bm, ob, tb)),
    ob => Maybe.bind(&2, Texts.Bytes(), Merges.Pick, Merges.Res.text(~d, b, t), tb => Merges.Pick.format(~d, b, h, f, bm, ob, tb)),
    p,
    +y => e => Stable.text(~d, a, b, o, y, g)(e),
    +ob => Shared.Maybe.bind_kept(
      Texts.Bytes(),
      Merges.Pick,
      Merges.Res.text(~d, a, t),
      Merges.Res.text(~d, b, t),
      tb => Merges.Pick.format(~d, a, h, f, bm, ob, tb),
      tb => Merges.Pick.format(~d, b, h, f, bm, ob, tb),
      p,
      +y => e => Stable.text(~d, a, b, t, y, g)(e),
      +tb => e => Stable.pick_format(~d, a, b, h, f, bm, ob, tb, p, g)(e)
    )
  )

# Stable.pick_both once the format of the merge mh is known
def Stable.pick_both.at(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +bm: Maybe<&2, Requests.Res>,
  +o: Maybe<&2, Requests.Res>,
  +t: Maybe<&2, Requests.Res>,
  mh: Maybe<&2, Hashes.Hash>,
  +p: Merges.Pick,
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b)
) -> {
  Maybe.default(
    &2,
    Maybe<&2, Merges.Pick>,
    Maybe.bind(
      &2,
      Hashes.Hash,
      Maybe<&2, Merges.Pick>,
      mh,
      +h => Some{Maybe.bind(&2, Formats.Format, Merges.Pick, Vend.Format.at(~d, a, h), f => Merges.Pick.in(~d, a, h, f, bm, o, t))}
    ),
    Some{Merges.Pick.Take{None{}}}
  )
    == Some{p}: Maybe<&2, Merges.Pick>
} -> {
  Maybe.default(
    &2,
    Maybe<&2, Merges.Pick>,
    Maybe.bind(
      &2,
      Hashes.Hash,
      Maybe<&2, Merges.Pick>,
      mh,
      +h => Some{Maybe.bind(&2, Formats.Format, Merges.Pick, Vend.Format.at(~d, b, h), f => Merges.Pick.in(~d, b, h, f, bm, o, t))}
    ),
    Some{Merges.Pick.Take{None{}}}
  )
    == Some{p}: Maybe<&2, Merges.Pick>
}:
  match mh:
    case None{}:
      e => e
    case Some{+h}:
      Shared.Maybe.bind_kept(
        Formats.Format,
        Merges.Pick,
        Vend.Format.at(~d, a, h),
        Vend.Format.at(~d, b, h),
        f => Merges.Pick.in(~d, a, h, f, bm, o, t),
        f => Merges.Pick.in(~d, b, h, f, bm, o, t),
        p,
        +f => e => Stable.format_at(~d, a, b, h, f, g)(e),
        +f => e => Stable.pick_in(~d, a, b, h, f, bm, o, t, p, g)(e)
      )

# the pick of a merge of both changes stays as the ledger grows
def Stable.pick_both(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +bm: Maybe<&2, Requests.Res>,
  +o: Maybe<&2, Requests.Res>,
  +t: Maybe<&2, Requests.Res>,
  +p: Merges.Pick,
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b)
) -> {Merges.Pick.both(~d, a, bm, o, t) == Some{p}: Maybe<&2, Merges.Pick>} -> {Merges.Pick.both(~d, b, bm, o, t) == Some{p}: Maybe<&2, Merges.Pick>}:
  Stable.when_same(
    Maybe<&2, Merges.Pick>,
    Merges.Res.one_format(o, t),
    u => Maybe.default(
      &2,
      Maybe<&2, Merges.Pick>,
      Maybe.bind(
        &2,
        Hashes.Hash,
        Maybe<&2, Merges.Pick>,
        Merges.Res.format.of(o, t),
        +h => Some{Maybe.bind(&2, Formats.Format, Merges.Pick, Vend.Format.at(~d, a, h), f => Merges.Pick.in(~d, a, h, f, bm, o, t))}
      ),
      Some{Merges.Pick.Take{None{}}}
    ),
    u => Some{Merges.Pick.Clash{}},
    u => Maybe.default(
      &2,
      Maybe<&2, Merges.Pick>,
      Maybe.bind(
        &2,
        Hashes.Hash,
        Maybe<&2, Merges.Pick>,
        Merges.Res.format.of(o, t),
        +h => Some{Maybe.bind(&2, Formats.Format, Merges.Pick, Vend.Format.at(~d, b, h), f => Merges.Pick.in(~d, b, h, f, bm, o, t))}
      ),
      Some{Merges.Pick.Take{None{}}}
    ),
    u => Some{Merges.Pick.Clash{}},
    Some{p},
    c => e => Stable.pick_both.at(~d, a, b, bm, o, t, Merges.Res.format.of(o, t), p, g)(e),
    c => e => e
  )

# what a merge keeps of a resource, by a side, stays as the ledger grows
def Stable.pick_side(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +bm: Maybe<&2, Requests.Res>,
  +o: Maybe<&2, Requests.Res>,
  +t: Maybe<&2, Requests.Res>,
  s: Sides.Side,
  +p: Merges.Pick,
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b)
) -> {Merges.Pick.side(~d, a, bm, o, t, s) == Some{p}: Maybe<&2, Merges.Pick>} -> {Merges.Pick.side(~d, b, bm, o, t, s) == Some{p}: Maybe<&2, Merges.Pick>}:
  match s:
    case Sides.Side.Theirs{}:
      e => e
    case Sides.Side.Ours{}:
      e => e
    case Sides.Side.Both{}:
      Stable.pick_both(~d, a, b, bm, o, t, p, g)

# what a merge keeps of a resource stays as the ledger grows
def Stable.pick_merge(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +bm: Maybe<&2, Requests.Res>,
  +o: Maybe<&2, Requests.Res>,
  +t: Maybe<&2, Requests.Res>,
  +p: Merges.Pick,
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b)
) -> {Merges.Pick.merge(~d, a, bm, o, t) == Some{p}: Maybe<&2, Merges.Pick>} -> {Merges.Pick.merge(~d, b, bm, o, t) == Some{p}: Maybe<&2, Merges.Pick>}:
  Stable.pick_side(~d, a, b, bm, o, t, Sides.Side.of(~Maybe<&2, Requests.Res>, ~Vend.Res.same, bm, o, t), p, g)

# the clash of a work stays, in a ledger that grows and holds its nodes
def Stable.clash(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +la: Vend.L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +W1: Merges.Work<Vend.L(d)>,
  +wa: Merges.Merge.Puts(~d, a, la, P),
  +hold1: {Depots.Depot.holds(~Vend.L(d), ~(s => x => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, x)), b, Merges.Merge.nodes(~d, W1)) == True{}: Bool},
  +hP: {Depots.Depot.holds(~Vend.L(d), ~(s => x => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, x)), b, P) == True{}: Bool},
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b)
) -> {Merges.Work.clash(~d, Merges.Work{la, h, P}, k, n) == Some{W1}: Maybe<&2, Merges.Work<Vend.L(d)>>}
  -> {Merges.Work.clash(~d, Merges.Work{Replicas.Led.puts(~Requests.Ask.machine(), ~d, P, b), h, P}, k, n) == Some{Stable.over(~d, b, W1)}: Maybe<&2, Merges.Work<Vend.L(d)>>}:
  +gla = Reads.Affects.cast(
    Vend.L(d),
    z => Replicas.Led.Grows(Requests.Ask.machine(), d, z, Replicas.Led.puts(~Requests.Ask.machine(), ~d, P, b)),
    Replicas.Led.puts(~Requests.Ask.machine(), ~d, P, a),
    la,
    Equal.sym(Vend.L(d), la, Replicas.Led.puts(~Requests.Ask.machine(), ~d, P, a), wa),
    Stable.puts_mono(~d, P, a, b, g, hP)
  )
  Stable.bind_to(
    List<&2, Resources.Name>,
    Merges.Work<Vend.L(d)>,
    Vend.Clash.names(~d, la, h, k),
    Vend.Clash.names(~d, Replicas.Led.puts(~Requests.Ask.machine(), ~d, P, b), h, k),
    cs => Merges.Work.set(~d, Merges.Work{la, h, P}, Vend.Key.clashes(k), Vend.Clash.value(Vend.Clash.put(n, cs))),
    cs => Merges.Work.set(~d, Merges.Work{Replicas.Led.puts(~Requests.Ask.machine(), ~d, P, b), h, P}, Vend.Key.clashes(k), Vend.Clash.value(Vend.Clash.put(n, cs))),
    W1,
    Stable.over(~d, b, W1),
    +cs => e => Stable.clash_names(~d, la, Replicas.Led.puts(~Requests.Ask.machine(), ~d, P, b), h, k, cs, gla)(e),
    +cs => e => Stable.set(~d, a, b, Merges.Work{la, h, P}, Vend.Key.clashes(k), Vend.Clash.value(Vend.Clash.put(n, cs)), W1, wa, hold1, g)(e)
  )

# Stable.pick once the work is known
def Stable.pick.at(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +la: Vend.L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  p: Merges.Pick,
  +W1: Merges.Work<Vend.L(d)>,
  +wa: Merges.Merge.Puts(~d, a, la, P),
  +hold1: {Depots.Depot.holds(~Vend.L(d), ~(s => x => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, x)), b, Merges.Merge.nodes(~d, W1)) == True{}: Bool},
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b)
) -> {Merges.Merge.pick(~d, Merges.Work{la, h, P}, k, n, p) == Some{W1}: Maybe<&2, Merges.Work<Vend.L(d)>>}
  -> {Merges.Merge.pick(~d, Merges.Work{Replicas.Led.puts(~Requests.Ask.machine(), ~d, P, b), h, P}, k, n, p) == Some{Stable.over(~d, b, W1)}: Maybe<&2, Merges.Work<Vend.L(d)>>}:
  match p:
    case Merges.Pick.Take{+x}:
      e => Stable.set(~d, a, b, Merges.Work{la, h, P}, Vend.Key.res(n), Vend.Res.value(x), W1, wa, hold1, g)(e)
    case Merges.Pick.Make{+hh, +bytes}:
      e =>
        %Merges.Merge.puts_append(~d, P, Ropes.Put.nodes(Ropes.Rope.of_bytes(bytes)), b): {
          Merges.Work.set(
            ~d,
            Merges.Work{_, h, List.append(&2, List<&2, U32>, P, Ropes.Put.nodes(Ropes.Rope.of_bytes(bytes)))},
            Vend.Key.res(n),
            Vend.Res.value(Some{Requests.Res{hh, Ropes.Put.root(Ropes.Rope.of_bytes(bytes))}})
          )
            == Some{Stable.over(~d, b, W1)}: Maybe<&2, Merges.Work<Vend.L(d)>>
        }
        Stable.set(
          ~d,
          a,
          b,
          Merges.Work{Replicas.Led.puts(~Requests.Ask.machine(), ~d, Ropes.Put.nodes(Ropes.Rope.of_bytes(bytes)), la), h, List.append(&2, List<&2, U32>, P, Ropes.Put.nodes(Ropes.Rope.of_bytes(bytes)))},
          Vend.Key.res(n),
          Vend.Res.value(Some{Requests.Res{hh, Ropes.Put.root(Ropes.Rope.of_bytes(bytes))}}),
          W1,
          Merges.Merge.keep_puts(~d, a, la, P, Ropes.Put.nodes(Ropes.Rope.of_bytes(bytes)), wa),
          hold1,
          g
        )(e)
    case Merges.Pick.Clash{}:
      +e => Stable.clash(
        ~d,
        a,
        b,
        la,
        h,
        P,
        k,
        n,
        W1,
        wa,
        hold1,
        Stable.holds_prefix(
          ~d,
          b,
          P,
          Merges.Merge.nodes(~d, W1),
          Stable.nodes_of(
            Merges.Merge.Puts(~d, a, Merges.Merge.ledger(~d, W1), Merges.Merge.nodes(~d, W1)),
            P,
            Merges.Merge.nodes(~d, W1),
            Merges.Merge.pick_facts(~d, a, la, h, P, k, n, Merges.Pick.Clash{}, W1, e, wa)
          ),
          hold1
        ),
        g
      )(e)

# the pick of a merge of a resource stays, in a ledger that grows and holds
# its nodes
def Stable.pick(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  w: Merges.Work<Vend.L(d)>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +p: Merges.Pick,
  +W1: Merges.Work<Vend.L(d)>,
  +wa: Merges.Merge.Puts(~d, a, Merges.Merge.ledger(~d, w), Merges.Merge.nodes(~d, w)),
  +hold1: {Depots.Depot.holds(~Vend.L(d), ~(s => x => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, x)), b, Merges.Merge.nodes(~d, W1)) == True{}: Bool},
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b)
) -> {Merges.Merge.pick(~d, w, k, n, p) == Some{W1}: Maybe<&2, Merges.Work<Vend.L(d)>>} -> {Merges.Merge.pick(~d, Stable.over(~d, b, w), k, n, p) == Some{Stable.over(~d, b, W1)}: Maybe<&2, Merges.Work<Vend.L(d)>>}:
  match w:
    case Merges.Work{+la, +h, +P}:
      Stable.pick.at(~d, a, b, la, h, P, k, n, p, W1, wa, hold1, g)

# the merge of a resource stays, in a ledger that grows and holds its nodes
def Stable.one(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +w: Merges.Work<Vend.L(d)>,
  +W1: Merges.Work<Vend.L(d)>,
  +wa: Merges.Merge.Puts(~d, a, Merges.Merge.ledger(~d, w), Merges.Merge.nodes(~d, w)),
  +hold1: {Depots.Depot.holds(~Vend.L(d), ~(s => x => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, x)), b, Merges.Merge.nodes(~d, W1)) == True{}: Bool},
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b)
) -> {Merges.Merge.one(~d, a, hb, ho, ht, k, n, w) == Some{W1}: Maybe<&2, Merges.Work<Vend.L(d)>>}
  -> {Merges.Merge.one(~d, b, hb, ho, ht, k, n, Stable.over(~d, b, w)) == Some{Stable.over(~d, b, W1)}: Maybe<&2, Merges.Work<Vend.L(d)>>}:
  Stable.bind_to(
    Maybe<&2, Requests.Res>,
    Merges.Work<Vend.L(d)>,
    Vend.Res.find(~d, a, hb, n),
    Vend.Res.find(~d, b, hb, n),
    +bm => Maybe.bind(
      &2,
      Maybe<&2, Requests.Res>,
      Merges.Work<Vend.L(d)>,
      Vend.Res.find(~d, a, ho, n),
      +o => Maybe.bind(
        &2,
        Maybe<&2, Requests.Res>,
        Merges.Work<Vend.L(d)>,
        Vend.Res.find(~d, a, ht, n),
        t => Maybe.bind(&2, Merges.Pick, Merges.Work<Vend.L(d)>, Merges.Pick.merge(~d, a, bm, o, t), p => Merges.Merge.pick(~d, w, k, n, p))
      )
    ),
    +bm => Maybe.bind(
      &2,
      Maybe<&2, Requests.Res>,
      Merges.Work<Vend.L(d)>,
      Vend.Res.find(~d, b, ho, n),
      +o => Maybe.bind(
        &2,
        Maybe<&2, Requests.Res>,
        Merges.Work<Vend.L(d)>,
        Vend.Res.find(~d, b, ht, n),
        t => Maybe.bind(&2, Merges.Pick, Merges.Work<Vend.L(d)>, Merges.Pick.merge(~d, b, bm, o, t), p => Merges.Merge.pick(~d, Stable.over(~d, b, w), k, n, p))
      )
    ),
    W1,
    Stable.over(~d, b, W1),
    +bm => e => Stable.res_find(~d, a, b, hb, n, bm, g)(e),
    +bm => Stable.bind_to(
      Maybe<&2, Requests.Res>,
      Merges.Work<Vend.L(d)>,
      Vend.Res.find(~d, a, ho, n),
      Vend.Res.find(~d, b, ho, n),
      +o => Maybe.bind(
        &2,
        Maybe<&2, Requests.Res>,
        Merges.Work<Vend.L(d)>,
        Vend.Res.find(~d, a, ht, n),
        t => Maybe.bind(&2, Merges.Pick, Merges.Work<Vend.L(d)>, Merges.Pick.merge(~d, a, bm, o, t), p => Merges.Merge.pick(~d, w, k, n, p))
      ),
      +o => Maybe.bind(
        &2,
        Maybe<&2, Requests.Res>,
        Merges.Work<Vend.L(d)>,
        Vend.Res.find(~d, b, ht, n),
        t => Maybe.bind(&2, Merges.Pick, Merges.Work<Vend.L(d)>, Merges.Pick.merge(~d, b, bm, o, t), p => Merges.Merge.pick(~d, Stable.over(~d, b, w), k, n, p))
      ),
      W1,
      Stable.over(~d, b, W1),
      +o => e => Stable.res_find(~d, a, b, ho, n, o, g)(e),
      +o => Stable.bind_to(
        Maybe<&2, Requests.Res>,
        Merges.Work<Vend.L(d)>,
        Vend.Res.find(~d, a, ht, n),
        Vend.Res.find(~d, b, ht, n),
        t => Maybe.bind(&2, Merges.Pick, Merges.Work<Vend.L(d)>, Merges.Pick.merge(~d, a, bm, o, t), p => Merges.Merge.pick(~d, w, k, n, p)),
        t => Maybe.bind(&2, Merges.Pick, Merges.Work<Vend.L(d)>, Merges.Pick.merge(~d, b, bm, o, t), p => Merges.Merge.pick(~d, Stable.over(~d, b, w), k, n, p)),
        W1,
        Stable.over(~d, b, W1),
        +t => e => Stable.res_find(~d, a, b, ht, n, t, g)(e),
        +t => Stable.bind_to(
          Merges.Pick,
          Merges.Work<Vend.L(d)>,
          Merges.Pick.merge(~d, a, bm, o, t),
          Merges.Pick.merge(~d, b, bm, o, t),
          p => Merges.Merge.pick(~d, w, k, n, p),
          p => Merges.Merge.pick(~d, Stable.over(~d, b, w), k, n, p),
          W1,
          Stable.over(~d, b, W1),
          +p => e => Stable.pick_merge(~d, a, b, bm, o, t, p, g)(e),
          +p => e => Stable.pick(~d, a, b, w, k, n, p, W1, wa, hold1, g)(e)
        )
      )
    )
  )

# a step of a merge stays, in a ledger that grows and holds its nodes
def Stable.next(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +w: Merges.Work<Vend.L(d)>,
  mn: Maybe<&2, Resources.Name>,
  +W1: Merges.Work<Vend.L(d)>,
  +wa: Merges.Merge.Puts(~d, a, Merges.Merge.ledger(~d, w), Merges.Merge.nodes(~d, w)),
  +hold1: {Depots.Depot.holds(~Vend.L(d), ~(s => x => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, x)), b, Merges.Merge.nodes(~d, W1)) == True{}: Bool},
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b)
) -> {Merges.Merge.next(~d, a, hb, ho, ht, k, w, mn) == Some{W1}: Maybe<&2, Merges.Work<Vend.L(d)>>}
  -> {Merges.Merge.next(~d, b, hb, ho, ht, k, Stable.over(~d, b, w), mn) == Some{Stable.over(~d, b, W1)}: Maybe<&2, Merges.Work<Vend.L(d)>>}:
  match mn:
    case None{}:
      e => Equal.cong(Merges.Work<Vend.L(d)>, Maybe<&2, Merges.Work<Vend.L(d)>>, z => Some{Stable.over(~d, b, z)}, w, W1, Shared.Maybe.some_inj(Merges.Work<Vend.L(d)>, w, W1, e))
    case Some{+n}:
      Stable.one(~d, a, b, hb, ho, ht, k, n, w, W1, wa, hold1, g)

# Stable.all after its first key x, once the work W1 after it is known
def Stable.all.con(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +x: List<&2, U32>,
  +rest: List<&2, List<&2, U32>>,
  +la: Vend.L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +lf: Vend.L(d),
  +hf: Maybe<&2, Hashes.Hash>,
  +N: List<&2, List<&2, U32>>,
  +wa: Merges.Merge.Puts(~d, a, la, P),
  +hold: {Depots.Depot.holds(~Vend.L(d), ~(s => x => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, x)), b, N) == True{}: Bool},
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b),
  +e: {Merges.Merge.all(~d, a, hb, ho, ht, k, x <> rest, Some{Merges.Work{la, hc, P}}) == Some{Merges.Work{lf, hf, N}}: Maybe<&2, Merges.Work<Vend.L(d)>>},
  pr: Sigma<&2, &2, Merges.Work<Vend.L(d)>, W1 => {Merges.Merge.step(~d, a, hb, ho, ht, k, x, Merges.Work{la, hc, P}) == Some{W1}: Maybe<&2, Merges.Work<Vend.L(d)>>}>,
  ih: @W1: Merges.Work<Vend.L(d)> -> Merges.Merge.Puts(~d, a, Merges.Merge.ledger(~d, W1), Merges.Merge.nodes(~d, W1)) -> {Depots.Depot.holds(~Vend.L(d), ~(s => x => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, x)), b, N) == True{}: Bool}
    -> {Merges.Merge.all(~d, a, hb, ho, ht, k, rest, Some{W1}) == Some{Merges.Work{lf, hf, N}}: Maybe<&2, Merges.Work<Vend.L(d)>>}
    -> {Merges.Merge.all(~d, b, hb, ho, ht, k, rest, Some{Stable.over(~d, b, W1)}) == Some{Stable.over(~d, b, Merges.Work{lf, hf, N})}: Maybe<&2, Merges.Work<Vend.L(d)>>}
) -> {
  Merges.Merge.all(~d, b, hb, ho, ht, k, x <> rest, Some{Stable.over(~d, b, Merges.Work{la, hc, P})}) == Some{Stable.over(~d, b, Merges.Work{lf, hf, N})}: Maybe<&2, Merges.Work<Vend.L(d)>>
}:
  match pr:
    case Tuple{Merges.Work{+l1, +h1, +P1}, +e1}:
      +en = Equal.trans(
        Maybe<&2, Merges.Work<Vend.L(d)>>,
        Merges.Merge.next(~d, a, hb, ho, ht, k, Merges.Work{la, hc, P}, Merges.Res.name(x)),
        Merges.Merge.step(~d, a, hb, ho, ht, k, x, Merges.Work{la, hc, P}),
        Some{Merges.Work{l1, h1, P1}},
        Equal.sym(
          Maybe<&2, Merges.Work<Vend.L(d)>>,
          Merges.Merge.step(~d, a, hb, ho, ht, k, x, Merges.Work{la, hc, P}),
          Merges.Merge.next(~d, a, hb, ho, ht, k, Merges.Work{la, hc, P}, Merges.Res.name(x)),
          Merges.Merge.step_eq(~d, a, hb, ho, ht, k, x, Merges.Work{la, hc, P})
        ),
        e1
      )
      +eall = Reads.Affects.cast(
        Maybe<&2, Merges.Work<Vend.L(d)>>,
        z => {Merges.Merge.all(~d, a, hb, ho, ht, k, rest, z) == Some{Merges.Work{lf, hf, N}}: Maybe<&2, Merges.Work<Vend.L(d)>>},
        Merges.Merge.step(~d, a, hb, ho, ht, k, x, Merges.Work{la, hc, P}),
        Some{Merges.Work{l1, h1, P1}},
        e1,
        e
      )
      +wa1 = Stable.puts_of(
        Merges.Merge.Puts(~d, a, l1, P1),
        Merges.Merge.Nodes(P, P1),
        Merges.Merge.next_facts(~d, a, la, hb, ho, ht, hc, P, k, Merges.Res.name(x), Merges.Work{l1, h1, P1}, en, wa)
      )
      +hold1 = Stable.holds_prefix(
        ~d,
        b,
        P1,
        N,
        Stable.nodes_of(Merges.Merge.Puts(~d, a, lf, N), P1, N, Merges.Merge.all_puts(~d, a, hb, ho, ht, k, rest, l1, h1, P1, lf, hf, N, eall, wa1)),
        hold
      )
      +sb = Equal.trans(
        Maybe<&2, Merges.Work<Vend.L(d)>>,
        Merges.Merge.step(~d, b, hb, ho, ht, k, x, Stable.over(~d, b, Merges.Work{la, hc, P})),
        Merges.Merge.next(~d, b, hb, ho, ht, k, Stable.over(~d, b, Merges.Work{la, hc, P}), Merges.Res.name(x)),
        Some{Stable.over(~d, b, Merges.Work{l1, h1, P1})},
        Merges.Merge.step_eq(~d, b, hb, ho, ht, k, x, Stable.over(~d, b, Merges.Work{la, hc, P})),
        Stable.next(~d, a, b, hb, ho, ht, k, Merges.Work{la, hc, P}, Merges.Res.name(x), Merges.Work{l1, h1, P1}, wa, hold1, g)(en)
      )
      Reads.Affects.cast(
        Maybe<&2, Merges.Work<Vend.L(d)>>,
        z => {Merges.Merge.all(~d, b, hb, ho, ht, k, rest, z) == Some{Stable.over(~d, b, Merges.Work{lf, hf, N})}: Maybe<&2, Merges.Work<Vend.L(d)>>},
        Some{Stable.over(~d, b, Merges.Work{l1, h1, P1})},
        Merges.Merge.step(~d, b, hb, ho, ht, k, x, Stable.over(~d, b, Merges.Work{la, hc, P})),
        Equal.sym(
          Maybe<&2, Merges.Work<Vend.L(d)>>,
          Merges.Merge.step(~d, b, hb, ho, ht, k, x, Stable.over(~d, b, Merges.Work{la, hc, P})),
          Some{Stable.over(~d, b, Merges.Work{l1, h1, P1})},
          sb
        ),
        ih(Merges.Work{l1, h1, P1})(wa1)(hold)(eall)
      )

# the merge of each resource among the keys xs stays, in a ledger that grows
# and holds its nodes
def Stable.all(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  xs: List<&2, List<&2, U32>>,
  w: Merges.Work<Vend.L(d)>,
  Wf: Merges.Work<Vend.L(d)>,
  +wa: Merges.Merge.Puts(~d, a, Merges.Merge.ledger(~d, w), Merges.Merge.nodes(~d, w)),
  +hold: {Depots.Depot.holds(~Vend.L(d), ~(s => x => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, x)), b, Merges.Merge.nodes(~d, Wf)) == True{}: Bool},
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b)
) -> {Merges.Merge.all(~d, a, hb, ho, ht, k, xs, Some{w}) == Some{Wf}: Maybe<&2, Merges.Work<Vend.L(d)>>}
  -> {Merges.Merge.all(~d, b, hb, ho, ht, k, xs, Some{Stable.over(~d, b, w)}) == Some{Stable.over(~d, b, Wf)}: Maybe<&2, Merges.Work<Vend.L(d)>>}:
  match xs w Wf:
    case Nil{} Merges.Work{+l1, +h1, +n1} Merges.Work{+l2, +h2, +n2}:
      e => Equal.cong(
        Merges.Work<Vend.L(d)>,
        Maybe<&2, Merges.Work<Vend.L(d)>>,
        z => Some{Stable.over(~d, b, z)},
        Merges.Work{l1, h1, n1},
        Merges.Work{l2, h2, n2},
        Shared.Maybe.some_inj(Merges.Work<Vend.L(d)>, Merges.Work{l1, h1, n1}, Merges.Work{l2, h2, n2}, e)
      )
    case Con{+x, +rest} Merges.Work{+la, +hc, +P} Merges.Work{+lf, +hf, +N}:
      +e => Stable.all.con(
        ~d,
        a,
        b,
        hb,
        ho,
        ht,
        k,
        x,
        rest,
        la,
        hc,
        P,
        lf,
        hf,
        N,
        wa,
        hold,
        g,
        e,
        Merges.Merge.all_from(~d, a, hb, ho, ht, k, rest, Merges.Merge.step(~d, a, hb, ho, ht, k, x, Merges.Work{la, hc, P}), Merges.Work{lf, hf, N}, e),
        W1 => wa1 => hold2 => e2 => Stable.all(~d, a, b, hb, ho, ht, k, rest, W1, Merges.Work{lf, hf, N}, wa1, hold2, g)(e2)
      )

# Stable.work_kept, once the act is the act of the work
def Stable.work_kept.fin(
  ~d: Vend.Led(),
  +b: Vend.L(d),
  +vs: Maybe<&2, List<&2, String>>,
  +hf: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>,
  +x: Replicas.Act,
  +ex: {Replicas.Act.Taken{vs, hf, ns} == x: Replicas.Act},
  +hb: {Depots.Depot.holds(~Vend.L(d), ~(s => x => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, x)), b, ns) == True{}: Bool}
) -> {Merges.Work.act(~d, vs, Some{Merges.Work{Replicas.Led.puts(~Requests.Ask.machine(), ~d, ns, b), hf, ns}}) == Some{x}: Maybe<&2, Replicas.Act>}:
  %Equal.sym(
    Bool,
    Depots.Depot.holds(~Vend.L(d), ~(s => x => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, x)), Replicas.Led.puts(~Requests.Ask.machine(), ~d, ns, b), ns),
    True{},
    Stable.holds(~d, b, Replicas.Led.puts(~Requests.Ask.machine(), ~d, ns, b), ns, Replicas.Hist.puts(~Requests.Ask.machine(), ~d, ns, b))(hb)
  ): {Shared.Maybe.when(Replicas.Act, _, u => Some{Replicas.Act.Taken{vs, hf, ns}}) == Some{x}: Maybe<&2, Replicas.Act>}
  Equal.cong(Replicas.Act, Maybe<&2, Replicas.Act>, z => Some{z}, Replicas.Act.Taken{vs, hf, ns}, x, ex)

# Stable.work_kept, once the act is known to be the act of the work
def Stable.work_kept.go(
  ~d: Vend.Led(),
  +b: Vend.L(d),
  +vs: Maybe<&2, List<&2, String>>,
  +lf: Vend.L(d),
  +hf: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>,
  -M2: Maybe<&2, Merges.Work<Vend.L(d)>>,
  +x: Replicas.Act,
  +ex: {Replicas.Act.Taken{vs, hf, ns} == x: Replicas.Act},
  hm: {Depots.Depot.holds(~Vend.L(d), ~(s => x => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, x)), b, ns) == True{}: Bool} -> {M2 == Some{Stable.over(~d, b, Merges.Work{lf, hf, ns})}: Maybe<&2, Merges.Work<Vend.L(d)>>},
  +hx: {Replicas.Act.held(~Requests.Ask.machine(), ~d, b, x) == True{}: Bool}
) -> {Merges.Work.act(~d, vs, M2) == Some{x}: Maybe<&2, Replicas.Act>}:
  +hb = Reads.Affects.cast(
    Replicas.Act,
    z => {Replicas.Act.held(~Requests.Ask.machine(), ~d, b, z) == True{}: Bool},
    x,
    Replicas.Act.Taken{vs, hf, ns},
    Equal.sym(Replicas.Act, Replicas.Act.Taken{vs, hf, ns}, x, ex),
    hx
  )
  Reads.Affects.cast(
    Maybe<&2, Merges.Work<Vend.L(d)>>,
    z => {Merges.Work.act(~d, vs, z) == Some{x}: Maybe<&2, Replicas.Act>},
    Some{Stable.over(~d, b, Merges.Work{lf, hf, ns})},
    M2,
    Equal.sym(Maybe<&2, Merges.Work<Vend.L(d)>>, M2, Some{Stable.over(~d, b, Merges.Work{lf, hf, ns})}, hm(hb)),
    Stable.work_kept.fin(~d, b, vs, hf, ns, x, ex, hb)
  )

# Stable.work_kept once the work is known
def Stable.work_kept.at(
  ~d: Vend.Led(),
  +b: Vend.L(d),
  +vs: Maybe<&2, List<&2, String>>,
  +lf: Vend.L(d),
  +hf: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>,
  -M2: Maybe<&2, Merges.Work<Vend.L(d)>>,
  +x: Replicas.Act,
  hm: {Depots.Depot.holds(~Vend.L(d), ~(s => x => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, x)), b, ns) == True{}: Bool} -> {M2 == Some{Stable.over(~d, b, Merges.Work{lf, hf, ns})}: Maybe<&2, Merges.Work<Vend.L(d)>>},
  +hx: {Replicas.Act.held(~Requests.Ask.machine(), ~d, b, x) == True{}: Bool}
) -> {Shared.Maybe.when(Replicas.Act, Depots.Depot.holds(~Vend.L(d), ~(s => x => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, x)), lf, ns), u => Some{Replicas.Act.Taken{vs, hf, ns}}) == Some{x}: Maybe<&2, Replicas.Act>}
  -> {Merges.Work.act(~d, vs, M2) == Some{x}: Maybe<&2, Replicas.Act>}:
  e => Reads.Affects.when_facts(
    Depots.Depot.holds(~Vend.L(d), ~(s => x => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, x)), lf, ns),
    Replicas.Act,
    u => Some{Replicas.Act.Taken{vs, hf, ns}},
    x,
    {Merges.Work.act(~d, vs, M2) == Some{x}: Maybe<&2, Replicas.Act>},
    c => ek => Stable.work_kept.go(
      ~d,
      b,
      vs,
      lf,
      hf,
      ns,
      M2,
      x,
      Shared.Maybe.some_inj(Replicas.Act, Replicas.Act.Taken{vs, hf, ns}, x, ek),
      hm,
      hx
    )
  )(e)

# the act of a work stays, in a ledger that grows and holds the nodes of the
# act, when the work does
def Stable.work_kept(
  ~d: Vend.Led(),
  +b: Vend.L(d),
  +vs: Maybe<&2, List<&2, String>>,
  M: Maybe<&2, Merges.Work<Vend.L(d)>>,
  -M2: Maybe<&2, Merges.Work<Vend.L(d)>>,
  +x: Replicas.Act,
  hm: @W1: Merges.Work<Vend.L(d)> -> {M == Some{W1}: Maybe<&2, Merges.Work<Vend.L(d)>>} -> {Depots.Depot.holds(~Vend.L(d), ~(s => x => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, x)), b, Merges.Merge.nodes(~d, W1)) == True{}: Bool} -> {M2 == Some{Stable.over(~d, b, W1)}: Maybe<&2, Merges.Work<Vend.L(d)>>},
  +hx: {Replicas.Act.held(~Requests.Ask.machine(), ~d, b, x) == True{}: Bool}
) -> {Merges.Work.act(~d, vs, M) == Some{x}: Maybe<&2, Replicas.Act>} -> {Merges.Work.act(~d, vs, M2) == Some{x}: Maybe<&2, Replicas.Act>}:
  match M:
    case None{}:
      e => Empty.absurd({Merges.Work.act(~d, vs, M2) == Some{x}: Maybe<&2, Replicas.Act>}, Shared.Maybe.none_ne_some(Replicas.Act, x, e))
    case Some{Merges.Work{+lf, +hf, +ns}}:
      e => Stable.work_kept.at(~d, b, vs, lf, hf, ns, M2, x, hm(Merges.Work{lf, hf, ns})({==}), hx)(e)

# the work of a resolve stays, in a ledger that grows and holds its nodes,
# once the work after its first write is known
def Stable.resolve_work.at(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +n: Resources.Name,
  +new: Maybe<&2, Requests.Res>,
  +k: Ledgers.Id,
  +cs: List<&2, Resources.Name>,
  +W: Merges.Work<Vend.L(d)>,
  W1: Merges.Work<Vend.L(d)>,
  +e1: {Merges.Work.set(~d, Merges.Work{a, h, []}, Vend.Key.res(n), Vend.Res.value(new)) == Some{W1}: Maybe<&2, Merges.Work<Vend.L(d)>>},
  +e2: {
    Merges.Work.set(~d, W1, Vend.Key.clashes(k), Vend.Clash.value(Shared.List.remove(~Resources.Name, ~Resources.Name.is_eq, cs, n))) == Some{W}: Maybe<&2, Merges.Work<Vend.L(d)>>
  },
  +hold: {Depots.Depot.holds(~Vend.L(d), ~(s => x => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, x)), b, Merges.Merge.nodes(~d, W)) == True{}: Bool},
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b)
) -> {
  Maybe.bind(
    &2,
    Merges.Work<Vend.L(d)>,
    Merges.Work<Vend.L(d)>,
    Merges.Work.set(~d, Merges.Work{b, h, []}, Vend.Key.res(n), Vend.Res.value(new)),
    w => Merges.Work.set(~d, w, Vend.Key.clashes(k), Vend.Clash.value(Shared.List.remove(~Resources.Name, ~Resources.Name.is_eq, cs, n)))
  )
    == Some{Stable.over(~d, b, W)}: Maybe<&2, Merges.Work<Vend.L(d)>>
}:
  match W1:
    case Merges.Work{+l1, +h1, +P1}:
      +wa1 = Stable.puts_of(
        Merges.Merge.Puts(~d, a, l1, P1),
        Merges.Merge.Nodes([], P1),
        Merges.Merge.set_facts(~d, a, a, h, [], Vend.Key.res(n), Vend.Res.value(new), Merges.Work{l1, h1, P1}, e1, {==})
      )
      +hold1 = Stable.holds_prefix(
        ~d,
        b,
        P1,
        Merges.Merge.nodes(~d, W),
        Stable.nodes_of(
          Merges.Merge.Puts(~d, a, Merges.Merge.ledger(~d, W), Merges.Merge.nodes(~d, W)),
          P1,
          Merges.Merge.nodes(~d, W),
          Merges.Merge.set_facts(
            ~d,
            a,
            l1,
            h1,
            P1,
            Vend.Key.clashes(k),
            Vend.Clash.value(Shared.List.remove(~Resources.Name, ~Resources.Name.is_eq, cs, n)),
            W,
            e2,
            wa1
          )
        ),
        hold
      )
      Reads.Affects.cast(
        Maybe<&2, Merges.Work<Vend.L(d)>>,
        z => {
          Maybe.bind(
            &2,
            Merges.Work<Vend.L(d)>,
            Merges.Work<Vend.L(d)>,
            z,
            w => Merges.Work.set(~d, w, Vend.Key.clashes(k), Vend.Clash.value(Shared.List.remove(~Resources.Name, ~Resources.Name.is_eq, cs, n)))
          )
            == Some{Stable.over(~d, b, W)}: Maybe<&2, Merges.Work<Vend.L(d)>>
        },
        Some{Stable.over(~d, b, Merges.Work{l1, h1, P1})},
        Merges.Work.set(~d, Merges.Work{b, h, []}, Vend.Key.res(n), Vend.Res.value(new)),
        Equal.sym(
          Maybe<&2, Merges.Work<Vend.L(d)>>,
          Merges.Work.set(~d, Merges.Work{b, h, []}, Vend.Key.res(n), Vend.Res.value(new)),
          Some{Stable.over(~d, b, Merges.Work{l1, h1, P1})},
          Stable.set(~d, a, b, Merges.Work{a, h, []}, Vend.Key.res(n), Vend.Res.value(new), Merges.Work{l1, h1, P1}, {==}, hold1, g)(e1)
        ),
        Stable.set(
          ~d,
          a,
          b,
          Merges.Work{l1, h1, P1},
          Vend.Key.clashes(k),
          Vend.Clash.value(Shared.List.remove(~Resources.Name, ~Resources.Name.is_eq, cs, n)),
          W,
          wa1,
          hold,
          g
        )(e2)
      )

# the work of a resolve stays, in a ledger that grows and holds its nodes
def Stable.resolve_work(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +n: Resources.Name,
  +new: Maybe<&2, Requests.Res>,
  +k: Ledgers.Id,
  +cs: List<&2, Resources.Name>,
  +W: Merges.Work<Vend.L(d)>,
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b)
) -> {
  Maybe.bind(
    &2,
    Merges.Work<Vend.L(d)>,
    Merges.Work<Vend.L(d)>,
    Merges.Work.set(~d, Merges.Work{a, h, []}, Vend.Key.res(n), Vend.Res.value(new)),
    w => Merges.Work.set(~d, w, Vend.Key.clashes(k), Vend.Clash.value(Shared.List.remove(~Resources.Name, ~Resources.Name.is_eq, cs, n)))
  )
    == Some{W}: Maybe<&2, Merges.Work<Vend.L(d)>>
} -> {Depots.Depot.holds(~Vend.L(d), ~(s => x => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, x)), b, Merges.Merge.nodes(~d, W)) == True{}: Bool} -> {
  Maybe.bind(
    &2,
    Merges.Work<Vend.L(d)>,
    Merges.Work<Vend.L(d)>,
    Merges.Work.set(~d, Merges.Work{b, h, []}, Vend.Key.res(n), Vend.Res.value(new)),
    w => Merges.Work.set(~d, w, Vend.Key.clashes(k), Vend.Clash.value(Shared.List.remove(~Resources.Name, ~Resources.Name.is_eq, cs, n)))
  )
    == Some{Stable.over(~d, b, W)}: Maybe<&2, Merges.Work<Vend.L(d)>>
}:
  eM => +hold => Reads.Affects.bind_some(
    Merges.Work<Vend.L(d)>,
    Merges.Work<Vend.L(d)>,
    {
      Maybe.bind(
        &2,
        Merges.Work<Vend.L(d)>,
        Merges.Work<Vend.L(d)>,
        Merges.Work.set(~d, Merges.Work{b, h, []}, Vend.Key.res(n), Vend.Res.value(new)),
        w => Merges.Work.set(~d, w, Vend.Key.clashes(k), Vend.Clash.value(Shared.List.remove(~Resources.Name, ~Resources.Name.is_eq, cs, n)))
      )
        == Some{Stable.over(~d, b, W)}: Maybe<&2, Merges.Work<Vend.L(d)>>
    },
    Merges.Work.set(~d, Merges.Work{a, h, []}, Vend.Key.res(n), Vend.Res.value(new)),
    w => Merges.Work.set(~d, w, Vend.Key.clashes(k), Vend.Clash.value(Shared.List.remove(~Resources.Name, ~Resources.Name.is_eq, cs, n))),
    W,
    +W1 => e1 => e2 => Stable.resolve_work.at(~d, a, b, h, n, new, k, cs, W, W1, e1, e2, hold, g)
  )(eM)

# a choice by a test that holds, and holds after, gives y when its choice is
# kept, given the test; its other choice gives no y
def Stable.when_test2(
  -R: Type,
  c: Bool,
  -c2: Bool,
  -k: Unit -> R,
  -e: Unit -> R,
  -k2: Unit -> R,
  -e2: Unit -> R,
  -y: R,
  hc: {c == True{}: Bool} -> {c2 == True{}: Bool},
  hk: {c == True{}: Bool} -> {k(Unit{}) == y: R} -> {k2(Unit{}) == y: R},
  he: {e(Unit{}) == y: R} -> Empty
) -> {Shared.Bool.when(R, c, k, e) == y: R} -> {Shared.Bool.when(R, c2, k2, e2) == y: R}:
  match c:
    case True{}:
      h =>
        %Equal.sym(Bool, c2, True{}, hc({==})): {Shared.Bool.when(R, _, k2, e2) == y: R}
        hk({==})(h)
    case False{}:
      h => Empty.absurd({Shared.Bool.when(R, c2, k2, e2) == y: R}, he(h))

# a read that tells gives some value
def Stable.some_of(-A: Data, m: Maybe<&2, A>, -R: Type, k: @v: A -> {m == Some{v}: Maybe<&2, A>} -> R) -> {
  Maybe.is_some(&2, A, m) == True{}: Bool
} -> R:
  match m:
    case None{}:
      h => Empty.absurd(R, Shared.Bool.false_ne_true(h))
    case Some{+v}:
      h => k(v)({==})

# Stable.diff_some once both listings are known
def Stable.diff_some.at(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  -R: Type,
  k: @ks: List<&2, List<&2, U32>> -> {Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, ho, ht) == Some{ks}: Maybe<&2, List<&2, List<&2, U32>>>} -> R,
  po: Sigma<&2, &2, List<&2, Trees.Binding>, bs => {Replicas.Tree.range(~Requests.Ask.machine(), ~d, l, ho, []) == Some{bs}: Maybe<&2, List<&2, Trees.Binding>>}>,
  pt: Sigma<&2, &2, List<&2, Trees.Binding>, bs => {Replicas.Tree.range(~Requests.Ask.machine(), ~d, l, ht, []) == Some{bs}: Maybe<&2, List<&2, Trees.Binding>>}>
) -> R:
  match po pt:
    case Tuple{bs1, e1} Tuple{bs2, e2}:
      Stable.some_of(List<&2, List<&2, U32>>, Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, ho, ht), R, k)(
        Merges.Merge.whole_diff(Vend.L(d), Replicas.Led.tree(Requests.Ask.machine(), d), Merges.Merge.laws_whole(d), l, ho, ht, bs1, bs2, e1, e2)
      )

# two trees that a ledger holds whole have a difference
def Stable.diff_some(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  -R: Type,
  k: @ks: List<&2, List<&2, U32>> -> {Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, ho, ht) == Some{ks}: Maybe<&2, List<&2, List<&2, U32>>>} -> R,
  ko: {Vend.Tree.kept(~d, l, ho) == True{}: Bool},
  kt: {Vend.Tree.kept(~d, l, ht) == True{}: Bool}
) -> R:
  Stable.diff_some.at(~d, l, ho, ht, R, k, Merges.Merge.kept_range(~d, l, ho, ko), Merges.Merge.kept_range(~d, l, ht, kt))

# what a resolve does once its content is known stays as the ledger grows
def Stable.resolve_of(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +t: Replicas.Tip,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +new: Maybe<&2, Requests.Res>,
  +x: Replicas.Act,
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b),
  +hx: {Replicas.Act.held(~Requests.Ask.machine(), ~d, b, x) == True{}: Bool}
) -> {Merges.Resolve.act.of(~d, a, t, k, n, new) == Some{x}: Maybe<&2, Replicas.Act>} -> {Merges.Resolve.act.of(~d, b, t, k, n, new) == Some{x}: Maybe<&2, Replicas.Act>}:
  Shared.Maybe.bind_kept(
    List<&2, Resources.Name>,
    Replicas.Act,
    Vend.Clash.names(~d, a, Replicas.Tip.content(t), k),
    Vend.Clash.names(~d, b, Replicas.Tip.content(t), k),
    +cs => Shared.Bool.when(
      Maybe<&2, Replicas.Act>,
      List.contains(~Resources.Name, ~Resources.Name.is_eq, cs, n),
      u => Shared.Bool.when(
        Maybe<&2, Replicas.Act>,
        Vend.Res.kept(~d, a, new),
        v => Merges.Work.act(
          ~d,
          None{},
          Maybe.bind(
            &2,
            Merges.Work<Vend.L(d)>,
            Merges.Work<Vend.L(d)>,
            Merges.Work.set(~d, Merges.Work{a, Replicas.Tip.content(t), []}, Vend.Key.res(n), Vend.Res.value(new)),
            w => Merges.Work.set(~d, w, Vend.Key.clashes(k), Vend.Clash.value(Shared.List.remove(~Resources.Name, ~Resources.Name.is_eq, cs, n)))
          )
        ),
        v => None{}
      ),
      u => Some{Replicas.Act.Stale{}}
    ),
    +cs => Shared.Bool.when(
      Maybe<&2, Replicas.Act>,
      List.contains(~Resources.Name, ~Resources.Name.is_eq, cs, n),
      u => Shared.Bool.when(
        Maybe<&2, Replicas.Act>,
        Vend.Res.kept(~d, b, new),
        v => Merges.Work.act(
          ~d,
          None{},
          Maybe.bind(
            &2,
            Merges.Work<Vend.L(d)>,
            Merges.Work<Vend.L(d)>,
            Merges.Work.set(~d, Merges.Work{b, Replicas.Tip.content(t), []}, Vend.Key.res(n), Vend.Res.value(new)),
            w => Merges.Work.set(~d, w, Vend.Key.clashes(k), Vend.Clash.value(Shared.List.remove(~Resources.Name, ~Resources.Name.is_eq, cs, n)))
          )
        ),
        v => None{}
      ),
      u => Some{Replicas.Act.Stale{}}
    ),
    x,
    +cs => e => Stable.clash_names(~d, a, b, Replicas.Tip.content(t), k, cs, g)(e),
    +cs => Stable.when_same(
      Maybe<&2, Replicas.Act>,
      List.contains(~Resources.Name, ~Resources.Name.is_eq, cs, n),
      u => Shared.Bool.when(
        Maybe<&2, Replicas.Act>,
        Vend.Res.kept(~d, a, new),
        v => Merges.Work.act(
          ~d,
          None{},
          Maybe.bind(
            &2,
            Merges.Work<Vend.L(d)>,
            Merges.Work<Vend.L(d)>,
            Merges.Work.set(~d, Merges.Work{a, Replicas.Tip.content(t), []}, Vend.Key.res(n), Vend.Res.value(new)),
            w => Merges.Work.set(~d, w, Vend.Key.clashes(k), Vend.Clash.value(Shared.List.remove(~Resources.Name, ~Resources.Name.is_eq, cs, n)))
          )
        ),
        v => None{}
      ),
      u => Some{Replicas.Act.Stale{}},
      u => Shared.Bool.when(
        Maybe<&2, Replicas.Act>,
        Vend.Res.kept(~d, b, new),
        v => Merges.Work.act(
          ~d,
          None{},
          Maybe.bind(
            &2,
            Merges.Work<Vend.L(d)>,
            Merges.Work<Vend.L(d)>,
            Merges.Work.set(~d, Merges.Work{b, Replicas.Tip.content(t), []}, Vend.Key.res(n), Vend.Res.value(new)),
            w => Merges.Work.set(~d, w, Vend.Key.clashes(k), Vend.Clash.value(Shared.List.remove(~Resources.Name, ~Resources.Name.is_eq, cs, n)))
          )
        ),
        v => None{}
      ),
      u => Some{Replicas.Act.Stale{}},
      Some{x},
      c => Stable.when_test(
        Maybe<&2, Replicas.Act>,
        Vend.Res.kept(~d, a, new),
        Vend.Res.kept(~d, b, new),
        v => Merges.Work.act(
          ~d,
          None{},
          Maybe.bind(
            &2,
            Merges.Work<Vend.L(d)>,
            Merges.Work<Vend.L(d)>,
            Merges.Work.set(~d, Merges.Work{a, Replicas.Tip.content(t), []}, Vend.Key.res(n), Vend.Res.value(new)),
            w => Merges.Work.set(~d, w, Vend.Key.clashes(k), Vend.Clash.value(Shared.List.remove(~Resources.Name, ~Resources.Name.is_eq, cs, n)))
          )
        ),
        v => None{},
        v => Merges.Work.act(
          ~d,
          None{},
          Maybe.bind(
            &2,
            Merges.Work<Vend.L(d)>,
            Merges.Work<Vend.L(d)>,
            Merges.Work.set(~d, Merges.Work{b, Replicas.Tip.content(t), []}, Vend.Key.res(n), Vend.Res.value(new)),
            w => Merges.Work.set(~d, w, Vend.Key.clashes(k), Vend.Clash.value(Shared.List.remove(~Resources.Name, ~Resources.Name.is_eq, cs, n)))
          )
        ),
        v => None{},
        Some{x},
        hc => Stable.res_kept(~d, a, b, new, g)(hc),
        Stable.work_kept(
          ~d,
          b,
          None{},
          Maybe.bind(
            &2,
            Merges.Work<Vend.L(d)>,
            Merges.Work<Vend.L(d)>,
            Merges.Work.set(~d, Merges.Work{a, Replicas.Tip.content(t), []}, Vend.Key.res(n), Vend.Res.value(new)),
            w => Merges.Work.set(~d, w, Vend.Key.clashes(k), Vend.Clash.value(Shared.List.remove(~Resources.Name, ~Resources.Name.is_eq, cs, n)))
          ),
          Maybe.bind(
            &2,
            Merges.Work<Vend.L(d)>,
            Merges.Work<Vend.L(d)>,
            Merges.Work.set(~d, Merges.Work{b, Replicas.Tip.content(t), []}, Vend.Key.res(n), Vend.Res.value(new)),
            w => Merges.Work.set(~d, w, Vend.Key.clashes(k), Vend.Clash.value(Shared.List.remove(~Resources.Name, ~Resources.Name.is_eq, cs, n)))
          ),
          x,
          +W => eM => hw => Stable.resolve_work(~d, a, b, Replicas.Tip.content(t), n, new, k, cs, W, g)(eM)(hw),
          hx
        ),
        e => Shared.Maybe.none_ne_some(Replicas.Act, x, e)
      ),
      c => e => e
    )
  )

# what a resolve does stays as the ledger grows
def Stable.resolve(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +t: Replicas.Tip,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +c: Requests.Content,
  +x: Replicas.Act,
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b),
  +hx: {Replicas.Act.held(~Requests.Ask.machine(), ~d, b, x) == True{}: Bool}
) -> {Merges.Resolve.act(~d, a, t, k, n, c) == Some{x}: Maybe<&2, Replicas.Act>} -> {Merges.Resolve.act(~d, b, t, k, n, c) == Some{x}: Maybe<&2, Replicas.Act>}:
  Shared.Maybe.bind_kept(
    Maybe<&2, Requests.Res>,
    Replicas.Act,
    Vend.Content.find(~d, a, t, n, c),
    Vend.Content.find(~d, b, t, n, c),
    new => Merges.Resolve.act.of(~d, a, t, k, n, new),
    new => Merges.Resolve.act.of(~d, b, t, k, n, new),
    x,
    +new => e => Stable.content(~d, a, b, t, n, c, new, g)(e),
    +new => e => Stable.resolve_of(~d, a, b, t, k, n, new, x, g, hx)(e)
  )

# Stable.merge once the difference ks of the trees is known
def Stable.merge.go(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +ks: List<&2, List<&2, U32>>,
  +eks: {Replicas.Tree.diff(~Requests.Ask.machine(), ~d, a, ho, ht) == Some{ks}: Maybe<&2, List<&2, List<&2, U32>>>},
  +x: Replicas.Act,
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b),
  +hx: {Replicas.Act.held(~Requests.Ask.machine(), ~d, b, x) == True{}: Bool}
) -> {
  Merges.Work.act(
    ~d,
    None{},
    Merges.Merge.all(
      ~d,
      a,
      hb,
      ho,
      ht,
      k,
      Maybe.default(&2, List<&2, List<&2, U32>>, Replicas.Tree.diff(~Requests.Ask.machine(), ~d, a, ho, ht), []),
      Some{Merges.Work{a, ho, []}}
    )
  )
    == Some{x}: Maybe<&2, Replicas.Act>
} -> {
  Merges.Work.act(
    ~d,
    None{},
    Merges.Merge.all(
      ~d,
      b,
      hb,
      ho,
      ht,
      k,
      Maybe.default(&2, List<&2, List<&2, U32>>, Replicas.Tree.diff(~Requests.Ask.machine(), ~d, b, ho, ht), []),
      Some{Merges.Work{b, ho, []}}
    )
  )
    == Some{x}: Maybe<&2, Replicas.Act>
}:
  e => Reads.Affects.cast(
    Maybe<&2, List<&2, List<&2, U32>>>,
    z => {
      Merges.Work.act(~d, None{}, Merges.Merge.all(~d, b, hb, ho, ht, k, Maybe.default(&2, List<&2, List<&2, U32>>, z, []), Some{Merges.Work{b, ho, []}}))
        == Some{x}: Maybe<&2, Replicas.Act>
    },
    Some{ks},
    Replicas.Tree.diff(~Requests.Ask.machine(), ~d, b, ho, ht),
    Equal.sym(
      Maybe<&2, List<&2, List<&2, U32>>>,
      Replicas.Tree.diff(~Requests.Ask.machine(), ~d, b, ho, ht),
      Some{ks},
      Stable.diff_grows(~d, a, b, ho, ht, ks, g)(eks)
    ),
    Stable.work_kept(
      ~d,
      b,
      None{},
      Merges.Merge.all(~d, a, hb, ho, ht, k, ks, Some{Merges.Work{a, ho, []}}),
      Merges.Merge.all(~d, b, hb, ho, ht, k, ks, Some{Merges.Work{b, ho, []}}),
      x,
      +W => eM => hw => Stable.all(~d, a, b, hb, ho, ht, k, ks, Merges.Work{a, ho, []}, W, {==}, hw, g)(eM),
      hx
    )(
      Reads.Affects.cast(
        Maybe<&2, List<&2, List<&2, U32>>>,
        z => {
          Merges.Work.act(~d, None{}, Merges.Merge.all(~d, a, hb, ho, ht, k, Maybe.default(&2, List<&2, List<&2, U32>>, z, []), Some{Merges.Work{a, ho, []}}))
            == Some{x}: Maybe<&2, Replicas.Act>
        },
        Replicas.Tree.diff(~Requests.Ask.machine(), ~d, a, ho, ht),
        Some{ks},
        eks,
        e
      )
    )
  )

# what a merge does stays as the ledger grows
def Stable.merge(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +t: Replicas.Tip,
  +k: Ledgers.Id,
  +from: Requests.Source,
  +base: Maybe<&2, Requests.Source>,
  +x: Replicas.Act,
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b),
  +hx: {Replicas.Act.held(~Requests.Ask.machine(), ~d, b, x) == True{}: Bool}
) -> {Merges.Merge.act(~d, a, t, k, from, base) == Some{x}: Maybe<&2, Replicas.Act>} -> {Merges.Merge.act(~d, b, t, k, from, base) == Some{x}: Maybe<&2, Replicas.Act>}:
  +ho = Replicas.Tip.content(t)
  +ht = Vend.Source.root(from)
  +hb = Merges.Base.tree(base)
  Stable.when_test2(
    Maybe<&2, Replicas.Act>,
    List.all.if(u => List.all.if(u2 => Vend.Tree.kept(~d, a, ho), Vend.Tree.kept(~d, a, hb)), Vend.Tree.kept(~d, a, ht)),
    List.all.if(u => List.all.if(u2 => Vend.Tree.kept(~d, b, ho), Vend.Tree.kept(~d, b, hb)), Vend.Tree.kept(~d, b, ht)),
    u => Merges.Work.act(
      ~d,
      None{},
      Merges.Merge.all(~d, a, hb, ho, ht, k, Maybe.default(&2, List<&2, List<&2, U32>>, Replicas.Tree.diff(~Requests.Ask.machine(), ~d, a, ho, ht), []), Some{Merges.Work{a, ho, []}})
    ),
    u => None{},
    u => Merges.Work.act(
      ~d,
      None{},
      Merges.Merge.all(~d, b, hb, ho, ht, k, Maybe.default(&2, List<&2, List<&2, U32>>, Replicas.Tree.diff(~Requests.Ask.machine(), ~d, b, ho, ht), []), Some{Merges.Work{b, ho, []}})
    ),
    u => None{},
    Some{x},
    +c => Shared.List.all.if_both(
      Vend.Tree.kept(~d, b, ht),
      u => List.all.if(u2 => Vend.Tree.kept(~d, b, ho), Vend.Tree.kept(~d, b, hb))
    )(
      Stable.tree_kept(~d, a, b, ht, g)(
        Shared.List.all.if_hit(Vend.Tree.kept(~d, a, ht), u => List.all.if(u2 => Vend.Tree.kept(~d, a, ho), Vend.Tree.kept(~d, a, hb)))(c)
      )
    )(
      Shared.List.all.if_both(Vend.Tree.kept(~d, b, hb), u2 => Vend.Tree.kept(~d, b, ho))(
        Stable.tree_kept(~d, a, b, hb, g)(
          Shared.List.all.if_hit(Vend.Tree.kept(~d, a, hb), u2 => Vend.Tree.kept(~d, a, ho))(
            Shared.List.all.if_rest(Vend.Tree.kept(~d, a, ht), u => List.all.if(u2 => Vend.Tree.kept(~d, a, ho), Vend.Tree.kept(~d, a, hb)))(c)
          )
        )
      )(
        Stable.tree_kept(~d, a, b, ho, g)(
          Shared.List.all.if_rest(Vend.Tree.kept(~d, a, hb), u2 => Vend.Tree.kept(~d, a, ho))(
            Shared.List.all.if_rest(Vend.Tree.kept(~d, a, ht), u => List.all.if(u2 => Vend.Tree.kept(~d, a, ho), Vend.Tree.kept(~d, a, hb)))(c)
          )
        )
      )
    ),
    +c => e => Stable.diff_some(
      ~d,
      a,
      ho,
      ht,
      {
        Merges.Work.act(
          ~d,
          None{},
          Merges.Merge.all(~d, b, hb, ho, ht, k, Maybe.default(&2, List<&2, List<&2, U32>>, Replicas.Tree.diff(~Requests.Ask.machine(), ~d, b, ho, ht), []), Some{Merges.Work{b, ho, []}})
        )
          == Some{x}: Maybe<&2, Replicas.Act>
      },
      +ks => eks => Stable.merge.go(~d, a, b, hb, ho, ht, k, ks, eks, x, g, hx)(e),
      Shared.List.all.if_rest(Vend.Tree.kept(~d, a, hb), u2 => Vend.Tree.kept(~d, a, ho))(
        Shared.List.all.if_rest(Vend.Tree.kept(~d, a, ht), u => List.all.if(u2 => Vend.Tree.kept(~d, a, ho), Vend.Tree.kept(~d, a, hb)))(c)
      ),
      Shared.List.all.if_hit(Vend.Tree.kept(~d, a, ht), u => List.all.if(u2 => Vend.Tree.kept(~d, a, ho), Vend.Tree.kept(~d, a, hb)))(c)
    ),
    e => Shared.Maybe.none_ne_some(Replicas.Act, x, e)
  )

# what a change does stays as the ledger grows
def Stable.change(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +t: Replicas.Tip,
  bo: Maybe<&2, String>,
  +i: Ledgers.Id,
  ch: Requests.Change,
  +x: Replicas.Act,
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b),
  +hx: {Replicas.Act.held(~Requests.Ask.machine(), ~d, b, x) == True{}: Bool}
) -> {Owners.Change.act(~d, a, t, bo, i, ch) == Some{x}: Maybe<&2, Replicas.Act>} -> {Owners.Change.act(~d, b, t, bo, i, ch) == Some{x}: Maybe<&2, Replicas.Act>}:
  match bo ch:
    case Some{y} Requests.Change.Write{+n, +base, +c}:
      Stable.write(~d, a, b, t, n, base, c, x, g)
    case Some{y} Requests.Change.Resolve{+k, +n, +c}:
      Stable.resolve(~d, a, b, t, k, n, c, x, g, hx)
    case Some{y} Requests.Change.Merge{+from, +base}:
      Stable.merge(~d, a, b, t, i, from, base, x, g, hx)
    case Some{y} Requests.Change.Move{+to}:
      Stable.move(~d, a, b, to, x, g)
    case Some{y} Requests.Change.Mark{m, text}:
      e => e
    case Some{y} Requests.Change.Branch{n, at}:
      e => e
    case Some{y} Requests.Change.Group{gn, ms}:
      e => e
    case Some{y} Requests.Change.Key{n, k}:
      e => e
    case Some{y} Requests.Change.Own{+gn, +at, +os}:
      Stable.own(~d, a, b, t, gn, at, os, x, g)
    case None{} Requests.Change.Branch{+n, +at}:
      Stable.branch(~d, a, b, t, n, at, x, g)
    case None{} Requests.Change.Group{+gn, +ms}:
      Stable.group(~d, a, b, t, gn, ms, x, g)
    case None{} Requests.Change.Key{+n, +k}:
      Stable.key(~d, a, b, t, n, k, x, g)
    case None{} Requests.Change.Own{+gn, +at, +os}:
      Stable.own(~d, a, b, t, gn, at, os, x, g)
    case None{} Requests.Change.Write{n, base, c}:
      e => e
    case None{} Requests.Change.Resolve{k, n, c}:
      e => e
    case None{} Requests.Change.Merge{from, base}:
      e => e
    case None{} Requests.Change.Move{to}:
      e => e
    case None{} Requests.Change.Mark{m, text}:
      e => e

# what a request does stays as the ledger grows
def Stable.ask(
  ~d: Vend.Led(),
  +a: Vend.L(d),
  +b: Vend.L(d),
  +t: Replicas.Tip,
  +c: Ledgers.Line,
  +i: Ledgers.Id,
  q: Requests.Ask,
  +x: Replicas.Act,
  +g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b),
  +hx: {Replicas.Act.held(~Requests.Ask.machine(), ~d, b, x) == True{}: Bool}
) -> {Owners.Ask.act(~d, a, t, c, i, q) == Some{x}: Maybe<&2, Replicas.Act>} -> {Owners.Ask.act(~d, b, t, c, i, q) == Some{x}: Maybe<&2, Replicas.Act>}:
  match q:
    case Requests.Ask.Start{vs}:
      e => e
    case Requests.Ask.On{+st, +bo, +ch}:
      Stable.when_same(
        Maybe<&2, Replicas.Act>,
        Ledgers.Line.is_eq(Ledgers.Line{st, bo}, c),
        u => Owners.Change.act(~d, a, t, bo, i, ch),
        u => Some{Replicas.Act.Stale{}},
        u => Owners.Change.act(~d, b, t, bo, i, ch),
        u => Some{Replicas.Act.Stale{}},
        Some{x},
        cc => e => Stable.change(~d, a, b, t, bo, i, ch, x, g, hx)(e),
        cc => e => e
      )

def Ask.act_stable(d):
  +t => +c => +i => +q => +a => +b => +x => +g => e => +hx => Stable.ask(~d, a, b, t, c, i, q, x, g, hx)(e)

# writers are told only about changes to what their work uses: each touch
# that Node.affects gives for a branch holds (Touch.holds)
law Node.affects_holds:
  for ~d: Vend.Led()
  for ~kern: Vend.Kern(d)
  for l: Vend.L(d)
  for view: List<&2, Formats.Cond>
  for b: Vend.Branch
  for ts: List<&2, Reads.Touch>
  for x: Reads.Touch
  {Reads.Node.affects(~d, ~kern, l, view, b) == Some{ts}: Maybe<&2, List<&2, Reads.Touch>>}
    -> {List.contains(~Reads.Touch, ~Reads.Touch.is_eq, ts, x) == True{}: Bool}
    -> {Reads.Touch.holds(~d, ~kern, l, view, x) == Some{True{}}: Maybe<&2, Bool>}

def Node.affects_holds(d, kern, l, view, b, ts, x):
  Reads.Affects.holds_law(~d, ~kern, l, view, b, ts, x)

# and they are told about each of them: a touch that holds is among the
# touches that Node.affects gives for its branch
law Node.affects_complete:
  for ~d: Vend.Led()
  for ~kern: Vend.Kern(d)
  for l: Vend.L(d)
  for view: List<&2, Formats.Cond>
  for x: Reads.Touch
  for ts: List<&2, Reads.Touch>
  {Reads.Touch.holds(~d, ~kern, l, view, x) == Some{True{}}: Maybe<&2, Bool>}
    -> {Reads.Node.affects(~d, ~kern, l, view, Reads.Touch.branch(x)) == Some{ts}: Maybe<&2, List<&2, Reads.Touch>>}
    -> {List.contains(~Reads.Touch, ~Reads.Touch.is_eq, ts, x) == True{}: Bool}

def Node.affects_complete(d, kern, l, view, x, ts):
  Reads.Affects.complete_law(~d, ~kern, l, view, x, ts)
