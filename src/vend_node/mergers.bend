import Base
import ../shared/shared/ledger.bend as Ledgers
import ../shared/shared/shared/shared/code.bend as Codes
import ../shared/shared/shared/shared/crit.bend as Crits
import ../shared/shared/shared/shared/crit_order.bend as Orders
import ../shared/shared/shared/shared/shared.bend as Shared
import ./codes.bend as Coded
import ./reads.bend as Reads
import ./run/known.bend as RKnown
import ./shared/lists.bend as Lists
import ./spec.bend as Spec
import ./types.bend as Types

# Lines of merges: laws
# ---------------------
# The line of each merge by its id (run/known.bend, Mergers) is what a walk of
# the facts reads (Mergers.get_line), and a fact that joins the facts changes
# it by one write of the map, unless it is a merge of an id that the map holds
# a line for (Mergers.of_insert).

# the line m, unless the request r of the id j is a merge and the key of j is
# q: then the line of the merge
def Request.keyed(r: Spec.Request, j: Ledgers.Id, q: List<&2, U32>, m: Maybe<&2, Ledgers.Line>) -> Maybe<&2, Ledgers.Line>:
  match r:
    case Spec.Request.Merge{ff, x}:
      Bool.pick(Maybe<&2, Ledgers.Line>, Crits.Key.is_eq(q, RKnown.Id.code(j)), Some{x}, m)
    case _:
      m

# the line m, unless the fact f is the ask of a merge of an id of the key q:
# then the line of the merge
def Fact.keyed(f: Types.Fact, q: List<&2, U32>, m: Maybe<&2, Ledgers.Line>) -> Maybe<&2, Ledgers.Line>:
  match f:
    case Types.Fact.Vote{v, st, x}:
      m
    case Types.Fact.Ask{Types.Ask{j, k, r}}:
      Request.keyed(r, j, q, m)

# the line of the first merge among fs whose id has the key q
def Line.keyed(fs: List<&2, Types.Fact>, +q: List<&2, U32>) -> Maybe<&2, Ledgers.Line>:
  match fs:
    case Nil{}:
      None{}
    case Con{f, rest}:
      Fact.keyed(f, q, Line.keyed(rest, q))

# one of Some and m is None only when it is m
def Pick.cond(c: Bool, -x: Ledgers.Line, -m: Maybe<&2, Ledgers.Line>) -> {Bool.pick(Maybe<&2, Ledgers.Line>, c, Some{x}, m) == None{}: Maybe<&2, Ledgers.Line>} -> {c == False{}: Bool}:
  match c:
    case True{}:
      h => Empty.absurd({True{} == False{}: Bool}, Crits.Crit.some_ne_none(Ledgers.Line, x, h))
    case False{}:
      h => {==}

# one of Some and m that is None is m, which is None
def Pick.rest(c: Bool, -x: Ledgers.Line, -m: Maybe<&2, Ledgers.Line>) -> {Bool.pick(Maybe<&2, Ledgers.Line>, c, Some{x}, m) == None{}: Maybe<&2, Ledgers.Line>} -> {m == None{}: Maybe<&2, Ledgers.Line>}:
  match c:
    case True{}:
      h => Empty.absurd({m == None{}: Maybe<&2, Ledgers.Line>}, Crits.Crit.some_ne_none(Ledgers.Line, x, h))
    case False{}:
      h => h

# one of Some and None that is Some is the Some
def Pick.hit(c: Bool, -x: Ledgers.Line, -y: Ledgers.Line) -> {Bool.pick(Maybe<&2, Ledgers.Line>, c, Some{x}, None{}) == Some{y}: Maybe<&2, Ledgers.Line>} -> {c == True{}: Bool}:
  match c:
    case True{}:
      h => {==}
    case False{}:
      h => Empty.absurd({False{} == True{}: Bool}, Shared.Maybe.none_ne_some(Ledgers.Line, y, h))

# one of Some and None, else m, is one of the Some and m
def Pick.or(c: Bool, -x: Ledgers.Line, -m: Maybe<&2, Ledgers.Line>) -> {
  Maybe.or(&2, Ledgers.Line, Bool.pick(Maybe<&2, Ledgers.Line>, c, Some{x}, None{}), m) == Bool.pick(Maybe<&2, Ledgers.Line>, c, Some{x}, m): Maybe<&2, Ledgers.Line>
}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

# a request that gives no line of the key q gives the line that it is given
def Request.keyed_pass(r: Spec.Request, j: Ledgers.Id, q: List<&2, U32>, m: Maybe<&2, Ledgers.Line>) -> {
  Request.keyed(r, j, q, None{}) == None{}: Maybe<&2, Ledgers.Line>
} -> {Request.keyed(r, j, q, m) == m: Maybe<&2, Ledgers.Line>}:
  match r:
    case Spec.Request.Start{os}:
      h => {==}
    case Spec.Request.Write{b, p, w}:
      h => {==}
    case Spec.Request.Merge{ff, +x}:
      h => Reads.Eq.back(Bool, d => {Bool.pick(Maybe<&2, Ledgers.Line>, d, Some{x}, m) == m: Maybe<&2, Ledgers.Line>}, Crits.Key.is_eq(q, RKnown.Id.code(j)), False{}, Pick.cond(Crits.Key.is_eq(q, RKnown.Id.code(j)), x, None{})(h), {==})
    case Spec.Request.Resolve{mm, p, w}:
      h => {==}
    case Spec.Request.Mark{b, mk, v}:
      h => {==}
    case Spec.Request.Move{b, t, v}:
      h => {==}
    case Spec.Request.Group{hh, gg, ms}:
      h => {==}
    case Spec.Request.Own{cc, gg}:
      h => {==}

# a fact that gives no line of the key q gives the line that it is given
def Fact.keyed_pass(f: Types.Fact, q: List<&2, U32>, m: Maybe<&2, Ledgers.Line>) -> {
  Fact.keyed(f, q, None{}) == None{}: Maybe<&2, Ledgers.Line>
} -> {Fact.keyed(f, q, m) == m: Maybe<&2, Ledgers.Line>}:
  match f:
    case Types.Fact.Vote{v, st, x}:
      h => {==}
    case Types.Fact.Ask{Types.Ask{j, k, r}}:
      h => Request.keyed_pass(r, j, q, m)(h)

# a request gives no line only when it is given none
def Request.keyed_none(r: Spec.Request, j: Ledgers.Id, q: List<&2, U32>, m: Maybe<&2, Ledgers.Line>) -> {
  Request.keyed(r, j, q, m) == None{}: Maybe<&2, Ledgers.Line>
} -> {m == None{}: Maybe<&2, Ledgers.Line>}:
  match r:
    case Spec.Request.Start{os}:
      h => h
    case Spec.Request.Write{b, p, w}:
      h => h
    case Spec.Request.Merge{ff, x}:
      h => Pick.rest(Crits.Key.is_eq(q, RKnown.Id.code(j)), x, m)(h)
    case Spec.Request.Resolve{mm, p, w}:
      h => h
    case Spec.Request.Mark{b, mk, v}:
      h => h
    case Spec.Request.Move{b, t, v}:
      h => h
    case Spec.Request.Group{hh, gg, ms}:
      h => h
    case Spec.Request.Own{cc, gg}:
      h => h

# a fact gives no line only when it is given none
def Fact.keyed_none(f: Types.Fact, q: List<&2, U32>, m: Maybe<&2, Ledgers.Line>) -> {
  Fact.keyed(f, q, m) == None{}: Maybe<&2, Ledgers.Line>
} -> {m == None{}: Maybe<&2, Ledgers.Line>}:
  match f:
    case Types.Fact.Vote{v, st, x}:
      h => h
    case Types.Fact.Ask{Types.Ask{j, k, r}}:
      h => Request.keyed_none(r, j, q, m)(h)

# a request that gives no line gives none when it is given none
def Request.keyed_out(r: Spec.Request, j: Ledgers.Id, q: List<&2, U32>, m: Maybe<&2, Ledgers.Line>) -> {
  Request.keyed(r, j, q, m) == None{}: Maybe<&2, Ledgers.Line>
} -> {Request.keyed(r, j, q, None{}) == None{}: Maybe<&2, Ledgers.Line>}:
  match r:
    case Spec.Request.Start{os}:
      h => {==}
    case Spec.Request.Write{b, p, w}:
      h => {==}
    case Spec.Request.Merge{ff, +x}:
      h => Reads.Eq.back(Bool, d => {Bool.pick(Maybe<&2, Ledgers.Line>, d, Some{x}, None{}) == None{}: Maybe<&2, Ledgers.Line>}, Crits.Key.is_eq(q, RKnown.Id.code(j)), False{}, Pick.cond(Crits.Key.is_eq(q, RKnown.Id.code(j)), x, m)(h), {==})
    case Spec.Request.Resolve{mm, p, w}:
      h => {==}
    case Spec.Request.Mark{b, mk, v}:
      h => {==}
    case Spec.Request.Move{b, t, v}:
      h => {==}
    case Spec.Request.Group{hh, gg, ms}:
      h => {==}
    case Spec.Request.Own{cc, gg}:
      h => {==}

# a fact that gives no line gives none when it is given none
def Fact.keyed_out(f: Types.Fact, q: List<&2, U32>, m: Maybe<&2, Ledgers.Line>) -> {
  Fact.keyed(f, q, m) == None{}: Maybe<&2, Ledgers.Line>
} -> {Fact.keyed(f, q, None{}) == None{}: Maybe<&2, Ledgers.Line>}:
  match f:
    case Types.Fact.Vote{v, st, x}:
      h => {==}
    case Types.Fact.Ask{Types.Ask{j, k, r}}:
      h => Request.keyed_out(r, j, q, m)(h)

# the line of a request, else m, is what the request gives when it is given m
def Request.keyed_or(r: Spec.Request, j: Ledgers.Id, q: List<&2, U32>, m: Maybe<&2, Ledgers.Line>) -> {
  Maybe.or(&2, Ledgers.Line, Request.keyed(r, j, q, None{}), m) == Request.keyed(r, j, q, m): Maybe<&2, Ledgers.Line>
}:
  match r:
    case Spec.Request.Start{os}:
      {==}
    case Spec.Request.Write{b, p, w}:
      {==}
    case Spec.Request.Merge{ff, x}:
      Pick.or(Crits.Key.is_eq(q, RKnown.Id.code(j)), x, m)
    case Spec.Request.Resolve{mm, p, w}:
      {==}
    case Spec.Request.Mark{b, mk, v}:
      {==}
    case Spec.Request.Move{b, t, v}:
      {==}
    case Spec.Request.Group{hh, gg, ms}:
      {==}
    case Spec.Request.Own{cc, gg}:
      {==}

# the line of a fact, else m, is what the fact gives when it is given m
def Fact.keyed_or(f: Types.Fact, q: List<&2, U32>, m: Maybe<&2, Ledgers.Line>) -> {
  Maybe.or(&2, Ledgers.Line, Fact.keyed(f, q, None{}), m) == Fact.keyed(f, q, m): Maybe<&2, Ledgers.Line>
}:
  match f:
    case Types.Fact.Vote{v, st, x}:
      {==}
    case Types.Fact.Ask{Types.Ask{j, k, r}}:
      Request.keyed_or(r, j, q, m)

# a fact that gives no line of the key q, put among the facts xs, leaves the
# line of the key q as it was
def Line.keyed_insert_pass(xs: List<&2, Types.Fact>, +f: Types.Fact, +q: List<&2, U32>) -> {
  Fact.keyed(f, q, None{}) == None{}: Maybe<&2, Ledgers.Line>
} -> {Line.keyed(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, xs, f), q) == Line.keyed(xs, q): Maybe<&2, Ledgers.Line>}:
  match xs:
    case Nil{}:
      h => h
    case Con{+y, +r}:
      +h => Lists.Bool.by(
        d => {Line.keyed(Shared.Bool.when(List<&2, Types.Fact>, d, u => f <> y <> r, u => Shared.Bool.when(List<&2, Types.Fact>, Crits.Key.is_eq(Coded.Fact.words(y), Coded.Fact.words(f)), u => f <> r, u => y <> Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, r, f))), q) == Line.keyed(y <> r, q): Maybe<&2, Ledgers.Line>},
        Orders.Key.lt(Coded.Fact.words(f), Coded.Fact.words(y)),
        et => Fact.keyed_pass(f, q, Line.keyed(y <> r, q))(h),
        ef => Lists.Bool.by(
          d2 => {Line.keyed(Shared.Bool.when(List<&2, Types.Fact>, d2, u => f <> r, u => y <> Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, r, f)), q) == Line.keyed(y <> r, q): Maybe<&2, Ledgers.Line>},
          Crits.Key.is_eq(Coded.Fact.words(y), Coded.Fact.words(f)),
          e2 => Reads.Eq.back(
            Types.Fact,
            z => {Line.keyed(f <> r, q) == Line.keyed(z <> r, q): Maybe<&2, Ledgers.Line>},
            y,
            f,
            Coded.Fact.words_inj(y, f)(Crits.Key.is_eq_sound(Coded.Fact.words(y), Coded.Fact.words(f))(e2)),
            {==}
          ),
          e2 => Equal.cong(
            Maybe<&2, Ledgers.Line>,
            Maybe<&2, Ledgers.Line>,
            m => Fact.keyed(y, q, m),
            Line.keyed(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, r, f), q),
            Line.keyed(r, q),
            Line.keyed_insert_pass(r, f, q)(h)
          )
        )
      )

# a fact put among facts that hold no line of the key q gives the line of q
def Line.keyed_insert_new(xs: List<&2, Types.Fact>, +f: Types.Fact, +q: List<&2, U32>) -> {
  Line.keyed(xs, q) == None{}: Maybe<&2, Ledgers.Line>
} -> {Line.keyed(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, xs, f), q) == Fact.keyed(f, q, None{}): Maybe<&2, Ledgers.Line>}:
  match xs:
    case Nil{}:
      h => {==}
    case Con{+y, +r}:
      +h => Lists.Bool.by(
        d => {Line.keyed(Shared.Bool.when(List<&2, Types.Fact>, d, u => f <> y <> r, u => Shared.Bool.when(List<&2, Types.Fact>, Crits.Key.is_eq(Coded.Fact.words(y), Coded.Fact.words(f)), u => f <> r, u => y <> Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, r, f))), q) == Fact.keyed(f, q, None{}): Maybe<&2, Ledgers.Line>},
        Orders.Key.lt(Coded.Fact.words(f), Coded.Fact.words(y)),
        et => Equal.cong(Maybe<&2, Ledgers.Line>, Maybe<&2, Ledgers.Line>, m => Fact.keyed(f, q, m), Line.keyed(y <> r, q), None{}, h),
        ef => Lists.Bool.by(
          d2 => {Line.keyed(Shared.Bool.when(List<&2, Types.Fact>, d2, u => f <> r, u => y <> Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, r, f)), q) == Fact.keyed(f, q, None{}): Maybe<&2, Ledgers.Line>},
          Crits.Key.is_eq(Coded.Fact.words(y), Coded.Fact.words(f)),
          e2 => Equal.cong(
            Maybe<&2, Ledgers.Line>,
            Maybe<&2, Ledgers.Line>,
            m => Fact.keyed(f, q, m),
            Line.keyed(r, q),
            None{},
            Fact.keyed_none(y, q, Line.keyed(r, q))(h)
          ),
          e2 => Equal.trans(
            Maybe<&2, Ledgers.Line>,
            Fact.keyed(y, q, Line.keyed(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, r, f), q)),
            Fact.keyed(y, q, Fact.keyed(f, q, None{})),
            Fact.keyed(f, q, None{}),
            Equal.cong(
              Maybe<&2, Ledgers.Line>,
              Maybe<&2, Ledgers.Line>,
              m => Fact.keyed(y, q, m),
              Line.keyed(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, r, f), q),
              Fact.keyed(f, q, None{}),
              Line.keyed_insert_new(r, f, q)(Fact.keyed_none(y, q, Line.keyed(r, q))(h))
            ),
            Fact.keyed_pass(y, q, Fact.keyed(f, q, None{}))(Fact.keyed_out(y, q, Line.keyed(r, q))(h))
          )
        )
      )

# Well formed lines
# -----------------

# a request keeps the lines of merges well formed
def Mergers.put_wf(+mx: Crits.Crit<Ledgers.Line>, i: Ledgers.Id, r: Spec.Request) -> {
  Crits.Crit.wf(~Ledgers.Line, mx, 0n) == True{}: Bool
} -> {Crits.Crit.wf(~Ledgers.Line, RKnown.Mergers.put(mx, i, r), 0n) == True{}: Bool}:
  match r:
    case Spec.Request.Start{os}:
      h => h
    case Spec.Request.Write{b, p, w}:
      h => h
    case Spec.Request.Merge{ff, x}:
      h => Crits.Crit.upsert_wf(~Ledgers.Line, ~RKnown.Line.first, mx, RKnown.Id.code(i), x)(h)
    case Spec.Request.Resolve{mm, p, w}:
      h => h
    case Spec.Request.Mark{b, mk, v}:
      h => h
    case Spec.Request.Move{b, t, v}:
      h => h
    case Spec.Request.Group{hh, gg, ms}:
      h => h
    case Spec.Request.Own{cc, gg}:
      h => h

# a fact keeps the lines of merges well formed
def Mergers.step_wf(+mx: Crits.Crit<Ledgers.Line>, f: Types.Fact) -> {
  Crits.Crit.wf(~Ledgers.Line, mx, 0n) == True{}: Bool
} -> {Crits.Crit.wf(~Ledgers.Line, RKnown.Mergers.step(mx, f), 0n) == True{}: Bool}:
  match f:
    case Types.Fact.Vote{v, st, x}:
      h => h
    case Types.Fact.Ask{Types.Ask{j, k, r}}:
      h => Mergers.put_wf(mx, j, r)(h)

# facts keep the lines of merges well formed
def Mergers.go_wf(fs: List<&2, Types.Fact>, +mx: Crits.Crit<Ledgers.Line>) -> {
  Crits.Crit.wf(~Ledgers.Line, mx, 0n) == True{}: Bool
} -> {Crits.Crit.wf(~Ledgers.Line, RKnown.Mergers.go(fs, mx), 0n) == True{}: Bool}:
  match fs:
    case Nil{}:
      h => h
    case Con{+f, rest}:
      h => Mergers.go_wf(rest, RKnown.Mergers.step(mx, f))(Mergers.step_wf(mx, f)(h))

# the lines of the merges of facts are well formed
def Mergers.of_wf(fs: List<&2, Types.Fact>) -> {Crits.Crit.wf(~Ledgers.Line, RKnown.Mergers.of(fs), 0n) == True{}: Bool}:
  Mergers.go_wf(fs, Crits.Crit.new(Ledgers.Line))(Crits.Crit.new_wf(~Ledgers.Line))

# What the lines hold
# -------------------

# the line that a map holds for a key after a write that keeps the old line:
# the line that it held, else the new one
def First.kept(e: Maybe<&2, Ledgers.Line>, -x: Ledgers.Line) -> {
  Some{Crits.Crit.merge(~Ledgers.Line, ~RKnown.Line.first, e, x)} == Maybe.or(&2, Ledgers.Line, e, Some{x}): Maybe<&2, Ledgers.Line>
}:
  match e:
    case None{}:
      {==}
    case Some{y}:
      {==}

# what the lines hold under the key q after the line x is put for the id i,
# unless they hold one
def Mergers.merge_lookup(+mx: Crits.Crit<Ledgers.Line>, +i: Ledgers.Id, +x: Ledgers.Line, +q: List<&2, U32>) -> {
  Crits.Crit.wf(~Ledgers.Line, mx, 0n) == True{}: Bool
} -> {
  Crits.Crit.lookup(Ledgers.Line, Crits.Crit.upsert(~Ledgers.Line, ~RKnown.Line.first, mx, RKnown.Id.code(i), x), q)
    == Maybe.or(&2, Ledgers.Line, Crits.Crit.lookup(Ledgers.Line, mx, q), Bool.pick(Maybe<&2, Ledgers.Line>, Crits.Key.is_eq(q, RKnown.Id.code(i)), Some{x}, None{})): Maybe<&2, Ledgers.Line>
}:
  h => Equal.trans(
    Maybe<&2, Ledgers.Line>,
    Crits.Crit.lookup(Ledgers.Line, Crits.Crit.upsert(~Ledgers.Line, ~RKnown.Line.first, mx, RKnown.Id.code(i), x), q),
    Bool.pick(Maybe<&2, Ledgers.Line>, Crits.Key.is_eq(q, RKnown.Id.code(i)), Some{Crits.Crit.merge(~Ledgers.Line, ~RKnown.Line.first, Crits.Crit.lookup(Ledgers.Line, mx, RKnown.Id.code(i)), x)}, Crits.Crit.lookup(Ledgers.Line, mx, q)),
    Maybe.or(&2, Ledgers.Line, Crits.Crit.lookup(Ledgers.Line, mx, q), Bool.pick(Maybe<&2, Ledgers.Line>, Crits.Key.is_eq(q, RKnown.Id.code(i)), Some{x}, None{})),
    Crits.Crit.upsert_lookup(~Ledgers.Line, ~RKnown.Line.first, mx, RKnown.Id.code(i), x, q)(h),
    Lists.Bool.by(
      d => {
        Bool.pick(Maybe<&2, Ledgers.Line>, d, Some{Crits.Crit.merge(~Ledgers.Line, ~RKnown.Line.first, Crits.Crit.lookup(Ledgers.Line, mx, RKnown.Id.code(i)), x)}, Crits.Crit.lookup(Ledgers.Line, mx, q))
          == Maybe.or(&2, Ledgers.Line, Crits.Crit.lookup(Ledgers.Line, mx, q), Bool.pick(Maybe<&2, Ledgers.Line>, d, Some{x}, None{})): Maybe<&2, Ledgers.Line>
      },
      Crits.Key.is_eq(q, RKnown.Id.code(i)),
      et => Reads.Eq.to(
        List<&2, U32>,
        k => {
          Some{Crits.Crit.merge(~Ledgers.Line, ~RKnown.Line.first, Crits.Crit.lookup(Ledgers.Line, mx, k), x)}
            == Maybe.or(&2, Ledgers.Line, Crits.Crit.lookup(Ledgers.Line, mx, q), Some{x}): Maybe<&2, Ledgers.Line>
        },
        q,
        RKnown.Id.code(i),
        Crits.Key.is_eq_sound(q, RKnown.Id.code(i))(et),
        First.kept(Crits.Crit.lookup(Ledgers.Line, mx, q), x)
      ),
      ef => Equal.sym(Maybe<&2, Ledgers.Line>, Maybe.or(&2, Ledgers.Line, Crits.Crit.lookup(Ledgers.Line, mx, q), None{}), Crits.Crit.lookup(Ledgers.Line, mx, q), Orders.Maybe.or_none(Ledgers.Line, Crits.Crit.lookup(Ledgers.Line, mx, q)))
    )
  )

# what the lines hold under the key q after a request: what they held, else
# the line of the request, if it is a merge of an id of the key q
def Mergers.put_lookup(+mx: Crits.Crit<Ledgers.Line>, +i: Ledgers.Id, r: Spec.Request, +q: List<&2, U32>) -> {
  Crits.Crit.wf(~Ledgers.Line, mx, 0n) == True{}: Bool
} -> {
  Crits.Crit.lookup(Ledgers.Line, RKnown.Mergers.put(mx, i, r), q)
    == Maybe.or(&2, Ledgers.Line, Crits.Crit.lookup(Ledgers.Line, mx, q), Request.keyed(r, i, q, None{})): Maybe<&2, Ledgers.Line>
}:
  match r:
    case Spec.Request.Start{os}:
      h => Equal.sym(Maybe<&2, Ledgers.Line>, Maybe.or(&2, Ledgers.Line, Crits.Crit.lookup(Ledgers.Line, mx, q), None{}), Crits.Crit.lookup(Ledgers.Line, mx, q), Orders.Maybe.or_none(Ledgers.Line, Crits.Crit.lookup(Ledgers.Line, mx, q)))
    case Spec.Request.Write{b, p, w}:
      h => Equal.sym(Maybe<&2, Ledgers.Line>, Maybe.or(&2, Ledgers.Line, Crits.Crit.lookup(Ledgers.Line, mx, q), None{}), Crits.Crit.lookup(Ledgers.Line, mx, q), Orders.Maybe.or_none(Ledgers.Line, Crits.Crit.lookup(Ledgers.Line, mx, q)))
    case Spec.Request.Merge{ff, +x}:
      h => Mergers.merge_lookup(mx, i, x, q)(h)
    case Spec.Request.Resolve{mm, p, w}:
      h => Equal.sym(Maybe<&2, Ledgers.Line>, Maybe.or(&2, Ledgers.Line, Crits.Crit.lookup(Ledgers.Line, mx, q), None{}), Crits.Crit.lookup(Ledgers.Line, mx, q), Orders.Maybe.or_none(Ledgers.Line, Crits.Crit.lookup(Ledgers.Line, mx, q)))
    case Spec.Request.Mark{b, mk, v}:
      h => Equal.sym(Maybe<&2, Ledgers.Line>, Maybe.or(&2, Ledgers.Line, Crits.Crit.lookup(Ledgers.Line, mx, q), None{}), Crits.Crit.lookup(Ledgers.Line, mx, q), Orders.Maybe.or_none(Ledgers.Line, Crits.Crit.lookup(Ledgers.Line, mx, q)))
    case Spec.Request.Move{b, t, v}:
      h => Equal.sym(Maybe<&2, Ledgers.Line>, Maybe.or(&2, Ledgers.Line, Crits.Crit.lookup(Ledgers.Line, mx, q), None{}), Crits.Crit.lookup(Ledgers.Line, mx, q), Orders.Maybe.or_none(Ledgers.Line, Crits.Crit.lookup(Ledgers.Line, mx, q)))
    case Spec.Request.Group{hh, gg, ms}:
      h => Equal.sym(Maybe<&2, Ledgers.Line>, Maybe.or(&2, Ledgers.Line, Crits.Crit.lookup(Ledgers.Line, mx, q), None{}), Crits.Crit.lookup(Ledgers.Line, mx, q), Orders.Maybe.or_none(Ledgers.Line, Crits.Crit.lookup(Ledgers.Line, mx, q)))
    case Spec.Request.Own{cc, gg}:
      h => Equal.sym(Maybe<&2, Ledgers.Line>, Maybe.or(&2, Ledgers.Line, Crits.Crit.lookup(Ledgers.Line, mx, q), None{}), Crits.Crit.lookup(Ledgers.Line, mx, q), Orders.Maybe.or_none(Ledgers.Line, Crits.Crit.lookup(Ledgers.Line, mx, q)))

# what the lines hold under the key q after a fact
def Mergers.step_lookup(+mx: Crits.Crit<Ledgers.Line>, f: Types.Fact, +q: List<&2, U32>) -> {
  Crits.Crit.wf(~Ledgers.Line, mx, 0n) == True{}: Bool
} -> {
  Crits.Crit.lookup(Ledgers.Line, RKnown.Mergers.step(mx, f), q)
    == Maybe.or(&2, Ledgers.Line, Crits.Crit.lookup(Ledgers.Line, mx, q), Fact.keyed(f, q, None{})): Maybe<&2, Ledgers.Line>
}:
  match f:
    case Types.Fact.Vote{v, st, x}:
      h => Equal.sym(Maybe<&2, Ledgers.Line>, Maybe.or(&2, Ledgers.Line, Crits.Crit.lookup(Ledgers.Line, mx, q), None{}), Crits.Crit.lookup(Ledgers.Line, mx, q), Orders.Maybe.or_none(Ledgers.Line, Crits.Crit.lookup(Ledgers.Line, mx, q)))
    case Types.Fact.Ask{Types.Ask{+j, k, r}}:
      h => Mergers.put_lookup(mx, j, r, q)(h)

# what the lines hold under the key q after facts: what they held, else the
# line of the first merge among the facts whose id has the key q
def Mergers.go_lookup(fs: List<&2, Types.Fact>, +mx: Crits.Crit<Ledgers.Line>, +q: List<&2, U32>) -> {
  Crits.Crit.wf(~Ledgers.Line, mx, 0n) == True{}: Bool
} -> {
  Crits.Crit.lookup(Ledgers.Line, RKnown.Mergers.go(fs, mx), q)
    == Maybe.or(&2, Ledgers.Line, Crits.Crit.lookup(Ledgers.Line, mx, q), Line.keyed(fs, q)): Maybe<&2, Ledgers.Line>
}:
  match fs:
    case Nil{}:
      h => Equal.sym(Maybe<&2, Ledgers.Line>, Maybe.or(&2, Ledgers.Line, Crits.Crit.lookup(Ledgers.Line, mx, q), None{}), Crits.Crit.lookup(Ledgers.Line, mx, q), Orders.Maybe.or_none(Ledgers.Line, Crits.Crit.lookup(Ledgers.Line, mx, q)))
    case Con{+f, +rest}:
      +h => Equal.trans(
        Maybe<&2, Ledgers.Line>,
        Crits.Crit.lookup(Ledgers.Line, RKnown.Mergers.go(rest, RKnown.Mergers.step(mx, f)), q),
        Maybe.or(&2, Ledgers.Line, Crits.Crit.lookup(Ledgers.Line, RKnown.Mergers.step(mx, f), q), Line.keyed(rest, q)),
        Maybe.or(&2, Ledgers.Line, Crits.Crit.lookup(Ledgers.Line, mx, q), Fact.keyed(f, q, Line.keyed(rest, q))),
        Mergers.go_lookup(rest, RKnown.Mergers.step(mx, f), q)(Mergers.step_wf(mx, f)(h)),
        Equal.trans(
          Maybe<&2, Ledgers.Line>,
          Maybe.or(&2, Ledgers.Line, Crits.Crit.lookup(Ledgers.Line, RKnown.Mergers.step(mx, f), q), Line.keyed(rest, q)),
          Maybe.or(&2, Ledgers.Line, Maybe.or(&2, Ledgers.Line, Crits.Crit.lookup(Ledgers.Line, mx, q), Fact.keyed(f, q, None{})), Line.keyed(rest, q)),
          Maybe.or(&2, Ledgers.Line, Crits.Crit.lookup(Ledgers.Line, mx, q), Fact.keyed(f, q, Line.keyed(rest, q))),
          Equal.cong(
            Maybe<&2, Ledgers.Line>,
            Maybe<&2, Ledgers.Line>,
            m => Maybe.or(&2, Ledgers.Line, m, Line.keyed(rest, q)),
            Crits.Crit.lookup(Ledgers.Line, RKnown.Mergers.step(mx, f), q),
            Maybe.or(&2, Ledgers.Line, Crits.Crit.lookup(Ledgers.Line, mx, q), Fact.keyed(f, q, None{})),
            Mergers.step_lookup(mx, f, q)(h)
          ),
          Equal.trans(
            Maybe<&2, Ledgers.Line>,
            Maybe.or(&2, Ledgers.Line, Maybe.or(&2, Ledgers.Line, Crits.Crit.lookup(Ledgers.Line, mx, q), Fact.keyed(f, q, None{})), Line.keyed(rest, q)),
            Maybe.or(&2, Ledgers.Line, Crits.Crit.lookup(Ledgers.Line, mx, q), Maybe.or(&2, Ledgers.Line, Fact.keyed(f, q, None{}), Line.keyed(rest, q))),
            Maybe.or(&2, Ledgers.Line, Crits.Crit.lookup(Ledgers.Line, mx, q), Fact.keyed(f, q, Line.keyed(rest, q))),
            Orders.Maybe.or_assoc(Ledgers.Line, Crits.Crit.lookup(Ledgers.Line, mx, q), Fact.keyed(f, q, None{}), Line.keyed(rest, q)),
            Equal.cong(
              Maybe<&2, Ledgers.Line>,
              Maybe<&2, Ledgers.Line>,
              m => Maybe.or(&2, Ledgers.Line, Crits.Crit.lookup(Ledgers.Line, mx, q), m),
              Maybe.or(&2, Ledgers.Line, Fact.keyed(f, q, None{}), Line.keyed(rest, q)),
              Fact.keyed(f, q, Line.keyed(rest, q)),
              Fact.keyed_or(f, q, Line.keyed(rest, q))
            )
          )
        )
      )

# the lines of the merges of facts hold under the key q the line of the first
# merge among them whose id has the key q
def Mergers.of_lookup(fs: List<&2, Types.Fact>, +q: List<&2, U32>) -> {
  Crits.Crit.lookup(Ledgers.Line, RKnown.Mergers.of(fs), q) == Line.keyed(fs, q): Maybe<&2, Ledgers.Line>
}:
  Mergers.go_lookup(fs, Crits.Crit.new(Ledgers.Line), q)(Crits.Crit.new_wf(~Ledgers.Line))

# The line of a merge
# -------------------

# two ids have one key only when they are one id
def Id.code_eq(+j: Ledgers.Id, +i: Ledgers.Id) -> {
  Crits.Key.is_eq(RKnown.Id.code(i), RKnown.Id.code(j)) == Ledgers.Id.is_eq(j, i): Bool
}:
  Lists.Bool.by(
    d => {Crits.Key.is_eq(RKnown.Id.code(i), RKnown.Id.code(j)) == d: Bool},
    Ledgers.Id.is_eq(j, i),
    et => Reads.Eq.back(
      Ledgers.Id,
      y => {Crits.Key.is_eq(RKnown.Id.code(i), RKnown.Id.code(y)) == True{}: Bool},
      j,
      i,
      Ledgers.Id.is_eq_sound(j, i)(et),
      Crits.Key.is_eq_refl(RKnown.Id.code(i))
    ),
    ef => Lists.Bool.by(
      d2 => {d2 == False{}: Bool},
      Crits.Key.is_eq(RKnown.Id.code(i), RKnown.Id.code(j)),
      e2 => Empty.absurd(
        {True{} == False{}: Bool},
        Shared.Bool.true_ne_false(
          Equal.trans(
            Bool,
            True{},
            Ledgers.Id.is_eq(j, j),
            False{},
            Equal.sym(Bool, Ledgers.Id.is_eq(j, j), True{}, Ledgers.Id.is_eq_refl(j)),
          Reads.Eq.to(
            Ledgers.Id,
            y => {Ledgers.Id.is_eq(j, y) == False{}: Bool},
            i,
            j,
            Codes.Code.is_eq_sound(
              ~Ledgers.Id,
              ~Ledgers.Id.code,
              ~Ledgers.Id.code.read,
              ~(a => r => Ledgers.Id.code_read(a, r)),
              i,
              j
            )(e2),
            ef
          )
          )
        )
      ),
      e2 => {==}
    )
  )

# the line of the first merge whose id has the key of the id i is the line
# of the merge of the id i
def Line.keyed_line(fs: List<&2, Types.Fact>, +i: Ledgers.Id) -> {
  Line.keyed(fs, RKnown.Id.code(i)) == RKnown.Merge.line(fs, i): Maybe<&2, Ledgers.Line>
}:
  match fs:
    case Nil{}:
      {==}
    case Con{Types.Fact.Vote{v, st, pk}, +rest}:
      Line.keyed_line(rest, i)
    case Con{Types.Fact.Ask{Types.Ask{+j, k, Spec.Request.Start{os}}}, +rest}:
      Line.keyed_line(rest, i)
    case Con{Types.Fact.Ask{Types.Ask{+j, k, Spec.Request.Write{b, p, w}}}, +rest}:
      Line.keyed_line(rest, i)
    case Con{Types.Fact.Ask{Types.Ask{+j, k, Spec.Request.Merge{ff, +x}}}, +rest}:
      Reads.Eq.back(
        Bool,
        d => {
          Bool.pick(Maybe<&2, Ledgers.Line>, d, Some{x}, Line.keyed(rest, RKnown.Id.code(i)))
            == Shared.Bool.when(Maybe<&2, Ledgers.Line>, Ledgers.Id.is_eq(j, i), u => Some{x}, u => RKnown.Merge.line(rest, i)): Maybe<&2, Ledgers.Line>
        },
        Crits.Key.is_eq(RKnown.Id.code(i), RKnown.Id.code(j)),
        Ledgers.Id.is_eq(j, i),
        Id.code_eq(j, i),
        Lists.Bool.by(
          d => {
            Bool.pick(Maybe<&2, Ledgers.Line>, d, Some{x}, Line.keyed(rest, RKnown.Id.code(i)))
              == Shared.Bool.when(Maybe<&2, Ledgers.Line>, d, u => Some{x}, u => RKnown.Merge.line(rest, i)): Maybe<&2, Ledgers.Line>
          },
          Ledgers.Id.is_eq(j, i),
          et => {==},
          ef => Line.keyed_line(rest, i)
        )
      )
    case Con{Types.Fact.Ask{Types.Ask{+j, k, Spec.Request.Resolve{mm, p, w}}}, +rest}:
      Line.keyed_line(rest, i)
    case Con{Types.Fact.Ask{Types.Ask{+j, k, Spec.Request.Mark{b, mk, v}}}, +rest}:
      Line.keyed_line(rest, i)
    case Con{Types.Fact.Ask{Types.Ask{+j, k, Spec.Request.Move{b, t, v}}}, +rest}:
      Line.keyed_line(rest, i)
    case Con{Types.Fact.Ask{Types.Ask{+j, k, Spec.Request.Group{hh, gg, ms}}}, +rest}:
      Line.keyed_line(rest, i)
    case Con{Types.Fact.Ask{Types.Ask{+j, k, Spec.Request.Own{cc, gg}}}, +rest}:
      Line.keyed_line(rest, i)

# the lines of the merges of facts hold for an id the line of its merge
def Mergers.get_line(+fs: List<&2, Types.Fact>, +i: Ledgers.Id) -> {
  RKnown.Mergers.get(RKnown.Mergers.of(fs), i) == RKnown.Merge.line(fs, i): Maybe<&2, Ledgers.Line>
}:
  Equal.trans(
    Maybe<&2, Ledgers.Line>,
    RKnown.Mergers.get(RKnown.Mergers.of(fs), i),
    Crits.Crit.lookup(Ledgers.Line, RKnown.Mergers.of(fs), RKnown.Id.code(i)),
    RKnown.Merge.line(fs, i),
    Crits.Crit.get_lookup(~Ledgers.Line, RKnown.Mergers.of(fs), RKnown.Id.code(i))(Mergers.of_wf(fs)),
    Equal.trans(
      Maybe<&2, Ledgers.Line>,
      Crits.Crit.lookup(Ledgers.Line, RKnown.Mergers.of(fs), RKnown.Id.code(i)),
      Line.keyed(fs, RKnown.Id.code(i)),
      RKnown.Merge.line(fs, i),
      Mergers.of_lookup(fs, RKnown.Id.code(i)),
      Line.keyed_line(fs, i)
    )
  )

# A fact joins the facts
# ----------------------

# a Maybe that is none is None
def None.of(m: Maybe<&2, Ledgers.Line>) -> {Maybe.is_none(&2, Ledgers.Line, m) == True{}: Bool} -> {m == None{}: Maybe<&2, Ledgers.Line>}:
  match m:
    case None{}:
      h => {==}
    case Some{x}:
      h => Empty.absurd({Some{x} == None{}: Maybe<&2, Ledgers.Line>}, Shared.Bool.false_ne_true(h))

# facts whose lines hold none for the id i hold no merge whose id has the key
# of i
def Fresh.id(+fs: List<&2, Types.Fact>, +i: Ledgers.Id) -> {
  Maybe.is_none(&2, Ledgers.Line, RKnown.Mergers.get(RKnown.Mergers.of(fs), i)) == True{}: Bool
} -> {Line.keyed(fs, RKnown.Id.code(i)) == None{}: Maybe<&2, Ledgers.Line>}:
  h => Equal.trans(
    Maybe<&2, Ledgers.Line>,
    Line.keyed(fs, RKnown.Id.code(i)),
    RKnown.Mergers.get(RKnown.Mergers.of(fs), i),
    None{},
    Equal.sym(
      Maybe<&2, Ledgers.Line>,
      RKnown.Mergers.get(RKnown.Mergers.of(fs), i),
      Line.keyed(fs, RKnown.Id.code(i)),
      Equal.trans(
        Maybe<&2, Ledgers.Line>,
        RKnown.Mergers.get(RKnown.Mergers.of(fs), i),
        Crits.Crit.lookup(Ledgers.Line, RKnown.Mergers.of(fs), RKnown.Id.code(i)),
        Line.keyed(fs, RKnown.Id.code(i)),
        Crits.Crit.get_lookup(~Ledgers.Line, RKnown.Mergers.of(fs), RKnown.Id.code(i))(Mergers.of_wf(fs)),
        Mergers.of_lookup(fs, RKnown.Id.code(i))
      )
    ),
    None.of(RKnown.Mergers.get(RKnown.Mergers.of(fs), i))(h)
  )

# facts hold no merge of the key q, when the request r of the id i gives a
# line of q and gives their lines none for an id that they hold one for
def Fresh.request(+fs: List<&2, Types.Fact>, +i: Ledgers.Id, r: Spec.Request, +q: List<&2, U32>, -y: Ledgers.Line) -> {
  RKnown.Mergers.free(RKnown.Mergers.of(fs), i, r) == True{}: Bool
} -> {
  Request.keyed(r, i, q, None{}) == Some{y}: Maybe<&2, Ledgers.Line>
} -> {Line.keyed(fs, q) == None{}: Maybe<&2, Ledgers.Line>}:
  match r:
    case Spec.Request.Start{os}:
      hf => es => Empty.absurd(
        {Line.keyed(fs, q) == None{}: Maybe<&2, Ledgers.Line>},
        Shared.Maybe.none_ne_some(Ledgers.Line, y, es)
      )
    case Spec.Request.Write{b, p, w}:
      hf => es => Empty.absurd(
        {Line.keyed(fs, q) == None{}: Maybe<&2, Ledgers.Line>},
        Shared.Maybe.none_ne_some(Ledgers.Line, y, es)
      )
    case Spec.Request.Merge{ff, x}:
      hf => es => Reads.Eq.back(
        List<&2, U32>,
        k => {Line.keyed(fs, k) == None{}: Maybe<&2, Ledgers.Line>},
        q,
        RKnown.Id.code(i),
        Crits.Key.is_eq_sound(q, RKnown.Id.code(i))(Pick.hit(Crits.Key.is_eq(q, RKnown.Id.code(i)), x, y)(es)),
        Fresh.id(fs, i)(hf)
      )
    case Spec.Request.Resolve{mm, p, w}:
      hf => es => Empty.absurd(
        {Line.keyed(fs, q) == None{}: Maybe<&2, Ledgers.Line>},
        Shared.Maybe.none_ne_some(Ledgers.Line, y, es)
      )
    case Spec.Request.Mark{b, mk, v}:
      hf => es => Empty.absurd(
        {Line.keyed(fs, q) == None{}: Maybe<&2, Ledgers.Line>},
        Shared.Maybe.none_ne_some(Ledgers.Line, y, es)
      )
    case Spec.Request.Move{b, t, v}:
      hf => es => Empty.absurd(
        {Line.keyed(fs, q) == None{}: Maybe<&2, Ledgers.Line>},
        Shared.Maybe.none_ne_some(Ledgers.Line, y, es)
      )
    case Spec.Request.Group{hh, gg, ms}:
      hf => es => Empty.absurd(
        {Line.keyed(fs, q) == None{}: Maybe<&2, Ledgers.Line>},
        Shared.Maybe.none_ne_some(Ledgers.Line, y, es)
      )
    case Spec.Request.Own{cc, gg}:
      hf => es => Empty.absurd(
        {Line.keyed(fs, q) == None{}: Maybe<&2, Ledgers.Line>},
        Shared.Maybe.none_ne_some(Ledgers.Line, y, es)
      )

# facts hold no merge of the key q, when the fact f gives a line of q and
# gives their lines none for an id that they hold one for
def Fresh.fact(+fs: List<&2, Types.Fact>, f: Types.Fact, +q: List<&2, U32>, -y: Ledgers.Line) -> {
  RKnown.Mergers.fresh(RKnown.Mergers.of(fs), f) == True{}: Bool
} -> {
  Fact.keyed(f, q, None{}) == Some{y}: Maybe<&2, Ledgers.Line>
} -> {Line.keyed(fs, q) == None{}: Maybe<&2, Ledgers.Line>}:
  match f:
    case Types.Fact.Vote{v, st, x}:
      hf => es => Empty.absurd(
        {Line.keyed(fs, q) == None{}: Maybe<&2, Ledgers.Line>},
        Shared.Maybe.none_ne_some(Ledgers.Line, y, es)
      )
    case Types.Fact.Ask{Types.Ask{+j, k, r}}:
      hf => es => Fresh.request(fs, j, r, q, y)(hf)(es)

# the facts with the fact f hold, for the key q, the line that the facts
# hold, else the line that f gives: when f gives their lines none for an id
# that they hold one for
def Line.keyed_insert(+fs: List<&2, Types.Fact>, +f: Types.Fact, +q: List<&2, U32>) -> {
  RKnown.Mergers.fresh(RKnown.Mergers.of(fs), f) == True{}: Bool
} -> {
  Line.keyed(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f), q)
    == Maybe.or(&2, Ledgers.Line, Line.keyed(fs, q), Fact.keyed(f, q, None{})): Maybe<&2, Ledgers.Line>
}:
  +hf => Lists.Maybe.by(
    Ledgers.Line,
    m => {
      Line.keyed(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f), q) == Maybe.or(&2, Ledgers.Line, Line.keyed(fs, q), m): Maybe<&2, Ledgers.Line>
    },
    Fact.keyed(f, q, None{}),
    en => Equal.trans(
      Maybe<&2, Ledgers.Line>,
      Line.keyed(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f), q),
      Line.keyed(fs, q),
      Maybe.or(&2, Ledgers.Line, Line.keyed(fs, q), None{}),
      Line.keyed_insert_pass(fs, f, q)(en),
      Equal.sym(Maybe<&2, Ledgers.Line>, Maybe.or(&2, Ledgers.Line, Line.keyed(fs, q), None{}), Line.keyed(fs, q), Orders.Maybe.or_none(Ledgers.Line, Line.keyed(fs, q)))
    ),
    y => +es => Reads.Eq.back(
      Maybe<&2, Ledgers.Line>,
      m => {
        Line.keyed(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f), q) == Maybe.or(&2, Ledgers.Line, m, Some{y}): Maybe<&2, Ledgers.Line>
      },
      Line.keyed(fs, q),
      None{},
      Fresh.fact(fs, f, q, y)(hf)(es),
      Equal.trans(
        Maybe<&2, Ledgers.Line>,
        Line.keyed(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f), q),
        Fact.keyed(f, q, None{}),
        Some{y},
        Line.keyed_insert_new(fs, f, q)(Fresh.fact(fs, f, q, y)(hf)(es)),
        es
      )
    )
  )

# the lines of the facts with the fact f, and the lines of the facts with f
# put, hold the same under the key q
def Mergers.insert_at(+fs: List<&2, Types.Fact>, +f: Types.Fact, +q: List<&2, U32>) -> {
  RKnown.Mergers.fresh(RKnown.Mergers.of(fs), f) == True{}: Bool
} -> {
  Orders.Binds.get(Ledgers.Line, Crits.Crit.entries(Ledgers.Line, RKnown.Mergers.of(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f))), q) == Orders.Binds.get(Ledgers.Line, Crits.Crit.entries(Ledgers.Line, RKnown.Mergers.step(RKnown.Mergers.of(fs), f)), q): Maybe<&2, Ledgers.Line>
}:
  hf => Equal.trans(
    Maybe<&2, Ledgers.Line>,
    Orders.Binds.get(Ledgers.Line, Crits.Crit.entries(Ledgers.Line, RKnown.Mergers.of(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f))), q),
    Crits.Crit.lookup(Ledgers.Line, RKnown.Mergers.of(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f)), q),
    Orders.Binds.get(Ledgers.Line, Crits.Crit.entries(Ledgers.Line, RKnown.Mergers.step(RKnown.Mergers.of(fs), f)), q),
    Orders.Crit.get_entries(Ledgers.Line, RKnown.Mergers.of(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f)), q),
    Equal.trans(
      Maybe<&2, Ledgers.Line>,
      Crits.Crit.lookup(Ledgers.Line, RKnown.Mergers.of(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f)), q),
      Maybe.or(&2, Ledgers.Line, Line.keyed(fs, q), Fact.keyed(f, q, None{})),
      Orders.Binds.get(Ledgers.Line, Crits.Crit.entries(Ledgers.Line, RKnown.Mergers.step(RKnown.Mergers.of(fs), f)), q),
      Equal.trans(
        Maybe<&2, Ledgers.Line>,
        Crits.Crit.lookup(Ledgers.Line, RKnown.Mergers.of(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f)), q),
        Line.keyed(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f), q),
        Maybe.or(&2, Ledgers.Line, Line.keyed(fs, q), Fact.keyed(f, q, None{})),
        Mergers.of_lookup(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f), q),
        Line.keyed_insert(fs, f, q)(hf)
      ),
      Equal.sym(
        Maybe<&2, Ledgers.Line>,
        Orders.Binds.get(Ledgers.Line, Crits.Crit.entries(Ledgers.Line, RKnown.Mergers.step(RKnown.Mergers.of(fs), f)), q),
        Maybe.or(&2, Ledgers.Line, Line.keyed(fs, q), Fact.keyed(f, q, None{})),
        Equal.trans(
          Maybe<&2, Ledgers.Line>,
          Orders.Binds.get(Ledgers.Line, Crits.Crit.entries(Ledgers.Line, RKnown.Mergers.step(RKnown.Mergers.of(fs), f)), q),
          Crits.Crit.lookup(Ledgers.Line, RKnown.Mergers.step(RKnown.Mergers.of(fs), f), q),
          Maybe.or(&2, Ledgers.Line, Line.keyed(fs, q), Fact.keyed(f, q, None{})),
          Orders.Crit.get_entries(Ledgers.Line, RKnown.Mergers.step(RKnown.Mergers.of(fs), f), q),
          Equal.trans(
            Maybe<&2, Ledgers.Line>,
            Crits.Crit.lookup(Ledgers.Line, RKnown.Mergers.step(RKnown.Mergers.of(fs), f), q),
            Maybe.or(&2, Ledgers.Line, Crits.Crit.lookup(Ledgers.Line, RKnown.Mergers.of(fs), q), Fact.keyed(f, q, None{})),
            Maybe.or(&2, Ledgers.Line, Line.keyed(fs, q), Fact.keyed(f, q, None{})),
            Mergers.step_lookup(RKnown.Mergers.of(fs), f, q)(Mergers.of_wf(fs)),
            Equal.cong(
              Maybe<&2, Ledgers.Line>,
              Maybe<&2, Ledgers.Line>,
              m => Maybe.or(&2, Ledgers.Line, m, Fact.keyed(f, q, None{})),
              Crits.Crit.lookup(Ledgers.Line, RKnown.Mergers.of(fs), q),
              Line.keyed(fs, q),
              Mergers.of_lookup(fs, q)
            )
          )
        )
      )
    )
  )

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- a proof does not run
# the lines of the facts with the fact f, and the lines of the facts with f
# put, hold the same under the key of each of the entries es
def Mergers.insert_same(es: List<&2, Crits.Bind<Ledgers.Line>>, +fs: List<&2, Types.Fact>, +f: Types.Fact, +hf: {
  RKnown.Mergers.fresh(RKnown.Mergers.of(fs), f) == True{}: Bool
}) -> Orders.Binds.Same(Ledgers.Line, es, Crits.Crit.entries(Ledgers.Line, RKnown.Mergers.of(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f))), Crits.Crit.entries(Ledgers.Line, RKnown.Mergers.step(RKnown.Mergers.of(fs), f))):
  match es:
    case Nil{}:
      Unit{}
    case Con{Crits.Bind{+q, v}, rest}:
      (Mergers.insert_at(fs, f, q)(hf), Mergers.insert_same(rest, fs, f, hf))
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# the lines of the merges of the facts with the fact f are the lines of the
# facts with f put: when f gives them no line for an id that they hold one
# for
def Mergers.of_insert(+fs: List<&2, Types.Fact>, +f: Types.Fact) -> {
  RKnown.Mergers.fresh(RKnown.Mergers.of(fs), f) == True{}: Bool
} -> {RKnown.Mergers.of(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f)) == RKnown.Mergers.step(RKnown.Mergers.of(fs), f): Crits.Crit<Ledgers.Line>}:
  +hf => Crits.Crit.ext(
    ~Ledgers.Line,
    RKnown.Mergers.of(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f)),
    RKnown.Mergers.step(RKnown.Mergers.of(fs), f)
  )(
    Mergers.of_wf(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f))
  )(
    Mergers.step_wf(RKnown.Mergers.of(fs), f)(Mergers.of_wf(fs))
  )(
    Orders.Binds.ext(
      ~Ledgers.Line,
      Crits.Crit.entries(Ledgers.Line, RKnown.Mergers.of(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f))),
      Crits.Crit.entries(Ledgers.Line, RKnown.Mergers.step(RKnown.Mergers.of(fs), f))
    )(
      Orders.Crit.entries_sorted(~Ledgers.Line, RKnown.Mergers.of(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f)))(Mergers.of_wf(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f)))
    )(
      Orders.Crit.entries_sorted(~Ledgers.Line, RKnown.Mergers.step(RKnown.Mergers.of(fs), f))(Mergers.step_wf(RKnown.Mergers.of(fs), f)(Mergers.of_wf(fs)))
    )(
      Mergers.insert_same(Crits.Crit.entries(Ledgers.Line, RKnown.Mergers.of(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f))), fs, f, hf)
    )(
      Mergers.insert_same(Crits.Crit.entries(Ledgers.Line, RKnown.Mergers.step(RKnown.Mergers.of(fs), f)), fs, f, hf)
    )
  )

# A fact that is no merge
# -----------------------

# a request that is no merge gives no line
def Request.keyed_plain(r: Spec.Request, j: Ledgers.Id, q: List<&2, U32>) -> {
  RKnown.Request.merges(r) == False{}: Bool
} -> {Request.keyed(r, j, q, None{}) == None{}: Maybe<&2, Ledgers.Line>}:
  match r:
    case Spec.Request.Start{os}:
      h => {==}
    case Spec.Request.Write{b, p, w}:
      h => {==}
    case Spec.Request.Merge{ff, x}:
      h => Empty.absurd({Request.keyed(Spec.Request.Merge{ff, x}, j, q, None{}) == None{}: Maybe<&2, Ledgers.Line>}, Shared.Bool.true_ne_false(h))
    case Spec.Request.Resolve{mm, p, w}:
      h => {==}
    case Spec.Request.Mark{b, mk, v}:
      h => {==}
    case Spec.Request.Move{b, t, v}:
      h => {==}
    case Spec.Request.Group{hh, gg, ms}:
      h => {==}
    case Spec.Request.Own{cc, gg}:
      h => {==}

# a fact that is no ask of a merge gives no line
def Fact.keyed_plain(f: Types.Fact, q: List<&2, U32>) -> {
  RKnown.Fact.merges(f) == False{}: Bool
} -> {Fact.keyed(f, q, None{}) == None{}: Maybe<&2, Ledgers.Line>}:
  match f:
    case Types.Fact.Vote{v, st, x}:
      h => {==}
    case Types.Fact.Ask{Types.Ask{j, k, r}}:
      h => Request.keyed_plain(r, j, q)(h)

# a fact that is no ask of a merge, put among facts, leaves the line of each
# merge as it was
def Merge.line_insert_pass(+fs: List<&2, Types.Fact>, +f: Types.Fact, +i: Ledgers.Id) -> {
  RKnown.Fact.merges(f) == False{}: Bool
} -> {RKnown.Merge.line(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f), i) == RKnown.Merge.line(fs, i): Maybe<&2, Ledgers.Line>}:
  h => Equal.trans(
    Maybe<&2, Ledgers.Line>,
    RKnown.Merge.line(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f), i),
    Line.keyed(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f), RKnown.Id.code(i)),
    RKnown.Merge.line(fs, i),
    Equal.sym(Maybe<&2, Ledgers.Line>, Line.keyed(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f), RKnown.Id.code(i)), RKnown.Merge.line(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f), i), Line.keyed_line(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f), i)),
    Equal.trans(
      Maybe<&2, Ledgers.Line>,
      Line.keyed(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f), RKnown.Id.code(i)),
      Line.keyed(fs, RKnown.Id.code(i)),
      RKnown.Merge.line(fs, i),
      Line.keyed_insert_pass(fs, f, RKnown.Id.code(i))(Fact.keyed_plain(f, RKnown.Id.code(i))(h)),
      Line.keyed_line(fs, i)
    )
  )

# a fact put among facts leaves the line that they hold for a merge: when it
# gives their lines none for an id that they hold one for
def Merge.line_insert_keep(+fs: List<&2, Types.Fact>, +f: Types.Fact, +i: Ledgers.Id, +c: Ledgers.Line) -> {
  RKnown.Mergers.fresh(RKnown.Mergers.of(fs), f) == True{}: Bool
} -> {
  RKnown.Merge.line(fs, i) == Some{c}: Maybe<&2, Ledgers.Line>
} -> {RKnown.Merge.line(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f), i) == Some{c}: Maybe<&2, Ledgers.Line>}:
  hf => es => Equal.trans(
    Maybe<&2, Ledgers.Line>,
    RKnown.Merge.line(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f), i),
    Line.keyed(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f), RKnown.Id.code(i)),
    Some{c},
    Equal.sym(Maybe<&2, Ledgers.Line>, Line.keyed(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f), RKnown.Id.code(i)), RKnown.Merge.line(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f), i), Line.keyed_line(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f), i)),
    Equal.trans(
      Maybe<&2, Ledgers.Line>,
      Line.keyed(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f), RKnown.Id.code(i)),
      Maybe.or(&2, Ledgers.Line, Line.keyed(fs, RKnown.Id.code(i)), Fact.keyed(f, RKnown.Id.code(i), None{})),
      Some{c},
      Line.keyed_insert(fs, f, RKnown.Id.code(i))(hf),
      Reads.Eq.back(
        Maybe<&2, Ledgers.Line>,
        m => {Maybe.or(&2, Ledgers.Line, m, Fact.keyed(f, RKnown.Id.code(i), None{})) == Some{c}: Maybe<&2, Ledgers.Line>},
        Line.keyed(fs, RKnown.Id.code(i)),
        Some{c},
        Equal.trans(Maybe<&2, Ledgers.Line>, Line.keyed(fs, RKnown.Id.code(i)), RKnown.Merge.line(fs, i), Some{c}, Line.keyed_line(fs, i), es),
        {==}
      )
    )
  )

# Same lines
# ----------

# a line, if any, is the same as itself
def Line.end_refl(
  e: Maybe<&2, Ledgers.Line>
) -> {Shared.Maybe.is_eq(~Ledgers.Line, ~Ledgers.Line.is_eq, e, e) == True{}: Bool}:
  match e:
    case None{}:
      {==}
    case Some{v}:
      Ledgers.Line.is_eq_refl(v)

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof does not run
# bend-lint: expect-begin bend-lint-rules/performance/missed_fork@hint -- a proof does not run
# Mergers.same is True for lines of merges and themselves
def Mergers.same_refl(a: Crits.Crit<Ledgers.Line>) -> {RKnown.Mergers.same(a, a) == True{}: Bool}:
  match a:
    case Crits.Crit.Tip{}:
      {==}
    case Crits.Crit.Leaf{+k, +v}:
      Shared.Bool.and_both(
        Crits.Key.is_eq(k, k),
        Ledgers.Line.is_eq(v, v)
      )(Crits.Key.is_eq_refl(k))(Ledgers.Line.is_eq_refl(v))
    case Crits.Crit.Fork{+r, +p, +e, +z, +o}:
      Shared.Bool.and_both(
        Crits.Key.is_eq(r, r),
        Bool.and(
          Nat.is_eq(p, p),
          Bool.and(
            Shared.Maybe.is_eq(~Ledgers.Line, ~Ledgers.Line.is_eq, e, e),
            Bool.and(RKnown.Mergers.same(z, z), RKnown.Mergers.same(o, o))
          )
        )
      )(
        Crits.Key.is_eq_refl(r)
      )(
        Shared.Bool.and_both(
          Nat.is_eq(p, p),
          Bool.and(
            Shared.Maybe.is_eq(~Ledgers.Line, ~Ledgers.Line.is_eq, e, e),
            Bool.and(RKnown.Mergers.same(z, z), RKnown.Mergers.same(o, o))
          )
        )(
          Shared.Nat.is_eq_refl(p)
        )(
          Shared.Bool.and_both(
            Shared.Maybe.is_eq(~Ledgers.Line, ~Ledgers.Line.is_eq, e, e),
            Bool.and(RKnown.Mergers.same(z, z), RKnown.Mergers.same(o, o))
          )(
            Line.end_refl(e)
          )(
            Shared.Bool.and_both(
              RKnown.Mergers.same(z, z),
              RKnown.Mergers.same(o, o)
            )(Mergers.same_refl(z))(Mergers.same_refl(o))
          )
        )
      )
# bend-lint: expect-end bend-lint-rules/performance/missed_fork@hint

# Mergers.same is True only for equal lines of merges
def Mergers.same_sound(
  a: Crits.Crit<Ledgers.Line>,
  b: Crits.Crit<Ledgers.Line>
) -> {RKnown.Mergers.same(a, b) == True{}: Bool} -> {a == b: Crits.Crit<Ledgers.Line>}:
  match a b:
    case Crits.Crit.Tip{} Crits.Crit.Tip{}:
      h => {==}
    case Crits.Crit.Tip{} Crits.Crit.Leaf{k2, v2}:
      h => Empty.absurd(
        {Crits.Crit.Tip{} == Crits.Crit.Leaf{k2, v2}: Crits.Crit<Ledgers.Line>},
        Shared.Bool.false_ne_true(h)
      )
    case Crits.Crit.Tip{} Crits.Crit.Fork{r2, p2, e2, z2, o2}:
      h => Empty.absurd(
        {Crits.Crit.Tip{} == Crits.Crit.Fork{r2, p2, e2, z2, o2}: Crits.Crit<Ledgers.Line>},
        Shared.Bool.false_ne_true(h)
      )
    case Crits.Crit.Leaf{k1, v1} Crits.Crit.Tip{}:
      h => Empty.absurd(
        {Crits.Crit.Leaf{k1, v1} == Crits.Crit.Tip{}: Crits.Crit<Ledgers.Line>},
        Shared.Bool.false_ne_true(h)
      )
    case Crits.Crit.Leaf{k1, v1} Crits.Crit.Fork{r2, p2, e2, z2, o2}:
      h => Empty.absurd(
        {Crits.Crit.Leaf{k1, v1} == Crits.Crit.Fork{r2, p2, e2, z2, o2}: Crits.Crit<Ledgers.Line>},
        Shared.Bool.false_ne_true(h)
      )
    case Crits.Crit.Fork{r1, p1, e1, z1, o1} Crits.Crit.Tip{}:
      h => Empty.absurd(
        {Crits.Crit.Fork{r1, p1, e1, z1, o1} == Crits.Crit.Tip{}: Crits.Crit<Ledgers.Line>},
        Shared.Bool.false_ne_true(h)
      )
    case Crits.Crit.Fork{r1, p1, e1, z1, o1} Crits.Crit.Leaf{k2, v2}:
      h => Empty.absurd(
        {Crits.Crit.Fork{r1, p1, e1, z1, o1} == Crits.Crit.Leaf{k2, v2}: Crits.Crit<Ledgers.Line>},
        Shared.Bool.false_ne_true(h)
      )
    case Crits.Crit.Leaf{+k1, +v1} Crits.Crit.Leaf{+k2, +v2}:
      +h => (
        %Crits.Key.is_eq_sound(k1, k2)(Shared.Bool.and_true_left(Crits.Key.is_eq(k1, k2), Ledgers.Line.is_eq(v1, v2))(h)): {Crits.Crit.Leaf{k1, v1} == Crits.Crit.Leaf{_, v2}: Crits.Crit<Ledgers.Line>}
        %Ledgers.Line.is_eq_sound(v1, v2)(Shared.Bool.and_true_right(Crits.Key.is_eq(k1, k2), Ledgers.Line.is_eq(v1, v2))(h)): {Crits.Crit.Leaf{k1, v1} == Crits.Crit.Leaf{k1, _}: Crits.Crit<Ledgers.Line>}
        {==})
    case Crits.Crit.Fork{+r1, +p1, +e1, +z1, +o1} Crits.Crit.Fork{+r2, +p2, +e2, +z2, +o2}:
      +h => (
        %Crits.Key.is_eq_sound(r1, r2)(Shared.Bool.and_true_left(Crits.Key.is_eq(r1, r2), Bool.and(Nat.is_eq(p1, p2), Bool.and(Shared.Maybe.is_eq(~Ledgers.Line, ~Ledgers.Line.is_eq, e1, e2), Bool.and(RKnown.Mergers.same(z1, z2), RKnown.Mergers.same(o1, o2)))))(h)): {Crits.Crit.Fork{r1, p1, e1, z1, o1} == Crits.Crit.Fork{_, p2, e2, z2, o2}: Crits.Crit<Ledgers.Line>}
        %Shared.Nat.is_eq_sound(p1, p2)(Shared.Bool.and_true_left(Nat.is_eq(p1, p2), Bool.and(Shared.Maybe.is_eq(~Ledgers.Line, ~Ledgers.Line.is_eq, e1, e2), Bool.and(RKnown.Mergers.same(z1, z2), RKnown.Mergers.same(o1, o2))))(Shared.Bool.and_true_right(Crits.Key.is_eq(r1, r2), Bool.and(Nat.is_eq(p1, p2), Bool.and(Shared.Maybe.is_eq(~Ledgers.Line, ~Ledgers.Line.is_eq, e1, e2), Bool.and(RKnown.Mergers.same(z1, z2), RKnown.Mergers.same(o1, o2)))))(h))): {Crits.Crit.Fork{r1, p1, e1, z1, o1} == Crits.Crit.Fork{r1, _, e2, z2, o2}: Crits.Crit<Ledgers.Line>}
        %Shared.Maybe.is_eq_sound(~Ledgers.Line, ~Ledgers.Line.is_eq, x => y => Ledgers.Line.is_eq_sound(x, y), e1, e2)(Shared.Bool.and_true_left(Shared.Maybe.is_eq(~Ledgers.Line, ~Ledgers.Line.is_eq, e1, e2), Bool.and(RKnown.Mergers.same(z1, z2), RKnown.Mergers.same(o1, o2)))(Shared.Bool.and_true_right(Nat.is_eq(p1, p2), Bool.and(Shared.Maybe.is_eq(~Ledgers.Line, ~Ledgers.Line.is_eq, e1, e2), Bool.and(RKnown.Mergers.same(z1, z2), RKnown.Mergers.same(o1, o2))))(Shared.Bool.and_true_right(Crits.Key.is_eq(r1, r2), Bool.and(Nat.is_eq(p1, p2), Bool.and(Shared.Maybe.is_eq(~Ledgers.Line, ~Ledgers.Line.is_eq, e1, e2), Bool.and(RKnown.Mergers.same(z1, z2), RKnown.Mergers.same(o1, o2)))))(h)))): {Crits.Crit.Fork{r1, p1, e1, z1, o1} == Crits.Crit.Fork{r1, p1, _, z2, o2}: Crits.Crit<Ledgers.Line>}
        %Mergers.same_sound(z1, z2)(Shared.Bool.and_true_left(RKnown.Mergers.same(z1, z2), RKnown.Mergers.same(o1, o2))(Shared.Bool.and_true_right(Shared.Maybe.is_eq(~Ledgers.Line, ~Ledgers.Line.is_eq, e1, e2), Bool.and(RKnown.Mergers.same(z1, z2), RKnown.Mergers.same(o1, o2)))(Shared.Bool.and_true_right(Nat.is_eq(p1, p2), Bool.and(Shared.Maybe.is_eq(~Ledgers.Line, ~Ledgers.Line.is_eq, e1, e2), Bool.and(RKnown.Mergers.same(z1, z2), RKnown.Mergers.same(o1, o2))))(Shared.Bool.and_true_right(Crits.Key.is_eq(r1, r2), Bool.and(Nat.is_eq(p1, p2), Bool.and(Shared.Maybe.is_eq(~Ledgers.Line, ~Ledgers.Line.is_eq, e1, e2), Bool.and(RKnown.Mergers.same(z1, z2), RKnown.Mergers.same(o1, o2)))))(h))))): {Crits.Crit.Fork{r1, p1, e1, z1, o1} == Crits.Crit.Fork{r1, p1, e1, _, o2}: Crits.Crit<Ledgers.Line>}
        %Mergers.same_sound(o1, o2)(Shared.Bool.and_true_right(RKnown.Mergers.same(z1, z2), RKnown.Mergers.same(o1, o2))(Shared.Bool.and_true_right(Shared.Maybe.is_eq(~Ledgers.Line, ~Ledgers.Line.is_eq, e1, e2), Bool.and(RKnown.Mergers.same(z1, z2), RKnown.Mergers.same(o1, o2)))(Shared.Bool.and_true_right(Nat.is_eq(p1, p2), Bool.and(Shared.Maybe.is_eq(~Ledgers.Line, ~Ledgers.Line.is_eq, e1, e2), Bool.and(RKnown.Mergers.same(z1, z2), RKnown.Mergers.same(o1, o2))))(Shared.Bool.and_true_right(Crits.Key.is_eq(r1, r2), Bool.and(Nat.is_eq(p1, p2), Bool.and(Shared.Maybe.is_eq(~Ledgers.Line, ~Ledgers.Line.is_eq, e1, e2), Bool.and(RKnown.Mergers.same(z1, z2), RKnown.Mergers.same(o1, o2)))))(h))))): {Crits.Crit.Fork{r1, p1, e1, z1, o1} == Crits.Crit.Fork{r1, p1, e1, z1, _}: Crits.Crit<Ledgers.Line>}
        {==})
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# equal lines of merges are the same
def Mergers.same_refl_of(
  a: Crits.Crit<Ledgers.Line>,
  b: Crits.Crit<Ledgers.Line>
) -> {a == b: Crits.Crit<Ledgers.Line>} -> {RKnown.Mergers.same(a, b) == True{}: Bool}:
  e =>
    %e: {RKnown.Mergers.same(a, _) == True{}: Bool}
    Mergers.same_refl(a)
