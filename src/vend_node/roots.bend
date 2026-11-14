import Base
import ../shared/shared/ledger.bend as Ledgers
import ../shared/shared/shared/shared/code.bend as Codes
import ../shared/shared/shared/shared/crit.bend as Crits
import ../shared/shared/shared/shared/crit_order.bend as Orders
import ../shared/shared/shared/shared/hash.bend as Hashes
import ../shared/shared/shared/shared/shared.bend as Shared
import ./codes.bend as Coded
import ./reads.bend as Reads
import ./run/facts.bend as RFacts
import ./run/known.bend as RKnown
import ./run/lines.bend as RLines
import ./shared/lists.bend as Lists
import ./spec.bend as Spec
import ./types.bend as Types

# Roots of stores: laws
# ---------------------
# The roots of the stores that the asks among some facts start
# (run/known.bend, Roots) hold a root exactly when an ask among the facts
# starts its store (Roots.has_empty, Roots.of_lookup), so a request starts
# no store that the facts start exactly when the roots do not hold its root
# (Roots.fresh_ok). A fact that joins the facts changes them by one write of
# the set (Roots.of_insert).

# m, or a mark when the bit b says so
def Roots.or(m: Maybe<&2, Unit>, b: Bool) -> Maybe<&2, Unit>:
  match b:
    case True{}:
      Some{Unit{}}
    case False{}:
      m

# the request r of the id i, which starts a store or not (start), starts the
# store of the key q
def Root.hit.if(start: Bool, +i: Ledgers.Id, +r: Spec.Request, +q: List<&2, U32>) -> Bool:
  match start:
    case True{}:
      Crits.Key.is_eq(q, RKnown.Root.key(RFacts.Start.root(i, r)))
    case False{}:
      False{}

# the fact f is an ask that starts the store of the key q
def Fact.hit(f: Types.Fact, +q: List<&2, U32>) -> Bool:
  match f:
    case Types.Fact.Vote{v, st, x}:
      False{}
    case Types.Fact.Ask{Types.Ask{+i, n, +r}}:
      Root.hit.if(RFacts.Request.is_start(r), i, r, q)

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a law-only Bool: no code runs it
# an ask among the facts fs starts the store of the key q
def Roots.has(fs: List<&2, Types.Fact>, +q: List<&2, U32>) -> Bool:
  match fs:
    case Nil{}:
      False{}
    case Con{f, rest}:
      Bool.or(Fact.hit(f, q), Roots.has(rest, q))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# each mark is the mark
def Unit.eta(u: Unit) -> {u == Unit{}: Unit}:
  match u:
    case Unit{}:
      {==}

# two roots have one key only when they are one root
def Root.code_eq(
  +j: Hashes.Hash,
  +i: Hashes.Hash
) -> {Crits.Key.is_eq(RKnown.Root.key(i), RKnown.Root.key(j)) == Hashes.Hash.is_eq(j, i): Bool}:
  Lists.Bool.by(
    d => {Crits.Key.is_eq(RKnown.Root.key(i), RKnown.Root.key(j)) == d: Bool},
    Hashes.Hash.is_eq(j, i),
    et => Reads.Eq.back(
      Hashes.Hash,
      y => {Crits.Key.is_eq(RKnown.Root.key(i), RKnown.Root.key(y)) == True{}: Bool},
      j,
      i,
      Hashes.Hash.is_eq_sound(j, i)(et),
      Crits.Key.is_eq_refl(RKnown.Root.key(i))
    ),
    ef => Lists.Bool.by(
      d2 => {d2 == False{}: Bool},
      Crits.Key.is_eq(RKnown.Root.key(i), RKnown.Root.key(j)),
      e2 => Empty.absurd(
        {True{} == False{}: Bool},
        Shared.Bool.true_ne_false(
          Equal.trans(
            Bool,
            True{},
            Hashes.Hash.is_eq(j, j),
            False{},
            Equal.sym(Bool, Hashes.Hash.is_eq(j, j), True{}, Hashes.Hash.is_eq_refl(j)),
            Reads.Eq.to(
              Hashes.Hash,
              y => {Hashes.Hash.is_eq(j, y) == False{}: Bool},
              i,
              j,
              Codes.Code.is_eq_sound(
                ~Hashes.Hash,
                ~Hashes.Hash.code,
                ~Hashes.Hash.code.read,
                ~(a => r => Hashes.Hash.code_read(a, r)),
                i,
                j
              )((
                  %Crits.Key.is_eq_list(RKnown.Root.key(i), RKnown.Root.key(j)): {_ == True{}: Bool}
                  e2)),
              ef
            )
          )
        )
      ),
      e2 => {==}
    )
  )

# Well formed roots
# -----------------

# a request keeps the roots well formed
def Roots.put_wf(
  start: Bool,
  +rx: Crits.Crit<Unit>,
  +i: Ledgers.Id,
  +r: Spec.Request
) -> {
  Crits.Crit.wf(~Unit, rx, 0n) == True{}: Bool
} -> {Crits.Crit.wf(~Unit, RKnown.Roots.put.if(start, rx, i, r), 0n) == True{}: Bool}:
  match start:
    case True{}:
      h => Crits.Crit.upsert_wf(
        ~Unit,
        ~RKnown.Root.keep,
        rx,
        RKnown.Root.key(RFacts.Start.root(i, r)),
        Unit{}
      )(h)
    case False{}:
      h => h

# a fact keeps the roots well formed
def Roots.step_wf(
  +rx: Crits.Crit<Unit>,
  f: Types.Fact
) -> {
  Crits.Crit.wf(~Unit, rx, 0n) == True{}: Bool
} -> {Crits.Crit.wf(~Unit, RKnown.Roots.step(rx, f), 0n) == True{}: Bool}:
  match f:
    case Types.Fact.Vote{v, st, x}:
      h => h
    case Types.Fact.Ask{Types.Ask{+i, n, +r}}:
      h => Roots.put_wf(RFacts.Request.is_start(r), rx, i, r)(h)

# facts keep the roots well formed
def Roots.go_wf(
  fs: List<&2, Types.Fact>,
  +rx: Crits.Crit<Unit>
) -> {
  Crits.Crit.wf(~Unit, rx, 0n) == True{}: Bool
} -> {Crits.Crit.wf(~Unit, RKnown.Roots.go(fs, rx), 0n) == True{}: Bool}:
  match fs:
    case Nil{}:
      h => h
    case Con{+f, rest}:
      h => Roots.go_wf(rest, RKnown.Roots.step(rx, f))(Roots.step_wf(rx, f)(h))

# the roots of facts are well formed
def Roots.of_wf(
  fs: List<&2, Types.Fact>
) -> {Crits.Crit.wf(~Unit, RKnown.Roots.of(fs), 0n) == True{}: Bool}:
  Roots.go_wf(fs, Crits.Crit.new(Unit))(Crits.Crit.new_wf(~Unit))

# What the roots hold
# -------------------

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof does not run
# what the roots hold under the key q after a request: what they held, or a
# mark when the request starts the store of q
def Roots.put_lookup(
  start: Bool,
  +rx: Crits.Crit<Unit>,
  +i: Ledgers.Id,
  +r: Spec.Request,
  +q: List<&2, U32>
) -> {
  Crits.Crit.wf(~Unit, rx, 0n) == True{}: Bool
} -> {
  Crits.Crit.lookup(
    Unit,
    RKnown.Roots.put.if(start, rx, i, r),
    q
  )
    == Roots.or(Crits.Crit.lookup(Unit, rx, q), Root.hit.if(start, i, r, q)): Maybe<&2, Unit>
}:
  match start:
    case True{}:
      h => Equal.trans(
        Maybe<&2, Unit>,
        Crits.Crit.lookup(
          Unit,
          Crits.Crit.upsert(
            ~Unit,
            ~RKnown.Root.keep,
            rx,
            RKnown.Root.key(RFacts.Start.root(i, r)),
            Unit{}
          ),
          q
        ),
        Bool.pick(
          Maybe<&2, Unit>,
          Crits.Key.is_eq(q, RKnown.Root.key(RFacts.Start.root(i, r))),
          Some{
            Crits.Crit.merge(
              ~Unit,
              ~RKnown.Root.keep,
              Crits.Crit.lookup(Unit, rx, RKnown.Root.key(RFacts.Start.root(i, r))),
              Unit{}
            )
          },
          Crits.Crit.lookup(Unit, rx, q)
        ),
        Roots.or(
          Crits.Crit.lookup(Unit, rx, q),
          Crits.Key.is_eq(q, RKnown.Root.key(RFacts.Start.root(i, r)))
        ),
        Crits.Crit.upsert_lookup.lo(
          ~Unit,
          ~RKnown.Root.keep,
          rx,
          0n,
          RKnown.Root.key(RFacts.Start.root(i, r)),
          Unit{},
          q
        )(h),
        Lists.Bool.by(
          d => {
            Bool.pick(
              Maybe<&2, Unit>,
              d,
              Some{
                Crits.Crit.merge(
                  ~Unit,
                  ~RKnown.Root.keep,
                  Crits.Crit.lookup(Unit, rx, RKnown.Root.key(RFacts.Start.root(i, r))),
                  Unit{}
                )
              },
              Crits.Crit.lookup(Unit, rx, q)
            )
              == Roots.or(Crits.Crit.lookup(Unit, rx, q), d): Maybe<&2, Unit>
          },
          Crits.Key.is_eq(q, RKnown.Root.key(RFacts.Start.root(i, r))),
          et => Equal.cong(
            Unit,
            Maybe<&2, Unit>,
            u => Some{u},
            Crits.Crit.merge(
              ~Unit,
              ~RKnown.Root.keep,
              Crits.Crit.lookup(Unit, rx, RKnown.Root.key(RFacts.Start.root(i, r))),
              Unit{}
            ),
            Unit{},
            Unit.eta(
              Crits.Crit.merge(
                ~Unit,
                ~RKnown.Root.keep,
                Crits.Crit.lookup(Unit, rx, RKnown.Root.key(RFacts.Start.root(i, r))),
                Unit{}
              )
            )
          ),
          ef => {==}
        )
      )
    case False{}:
      h => {==}
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# what the roots hold under the key q after a fact: what they held, or a
# mark when the fact starts the store of q
def Roots.step_lookup(
  +rx: Crits.Crit<Unit>,
  f: Types.Fact,
  +q: List<&2, U32>
) -> {
  Crits.Crit.wf(~Unit, rx, 0n) == True{}: Bool
} -> {
  Crits.Crit.lookup(
    Unit,
    RKnown.Roots.step(rx, f),
    q
  )
    == Roots.or(Crits.Crit.lookup(Unit, rx, q), Fact.hit(f, q)): Maybe<&2, Unit>
}:
  match f:
    case Types.Fact.Vote{v, st, x}:
      h => {==}
    case Types.Fact.Ask{Types.Ask{+i, n, +r}}:
      h => Roots.put_lookup(RFacts.Request.is_start(r), rx, i, r, q)(h)

# a mark, or a mark, is a mark when either says so
def Roots.or_or(
  m: Maybe<&2, Unit>,
  a: Bool,
  b: Bool
) -> {Roots.or(Roots.or(m, a), b) == Roots.or(m, Bool.or(a, b)): Maybe<&2, Unit>}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} b:
      {==}

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof does not run
# what the roots hold under the key q after facts: what they held, or a mark
# when an ask among the facts starts the store of q
def Roots.go_lookup(
  fs: List<&2, Types.Fact>,
  +rx: Crits.Crit<Unit>,
  +q: List<&2, U32>
) -> {
  Crits.Crit.wf(~Unit, rx, 0n) == True{}: Bool
} -> {
  Crits.Crit.lookup(
    Unit,
    RKnown.Roots.go(fs, rx),
    q
  )
    == Roots.or(Crits.Crit.lookup(Unit, rx, q), Roots.has(fs, q)): Maybe<&2, Unit>
}:
  match fs:
    case Nil{}:
      h => {==}
    case Con{+f, +rest}:
      +h => Equal.trans(
        Maybe<&2, Unit>,
        Crits.Crit.lookup(Unit, RKnown.Roots.go(rest, RKnown.Roots.step(rx, f)), q),
        Roots.or(Crits.Crit.lookup(Unit, RKnown.Roots.step(rx, f), q), Roots.has(rest, q)),
        Roots.or(Crits.Crit.lookup(Unit, rx, q), Bool.or(Fact.hit(f, q), Roots.has(rest, q))),
        Roots.go_lookup(rest, RKnown.Roots.step(rx, f), q)(Roots.step_wf(rx, f)(h)),
        Equal.trans(
          Maybe<&2, Unit>,
          Roots.or(Crits.Crit.lookup(Unit, RKnown.Roots.step(rx, f), q), Roots.has(rest, q)),
          Roots.or(Roots.or(Crits.Crit.lookup(Unit, rx, q), Fact.hit(f, q)), Roots.has(rest, q)),
          Roots.or(Crits.Crit.lookup(Unit, rx, q), Bool.or(Fact.hit(f, q), Roots.has(rest, q))),
          Equal.cong(
            Maybe<&2, Unit>,
            Maybe<&2, Unit>,
            m => Roots.or(m, Roots.has(rest, q)),
            Crits.Crit.lookup(Unit, RKnown.Roots.step(rx, f), q),
            Roots.or(Crits.Crit.lookup(Unit, rx, q), Fact.hit(f, q)),
            Roots.step_lookup(rx, f, q)(h)
          ),
          Roots.or_or(Crits.Crit.lookup(Unit, rx, q), Fact.hit(f, q), Roots.has(rest, q))
        )
      )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the roots of facts hold a mark under the key q exactly when an ask among
# them starts the store of q
def Roots.of_lookup(
  fs: List<&2, Types.Fact>,
  +q: List<&2, U32>
) -> {
  Crits.Crit.lookup(
    Unit,
    RKnown.Roots.of(fs),
    q
  )
    == Roots.or(None{}, Roots.has(fs, q)): Maybe<&2, Unit>
}:
  Roots.go_lookup(fs, Crits.Crit.new(Unit), q)(Crits.Crit.new_wf(~Unit))

# A fact joins the facts
# ----------------------

# a bit, or itself or another, is the bit or the other
def Bool.or_again(a: Bool, b: Bool) -> {Bool.or(a, Bool.or(a, b)) == Bool.or(a, b): Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# the first of three bits may go second
def Bool.or_swap(
  a: Bool,
  b: Bool,
  c: Bool
) -> {Bool.or(b, Bool.or(a, c)) == Bool.or(a, Bool.or(b, c)): Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof does not run
# the facts xs with the fact f put among them start the store of the key q
# exactly when f or one of xs does
def Roots.has_insert(
  xs: List<&2, Types.Fact>,
  +f: Types.Fact,
  +q: List<&2, U32>
) -> {
  Roots.has(
    Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, xs, f),
    q
  )
    == Bool.or(Fact.hit(f, q), Roots.has(xs, q)): Bool
}:
  match xs:
    case Nil{}:
      {==}
    case Con{+y, +r}:
      Lists.Bool.by(
        d => {
          Roots.has(
            Shared.Bool.when(
              List<&2, Types.Fact>,
              d,
              u => f <> y <> r,
              u => Shared.Bool.when(
                List<&2, Types.Fact>,
                Crits.Key.is_eq(Coded.Fact.words(y), Coded.Fact.words(f)),
                u => f <> r,
                u => y <> Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, r, f)
              )
            ),
            q
          )
            == Bool.or(Fact.hit(f, q), Roots.has(y <> r, q)): Bool
        },
        Orders.Key.lt(Coded.Fact.words(f), Coded.Fact.words(y)),
        et => {==},
        ef => Lists.Bool.by(
          d2 => {
            Roots.has(
              Shared.Bool.when(
                List<&2, Types.Fact>,
                d2,
                u => f <> r,
                u => y <> Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, r, f)
              ),
              q
            )
              == Bool.or(Fact.hit(f, q), Roots.has(y <> r, q)): Bool
          },
          Crits.Key.is_eq(Coded.Fact.words(y), Coded.Fact.words(f)),
          e2 => Reads.Eq.back(
            Types.Fact,
            z => {
              Roots.has(
                f <> r,
                q
              )
                == Bool.or(Fact.hit(f, q), Bool.or(Fact.hit(z, q), Roots.has(r, q))): Bool
            },
            y,
            f,
            Coded.Fact.words_inj(
              y,
              f
            )(Crits.Key.is_eq_sound(Coded.Fact.words(y), Coded.Fact.words(f))(e2)),
            Equal.sym(
              Bool,
              Bool.or(Fact.hit(f, q), Bool.or(Fact.hit(f, q), Roots.has(r, q))),
              Bool.or(Fact.hit(f, q), Roots.has(r, q)),
              Bool.or_again(Fact.hit(f, q), Roots.has(r, q))
            )
          ),
          e2 => Equal.trans(
            Bool,
            Bool.or(
              Fact.hit(y, q),
              Roots.has(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, r, f), q)
            ),
            Bool.or(Fact.hit(y, q), Bool.or(Fact.hit(f, q), Roots.has(r, q))),
            Bool.or(Fact.hit(f, q), Bool.or(Fact.hit(y, q), Roots.has(r, q))),
            Equal.cong(
              Bool,
              Bool,
              b => Bool.or(Fact.hit(y, q), b),
              Roots.has(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, r, f), q),
              Bool.or(Fact.hit(f, q), Roots.has(r, q)),
              Roots.has_insert(r, f, q)
            ),
            Bool.or_swap(Fact.hit(f, q), Fact.hit(y, q), Roots.has(r, q))
          )
        )
      )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof does not run
# the roots of the facts with the fact f put, and the roots of the facts
# with f, hold the same under the key q
def Roots.insert_at(
  +fs: List<&2, Types.Fact>,
  +f: Types.Fact,
  +q: List<&2, U32>
) -> {
  Orders.Binds.get(
    Unit,
    Crits.Crit.entries(
      Unit,
      RKnown.Roots.of(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f))
    ),
    q
  )
    == Orders.Binds.get(
      Unit,
      Crits.Crit.entries(Unit, RKnown.Roots.step(RKnown.Roots.of(fs), f)),
      q
    ): Maybe<&2, Unit>
}:
  Equal.trans(
    Maybe<&2, Unit>,
    Orders.Binds.get(
      Unit,
      Crits.Crit.entries(
        Unit,
        RKnown.Roots.of(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f))
      ),
      q
    ),
    Crits.Crit.lookup(
      Unit,
      RKnown.Roots.of(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f)),
      q
    ),
    Orders.Binds.get(Unit, Crits.Crit.entries(Unit, RKnown.Roots.step(RKnown.Roots.of(fs), f)), q),
    Orders.Crit.get_entries(
      Unit,
      RKnown.Roots.of(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f)),
      q
    ),
    Equal.trans(
      Maybe<&2, Unit>,
      Crits.Crit.lookup(
        Unit,
        RKnown.Roots.of(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f)),
        q
      ),
      Roots.or(None{}, Bool.or(Roots.has(fs, q), Fact.hit(f, q))),
      Orders.Binds.get(
        Unit,
        Crits.Crit.entries(Unit, RKnown.Roots.step(RKnown.Roots.of(fs), f)),
        q
      ),
      (
        %Shared.Bool.or_comm(Fact.hit(f, q), Roots.has(fs, q)): {Crits.Crit.lookup(Unit, RKnown.Roots.of(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f)), q) == Roots.or(None{}, _): Maybe<&2, Unit>}
        %Roots.has_insert(fs, f, q): {Crits.Crit.lookup(Unit, RKnown.Roots.of(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f)), q) == Roots.or(None{}, _): Maybe<&2, Unit>}
        Roots.of_lookup(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f), q)),
      Equal.sym(
        Maybe<&2, Unit>,
        Orders.Binds.get(
          Unit,
          Crits.Crit.entries(Unit, RKnown.Roots.step(RKnown.Roots.of(fs), f)),
          q
        ),
        Roots.or(None{}, Bool.or(Roots.has(fs, q), Fact.hit(f, q))),
        Equal.trans(
          Maybe<&2, Unit>,
          Orders.Binds.get(
            Unit,
            Crits.Crit.entries(Unit, RKnown.Roots.step(RKnown.Roots.of(fs), f)),
            q
          ),
          Crits.Crit.lookup(Unit, RKnown.Roots.step(RKnown.Roots.of(fs), f), q),
          Roots.or(None{}, Bool.or(Roots.has(fs, q), Fact.hit(f, q))),
          Orders.Crit.get_entries(Unit, RKnown.Roots.step(RKnown.Roots.of(fs), f), q),
          Equal.trans(
            Maybe<&2, Unit>,
            Crits.Crit.lookup(Unit, RKnown.Roots.step(RKnown.Roots.of(fs), f), q),
            Roots.or(Roots.or(None{}, Roots.has(fs, q)), Fact.hit(f, q)),
            Roots.or(None{}, Bool.or(Roots.has(fs, q), Fact.hit(f, q))),
            (
              %Roots.of_lookup(fs, q): {Crits.Crit.lookup(Unit, RKnown.Roots.step(RKnown.Roots.of(fs), f), q) == Roots.or(_, Fact.hit(f, q)): Maybe<&2, Unit>}
              Roots.step_lookup(RKnown.Roots.of(fs), f, q)(Roots.of_wf(fs))),
            Roots.or_or(None{}, Roots.has(fs, q), Fact.hit(f, q))
          )
        )
      )
    )
  )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- a proof does not run
# the roots of the facts with the fact f put, and the roots of the facts
# with f, hold the same under the key of each of the entries es
def Roots.insert_same(
  es: List<&2, Crits.Bind<Unit>>,
  +fs: List<&2, Types.Fact>,
  +f: Types.Fact
) -> Orders.Binds.Same(
  Unit,
  es,
  Crits.Crit.entries(
    Unit,
    RKnown.Roots.of(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f))
  ),
  Crits.Crit.entries(Unit, RKnown.Roots.step(RKnown.Roots.of(fs), f))
):
  match es:
    case Nil{}:
      Unit{}
    case Con{Crits.Bind{+q, v}, rest}:
      (Roots.insert_at(fs, f, q), Roots.insert_same(rest, fs, f))
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# the roots of the facts with the fact f put are the roots of the facts
# with f
def Roots.of_insert(
  +fs: List<&2, Types.Fact>,
  +f: Types.Fact
) -> {
  RKnown.Roots.of(
    Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f)
  )
    == RKnown.Roots.step(RKnown.Roots.of(fs), f): Crits.Crit<Unit>
}:
  Crits.Crit.ext(
    ~Unit,
    RKnown.Roots.of(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f)),
    RKnown.Roots.step(RKnown.Roots.of(fs), f)
  )(
    Roots.of_wf(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f))
  )(
    Roots.step_wf(RKnown.Roots.of(fs), f)(Roots.of_wf(fs))
  )(
    Orders.Binds.ext(
      ~Unit,
      Crits.Crit.entries(
        Unit,
        RKnown.Roots.of(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f))
      ),
      Crits.Crit.entries(Unit, RKnown.Roots.step(RKnown.Roots.of(fs), f))
    )(
      Orders.Crit.entries_sorted(
        ~Unit,
        RKnown.Roots.of(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f))
      )(Roots.of_wf(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f)))
    )(
      Orders.Crit.entries_sorted(
        ~Unit,
        RKnown.Roots.step(RKnown.Roots.of(fs), f)
      )(Roots.step_wf(RKnown.Roots.of(fs), f)(Roots.of_wf(fs)))
    )(
      Roots.insert_same(
        Crits.Crit.entries(
          Unit,
          RKnown.Roots.of(Orders.Values.insert(~Types.Fact, ~Coded.Fact.words, fs, f))
        ),
        fs,
        f
      )
    )(Roots.insert_same(Crits.Crit.entries(Unit, RKnown.Roots.step(RKnown.Roots.of(fs), f)), fs, f))
  )

# A request that starts a store
# -----------------------------

# Starts.has_empty, once the ask is known to start a store or not (start)
def Starts.has_empty.at(
  start: Bool,
  +i: Ledgers.Id,
  +n: Nat,
  +r: Spec.Request,
  +rest: List<&2, Types.Fact>,
  +h: Hashes.Hash
) -> {
  List.is_empty(
    &2,
    Types.Ask,
    RLines.Starts.of(rest, h)
  )
    == Bool.not(Roots.has(rest, RKnown.Root.key(h))): Bool
} -> {
  List.is_empty(
    &2,
    Types.Ask,
    List.filter.put(
      Types.Ask,
      Types.Ask{i, n, r},
      RLines.Starts.of(rest, h),
      Shared.Bool.when(
        Bool,
        start,
        u => Hashes.Hash.is_eq(RFacts.Start.root(i, r), h),
        u => False{}
      )
    )
  )
    == Bool.not(
      Bool.or(Root.hit.if(start, i, r, RKnown.Root.key(h)), Roots.has(rest, RKnown.Root.key(h)))
    ): Bool
}:
  match start:
    case True{}:
      e => (
        %Equal.sym(Bool, Crits.Key.is_eq(RKnown.Root.key(h), RKnown.Root.key(RFacts.Start.root(i, r))), Hashes.Hash.is_eq(RFacts.Start.root(i, r), h), Root.code_eq(RFacts.Start.root(i, r), h)): {List.is_empty(&2, Types.Ask, List.filter.put(Types.Ask, Types.Ask{i, n, r}, RLines.Starts.of(rest, h), Hashes.Hash.is_eq(RFacts.Start.root(i, r), h))) == Bool.not(Bool.or(_, Roots.has(rest, RKnown.Root.key(h)))): Bool}
        Lists.Bool.by(d => {List.is_empty(&2, Types.Ask, List.filter.put(Types.Ask, Types.Ask{i, n, r}, RLines.Starts.of(rest, h), d)) == Bool.not(Bool.or(d, Roots.has(rest, RKnown.Root.key(h)))): Bool}, Hashes.Hash.is_eq(RFacts.Start.root(i, r), h), et => {==}, ef => e))
    case False{}:
      e => e

# the asks among fs that start the store of the root h are none exactly when
# no ask among fs starts the store of its key
def Starts.has_empty(
  fs: List<&2, Types.Fact>,
  +h: Hashes.Hash
) -> {
  List.is_empty(
    &2,
    Types.Ask,
    RLines.Starts.of(fs, h)
  )
    == Bool.not(Roots.has(fs, RKnown.Root.key(h))): Bool
}:
  match fs:
    case Nil{}:
      {==}
    case Con{Types.Fact.Vote{v, st, x}, rest}:
      Starts.has_empty(rest, h)
    case Con{Types.Fact.Ask{Types.Ask{+i, +n, +r}}, +rest}:
      Starts.has_empty.at(RFacts.Request.is_start(r), i, n, r, rest, h)(Starts.has_empty(rest, h))

# no mark, or a mark, is no mark exactly when the bit is not set
def Roots.or_none(b: Bool) -> {Maybe.is_none(&2, Unit, Roots.or(None{}, b)) == Bool.not(b): Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# Roots.fresh_ok, once the request is known to start a store or not (start)
def Roots.fresh_ok.at(
  start: Bool,
  +s: RFacts.Plain(),
  +i: Ledgers.Id,
  +r: Spec.Request
) -> {
  RKnown.Roots.fresh.if(
    start,
    RKnown.Roots.of(RFacts.Facts.list(s)),
    i,
    r
  )
    == RLines.Request.fresh.if(start, s, i, r): Bool
}:
  match start:
    case True{}:
      (
        %Equal.sym(Maybe<&2, Unit>, Crits.Crit.get(Unit, RKnown.Roots.of(RFacts.Facts.list(s)), RKnown.Root.key(RFacts.Start.root(i, r))), Crits.Crit.lookup(Unit, RKnown.Roots.of(RFacts.Facts.list(s)), RKnown.Root.key(RFacts.Start.root(i, r))), Crits.Crit.get_lookup(~Unit, RKnown.Roots.of(RFacts.Facts.list(s)), RKnown.Root.key(RFacts.Start.root(i, r)))(Roots.of_wf(RFacts.Facts.list(s)))): {Maybe.is_none(&2, Unit, _) == List.is_empty(&2, Types.Ask, RLines.Starts.of(RFacts.Facts.list(s), RFacts.Start.root(i, r))): Bool}
        %Equal.sym(Maybe<&2, Unit>, Crits.Crit.lookup(Unit, RKnown.Roots.of(RFacts.Facts.list(s)), RKnown.Root.key(RFacts.Start.root(i, r))), Roots.or(None{}, Roots.has(RFacts.Facts.list(s), RKnown.Root.key(RFacts.Start.root(i, r)))), Roots.of_lookup(RFacts.Facts.list(s), RKnown.Root.key(RFacts.Start.root(i, r)))): {Maybe.is_none(&2, Unit, _) == List.is_empty(&2, Types.Ask, RLines.Starts.of(RFacts.Facts.list(s), RFacts.Start.root(i, r))): Bool}
        %Equal.sym(Bool, List.is_empty(&2, Types.Ask, RLines.Starts.of(RFacts.Facts.list(s), RFacts.Start.root(i, r))), Bool.not(Roots.has(RFacts.Facts.list(s), RKnown.Root.key(RFacts.Start.root(i, r)))), Starts.has_empty(RFacts.Facts.list(s), RFacts.Start.root(i, r))): {Maybe.is_none(&2, Unit, Roots.or(None{}, Roots.has(RFacts.Facts.list(s), RKnown.Root.key(RFacts.Start.root(i, r))))) == _: Bool}
        Roots.or_none(Roots.has(RFacts.Facts.list(s), RKnown.Root.key(RFacts.Start.root(i, r)))))
    case False{}:
      {==}

# the roots of the facts s say that a request starts no store that s start
# exactly when s say so
def Roots.fresh_ok(
  +s: RFacts.Plain(),
  +i: Ledgers.Id,
  +r: Spec.Request
) -> {
  RKnown.Roots.fresh(
    RKnown.Roots.of(RFacts.Facts.list(s)),
    i,
    r
  )
    == RLines.Request.fresh(s, i, r): Bool
}:
  Roots.fresh_ok.at(RFacts.Request.is_start(r), s, i, r)

# Same roots
# ----------

# a mark, if any, is there exactly when it is there
def Mark.same_sound(
  a: Maybe<&2, Unit>,
  b: Maybe<&2, Unit>
) -> {
  Shared.Bool.is_eq(Maybe.is_some(&2, Unit, a), Maybe.is_some(&2, Unit, b)) == True{}: Bool
} -> {a == b: Maybe<&2, Unit>}:
  match a b:
    case None{} None{}:
      h => {==}
    case None{} Some{y}:
      h => Empty.absurd({None{} == Some{y}: Maybe<&2, Unit>}, Shared.Bool.false_ne_true(h))
    case Some{x} None{}:
      h => Empty.absurd({Some{x} == None{}: Maybe<&2, Unit>}, Shared.Bool.false_ne_true(h))
    case Some{Unit{}} Some{Unit{}}:
      h => {==}

# Roots.same is True for roots and themselves
def Roots.same_refl(a: Crits.Crit<Unit>) -> {RKnown.Roots.same(a, a) == True{}: Bool}:
  match a:
    case Crits.Crit.Tip{}:
      {==}
    case Crits.Crit.Leaf{+k, v}:
      Crits.Key.is_eq_refl(k)
    case Crits.Crit.Fork{+r, +p, +e, +z, +o}:
      (
        %Equal.sym(Bool, Crits.Key.is_eq(r, r), True{}, Crits.Key.is_eq_refl(r)): {List.all.if(u => List.all.if(u2 => List.all.if(u3 => List.all.if(u4 => RKnown.Roots.same(o, o), RKnown.Roots.same(z, z)), Shared.Bool.is_eq(Maybe.is_some(&2, Unit, e), Maybe.is_some(&2, Unit, e))), Nat.is_eq(p, p)), _) == True{}: Bool}
        %Equal.sym(Bool, Nat.is_eq(p, p), True{}, Shared.Nat.is_eq_refl(p)): {List.all.if(u2 => List.all.if(u3 => List.all.if(u4 => RKnown.Roots.same(o, o), RKnown.Roots.same(z, z)), Shared.Bool.is_eq(Maybe.is_some(&2, Unit, e), Maybe.is_some(&2, Unit, e))), _) == True{}: Bool}
        %Equal.sym(Bool, Shared.Bool.is_eq(Maybe.is_some(&2, Unit, e), Maybe.is_some(&2, Unit, e)), True{}, Shared.Bool.is_eq_refl(Maybe.is_some(&2, Unit, e))): {List.all.if(u3 => List.all.if(u4 => RKnown.Roots.same(o, o), RKnown.Roots.same(z, z)), _) == True{}: Bool}
        %Equal.sym(Bool, RKnown.Roots.same(z, z), True{}, Roots.same_refl(z)): {List.all.if(u4 => RKnown.Roots.same(o, o), _) == True{}: Bool}
        Roots.same_refl(o))

# a lazy "and" that is True has its left side True
def All.left(a: Bool, -b: Bool) -> {List.all.if(u => b, a) == True{}: Bool} -> {a == True{}: Bool}:
  match a:
    case True{}:
      h => {==}
    case False{}:
      h => Empty.absurd({False{} == True{}: Bool}, Shared.Bool.false_ne_true(h))

# a lazy "and" that is True has its right side True
def All.right(a: Bool, b: Bool) -> {List.all.if(u => b, a) == True{}: Bool} -> {b == True{}: Bool}:
  match a:
    case True{}:
      h => h
    case False{}:
      h => Empty.absurd({b == True{}: Bool}, Shared.Bool.false_ne_true(h))

# Roots.same is True only for equal roots
def Roots.same_sound(
  a: Crits.Crit<Unit>,
  b: Crits.Crit<Unit>
) -> {RKnown.Roots.same(a, b) == True{}: Bool} -> {a == b: Crits.Crit<Unit>}:
  match a b:
    case Crits.Crit.Tip{} Crits.Crit.Tip{}:
      h => {==}
    case Crits.Crit.Tip{} Crits.Crit.Leaf{k2, v2}:
      h => Empty.absurd(
        {Crits.Crit.Tip{} == Crits.Crit.Leaf{k2, v2}: Crits.Crit<Unit>},
        Shared.Bool.false_ne_true(h)
      )
    case Crits.Crit.Tip{} Crits.Crit.Fork{r2, p2, e2, z2, o2}:
      h => Empty.absurd(
        {Crits.Crit.Tip{} == Crits.Crit.Fork{r2, p2, e2, z2, o2}: Crits.Crit<Unit>},
        Shared.Bool.false_ne_true(h)
      )
    case Crits.Crit.Leaf{k1, v1} Crits.Crit.Tip{}:
      h => Empty.absurd(
        {Crits.Crit.Leaf{k1, v1} == Crits.Crit.Tip{}: Crits.Crit<Unit>},
        Shared.Bool.false_ne_true(h)
      )
    case Crits.Crit.Leaf{k1, v1} Crits.Crit.Fork{r2, p2, e2, z2, o2}:
      h => Empty.absurd(
        {Crits.Crit.Leaf{k1, v1} == Crits.Crit.Fork{r2, p2, e2, z2, o2}: Crits.Crit<Unit>},
        Shared.Bool.false_ne_true(h)
      )
    case Crits.Crit.Fork{r1, p1, e1, z1, o1} Crits.Crit.Tip{}:
      h => Empty.absurd(
        {Crits.Crit.Fork{r1, p1, e1, z1, o1} == Crits.Crit.Tip{}: Crits.Crit<Unit>},
        Shared.Bool.false_ne_true(h)
      )
    case Crits.Crit.Fork{r1, p1, e1, z1, o1} Crits.Crit.Leaf{k2, v2}:
      h => Empty.absurd(
        {Crits.Crit.Fork{r1, p1, e1, z1, o1} == Crits.Crit.Leaf{k2, v2}: Crits.Crit<Unit>},
        Shared.Bool.false_ne_true(h)
      )
    case Crits.Crit.Leaf{+k1, Unit{}} Crits.Crit.Leaf{+k2, Unit{}}:
      h => (
        %Crits.Key.is_eq_sound(k1, k2)(h): {Crits.Crit.Leaf{k1, Unit{}} == Crits.Crit.Leaf{_, Unit{}}: Crits.Crit<Unit>}
        {==})
    case Crits.Crit.Fork{+r1, +p1, +e1, +z1, +o1} Crits.Crit.Fork{+r2, +p2, +e2, +z2, +o2}:
      +h => (
        %Crits.Key.is_eq_sound(r1, r2)(All.left(Crits.Key.is_eq(r1, r2), List.all.if(u2 => List.all.if(u3 => List.all.if(u4 => RKnown.Roots.same(o1, o2), RKnown.Roots.same(z1, z2)), Shared.Bool.is_eq(Maybe.is_some(&2, Unit, e1), Maybe.is_some(&2, Unit, e2))), Nat.is_eq(p1, p2)))(h)): {Crits.Crit.Fork{r1, p1, e1, z1, o1} == Crits.Crit.Fork{_, p2, e2, z2, o2}: Crits.Crit<Unit>}
        %Shared.Nat.is_eq_sound(p1, p2)(All.left(Nat.is_eq(p1, p2), List.all.if(u3 => List.all.if(u4 => RKnown.Roots.same(o1, o2), RKnown.Roots.same(z1, z2)), Shared.Bool.is_eq(Maybe.is_some(&2, Unit, e1), Maybe.is_some(&2, Unit, e2))))(All.right(Crits.Key.is_eq(r1, r2), List.all.if(u2 => List.all.if(u3 => List.all.if(u4 => RKnown.Roots.same(o1, o2), RKnown.Roots.same(z1, z2)), Shared.Bool.is_eq(Maybe.is_some(&2, Unit, e1), Maybe.is_some(&2, Unit, e2))), Nat.is_eq(p1, p2)))(h))): {Crits.Crit.Fork{r1, p1, e1, z1, o1} == Crits.Crit.Fork{r1, _, e2, z2, o2}: Crits.Crit<Unit>}
        %Mark.same_sound(e1, e2)(All.left(Shared.Bool.is_eq(Maybe.is_some(&2, Unit, e1), Maybe.is_some(&2, Unit, e2)), List.all.if(u4 => RKnown.Roots.same(o1, o2), RKnown.Roots.same(z1, z2)))(All.right(Nat.is_eq(p1, p2), List.all.if(u3 => List.all.if(u4 => RKnown.Roots.same(o1, o2), RKnown.Roots.same(z1, z2)), Shared.Bool.is_eq(Maybe.is_some(&2, Unit, e1), Maybe.is_some(&2, Unit, e2))))(All.right(Crits.Key.is_eq(r1, r2), List.all.if(u2 => List.all.if(u3 => List.all.if(u4 => RKnown.Roots.same(o1, o2), RKnown.Roots.same(z1, z2)), Shared.Bool.is_eq(Maybe.is_some(&2, Unit, e1), Maybe.is_some(&2, Unit, e2))), Nat.is_eq(p1, p2)))(h)))): {Crits.Crit.Fork{r1, p1, e1, z1, o1} == Crits.Crit.Fork{r1, p1, _, z2, o2}: Crits.Crit<Unit>}
        %Roots.same_sound(z1, z2)(All.left(RKnown.Roots.same(z1, z2), RKnown.Roots.same(o1, o2))(All.right(Shared.Bool.is_eq(Maybe.is_some(&2, Unit, e1), Maybe.is_some(&2, Unit, e2)), List.all.if(u4 => RKnown.Roots.same(o1, o2), RKnown.Roots.same(z1, z2)))(All.right(Nat.is_eq(p1, p2), List.all.if(u3 => List.all.if(u4 => RKnown.Roots.same(o1, o2), RKnown.Roots.same(z1, z2)), Shared.Bool.is_eq(Maybe.is_some(&2, Unit, e1), Maybe.is_some(&2, Unit, e2))))(All.right(Crits.Key.is_eq(r1, r2), List.all.if(u2 => List.all.if(u3 => List.all.if(u4 => RKnown.Roots.same(o1, o2), RKnown.Roots.same(z1, z2)), Shared.Bool.is_eq(Maybe.is_some(&2, Unit, e1), Maybe.is_some(&2, Unit, e2))), Nat.is_eq(p1, p2)))(h))))): {Crits.Crit.Fork{r1, p1, e1, z1, o1} == Crits.Crit.Fork{r1, p1, e1, _, o2}: Crits.Crit<Unit>}
        %Roots.same_sound(o1, o2)(All.right(RKnown.Roots.same(z1, z2), RKnown.Roots.same(o1, o2))(All.right(Shared.Bool.is_eq(Maybe.is_some(&2, Unit, e1), Maybe.is_some(&2, Unit, e2)), List.all.if(u4 => RKnown.Roots.same(o1, o2), RKnown.Roots.same(z1, z2)))(All.right(Nat.is_eq(p1, p2), List.all.if(u3 => List.all.if(u4 => RKnown.Roots.same(o1, o2), RKnown.Roots.same(z1, z2)), Shared.Bool.is_eq(Maybe.is_some(&2, Unit, e1), Maybe.is_some(&2, Unit, e2))))(All.right(Crits.Key.is_eq(r1, r2), List.all.if(u2 => List.all.if(u3 => List.all.if(u4 => RKnown.Roots.same(o1, o2), RKnown.Roots.same(z1, z2)), Shared.Bool.is_eq(Maybe.is_some(&2, Unit, e1), Maybe.is_some(&2, Unit, e2))), Nat.is_eq(p1, p2)))(h))))): {Crits.Crit.Fork{r1, p1, e1, z1, o1} == Crits.Crit.Fork{r1, p1, e1, z1, _}: Crits.Crit<Unit>}
        {==})
