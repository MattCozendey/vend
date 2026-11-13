import Base
import ../shared/shared/ledger.bend as Ledgers
import ../shared/shared/shared/shared/hash.bend as Hashes
import ../shared/shared/shared/shared/shared.bend as Shared
import ../shared/shared/shared/text.bend as Texts
import ./codes.bend as Coded
import ./facts.bend as Facts
import ./groups.bend as Groups
import ./lines.bend as Lines
import ./shared/lists.bend as Lists
import ./spec.bend as Spec
import ./types.bend as Types

# What the versions of a line are
# -------------------------------
# Facts about the versions that the facts of a node decide, in one set of
# facts.

# The run of a line
# -----------------

# what a decided slot of the state a gives: the pick pk that it decided, and
# the state b after it
def Step.Made(s: Facts.Facts(), c: Ledgers.Line, a: Lines.State, b: Lines.State, u: Lines.Rule) -> Type:
  Exists(
    Types.Pick,
    pk => {
      Lines.Votes.decided(s, Types.Step.At{c, Lines.State.slot(a)}, Lines.Rule.nodes(u)) == Some{pk}: Maybe<&2, Types.Pick>
    }
      & {Lines.State.put(Lines.State.versions(a), Lines.State.slot(a), pk) == b: Lines.State}
  )

# a state after the next slot of a comes from a decided pick d
def Step.of_inv(a: Lines.State, -b: Lines.State, d: Maybe<&2, Types.Pick>) -> {
  Lines.Line.step.of(a, d) == Some{b}: Maybe<&2, Lines.State>
} -> Exists(
  Types.Pick,
  pk => {d == Some{pk}: Maybe<&2, Types.Pick>}
    & {Lines.State.put(Lines.State.versions(a), Lines.State.slot(a), pk) == b: Lines.State}
):
  match a d:
    case Lines.State{+vs, +k} None{}:
      h => Empty.absurd(
        Exists(
          Types.Pick,
          pk => {None{} == Some{pk}: Maybe<&2, Types.Pick>} & {Lines.State.put(vs, k, pk) == b: Lines.State}
        ),
        Shared.Maybe.none_ne_some(Lines.State, b, h)
      )
    case Lines.State{+vs, +k} Some{+pk}:
      h => (pk, ({==}, Shared.Maybe.some_inj(Lines.State, Lines.State.put(vs, k, pk), b, h)))

# a state after the next slot of a comes from a rule m and the pick that its
# nodes decided
def Step.at_inv(+s: Facts.Facts(), +c: Ledgers.Line, +a: Lines.State, -b: Lines.State, m: Maybe<&2, Lines.Rule>) -> {
  Lines.Line.step.at(s, c, a, m) == Some{b}: Maybe<&2, Lines.State>
} -> Exists(Lines.Rule, u => {m == Some{u}: Maybe<&2, Lines.Rule>} & Step.Made(s, c, a, b, u)):
  match m:
    case None{}:
      h => Empty.absurd(
        Exists(Lines.Rule, u => {None{} == Some{u}: Maybe<&2, Lines.Rule>} & Step.Made(s, c, a, b, u)),
        Shared.Maybe.none_ne_some(Lines.State, b, h)
      )
    case Some{+u}:
      h => (
        u,
        (
          {==},
          Step.of_inv(
            a,
            b,
            Lines.Votes.decided(s, Types.Step.At{c, Lines.State.slot(a)}, Lines.Rule.nodes(u))
          )(h)
        )
      )

# Step.at_inv, as what follows from it
def Step.at_by(
  -Q: Type,
  -s: Facts.Facts(),
  -c: Ledgers.Line,
  -a: Lines.State,
  -b: Lines.State,
  -m: Maybe<&2, Lines.Rule>,
  r: Exists(Lines.Rule, u => {m == Some{u}: Maybe<&2, Lines.Rule>} & Step.Made(s, c, a, b, u)),
  k: @u: Lines.Rule -> @pk: Types.Pick -> {m == Some{u}: Maybe<&2, Lines.Rule>} -> {
    Lines.Votes.decided(s, Types.Step.At{c, Lines.State.slot(a)}, Lines.Rule.nodes(u)) == Some{pk}: Maybe<&2, Types.Pick>
  } -> {Lines.State.put(Lines.State.versions(a), Lines.State.slot(a), pk) == b: Lines.State} -> Q
) -> Q:
  (u, w) = r
  (eu, w2) = w
  (pk, w3) = w2
  (ed, eb) = w3
  k(u)(pk)(eu)(ed)(eb)

# what holds of a state, and of the state after each decided slot of a state
# that it holds of, holds of the state after a run
def Run.keeps(
  ~V: Data,
  ~P: V -> Facts.Facts() -> Maybe<&2, List<&2, Types.Entry>> -> Ledgers.Line -> Lines.State -> Type,
  ~step: @+g: V -> @+s: Facts.Facts() -> @+R: Maybe<&2, List<&2, Types.Entry>> -> @+c: Ledgers.Line -> @+a: Lines.State -> @+u: Lines.Rule -> @+pk: Types.Pick -> {
    Lines.Line.rule(R, c, Lines.State.versions(a)) == Some{u}: Maybe<&2, Lines.Rule>
  } -> {
    Lines.Votes.decided(s, Types.Step.At{c, Lines.State.slot(a)}, Lines.Rule.nodes(u)) == Some{pk}: Maybe<&2, Types.Pick>
  } -> P(g)(s)(R)(c)(a) -> P(g)(s)(R)(c)(Lines.State.put(Lines.State.versions(a), Lines.State.slot(a), pk)),
  f: Nat,
  +g: V,
  +s: Facts.Facts(),
  +R: Maybe<&2, List<&2, Types.Entry>>,
  +c: Ledgers.Line,
  +st: Lines.State,
  base: P(g)(s)(R)(c)(st)
) -> P(g)(s)(R)(c)(Lines.Line.run(f, s, R, c, st, Lines.Line.step(s, R, c, st))):
  match f:
    case 0n:
      base
    case 1n+(+p):
      Lists.Maybe.by(
        Lines.State,
        m => P(g)(s)(R)(c)(st) -> P(g)(s)(R)(c)(Lines.Line.run(1n+p, s, R, c, st, m)),
        Lines.Line.step(s, R, c, st),
        en => b => b,
        +st2 => e => b => Step.at_by(
          P(g)(s)(R)(c)(Lines.Line.run(p, s, R, c, st2, Lines.Line.step(s, R, c, st2))),
          s,
          c,
          st,
          st2,
          Lines.Line.rule(R, c, Lines.State.versions(st)),
          Step.at_inv(s, c, st, st2, Lines.Line.rule(R, c, Lines.State.versions(st)))(e),
          +u => +pk => eu => ed => eb => (
            %eb: P(g)(s)(R)(c)(Lines.Line.run(p, s, R, c, _, Lines.Line.step(s, R, c, _)))
            Run.keeps(
              ~V,
              ~P,
              ~step,
              p,
              g,
              s,
              R,
              c,
              Lines.State.put(Lines.State.versions(st), Lines.State.slot(st), pk),
              step(g)(s)(R)(c)(st)(u)(pk)(eu)(ed)(b)
            )
          )
        )
      )(base)

# the versions after a decided slot extend the versions before it
def Put.ext(+vs: List<&2, Types.Entry>, +k: Nat, +pk: Types.Pick) -> Lists.List.Ext(
  Types.Entry,
  vs,
  Lines.State.versions(Lines.State.put(vs, k, pk))
):
  Lists.Bool.by(
    d => Lists.List.Ext(Types.Entry, vs, Lines.State.versions(Lines.State.put.if(vs, k, pk, d))),
    Shared.List.some(~Types.Entry, ~Ledgers.Id, ~Lines.Entry.is_of, vs, Lines.Pick.id(pk)),
    et => Lists.List.ext_refl(Types.Entry, vs),
    ef => Lists.List.ext_snoc(Types.Entry, vs, Types.Entry{pk, k})
  )

# the versions of a state extend g
def Run.Ext(g: List<&2, Types.Entry>, s: Facts.Facts(), R: Maybe<&2, List<&2, Types.Entry>>, c: Ledgers.Line, a: Lines.State) -> Type:
  Lists.List.Ext(Types.Entry, g, Lines.State.versions(a))

# a decided slot keeps Run.Ext
def Run.ext_step(+g: List<&2, Types.Entry>, +s: Facts.Facts(), +R: Maybe<&2, List<&2, Types.Entry>>, +c: Ledgers.Line, +a: Lines.State, +u: Lines.Rule, +pk: Types.Pick) -> {
  Lines.Line.rule(R, c, Lines.State.versions(a)) == Some{u}: Maybe<&2, Lines.Rule>
} -> {
  Lines.Votes.decided(s, Types.Step.At{c, Lines.State.slot(a)}, Lines.Rule.nodes(u)) == Some{pk}: Maybe<&2, Types.Pick>
} -> Run.Ext(g, s, R, c, a) -> Run.Ext(g, s, R, c, Lines.State.put(Lines.State.versions(a), Lines.State.slot(a), pk)):
  eu => ed => p => Lists.List.ext_trans(
    Types.Entry,
    g,
    Lines.State.versions(a),
    Lines.State.versions(Lines.State.put(Lines.State.versions(a), Lines.State.slot(a), pk))
  )(p)(Put.ext(Lines.State.versions(a), Lines.State.slot(a), pk))

# the versions after a run extend the versions before it
def Run.ext(+s: Facts.Facts(), +R: Maybe<&2, List<&2, Types.Entry>>, +c: Ledgers.Line, +st: Lines.State) -> Lists.List.Ext(
  Types.Entry,
  Lines.State.versions(st),
  Lines.State.versions(Lines.Line.start(s, R, c, st))
):
  Run.keeps(
    ~List<&2, Types.Entry>,
    ~Run.Ext,
    ~Run.ext_step,
    Lines.Line.bound(Facts.Facts.list(s), c),
    Lines.State.versions(st),
    s,
    R,
    c,
    st,
    Lists.List.ext_refl(Types.Entry, Lines.State.versions(st))
  )

# Version 0
# ---------

# the entry e is an ask of the number 0 whose request opens a line
def Entry.Opens(e: Types.Entry) -> Type:
  {Facts.Ask.seq(Lines.Entry.ask(e)) == 0n: Nat}
    & {Lines.Request.opens(Lines.Ask.request(Lines.Entry.ask(e))) == True{}: Bool}

# a request that makes a group the owner of a line opens a line
def Request.owns_opens(c: Ledgers.Line, r: Spec.Request) -> {Lines.Request.owns(c, r) == True{}: Bool} -> {
  Lines.Request.opens(r) == True{}: Bool
}:
  match r:
    case Spec.Request.Own{c2, g}:
      h => {==}
    case Spec.Request.Start{os}:
      h => {==}
    case Spec.Request.Write{x0, x1, x2}:
      h => h
    case Spec.Request.Merge{x0, x1}:
      h => h
    case Spec.Request.Resolve{x0, x1, x2}:
      h => h
    case Spec.Request.Mark{x0, x1, x2}:
      h => h
    case Spec.Request.Move{x0, x1, x2}:
      h => h
    case Spec.Request.Group{x0, x1, x2}:
      h => h

# a request that starts a store opens a line
def Request.start_opens(r: Spec.Request) -> {Facts.Request.is_start(r) == True{}: Bool} -> {
  Lines.Request.opens(r) == True{}: Bool
}:
  match r:
    case Spec.Request.Start{os}:
      h => {==}
    case Spec.Request.Own{c2, g}:
      h => {==}
    case Spec.Request.Write{x0, x1, x2}:
      h => h
    case Spec.Request.Merge{x0, x1}:
      h => h
    case Spec.Request.Resolve{x0, x1, x2}:
      h => h
    case Spec.Request.Mark{x0, x1, x2}:
      h => h
    case Spec.Request.Move{x0, x1, x2}:
      h => h
    case Spec.Request.Group{x0, x1, x2}:
      h => h

# each of the asks that start a store starts it
def Starts.of_in(fs: List<&2, Types.Fact>, +h: Hashes.Hash, +a: Types.Ask) -> {
  List.contains(~Types.Ask, ~Coded.Ask.is_eq, Lines.Starts.of(fs, h), a) == True{}: Bool
} -> {Facts.Ask.starts(h, a) == True{}: Bool}:
  match fs:
    case Nil{}:
      hin => Empty.absurd({Facts.Ask.starts(h, a) == True{}: Bool}, Shared.Bool.false_ne_true(hin))
    case Con{Types.Fact.Vote{v, st, pk}, rest}:
      hin => Starts.of_in(rest, h, a)(hin)
    case Con{Types.Fact.Ask{+b}, +rest}:
      Lists.Bool.by(
        d => {
          List.contains(~Types.Ask, ~Coded.Ask.is_eq, List.filter.put(Types.Ask, b, Lines.Starts.of(rest, h), d), a) == True{}: Bool
        } -> {Facts.Ask.starts(h, a) == True{}: Bool},
        Facts.Ask.starts(h, b),
        et => hin => Lists.List.contains_cons_by(
          ~Types.Ask,
          ~Coded.Ask.is_eq,
          ~Coded.Ask.laws(),
          {Facts.Ask.starts(h, a) == True{}: Bool},
          b,
          Lines.Starts.of(rest, h),
          a,
          hin,
          e => (
            %e: {Facts.Ask.starts(h, _) == True{}: Bool}
            et
          ),
          cin => Starts.of_in(rest, h, a)(cin)
        ),
        ef => hin => Starts.of_in(rest, h, a)(hin)
      )

# what version 0 of a store comes from: an ask among the starts of the store
# that leads them
def Store.First(fs: List<&2, Types.Fact>, h: Hashes.Hash, e0: Types.Entry) -> Type:
  Exists(
    Types.Ask,
    a => {
      List.contains(~Types.Ask, ~Coded.Ask.is_eq, Lines.Starts.of(fs, h), a) == True{}: Bool
    }
      & (
        {
          Lines.Ask.leads(Lines.Starts.of(fs, h), a) == True{}: Bool
        }
          & {Lines.Store.first.of(Some{a}) == Some{e0}: Maybe<&2, Types.Entry>}
      )
  )

# version 0 of a store comes from an ask among its starts that leads them
def Store.first_inv(+fs: List<&2, Types.Fact>, +h: Hashes.Hash, -e0: Types.Entry) -> {
  Lines.Store.first(fs, h) == Some{e0}: Maybe<&2, Types.Entry>
} -> Store.First(fs, h, e0):
  Lists.Maybe.by(
    Types.Ask,
    m => {Lines.Store.first.of(m) == Some{e0}: Maybe<&2, Types.Entry>} -> Exists(
      Types.Ask,
      a => {
        List.contains(~Types.Ask, ~Coded.Ask.is_eq, Lines.Starts.of(fs, h), a) == True{}: Bool
      }
        & (
          {
            Lines.Ask.leads(Lines.Starts.of(fs, h), a) == True{}: Bool
          }
            & {Lines.Store.first.of(Some{a}) == Some{e0}: Maybe<&2, Types.Entry>}
        )
    ),
    Lists.List.pick(~Types.Ask, ~List<&2, Types.Ask>, ~Lines.Ask.leads, Lines.Starts.of(fs, h), Lines.Starts.of(fs, h)),
    en => hh => Empty.absurd(Store.First(fs, h, e0), Shared.Maybe.none_ne_some(Types.Entry, e0, hh)),
    +a => +ep => hh => (
      a,
      (
        Lists.List.pick_in(
          ~Types.Ask,
          ~List<&2, Types.Ask>,
          ~Lines.Ask.leads,
          ~Coded.Ask.is_eq,
          ~Coded.Ask.laws(),
          Lines.Starts.of(fs, h),
          Lines.Starts.of(fs, h),
          a
        )(ep),
        (
          Lists.List.pick_hit(
            ~Types.Ask,
            ~List<&2, Types.Ask>,
            ~Lines.Ask.leads,
            Lines.Starts.of(fs, h),
            Lines.Starts.of(fs, h),
            a
          )(ep),
          hh
        )
      )
    )
  )

# the entry that an ask that starts a store gives opens a line
def Store.first_opens.at(+h: Hashes.Hash, a: Types.Ask, -e0: Types.Entry) -> {
  Facts.Ask.starts(h, a) == True{}: Bool
} -> {Lines.Store.first.of(Some{a}) == Some{e0}: Maybe<&2, Types.Entry>} -> Entry.Opens(e0):
  match a:
    case Types.Ask{+i, +k, +r}:
      hs => e => (
        %Shared.Maybe.some_inj(Types.Entry, Lines.Entry.first(i, r, 0n), e0, e): Entry.Opens(_)
        (
          {==},
          Request.start_opens(r)(
            Shared.Bool.and_true_left(
              Facts.Request.is_start(r),
              Hashes.Hash.is_eq(Facts.Start.root(i, r), h)
            )(hs)
          )
        )
      )

# Store.first_opens, from where version 0 comes from
def Store.first_opens.of(+fs: List<&2, Types.Fact>, +h: Hashes.Hash, -e0: Types.Entry, r: Store.First(fs, h, e0)) -> Entry.Opens(
  e0
):
  (+a, w) = r
  (hin, w2) = w
  (hl, e) = w2
  Store.first_opens.at(h, a, e0)(Starts.of_in(fs, h, a)(hin))(e)

# version 0 of a store opens a line
def Store.first_opens(+fs: List<&2, Types.Fact>, +h: Hashes.Hash, -e0: Types.Entry) -> {
  Lines.Store.first(fs, h) == Some{e0}: Maybe<&2, Types.Entry>
} -> Entry.Opens(e0):
  hh => Store.first_opens.of(fs, h, e0, Store.first_inv(fs, h, e0)(hh))

# what version 0 of a branch comes from: the version n of its store, which
# owns it
def Branch.First(R: List<&2, Types.Entry>, c: Ledgers.Line, e0: Types.Entry, n: Nat) -> Type:
  Exists(
    Types.Entry,
    x => {
      List.get(&2, Types.Entry, R, n) == Some{x}: Maybe<&2, Types.Entry>
    }
      & (
        {
          Lines.Entry.owns(c, x) == True{}: Bool
        }
          & {Lines.Branch.first.of(n, Some{x}) == Some{e0}: Maybe<&2, Types.Entry>}
      )
  )

# Branch.first_inv, once the version of the store is known
def Branch.first_inv.of(
  +R: List<&2, Types.Entry>,
  +c: Ledgers.Line,
  -e0: Types.Entry,
  +n: Nat,
  r: Exists(
    Types.Entry,
    x => {
      List.get(&2, Types.Entry, R, n) == Some{x}: Maybe<&2, Types.Entry>
    }
      & {Lines.Entry.owns(c, x) == True{}: Bool}
  ),
  hh: {Lines.Branch.first.of(n, List.get(&2, Types.Entry, R, n)) == Some{e0}: Maybe<&2, Types.Entry>}
) -> Branch.First(R, c, e0, n):
  (+x, w) = r
  (+eg, eo) = w
  (
    x,
    (
      eg,
      (
        eo,
        (
          %eg: {Lines.Branch.first.of(n, _) == Some{e0}: Maybe<&2, Types.Entry>}
          hh
        )
      )
    )
  )

# version 0 of a branch comes from a version of its store that owns it
def Branch.first_inv(+R: List<&2, Types.Entry>, +c: Ledgers.Line, -e0: Types.Entry) -> {
  Lines.Branch.first(R, c) == Some{e0}: Maybe<&2, Types.Entry>
} -> Exists(Nat, n => Branch.First(R, c, e0, n)):
  Lists.Maybe.by(
    Nat,
    j => {Lines.Branch.first.at(R, j) == Some{e0}: Maybe<&2, Types.Entry>} -> Exists(Nat, n => Branch.First(R, c, e0, n)),
    Lists.List.index(~Types.Entry, ~Ledgers.Line, ~Lines.Entry.owns, R, c),
    en => hh => Empty.absurd(
      Exists(Nat, n => Branch.First(R, c, e0, n)),
      Shared.Maybe.none_ne_some(Types.Entry, e0, hh)
    ),
    +n => ei => hh => (
      n,
      Branch.first_inv.of(
        R,
        c,
        e0,
        n,
        Lists.List.index_get(~Types.Entry, ~Ledgers.Line, ~Lines.Entry.owns, R, c, n)(ei),
        hh
      )
    )
  )

# the entry that a version of a store that owns a branch gives opens a line
def Branch.first_opens.at(+c: Ledgers.Line, x: Types.Entry, -e0: Types.Entry, +n: Nat) -> {
  Lines.Entry.owns(c, x) == True{}: Bool
} -> {Lines.Branch.first.of(n, Some{x}) == Some{e0}: Maybe<&2, Types.Entry>} -> Entry.Opens(e0):
  match x:
    case Types.Entry{Types.Pick{Types.Ask{+i, +k, +r}, pins}, slot}:
      ho => e => (
        %Shared.Maybe.some_inj(Types.Entry, Lines.Entry.first(i, r, n), e0, e): Entry.Opens(_)
        ({==}, Request.owns_opens(c, r)(ho))
      )

# Branch.first_opens, from where version 0 comes from
def Branch.first_opens.of(
  -R: List<&2, Types.Entry>,
  +c: Ledgers.Line,
  -e0: Types.Entry,
  r: Exists(Nat, n => Branch.First(R, c, e0, n))
) -> Entry.Opens(e0):
  (+n, w) = r
  (+x, w2) = w
  (eg, w3) = w2
  (eo, e) = w3
  Branch.first_opens.at(c, x, e0, n)(eo)(e)

# version 0 of a branch opens a line
def Branch.first_opens(+R: List<&2, Types.Entry>, +c: Ledgers.Line, -e0: Types.Entry) -> {
  Lines.Branch.first(R, c) == Some{e0}: Maybe<&2, Types.Entry>
} -> Entry.Opens(e0):
  hh => Branch.first_opens.of(R, c, e0, Branch.first_inv(R, c, e0)(hh))

# Where a state comes from
# ------------------------

# the state st of the line c is the run from its version 0, e0, with the
# versions R of its store when it is a branch
def Line.Rooted(s: Facts.Facts(), c: Ledgers.Line, st: Lines.State, R: Maybe<&2, List<&2, Types.Entry>>, e0: Types.Entry) -> Type:
  {Lines.Line.start(s, R, c, Lines.State{[e0], 1n}) == st: Lines.State}
    & (
      {
        Lines.Rule.after(s, c, Lines.State.versions(st)) == Lines.Line.rule(R, c, Lines.State.versions(st)): Maybe<&2, Lines.Rule>
      }
        & Entry.Opens(e0)
    )

# the state of a line is the run from its version 0
def Line.state_inv(+s: Facts.Facts(), +c: Ledgers.Line, +st: Lines.State) -> {
  Lines.Line.state(s, c) == Some{st}: Maybe<&2, Lines.State>
} -> Exists(Maybe<&2, List<&2, Types.Entry>>, R => Exists(Types.Entry, e0 => Line.Rooted(s, c, st, R, e0))):
  match c:
    case Ledgers.Line{+h, None{}}:
      Lists.Maybe.by(
        Types.Entry,
        m => {
          Lines.Line.from(s, None{}, Ledgers.Line{h, None{}}, m) == Some{st}: Maybe<&2, Lines.State>
        } -> Exists(Maybe<&2, List<&2, Types.Entry>>, R => Exists(Types.Entry, e0 => Line.Rooted(s, Ledgers.Line{h, None{}}, st, R, e0))),
        Lines.Store.first(Facts.Facts.list(s), h),
        en => hh => Empty.absurd(
          Exists(Maybe<&2, List<&2, Types.Entry>>, R => Exists(Types.Entry, e0 => Line.Rooted(s, Ledgers.Line{h, None{}}, st, R, e0))),
          Shared.Maybe.none_ne_some(Lines.State, st, hh)
        ),
        +e0 => ef => hh => (
          None{},
          (
            e0,
            (
              Shared.Maybe.some_inj(
                Lines.State,
                Lines.Line.start(s, None{}, Ledgers.Line{h, None{}}, Lines.State{[e0], 1n}),
                st,
                hh
              ),
              ({==}, Store.first_opens(Facts.Facts.list(s), h, e0)(ef))
            )
          )
        )
      )
    case Ledgers.Line{+h, Some{+b}}:
      Lists.Maybe.by(
        List<&2, Types.Entry>,
        m => {
          Lines.Branch.state(s, Ledgers.Line{h, Some{b}}, m) == Some{st}: Maybe<&2, Lines.State>
        } -> Exists(Maybe<&2, List<&2, Types.Entry>>, R => Exists(Types.Entry, e0 => Line.Rooted(s, Ledgers.Line{h, Some{b}}, st, R, e0))),
        Lines.Store.versions(s, h),
        en => hh => Empty.absurd(
          Exists(Maybe<&2, List<&2, Types.Entry>>, R => Exists(Types.Entry, e0 => Line.Rooted(s, Ledgers.Line{h, Some{b}}, st, R, e0))),
          Shared.Maybe.none_ne_some(Lines.State, st, hh)
        ),
        +r => er => Lists.Maybe.by(
          Types.Entry,
          m => {
            Lines.Line.from(s, Some{r}, Ledgers.Line{h, Some{b}}, m) == Some{st}: Maybe<&2, Lines.State>
          } -> Exists(Maybe<&2, List<&2, Types.Entry>>, R => Exists(Types.Entry, e0 => Line.Rooted(s, Ledgers.Line{h, Some{b}}, st, R, e0))),
          Lines.Branch.first(r, Ledgers.Line{h, Some{b}}),
          en => hh => Empty.absurd(
            Exists(Maybe<&2, List<&2, Types.Entry>>, R => Exists(Types.Entry, e0 => Line.Rooted(s, Ledgers.Line{h, Some{b}}, st, R, e0))),
            Shared.Maybe.none_ne_some(Lines.State, st, hh)
          ),
          +e0 => ef => hh => (
            Some{r},
            (
              e0,
              (
                Shared.Maybe.some_inj(
                  Lines.State,
                  Lines.Line.start(s, Some{r}, Ledgers.Line{h, Some{b}}, Lines.State{[e0], 1n}),
                  st,
                  hh
                ),
                (
                  (
                    %Equal.sym(Maybe<&2, List<&2, Types.Entry>>, Lines.Store.versions(s, h), Some{r}, er): {
                      Lines.Rule.after.of(Ledgers.Line{h, Some{b}}, Lines.State.versions(st), _)
                        == Lines.Line.rule(Some{r}, Ledgers.Line{h, Some{b}}, Lines.State.versions(st)): Maybe<&2, Lines.Rule>
                    }
                    {==}
                  ),
                  Branch.first_opens(r, Ledgers.Line{h, Some{b}}, e0)(ef)
                )
              )
            )
          )
        )
      )

# Line.state_inv, as what follows from it
def Line.state_by(
  -Q: Type,
  -s: Facts.Facts(),
  -c: Ledgers.Line,
  -st: Lines.State,
  r: Exists(Maybe<&2, List<&2, Types.Entry>>, R => Exists(Types.Entry, e0 => Line.Rooted(s, c, st, R, e0))),
  k: @R: Maybe<&2, List<&2, Types.Entry>> -> @e0: Types.Entry -> {Lines.Line.start(s, R, c, Lines.State{[e0], 1n}) == st: Lines.State} -> {
    Lines.Rule.after(s, c, Lines.State.versions(st)) == Lines.Line.rule(R, c, Lines.State.versions(st)): Maybe<&2, Lines.Rule>
  } -> Entry.Opens(e0) -> Q
) -> Q:
  (R, w) = r
  (e0, w2) = w
  (e1, w3) = w2
  (e3, good) = w3
  k(R)(e0)(e1)(e3)(good)

# the versions of a line are those of its state
def Line.versions_inv(+s: Facts.Facts(), +c: Ledgers.Line, -vs: List<&2, Types.Entry>) -> {
  Lines.Line.versions(s, c) == Some{vs}: Maybe<&2, List<&2, Types.Entry>>
} -> Exists(
  Lines.State,
  st => {Lines.Line.state(s, c) == Some{st}: Maybe<&2, Lines.State>} & {Lines.State.versions(st) == vs: List<&2, Types.Entry>}
):
  Lists.Maybe.by(
    Lines.State,
    m => {Maybe.map(&2, Lines.State, List<&2, Types.Entry>, Lines.State.versions, m) == Some{vs}: Maybe<&2, List<&2, Types.Entry>>} -> Exists(
      Lines.State,
      st => {m == Some{st}: Maybe<&2, Lines.State>} & {Lines.State.versions(st) == vs: List<&2, Types.Entry>}
    ),
    Lines.Line.state(s, c),
    en => hh => Empty.absurd(
      Exists(
        Lines.State,
        st => {None{} == Some{st}: Maybe<&2, Lines.State>} & {Lines.State.versions(st) == vs: List<&2, Types.Entry>}
      ),
      Shared.Maybe.none_ne_some(List<&2, Types.Entry>, vs, hh)
    ),
    +st => e => hh => (st, ({==}, Shared.Maybe.some_inj(List<&2, Types.Entry>, Lines.State.versions(st), vs, hh)))
  )

# Line.versions_by, once the state is known
def Line.versions_by.of(
  -Q: Type,
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  -vs: List<&2, Types.Entry>,
  r: Exists(
    Lines.State,
    st => {Lines.Line.state(s, c) == Some{st}: Maybe<&2, Lines.State>} & {Lines.State.versions(st) == vs: List<&2, Types.Entry>}
  ),
  k: @R: Maybe<&2, List<&2, Types.Entry>> -> @e0: Types.Entry -> {
    Lines.State.versions(Lines.Line.start(s, R, c, Lines.State{[e0], 1n})) == vs: List<&2, Types.Entry>
  } -> Entry.Opens(e0) -> Q
) -> Q:
  (+st, w) = r
  (es, ev) = w
  Line.state_by(
    Q,
    s,
    c,
    st,
    Line.state_inv(s, c, st)(es),
    R => e0 => e1 => e3 => good => k(R)(e0)(
      Equal.trans(
        List<&2, Types.Entry>,
        Lines.State.versions(Lines.Line.start(s, R, c, Lines.State{[e0], 1n})),
        Lines.State.versions(st),
        vs,
        Equal.cong(
          Lines.State,
          List<&2, Types.Entry>,
          z => Lines.State.versions(z),
          Lines.Line.start(s, R, c, Lines.State{[e0], 1n}),
          st,
          e1
        ),
        ev
      )
    )(good)
  )

# the versions of a line are those of the run from its version 0, which opens
# a line
def Line.versions_by(
  -Q: Type,
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  -vs: List<&2, Types.Entry>,
  hv: {Lines.Line.versions(s, c) == Some{vs}: Maybe<&2, List<&2, Types.Entry>>},
  k: @R: Maybe<&2, List<&2, Types.Entry>> -> @e0: Types.Entry -> {
    Lines.State.versions(Lines.Line.start(s, R, c, Lines.State{[e0], 1n})) == vs: List<&2, Types.Entry>
  } -> Entry.Opens(e0) -> Q
) -> Q:
  Line.versions_by.of(Q, s, c, vs, Line.versions_inv(s, c, vs)(hv), k)

# the run from a version 0 holds it as version 0
def Line.start_zero(+s: Facts.Facts(), +R: Maybe<&2, List<&2, Types.Entry>>, +c: Ledgers.Line, +e0: Types.Entry) -> {
  List.get(&2, Types.Entry, Lines.State.versions(Lines.Line.start(s, R, c, Lines.State{[e0], 1n})), 0n) == Some{e0}: Maybe<&2, Types.Entry>
}:
  Lists.List.ext_get(
    Types.Entry,
    [e0],
    Lines.State.versions(Lines.Line.start(s, R, c, Lines.State{[e0], 1n})),
    0n,
    e0
  )(Run.ext(s, R, c, Lines.State{[e0], 1n}))({==})

# The versions of a line
# ----------------------

# the first version of the id of each of the versions vs is that version
def Entries.Distinct(vs: List<&2, Types.Entry>) -> Type:
  @+k: Nat -> @+e: Types.Entry -> {List.get(&2, Types.Entry, vs, k) == Some{e}: Maybe<&2, Types.Entry>} -> {
    Lists.List.index(~Types.Entry, ~Ledgers.Id, ~Lines.Entry.is_of, vs, Lines.Entry.id(e)) == Some{k}: Maybe<&2, Nat>
  }

# no index of an id that none of the versions is of
def Entries.index_none(vs: List<&2, Types.Entry>, +i: Ledgers.Id) -> {
  Shared.List.some(~Types.Entry, ~Ledgers.Id, ~Lines.Entry.is_of, vs, i) == False{}: Bool
} -> {Lists.List.index(~Types.Entry, ~Ledgers.Id, ~Lines.Entry.is_of, vs, i) == None{}: Maybe<&2, Nat>}:
  match vs:
    case Nil{}:
      h => {==}
    case Con{+x, +r}:
      Lists.Bool.by(
        d => {
          List.any.if(u => Shared.List.some(~Types.Entry, ~Ledgers.Id, ~Lines.Entry.is_of, r, i), d) == False{}: Bool
        } -> {Lists.List.index.if(u => Lists.List.index(~Types.Entry, ~Ledgers.Id, ~Lines.Entry.is_of, r, i), d) == None{}: Maybe<&2, Nat>},
        Lines.Entry.is_of(i, x),
        et => h => Empty.absurd({Some{0n} == None{}: Maybe<&2, Nat>}, Shared.Bool.true_ne_false(h)),
        ef => h => (
          %Equal.sym(Maybe<&2, Nat>, Lists.List.index(~Types.Entry, ~Ledgers.Id, ~Lines.Entry.is_of, r, i), None{}, Entries.index_none(r, i)(h)): {
            Lists.List.index.up(_) == None{}: Maybe<&2, Nat>
          }
          {==}
        )
      )

# Entries.get_snoc, one item further
def Entries.get_snoc.up(
  -y: Types.Entry,
  -t: List<&2, Types.Entry>,
  -x: Types.Entry,
  -p: Nat,
  -e: Types.Entry,
  r: {List.get(&2, Types.Entry, t, p) == Some{e}: Maybe<&2, Types.Entry>}
    | ({List.length(&2, Types.Entry, t) == p: Nat} & {x == e: Types.Entry})
) -> {List.get(&2, Types.Entry, y <> t, 1n+p) == Some{e}: Maybe<&2, Types.Entry>}
  | ({List.length(&2, Types.Entry, y <> t) == 1n+p: Nat} & {x == e: Types.Entry}):
  match r:
    case Inl{a}:
      Inl{a}
    case Inr{w}:
      (el, ex) = w
      Inr{(Equal.cong(Nat, Nat, z => 1n+z, List.length(&2, Types.Entry, t), p, el), ex)}

# what xs with one more item x at its end holds at k: what xs holds at k, or x
# when k is the length of xs
def Entries.get_snoc(xs: List<&2, Types.Entry>, -x: Types.Entry, k: Nat, -e: Types.Entry) -> {
  List.get(&2, Types.Entry, List.append(&2, Types.Entry, xs, [x]), k) == Some{e}: Maybe<&2, Types.Entry>
} -> {List.get(&2, Types.Entry, xs, k) == Some{e}: Maybe<&2, Types.Entry>}
  | ({List.length(&2, Types.Entry, xs) == k: Nat} & {x == e: Types.Entry}):
  match xs k:
    case Nil{} 0n:
      h => Inr{({==}, Shared.Maybe.some_inj(Types.Entry, x, e, h))}
    case Nil{} 1n+p:
      h => Empty.absurd(
        {None{} == Some{e}: Maybe<&2, Types.Entry>} | ({0n == 1n+p: Nat} & {x == e: Types.Entry}),
        Shared.Maybe.none_ne_some(Types.Entry, e, h)
      )
    case Con{y, t} 0n:
      h => Inl{h}
    case Con{y, t} 1n+p:
      h => Entries.get_snoc.up(y, t, x, p, e, Entries.get_snoc(t, x, p, e)(h))

# the id of the entry of a pick is the id of the pick
def Entry.id_pick(pk: Types.Pick, -k: Nat) -> {Lines.Pick.id(pk) == Lines.Entry.id(Types.Entry{pk, k}): Ledgers.Id}:
  match pk:
    case Types.Pick{a, pins}:
      {==}

# Entries.distinct_snoc at one version, once it is known where it is
def Entries.distinct_snoc.at(
  +vs: List<&2, Types.Entry>,
  +x: Types.Entry,
  +k: Nat,
  +e: Types.Entry,
  r: {List.get(&2, Types.Entry, vs, k) == Some{e}: Maybe<&2, Types.Entry>}
    | ({List.length(&2, Types.Entry, vs) == k: Nat} & {x == e: Types.Entry}),
  p: Entries.Distinct(vs),
  en: {Lists.List.index(~Types.Entry, ~Ledgers.Id, ~Lines.Entry.is_of, vs, Lines.Entry.id(x)) == None{}: Maybe<&2, Nat>}
) -> {Lists.List.index(~Types.Entry, ~Ledgers.Id, ~Lines.Entry.is_of, List.append(&2, Types.Entry, vs, [x]), Lines.Entry.id(e)) == Some{k}: Maybe<&2, Nat>}:
  match r:
    case Inl{hg}:
      Lists.List.index_append(~Types.Entry, ~Ledgers.Id, ~Lines.Entry.is_of, vs, [x], Lines.Entry.id(e), k)(p(k)(e)(hg))
    case Inr{w}:
      (el, ex) = w
      %ex: {Lists.List.index(~Types.Entry, ~Ledgers.Id, ~Lines.Entry.is_of, List.append(&2, Types.Entry, vs, [x]), Lines.Entry.id(_)) == Some{k}: Maybe<&2, Nat>}
      %el: {Lists.List.index(~Types.Entry, ~Ledgers.Id, ~Lines.Entry.is_of, List.append(&2, Types.Entry, vs, [x]), Lines.Entry.id(x)) == Some{_}: Maybe<&2, Nat>}
      Lists.List.index_snoc(~Types.Entry, ~Ledgers.Id, ~Lines.Entry.is_of, vs, x, Lines.Entry.id(x))(en)(
        Ledgers.Id.is_eq_refl(Lines.Entry.id(x))
      )

# versions with one more, of an id that none of them is of, keep
# Entries.Distinct
def Entries.distinct_snoc(+vs: List<&2, Types.Entry>, +x: Types.Entry) -> {
  Lists.List.index(~Types.Entry, ~Ledgers.Id, ~Lines.Entry.is_of, vs, Lines.Entry.id(x)) == None{}: Maybe<&2, Nat>
} -> Entries.Distinct(vs) -> Entries.Distinct(List.append(&2, Types.Entry, vs, [x])):
  +en => p => +k => +e => hg => Entries.distinct_snoc.at(vs, x, k, e, Entries.get_snoc(vs, x, k, e)(hg), p, en)

# the versions after a decided slot keep Entries.Distinct
def Put.distinct(+vs: List<&2, Types.Entry>, +k: Nat, +pk: Types.Pick) -> Entries.Distinct(vs) -> Entries.Distinct(
  Lines.State.versions(Lines.State.put(vs, k, pk))
):
  Lists.Bool.by(
    d => Entries.Distinct(vs) -> Entries.Distinct(Lines.State.versions(Lines.State.put.if(vs, k, pk, d))),
    Shared.List.some(~Types.Entry, ~Ledgers.Id, ~Lines.Entry.is_of, vs, Lines.Pick.id(pk)),
    et => p => p,
    ef => p => Entries.distinct_snoc(vs, Types.Entry{pk, k})(
      %Entry.id_pick(pk, k): {Lists.List.index(~Types.Entry, ~Ledgers.Id, ~Lines.Entry.is_of, vs, _) == None{}: Maybe<&2, Nat>}
      Entries.index_none(vs, Lines.Pick.id(pk))(ef)
    )(p)
  )

# Entries.distinct_one at one index
def Entries.distinct_one.at(+e0: Types.Entry, k: Nat, +e: Types.Entry) -> {
  List.get(&2, Types.Entry, [e0], k) == Some{e}: Maybe<&2, Types.Entry>
} -> {Lists.List.index(~Types.Entry, ~Ledgers.Id, ~Lines.Entry.is_of, [e0], Lines.Entry.id(e)) == Some{k}: Maybe<&2, Nat>}:
  match k:
    case 0n:
      hg => (
        %Shared.Maybe.some_inj(Types.Entry, e0, e, hg): {Lists.List.index(~Types.Entry, ~Ledgers.Id, ~Lines.Entry.is_of, [e0], Lines.Entry.id(_)) == Some{0n}: Maybe<&2, Nat>}
        %Equal.sym(Bool, Lines.Entry.is_of(Lines.Entry.id(e0), e0), True{}, Ledgers.Id.is_eq_refl(Lines.Entry.id(e0))): {
          Lists.List.index.if(u => None{}, _) == Some{0n}: Maybe<&2, Nat>
        }
        {==}
      )
    case 1n+j:
      hg => Empty.absurd(
        {Lists.List.index(~Types.Entry, ~Ledgers.Id, ~Lines.Entry.is_of, [e0], Lines.Entry.id(e)) == Some{1n+j}: Maybe<&2, Nat>},
        Shared.Maybe.none_ne_some(Types.Entry, e, hg)
      )

# one version is Entries.Distinct
def Entries.distinct_one(+e0: Types.Entry) -> Entries.Distinct([e0]):
  +k => +e => hg => Entries.distinct_one.at(e0, k, e)(hg)

# the versions of a state are Entries.Distinct
def Run.Distinct(g: Unit, s: Facts.Facts(), R: Maybe<&2, List<&2, Types.Entry>>, c: Ledgers.Line, a: Lines.State) -> Type:
  Entries.Distinct(Lines.State.versions(a))

# a decided slot keeps Run.Distinct
def Run.distinct_step(+g: Unit, +s: Facts.Facts(), +R: Maybe<&2, List<&2, Types.Entry>>, +c: Ledgers.Line, +a: Lines.State, +u: Lines.Rule, +pk: Types.Pick) -> {
  Lines.Line.rule(R, c, Lines.State.versions(a)) == Some{u}: Maybe<&2, Lines.Rule>
} -> {
  Lines.Votes.decided(s, Types.Step.At{c, Lines.State.slot(a)}, Lines.Rule.nodes(u)) == Some{pk}: Maybe<&2, Types.Pick>
} -> Run.Distinct(g, s, R, c, a) -> Run.Distinct(g, s, R, c, Lines.State.put(Lines.State.versions(a), Lines.State.slot(a), pk)):
  eu => ed => p => Put.distinct(Lines.State.versions(a), Lines.State.slot(a), pk)(p)

# each version of a line is of its own id: the first version of the id of
# version k is k
def Line.versions_index(+s: Facts.Facts(), +c: Ledgers.Line, +vs: List<&2, Types.Entry>, +k: Nat, +e: Types.Entry) -> {
  Lines.Line.versions(s, c) == Some{vs}: Maybe<&2, List<&2, Types.Entry>>
} -> {List.get(&2, Types.Entry, vs, k) == Some{e}: Maybe<&2, Types.Entry>} -> {
  Lists.List.index(~Types.Entry, ~Ledgers.Id, ~Lines.Entry.is_of, vs, Lines.Entry.id(e)) == Some{k}: Maybe<&2, Nat>
}:
  hv => hg => Line.versions_by(
    {List.get(&2, Types.Entry, vs, k) == Some{e}: Maybe<&2, Types.Entry>} -> {
      Lists.List.index(~Types.Entry, ~Ledgers.Id, ~Lines.Entry.is_of, vs, Lines.Entry.id(e)) == Some{k}: Maybe<&2, Nat>
    },
    s,
    c,
    vs,
    hv,
    +R => +e0 => ev => good => (
      %ev: {List.get(&2, Types.Entry, _, k) == Some{e}: Maybe<&2, Types.Entry>} -> {
        Lists.List.index(~Types.Entry, ~Ledgers.Id, ~Lines.Entry.is_of, _, Lines.Entry.id(e)) == Some{k}: Maybe<&2, Nat>
      }
      Run.keeps(
        ~Unit,
        ~Run.Distinct,
        ~Run.distinct_step,
        Lines.Line.bound(Facts.Facts.list(s), c),
        Unit{},
        s,
        R,
        c,
        Lines.State{[e0], 1n},
        Entries.distinct_one(e0)
      )(k)(e)
    )
  )(hg)

# the facts s hold a vote for the pick pk at the step st
def Votes.Voted(s: Facts.Facts(), st: Types.Step, pk: Types.Pick) -> Type:
  Exists(String, v => {Facts.Facts.has(s, Types.Fact.Vote{v, st, pk}) == True{}: Bool})

# Votes.decided_voted, from a node that voted
def Votes.decided_voted.of(
  -s: Facts.Facts(),
  -st: Types.Step,
  -ds: List<&2, String>,
  -pk: Types.Pick,
  r: Exists(
    String,
    x => {
      List.contains(~String, ~String.eq, ds, x) == True{}: Bool
    }
      & {Lines.Voting.voted(Lines.Voting{s, st, pk}, x) == True{}: Bool}
  )
) -> Votes.Voted(s, st, pk):
  (x, w) = r
  (hin, hv) = w
  (x, hv)

# the facts hold a vote for the pick that the nodes ds decided for a step
def Votes.decided_voted(+s: Facts.Facts(), +st: Types.Step, +ds: List<&2, String>, +pk: Types.Pick) -> {
  Lines.Votes.decided(s, st, ds) == Some{pk}: Maybe<&2, Types.Pick>
} -> Votes.Voted(s, st, pk):
  hd => Votes.decided_voted.of(
    s,
    st,
    ds,
    pk,
    Lists.List.count_pos(
      ~String,
      ~Lines.Voting,
      ~Lines.Voting.voted,
      ~String.eq,
      ~Texts.String.laws(),
      ds,
      Lines.Voting{s, st, pk}
    )(
      Lists.Nat.most_pos(
        List.length(&2, String, ds),
        Lists.List.count(~String, ~Lines.Voting, ~Lines.Voting.voted, ds, Lines.Voting{s, st, pk})
      )(
        Shared.Bool.and_true_left(
          Lists.Nat.most(
            List.length(&2, String, ds),
            Lists.List.count(~String, ~Lines.Voting, ~Lines.Voting.voted, ds, Lines.Voting{s, st, pk})
          ),
          Shared.List.holds(
            ~Types.Pick,
            ~Lines.Rival,
            ~Lines.Rival.beats,
            Lines.Votes.picks(Facts.Facts.list(s), st),
            Lines.Rival{Lines.Tally{s, st, ds, Lines.Votes.picks(Facts.Facts.list(s), st)}, pk}
          )
        )(
          Lists.List.pick_hit(
            ~Types.Pick,
            ~Lines.Tally,
            ~Lines.Tally.wins,
            Lines.Votes.picks(Facts.Facts.list(s), st),
            Lines.Tally{s, st, ds, Lines.Votes.picks(Facts.Facts.list(s), st)},
            pk
          )(hd)
        )
      )
    )
  )

# the facts s hold a vote for each of the versions vs of the line c after the
# first, for its pick at its slot
def Entries.Voted(s: Facts.Facts(), c: Ledgers.Line, vs: List<&2, Types.Entry>) -> Type:
  @+j: Nat -> @+e: Types.Entry -> {List.get(&2, Types.Entry, vs, 1n+j) == Some{e}: Maybe<&2, Types.Entry>} -> Votes.Voted(
    s,
    Types.Step.At{c, Lines.Entry.slot(e)},
    Lines.Entry.pick(e)
  )

# Entries.voted_snoc at one version, once it is known where it is
def Entries.voted_snoc.at(
  -s: Facts.Facts(),
  -c: Ledgers.Line,
  -vs: List<&2, Types.Entry>,
  -x: Types.Entry,
  +j: Nat,
  +e: Types.Entry,
  r: {List.get(&2, Types.Entry, vs, 1n+j) == Some{e}: Maybe<&2, Types.Entry>}
    | ({List.length(&2, Types.Entry, vs) == 1n+j: Nat} & {x == e: Types.Entry}),
  p: Entries.Voted(s, c, vs),
  hx: Votes.Voted(s, Types.Step.At{c, Lines.Entry.slot(x)}, Lines.Entry.pick(x))
) -> Votes.Voted(s, Types.Step.At{c, Lines.Entry.slot(e)}, Lines.Entry.pick(e)):
  match r:
    case Inl{hg}:
      p(j)(e)(hg)
    case Inr{w}:
      (el, ex) = w
      %ex: Votes.Voted(s, Types.Step.At{c, Lines.Entry.slot(_)}, Lines.Entry.pick(_))
      hx

# the versions after a decided slot keep Entries.Voted
def Put.voted(+s: Facts.Facts(), +c: Ledgers.Line, +vs: List<&2, Types.Entry>, +k: Nat, +pk: Types.Pick) -> Votes.Voted(
  s,
  Types.Step.At{c, k},
  pk
) -> Entries.Voted(s, c, vs) -> Entries.Voted(s, c, Lines.State.versions(Lines.State.put(vs, k, pk))):
  Lists.Bool.by(
    d => Votes.Voted(s, Types.Step.At{c, k}, pk) -> Entries.Voted(s, c, vs) -> Entries.Voted(
      s,
      c,
      Lines.State.versions(Lines.State.put.if(vs, k, pk, d))
    ),
    Shared.List.some(~Types.Entry, ~Ledgers.Id, ~Lines.Entry.is_of, vs, Lines.Pick.id(pk)),
    et => hx => p => p,
    ef => hx => p => +j => +e => hg => Entries.voted_snoc.at(
      s,
      c,
      vs,
      Types.Entry{pk, k},
      j,
      e,
      Entries.get_snoc(vs, Types.Entry{pk, k}, 1n+j, e)(hg),
      p,
      hx
    )
  )

# one version is Entries.Voted
def Entries.voted_one(-s: Facts.Facts(), -c: Ledgers.Line, -e0: Types.Entry) -> Entries.Voted(s, c, [e0]):
  +j => +e => hg => Empty.absurd(
    Votes.Voted(s, Types.Step.At{c, Lines.Entry.slot(e)}, Lines.Entry.pick(e)),
    Shared.Maybe.none_ne_some(Types.Entry, e, hg)
  )

# the versions of a state are Entries.Voted
def Run.Voted(g: Unit, s: Facts.Facts(), R: Maybe<&2, List<&2, Types.Entry>>, c: Ledgers.Line, a: Lines.State) -> Type:
  Entries.Voted(s, c, Lines.State.versions(a))

# a decided slot keeps Run.Voted
def Run.voted_step(+g: Unit, +s: Facts.Facts(), +R: Maybe<&2, List<&2, Types.Entry>>, +c: Ledgers.Line, +a: Lines.State, +u: Lines.Rule, +pk: Types.Pick) -> {
  Lines.Line.rule(R, c, Lines.State.versions(a)) == Some{u}: Maybe<&2, Lines.Rule>
} -> {
  Lines.Votes.decided(s, Types.Step.At{c, Lines.State.slot(a)}, Lines.Rule.nodes(u)) == Some{pk}: Maybe<&2, Types.Pick>
} -> Run.Voted(g, s, R, c, a) -> Run.Voted(g, s, R, c, Lines.State.put(Lines.State.versions(a), Lines.State.slot(a), pk)):
  eu => ed => p => Put.voted(s, c, Lines.State.versions(a), Lines.State.slot(a), pk)(
    Votes.decided_voted(s, Types.Step.At{c, Lines.State.slot(a)}, Lines.Rule.nodes(u), pk)(ed)
  )(p)

# each version of a line after version 0 was voted for: the facts hold a vote
# for its pick at its slot
def Line.versions_voted(+s: Facts.Facts(), +c: Ledgers.Line, +vs: List<&2, Types.Entry>, +j: Nat, +e: Types.Entry) -> {
  Lines.Line.versions(s, c) == Some{vs}: Maybe<&2, List<&2, Types.Entry>>
} -> {List.get(&2, Types.Entry, vs, 1n+j) == Some{e}: Maybe<&2, Types.Entry>} -> Exists(
  String,
  v => {
    Facts.Facts.has(s, Types.Fact.Vote{v, Types.Step.At{c, Lines.Entry.slot(e)}, Lines.Entry.pick(e)}) == True{}: Bool
  }
):
  hv => hg => Line.versions_by(
    {List.get(&2, Types.Entry, vs, 1n+j) == Some{e}: Maybe<&2, Types.Entry>} -> Votes.Voted(
      s,
      Types.Step.At{c, Lines.Entry.slot(e)},
      Lines.Entry.pick(e)
    ),
    s,
    c,
    vs,
    hv,
    +R => +e0 => ev => good => (
      %ev: {List.get(&2, Types.Entry, _, 1n+j) == Some{e}: Maybe<&2, Types.Entry>} -> Votes.Voted(
        s,
        Types.Step.At{c, Lines.Entry.slot(e)},
        Lines.Entry.pick(e)
      )
      Run.keeps(
        ~Unit,
        ~Run.Voted,
        ~Run.voted_step,
        Lines.Line.bound(Facts.Facts.list(s), c),
        Unit{},
        s,
        R,
        c,
        Lines.State{[e0], 1n},
        Entries.voted_one(s, c, e0)
      )(j)(e)
    )
  )(hg)

# version 0 of a line is an ask of the number 0 whose request opens a line
def Line.versions_zero(+s: Facts.Facts(), +c: Ledgers.Line, +vs: List<&2, Types.Entry>, +e: Types.Entry) -> {
  Lines.Line.versions(s, c) == Some{vs}: Maybe<&2, List<&2, Types.Entry>>
} -> {List.get(&2, Types.Entry, vs, 0n) == Some{e}: Maybe<&2, Types.Entry>} -> {
  Facts.Ask.seq(Lines.Entry.ask(e)) == 0n: Nat
}
  & {Lines.Request.opens(Lines.Ask.request(Lines.Entry.ask(e))) == True{}: Bool}:
  hv => hg => Line.versions_by(
    Entry.Opens(e),
    s,
    c,
    vs,
    hv,
    +R => +e0 => ev => good => (
      %Shared.Maybe.some_inj(
        Types.Entry,
        e0,
        e,
        Equal.trans(
          Maybe<&2, Types.Entry>,
          Some{e0},
          List.get(&2, Types.Entry, vs, 0n),
          Some{e},
          Equal.sym(
            Maybe<&2, Types.Entry>,
            List.get(&2, Types.Entry, vs, 0n),
            Some{e0},
            (
              %ev: {List.get(&2, Types.Entry, _, 0n) == Some{e0}: Maybe<&2, Types.Entry>}
              Line.start_zero(s, R, c, e0)
            )
          ),
          hg
        )
      ): Entry.Opens(_)
      good
    )
  )

# a line that has versions has version 0
def Line.versions_some(+s: Facts.Facts(), +c: Ledgers.Line, +vs: List<&2, Types.Entry>) -> {
  Lines.Line.versions(s, c) == Some{vs}: Maybe<&2, List<&2, Types.Entry>>
} -> Exists(Types.Entry, e => {List.get(&2, Types.Entry, vs, 0n) == Some{e}: Maybe<&2, Types.Entry>}):
  hv => Line.versions_by(
    Exists(Types.Entry, e => {List.get(&2, Types.Entry, vs, 0n) == Some{e}: Maybe<&2, Types.Entry>}),
    s,
    c,
    vs,
    hv,
    +R => +e0 => ev => good => (
      e0,
      (
        %ev: {List.get(&2, Types.Entry, _, 0n) == Some{e0}: Maybe<&2, Types.Entry>}
        Line.start_zero(s, R, c, e0)
      )
    )
  )

# a branch has versions only when a version of its store made a group its
# owner
def Line.branch_owned(+s: Facts.Facts(), +h: Hashes.Hash, +b: String, +vs: List<&2, Types.Entry>) -> {
  Lines.Line.versions(s, Ledgers.Line{h, Some{b}}) == Some{vs}: Maybe<&2, List<&2, Types.Entry>>
} -> Exists(
  List<&2, Types.Entry>,
  R => {
    Lines.Line.versions(s, Ledgers.Line{h, None{}}) == Some{R}: Maybe<&2, List<&2, Types.Entry>>
  }
    & Exists(
      Nat,
      k => Exists(
        Types.Entry,
        e => {
          List.get(&2, Types.Entry, R, k) == Some{e}: Maybe<&2, Types.Entry>
        }
          & {Lines.Entry.owns(Ledgers.Line{h, Some{b}}, e) == True{}: Bool}
      )
    )
):
  hv => Lists.Maybe.by(
    List<&2, Types.Entry>,
    m => {
      Maybe.map(&2, Lines.State, List<&2, Types.Entry>, Lines.State.versions, Lines.Branch.state(s, Ledgers.Line{h, Some{b}}, m)) == Some{vs}: Maybe<&2, List<&2, Types.Entry>>
    } -> Exists(
      List<&2, Types.Entry>,
      R => {m == Some{R}: Maybe<&2, List<&2, Types.Entry>>} & Exists(
        Nat,
        k => Exists(
          Types.Entry,
          e => {
            List.get(&2, Types.Entry, R, k) == Some{e}: Maybe<&2, Types.Entry>
          }
            & {Lines.Entry.owns(Ledgers.Line{h, Some{b}}, e) == True{}: Bool}
        )
      )
    ),
    Lines.Store.versions(s, h),
    en => hh => Empty.absurd(
      Exists(
        List<&2, Types.Entry>,
        R => {None{} == Some{R}: Maybe<&2, List<&2, Types.Entry>>} & Exists(
        Nat,
        k => Exists(
          Types.Entry,
          e => {
            List.get(&2, Types.Entry, R, k) == Some{e}: Maybe<&2, Types.Entry>
          }
            & {Lines.Entry.owns(Ledgers.Line{h, Some{b}}, e) == True{}: Bool}
        )
      )
      ),
      Shared.Maybe.none_ne_some(List<&2, Types.Entry>, vs, hh)
    ),
    +r => er => hh => (
      r,
      (
        {==},
        Lists.Maybe.by(
          Nat,
          j => {
            Maybe.map(
              &2,
              Lines.State,
              List<&2, Types.Entry>,
              Lines.State.versions,
              Lines.Line.from(s, Some{r}, Ledgers.Line{h, Some{b}}, Lines.Branch.first.at(r, j))
            )
              == Some{vs}: Maybe<&2, List<&2, Types.Entry>>
          } -> Exists(
        Nat,
        k => Exists(
          Types.Entry,
          e => {
            List.get(&2, Types.Entry, r, k) == Some{e}: Maybe<&2, Types.Entry>
          }
            & {Lines.Entry.owns(Ledgers.Line{h, Some{b}}, e) == True{}: Bool}
        )
      ),
          Lists.List.index(~Types.Entry, ~Ledgers.Line, ~Lines.Entry.owns, r, Ledgers.Line{h, Some{b}}),
          en => h2 => Empty.absurd(Exists(
        Nat,
        k => Exists(
          Types.Entry,
          e => {
            List.get(&2, Types.Entry, r, k) == Some{e}: Maybe<&2, Types.Entry>
          }
            & {Lines.Entry.owns(Ledgers.Line{h, Some{b}}, e) == True{}: Bool}
        )
      ), Shared.Maybe.none_ne_some(List<&2, Types.Entry>, vs, h2)),
          +n => ei => h2 => (
            n,
            Lists.List.index_get(~Types.Entry, ~Ledgers.Line, ~Lines.Entry.owns, r, Ledgers.Line{h, Some{b}}, n)(ei)
          )
        )(hh)
      )
    )
  )(hv)

# a node that takes in a request that starts a store holds version 0 of the
# store: that request
def Line.started(+name: String, +s: Facts.Facts(), +i: Ledgers.Id, +os: List<&2, String>) -> {
  Lines.Line.at(
    Facts.Facts.ask(name, s, i, Spec.Request.Start{os}),
    Ledgers.Line{Facts.Start.root(i, Spec.Request.Start{os}), None{}},
    0n
  )
    == Some{Lines.Entry.first(i, Spec.Request.Start{os}, 0n)}: Maybe<&2, Types.Entry>
}:
  ?TODO

# Where a run stops
# -----------------

# how far the fact f makes the line c reach: one more than its slot, when it
# is a vote for a slot of c
def Fact.reach(c: Ledgers.Line, f: Types.Fact) -> Nat:
  match f:
    case Types.Fact.Ask{a}:
      0n
    case Types.Fact.Vote{v, Types.Step.Broken{}, pk}:
      0n
    case Types.Fact.Vote{v, Types.Step.At{c2, k}, pk}:
      Lines.Line.bound.at(Ledgers.Line.is_eq(c2, c), k)

# the bound of a line is at least the reach of the first fact
def Bound.head(f: Types.Fact, +rest: List<&2, Types.Fact>, +c: Ledgers.Line) -> {
  Nat.is_le(Fact.reach(c, f), Lines.Line.bound(f <> rest, c)) == True{}: Bool
}:
  match f:
    case Types.Fact.Ask{a}:
      Shared.Nat.le_zero(Lines.Line.bound(rest, c))
    case Types.Fact.Vote{v, Types.Step.Broken{}, pk}:
      Shared.Nat.le_zero(Lines.Line.bound(rest, c))
    case Types.Fact.Vote{v, Types.Step.At{+c2, +k}, pk}:
      Lists.Nat.le_max_left(Lines.Line.bound.at(Ledgers.Line.is_eq(c2, c), k), Lines.Line.bound(rest, c))

# the bound of a line is at least the bound in the facts after the first
def Bound.tail(f: Types.Fact, +rest: List<&2, Types.Fact>, +c: Ledgers.Line) -> {
  Nat.is_le(Lines.Line.bound(rest, c), Lines.Line.bound(f <> rest, c)) == True{}: Bool
}:
  match f:
    case Types.Fact.Ask{a}:
      Shared.Nat.le_refl(Lines.Line.bound(rest, c))
    case Types.Fact.Vote{v, Types.Step.Broken{}, pk}:
      Shared.Nat.le_refl(Lines.Line.bound(rest, c))
    case Types.Fact.Vote{v, Types.Step.At{+c2, +k}, pk}:
      Lists.Nat.le_max_right(Lines.Line.bound.at(Ledgers.Line.is_eq(c2, c), k), Lines.Line.bound(rest, c))

# a vote for the slot k of the line c reaches one more than k
def Fact.reach_vote(+c: Ledgers.Line, -v: String, -k: Nat, -pk: Types.Pick) -> {
  Fact.reach(c, Types.Fact.Vote{v, Types.Step.At{c, k}, pk}) == 1n+k: Nat
}:
  %Equal.sym(Bool, Ledgers.Line.is_eq(c, c), True{}, Ledgers.Line.is_eq_refl(c)): {
    Lines.Line.bound.at(_, k) == 1n+k: Nat
  }
  {==}

# the slot of a vote among fs for a slot of the line c is below the bound
def Bound.in(fs: List<&2, Types.Fact>, +c: Ledgers.Line, +v: String, +k: Nat, +pk: Types.Pick) -> {
  List.contains(~Types.Fact, ~Coded.Fact.is_eq, fs, Types.Fact.Vote{v, Types.Step.At{c, k}, pk}) == True{}: Bool
} -> {Nat.is_lt(k, Lines.Line.bound(fs, c)) == True{}: Bool}:
  match fs:
    case Nil{}:
      hin => Empty.absurd({Nat.is_lt(k, 1n) == True{}: Bool}, Shared.Bool.false_ne_true(hin))
    case Con{+f, +rest}:
      hin => Lists.List.contains_cons_by(
        ~Types.Fact,
        ~Coded.Fact.is_eq,
        ~Coded.Fact.laws(),
        {Nat.is_lt(k, Lines.Line.bound(f <> rest, c)) == True{}: Bool},
        f,
        rest,
        Types.Fact.Vote{v, Types.Step.At{c, k}, pk},
        hin,
        e => Shared.Nat.lt_le(k, 1n+k, Lines.Line.bound(f <> rest, c))(Shared.Nat.lt_succ(k))(
          %Equal.trans(
            Nat,
            Fact.reach(c, f),
            Fact.reach(c, Types.Fact.Vote{v, Types.Step.At{c, k}, pk}),
            1n+k,
            Equal.cong(
              Types.Fact,
              Nat,
              z => Fact.reach(c, z),
              f,
              Types.Fact.Vote{v, Types.Step.At{c, k}, pk},
              e
            ),
            Fact.reach_vote(c, v, k, pk)
          ): {Nat.is_le(_, Lines.Line.bound(f <> rest, c)) == True{}: Bool}
          Bound.head(f, rest, c)
        ),
        cin => Shared.Nat.lt_le(k, Lines.Line.bound(rest, c), Lines.Line.bound(f <> rest, c))(
          Bound.in(rest, c, v, k, pk)(cin)
        )(Bound.tail(f, rest, c))
      )

# Votes.decided_lt, from the vote
def Votes.decided_lt.of(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +pk: Types.Pick,
  r: Votes.Voted(s, Types.Step.At{c, k}, pk)
) -> {Nat.is_lt(k, Lines.Line.bound(Facts.Facts.list(s), c)) == True{}: Bool}:
  (+v, hv) = r
  Bound.in(Facts.Facts.list(s), c, v, k, pk)(
    Equal.trans(
      Bool,
      List.contains(~Types.Fact, ~Coded.Fact.is_eq, Facts.Facts.list(s), Types.Fact.Vote{v, Types.Step.At{c, k}, pk}),
      Facts.Facts.has(s, Types.Fact.Vote{v, Types.Step.At{c, k}, pk}),
      True{},
      Equal.sym(
        Bool,
        Facts.Facts.has(s, Types.Fact.Vote{v, Types.Step.At{c, k}, pk}),
        List.contains(~Types.Fact, ~Coded.Fact.is_eq, Facts.Facts.list(s), Types.Fact.Vote{v, Types.Step.At{c, k}, pk}),
        Facts.Facts.has_list(s, Types.Fact.Vote{v, Types.Step.At{c, k}, pk})
      ),
      hv
    )
  )

# a decided slot of a line is below the bound of the line
def Votes.decided_lt(+s: Facts.Facts(), +c: Ledgers.Line, +k: Nat, +ds: List<&2, String>, +pk: Types.Pick) -> {
  Lines.Votes.decided(s, Types.Step.At{c, k}, ds) == Some{pk}: Maybe<&2, Types.Pick>
} -> {Nat.is_lt(k, Lines.Line.bound(Facts.Facts.list(s), c)) == True{}: Bool}:
  hd => Votes.decided_lt.of(s, c, k, pk, Votes.decided_voted(s, Types.Step.At{c, k}, ds, pk)(hd))

# the slot after a decided slot is the next one
def Put.slot(+vs: List<&2, Types.Entry>, +k: Nat, +pk: Types.Pick) -> {Lines.State.slot(Lines.State.put(vs, k, pk)) == 1n+k: Nat}:
  Lists.Bool.by(
    d => {Lines.State.slot(Lines.State.put.if(vs, k, pk, d)) == 1n+k: Nat},
    Shared.List.some(~Types.Entry, ~Ledgers.Id, ~Lines.Entry.is_of, vs, Lines.Pick.id(pk)),
    et => {==},
    ef => {==}
  )

# a number is below itself plus one
def Nat.lt_add_one(+b: Nat) -> {Nat.is_lt(b, Nat.add(b, 1n)) == True{}: Bool}:
  %Equal.sym(Nat, Nat.add(b, 1n), 1n+Nat.add(b, 0n), Shared.Nat.add_succ(b, 0n)): {Nat.is_lt(b, _) == True{}: Bool}
  %Equal.sym(Nat, Nat.add(b, 0n), b, Shared.Nat.add_zero(b)): {Nat.is_lt(b, 1n+_) == True{}: Bool}
  Shared.Nat.lt_succ(b)

# a run that may go past the bound of the line stops at a slot that is not
# decided
def Run.stops(f: Nat, +s: Facts.Facts(), +R: Maybe<&2, List<&2, Types.Entry>>, +c: Ledgers.Line, +st: Lines.State) -> {
  Nat.is_lt(Lines.Line.bound(Facts.Facts.list(s), c), Nat.add(f, Lines.State.slot(st))) == True{}: Bool
} -> {
  Lines.Line.step(s, R, c, Lines.Line.run(f, s, R, c, st, Lines.Line.step(s, R, c, st))) == None{}: Maybe<&2, Lines.State>
}:
  match f:
    case 0n:
      hb => Lists.Maybe.by(
        Lines.State,
        m => {m == None{}: Maybe<&2, Lines.State>},
        Lines.Line.step(s, R, c, st),
        en => {==},
        +st2 => e => Step.at_by(
          {Some{st2} == None{}: Maybe<&2, Lines.State>},
          s,
          c,
          st,
          st2,
          Lines.Line.rule(R, c, Lines.State.versions(st)),
          Step.at_inv(s, c, st, st2, Lines.Line.rule(R, c, Lines.State.versions(st)))(e),
          +u => +pk => eu => ed => eb => Lists.Bool.clash(
            {Some{st2} == None{}: Maybe<&2, Lines.State>},
            Nat.is_lt(Lines.Line.bound(Facts.Facts.list(s), c), Lines.State.slot(st)),
            Shared.Nat.le_nlt(Lines.State.slot(st), Lines.Line.bound(Facts.Facts.list(s), c))(
              Shared.Nat.lt_weak(Lines.State.slot(st), Lines.Line.bound(Facts.Facts.list(s), c))(
                Votes.decided_lt(s, c, Lines.State.slot(st), Lines.Rule.nodes(u), pk)(ed)
              )
            ),
            hb
          )
        )
      )
    case 1n+(+p):
      hb => Lists.Maybe.by(
        Lines.State,
        m => {
          Lines.Line.step(s, R, c, Lines.Line.run(1n+p, s, R, c, st, m)) == None{}: Maybe<&2, Lines.State>
        },
        Lines.Line.step(s, R, c, st),
        en => en,
        +st2 => e => Step.at_by(
          {
            Lines.Line.step(s, R, c, Lines.Line.run(p, s, R, c, st2, Lines.Line.step(s, R, c, st2))) == None{}: Maybe<&2, Lines.State>
          },
          s,
          c,
          st,
          st2,
          Lines.Line.rule(R, c, Lines.State.versions(st)),
          Step.at_inv(s, c, st, st2, Lines.Line.rule(R, c, Lines.State.versions(st)))(e),
          +u => +pk => eu => ed => eb => (
            %eb: {
              Lines.Line.step(s, R, c, Lines.Line.run(p, s, R, c, _, Lines.Line.step(s, R, c, _))) == None{}: Maybe<&2, Lines.State>
            }
            Run.stops(p, s, R, c, Lines.State.put(Lines.State.versions(st), Lines.State.slot(st), pk))(
              %Equal.sym(
                Nat,
                Lines.State.slot(Lines.State.put(Lines.State.versions(st), Lines.State.slot(st), pk)),
                1n+Lines.State.slot(st),
                Put.slot(Lines.State.versions(st), Lines.State.slot(st), pk)
              ): {Nat.is_lt(Lines.Line.bound(Facts.Facts.list(s), c), Nat.add(p, _)) == True{}: Bool}
              %Equal.sym(
                Nat,
                Nat.add(p, 1n+Lines.State.slot(st)),
                1n+Nat.add(p, Lines.State.slot(st)),
                Shared.Nat.add_succ(p, Lines.State.slot(st))
              ): {Nat.is_lt(Lines.Line.bound(Facts.Facts.list(s), c), _) == True{}: Bool}
              hb
            )
          )
        )
      )

# the state of a line stops at a slot that is not decided
def Line.state_open(+s: Facts.Facts(), +c: Ledgers.Line, +st: Lines.State) -> {
  Lines.Line.state(s, c) == Some{st}: Maybe<&2, Lines.State>
} -> {Lines.Line.next(s, c, st) == None{}: Maybe<&2, Lines.State>}:
  hs => Line.state_by(
    {Lines.Line.next(s, c, st) == None{}: Maybe<&2, Lines.State>},
    s,
    c,
    st,
    Line.state_inv(s, c, st)(hs),
    +R => +e0 => e1 => e3 => good => (
      %Equal.sym(
        Maybe<&2, Lines.Rule>,
        Lines.Rule.after(s, c, Lines.State.versions(st)),
        Lines.Line.rule(R, c, Lines.State.versions(st)),
        e3
      ): {Lines.Line.step.at(s, c, st, _) == None{}: Maybe<&2, Lines.State>}
      %e1: {Lines.Line.step(s, R, c, _) == None{}: Maybe<&2, Lines.State>}
      Run.stops(Lines.Line.bound(Facts.Facts.list(s), c), s, R, c, Lines.State{[e0], 1n})(
        Nat.lt_add_one(Lines.Line.bound(Facts.Facts.list(s), c))
      )
    )
  )
