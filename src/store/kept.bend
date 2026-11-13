import Base
import ../branch/merges.bend as Merges
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
import ../writer/requests.bend as Requests

# Kept
# ----
# The tree of a ledger that holds the whole of a tree keeps it whole, and keeps
# the format and the bytes of each resource of it, as it is written.

# the law of a listing, of the tree of the ledger d
def Kept.laws_range(d: Vend.Led()) -> Trees.Laws.Range(Vend.L(d), Replicas.Led.tree(Requests.Ask.machine(), d)):
  match d:
    case Tuple{x, Tuple{o, Tuple{fin, Tuple{pf, Tuple{wr, Tuple{cn, Tuple{rg, rest}}}}}}}:
      rg

# the law that a write keeps a tree whole, of the tree of the ledger d
def Kept.laws_kept(d: Vend.Led()) -> Trees.Laws.Kept(
  Vend.L(d),
  l => h => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, l, h),
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
    case Tuple{x, Tuple{o, Tuple{fin, Tuple{pf, Tuple{wr, Tuple{cn, Tuple{rg, Tuple{df, Tuple{wh, Tuple{kp, rest}}}}}}}}}}:
      kp

# a binding is the same as itself
def Bind.is_eq_refl(
  +k: List<&2, U32>,
  +v: List<&2, U32>
) -> {Trees.Binding.is_eq(Trees.Binding{k, v}, Trees.Binding{k, v}) == True{}: Bool}:
  %Equal.sym(Bool, Shared.List.is_eq(~U32, ~U32.is_eq, k, k), True{}, Shared.List.is_eq_refl(~U32, ~U32.is_eq, ~Shared.U32.laws(), k)): {
    List.all.if(u => Shared.List.is_eq(~U32, ~U32.is_eq, v, v), _) == True{}: Bool
  }
  Shared.List.is_eq_refl(~U32, ~U32.is_eq, ~Shared.U32.laws(), v)

# bindings that are the same are the same
def Bind.is_eq_sound(
  a: Trees.Binding,
  b: Trees.Binding
) -> {Trees.Binding.is_eq(a, b) == True{}: Bool} -> {a == b: Trees.Binding}:
  match a b:
    case Trees.Binding{+k1, +v1} Trees.Binding{+k2, +v2}:
      +h =>
        %Shared.List.is_eq_sound(~U32, ~U32.is_eq, ~Shared.U32.laws(), k1, k2)(
          Shared.List.all.if_hit(
            Shared.List.is_eq(~U32, ~U32.is_eq, k1, k2),
            u => Shared.List.is_eq(~U32, ~U32.is_eq, v1, v2)
          )(h)
        ): {Trees.Binding{k1, v1} == Trees.Binding{_, v2}: Trees.Binding}
        %Shared.List.is_eq_sound(~U32, ~U32.is_eq, ~Shared.U32.laws(), v1, v2)(
          Shared.List.all.if_rest(
            Shared.List.is_eq(~U32, ~U32.is_eq, k1, k2),
            u => Shared.List.is_eq(~U32, ~U32.is_eq, v1, v2)
          )(h)
        ): {Trees.Binding{k1, v1} == Trees.Binding{k1, _}: Trees.Binding}
        {==}

# a binding is in a list that it starts
def Bind.contains_head(
  +x: Trees.Binding,
  r: List<&2, Trees.Binding>
) -> {List.contains(~Trees.Binding, ~Trees.Binding.is_eq, x <> r, x) == True{}: Bool}:
  match x:
    case Trees.Binding{+k, +v}:
      %Equal.sym(Bool, Trees.Binding.is_eq(Trees.Binding{k, v}, Trees.Binding{k, v}), True{}, Bind.is_eq_refl(k, v)): {
        List.any.if(u => List.contains(~Trees.Binding, ~Trees.Binding.is_eq, r, Trees.Binding{k, v}), _) == True{}: Bool
      }
      {==}

# the bindings ps, each in ks, are each in ks with one more binding
def Bind.within_cons(
  ps: List<&2, Trees.Binding>,
  +x: Trees.Binding,
  +ks: List<&2, Trees.Binding>
) -> {Shared.List.within(~Trees.Binding, ~Trees.Binding.is_eq, ps, ks) == True{}: Bool}
  -> {Shared.List.within(~Trees.Binding, ~Trees.Binding.is_eq, ps, x <> ks) == True{}: Bool}:
  match ps:
    case Nil{}:
      h => {==}
    case Con{+p, +r}:
      +h => Shared.Bool.and_both(
        List.contains(~Trees.Binding, ~Trees.Binding.is_eq, x <> ks, p),
        Shared.List.within(~Trees.Binding, ~Trees.Binding.is_eq, r, x <> ks)
      )(
        Shared.List.contains_cons(~Trees.Binding, ~Trees.Binding.is_eq, x, ks, p)(
          Shared.Bool.and_true_left(
            List.contains(~Trees.Binding, ~Trees.Binding.is_eq, ks, p),
            Shared.List.within(~Trees.Binding, ~Trees.Binding.is_eq, r, ks)
          )(h)
        )
      )(
        Bind.within_cons(r, x, ks)(
          Shared.Bool.and_true_right(
            List.contains(~Trees.Binding, ~Trees.Binding.is_eq, ks, p),
            Shared.List.within(~Trees.Binding, ~Trees.Binding.is_eq, r, ks)
          )(h)
        )
      )

# each binding of a list is in it
def Bind.within_refl(ks: List<&2, Trees.Binding>) -> {
  Shared.List.within(~Trees.Binding, ~Trees.Binding.is_eq, ks, ks) == True{}: Bool
}:
  match ks:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      Shared.Bool.and_both(
        List.contains(~Trees.Binding, ~Trees.Binding.is_eq, x <> r, x),
        Shared.List.within(~Trees.Binding, ~Trees.Binding.is_eq, r, x <> r)
      )(Bind.contains_head(x, r))(Bind.within_cons(r, x, r)(Bind.within_refl(r)))
# a tree that is kept lists its bindings, and the ledger holds each resource
# among them
def Kept.Listed(~d: Vend.Led(), l: Vend.L(d), h: Maybe<&2, Hashes.Hash>) -> Data:
  Sigma<&2, &2, List<&2, Trees.Binding>, bs => Merges.Merge.And({Vend.Tree.range(~d, l, h, []) == Some{bs}: Maybe<&2, List<&2, Trees.Binding>>}, {Vend.Res.all_held(~d, l, bs) == True{}: Bool})>

# a tree that is kept is listed, once the listing is known (mr)
def Kept.split.at(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +h: Maybe<&2, Hashes.Hash>,
  mr: Maybe<&2, List<&2, Trees.Binding>>,
  em: {Vend.Tree.range(~d, l, h, []) == mr: Maybe<&2, List<&2, Trees.Binding>>},
  hk: {
    Maybe.default(&2, Bool, Maybe.bind(&2, List<&2, Trees.Binding>, Bool, mr, bs => Some{Vend.Res.all_held(~d, l, bs)}), False{}) == True{}: Bool
  }
) -> Kept.Listed(~d, l, h):
  match mr:
    case None{}:
      Empty.absurd(Kept.Listed(~d, l, h), Shared.Bool.false_ne_true(hk))
    case Some{+bs}:
      (bs, (em, hk))

# a tree that is kept is listed
def Kept.split(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +h: Maybe<&2, Hashes.Hash>,
  hk: {Vend.Tree.kept(~d, l, h) == True{}: Bool}
) -> Kept.Listed(~d, l, h):
  Kept.split.at(~d, l, h, Vend.Tree.range(~d, l, h, []), {==}, hk)

# a tree is kept when it is listed and the ledger holds each resource among its
# bindings
def Kept.of(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +bs: List<&2, Trees.Binding>,
  e1: {Vend.Tree.range(~d, l, h, []) == Some{bs}: Maybe<&2, List<&2, Trees.Binding>>},
  ha: {Vend.Res.all_held(~d, l, bs) == True{}: Bool}
) -> {Vend.Tree.kept(~d, l, h) == True{}: Bool}:
  %Equal.sym(Maybe<&2, List<&2, Trees.Binding>>, Vend.Tree.range(~d, l, h, []), Some{bs}, e1): {
    Maybe.default(&2, Bool, Maybe.bind(&2, List<&2, Trees.Binding>, Bool, _, bs2 => Some{Vend.Res.all_held(~d, l, bs2)}), False{}) == True{}: Bool
  }
  ha

# the ledger holds each resource among some bindings, when it holds each
# resource that is among the bindings bs0, and they are among them
def Kept.all_within(
  ~d: Vend.Led(),
  ~l: Vend.L(d),
  ~bs0: List<&2, Trees.Binding>,
  ~f: @B: Trees.Binding -> {List.contains(~Trees.Binding, ~Trees.Binding.is_eq, bs0, B) == True{}: Bool} -> {
    Vend.Res.held(~d, l, B) == True{}: Bool
  },
  xs: List<&2, Trees.Binding>
) -> {Shared.List.within(~Trees.Binding, ~Trees.Binding.is_eq, xs, bs0) == True{}: Bool}
  -> {Vend.Res.all_held(~d, l, xs) == True{}: Bool}:
  match xs:
    case Nil{}:
      h => {==}
    case Con{+x, +r}:
      +h => Shared.List.all.if_both(Vend.Res.held(~d, l, x), u => Vend.Res.all_held(~d, l, r))(
        f(x)(
          Shared.Bool.and_true_left(
            List.contains(~Trees.Binding, ~Trees.Binding.is_eq, bs0, x),
            Shared.List.within(~Trees.Binding, ~Trees.Binding.is_eq, r, bs0)
          )(h)
        )
      )(
        Kept.all_within(~d, ~l, ~bs0, ~f, r)(
          Shared.Bool.and_true_right(
            List.contains(~Trees.Binding, ~Trees.Binding.is_eq, bs0, x),
            Shared.List.within(~Trees.Binding, ~Trees.Binding.is_eq, r, bs0)
          )(h)
        )
      )

# the ledger holds each resource among some bindings, when it holds each
# resource that is among them
def Kept.all_of(
  ~d: Vend.Led(),
  ~l: Vend.L(d),
  ~bs: List<&2, Trees.Binding>,
  ~f: @B: Trees.Binding -> {List.contains(~Trees.Binding, ~Trees.Binding.is_eq, bs, B) == True{}: Bool} -> {
    Vend.Res.held(~d, l, B) == True{}: Bool
  }
) -> {Vend.Res.all_held(~d, l, bs) == True{}: Bool}:
  Kept.all_within(~d, ~l, ~bs, ~f, bs)(Bind.within_refl(bs))

# a binding among those that the ledger holds, once the first binding is known
# to be it or not (p), is held
def Kept.of_all.at(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  p: Bool,
  +x: Trees.Binding,
  +r: List<&2, Trees.Binding>,
  +B: Trees.Binding,
  ep: {Trees.Binding.is_eq(x, B) == p: Bool},
  ha: {Vend.Res.all_held(~d, l, x <> r) == True{}: Bool},
  hc: {List.contains(~Trees.Binding, ~Trees.Binding.is_eq, x <> r, B) == True{}: Bool},
  ih: {Vend.Res.all_held(~d, l, r) == True{}: Bool}
    -> {List.contains(~Trees.Binding, ~Trees.Binding.is_eq, r, B) == True{}: Bool}
    -> {Vend.Res.held(~d, l, B) == True{}: Bool}
) -> {Vend.Res.held(~d, l, B) == True{}: Bool}:
  match p:
    case True{}:
      %Bind.is_eq_sound(x, B)(ep): {Vend.Res.held(~d, l, _) == True{}: Bool}
      Shared.List.all.if_hit(Vend.Res.held(~d, l, x), u => Vend.Res.all_held(~d, l, r))(ha)
    case False{}:
      ih(Shared.List.all.if_rest(Vend.Res.held(~d, l, x), u => Vend.Res.all_held(~d, l, r))(ha))(
        %ep: {List.any.if(u => List.contains(~Trees.Binding, ~Trees.Binding.is_eq, r, B), _) == True{}: Bool}
        hc
      )

# a binding among those that the ledger holds is held
def Kept.of_all(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  bs: List<&2, Trees.Binding>,
  +B: Trees.Binding,
  ha: {Vend.Res.all_held(~d, l, bs) == True{}: Bool}
) -> {List.contains(~Trees.Binding, ~Trees.Binding.is_eq, bs, B) == True{}: Bool} -> {Vend.Res.held(~d, l, B) == True{}: Bool}:
  match bs:
    case Nil{}:
      hc => Empty.absurd({Vend.Res.held(~d, l, B) == True{}: Bool}, Shared.Bool.false_ne_true(hc))
    case Con{+x, +r}:
      +hc => Kept.of_all.at(
        ~d,
        l,
        Trees.Binding.is_eq(x, B),
        x,
        r,
        B,
        {==},
        ha,
        hc,
        ih => ic => Kept.of_all(~d, l, r, B, ih)(ic)
      )
# a read whose value is v is the read that found v
def Kept.look_found(
  r: Trees.Look,
  +v: List<&2, U32>,
  e: {Trees.Look.value(r) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> {r == Trees.Look.Found{v}: Trees.Look}:
  match r:
    case Trees.Look.Found{+u}:
      %Shared.Maybe.some_inj(List<&2, U32>, u, v, e): {Trees.Look.Found{u} == Trees.Look.Found{_}: Trees.Look}
      {==}
    case Trees.Look.Absent{}:
      Empty.absurd({Trees.Look.Absent{} == Trees.Look.Found{v}: Trees.Look}, Shared.Maybe.none_ne_some(List<&2, U32>, v, e))
    case Trees.Look.Missing{h}:
      Empty.absurd({Trees.Look.Missing{h} == Trees.Look.Found{v}: Trees.Look}, Shared.Maybe.none_ne_some(List<&2, U32>, v, e))

# the value of the read of a written value is the value
def Kept.value_of(m: Maybe<&2, List<&2, U32>>) -> {Trees.Look.value(Trees.Look.of(m)) == m: Maybe<&2, List<&2, U32>>}:
  match m:
    case None{}:
      {==}
    case Some{v}:
      {==}

# a value that a read of a tree finds is the value of the read, once the read
# is known (m)
def Kept.Some(-A: Data, m: Maybe<&2, A>) -> Data:
  Sigma<&2, &2, A, x => {m == Some{x}: Maybe<&2, A>}>

# a maybe that is some is some value
def Kept.some_of(-A: Data, m: Maybe<&2, A>, h: {Maybe.is_some(&2, A, m) == True{}: Bool}) -> Kept.Some(A, m):
  match m:
    case None{}:
      Empty.absurd(Kept.Some(A, m), Shared.Bool.false_ne_true(h))
    case Some{+x}:
      (x, {==})

# the law of a listing: a binding is in the listing under a prefix exactly when
# its key leads and the tree reads it so
def Kept.range_mem(
  -S: Data,
  -o: Trees.Tree.Ops(S),
  rg: Trees.Laws.Range(S, o),
  s: S,
  h: Maybe<&2, Hashes.Hash>,
  p: List<&2, U32>,
  bs: List<&2, Trees.Binding>,
  e1: {Trees.Ops.range(S, o)(s)(h)(p) == Some{bs}: Maybe<&2, List<&2, Trees.Binding>>},
  k: List<&2, U32>,
  v: List<&2, U32>
) -> {
  List.contains(~Trees.Binding, ~Trees.Binding.is_eq, bs, Trees.Binding{k, v})
    == Bool.and(
      Trees.Key.leads(p, k),
      Shared.Maybe.is_eq(
        ~List<&2, U32>,
        ~Shared.List.is_eq(~U32, ~U32.is_eq),
        Trees.Look.value(Trees.Ops.look(S, o)(s)(h)(k)),
        Some{v}
      )
    ): Bool
}:
  Merges.Merge.snd(
    {Trees.Bindings.sorted(bs) == True{}: Bool},
    (@k2: List<&2, U32> -> @v2: List<&2, U32> -> {
      List.contains(~Trees.Binding, ~Trees.Binding.is_eq, bs, Trees.Binding{k2, v2})
        == Bool.and(
          Trees.Key.leads(p, k2),
          Shared.Maybe.is_eq(
            ~List<&2, U32>,
            ~Shared.List.is_eq(~U32, ~U32.is_eq),
            Trees.Look.value(Trees.Ops.look(S, o)(s)(h)(k2)),
            Some{v2}
          )
        ): Bool
    }),
    rg(s)(h)(p)(bs)(e1)
  )(k)(v)

# a binding of a listing is read so by the tree
def Kept.in_range(
  ~d: Vend.Led(),
  +lf: Vend.L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +bs: List<&2, Trees.Binding>,
  e1: {Vend.Tree.range(~d, lf, h, []) == Some{bs}: Maybe<&2, List<&2, Trees.Binding>>},
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  hc: {List.contains(~Trees.Binding, ~Trees.Binding.is_eq, bs, Trees.Binding{k, v}) == True{}: Bool}
) -> {Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, lf, h, k)) == Some{v}: Maybe<&2, List<&2, U32>>}:
  Shared.Maybe.is_eq_sound(
    ~List<&2, U32>,
    ~Shared.List.is_eq(~U32, ~U32.is_eq),
    x => y => Shared.List.is_eq_sound(~U32, ~U32.is_eq, ~Shared.U32.laws(), x, y),
    Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, lf, h, k)),
    Some{v}
  )(
    Shared.Bool.and_true_right(
      Trees.Key.leads([], k),
      Shared.Maybe.is_eq(
        ~List<&2, U32>,
        ~Shared.List.is_eq(~U32, ~U32.is_eq),
        Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, lf, h, k)),
        Some{v}
      )
    )(
      Equal.trans(
        Bool,
        Bool.and(
          Trees.Key.leads([], k),
          Shared.Maybe.is_eq(
            ~List<&2, U32>,
            ~Shared.List.is_eq(~U32, ~U32.is_eq),
            Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, lf, h, k)),
            Some{v}
          )
        ),
        List.contains(~Trees.Binding, ~Trees.Binding.is_eq, bs, Trees.Binding{k, v}),
        True{},
        Equal.sym(
          Bool,
          List.contains(~Trees.Binding, ~Trees.Binding.is_eq, bs, Trees.Binding{k, v}),
          Bool.and(
            Trees.Key.leads([], k),
            Shared.Maybe.is_eq(
              ~List<&2, U32>,
              ~Shared.List.is_eq(~U32, ~U32.is_eq),
              Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, lf, h, k)),
              Some{v}
            )
          ),
          Kept.range_mem(
            Vend.L(d),
            Replicas.Led.tree(Requests.Ask.machine(), d),
            Kept.laws_range(d),
            lf,
            h,
            [],
            bs,
            e1,
            k,
            v
          )
        ),
        hc
      )
    )
  )

# a binding that the tree reads so is in a listing of it
def Kept.of_range(
  ~d: Vend.Led(),
  +lf: Vend.L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +bs: List<&2, Trees.Binding>,
  e1: {Vend.Tree.range(~d, lf, h, []) == Some{bs}: Maybe<&2, List<&2, Trees.Binding>>},
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  hv: {Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, lf, h, k)) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> {List.contains(~Trees.Binding, ~Trees.Binding.is_eq, bs, Trees.Binding{k, v}) == True{}: Bool}:
  Equal.trans(
    Bool,
    List.contains(~Trees.Binding, ~Trees.Binding.is_eq, bs, Trees.Binding{k, v}),
    Bool.and(
      Trees.Key.leads([], k),
      Shared.Maybe.is_eq(
        ~List<&2, U32>,
        ~Shared.List.is_eq(~U32, ~U32.is_eq),
        Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, lf, h, k)),
        Some{v}
      )
    ),
    True{},
    Kept.range_mem(
      Vend.L(d),
      Replicas.Led.tree(Requests.Ask.machine(), d),
      Kept.laws_range(d),
      lf,
      h,
      [],
      bs,
      e1,
      k,
      v
    ),
    Equal.trans(
      Bool,
      Bool.and(
        Trees.Key.leads([], k),
        Shared.Maybe.is_eq(
          ~List<&2, U32>,
          ~Shared.List.is_eq(~U32, ~U32.is_eq),
          Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, lf, h, k)),
          Some{v}
        )
      ),
      Bool.and(
        Trees.Key.leads([], k),
        Shared.Maybe.is_eq(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), Some{v}, Some{v})
      ),
      True{},
      Equal.cong(
        Maybe<&2, List<&2, U32>>,
        Bool,
        x => Bool.and(
          Trees.Key.leads([], k),
          Shared.Maybe.is_eq(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), x, Some{v})
        ),
        Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, lf, h, k)),
        Some{v},
        hv
      ),
      %Equal.sym(
        Bool,
        Shared.List.is_eq(~U32, ~U32.is_eq, v, v),
        True{},
        Shared.List.is_eq_refl(~U32, ~U32.is_eq, ~Shared.U32.laws(), v)
      ): {Bool.and(Trees.Key.leads([], k), _) == True{}: Bool}
      {==}
    )
  )
# a binding of a tree after a write of a key whose value is not the one that
# the tree read is a binding that the tree read before, once the old read is
# known (sx)
def Kept.new_held.frame(
  ~d: Vend.Led(),
  +lf: Vend.L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +h1: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  +m: Maybe<&2, List<&2, U32>>,
  +bs: List<&2, Trees.Binding>,
  +k2: List<&2, U32>,
  +v2: List<&2, U32>,
  ep: {Shared.List.is_eq(~U32, ~U32.is_eq, k, k2) == False{}: Bool},
  +e1: {Vend.Tree.range(~d, lf, h, []) == Some{bs}: Maybe<&2, List<&2, Trees.Binding>>},
  +ha: {Vend.Res.all_held(~d, lf, bs) == True{}: Bool},
  wr: Merges.Merge.Writes(~d, lf, h1, h, k, m),
  hv: {Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, lf, h1, k2)) == Some{v2}: Maybe<&2, List<&2, U32>>},
  sx: Kept.Some(Maybe<&2, List<&2, U32>>, Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, h, k2))
) -> {Vend.Res.held(~d, lf, Trees.Binding{k2, v2}) == True{}: Bool}:
  (+x, +ex) = sx
  Kept.of_all(
    ~d,
    lf,
    bs,
    Trees.Binding{k2, v2},
    ha
  )(
    Kept.of_range(
      ~d,
      lf,
      h,
      bs,
      e1,
      k2,
      v2,
      Merges.Merge.value_known(
        Replicas.Tree.look(~Requests.Ask.machine(), ~d, lf, h, k2),
        Some{v2},
        %Equal.sym(
          Maybe<&2, List<&2, U32>>,
          Some{v2},
          x,
          Shared.Maybe.some_inj(
            Maybe<&2, List<&2, U32>>,
            Some{v2},
            x,
            %Kept.look_found(Replicas.Tree.look(~Requests.Ask.machine(), ~d, lf, h1, k2), v2, hv): {
              Trees.Look.known(_) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
            }
            Merges.Merge.writes_frame(~d, lf, h1, h, k, m, wr, k2, x, ep, ex)
          )
        ): {Trees.Look.known(Replicas.Tree.look(~Requests.Ask.machine(), ~d, lf, h, k2)) == Some{_}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
        ex
      )
    )
  )

# a binding of a tree after a write is held, once the key is known to be the
# written one or not (p)
def Kept.new_held.at(
  ~d: Vend.Led(),
  p: Bool,
  +lf: Vend.L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +h1: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  +m: Maybe<&2, List<&2, U32>>,
  +bs: List<&2, Trees.Binding>,
  +k2: List<&2, U32>,
  +v2: List<&2, U32>,
  +ep: {Shared.List.is_eq(~U32, ~U32.is_eq, k, k2) == p: Bool},
  +e1: {Vend.Tree.range(~d, lf, h, []) == Some{bs}: Maybe<&2, List<&2, Trees.Binding>>},
  +ha: {Vend.Res.all_held(~d, lf, bs) == True{}: Bool},
  wr: Merges.Merge.Writes(~d, lf, h1, h, k, m),
  hm: @v: List<&2, U32> -> {m == Some{v}: Maybe<&2, List<&2, U32>>} -> {Vend.Res.held(~d, lf, Trees.Binding{k, v}) == True{}: Bool},
  +hv: {Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, lf, h1, k2)) == Some{v2}: Maybe<&2, List<&2, U32>>}
) -> {Vend.Res.held(~d, lf, Trees.Binding{k2, v2}) == True{}: Bool}:
  match p:
    case True{}:
      %Shared.List.is_eq_sound(~U32, ~U32.is_eq, ~Shared.U32.laws(), k, k2)(ep): {Vend.Res.held(~d, lf, Trees.Binding{_, v2}) == True{}: Bool}
      hm(v2)(
        Equal.trans(
          Maybe<&2, List<&2, U32>>,
          m,
          Trees.Look.value(Trees.Look.of(m)),
          Some{v2},
          Equal.sym(Maybe<&2, List<&2, U32>>, Trees.Look.value(Trees.Look.of(m)), m, Kept.value_of(m)),
          %Merges.Merge.writes_hit(~d, lf, h1, h, k, m, wr): {Trees.Look.value(_) == Some{v2}: Maybe<&2, List<&2, U32>>}
          %Equal.sym(
            List<&2, U32>,
            k,
            k2,
            Shared.List.is_eq_sound(~U32, ~U32.is_eq, ~Shared.U32.laws(), k, k2)(ep)
          ): {Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, lf, h1, _)) == Some{v2}: Maybe<&2, List<&2, U32>>}
          hv
        )
      )
    case False{}:
      Kept.new_held.frame(
        ~d,
        lf,
        h,
        h1,
        k,
        m,
        bs,
        k2,
        v2,
        ep,
        e1,
        ha,
        wr,
        hv,
        Kept.some_of(
          Maybe<&2, List<&2, U32>>,
          Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, h, k2),
          Merges.Merge.final_look(
            Vend.L(d),
            Replicas.Led.tree(Requests.Ask.machine(), d),
            Merges.Merge.laws_whole(d),
            lf,
            h,
            bs,
            e1,
            k2
          )
        )
      )

# a binding of the listing of a tree after a write is held
def Kept.new_held(
  ~d: Vend.Led(),
  +lf: Vend.L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +h1: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  +m: Maybe<&2, List<&2, U32>>,
  +bs: List<&2, Trees.Binding>,
  +e1: {Vend.Tree.range(~d, lf, h, []) == Some{bs}: Maybe<&2, List<&2, Trees.Binding>>},
  +ha: {Vend.Res.all_held(~d, lf, bs) == True{}: Bool},
  wr: Merges.Merge.Writes(~d, lf, h1, h, k, m),
  hm: @v: List<&2, U32> -> {m == Some{v}: Maybe<&2, List<&2, U32>>} -> {Vend.Res.held(~d, lf, Trees.Binding{k, v}) == True{}: Bool},
  +bs2: List<&2, Trees.Binding>,
  +e2: {Vend.Tree.range(~d, lf, h1, []) == Some{bs2}: Maybe<&2, List<&2, Trees.Binding>>},
  B: Trees.Binding,
  hc: {List.contains(~Trees.Binding, ~Trees.Binding.is_eq, bs2, B) == True{}: Bool}
) -> {Vend.Res.held(~d, lf, B) == True{}: Bool}:
  match B:
    case Trees.Binding{+k2, +v2}:
      Kept.new_held.at(
        ~d,
        Shared.List.is_eq(~U32, ~U32.is_eq, k, k2),
        lf,
        h,
        h1,
        k,
        m,
        bs,
        k2,
        v2,
        {==},
        e1,
        ha,
        wr,
        hm,
        Kept.in_range(~d, lf, h1, bs2, e2, k2, v2, hc)
      )

# a write to a kept tree, of a key whose value is held, once the tree after it
# is listed (sr), gives a kept tree
def Kept.put.range(
  ~d: Vend.Led(),
  +lf: Vend.L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +h1: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  +m: Maybe<&2, List<&2, U32>>,
  +bs: List<&2, Trees.Binding>,
  +e1: {Vend.Tree.range(~d, lf, h, []) == Some{bs}: Maybe<&2, List<&2, Trees.Binding>>},
  +ha: {Vend.Res.all_held(~d, lf, bs) == True{}: Bool},
  wr: Merges.Merge.Writes(~d, lf, h1, h, k, m),
  hm: @v: List<&2, U32> -> {m == Some{v}: Maybe<&2, List<&2, U32>>} -> {Vend.Res.held(~d, lf, Trees.Binding{k, v}) == True{}: Bool},
  sr: Kept.Some(List<&2, Trees.Binding>, Vend.Tree.range(~d, lf, h1, []))
) -> {Vend.Tree.kept(~d, lf, h1) == True{}: Bool}:
  (+bs2, +e2) = sr
  Kept.of(
    ~d,
    lf,
    h1,
    bs2,
    e2,
    Kept.all_of(
      ~d,
      ~lf,
      ~bs2,
      ~(B => hc => Kept.new_held(~d, lf, h, h1, k, m, bs, e1, ha, wr, hm, bs2, e2, B, hc))
    )
  )

# a write to a kept tree, of a key whose value is held, once the tree is listed
# (ls), gives a kept tree
def Kept.put.listed(
  ~d: Vend.Led(),
  +lf: Vend.L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  +m: Maybe<&2, List<&2, U32>>,
  +e: Trees.Edit,
  +ep: {Replicas.Tree.put(~Requests.Ask.machine(), ~d, lf, h, k, m) == Some{e}: Maybe<&2, Trees.Edit>},
  +hh: Merges.Merge.Held(~d, lf, Trees.Edit.nodes(e)),
  hm: @v: List<&2, U32> -> {m == Some{v}: Maybe<&2, List<&2, U32>>} -> {Vend.Res.held(~d, lf, Trees.Binding{k, v}) == True{}: Bool},
  ls: Kept.Listed(~d, lf, h)
) -> {Vend.Tree.kept(~d, lf, Trees.Edit.root(e)) == True{}: Bool}:
  (+bs, r1) = ls
  (+e1, +ha) = r1
  Kept.put.range(
    ~d,
    lf,
    h,
    Trees.Edit.root(e),
    k,
    m,
    bs,
    e1,
    ha,
    Replicas.Hist.write(Requests.Ask.machine(), d)(lf)(lf)(h)(k)(m)(e)(ep)(Replicas.Hist.refl(~Requests.Ask.machine(), ~d, lf))(
      Replicas.Ext.held(~Requests.Ask.machine(), ~d, lf, e, hh)
    ),
    hm,
    Kept.some_of(
      List<&2, Trees.Binding>,
      Vend.Tree.range(~d, lf, Trees.Edit.root(e), []),
      Kept.laws_kept(d)(lf)(lf)(h)(bs)(k)(m)(e)(e1)(ep)(Replicas.Hist.refl(~Requests.Ask.machine(), ~d, lf))(
        Replicas.Ext.held(~Requests.Ask.machine(), ~d, lf, e, hh)
      )
    )
  )

# a write to a kept tree, of a key whose value is held, gives a kept tree
def Kept.put(
  ~d: Vend.Led(),
  +lf: Vend.L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  +m: Maybe<&2, List<&2, U32>>,
  +e: Trees.Edit,
  hk: {Vend.Tree.kept(~d, lf, h) == True{}: Bool},
  +ep: {Replicas.Tree.put(~Requests.Ask.machine(), ~d, lf, h, k, m) == Some{e}: Maybe<&2, Trees.Edit>},
  +hh: Merges.Merge.Held(~d, lf, Trees.Edit.nodes(e)),
  hm: @v: List<&2, U32> -> {m == Some{v}: Maybe<&2, List<&2, U32>>} -> {Vend.Res.held(~d, lf, Trees.Binding{k, v}) == True{}: Bool}
) -> {Vend.Tree.kept(~d, lf, Trees.Edit.root(e)) == True{}: Bool}:
  Kept.put.listed(~d, lf, h, k, m, e, ep, hh, hm, Kept.split(~d, lf, h, hk))
# what an act does to the content of a line, in a ledger: a taken act gives a
# tree that the ledger holds whole, and an opened line starts from one, with no
# log
def Acts.Kept(~d: Vend.Led(), lf: Vend.L(d), a: Replicas.Act) -> Data:
  match a:
    case Replicas.Act.Stale{}:
      Unit
    case Replicas.Act.Label{x}:
      Unit
    case Replicas.Act.Taken{vs, h, ns}:
      {Vend.Tree.kept(~d, lf, h) == True{}: Bool}
    case Replicas.Act.Opens{b, t2, ns}:
      Merges.Merge.And({Vend.Tree.kept(~d, lf, Replicas.Tip.content(t2)) == True{}: Bool}, {Replicas.Tip.log(t2) == None{}: Maybe<&2, Hashes.Hash>})

# the binding of a resource that the ledger holds is held
def Res.held_res(
  ~d: Vend.Led(),
  +lf: Vend.L(d),
  +n: Resources.Name,
  +new: Maybe<&2, Requests.Res>,
  hk: {Vend.Res.kept(~d, lf, new) == True{}: Bool}
) -> @v: List<&2, U32> -> {Vend.Res.value(new) == Some{v}: Maybe<&2, List<&2, U32>>} -> {
  Vend.Res.held(~d, lf, Trees.Binding{Vend.Key.res(n), v}) == True{}: Bool
}:
  match new:
    case None{}:
      v => x => Empty.absurd({Vend.Res.held(d, lf, Trees.Binding{Vend.Key.res(n), v}) == True{} : Bool}, {(%x : {\{None: Unit; \{Some: f0 => Empty; \{}}} : Maybe<&2, List<&2, U32>> -> Type}(_); Unit{}) : Empty})
    case Some{value}:
      v => x => (%{(%Equal.sym(Maybe<&2, List<&2, U32>>, Some{Requests.Res.code(value, [])}, Some{v}, x) : {\{None: Unit; \{Some: f0 => {f0 == v : List<&2, U32>}; \{}}} : Maybe<&2, List<&2, U32>> -> Type}(_); {==}) : {Requests.Res.code(value, []) == v : List<&2, U32>}} : {Vend.Res.held(d, lf, Trees.Binding{Vend.Key.res(n), _}) == True{} : Bool}; (%Equal.sym(Maybe<&2, Codes.Read<Requests.Res>>, Requests.Res.code.read(Requests.Res.code(value, [])), Some{Codes.Read{value, []}}, Requests.Res.code_read(value, [])) : {Vend.Res.kept(d, lf, Codes.Code.whole.check(Requests.Res, Requests.Res.code, Codes.Read.whole(Requests.Res, _), Requests.Res.code(value, []))) == True{} : Bool}; (%Equal.sym(Bool, Crits.Key.is_eq(Requests.Res.code(value, []), Requests.Res.code(value, [])), True{}, Crits.Key.is_eq_refl(Requests.Res.code(value, []))) : {Vend.Res.kept(d, lf, Bool.pick(Maybe<&2, Requests.Res>, _, Some{value}, None{})) == True{} : Bool}; hk)))

# an act that puts a tree gives a kept tree, once the tree that it writes is
# known (p)
def Act.put_kept.at(
  ~d: Vend.Led(),
  +lf: Vend.L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  +m: Maybe<&2, List<&2, U32>>,
  +vs: Maybe<&2, List<&2, String>>,
  +ns: List<&2, List<&2, U32>>,
  +a: Replicas.Act,
  hk: {Vend.Tree.kept(~d, lf, h) == True{}: Bool},
  p: Maybe<&2, Trees.Edit>,
  +ep: {Replicas.Tree.put(~Requests.Ask.machine(), ~d, lf, h, k, m) == p: Maybe<&2, Trees.Edit>},
  +ec: {Vend.Act.put(vs, ns, p) == Some{a}: Maybe<&2, Replicas.Act>},
  +hh: {Replicas.Act.held(~Requests.Ask.machine(), ~d, lf, a) == True{}: Bool},
  hm: @v: List<&2, U32> -> {m == Some{v}: Maybe<&2, List<&2, U32>>} -> {Vend.Res.held(~d, lf, Trees.Binding{k, v}) == True{}: Bool}
) -> Acts.Kept(~d, lf, a):
  match p:
    case None{}:
      Empty.absurd(Acts.Kept(~d, lf, a), Shared.Maybe.none_ne_some(Replicas.Act, a, ec))
    case Some{+e}:
      %Shared.Maybe.some_inj(
        Replicas.Act,
        Replicas.Act.Taken{vs, Trees.Edit.root(e), List.append(&2, List<&2, U32>, ns, Trees.Edit.nodes(e))},
        a,
        ec
      ): Acts.Kept(~d, lf, _)
      Kept.put(
        ~d,
        lf,
        h,
        k,
        m,
        e,
        hk,
        ep,
        Replicas.Ext.holds_right(~Requests.Ask.machine(), ~d, lf, ns, Trees.Edit.nodes(e))(
          %Equal.sym(
            Replicas.Act,
            Replicas.Act.Taken{vs, Trees.Edit.root(e), List.append(&2, List<&2, U32>, ns, Trees.Edit.nodes(e))},
            a,
            Shared.Maybe.some_inj(
              Replicas.Act,
              Replicas.Act.Taken{vs, Trees.Edit.root(e), List.append(&2, List<&2, U32>, ns, Trees.Edit.nodes(e))},
              a,
              ec
            )
          ): {Replicas.Act.held(~Requests.Ask.machine(), ~d, lf, _) == True{}: Bool}
          hh
        ),
        hm
      )

# an act that puts a tree gives a kept tree, when the tree that it writes to is
# kept, the ledger holds what the act adds, and the value that it writes is held
def Act.put_kept(
  ~d: Vend.Led(),
  +lf: Vend.L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  +m: Maybe<&2, List<&2, U32>>,
  +vs: Maybe<&2, List<&2, String>>,
  +ns: List<&2, List<&2, U32>>,
  +a: Replicas.Act,
  hk: {Vend.Tree.kept(~d, lf, h) == True{}: Bool},
  ec: {Vend.Act.put(vs, ns, Replicas.Tree.put(~Requests.Ask.machine(), ~d, lf, h, k, m)) == Some{a}: Maybe<&2, Replicas.Act>},
  hh: {Replicas.Act.held(~Requests.Ask.machine(), ~d, lf, a) == True{}: Bool},
  hm: @v: List<&2, U32> -> {m == Some{v}: Maybe<&2, List<&2, U32>>} -> {Vend.Res.held(~d, lf, Trees.Binding{k, v}) == True{}: Bool}
) -> Acts.Kept(~d, lf, a):
  Act.put_kept.at(~d, lf, h, k, m, vs, ns, a, hk, Replicas.Tree.put(~Requests.Ask.machine(), ~d, lf, h, k, m), {==}, ec, hh, hm)


# a bind that gives an act whose content is kept, when the rest gives such an
# act for each value that the read gives
def Kept.bind(
  ~d: Vend.Led(),
  +lf: Vend.L(d),
  -A: Data,
  m: Maybe<&2, A>,
  f: A -> Maybe<&2, Replicas.Act>,
  +a: Replicas.Act,
  hf: @x: A -> {f(x) == Some{a}: Maybe<&2, Replicas.Act>} -> Acts.Kept(~d, lf, a),
  e: {Maybe.bind(&2, A, Replicas.Act, m, f) == Some{a}: Maybe<&2, Replicas.Act>}
) -> Acts.Kept(~d, lf, a):
  match m:
    case None{}:
      Empty.absurd(Acts.Kept(d, lf, a), {(%e : {\{None: Unit; \{Some: f0 => Empty; \{}}} : Maybe<&2, Replicas.Act> -> Type}(_); Unit{}) : Empty})
    case Some{value}:
      hf(value)(e)

# a test that gives an act whose content is kept, when each branch does
def Kept.when(
  ~d: Vend.Led(),
  +lf: Vend.L(d),
  p: Bool,
  f: Unit -> Maybe<&2, Replicas.Act>,
  g: Unit -> Maybe<&2, Replicas.Act>,
  +a: Replicas.Act,
  hf: {f(Unit{}) == Some{a}: Maybe<&2, Replicas.Act>} -> Acts.Kept(~d, lf, a),
  hg: {g(Unit{}) == Some{a}: Maybe<&2, Replicas.Act>} -> Acts.Kept(~d, lf, a),
  e: {Shared.Bool.when(Maybe<&2, Replicas.Act>, p, f, g) == Some{a}: Maybe<&2, Replicas.Act>}
) -> Acts.Kept(~d, lf, a):
  match p:
    case False{}:
      hg(e)
    case True{}:
      hf(e)

# the act that sets a resource that the ledger holds gives a kept tree, once it
# is known whether the ledger holds the resource (p)
def Res.set_kept.at.g22(
  ~d: Vend.Led(),
  +lf: Vend.L(d),
  +t: Replicas.Tip,
  +n: Resources.Name,
  +new: Maybe<&2, Requests.Res>,
  +a: Replicas.Act,
  +hk: {Vend.Tree.kept(d, lf, Replicas.Tip.content(t)) == True{} : Bool},
  +hh: {Replicas.Act.held(Requests.Ask.machine(), d, lf, a) == True{} : Bool},
  +x: Bool,
  hx: {x == Vend.Res.kept(d, lf, new) : Bool},
  +ep: {x == False{} : Bool},
  +ec: {Shared.Bool.when(Maybe<&2, Replicas.Act>, x, u => Vend.Act.put(None{}, [], Replicas.Tree.put(Requests.Ask.machine(), d, lf, Replicas.Tip.content(t), Vend.Key.res(n), Vend.Res.value(new))), u => None{}) == Some{a} : Maybe<&2, Replicas.Act>}) ->
  Acts.Kept(d, lf, a):
  match x:
    case False{}:
      Empty.absurd(Acts.Kept(d, lf, a), {(%ec : {\{None: Unit; \{Some: f0 => Empty; \{}}} : Maybe<&2, Replicas.Act> -> Type}(_); Unit{}) : Empty})
    case True{}:
      Empty.absurd(Acts.Kept(d, lf, a), {(%ep : {\{False: Empty; \{True: Unit; \{}}} : Bool -> Type}(_); Unit{}) : Empty})

def Res.set_kept.at(
  ~d: Vend.Led(),
  +lf: Vend.L(d),
  p: Bool,
  +t: Replicas.Tip,
  +n: Resources.Name,
  +new: Maybe<&2, Requests.Res>,
  +a: Replicas.Act,
  ep: {Vend.Res.kept(~d, lf, new) == p: Bool},
  hk: {Vend.Tree.kept(~d, lf, Replicas.Tip.content(t)) == True{}: Bool},
  ec: {Vend.Res.set(~d, lf, t, n, new) == Some{a}: Maybe<&2, Replicas.Act>},
  hh: {Replicas.Act.held(~Requests.Ask.machine(), ~d, lf, a) == True{}: Bool}
) -> Acts.Kept(~d, lf, a):
  match p:
    case False{}:
      Res.set_kept.at.g22(~d, lf, t, n, new, a, hk, hh, Vend.Res.kept(d, lf, new), {==}, ep, ec)
    case True{}:
      Kept.when(~d, lf, Vend.Res.kept(d, lf, new), u => Vend.Act.put(None{}, [], Replicas.Tree.put(Requests.Ask.machine(), d, lf, Replicas.Tip.content(t), Vend.Key.res(n), Vend.Res.value(new))), u => None{}, a, x => Act.put_kept(~d, lf, Replicas.Tip.content(t), Vend.Key.res(n), Vend.Res.value(new), None{}, [], a, hk, x, hh, v => x1 => Res.held_res(~d, lf, n, new, ep)(v)(x1)), x => Empty.absurd(Acts.Kept(d, lf, a), {(%x : {\{None: Unit; \{Some: f0 => Empty; \{}}} : Maybe<&2, Replicas.Act> -> Type}(_); Unit{}) : Empty}), ec)

# the act that sets a resource gives a kept tree
def Res.set_kept(
  ~d: Vend.Led(),
  +lf: Vend.L(d),
  +t: Replicas.Tip,
  +n: Resources.Name,
  +new: Maybe<&2, Requests.Res>,
  +a: Replicas.Act,
  hk: {Vend.Tree.kept(~d, lf, Replicas.Tip.content(t)) == True{}: Bool},
  ec: {Vend.Res.set(~d, lf, t, n, new) == Some{a}: Maybe<&2, Replicas.Act>},
  hh: {Replicas.Act.held(~Requests.Ask.machine(), ~d, lf, a) == True{}: Bool}
) -> Acts.Kept(~d, lf, a):
  Res.set_kept.at(~d, lf, Vend.Res.kept(~d, lf, new), t, n, new, a, {==}, hk, ec, hh)

# a write, once its reads are known, gives a kept tree
def Write.act.of_kept(
  ~d: Vend.Led(),
  +lf: Vend.L(d),
  +t: Replicas.Tip,
  +n: Resources.Name,
  +ours: Maybe<&2, Requests.Res>,
  +held: Maybe<&2, Requests.Res>,
  +new: Maybe<&2, Requests.Res>,
  +a: Replicas.Act,
  hk: {Vend.Tree.kept(~d, lf, Replicas.Tip.content(t)) == True{}: Bool},
  ec: {Vend.Write.act.of(~d, lf, t, n, ours, held, new) == Some{a}: Maybe<&2, Replicas.Act>},
  hh: {Replicas.Act.held(~Requests.Ask.machine(), ~d, lf, a) == True{}: Bool}
) -> Acts.Kept(~d, lf, a):
  Kept.when(~d, lf, Shared.Maybe.is_eq(Requests.Res, x => y => Codes.Code.is_eq(Requests.Res, Requests.Res.code, x, y), ours, held), u => Vend.Res.set(d, lf, t, n, new), u => Some{Replicas.Act.Stale{}}, a, x => Res.set_kept(~d, lf, t, n, new, a, hk, x, hh), x => (%Shared.Maybe.some_inj(Replicas.Act, Replicas.Act.Stale{}, a, x) : Acts.Kept(d, lf, _); Unit{}), ec)

# a write gives a kept tree
def Write.act_kept(
  ~d: Vend.Led(),
  +lf: Vend.L(d),
  +t: Replicas.Tip,
  +n: Resources.Name,
  +base: Maybe<&2, Ledgers.Id>,
  +x: Requests.Content,
  +a: Replicas.Act,
  hk: {Vend.Tree.kept(~d, lf, Replicas.Tip.content(t)) == True{}: Bool},
  ec: {Vend.Write.act(~d, lf, t, n, base, x) == Some{a}: Maybe<&2, Replicas.Act>},
  hh: {Replicas.Act.held(~Requests.Ask.machine(), ~d, lf, a) == True{}: Bool}
) -> Acts.Kept(~d, lf, a):
  Kept.bind(
    ~d,
    lf,
    Maybe<&2, Requests.Res>,
    Vend.Res.find(~d, lf, Replicas.Tip.content(t), n),
    ours => Maybe.bind(
      &2,
      Maybe<&2, Hashes.Hash>,
      Replicas.Act,
      Vend.Base.root(~d, lf, t, base),
      h => Maybe.bind(
        &2,
        Maybe<&2, Requests.Res>,
        Replicas.Act,
        Vend.Res.find(~d, lf, h, n),
        held => Maybe.bind(
          &2,
          Maybe<&2, Requests.Res>,
          Replicas.Act,
          Vend.Content.find(~d, lf, t, n, x),
          new => Vend.Write.act.of(~d, lf, t, n, ours, held, new)
        )
      )
    ),
    a,
    +ours => e1 => Kept.bind(
      ~d,
      lf,
      Maybe<&2, Hashes.Hash>,
      Vend.Base.root(~d, lf, t, base),
      h => Maybe.bind(
        &2,
        Maybe<&2, Requests.Res>,
        Replicas.Act,
        Vend.Res.find(~d, lf, h, n),
        held => Maybe.bind(
          &2,
          Maybe<&2, Requests.Res>,
          Replicas.Act,
          Vend.Content.find(~d, lf, t, n, x),
          new => Vend.Write.act.of(~d, lf, t, n, ours, held, new)
        )
      ),
      a,
      +h => e2 => Kept.bind(
        ~d,
        lf,
        Maybe<&2, Requests.Res>,
        Vend.Res.find(~d, lf, h, n),
        held => Maybe.bind(
          &2,
          Maybe<&2, Requests.Res>,
          Replicas.Act,
          Vend.Content.find(~d, lf, t, n, x),
          new => Vend.Write.act.of(~d, lf, t, n, ours, held, new)
        ),
        a,
        +held => e3 => Kept.bind(
          ~d,
          lf,
          Maybe<&2, Requests.Res>,
          Vend.Content.find(~d, lf, t, n, x),
          new => Vend.Write.act.of(~d, lf, t, n, ours, held, new),
          a,
          +new => e4 => Write.act.of_kept(~d, lf, t, n, ours, held, new, a, hk, e4, hh),
          e3
        ),
        e2
      ),
      e1
    ),
    ec
  )

# the empty tree lists nothing, by the law of a tree
def Kept.empty_range(
  -S: Data,
  -o: Trees.Tree.Ops(S),
  wh: Trees.Laws.Whole(S, o),
  s: S
) -> {Trees.Ops.range(S, o)(s)(None{})([]) == Some{[]}: Maybe<&2, List<&2, Trees.Binding>>}:
  match wh:
    case Tuple{fst, snd}:
      fst(s)([])

# the empty tree is kept
def Kept.empty(~d: Vend.Led(), +lf: Vend.L(d)) -> {Vend.Tree.kept(~d, lf, None{}) == True{}: Bool}:
  Kept.of(
    ~d,
    lf,
    None{},
    [],
    Kept.empty_range(Vend.L(d), Replicas.Led.tree(Requests.Ask.machine(), d), Merges.Merge.laws_whole(d), lf),
    {==}
  )

# a move gives a kept tree, once it is known whether the ledger holds the tree
# whole (p)
def Move.act_kept.at.g3(
  ~d: Vend.Led(),
  +lf: Vend.L(d),
  +p: Bool,
  +s: Requests.Source,
  +a: Replicas.Act,
  +x: Bool,
  hx: {x == Maybe.default(&2, Bool, Maybe.bind(&2, List<&2, Trees.Binding>, Bool, Trees.Ops.range(Ledgers.Kind.L(Requests.Ask, Replicas.Led.kind((Requests.Ask, (Requests.Ask.code, Requests.Ask.code.read, x => r => Requests.Ask.code_read(x, r)), Requests.Ask.arrival, Requests.Ask.governs, Requests.Key.seal), d)), Replicas.Led.tree((Requests.Ask, (Requests.Ask.code, Requests.Ask.code.read, x => r => Requests.Ask.code_read(x, r)), Requests.Ask.arrival, Requests.Ask.governs, Requests.Key.seal), d), lf, Vend.Source.root(s), []), bs => Some{Vend.Res.all_held(d, lf, bs)}), False{}) : Bool},
  +ep: {x == p : Bool},
  +ec: {Shared.Bool.when(Maybe<&2, Replicas.Act>, x, u => Some{Replicas.Act.Taken{None{}, Vend.Source.root(s), []}}, u => None{}) == Some{a} : Maybe<&2, Replicas.Act>}) ->
  Acts.Kept(d, lf, a):
  match x:
    case False{}:
      Empty.absurd(Acts.Kept(d, lf, a), {(%ec : {\{None: Unit; \{Some: f0 => Empty; \{}}} : Maybe<&2, Replicas.Act> -> Type}(_); Unit{}) : Empty})
    case True{}:
      %Shared.Maybe.some_inj(Replicas.Act, Replicas.Act.Taken{None{}, Vend.Source.root(s), []}, a, ec) :
        Acts.Kept(d, lf, _)
      Equal.sym(Bool, True{}, Maybe.default(&2, Bool, Maybe.bind(&2, List<&2, Trees.Binding>, Bool, Trees.Ops.range(Ledgers.Kind.L(Requests.Ask, Replicas.Led.kind((Requests.Ask, (Requests.Ask.code, Requests.Ask.code.read, x => r => Requests.Ask.code_read(x, r)), Requests.Ask.arrival, Requests.Ask.governs, Requests.Key.seal), d)), Replicas.Led.tree((Requests.Ask, (Requests.Ask.code, Requests.Ask.code.read, x => r => Requests.Ask.code_read(x, r)), Requests.Ask.arrival, Requests.Ask.governs, Requests.Key.seal), d), lf, Vend.Source.root(s), []), bs => Some{Vend.Res.all_held(d, lf, bs)}), False{}), hx)

# a move gives a kept tree
def Move.act_kept.g3(
  ~d: Vend.Led(),
  +lf: Vend.L(d),
  +s: Requests.Source,
  +a: Replicas.Act,
  +x: Bool,
  hx: {x == Maybe.default(&2, Bool, Maybe.bind(&2, List<&2, Trees.Binding>, Bool, Trees.Ops.range(Ledgers.Kind.L(Requests.Ask, Replicas.Led.kind((Requests.Ask, (Requests.Ask.code, Requests.Ask.code.read, x => r => Requests.Ask.code_read(x, r)), Requests.Ask.arrival, Requests.Ask.governs, Requests.Key.seal), d)), Replicas.Led.tree((Requests.Ask, (Requests.Ask.code, Requests.Ask.code.read, x => r => Requests.Ask.code_read(x, r)), Requests.Ask.arrival, Requests.Ask.governs, Requests.Key.seal), d), lf, Vend.Source.root(s), []), bs => Some{Vend.Res.all_held(d, lf, bs)}), False{}) : Bool},
  +ec: {Shared.Bool.when(Maybe<&2, Replicas.Act>, x, u => Some{Replicas.Act.Taken{None{}, Vend.Source.root(s), []}}, u => None{}) == Some{a} : Maybe<&2, Replicas.Act>}) ->
  Acts.Kept(d, lf, a):
  match x:
    case False{}:
      Empty.absurd(Acts.Kept(d, lf, a), {(%ec : {\{None: Unit; \{Some: f0 => Empty; \{}}} : Maybe<&2, Replicas.Act> -> Type}(_); Unit{}) : Empty})
    case True{}:
      +hx = hx
      Move.act_kept.at.g3(~d, lf, Maybe.default(&2, Bool, Maybe.bind(&2, List<&2, Trees.Binding>, Bool, Trees.Ops.range(Ledgers.Kind.L(Requests.Ask, Replicas.Led.kind((Requests.Ask, (Requests.Ask.code, Requests.Ask.code.read, x => r => Requests.Ask.code_read(x, r)), Requests.Ask.arrival, Requests.Ask.governs, Requests.Key.seal), d)), Replicas.Led.tree((Requests.Ask, (Requests.Ask.code, Requests.Ask.code.read, x => r => Requests.Ask.code_read(x, r)), Requests.Ask.arrival, Requests.Ask.governs, Requests.Key.seal), d), lf, Vend.Source.root(s), []), bs => Some{Vend.Res.all_held(d, lf, bs)}), False{}), s, a, True{}, hx, hx, ec)

def Move.act_kept(
  ~d: Vend.Led(),
  +lf: Vend.L(d),
  +s: Requests.Source,
  +a: Replicas.Act,
  ec: {Vend.Move.act(~d, lf, s) == Some{a}: Maybe<&2, Replicas.Act>}
) -> Acts.Kept(~d, lf, a):
  Move.act_kept.g3(~d, lf, s, a, Maybe.default(&2, Bool, Maybe.bind(&2, List<&2, Trees.Binding>, Bool, Trees.Ops.range(Ledgers.Kind.L(Requests.Ask, Replicas.Led.kind((Requests.Ask, (Requests.Ask.code, Requests.Ask.code.read, x => r => Requests.Ask.code_read(x, r)), Requests.Ask.arrival, Requests.Ask.governs, Requests.Key.seal), d)), Replicas.Led.tree((Requests.Ask, (Requests.Ask.code, Requests.Ask.code.read, x => r => Requests.Ask.code_read(x, r)), Requests.Ask.arrival, Requests.Ask.governs, Requests.Key.seal), d), lf, Vend.Source.root(s), []), bs => Some{Vend.Res.all_held(d, lf, bs)}), False{}), {==}, ec)

# a new branch gives a first tip of a kept tree, once the tree of its source is
# known to be kept or not (p)
def Branch.act_kept.at(
  ~d: Vend.Led(),
  +lf: Vend.L(d),
  p: Bool,
  +t: Replicas.Tip,
  +b: String,
  +s: Requests.Source,
  +a: Replicas.Act,
  +ep: {Vend.Tree.kept(~d, lf, Vend.Source.root(s)) == p: Bool},
  ec: {Vend.Tree.when_kept(~d, lf, Vend.Source.root(s), u => Some{Replicas.Act.Opens{b, Vend.Branch.tip(t, Vend.Source.root(s)), []}}) == Some{a}: Maybe<&2, Replicas.Act>}
) -> Acts.Kept(~d, lf, a):
  match p:
    case True{}:
      %Shared.Maybe.some_inj(
        Replicas.Act,
        Replicas.Act.Opens{b, Vend.Branch.tip(t, Vend.Source.root(s)), []},
        a,
        %ep: {
          Shared.Bool.when(
            Maybe<&2, Replicas.Act>,
            _,
            u => Some{Replicas.Act.Opens{b, Vend.Branch.tip(t, Vend.Source.root(s)), []}},
            u => None{}
          )
            == Some{a}: Maybe<&2, Replicas.Act>
        }
        ec
      ): Acts.Kept(~d, lf, _)
      (ep, {==})
    case False{}:
      Empty.absurd(
        Acts.Kept(~d, lf, a),
        Shared.Maybe.none_ne_some(
          Replicas.Act,
          a,
          %ep: {
            Shared.Bool.when(
              Maybe<&2, Replicas.Act>,
              _,
              u => Some{Replicas.Act.Opens{b, Vend.Branch.tip(t, Vend.Source.root(s)), []}},
              u => None{}
            )
              == Some{a}: Maybe<&2, Replicas.Act>
          }
          ec
        )
      )

# a new branch gives a first tip of a kept tree
def Branch.act_kept(
  ~d: Vend.Led(),
  +lf: Vend.L(d),
  +t: Replicas.Tip,
  +b: String,
  m: Maybe<&2, Requests.Source>,
  +a: Replicas.Act,
  ec: {Vend.Branch.act(~d, lf, t, b, m) == Some{a}: Maybe<&2, Replicas.Act>}
) -> Acts.Kept(~d, lf, a):
  match m:
    case None{}:
      %Shared.Maybe.some_inj(Replicas.Act, Replicas.Act.Opens{b, Vend.Branch.tip(t, None{}), []}, a, ec): Acts.Kept(~d, lf, _)
      (Kept.empty(~d, lf), {==})
    case Some{+s}:
      Branch.act_kept.at(~d, lf, Vend.Tree.kept(~d, lf, Vend.Source.root(s)), t, b, s, a, {==}, ec)

# the first key of a node gives a kept tree
def Key.act_kept(
  ~d: Vend.Led(),
  +lf: Vend.L(d),
  +t: Replicas.Tip,
  +n: String,
  +k: Hashes.Hash,
  +a: Replicas.Act,
  hk: {Vend.Tree.kept(~d, lf, Replicas.Tip.content(t)) == True{}: Bool},
  ec: {Vend.Key.act(~d, lf, t, n, k) == Some{a}: Maybe<&2, Replicas.Act>},
  hh: {Replicas.Act.held(~Requests.Ask.machine(), ~d, lf, a) == True{}: Bool}
) -> Acts.Kept(~d, lf, a):
  Act.put_kept(
    ~d,
    lf,
    Replicas.Tip.content(t),
    Requests.Key.seal(n),
    Some{Hashes.Hash.code(k, [])},
    None{},
    [],
    a,
    hk,
    ec,
    hh,
    v => e => {==}
  )

# a resource that a kept tree reads is held, once the value that the read finds
# is known (v)
def Kept.res_find.at(
  ~d: Vend.Led(),
  +lf: Vend.L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +n: Resources.Name,
  +o: Maybe<&2, Requests.Res>,
  v: Maybe<&2, List<&2, U32>>,
  ev: {Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, h, Vend.Key.res(n)) == Some{v}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
  eo: {Vend.Res.found(v) == o: Maybe<&2, Requests.Res>},
  ls: Kept.Listed(~d, lf, h)
) -> {Vend.Res.kept(~d, lf, o) == True{}: Bool}:
  match v:
    case None{}:
      %eo: {Vend.Res.kept(~d, lf, _) == True{}: Bool}
      {==}
    case Some{+ws}:
      (+bs, r1) = ls
      (+e1, +ha) = r1
      %eo: {Vend.Res.kept(~d, lf, _) == True{}: Bool}
      Kept.of_all(~d, lf, bs, Trees.Binding{Vend.Key.res(n), ws}, ha)(
        Kept.of_range(
          ~d,
          lf,
          h,
          bs,
          e1,
          Vend.Key.res(n),
          ws,
          Merges.Merge.value_known(Replicas.Tree.look(~Requests.Ask.machine(), ~d, lf, h, Vend.Key.res(n)), Some{ws}, ev)
        )
      )

# a resource that a kept tree reads is held, once the read is known to find a
# value that holds it (fo) and the tree is listed (ls)
def Kept.res_find.found(
  ~d: Vend.Led(),
  +lf: Vend.L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +n: Resources.Name,
  +o: Maybe<&2, Requests.Res>,
  ls: Kept.Listed(~d, lf, h),
  fo: Merges.Merge.Found(~d, lf, h, n, o)
) -> {Vend.Res.kept(~d, lf, o) == True{}: Bool}:
  (+v, r) = fo
  (+ev, +eo) = r
  Kept.res_find.at(~d, lf, h, n, o, v, ev, eo, ls)

# a resource that a kept tree reads is held
def Kept.res_find(
  ~d: Vend.Led(),
  +lf: Vend.L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +n: Resources.Name,
  +o: Maybe<&2, Requests.Res>,
  hk: {Vend.Tree.kept(~d, lf, h) == True{}: Bool},
  e: {Vend.Res.find(~d, lf, h, n) == Some{o}: Maybe<&2, Maybe<&2, Requests.Res>>}
) -> {Vend.Res.kept(~d, lf, o) == True{}: Bool}:
  Kept.res_find.found(~d, lf, h, n, o, Kept.split(~d, lf, h, hk), Merges.Merge.find_some(~d, lf, h, n, o, e))

# Work.set_kept, once the write of the key to the tree of the work is known (p)
def Work.set_kept.at(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +lw: Vend.L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +m: Maybe<&2, List<&2, U32>>,
  +W1: Merges.Work<Vend.L(d)>,
  p: Maybe<&2, Trees.Edit>,
  ep: {Replicas.Tree.put(~Requests.Ask.machine(), ~d, lw, h, k, m) == p: Maybe<&2, Trees.Edit>},
  wc: Merges.Merge.Puts(~d, l, lw, ns),
  hk: {Vend.Tree.kept(~d, l, h) == True{}: Bool},
  +e: {Merges.Work.put(~d, lw, ns, p) == Some{W1}: Maybe<&2, Merges.Work<Vend.L(d)>>},
  +hh: {Replicas.Ext.holds(~Requests.Ask.machine(), ~d, l, Merges.Merge.nodes(~d, W1)) == True{}: Bool},
  hm: @v: List<&2, U32> -> {m == Some{v}: Maybe<&2, List<&2, U32>>} -> {Vend.Res.held(~d, l, Trees.Binding{k, v}) == True{}: Bool}
) -> {Vend.Tree.kept(~d, l, Merges.Merge.root(~d, W1)) == True{}: Bool}:
  match p:
    case None{}:
      Empty.absurd({Vend.Tree.kept(~d, l, Merges.Merge.root(~d, W1)) == True{}: Bool}, Shared.Maybe.none_ne_some(Merges.Work<Vend.L(d)>, W1, e))
    case Some{+e0}:
      %Merges.Merge.put_root(~d, lw, ns, e0, W1, e): {Vend.Tree.kept(~d, l, _) == True{}: Bool}
      Kept.put(
        ~d,
        l,
        h,
        k,
        m,
        e0,
        hk,
        Replicas.Hist.put(
          ~Requests.Ask.machine(),
          ~d,
          lw,
          l,
          h,
          k,
          m,
          e0,
          %Equal.sym(Vend.L(d), lw, Replicas.Led.puts(~Requests.Ask.machine(), ~d, ns, l), wc): Replicas.Led.Grows(Requests.Ask.machine(), d, _, l)
          Replicas.Ext.puts_into(
            ~Requests.Ask.machine(),
            ~d,
            ns,
            l,
            l,
            Replicas.Hist.refl(~Requests.Ask.machine(), ~d, l),
            Replicas.Ext.holds_left(~Requests.Ask.machine(), ~d, l, ns, Trees.Edit.nodes(e0))(
              %Equal.sym(
                List<&2, List<&2, U32>>,
                List.append(&2, List<&2, U32>, ns, Trees.Edit.nodes(e0)),
                Merges.Merge.nodes(~d, W1),
                Equal.cong(
                  Merges.Work<Vend.L(d)>,
                  List<&2, List<&2, U32>>,
                  w => Merges.Merge.nodes(~d, w),
                  Merges.Work{
                    Replicas.Led.puts(~Requests.Ask.machine(), ~d, Trees.Edit.nodes(e0), lw),
                    Trees.Edit.root(e0),
                    List.append(&2, List<&2, U32>, ns, Trees.Edit.nodes(e0))
                  },
                  W1,
                  Merges.Merge.put_work(~d, lw, ns, e0, W1, e)
                )
              ): {Replicas.Ext.holds(~Requests.Ask.machine(), ~d, l, _) == True{}: Bool}
              hh
            )
          )
        )(ep),
        Replicas.Ext.holds_right(~Requests.Ask.machine(), ~d, l, ns, Trees.Edit.nodes(e0))(
          %Equal.sym(
            List<&2, List<&2, U32>>,
            List.append(&2, List<&2, U32>, ns, Trees.Edit.nodes(e0)),
            Merges.Merge.nodes(~d, W1),
            Equal.cong(
              Merges.Work<Vend.L(d)>,
              List<&2, List<&2, U32>>,
              w => Merges.Merge.nodes(~d, w),
              Merges.Work{
                Replicas.Led.puts(~Requests.Ask.machine(), ~d, Trees.Edit.nodes(e0), lw),
                Trees.Edit.root(e0),
                List.append(&2, List<&2, U32>, ns, Trees.Edit.nodes(e0))
              },
              W1,
              Merges.Merge.put_work(~d, lw, ns, e0, W1, e)
            )
          ): {Replicas.Ext.holds(~Requests.Ask.machine(), ~d, l, _) == True{}: Bool}
          hh
        ),
        hm
      )

# a work whose tree is kept, whose ledger is the ledger of its nodes, and whose
# nodes the ledger holds, after a write of a held value, has a kept tree
def Work.set_kept(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +lw: Vend.L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +m: Maybe<&2, List<&2, U32>>,
  +W1: Merges.Work<Vend.L(d)>,
  wc: Merges.Merge.Puts(~d, l, lw, ns),
  hk: {Vend.Tree.kept(~d, l, h) == True{}: Bool},
  e: {Merges.Work.set(~d, Merges.Work{lw, h, ns}, k, m) == Some{W1}: Maybe<&2, Merges.Work<Vend.L(d)>>},
  hh: {Replicas.Ext.holds(~Requests.Ask.machine(), ~d, l, Merges.Merge.nodes(~d, W1)) == True{}: Bool},
  hm: @v: List<&2, U32> -> {m == Some{v}: Maybe<&2, List<&2, U32>>} -> {Vend.Res.held(~d, l, Trees.Binding{k, v}) == True{}: Bool}
) -> {Vend.Tree.kept(~d, l, Merges.Merge.root(~d, W1)) == True{}: Bool}:
  Work.set_kept.at(~d, l, lw, h, ns, k, m, W1, Replicas.Tree.put(~Requests.Ask.machine(), ~d, lw, h, k, m), {==}, wc, hk, e, hh, hm)

# a property of what a bind gives, when the rest gives it for each value that
# the read gives
def Bind.holds(
  -A: Data,
  -B: Data,
  -P: B -> Type,
  m: Maybe<&2, A>,
  f: A -> Maybe<&2, B>,
  +y: B,
  hf: @x: A -> {m == Some{x}: Maybe<&2, A>} -> {f(x) == Some{y}: Maybe<&2, B>} -> P(y),
  e: {Maybe.bind(&2, A, B, m, f) == Some{y}: Maybe<&2, B>}
) -> P(y):
  match m:
    case None{}:
      Empty.absurd(P(y), Shared.Maybe.none_ne_some(B, y, e))
    case Some{+x}:
      hf(x)({==})(e)

# a property of what a test gives, when each branch gives it
def When.holds(
  -B: Data,
  -P: B -> Type,
  p: Bool,
  f: Unit -> Maybe<&2, B>,
  g: Unit -> Maybe<&2, B>,
  +y: B,
  hf: {f(Unit{}) == Some{y}: Maybe<&2, B>} -> P(y),
  hg: {g(Unit{}) == Some{y}: Maybe<&2, B>} -> P(y),
  e: {Shared.Bool.when(Maybe<&2, B>, p, f, g) == Some{y}: Maybe<&2, B>}
) -> P(y):
  match p:
    case True{}:
      hf(e)
    case False{}:
      hg(e)

# what a pick of a merge leaves the ledger to hold: the resource that it takes,
# or the format of the resource that it makes
def Pick.Held(~d: Vend.Led(), lf: Vend.L(d), p: Merges.Pick) -> Data:
  match p:
    case Merges.Pick.Take{x}:
      {Vend.Res.kept(~d, lf, x) == True{}: Bool}
    case Merges.Pick.Make{h, bytes}:
      {Maybe.is_some(&2, Formats.Format, Vend.Format.at(~d, lf, h)) == True{}: Bool}
    case Merges.Pick.Clash{}:
      Unit

# a pick that a merge of bytes in a format whose hash is h gives makes bytes in
# that format, or clashes
def Pick.Shape(h: Hashes.Hash, p: Merges.Pick) -> Data:
  match p:
    case Merges.Pick.Take{x}:
      Empty
    case Merges.Pick.Make{h2, bytes}:
      {h2 == h: Hashes.Hash}
    case Merges.Pick.Clash{}:
      Unit

# the pick of merged bytes makes bytes in the format, or clashes
def Pick.of_shape(+h: Hashes.Hash, m: Formats.Merged) -> Pick.Shape(h, Merges.Pick.of(h, m)):
  match m:
    case Formats.Merged.Clean{+x}:
      {==}
    case Formats.Merged.Clash{}:
      Unit{}

# the merge of two pointers makes bytes in the format, or clashes, once the
# newer of them is known (m)
def Pointer.merge_shape.at(
  +h: Hashes.Hash,
  m: Maybe<&2, Merges.Pointer>
) -> Pick.Shape(
  h,
  Maybe.default(
    &2,
    Merges.Pick,
    Maybe.bind(&2, Merges.Pointer, Merges.Pick, m, p => Some{Merges.Pick.Make{h, Merges.Pointer.bytes(p)}}),
    Merges.Pick.Clash{}
  )
):
  match m:
    case None{}:
      Unit{}
    case Some{+p}:
      {==}

# the merge of two pointers makes bytes in the format, or clashes
def Pointer.merge_shape(
  +h: Hashes.Hash,
  x: Maybe<&2, Merges.Pointer>,
  y: Maybe<&2, Merges.Pointer>
) -> Pick.Shape(h, Merges.Pointer.merge(h, x, y)):
  match x y:
    case Some{+px} Some{+py}:
      Pointer.merge_shape.at(h, Merges.Pointer.newer(px, py))
    case Some{px} None{}:
      Unit{}
    case None{} z:
      Unit{}

# the pick of a merge of bytes of one format other than a submodule makes bytes
# in the format whose hash is h, or clashes
def Pick.format_shape.g(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +h: Hashes.Hash,
  +g: Formats.Format,
  +b: Maybe<&2, Requests.Res>,
  +ob: Texts.Bytes(),
  +tb: Texts.Bytes(),
  +p: Merges.Pick,
  e: {
    Maybe.bind(
      &2,
      Texts.Bytes(),
      Merges.Pick,
      Merges.Res.text(~d, l, b),
      bb => Some{Merges.Pick.of(h, Formats.Format.merge(g, bb, ob, tb))}
    )
      == Some{p}: Maybe<&2, Merges.Pick>
  }
) -> Pick.Shape(h, p):
  Bind.holds(
    Texts.Bytes(),
    Merges.Pick,
    q => Pick.Shape(h, q),
    Merges.Res.text(~d, l, b),
    bb => Some{Merges.Pick.of(h, Formats.Format.merge(g, bb, ob, tb))},
    p,
    bb => eb => e2 =>
      %Shared.Maybe.some_inj(Merges.Pick, Merges.Pick.of(h, Formats.Format.merge(g, bb, ob, tb)), p, e2): Pick.Shape(h, _)
      Pick.of_shape(h, Formats.Format.merge(g, bb, ob, tb)),
    e
  )

# the pick of a merge of bytes of one format, in the format whose hash is h, and
# in the format f, makes bytes in the format, or clashes
def Pick.format_shape(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +h: Hashes.Hash,
  +f: Formats.Format,
  +b: Maybe<&2, Requests.Res>,
  +ob: Texts.Bytes(),
  +tb: Texts.Bytes(),
  +p: Merges.Pick,
  e: {Merges.Pick.format(~d, l, h, f, b, ob, tb) == Some{p}: Maybe<&2, Merges.Pick>}
) -> Pick.Shape(h, p):
  match f:
    case Formats.Format.Leaf{Formats.Leaf.Module{}}:
      %Shared.Maybe.some_inj(Merges.Pick, Merges.Pointer.merge(h, Merges.Pointer.read(ob), Merges.Pointer.read(tb)), p, e): Pick.Shape(h, _)
      Pointer.merge_shape(h, Merges.Pointer.read(ob), Merges.Pointer.read(tb))
    case Formats.Format.Leaf{Formats.Leaf.Lines{}}:
      Pick.format_shape.g(~d, l, h, Formats.Format.Leaf{Formats.Leaf.Lines{}}, b, ob, tb, p, e)
    case Formats.Format.Leaf{Formats.Leaf.Whole{}}:
      Pick.format_shape.g(~d, l, h, Formats.Format.Leaf{Formats.Leaf.Whole{}}, b, ob, tb, p, e)
    case Formats.Format.Embed{+fo, +op, +cl, +fi}:
      Pick.format_shape.g(~d, l, h, Formats.Format.Embed{fo, op, cl, fi}, b, ob, tb, p, e)
    case Formats.Format.Code{+fb, +ru, +im}:
      Pick.format_shape.g(~d, l, h, Formats.Format.Code{fb, ru, im}, b, ob, tb, p, e)

# the pick of a merge of both changes in the format f makes bytes in the format
# whose hash is h, or clashes
def Pick.in_shape(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +h: Hashes.Hash,
  +f: Formats.Format,
  +b: Maybe<&2, Requests.Res>,
  +o: Maybe<&2, Requests.Res>,
  +t: Maybe<&2, Requests.Res>,
  +p: Merges.Pick,
  e: {Merges.Pick.in(~d, l, h, f, b, o, t) == Some{p}: Maybe<&2, Merges.Pick>}
) -> Pick.Shape(h, p):
  Bind.holds(
    Texts.Bytes(),
    Merges.Pick,
    q => Pick.Shape(h, q),
    Merges.Res.text(~d, l, o),
    ob => Maybe.bind(&2, Texts.Bytes(), Merges.Pick, Merges.Res.text(~d, l, t), tb => Merges.Pick.format(~d, l, h, f, b, ob, tb)),
    p,
    +ob => eo => e1 => Bind.holds(
      Texts.Bytes(),
      Merges.Pick,
      q => Pick.Shape(h, q),
      Merges.Res.text(~d, l, t),
      tb => Merges.Pick.format(~d, l, h, f, b, ob, tb),
      p,
      +tb => et => e2 => Pick.format_shape(~d, l, h, f, b, ob, tb, p, e2),
      e1
    ),
    e
  )

# a pick that makes bytes in the format whose hash is h leaves the ledger to hold
# the format, once it holds it (ef)
def Pick.held_of_shape(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +h: Hashes.Hash,
  +f: Formats.Format,
  p: Merges.Pick,
  ef: {Vend.Format.at(~d, l, h) == Some{f}: Maybe<&2, Formats.Format>},
  sh: Pick.Shape(h, p)
) -> Pick.Held(~d, l, p):
  match p:
    case Merges.Pick.Take{x}:
      Empty.absurd(Pick.Held(~d, l, Merges.Pick.Take{x}), sh)
    case Merges.Pick.Make{+h2, +bytes}:
      %Equal.sym(Hashes.Hash, h2, h, sh): {Maybe.is_some(&2, Formats.Format, Vend.Format.at(~d, l, _)) == True{}: Bool}
      %Equal.sym(Maybe<&2, Formats.Format>, Vend.Format.at(~d, l, h), Some{f}, ef): {Maybe.is_some(&2, Formats.Format, _) == True{}: Bool}
      {==}
    case Merges.Pick.Clash{}:
      Unit{}

# the pick of a merge of both changes leaves the ledger to hold what it needs,
# once the format of the two is known (fm)
def Pick.both_held.fm(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +b: Maybe<&2, Requests.Res>,
  +o: Maybe<&2, Requests.Res>,
  +t: Maybe<&2, Requests.Res>,
  +p: Merges.Pick,
  fm: Maybe<&2, Hashes.Hash>,
  e: {
    Maybe.default(
      &2,
      Maybe<&2, Merges.Pick>,
      Maybe.bind(
        &2,
        Hashes.Hash,
        Maybe<&2, Merges.Pick>,
        fm,
        +h => Some{Maybe.bind(&2, Formats.Format, Merges.Pick, Vend.Format.at(~d, l, h), f => Merges.Pick.in(~d, l, h, f, b, o, t))}
      ),
      Some{Merges.Pick.Take{None{}}}
    )
      == Some{p}: Maybe<&2, Merges.Pick>
  }
) -> Pick.Held(~d, l, p):
  match fm:
    case None{}:
      %Shared.Maybe.some_inj(Merges.Pick, Merges.Pick.Take{None{}}, p, e): Pick.Held(~d, l, _)
      {==}
    case Some{+h}:
      Bind.holds(
        Formats.Format,
        Merges.Pick,
        q => Pick.Held(~d, l, q),
        Vend.Format.at(~d, l, h),
        f => Merges.Pick.in(~d, l, h, f, b, o, t),
        p,
        +f => ef => ei => Pick.held_of_shape(~d, l, h, f, p, ef, Pick.in_shape(~d, l, h, f, b, o, t, p, ei)),
        e
      )

# the pick of a merge of both changes leaves the ledger to hold what it needs
def Pick.both_held(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +b: Maybe<&2, Requests.Res>,
  +o: Maybe<&2, Requests.Res>,
  +t: Maybe<&2, Requests.Res>,
  +p: Merges.Pick,
  ho: {Vend.Res.kept(~d, l, o) == True{}: Bool},
  ht: {Vend.Res.kept(~d, l, t) == True{}: Bool},
  e: {Merges.Pick.both(~d, l, b, o, t) == Some{p}: Maybe<&2, Merges.Pick>}
) -> Pick.Held(~d, l, p):
  When.holds(
    Merges.Pick,
    q => Pick.Held(~d, l, q),
    Merges.Res.one_format(o, t),
    u => Maybe.default(
      &2,
      Maybe<&2, Merges.Pick>,
      Maybe.bind(
        &2,
        Hashes.Hash,
        Maybe<&2, Merges.Pick>,
        Merges.Res.format.of(o, t),
        +h => Some{Maybe.bind(&2, Formats.Format, Merges.Pick, Vend.Format.at(~d, l, h), f => Merges.Pick.in(~d, l, h, f, b, o, t))}
      ),
      Some{Merges.Pick.Take{None{}}}
    ),
    u => Some{Merges.Pick.Clash{}},
    p,
    e1 => Pick.both_held.fm(~d, l, b, o, t, p, Merges.Res.format.of(o, t), e1),
    e2 =>
      %Shared.Maybe.some_inj(Merges.Pick, Merges.Pick.Clash{}, p, e2): Pick.Held(~d, l, _)
      Unit{},
    e
  )

# the pick of a merge leaves the ledger to hold what it needs, once the side that
# it takes is known (s)
def Pick.merge_held.at(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +b: Maybe<&2, Requests.Res>,
  +o: Maybe<&2, Requests.Res>,
  +t: Maybe<&2, Requests.Res>,
  +p: Merges.Pick,
  s: Sides.Side,
  ho: {Vend.Res.kept(~d, l, o) == True{}: Bool},
  ht: {Vend.Res.kept(~d, l, t) == True{}: Bool},
  e: {Merges.Pick.side(~d, l, b, o, t, s) == Some{p}: Maybe<&2, Merges.Pick>}
) -> Pick.Held(~d, l, p):
  match s:
    case Sides.Side.Theirs{}:
      %Shared.Maybe.some_inj(Merges.Pick, Merges.Pick.Take{t}, p, e): Pick.Held(~d, l, _)
      ht
    case Sides.Side.Ours{}:
      %Shared.Maybe.some_inj(Merges.Pick, Merges.Pick.Take{o}, p, e): Pick.Held(~d, l, _)
      ho
    case Sides.Side.Both{}:
      Pick.both_held(~d, l, b, o, t, p, ho, ht, e)

# the pick of a merge leaves the ledger to hold what it needs, when it holds
# each side
def Pick.merge_held(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +b: Maybe<&2, Requests.Res>,
  +o: Maybe<&2, Requests.Res>,
  +t: Maybe<&2, Requests.Res>,
  +p: Merges.Pick,
  ho: {Vend.Res.kept(~d, l, o) == True{}: Bool},
  ht: {Vend.Res.kept(~d, l, t) == True{}: Bool},
  e: {Merges.Pick.merge(~d, l, b, o, t) == Some{p}: Maybe<&2, Merges.Pick>}
) -> Pick.Held(~d, l, p):
  Pick.merge_held.at(~d, l, b, o, t, p, Sides.Side.of(~Maybe<&2, Requests.Res>, ~Vend.Res.same, b, o, t), ho, ht, e)


# the bytes of a rope that the ledger holds can be read
def Rope.kept_bytes(
  ~d: Vend.Led(),
  +lf: Vend.L(d),
  +bytes: Texts.Bytes(),
  hh: {Replicas.Ext.holds(~Requests.Ask.machine(), ~d, lf, Ropes.Put.nodes(Ropes.Rope.of_bytes(bytes))) == True{}: Bool}
) -> {Maybe.is_some(&2, Texts.Bytes(), Vend.Root.bytes(~d, lf, Ropes.Put.root(Ropes.Rope.of_bytes(bytes)))) == True{}: Bool}:
  %Equal.sym(Maybe<&2, List<&2, U32>>, Ropes.Rope.read(Ledgers.Kind.L(Requests.Ask, Replicas.Led.kind((Requests.Ask, (Requests.Ask.code, Requests.Ask.code.read, x => r => Requests.Ask.code_read(x, r)), Requests.Ask.arrival, Requests.Ask.governs, Requests.Key.seal), d)), Replicas.Led.fetch((Requests.Ask, (Requests.Ask.code, Requests.Ask.code.read, x => r => Requests.Ask.code_read(x, r)), Requests.Ask.arrival, Requests.Ask.governs, Requests.Key.seal), d), lf, Ropes.Put.root(Ropes.Rope.put(Packs.Pack.pieces(Shared.List.cut.with(U32, U32, Ropes.Gear.step, Ropes.Gear.edge, bytes, 0))))), Some{List.concat(&2, U32, Packs.Pack.pieces(Shared.List.cut.with(U32, U32, Ropes.Gear.step, Ropes.Gear.edge, bytes, 0)))}, Ropes.Rope.read_put(~Ledgers.Kind.L(Requests.Ask, Replicas.Led.kind((Requests.Ask, (Requests.Ask.code, Requests.Ask.code.read, x => r => Requests.Ask.code_read(x, r)), Requests.Ask.arrival, Requests.Ask.governs, Requests.Key.seal), d)), ~Replicas.Led.fetch((Requests.Ask, (Requests.Ask.code, Requests.Ask.code.read, x => r => Requests.Ask.code_read(x, r)), Requests.Ask.arrival, Requests.Ask.governs, Requests.Key.seal), d), lf, Packs.Pack.pieces(Shared.List.cut.with(U32, U32, Ropes.Gear.step, Ropes.Gear.edge, bytes, 0)))(hh)) :
    {Maybe.is_some(&2, List<&2, U32>, Maybe.bind(&2, List<&2, U32>, List<&2, U32>, _, ws => Some{Packs.Pack.read(ws, Packs.At.Length{0n})})) == True{} : Bool}
  {==}

# the resource that a merge makes is held, once the ledger holds its format and
# the nodes of its bytes
def Res.kept_make(
  ~d: Vend.Led(),
  +lf: Vend.L(d),
  +h: Hashes.Hash,
  +bytes: Texts.Bytes(),
  hf: {Maybe.is_some(&2, Formats.Format, Vend.Format.at(~d, lf, h)) == True{}: Bool},
  hh: {Replicas.Ext.holds(~Requests.Ask.machine(), ~d, lf, Ropes.Put.nodes(Ropes.Rope.of_bytes(bytes))) == True{}: Bool}
) -> {Vend.Res.kept(~d, lf, Some{Requests.Res{h, Ropes.Put.root(Ropes.Rope.of_bytes(bytes))}}) == True{}: Bool}:
  Shared.List.all.if_both(
    Maybe.is_some(&2, Formats.Format, Vend.Format.at(~d, lf, h)),
    u => Maybe.is_some(&2, Texts.Bytes(), Vend.Root.bytes(~d, lf, Ropes.Put.root(Ropes.Rope.of_bytes(bytes))))
  )(hf)(Rope.kept_bytes(~d, lf, bytes, hh))

# a ledger that holds the nodes ns2 holds the nodes ns, when ns2 are the nodes
# ns and others
def Merge.holds_nodes(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +ns: List<&2, List<&2, U32>>,
  +N: List<&2, List<&2, U32>>,
  nd: Merges.Merge.Nodes(ns, N),
  hh: {Replicas.Ext.holds(~Requests.Ask.machine(), ~d, l, N) == True{}: Bool}
) -> {Replicas.Ext.holds(~Requests.Ask.machine(), ~d, l, ns) == True{}: Bool}:
  (+ex, pe) = nd
  Replicas.Ext.holds_left(~Requests.Ask.machine(), ~d, l, ns, ex)(
    %pe: {Replicas.Ext.holds(~Requests.Ask.machine(), ~d, l, _) == True{}: Bool}
    hh
  )

# the ledger holds the nodes of the work before a write, once the write of the
# key to its tree is known (p)
def Work.set_holds.at(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +lw: Vend.L(d),
  +ns: List<&2, List<&2, U32>>,
  +W1: Merges.Work<Vend.L(d)>,
  p: Maybe<&2, Trees.Edit>,
  e: {Merges.Work.put(~d, lw, ns, p) == Some{W1}: Maybe<&2, Merges.Work<Vend.L(d)>>},
  hh: {Replicas.Ext.holds(~Requests.Ask.machine(), ~d, l, Merges.Merge.nodes(~d, W1)) == True{}: Bool}
) -> {Replicas.Ext.holds(~Requests.Ask.machine(), ~d, l, ns) == True{}: Bool}:
  match p:
    case None{}:
      Empty.absurd(
        {Replicas.Ext.holds(~Requests.Ask.machine(), ~d, l, ns) == True{}: Bool},
        Shared.Maybe.none_ne_some(Merges.Work<Vend.L(d)>, W1, e)
      )
    case Some{+e0}:
      Replicas.Ext.holds_left(~Requests.Ask.machine(), ~d, l, ns, Trees.Edit.nodes(e0))(
        %Equal.sym(
          List<&2, List<&2, U32>>,
          List.append(&2, List<&2, U32>, ns, Trees.Edit.nodes(e0)),
          Merges.Merge.nodes(~d, W1),
          Equal.cong(
            Merges.Work<Vend.L(d)>,
            List<&2, List<&2, U32>>,
            w => Merges.Merge.nodes(~d, w),
            Merges.Work{
              Replicas.Led.puts(~Requests.Ask.machine(), ~d, Trees.Edit.nodes(e0), lw),
              Trees.Edit.root(e0),
              List.append(&2, List<&2, U32>, ns, Trees.Edit.nodes(e0))
            },
            W1,
            Merges.Merge.put_work(~d, lw, ns, e0, W1, e)
          )
        ): {Replicas.Ext.holds(~Requests.Ask.machine(), ~d, l, _) == True{}: Bool}
        hh
      )

# the ledger holds the nodes of the work before a write
def Work.set_holds(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +lw: Vend.L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +m: Maybe<&2, List<&2, U32>>,
  +W1: Merges.Work<Vend.L(d)>,
  e: {Merges.Work.set(~d, Merges.Work{lw, h, ns}, k, m) == Some{W1}: Maybe<&2, Merges.Work<Vend.L(d)>>},
  hh: {Replicas.Ext.holds(~Requests.Ask.machine(), ~d, l, Merges.Merge.nodes(~d, W1)) == True{}: Bool}
) -> {Replicas.Ext.holds(~Requests.Ask.machine(), ~d, l, ns) == True{}: Bool}:
  Work.set_holds.at(~d, l, lw, ns, W1, Replicas.Tree.put(~Requests.Ask.machine(), ~d, lw, h, k, m), e, hh)

# a pick that clashes, once the clashes that are open are read (mc), leaves the
# tree of the work kept
def Merge.pick_kept.clash(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +lc: Vend.L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +W1: Merges.Work<Vend.L(d)>,
  mc: Maybe<&2, List<&2, Resources.Name>>,
  e: {
    Maybe.bind(
      &2,
      List<&2, Resources.Name>,
      Merges.Work<Vend.L(d)>,
      mc,
      cs => Merges.Work.set(~d, Merges.Work{lc, hc, P}, Vend.Key.clashes(k), Vend.Clash.value(Vend.Clash.put(n, cs)))
    )
      == Some{W1}: Maybe<&2, Merges.Work<Vend.L(d)>>
  },
  wc: Merges.Merge.Puts(~d, l, lc, P),
  hk: {Vend.Tree.kept(~d, l, hc) == True{}: Bool},
  hh: {Replicas.Ext.holds(~Requests.Ask.machine(), ~d, l, Merges.Merge.nodes(~d, W1)) == True{}: Bool}
) -> {Vend.Tree.kept(~d, l, Merges.Merge.root(~d, W1)) == True{}: Bool}:
  match mc:
    case None{}:
      Empty.absurd({Vend.Tree.kept(~d, l, Merges.Merge.root(~d, W1)) == True{}: Bool}, Shared.Maybe.none_ne_some(Merges.Work<Vend.L(d)>, W1, e))
    case Some{+cs}:
      Work.set_kept(~d, l, lc, hc, P, Vend.Key.clashes(k), Vend.Clash.value(Vend.Clash.put(n, cs)), W1, wc, hk, e, hh, v => ev => {==})

# a pick of a merge leaves the tree of the work kept, when the ledger holds the
# nodes of the work and what the pick needs
def Merge.pick_kept(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +lc: Vend.L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  p: Merges.Pick,
  +W1: Merges.Work<Vend.L(d)>,
  +N: List<&2, List<&2, U32>>,
  +e1: {Merges.Merge.pick(~d, Merges.Work{lc, hc, P}, k, n, p) == Some{W1}: Maybe<&2, Merges.Work<Vend.L(d)>>},
  +wc: Merges.Merge.Puts(~d, l, lc, P),
  hk: {Vend.Tree.kept(~d, l, hc) == True{}: Bool},
  ph: Pick.Held(~d, l, p),
  +hh: {Replicas.Ext.holds(~Requests.Ask.machine(), ~d, l, N) == True{}: Bool},
  +nd: Merges.Merge.Nodes(Merges.Merge.nodes(~d, W1), N)
) -> {Vend.Tree.kept(~d, l, Merges.Merge.root(~d, W1)) == True{}: Bool}:
  match p:
    case Merges.Pick.Take{+x}:
      Work.set_kept(
        ~d,
        l,
        lc,
        hc,
        P,
        Vend.Key.res(n),
        Vend.Res.value(x),
        W1,
        wc,
        hk,
        e1,
        Merge.holds_nodes(~d, l, Merges.Merge.nodes(~d, W1), N, nd, hh),
        Res.held_res(~d, l, n, x, ph)
      )
    case Merges.Pick.Make{+h, +bytes}:
      Work.set_kept(
        ~d,
        l,
        Replicas.Led.puts(~Requests.Ask.machine(), ~d, Ropes.Put.nodes(Ropes.Rope.of_bytes(bytes)), lc),
        hc,
        List.append(&2, List<&2, U32>, P, Ropes.Put.nodes(Ropes.Rope.of_bytes(bytes))),
        Vend.Key.res(n),
        Vend.Res.value(Some{Requests.Res{h, Ropes.Put.root(Ropes.Rope.of_bytes(bytes))}}),
        W1,
        Merges.Merge.keep_puts(~d, l, lc, P, Ropes.Put.nodes(Ropes.Rope.of_bytes(bytes)), wc),
        hk,
        e1,
        Merge.holds_nodes(~d, l, Merges.Merge.nodes(~d, W1), N, nd, hh),
        Res.held_res(
          ~d,
          l,
          n,
          Some{Requests.Res{h, Ropes.Put.root(Ropes.Rope.of_bytes(bytes))}},
          Res.kept_make(
            ~d,
            l,
            h,
            bytes,
            ph,
            Replicas.Ext.holds_right(~Requests.Ask.machine(), ~d, l, P, Ropes.Put.nodes(Ropes.Rope.of_bytes(bytes)))(
              Work.set_holds(
                ~d,
                l,
                Replicas.Led.puts(~Requests.Ask.machine(), ~d, Ropes.Put.nodes(Ropes.Rope.of_bytes(bytes)), lc),
                hc,
                List.append(&2, List<&2, U32>, P, Ropes.Put.nodes(Ropes.Rope.of_bytes(bytes))),
                Vend.Key.res(n),
                Vend.Res.value(Some{Requests.Res{h, Ropes.Put.root(Ropes.Rope.of_bytes(bytes))}}),
                W1,
                e1,
                Merge.holds_nodes(~d, l, Merges.Merge.nodes(~d, W1), N, nd, hh)
              )
            )
          )
        )
      )
    case Merges.Pick.Clash{}:
      Merge.pick_kept.clash(
        ~d,
        l,
        lc,
        hc,
        P,
        k,
        n,
        W1,
        Vend.Clash.names(~d, lc, hc, k),
        e1,
        wc,
        hk,
        Merge.holds_nodes(~d, l, Merges.Merge.nodes(~d, W1), N, nd, hh)
      )

# a merge of a resource leaves the tree of the work kept, when the ledger holds
# the nodes of the work and the two trees that it merges
def Merge.one_kept.at(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +lc: Vend.L(d),
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  mb: Maybe<&2, Maybe<&2, Requests.Res>>,
  +W1: Merges.Work<Vend.L(d)>,
  rd: Merges.Merge.Read.b(~d, l, ho, ht, Merges.Work{lc, hc, P}, k, n, mb, W1),
  +N: List<&2, List<&2, U32>>,
  +wc: Merges.Merge.Puts(~d, l, lc, P),
  +hk: {Vend.Tree.kept(~d, l, hc) == True{}: Bool},
  hko: {Vend.Tree.kept(~d, l, ho) == True{}: Bool},
  hkt: {Vend.Tree.kept(~d, l, ht) == True{}: Bool},
  +hh: {Replicas.Ext.holds(~Requests.Ask.machine(), ~d, l, N) == True{}: Bool},
  +nd: Merges.Merge.Nodes(Merges.Merge.nodes(~d, W1), N)
) -> {Vend.Tree.kept(~d, l, Merges.Merge.root(~d, W1)) == True{}: Bool}:
  (+b, r1) = rd
  (eb, r2) = r1
  (+o, r3) = r2
  (+eo, r4) = r3
  (+t, r5) = r4
  (+et, r6) = r5
  (+p, r7) = r6
  (+ep, e) = r7
  Merge.pick_kept(
    ~d,
    l,
    lc,
    hc,
    P,
    k,
    n,
    p,
    W1,
    N,
    e,
    wc,
    hk,
    Pick.merge_held(~d, l, b, o, t, p, Kept.res_find(~d, l, ho, n, o, hko, eo), Kept.res_find(~d, l, ht, n, t, hkt, et), ep),
    hh,
    nd
  )

# the next merge of the work leaves its tree kept
def Merge.next_kept(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +lc: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +k: Ledgers.Id,
  mn: Maybe<&2, Resources.Name>,
  +W1: Merges.Work<Vend.L(d)>,
  +N: List<&2, List<&2, U32>>,
  +e: {Merges.Merge.next(~d, l, hb, ho, ht, k, Merges.Work{lc, hc, P}, mn) == Some{W1}: Maybe<&2, Merges.Work<Vend.L(d)>>},
  +wc: Merges.Merge.Puts(~d, l, lc, P),
  +hk: {Vend.Tree.kept(~d, l, hc) == True{}: Bool},
  hko: {Vend.Tree.kept(~d, l, ho) == True{}: Bool},
  hkt: {Vend.Tree.kept(~d, l, ht) == True{}: Bool},
  +hh: {Replicas.Ext.holds(~Requests.Ask.machine(), ~d, l, N) == True{}: Bool},
  +nd: Merges.Merge.Nodes(Merges.Merge.nodes(~d, W1), N)
) -> {Vend.Tree.kept(~d, l, Merges.Merge.root(~d, W1)) == True{}: Bool}:
  match mn:
    case None{}:
      %Shared.Maybe.some_inj(Merges.Work<Vend.L(d)>, Merges.Work{lc, hc, P}, W1, e): {Vend.Tree.kept(~d, l, Merges.Merge.root(~d, _)) == True{}: Bool}
      hk
    case Some{+n}:
      Merge.one_kept.at(
        ~d,
        l,
        lc,
        ho,
        ht,
        hc,
        P,
        k,
        n,
        Vend.Res.find(~d, l, hb, n),
        W1,
        Merges.Merge.read(~d, l, ho, ht, Merges.Work{lc, hc, P}, k, n, Vend.Res.find(~d, l, hb, n), W1, e),
        N,
        wc,
        hk,
        hko,
        hkt,
        hh,
        nd
      )

# the induction hypothesis of Merge.all_kept for the keys rest
def Merge.KeptIH(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  rest: List<&2, List<&2, U32>>,
  lf: Vend.L(d),
  hf: Maybe<&2, Hashes.Hash>,
  N: List<&2, List<&2, U32>>
) -> Type:
  @lc1: Vend.L(d) -> @hc1: Maybe<&2, Hashes.Hash> -> @P1: List<&2, List<&2, U32>> -> {
    Merges.Merge.all(~d, l, hb, ho, ht, k, rest, Some{Merges.Work{lc1, hc1, P1}}) == Some{Merges.Work{lf, hf, N}}: Maybe<&2, Merges.Work<Vend.L(d)>>
  } -> Merges.Merge.Puts(~d, l, lc1, P1) -> {Vend.Tree.kept(~d, l, hc1) == True{}: Bool} -> {Vend.Tree.kept(~d, l, hf) == True{}: Bool}

# Merge.all_kept for the keys x then rest, once the work W1 after the first step
# is known
def Merge.all_kept.con2(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +x: List<&2, U32>,
  +rest: List<&2, List<&2, U32>>,
  +lc: Vend.L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +lf: Vend.L(d),
  +hf: Maybe<&2, Hashes.Hash>,
  +N: List<&2, List<&2, U32>>,
  +wc: Merges.Merge.Puts(~d, l, lc, P),
  +hk: {Vend.Tree.kept(~d, l, hc) == True{}: Bool},
  +hko: {Vend.Tree.kept(~d, l, ho) == True{}: Bool},
  +hkt: {Vend.Tree.kept(~d, l, ht) == True{}: Bool},
  +hh: {Replicas.Ext.holds(~Requests.Ask.machine(), ~d, l, N) == True{}: Bool},
  W1: Merges.Work<Vend.L(d)>,
  +erest: {Merges.Merge.all(~d, l, hb, ho, ht, k, rest, Some{W1}) == Some{Merges.Work{lf, hf, N}}: Maybe<&2, Merges.Work<Vend.L(d)>>},
  +enext: {Merges.Merge.next(~d, l, hb, ho, ht, k, Merges.Work{lc, hc, P}, Merges.Res.name(x)) == Some{W1}: Maybe<&2, Merges.Work<Vend.L(d)>>},
  ih: Merge.KeptIH(~d, l, hb, ho, ht, k, rest, lf, hf, N)
) -> {Vend.Tree.kept(~d, l, hf) == True{}: Bool}:
  match W1:
    case Merges.Work{+lc1, +hc1, +P1}:
      ih(lc1)(hc1)(P1)(erest)(
        Merges.Merge.And.left(
          Merges.Merge.Puts(~d, l, lc1, P1),
          Merges.Merge.Nodes(P, P1),
          Merges.Merge.next_facts(~d, l, lc, hb, ho, ht, hc, P, k, Merges.Res.name(x), Merges.Work{lc1, hc1, P1}, enext, wc)
        )
      )(
        Merge.next_kept(
          ~d,
          l,
          lc,
          hb,
          ho,
          ht,
          hc,
          P,
          k,
          Merges.Res.name(x),
          Merges.Work{lc1, hc1, P1},
          N,
          enext,
          wc,
          hk,
          hko,
          hkt,
          hh,
          Merges.Merge.And.right(
            Merges.Merge.Puts(~d, l, lf, N),
            Merges.Merge.Nodes(P1, N),
            Merges.Merge.all_puts(
              ~d,
              l,
              hb,
              ho,
              ht,
              k,
              rest,
              lc1,
              hc1,
              P1,
              lf,
              hf,
              N,
              erest,
              Merges.Merge.And.left(
                Merges.Merge.Puts(~d, l, lc1, P1),
                Merges.Merge.Nodes(P, P1),
                Merges.Merge.next_facts(~d, l, lc, hb, ho, ht, hc, P, k, Merges.Res.name(x), Merges.Work{lc1, hc1, P1}, enext, wc)
              )
            )
          )
        )
      )

# Merge.all_kept for the keys x then rest, once the first step is known
def Merge.all_kept.con(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +x: List<&2, U32>,
  +rest: List<&2, List<&2, U32>>,
  +lc: Vend.L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +lf: Vend.L(d),
  +hf: Maybe<&2, Hashes.Hash>,
  +N: List<&2, List<&2, U32>>,
  +wc: Merges.Merge.Puts(~d, l, lc, P),
  +hk: {Vend.Tree.kept(~d, l, hc) == True{}: Bool},
  +hko: {Vend.Tree.kept(~d, l, ho) == True{}: Bool},
  +hkt: {Vend.Tree.kept(~d, l, ht) == True{}: Bool},
  +hh: {Replicas.Ext.holds(~Requests.Ask.machine(), ~d, l, N) == True{}: Bool},
  sg: Merges.Merge.Stepped(~d, l, hb, ho, ht, k, x, rest, Merges.Work{lc, hc, P}, Merges.Work{lf, hf, N}),
  ih: Merge.KeptIH(~d, l, hb, ho, ht, k, rest, lf, hf, N)
) -> {Vend.Tree.kept(~d, l, hf) == True{}: Bool}:
  (+W1, st) = sg
  (erest, enext) = st
  Merge.all_kept.con2(~d, l, hb, ho, ht, k, x, rest, lc, hc, P, lf, hf, N, wc, hk, hko, hkt, hh, W1, erest, enext, ih)

# a merge of keys leaves the tree of the work kept, when the ledger holds the
# nodes of the work and the two trees that it merges
def Merge.all_kept(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  xs: List<&2, List<&2, U32>>,
  +lc: Vend.L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +lf: Vend.L(d),
  +hf: Maybe<&2, Hashes.Hash>,
  +N: List<&2, List<&2, U32>>,
  +e: {Merges.Merge.all(~d, l, hb, ho, ht, k, xs, Some{Merges.Work{lc, hc, P}}) == Some{Merges.Work{lf, hf, N}}: Maybe<&2, Merges.Work<Vend.L(d)>>},
  +wc: Merges.Merge.Puts(~d, l, lc, P),
  +hk: {Vend.Tree.kept(~d, l, hc) == True{}: Bool},
  +hko: {Vend.Tree.kept(~d, l, ho) == True{}: Bool},
  +hkt: {Vend.Tree.kept(~d, l, ht) == True{}: Bool},
  +hh: {Replicas.Ext.holds(~Requests.Ask.machine(), ~d, l, N) == True{}: Bool}
) -> {Vend.Tree.kept(~d, l, hf) == True{}: Bool}:
  match xs:
    case Nil{}:
      %Merges.Merge.work_eq.root(~d, lc, hc, P, lf, hf, N, e): {Vend.Tree.kept(~d, l, _) == True{}: Bool}
      hk
    case Con{+x, +rest}:
      Merge.all_kept.con(
        ~d,
        l,
        hb,
        ho,
        ht,
        k,
        x,
        rest,
        lc,
        hc,
        P,
        lf,
        hf,
        N,
        wc,
        hk,
        hko,
        hkt,
        hh,
        Merges.Merge.all_step(~d, l, hb, ho, ht, k, x, rest, Merges.Work{lc, hc, P}, Merges.Work{lf, hf, N}, e),
        lc1 => hc1 => P1 => e1 => wc1 => hk1 => Merge.all_kept(~d, l, hb, ho, ht, k, rest, lc1, hc1, P1, lf, hf, N, e1, wc1, hk1, hko, hkt, hh)
      )

# a property of what a test that gives a maybe gives, when the branch gives it
def MWhen.holds(
  -B: Data,
  -P: B -> Type,
  p: Bool,
  f: Unit -> Maybe<&2, B>,
  +y: B,
  hf: {p == True{}: Bool} -> {f(Unit{}) == Some{y}: Maybe<&2, B>} -> P(y),
  e: {Shared.Maybe.when(B, p, f) == Some{y}: Maybe<&2, B>}
) -> P(y):
  match p:
    case True{}:
      hf({==})(e)
    case False{}:
      Empty.absurd(P(y), Shared.Maybe.none_ne_some(B, y, e))

# what the act of a work is
def Work.ActShape(vs: Maybe<&2, List<&2, String>>, a: Replicas.Act) -> Data:
  Sigma<&2, &2, Maybe<&2, Hashes.Hash>, h => Sigma<&2, &2, List<&2, List<&2, U32>>, ns => {a == Replicas.Act.Taken{vs, h, ns}: Replicas.Act}>>

# the act of a work is a taken act
def Work.act_shape(
  ~d: Vend.Led(),
  +vs: Maybe<&2, List<&2, String>>,
  m: Maybe<&2, Merges.Work<Vend.L(d)>>,
  +a: Replicas.Act,
  e: {Merges.Work.act(~d, vs, m) == Some{a}: Maybe<&2, Replicas.Act>}
) -> Work.ActShape(vs, a):
  match m:
    case None{}:
      Empty.absurd(Work.ActShape(vs, a), Shared.Maybe.none_ne_some(Replicas.Act, a, e))
    case Some{Merges.Work{+lw, +h, +ns}}:
      MWhen.holds(
        Replicas.Act,
        a2 => Work.ActShape(vs, a2),
        Depots.Depot.holds(~Vend.L(d), ~(s => x => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, x)), lw, ns),
        u => Some{Replicas.Act.Taken{vs, h, ns}},
        a,
        ph => ea => (h, (ns, Equal.sym(Replicas.Act, Replicas.Act.Taken{vs, h, ns}, a, Shared.Maybe.some_inj(Replicas.Act, Replicas.Act.Taken{vs, h, ns}, a, ea)))),
        e
      )

# what the act of a merge is
def Merge.ActShape(a: Replicas.Act) -> Data:
  Work.ActShape(None{}, a)

# the act of a merge is a taken act
def Merge.act_shape(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +t: Replicas.Tip,
  +k: Ledgers.Id,
  +from: Requests.Source,
  +base: Maybe<&2, Requests.Source>,
  +a: Replicas.Act,
  e: {Merges.Merge.act(~d, l, t, k, from, base) == Some{a}: Maybe<&2, Replicas.Act>}
) -> Merge.ActShape(a):
  When.holds(
    Replicas.Act,
    a2 => Merge.ActShape(a2),
    List.all.if(
      u => List.all.if(u2 => Vend.Tree.kept(~d, l, Replicas.Tip.content(t)), Vend.Tree.kept(~d, l, Merges.Base.tree(base))),
      Vend.Tree.kept(~d, l, Vend.Source.root(from))
    ),
    u => Merges.Work.act(
      ~d,
      None{},
      Merges.Merge.all(
        ~d,
        l,
        Merges.Base.tree(base),
        Replicas.Tip.content(t),
        Vend.Source.root(from),
        k,
        Maybe.default(
          &2,
          List<&2, List<&2, U32>>,
          Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, Replicas.Tip.content(t), Vend.Source.root(from)),
          []
        ),
        Some{Merges.Work{l, Replicas.Tip.content(t), []}}
      )
    ),
    u => None{},
    a,
    ef => Work.act_shape(
      ~d,
      None{},
      Merges.Merge.all(
        ~d,
        l,
        Merges.Base.tree(base),
        Replicas.Tip.content(t),
        Vend.Source.root(from),
        k,
        Maybe.default(
          &2,
          List<&2, List<&2, U32>>,
          Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, Replicas.Tip.content(t), Vend.Source.root(from)),
          []
        ),
        Some{Merges.Work{l, Replicas.Tip.content(t), []}}
      ),
      a,
      ef
    ),
    eg => Empty.absurd(Merge.ActShape(a), Shared.Maybe.none_ne_some(Replicas.Act, a, eg)),
    e
  )

# a merge whose work is known (W) gives a kept tree
def Merge.act_kept.work(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +h2: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>,
  +ks: List<&2, List<&2, U32>>,
  W: Merges.Work<Vend.L(d)>,
  +hh: {Replicas.Ext.holds(~Requests.Ask.machine(), ~d, l, ns) == True{}: Bool},
  +eall: {Merges.Merge.all(~d, l, hb, ho, ht, k, ks, Some{Merges.Work{l, ho, []}}) == Some{W}: Maybe<&2, Merges.Work<Vend.L(d)>>},
  +eroot: {Merges.Merge.root(~d, W) == h2: Maybe<&2, Hashes.Hash>},
  +enodes: {Merges.Merge.nodes(~d, W) == ns: List<&2, List<&2, U32>>},
  +hko: {Vend.Tree.kept(~d, l, ho) == True{}: Bool},
  +hkt: {Vend.Tree.kept(~d, l, ht) == True{}: Bool}
) -> {Vend.Tree.kept(~d, l, h2) == True{}: Bool}:
  match W:
    case Merges.Work{+lf, +hf, +N}:
      %eroot: {Vend.Tree.kept(~d, l, _) == True{}: Bool}
      Merge.all_kept(
        ~d,
        l,
        hb,
        ho,
        ht,
        k,
        ks,
        l,
        ho,
        [],
        lf,
        hf,
        N,
        eall,
        {==},
        hko,
        hko,
        hkt,
        %Equal.sym(List<&2, List<&2, U32>>, N, ns, enodes): {Replicas.Ext.holds(~Requests.Ask.machine(), ~d, l, _) == True{}: Bool}
        hh
      )

# a merge that gives an act, once what it has gone through (fs) and that it
# checked the three trees (ck) are known, gives a kept tree
def Merge.act_kept.go(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +h2: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>,
  hh: {Replicas.Ext.holds(~Requests.Ask.machine(), ~d, l, ns) == True{}: Bool},
  fs: Merges.Merge.Facts(~d, l, hb, ho, ht, k, h2, ns),
  +ck: Merges.Merge.And({Vend.Tree.kept(~d, l, ht) == True{}: Bool}, Merges.Merge.And({Vend.Tree.kept(~d, l, hb) == True{}: Bool}, {Vend.Tree.kept(~d, l, ho) == True{}: Bool}))
) -> {Vend.Tree.kept(~d, l, h2) == True{}: Bool}:
  (+ks, r1) = fs
  (+W, r2) = r1
  (+eall, r3) = r2
  (+eroot, r4) = r3
  (+enodes, r5) = r4
  (+ediff, held) = r5
  Merge.act_kept.work(
    ~d,
    l,
    hb,
    ho,
    ht,
    k,
    h2,
    ns,
    ks,
    W,
    hh,
    eall,
    eroot,
    enodes,
    Merges.Merge.And.right(
      {Vend.Tree.kept(~d, l, hb) == True{}: Bool},
      {Vend.Tree.kept(~d, l, ho) == True{}: Bool},
      Merges.Merge.And.right(
        {Vend.Tree.kept(~d, l, ht) == True{}: Bool},
        Merges.Merge.And({Vend.Tree.kept(~d, l, hb) == True{}: Bool}, {Vend.Tree.kept(~d, l, ho) == True{}: Bool}),
        ck
      )
    ),
    Merges.Merge.And.left(
      {Vend.Tree.kept(~d, l, ht) == True{}: Bool},
      Merges.Merge.And({Vend.Tree.kept(~d, l, hb) == True{}: Bool}, {Vend.Tree.kept(~d, l, ho) == True{}: Bool}),
      ck
    )
  )

# a merge that gives a taken act gives a kept tree, when the ledger holds the
# nodes that the act adds
def Merge.act_kept(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +t: Replicas.Tip,
  +k: Ledgers.Id,
  +from: Requests.Source,
  +base: Maybe<&2, Requests.Source>,
  +vs: Maybe<&2, List<&2, String>>,
  +h2: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>,
  +e0: {Merges.Merge.act(~d, l, t, k, from, base) == Some{Replicas.Act.Taken{vs, h2, ns}}: Maybe<&2, Replicas.Act>},
  hh: {Replicas.Ext.holds(~Requests.Ask.machine(), ~d, l, ns) == True{}: Bool}
) -> {Vend.Tree.kept(~d, l, h2) == True{}: Bool}:
  Merge.act_kept.go(
    ~d,
    l,
    Merges.Base.tree(base),
    Replicas.Tip.content(t),
    Vend.Source.root(from),
    k,
    h2,
    ns,
    hh,
    Merges.Merge.facts_go(~d, l, t, k, from, base, vs, h2, ns, e0),
    Merges.Merge.guard3(
      Vend.Tree.kept(~d, l, Vend.Source.root(from)),
      Vend.Tree.kept(~d, l, Merges.Base.tree(base)),
      Vend.Tree.kept(~d, l, Replicas.Tip.content(t)),
      Merges.Merge.act_ok(
        ~d,
        l,
        k,
        Merges.Base.tree(base),
        Replicas.Tip.content(t),
        Vend.Source.root(from),
        Merges.Merge.ok(~d, l, Merges.Base.tree(base), Replicas.Tip.content(t), Vend.Source.root(from)),
        Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, Replicas.Tip.content(t), Vend.Source.root(from)),
        Replicas.Act.Taken{vs, h2, ns},
        Merges.Merge.act_go_of(~d, l, t, k, from, base, vs, h2, ns, e0)
      )
    )
  )

# a merge that gives an act, once the act is known to be a taken one (sh), gives
# the kept tree of its content
def Merge.act_kept_a.at(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +t: Replicas.Tip,
  +k: Ledgers.Id,
  +from: Requests.Source,
  +base: Maybe<&2, Requests.Source>,
  +a: Replicas.Act,
  +e: {Merges.Merge.act(~d, l, t, k, from, base) == Some{a}: Maybe<&2, Replicas.Act>},
  +hh: {Replicas.Act.held(~Requests.Ask.machine(), ~d, l, a) == True{}: Bool},
  sh: Merge.ActShape(a)
) -> Acts.Kept(~d, l, a):
  (+h2, r) = sh
  (+ns, +ea) = r
  %Equal.sym(Replicas.Act, a, Replicas.Act.Taken{None{}, h2, ns}, ea): Acts.Kept(~d, l, _)
  Merge.act_kept(
    ~d,
    l,
    t,
    k,
    from,
    base,
    None{},
    h2,
    ns,
    %ea: {Merges.Merge.act(~d, l, t, k, from, base) == Some{_}: Maybe<&2, Replicas.Act>}
    e,
    %ea: {Replicas.Act.held(~Requests.Ask.machine(), ~d, l, _) == True{}: Bool}
    hh
  )

# a merge that gives an act gives a kept tree, when the ledger holds the nodes
# that the act adds
def Merge.act_kept_a(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +t: Replicas.Tip,
  +k: Ledgers.Id,
  +from: Requests.Source,
  +base: Maybe<&2, Requests.Source>,
  +a: Replicas.Act,
  +e: {Merges.Merge.act(~d, l, t, k, from, base) == Some{a}: Maybe<&2, Replicas.Act>},
  +hh: {Replicas.Act.held(~Requests.Ask.machine(), ~d, l, a) == True{}: Bool}
) -> Acts.Kept(~d, l, a):
  Merge.act_kept_a.at(~d, l, t, k, from, base, a, e, hh, Merge.act_shape(~d, l, t, k, from, base, a, e))

# a property of what a test gives, when each branch gives it, and the branch
# that gives it tells what the test was
def When.holds2(
  -B: Data,
  -P: B -> Type,
  p: Bool,
  f: Unit -> Maybe<&2, B>,
  g: Unit -> Maybe<&2, B>,
  +y: B,
  hf: {p == True{}: Bool} -> {f(Unit{}) == Some{y}: Maybe<&2, B>} -> P(y),
  hg: {p == False{}: Bool} -> {g(Unit{}) == Some{y}: Maybe<&2, B>} -> P(y),
  e: {Shared.Bool.when(Maybe<&2, B>, p, f, g) == Some{y}: Maybe<&2, B>}
) -> P(y):
  match p:
    case True{}:
      hf({==})(e)
    case False{}:
      hg({==})(e)

# two writes to the tree of a work that the ledger holds whole, of held values,
# give a kept tree
def Resolve.two_kept(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +ho: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +new: Maybe<&2, Requests.Res>,
  +cs: List<&2, Resources.Name>,
  +W1: Merges.Work<Vend.L(d)>,
  +W2: Merges.Work<Vend.L(d)>,
  +hk: {Vend.Tree.kept(~d, l, ho) == True{}: Bool},
  +hn: {Vend.Res.kept(~d, l, new) == True{}: Bool},
  +e1: {Merges.Work.set(~d, Merges.Work{l, ho, []}, Vend.Key.res(n), Vend.Res.value(new)) == Some{W1}: Maybe<&2, Merges.Work<Vend.L(d)>>},
  +e2: {
    Merges.Work.set(~d, W1, Vend.Key.clashes(k), Vend.Clash.value(Shared.List.remove(~Resources.Name, ~Resources.Name.is_eq, cs, n))) == Some{W2}: Maybe<&2, Merges.Work<Vend.L(d)>>
  },
  +hh: {Replicas.Ext.holds(~Requests.Ask.machine(), ~d, l, Merges.Merge.nodes(~d, W2)) == True{}: Bool}
) -> {Vend.Tree.kept(~d, l, Merges.Merge.root(~d, W2)) == True{}: Bool}:
  match W1:
    case Merges.Work{+lw1, +h1, +ns1}:
      Work.set_kept(
        ~d,
        l,
        lw1,
        h1,
        ns1,
        Vend.Key.clashes(k),
        Vend.Clash.value(Shared.List.remove(~Resources.Name, ~Resources.Name.is_eq, cs, n)),
        W2,
        Merges.Merge.And.left(
          Merges.Merge.Puts(~d, l, Merges.Merge.ledger(~d, Merges.Work{lw1, h1, ns1}), Merges.Merge.nodes(~d, Merges.Work{lw1, h1, ns1})),
          Merges.Merge.Nodes([], Merges.Merge.nodes(~d, Merges.Work{lw1, h1, ns1})),
          Merges.Merge.set_facts(~d, l, l, ho, [], Vend.Key.res(n), Vend.Res.value(new), Merges.Work{lw1, h1, ns1}, e1, {==})
        ),
        Work.set_kept(
          ~d,
          l,
          l,
          ho,
          [],
          Vend.Key.res(n),
          Vend.Res.value(new),
          Merges.Work{lw1, h1, ns1},
          {==},
          hk,
          e1,
          Work.set_holds(
            ~d,
            l,
            lw1,
            h1,
            ns1,
            Vend.Key.clashes(k),
            Vend.Clash.value(Shared.List.remove(~Resources.Name, ~Resources.Name.is_eq, cs, n)),
            W2,
            e2,
            hh
          ),
          Res.held_res(~d, l, n, new, hn)
        ),
        e2,
        hh,
        v => ev => {==}
      )

# the work that a resolve of the resource n of the merge k, with the new
# resource new, takes at the tip t, when the clashes that are open are cs
def Resolve.work(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +t: Replicas.Tip,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +new: Maybe<&2, Requests.Res>,
  +cs: List<&2, Resources.Name>
) -> Maybe<&2, Merges.Work<Vend.L(d)>>:
  Maybe.bind(
    &2,
    Merges.Work<Vend.L(d)>,
    Merges.Work<Vend.L(d)>,
    Merges.Work.set(~d, Merges.Work{l, Replicas.Tip.content(t), []}, Vend.Key.res(n), Vend.Res.value(new)),
    w => Merges.Work.set(~d, w, Vend.Key.clashes(k), Vend.Clash.value(Shared.List.remove(~Resources.Name, ~Resources.Name.is_eq, cs, n)))
  )

# the work that a resolve takes gives a kept tree, once what it has gone through
# (ac) is known
def Resolve.work_kept.acted(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +t: Replicas.Tip,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +new: Maybe<&2, Requests.Res>,
  +cs: List<&2, Resources.Name>,
  +h2: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>,
  +hk: {Vend.Tree.kept(~d, l, Replicas.Tip.content(t)) == True{}: Bool},
  +hn: {Vend.Res.kept(~d, l, new) == True{}: Bool},
  +hh: {Replicas.Ext.holds(~Requests.Ask.machine(), ~d, l, ns) == True{}: Bool},
  ac: Merges.Merge.Acted(~d, Resolve.work(~d, l, t, k, n, new, cs), h2, ns)
) -> {Vend.Tree.kept(~d, l, h2) == True{}: Bool}:
  (+W2, r) = ac
  (+em, r2) = r
  (+eroot, r3) = r2
  (+enodes, held) = r3
  %eroot: {Vend.Tree.kept(~d, l, _) == True{}: Bool}
  Bind.holds(
    Merges.Work<Vend.L(d)>,
    Merges.Work<Vend.L(d)>,
    w => {Vend.Tree.kept(~d, l, Merges.Merge.root(~d, w)) == True{}: Bool},
    Merges.Work.set(~d, Merges.Work{l, Replicas.Tip.content(t), []}, Vend.Key.res(n), Vend.Res.value(new)),
    w => Merges.Work.set(~d, w, Vend.Key.clashes(k), Vend.Clash.value(Shared.List.remove(~Resources.Name, ~Resources.Name.is_eq, cs, n))),
    W2,
    W1 => em1 => e2 => Resolve.two_kept(
      ~d,
      l,
      Replicas.Tip.content(t),
      k,
      n,
      new,
      cs,
      W1,
      W2,
      hk,
      hn,
      em1,
      e2,
      %Equal.sym(List<&2, List<&2, U32>>, Merges.Merge.nodes(~d, W2), ns, enodes): {Replicas.Ext.holds(~Requests.Ask.machine(), ~d, l, _) == True{}: Bool}
      hh
    ),
    em
  )

# the act of the work that a resolve takes is a kept tree, once the act is known
# to be a taken one (sh)
def Resolve.work_kept.sh(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +t: Replicas.Tip,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +new: Maybe<&2, Requests.Res>,
  +cs: List<&2, Resources.Name>,
  +a: Replicas.Act,
  +hk: {Vend.Tree.kept(~d, l, Replicas.Tip.content(t)) == True{}: Bool},
  +hn: {Vend.Res.kept(~d, l, new) == True{}: Bool},
  +hh: {Replicas.Act.held(~Requests.Ask.machine(), ~d, l, a) == True{}: Bool},
  +e: {Merges.Work.act(~d, None{}, Resolve.work(~d, l, t, k, n, new, cs)) == Some{a}: Maybe<&2, Replicas.Act>},
  sh: Work.ActShape(None{}, a)
) -> Acts.Kept(~d, l, a):
  (+h2, r) = sh
  (+ns, +ea) = r
  %Equal.sym(Replicas.Act, a, Replicas.Act.Taken{None{}, h2, ns}, ea): Acts.Kept(~d, l, _)
  Resolve.work_kept.acted(
    ~d,
    l,
    t,
    k,
    n,
    new,
    cs,
    h2,
    ns,
    hk,
    hn,
    %ea: {Replicas.Act.held(~Requests.Ask.machine(), ~d, l, _) == True{}: Bool}
    hh,
    Merges.Merge.work_act(
      ~d,
      Resolve.work(~d, l, t, k, n, new, cs),
      None{},
      h2,
      ns,
      %ea: {Merges.Work.act(~d, None{}, Resolve.work(~d, l, t, k, n, new, cs)) == Some{_}: Maybe<&2, Replicas.Act>}
      e
    )
  )

# the act of the work that a resolve takes is a kept tree
def Resolve.work_kept(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +t: Replicas.Tip,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +new: Maybe<&2, Requests.Res>,
  +cs: List<&2, Resources.Name>,
  +a: Replicas.Act,
  hk: {Vend.Tree.kept(~d, l, Replicas.Tip.content(t)) == True{}: Bool},
  hn: {Vend.Res.kept(~d, l, new) == True{}: Bool},
  hh: {Replicas.Act.held(~Requests.Ask.machine(), ~d, l, a) == True{}: Bool},
  +e: {Merges.Work.act(~d, None{}, Resolve.work(~d, l, t, k, n, new, cs)) == Some{a}: Maybe<&2, Replicas.Act>}
) -> Acts.Kept(~d, l, a):
  Resolve.work_kept.sh(
    ~d,
    l,
    t,
    k,
    n,
    new,
    cs,
    a,
    hk,
    hn,
    hh,
    e,
    Work.act_shape(~d, None{}, Resolve.work(~d, l, t, k, n, new, cs), a, e)
  )

# a resolve gives a kept tree, once what it takes is known
def Resolve.act_of_kept(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +t: Replicas.Tip,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +new: Maybe<&2, Requests.Res>,
  +a: Replicas.Act,
  hk: {Vend.Tree.kept(~d, l, Replicas.Tip.content(t)) == True{}: Bool},
  e: {Merges.Resolve.act.of(~d, l, t, k, n, new) == Some{a}: Maybe<&2, Replicas.Act>},
  +hh: {Replicas.Act.held(~Requests.Ask.machine(), ~d, l, a) == True{}: Bool}
) -> Acts.Kept(~d, l, a):
  Bind.holds(
    List<&2, Resources.Name>,
    Replicas.Act,
    a2 => Acts.Kept(~d, l, a2),
    Vend.Clash.names(~d, l, Replicas.Tip.content(t), k),
    +cs => Shared.Bool.when(
      Maybe<&2, Replicas.Act>,
      List.contains(~Resources.Name, ~Resources.Name.is_eq, cs, n),
      u => Shared.Bool.when(
        Maybe<&2, Replicas.Act>,
        Vend.Res.kept(~d, l, new),
        v => Merges.Work.act(
          ~d,
          None{},
          Maybe.bind(
            &2,
            Merges.Work<Vend.L(d)>,
            Merges.Work<Vend.L(d)>,
            Merges.Work.set(~d, Merges.Work{l, Replicas.Tip.content(t), []}, Vend.Key.res(n), Vend.Res.value(new)),
            w => Merges.Work.set(
              ~d,
              w,
              Vend.Key.clashes(k),
              Vend.Clash.value(Shared.List.remove(~Resources.Name, ~Resources.Name.is_eq, cs, n))
            )
          )
        ),
        v => None{}
      ),
      u => Some{Replicas.Act.Stale{}}
    ),
    a,
    +cs => ec => e1 => When.holds(
      Replicas.Act,
      a2 => Acts.Kept(~d, l, a2),
      List.contains(~Resources.Name, ~Resources.Name.is_eq, cs, n),
      u => Shared.Bool.when(
        Maybe<&2, Replicas.Act>,
        Vend.Res.kept(~d, l, new),
        v => Merges.Work.act(
          ~d,
          None{},
          Maybe.bind(
            &2,
            Merges.Work<Vend.L(d)>,
            Merges.Work<Vend.L(d)>,
            Merges.Work.set(~d, Merges.Work{l, Replicas.Tip.content(t), []}, Vend.Key.res(n), Vend.Res.value(new)),
            w => Merges.Work.set(
              ~d,
              w,
              Vend.Key.clashes(k),
              Vend.Clash.value(Shared.List.remove(~Resources.Name, ~Resources.Name.is_eq, cs, n))
            )
          )
        ),
        v => None{}
      ),
      u => Some{Replicas.Act.Stale{}},
      a,
      e2 => When.holds2(
        Replicas.Act,
        a2 => Acts.Kept(~d, l, a2),
        Vend.Res.kept(~d, l, new),
        v => Merges.Work.act(
          ~d,
          None{},
          Maybe.bind(
            &2,
            Merges.Work<Vend.L(d)>,
            Merges.Work<Vend.L(d)>,
            Merges.Work.set(~d, Merges.Work{l, Replicas.Tip.content(t), []}, Vend.Key.res(n), Vend.Res.value(new)),
            w => Merges.Work.set(
              ~d,
              w,
              Vend.Key.clashes(k),
              Vend.Clash.value(Shared.List.remove(~Resources.Name, ~Resources.Name.is_eq, cs, n))
            )
          )
        ),
        v => None{},
        a,
        hn => e3 => Resolve.work_kept(~d, l, t, k, n, new, cs, a, hk, hn, hh, e3),
        hn => e3 => Empty.absurd(Acts.Kept(~d, l, a), Shared.Maybe.none_ne_some(Replicas.Act, a, e3)),
        e2
      ),
      e3 =>
        %Shared.Maybe.some_inj(Replicas.Act, Replicas.Act.Stale{}, a, e3): Acts.Kept(~d, l, _)
        Unit{},
      e1
    ),
    e
  )

# a resolve gives a kept tree
def Resolve.act_kept(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +t: Replicas.Tip,
  +k: Ledgers.Id,
  +n: Resources.Name,
  x: Requests.Content,
  +a: Replicas.Act,
  hk: {Vend.Tree.kept(~d, l, Replicas.Tip.content(t)) == True{}: Bool},
  e: {Merges.Resolve.act(~d, l, t, k, n, x) == Some{a}: Maybe<&2, Replicas.Act>},
  +hh: {Replicas.Act.held(~Requests.Ask.machine(), ~d, l, a) == True{}: Bool}
) -> Acts.Kept(~d, l, a):
  Bind.holds(
    Maybe<&2, Requests.Res>,
    Replicas.Act,
    a2 => Acts.Kept(~d, l, a2),
    Vend.Content.find(~d, l, t, n, x),
    new => Merges.Resolve.act.of(~d, l, t, k, n, new),
    a,
    new => en => e1 => Resolve.act_of_kept(~d, l, t, k, n, new, a, hk, e1, hh),
    e
  )
