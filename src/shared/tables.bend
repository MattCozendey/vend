import Base
import ./bools.bend as Bools
import ./maybes.bend as Maybes
import ./shared.bend as Shared
import ./strings.bend as Strings

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# Tables
# ------
# A table maps keys to values. It is a plain list of rows for now, with no
# key twice; a faster inside (Base's Map, say) may replace it later by
# proving the same three laws. No other spec may rely on anything else
# about a table.

# A table: rows of a key and its value.
type Table<-V: Data> is Data:
  TNil{}
  TRow{key: String, val: V, rest: Table<V>}
# a table with no rows
def Table.new(-V: Data) -> Table<V>:
  TNil{}
# the value of key k in t, or None
def Table.get(-V: Data, t: Table<V>, +k: String) -> Maybe<&2, V>:
  match t:
    case TNil{}:
      None{}
    case TRow{rk, v, r}:
      Bools.Bool.when(Maybe<&2, V>, String.eq(rk, k), u => Some{v}, u => Table.get(V, r, k))
# t without the row of key k
def Table.del(-V: Data, t: Table<V>, +k: String) -> Table<V>:
  match t:
    case TNil{}:
      TNil{}
    case TRow{+rk, v, +r}:
      Bools.Bool.when(
        Table<V>,
        String.eq(rk, k),
        u => Table.del(V, r, k),
        u => TRow{rk, v, Table.del(V, r, k)}
      )
# t with key k mapped to v
def Table.set(-V: Data, t: Table<V>, +k: String, v: V) -> Table<V>:
  TRow{k, v, Table.del(V, t, k)}
# the keys of t
def Table.keys(-V: Data, t: Table<V>) -> List<&2, String>:
  match t:
    case TNil{}:
      Nil{}
    case TRow{k, v, r}:
      k <> Table.keys(V, r)
# a new table has no value for any key
law Table.get_new:
  for -V: Data
  for k: String
  {Table.get(V, Table.new(V), k) == None{}: Maybe<&2, V>}

def Table.get_new(ty, k):
  {==}
# after setting k to v, k has v
law Table.get_after_set:
  for -V: Data
  for t: Table<V>
  for k: String
  for v: V
  {Table.get(V, Table.set(V, t, k, v), k) == Some{v}: Maybe<&2, V>}

def Table.get_after_set(ty, t, k, v):
  %Equal.sym(Bool, String.eq(k, k), True{}, Strings.String.eq_refl(k)):
    {
      Bools.Bool.when(
        Maybe<&2, ty>,
        _,
        u => Some{v},
        u => Table.get(ty, Table.del(ty, t, k), k)
      )
        == Some{v}: Maybe<&2, ty>
    }
  {==}
# deleting k, with b the answer of String.eq(rk, k) for the first row
def Table.get_del.at(
  -V: Data,
  rk: String,
  v: V,
  -r: Table<V>,
  k: String,
  k2: String,
  b: Bool,
  ih: {Table.get(V, Table.del(V, r, k), k2) == Table.get(V, r, k2): Maybe<&2, V>}
) -> {
  String.eq(rk, k) == b: Bool
} -> {
  String.eq(k, k2) == False{}: Bool
} -> {
  Table.get(
    V,
    Bools.Bool.when(Table<V>, b, u => Table.del(V, r, k), u => TRow{rk, v, Table.del(V, r, k)}),
    k2
  )
    == Table.get(V, TRow{rk, v, r}, k2): Maybe<&2, V>
}:
  match b:
    case True{}:
      e => d =>
        %Equal.sym(
          String,
          rk,
          k,
          Strings.String.eq_sound(rk, k)(e)
        ): {
          Table.get(
            V,
            Table.del(V, r, k),
            k2
          )
            == Bools.Bool.when(
              Maybe<&2, V>,
              String.eq(_, k2),
              u => Some{v},
              u => Table.get(V, r, k2)
            ): Maybe<&2, V>
        }
        %Equal.sym(
          Bool,
          String.eq(k, k2),
          False{},
          d
        ): {
          Table.get(
            V,
            Table.del(V, r, k),
            k2
          )
            == Bools.Bool.when(
              Maybe<&2, V>,
              _,
              u => Some{v},
              u => Table.get(V, r, k2)
            ): Maybe<&2, V>
        }
        ih
    case False{}:
      e => d =>
        %Equal.sym(Maybe<&2, V>, Table.get(V, Table.del(V, r, k), k2), Table.get(V, r, k2), ih):
          {
            Bools.Bool.when(
              Maybe<&2, V>,
              String.eq(rk, k2),
              u => Some{v},
              u => _
            )
              == Table.get(V, TRow{rk, v, r}, k2): Maybe<&2, V>
          }
        {==}
# deleting k keeps the value of every other key
def Table.get_del(
  -V: Data,
  t: Table<V>,
  +k: String,
  +k2: String
) -> {
  String.eq(k, k2) == False{}: Bool
} -> {Table.get(V, Table.del(V, t, k), k2) == Table.get(V, t, k2): Maybe<&2, V>}:
  match t:
    case TNil{}:
      _ => {==}
    case TRow{+rk, v, r}:
      +d => Table.get_del.at(
        V,
        rk,
        v,
        r,
        k,
        k2,
        String.eq(rk, k),
        Table.get_del(V, r, k, k2)(d)
      )({==}, d)
# setting k keeps the value of every other key
law Table.set_keeps_other:
  for -V: Data
  for t: Table<V>
  for k: String
  for v: V
  for k2: String
  for d: {String.eq(k, k2) == False{}: Bool}
  {Table.get(V, Table.set(V, t, k, v), k2) == Table.get(V, t, k2): Maybe<&2, V>}

def Table.set_keeps_other(ty, t, k, v, k2, d):
  +d = d
  %Equal.sym(Bool, String.eq(k, k2), False{}, d):
    {
      Bools.Bool.when(
        Maybe<&2, ty>,
        _,
        u => Some{v},
        u => Table.get(ty, Table.del(ty, t, k), k2)
      )
        == Table.get(ty, t, k2): Maybe<&2, ty>
    }
  Table.get_del(ty, t, k, k2)(d)
# Table.get_set, by the answer b of String.eq(k, c)
def Table.get_set.at(
  -V: Data,
  t: Table<V>,
  k: String,
  v: V,
  c: String,
  b: Bool
) -> {
  String.eq(k, c) == b: Bool
} -> {
  Bools.Bool.when(
    Maybe<&2, V>,
    String.eq(k, c),
    u => Some{v},
    u => Table.get(V, Table.del(V, t, k), c)
  )
    == Bools.Bool.when(
      Maybe<&2, V>,
      String.eq(k, c),
      u => Some{v},
      u => Table.get(V, t, c)
    ): Maybe<&2, V>
}:
  match b:
    case True{}:
      e =>
        %Equal.sym(Bool, String.eq(k, c), True{}, e):
          {
            Bools.Bool.when(
              Maybe<&2, V>,
              _,
              u => Some{v},
              u => Table.get(V, Table.del(V, t, k), c)
            )
              == Bools.Bool.when(
                Maybe<&2, V>,
                _,
                u => Some{v},
                u => Table.get(V, t, c)
              ): Maybe<&2, V>
          }
        {==}
    case False{}:
      +e =>
        %Equal.sym(Bool, String.eq(k, c), False{}, e):
          {
            Bools.Bool.when(
              Maybe<&2, V>,
              _,
              u => Some{v},
              u => Table.get(V, Table.del(V, t, k), c)
            )
              == Bools.Bool.when(
                Maybe<&2, V>,
                _,
                u => Some{v},
                u => Table.get(V, t, c)
              ): Maybe<&2, V>
          }
        Table.get_del(V, t, k, c)(e)

# after setting k to v, a key c has v when it is k, else what it had
def Table.get_set(
  -V: Data,
  t: Table<V>,
  +k: String,
  v: V,
  +c: String
) -> {
  Table.get(
    V,
    Table.set(V, t, k, v),
    c
  )
    == Bools.Bool.when(
      Maybe<&2, V>,
      String.eq(k, c),
      u => Some{v},
      u => Table.get(V, t, c)
    ): Maybe<&2, V>
}:
  Table.get_set.at(V, t, k, v, c, String.eq(k, c))({==})

# Table.keys_get at a row of key rk, by the answer b of String.eq(rk, k)
def Table.keys_get.at(
  -V: Data,
  rk: String,
  v: V,
  r: Table<V>,
  k: String,
  b: Bool,
  ih: {
    Shared.List.has(
      ~String,
      ~String.eq,
      Table.keys(V, r),
      k
    )
      == Maybe.is_some(&2, V, Table.get(V, r, k)): Bool
  }
) -> {
  String.eq(rk, k) == b: Bool
} -> {
  List.any.if(
    u => Shared.List.has(~String, ~String.eq, Table.keys(V, r), k),
    String.eq(rk, k)
  )
    == Maybe.is_some(
      &2,
      V,
      Bools.Bool.when(Maybe<&2, V>, String.eq(rk, k), u => Some{v}, u => Table.get(V, r, k))
    ): Bool
}:
  match b:
    case True{}:
      e =>
        %Equal.sym(Bool, String.eq(rk, k), True{}, e):
          {
            List.any.if(
              u => Shared.List.has(~String, ~String.eq, Table.keys(V, r), k),
              _
            )
              == Maybe.is_some(
                &2,
                V,
                Bools.Bool.when(Maybe<&2, V>, _, u => Some{v}, u => Table.get(V, r, k))
              ): Bool
          }
        {==}
    case False{}:
      e =>
        %Equal.sym(Bool, String.eq(rk, k), False{}, e):
          {
            List.any.if(
              u => Shared.List.has(~String, ~String.eq, Table.keys(V, r), k),
              _
            )
              == Maybe.is_some(
                &2,
                V,
                Bools.Bool.when(Maybe<&2, V>, _, u => Some{v}, u => Table.get(V, r, k))
              ): Bool
          }
        ih

# a key is among the keys of t exactly when t has a value for it
def Table.keys_get(
  -V: Data,
  t: Table<V>,
  +k: String
) -> {
  Shared.List.has(
    ~String,
    ~String.eq,
    Table.keys(V, t),
    k
  )
    == Maybe.is_some(&2, V, Table.get(V, t, k)): Bool
}:
  match t:
    case TNil{}:
      {==}
    case TRow{+rk, v, +r}:
      Table.keys_get.at(V, rk, v, r, k, String.eq(rk, k), Table.keys_get(V, r, k))({==})

# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# a key and its value
type Row<-V: Data> is Data:
  Row{key: String, val: V}

# the row of the key k, when m holds its value, then rest
def Table.rows.at(-V: Data, k: String, m: Maybe<&2, V>, rest: List<&2, Row<V>>) -> List<&2, Row<V>>:
  match m:
    case None{}:
      rest
    case Some{v}:
      Row{k, v} <> rest

# the rows of t under the keys ks, as lookups see them
def Table.rows(-V: Data, ks: List<&2, String>, +t: Table<V>) -> List<&2, Row<V>>:
  match ks:
    case Nil{}:
      Nil{}
    case Con{+k, r}:
      Table.rows.at(V, k, Table.get(V, t, k), Table.rows(V, r, t))

# the value of the first row of rs with the key k
def Table.find_row(-V: Data, rs: List<&2, Row<V>>, +k: String) -> Maybe<&2, V>:
  match rs:
    case Nil{}:
      None{}
    case Con{Row{rk, v}, r}:
      Bools.Bool.when(Maybe<&2, V>, String.eq(rk, k), u => Some{v}, u => Table.find_row(V, r, k))

# each key of ns has values that eq calls the same in a and b
def Table.agree(
  ~V: Data,
  ~eq: V -> V -> Bool,
  ns: List<&2, String>,
  +a: Table<V>,
  +b: Table<V>
) -> Bool:
  match ns:
    case Nil{}:
      True{}
    case Con{+n, r}:
      List.all.if(
        u => Table.agree(~V, ~eq, r, a, b),
        Maybes.Maybe.same(~V, ~eq, Table.get(V, a, n), Table.get(V, b, n))
      )

# a and b hold the same keys, with values that eq calls the same
def Table.same(~V: Data, ~eq: V -> V -> Bool, +a: Table<V>, +b: Table<V>) -> Bool:
  Table.agree(~V, ~eq, Strings.union(Table.keys(V, b), Table.keys(V, a)), a, b)

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run

# Table.agree_at at the first key m, by whether m is n (hit)
def Table.agree_at.at(
  ~V: Data,
  ~eq: V -> V -> Bool,
  +m: String,
  r: List<&2, String>,
  +a: Table<V>,
  +b: Table<V>,
  n: String,
  hit: Bool,
  ih: {
    Table.agree(~V, ~eq, r, a, b) == True{}: Bool
  } -> {
    Shared.List.has(~String, ~String.eq, r, n) == True{}: Bool
  } -> {Maybes.Maybe.same(~V, ~eq, Table.get(V, a, n), Table.get(V, b, n)) == True{}: Bool}
) -> {
  String.eq(m, n) == hit: Bool
} -> {
  List.all.if(
    u => Table.agree(~V, ~eq, r, a, b),
    Maybes.Maybe.same(~V, ~eq, Table.get(V, a, m), Table.get(V, b, m))
  )
    == True{}: Bool
} -> {
  List.any.if(u => Shared.List.has(~String, ~String.eq, r, n), hit) == True{}: Bool
} -> {Maybes.Maybe.same(~V, ~eq, Table.get(V, a, n), Table.get(V, b, n)) == True{}: Bool}:
  match hit:
    case False{}:
      e => +hg => hn => ih(
        Shared.List.all.if_rest(
          Maybes.Maybe.same(~V, ~eq, Table.get(V, a, m), Table.get(V, b, m)),
          u => Table.agree(~V, ~eq, r, a, b)
        )(hg)
      )(hn)
    case True{}:
      +e => +hg => hn =>
        %Strings.String.eq_sound(
          m,
          n
        )(e): {Maybes.Maybe.same(~V, ~eq, Table.get(V, a, _), Table.get(V, b, _)) == True{}: Bool}
        Shared.List.all.if_hit(
          Maybes.Maybe.same(~V, ~eq, Table.get(V, a, m), Table.get(V, b, m)),
          u => Table.agree(~V, ~eq, r, a, b)
        )(hg)

# when a and b agree on the keys ns, they agree on each key of ns
def Table.agree_at(
  ~V: Data,
  ~eq: V -> V -> Bool,
  ns: List<&2, String>,
  +a: Table<V>,
  +b: Table<V>,
  +n: String
) -> {
  Table.agree(~V, ~eq, ns, a, b) == True{}: Bool
} -> {
  Shared.List.has(~String, ~String.eq, ns, n) == True{}: Bool
} -> {Maybes.Maybe.same(~V, ~eq, Table.get(V, a, n), Table.get(V, b, n)) == True{}: Bool}:
  match ns:
    case Nil{}:
      hg => hn => Empty.absurd(
        {Maybes.Maybe.same(~V, ~eq, Table.get(V, a, n), Table.get(V, b, n)) == True{}: Bool},
        Shared.Bool.false_ne_true(hn)
      )
    case Con{+m, +r}:
      Table.agree_at.at(
        ~V,
        ~eq,
        m,
        r,
        a,
        b,
        n,
        String.eq(m, n),
        Table.agree_at(~V, ~eq, r, a, b, n)
      )({==})

# a lookup that is not some is none
def Table.none_of(
  -V: Data,
  m: Maybe<&2, V>
) -> {Maybe.is_some(&2, V, m) == False{}: Bool} -> {m == None{}: Maybe<&2, V>}:
  match m:
    case None{}:
      h => {==}
    case Some{x}:
      h => Empty.absurd(
        {Some{x} == None{}: Maybe<&2, V>},
        Shared.Bool.false_ne_true(Equal.sym(Bool, True{}, False{}, h))
      )

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# a key that a list misses is missing from a sublist of it: by whether the
# smaller list holds it (c)
def Table.absent.at(
  c: Bool,
  ks: List<&2, String>,
  u: List<&2, String>,
  n: String,
  sub: {
    Shared.List.has(~String, ~String.eq, ks, n) == True{}: Bool
  } -> {Shared.List.has(~String, ~String.eq, u, n) == True{}: Bool}
) -> {
  Shared.List.has(~String, ~String.eq, ks, n) == c: Bool
} -> {
  Shared.List.has(~String, ~String.eq, u, n) == False{}: Bool
} -> {Shared.List.has(~String, ~String.eq, ks, n) == False{}: Bool}:
  match c:
    case False{}:
      e => hu => e
    case True{}:
      e => hu =>
        Empty.absurd(
          {Shared.List.has(~String, ~String.eq, ks, n) == False{}: Bool},
          Shared.Bool.false_ne_true(
            Equal.trans(
              Bool,
              False{},
              Shared.List.has(~String, ~String.eq, u, n),
              True{},
              Equal.sym(Bool, Shared.List.has(~String, ~String.eq, u, n), False{}, hu),
              sub(e)
            )
          )
        )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# a key missing from u, a list that holds each key of t, has no value in t
def Table.missing(
  -V: Data,
  +t: Table<V>,
  u: List<&2, String>,
  +n: String,
  sub: {
    Shared.List.has(~String, ~String.eq, Table.keys(V, t), n) == True{}: Bool
  } -> {Shared.List.has(~String, ~String.eq, u, n) == True{}: Bool}
) -> {
  Shared.List.has(~String, ~String.eq, u, n) == False{}: Bool
} -> {Table.get(V, t, n) == None{}: Maybe<&2, V>}:
  hu =>
    Table.none_of(
      V,
      Table.get(V, t, n)
    )(
      Equal.trans(
        Bool,
        Maybe.is_some(&2, V, Table.get(V, t, n)),
        Shared.List.has(~String, ~String.eq, Table.keys(V, t), n),
        False{},
        Equal.sym(
          Bool,
          Shared.List.has(~String, ~String.eq, Table.keys(V, t), n),
          Maybe.is_some(&2, V, Table.get(V, t, n)),
          Table.keys_get(V, t, n)
        ),
        Table.absent.at(
          Shared.List.has(~String, ~String.eq, Table.keys(V, t), n),
          Table.keys(V, t),
          u,
          n,
          sub
        )({==})(hu)
      )
    )

# Table.same_sound at the key n, by whether the union of the keys holds n (c)
def Table.same_sound.at(
  ~V: Data,
  ~eq: V -> V -> Bool,
  eqs: @x: V -> @y: V -> {eq(x, y) == True{}: Bool} -> {x == y: V},
  +a: Table<V>,
  +b: Table<V>,
  +n: String,
  c: Bool
) -> {
  Shared.List.has(
    ~String,
    ~String.eq,
    Strings.union(Table.keys(V, b), Table.keys(V, a)),
    n
  )
    == c: Bool
} -> {
  Table.same(~V, ~eq, a, b) == True{}: Bool
} -> {Table.get(V, a, n) == Table.get(V, b, n): Maybe<&2, V>}:
  match c:
    case True{}:
      e => h => Maybes.Maybe.same_sound(
        ~V,
        ~eq,
        eqs,
        Table.get(V, a, n),
        Table.get(V, b, n)
      )(Table.agree_at(~V, ~eq, Strings.union(Table.keys(V, b), Table.keys(V, a)), a, b, n)(h)(e))
    case False{}:
      +e => h =>
        Equal.trans(
          Maybe<&2, V>,
          Table.get(V, a, n),
          None{},
          Table.get(V, b, n),
          Table.missing(
            V,
            a,
            Strings.union(Table.keys(V, b), Table.keys(V, a)),
            n,
            Strings.union_right(Table.keys(V, b), Table.keys(V, a), n)
          )(e),
          Equal.sym(
            Maybe<&2, V>,
            Table.get(V, b, n),
            None{},
            Table.missing(
              V,
              b,
              Strings.union(Table.keys(V, b), Table.keys(V, a)),
              n,
              Strings.union_left(Table.keys(V, b), Table.keys(V, a), n)
            )(e)
          )
        )

# tables that Table.same calls the same have the same value for every key,
# when eq is True only for equal values
def Table.same_sound(
  ~V: Data,
  ~eq: V -> V -> Bool,
  eqs: @x: V -> @y: V -> {eq(x, y) == True{}: Bool} -> {x == y: V},
  +a: Table<V>,
  +b: Table<V>,
  +n: String
) -> {
  Table.same(~V, ~eq, a, b) == True{}: Bool
} -> {Table.get(V, a, n) == Table.get(V, b, n): Maybe<&2, V>}:
  Table.same_sound.at(
    ~V,
    ~eq,
    eqs,
    a,
    b,
    n,
    Shared.List.has(~String, ~String.eq, Strings.union(Table.keys(V, b), Table.keys(V, a)), n)
  )({==})
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# a when on a value that both sides give is that value
def Table.when_same(
  -V: Data,
  b: Bool,
  m: Maybe<&2, V>
) -> {Bools.Bool.when(Maybe<&2, V>, b, u => m, u => m) == m: Maybe<&2, V>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# Table.rows_find at a key j that is not k: by the lookup g of j
def Table.rows_find.miss(
  -V: Data,
  j: String,
  t: Table<V>,
  r: List<&2, String>,
  k: String,
  g: Maybe<&2, V>
) -> {
  String.eq(j, k) == False{}: Bool
} -> {
  Table.find_row(
    V,
    Table.rows.at(V, j, g, Table.rows(V, r, t)),
    k
  )
    == Table.find_row(V, Table.rows(V, r, t), k): Maybe<&2, V>
}:
  match g:
    case None{}:
      e => {==}
    case Some{v}:
      e =>
        %Equal.sym(
          Bool,
          String.eq(j, k),
          False{},
          e
        ): {
          Bools.Bool.when(
            Maybe<&2, V>,
            _,
            u => Some{v},
            u => Table.find_row(V, Table.rows(V, r, t), k)
          )
            == Table.find_row(V, Table.rows(V, r, t), k): Maybe<&2, V>
        }
        {==}

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Table.rows_find at the key k itself: by the lookup g of k, which t gives
def Table.rows_find.hit(
  -V: Data,
  t: Table<V>,
  r: List<&2, String>,
  k: String,
  g: Maybe<&2, V>,
  ih: {
    Table.find_row(
      V,
      Table.rows(V, r, t),
      k
    )
      == Bools.Bool.when(
        Maybe<&2, V>,
        Shared.List.has(~String, ~String.eq, r, k),
        u => Table.get(V, t, k),
        u => None{}
      ): Maybe<&2, V>
  }
) -> {
  Table.get(V, t, k) == g: Maybe<&2, V>
} -> {
  Table.find_row(
    V,
    Table.rows.at(V, k, g, Table.rows(V, r, t)),
    k
  )
    == Table.get(V, t, k): Maybe<&2, V>
}:
  match g:
    case None{}:
      +e =>
        Equal.trans(
          Maybe<&2, V>,
          Table.find_row(V, Table.rows(V, r, t), k),
          Bools.Bool.when(
            Maybe<&2, V>,
            Shared.List.has(~String, ~String.eq, r, k),
            u => Table.get(V, t, k),
            u => None{}
          ),
          Table.get(V, t, k),
          ih,
          (
            %Equal.sym(Maybe<&2, V>, Table.get(V, t, k), None{}, e): {Bools.Bool.when(Maybe<&2, V>, Shared.List.has(~String, ~String.eq, r, k), u => _, u => None{}) == _: Maybe<&2, V>}
            Table.when_same(V, Shared.List.has(~String, ~String.eq, r, k), None{}))
        )
    case Some{v}:
      e =>
        %Equal.sym(
          Bool,
          String.eq(k, k),
          True{},
          Strings.String.eq_refl(k)
        ): {
          Bools.Bool.when(
            Maybe<&2, V>,
            _,
            u => Some{v},
            u => Table.find_row(V, Table.rows(V, r, t), k)
          )
            == Table.get(V, t, k): Maybe<&2, V>
        }
        Equal.sym(Maybe<&2, V>, Table.get(V, t, k), Some{v}, e)

# Table.rows_find at the first key j, by whether j is k (hit)
def Table.rows_find.at(
  -V: Data,
  +j: String,
  r: List<&2, String>,
  +t: Table<V>,
  +k: String,
  hit: Bool,
  ih: {
    Table.find_row(
      V,
      Table.rows(V, r, t),
      k
    )
      == Bools.Bool.when(
        Maybe<&2, V>,
        Shared.List.has(~String, ~String.eq, r, k),
        u => Table.get(V, t, k),
        u => None{}
      ): Maybe<&2, V>
  }
) -> {
  String.eq(j, k) == hit: Bool
} -> {
  Table.find_row(
    V,
    Table.rows.at(V, j, Table.get(V, t, j), Table.rows(V, r, t)),
    k
  )
    == Bools.Bool.when(
      Maybe<&2, V>,
      List.any.if(u => Shared.List.has(~String, ~String.eq, r, k), hit),
      u => Table.get(V, t, k),
      u => None{}
    ): Maybe<&2, V>
}:
  match hit:
    case False{}:
      e => Equal.trans(
        Maybe<&2, V>,
        Table.find_row(V, Table.rows.at(V, j, Table.get(V, t, j), Table.rows(V, r, t)), k),
        Table.find_row(V, Table.rows(V, r, t), k),
        Bools.Bool.when(
          Maybe<&2, V>,
          Shared.List.has(~String, ~String.eq, r, k),
          u => Table.get(V, t, k),
          u => None{}
        ),
        Table.rows_find.miss(V, j, t, r, k, Table.get(V, t, j))(e),
        ih
      )
    case True{}:
      +e =>
        %Equal.sym(
          String,
          j,
          k,
          Strings.String.eq_sound(j, k)(e)
        ): {
          Table.find_row(
            V,
            Table.rows.at(V, _, Table.get(V, t, _), Table.rows(V, r, t)),
            k
          )
            == Table.get(V, t, k): Maybe<&2, V>
        }
        Table.rows_find.hit(V, t, r, k, Table.get(V, t, k), ih)({==})
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# the first row of the keys ks with the key k has t's value, when ks holds k
def Table.rows_find(
  -V: Data,
  ks: List<&2, String>,
  +t: Table<V>,
  +k: String
) -> {
  Table.find_row(
    V,
    Table.rows(V, ks, t),
    k
  )
    == Bools.Bool.when(
      Maybe<&2, V>,
      Shared.List.has(~String, ~String.eq, ks, k),
      u => Table.get(V, t, k),
      u => None{}
    ): Maybe<&2, V>
}:
  match ks:
    case Nil{}:
      {==}
    case Con{+j, +r}:
      Table.rows_find.at(V, j, r, t, k, String.eq(j, k), Table.rows_find(V, r, t, k))({==})

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Table.rows_find over all keys of t, by the lookup g of k
def Table.rows_find_keys.of(
  -V: Data,
  t: Table<V>,
  k: String,
  g: Maybe<&2, V>
) -> {
  Table.get(V, t, k) == g: Maybe<&2, V>
} -> {
  Bools.Bool.when(
    Maybe<&2, V>,
    Shared.List.has(~String, ~String.eq, Table.keys(V, t), k),
    u => Table.get(V, t, k),
    u => None{}
  )
    == Table.get(V, t, k): Maybe<&2, V>
}:
  match g:
    case None{}:
      +e =>
        %Equal.sym(
          Bool,
          Shared.List.has(~String, ~String.eq, Table.keys(V, t), k),
          Maybe.is_some(&2, V, Table.get(V, t, k)),
          Table.keys_get(V, t, k)
        ): {
          Bools.Bool.when(
            Maybe<&2, V>,
            _,
            u => Table.get(V, t, k),
            u => None{}
          )
            == Table.get(V, t, k): Maybe<&2, V>
        }
        %Equal.sym(
          Maybe<&2, V>,
          Table.get(V, t, k),
          None{},
          e
        ): {
          Bools.Bool.when(
            Maybe<&2, V>,
            Maybe.is_some(&2, V, _),
            u => _,
            u => None{}
          )
            == _: Maybe<&2, V>
        }
        {==}
    case Some{v}:
      +e =>
        %Equal.sym(
          Bool,
          Shared.List.has(~String, ~String.eq, Table.keys(V, t), k),
          Maybe.is_some(&2, V, Table.get(V, t, k)),
          Table.keys_get(V, t, k)
        ): {
          Bools.Bool.when(
            Maybe<&2, V>,
            _,
            u => Table.get(V, t, k),
            u => None{}
          )
            == Table.get(V, t, k): Maybe<&2, V>
        }
        %Equal.sym(
          Maybe<&2, V>,
          Table.get(V, t, k),
          Some{v},
          e
        ): {
          Bools.Bool.when(
            Maybe<&2, V>,
            Maybe.is_some(&2, V, _),
            u => _,
            u => None{}
          )
            == _: Maybe<&2, V>
        }
        {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# the rows of all keys of t find what t gives
def Table.rows_find_keys(
  -V: Data,
  +t: Table<V>,
  +k: String
) -> {Table.find_row(V, Table.rows(V, Table.keys(V, t), t), k) == Table.get(V, t, k): Maybe<&2, V>}:
  Equal.trans(
    Maybe<&2, V>,
    Table.find_row(V, Table.rows(V, Table.keys(V, t), t), k),
    Bools.Bool.when(
      Maybe<&2, V>,
      Shared.List.has(~String, ~String.eq, Table.keys(V, t), k),
      u => Table.get(V, t, k),
      u => None{}
    ),
    Table.get(V, t, k),
    Table.rows_find(V, Table.keys(V, t), t, k),
    Table.rows_find_keys.of(V, t, k, Table.get(V, t, k))({==})
  )

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Table.differ, by whether a is b (hit)
def Table.differ.at(
  -V: Data,
  hit: Bool,
  t: Table<V>,
  a: String,
  b: String
) -> {
  String.eq(a, b) == hit: Bool
} -> {
  Maybe.is_some(&2, V, Table.get(V, t, a)) == False{}: Bool
} -> {Maybe.is_some(&2, V, Table.get(V, t, b)) == True{}: Bool} -> {hit == False{}: Bool}:
  match hit:
    case True{}:
      e => ha => hb =>
        Empty.absurd(
          {True{} == False{}: Bool},
          Shared.Bool.false_ne_true(
            Equal.trans(
              Bool,
              False{},
              Maybe.is_some(&2, V, Table.get(V, t, a)),
              True{},
              Equal.sym(Bool, Maybe.is_some(&2, V, Table.get(V, t, a)), False{}, ha),
              Equal.trans(
                Bool,
                Maybe.is_some(&2, V, Table.get(V, t, a)),
                Maybe.is_some(&2, V, Table.get(V, t, b)),
                True{},
                Equal.cong(
                  String,
                  Bool,
                  z => Maybe.is_some(&2, V, Table.get(V, t, z)),
                  a,
                  b,
                  Strings.String.eq_sound(a, b)(e)
                ),
                hb
              )
            )
          )
        )
    case False{}:
      e => ha => hb => {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# a key that t lacks is not a key that it holds
def Table.differ(
  -V: Data,
  t: Table<V>,
  +a: String,
  +b: String
) -> {
  Maybe.is_some(&2, V, Table.get(V, t, a)) == False{}: Bool
} -> {
  Maybe.is_some(&2, V, Table.get(V, t, b)) == True{}: Bool
} -> {String.eq(a, b) == False{}: Bool}:
  Table.differ.at(V, String.eq(a, b), t, a, b)({==})
