import Base
import ./bools.bend as Bools
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

# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information
