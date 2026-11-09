import Base
import ../../../shared.bend as Shared
import ./shared/trie.bend as Tries

# Cells
# -----
# A cell holds what every holder of a slot agrees on: one value, or many when
# two holders put different values in the same slot. Joining cells is a
# semilattice, so a trie of cells is one too (Trie.union_comm and the rest):
# holders that take in each other's cells end with the same ones, and a
# contradiction is kept, not settled by an arbitrary winner.

# one value, or the mark that two values met
type Cell<-V: Data> is Data:
  one{value: V}
  many{}

# what a and b agree on
def Cell.join(~V: Data, ~same: V -> V -> Bool, a: Cell<V>, b: Cell<V>) -> Cell<V>:
  match a b:
    case one{+x} one{y}:
      Bool.pick(Cell<V>, same(x, y), one{x}, many{})
    case one{x} many{}:
      many{}
    case many{} y:
      many{}

# the value of a cell, when every holder agrees on it
def Cell.value(-V: Data, m: Maybe<&2, Cell<V>>) -> Maybe<&2, V>:
  match m:
    case Some{one{e}}:
      Some{e}
    case _:
      None{}

# Laws
# ----
# Each law asks of same only its laws (Shared.Eq.Laws).

# a cell joined with itself is itself
law Cell.join_idem:
  for ~V: Data
  for ~same: V -> V -> Bool
  for ~laws: Shared.Eq.Laws(V, same)
  for a: Cell<V>
  {Cell.join(~V, ~same, a, a) == a: Cell<V>}

def Cell.join_idem(ty, same, laws, a):
  match a:
    case one{x}:
      %Equal.sym(
        Bool,
        same(x, x),
        True{},
        Shared.Eq.refl(~ty, ~same, laws, x)
      ): {Bool.pick(Cell<ty>, _, one{x}, many{}) == one{x}: Cell<ty>}
      {==}
    case many{}:
      {==}

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Cell.join_comm once same(y, x) is known (back)
def Cell.join_comm.back(
  ~V: Data,
  ~same: V -> V -> Bool,
  ~laws: Shared.Eq.Laws(V, same),
  back: Bool,
  +x: V,
  y: V,
  no: {same(x, y) == False{}: Bool},
  e: {same(y, x) == back: Bool}
) -> {many{} == Bool.pick(Cell<V>, back, one{y}, many{}): Cell<V>}:
  match back:
    case False{}:
      {==}
    case True{}:
      Empty.absurd(
        {many{} == one{y}: Cell<V>},
        Shared.Bool.false_ne_true(
          Equal.trans(
            Bool,
            False{},
            same(x, y),
            True{},
            Equal.sym(Bool, same(x, y), False{}, no),
            Equal.trans(
              Bool,
              same(x, y),
              same(x, x),
              True{},
              Equal.cong(V, Bool, z => same(x, z), y, x, Shared.Eq.sound(~V, ~same, laws, y)(x)(e)),
              Shared.Eq.refl(~V, ~same, laws, x)
            )
          )
        )
      )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# Cell.join_comm once same(x, y) is known (held)
def Cell.join_comm.at(
  ~V: Data,
  ~same: V -> V -> Bool,
  ~laws: Shared.Eq.Laws(V, same),
  held: Bool,
  +x: V,
  +y: V,
  e: {same(x, y) == held: Bool}
) -> {
  Bool.pick(
    Cell<V>,
    held,
    one{x},
    many{}
  )
    == Bool.pick(Cell<V>, same(y, x), one{y}, many{}): Cell<V>
}:
  match held:
    case True{}:
      %Shared.Eq.sound(
        ~V,
        ~same,
        laws,
        x
      )(y)(e): {one{x} == Bool.pick(Cell<V>, same(_, x), one{_}, many{}): Cell<V>}
      %Equal.sym(
        Bool,
        same(x, x),
        True{},
        Shared.Eq.refl(~V, ~same, laws, x)
      ): {one{x} == Bool.pick(Cell<V>, _, one{x}, many{}): Cell<V>}
      {==}
    case False{}:
      Cell.join_comm.back(~V, ~same, ~laws, same(y, x), x, y, e, {==})

# a join is the same either way round
law Cell.join_comm:
  for ~V: Data
  for ~same: V -> V -> Bool
  for ~laws: Shared.Eq.Laws(V, same)
  for a: Cell<V>
  for b: Cell<V>
  {Cell.join(~V, ~same, a, b) == Cell.join(~V, ~same, b, a): Cell<V>}

def Cell.join_comm(ty, same, laws, a, b):
  match a b:
    case one{+x} one{+y}:
      Cell.join_comm.at(~ty, ~same, ~laws, same(x, y), x, y, {==})
    case one{x} many{}:
      {==}
    case many{} one{y}:
      {==}
    case many{} many{}:
      {==}

# a cell that met many is many, whatever x and y were (held)
def Cell.join_assoc.many(
  ~V: Data,
  ~same: V -> V -> Bool,
  held: Bool,
  x: V
) -> {Cell.join(~V, ~same, Bool.pick(Cell<V>, held, one{x}, many{}), many{}) == many{}: Cell<V>}:
  match held:
    case True{}:
      {==}
    case False{}:
      {==}

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Cell.join_assoc for three values, once same(x, y) (xy) and same(y, z) (yz)
# are known
def Cell.join_assoc.at(
  ~V: Data,
  ~same: V -> V -> Bool,
  ~laws: Shared.Eq.Laws(V, same),
  xy: Bool,
  yz: Bool,
  x: V,
  y: V,
  z: V,
  e1: {same(x, y) == xy: Bool},
  e2: {same(y, z) == yz: Bool}
) -> {
  Cell.join(
    ~V,
    ~same,
    Bool.pick(Cell<V>, xy, one{x}, many{}),
    one{z}
  )
    == Cell.join(~V, ~same, one{x}, Bool.pick(Cell<V>, yz, one{y}, many{})): Cell<V>
}:
  match xy yz:
    case True{} True{}:
      %Shared.Eq.sound(~V, ~same, laws, y)(z)(e2):
        {
          Cell.join(
            ~V,
            ~same,
            Bool.pick(Cell<V>, True{}, one{x}, many{}),
            one{_}
          )
            == Cell.join(~V, ~same, one{x}, Bool.pick(Cell<V>, True{}, one{y}, many{})): Cell<V>
        }
      {==}
    case True{} False{}:
      %Equal.sym(V, x, y, Shared.Eq.sound(~V, ~same, laws, x)(y)(e1)):
        {
          Cell.join(
            ~V,
            ~same,
            Bool.pick(Cell<V>, True{}, one{_}, many{}),
            one{z}
          )
            == Cell.join(~V, ~same, one{_}, Bool.pick(Cell<V>, False{}, one{y}, many{})): Cell<V>
        }
      %Equal.sym(
        Bool,
        same(y, z),
        False{},
        e2
      ): {Bool.pick(Cell<V>, _, one{y}, many{}) == many{}: Cell<V>}
      {==}
    case False{} True{}:
      %Equal.sym(
        Bool,
        same(x, y),
        False{},
        e1
      ): {many{} == Bool.pick(Cell<V>, _, one{x}, many{}): Cell<V>}
      {==}
    case False{} False{}:
      {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# a join groups either way
law Cell.join_assoc:
  for ~V: Data
  for ~same: V -> V -> Bool
  for ~laws: Shared.Eq.Laws(V, same)
  for a: Cell<V>
  for b: Cell<V>
  for c: Cell<V>
  {
    Cell.join(
      ~V,
      ~same,
      Cell.join(~V, ~same, a, b),
      c
    )
      == Cell.join(~V, ~same, a, Cell.join(~V, ~same, b, c)): Cell<V>
  }

def Cell.join_assoc(ty, same, laws, a, b, c):
  match a b c:
    case many{} y w:
      {==}
    case one{x} many{} w:
      {==}
    case one{+x} one{+y} many{}:
      Cell.join_assoc.many(~ty, ~same, same(x, y), x)
    case one{+x} one{+y} one{+z}:
      Cell.join_assoc.at(~ty, ~same, ~laws, same(x, y), same(y, z), x, y, z, {==}, {==})

# a and b hold the same, as same calls values the same
def Cell.is_eq(~V: Data, ~same: V -> V -> Bool, a: Cell<V>, b: Cell<V>) -> Bool:
  match a b:
    case one{x} one{y}:
      same(x, y)
    case many{} many{}:
      True{}
    case _ _:
      False{}

# Cell.is_eq is True only for equal cells
law Cell.is_eq_sound:
  for ~V: Data
  for ~same: V -> V -> Bool
  for ~laws: Shared.Eq.Laws(V, same)
  for a: Cell<V>
  for b: Cell<V>
  {Cell.is_eq(~V, ~same, a, b) == True{}: Bool} -> {a == b: Cell<V>}

def Cell.is_eq_sound(ty, same, laws, a, b):
  match a b:
    case one{x} one{y}:
      h =>
        %Shared.Eq.sound(~ty, ~same, laws, x)(y)(h): {one{x} == one{_}: Cell<ty>}
        {==}
    case one{x} many{}:
      h => Empty.absurd({one{x} == many{}: Cell<ty>}, Shared.Bool.false_ne_true(h))
    case many{} one{y}:
      h => Empty.absurd({many{} == one{y}: Cell<ty>}, Shared.Bool.false_ne_true(h))
    case many{} many{}:
      h => {==}

# Agreement
# ---------
# t agrees with s when no cell of t contradicts a value that s holds: then a
# holder of s that takes in t keeps every value it held.

# b does not contradict the value that a holds
def Cell.agrees.here(
  ~V: Data,
  ~same: V -> V -> Bool,
  a: Maybe<&2, Cell<V>>,
  b: Maybe<&2, Cell<V>>
) -> Bool:
  match a b:
    case Some{one{x}} Some{one{y}}:
      same(x, y)
    case Some{one{x}} Some{many{}}:
      False{}
    case _ _:
      True{}

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- an equality, or a proof, keeps each and/or as one value for the proofs to split on
# no cell of t contradicts a value of s
def Cell.agrees(
  ~V: Data,
  ~same: V -> V -> Bool,
  s: Tries.Trie<Cell<V>>,
  t: Tries.Trie<Cell<V>>
) -> Bool:
  match s t:
    case Tries.tip{} y:
      True{}
    case Tries.bin{h, z, o} Tries.tip{}:
      True{}
    case Tries.bin{h1, z1, o1} Tries.bin{h2, z2, o2}:
      Bool.and(
        Cell.agrees.here(~V, ~same, h1, h2),
        Bool.and(Cell.agrees(~V, ~same, z1, z2), Cell.agrees(~V, ~same, o1, o2))
      )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# a cell that is here, whether one or not
def Cell.is_one(-V: Data, m: Maybe<&2, Cell<V>>) -> Bool:
  match m:
    case Some{one{x}}:
      True{}
    case _:
      False{}

# the value v that a holds is kept when b agrees with it
def Cell.kept.here(
  ~V: Data,
  ~same: V -> V -> Bool,
  ~laws: Shared.Eq.Laws(V, same),
  a: Maybe<&2, Cell<V>>,
  b: Maybe<&2, Cell<V>>,
  -v: V
) -> {
  Cell.agrees.here(~V, ~same, a, b) == True{}: Bool
} -> {
  a == Some{one{v}}: Maybe<&2, Cell<V>>
} -> {Tries.Trie.pick(~Cell<V>, ~Cell.join(~V, ~same), a, b) == Some{one{v}}: Maybe<&2, Cell<V>>}:
  match a b:
    case None{} y:
      h => g => Empty.absurd(
        {
          Tries.Trie.pick(
            ~Cell<V>,
            ~Cell.join(~V, ~same),
            None{},
            y
          )
            == Some{one{v}}: Maybe<&2, Cell<V>>
        },
        Shared.Bool.false_ne_true(
          Equal.cong(Maybe<&2, Cell<V>>, Bool, m => Cell.is_one(V, m), None{}, Some{one{v}}, g)
        )
      )
    case Some{many{}} y:
      h => g => Empty.absurd(
        {
          Tries.Trie.pick(
            ~Cell<V>,
            ~Cell.join(~V, ~same),
            Some{many{}},
            y
          )
            == Some{one{v}}: Maybe<&2, Cell<V>>
        },
        Shared.Bool.false_ne_true(
          Equal.cong(
            Maybe<&2, Cell<V>>,
            Bool,
            m => Cell.is_one(V, m),
            Some{many{}},
            Some{one{v}},
            g
          )
        )
      )
    case Some{one{x}} None{}:
      h => g => g
    case Some{one{+x}} Some{one{y}}:
      h => g =>
        %Equal.sym(
          Bool,
          same(x, y),
          True{},
          h
        ): {Some{Bool.pick(Cell<V>, _, one{x}, many{})} == Some{one{v}}: Maybe<&2, Cell<V>>}
        g
    case Some{one{x}} Some{many{}}:
      h => g => Empty.absurd(
        {Some{many{}} == Some{one{v}}: Maybe<&2, Cell<V>>},
        Shared.Bool.false_ne_true(h)
      )

# a value that s holds is kept in s and t, when t agrees with s
law Cell.agrees_kept:
  for ~V: Data
  for ~same: V -> V -> Bool
  for ~laws: Shared.Eq.Laws(V, same)
  for s: Tries.Trie<Cell<V>>
  for t: Tries.Trie<Cell<V>>
  for k: List<&2, Bool>
  for -v: V
  {Cell.agrees(~V, ~same, s, t) == True{}: Bool}
    -> {Tries.Trie.get(Cell<V>, s, k) == Some{one{v}}: Maybe<&2, Cell<V>>}
    -> {
      Tries.Trie.get(
        Cell<V>,
        Tries.Trie.union(~Cell<V>, ~Cell.join(~V, ~same), s, t),
        k
      )
        == Some{one{v}}: Maybe<&2, Cell<V>>
    }

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- an equality, or a proof, keeps each and/or as one value for the proofs to split on
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
def Cell.agrees_kept(ty, same, laws, s, t, k, v):
  match s t k:
    case Tries.tip{} y q:
      a => g => Empty.absurd(
        {Tries.Trie.get(Cell<ty>, y, q) == Some{one{v}}: Maybe<&2, Cell<ty>>},
        Shared.Bool.false_ne_true(
          Equal.cong(Maybe<&2, Cell<ty>>, Bool, m => Cell.is_one(ty, m), None{}, Some{one{v}}, g)
        )
      )
    case Tries.bin{h, z, o} Tries.tip{} q:
      a => g => g
    case Tries.bin{+h1, +z1, +o1} Tries.bin{+h2, +z2, +o2} Nil{}:
      +a => g => Cell.kept.here(
        ~ty,
        ~same,
        ~laws,
        h1,
        h2,
        v
      )(
        Shared.Bool.and_true_left(
          Cell.agrees.here(~ty, ~same, h1, h2),
          Bool.and(Cell.agrees(~ty, ~same, z1, z2), Cell.agrees(~ty, ~same, o1, o2))
        )(a)
      )(g)
    case Tries.bin{+h1, +z1, +o1} Tries.bin{+h2, +z2, +o2} Con{False{}, r}:
      +agrees1 = Cell.agrees(~ty, ~same, z1, z2)
      agrees2 = Cell.agrees(~ty, ~same, o1, o2)
      +a => g => Cell.agrees_kept(
        ~ty,
        ~same,
        ~laws,
        z1,
        z2,
        r,
        v
      )(
        Shared.Bool.and_true_left(
          agrees1,
          agrees2
        )(
          Shared.Bool.and_true_right(
            Cell.agrees.here(~ty, ~same, h1, h2),
            Bool.and(agrees1, agrees2)
          )(a)
        )
      )(g)
    case Tries.bin{+h1, +z1, +o1} Tries.bin{+h2, +z2, +o2} Con{True{}, r}:
      +agrees1 = Cell.agrees(~ty, ~same, z1, z2)
      +agrees2 = Cell.agrees(~ty, ~same, o1, o2)
      +a => g => Cell.agrees_kept(
        ~ty,
        ~same,
        ~laws,
        o1,
        o2,
        r,
        v
      )(
        Shared.Bool.and_true_right(
          agrees1,
          agrees2
        )(
          Shared.Bool.and_true_right(
            Cell.agrees.here(~ty, ~same, h1, h2),
            Bool.and(agrees1, agrees2)
          )(a)
        )
      )(g)
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# nothing contradicts a value of s
def Cell.agrees_tip(
  ~V: Data,
  ~same: V -> V -> Bool,
  s: Tries.Trie<Cell<V>>
) -> {Cell.agrees(~V, ~same, s, Tries.tip{}) == True{}: Bool}:
  match s:
    case Tries.tip{}:
      {==}
    case Tries.bin{h, z, o}:
      {==}

# nothing at a key does not contradict what a holds there
def Cell.agrees_none(
  ~V: Data,
  ~same: V -> V -> Bool,
  a: Maybe<&2, Cell<V>>
) -> {Cell.agrees.here(~V, ~same, a, None{}) == True{}: Bool}:
  match a:
    case None{}:
      {==}
    case Some{one{x}}:
      {==}
    case Some{many{}}:
      {==}

# one cell at a key that s does not hold agrees with s
law Cell.agrees_one:
  for ~V: Data
  for ~same: V -> V -> Bool
  for s: Tries.Trie<Cell<V>>
  for k: List<&2, Bool>
  for +x: Cell<V>
  {Tries.Trie.get(Cell<V>, s, k) == None{}: Maybe<&2, Cell<V>>}
    -> {Cell.agrees(~V, ~same, s, Tries.Trie.one(Cell<V>, k, x)) == True{}: Bool}

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
def Cell.agrees_one(ty, same, s, k, x):
  match s k:
    case Tries.tip{} q:
      g => {==}
    case Tries.bin{+h, +z, +o} Nil{}:
      g =>
        +agrees1 = Cell.agrees(~ty, ~same, z, Tries.tip{})
        +agrees2 = Cell.agrees(~ty, ~same, o, Tries.tip{})
        %Equal.sym(
          Maybe<&2, Cell<ty>>,
          h,
          None{},
          g
        ): {
          Bool.and(
            Cell.agrees.here(~ty, ~same, _, Some{x}),
            Bool.and(agrees1, agrees2)
          )
            == True{}: Bool
        }
        %Equal.sym(Bool, agrees1, True{}, Cell.agrees_tip(~ty, ~same, z)):
          {Bool.and(_, agrees2) == True{}: Bool}
        Cell.agrees_tip(~ty, ~same, o)
    case Tries.bin{+h, +z, +o} Con{False{}, +r}:
      +agrees1 = Cell.agrees(~ty, ~same, z, Tries.Trie.one(Cell<ty>, r, x))
      +agrees2 = Cell.agrees(~ty, ~same, o, Tries.tip{})
      g => Shared.Bool.and_both(
        Cell.agrees.here(~ty, ~same, h, None{}),
        Bool.and(agrees1, agrees2)
      )(
        Cell.agrees_none(~ty, ~same, h)
      )(
        Shared.Bool.and_both(
          agrees1,
          agrees2
        )(Cell.agrees_one(~ty, ~same, z, r, x)(g))(Cell.agrees_tip(~ty, ~same, o))
      )
    case Tries.bin{+h, +z, +o} Con{True{}, +r}:
      +agrees1 = Cell.agrees(~ty, ~same, o, Tries.Trie.one(Cell<ty>, r, x))
      +agrees2 = Cell.agrees(~ty, ~same, z, Tries.tip{})
      g => Shared.Bool.and_both(
        Cell.agrees.here(~ty, ~same, h, None{}),
        Bool.and(agrees2, agrees1)
      )(
        Cell.agrees_none(~ty, ~same, h)
      )(
        Shared.Bool.and_both(
          agrees2,
          agrees1
        )(Cell.agrees_tip(~ty, ~same, z))(Cell.agrees_one(~ty, ~same, o, r, x)(g))
      )
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# Cell.is_eq is True for a cell and itself
def Cell.is_eq_refl(
  ~V: Data,
  ~same: V -> V -> Bool,
  ~laws: Shared.Eq.Laws(V, same),
  a: Cell<V>
) -> {Cell.is_eq(~V, ~same, a, a) == True{}: Bool}:
  match a:
    case one{x}:
      Shared.Eq.refl(~V, ~same, laws, x)
    case many{}:
      {==}

# Syncs
# -----

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Cell.through once the cell m of k in s is known
def Cell.through.at(
  ~V: Data,
  ~W: Data,
  ~same: V -> V -> Bool,
  ~laws: Shared.Eq.Laws(V, same),
  f: Maybe<&2, V> -> Maybe<&2, W>,
  fnone: {f(None{}) == None{}: Maybe<&2, W>},
  s: Tries.Trie<Cell<V>>,
  t: Tries.Trie<Cell<V>>,
  k: List<&2, Bool>,
  -w: W,
  m: Maybe<&2, Cell<V>>,
  e: {Tries.Trie.get(Cell<V>, s, k) == m: Maybe<&2, Cell<V>>}
) -> {
  Cell.agrees(~V, ~same, s, t) == True{}: Bool
} -> {
  f(Cell.value(V, m)) == Some{w}: Maybe<&2, W>
} -> {
  f(
    Cell.value(
      V,
      Tries.Trie.get(Cell<V>, Tries.Trie.union(~Cell<V>, ~Cell.join(~V, ~same), s, t), k)
    )
  )
    == Some{w}: Maybe<&2, W>
}:
  match m:
    case None{}:
      ag => h => Empty.absurd(
        {
          f(
            Cell.value(
              V,
              Tries.Trie.get(Cell<V>, Tries.Trie.union(~Cell<V>, ~Cell.join(~V, ~same), s, t), k)
            )
          )
            == Some{w}: Maybe<&2, W>
        },
        Shared.Maybe.none_ne_some(
          W,
          w,
          Equal.trans(
            Maybe<&2, W>,
            None{},
            f(None{}),
            Some{w},
            Equal.sym(Maybe<&2, W>, f(None{}), None{}, fnone),
            h
          )
        )
      )
    case Some{many{}}:
      ag => h => Empty.absurd(
        {
          f(
            Cell.value(
              V,
              Tries.Trie.get(Cell<V>, Tries.Trie.union(~Cell<V>, ~Cell.join(~V, ~same), s, t), k)
            )
          )
            == Some{w}: Maybe<&2, W>
        },
        Shared.Maybe.none_ne_some(
          W,
          w,
          Equal.trans(
            Maybe<&2, W>,
            None{},
            f(None{}),
            Some{w},
            Equal.sym(Maybe<&2, W>, f(None{}), None{}, fnone),
            h
          )
        )
      )
    case Some{one{v}}:
      ag => h =>
        %Equal.sym(
          Maybe<&2, Cell<V>>,
          Tries.Trie.get(Cell<V>, Tries.Trie.union(~Cell<V>, ~Cell.join(~V, ~same), s, t), k),
          Some{one{v}},
          Cell.agrees_kept(~V, ~same, ~laws, s, t, k, v)(ag)(e)
        ): {f(Cell.value(V, _)) == Some{w}: Maybe<&2, W>}
        h
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# a value read through f (none from no value) of a cell of s stays in s and t,
# when t agrees with s
def Cell.through(
  ~V: Data,
  ~W: Data,
  ~same: V -> V -> Bool,
  ~laws: Shared.Eq.Laws(V, same),
  f: Maybe<&2, V> -> Maybe<&2, W>,
  fnone: {f(None{}) == None{}: Maybe<&2, W>},
  +s: Tries.Trie<Cell<V>>,
  t: Tries.Trie<Cell<V>>,
  +k: List<&2, Bool>,
  -w: W
) -> {
  Cell.agrees(~V, ~same, s, t) == True{}: Bool
} -> {
  f(Cell.value(V, Tries.Trie.get(Cell<V>, s, k))) == Some{w}: Maybe<&2, W>
} -> {
  f(
    Cell.value(
      V,
      Tries.Trie.get(Cell<V>, Tries.Trie.union(~Cell<V>, ~Cell.join(~V, ~same), s, t), k)
    )
  )
    == Some{w}: Maybe<&2, W>
}:
  Cell.through.at(~V, ~W, ~same, ~laws, f, fnone, s, t, k, w, Tries.Trie.get(Cell<V>, s, k), {==})

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# the entries at zero of tries that agree agree
def Cell.agrees_zero(
  ~V: Data,
  ~same: V -> V -> Bool,
  h1: Maybe<&2, Cell<V>>,
  h2: Maybe<&2, Cell<V>>,
  z1: Tries.Trie<Cell<V>>,
  z2: Tries.Trie<Cell<V>>,
  o1: Tries.Trie<Cell<V>>,
  o2: Tries.Trie<Cell<V>>
) -> {
  Cell.agrees(~V, ~same, Tries.bin{h1, z1, o1}, Tries.bin{h2, z2, o2}) == True{}: Bool
} -> {Cell.agrees(~V, ~same, z1, z2) == True{}: Bool}:
  +agrees1 = Cell.agrees(~V, ~same, z1, z2)
  agrees2 = Cell.agrees(~V, ~same, o1, o2)
  h => Shared.Bool.and_true_left(
    agrees1,
    agrees2
  )(Shared.Bool.and_true_right(Cell.agrees.here(~V, ~same, h1, h2), Bool.and(agrees1, agrees2))(h))
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# the entries at one of tries that agree agree
def Cell.agrees_one_side(
  ~V: Data,
  ~same: V -> V -> Bool,
  h1: Maybe<&2, Cell<V>>,
  h2: Maybe<&2, Cell<V>>,
  z1: Tries.Trie<Cell<V>>,
  z2: Tries.Trie<Cell<V>>,
  o1: Tries.Trie<Cell<V>>,
  o2: Tries.Trie<Cell<V>>
) -> {
  Cell.agrees(~V, ~same, Tries.bin{h1, z1, o1}, Tries.bin{h2, z2, o2}) == True{}: Bool
} -> {Cell.agrees(~V, ~same, o1, o2) == True{}: Bool}:
  +agrees1 = Cell.agrees(~V, ~same, z1, z2)
  +agrees2 = Cell.agrees(~V, ~same, o1, o2)
  h => Shared.Bool.and_true_right(
    agrees1,
    agrees2
  )(Shared.Bool.and_true_right(Cell.agrees.here(~V, ~same, h1, h2), Bool.and(agrees1, agrees2))(h))

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# the entries under p of tries that agree agree
def Cell.agrees_under(
  ~V: Data,
  ~same: V -> V -> Bool,
  s: Tries.Trie<Cell<V>>,
  t: Tries.Trie<Cell<V>>,
  p: List<&2, Bool>
) -> {
  Cell.agrees(~V, ~same, s, t) == True{}: Bool
} -> {
  Cell.agrees(
    ~V,
    ~same,
    Tries.Trie.under(Cell<V>, s, p),
    Tries.Trie.under(Cell<V>, t, p)
  )
    == True{}: Bool
}:
  match s t p:
    case Tries.tip{} y q:
      h => {==}
    case Tries.bin{h1, z1, o1} Tries.tip{} q:
      h => Cell.agrees_tip(~V, ~same, Tries.Trie.under(Cell<V>, Tries.bin{h1, z1, o1}, q))
    case Tries.bin{h1, z1, o1} Tries.bin{h2, z2, o2} Nil{}:
      h => h
    case Tries.bin{h1, +z1, +o1} Tries.bin{h2, +z2, +o2} Con{False{}, r}:
      h => Cell.agrees_under(
        ~V,
        ~same,
        z1,
        z2,
        r
      )(Cell.agrees_zero(~V, ~same, h1, h2, z1, z2, o1, o2)(h))
    case Tries.bin{h1, +z1, +o1} Tries.bin{h2, +z2, +o2} Con{True{}, r}:
      h => Cell.agrees_under(
        ~V,
        ~same,
        o1,
        o2,
        r
      )(Cell.agrees_one_side(~V, ~same, h1, h2, z1, z2, o1, o2)(h))
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# Growth
# ------
# A trie s2 grows from s when it keeps every cell of s: a value stays the
# value, many stays many, and only empty keys may fill. A sync that agrees
# grows a trie (Cell.grows_join), and growth composes (Cell.grows_trans).

# the cell b keeps what the cell a holds
def Cell.keeps(
  ~V: Data,
  ~same: V -> V -> Bool,
  a: Maybe<&2, Cell<V>>,
  b: Maybe<&2, Cell<V>>
) -> Bool:
  match a b:
    case None{} y:
      True{}
    case Some{one{x}} Some{one{y}}:
      same(x, y)
    case Some{many{}} Some{many{}}:
      True{}
    case Some{one{x}} Some{many{}}:
      False{}
    case Some{many{}} Some{one{y}}:
      False{}
    case Some{c} None{}:
      False{}

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- an equality, or a proof, keeps each and/or as one value for the proofs to split on
# the trie t holds no cell
def Cell.none(-V: Data, t: Tries.Trie<Cell<V>>) -> Bool:
  match t:
    case Tries.tip{}:
      True{}
    case Tries.bin{h, z, o}:
      Bool.and(Maybe.is_none(&2, Cell<V>, h), Bool.and(Cell.none(V, z), Cell.none(V, o)))

# every cell of s is kept in s2
def Cell.grows(
  ~V: Data,
  ~same: V -> V -> Bool,
  s: Tries.Trie<Cell<V>>,
  s2: Tries.Trie<Cell<V>>
) -> Bool:
  match s s2:
    case Tries.tip{} y:
      True{}
    case Tries.bin{h, z, o} Tries.tip{}:
      Bool.and(Maybe.is_none(&2, Cell<V>, h), Bool.and(Cell.none(V, z), Cell.none(V, o)))
    case Tries.bin{h1, z1, o1} Tries.bin{h2, z2, o2}:
      Bool.and(
        Cell.keeps(~V, ~same, h1, h2),
        Bool.and(Cell.grows(~V, ~same, z1, z2), Cell.grows(~V, ~same, o1, o2))
      )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof's statement, or code that the laws split on, keeps each and/or as one value
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# a trie that holds no cell has none at any key
def Cell.none_get(
  -V: Data,
  t: Tries.Trie<Cell<V>>,
  k: List<&2, Bool>
) -> {
  Cell.none(V, t) == True{}: Bool
} -> {Tries.Trie.get(Cell<V>, t, k) == None{}: Maybe<&2, Cell<V>>}:
  match t k:
    case Tries.tip{} r:
      h => {==}
    case Tries.bin{+h0, +z, +o} Nil{}:
      +h => Shared.Maybe.is_none_eq(
        Cell<V>,
        h0
      )(
        Shared.Bool.and_true_left(
          Maybe.is_none(&2, Cell<V>, h0),
          Bool.and(Cell.none(V, z), Cell.none(V, o))
        )(h)
      )
    case Tries.bin{h0, +z, +o} Con{False{}, r}:
      +h =>
        +rest = Shared.Bool.and_true_right(
          Maybe.is_none(&2, Cell<V>, h0),
          Bool.and(Cell.none(V, z), Cell.none(V, o))
        )(h)
        Cell.none_get(V, z, r)(Shared.Bool.and_true_left(Cell.none(V, z), Cell.none(V, o))(rest))
    case Tries.bin{h0, +z, +o} Con{True{}, r}:
      +h =>
        +rest = Shared.Bool.and_true_right(
          Maybe.is_none(&2, Cell<V>, h0),
          Bool.and(Cell.none(V, z), Cell.none(V, o))
        )(h)
        Cell.none_get(V, o, r)(Shared.Bool.and_true_right(Cell.none(V, z), Cell.none(V, o))(rest))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# every cell of s is kept in s2 at the key k
law Cell.grows_get:
  for ~V: Data
  for ~same: V -> V -> Bool
  for s: Tries.Trie<Cell<V>>
  for s2: Tries.Trie<Cell<V>>
  for k: List<&2, Bool>
  {Cell.grows(~V, ~same, s, s2) == True{}: Bool}
    -> {
      Cell.keeps(
        ~V,
        ~same,
        Tries.Trie.get(Cell<V>, s, k),
        Tries.Trie.get(Cell<V>, s2, k)
      )
        == True{}: Bool
    }

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof's statement, or code that the laws split on, keeps each and/or as one value
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
def Cell.grows_get(ty, same, s, s2, k):
  match s s2 k:
    case Tries.tip{} y q:
      h => {==}
    case Tries.bin{h1, z1, o1} Tries.tip{} q:
      h =>
        %Equal.sym(
          Maybe<&2, Cell<ty>>,
          Tries.Trie.get(Cell<ty>, Tries.bin{h1, z1, o1}, q),
          None{},
          Cell.none_get(ty, Tries.bin{h1, z1, o1}, q)(h)
        ): {Cell.keeps(~ty, ~same, _, Tries.Trie.get(Cell<ty>, Tries.tip{}, q)) == True{}: Bool}
        {==}
    case Tries.bin{h1, +z1, +o1} Tries.bin{h2, +z2, +o2} Nil{}:
      +h => Shared.Bool.and_true_left(
        Cell.keeps(~ty, ~same, h1, h2),
        Bool.and(Cell.grows(~ty, ~same, z1, z2), Cell.grows(~ty, ~same, o1, o2))
      )(h)
    case Tries.bin{h1, +z1, +o1} Tries.bin{h2, +z2, +o2} Con{False{}, r}:
      +h =>
        +rest = Shared.Bool.and_true_right(
          Cell.keeps(~ty, ~same, h1, h2),
          Bool.and(Cell.grows(~ty, ~same, z1, z2), Cell.grows(~ty, ~same, o1, o2))
        )(h)
        Cell.grows_get(
          ~ty,
          ~same,
          z1,
          z2,
          r
        )(
          Shared.Bool.and_true_left(
            Cell.grows(~ty, ~same, z1, z2),
            Cell.grows(~ty, ~same, o1, o2)
          )(rest)
        )
    case Tries.bin{h1, +z1, +o1} Tries.bin{h2, +z2, +o2} Con{True{}, r}:
      +h =>
        +rest = Shared.Bool.and_true_right(
          Cell.keeps(~ty, ~same, h1, h2),
          Bool.and(Cell.grows(~ty, ~same, z1, z2), Cell.grows(~ty, ~same, o1, o2))
        )(h)
        Cell.grows_get(
          ~ty,
          ~same,
          o1,
          o2,
          r
        )(
          Shared.Bool.and_true_right(
            Cell.grows(~ty, ~same, z1, z2),
            Cell.grows(~ty, ~same, o1, o2)
          )(rest)
        )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# a cell keeps itself
def Cell.keeps_refl(
  ~V: Data,
  ~same: V -> V -> Bool,
  ~laws: Shared.Eq.Laws(V, same),
  a: Maybe<&2, Cell<V>>
) -> {Cell.keeps(~V, ~same, a, a) == True{}: Bool}:
  match a:
    case None{}:
      {==}
    case Some{one{x}}:
      Shared.Eq.refl(~V, ~same, laws, x)
    case Some{many{}}:
      {==}

# keeping composes
def Cell.keeps_trans(
  ~V: Data,
  ~same: V -> V -> Bool,
  ~laws: Shared.Eq.Laws(V, same),
  a: Maybe<&2, Cell<V>>,
  b: Maybe<&2, Cell<V>>,
  c: Maybe<&2, Cell<V>>
) -> {
  Cell.keeps(~V, ~same, a, b) == True{}: Bool
} -> {Cell.keeps(~V, ~same, b, c) == True{}: Bool} -> {Cell.keeps(~V, ~same, a, c) == True{}: Bool}:
  match a b c:
    case None{} y w:
      h1 => h2 => {==}
    case Some{one{x}} Some{one{y}} Some{one{z}}:
      h1 => h2 =>
        %Equal.sym(
          V,
          x,
          y,
          Shared.Eq.sound(~V, ~same, laws, x, y)(h1)
        ): {same(_, z) == True{}: Bool}
        h2
    case Some{one{x}} Some{one{y}} Some{many{}}:
      h1 => h2 => h2
    case Some{one{x}} Some{one{y}} None{}:
      h1 => h2 => h2
    case Some{one{x}} Some{many{}} w:
      h1 => h2 => Empty.absurd(
        {Cell.keeps(~V, ~same, Some{one{x}}, w) == True{}: Bool},
        Shared.Bool.false_ne_true(h1)
      )
    case Some{one{x}} None{} w:
      h1 => h2 => Empty.absurd(
        {Cell.keeps(~V, ~same, Some{one{x}}, w) == True{}: Bool},
        Shared.Bool.false_ne_true(h1)
      )
    case Some{many{}} Some{many{}} w:
      h1 => h2 => h2
    case Some{many{}} Some{one{y}} w:
      h1 => h2 => Empty.absurd(
        {Cell.keeps(~V, ~same, Some{many{}}, w) == True{}: Bool},
        Shared.Bool.false_ne_true(h1)
      )
    case Some{many{}} None{} w:
      h1 => h2 => Empty.absurd(
        {Cell.keeps(~V, ~same, Some{many{}}, w) == True{}: Bool},
        Shared.Bool.false_ne_true(h1)
      )

# a cell that keeps the value x is x
def Cell.keeps_value(
  ~V: Data,
  ~same: V -> V -> Bool,
  ~laws: Shared.Eq.Laws(V, same),
  x: V,
  b: Maybe<&2, Cell<V>>
) -> {
  Cell.keeps(~V, ~same, Some{one{x}}, b) == True{}: Bool
} -> {b == Some{one{x}}: Maybe<&2, Cell<V>>}:
  match b:
    case Some{one{z}}:
      h =>
        %Equal.sym(
          V,
          x,
          z,
          Shared.Eq.sound(~V, ~same, laws, x, z)(h)
        ): {Some{one{z}} == Some{one{_}}: Maybe<&2, Cell<V>>}
        {==}
    case Some{many{}}:
      h => Empty.absurd(
        {Some{many{}} == Some{one{x}}: Maybe<&2, Cell<V>>},
        Shared.Bool.false_ne_true(h)
      )
    case None{}:
      h => Empty.absurd({None{} == Some{one{x}}: Maybe<&2, Cell<V>>}, Shared.Bool.false_ne_true(h))

# a value read through f (none from no value) stays where the cells grow
def Cell.read_grows(
  ~V: Data,
  ~W: Data,
  ~same: V -> V -> Bool,
  ~laws: Shared.Eq.Laws(V, same),
  f: Maybe<&2, V> -> Maybe<&2, W>,
  fnone: {f(None{}) == None{}: Maybe<&2, W>},
  a: Maybe<&2, Cell<V>>,
  b: Maybe<&2, Cell<V>>,
  -w: W
) -> {
  Cell.keeps(~V, ~same, a, b) == True{}: Bool
} -> {
  f(Cell.value(V, a)) == Some{w}: Maybe<&2, W>
} -> {f(Cell.value(V, b)) == Some{w}: Maybe<&2, W>}:
  match a:
    case Some{one{x}}:
      k => h =>
        %Equal.sym(
          Maybe<&2, Cell<V>>,
          b,
          Some{one{x}},
          Cell.keeps_value(~V, ~same, ~laws, x, b)(k)
        ):
          {f(Cell.value(V, _)) == Some{w}: Maybe<&2, W>}
        h
    case Some{many{}}:
      k => h => Empty.absurd(
        {f(Cell.value(V, b)) == Some{w}: Maybe<&2, W>},
        Shared.Maybe.none_ne_some(
          W,
          w,
          Equal.trans(
            Maybe<&2, W>,
            None{},
            f(None{}),
            Some{w},
            Equal.sym(Maybe<&2, W>, f(None{}), None{}, fnone),
            h
          )
        )
      )
    case None{}:
      k => h => Empty.absurd(
        {f(Cell.value(V, b)) == Some{w}: Maybe<&2, W>},
        Shared.Maybe.none_ne_some(
          W,
          w,
          Equal.trans(
            Maybe<&2, W>,
            None{},
            f(None{}),
            Some{w},
            Equal.sym(Maybe<&2, W>, f(None{}), None{}, fnone),
            h
          )
        )
      )

# a cell keeps its join with one that agrees with it
def Cell.keeps_pick(
  ~V: Data,
  ~same: V -> V -> Bool,
  ~laws: Shared.Eq.Laws(V, same),
  a: Maybe<&2, Cell<V>>,
  b: Maybe<&2, Cell<V>>
) -> {
  Cell.agrees.here(~V, ~same, a, b) == True{}: Bool
} -> {
  Cell.keeps(~V, ~same, a, Tries.Trie.pick(~Cell<V>, ~Cell.join(~V, ~same), a, b)) == True{}: Bool
}:
  match a b:
    case None{} y:
      h => {==}
    case Some{one{x}} None{}:
      h => Shared.Eq.refl(~V, ~same, laws, x)
    case Some{one{+x}} Some{one{y}}:
      h =>
        %Equal.sym(Bool, same(x, y), True{}, h):
          {
            Cell.keeps(
              ~V,
              ~same,
              Some{one{x}},
              Some{Bool.pick(Cell<V>, _, one{x}, many{})}
            )
              == True{}: Bool
          }
        Shared.Eq.refl(~V, ~same, laws, x)
    case Some{one{x}} Some{many{}}:
      h => Empty.absurd(
        {Cell.keeps(~V, ~same, Some{one{x}}, Some{many{}}) == True{}: Bool},
        Shared.Bool.false_ne_true(h)
      )
    case Some{many{}} None{}:
      h => {==}
    case Some{many{}} Some{y}:
      h => {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof's statement, or code that the laws split on, keeps each and/or as one value
# bend-lint: expect-begin bend-lint-rules/performance/missed_fork@hint -- a proof does not run, so it gains nothing from a fork
# a trie grows to itself
def Cell.grows_refl(
  ~V: Data,
  ~same: V -> V -> Bool,
  ~laws: Shared.Eq.Laws(V, same),
  s: Tries.Trie<Cell<V>>
) -> {Cell.grows(~V, ~same, s, s) == True{}: Bool}:
  match s:
    case Tries.tip{}:
      {==}
    case Tries.bin{+h, +z, +o}:
      Shared.Bool.and_both(
        Cell.keeps(~V, ~same, h, h),
        Bool.and(Cell.grows(~V, ~same, z, z), Cell.grows(~V, ~same, o, o))
      )(
        Cell.keeps_refl(~V, ~same, ~laws, h)
      )(
        Shared.Bool.and_both(
          Cell.grows(~V, ~same, z, z),
          Cell.grows(~V, ~same, o, o)
        )(Cell.grows_refl(~V, ~same, ~laws, z))(Cell.grows_refl(~V, ~same, ~laws, o))
      )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information
# bend-lint: expect-end bend-lint-rules/performance/missed_fork@hint

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof's statement, or code that the laws split on, keeps each and/or as one value
# bend-lint: expect-begin bend-lint-rules/performance/missed_fork@hint -- a proof does not run, so it gains nothing from a fork
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# a trie that holds no cell grows to any trie
def Cell.none_grows(
  ~V: Data,
  ~same: V -> V -> Bool,
  s: Tries.Trie<Cell<V>>,
  w: Tries.Trie<Cell<V>>
) -> {Cell.none(V, s) == True{}: Bool} -> {Cell.grows(~V, ~same, s, w) == True{}: Bool}:
  match s w:
    case Tries.tip{} y:
      h => {==}
    case Tries.bin{h0, z, o} Tries.tip{}:
      h => h
    case Tries.bin{+h1, +z1, +o1} Tries.bin{h2, +z2, +o2}:
      +h =>
        +rest = Shared.Bool.and_true_right(
          Maybe.is_none(&2, Cell<V>, h1),
          Bool.and(Cell.none(V, z1), Cell.none(V, o1))
        )(h)
        %Equal.sym(
          Maybe<&2, Cell<V>>,
          h1,
          None{},
          Shared.Maybe.is_none_eq(
            Cell<V>,
            h1
          )(
            Shared.Bool.and_true_left(
              Maybe.is_none(&2, Cell<V>, h1),
              Bool.and(Cell.none(V, z1), Cell.none(V, o1))
            )(h)
          )
        ): {
          Bool.and(
            Cell.keeps(~V, ~same, _, h2),
            Bool.and(Cell.grows(~V, ~same, z1, z2), Cell.grows(~V, ~same, o1, o2))
          )
            == True{}: Bool
        }
        Shared.Bool.and_both(
          Cell.grows(~V, ~same, z1, z2),
          Cell.grows(~V, ~same, o1, o2)
        )(
          Cell.none_grows(
            ~V,
            ~same,
            z1,
            z2
          )(Shared.Bool.and_true_left(Cell.none(V, z1), Cell.none(V, o1))(rest))
        )(
          Cell.none_grows(
            ~V,
            ~same,
            o1,
            o2
          )(Shared.Bool.and_true_right(Cell.none(V, z1), Cell.none(V, o1))(rest))
        )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information
# bend-lint: expect-end bend-lint-rules/performance/missed_fork@hint
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# a cell kept as none was none
def Cell.keeps_none(
  ~V: Data,
  ~same: V -> V -> Bool,
  a: Maybe<&2, Cell<V>>
) -> {
  Cell.keeps(~V, ~same, a, None{}) == True{}: Bool
} -> {Maybe.is_none(&2, Cell<V>, a) == True{}: Bool}:
  match a:
    case None{}:
      h => {==}
    case Some{one{x}}:
      h => h
    case Some{many{}}:
      h => h

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof's statement, or code that the laws split on, keeps each and/or as one value
# bend-lint: expect-begin bend-lint-rules/performance/missed_fork@hint -- a proof does not run, so it gains nothing from a fork
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# a trie that grows to one that holds no cell holds none
def Cell.grows_none(
  ~V: Data,
  ~same: V -> V -> Bool,
  s: Tries.Trie<Cell<V>>,
  s2: Tries.Trie<Cell<V>>
) -> {
  Cell.grows(~V, ~same, s, s2) == True{}: Bool
} -> {Cell.none(V, s2) == True{}: Bool} -> {Cell.none(V, s) == True{}: Bool}:
  match s s2:
    case Tries.tip{} y:
      g => h => {==}
    case Tries.bin{h0, z, o} Tries.tip{}:
      g => h => g
    case Tries.bin{+h1, +z1, +o1} Tries.bin{+h2, +z2, +o2}:
      +g => +h =>
        +gr = Shared.Bool.and_true_right(
          Cell.keeps(~V, ~same, h1, h2),
          Bool.and(Cell.grows(~V, ~same, z1, z2), Cell.grows(~V, ~same, o1, o2))
        )(g)
        +nr = Shared.Bool.and_true_right(
          Maybe.is_none(&2, Cell<V>, h2),
          Bool.and(Cell.none(V, z2), Cell.none(V, o2))
        )(h)
        Shared.Bool.and_both(
          Maybe.is_none(&2, Cell<V>, h1),
          Bool.and(Cell.none(V, z1), Cell.none(V, o1))
        )(Cell.keeps_none(~V, ~same, h1)(
            %Shared.Maybe.is_none_eq(Cell<V>, h2)(Shared.Bool.and_true_left(Maybe.is_none(&2, Cell<V>, h2), Bool.and(Cell.none(V, z2), Cell.none(V, o2)))(h)):
              {Cell.keeps(~V, ~same, h1, _) == True{}: Bool}
            Shared.Bool.and_true_left(Cell.keeps(~V, ~same, h1, h2), Bool.and(Cell.grows(~V, ~same, z1, z2), Cell.grows(~V, ~same, o1, o2)))(g)))(
          Shared.Bool.and_both(
            Cell.none(V, z1),
            Cell.none(V, o1)
          )(
            Cell.grows_none(
              ~V,
              ~same,
              z1,
              z2
            )(
              Shared.Bool.and_true_left(
                Cell.grows(~V, ~same, z1, z2),
                Cell.grows(~V, ~same, o1, o2)
              )(gr)
            )(Shared.Bool.and_true_left(Cell.none(V, z2), Cell.none(V, o2))(nr))
          )(
            Cell.grows_none(
              ~V,
              ~same,
              o1,
              o2
            )(
              Shared.Bool.and_true_right(
                Cell.grows(~V, ~same, z1, z2),
                Cell.grows(~V, ~same, o1, o2)
              )(gr)
            )(Shared.Bool.and_true_right(Cell.none(V, z2), Cell.none(V, o2))(nr))
          )
        )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information
# bend-lint: expect-end bend-lint-rules/performance/missed_fork@hint
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# growth composes
law Cell.grows_trans:
  for ~V: Data
  for ~same: V -> V -> Bool
  for ~laws: Shared.Eq.Laws(V, same)
  for s1: Tries.Trie<Cell<V>>
  for s2: Tries.Trie<Cell<V>>
  for s3: Tries.Trie<Cell<V>>
  {Cell.grows(~V, ~same, s1, s2) == True{}: Bool}
    -> {Cell.grows(~V, ~same, s2, s3) == True{}: Bool}
    -> {Cell.grows(~V, ~same, s1, s3) == True{}: Bool}

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof's statement, or code that the laws split on, keeps each and/or as one value
# bend-lint: expect-begin bend-lint-rules/performance/missed_fork@hint -- a proof does not run, so it gains nothing from a fork
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
def Cell.grows_trans(ty, same, laws, s1, s2, s3):
  match s1 s2 s3:
    case Tries.tip{} y w:
      g1 => g2 => {==}
    case Tries.bin{h1, z1, o1} Tries.tip{} w:
      g1 => g2 => Cell.none_grows(~ty, ~same, Tries.bin{h1, z1, o1}, w)(g1)
    case Tries.bin{h1, z1, o1} Tries.bin{h2, z2, o2} Tries.tip{}:
      g1 => g2 => Cell.grows_none(~ty, ~same, Tries.bin{h1, z1, o1}, Tries.bin{h2, z2, o2})(g1)(g2)
    case Tries.bin{+h1, +z1, +o1} Tries.bin{+h2, +z2, +o2} Tries.bin{+h3, +z3, +o3}:
      +g1 => +g2 =>
        +a1 = Shared.Bool.and_true_right(
          Cell.keeps(~ty, ~same, h1, h2),
          Bool.and(Cell.grows(~ty, ~same, z1, z2), Cell.grows(~ty, ~same, o1, o2))
        )(g1)
        +a2 = Shared.Bool.and_true_right(
          Cell.keeps(~ty, ~same, h2, h3),
          Bool.and(Cell.grows(~ty, ~same, z2, z3), Cell.grows(~ty, ~same, o2, o3))
        )(g2)
        Shared.Bool.and_both(
          Cell.keeps(~ty, ~same, h1, h3),
          Bool.and(Cell.grows(~ty, ~same, z1, z3), Cell.grows(~ty, ~same, o1, o3))
        )(
          Cell.keeps_trans(
            ~ty,
            ~same,
            ~laws,
            h1,
            h2,
            h3
          )(
            Shared.Bool.and_true_left(
              Cell.keeps(~ty, ~same, h1, h2),
              Bool.and(Cell.grows(~ty, ~same, z1, z2), Cell.grows(~ty, ~same, o1, o2))
            )(g1)
          )(
            Shared.Bool.and_true_left(
              Cell.keeps(~ty, ~same, h2, h3),
              Bool.and(Cell.grows(~ty, ~same, z2, z3), Cell.grows(~ty, ~same, o2, o3))
            )(g2)
          )
        )(
          Shared.Bool.and_both(
            Cell.grows(~ty, ~same, z1, z3),
            Cell.grows(~ty, ~same, o1, o3)
          )(
            Cell.grows_trans(
              ~ty,
              ~same,
              ~laws,
              z1,
              z2,
              z3
            )(
              Shared.Bool.and_true_left(
                Cell.grows(~ty, ~same, z1, z2),
                Cell.grows(~ty, ~same, o1, o2)
              )(a1)
            )(
              Shared.Bool.and_true_left(
                Cell.grows(~ty, ~same, z2, z3),
                Cell.grows(~ty, ~same, o2, o3)
              )(a2)
            )
          )(
            Cell.grows_trans(
              ~ty,
              ~same,
              ~laws,
              o1,
              o2,
              o3
            )(
              Shared.Bool.and_true_right(
                Cell.grows(~ty, ~same, z1, z2),
                Cell.grows(~ty, ~same, o1, o2)
              )(a1)
            )(
              Shared.Bool.and_true_right(
                Cell.grows(~ty, ~same, z2, z3),
                Cell.grows(~ty, ~same, o2, o3)
              )(a2)
            )
          )
        )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information
# bend-lint: expect-end bend-lint-rules/performance/missed_fork@hint
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# a sync that agrees grows a trie
law Cell.grows_join:
  for ~V: Data
  for ~same: V -> V -> Bool
  for ~laws: Shared.Eq.Laws(V, same)
  for s: Tries.Trie<Cell<V>>
  for t: Tries.Trie<Cell<V>>
  {Cell.agrees(~V, ~same, s, t) == True{}: Bool}
    -> {
      Cell.grows(
        ~V,
        ~same,
        s,
        Tries.Trie.union(~Cell<V>, ~Cell.join(~V, ~same), s, t)
      )
        == True{}: Bool
    }

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof's statement, or code that the laws split on, keeps each and/or as one value
# bend-lint: expect-begin bend-lint-rules/performance/missed_fork@hint -- a proof does not run, so it gains nothing from a fork
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
def Cell.grows_join(ty, same, laws, s, t):
  match s t:
    case Tries.tip{} y:
      a => {==}
    case Tries.bin{h, z, o} Tries.tip{}:
      a => Cell.grows_refl(~ty, ~same, ~laws, Tries.bin{h, z, o})
    case Tries.bin{+h1, +z1, +o1} Tries.bin{+h2, +z2, +o2}:
      +a =>
        +ar = Shared.Bool.and_true_right(
          Cell.agrees.here(~ty, ~same, h1, h2),
          Bool.and(Cell.agrees(~ty, ~same, z1, z2), Cell.agrees(~ty, ~same, o1, o2))
        )(a)
        Shared.Bool.and_both(
          Cell.keeps(~ty, ~same, h1, Tries.Trie.pick(~Cell<ty>, ~Cell.join(~ty, ~same), h1, h2)),
          Bool.and(
            Cell.grows(~ty, ~same, z1, Tries.Trie.union(~Cell<ty>, ~Cell.join(~ty, ~same), z1, z2)),
            Cell.grows(~ty, ~same, o1, Tries.Trie.union(~Cell<ty>, ~Cell.join(~ty, ~same), o1, o2))
          )
        )(
          Cell.keeps_pick(
            ~ty,
            ~same,
            ~laws,
            h1,
            h2
          )(
            Shared.Bool.and_true_left(
              Cell.agrees.here(~ty, ~same, h1, h2),
              Bool.and(Cell.agrees(~ty, ~same, z1, z2), Cell.agrees(~ty, ~same, o1, o2))
            )(a)
          )
        )(
          Shared.Bool.and_both(
            Cell.grows(~ty, ~same, z1, Tries.Trie.union(~Cell<ty>, ~Cell.join(~ty, ~same), z1, z2)),
            Cell.grows(~ty, ~same, o1, Tries.Trie.union(~Cell<ty>, ~Cell.join(~ty, ~same), o1, o2))
          )(
            Cell.grows_join(
              ~ty,
              ~same,
              ~laws,
              z1,
              z2
            )(
              Shared.Bool.and_true_left(
                Cell.agrees(~ty, ~same, z1, z2),
                Cell.agrees(~ty, ~same, o1, o2)
              )(ar)
            )
          )(
            Cell.grows_join(
              ~ty,
              ~same,
              ~laws,
              o1,
              o2
            )(
              Shared.Bool.and_true_right(
                Cell.agrees(~ty, ~same, z1, z2),
                Cell.agrees(~ty, ~same, o1, o2)
              )(ar)
            )
          )
        )

# a trie that holds no cell has no entry
def Cell.none_size(
  -V: Data,
  t: Tries.Trie<Cell<V>>
) -> {Cell.none(V, t) == True{}: Bool} -> {Tries.Trie.size(Cell<V>, t) == 0n: Nat}:
  match t:
    case Tries.tip{}:
      e => {==}
    case Tries.bin{None{}, +z, +o}:
      +e =>
        %Equal.sym(
          Nat,
          Tries.Trie.size(Cell<V>, z),
          0n,
          Cell.none_size(V, z)(Shared.Bool.and_true_left(Cell.none(V, z), Cell.none(V, o))(e))
        ): {Nat.add(_, Tries.Trie.size(Cell<V>, o)) == 0n: Nat}
        %Equal.sym(
          Nat,
          Tries.Trie.size(Cell<V>, o),
          0n,
          Cell.none_size(V, o)(Shared.Bool.and_true_right(Cell.none(V, z), Cell.none(V, o))(e))
        ): {Nat.add(0n, _) == 0n: Nat}
        {==}
    case Tries.bin{Some{c}, z, o}:
      e => Empty.absurd(
        {Tries.Trie.size(Cell<V>, Tries.bin{Some{c}, z, o}) == 0n: Nat},
        Shared.Bool.false_ne_true(e)
      )

# a trie that holds no cell holds none below any key
def Cell.none_under(
  -V: Data,
  t: Tries.Trie<Cell<V>>,
  k: List<&2, Bool>
) -> {
  Cell.none(V, t) == True{}: Bool
} -> {Cell.none(V, Tries.Trie.under(Cell<V>, t, k)) == True{}: Bool}:
  match t k:
    case Tries.tip{} q:
      e => {==}
    case Tries.bin{h, z, o} Nil{}:
      e => e
    case Tries.bin{+h, +z, +o} Con{False{}, r}:
      e => Cell.none_under(
        V,
        z,
        r
      )(
        Shared.Bool.and_true_left(
          Cell.none(V, z),
          Cell.none(V, o)
        )(
          Shared.Bool.and_true_right(
            Maybe.is_none(&2, Cell<V>, h),
            Bool.and(Cell.none(V, z), Cell.none(V, o))
          )(e)
        )
      )
    case Tries.bin{+h, +z, +o} Con{True{}, r}:
      e => Cell.none_under(
        V,
        o,
        r
      )(
        Shared.Bool.and_true_right(
          Cell.none(V, z),
          Cell.none(V, o)
        )(
          Shared.Bool.and_true_right(
            Maybe.is_none(&2, Cell<V>, h),
            Bool.and(Cell.none(V, z), Cell.none(V, o))
          )(e)
        )
      )

# a trie grows into the empty trie only when it holds no cell
def Cell.grows_tip(
  ~V: Data,
  ~same: V -> V -> Bool,
  x: Tries.Trie<Cell<V>>
) -> {Cell.grows(~V, ~same, x, Tries.tip{}) == Cell.none(V, x): Bool}:
  match x:
    case Tries.tip{}:
      {==}
    case Tries.bin{h, z, o}:
      {==}

# a trie grows from one no larger: what grows keeps every entry
def Cell.grows_size(
  ~V: Data,
  ~same: V -> V -> Bool,
  s: Tries.Trie<Cell<V>>,
  s2: Tries.Trie<Cell<V>>
) -> {
  Cell.grows(~V, ~same, s, s2) == True{}: Bool
} -> {Nat.is_le(Tries.Trie.size(Cell<V>, s), Tries.Trie.size(Cell<V>, s2)) == True{}: Bool}:
  match s s2:
    case Tries.tip{} y:
      e => Shared.Nat.le_zero(Tries.Trie.size(Cell<V>, y))
    case Tries.bin{+h, +z, +o} Tries.tip{}:
      e =>
        %Equal.sym(
          Nat,
          Tries.Trie.size(Cell<V>, Tries.bin{h, z, o}),
          0n,
          Cell.none_size(V, Tries.bin{h, z, o})(e)
        ): {Nat.is_le(_, 0n) == True{}: Bool}
        {==}
    case Tries.bin{None{}, +z1, +o1} Tries.bin{None{}, +z2, +o2}:
      +e => Shared.Nat.add_le(
        Tries.Trie.size(Cell<V>, z1),
        Tries.Trie.size(Cell<V>, z2),
        Tries.Trie.size(Cell<V>, o1),
        Tries.Trie.size(Cell<V>, o2)
      )(
        Cell.grows_size(
          ~V,
          ~same,
          z1,
          z2
        )(
          Shared.Bool.and_true_left(Cell.grows(~V, ~same, z1, z2), Cell.grows(~V, ~same, o1, o2))(e)
        )
      )(
        Cell.grows_size(
          ~V,
          ~same,
          o1,
          o2
        )(
          Shared.Bool.and_true_right(
            Cell.grows(~V, ~same, z1, z2),
            Cell.grows(~V, ~same, o1, o2)
          )(e)
        )
      )
    case Tries.bin{None{}, +z1, +o1} Tries.bin{Some{c2}, +z2, +o2}:
      +e => Shared.Nat.le_succ(
        Nat.add(Tries.Trie.size(Cell<V>, z1), Tries.Trie.size(Cell<V>, o1)),
        Nat.add(Tries.Trie.size(Cell<V>, z2), Tries.Trie.size(Cell<V>, o2))
      )(
        Shared.Nat.add_le(
          Tries.Trie.size(Cell<V>, z1),
          Tries.Trie.size(Cell<V>, z2),
          Tries.Trie.size(Cell<V>, o1),
          Tries.Trie.size(Cell<V>, o2)
        )(
          Cell.grows_size(
            ~V,
            ~same,
            z1,
            z2
          )(
            Shared.Bool.and_true_left(
              Cell.grows(~V, ~same, z1, z2),
              Cell.grows(~V, ~same, o1, o2)
            )(e)
          )
        )(
          Cell.grows_size(
            ~V,
            ~same,
            o1,
            o2
          )(
            Shared.Bool.and_true_right(
              Cell.grows(~V, ~same, z1, z2),
              Cell.grows(~V, ~same, o1, o2)
            )(e)
          )
        )
      )
    case Tries.bin{Some{c1}, +z1, +o1} Tries.bin{Some{+c2}, +z2, +o2}:
      +e => Shared.Nat.add_le(
        Tries.Trie.size(Cell<V>, z1),
        Tries.Trie.size(Cell<V>, z2),
        Tries.Trie.size(Cell<V>, o1),
        Tries.Trie.size(Cell<V>, o2)
      )(
        Cell.grows_size(
          ~V,
          ~same,
          z1,
          z2
        )(
          Shared.Bool.and_true_left(
            Cell.grows(~V, ~same, z1, z2),
            Cell.grows(~V, ~same, o1, o2)
          )(
            Shared.Bool.and_true_right(
              Cell.keeps(~V, ~same, Some{c1}, Some{c2}),
              Bool.and(Cell.grows(~V, ~same, z1, z2), Cell.grows(~V, ~same, o1, o2))
            )(e)
          )
        )
      )(
        Cell.grows_size(
          ~V,
          ~same,
          o1,
          o2
        )(
          Shared.Bool.and_true_right(
            Cell.grows(~V, ~same, z1, z2),
            Cell.grows(~V, ~same, o1, o2)
          )(
            Shared.Bool.and_true_right(
              Cell.keeps(~V, ~same, Some{c1}, Some{c2}),
              Bool.and(Cell.grows(~V, ~same, z1, z2), Cell.grows(~V, ~same, o1, o2))
            )(e)
          )
        )
      )
    case Tries.bin{Some{one{x}}, z1, o1} Tries.bin{None{}, z2, o2}:
      e => Empty.absurd(
        {
          Nat.is_le(
            Tries.Trie.size(Cell<V>, Tries.bin{Some{one{x}}, z1, o1}),
            Tries.Trie.size(Cell<V>, Tries.bin{None{}, z2, o2})
          )
            == True{}: Bool
        },
        Shared.Bool.false_ne_true(e)
      )
    case Tries.bin{Some{many{}}, z1, o1} Tries.bin{None{}, z2, o2}:
      e => Empty.absurd(
        {
          Nat.is_le(
            Tries.Trie.size(Cell<V>, Tries.bin{Some{many{}}, z1, o1}),
            Tries.Trie.size(Cell<V>, Tries.bin{None{}, z2, o2})
          )
            == True{}: Bool
        },
        Shared.Bool.false_ne_true(e)
      )

# the entries below a key grow as the trie does
def Cell.grows_under(
  ~V: Data,
  ~same: V -> V -> Bool,
  s: Tries.Trie<Cell<V>>,
  s2: Tries.Trie<Cell<V>>,
  k: List<&2, Bool>
) -> {
  Cell.grows(~V, ~same, s, s2) == True{}: Bool
} -> {
  Cell.grows(
    ~V,
    ~same,
    Tries.Trie.under(Cell<V>, s, k),
    Tries.Trie.under(Cell<V>, s2, k)
  )
    == True{}: Bool
}:
  match s s2 k:
    case Tries.tip{} y q:
      e => {==}
    case Tries.bin{+h, +z, +o} Tries.tip{} +q:
      e =>
        %Equal.sym(
          Bool,
          Cell.grows(~V, ~same, Tries.Trie.under(Cell<V>, Tries.bin{h, z, o}, q), Tries.tip{}),
          Cell.none(V, Tries.Trie.under(Cell<V>, Tries.bin{h, z, o}, q)),
          Cell.grows_tip(~V, ~same, Tries.Trie.under(Cell<V>, Tries.bin{h, z, o}, q))
        ): {_ == True{}: Bool}
        Cell.none_under(V, Tries.bin{h, z, o}, q)(e)
    case Tries.bin{h1, z1, o1} Tries.bin{h2, z2, o2} Nil{}:
      e => e
    case Tries.bin{+h1, +z1, +o1} Tries.bin{+h2, +z2, +o2} Con{False{}, r}:
      e => Cell.grows_under(
        ~V,
        ~same,
        z1,
        z2,
        r
      )(
        Shared.Bool.and_true_left(
          Cell.grows(~V, ~same, z1, z2),
          Cell.grows(~V, ~same, o1, o2)
        )(
          Shared.Bool.and_true_right(
            Cell.keeps(~V, ~same, h1, h2),
            Bool.and(Cell.grows(~V, ~same, z1, z2), Cell.grows(~V, ~same, o1, o2))
          )(e)
        )
      )
    case Tries.bin{+h1, +z1, +o1} Tries.bin{+h2, +z2, +o2} Con{True{}, r}:
      e => Cell.grows_under(
        ~V,
        ~same,
        o1,
        o2,
        r
      )(
        Shared.Bool.and_true_right(
          Cell.grows(~V, ~same, z1, z2),
          Cell.grows(~V, ~same, o1, o2)
        )(
          Shared.Bool.and_true_right(
            Cell.keeps(~V, ~same, h1, h2),
            Bool.and(Cell.grows(~V, ~same, z1, z2), Cell.grows(~V, ~same, o1, o2))
          )(e)
        )
      )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information
# bend-lint: expect-end bend-lint-rules/performance/missed_fork@hint
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information
