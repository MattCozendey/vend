import Base
import ./bools.bend as Bools
import ./shared.bend as Shared
import ./tries.bend as Tries

# Cells
# -----
# A cell holds what every holder of a slot agrees on: one value, or Many when
# two holders put different values in the same slot. Joining cells is a
# semilattice, so a trie of cells is one too (Trie.union_comm and the rest):
# holders that take in each other's cells end with the same ones, and a
# contradiction is kept, not settled by an arbitrary winner.

# one value, or the mark that two values met
type Cell<-V: Data> is Data:
  One{value: V}
  Many{}

# what a and b agree on
def Cell.join(~V: Data, ~same: V -> V -> Bool, a: Cell<V>, b: Cell<V>) -> Cell<V>:
  match a b:
    case One{+x} One{y}:
      Bool.pick(Cell<V>, same(x, y), One{x}, Many{})
    case One{x} Many{}:
      Many{}
    case Many{} y:
      Many{}

# Laws
# ----
# Each law asks of same only that it is True for a value and itself (refl),
# and only for equal values (sound).

# a cell joined with itself is itself
law Cell.join_idem:
  for ~V: Data
  for ~same: V -> V -> Bool
  for ~refl: @x: V -> {same(x, x) == True{}: Bool}
  for a: Cell<V>
  {Cell.join(~V, ~same, a, a) == a: Cell<V>}

def Cell.join_idem(ty, same, refl, a):
  match a:
    case One{x}:
      %Equal.sym(
        Bool,
        same(x, x),
        True{},
        refl(x)
      ): {Bool.pick(Cell<ty>, _, One{x}, Many{}) == One{x}: Cell<ty>}
      {==}
    case Many{}:
      {==}

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Cell.join_comm once same(y, x) is known (back)
def Cell.join_comm.back(
  ~V: Data,
  ~same: V -> V -> Bool,
  ~refl: @x: V -> {same(x, x) == True{}: Bool},
  ~sound: @x: V -> @y: V -> {same(x, y) == True{}: Bool} -> {x == y: V},
  back: Bool,
  +x: V,
  y: V,
  no: {same(x, y) == False{}: Bool},
  e: {same(y, x) == back: Bool}
) -> {Many{} == Bool.pick(Cell<V>, back, One{y}, Many{}): Cell<V>}:
  match back:
    case False{}:
      {==}
    case True{}:
      Empty.absurd(
        {Many{} == One{y}: Cell<V>},
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
              Equal.cong(V, Bool, z => same(x, z), y, x, sound(y)(x)(e)),
              refl(x)
            )
          )
        )
      )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# Cell.join_comm once same(x, y) is known (held)
def Cell.join_comm.at(
  ~V: Data,
  ~same: V -> V -> Bool,
  ~refl: @x: V -> {same(x, x) == True{}: Bool},
  ~sound: @x: V -> @y: V -> {same(x, y) == True{}: Bool} -> {x == y: V},
  held: Bool,
  +x: V,
  +y: V,
  e: {same(x, y) == held: Bool}
) -> {
  Bool.pick(
    Cell<V>,
    held,
    One{x},
    Many{}
  )
    == Bool.pick(Cell<V>, same(y, x), One{y}, Many{}): Cell<V>
}:
  match held:
    case True{}:
      %sound(x)(y)(e): {One{x} == Bool.pick(Cell<V>, same(_, x), One{_}, Many{}): Cell<V>}
      %Equal.sym(
        Bool,
        same(x, x),
        True{},
        refl(x)
      ): {One{x} == Bool.pick(Cell<V>, _, One{x}, Many{}): Cell<V>}
      {==}
    case False{}:
      Cell.join_comm.back(~V, ~same, ~refl, ~sound, same(y, x), x, y, e, {==})

# a join is the same either way round
law Cell.join_comm:
  for ~V: Data
  for ~same: V -> V -> Bool
  for ~refl: @x: V -> {same(x, x) == True{}: Bool}
  for ~sound: @x: V -> @y: V -> {same(x, y) == True{}: Bool} -> {x == y: V}
  for a: Cell<V>
  for b: Cell<V>
  {Cell.join(~V, ~same, a, b) == Cell.join(~V, ~same, b, a): Cell<V>}

def Cell.join_comm(ty, same, refl, sound, a, b):
  match a b:
    case One{+x} One{+y}:
      Cell.join_comm.at(~ty, ~same, ~refl, ~sound, same(x, y), x, y, {==})
    case One{x} Many{}:
      {==}
    case Many{} One{y}:
      {==}
    case Many{} Many{}:
      {==}

# a cell that met Many is Many, whatever x and y were (held)
def Cell.join_assoc.many(
  ~V: Data,
  ~same: V -> V -> Bool,
  held: Bool,
  x: V
) -> {Cell.join(~V, ~same, Bool.pick(Cell<V>, held, One{x}, Many{}), Many{}) == Many{}: Cell<V>}:
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
  ~sound: @x: V -> @y: V -> {same(x, y) == True{}: Bool} -> {x == y: V},
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
    Bool.pick(Cell<V>, xy, One{x}, Many{}),
    One{z}
  )
    == Cell.join(~V, ~same, One{x}, Bool.pick(Cell<V>, yz, One{y}, Many{})): Cell<V>
}:
  match xy yz:
    case True{} True{}:
      %sound(y)(z)(e2):
        {
          Cell.join(
            ~V,
            ~same,
            Bool.pick(Cell<V>, True{}, One{x}, Many{}),
            One{_}
          )
            == Cell.join(~V, ~same, One{x}, Bool.pick(Cell<V>, True{}, One{y}, Many{})): Cell<V>
        }
      {==}
    case True{} False{}:
      %Equal.sym(V, x, y, sound(x)(y)(e1)):
        {
          Cell.join(
            ~V,
            ~same,
            Bool.pick(Cell<V>, True{}, One{_}, Many{}),
            One{z}
          )
            == Cell.join(~V, ~same, One{_}, Bool.pick(Cell<V>, False{}, One{y}, Many{})): Cell<V>
        }
      %Equal.sym(
        Bool,
        same(y, z),
        False{},
        e2
      ): {Bool.pick(Cell<V>, _, One{y}, Many{}) == Many{}: Cell<V>}
      {==}
    case False{} True{}:
      %Equal.sym(
        Bool,
        same(x, y),
        False{},
        e1
      ): {Many{} == Bool.pick(Cell<V>, _, One{x}, Many{}): Cell<V>}
      {==}
    case False{} False{}:
      {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# a join groups either way
law Cell.join_assoc:
  for ~V: Data
  for ~same: V -> V -> Bool
  for ~refl: @x: V -> {same(x, x) == True{}: Bool}
  for ~sound: @x: V -> @y: V -> {same(x, y) == True{}: Bool} -> {x == y: V}
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

def Cell.join_assoc(ty, same, refl, sound, a, b, c):
  match a b c:
    case Many{} y w:
      {==}
    case One{x} Many{} w:
      {==}
    case One{+x} One{+y} Many{}:
      Cell.join_assoc.many(~ty, ~same, same(x, y), x)
    case One{+x} One{+y} One{+z}:
      Cell.join_assoc.at(~ty, ~same, ~sound, same(x, y), same(y, z), x, y, z, {==}, {==})

# a and b hold the same, as same calls values the same
def Cell.same(~V: Data, ~same: V -> V -> Bool, a: Cell<V>, b: Cell<V>) -> Bool:
  match a b:
    case One{x} One{y}:
      same(x, y)
    case Many{} Many{}:
      True{}
    case _ _:
      False{}

# Cell.same is True only for equal cells
law Cell.same_sound:
  for ~V: Data
  for ~same: V -> V -> Bool
  for ~sound: @x: V -> @y: V -> {same(x, y) == True{}: Bool} -> {x == y: V}
  for a: Cell<V>
  for b: Cell<V>
  {Cell.same(~V, ~same, a, b) == True{}: Bool} -> {a == b: Cell<V>}

def Cell.same_sound(ty, same, sound, a, b):
  match a b:
    case One{x} One{y}:
      h =>
        %sound(x)(y)(h): {One{x} == One{_}: Cell<ty>}
        {==}
    case One{x} Many{}:
      h => Empty.absurd({One{x} == Many{}: Cell<ty>}, Shared.Bool.false_ne_true(h))
    case Many{} One{y}:
      h => Empty.absurd({Many{} == One{y}: Cell<ty>}, Shared.Bool.false_ne_true(h))
    case Many{} Many{}:
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
    case Some{One{x}} Some{One{y}}:
      same(x, y)
    case Some{One{x}} Some{Many{}}:
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
    case Tries.Tip{} y:
      True{}
    case Tries.Bin{h, z, o} Tries.Tip{}:
      True{}
    case Tries.Bin{h1, z1, o1} Tries.Bin{h2, z2, o2}:
      Bool.and(
        Cell.agrees.here(~V, ~same, h1, h2),
        Bool.and(Cell.agrees(~V, ~same, z1, z2), Cell.agrees(~V, ~same, o1, o2))
      )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# a cell that is here, whether One or not
def Cell.is_one(-V: Data, m: Maybe<&2, Cell<V>>) -> Bool:
  match m:
    case Some{One{x}}:
      True{}
    case _:
      False{}

# the value v that a holds is kept when b agrees with it
def Cell.kept.here(
  ~V: Data,
  ~same: V -> V -> Bool,
  ~sound: @x: V -> @y: V -> {same(x, y) == True{}: Bool} -> {x == y: V},
  a: Maybe<&2, Cell<V>>,
  b: Maybe<&2, Cell<V>>,
  -v: V
) -> {
  Cell.agrees.here(~V, ~same, a, b) == True{}: Bool
} -> {
  a == Some{One{v}}: Maybe<&2, Cell<V>>
} -> {Tries.Trie.pick(~Cell<V>, ~Cell.join(~V, ~same), a, b) == Some{One{v}}: Maybe<&2, Cell<V>>}:
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
            == Some{One{v}}: Maybe<&2, Cell<V>>
        },
        Shared.Bool.false_ne_true(
          Equal.cong(Maybe<&2, Cell<V>>, Bool, m => Cell.is_one(V, m), None{}, Some{One{v}}, g)
        )
      )
    case Some{Many{}} y:
      h => g => Empty.absurd(
        {
          Tries.Trie.pick(
            ~Cell<V>,
            ~Cell.join(~V, ~same),
            Some{Many{}},
            y
          )
            == Some{One{v}}: Maybe<&2, Cell<V>>
        },
        Shared.Bool.false_ne_true(
          Equal.cong(
            Maybe<&2, Cell<V>>,
            Bool,
            m => Cell.is_one(V, m),
            Some{Many{}},
            Some{One{v}},
            g
          )
        )
      )
    case Some{One{x}} None{}:
      h => g => g
    case Some{One{+x}} Some{One{y}}:
      h => g =>
        %Equal.sym(
          Bool,
          same(x, y),
          True{},
          h
        ): {Some{Bool.pick(Cell<V>, _, One{x}, Many{})} == Some{One{v}}: Maybe<&2, Cell<V>>}
        g
    case Some{One{x}} Some{Many{}}:
      h => g => Empty.absurd(
        {Some{Many{}} == Some{One{v}}: Maybe<&2, Cell<V>>},
        Shared.Bool.false_ne_true(h)
      )

# a value that s holds is kept in s and t, when t agrees with s
law Cell.agrees_kept:
  for ~V: Data
  for ~same: V -> V -> Bool
  for ~sound: @x: V -> @y: V -> {same(x, y) == True{}: Bool} -> {x == y: V}
  for s: Tries.Trie<Cell<V>>
  for t: Tries.Trie<Cell<V>>
  for k: List<&2, Bool>
  for -v: V
  {Cell.agrees(~V, ~same, s, t) == True{}: Bool}
    -> {Tries.Trie.get(Cell<V>, s, k) == Some{One{v}}: Maybe<&2, Cell<V>>}
    -> {
      Tries.Trie.get(
        Cell<V>,
        Tries.Trie.union(~Cell<V>, ~Cell.join(~V, ~same), s, t),
        k
      )
        == Some{One{v}}: Maybe<&2, Cell<V>>
    }

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- an equality, or a proof, keeps each and/or as one value for the proofs to split on
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
def Cell.agrees_kept(ty, same, sound, s, t, k, v):
  match s t k:
    case Tries.Tip{} y q:
      a => g => Empty.absurd(
        {Tries.Trie.get(Cell<ty>, y, q) == Some{One{v}}: Maybe<&2, Cell<ty>>},
        Shared.Bool.false_ne_true(
          Equal.cong(Maybe<&2, Cell<ty>>, Bool, m => Cell.is_one(ty, m), None{}, Some{One{v}}, g)
        )
      )
    case Tries.Bin{h, z, o} Tries.Tip{} q:
      a => g => g
    case Tries.Bin{+h1, +z1, +o1} Tries.Bin{+h2, +z2, +o2} Nil{}:
      +a => g => Cell.kept.here(
        ~ty,
        ~same,
        ~sound,
        h1,
        h2,
        v
      )(
        Bools.Bool.and_true_left(
          Cell.agrees.here(~ty, ~same, h1, h2),
          Bool.and(Cell.agrees(~ty, ~same, z1, z2), Cell.agrees(~ty, ~same, o1, o2))
        )(a)
      )(g)
    case Tries.Bin{+h1, +z1, +o1} Tries.Bin{+h2, +z2, +o2} Con{False{}, r}:
      +a => g => Cell.agrees_kept(
        ~ty,
        ~same,
        ~sound,
        z1,
        z2,
        r,
        v
      )(
        Bools.Bool.and_true_left(
          Cell.agrees(~ty, ~same, z1, z2),
          Cell.agrees(~ty, ~same, o1, o2)
        )(
          Bools.Bool.and_true_right(
            Cell.agrees.here(~ty, ~same, h1, h2),
            Bool.and(Cell.agrees(~ty, ~same, z1, z2), Cell.agrees(~ty, ~same, o1, o2))
          )(a)
        )
      )(g)
    case Tries.Bin{+h1, +z1, +o1} Tries.Bin{+h2, +z2, +o2} Con{True{}, r}:
      +a => g => Cell.agrees_kept(
        ~ty,
        ~same,
        ~sound,
        o1,
        o2,
        r,
        v
      )(
        Bools.Bool.and_true_right(
          Cell.agrees(~ty, ~same, z1, z2),
          Cell.agrees(~ty, ~same, o1, o2)
        )(
          Bools.Bool.and_true_right(
            Cell.agrees.here(~ty, ~same, h1, h2),
            Bool.and(Cell.agrees(~ty, ~same, z1, z2), Cell.agrees(~ty, ~same, o1, o2))
          )(a)
        )
      )(g)
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# nothing contradicts a value of s
def Cell.agrees_tip(
  ~V: Data,
  ~same: V -> V -> Bool,
  s: Tries.Trie<Cell<V>>
) -> {Cell.agrees(~V, ~same, s, Tries.Tip{}) == True{}: Bool}:
  match s:
    case Tries.Tip{}:
      {==}
    case Tries.Bin{h, z, o}:
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
    case Some{One{x}}:
      {==}
    case Some{Many{}}:
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

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- an equality, or a proof, keeps each and/or as one value for the proofs to split on
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
def Cell.agrees_one(ty, same, s, k, x):
  match s k:
    case Tries.Tip{} q:
      g => {==}
    case Tries.Bin{+h, +z, +o} Nil{}:
      g =>
        %Equal.sym(
          Maybe<&2, Cell<ty>>,
          h,
          None{},
          g
        ): {
          Bool.and(
            Cell.agrees.here(~ty, ~same, _, Some{x}),
            Bool.and(
              Cell.agrees(~ty, ~same, z, Tries.Tip{}),
              Cell.agrees(~ty, ~same, o, Tries.Tip{})
            )
          )
            == True{}: Bool
        }
        %Equal.sym(
          Bool,
          Cell.agrees(~ty, ~same, z, Tries.Tip{}),
          True{},
          Cell.agrees_tip(~ty, ~same, z)
        ):
          {Bool.and(_, Cell.agrees(~ty, ~same, o, Tries.Tip{})) == True{}: Bool}
        Cell.agrees_tip(~ty, ~same, o)
    case Tries.Bin{+h, +z, +o} Con{False{}, +r}:
      g => Bools.Bool.and_both(
        Cell.agrees.here(~ty, ~same, h, None{}),
        Bool.and(
          Cell.agrees(~ty, ~same, z, Tries.Trie.one(Cell<ty>, r, x)),
          Cell.agrees(~ty, ~same, o, Tries.Tip{})
        )
      )(
        Cell.agrees_none(~ty, ~same, h)
      )(
        Bools.Bool.and_both(
          Cell.agrees(~ty, ~same, z, Tries.Trie.one(Cell<ty>, r, x)),
          Cell.agrees(~ty, ~same, o, Tries.Tip{})
        )(Cell.agrees_one(~ty, ~same, z, r, x)(g))(Cell.agrees_tip(~ty, ~same, o))
      )
    case Tries.Bin{+h, +z, +o} Con{True{}, +r}:
      g => Bools.Bool.and_both(
        Cell.agrees.here(~ty, ~same, h, None{}),
        Bool.and(
          Cell.agrees(~ty, ~same, z, Tries.Tip{}),
          Cell.agrees(~ty, ~same, o, Tries.Trie.one(Cell<ty>, r, x))
        )
      )(
        Cell.agrees_none(~ty, ~same, h)
      )(
        Bools.Bool.and_both(
          Cell.agrees(~ty, ~same, z, Tries.Tip{}),
          Cell.agrees(~ty, ~same, o, Tries.Trie.one(Cell<ty>, r, x))
        )(Cell.agrees_tip(~ty, ~same, z))(Cell.agrees_one(~ty, ~same, o, r, x)(g))
      )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information
